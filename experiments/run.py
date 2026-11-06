#!/usr/bin/env python
"""Driver: python run.py --exp A|B|C|D|plots|summary [--part reduced|full|all] [--config config.yaml]"""
import argparse, json, os, pathlib, time
import numpy as np, yaml
HERE = pathlib.Path(__file__).resolve().parent
RES = HERE / "results"; FIG = HERE / "figures"; CACHE = RES / "cache"
for d in (RES, FIG, CACHE):
    d.mkdir(exist_ok=True, parents=True)
import numba
from scipy.integrate import solve_ivp
import model as M, kernels as kn, evaluate as ev, dfs

IDX = {n: i for i, n in enumerate(M.NAMES)}


def checkpoints(horizon, lo=1.0, mant=(1, 1.5, 2, 3, 5, 7)):
    ts = []
    for k in range(int(np.floor(np.log10(lo))), int(np.ceil(np.log10(horizon))) + 1):
        for m in mant:
            t = m * 10.0 ** k
            if lo <= t <= horizon * (1 + 1e-9):
                ts.append(t)
    return np.array(sorted(set(ts)))


def ols(x, y):
    """OLS y ~ a + b x: slope, intercept, slope standard error, R^2."""
    x, y = np.asarray(x), np.asarray(y)
    n = len(x)
    Xm = np.c_[np.ones(n), x]
    beta, *_ = np.linalg.lstsq(Xm, y, rcond=None)
    res = y - Xm @ beta
    s2 = res @ res / max(n - 2, 1)
    se = np.sqrt(s2 * np.linalg.inv(Xm.T @ Xm)[1, 1])
    ss = ((y - y.mean()) ** 2).sum()
    return dict(slope=float(beta[1]), intercept=float(beta[0]), se=float(se),
                r2=float(1 - res @ res / ss) if ss > 0 else float("nan"), n=int(n))


def integrate_reduced(c, th0, horizon, method, rtol, atol, eps, relu0=1):
    """Plan 1.6: t in [0,1], then in s = log t. Output on 40 points per decade for t in [1e-3, horizon]."""
    t_small = np.geomspace(1e-3, 1, 61)
    r0 = solve_ivp(lambda t, y: c.flow(y, relu0, eps), (0, 1), th0, method=method, rtol=rtol, atol=atol,
                   t_eval=t_small)
    assert r0.status == 0, r0.message
    tl = np.union1d(np.geomspace(1, horizon, int(40 * np.log10(horizon)) + 1), checkpoints(horizon))
    tl = tl[tl <= horizon]
    s_eval = np.clip(np.log(tl), 0, np.log(horizon))
    r1 = solve_ivp(lambda s, y: np.exp(s) * c.flow(y, relu0, eps), (0, np.log(horizon)), r0.y[:, -1], method=method,
                   rtol=rtol, atol=atol, t_eval=s_eval)
    assert r1.status == 0, r1.message
    ts = np.r_[0.0, t_small[:-1], tl]
    th = np.c_[th0[None].T, r0.y[:, :-1], r1.y].T
    return ts, th, r0.nfev + r1.nfev


def derived(th):
    d = {n: th[..., IDX[n]] for n in M.NAMES}
    d["g1-d1"] = d["g1"] - d["d1"]
    d["g2-d2"] = d["g2"] - d["d2"]
    d["u"] = d["a2"] - d["b1"]
    d["v"] = d["g1-d1"] - d["g2-d2"]
    d["2(g1-d1)-a2"] = 2 * d["g1-d1"] - d["a2"]
    return d


def conserved(th, N):
    return th[..., IDX["g1"]] + (N - 1) * th[..., IDX["d1"]], th[..., IDX["g2"]] + (N - 1) * th[..., IDX["d2"]]


def slopes(ts, th, lo, hi):
    d = derived(th)
    m = (ts >= lo) & (ts <= hi * (1 + 1e-9))
    return {k: ols(np.log(ts[m]), d[k][m]) for k in ("a2", "b1", "g1-d1", "g2-d2", "g1", "g2", "d1", "d2")}


def handoff(ts, th):
    ok = (th[:, IDX["b2"]] <= 0) & (th[:, IDX["d2"]] <= 0)
    return float(ts[np.argmax(ok)]) if ok.any() else None


def exp_A_reduced(cfg):
    a = cfg["A"]; N, K = a["N"], a["K"]; o = a["ode"]
    c = M.Canonical(N, K); th0 = M.init_theta(N)
    t0 = time.time()
    ts, th, nfev = integrate_reduced(c, th0, o["horizon"], o["method"], o["rtol"], o["atol"], o["eps"])
    wall = time.time() - t0
    np.savez(RES / "A1_reduced.npz", t=ts, theta=th, names=M.NAMES, N=N, K=K)
    # regularisation insensitivity
    sens = {}
    for e in o["eps_check"]:
        t2, th2, _ = integrate_reduced(c, th0, o["horizon"], o["method"], o["rtol"], o["atol"], e)
        np.savez(RES / f"A1_reduced_eps{e:g}.npz", t=t2, theta=th2)
        sens[f"{e:g}"] = float(np.abs(th2 - th).max())
    # integrator cross-check: literal GD with eta on the scalars
    ec = a["euler_check"]
    chk = checkpoints(ec["horizon"]); x = th0.copy(); done = 0; rows = []
    for t in chk:
        n = int(round(t / ec["eta"]))
        x = c.euler(x, n - done, ec["eta"]); done = n; rows.append(x.copy())
    rows = np.array(rows)
    np.savez(RES / "A1_reduced_euler.npz", t=chk, theta=rows)
    interp = np.array([np.interp(np.log(chk), np.log(ts[1:]), th[1:, k]) for k in range(8)]).T
    print("euler-vs-ODE max|diff| for t>=1:", np.abs(interp - rows).max())
    d = derived(th)
    c1, c2 = conserved(th, N)
    out = dict(
        N=N, K=K, integrator=o, nfev=int(nfev), wall_s=wall,
        slopes=slopes(ts, th, a["fit_from"], o["horizon"]),
        handoff_t=handoff(ts, th), sup_u=float(d["u"][ts >= 1].max()), min_u=float(d["u"].min()),
        min_u_t_ge_1=float(d["u"][ts >= 1].min()), sup_abs_v=float(np.abs(d["v"]).max()),
        sup_abs_v_after_t1=float(np.abs(d["v"][ts >= 1]).max()),
        conservation_err_g1=float(np.abs(c1 - c1[0]).max()),
        conservation_g2_drift_total=float(np.abs(c2 - c2[0]).max()),
        conservation_g2_drift_after_t1e3=float(np.ptp(c2[ts >= 1e3])),
        final={n: float(th[-1, IDX[n]]) for n in M.NAMES}, final_t=float(ts[-1]),
        eps_sensitivity_max_abs=sens, euler_vs_ode_max_abs=float(np.abs(interp - rows).max()),
        euler_eta=ec["eta"],
    )
    (RES / "A1_slopes.json").write_text(json.dumps(out, indent=2))
    print(json.dumps({k: out[k] for k in ("handoff_t", "sup_u", "min_u", "sup_abs_v", "sup_abs_v_after_t1", "conservation_err_g1", "eps_sensitivity_max_abs", "wall_s", "nfev")}, indent=1))
    print({k: round(v["slope"], 4) for k, v in out["slopes"].items()})


def run_full(tag, X0, N, K, eta, B, steps, chunks, seed, relu0, resume=True):
    """Full-matrix sampled GD with resumable checkpoints."""
    c = M.Canonical(N, K)
    ck = RES / f"{tag}_state.npz"
    chk_steps = np.unique(np.round(np.r_[np.array([eta]), checkpoints(steps * eta, lo=eta)] / eta).astype(np.int64))
    chk_steps = chk_steps[(chk_steps >= 1) & (chk_steps <= steps)]
    if resume and ck.exists():
        s = np.load(ck)
        X, done = s["X"].copy(), int(s["done"])
        Xs, losses, walls = list(s["Xs"]), list(s["losses"]), list(s["walls"])
        recorded = list(s["steps"])
    else:
        X = X0.copy(); done = 0
        Xs, losses, walls, recorded = [X0.copy()], [np.nan], [0.0], [0]
    t_base = walls[-1]; t0 = time.time()
    for n in chk_steps:
        if n <= done:
            continue
        segment_seed = (seed * 1000003 + done) % (2 ** 31 - 1)
        loss = kn.gd_segment(X, int(n - done), eta, B, segment_seed, chunks, *c.args, relu0, 0.0)
        done = int(n)
        Xs.append(X.copy()); losses.append(loss); recorded.append(done); walls.append(t_base + time.time() - t0)
        tmp = RES / f"{tag}_state.tmp.npz"
        np.savez(tmp, X=X, done=done, Xs=np.array(Xs), losses=np.array(losses),
                 walls=np.array(walls), steps=np.array(recorded), eta=eta, B=B, N=N, K=K, relu0=relu0, seed=seed)
        os.replace(tmp, ck)
        print(f"[{tag}] step {done} t={done * eta:g} loss={loss:.4f} wall={walls[-1]:.0f}s dist={M.subspace_distance(X).round(5)}", flush=True)
    return np.array(recorded), np.array(Xs), np.array(losses)


def exp_A_full(cfg):
    a = cfg["A"]; f = a["full"]; N, K = a["N"], a["K"]
    numba.set_num_threads(cfg["threads"])
    X0 = M.theta_to_X(M.init_theta(N), N)
    steps, Xs, losses = run_full("A2_full", X0, N, K, f["eta"], f["B"], f["steps"], f["chunks"], cfg["seed"], 1)
    analyze_A_full(cfg, steps, Xs, losses)


def analyze_A_full(cfg, steps, Xs, losses):
    a = cfg["A"]; f = a["full"]; N = a["N"]
    ts = steps * f["eta"]
    th = np.array([M.X_to_theta(X) for X in Xs])
    dist = np.array([M.subspace_distance(X) for X in Xs])
    np.savez(RES / "A2_full.npz", t=ts, theta=th, dist=dist, loss=losses, names=M.NAMES)
    ref = np.load(RES / "A1_reduced.npz")
    m = ts >= f["eta"]
    A1 = np.array([np.interp(np.log(ts[m]), np.log(ref["t"][1:]), ref["theta"][1:, k]) for k in range(8)]).T
    d = derived(th)
    hor = ts[-1]
    out = dict(steps=int(steps[-1]), horizon_t=float(hor), slopes=slopes(ts, th, a["fit_from"], hor),
               handoff_t=handoff(ts, th), sup_u=float(d["u"].max()), min_u=float(d["u"].min()),
               sup_abs_v=float(np.abs(d["v"]).max()),
               subspace_distance_sup={k: float(dist[1:, i].max()) for i, k in enumerate(("A1", "A2", "B1", "B2"))},
               subspace_distance_sup_after_t1={k: float(dist[ts >= 1, i].max()) for i, k in enumerate(("A1", "A2", "B1", "B2"))},
               max_abs_diff_to_A1={n: float(np.abs(th[m, i] - A1[:, i]).max()) for i, n in enumerate(M.NAMES)},
               final={n: float(th[-1, i]) for i, n in enumerate(M.NAMES)})
    (RES / "A2_slopes.json").write_text(json.dumps(out, indent=2))
    print(json.dumps(out["max_abs_diff_to_A1"]), out["subspace_distance_sup"])
    # plan's single file, merged
    merged = dict(A1=json.loads((RES / "A1_slopes.json").read_text()), A2=out)
    (RES / "A_slopes.json").write_text(json.dumps(merged, indent=2))


def gen_metrics(ts_set, loss, correct):
    out = {}
    for c in dfs.CATEGORIES:
        m = ts_set["category"] == c
        out[f"mean_{c}"] = loss[m].mean() if m.any() else np.nan
        out[f"max_{c}"] = loss[m].max() if m.any() else np.nan
    out["L_gen"] = loss.max()
    out["accuracy"] = correct.mean()
    return out


def exp_B(cfg, part):
    a = cfg["A"]; N, K = a["N"], a["K"]
    numba.set_num_threads(cfg["threads"])
    ts_set = ev.load_test_set(N, K, cfg["test_set_seed"], CACHE)
    print("test set:", ts_set["n_pref"], {c: int((ts_set["category"] == c).sum()) for c in dfs.CATEGORIES},
          "kinds", {k: int((ts_set["kind"] == k).sum()) for k in np.unique(ts_set["kind"])})
    res = {}
    if part in ("reduced", "all"):
        r = np.load(RES / "A1_reduced.npz")
        tg = np.union1d(np.geomspace(1, 1e9, 91), checkpoints(1e9))
        th = np.array([np.interp(np.log(tg), np.log(r["t"][1:]), r["theta"][1:, k]) for k in range(8)]).T
        res["A1"] = _gen_run(ts_set, tg, [M.theta_to_X(x, N) for x in th], th, cfg["B"]["fit_window"], "B_gen_reduced", N, K)
    if part in ("full", "all"):
        r = np.load(RES / "A2_full_state.npz")
        s = r["steps"] * float(r["eta"]); m = s >= 1
        res["A2"] = _gen_run(ts_set, s[m], list(r["Xs"][m]), np.array([M.X_to_theta(x) for x in r["Xs"][m]]), cfg["B"]["a2_fit_window"], "B_gen_full", N, K)
    path = RES / "B_exponents.json"
    old = json.loads(path.read_text()) if path.exists() else {}
    old.update(res)
    path.write_text(json.dumps(old, indent=2))
    for k, v in res.items():
        print(k, json.dumps({q: v[q] for q in ("exponents", "acc_one_from_t", "acc_at_t_ge_100", "argmax_final")}, indent=1, default=str)[:1800])


def _gen_run(ts_set, tg, Xs, th, window, tag, N, K):
    rows = []; acc = []
    for X in Xs:
        Z, loss, correct = ev.evaluate(ts_set, X)
        rows.append(gen_metrics(ts_set, loss, correct))
    keys = list(rows[0])
    arr = {k: np.array([r[k] for r in rows]) for k in keys}
    np.savez(RES / f"{tag}.npz", t=tg, **{k.replace('-', '_'): v for k, v in arr.items()})
    m = (tg >= window[0]) & (tg <= window[1] * (1 + 1e-9))
    exps = {k: ols(np.log(tg[m]), np.log(arr[k][m])) for k in keys if k != "accuracy" and np.all(arr[k][m] > 0)}
    # identity of the sup prefix at the final time
    Z, loss, correct = ev.evaluate(ts_set, Xs[-1])
    p = int(np.argmax(loss))
    rec = ts_set["records"][ts_set["gid"][p]]
    # logit of the parent = root vs g1-d1+d2 (differs only by forward-head term if n_t->root exists)
    g1, d1, d2 = th[-1, IDX["g1"]], th[-1, IDX["d1"]], th[-1, IDX["d2"]]
    br = np.where(ts_set["category"] == dfs.BT_ROOT)[0]
    pred = g1 - d1 + d2
    dec = Z[br, ts_set["parent"][br]] - pred
    has_edge = np.array([(ts_set["q"][i], ts_set["parent"][i]) in set(map(tuple, ts_set["records"][ts_set["gid"][i]][1])) for i in br])
    acc1 = np.where(arr["accuracy"] < 1)[0]
    return dict(
        fit_window=window, exponents=exps,
        n_prefixes=int(ts_set["n_pref"]), counts={c: int((ts_set["category"] == c).sum()) for c in dfs.CATEGORIES},
        argmax_final=dict(t=float(tg[-1]), loss=float(loss[p]), category=str(ts_set["category"][p]), kind=str(ts_set["kind"][p]),
                          prefix=[int(x) for x in ts_set["prefixes"][p]], root=int(rec[2]), target=int(rec[3])),
        acc_one_from_t=float(tg[acc1[-1] + 1]) if len(acc1) and acc1[-1] + 1 < len(tg) else (float(tg[0]) if not len(acc1) else None),
        acc_at_t_ge_100=float(arr["accuracy"][tg >= 100].min()),
        decomposition=dict(no_edge_max_abs=float(np.abs(dec[~has_edge]).max()) if (~has_edge).any() else None,
                           n_no_edge=int((~has_edge).sum()), n_edge=int(has_edge.sum()),
                           edge_residual_min=float(dec[has_edge].min()) if has_edge.any() else None,
                           edge_residual_max=float(dec[has_edge].max()) if has_edge.any() else None))


def exp_B_diagnostics(cfg):
    """Why L_gen/accuracy differ from the plan's expectation: split forward steps by whether n_t -> parent
    is an edge (a "back-edge"), use later fit windows, and extend the reduced flow far past t=1e9."""
    a = cfg["A"]; N, K = a["N"], a["K"]; o = a["ode"]
    numba.set_num_threads(4)
    S = ev.load_test_set(N, K, cfg["test_set_seed"], CACHE)
    stacks = [dfs.stack_of(p) for p in S["prefixes"]]
    edge_sets = [set(map(tuple, r[1])) for r in S["records"]]
    back = np.array([len(st) > 1 and (st[-1], st[-2]) in edge_sets[g] for st, g in zip(stacks, S["gid"])])
    fw = S["category"] == dfs.FORWARD
    groups = {"forward_backedge": fw & back, "forward_no_backedge": fw & ~back,
              "backtrack_nonroot": S["category"] == dfs.BT_NONROOT, "backtrack_root": S["category"] == dfs.BT_ROOT}
    c = M.Canonical(N, K)
    H = float(cfg["B"]["long_horizon"])
    # the stiff solver cannot resolve eps=1e-6 at these horizons; eps only moves b2 by ~eps (A1_slopes.json)
    ts, th, _ = integrate_reduced(c, M.init_theta(N), H, o["method"], cfg["B"]["long_horizon_rtol"], o["atol"], cfg["B"]["long_horizon_eps"])
    tg = np.geomspace(1, H, 121)
    rows = {f"{k}_{g}": [] for g in groups for k in ("mean", "max", "acc")}
    rows["L_gen"] = []; rows["accuracy"] = []; rows["argmax_category"] = []; rows["argmax_backedge"] = []
    for t in tg:
        x = np.array([np.interp(np.log(t), np.log(ts[1:]), th[1:, k]) for k in range(8)])
        _, loss, ok = ev.evaluate(S, M.theta_to_X(x, N))
        for g, m in groups.items():
            rows[f"mean_{g}"].append(loss[m].mean()); rows[f"max_{g}"].append(loss[m].max()); rows[f"acc_{g}"].append(ok[m].mean())
        rows["L_gen"].append(loss.max()); rows["accuracy"].append(ok.mean())
        p = int(np.argmax(loss)); rows["argmax_category"].append(str(S["category"][p])); rows["argmax_backedge"].append(bool(back[p]))
    arr = {k: np.array(v) for k, v in rows.items()}
    np.savez(RES / "B_diagnostics.npz", t=tg, **arr)
    def fit(k, lo, hi):
        m = (tg >= lo) & (tg <= hi)
        return round(ols(np.log(tg[m]), np.log(arr[k][m]))["slope"], 4)
    keys = [f"{k}_{g}" for g in groups for k in ("mean", "max")] + ["L_gen"]
    out = dict(
        counts={g: int(m.sum()) for g, m in groups.items()},
        exponents={f"[{lo:g},{hi:g}]": {k: fit(k, lo, hi) for k in keys} for lo, hi in ((1e3, 1e9), (1e6, 1e9), (1e9, 1e12), (1e12, 1e16))},
        accuracy_one_from={g: (float(tg[np.where(arr[f"acc_{g}"] < 1)[0][-1] + 1]) if (arr[f"acc_{g}"] < 1).any() else 1.0) for g in groups},
        accuracy_at_t100={g: float(np.interp(np.log(100), np.log(tg), arr[f"acc_{g}"])) for g in groups},
        L_gen_category_at={f"{t:g}": (rows["argmax_category"][int(np.argmin(abs(np.log(tg) - np.log(t))))], rows["argmax_backedge"][int(np.argmin(abs(np.log(tg) - np.log(t))))]) for t in (1e3, 1e6, 1e9, 1e12, 1e16)},
    )
    # extrapolated crossover of the two largest envelopes, from the last decades (an estimate, not observed)
    m = tg >= 1e12
    fa = ols(np.log(tg[m]), np.log(arr["max_forward_backedge"][m])); fb = ols(np.log(tg[m]), np.log(arr["max_backtrack_root"][m]))
    out["extrapolated_crossover_t_backedge_vs_root"] = float(np.exp((fb["intercept"] - fa["intercept"]) / (fa["slope"] - fb["slope"])))
    switch = [float(tg[i]) for i in range(1, len(tg)) if rows["argmax_category"][i] != rows["argmax_category"][i - 1]]
    out["L_gen_category_switch_times"] = switch
    (RES / "B_diagnostics.json").write_text(json.dumps(out, indent=2))
    print(json.dumps(out, indent=1))


def exp_C(cfg):
    numba.set_num_threads(cfg["threads"])
    o = cfg["A"]["ode"]; lo, hi = cfg["C"]["fit_window"]
    rows = []; curves = {}
    for N, K in cfg["C"]["cases"]:
        c = M.Canonical(N, K)
        ts, th, _ = integrate_reduced(c, M.init_theta(N), o["horizon"], o["method"], o["rtol"], o["atol"], o["eps"])
        np.savez(RES / f"C_traj_N{N}.npz", t=ts, theta=th)
        S = ev.load_test_set(N, K, cfg["test_set_seed"], CACHE, only_category=dfs.BT_ROOT)
        tg = np.geomspace(lo, hi, 51)
        means = []
        for t in tg:
            x = np.array([np.interp(np.log(t), np.log(ts[1:]), th[1:, k]) for k in range(8)])
            _, loss, _ = ev.evaluate(S, M.theta_to_X(x, N))
            means.append(loss.mean())
        means = np.array(means)
        f = ols(np.log(tg), np.log(means))
        rows.append(dict(N=N, K=K, n_prefixes=S["n_pref"], fitted=f["slope"], se=f["se"], r2=f["r2"], theory=-(N - 1) / N, diff=f["slope"] + (N - 1) / N))
        curves[f"t_{N}"] = tg; curves[f"mean_{N}"] = means
        print(rows[-1], flush=True)
    np.savez(RES / "C_curves.npz", **curves)
    with open(RES / "C_exponents.csv", "w") as fh:
        fh.write(",".join(rows[0]) + "\n")
        for r in rows:
            fh.write(",".join(str(v) for v in r.values()) + "\n")


def region_entry(ts, th):
    ok = (th[:, IDX["b2"]] < th[:, IDX["b1"]]) & (th[:, IDX["g1"]] > th[:, IDX["d1"]])
    if not ok.any():
        return None, False
    last_out = np.where(~ok)[0]
    first = float(ts[np.argmax(ok)])
    stays = float(ts[last_out[-1] + 1]) if len(last_out) and last_out[-1] + 1 < len(ts) else (first if not len(last_out) else None)
    return first, stays


def exp_D(cfg, part):
    a = cfg["A"]; D = cfg["D"]; N, K = a["N"], a["K"]
    c = M.Canonical(N, K)
    out = {}
    path = RES / "D_ablation.json"
    if path.exists():
        out = json.loads(path.read_text())
    if part in ("reduced", "all"):
        eta = D["eta"]; chk = checkpoints(D["reduced_horizon"], lo=eta)
        C = kn.scalar_coefficients(N, *c.args[:6]); q, y = c.pk["q"], c.pk["y"]
        # D1-D3: closed-form heads, no round-off on the kink. *_roundoff: heads summed term by term from the
        # matrix entries (as a matrix implementation would), so exact zeros may become +-1e-19.
        for tag, kind, relu0, exact in (("D1", "new", 1, True), ("D2", "constant", 1, True), ("D3", "constant", 0, True),
                                        ("D2_roundoff", "constant", 1, False), ("D3_roundoff", "constant", 0, False)):
            x = M.init_theta(N, kind); done = 0; th = [x.copy()]; ts = [0.0]
            for t in chk:
                n = int(round(t / eta))
                if n > done:
                    x = kn.euler_coef(x, n - done, eta, C, q, y, relu0, 0.0) if exact else c.euler(x, n - done, eta, relu0)
                    done = n
                    th.append(x.copy()); ts.append(n * eta)
            ts = np.array(ts); th = np.array(th)
            np.savez(RES / f"{tag}_reduced.npz", t=ts, theta=th)
            out[tag] = _d_row(ts, th, kind, relu0, "reduced GD")
            print(tag, json.dumps(out[tag]), flush=True)
    if part in ("full", "all"):
        f = D["full"]; numba.set_num_threads(f["threads"])
        import sys
        seeds = f["seeds"]
        for sd in seeds:
            tag = f"D4_seed{sd}"
            X0 = M.theta_to_X(M.init_theta(N, "constant"), N)
            steps, Xs, _ = run_full(tag, X0, N, K, D["eta"], f["B"], f["steps"], f["chunks"], 1000 + sd, 0)
            ts = steps * D["eta"]; th = np.array([M.X_to_theta(X) for X in Xs])
            np.savez(RES / f"{tag}.npz", t=ts, theta=th, dist=np.array([M.subspace_distance(X) for X in Xs]))
            out[tag] = _d_row(ts, th, "constant", 0, "full-matrix sampled GD")
            print(tag, json.dumps(out[tag]), flush=True)
    path.write_text(json.dumps(out, indent=2))


def _d_row(ts, th, kind, relu0, label):
    first, stays = region_entry(ts, th)
    gap = th[:, IDX["b2"]] - th[:, IDX["b1"]]
    gd = th[:, IDX["g1"]] - th[:, IDX["d1"]]
    return dict(init=kind, relu0=relu0, model=label, first_in_region_t=first, stays_in_region_from_t=stays,
                max_b2_minus_b1=float(gap.max()), min_b1=float(th[:, IDX["b1"]].min()),
                max_abs_g1_minus_d1=float(np.abs(gd).max()), final_t=float(ts[-1]),
                final={n: float(th[-1, i]) for i, n in enumerate(M.NAMES)},
                final_loss_note=None)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--exp", required=True, choices=list("ABCD") + ["Bdiag", "plots", "summary"])
    ap.add_argument("--part", default="all", choices=["reduced", "full", "all"])
    ap.add_argument("--config", default=str(HERE / "config.yaml"))
    args = ap.parse_args()
    cfg = yaml.safe_load(open(args.config))
    if args.exp == "A":
        if args.part in ("reduced", "all"):
            exp_A_reduced(cfg)
        if args.part in ("full", "all"):
            exp_A_full(cfg)
    elif args.exp == "B":
        exp_B(cfg, args.part)
    elif args.exp == "Bdiag":
        exp_B_diagnostics(cfg)
    elif args.exp == "C":
        exp_C(cfg)
    elif args.exp == "D":
        exp_D(cfg, args.part)
    elif args.exp == "plots":
        import plots; plots.main(cfg)
    elif args.exp == "summary":
        import summarize; summarize.main(cfg)
