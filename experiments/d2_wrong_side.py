"""D2 (constant init, R'(0)=1) across (N,K): does the flow exit on the wrong side (b2>b1, b1<0)?
Uses closed-form heads (no round-off on the kink). Writes results/D2_wrong_side.{json,npz}."""
import json, pathlib, sys
import numpy as np
import model as M, kernels as kn
from run import checkpoints, IDX
RES = pathlib.Path(__file__).resolve().parent / "results"


def run(N, K, kind, relu0, eta, horizon, fine_until=100.0):
    c = M.Canonical(N, K)
    C = kn.scalar_coefficients(N, *c.args[:6]); q, y = c.pk["q"], c.pk["y"]
    x = M.init_theta(N, kind); ts = [0.0]; th = [x.copy()]; done = 0
    n_fine = int(round(fine_until / eta))
    step = max(1, n_fine // 4000)                       # record finely through the transient
    targets = list(range(step, n_fine + 1, step)) + [int(round(t / eta)) for t in checkpoints(horizon, lo=eta) if t > fine_until]
    for n in targets:
        x = kn.euler_coef(x, n - done, eta, C, q, y, relu0, 0.0); done = n
        ts.append(n * eta); th.append(x.copy())
    return np.array(ts), np.array(th)


def stats(N, K, ts, th):
    gap, b1, gd = th[:, IDX["b2"]] - th[:, IDX["b1"]], th[:, IDX["b1"]], th[:, IDX["g1"]] - th[:, IDX["d1"]]
    in_region = (gap < 0) & (gd > 0)
    out = np.where(~in_region)[0]
    last = out[-1] if len(out) else -1
    wrong = gap > 0
    neg = b1 < 0
    return dict(N=N, K=K, threshold=(K + 2) ** 2 / 2, N_gt_threshold=bool(N > (K + 2) ** 2 / 2),
                wrong_side=bool(wrong.any() and neg.any()), max_b2_minus_b1=float(gap.max()), min_b1=float(b1.min()),
                b2_gt_b1_from=float(ts[wrong][0]) if wrong.any() else None, b2_gt_b1_until=float(ts[wrong][-1]) if wrong.any() else None,
                b1_neg_from=float(ts[neg][0]) if neg.any() else None, b1_neg_until=float(ts[neg][-1]) if neg.any() else None,
                stays_in_region_from=float(ts[last + 1]) if last + 1 < len(ts) else None, final_t=float(ts[-1]),
                final={n: float(th[-1, i]) for n, i in IDX.items()})


main, arrays = {}, {}
for N, K in [(16, 2), (40, 3), (16, 8)]:
    for tag, kind, relu0, eta in [("D2", "constant", 1, .05), ("D2_eta005", "constant", 1, .005), ("D1", "new", 1, .05), ("D3", "constant", 0, .05)]:
        ts, th = run(N, K, kind, relu0, eta, 5e5 if eta == .05 else 5e3)
        key = f"{tag}_N{N}_K{K}"; main[key] = stats(N, K, ts, th); arrays[key + "_t"] = ts; arrays[key + "_theta"] = th
        s = main[key]
        print(key, {k: s[k] for k in ("wrong_side", "max_b2_minus_b1", "min_b1", "b2_gt_b1_from", "b2_gt_b1_until", "b1_neg_from", "b1_neg_until", "stays_in_region_from")}, flush=True)
np.savez(RES / "D2_wrong_side.npz", **arrays)
path = RES / "D2_wrong_side.json"
scan = json.loads(path.read_text())["scan"] if path.exists() else []
for N in () if scan else (8, 10, 12, 16, 20, 24, 32, 40, 48, 64):
    for K in (2, 3, 4, 5, 6, 8, 10):
        if K > N - 5:
            continue
        ts, th = run(N, K, "constant", 1, .05, 5e3)
        s = stats(N, K, ts, th); scan.append({k: s[k] for k in ("N", "K", "threshold", "N_gt_threshold", "wrong_side", "max_b2_minus_b1", "min_b1")})
(RES / "D2_wrong_side.json").write_text(json.dumps(dict(main=main, scan=scan), indent=1))
Ks = sorted({r["K"] for r in scan})
print("scan: W = wrong-side exit, . = none, blank = K>N-5; * = N > (K+2)^2/2")
print("N\\K " + " ".join(f"{k:>3}" for k in Ks))
for N in sorted({r["N"] for r in scan}):
    print(f"{N:>3} " + " ".join(next((f"{'W' if r['wrong_side'] else '.'}{'*' if r['N_gt_threshold'] else ' '} ".rjust(3) for r in scan if r["N"] == N and r["K"] == k), "   ") for k in Ks))
agree = sum(r["wrong_side"] == r["N_gt_threshold"] for r in scan); print("rule agrees on", agree, "of", len(scan))
print("disagreements:", [(r["N"], r["K"], r["wrong_side"], r["threshold"]) for r in scan if r["wrong_side"] != r["N_gt_threshold"]])
