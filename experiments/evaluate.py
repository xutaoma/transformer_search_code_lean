"""Test-set packing and evaluation (plan sec. 1.7)."""
import numpy as np, pickle, pathlib
import dfs, kernels as kn


def pack_test_set(N, graphs, rng, extra=(), only_category=None):
    """graphs: (kind, edges, root, target). extra: (kind, edges, root, target, [prefixes])."""
    pptr, pmat, pv, pi, pval = [0], [], [], [], []
    gptr, gv, gi = [0], [], []
    gid, q, notC, cat, parent, kind_of, adm, prefixes = [], [], [], [], [], [], [], []
    records = [(*g, None) for g in graphs] + list(extra)
    for g_idx, (kind, edges, root, target, given) in enumerate(records):
        for s, t in edges:
            gv.append(t); gi.append(s)
        gptr.append(len(gv))
        out = dfs.out_map(edges)
        prefs = given if given is not None else dfs.prefixes_of_graph(edges, root, target, rng)
        for pf in prefs:
            C, c, par = dfs.dfs_step(out, target, pf)
            if only_category is not None and c != only_category:
                continue
            for (m, v, i), x in kn.sparse_from_prefix((), pf).items():
                pmat.append(m); pv.append(v); pi.append(i); pval.append(x)
            pptr.append(len(pmat))
            gid.append(g_idx); q.append(pf[-1]); cat.append(c)
            parent.append(-1 if par is None else par)
            mask = (1 << N) - 1
            for v in C:
                mask &= ~(1 << v)
            notC.append(mask); kind_of.append(kind); adm.append(C); prefixes.append(pf)
    return dict(N=N, n_pref=len(q), pptr=np.array(pptr, np.int64), pmat=np.array(pmat, np.int64),
                pv=np.array(pv, np.int64), pi=np.array(pi, np.int64), pval=np.array(pval, np.float64),
                gid=np.array(gid, np.int64), gptr=np.array(gptr, np.int64), gv=np.array(gv, np.int64),
                gi=np.array(gi, np.int64), q=np.array(q, np.int64), notC=np.array(notC, np.uint64),
                category=np.array(cat), parent=np.array(parent, np.int64), kind=np.array(kind_of),
                admissible=adm, prefixes=prefixes, records=[r[:4] for r in records])


def evaluate(ts, X):
    return kn.eval_prefixes(X, ts["n_pref"], ts["pptr"], ts["pmat"], ts["pv"], ts["pi"], ts["pval"],
                            ts["gid"], ts["gptr"], ts["gv"], ts["gi"], ts["q"], ts["notC"])


def standard_extras(N, K):
    """Plan: the paper's own full canonical trace and the single-edge graph."""
    c = dfs.canonical(N, K)
    out = dfs.out_map(c["edges"])
    tr = c["full"]
    can = [tr[:k] for k in range(1, len(tr) + 1) if dfs.dfs_step(out, c["target"], tr[:k]) is not None]
    root, a, tgt = 0, 1, 2
    single = [(0,), (0, 1)]
    return [("canonical", c["edges"], c["root"], c["target"], can),
            ("single_edge", [(root, a)], root, tgt, single)]


def load_test_set(N, K, seed, cache_dir, only_category=None):
    tag = only_category or "all"
    path = pathlib.Path(cache_dir) / f"testset_N{N}_K{K}_seed{seed}_{tag}.pkl"
    if path.exists():
        return pickle.loads(path.read_bytes())
    graphs, rng = dfs.generate_test_graphs(N, K, seed)
    ts = pack_test_set(N, graphs, rng, standard_extras(N, K), only_category)
    path.write_bytes(pickle.dumps(ts))
    return ts
