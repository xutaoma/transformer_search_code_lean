"""Diagnostic for A2's early departure from the subspace: vary batch size and step size up to t=30.
Not part of the acceptance runs. Writes results/A2_early_diagnostic.json."""
import json, pathlib
import numpy as np, numba
import model as M, kernels as kn
RES = pathlib.Path(__file__).resolve().parent / "results"
numba.set_num_threads(16)
N, K = 16, 8
c = M.Canonical(N, K)
r = np.load(RES / "A1_reduced.npz")
marks = [0.5, 1, 2, 5, 10, 15, 20, 30]
out = []
for B, eta, seed in [(128, .05, 1), (128, .05, 2), (512, .05, 1), (2048, .05, 1), (8192, .05, 1), (32768, .05, 1), (128, .005, 1), (2048, .005, 1)]:
    X = M.theta_to_X(M.init_theta(N), N); done = 0; rows = {}
    for t in marks:
        n = int(round(t / eta))
        kn.gd_segment(X, n - done, eta, B, seed * 1000 + done, 16, *c.args, 1, 0.0); done = n
        th = M.X_to_theta(X)
        A1 = np.array([np.interp(np.log(t), np.log(r["t"][1:]), r["theta"][1:, k]) for k in range(8)])
        rows[t] = dict(dist_max=float(M.subspace_distance(X).max()), dist=M.subspace_distance(X).round(4).tolist(), max_diff_A1=float(np.abs(th - A1).max()))
    out.append(dict(B=B, eta=eta, seed=seed, rows=rows))
    print(f"B={B:<6} eta={eta:<6} seed={seed} " + " ".join(f"t={t}: d={rows[t]['dist_max']:.3f} e={rows[t]['max_diff_A1']:.3f} |" for t in marks), flush=True)
(RES / "A2_early_diagnostic.json").write_text(json.dumps(out, indent=1))
