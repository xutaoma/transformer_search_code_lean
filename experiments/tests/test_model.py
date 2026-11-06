import numpy as np, torch, pytest, itertools
import dfs, kernels as kn, model as M
import reference as ref


def random_prefixes(N, seed, n=30):
    rng = np.random.default_rng(seed)
    for _ in range(n):
        kind = rng.integers(3)
        if kind == 0:
            edges, r, g = dfs._er(N, rng, rng.choice([.1, .2, .4]))
        elif kind == 1:
            edges, r, g = dfs._tree(N, rng)
        else:
            edges, r, g = dfs._fan(N, rng)
        prefs = dfs.prefixes_of_graph(edges, r, g, rng, 10)
        for p in prefs[:: max(1, len(prefs) // 8)]:
            yield edges, r, g, p


def test_sparse_equals_block_products():
    N = 9
    for edges, r, g, p in random_prefixes(N, 0):
        a, b, c, d = dfs.build_blocks(N, edges, g, p)
        dense = [(d - a).T @ a, (d - a).T @ c, (b - a).T @ a, (b - a).T @ b]
        sp = np.zeros((4, N, N))
        for (m, v, i), x in kn.sparse_from_prefix(edges, p).items():
            sp[m, v, i] = x
        assert np.array_equal(np.array(dense), sp)


def test_closed_form_tables():
    """Pre-ReLU heads against plan sec. 3's tables, generic scalars."""
    N = 10
    th = np.random.default_rng(1).normal(size=8)
    a1, b1, a2, b2, g1, d1, g2, d2 = th
    Xs = ref.from_theta(torch.as_tensor(th), N)
    checked = 0
    for edges, r, g, p in random_prefixes(N, 2):
        h1, h2 = ref.heads(Xs, dfs.build_blocks(N, edges, g, p), p[-1])
        h1, h2 = h1.numpy(), h2.numpy()
        cur = p[-1]
        out = dfs.out_map(edges)
        indeg = np.zeros(N)
        for _, t in edges:
            indeg[t] += 1
        m = np.array([p.count(v) for v in range(N)])
        visited = set(p)
        stack = dfs.stack_of(p)
        parent = stack[-2] if len(stack) > 1 else None
        # children entered from cur and returned from
        returned = {p[k + 1] for k in range(len(p) - 1) if p[k] == cur and p[k + 1] != parent}
        for v in range(N):
            if v == cur:
                continue
            # A self-loop on cur is the only in-edge that uses the diagonal for a non-child target.
            if v in out.get(cur, ()):
                f = a2 - b2 + b2 * indeg[v] - (0 if v not in visited else b1 * m[v])
            else:
                f = b2 * indeg[v] - b1 * m[v]
            assert h1[v] == pytest.approx(f, abs=1e-10)
            if v == parent:
                e = g1 - d1 + (d2 if parent == r else 0)
            elif v in returned:
                e = g1 - g2 - d1 + d2
            elif v == r:
                e = d2
            else:
                e = 0.0
            assert h2[v] == pytest.approx(e, abs=1e-10), (edges, p, v)
            checked += 1
    assert checked > 500


@pytest.mark.parametrize("relu0", [0, 1])
def test_kernel_gradient_equals_autograd_full_matrix(relu0):
    N, K = 9, 3
    c = M.Canonical(N, K)
    rng = np.random.default_rng(3)
    X = rng.normal(size=(4, N, N)) * 0.7
    perm = rng.permutation(N).astype(np.int64)
    loss, G = kn.grad_single(X, perm, *c.args, relu0, 0.0)
    # relabelled instance
    inst = dict(c.inst)
    inst["edges"] = [(int(perm[s]), int(perm[t])) for s, t in inst["edges"]]
    inst["target"] = int(perm[inst["target"]])
    inst["steps"] = [(tuple(int(perm[v]) for v in pf), int(perm[y])) for pf, y in inst["steps"]]
    Xs = [torch.tensor(X[m], requires_grad=True) for m in range(4)]
    l = ref.canonical_loss(Xs, inst, relu0)
    l.backward()
    assert loss == pytest.approx(l.item(), rel=1e-12)
    for m in range(4):
        np.testing.assert_allclose(G[m], Xs[m].grad.numpy(), atol=1e-12)


def generic_point(N, seed=5):
    return np.random.default_rng(seed).normal(0.8, 0.5, size=8)


def test_scalar_gradient_vs_finite_difference():
    N, K = 12, 4
    c = M.Canonical(N, K)
    th = generic_point(N)
    _, g = c.grad_theta(th)
    th_t = torch.tensor(th, requires_grad=True)
    ref.canonical_loss(ref.from_theta(th_t, N), c.inst).backward()
    np.testing.assert_allclose(g, th_t.grad.numpy(), atol=1e-12)
    h = 1e-6
    for k in range(8):
        e = np.zeros(8); e[k] = h
        fd = (c.grad_theta(th + e)[0] - c.grad_theta(th - e)[0]) / (2 * h)
        assert abs(fd - g[k]) <= 1e-6 * max(abs(g[k]), 1e-3), k


def test_gradient_identities():
    N, K = 16, 8
    c = M.Canonical(N, K)
    for seed in range(5):
        _, g = c.grad_theta(generic_point(N, seed))
        assert g[0] == 0.0                      # d/da1
        assert g[5] == pytest.approx(-g[4], abs=1e-12)  # d/dd1 = -d/dg1, up to summation round-off


@pytest.mark.parametrize("relu0", [0, 1])
def test_all_permutation_average_stays_on_subspace(relu0):
    """Exact average over S_7: the gradient is on the subspace and equals the normalised scalar flow."""
    N, K = 7, 2
    c = M.Canonical(N, K)
    th = generic_point(N)
    X = M.theta_to_X(th, N)
    G = np.zeros_like(X)
    perms = list(itertools.permutations(range(N)))
    for p in perms:
        G += kn.grad_single(X, np.array(p, dtype=np.int64), *c.args, relu0, 0.0)[1]
    G /= len(perms)
    gth = M.X_to_theta(G)
    np.testing.assert_allclose(G, M.theta_to_X(gth, N), atol=1e-12)
    np.testing.assert_allclose(-gth, c.flow(th, relu0), atol=1e-12)


def test_gd_segment_invariant_to_thread_count_and_consistent():
    import numba
    N, K = 9, 3
    c = M.Canonical(N, K)
    X0 = M.theta_to_X(M.init_theta(N), N)
    res = []
    for nt in (1, 4):
        numba.set_num_threads(nt)
        X = X0.copy()
        kn.gd_segment(X, 50, 0.05, 16, 12345, 8, *c.args, 1, 0.0)
        res.append(X)
    assert np.array_equal(res[0], res[1])


def test_eval_loss_matches_softmax():
    N = 10
    rng = np.random.default_rng(7)
    edges, r, g = dfs._tree(N, rng)
    import evaluate as ev
    ts = ev.pack_test_set(N, [("tree", edges, r, g)], rng)
    X = rng.normal(size=(4, N, N))
    Z, loss, correct = ev.evaluate(ts, X)
    for p in range(ts["n_pref"]):
        pf = ts["prefixes"][p]
        Xs = [torch.tensor(X[m]) for m in range(4)]
        z = ref.logits(Xs, dfs.build_blocks(N, edges, g, pf), pf[-1], relu0=1)
        np.testing.assert_allclose(Z[p], z.numpy(), atol=1e-12)
        C = list(ts["admissible"][p])
        logp = torch.log_softmax(z, 0)[C]
        assert loss[p] == pytest.approx(-torch.logsumexp(logp, 0).item(), rel=1e-9, abs=1e-12)


def test_permutation_sampling_uniform():
    from scipy.stats import chisquare
    kn.seed_rng(11)
    perms = np.zeros((48000, 4), dtype=np.int64)
    kn.draw_perms(perms)
    codes = perms @ np.array([64, 16, 4, 1])
    _, counts = np.unique(codes, return_counts=True)
    assert len(counts) == 24
    assert chisquare(counts).pvalue > 1e-3


def test_sampled_gd_tracks_mean_flow_short_run():
    """Averaged over many permutations, one GD step matches the reduced Euler step."""
    N, K = 8, 3
    c = M.Canonical(N, K)
    th = M.init_theta(N)
    X = M.theta_to_X(th, N)
    kn.gd_segment(X, 1, 1e-3, 20000, 5, 8, *c.args, 1, 0.0)
    np.testing.assert_allclose(M.X_to_theta(X), c.euler(th, 1, 1e-3), atol=2e-5)


@pytest.mark.parametrize("relu0", [0, 1])
def test_coefficient_kernel_equals_matrix_kernel(relu0):
    N, K = 16, 8
    c = M.Canonical(N, K)
    C = kn.scalar_coefficients(N, *c.args[:6])
    for seed in range(5):
        th = generic_point(N, seed)
        l1, g1 = kn.coef_grad(th, C, c.pk["q"], c.pk["y"], relu0, 0.0)
        l2, g2 = c.grad_theta(th, relu0)
        assert l1 == pytest.approx(l2, rel=1e-10)
        np.testing.assert_allclose(g1, g2, atol=1e-11)
