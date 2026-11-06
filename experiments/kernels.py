"""Compiled forward/backward kernels. The model is linear in the four matrices before the ReLU:
   head1[v] = sum_i P1[v,i] A1[i,q] + P2[v,i] A2[i,q]      P1=(D-A)^T A, P2=(D-A)^T C
   head2[v] = sum_i P3[v,i] B1[i,q] + P4[v,i] B2[i,q]      P3=(B-A)^T A, P4=(B-A)^T B
so a prefix is a sparse list (mat, v, i, val). tests/test_model.py checks this and the hand-written
gradient against a literal autograd implementation of the plan's formula."""
import numpy as np
from numba import njit, prange


def sparse_from_prefix(edges, prefix):
    """Sparse P-tensors of one prefix (mat: 0=A1, 1=A2, 2=B1, 3=B2). Equal to the blocks' products."""
    d = {}
    def add(m, v, i, x):
        d[(m, v, i)] = d.get((m, v, i), 0) + x
    for s, t in edges:
        add(1, t, s, 1)
    prev = None
    for x in prefix:
        add(0, x, x, -1)
        add(2, x, x, -1)
        if prev is not None:
            add(2, prev, x, 1)
            add(3, x, prev, -1)
            add(3, prev, prev, 1)
        prev = x
    return {k: v for k, v in d.items() if v != 0}


def pack_steps(edges, steps):
    """steps: list of (prefix, label). Returns the arrays consumed by the training kernels."""
    ptr, mat, vv, ii, val, q, y = [0], [], [], [], [], [], []
    for prefix, label in steps:
        for (m, v, i), x in sorted(sparse_from_prefix(edges, prefix).items()):
            mat.append(m); vv.append(v); ii.append(i); val.append(x)
        ptr.append(len(mat)); q.append(prefix[-1]); y.append(label)
    return dict(ptr=np.array(ptr, np.int64), mat=np.array(mat, np.int64), v=np.array(vv, np.int64),
                i=np.array(ii, np.int64), val=np.array(val, np.float64),
                q=np.array(q, np.int64), y=np.array(y, np.int64))


@njit(inline="always")
def _indicator(x, relu0, eps):
    if eps > 0.0:
        r = x / eps + (1.0 if relu0 == 1 else 0.0)
        return 0.0 if r <= 0.0 else (1.0 if r >= 1.0 else r)
    if x > 0.0:
        return 1.0
    if x == 0.0 and relu0 == 1:
        return 1.0
    return 0.0


@njit(fastmath=False)
def _instance(X, G, perm, s, ptr, mat, ev, ei, val, q, y, relu0, eps, h0, h1, z, w0, w1):
    """Add d(loss of step s under relabelling perm)/dX to G; return the loss."""
    N = X.shape[1]
    for v in range(N):
        h0[v] = 0.0; h1[v] = 0.0
    pq = perm[q[s]]
    for e in range(ptr[s], ptr[s + 1]):
        m = mat[e]
        c = val[e] * X[m, perm[ei[e]], pq]
        if m < 2:
            h0[ev[e]] += c
        else:
            h1[ev[e]] += c
    zmax = 0.0
    for v in range(N):
        a = h0[v] if h0[v] > 0.0 else 0.0
        b = h1[v] if h1[v] > 0.0 else 0.0
        z[v] = a + b
        if z[v] > zmax:
            zmax = z[v]
    z[q[s]] = 0.0
    total = 0.0
    for v in range(N):
        z[v] = np.exp(z[v] - zmax)
        total += z[v]
    ys = y[s]
    # competitors' total: gives p(y)-1 and -log p(y) without losing digits when p(y) -> 1
    rest = 0.0
    for v in range(N):
        if v != ys:
            rest += z[v]
    for v in range(N):
        g = -rest / total if v == ys else z[v] / total
        if v == q[s]:
            g = 0.0
        w0[v] = g * _indicator(h0[v], relu0, eps)
        w1[v] = g * _indicator(h1[v], relu0, eps)
    loss = np.log1p(rest / z[ys]) if z[ys] > 0.0 else np.inf
    for e in range(ptr[s], ptr[s + 1]):
        m = mat[e]
        G[m, perm[ei[e]], pq] += val[e] * (w0[ev[e]] if m < 2 else w1[ev[e]])
    return loss


@njit
def grad_single(X, perm, ptr, mat, ev, ei, val, q, y, relu0, eps):
    """Sum of step losses and gradient for one relabelled instance."""
    N = X.shape[1]
    G = np.zeros_like(X)
    h0, h1, z, w0, w1 = np.zeros(N), np.zeros(N), np.zeros(N), np.zeros(N), np.zeros(N)
    loss = 0.0
    for s in range(len(q)):
        loss += _instance(X, G, perm, s, ptr, mat, ev, ei, val, q, y, relu0, eps, h0, h1, z, w0, w1)
    return loss, G


@njit
def draw_perms(perms):
    """Fisher-Yates with numba's generator (call on the main thread only)."""
    B, N = perms.shape
    for b in range(B):
        for i in range(N):
            perms[b, i] = i
        for i in range(N - 1, 0, -1):
            j = np.random.randint(0, i + 1)
            tmp = perms[b, i]; perms[b, i] = perms[b, j]; perms[b, j] = tmp


@njit
def seed_rng(seed):
    np.random.seed(seed)


@njit(parallel=True)
def gd_segment(X, n_steps, eta, B, seed, n_chunks, ptr, mat, ev, ei, val, q, y, relu0, eps):
    """n_steps of minibatch GD with B fresh permutations per step. Modifies X in place.

    Gradients are accumulated in fixed chunks and summed in order, so results do not depend on the
    number of threads. The segment's permutations are determined by `seed`, so a resumed run replays
    identically. Returns the mean batch loss of the last step."""
    N = X.shape[1]
    S = len(q)
    perms = np.zeros((B, N), dtype=np.int64)
    Gs = np.zeros((n_chunks, 4, N, N))
    losses = np.zeros(n_chunks)
    last = 0.0
    np.random.seed(seed)
    for step in range(n_steps):
        draw_perms(perms)
        for c in prange(n_chunks):
            G = Gs[c]
            G[:] = 0.0
            h0, h1, z, w0, w1 = np.empty(N), np.empty(N), np.empty(N), np.empty(N), np.empty(N)
            l = 0.0
            for b in range(c * B // n_chunks, (c + 1) * B // n_chunks):
                for s in range(S):
                    l += _instance(X, G, perms[b], s, ptr, mat, ev, ei, val, q, y, relu0, eps, h0, h1, z, w0, w1)
            losses[c] = l
        for c in range(n_chunks):
            X -= (eta / B) * Gs[c]
        last = losses.sum() / B
    return last


@njit(parallel=True)
def eval_prefixes(X, n_pref, pptr, pmat, pv, pi, pval, gid, gptr, gv, gi, q, notC):
    """Logits, admissible-token loss and strict accuracy for each prefix.

    Trace entries are per prefix (pptr, ...), the A2-edge entries are per graph (gptr, ...).
    notC[p] is a bitmask of the vertices outside C_t."""
    N = X.shape[1]
    Z = np.zeros((n_pref, N))
    loss = np.zeros(n_pref)
    correct = np.zeros(n_pref, dtype=np.bool_)
    for p in prange(n_pref):
        h0 = np.zeros(N); h1 = np.zeros(N)
        qq = q[p]
        for e in range(pptr[p], pptr[p + 1]):
            m = pmat[e]
            c = pval[e] * X[m, pi[e], qq]
            if m < 2:
                h0[pv[e]] += c
            else:
                h1[pv[e]] += c
        g = gid[p]
        for e in range(gptr[g], gptr[g + 1]):
            h0[gv[e]] += X[1, gi[e], qq]
        zmax = 0.0
        for v in range(N):
            Z[p, v] = max(h0[v], 0.0) + max(h1[v], 0.0)
        Z[p, qq] = 0.0
        zmax = Z[p].max()
        sum_c, sum_not, max_c, max_not = 0.0, 0.0, -np.inf, -np.inf
        for v in range(N):
            ex = np.exp(Z[p, v] - zmax)
            if (notC[p] >> np.uint64(v)) & np.uint64(1):
                sum_not += ex
                if Z[p, v] > max_not:
                    max_not = Z[p, v]
            else:
                sum_c += ex
                if Z[p, v] > max_c:
                    max_c = Z[p, v]
        # -log(sum_c/(sum_c+sum_not)), accurate for tiny losses
        loss[p] = np.log1p(sum_not / sum_c) if sum_c > 0.0 else np.inf
        correct[p] = max_c > max_not   # strict: ties do not count as correct
    return Z, loss, correct


@njit
def expand_theta(theta, X):
    N = X.shape[1]
    for m in range(4):
        for i in range(N):
            for j in range(N):
                X[m, i, j] = theta[2 * m] if i == j else theta[2 * m + 1]


@njit
def scalar_grad(theta, N, ptr, mat, ev, ei, val, q, y, relu0, eps):
    """dL/dtheta on the canonical instance."""
    X = np.empty((4, N, N))
    expand_theta(theta, X)
    h0, h1, z, w0, w1 = np.empty(N), np.empty(N), np.empty(N), np.empty(N), np.empty(N)
    G = np.zeros((4, N, N))
    perm = np.arange(N)
    loss = 0.0
    for s in range(len(q)):
        loss += _instance(X, G, perm, s, ptr, mat, ev, ei, val, q, y, relu0, eps, h0, h1, z, w0, w1)
    g = np.zeros(8)
    for m in range(4):
        for i in range(N):
            for j in range(N):
                g[2 * m + (0 if i == j else 1)] += G[m, i, j]
    return loss, g


@njit
def euler_scalar(theta, n, eta, N, ptr, mat, ev, ei, val, q, y, relu0, eps):
    """n steps of fixed-step GD on the reduced model with learning rates alpha/N, alpha/(N(N-1))."""
    th = theta.copy()
    for _ in range(n):
        _, g = scalar_grad(th, N, ptr, mat, ev, ei, val, q, y, relu0, eps)
        for k in range(8):
            th[k] -= eta * g[k] / (N if k % 2 == 0 else N * (N - 1))
    return th


def scalar_coefficients(N, ptr, mat, ev, ei, val, q):
    """Integer coefficients C[s, head, v, k] with head_h[v] = sum_k C[s,h,v,k] theta_k (closed-form heads)."""
    C = np.zeros((len(q), 2, N, 8))
    for s in range(len(q)):
        for e in range(ptr[s], ptr[s + 1]):
            k = 2 * mat[e] + (0 if ei[e] == q[s] else 1)
            C[s, 0 if mat[e] < 2 else 1, ev[e], k] += val[e]
    return C


@njit
def coef_grad(th, C, q, y, relu0, eps):
    """Loss/gradient from C. Coefficients are summed before evaluation, so exact cancellations (g1-d1
    when g1==d1) stay exactly zero: no round-off lands on the ReLU kink."""
    S, _, N, _ = C.shape
    g = np.zeros(8)
    loss = 0.0
    h = np.zeros((2, N)); z = np.zeros(N)
    for s in range(S):
        for hh in range(2):
            for v in range(N):
                x = 0.0
                for k in range(8):
                    if C[s, hh, v, k] != 0.0:
                        x += C[s, hh, v, k] * th[k]
                h[hh, v] = x
        for v in range(N):
            z[v] = max(h[0, v], 0.0) + max(h[1, v], 0.0)
        z[q[s]] = 0.0
        zm = z.max()
        ex = np.exp(z - zm)
        tot = ex.sum()
        loss += np.log(tot) - np.log(ex[y[s]])
        for v in range(N):
            if v == q[s]:
                continue
            w = ex[v] / tot - (1.0 if v == y[s] else 0.0)
            for hh in range(2):
                ind = _indicator(h[hh, v], relu0, eps)
                if ind != 0.0:
                    for k in range(8):
                        g[k] += w * ind * C[s, hh, v, k]
    return loss, g


@njit
def euler_coef(theta, n, eta, C, q, y, relu0, eps):
    th = theta.copy()
    N = C.shape[2]
    for _ in range(n):
        _, g = coef_grad(th, C, q, y, relu0, eps)
        for k in range(8):
            th[k] -= eta * g[k] / (N if k % 2 == 0 else N * (N - 1))
    return th
