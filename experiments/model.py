"""Parameters, initialisation, gradients, and the reduced 8-scalar flow."""
import numpy as np
import kernels as kn
import dfs

NAMES = ("a1", "b1", "a2", "b2", "g1", "d1", "g2", "d2")  # X[0..3] = A1, A2, B1, B2


def theta_to_X(theta, N):
    """8 scalars -> X with shape [4,N,N]; order (A1,A2,B1,B2)."""
    X = np.empty((4, N, N))
    for m in range(4):
        X[m].fill(theta[2 * m + 1])
        np.fill_diagonal(X[m], theta[2 * m])
    return X


def X_to_theta(X):
    """Effective scalars diag(X), off(X) of each matrix."""
    N = X.shape[1]
    out = np.empty(8)
    for m in range(4):
        tr = np.trace(X[m])
        out[2 * m] = tr / N
        out[2 * m + 1] = (X[m].sum() - tr) / (N * (N - 1))
    return out


def subspace_distance(X):
    th = X_to_theta(X)
    N = X.shape[1]
    P = theta_to_X(th, N)
    return np.sqrt(((X - P) ** 2).sum((1, 2))) / np.sqrt((X ** 2).sum((1, 2)))


def init_theta(N, kind="new", c0=None, c0p=None):
    c0 = 1.0 / N ** 2 if c0 is None else c0
    c0p = c0 / 2 if c0p is None else c0p
    if kind == "new":
        th = dict(a1=c0, b1=c0, a2=c0, b2=c0p, g1=c0, d1=c0p, g2=c0, d2=c0)
    elif kind == "constant":
        th = {k: c0 for k in NAMES}
    else:
        raise ValueError(kind)
    return np.array([th[k] for k in NAMES])


class Canonical:
    """Canonical training instance with packed kernel arrays."""

    def __init__(self, N, K):
        self.N, self.K = N, K
        self.inst = dfs.canonical(N, K)
        self.pk = kn.pack_steps(self.inst["edges"], self.inst["steps"])
        self.identity = np.arange(N, dtype=np.int64)
        self.args = tuple(self.pk[k] for k in ("ptr", "mat", "v", "i", "val", "q", "y"))

    def grad_theta(self, theta, relu0=1, eps=0.0):
        """Loss and raw partial derivatives dL/dtheta (no learning-rate normalisation)."""
        return kn.scalar_grad(np.asarray(theta, dtype=float), self.N, *self.args, relu0, eps)

    def flow(self, theta, relu0=1, eps=0.0, alpha=1.0):
        """Right-hand side of the reduced flow, = full-matrix flow restricted to the subspace."""
        _, g = self.grad_theta(theta, relu0, eps)
        return -alpha * g * lr_scale(self.N)

    def euler(self, theta, n, eta, relu0=1, eps=0.0):
        """Fixed-step GD on the scalars (the discrete analogue of the full-matrix GD)."""
        return kn.euler_scalar(np.asarray(theta, dtype=float), n, eta, self.N, *self.args, relu0, eps)


def lr_scale(N):
    s = np.empty(8)
    s[0::2] = 1.0 / N
    s[1::2] = 1.0 / (N * (N - 1))
    return s
