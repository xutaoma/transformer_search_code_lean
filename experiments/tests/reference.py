"""Literal torch implementation of plan sec. 1.3 (dense blocks + autograd), independent of kernels.py."""
import torch
import dfs


def relu_conv(x, relu0):
    ind = (x >= 0) if relu0 == 1 else (x > 0)
    return x * ind.to(x.dtype)


def heads(Xs, blocks, q):
    a, b, c, d = [torch.as_tensor(z, dtype=torch.float64) for z in blocks]
    A1, A2, B1, B2 = Xs
    aq = torch.zeros(a.shape[1], dtype=torch.float64); aq[q] = 1.0
    s1 = a @ (A1 @ aq) + c @ (A2 @ aq)
    h1 = (d - a).T @ s1
    s2 = a @ (B1 @ aq) + b @ (B2 @ aq)
    h2 = (b - a).T @ s2
    return h1, h2


def logits(Xs, blocks, q, relu0=1):
    h1, h2 = heads(Xs, blocks, q)
    z = relu_conv(h1, relu0) + relu_conv(h2, relu0)
    mask = torch.ones_like(z); mask[q] = 0.0
    return z * mask


def canonical_loss(Xs, inst, relu0=1):
    N = inst["N"]
    total = 0.0
    for prefix, y in inst["steps"]:
        blk = dfs.build_blocks(N, inst["edges"], inst["target"], prefix)
        z = logits(Xs, blk, prefix[-1], relu0)
        total = total - torch.log_softmax(z, 0)[y]
    return total


def from_theta(theta, N):
    I = torch.eye(N, dtype=torch.float64); Eoff = 1 - I
    return [theta[2 * m] * I + theta[2 * m + 1] * Eoff for m in range(4)]
