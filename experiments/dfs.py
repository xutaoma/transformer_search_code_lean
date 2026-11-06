"""Graphs, DFS rule, traces, token blocks (plan sec. 1.1-1.2, 1.4, 1.7). Vertices are 0-indexed
internally: the plan's vertex k is k-1 here."""
from __future__ import annotations
import numpy as np

FORWARD, BT_NONROOT, BT_ROOT = "forward", "backtrack_nonroot", "backtrack_root"
CATEGORIES = (FORWARD, BT_NONROOT, BT_ROOT)


def stack_of(prefix):
    stack = [prefix[0]]
    for b in prefix[1:]:
        if len(stack) >= 2 and stack[-2] == b:
            stack.pop()
        else:
            stack.append(b)
    return stack


def dfs_step(out, target, prefix):
    """Return (C_t sorted tuple, category, parent) or None if the trace has terminated."""
    cur = prefix[-1]
    if cur == target:
        return None
    visited = set(prefix)
    unvisited = sorted(v for v in out.get(cur, ()) if v not in visited)
    if unvisited:
        return tuple(unvisited), FORWARD, None
    stack = stack_of(prefix)
    if len(stack) == 1:  # exhausted at the root
        return None
    parent = stack[-2]
    return (parent,), (BT_ROOT if parent == prefix[0] else BT_NONROOT), parent


def out_map(edges):
    out = {}
    for s, t in edges:
        out.setdefault(s, set()).add(t)
    return out


def is_valid_trace(edges, target, trace):
    out = out_map(edges)
    for k in range(len(trace) - 1):
        st = dfs_step(out, target, trace[: k + 1])
        if st is None or trace[k + 1] not in st[0]:
            return False
    return True


def count_traces(out, target, prefix, cap):
    st = dfs_step(out, target, prefix)
    if st is None:
        return 1
    total = 0
    for v in st[0]:
        total += count_traces(out, target, prefix + (v,), cap - total)
        if total >= cap:
            return total
    return total


def all_traces(out, target, prefix):
    st = dfs_step(out, target, prefix)
    if st is None:
        yield prefix
        return
    for v in st[0]:
        yield from all_traces(out, target, prefix + (v,))


def random_trace(out, target, root, rng):
    prefix = (root,)
    while (st := dfs_step(out, target, prefix)) is not None:
        prefix += (st[0][rng.integers(len(st[0]))],)
    return prefix


def canonical(N, K):
    """Return dict with G0 (0-indexed), the full trace, and the trained part tau0.

    `steps` lists the 2K+2 trained (prefix, label) pairs."""
    if not (N >= 7 and 2 <= K <= N - 4):  # K=N-4 is representable, only so a test can show it is invalid
        raise ValueError((N, K))
    v = lambda k: k - 1  # plan's 1-indexed label
    edges = [(v(1), v(i)) for i in range(2, K + 2)] + [
        (v(N - 1), v(N - 2)), (v(N - 2), v(N - 3)), (v(N - 3), v(1))]
    root, target = v(N - 1), v(N)
    full = [v(N - 1), v(N - 2), v(N - 3), v(1)]
    for i in range(2, K + 2):
        full += [v(i), v(1)]
    head = full[:]
    full += [v(N - 3), v(N - 2), v(N - 1)]
    # trained labels: 1, then 2,1,...,K+1,1, then N-3
    labels = head[3:] + [v(N - 3)]
    steps = [(tuple(full[: 3 + j]), y) for j, y in enumerate(labels)]
    assert len(steps) == 2 * K + 2
    return dict(N=N, K=K, edges=edges, root=root, target=target, full=tuple(full), steps=steps)


def build_blocks(N, edges, target, prefix):
    """Literal layer-2 input of table 1.2: arrays a,b,c,d of shape [T,N] for the whole sequence."""
    rows = []
    z = None
    rows.append((z, z, z, z))  # <s>
    for s, t in edges:
        rows.append((z, z, z, s))        # edge source
        rows.append((z, z, s, t))        # edge target
        rows.append((z, z, t, z))        # <e>
    rows.append((z, z, z, target))       # target
    rows.append((z, z, target, z))       # <r>
    rows.append((prefix[0], z, z, z))    # root
    for k in range(1, len(prefix)):
        rows.append((prefix[k], prefix[k - 1], z, z))
    T = len(rows)
    out = np.zeros((4, T, N))
    for j, row in enumerate(rows):
        for blk, val in enumerate(row):
            if val is not None:
                out[blk, j, val] = 1.0
    return out  # a,b,c,d = out


# ---------------------------------------------------------------- test set (sec 1.7)

def _er(N, rng, p):
    allow_loops = rng.random() < 0.2
    edges = [(i, j) for i in range(N) for j in range(N)
             if (i != j or allow_loops) and rng.random() < p]
    root = int(rng.integers(N))
    target = int(rng.choice([v for v in range(N) if v != root]))
    return edges, root, target


def _tree(N, rng):
    perm = rng.permutation(N).tolist()
    edges = {(perm[int(rng.integers(i))], perm[i]) for i in range(1, N)}
    for _ in range(int(rng.integers(0, 4))):
        edges.add((int(rng.integers(N)), int(rng.integers(N))))
    root = perm[0]
    target = int(rng.choice(perm[1:]))
    return sorted(edges), root, target


def _fan(N, rng):
    perm = rng.permutation(N).tolist()
    root, rest = perm[0], perm[1:]
    k = int(rng.integers(2, 5))
    unreachable = rng.random() < 0.5
    spare = rest.pop() if unreachable else None
    # split `rest` into k non-empty chains (leaving out a few vertices at random)
    n_used = int(rng.integers(k, len(rest) + 1))
    used = rest[:n_used]
    cuts = sorted(rng.choice(np.arange(1, n_used), size=k - 1, replace=False).tolist())
    chains = [used[i:j] for i, j in zip([0] + cuts, cuts + [n_used])]
    edges = []
    for ch in chains:
        edges.append((root, ch[0]))
        edges += list(zip(ch[:-1], ch[1:]))
    target = spare if unreachable else chains[-1][-1]
    return edges, root, target


def generate_test_graphs(N, K, seed, n_each=100):
    rng = np.random.default_rng([seed, N])
    graphs = []
    ps = (0.1, 0.2, 0.4)
    for i in range(n_each):
        graphs.append(("er", *_er(N, rng, ps[i % 3])))
    for _ in range(n_each):
        graphs.append(("tree", *_tree(N, rng)))
    for _ in range(n_each):
        graphs.append(("fan", *_fan(N, rng)))
    return graphs, rng


def prefixes_of_graph(edges, root, target, rng, max_traces=50):
    out = out_map(edges)
    if count_traces(out, target, (root,), max_traces + 1) <= max_traces:
        traces = list(all_traces(out, target, (root,)))
    else:
        traces = [random_trace(out, target, root, rng) for _ in range(max_traces)]
    pref = set()
    for tr in traces:
        for k in range(1, len(tr) + 1):
            if dfs_step(out, target, tr[:k]) is not None:
                pref.add(tr[:k])
    return sorted(pref)
