import numpy as np, dfs, pytest


@pytest.mark.parametrize("N,K", [(7, 2), (12, 4), (16, 8), (16, 11)])
def test_canonical_trace_valid(N, K):
    c = dfs.canonical(N, K)
    assert dfs.is_valid_trace(c["edges"], c["target"], c["full"])
    assert len(c["steps"]) == 2 * K + 2
    for prefix, y in c["steps"]:
        assert y in dfs.dfs_step(dfs.out_map(c["edges"]), c["target"], prefix)[0]
    # final trained step goes to N-3 (index N-4); first predicts vertex 1 (index 0) from N-3
    assert c["steps"][0] == ((N - 2, N - 3, N - 4), 0)
    assert c["steps"][-1][1] == N - 4


@pytest.mark.parametrize("N", [9, 12, 16])
def test_canonical_invalid_at_N_minus_4(N):
    c = dfs.canonical(N, N - 4)
    assert not dfs.is_valid_trace(c["edges"], c["target"], c["full"])


def test_categories():
    c = dfs.canonical(16, 8)
    out = dfs.out_map(c["edges"])
    tr = c["full"]
    cats = [dfs.dfs_step(out, c["target"], tr[:k])[1] for k in range(1, len(tr))]
    assert cats[-1] == dfs.BT_ROOT and dfs.BT_NONROOT in cats and dfs.FORWARD in cats
    assert dfs.dfs_step(out, c["target"], tr) is None      # exhausted at root


@pytest.mark.parametrize("seed", range(3))
def test_generated_traces_valid(seed):
    graphs, rng = dfs.generate_test_graphs(10, 4, seed, n_each=20)
    assert len(graphs) == 60
    for kind, edges, root, target in graphs:
        assert root != target
        assert len(set(edges)) == len(edges)
        out = dfs.out_map(edges)
        for pref in dfs.prefixes_of_graph(edges, root, target, rng):
            assert dfs.is_valid_trace(edges, target, pref)
            assert dfs.dfs_step(out, target, pref) is not None
