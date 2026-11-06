# Experiments: training dynamics of the two-layer DFS transformer

These experiments support Sec. 4 and the experiments section of the paper. All runs use float64.
All hyperparameters and seeds are in `config.yaml` (learning rate `α = 1` throughout).

## Setup

Python 3.10 or later.

```bash
pip install -r requirements.txt
python -m pytest -q tests        # unit tests; run them first
```

`torch` and `pytest` are needed only for the tests: `tests/reference.py` is a literal PyTorch implementation
of the model, and the fast kernels are checked against it and against autograd.

## Running the experiments

Run these from this folder, in this order (B uses the trajectories of A, and `diag_early.py` uses A1). The
runs write their results to `results/`; test sets are generated once and cached in `results/cache/`.

```bash
python run.py --exp A --part reduced    # A1: eight-scalar flow to t = 1e9 (minutes, including the eps and GD checks)
python run.py --exp A --part full       # A2: full matrices, 1e7 steps, B = 128 permutations per step (about 2 h on 12 CPU threads; resumable)
python run.py --exp B --part all        # generalization loss along A1 and A2
python run.py --exp Bdiag               # back-edge split and flow to t = 1e16
python diag_early.py                    # A2 early phase vs batch size and step size (diagnostic)
python run.py --exp C                   # exponent vs N
python run.py --exp D --part reduced    # D1-D3: initialization ablation, eight-scalar flow
python run.py --exp D --part full       # D4: full matrices, 3 seeds, 1e6 steps
python d2_wrong_side.py                 # D1-D3 at (N, K) = (16, 2), (40, 3), (16, 8) and threshold scan
python run.py --exp plots               # diagnostic figures in figures/
python run.py --exp summary             # results/summary.md: summary table of the results
```

The number of CPU threads is set by `threads` in `config.yaml` (12 by default, and 4 for D4).
`run.py --exp Bdiag` always uses 4 threads. numba refuses more threads than the machine has cores, so on a
smaller machine lower these values. The thread count does not change the results; the unit test
`test_gd_segment_invariant_to_thread_count_and_consistent` checks this and needs at least 4 cores.

## Figures of the paper

After the runs, regenerate the 9 figures of the paper from `results/`. From the repository root:

```bash
python experiments/make_figures.py
```

This writes the figures as PDFs to `figure/`, and PDF and PNG previews to `experiments/figures/`.

| Paper figure | Results file(s) | Produced by |
|---|---|---|
| `rates_main` | `A1_reduced.npz`, `A2_full.npz` | `run.py --exp A` |
| `rates_individual`, `gaps` | `A1_reduced.npz` | `run.py --exp A --part reduced` |
| `subspace` | `A2_full.npz` | `run.py --exp A --part full` |
| `gen_decay` | `B_gen_reduced.npz`, `B_gen_full.npz` | `run.py --exp B --part all` |
| `gen_accuracy` | `B_diagnostics.npz` | `run.py --exp Bdiag` |
| `exponent_vs_N` | `C_curves.npz` | `run.py --exp C` |
| `init_ablation` | `D1_reduced.npz` … `D3_roundoff_reduced.npz`, `D4_seed{1,2,3}.npz` | `run.py --exp D` |
| `init_wrong_side` | `D2_wrong_side.npz` | `d2_wrong_side.py` |

## Files

- `dfs.py`: DFS rule, canonical training instance, token blocks, test graphs.
- `kernels.py`: compiled (numba) forward and backward passes.
- `model.py`: parameters, initialization, the eight-scalar (reduced) flow.
- `evaluate.py`: test-set construction and metrics.
- `run.py`: driver for experiments A–D. `summarize.py` and `plots.py`: summary table and diagnostic figures.
- `d2_wrong_side.py`, `diag_early.py`: the two additional studies above.
- `make_figures.py`: the figures of the paper.
- `tests/`: unit tests. `tests/reference.py` is the PyTorch reference implementation.
