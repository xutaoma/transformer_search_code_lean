# Transformers Provably Learn Graph Search: code and Lean 4 proofs

This repository accompanies the paper *Transformers Provably Learn Graph Search: Training Dynamics and the Exponential Power of Depth*, NeurIPS 2026.

| Folder | Contents |
|---|---|
| [`lean/`](lean/) | Lean 4 + Mathlib proofs. `lean/DFSExpr/`: expressivity (Sec. 3 and its appendix). `lean/DFSLean/`: training dynamics (Sec. 4 and App. C: Prop. 4.1, Lemmas C.1–C.4, Cor. C.3, Thm C.5, **Theorem 4.2**). |
| [`experiments/`](experiments/) | Python code for the experiments and the figures of the paper |

---

## 1. Checking the Lean proofs

Install [elan](https://github.com/leanprover/elan) (the Lean version manager). The Lean version and the
Mathlib commit are pinned in `lean/lean-toolchain` and `lean/lake-manifest.json`, and elan downloads the
right toolchain automatically.

```bash
cd lean
lake exe cache get      # download prebuilt Mathlib
lake build              # builds both libraries and the statement check SpecCheck
```

A successful build shows:
* no errors;
* "declaration uses sorry" warnings only from the `Spec*.lean` files. These state the theorems without
  proofs, and nothing depends on them;
* axiom reports from `SpecCheck` showing that every main theorem depends only on Lean's standard axioms
  `propext`, `Classical.choice` and `Quot.sound`.

The GitHub Actions workflow `.github/workflows/lean.yml` runs this build and these checks on every push.

### Where the statements are

| Paper | Statement file | Definitions used |
|---|---|---|
| Sec. 3: Thm `thm:lower_bound`, Cor `cor:dense_graph_lower_bound`, Lemma `lem:first-layer-softmax-copy-relu`, Thm `thm:two_layer_dfs`, Lemma `lem:k-layer-lookahead`, Thm `thm:exponential-depth-advantage`, Lemma `lem:lookahead-efficiency`, Cor `cor:k-layer-efficiency` | `lean/DFSExpr/Spec.lean` | `lean/DFSExpr/Defs.lean` |
| Lemma C.4, Theorem C.5 | `lean/DFSLean/Spec.lean` | `lean/DFSLean/Defs.lean` |
| Prop. 4.1, Lemma C.1, Tables 1–2, Lemma C.2, Cor. C.3, **Theorem 4.2** | `lean/DFSLean/Spec2.lean` | `lean/DFSLean/Model.lean` |


The proof of `X.Spec.foo` is the theorem `X.foo` in another file. `SpecCheck.lean` (one in each library)
contains, for every theorem,

```lean
example : type_of% @DFS.Spec.learning_dynamics := @DFS.learning_dynamics
```

This compiles only if the proved theorem has exactly the type stated in the Spec file. So, to check what has
been proved, you only need to read the Spec files and the definitions they use, not the proofs.

The main result of the training-dynamics part is `DFS.learning_dynamics` (Theorem 4.2,
`lean/DFSLean/Spec2.lean`, line 330). [`lean/DFSLean/README.md`](lean/DFSLean/README.md) and
[`lean/DFSExpr/README.md`](lean/DFSExpr/README.md) link every Lean theorem to its paper result and describe the
modelling choices.

### Scope

* **Training dynamics.**
  * The first layer is idealized: it copies exactly (`δ = 0`), as in App. C.
  * Theorem 4.2 is stated for every solution of the eight-scalar gradient flow. `IsSol8.iota` shows that these
    give solutions of the matrix-level gradient flow on `ℒ_train` that stay in the permutation-invariant family 𝓕.
  * Matrix-level solutions that leave 𝓕 are not covered.
  * The sharpness remark after Theorem 4.2 is not formalized.
* **Expressivity.**
  * The constructions are proved in exact real arithmetic. Bit precision is formalized for the lower bound only.
  * The two-layer theorem bounds the parameter magnitudes.

---

## 2. Reproducing the experiments

See [`experiments/README.md`](experiments/README.md) for details.

```bash
cd experiments
pip install -r requirements.txt
python -m pytest -q tests     # unit tests (the model is checked against a literal PyTorch implementation)
```

Then run the experiments (all hyperparameters and seeds are in `experiments/config.yaml`), and regenerate the
figures of the paper from their results:

```bash
python experiments/make_figures.py   # from the repository root; writes the 9 figures to figure/
```

| Paper figure | Produced by (in `experiments/`) |
|---|---|
| `rates_main` | `run.py --exp A --part reduced` and `--part full` |
| `rates_individual`, `gaps` | `run.py --exp A --part reduced` |
| `subspace` | `run.py --exp A --part full` |
| `gen_decay` | `run.py --exp B --part all` |
| `gen_accuracy` | `run.py --exp Bdiag` |
| `exponent_vs_N` | `run.py --exp C` |
| `init_ablation` | `run.py --exp D --part reduced` and `--part full` |
| `init_wrong_side` | `d2_wrong_side.py` |

The longest run, the full-matrix training (`--exp A --part full`), takes about 2 hours on 12 CPU threads.
