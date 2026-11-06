# DFS paper: Lean 4 formalization of the learning-dynamics theorem (Stages 1–4)

Machine-checked proofs, in Lean 4 + Mathlib, of the learning-dynamics part of the DFS paper:
Prop. 4.1 and Thm 4.2 (Sec. 4) with their appendix lemmas: Lemma C.1, Lemma C.2, Cor. C.3,
Lemma C.4, Thm C.5, the node-logit tables, and the generalization bound.
Lean `v4.36.0-rc2`, Mathlib commit `e75a902d` (see `../lakefile.toml`, `../lake-manifest.json`).

**Status: complete.** No `sorry` in any proof file. All 63 main theorems depend only on Lean's
standard axioms (`propext`, `Classical.choice`, `Quot.sound`), checked with `#print axioms`.

## Build
Build from the parent folder `lean/`, which builds this library, `DFSExpr` and `SpecCheck` (see `../README.md`):
```bash
cd lean
lake exe cache get   # prebuilt Mathlib (cache.mathlib.org)
lake build
```
`SpecCheck` (`SpecCheck.lean` in this folder) checks that each proved theorem has exactly the type of its statement in `Spec.lean`
(Stage 1) or `Spec2.lean` (Stages 2–4). Those files were frozen before any proof was written. It
also prints the axioms of the main results. The two `Spec` files are the only ones that contain
`sorry`; nothing depends on them.

## Main results (namespace `DFS`)
| Lean | Paper |
|---|---|
| `learning_dynamics` | **Thm 4.2**: rates of `a₂, b₁, g₁−d₁`, `|g₁−d₁−g₂+d₂| ≤ C`, rates of `g₁, g₂, d₁, d₂`, and `ℒ_gen ≤ C (αt)^{-(N-1)/N}` |
| `logit_perm`, `lossInst_perm`, `lossTrain_perm`, `fixed_iff`, `lossTrain_iota`, `VelM_perm` | **Prop. 4.1**, Steps 1–4 (equivariance, invariance, fixed points = 𝓕, reduction to one instance, ∂L(π·θ) = π·∂L(θ)) |
| `gTrain_iota`, `IsSol8.iota` | **Lemma C.1**, and the flow part of Prop. 4.1 |
| `head1_iota`, `head2_iota`, `logit_of_ne` | node-logit **Tables 1–2** (any graph, any context) |
| `g8_on_R`, `g8_bound_on_R` | **Lemma C.2**, Step 2 (gradient on the region, eq. `grad_bound`) |
| `lemmaC2_region`, `lemmaC2_mono`, `lemmaC2_lip`, `lemmaC2_initial` | **Lemma C.2**, items 1–2 (invariant region, initial phase) |
| `corC3` | **Cor. C.3** (reduction to the 4-variable system, recovery identities) |
| `four_parameter_log_convergence`, `item1`…`item4` | **Thm C.5** |
| `log_growth`, `log_growth_asymp` | **Lemma C.4** |
| `genLoss_bound`, `trace_length_le` | generalization bound in the proof of Thm 4.2 (Cases 1–3, normalizer bound) |
| `exists_IsDI`, `exists_IsSol8` | existence of Filippov solutions (the theorems are not vacuous) |
| `lossInst_hasFDerivAt`, `lossTrain_hasFDerivAt`, `loss8_hasFDerivAt` | the generalized gradient is the true derivative wherever the loss is smooth |

## Modelling choices
- **Model** (`Model.lean`). The second layer is formalized literally: hidden states entering layer 2
  (Sec. 3, eq. `hidden_state_after_first_layer`), the two linear-attention heads with the trainable
  blocks `A₁, A₂, B₁, B₂`, the values `W_V`, routing `W_O`, ReLU, residual, and the dynamic readout
  masking `n_t`, followed by a softmax over the vertex tokens. The canonical training data is
  `E₀, τ_pre, τ₀`, and the training loss is the permutation average of eq. `permutation_loss`.
  Vertices are `Fin N`; paper vertex `k` is index `k−1`.
- **δ = 0 idealization.** The first layer is taken to copy one-hot vectors exactly, as App. C assumes.
  The Sec. 3 construction has leakage δ > 0.
- **Generalized gradients.** Every ReLU argument is a linear functional of the parameters. A *selection*
  gives each functional a value in [0,1]: 1 where it is positive, 0 where it is negative, and the same
  value for identical functionals. The selection gradients form a convex set that contains Clarke's
  generalized gradient. So every Filippov/Clarke gradient-flow solution is a solution in our sense,
  and the theorems apply to all of them.
  - For the eight-scalar flow (`IsSol8`), the set equals the Filippov set wherever `b₁ ≠ 0`, which
    holds along the whole trajectory.
  - At the matrix level (`IsMatSol`) it can be strictly larger than Clarke's set. So `IsSol8.iota`
    shows that the embedded scalar solution solves this relaxed matrix inclusion.
- **Solutions** (`IsDI`, as in Stage 1): continuous on [0,∞), and at every `t ≥ 0` the right difference
  quotients approach the velocity set. This is equivalent to "Filippov solution" (absolutely
  continuous, a.e. inclusion) for upper semicontinuous convex compact velocity sets. Existence is
  proved (`exists_IsDI`, Euler steps plus an ultrafilter limit).
- **Thm 4.2 is stated for the eight-scalar flow** from the initialization. By Prop. 4.1, these are the
  matrix-level solutions that stay in 𝓕. Matrix-level solutions that leave 𝓕 are not covered; the
  paper doesn't rule them out either, since uniqueness fails at the initialization, where `u = 0`.
- **ℒ_gen** is a supremum. It is formalized as a bound on `genLoss` for every edge set without
  duplicates and every valid nonterminated DFS trace (`ValidTrace`), which is equivalent.
- **Uniform constants.** All constants depend only on `N, K, c₀, c₀'`. They do not depend on `α` or
  on the choice of (possibly non-unique) Filippov solution. The constant `c* = c*(K)` is explicit:
  `min(1/(4(K+1)(1+(K+3)e²)), 1/2)`.

## Files
- **Stage 1:**
  - `Defs.lean`: definitions.
  - `Basic.lean`: infrastructure and invariants.
  - `LogGrowth.lean`: Lemma C.4.
  - `Item1.lean`, `Item2.lean`, `Lyapunov.lean`, `Item3.lean`, `Coeffs.lean`, `Item4.lean`: Thm C.5.
- **Stages 2–4:**
  - `Model.lean`: definitions.
  - `GenericDI.lean`: generic differential-inclusion lemmas.
  - `Existence.lean`, `V8Props.lean`: existence of solutions.
  - `Equivariance.lean`, `LemmaC1.lean`: Prop. 4.1 and Lemma C.1.
  - `Smooth.lean`: the generalized gradient is the derivative where the loss is smooth.
  - `Tables.lean`: the node-logit tables.
  - `CanonGrad.lean`, `LemmaC2.lean`: Lemma C.2.
  - `CorC3.lean`: Cor. C.3.
  - `GenBound.lean`: DFS traces and `ℒ_gen`.
  - `Final.lean`: Thm 4.2.
- **Specification:** `Spec.lean`, `Spec2.lean` (frozen statements) and `SpecCheck.lean`.

## Not formalized
- The first layer (Sec. 3 construction, `lem:first-layer-softmax-copy-relu`); the model starts from
  its idealized (δ = 0) output.
- The expressivity results of Sec. 3 (one-layer lower bound, two-layer construction, look-ahead).
- Uniqueness of the matrix-level flow, and matrix-level solutions that leave 𝓕.
- The sharpness remark after Thm 4.2 (the matching lower bound `(αt)^{-(N-1)/N}`).
