import DFSLean.Model
import DFSLean.Item4

/-!
# Stages 2–4: frozen specification (all `sorry`; checked against the proofs in `SpecCheck.lean`)

Each block is one work package; a package may use the statements of other packages as black
boxes (as listed in its brief), plus everything proved in Stage 1 (`DFS.IsSol.*`, `DFS.item*`,
`DFS.four_parameter_log_convergence`, …).
-/

noncomputable section
open Real Finset Filter Topology Set

namespace DFS.Spec

variable {N K : ℕ}

/-! ## G. Generic differential inclusions on `ℝⁿ` -/

section generic
variable {n : ℕ} {V : (Fin n → ℝ) → Set (Fin n → ℝ)} {z : ℝ → Fin n → ℝ}

theorem IsSol_iff_IsDI {α : ℝ} {z : ℝ → Fin 4 → ℝ} : IsSol N K α z ↔ IsDI (Vel N K α) z := by
  sorry

theorem IsDI.mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {V W : E → Set E}
    {z : ℝ → E} (hVW : ∀ x, V x ⊆ W x) (hz : IsDI V z) : IsDI W z := by
  sorry

theorem IsDI.shift (hz : IsDI V z) {T : ℝ} (hT : 0 ≤ T) : IsDI V (fun t => z (T + t)) := by
  sorry

theorem IsDI.slope_dot (hz : IsDI V z) (c d : Fin n → ℝ) {t : ℝ} (ht : 0 ≤ t) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), ∃ w ∈ V (z t),
      |(c ⬝ᵥ z (t + h) - c ⬝ᵥ z t) / h - c ⬝ᵥ w| < ε ∧
      |(d ⬝ᵥ z (t + h) - d ⬝ᵥ z t) / h - d ⬝ᵥ w| < ε := by
  sorry

/-- Mean-value bound: velocities with `c ⬝ᵥ w ≤ M` on `[a, b)` give `c ⬝ᵥ z b ≤ c ⬝ᵥ z a + M (b - a)`. -/
theorem IsDI.dot_le (hz : IsDI V z) (c : Fin n → ℝ) (M : ℝ) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (h : ∀ t ∈ Ico a b, ∀ w ∈ V (z t), c ⬝ᵥ w ≤ M) :
    c ⬝ᵥ z b ≤ c ⬝ᵥ z a + M * (b - a) := by
  sorry

theorem IsDI.barrier (hz : IsDI V z) (c : Fin n → ℝ) (L : ℝ) {a b : ℝ} (ha : 0 ≤ a)
    (h : ∀ t ∈ Ico a b, L < c ⬝ᵥ z t → ∀ w ∈ V (z t), c ⬝ᵥ w ≤ 0) :
    ∀ t ∈ Icc a b, c ⬝ᵥ z t ≤ max (c ⬝ᵥ z a) L := by
  sorry

theorem IsDI.reach (hz : IsDI V z) (c : Fin n → ℝ) (L δ : ℝ) (hδ : 0 < δ) {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ t ≥ a, c ⬝ᵥ z t < L → ∀ w ∈ V (z t), δ ≤ c ⬝ᵥ w) :
    ∀ t ≥ a, a + (L - c ⬝ᵥ z a) / δ ≤ t → L ≤ c ⬝ᵥ z t := by
  sorry

end generic

/-! ## E1. Existence of solutions (Filippov's theorem, measure-free form) -/

theorem exists_IsDI {n : ℕ} (V : (Fin n → ℝ) → Set (Fin n → ℝ)) (M : ℝ)
    (hne : ∀ x, (V x).Nonempty) (hconv : ∀ x, Convex ℝ (V x)) (hclosed : ∀ x, IsClosed (V x))
    (hbdd : ∀ x, ∀ w ∈ V x, ‖w‖ ≤ M)
    (husc : ∀ x, ∀ ε > 0, ∃ δ > 0, ∀ y, ‖y - x‖ < δ → ∀ w ∈ V y, ∃ w' ∈ V x, ‖w - w'‖ < ε)
    (x0 : Fin n → ℝ) : ∃ z : ℝ → Fin n → ℝ, IsDI V z ∧ z 0 = x0 := by
  sorry

/-! ## E2. The scalar velocity set satisfies the hypotheses of `exists_IsDI` -/

section V8props
variable [NeZero N]

theorem V8_nonempty (α : ℝ) (s : Fin 8 → ℝ) : (V8 N K α s).Nonempty := by
  sorry

theorem V8_convex (α : ℝ) (s : Fin 8 → ℝ) : Convex ℝ (V8 N K α s) := by
  sorry

theorem V8_closed (α : ℝ) (s : Fin 8 → ℝ) : IsClosed (V8 N K α s) := by
  sorry

theorem V8_bounded (α : ℝ) : ∃ M : ℝ, ∀ s, ∀ w ∈ V8 N K α s, ‖w‖ ≤ M := by
  sorry

theorem V8_usc (α : ℝ) (s : Fin 8 → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s', ‖s' - s‖ < δ → ∀ w ∈ V8 N K α s', ∃ w' ∈ V8 N K α s, ‖w - w'‖ < ε := by
  sorry

/-- The eight-scalar gradient flow has a (global, Filippov) solution from every initial point. -/
theorem exists_IsSol8 (α : ℝ) (s0 : Fin 8 → ℝ) : ∃ s, IsSol8 N K α s ∧ s 0 = s0 := by
  sorry

end V8props

/-! ## M1. Permutation equivariance (Prop. 4.1, Steps 1–4) -/

theorem head1_eq_pair (θ : Params N) (c : Ctx N) (v : Fin N) : head1 θ c v = pair (coef1 c v) θ := by
  sorry

theorem head2_eq_pair (θ : Params N) (c : Ctx N) (v : Fin N) : head2 θ c v = pair (coef2 c v) θ := by
  sorry

theorem coef1_perm (pm : Equiv.Perm (Fin N)) (c : Ctx N) (v : Fin N) :
    coef1 (c.perm pm) (pm v) = permP pm (coef1 c v) := by
  sorry

theorem coef2_perm (pm : Equiv.Perm (Fin N)) (c : Ctx N) (v : Fin N) :
    coef2 (c.perm pm) (pm v) = permP pm (coef2 c v) := by
  sorry

/-- Step 1: the network is equivariant, `TF(Π X; π·θ) = P_π TF(X; θ)`. -/
theorem logit_perm (pm : Equiv.Perm (Fin N)) (θ : Params N) (c : Ctx N) (v : Fin N) :
    logit (permP pm θ) (c.perm pm) (pm v) = logit θ c v := by
  sorry

theorem prob_perm (pm : Equiv.Perm (Fin N)) (θ : Params N) (c : Ctx N) (v : Fin N) :
    prob (permP pm θ) (c.perm pm) (pm v) = prob θ c v := by
  sorry

section M1canon
variable [NeZero N]

/-- Eq. `loss_equivariance`. -/
theorem lossInst_perm (pm : Equiv.Perm (Fin N)) (θ : Params N) :
    lossInst N K pm (permP pm θ) = lossInst N K 1 θ := by
  sorry

/-- Step 2: the averaged loss is invariant. -/
theorem lossTrain_perm (pm : Equiv.Perm (Fin N)) (θ : Params N) :
    lossTrain N K (permP pm θ) = lossTrain N K θ := by
  sorry

/-- Step 3: the fixed points of the action are exactly the eight-scalar family `F`. -/
theorem fixed_iff (θ : Params N) : (∀ pm : Equiv.Perm (Fin N), permP pm θ = θ) ↔ ∃ s, θ = iota s := by
  sorry

/-- Step 4: on `F` the averaged loss equals the loss of one instance. -/
theorem lossTrain_iota (s : Fin 8 → ℝ) : lossTrain N K (iota s) = lossInst N K 1 (iota s) := by
  sorry

theorem gInst_perm (pm : Equiv.Perm (Fin N)) (θ : Params N) (σ : Params N → ℝ) :
    gInst N K pm (permP pm θ) σ = permP pm (gInst N K 1 θ (σ ∘ permP pm)) := by
  sorry

/-- Step 3: the generalized gradient is equivariant, `∂L(π·θ) = π·∂L(θ)`. -/
theorem VelM_perm (α : ℝ) (pm : Equiv.Perm (Fin N)) (θ : Params N) :
    VelM N K α (permP pm θ) = permP pm '' VelM N K α θ := by
  sorry

end M1canon

/-! ## M2. Lemma C.1 and the flow statement of Prop. 4.1 -/

section M2
variable [NeZero N]

theorem Sel_iota (s : Fin 8 → ℝ) (σ : (Fin 8 → ℝ) → ℝ) (hσ : Sel8 s σ) :
    Sel (iota (N := N) s) (σ ∘ iotaT) := by
  sorry

/-- **Lemma C.1.** On `F`, the generalized gradient of the averaged loss is
`(1/N) ∂ℓ/∂a · I + (1/(N(N-1))) ∂ℓ/∂b · E_off` (and likewise for each matrix). -/
theorem gTrain_iota (hN : 2 ≤ N) (s : Fin 8 → ℝ) (σ : (Fin 8 → ℝ) → ℝ) :
    gTrain N K (iota s) (σ ∘ iotaT) = iota (fun m => P8 N m * g8 N K s σ m) := by
  sorry

/-- **Prop. 4.1** (flow part): a solution of the eight-scalar flow, embedded in `F`, is a solution
of the full matrix-level gradient flow. -/
theorem IsSol8.iota (hN : 2 ≤ N) {α : ℝ} {s : ℝ → Fin 8 → ℝ} (hs : IsSol8 N K α s) :
    IsMatSol N K α (fun t => iota (s t)) := by
  sorry

end M2

/-! ## D. The selection gradient is the derivative wherever the loss is smooth -/

section smooth
variable [NeZero N]

theorem lossInst_hasFDerivAt (pm : Equiv.Perm (Fin N)) (θ : Params N) (σ : Params N → ℝ)
    (hσ : Sel θ σ) (hθ : SmoothInst N K pm θ) :
    HasFDerivAt (lossInst N K pm) (pairL (gInst N K pm θ σ)) θ := by
  sorry

theorem lossTrain_hasFDerivAt (θ : Params N) (σ : Params N → ℝ) (hσ : Sel θ σ)
    (hθ : ∀ pm, SmoothInst N K pm θ) :
    HasFDerivAt (lossTrain N K) (pairL (gTrain N K θ σ)) θ := by
  sorry

theorem loss8_hasFDerivAt (s : Fin 8 → ℝ) (σ : (Fin 8 → ℝ) → ℝ) (hσ : Sel8 s σ)
    (hs : SmoothInst N K 1 (iota s)) :
    HasFDerivAt (fun s' => lossInst N K 1 (iota s')) (dotL (g8 N K s σ)) s := by
  sorry

end smooth

/-! ## T. Node-logit tables (App. C, Tables 1–2) for permutation-invariant parameters -/

theorem logit_of_ne (θ : Params N) (c : Ctx N) (v : Fin N) (hv : v ≠ c.cur) :
    logit θ c v = max (head1 θ c v) 0 + max (head2 θ c v) 0 := by
  sorry

/-- Forward head (Table 1): `(head₁)_v = b₂ d_v^in + (a₂ - b₂)·[n_t → v] - m_v·A₁[v, n_t]`. -/
theorem head1_iota (s : Fin 8 → ℝ) (c : Ctx N) (v : Fin N) :
    head1 (iota s) c v =
      s 3 * c.din v + (s 2 - s 3) * c.ecnt c.cur v - c.mcnt v * (if v = c.cur then s 0 else s 1) := by
  sorry

/-- Backtracking head (Table 2, `v ≠ n_t`):
`(head₂)_v = (g₁ - d₁) A_{v→n_t} - (g₂ - d₂) A_{n_t→v} + d₂·[v = n_Root]`. -/
theorem head2_iota (s : Fin 8 → ℝ) (c : Ctx N) (v : Fin N) (hv : v ≠ c.cur) :
    head2 (iota s) c v =
      (s 4 - s 5) * c.trans v c.cur - (s 6 - s 7) * c.trans c.cur v +
        (if v = c.root then s 7 else 0) := by
  sorry

/-! ## C. Gradient of the canonical loss on the region `R` (Lemma C.2, Step 2) -/

section canonGrad
variable [NeZero N]

/-- Eqs. `grad_R_a1` – `grad_R_d2`, with `σ cu8, σ cv8, σ cb8, σ cd8` the selected values of
`𝟙{u ≥ 0}, 𝟙{v ≥ 0}, 𝟙{b₂ ≥ 0}, 𝟙{d₂ ≥ 0}`, on `R' = {b₁ > 0, b₂ < b₁, a₂ > 0, g₁ - d₁ > 0}`. -/
theorem g8_on_R (hK : 2 ≤ K) (hN : K + 5 ≤ N) (s : Fin 8 → ℝ) (σ : (Fin 8 → ℝ) → ℝ)
    (hσ : Sel8 s σ) (hb1 : 0 < s 1) (hb2 : s 3 < s 1) (ha2 : 0 < s 2) (hy : 0 < s 4 - s 5) :
    g8 N K s σ = ![0,
      -(∑ j ∈ range K, (j : ℝ) * E8 s * σ cu8 / Q2 N K s j) - (K : ℝ) * E8 s * σ cu8 / Q4 N K s,
      -1 + exp (s 2) / Q1 N K s
        + ∑ j ∈ range K, (-1 + (((K : ℝ) - j) * exp (s 2) + (j : ℝ) * E8 s * σ cu8) / Q2 N K s j)
        + (K : ℝ) * E8 s * σ cu8 / Q4 N K s,
      eb8 s * σ cb8 * ((K : ℝ) / Q1 N K s + ∑ j ∈ range K, ((K : ℝ) - 1 - j) / Q3 N K s j),
      exp (s 4 - s 5) / Q1 N K s
        + ∑ j ∈ range K, ((j : ℝ) * E8 s * σ cv8 + exp (s 4 - s 5)) / Q2 N K s j
        + ∑ j ∈ range K, (-1 + exp (s 4 - s 5) / Q3 N K s j)
        - 1 + ((K : ℝ) * E8 s * σ cv8 + exp (s 4 - s 5)) / Q4 N K s,
      -(exp (s 4 - s 5) / Q1 N K s
        + ∑ j ∈ range K, ((j : ℝ) * E8 s * σ cv8 + exp (s 4 - s 5)) / Q2 N K s j
        + ∑ j ∈ range K, (-1 + exp (s 4 - s 5) / Q3 N K s j)
        - 1 + ((K : ℝ) * E8 s * σ cv8 + exp (s 4 - s 5)) / Q4 N K s),
      -(∑ j ∈ range K, (j : ℝ) * E8 s * σ cv8 / Q2 N K s j) - (K : ℝ) * E8 s * σ cv8 / Q4 N K s,
      (∑ j ∈ range K, (j : ℝ) * E8 s * σ cv8 / Q2 N K s j) + (K : ℝ) * E8 s * σ cv8 / Q4 N K s
        + ed8 s * σ cd8 * (1 / Q1 N K s + ∑ j ∈ range K, 1 / Q2 N K s j
            + ∑ j ∈ range K, 1 / Q3 N K s j + 1 / Q4 N K s)] := by
  sorry

/-- Eq. `grad_bound`: on `R'` every partial derivative is at most `2K + 2` in absolute value. -/
theorem g8_bound_on_R (hK : 2 ≤ K) (hN : K + 5 ≤ N) (s : Fin 8 → ℝ) (σ : (Fin 8 → ℝ) → ℝ)
    (hσ : Sel8 s σ) (hb1 : 0 < s 1) (hb2 : s 3 < s 1) (ha2 : 0 < s 2) (hy : 0 < s 4 - s 5)
    (m : Fin 8) : |g8 N K s σ m| ≤ 2 * K + 2 := by
  sorry

end canonGrad

/-! ## L. Lemma C.2: invariant region and initial phase -/

section lemmaC2
variable [NeZero N]

/-- Lemma C.2, item 1 (region; `b₂ ∈ [0, c₀']` since `b₂` freezes at `0`). -/
theorem lemmaC2_region (hK : 2 ≤ K) (hN : K + 5 ≤ N) {c0 c0' α : ℝ} (h0 : 0 < c0')
    (h1 : c0' < c0) (hα : 0 < α) {s : ℝ → Fin 8 → ℝ} (hs : IsSol8 N K α s)
    (hs0 : s 0 = init8 c0 c0') :
    ∀ t ≥ 0, s t 0 = c0 ∧ c0 ≤ s t 1 ∧ 0 ≤ s t 3 ∧ s t 3 ≤ c0' ∧ s t 1 ≤ s t 2 ∧
      0 < s t 4 - s t 5 ∧ 0 ≤ s t 6 - s t 7 ∧ s t 7 ≤ c0 := by
  sorry

/-- Lemma C.2, item 1 (monotonicity): `b₁ ↑`, `b₂ ↓`, `g₂ - d₂ ↑`, `d₂ ↓`. -/
theorem lemmaC2_mono (hK : 2 ≤ K) (hN : K + 5 ≤ N) {c0 c0' α : ℝ} (h0 : 0 < c0')
    (h1 : c0' < c0) (hα : 0 < α) {s : ℝ → Fin 8 → ℝ} (hs : IsSol8 N K α s)
    (hs0 : s 0 = init8 c0 c0') :
    ∀ t₁ t₂, 0 ≤ t₁ → t₁ ≤ t₂ → s t₁ 1 ≤ s t₂ 1 ∧ s t₂ 3 ≤ s t₁ 3 ∧
      s t₁ 6 - s t₁ 7 ≤ s t₂ 6 - s t₂ 7 ∧ s t₂ 7 ≤ s t₁ 7 := by
  sorry

/-- Speed bound from eq. `grad_bound` and eq. `scalar_flow`. -/
theorem lemmaC2_lip (hK : 2 ≤ K) (hN : K + 5 ≤ N) {c0 c0' α : ℝ} (h0 : 0 < c0')
    (h1 : c0' < c0) (hα : 0 < α) {s : ℝ → Fin 8 → ℝ} (hs : IsSol8 N K α s)
    (hs0 : s 0 = init8 c0 c0') :
    ∀ t₁ t₂, 0 ≤ t₁ → t₁ ≤ t₂ → ∀ m, |s t₂ m - s t₁ m| ≤ (2 * K + 2) * α * P8 N m * (t₂ - t₁) := by
  sorry

end lemmaC2

/-- Lemma C.2, item 2 (initial phase): after `T₀`, `b₂ = 0` and `d₂ ≤ 0`. -/
theorem lemmaC2_initial (hK : 2 ≤ K) :
    ∃ cstar : ℝ, 0 < cstar ∧ ∀ (N : ℕ) [NeZero N], K + 5 ≤ N →
      ∀ c0 c0' α : ℝ, 0 < c0' → c0' < c0 → c0 ≤ cstar / (N : ℝ) ^ 2 → 0 < α →
      ∀ s : ℝ → Fin 8 → ℝ, IsSol8 N K α s → s 0 = init8 c0 c0' →
      ∀ t ≥ T0 N K α, s t 3 = 0 ∧ s t 7 ≤ 0 := by
  sorry

/-! ## R. Cor. C.3: reduction to the four-variable system of Stage 1 -/

/-- **Cor. C.3.** After `T₀` the aggregated variables solve the Stage 1 system (as a Filippov
solution), from a state in `[0, 2]⁴` with `u ≥ 0`; and the recovery identities hold. -/
theorem corC3 [NeZero N] (hK : 2 ≤ K) (hN : K + 5 ≤ N) {c0 c0' α : ℝ} (h0 : 0 < c0')
    (h1 : c0' < c0) (hc0 : c0 ≤ 1 / 2) (hα : 0 < α) {s : ℝ → Fin 8 → ℝ} (hs : IsSol8 N K α s)
    (hs0 : s 0 = init8 c0 c0') (hT0 : ∀ t ≥ T0 N K α, s t 3 = 0 ∧ s t 7 ≤ 0) :
    IsSol N K α (fun t => proj (s (T0 N K α + t))) ∧ Init 2 (proj (s (T0 N K α))) ∧
    (∀ t ≥ 0, s t 4 + ((N : ℝ) - 1) * s t 5 = c0 + ((N : ℝ) - 1) * c0') ∧
    ∃ κ : ℝ, |κ - N * c0| ≤ 1 ∧ ∀ t ≥ T0 N K α, s t 6 + ((N : ℝ) - 1) * s t 7 = κ := by
  sorry

/-! ## S. DFS traces and the generalization loss (proof of Thm 4.2, second part) -/

/-- A valid DFS trace on `N` vertices has at most `2(N-1)` steps. -/
theorem trace_length_le (E : List (Fin N × Fin N)) (tgt root : Fin N) (τ : List (Fin N))
    (hτ : ValidTrace E tgt root τ) : τ.length ≤ 2 * (N - 1) := by
  sorry

/-- Generalization loss bound in terms of the scalars (eq. `gen_normalizer` and Cases 1–3). -/
theorem genLoss_bound (hN : 2 ≤ N) (Cu Cv : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : Fin 8 → ℝ, s 3 = 0 → s 7 ≤ 0 → 0 < s 1 → 0 ≤ s 2 - s 1 →
      s 2 - s 1 ≤ Cu → s 4 - s 5 - (s 6 - s 7) ≤ Cv → 0 ≤ s 4 - s 5 →
      ∀ (E : List (Fin N × Fin N)) (tgt root : Fin N) (τ : List (Fin N)), E.Nodup →
        ValidTrace E tgt root τ →
        genLoss (iota s) E tgt root τ ≤
          C * (exp (s 4 - s 5 - s 2) + exp (-s 2) + exp (-(s 4 - s 5)) +
            exp (-(s 4 - s 5 + s 7))) := by
  sorry

/-! ## F. Theorem 4.2 -/

/-- **Theorem 4.2** (`thm:learning_dynamics`). For the eight-scalar gradient flow from the
initialization (by `IsSol8.iota` its embedding in `F` solves the matrix-level flow; matrix-level
solutions that leave `F` are not covered, as in the paper):
`a₂, b₁ = 2 log(αt) + O(1)`, `g₁ - d₁ = log(αt) + O(1)`, `|g₁ - d₁ - g₂ + d₂| ≤ C`, the individual
rates of `g₁, g₂, d₁, d₂`, and `ℒ_gen ≤ C_{N,K} (αt)^{-(N-1)/N}` for `t ≥ t*/α`. All constants depend
only on `N, K, c₀, c₀'`. -/
theorem learning_dynamics (hK : 2 ≤ K) :
    ∃ cstar : ℝ, 0 < cstar ∧ ∀ (N : ℕ) [NeZero N], K + 5 ≤ N →
      ∀ c0 c0' : ℝ, 0 < c0' → c0' < c0 → c0 ≤ cstar / (N : ℝ) ^ 2 →
      ∃ C Cgen tstar : ℝ, ∀ α > 0, ∀ s : ℝ → Fin 8 → ℝ, IsSol8 N K α s → s 0 = init8 c0 c0' →
        (∀ t ≥ tstar / α, |s t 2 - 2 * log (α * t)| ≤ C ∧ |s t 1 - 2 * log (α * t)| ≤ C ∧
          |s t 4 - s t 5 - log (α * t)| ≤ C) ∧
        (∀ t ≥ 0, |s t 4 - s t 5 - (s t 6 - s t 7)| ≤ C) ∧
        (∀ t ≥ tstar / α, |s t 4 - ((N : ℝ) - 1) / N * log (α * t)| ≤ C ∧
          |s t 6 - ((N : ℝ) - 1) / N * log (α * t)| ≤ C ∧
          |s t 5 + log (α * t) / N| ≤ C ∧ |s t 7 + log (α * t) / N| ≤ C) ∧
        (∀ t ≥ tstar / α, ∀ (E : List (Fin N × Fin N)) (tgt root : Fin N) (τ : List (Fin N)),
          E.Nodup → ValidTrace E tgt root τ →
          genLoss (iota (s t)) E tgt root τ ≤ Cgen * (α * t) ^ (-(((N : ℝ) - 1) / N))) := by
  sorry

/-! Sanity checks of the definitions (help for the work packages). -/

example [NeZero N] : (tau0 N K).length = 2 * K + 2 := by
  simp [tau0]; ring

example (s : Fin 8 → ℝ) (i j : Fin N) : iota s 1 i j = if i = j then s 2 else s 3 := by
  simp [iota, sym]

end DFS.Spec
