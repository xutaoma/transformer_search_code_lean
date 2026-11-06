import DFSLean.Defs

/-!
# Frozen Stage 1 specification (all `sorry`; checked against the proofs in `SpecCheck.lean`): Lemma C.4 and Theorem C.5 of the DFS paper

This file is the frozen interface for the parallel proof work. Every theorem here is proved in
its own work file (`DFSLean/Work/*.lean`), which may use any *earlier* statement of this file.

Conventions.
* State `z = (x₁, x₂, y₁, y₂)`, `z 0 = x₁`, `z 1 = x₂`, `z 2 = y₁`, `z 3 = y₂`.
* Time is shifted so that the paper's `T₀` is `0`.
* Items of Thm C.5 are proved for learning rate `α = 1`; `IsSol.rescale` transfers them to every
  `α > 0` (paper l.1187), which is why the final constants do not depend on `α`.
* Constants are uniform over **all** solutions whose initial state lies in `[0, R]⁴`
  (`Init R`), not just per solution. This is stronger than the paper's statement and is what the
  end-to-end Thm 4.2 needs (constants independent of `α` and of the choice of Filippov solution).
* Lyapunov exponent: the paper takes any `3 - 1/N < p < 1 + 2N/(N-1)`; we fix `p = 3`, so
  `log W = 2 y₁ - x₁ + 3 (x₁ - x₂) = 2 x₁ - 3 x₂ + 2 y₁` (linear in `z`).
-/

noncomputable section
open Real Filter Topology Set

namespace DFS.Spec

variable {N K : ℕ}

/-! ## Basic infrastructure (work package A) -/

/-- Every component of the field is bounded (each fraction in Cor. C.3 is at most 1). -/
theorem F_bound (hK : 2 ≤ K) (hN : K + 5 ≤ N) {α θ η : ℝ} (hα : 0 ≤ α)
    (hθ : θ ∈ Icc (0 : ℝ) 1) (hη : η ∈ Icc (0 : ℝ) 1) (z : Fin 4 → ℝ) (i : Fin 4) :
    |F N K α θ η z i| ≤ (K + 2) * α := by
  sorry

/-- Solutions are Lipschitz with the constant of `F_bound`. -/
theorem IsSol.lipschitz (hK : 2 ≤ K) (hN : K + 5 ≤ N) {α : ℝ} (hα : 0 ≤ α)
    {z : ℝ → Fin 4 → ℝ} (hz : IsSol N K α z) (i : Fin 4) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    |z t i - z s i| ≤ (K + 2) * α * (t - s) := by
  sorry

/-- Right difference quotients of two linear functionals are simultaneously close to the
values on one admissible velocity. -/
theorem IsSol.slope_lin₂ {α : ℝ} {z : ℝ → Fin 4 → ℝ} (hz : IsSol N K α z) (c d : Fin 4 → ℝ)
    {t : ℝ} (ht : 0 ≤ t) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), ∃ θ η, Adm (z t) θ η ∧
      |(lin c (z (t + h)) - lin c (z t)) / h - lin c (F N K α θ η (z t))| < ε ∧
      |(lin d (z (t + h)) - lin d (z t)) / h - lin d (F N K α θ η (z t))| < ε := by
  sorry

/-- One-sided barrier (weak form). If, whenever `ℓ = lin c ∘ z` is above the level `L`, every
admissible velocity has `ℓ' ≤ 0`, then `ℓ` never rises above `max (ℓ a) L`. -/
theorem IsSol.barrier {α : ℝ} {z : ℝ → Fin 4 → ℝ} (hz : IsSol N K α z) (c : Fin 4 → ℝ) (L : ℝ)
    {a b : ℝ} (ha : 0 ≤ a)
    (h : ∀ t ∈ Ico a b, L < lin c (z t) →
      ∀ θ η, Adm (z t) θ η → lin c (F N K α θ η (z t)) ≤ 0) :
    ∀ t ∈ Icc a b, lin c (z t) ≤ max (lin c (z a)) L := by
  sorry

/-- Reaching a level. If `ℓ' ≥ δ > 0` for every admissible velocity whenever `ℓ < L` (and
`t ≥ a`), then `ℓ ≥ L` from time `a + (L - ℓ a) / δ` on. -/
theorem IsSol.reach {α : ℝ} {z : ℝ → Fin 4 → ℝ} (hz : IsSol N K α z) (c : Fin 4 → ℝ)
    (L δ : ℝ) (hδ : 0 < δ) {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ t ≥ a, lin c (z t) < L →
      ∀ θ η, Adm (z t) θ η → δ ≤ lin c (F N K α θ η (z t))) :
    ∀ t ≥ a, a + (L - lin c (z a)) / δ ≤ t → L ≤ lin c (z t) := by
  sorry

/-- Time rescaling (paper l.1187): a solution for learning rate `α` run at time `s / α` is a
solution for learning rate `1`. -/
theorem IsSol.rescale {α : ℝ} (hα : 0 < α) {z : ℝ → Fin 4 → ℝ} (hz : IsSol N K α z) :
    IsSol N K 1 (fun s => z (s / α)) := by
  sorry

/-- `x₂` is non-decreasing (`x₂' ≥ 0` for every selection). -/
theorem IsSol.mono_x2 (hK : 2 ≤ K) (hN : K + 5 ≤ N) {z : ℝ → Fin 4 → ℝ} (hz : IsSol N K 1 z)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : z s 1 ≤ z t 1 := by
  sorry

/-- `y₂` is non-decreasing (`y₂' ≥ 0` for every selection). -/
theorem IsSol.mono_y2 (hK : 2 ≤ K) (hN : K + 5 ≤ N) {z : ℝ → Fin 4 → ℝ} (hz : IsSol N K 1 z)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : z s 3 ≤ z t 3 := by
  sorry

/-- Invariant region (paper l.443–461 for `u ≥ 0`): `u ≥ 0`, `x₂ ≥ 0`, `y₁ ≥ 0`, `y₂ ≥ 0`
persist. (`y₁ ≥ 0`: on `{y₁ < 0}` we have `v < 0`, hence `η = 0` and `y₁' > 0`.) -/
theorem IsSol.good (hK : 2 ≤ K) (hN : K + 5 ≤ N) {z : ℝ → Fin 4 → ℝ} (hz : IsSol N K 1 z)
    (h0 : Good (z 0)) : ∀ t ≥ 0, Good (z t) := by
  sorry

/-! ## Lemma C.4, logarithmic growth (work package B)

Measure-free restatement: the a.e. ODEs `X' = a e^{Y-X}`, `Y' = b e^{-Y} - ã e^{Y-X} + r` are
replaced by "right difference quotients approach the admissible velocities"; only
`β = b + e^Y r` enters, so `Y' = β e^{-Y} - ã e^{Y-X}`. -/

/-- Lemma C.4 (`lemma:log_growth`), two-sided bounds on `Θ = e^{2Y-X}` and on `e^{X/2}`. -/
theorem log_growth {t₀ : ℝ} {X Y : ℝ → ℝ} {aLo aHi ãLo ãHi βLo βHi c C : ℝ}
    (ha : 0 < aLo) (ha' : aLo ≤ aHi) (hã : 0 < ãLo) (hã' : ãLo ≤ ãHi)
    (hβ : 0 < βLo) (hβ' : βLo ≤ βHi)
    (hXc : ContinuousOn X (Ici t₀)) (hYc : ContinuousOn Y (Ici t₀))
    (hslope : ∀ t ≥ t₀, ∀ ε > 0, ∀ᶠ h in 𝓝[>] (0 : ℝ),
      ∃ a ∈ Icc aLo aHi, ∃ ã ∈ Icc ãLo ãHi, ∃ β ∈ Icc βLo βHi,
        |(X (t + h) - X t) / h - a * exp (Y t - X t)| < ε ∧
        |(Y (t + h) - Y t) / h - (β * exp (-Y t) - ã * exp (Y t - X t))| < ε)
    (hc : c = min (exp (2 * Y t₀ - X t₀)) (2 * βLo / (aHi + 2 * ãHi)))
    (hC : C = max (exp (2 * Y t₀ - X t₀)) (2 * βHi / (aLo + 2 * ãLo))) :
    ∀ t ≥ t₀,
      c ≤ exp (2 * Y t - X t) ∧ exp (2 * Y t - X t) ≤ C ∧
      exp (X t₀ / 2) + aLo * sqrt c / 2 * (t - t₀) ≤ exp (X t / 2) ∧
      exp (X t / 2) ≤ exp (X t₀ / 2) + aHi * sqrt C / 2 * (t - t₀) := by
  sorry

/-- Lemma C.4, "in particular" part, with the constant uniform over initial values
`|X t₀|, |Y t₀| ≤ M` (it depends only on `t₀`, `M` and the coefficient bounds). -/
theorem log_growth_asymp {t₀ M aLo aHi ãLo ãHi βLo βHi : ℝ} (ht₀ : 1 ≤ t₀)
    (ha : 0 < aLo) (ha' : aLo ≤ aHi) (hã : 0 < ãLo) (hã' : ãLo ≤ ãHi)
    (hβ : 0 < βLo) (hβ' : βLo ≤ βHi) :
    ∃ C' : ℝ, ∀ X Y : ℝ → ℝ, ContinuousOn X (Ici t₀) → ContinuousOn Y (Ici t₀) →
      (∀ t ≥ t₀, ∀ ε > 0, ∀ᶠ h in 𝓝[>] (0 : ℝ),
        ∃ a ∈ Icc aLo aHi, ∃ ã ∈ Icc ãLo ãHi, ∃ β ∈ Icc βLo βHi,
          |(X (t + h) - X t) / h - a * exp (Y t - X t)| < ε ∧
          |(Y (t + h) - Y t) / h - (β * exp (-Y t) - ã * exp (Y t - X t))| < ε) →
      |X t₀| ≤ M → |Y t₀| ≤ M →
      ∀ t ≥ 2 * t₀, |X t - 2 * log t| ≤ C' ∧ |Y t - log t| ≤ C' := by
  sorry

/-! ## Theorem C.5 (`thm:four_parameter_log_convergence`), items for `α = 1` -/

/-- Item 1 (work package C): `v₊` is bounded. Paper l.466–570. -/
theorem item1 (hK : 2 ≤ K) (hN : K + 5 ≤ N) (R : ℝ) :
    ∃ Cv : ℝ, ∀ z : ℝ → Fin 4 → ℝ, IsSol N K 1 z → Init R (z 0) → ∀ t ≥ 0, v (z t) ≤ Cv := by
  sorry

/-- Item 2 (work package D), quantitative and uniform: `x₁, y₁, y₂ → ∞`. Paper l.572–592.
(`x₂ → ∞` follows from item 3 and is part of the final theorem.) -/
theorem item2 (hK : 2 ≤ K) (hN : K + 5 ≤ N) (R B : ℝ) :
    ∃ T : ℝ, ∀ z : ℝ → Fin 4 → ℝ, IsSol N K 1 z → Init R (z 0) →
      ∀ t ≥ T, B ≤ z t 0 ∧ B ≤ z t 2 ∧ B ≤ z t 3 := by
  sorry

/-- Lyapunov estimate in state space (work package E), paper l.596–988 with `p = 3`:
once `y₁ ≥ B₀` and `log W = 2x₁ - 3x₂ + 2y₁` exceeds `CW`, every admissible velocity
(interior `u > 0` and boundary `u = 0`, any `θ, η`) has `(log W)' ≤ 0`. -/
theorem lyapunov_state (hK : 2 ≤ K) (hN : K + 5 ≤ N) (Cv : ℝ) :
    ∃ B₀ CW : ℝ, ∀ z : Fin 4 → ℝ, Good z → v z ≤ Cv → B₀ ≤ z 2 →
      CW < lin ![2, -3, 2, 0] z →
      ∀ θ η, Adm z θ η → lin ![2, -3, 2, 0] (F N K 1 θ η z) ≤ 0 := by
  sorry

/-- Item 3 (work package C): `2y₁ - x₁` and `u = x₁ - x₂` are bounded above.
Paper l.596–1065. -/
theorem item3 (hK : 2 ≤ K) (hN : K + 5 ≤ N) (R : ℝ) :
    ∃ CZ Cu : ℝ, ∀ z : ℝ → Fin 4 → ℝ, IsSol N K 1 z → Init R (z 0) →
      ∀ t ≥ 0, 2 * z t 2 - z t 0 ≤ CZ ∧ u (z t) ≤ Cu := by
  sorry

/-- Coefficient bounds for Lemma C.4 in state space (work package F1), paper l.1067–1173:
with `X = lin (Xc N) z` and `Y = y₁`, every admissible velocity has
`X' = a e^{Y-X}` and `Y' = β e^{-Y} - ã e^{Y-X}` with `a, ã, β` in fixed positive ranges. -/
theorem growth_coeffs (hK : 2 ≤ K) (hN : K + 5 ≤ N) (Cv Cu CZ : ℝ) :
    ∃ B₀ aLo aHi ãLo ãHi βLo βHi : ℝ, 0 < aLo ∧ aLo ≤ aHi ∧ 0 < ãLo ∧ ãLo ≤ ãHi ∧ 0 < βLo ∧ βLo ≤ βHi ∧
      ∀ z : Fin 4 → ℝ, Good z → v z ≤ Cv → u z ≤ Cu → 2 * z 2 - z 0 ≤ CZ → B₀ ≤ z 2 →
      ∀ θ η, Adm z θ η →
        ∃ a ∈ Icc aLo aHi, ∃ ã ∈ Icc ãLo ãHi, ∃ β ∈ Icc βLo βHi,
          lin (Xc N) (F N K 1 θ η z) = a * exp (z 2 - lin (Xc N) z) ∧
          F N K 1 θ η z 2 = β * exp (-z 2) - ã * exp (z 2 - lin (Xc N) z) := by
  sorry

/-- Item 4 for `α = 1` (work package F2): logarithmic rates. Paper l.1067–1214. -/
theorem item4 (hK : 2 ≤ K) (hN : K + 5 ≤ N) (R : ℝ) :
    ∃ C T : ℝ, ∀ z : ℝ → Fin 4 → ℝ, IsSol N K 1 z → Init R (z 0) → ∀ t ≥ T,
      |z t 0 - 2 * log t| ≤ C ∧ |z t 1 - 2 * log t| ≤ C ∧
      |z t 2 - log t| ≤ C ∧ |z t 3 - log t| ≤ C := by
  sorry

/-! ## Theorem C.5, final form (work package F2) -/

/-- **Theorem C.5** (`thm:four_parameter_log_convergence`). For every learning rate `α > 0` and
every Filippov solution starting (at the shifted time `T₀ = 0`) in `[0, R]⁴` with `u ≥ 0`:
1. `v₊` is bounded; 2. all four coordinates tend to `∞`; 3. `2y₁ - x₁` and `x₁ - x₂` are bounded
above; 4. `x₁, x₂ = 2 log (α t) + O(1)` and `y₁, y₂ = log (α t) + O(1)`.
All constants depend only on `N`, `K`, `R`; not on `α` and not on the solution. -/
theorem four_parameter_log_convergence (hK : 2 ≤ K) (hN : K + 5 ≤ N) (R : ℝ) :
    ∃ Cv CZ Cu C T : ℝ, ∀ α > 0, ∀ z : ℝ → Fin 4 → ℝ, IsSol N K α z → Init R (z 0) →
      (∀ t ≥ 0, max (v (z t)) 0 ≤ Cv) ∧
      (∀ i, Tendsto (fun t => z t i) atTop atTop) ∧
      (∀ t ≥ 0, 2 * z t 2 - z t 0 ≤ CZ ∧ u (z t) ≤ Cu) ∧
      (∀ t ≥ T / α,
        |z t 0 - 2 * log (α * t)| ≤ C ∧ |z t 1 - 2 * log (α * t)| ≤ C ∧
        |z t 2 - log (α * t)| ≤ C ∧ |z t 3 - log (α * t)| ≤ C) := by
  sorry

/-! Unfolding sanity checks (help for the work packages). -/

example (α θ η : ℝ) (z : Fin 4 → ℝ) :
    lin ![1, -1, 0, 0] (F N K α θ η z) = F N K α θ η z 0 - F N K α θ η z 1 := by
  simp [lin]; ring

example (z : Fin 4 → ℝ) : lin ![2, -3, 2, 0] z = 2 * z 2 - z 0 + 3 * u z := by
  simp [lin, u]; ring

example (z : Fin 4 → ℝ) : lin (Xc N) z = (z 0 + ((N : ℝ) - 1) * z 1) / N := by
  simp [lin, Xc]; ring

end DFS.Spec
