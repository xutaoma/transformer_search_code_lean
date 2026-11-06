import DFSLean.Basic
import DFSLean.LogGrowth
import DFSLean.Item1
import DFSLean.Item2
import DFSLean.Item3
import DFSLean.Coeffs

/-!
# Work package F2: Theorem C.5 item 4 (`α = 1`) and the final theorem

Paper l.1067–1214. Item 4 combines the coefficient bounds `growth_coeffs` (F1) with the uniform
form of Lemma C.4 (`log_growth_asymp`), and handles `y₂` via item 1 (lower bound) and a barrier
(upper bound). The final theorem transfers items 1–4 to every `α > 0` by time rescaling.
-/

namespace DFS

open Real Filter Topology Set

variable {N K : ℕ}

private lemma F2_lin_e2 (w : Fin 4 → ℝ) : lin ![0, 0, 1, 0] w = w 2 := by
  simp [lin]

private lemma F2_lin_e3 (w : Fin 4 → ℝ) : lin ![0, 0, 0, 1] w = w 3 := by
  simp [lin]

private lemma F2_lin_Xc (n : ℕ) (w : Fin 4 → ℝ) :
    lin (Xc n) w = (w 0 + ((n : ℝ) - 1) * w 1) / n := by
  simp [lin, Xc]; ring

/-- On `{v < 0}` the `y₂`-component of the field vanishes (every term carries `η = 0`). -/
private lemma F2_F3_zero {α θ η : ℝ} {w : Fin 4 → ℝ} (hadm : Adm w θ η) (hv : v w < 0) :
    F N K α θ η w 3 = 0 := by
  have hη : η = 0 := hadm.2.2.2.2.2 hv
  subst hη
  simp [F]

/-- Coordinates of a solution in the invariant region are nonnegative. -/
private lemma F2_nonneg {w : Fin 4 → ℝ} (h : Good w) (i : Fin 4) : 0 ≤ w i := by
  obtain ⟨hu, h1, h2, h3⟩ := h
  unfold u at hu
  fin_cases i
  · show 0 ≤ w 0; linarith
  · exact h1
  · exact h2
  · exact h3

theorem item4 (hK : 2 ≤ K) (hN : K + 5 ≤ N) (R : ℝ) :
    ∃ C T : ℝ, ∀ z : ℝ → Fin 4 → ℝ, IsSol N K 1 z → Init R (z 0) → ∀ t ≥ T,
      |z t 0 - 2 * log t| ≤ C ∧ |z t 1 - 2 * log t| ≤ C ∧
      |z t 2 - log t| ≤ C ∧ |z t 3 - log t| ≤ C := by
  obtain ⟨Cv, hCv⟩ := DFS.item1 hK hN R
  obtain ⟨CZ, Cu, hCZu⟩ := DFS.item3 hK hN R
  obtain ⟨B₀, aLo, aHi, ãLo, ãHi, βLo, βHi, ha, ha', hã, hã', hβ, hβ', hcoef⟩ :=
    DFS.growth_coeffs hK hN Cv Cu CZ
  obtain ⟨T₁, hT₁⟩ := DFS.item2 hK hN R B₀
  set t₀ : ℝ := max T₁ 1 with ht₀_def
  have ht₀1 : 1 ≤ t₀ := le_max_right _ _
  have ht₀0 : 0 ≤ t₀ := by linarith
  set M : ℝ := R + ((K : ℝ) + 2) * t₀ with hM_def
  obtain ⟨C', hC'⟩ := DFS.log_growth_asymp (t₀ := t₀) (M := M) ht₀1 ha ha' hã hã' hβ hβ'
  set M' : ℝ := R + ((K : ℝ) + 2) * (2 * t₀) with hM'_def
  have hN7 : (7 : ℝ) ≤ N := by
    have : 7 ≤ N := by omega
    exact_mod_cast this
  have hn : (0 : ℝ) < N := by linarith
  have hK0 : (0 : ℝ) ≤ (K : ℝ) + 2 := by positivity
  refine ⟨|C'| + |Cu| + |Cv| + |R| + |M'|, 2 * t₀, ?_⟩
  intro z hz hinit t ht
  have hgood : ∀ s ≥ 0, Good (z s) := hz.good hK hN hinit.1
  -- Lipschitz upper bound on every coordinate
  have hup : ∀ i, ∀ s ≥ 0, z s i ≤ R + ((K : ℝ) + 2) * s := by
    intro i s hs
    have h1 := (abs_le.mp (hz.lipschitz hK hN zero_le_one i le_rfl hs)).2
    have h2 := hinit.2 i
    linarith
  -- the averaged variable and `Y = y₁`
  set X : ℝ → ℝ := fun s => lin (Xc N) (z s) with hX_def
  set Y : ℝ → ℝ := fun s => z s 2 with hY_def
  have hzi : ∀ i, ContinuousOn (fun s => z s i) (Ici t₀) := fun i =>
    ((continuous_apply i).comp_continuousOn hz.1).mono (Ici_subset_Ici.mpr ht₀0)
  have hXc : ContinuousOn X (Ici t₀) := by
    simp only [hX_def, lin]
    exact (((continuousOn_const.mul (hzi 0)).add (continuousOn_const.mul (hzi 1))).add
      (continuousOn_const.mul (hzi 2))).add (continuousOn_const.mul (hzi 3))
  have hYc : ContinuousOn Y (Ici t₀) := hzi 2
  -- `n X = x₁ + (n-1) x₂`
  have hXe : ∀ s, (N : ℝ) * X s = z s 0 + ((N : ℝ) - 1) * z s 1 := by
    intro s
    simp only [hX_def, F2_lin_Xc]
    field_simp
  -- uniform initial bounds at `t₀`
  have hz0 : ∀ i, 0 ≤ z t₀ i ∧ z t₀ i ≤ M := fun i =>
    ⟨F2_nonneg (hgood t₀ ht₀0) i, hup i t₀ ht₀0⟩
  have hX0 : |X t₀| ≤ M := by
    obtain ⟨h00, h0M⟩ := hz0 0
    obtain ⟨h10, h1M⟩ := hz0 1
    have e := hXe t₀
    have hA : 0 ≤ ((N : ℝ) - 1) * z t₀ 1 := mul_nonneg (by linarith) h10
    have hB : ((N : ℝ) - 1) * z t₀ 1 ≤ ((N : ℝ) - 1) * M :=
      mul_le_mul_of_nonneg_left h1M (by linarith)
    have hXn : 0 ≤ X t₀ := by
      have : 0 ≤ (N : ℝ) * X t₀ := by rw [e]; linarith
      exact (mul_nonneg_iff_of_pos_left hn).mp this
    have hXM : X t₀ ≤ M := by
      have : (N : ℝ) * X t₀ ≤ (N : ℝ) * M := by rw [e]; linarith
      exact le_of_mul_le_mul_left this hn
    rw [abs_le]; constructor <;> linarith
  have hY0 : |Y t₀| ≤ M := by
    obtain ⟨h0, hM⟩ := hz0 2
    rw [abs_le]; constructor <;> simp only [hY_def] <;> linarith
  -- slope hypothesis of Lemma C.4
  have hslope : ∀ s ≥ t₀, ∀ ε > 0, ∀ᶠ h in 𝓝[>] (0 : ℝ),
      ∃ a ∈ Icc aLo aHi, ∃ ã ∈ Icc ãLo ãHi, ∃ β ∈ Icc βLo βHi,
        |(X (s + h) - X s) / h - a * exp (Y s - X s)| < ε ∧
        |(Y (s + h) - Y s) / h - (β * exp (-Y s) - ã * exp (Y s - X s))| < ε := by
    intro s hs ε hε
    have hs0 : 0 ≤ s := by linarith
    have hs1 : T₁ ≤ s := le_trans (le_max_left _ _) hs
    filter_upwards [hz.slope_lin₂ (Xc N) ![0, 0, 1, 0] hs0 hε] with h hh
    obtain ⟨θ, η, hadm, h1, h2⟩ := hh
    obtain ⟨hZ, hu⟩ := hCZu z hz hinit s hs0
    obtain ⟨a, haI, ã, hãI, β, hβI, e1, e2⟩ :=
      hcoef (z s) (hgood s hs0) (hCv z hz hinit s hs0) hu hZ (hT₁ z hz hinit s hs1).2.1 θ η hadm
    refine ⟨a, haI, ã, hãI, β, hβI, ?_, ?_⟩
    · simp only [hX_def, hY_def]
      rw [← e1]; exact h1
    · simp only [hX_def, hY_def]
      rw [F2_lin_e2, F2_lin_e2, F2_lin_e2] at h2
      rw [← e2]; exact h2
  have hmain := hC' X Y hXc hYc hslope hX0 hY0
  obtain ⟨hXt, hYt⟩ := hmain t ht
  rw [abs_le] at hXt hYt
  have ht0 : 0 ≤ t := by linarith
  have hlogt : 0 ≤ log t := Real.log_nonneg (by linarith)
  -- bounds on `u` at time `t`
  obtain ⟨-, hut⟩ := hCZu z hz hinit t ht0
  have hu0 : 0 ≤ u (z t) := (hgood t ht0).1
  unfold u at hut hu0
  have e := hXe t
  -- `0 ≤ x₁ - X ≤ u`
  have hx1a : 0 ≤ z t 0 - X t := by
    have : 0 ≤ (N : ℝ) * (z t 0 - X t) := by
      have : (N : ℝ) * (z t 0 - X t) = ((N : ℝ) - 1) * (z t 0 - z t 1) := by linarith
      rw [this]; exact mul_nonneg (by linarith) hu0
    exact (mul_nonneg_iff_of_pos_left hn).mp this
  have hx1b : z t 0 - X t ≤ z t 0 - z t 1 := by
    have : (N : ℝ) * (z t 0 - X t) ≤ (N : ℝ) * (z t 0 - z t 1) := by
      have h' : (N : ℝ) * (z t 0 - X t) = ((N : ℝ) - 1) * (z t 0 - z t 1) := by linarith
      rw [h']; nlinarith
    exact le_of_mul_le_mul_left this hn
  -- `0 ≤ X - x₂ ≤ u`
  have hx2a : 0 ≤ X t - z t 1 := by
    have : 0 ≤ (N : ℝ) * (X t - z t 1) := by
      have : (N : ℝ) * (X t - z t 1) = z t 0 - z t 1 := by linarith
      rw [this]; exact hu0
    exact (mul_nonneg_iff_of_pos_left hn).mp this
  have hx2b : X t - z t 1 ≤ z t 0 - z t 1 := by
    have : (N : ℝ) * (X t - z t 1) ≤ (N : ℝ) * (z t 0 - z t 1) := by
      have h' : (N : ℝ) * (X t - z t 1) = z t 0 - z t 1 := by linarith
      rw [h']; nlinarith
    exact le_of_mul_le_mul_left this hn
  -- `y₂` lower bound from item 1
  have hvt := hCv z hz hinit t ht0
  unfold v at hvt
  -- `y₂` upper bound via a barrier at level `L`
  set L : ℝ := max R (max M' (log t + C')) with hL_def
  have hy1L : ∀ r ∈ Icc (0 : ℝ) t, z r 2 ≤ L := by
    rintro r ⟨hr0, hrt⟩
    by_cases hr : r ≤ 2 * t₀
    · have h1 := hup 2 r hr0
      have h2 : ((K : ℝ) + 2) * r ≤ ((K : ℝ) + 2) * (2 * t₀) :=
        mul_le_mul_of_nonneg_left hr hK0
      have h3 : M' ≤ L := le_trans (le_max_left _ _) (le_max_right _ _)
      linarith
    · replace hr := (not_le.mp hr)
      have h1 := (abs_le.mp (hmain r hr.le).2).2
      simp only [hY_def] at h1
      have h2 : log r ≤ log t := Real.log_le_log (by linarith) hrt
      have h3 : log t + C' ≤ L := le_trans (le_max_right _ _) (le_max_right _ _)
      linarith
  have hbar := hz.barrier ![0, 0, 0, 1] L (a := 0) (b := t) le_rfl (by
    intro r hr hL θ η hadm
    rw [F2_lin_e3] at hL ⊢
    apply le_of_eq
    apply F2_F3_zero hadm
    have := hy1L r ⟨hr.1, hr.2.le⟩
    unfold v; linarith) t ⟨ht0, le_rfl⟩
  rw [F2_lin_e3, F2_lin_e3] at hbar
  have hy20 : z 0 3 ≤ L := le_trans (hinit.2 3) (le_max_left _ _)
  have hy2L : z t 3 ≤ L := le_trans hbar (max_le hy20 le_rfl)
  have hL : L ≤ |R| + |M'| + |C'| + log t := by
    refine max_le ?_ (max_le ?_ ?_)
    · linarith [le_abs_self R, abs_nonneg M', abs_nonneg C']
    · linarith [le_abs_self M', abs_nonneg R, abs_nonneg C']
    · linarith [le_abs_self C', abs_nonneg R, abs_nonneg M']
  have hCu : Cu ≤ |Cu| := le_abs_self Cu
  have hCv' : Cv ≤ |Cv| := le_abs_self Cv
  have hC'1 : C' ≤ |C'| := le_abs_self C'
  have hR0 := abs_nonneg R
  have hM'0 := abs_nonneg M'
  have hCu0 := abs_nonneg Cu
  have hCv0 := abs_nonneg Cv
  simp only [hX_def, hY_def] at hXt hYt hx1a hx1b hx2a hx2b
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [abs_le] <;> constructor <;> linarith



/-- A function within `C` of `k log (α t)` (`k ≥ 1`, `α > 0`) tends to `∞`. -/
private lemma F2_tendsto {f : ℝ → ℝ} {α k a₀ C : ℝ} (hα : 0 < α) (hk : 1 ≤ k)
    (h : ∀ t ≥ a₀, |f t - k * log (α * t)| ≤ C) : Tendsto f atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨max a₀ (exp (|b| + |C|) / α), fun t ht => ?_⟩
  have ht1 : a₀ ≤ t := le_trans (le_max_left _ _) ht
  have ht2 : exp (|b| + |C|) / α ≤ t := le_trans (le_max_right _ _) ht
  have hαt : exp (|b| + |C|) ≤ α * t := by rwa [div_le_iff₀ hα, mul_comm] at ht2
  have hlog : |b| + |C| ≤ log (α * t) :=
    (Real.le_log_iff_exp_le (lt_of_lt_of_le (exp_pos _) hαt)).mpr hαt
  have hl0 : 0 ≤ log (α * t) := le_trans (by positivity) hlog
  have hkl : log (α * t) ≤ k * log (α * t) := le_mul_of_one_le_left hl0 hk
  have := (abs_le.mp (h t ht1)).1
  linarith [le_abs_self b, le_abs_self C]

theorem four_parameter_log_convergence (hK : 2 ≤ K) (hN : K + 5 ≤ N) (R : ℝ) :
    ∃ Cv CZ Cu C T : ℝ, ∀ α > 0, ∀ z : ℝ → Fin 4 → ℝ, IsSol N K α z → Init R (z 0) →
      (∀ t ≥ 0, max (v (z t)) 0 ≤ Cv) ∧
      (∀ i, Tendsto (fun t => z t i) atTop atTop) ∧
      (∀ t ≥ 0, 2 * z t 2 - z t 0 ≤ CZ ∧ u (z t) ≤ Cu) ∧
      (∀ t ≥ T / α,
        |z t 0 - 2 * log (α * t)| ≤ C ∧ |z t 1 - 2 * log (α * t)| ≤ C ∧
        |z t 2 - log (α * t)| ≤ C ∧ |z t 3 - log (α * t)| ≤ C) := by
  obtain ⟨Cv, hCv⟩ := DFS.item1 hK hN R
  obtain ⟨CZ, Cu, hCZu⟩ := DFS.item3 hK hN R
  obtain ⟨C, T, hCT⟩ := DFS.item4 hK hN R
  refine ⟨max Cv 0, CZ, Cu, C, T, ?_⟩
  intro α hα z hz hinit
  set zh : ℝ → Fin 4 → ℝ := fun s => z (s / α) with hzh_def
  have hzh : IsSol N K 1 zh := hz.rescale hα
  have hinit' : Init R (zh 0) := by simpa [zh] using hinit
  have key : ∀ t, z t = zh (α * t) := fun t => by
    simp only [zh]; rw [mul_div_cancel_left₀ t hα.ne']
  have hrate : ∀ t ≥ T / α,
      |z t 0 - 2 * log (α * t)| ≤ C ∧ |z t 1 - 2 * log (α * t)| ≤ C ∧
      |z t 2 - log (α * t)| ≤ C ∧ |z t 3 - log (α * t)| ≤ C := by
    intro t ht
    have hT : T ≤ α * t := by rwa [ge_iff_le, div_le_iff₀ hα, mul_comm] at ht
    rw [key t]
    exact hCT zh hzh hinit' (α * t) hT
  refine ⟨?_, ?_, ?_, hrate⟩
  · intro t ht
    rw [key t]
    exact max_le_max (hCv zh hzh hinit' _ (by positivity)) le_rfl
  · intro i
    fin_cases i
    · exact F2_tendsto (k := 2) hα (by norm_num) (fun t ht => (hrate t ht).1)
    · exact F2_tendsto (k := 2) hα (by norm_num) (fun t ht => (hrate t ht).2.1)
    · exact F2_tendsto (k := 1) hα le_rfl (fun t ht => by
        simpa using (hrate t ht).2.2.1)
    · exact F2_tendsto (k := 1) hα le_rfl (fun t ht => by
        simpa using (hrate t ht).2.2.2)
  · intro t ht
    rw [key t]
    exact hCZu zh hzh hinit' _ (by positivity)



end DFS
