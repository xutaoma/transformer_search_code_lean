import DFSLean.LemmaC2
import DFSLean.GenericDI
import DFSLean.Basic

/-!
# Package R: Cor. C.3 (reduction to the Stage 1 four-variable system)
-/

namespace DFS
open Real Finset Filter Topology Set
variable {N K : ℕ}

/-! ### Elementary evaluations -/

private lemma R_P8_even {m : Fin 8} (h : (m : ℕ) % 2 = 0) : P8 N m = 1 / (N : ℝ) := by
  simp [P8, h]

private lemma R_P8_odd {m : Fin 8} (h : (m : ℕ) % 2 = 1) :
    P8 N m = 1 / ((N : ℝ) * ((N : ℝ) - 1)) := by
  simp [P8, h]

@[simp] private lemma R_proj0 (s : Fin 8 → ℝ) : proj s 0 = s 2 := rfl
@[simp] private lemma R_proj1 (s : Fin 8 → ℝ) : proj s 1 = s 1 := rfl
@[simp] private lemma R_proj2 (s : Fin 8 → ℝ) : proj s 2 = s 4 - s 5 := rfl
@[simp] private lemma R_proj3 (s : Fin 8 → ℝ) : proj s 3 = s 6 - s 7 := rfl

private lemma R_E8 (s : Fin 8 → ℝ) : E8 s = E (proj s) := rfl

private lemma R_eb8 {s : Fin 8 → ℝ} (h : s 3 = 0) : eb8 s = 1 := by simp [eb8, h]

private lemma R_ed8 {s : Fin 8 → ℝ} (h : s 7 ≤ 0) : ed8 s = 1 := by
  simp [ed8, max_eq_right h]

private lemma R_Q1 {s : Fin 8 → ℝ} (h3 : s 3 = 0) (h7 : s 7 ≤ 0) :
    Q1 N K s = D1 N (proj s) := by
  simp only [Q1, D1, R_eb8 h3, R_ed8 h7, R_proj0, R_proj2]; ring

private lemma R_Q2 {s : Fin 8 → ℝ} (h7 : s 7 ≤ 0) (j : ℕ) :
    Q2 N K s j = D2 N K j (proj s) := by
  simp only [Q2, D2, R_ed8 h7, R_proj0, R_proj2, R_E8]; ring

private lemma R_Q3 {s : Fin 8 → ℝ} (h3 : s 3 = 0) (h7 : s 7 ≤ 0) (j : ℕ) :
    Q3 N K s j = D3 N (proj s) := by
  simp only [Q3, D3, R_eb8 h3, R_ed8 h7, R_proj2]; ring

private lemma R_Q4 {s : Fin 8 → ℝ} (h7 : s 7 ≤ 0) :
    Q4 N K s = D4 N K (proj s) := by
  simp only [Q4, D4, R_ed8 h7, R_proj2, R_E8]; ring

/-! ### Positivity of the normalizers (everywhere) -/

private lemma R_Q1_pos (hN : K + 5 ≤ N) (s : Fin 8 → ℝ) : 0 < Q1 N K s := by
  have hNK : (K : ℝ) + 5 ≤ N := by exact_mod_cast hN
  have : 0 ≤ (K : ℝ) * eb8 s := mul_nonneg (Nat.cast_nonneg K) (exp_pos _).le
  unfold Q1 ed8
  linarith [exp_pos (s 2), exp_pos (s 4 - s 5), exp_pos (max (s 7) 0)]

private lemma R_Q2_pos (hN : K + 5 ≤ N) (s : Fin 8 → ℝ) {j : ℕ} (hj : j < K) :
    0 < Q2 N K s j := by
  have hNK : (K : ℝ) + 5 ≤ N := by exact_mod_cast hN
  have hjK : (j : ℝ) < K := by exact_mod_cast hj
  have h1 : 0 ≤ ((K : ℝ) - j) * exp (s 2) := mul_nonneg (by linarith) (exp_pos _).le
  have h2 : 0 ≤ (j : ℝ) * E8 s := mul_nonneg (Nat.cast_nonneg j) (exp_pos _).le
  unfold Q2 ed8
  linarith [exp_pos (s 4 - s 5), exp_pos (max (s 7) 0)]

private lemma R_Q3_pos (hN : K + 5 ≤ N) (s : Fin 8 → ℝ) {j : ℕ} (hj : j < K) :
    0 < Q3 N K s j := by
  have hNK : (K : ℝ) + 5 ≤ N := by exact_mod_cast hN
  have hjK : (j : ℝ) + 1 ≤ K := by exact_mod_cast hj
  have h1 : 0 ≤ ((K : ℝ) - 1 - j) * eb8 s := mul_nonneg (by linarith) (exp_pos _).le
  unfold Q3 ed8
  linarith [exp_pos (s 4 - s 5), exp_pos (max (s 7) 0), (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

private lemma R_Q4_pos (hN : K + 5 ≤ N) (s : Fin 8 → ℝ) : 0 < Q4 N K s := by
  have hNK : (K : ℝ) + 5 ≤ N := by exact_mod_cast hN
  have h2 : 0 ≤ (K : ℝ) * E8 s := mul_nonneg (Nat.cast_nonneg K) (exp_pos _).le
  unfold Q4 ed8
  linarith [exp_pos (s 4 - s 5), exp_pos (max (s 7) 0)]

/-- The sum `S` multiplying `σ cd8` in `∂ℓ/∂d₂` is positive. -/
private lemma R_S_pos (hN : K + 5 ≤ N) (s : Fin 8 → ℝ) :
    0 < 1 / Q1 N K s + ∑ j ∈ range K, 1 / Q2 N K s j + ∑ j ∈ range K, 1 / Q3 N K s j
      + 1 / Q4 N K s := by
  have h1 := one_div_pos.2 (R_Q1_pos hN s)
  have h4 := one_div_pos.2 (R_Q4_pos hN s)
  have h2 : 0 ≤ ∑ j ∈ range K, 1 / Q2 N K s j :=
    Finset.sum_nonneg fun j hj => (one_div_pos.2 (R_Q2_pos hN s (Finset.mem_range.1 hj))).le
  have h3 : 0 ≤ ∑ j ∈ range K, 1 / Q3 N K s j :=
    Finset.sum_nonneg fun j hj => (one_div_pos.2 (R_Q3_pos hN s (Finset.mem_range.1 hj))).le
  linarith

/-! ### Dot products with the functionals -/

private lemma R_dot_cu8 (s : Fin 8 → ℝ) : cu8 ⬝ᵥ s = s 2 - s 1 := by
  simp [cu8, dotProduct, Fin.sum_univ_eight]; ring

private lemma R_dot_cv8 (s : Fin 8 → ℝ) : cv8 ⬝ᵥ s = s 4 - s 5 - (s 6 - s 7) := by
  simp [cv8, dotProduct, Fin.sum_univ_eight]; ring

private lemma R_dot_cd8 (s : Fin 8 → ℝ) : cd8 ⬝ᵥ s = s 7 := by
  simp [cd8, dotProduct, Fin.sum_univ_eight]

private lemma R_m1_add_div {X D : ℝ} (hD : D ≠ 0) : -1 + X / D = -((D - X) / D) := by
  field_simp; ring

/-! ### Lemma C.2, Step 5: the velocities of the aggregated variables -/

section vel
variable [NeZero N]

private lemma R_vel (hK : 2 ≤ K) (hN : K + 5 ≤ N) (α : ℝ) (s : Fin 8 → ℝ)
    (σ : (Fin 8 → ℝ) → ℝ) (hσ : Sel8 s σ) (hb1 : 0 < s 1) (hb2 : s 3 < s 1) (ha2 : 0 < s 2)
    (hy : 0 < s 4 - s 5) (h3 : s 3 = 0) (h7 : s 7 ≤ 0) :
    -α * P8 N 2 * g8 N K s σ 2 = F N K α (σ cu8) (σ cv8) (proj s) 0 ∧
    -α * P8 N 1 * g8 N K s σ 1 = F N K α (σ cu8) (σ cv8) (proj s) 1 ∧
    -α * P8 N 4 * g8 N K s σ 4 - -α * P8 N 5 * g8 N K s σ 5
      = F N K α (σ cu8) (σ cv8) (proj s) 2 ∧
    (N : ℝ) / ((N : ℝ) - 1) * (-α * P8 N 6 * g8 N K s σ 6)
      = F N K α (σ cu8) (σ cv8) (proj s) 3 := by
  have hg := DFS.g8_on_R hK hN s σ hσ hb1 hb2 ha2 hy
  have hNK : (K : ℝ) + 5 ≤ N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := by linarith
  have hN1 : (N : ℝ) - 1 ≠ 0 := by linarith
  rw [hg, R_P8_even (m := 2) (by decide), R_P8_odd (m := 1) (by decide),
    R_P8_even (m := 4) (by decide), R_P8_odd (m := 5) (by decide),
    R_P8_even (m := 6) (by decide), DFS.A_F0, DFS.A_F1, DFS.A_F2, DFS.A_F3]
  simp only [Matrix.cons_val, R_Q1 h3 h7, R_Q2 h7, R_Q3 h3 h7, R_Q4 h7, R_E8, R_proj2]
  set z := proj s with hz
  set θ := σ cu8
  set η := σ cv8
  have hD1 : D1 N z ≠ 0 := (DFS.A_D1_pos hN z).ne'
  have hD3 : D3 N z ≠ 0 := (DFS.A_D3_pos hN z).ne'
  have hD4 : D4 N K z ≠ 0 := (DFS.A_D4_pos hN z).ne'
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hsum : ∑ x ∈ range K, (-1 + (((K : ℝ) - x) * exp (s 2) + x * E z * θ) / D2 N K x z)
        = -∑ j ∈ range K, (exp (s 4 - s 5) + N - K - 1 + j * E z * (1 - θ)) / D2 N K j z := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [R_m1_add_div (DFS.A_D2_pos hN (Finset.mem_range.1 hj) z).ne']
      congr 2
      simp only [D2, hz, R_proj0, R_proj2]; ring
    have h1 : -1 + exp (s 2) / D1 N z = -((exp (s 4 - s 5) + N - 2) / D1 N z) := by
      rw [R_m1_add_div hD1]; congr 2; simp only [D1, hz, R_proj0, R_proj2]; ring
    rw [hsum, h1]; ring
  · ring
  · have hsum : ∑ x ∈ range K, (-1 + exp (s 4 - s 5) / D3 N z)
        = -((K : ℝ) * ((N : ℝ) - 1) / D3 N z) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, R_m1_add_div hD3]
      have : D3 N z - exp (s 4 - s 5) = (N : ℝ) - 1 := by simp only [D3, hz, R_proj2]; ring
      rw [this]; ring
    have h4 : -1 + ((K : ℝ) * E z * η + exp (s 4 - s 5)) / D4 N K z
        = -(((N : ℝ) - K - 1 + K * E z * (1 - η)) / D4 N K z) := by
      rw [R_m1_add_div hD4]; congr 2; simp only [D4, hz, R_proj2]; ring
    have hc : ∀ G : ℝ, -α * (1 / (N : ℝ)) * G - -α * (1 / ((N : ℝ) * ((N : ℝ) - 1))) * -G
        = -α / ((N : ℝ) - 1) * G := by
      intro G; field_simp; ring
    rw [hc, hsum]
    have : ∀ A B C D : ℝ, A + B + -C - 1 + D = A + B + -C + (-1 + D) := by intros; ring
    rw [this, h4]; ring
  · have hc : ∀ G : ℝ, (N : ℝ) / ((N : ℝ) - 1) * (-α * (1 / (N : ℝ)) * G)
        = -α / ((N : ℝ) - 1) * G := by
      intro G; field_simp
    rw [hc]; ring

private lemma R_g45 (hK : 2 ≤ K) (hN : K + 5 ≤ N) (s : Fin 8 → ℝ)
    (σ : (Fin 8 → ℝ) → ℝ) (hσ : Sel8 s σ) (hb1 : 0 < s 1) (hb2 : s 3 < s 1) (ha2 : 0 < s 2)
    (hy : 0 < s 4 - s 5) : g8 N K s σ 5 = -g8 N K s σ 4 := by
  rw [DFS.g8_on_R hK hN s σ hσ hb1 hb2 ha2 hy]
  simp only [Matrix.cons_val]

private lemma R_g67 (hK : 2 ≤ K) (hN : K + 5 ≤ N) (s : Fin 8 → ℝ)
    (σ : (Fin 8 → ℝ) → ℝ) (hσ : Sel8 s σ) (hb1 : 0 < s 1) (hb2 : s 3 < s 1) (ha2 : 0 < s 2)
    (hy : 0 < s 4 - s 5) : g8 N K s σ 6 + g8 N K s σ 7 = ed8 s * σ cd8 *
      (1 / Q1 N K s + ∑ j ∈ range K, 1 / Q2 N K s j + ∑ j ∈ range K, 1 / Q3 N K s j
        + 1 / Q4 N K s) := by
  rw [DFS.g8_on_R hK hN s σ hσ hb1 hb2 ha2 hy]
  simp only [Matrix.cons_val]
  ring

end vel

/-! ### Linear functionals of the eight scalars -/

/-- `g₁ + (N-1) d₁`. -/
private def R_c1 (N : ℕ) : Fin 8 → ℝ := ![0, 0, 0, 0, 1, (N : ℝ) - 1, 0, 0]
/-- `φ = g₂ + (N-1) d₂`. -/
private def R_c2 (N : ℕ) : Fin 8 → ℝ := ![0, 0, 0, 0, 0, 0, 1, (N : ℝ) - 1]

private lemma R_dot_c1 (w : Fin 8 → ℝ) : R_c1 N ⬝ᵥ w = w 4 + ((N : ℝ) - 1) * w 5 := by
  simp [R_c1, dotProduct, Fin.sum_univ_eight]

private lemma R_dot_c2 (w : Fin 8 → ℝ) : R_c2 N ⬝ᵥ w = w 6 + ((N : ℝ) - 1) * w 7 := by
  simp [R_c2, dotProduct, Fin.sum_univ_eight]

/-- Constancy of `c ⬝ᵥ s` from vanishing velocities (both directions of `dot_le`). -/
private lemma R_const {α : ℝ} {s : ℝ → Fin 8 → ℝ} [NeZero N] (hs : IsSol8 N K α s)
    (c : Fin 8 → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (h : ∀ t ∈ Set.Ico a b, ∀ w ∈ V8 N K α (s t), c ⬝ᵥ w = 0) : c ⬝ᵥ s b = c ⬝ᵥ s a := by
  have h1 := DFS.IsDI.dot_le hs c 0 ha hab (fun t ht w hw => (h t ht w hw).le)
  have h2 := DFS.IsDI.dot_le hs (-c) 0 ha hab
    (fun t ht w hw => by rw [neg_dotProduct, h t ht w hw, neg_zero])
  simp only [neg_dotProduct, zero_mul, add_zero] at h1 h2
  linarith

/-! ### A gluing argument for `φ` on `[T₀, ∞)` -/

private lemma R_glue {φ d : ℝ → ℝ} {T : ℝ} (hT : 0 < T) (hφc : ContinuousOn φ (Ici 0))
    (hφ_anti : ∀ a b, 0 ≤ a → a ≤ b → φ b ≤ φ a)
    (hφ_const : ∀ a b, 0 ≤ a → a ≤ b → (∀ t ∈ Set.Ico a b, d t < 0) → φ b = φ a)
    (hd_anti : ∀ a b, 0 ≤ a → a ≤ b → d b ≤ d a)
    (hd_nonpos : ∀ t ≥ T, d t ≤ 0)
    (hzero : ∀ t ≥ T, d t = 0 → φ T ≤ φ t) :
    ∀ t ≥ T, φ t = φ T := by
  intro t ht
  refine le_antisymm (hφ_anti T t hT.le ht) ?_
  by_cases hdt : d t = 0
  · exact hzero t ht hdt
  have hdt' : d t < 0 := lt_of_le_of_ne (hd_nonpos t ht) hdt
  set A : Set ℝ := {r | r ∈ Icc T t ∧ d r < 0} with hAdef
  have hA_ne : A.Nonempty := ⟨t, ⟨ht, le_rfl⟩, hdt'⟩
  have hA_bdd : BddBelow A := ⟨T, fun r hr => hr.1.1⟩
  set ρ := sInf A with hρdef
  have hρt : ρ ≤ t := csInf_le hA_bdd ⟨⟨ht, le_rfl⟩, hdt'⟩
  have hTρ : T ≤ ρ := le_csInf hA_ne (fun r hr => hr.1.1)
  have hright : ∀ r, ρ < r → r ≤ t → d r < 0 := by
    intro r hr hrt
    obtain ⟨r', hr'A, hr'r⟩ := exists_lt_of_csInf_lt hA_ne hr
    exact lt_of_le_of_lt (hd_anti r' r (by linarith [hr'A.1.1]) hr'r.le) hr'A.2
  have hleft : ∀ r, T ≤ r → r < ρ → d r = 0 := by
    intro r hTr hrρ
    by_contra hne
    have hlt : d r < 0 := lt_of_le_of_ne (hd_nonpos r hTr) hne
    have := csInf_le hA_bdd ⟨⟨hTr, by linarith⟩, hlt⟩
    linarith
  have hcont : ContinuousAt φ ρ := hφc.continuousAt (Ici_mem_nhds (by linarith))
  have hρ : φ T ≤ φ ρ := by
    rcases eq_or_lt_of_le hTρ with h | h
    · rw [h]
    · refine ge_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds :
        Tendsto φ (𝓝[<] ρ) (𝓝 (φ ρ))) ?_
      filter_upwards [Ioo_mem_nhdsLT h] with r hr
      exact hzero r hr.1.le (hleft r hr.1.le hr.2)
  rcases eq_or_lt_of_le hρt with h | h
  · rw [← h]; exact hρ
  · have : φ ρ ≤ φ t := by
      refine le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds :
        Tendsto φ (𝓝[>] ρ) (𝓝 (φ ρ))) ?_
      filter_upwards [Ioo_mem_nhdsGT h] with a ha
      rw [hφ_const a t (by linarith [ha.1]) ha.2.le
        (fun r hr => hright r (by linarith [hr.1, ha.1]) hr.2.le)]
    linarith

/-! ### Consequences of Lemma C.2 along a solution -/

section along
variable [NeZero N] {c0 c0' α : ℝ} {s : ℝ → Fin 8 → ℝ}

private lemma R_inR (hK : 2 ≤ K) (hN : K + 5 ≤ N) (h0 : 0 < c0') (h1 : c0' < c0) (hα : 0 < α)
    (hs : IsSol8 N K α s) (hs0 : s 0 = init8 c0 c0') {t : ℝ} (ht : 0 ≤ t) :
    0 < s t 1 ∧ s t 3 < s t 1 ∧ 0 < s t 2 ∧ 0 < s t 4 - s t 5 := by
  obtain ⟨-, h2, -, h4, h5, h6, -, -⟩ := DFS.lemmaC2_region hK hN h0 h1 hα hs hs0 t ht
  refine ⟨by linarith, by linarith, by linarith, h6⟩

private lemma R_vel_c1 (hK : 2 ≤ K) (hN : K + 5 ≤ N) (h0 : 0 < c0') (h1 : c0' < c0)
    (hα : 0 < α) (hs : IsSol8 N K α s) (hs0 : s 0 = init8 c0 c0') {t : ℝ} (ht : 0 ≤ t)
    (w : Fin 8 → ℝ) (hw : w ∈ V8 N K α (s t)) : R_c1 N ⬝ᵥ w = 0 := by
  obtain ⟨σ, hσ, rfl⟩ := hw
  obtain ⟨hb1, hb2, ha2, hy⟩ := R_inR hK hN h0 h1 hα hs hs0 ht
  have hNK : (K : ℝ) + 5 ≤ N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := by linarith
  have hN1 : (N : ℝ) - 1 ≠ 0 := by linarith
  rw [R_dot_c1, R_P8_even (m := 4) (by decide), R_P8_odd (m := 5) (by decide),
    R_g45 hK hN (s t) σ hσ hb1 hb2 ha2 hy]
  field_simp; ring

private lemma R_vel_c2 (hK : 2 ≤ K) (hN : K + 5 ≤ N) (h0 : 0 < c0') (h1 : c0' < c0)
    (hα : 0 < α) (hs : IsSol8 N K α s) (hs0 : s 0 = init8 c0 c0') {t : ℝ} (ht : 0 ≤ t)
    (w : Fin 8 → ℝ) (hw : w ∈ V8 N K α (s t)) :
    ∃ σ : (Fin 8 → ℝ) → ℝ, Sel8 (s t) σ ∧ R_c2 N ⬝ᵥ w = -(α / N) * (ed8 (s t) * σ cd8 *
      (1 / Q1 N K (s t) + ∑ j ∈ range K, 1 / Q2 N K (s t) j + ∑ j ∈ range K, 1 / Q3 N K (s t) j
        + 1 / Q4 N K (s t))) := by
  obtain ⟨σ, hσ, rfl⟩ := hw
  obtain ⟨hb1, hb2, ha2, hy⟩ := R_inR hK hN h0 h1 hα hs hs0 ht
  have hNK : (K : ℝ) + 5 ≤ N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := by linarith
  have hN1 : (N : ℝ) - 1 ≠ 0 := by linarith
  refine ⟨σ, hσ, ?_⟩
  rw [R_dot_c2, R_P8_even (m := 6) (by decide), R_P8_odd (m := 7) (by decide),
    ← R_g67 hK hN (s t) σ hσ hb1 hb2 ha2 hy]
  field_simp; ring

end along

/-! ### Difference quotients of the aggregated variables -/

private lemma R_proj_cont : Continuous (proj : (Fin 8 → ℝ) → Fin 4 → ℝ) := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact continuous_apply 2
  · exact continuous_apply 1
  · exact (continuous_apply 4).sub (continuous_apply 5)
  · exact (continuous_apply 6).sub (continuous_apply 7)

private lemma R_quot (hN : 2 ≤ N) (a b w : Fin 8 → ℝ) (Fv : Fin 4 → ℝ) {h ε : ℝ} (hε : 0 < ε)
    (hlt : ‖h⁻¹ • (b - a) - w‖ < ε / 3)
    (e0 : w 2 = Fv 0) (e1 : w 1 = Fv 1) (e2 : w 4 - w 5 = Fv 2)
    (e3 : (N : ℝ) / ((N : ℝ) - 1) * w 6 = Fv 3)
    (hκ : b 6 + ((N : ℝ) - 1) * b 7 = a 6 + ((N : ℝ) - 1) * a 7) :
    ‖h⁻¹ • (proj b - proj a) - Fv‖ < ε := by
  rw [pi_norm_lt_iff (by positivity)] at hlt
  rw [pi_norm_lt_iff hε]
  have q : ∀ m, |h⁻¹ * (b m - a m) - w m| < ε / 3 := fun m => by
    simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs] using hlt m
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  intro i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
  fin_cases i
  · simp only [Fin.zero_eta, R_proj0]; rw [← e0]; linarith [q 2]
  · simp only [Fin.mk_one, R_proj1]; rw [← e1]; linarith [q 1]
  · simp only [Fin.reduceFinMk, R_proj2]
    rw [← e2]
    have : h⁻¹ * (b 4 - b 5 - (a 4 - a 5)) - (w 4 - w 5)
        = (h⁻¹ * (b 4 - a 4) - w 4) - (h⁻¹ * (b 5 - a 5) - w 5) := by ring
    rw [this]
    calc _ ≤ |h⁻¹ * (b 4 - a 4) - w 4| + |h⁻¹ * (b 5 - a 5) - w 5| := abs_sub _ _
      _ < ε := by linarith [q 4, q 5]
  · simp only [Fin.reduceFinMk, R_proj3]
    rw [← e3]
    have hN1 : (N : ℝ) - 1 ≠ 0 := by linarith
    have hb7 : b 7 - a 7 = -(b 6 - a 6) / ((N : ℝ) - 1) := by
      field_simp; linarith
    have : h⁻¹ * (b 6 - b 7 - (a 6 - a 7)) - (N : ℝ) / ((N : ℝ) - 1) * w 6
        = (N : ℝ) / ((N : ℝ) - 1) * (h⁻¹ * (b 6 - a 6) - w 6) := by
      have e : b 6 - b 7 - (a 6 - a 7) = (b 6 - a 6) - (b 7 - a 7) := by ring
      rw [e, hb7]; field_simp; ring
    rw [this, abs_mul, abs_of_pos (div_pos (by linarith) (by linarith))]
    have hc : (N : ℝ) / ((N : ℝ) - 1) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have := q 6
    have := abs_nonneg (h⁻¹ * (b 6 - a 6) - w 6)
    nlinarith

/-! ### The initial phase moves each scalar by at most `1/2` (resp. `1/(2(N-1))`) -/

private lemma R_T0_even (hN : 2 ≤ N) {α : ℝ} (hα : 0 < α) :
    (2 * (K : ℝ) + 2) * α * (1 / (N : ℝ)) * (T0 N K α - 0) = 1 / 2 := by
  have hN0 : (N : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hK1 : (K : ℝ) + 1 ≠ 0 := by positivity
  unfold T0
  field_simp; ring

private lemma R_T0_odd (hN : 2 ≤ N) {α : ℝ} (hα : 0 < α) :
    ((N : ℝ) - 1) * ((2 * (K : ℝ) + 2) * α * (1 / ((N : ℝ) * ((N : ℝ) - 1))) * (T0 N K α - 0))
      = 1 / 2 := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := by linarith
  have hN1 : (N : ℝ) - 1 ≠ 0 := by linarith
  have hK1 : (K : ℝ) + 1 ≠ 0 := by positivity
  unfold T0
  field_simp; ring

/-! ### Cor. C.3 -/

theorem corC3 [NeZero N] (hK : 2 ≤ K) (hN : K + 5 ≤ N) {c0 c0' α : ℝ} (h0 : 0 < c0')
    (h1 : c0' < c0) (hc0 : c0 ≤ 1 / 2) (hα : 0 < α) {s : ℝ → Fin 8 → ℝ} (hs : IsSol8 N K α s)
    (hs0 : s 0 = init8 c0 c0') (hT0 : ∀ t ≥ T0 N K α, s t 3 = 0 ∧ s t 7 ≤ 0) :
    IsSol N K α (fun t => proj (s (T0 N K α + t))) ∧ Init 2 (proj (s (T0 N K α))) ∧
    (∀ t ≥ 0, s t 4 + ((N : ℝ) - 1) * s t 5 = c0 + ((N : ℝ) - 1) * c0') ∧
    ∃ κ : ℝ, |κ - N * c0| ≤ 1 ∧ ∀ t ≥ T0 N K α, s t 6 + ((N : ℝ) - 1) * s t 7 = κ := by
  have hNK : (K : ℝ) + 5 ≤ N := by exact_mod_cast hN
  have hN2 : 2 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by linarith
  have hT : 0 < T0 N K α := by unfold T0; exact div_pos hNpos (by positivity)
  set T := T0 N K α with hTdef
  have hcont : ContinuousOn s (Ici 0) := hs.1
  -- `φ = g₂ + (N-1) d₂` is constant on `[T₀, ∞)`
  set φ : ℝ → ℝ := fun t => R_c2 N ⬝ᵥ s t with hφdef
  have hφ_eq : ∀ t, φ t = s t 6 + ((N : ℝ) - 1) * s t 7 := fun t => R_dot_c2 _
  have hφc : ContinuousOn φ (Ici 0) := by
    have : φ = fun t => s t 6 + ((N : ℝ) - 1) * s t 7 := funext hφ_eq
    rw [this]
    exact ((continuous_apply 6).comp_continuousOn hcont).add
      (continuousOn_const.mul ((continuous_apply 7).comp_continuousOn hcont))
  have hφ_anti : ∀ a b, 0 ≤ a → a ≤ b → φ b ≤ φ a := by
    intro a b ha hab
    have key := DFS.IsDI.dot_le hs (R_c2 N) 0 ha hab (fun t ht w hw => by
      obtain ⟨σ, hσ, hw'⟩ := R_vel_c2 hK hN h0 h1 hα hs hs0 (ha.trans ht.1) w hw
      rw [hw']
      have hS := R_S_pos hN (s t)
      have hσ0 := (hσ cd8).1.1
      have he : 0 < ed8 (s t) := exp_pos _
      have hαN : 0 ≤ α / N := by positivity
      have : 0 ≤ ed8 (s t) * σ cd8 * (1 / Q1 N K (s t) + ∑ j ∈ range K, 1 / Q2 N K (s t) j
          + ∑ j ∈ range K, 1 / Q3 N K (s t) j + 1 / Q4 N K (s t)) := by positivity
      nlinarith)
    simpa [φ] using key
  have hφ_const : ∀ a b, 0 ≤ a → a ≤ b → (∀ t ∈ Set.Ico a b, s t 7 < 0) → φ b = φ a := by
    intro a b ha hab hneg
    refine R_const hs (R_c2 N) ha hab (fun t ht w hw => ?_)
    obtain ⟨σ, hσ, hw'⟩ := R_vel_c2 hK hN h0 h1 hα hs hs0 (ha.trans ht.1) w hw
    have : σ cd8 = 0 := (hσ cd8).2.2 (by rw [R_dot_cd8]; exact hneg t ht)
    rw [hw', this]; ring
  have hmono := DFS.lemmaC2_mono hK hN h0 h1 hα hs hs0
  have hd_anti : ∀ a b, 0 ≤ a → a ≤ b → s b 7 ≤ s a 7 :=
    fun a b ha hab => (hmono a b ha hab).2.2.2
  have hzero : ∀ t ≥ T, s t 7 = 0 → φ T ≤ φ t := by
    intro t ht hd
    have hdT : s T 7 = 0 := le_antisymm (hT0 T le_rfl).2 (hd ▸ hd_anti T t hT.le ht)
    have hy := (hmono T t hT.le ht).2.2.1
    rw [hφ_eq, hφ_eq, hd, hdT]
    rw [hd, hdT] at hy
    linarith
  have hφT : ∀ t ≥ T, φ t = φ T :=
    R_glue (d := fun t => s t 7) hT hφc hφ_anti hφ_const hd_anti (fun t ht => (hT0 t ht).2) hzero
  -- the initial phase
  have hlip := fun m => DFS.lemmaC2_lip hK hN h0 h1 hα hs hs0 0 T le_rfl hT.le m
  have hev : ∀ m : Fin 8, (m : ℕ) % 2 = 0 → |s T m - s 0 m| ≤ 1 / 2 := fun m hm => by
    have := hlip m; rwa [R_P8_even hm, R_T0_even hN2 hα] at this
  have hod : ∀ m : Fin 8, (m : ℕ) % 2 = 1 →
      ((N : ℝ) - 1) * |s T m - s 0 m| ≤ 1 / 2 := fun m hm => by
    have := hlip m
    rw [R_P8_odd hm] at this
    rw [← R_T0_odd (K := K) hN2 hα]
    exact mul_le_mul_of_nonneg_left this (by linarith)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) - 1 := by linarith
  have hod' : ∀ m : Fin 8, (m : ℕ) % 2 = 1 → |s T m - s 0 m| ≤ 1 / 2 := fun m hm => by
    have := hod m hm
    have := abs_nonneg (s T m - s 0 m)
    nlinarith
  have hs00 : ∀ m : Fin 8, s 0 m = init8 c0 c0' m := fun m => by rw [hs0]
  refine ⟨?_, ?_, ?_, ⟨φ T, ?_, fun t ht => by rw [← hφ_eq, hφT t ht]⟩⟩
  · -- `IsSol`
    refine ⟨?_, ?_⟩
    · refine R_proj_cont.comp_continuousOn (hcont.comp (continuousOn_const.add continuousOn_id)
        (fun t (ht : t ∈ Set.Ici 0) => ?_))
      show T + t ∈ Set.Ici 0
      simp only [Set.mem_Ici] at ht ⊢; linarith
    · intro t ht ε hε
      have hTt : 0 ≤ T + t := by linarith
      filter_upwards [hs.2 (T + t) hTt (ε / 3) (by positivity), self_mem_nhdsWithin]
        with h hh hpos
      obtain ⟨w, ⟨σ, hσ, rfl⟩, hlt⟩ := hh
      obtain ⟨hb1, hb2, ha2, hy⟩ := R_inR hK hN h0 h1 hα hs hs0 hTt
      obtain ⟨h3, h7⟩ := hT0 (T + t) (by linarith)
      obtain ⟨e0, e1, e2, e3⟩ := R_vel hK hN α (s (T + t)) σ hσ hb1 hb2 ha2 hy h3 h7
      refine ⟨F N K α (σ cu8) (σ cv8) (proj (s (T + t))), ⟨σ cu8, σ cv8, ?_, rfl⟩, ?_⟩
      · refine ⟨(hσ cu8).1, (hσ cv8).1, fun hu => (hσ cu8).2.1 ?_, fun hu => (hσ cu8).2.2 ?_,
          fun hu => (hσ cv8).2.1 ?_, fun hu => (hσ cv8).2.2 ?_⟩ <;>
        simp only [R_dot_cu8, R_dot_cv8] <;>
        simpa only [DFS.u, DFS.v, R_proj0, R_proj1, R_proj2, R_proj3] using hu
      · have hκ : s (T + t + h) 6 + ((N : ℝ) - 1) * s (T + t + h) 7
            = s (T + t) 6 + ((N : ℝ) - 1) * s (T + t) 7 := by
          rw [← hφ_eq, ← hφ_eq,
            hφT (T + t + h) (by simp only [Set.mem_Ioi] at hpos; linarith),
            hφT (T + t) (by linarith)]
        have := R_quot hN2 (s (T + t)) (s (T + t + h)) _ _ hε hlt e0 e1 e2 e3 hκ
        simpa only [add_assoc] using this
  · -- `Init 2`
    obtain ⟨-, r1, -, -, r4, r5, r6, -⟩ := DFS.lemmaC2_region hK hN h0 h1 hα hs hs0 T hT.le
    have a1 := abs_le.1 (hod' 1 (by decide))
    have a2 := abs_le.1 (hev 2 (by decide))
    have a4 := abs_le.1 (hev 4 (by decide))
    have a5 := abs_le.1 (hod' 5 (by decide))
    have a6 := abs_le.1 (hev 6 (by decide))
    have a7 := abs_le.1 (hod' 7 (by decide))
    simp only [hs00, init8] at a1 a2 a4 a5 a6 a7
    simp only [Matrix.cons_val] at a1 a2 a4 a5 a6 a7
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simp only [DFS.u, R_proj0, R_proj1]; linarith
    · simp only [R_proj1]; linarith
    · simp only [R_proj2]; linarith
    · simp only [R_proj3]; linarith
    · intro i
      fin_cases i
      · simp only [Fin.zero_eta, R_proj0]; linarith
      · simp only [Fin.mk_one, R_proj1]; linarith
      · simp only [Fin.reduceFinMk, R_proj2]; linarith
      · simp only [Fin.reduceFinMk, R_proj3]; linarith
  · -- recovery of `g₁ + (N-1) d₁`
    intro t ht
    have := R_const hs (R_c1 N) le_rfl ht
      (fun r hr w hw => R_vel_c1 hK hN h0 h1 hα hs hs0 hr.1 w hw)
    rw [R_dot_c1, R_dot_c1, hs00, hs00] at this
    simpa only [init8, Matrix.cons_val] using this
  · -- `|κ - N c₀| ≤ 1`
    have a6 := hev 6 (by decide)
    have a7 := hod 7 (by decide)
    simp only [hs00, init8, Matrix.cons_val] at a6 a7
    rw [hφ_eq]
    have e : s T 6 + ((N : ℝ) - 1) * s T 7 - N * c0
        = (s T 6 - c0) + ((N : ℝ) - 1) * (s T 7 - c0) := by ring
    rw [e]
    calc _ ≤ |s T 6 - c0| + |((N : ℝ) - 1) * (s T 7 - c0)| := abs_add_le _ _
      _ = |s T 6 - c0| + ((N : ℝ) - 1) * |s T 7 - c0| := by
          rw [abs_mul, abs_of_pos (a := (N : ℝ) - 1) (by linarith)]
      _ ≤ 1 := by linarith



end DFS
