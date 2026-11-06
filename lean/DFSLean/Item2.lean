import DFSLean.Basic
import DFSLean.Item1


namespace DFS

open Real Filter Topology Set

variable {N K : ℕ}

set_option linter.unusedSimpArgs false

/-! ### Positivity of the denominators -/

private lemma D_N7 (hK : 2 ≤ K) (hN : K + 5 ≤ N) : (7 : ℝ) ≤ N ∧ (K : ℝ) + 5 ≤ N ∧ (2 : ℝ) ≤ K := by
  refine ⟨?_, ?_, ?_⟩
  · have : 7 ≤ N := by omega
    exact_mod_cast this
  · exact_mod_cast hN
  · exact_mod_cast hK

private lemma D_E_pos (z : Fin 4 → ℝ) : 0 < E z := exp_pos _

private lemma D_D1_ge (hK : 2 ≤ K) (hN : K + 5 ≤ N) (z : Fin 4 → ℝ) : exp (z 0) ≤ D1 N z := by
  obtain ⟨h7, -, -⟩ := D_N7 hK hN
  have := exp_pos (z 2)
  unfold D1; linarith

private lemma D_D1_pos (hK : 2 ≤ K) (hN : K + 5 ≤ N) (z : Fin 4 → ℝ) : 0 < D1 N z :=
  lt_of_lt_of_le (exp_pos _) (D_D1_ge hK hN z)

private lemma D_D2_ge (hK : 2 ≤ K) (hN : K + 5 ≤ N) (z : Fin 4 → ℝ) {j : ℕ} (hj : j < K) :
    exp (z 0) ≤ D2 N K j z := by
  obtain ⟨h7, hNK, -⟩ := D_N7 hK hN
  have hj' : (j : ℝ) + 1 ≤ K := by exact_mod_cast hj
  have h0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have := exp_pos (z 2)
  have := exp_pos (z 0)
  have hE := D_E_pos z
  unfold D2
  nlinarith [mul_nonneg h0 hE.le]

private lemma D_D2_pos (hK : 2 ≤ K) (hN : K + 5 ≤ N) (z : Fin 4 → ℝ) {j : ℕ} (hj : j < K) :
    0 < D2 N K j z :=
  lt_of_lt_of_le (exp_pos _) (D_D2_ge hK hN z hj)

private lemma D_D3_pos (hK : 2 ≤ K) (hN : K + 5 ≤ N) (z : Fin 4 → ℝ) : 0 < D3 N z := by
  obtain ⟨h7, -, -⟩ := D_N7 hK hN
  have := exp_pos (z 2)
  unfold D3; linarith

private lemma D_D4_pos (hK : 2 ≤ K) (hN : K + 5 ≤ N) (z : Fin 4 → ℝ) : 0 < D4 N K z := by
  obtain ⟨h7, hNK, hK2⟩ := D_N7 hK hN
  have := exp_pos (z 2)
  have hE := D_E_pos z
  unfold D4; nlinarith

/-! ### Lower bound for `(x₁ + (N-1) x₂)'` -/

private lemma D_w_lower (hK : 2 ≤ K) (hN : K + 5 ≤ N) {θ η : ℝ} (hθ : θ ∈ Icc (0:ℝ) 1)
    (z : Fin 4 → ℝ) :
    (exp (z 2) + (N:ℝ) - 2) / D1 N z / N ≤ lin ![1, (N:ℝ)-1, 0, 0] (F N K 1 θ η z) := by
  obtain ⟨h7, hNK, hK2⟩ := D_N7 hK hN
  simp only [lin, F, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  have hE := D_E_pos z
  have hS1 : 0 ≤ ∑ j ∈ Finset.range K,
      (exp (z 2) + (N:ℝ) - K - 1 + (j:ℝ) * E z * (1 - θ)) / D2 N K j z := by
    apply Finset.sum_nonneg
    intro j hj
    have hjK := Finset.mem_range.mp hj
    apply div_nonneg _ (D_D2_pos hK hN z hjK).le
    have := exp_pos (z 2)
    have : 0 ≤ (j:ℝ) * E z * (1 - θ) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg j) hE.le) (by linarith [hθ.2])
    linarith
  have hS2 : 0 ≤ ∑ j ∈ Finset.range K, (j:ℝ) * E z * θ / D2 N K j z := by
    apply Finset.sum_nonneg
    intro j hj
    have hjK := Finset.mem_range.mp hj
    exact div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg j) hE.le) hθ.1)
      (D_D2_pos hK hN z hjK).le
  set S1 := ∑ j ∈ Finset.range K,
      (exp (z 2) + (N:ℝ) - K - 1 + (j:ℝ) * E z * (1 - θ)) / D2 N K j z
  set S2 := ∑ j ∈ Finset.range K, (j:ℝ) * E z * θ / D2 N K j z
  set G := (exp (z 2) + (N:ℝ) - 2) / D1 N z
  set q := (K:ℝ) * E z * θ / D4 N K z
  have hN0 : (N:ℝ) ≠ 0 := by positivity
  have hN1 : (N:ℝ) - 1 ≠ 0 := by linarith
  have : 1 * (1 / (N:ℝ) * (G + S1 - q)) + ((N:ℝ) - 1) * (1 / ((N:ℝ) * ((N:ℝ) - 1)) * (S2 + q))
      = (G + S1 + S2) / N := by
    field_simp
    ring
  rw [zero_mul, zero_mul, add_zero, add_zero, this]
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

/-! ### Lower bound for `(y₁ + y₂)'` -/

private lemma D_y_lower (hK : 2 ≤ K) (hN : K + 5 ≤ N) {θ η : ℝ} (hη : η ∈ Icc (0:ℝ) 1)
    (z : Fin 4 → ℝ) :
    ((K:ℝ) * ((N:ℝ)-1) / D3 N z - exp (z 2) / D1 N z
        - ∑ j ∈ Finset.range K, exp (z 2) / D2 N K j z) / ((N:ℝ)-1)
      ≤ F N K 1 θ η z 2 + F N K 1 θ η z 3 := by
  obtain ⟨h7, hNK, hK2⟩ := D_N7 hK hN
  simp only [F, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  have hE := D_E_pos z
  have hs : ∑ j ∈ Finset.range K, ((j:ℝ) * E z * η + exp (z 2)) / D2 N K j z
      = ∑ j ∈ Finset.range K, (j:ℝ) * E z * η / D2 N K j z
        + ∑ j ∈ Finset.range K, exp (z 2) / D2 N K j z := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => add_div _ _ _)
  rw [hs]
  have hD4 := D_D4_pos hK hN z
  have hq1 : 0 ≤ ((N:ℝ) - K - 1 + (K:ℝ) * E z * (1 - η)) / D4 N K z := by
    apply div_nonneg _ hD4.le
    have : 0 ≤ (K:ℝ) * E z * (1 - η) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg K) hE.le) (by linarith [hη.2])
    linarith
  have hq2 : 0 ≤ (K:ℝ) * E z * η / D4 N K z :=
    div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg K) hE.le) hη.1) hD4.le
  set P := ∑ j ∈ Finset.range K, (j:ℝ) * E z * η / D2 N K j z
  set S := ∑ j ∈ Finset.range K, exp (z 2) / D2 N K j z
  set q1 := ((N:ℝ) - K - 1 + (K:ℝ) * E z * (1 - η)) / D4 N K z
  set q2 := (K:ℝ) * E z * η / D4 N K z
  set M := (K:ℝ) * ((N:ℝ)-1) / D3 N z
  set H := exp (z 2) / D1 N z
  have hN1 : (0:ℝ) < (N:ℝ) - 1 := by linarith
  have : 1 / ((N:ℝ) - 1) * (M + q1 - H - (P + S)) + 1 / ((N:ℝ) - 1) * (P + q2)
      = (M - H - S) / ((N:ℝ) - 1) + (q1 + q2) / ((N:ℝ) - 1) := by
    field_simp
    ring
  rw [this]
  have : 0 ≤ (q1 + q2) / ((N:ℝ) - 1) := div_nonneg (by linarith) hN1.le
  linarith

private lemma D_F3_zero (θ : ℝ) (z : Fin 4 → ℝ) : F N K 1 θ 0 z 3 = 0 := by
  simp [F]

/-! ### Bounds on `H + Σ Bᵢ` and on `G` -/

private lemma D_HB (hK : 2 ≤ K) (hN : K + 5 ≤ N) (z : Fin 4 → ℝ) :
    exp (z 2) / D1 N z + ∑ j ∈ Finset.range K, exp (z 2) / D2 N K j z
      ≤ ((K:ℝ) + 1) * (exp (z 2) / exp (z 0)) := by
  have hb := exp_pos (z 2)
  have ha := exp_pos (z 0)
  have h1 : exp (z 2) / D1 N z ≤ exp (z 2) / exp (z 0) :=
    div_le_div_of_nonneg_left hb.le ha (D_D1_ge hK hN z)
  have h2 : ∑ j ∈ Finset.range K, exp (z 2) / D2 N K j z
      ≤ ∑ j ∈ Finset.range K, exp (z 2) / exp (z 0) := by
    apply Finset.sum_le_sum
    intro j hj
    exact div_le_div_of_nonneg_left hb.le ha (D_D2_ge hK hN z (Finset.mem_range.mp hj))
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
  linarith

private lemma D_G (hK : 2 ≤ K) (hN : K + 5 ≤ N) (z : Fin 4 → ℝ) (hy : 0 ≤ z 2) {L : ℝ}
    (hx : z 0 ≤ L) :
    1 / (exp L + 1) ≤ (exp (z 2) + (N:ℝ) - 2) / D1 N z := by
  obtain ⟨h7, hNK, hK2⟩ := D_N7 hK hN
  have hb : 1 ≤ exp (z 2) := one_le_exp hy
  have ha := exp_pos (z 0)
  have haL : exp (z 0) ≤ exp L := exp_le_exp.mpr hx
  have hD1 := D_D1_pos hK hN z
  calc 1 / (exp L + 1) ≤ 1 / (exp (z 0) + 1) :=
        div_le_div_of_nonneg_left zero_le_one (by linarith) (by linarith)
    _ ≤ (exp (z 2) + (N:ℝ) - 2) / D1 N z := by
        rw [div_le_div_iff₀ (by linarith) hD1]
        unfold D1
        nlinarith

/-! ### State-space estimates -/

/-- If `x₁ ≤ L` (and `y₁ ≥ 0`) then `(x₁ + (N-1) x₂)' ≥ 1 / (N (e^L + 1))`. -/
private lemma D_keyx (hK : 2 ≤ K) (hN : K + 5 ≤ N) (L : ℝ) (z : Fin 4 → ℝ) (hy : 0 ≤ z 2)
    (hx : z 0 ≤ L) {θ η : ℝ} (hθ : θ ∈ Icc (0:ℝ) 1) :
    1 / ((N:ℝ) * (exp L + 1)) ≤ lin ![1, (N:ℝ)-1, 0, 0] (F N K 1 θ η z) := by
  obtain ⟨h7, hNK, hK2⟩ := D_N7 hK hN
  refine le_trans ?_ (D_w_lower hK hN (η := η) hθ z)
  have := D_G hK hN z hy hx
  rw [mul_comm, ← div_div]
  exact div_le_div_of_nonneg_right this (by linarith)

/-- If `y₁ ≤ B'` and `x₁ ≥ X₀` then `(y₁ + y₂)' ≥ δ`, for every `θ` and `η ∈ [0,1]`. -/
private lemma D_key (hK : 2 ≤ K) (hN : K + 5 ≤ N) (B' : ℝ) :
    ∃ X₀ δ : ℝ, 0 < δ ∧ ∀ z : Fin 4 → ℝ, X₀ ≤ z 0 → z 2 ≤ B' → ∀ θ η : ℝ, η ∈ Icc (0:ℝ) 1 →
      δ ≤ F N K 1 θ η z 2 + F N K 1 θ η z 3 := by
  obtain ⟨h7, hNK, hK2⟩ := D_N7 hK hN
  have hN1 : (0:ℝ) < (N:ℝ) - 1 := by linarith
  set m := (K:ℝ) * ((N:ℝ) - 1) / (exp B' + (N:ℝ) - 1) with hm
  have hm0 : 0 < m := by
    have := exp_pos B'
    apply div_pos (mul_pos (by linarith) hN1) (by linarith)
  refine ⟨2 * ((K:ℝ) + 1) * exp B' / m, m / 2 / ((N:ℝ) - 1), by positivity, ?_⟩
  intro z hx hy θ η hη
  refine le_trans ?_ (D_y_lower hK hN (θ := θ) hη z)
  apply div_le_div_of_nonneg_right _ hN1.le
  have hHB := D_HB hK hN z
  have hM : m ≤ (K:ℝ) * ((N:ℝ)-1) / D3 N z := by
    apply div_le_div_of_nonneg_left (by positivity) (D_D3_pos hK hN z)
    unfold D3
    have := exp_le_exp.mpr hy
    linarith
  have hX0 : 0 < 2 * ((K:ℝ) + 1) * exp B' / m := by positivity
  have ha : 2 * ((K:ℝ) + 1) * exp B' / m < exp (z 0) := by
    have := add_one_le_exp (z 0)
    linarith
  have hb : exp (z 2) ≤ exp B' := exp_le_exp.mpr hy
  have hq : ((K:ℝ) + 1) * (exp (z 2) / exp (z 0)) ≤ m / 2 := by
    have hpos := exp_pos (z 0)
    rw [mul_div_assoc', div_le_iff₀ hpos]
    have h1 : ((K:ℝ) + 1) * exp (z 2) ≤ ((K:ℝ) + 1) * exp B' :=
      mul_le_mul_of_nonneg_left hb (by linarith)
    have h2 : m / 2 * (2 * ((K:ℝ) + 1) * exp B' / m) = ((K:ℝ) + 1) * exp B' := by
      field_simp
    have h3 : m / 2 * (2 * ((K:ℝ) + 1) * exp B' / m) ≤ m / 2 * exp (z 0) :=
      mul_le_mul_of_nonneg_left ha.le (by positivity)
    linarith
  linarith

/-! ### Dynamic steps (uniform in the solution) -/

/-- Step 1: `x₁ → ∞`, uniformly over solutions starting in the invariant region. -/
private lemma D_x1 (hK : 2 ≤ K) (hN : K + 5 ≤ N) (X : ℝ) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ z : ℝ → Fin 4 → ℝ, IsSol N K 1 z → Good (z 0) → ∀ t ≥ T, X ≤ z t 0 := by
  obtain ⟨h7, hNK, hK2⟩ := D_N7 hK hN
  have hNpos : (0:ℝ) < N := by linarith
  set L := (N:ℝ) * max X 0 with hL
  have hL0 : 0 ≤ L := mul_nonneg hNpos.le (le_max_right _ _)
  set δ := 1 / ((N:ℝ) * (exp L + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  refine ⟨L / δ, div_nonneg hL0 hδ0.le, ?_⟩
  intro z hz h0 t ht
  have hgood := hz.good hK hN h0
  have hlin : ∀ s, lin ![1, (N:ℝ)-1, 0, 0] (z s) = z s 0 + ((N:ℝ) - 1) * z s 1 := by
    intro s
    simp only [lin, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    ring
  have hr := hz.reach ![1, (N:ℝ)-1, 0, 0] L δ hδ0 (le_refl 0) (by
    intro s hs hlt θ η hadm
    obtain ⟨hu, hx2, hy1, hy2⟩ := hgood s hs
    apply D_keyx hK hN L (z s) hy1 _ hadm.1
    rw [hlin] at hlt
    have : 0 ≤ ((N:ℝ) - 1) * z s 1 := mul_nonneg (by linarith) hx2
    linarith)
  have ht0 : 0 ≤ t := le_trans (div_nonneg hL0 hδ0.le) ht
  obtain ⟨hu0, hx20, -, -⟩ := h0
  have hw0 : 0 ≤ lin ![1, (N:ℝ)-1, 0, 0] (z 0) := by
    rw [hlin]
    unfold u at hu0
    have : 0 ≤ ((N:ℝ) - 1) * z 0 1 := mul_nonneg (by linarith) hx20
    linarith
  have hT : 0 + (L - lin ![1, (N:ℝ)-1, 0, 0] (z 0)) / δ ≤ t := by
    rw [zero_add]
    refine le_trans ?_ ht
    exact div_le_div_of_nonneg_right (by linarith) hδ0.le
  have hw := hr t ht0 hT
  rw [hlin] at hw
  obtain ⟨hu, hx2, -, -⟩ := hgood t ht0
  unfold u at hu
  have h1 : ((N:ℝ) - 1) * z t 1 ≤ ((N:ℝ) - 1) * z t 0 :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h2 : (N:ℝ) * max X 0 ≤ (N:ℝ) * z t 0 := by linarith
  have h3 : max X 0 ≤ z t 0 := le_of_mul_le_mul_left h2 hNpos
  exact le_trans (le_max_left _ _) h3

/-- Step 2: `y₁ + y₂ → ∞`, uniformly. -/
private lemma D_y12 (hK : 2 ≤ K) (hN : K + 5 ≤ N) (B' : ℝ) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ z : ℝ → Fin 4 → ℝ, IsSol N K 1 z → Good (z 0) →
      ∀ t ≥ T, B' ≤ z t 2 + z t 3 := by
  obtain ⟨X₀, δ, hδ0, hkey⟩ := D_key hK hN B'
  obtain ⟨T₁, hT₁0, hx⟩ := D_x1 hK hN X₀
  have hc : 0 ≤ max B' 0 / δ := div_nonneg (le_max_right _ _) hδ0.le
  refine ⟨T₁ + max B' 0 / δ, by linarith, ?_⟩
  intro z hz h0 t ht
  have hgood := hz.good hK hN h0
  have hlin : ∀ w : Fin 4 → ℝ, lin ![0, 0, 1, 1] w = w 2 + w 3 := by
    intro w
    simp only [lin, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    ring
  have hr := hz.reach ![0, 0, 1, 1] B' δ hδ0 hT₁0 (by
    intro s hs hlt θ η hadm
    obtain ⟨hu, hx2, hy1, hy2⟩ := hgood s (le_trans hT₁0 hs)
    rw [hlin] at hlt ⊢
    exact hkey (z s) (hx z hz h0 s hs) (by linarith) θ η hadm.2.1)
  obtain ⟨-, -, hy1, hy2⟩ := hgood T₁ hT₁0
  have hT : T₁ + (B' - lin ![0, 0, 1, 1] (z T₁)) / δ ≤ t := by
    refine le_trans ?_ ht
    have : (B' - lin ![0, 0, 1, 1] (z T₁)) / δ ≤ max B' 0 / δ := by
      apply div_le_div_of_nonneg_right _ hδ0.le
      rw [hlin]
      have := le_max_left B' 0
      linarith
    linarith
  have := hr t (by linarith) hT
  rwa [hlin] at this

/-! ### Item 2 -/

theorem item2 (hK : 2 ≤ K) (hN : K + 5 ≤ N) (R B : ℝ) :
    ∃ T : ℝ, ∀ z : ℝ → Fin 4 → ℝ, IsSol N K 1 z → Init R (z 0) →
      ∀ t ≥ T, B ≤ z t 0 ∧ B ≤ z t 2 ∧ B ≤ z t 3 := by
  obtain ⟨Cv, hCv⟩ := DFS.item1 hK hN R
  set B₀ := max B 0 with hB₀
  have hBB₀ : B ≤ B₀ := le_max_left _ _
  have hB₀0 : 0 ≤ B₀ := le_max_right _ _
  obtain ⟨Tx, hTx0, hTx⟩ := D_x1 hK hN B₀
  obtain ⟨X₀, δ, hδ0, hkey⟩ := D_key hK hN B₀
  obtain ⟨Tx', hTx'0, hTx'⟩ := D_x1 hK hN X₀
  obtain ⟨T₂, hT₂0, hT₂⟩ := D_y12 hK hN (2 * B₀ + |Cv|)
  set T₃ := max T₂ Tx' with hT₃
  have hT₃0 : 0 ≤ T₃ := le_trans hT₂0 (le_max_left _ _)
  have hc : 0 ≤ B₀ / δ := div_nonneg hB₀0 hδ0.le
  refine ⟨max Tx (T₃ + B₀ / δ), ?_⟩
  intro z hz hinit t ht
  have h0 := hinit.1
  have hgood := hz.good hK hN h0
  have htx : Tx ≤ t := le_trans (le_max_left _ _) ht
  have ht3 : T₃ + B₀ / δ ≤ t := le_trans (le_max_right _ _) ht
  have ht0 : 0 ≤ t := le_trans hTx0 htx
  -- `y₂ ≥ B₀` from time `T₂` on
  have hy2 : ∀ s ≥ T₂, B₀ ≤ z s 3 := by
    intro s hs
    have h1 := hT₂ z hz h0 s hs
    have h2 := hCv z hz hinit s (le_trans hT₂0 hs)
    unfold v at h2
    have := le_abs_self Cv
    linarith
  -- `y₁ ≥ B₀` from time `T₃ + B₀ / δ` on
  have hlin : ∀ w : Fin 4 → ℝ, lin ![0, 0, 1, 0] w = w 2 := by
    intro w
    simp only [lin, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    ring
  have hr := hz.reach ![0, 0, 1, 0] B₀ δ hδ0 hT₃0 (by
    intro s hs hlt θ η hadm
    rw [hlin] at hlt ⊢
    have hs2 : T₂ ≤ s := le_trans (le_max_left _ _) hs
    have hs' : Tx' ≤ s := le_trans (le_max_right _ _) hs
    have hv : v (z s) < 0 := by
      unfold v
      have := hy2 s hs2
      linarith
    have hη : η = 0 := hadm.2.2.2.2.2 hv
    subst hη
    have := hkey (z s) (hTx' z hz h0 s hs') hlt.le θ 0 ⟨le_refl 0, zero_le_one⟩
    rwa [D_F3_zero, add_zero] at this)
  obtain ⟨-, -, hy1T, -⟩ := hgood T₃ hT₃0
  have hT : T₃ + (B₀ - lin ![0, 0, 1, 0] (z T₃)) / δ ≤ t := by
    refine le_trans ?_ ht3
    have : (B₀ - lin ![0, 0, 1, 0] (z T₃)) / δ ≤ B₀ / δ := by
      apply div_le_div_of_nonneg_right _ hδ0.le
      rw [hlin]
      linarith
    exact add_le_add_right this _
  have ht3' : T₃ ≤ t := le_trans (le_add_of_nonneg_right hc) ht3
  have hy1 := hr t ht3' hT
  rw [hlin] at hy1
  refine ⟨le_trans hBB₀ (hTx z hz h0 t htx), le_trans hBB₀ hy1, le_trans hBB₀ ?_⟩
  exact hy2 t (le_trans (le_max_left _ _) ht3')




end DFS
