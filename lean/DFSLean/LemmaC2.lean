import DFSLean.GenericDI
import DFSLean.CanonGrad

/-!
# Package L: Lemma C.2 (invariant region, monotonicity, speed bound, initial phase)
-/

noncomputable section

namespace DFS

open Real Finset Filter Topology Set
open DFS

set_option linter.unusedSectionVars false

variable {N K : ℕ}

/-! ### The open region `R'` -/

/-- `R' = {b₁ > 0, b₂ < b₁, a₂ > 0, g₁ - d₁ > 0}`. -/
def L_R (x : Fin 8 → ℝ) : Prop := 0 < x 1 ∧ x 3 < x 1 ∧ 0 < x 2 ∧ 0 < x 4 - x 5

lemma L_isOpen_R : IsOpen {x : Fin 8 → ℝ | L_R x} := by
  have h1 : Continuous fun x : Fin 8 → ℝ => x 1 := continuous_apply 1
  have h2 : Continuous fun x : Fin 8 → ℝ => x 2 := continuous_apply 2
  have h3 : Continuous fun x : Fin 8 → ℝ => x 3 := continuous_apply 3
  have h45 : Continuous fun x : Fin 8 → ℝ => x 4 - x 5 :=
    (continuous_apply 4).sub (continuous_apply 5)
  have : {x : Fin 8 → ℝ | L_R x} = {x | (0:ℝ) < x 1} ∩ {x | x 3 < x 1} ∩
      ({x | (0:ℝ) < x 2} ∩ {x | (0:ℝ) < x 4 - x 5}) := by
    ext x; simp only [L_R, mem_ofPred_eq, mem_inter_iff, and_assoc]
  rw [this]
  exact ((isOpen_lt continuous_const h1).inter (isOpen_lt h3 h1)).inter
    ((isOpen_lt continuous_const h2).inter (isOpen_lt continuous_const h45))

/-! ### Entries of `g8` on `R'` -/

section entries
variable [NeZero N] (hK : 2 ≤ K) (hN : K + 5 ≤ N) {x : Fin 8 → ℝ} {σ : (Fin 8 → ℝ) → ℝ}
  (hσ : Sel8 x σ) (hR : L_R x)
include hK hN hσ hR

lemma L_g0 : g8 N K x σ 0 = 0 := by
  rw [DFS.g8_on_R hK hN x σ hσ hR.1 hR.2.1 hR.2.2.1 hR.2.2.2]; rfl

lemma L_g1 : g8 N K x σ 1 =
    -(∑ j ∈ range K, (j : ℝ) * E8 x * σ cu8 / Q2 N K x j) - (K : ℝ) * E8 x * σ cu8 / Q4 N K x := by
  rw [DFS.g8_on_R hK hN x σ hσ hR.1 hR.2.1 hR.2.2.1 hR.2.2.2]; rfl

lemma L_g2 : g8 N K x σ 2 =
    -1 + exp (x 2) / Q1 N K x
        + ∑ j ∈ range K, (-1 + (((K : ℝ) - j) * exp (x 2) + (j : ℝ) * E8 x * σ cu8) / Q2 N K x j)
        + (K : ℝ) * E8 x * σ cu8 / Q4 N K x := by
  rw [DFS.g8_on_R hK hN x σ hσ hR.1 hR.2.1 hR.2.2.1 hR.2.2.2]; rfl

lemma L_g3 : g8 N K x σ 3 =
    eb8 x * σ cb8 * ((K : ℝ) / Q1 N K x + ∑ j ∈ range K, ((K : ℝ) - 1 - j) / Q3 N K x j) := by
  rw [DFS.g8_on_R hK hN x σ hσ hR.1 hR.2.1 hR.2.2.1 hR.2.2.2]; rfl

lemma L_g4 : g8 N K x σ 4 =
    exp (x 4 - x 5) / Q1 N K x
        + ∑ j ∈ range K, ((j : ℝ) * E8 x * σ cv8 + exp (x 4 - x 5)) / Q2 N K x j
        + ∑ j ∈ range K, (-1 + exp (x 4 - x 5) / Q3 N K x j)
        - 1 + ((K : ℝ) * E8 x * σ cv8 + exp (x 4 - x 5)) / Q4 N K x := by
  rw [DFS.g8_on_R hK hN x σ hσ hR.1 hR.2.1 hR.2.2.1 hR.2.2.2]; rfl

lemma L_g5 : g8 N K x σ 5 = -g8 N K x σ 4 := by
  rw [DFS.g8_on_R hK hN x σ hσ hR.1 hR.2.1 hR.2.2.1 hR.2.2.2]; rfl

lemma L_g6 : g8 N K x σ 6 =
    -(∑ j ∈ range K, (j : ℝ) * E8 x * σ cv8 / Q2 N K x j) - (K : ℝ) * E8 x * σ cv8 / Q4 N K x := by
  rw [DFS.g8_on_R hK hN x σ hσ hR.1 hR.2.1 hR.2.2.1 hR.2.2.2]; rfl

lemma L_g7 : g8 N K x σ 7 =
    (∑ j ∈ range K, (j : ℝ) * E8 x * σ cv8 / Q2 N K x j) + (K : ℝ) * E8 x * σ cv8 / Q4 N K x
        + ed8 x * σ cd8 * (1 / Q1 N K x + ∑ j ∈ range K, 1 / Q2 N K x j
            + ∑ j ∈ range K, 1 / Q3 N K x j + 1 / Q4 N K x) := by
  rw [DFS.g8_on_R hK hN x σ hσ hR.1 hR.2.1 hR.2.2.1 hR.2.2.2]; rfl

end entries

/-! ### Bounds on the normalizers -/

section norms
variable (x : Fin 8 → ℝ)

lemma L_one_le_eb8 : 1 ≤ eb8 x := Real.one_le_exp (le_max_right _ _)

lemma L_one_le_ed8 : 1 ≤ ed8 x := Real.one_le_exp (le_max_right _ _)

lemma L_one_le_E8 : 1 ≤ E8 x :=
  Real.one_le_exp (add_nonneg (le_max_right _ _) (le_max_right _ _))

lemma L_Q1_ge : exp (x 2) + exp (x 4 - x 5) + (N : ℝ) - 2 ≤ Q1 N K x := by
  have h1 := L_one_le_eb8 x
  have h2 := L_one_le_ed8 x
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  unfold Q1
  nlinarith

lemma L_Q2_ge (j : ℕ) :
    ((K : ℝ) - j) * exp (x 2) + exp (x 4 - x 5) + (N : ℝ) - K - 1 + j ≤ Q2 N K x j := by
  have h1 := L_one_le_E8 x
  have h2 := L_one_le_ed8 x
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  unfold Q2
  nlinarith

lemma L_Q3_ge {j : ℕ} (hj : j < K) : exp (x 4 - x 5) + (N : ℝ) - 1 ≤ Q3 N K x j := by
  have h1 := L_one_le_eb8 x
  have h2 := L_one_le_ed8 x
  have hj1 : (j : ℝ) + 1 ≤ K := by exact_mod_cast hj
  unfold Q3
  nlinarith

lemma L_Q4_ge : (K : ℝ) * E8 x + exp (x 4 - x 5) + (N : ℝ) - K - 1 ≤ Q4 N K x := by
  have h2 := L_one_le_ed8 x
  unfold Q4
  linarith

lemma L_Q1_pos (hN : K + 5 ≤ N) : 0 < Q1 N K x := by
  have := L_Q1_ge (N := N) (K := K) x
  have hNr : (K : ℝ) + 5 ≤ N := by exact_mod_cast hN
  have := exp_pos (x 2); have := exp_pos (x 4 - x 5)
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  linarith

lemma L_Q2_pos (hN : K + 5 ≤ N) {j : ℕ} (hj : j < K) : 0 < Q2 N K x j := by
  have := L_Q2_ge (N := N) (K := K) x j
  have hNr : (K : ℝ) + 5 ≤ N := by exact_mod_cast hN
  have hj1 : (j : ℝ) + 1 ≤ K := by exact_mod_cast hj
  have := exp_pos (x 2); have := exp_pos (x 4 - x 5)
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  nlinarith

lemma L_Q3_pos (hN : K + 5 ≤ N) {j : ℕ} (hj : j < K) : 0 < Q3 N K x j := by
  have := L_Q3_ge (N := N) (K := K) x hj
  have hNr : (K : ℝ) + 5 ≤ N := by exact_mod_cast hN
  have := exp_pos (x 4 - x 5)
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  linarith

lemma L_Q4_pos (hN : K + 5 ≤ N) : 0 < Q4 N K x := by
  have := L_Q4_ge (N := N) (K := K) x
  have hNr : (K : ℝ) + 5 ≤ N := by exact_mod_cast hN
  have := exp_pos (x 4 - x 5)
  have h1 := L_one_le_E8 x
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  nlinarith

end norms

/-! ### Signs of the entries of `g8` on `R'` -/

section signs
variable [NeZero N] (hK : 2 ≤ K) (hN : K + 5 ≤ N) {x : Fin 8 → ℝ} {σ : (Fin 8 → ℝ) → ℝ}
  (hσ : Sel8 x σ) (hR : L_R x)
include hK hN hσ hR

private lemma L_sum_jE_nonneg (c : Fin 8 → ℝ) :
    0 ≤ ∑ j ∈ range K, (j : ℝ) * E8 x * σ c / Q2 N K x j := by
  refine Finset.sum_nonneg fun j hj => div_nonneg ?_ (L_Q2_pos x hN (Finset.mem_range.1 hj)).le
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg j) (exp_pos _).le) (hσ c).1.1

private lemma L_KE_nonneg (c : Fin 8 → ℝ) : 0 ≤ (K : ℝ) * E8 x * σ c / Q4 N K x :=
  div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg K) (exp_pos _).le) (hσ c).1.1)
    (L_Q4_pos x hN).le

lemma L_g1_nonpos : g8 N K x σ 1 ≤ 0 := by
  rw [L_g1 hK hN hσ hR]
  have := L_sum_jE_nonneg hK hN hσ hR cu8
  have := L_KE_nonneg hK hN hσ hR cu8
  linarith

lemma L_g1_eq_zero (hu : σ cu8 = 0) : g8 N K x σ 1 = 0 := by
  rw [L_g1 hK hN hσ hR, hu]; simp

lemma L_g2_nonpos (hu : σ cu8 = 0) : g8 N K x σ 2 ≤ 0 := by
  rw [L_g2 hK hN hσ hR, hu]
  simp only [mul_zero, add_zero, zero_div]
  have hNr : (K : ℝ) + 5 ≤ N := by exact_mod_cast hN
  have h1 : exp (x 2) / Q1 N K x ≤ 1 := by
    refine div_le_one_of_le₀ ?_ (L_Q1_pos x hN).le
    have := L_Q1_ge (N := N) (K := K) x
    have := exp_pos (x 4 - x 5)
    linarith
  have h2 : ∑ j ∈ range K, (-1 + ((K : ℝ) - j) * exp (x 2) / Q2 N K x j) ≤ 0 := by
    refine Finset.sum_nonpos fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    have : ((K : ℝ) - j) * exp (x 2) / Q2 N K x j ≤ 1 := by
      refine div_le_one_of_le₀ ?_ (L_Q2_pos x hN hj').le
      have := L_Q2_ge (N := N) (K := K) x j
      have := exp_pos (x 4 - x 5)
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    linarith
  linarith

lemma L_g3_nonneg : 0 ≤ g8 N K x σ 3 := by
  rw [L_g3 hK hN hσ hR]
  refine mul_nonneg (mul_nonneg (exp_pos _).le (hσ cb8).1.1) (add_nonneg ?_ ?_)
  · exact div_nonneg (Nat.cast_nonneg K) (L_Q1_pos x hN).le
  · refine Finset.sum_nonneg fun j hj => div_nonneg ?_ (L_Q3_pos x hN (Finset.mem_range.1 hj)).le
    have : (j : ℝ) + 1 ≤ K := by exact_mod_cast Finset.mem_range.1 hj
    linarith

lemma L_g3_eq_zero (hb : σ cb8 = 0) : g8 N K x σ 3 = 0 := by
  rw [L_g3 hK hN hσ hR, hb]; simp

lemma L_g6_nonpos : g8 N K x σ 6 ≤ 0 := by
  rw [L_g6 hK hN hσ hR]
  have := L_sum_jE_nonneg hK hN hσ hR cv8
  have := L_KE_nonneg hK hN hσ hR cv8
  linarith

private lemma L_S_nonneg : 0 ≤ 1 / Q1 N K x + ∑ j ∈ range K, 1 / Q2 N K x j
            + ∑ j ∈ range K, 1 / Q3 N K x j + 1 / Q4 N K x := by
  have h1 := L_Q1_pos x hN
  have h4 := L_Q4_pos x hN
  have h2 : 0 ≤ ∑ j ∈ range K, 1 / Q2 N K x j :=
    Finset.sum_nonneg fun j hj => (one_div_pos.2 (L_Q2_pos x hN (Finset.mem_range.1 hj))).le
  have h3 : 0 ≤ ∑ j ∈ range K, 1 / Q3 N K x j :=
    Finset.sum_nonneg fun j hj => (one_div_pos.2 (L_Q3_pos x hN (Finset.mem_range.1 hj))).le
  have := one_div_pos.2 h1
  have := one_div_pos.2 h4
  linarith

lemma L_g67 : 0 ≤ g8 N K x σ 7 + g8 N K x σ 6 := by
  rw [L_g7 hK hN hσ hR, L_g6 hK hN hσ hR]
  have := L_S_nonneg hK hN hσ hR
  have := mul_nonneg (mul_nonneg (exp_pos (max (x 7) 0)).le (hσ cd8).1.1) this
  unfold ed8
  linarith

lemma L_g6_le (hv : σ cv8 = 1) : (K : ℝ) * E8 x / Q4 N K x ≤ -g8 N K x σ 6 := by
  have := L_sum_jE_nonneg hK hN hσ hR cv8
  rw [L_g6 hK hN hσ hR]
  rw [hv] at this ⊢
  simp only [mul_one] at this ⊢
  linarith

lemma L_g4_nonpos (hv : σ cv8 = 0) (hx : exp (x 4 - x 5) ≤ 2) : g8 N K x σ 4 ≤ 0 := by
  rw [L_g4 hK hN hσ hR, hv]
  simp only [mul_zero, zero_add]
  have hNr : (K : ℝ) + 5 ≤ N := by exact_mod_cast hN
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have he := exp_pos (x 4 - x 5)
  have h1 : exp (x 4 - x 5) / Q1 N K x ≤ 1 / 2 := by
    rw [div_le_iff₀ (L_Q1_pos x hN)]
    have := L_Q1_ge (N := N) (K := K) x
    have := exp_pos (x 2)
    linarith
  have h2 : ∑ j ∈ range K, exp (x 4 - x 5) / Q2 N K x j ≤ ∑ j ∈ range K, (1 / 2 : ℝ) := by
    refine Finset.sum_le_sum fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    rw [div_le_iff₀ (L_Q2_pos x hN hj')]
    have := L_Q2_ge (N := N) (K := K) x j
    have := exp_pos (x 2)
    have hj1 : (j : ℝ) + 1 ≤ K := by exact_mod_cast hj'
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith
  have h3 : ∑ j ∈ range K, (-1 + exp (x 4 - x 5) / Q3 N K x j) ≤
      ∑ j ∈ range K, (-1 + 1 / 3 : ℝ) := by
    refine Finset.sum_le_sum fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    have : exp (x 4 - x 5) / Q3 N K x j ≤ 1 / 3 := by
      rw [div_le_iff₀ (L_Q3_pos x hN hj')]
      have := L_Q3_ge (N := N) (K := K) x hj'
      linarith
    linarith
  have h4 : exp (x 4 - x 5) / Q4 N K x ≤ 1 / 3 := by
    rw [div_le_iff₀ (L_Q4_pos x hN)]
    have := L_Q4_ge (N := N) (K := K) x
    have := L_one_le_E8 x
    nlinarith
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2 h3
  nlinarith

lemma L_g3_ge (hb : σ cb8 = 1) : 1 / Q1 N K x ≤ g8 N K x σ 3 := by
  rw [L_g3 hK hN hσ hR, hb, mul_one]
  have hQ := L_Q1_pos x hN
  have hS : 0 ≤ ∑ j ∈ range K, ((K : ℝ) - 1 - j) / Q3 N K x j := by
    refine Finset.sum_nonneg fun j hj => div_nonneg ?_ (L_Q3_pos x hN (Finset.mem_range.1 hj)).le
    have : (j : ℝ) + 1 ≤ K := by exact_mod_cast Finset.mem_range.1 hj
    linarith
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  have h1 : 1 / Q1 N K x ≤ (K : ℝ) / Q1 N K x := div_le_div_of_nonneg_right hK1 hQ.le
  calc 1 / Q1 N K x ≤ (K : ℝ) / Q1 N K x + ∑ j ∈ range K, ((K : ℝ) - 1 - j) / Q3 N K x j := by
        linarith
    _ ≤ _ := le_mul_of_one_le_left (by positivity) (L_one_le_eb8 x)

lemma L_g7_ge (hd : σ cd8 = 1) : 1 / Q1 N K x ≤ g8 N K x σ 7 := by
  have hA := L_sum_jE_nonneg hK hN hσ hR cv8
  have hB := L_KE_nonneg hK hN hσ hR cv8
  rw [L_g7 hK hN hσ hR, hd, mul_one]
  have h2 : 0 ≤ ∑ j ∈ range K, 1 / Q2 N K x j :=
    Finset.sum_nonneg fun j hj => (one_div_pos.2 (L_Q2_pos x hN (Finset.mem_range.1 hj))).le
  have h3 : 0 ≤ ∑ j ∈ range K, 1 / Q3 N K x j :=
    Finset.sum_nonneg fun j hj => (one_div_pos.2 (L_Q3_pos x hN (Finset.mem_range.1 hj))).le
  have h4 := one_div_pos.2 (L_Q4_pos x hN)
  have hS := L_S_nonneg hK hN hσ hR
  have := le_mul_of_one_le_left hS (L_one_le_ed8 x)
  linarith

end signs

/-! ### Coordinates, `P8`, functionals -/

/-- Coordinate vector `e_m`. -/
def L_e (m : Fin 8) : Fin 8 → ℝ := Pi.single m 1

@[simp] lemma L_e_dot (m : Fin 8) (v : Fin 8 → ℝ) : L_e m ⬝ᵥ v = v m := by
  simp [L_e, single_dotProduct]

lemma L_cu8_dot (x : Fin 8 → ℝ) : cu8 ⬝ᵥ x = x 2 - x 1 := by
  simp [cu8, dotProduct, Fin.sum_univ_eight]; ring

lemma L_cv8_dot (x : Fin 8 → ℝ) : cv8 ⬝ᵥ x = x 4 - x 5 - x 6 + x 7 := by
  simp [cv8, dotProduct, Fin.sum_univ_eight]; ring

lemma L_cb8_dot (x : Fin 8 → ℝ) : cb8 ⬝ᵥ x = x 3 := by
  simp [cb8, dotProduct, Fin.sum_univ_eight]

lemma L_cd8_dot (x : Fin 8 → ℝ) : cd8 ⬝ᵥ x = x 7 := by
  simp [cd8, dotProduct, Fin.sum_univ_eight]

lemma L_P8_pos (hN2 : 2 ≤ N) (m : Fin 8) : 0 < P8 N m := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN2
  unfold P8
  split_ifs
  · exact one_div_pos.2 (by linarith)
  · exact one_div_pos.2 (mul_pos (by linarith) (by linarith))

lemma L_P8_le (hN2 : 2 ≤ N) (m : Fin 8) : P8 N m ≤ 1 / N := by
  have hN1 : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  unfold P8
  split_ifs
  · exact le_rfl
  · exact one_div_le_one_div_of_le (by linarith) (by nlinarith)

lemma L_P8_3 : P8 N 3 = 1 / ((N : ℝ) * (N - 1)) := by
  unfold P8; split_ifs with h
  · exact absurd h (by decide)
  · rfl

lemma L_P8_7 : P8 N 7 = 1 / ((N : ℝ) * (N - 1)) := by
  unfold P8; split_ifs with h
  · exact absurd h (by decide)
  · rfl

/-! ### Velocities on `R'` -/

section vel
variable [NeZero N] (hK : 2 ≤ K) (hN : K + 5 ≤ N) {α : ℝ} (hα : 0 < α) {x : Fin 8 → ℝ}
  (hR : L_R x) {w : Fin 8 → ℝ} (hw : w ∈ V8 N K α x)
include hK hN hα hR hw

lemma L_w0 : w 0 = 0 := by
  obtain ⟨σ, hσ, rfl⟩ := hw
  show -α * P8 N 0 * g8 N K x σ 0 = 0
  rw [L_g0 hK hN hσ hR]; ring

lemma L_w1 : 0 ≤ w 1 := by
  obtain ⟨σ, hσ, rfl⟩ := hw
  show 0 ≤ -α * P8 N 1 * g8 N K x σ 1
  have := L_g1_nonpos hK hN hσ hR
  have := L_P8_pos (by omega : 2 ≤ N) 1
  have := mul_nonneg (mul_nonneg hα.le this.le) (neg_nonneg.2 (L_g1_nonpos hK hN hσ hR))
  linarith

lemma L_w3 : w 3 ≤ 0 := by
  obtain ⟨σ, hσ, rfl⟩ := hw
  show -α * P8 N 3 * g8 N K x σ 3 ≤ 0
  have := L_P8_pos (by omega : 2 ≤ N) 3
  have := mul_nonneg (mul_nonneg hα.le this.le) (L_g3_nonneg hK hN hσ hR)
  linarith

lemma L_w7 : w 7 ≤ 0 := by
  obtain ⟨σ, hσ, rfl⟩ := hw
  show -α * P8 N 7 * g8 N K x σ 7 ≤ 0
  have := L_P8_pos (by omega : 2 ≤ N) 7
  have h6 := L_g6_nonpos hK hN hσ hR
  have h67 := L_g67 hK hN hσ hR
  have := mul_nonneg (mul_nonneg hα.le this.le) (by linarith : 0 ≤ g8 N K x σ 7)
  linarith

lemma L_wy2 : 0 ≤ w 6 - w 7 := by
  obtain ⟨σ, hσ, rfl⟩ := hw
  show 0 ≤ -α * P8 N 6 * g8 N K x σ 6 - -α * P8 N 7 * g8 N K x σ 7
  have h6 := L_g6_nonpos hK hN hσ hR
  have h67 := L_g67 hK hN hσ hR
  have A := mul_nonneg (mul_nonneg hα.le (L_P8_pos (by omega : 2 ≤ N) 6).le) (neg_nonneg.2 h6)
  have B := mul_nonneg (mul_nonneg hα.le (L_P8_pos (by omega : 2 ≤ N) 7).le)
    (by linarith : 0 ≤ g8 N K x σ 7)
  linarith

lemma L_wy2_pos (hv : 0 < x 4 - x 5 - x 6 + x 7) :
    α * P8 N 6 * ((K : ℝ) * E8 x / Q4 N K x) ≤ w 6 - w 7 := by
  obtain ⟨σ, hσ, rfl⟩ := hw
  show _ ≤ -α * P8 N 6 * g8 N K x σ 6 - -α * P8 N 7 * g8 N K x σ 7
  have hv1 : σ cv8 = 1 := (hσ cv8).2.1 (by rw [L_cv8_dot]; exact hv)
  have h6 := L_g6_nonpos hK hN hσ hR
  have h67 := L_g67 hK hN hσ hR
  have hle := L_g6_le hK hN hσ hR hv1
  have A := mul_le_mul_of_nonneg_left hle
    (mul_nonneg hα.le (L_P8_pos (by omega : 2 ≤ N) 6).le)
  have B := mul_nonneg (mul_nonneg hα.le (L_P8_pos (by omega : 2 ≤ N) 7).le)
    (by linarith : 0 ≤ g8 N K x σ 7)
  linarith

lemma L_wu (hu : x 2 - x 1 < 0) : 0 ≤ w 2 - w 1 := by
  obtain ⟨σ, hσ, rfl⟩ := hw
  show 0 ≤ -α * P8 N 2 * g8 N K x σ 2 - -α * P8 N 1 * g8 N K x σ 1
  have hu0 : σ cu8 = 0 := (hσ cu8).2.2 (by rw [L_cu8_dot]; exact hu)
  rw [L_g1_eq_zero hK hN hσ hR hu0]
  have := mul_nonneg (mul_nonneg hα.le (L_P8_pos (by omega : 2 ≤ N) 2).le)
    (neg_nonneg.2 (L_g2_nonpos hK hN hσ hR hu0))
  linarith

lemma L_wb (hb : x 3 < 0) : w 3 = 0 := by
  obtain ⟨σ, hσ, rfl⟩ := hw
  show -α * P8 N 3 * g8 N K x σ 3 = 0
  have hb0 : σ cb8 = 0 := (hσ cb8).2.2 (by rw [L_cb8_dot]; exact hb)
  rw [L_g3_eq_zero hK hN hσ hR hb0]; ring

lemma L_wy1 (hx : exp (x 4 - x 5) ≤ 2) (hv : x 4 - x 5 - x 6 + x 7 < 0) : 0 ≤ w 4 - w 5 := by
  obtain ⟨σ, hσ, rfl⟩ := hw
  show 0 ≤ -α * P8 N 4 * g8 N K x σ 4 - -α * P8 N 5 * g8 N K x σ 5
  have hv0 : σ cv8 = 0 := (hσ cv8).2.2 (by rw [L_cv8_dot]; exact hv)
  rw [L_g5 hK hN hσ hR]
  have h4 := L_g4_nonpos hK hN hσ hR hv0 hx
  have := mul_nonneg (mul_nonneg hα.le
    (add_pos (L_P8_pos (by omega : 2 ≤ N) 4) (L_P8_pos (by omega : 2 ≤ N) 5)).le) (neg_nonneg.2 h4)
  linarith

lemma L_wlip (m : Fin 8) : |w m| ≤ (2 * K + 2) * α * P8 N m := by
  obtain ⟨σ, hσ, rfl⟩ := hw
  show |-α * P8 N m * g8 N K x σ m| ≤ _
  have hP := L_P8_pos (by omega : 2 ≤ N) m
  have hb := DFS.g8_bound_on_R hK hN x σ hσ hR.1 hR.2.1 hR.2.2.1 hR.2.2.2 m
  rw [abs_mul, abs_mul, abs_neg, abs_of_pos hα, abs_of_pos hP]
  have := mul_le_mul_of_nonneg_left hb (mul_nonneg hα.le hP.le)
  linarith

lemma L_w3_rate (hb : 0 < x 3) : w 3 ≤ -(α * P8 N 3 / Q1 N K x) := by
  obtain ⟨σ, hσ, rfl⟩ := hw
  show -α * P8 N 3 * g8 N K x σ 3 ≤ _
  have hb1 : σ cb8 = 1 := (hσ cb8).2.1 (by rw [L_cb8_dot]; exact hb)
  have h := L_g3_ge hK hN hσ hR hb1
  have := mul_le_mul_of_nonneg_left h (mul_nonneg hα.le (L_P8_pos (by omega : 2 ≤ N) 3).le)
  rw [mul_one_div] at this
  linarith

lemma L_w7_rate (hd : 0 < x 7) : w 7 ≤ -(α * P8 N 7 / Q1 N K x) := by
  obtain ⟨σ, hσ, rfl⟩ := hw
  show -α * P8 N 7 * g8 N K x σ 7 ≤ _
  have hd1 : σ cd8 = 1 := (hσ cd8).2.1 (by rw [L_cd8_dot]; exact hd)
  have h := L_g7_ge hK hN hσ hR hd1
  have := mul_le_mul_of_nonneg_left h (mul_nonneg hα.le (L_P8_pos (by omega : 2 ≤ N) 7).le)
  rw [mul_one_div] at this
  linarith

end vel

/-! ### The region on an interval where `R'` holds -/

section region
variable [NeZero N] (hK : 2 ≤ K) (hN : K + 5 ≤ N) {c0 c0' α : ℝ} (h0 : 0 < c0')
  (h1 : c0' < c0) (hα : 0 < α) {s : ℝ → Fin 8 → ℝ} (hs : IsSol8 N K α s)
  (hs0 : s 0 = init8 c0 c0')

private lemma L_nonincr (hs : IsSol8 N K α s) (c : Fin 8 → ℝ) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (h : ∀ t ∈ Ico a b, ∀ w ∈ V8 N K α (s t), c ⬝ᵥ w ≤ 0) :
    c ⬝ᵥ s b ≤ c ⬝ᵥ s a := by
  have := DFS.IsDI.dot_le (V := V8 N K α) hs c 0 ha hab h
  simpa using this

include hK hN hα hs in
/-- Monotonicity on an interval where `R'` holds. -/
lemma L_mono_on {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (h12 : t₁ ≤ t₂)
    (hR : ∀ t ∈ Ico t₁ t₂, L_R (s t)) :
    s t₁ 1 ≤ s t₂ 1 ∧ s t₂ 3 ≤ s t₁ 3 ∧ s t₁ 6 - s t₁ 7 ≤ s t₂ 6 - s t₂ 7 ∧
      s t₂ 7 ≤ s t₁ 7 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := L_nonincr hs (-L_e 1) ht₁ h12 (fun t ht w hw => by
      simp only [neg_dotProduct, L_e_dot]; have := L_w1 hK hN hα (hR t ht) hw; linarith)
    simp only [neg_dotProduct, L_e_dot] at this; linarith
  · have := L_nonincr hs (L_e 3) ht₁ h12 (fun t ht w hw => by
      simp only [L_e_dot]; exact L_w3 hK hN hα (hR t ht) hw)
    simpa using this
  · have := L_nonincr hs (L_e 7 - L_e 6) ht₁ h12 (fun t ht w hw => by
      simp only [sub_dotProduct, L_e_dot]; have := L_wy2 hK hN hα (hR t ht) hw; linarith)
    simp only [sub_dotProduct, L_e_dot] at this; linarith
  · have := L_nonincr hs (L_e 7) ht₁ h12 (fun t ht w hw => by
      simp only [L_e_dot]; exact L_w7 hK hN hα (hR t ht) hw)
    simpa using this

include hK hN h0 h1 hα hs hs0 in
/-- Everything except `y₁ > 0`, on `[0, T]`, from `R'` on `[0, T)`. -/
lemma L_core_basic {T : ℝ} (hRT : ∀ t ∈ Ico 0 T, L_R (s t)) :
    ∀ t ∈ Icc 0 T, s t 0 = c0 ∧ c0 ≤ s t 1 ∧ 0 ≤ s t 3 ∧ s t 3 ≤ c0' ∧ s t 1 ≤ s t 2 ∧
      0 ≤ s t 6 - s t 7 ∧ s t 7 ≤ c0 := by
  intro t ht
  have hR : ∀ t' ∈ Ico 0 t, L_R (s t') := fun t' ht' => hRT t' ⟨ht'.1, ht'.2.trans_le ht.2⟩
  have hi : ∀ m, s 0 m = init8 c0 c0' m := fun m => by rw [hs0]
  obtain ⟨hm1, hm3, hm6, hm7⟩ := L_mono_on hK hN hα hs le_rfl ht.1 hR
  have i0 : s 0 0 = c0 := hi 0
  have i1 : s 0 1 = c0 := hi 1
  have i2 : s 0 2 = c0 := hi 2
  have i3 : s 0 3 = c0' := hi 3
  have i6 : s 0 6 = c0 := hi 6
  have i7 : s 0 7 = c0 := hi 7
  refine ⟨?_, by linarith, ?_, by linarith, ?_, by linarith, by linarith⟩
  · have A := L_nonincr hs (L_e 0) le_rfl ht.1 (fun t' ht' w hw => by
      simp only [L_e_dot]; rw [L_w0 hK hN hα (hR t' ht') hw])
    have B := L_nonincr hs (-L_e 0) le_rfl ht.1 (fun t' ht' w hw => by
      simp only [neg_dotProduct, L_e_dot]; rw [L_w0 hK hN hα (hR t' ht') hw]; simp)
    simp only [neg_dotProduct, L_e_dot] at A B
    linarith
  · have := DFS.IsDI.barrier (V := V8 N K α) hs (-L_e 3) 0 le_rfl (b := t)
      (fun t' ht' hlt w hw => by
        simp only [neg_dotProduct, L_e_dot] at hlt ⊢
        rw [L_wb hK hN hα (hR t' ht') hw (by linarith)]; simp) t ⟨ht.1, le_rfl⟩
    simp only [neg_dotProduct, L_e_dot, i3] at this
    have : -c0' ≤ 0 := by linarith
    rw [max_eq_right this] at *
    linarith
  · have := DFS.IsDI.barrier (V := V8 N K α) hs (L_e 1 - L_e 2) 0 le_rfl (b := t)
      (fun t' ht' hlt w hw => by
        simp only [sub_dotProduct, L_e_dot] at hlt ⊢
        have := L_wu hK hN hα (hR t' ht') hw (by linarith); linarith) t ⟨ht.1, le_rfl⟩
    simp only [sub_dotProduct, L_e_dot, i1, i2, sub_self, max_self] at this
    linarith

include hK hN h0 h1 hα hs hs0 in
/-- `y₁ > 0` on `[0, T]`, from `R'` on `[0, T)`. -/
lemma L_core_y1 {T : ℝ} (hRT : ∀ t ∈ Ico 0 T, L_R (s t)) :
    ∀ t ∈ Icc 0 T, 0 < s t 4 - s t 5 := by
  intro t ht
  have hi : ∀ m, s 0 m = init8 c0 c0' m := fun m => by rw [hs0]
  have i4 : s 0 4 = c0 := hi 4
  have i5 : s 0 5 = c0' := hi 5
  have i6 : s 0 6 = c0 := hi 6
  have i7 : s 0 7 = c0 := hi 7
  rcases eq_or_lt_of_le ht.1 with h | htpos
  · subst h; rw [i4, i5]; linarith
  -- Step 1: `y₂` becomes positive right after `0`.
  have hR0 : L_R (s 0) := hRT 0 ⟨le_rfl, htpos.trans_le ht.2⟩
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hδpos : 0 < α * P8 N 6 * ((K : ℝ) * E8 (s 0) / Q4 N K (s 0)) :=
    mul_pos (mul_pos hα (L_P8_pos (by omega) 6))
      (div_pos (mul_pos hKpos (exp_pos _)) (L_Q4_pos _ hN))
  have hev := DFS.IsDI.slope_dot (V := V8 N K α) hs (L_e 6 - L_e 7) (L_e 6 - L_e 7)
    (t := 0) le_rfl hδpos
  obtain ⟨a, ⟨w, hw, hlt, -⟩, haI⟩ := (hev.and (Ioo_mem_nhdsGT htpos)).exists
  simp only [zero_add, sub_dotProduct, L_e_dot, i6, i7, sub_self, sub_zero] at hlt
  have hv0 : 0 < s 0 4 - s 0 5 - s 0 6 + s 0 7 := by rw [i4, i5, i6, i7]; linarith
  have hwv := L_wy2_pos hK hN hα hR0 hw hv0
  have hy2a : 0 < s a 6 - s a 7 := by
    have := (abs_lt.1 hlt).1
    have hq : 0 < (s a 6 - s a 7) / a := by linarith
    exact (div_pos_iff_of_pos_right haI.1).1 hq
  -- Step 2: a barrier for `-y₁` at level `-ℓ`.
  have hRa : L_R (s a) := hRT a ⟨haI.1.le, haI.2.trans_le ht.2⟩
  have hℓ : 0 < min (s a 6 - s a 7) (log 2) := lt_min hy2a (Real.log_pos one_lt_two)
  have key := DFS.IsDI.barrier (V := V8 N K α) hs (L_e 5 - L_e 4)
    (-min (s a 6 - s a 7) (log 2)) haI.1.le (b := t)
    (fun t' ht' hlt' w hw => by
      simp only [sub_dotProduct, L_e_dot] at hlt' ⊢
      have hRt' : L_R (s t') := hRT t' ⟨haI.1.le.trans ht'.1, ht'.2.trans_le ht.2⟩
      have hm := (L_mono_on hK hN hα hs haI.1.le ht'.1 (fun t'' ht'' =>
        hRT t'' ⟨haI.1.le.trans ht''.1, ht''.2.trans_le (ht'.2.le.trans ht.2)⟩)).2.2.1
      have hexp : exp (s t' 4 - s t' 5) ≤ 2 := by
        have : s t' 4 - s t' 5 < log 2 := by
          have := min_le_right (s a 6 - s a 7) (log 2); linarith
        have := exp_lt_exp.2 this
        rw [exp_log two_pos] at this
        exact this.le
      have hv : s t' 4 - s t' 5 - s t' 6 + s t' 7 < 0 := by
        have := min_le_left (s a 6 - s a 7) (log 2); linarith
      have := L_wy1 hK hN hα hRt' hw hexp hv
      linarith) t ⟨haI.2.le, le_rfl⟩
  simp only [sub_dotProduct, L_e_dot] at key
  have ha45 : s a 5 - s a 4 < 0 := by linarith [hRa.2.2.2]
  have := max_lt ha45 (neg_neg_of_pos hℓ)
  linarith

/-- The conclusion of `lemmaC2_region` at one state. -/
def L_Reg (c0 c0' : ℝ) (x : Fin 8 → ℝ) : Prop :=
  x 0 = c0 ∧ c0 ≤ x 1 ∧ 0 ≤ x 3 ∧ x 3 ≤ c0' ∧ x 1 ≤ x 2 ∧
      0 < x 4 - x 5 ∧ 0 ≤ x 6 - x 7 ∧ x 7 ≤ c0

include hK hN h0 h1 hα hs hs0 in
lemma L_core {T : ℝ} (hRT : ∀ t ∈ Ico 0 T, L_R (s t)) :
    ∀ t ∈ Icc 0 T, L_Reg c0 c0' (s t) := by
  intro t ht
  obtain ⟨a, b, c, d, e, f, g⟩ := L_core_basic hK hN h0 h1 hα hs hs0 hRT t ht
  exact ⟨a, b, c, d, e, L_core_y1 hK hN h0 h1 hα hs hs0 hRT t ht, f, g⟩

include h0 h1 in
lemma L_R_of_Reg {x : Fin 8 → ℝ} (h : L_Reg c0 c0' x) : L_R x := by
  obtain ⟨_, hb1, hb3, hb3', hu, hy, _, _⟩ := h
  exact ⟨by linarith, by linarith, by linarith, hy⟩

include hK hN h0 h1 hα hs hs0 in
lemma L_R_all : ∀ t ≥ 0, L_R (s t) := by
  by_contra hne
  push Not at hne
  have hBne : ({t : ℝ | 0 ≤ t ∧ ¬ L_R (s t)}).Nonempty := hne
  have hBbdd : BddBelow {t : ℝ | 0 ≤ t ∧ ¬ L_R (s t)} := ⟨0, fun t ht => ht.1⟩
  have hBclosed : IsClosed {t : ℝ | 0 ≤ t ∧ ¬ L_R (s t)} := by
    have := ContinuousOn.preimage_isClosed_of_isClosed (hs.1 : ContinuousOn s (Ici 0))
      isClosed_Ici (L_isOpen_R.isClosed_compl)
    convert this using 1
    ext t; exact Iff.rfl
  have hmem := hBclosed.csInf_mem hBne hBbdd
  have hlt : ∀ t ∈ Ico 0 (sInf {t : ℝ | 0 ≤ t ∧ ¬ L_R (s t)}), L_R (s t) := by
    intro t ht
    by_contra h
    have := csInf_le hBbdd ⟨ht.1, h⟩
    linarith [ht.2]
  exact hmem.2 (L_R_of_Reg h0 h1
    (L_core hK hN h0 h1 hα hs hs0 hlt _ ⟨hmem.1, le_rfl⟩))

end region

/-! ### Lemma C.2 -/

section lemmaC2
variable [NeZero N]

/-- Lemma C.2, item 1 (region; `b₂ ∈ [0, c₀']` since `b₂` freezes at `0`). -/
theorem lemmaC2_region (hK : 2 ≤ K) (hN : K + 5 ≤ N) {c0 c0' α : ℝ} (h0 : 0 < c0')
    (h1 : c0' < c0) (hα : 0 < α) {s : ℝ → Fin 8 → ℝ} (hs : IsSol8 N K α s)
    (hs0 : s 0 = init8 c0 c0') :
    ∀ t ≥ 0, s t 0 = c0 ∧ c0 ≤ s t 1 ∧ 0 ≤ s t 3 ∧ s t 3 ≤ c0' ∧ s t 1 ≤ s t 2 ∧
      0 < s t 4 - s t 5 ∧ 0 ≤ s t 6 - s t 7 ∧ s t 7 ≤ c0 := by
  intro t ht
  exact L_core hK hN h0 h1 hα hs hs0 (T := t)
    (fun t' ht' => L_R_all hK hN h0 h1 hα hs hs0 t' ht'.1) t ⟨ht, le_rfl⟩



/-- Lemma C.2, item 1 (monotonicity): `b₁ ↑`, `b₂ ↓`, `g₂ - d₂ ↑`, `d₂ ↓`. -/
theorem lemmaC2_mono (hK : 2 ≤ K) (hN : K + 5 ≤ N) {c0 c0' α : ℝ} (h0 : 0 < c0')
    (h1 : c0' < c0) (hα : 0 < α) {s : ℝ → Fin 8 → ℝ} (hs : IsSol8 N K α s)
    (hs0 : s 0 = init8 c0 c0') :
    ∀ t₁ t₂, 0 ≤ t₁ → t₁ ≤ t₂ → s t₁ 1 ≤ s t₂ 1 ∧ s t₂ 3 ≤ s t₁ 3 ∧
      s t₁ 6 - s t₁ 7 ≤ s t₂ 6 - s t₂ 7 ∧ s t₂ 7 ≤ s t₁ 7 := by
  intro t₁ t₂ ht₁ h12
  exact L_mono_on hK hN hα hs ht₁ h12
    (fun t ht => L_R_all hK hN h0 h1 hα hs hs0 t (ht₁.trans ht.1))



/-- Speed bound from eq. `grad_bound` and eq. `scalar_flow`. -/
theorem lemmaC2_lip (hK : 2 ≤ K) (hN : K + 5 ≤ N) {c0 c0' α : ℝ} (h0 : 0 < c0')
    (h1 : c0' < c0) (hα : 0 < α) {s : ℝ → Fin 8 → ℝ} (hs : IsSol8 N K α s)
    (hs0 : s 0 = init8 c0 c0') :
    ∀ t₁ t₂, 0 ≤ t₁ → t₁ ≤ t₂ → ∀ m, |s t₂ m - s t₁ m| ≤ (2 * K + 2) * α * P8 N m * (t₂ - t₁) := by
  intro t₁ t₂ ht₁ h12 m
  have hR : ∀ t ∈ Ico t₁ t₂, L_R (s t) :=
    fun t ht => L_R_all hK hN h0 h1 hα hs hs0 t (ht₁.trans ht.1)
  have A := DFS.IsDI.dot_le (V := V8 N K α) hs (L_e m) ((2 * K + 2) * α * P8 N m) ht₁ h12
    (fun t ht w hw => by
      simp only [L_e_dot]
      exact (le_abs_self _).trans (L_wlip hK hN hα (hR t ht) hw m))
  have B := DFS.IsDI.dot_le (V := V8 N K α) hs (-L_e m) ((2 * K + 2) * α * P8 N m) ht₁ h12
    (fun t ht w hw => by
      simp only [neg_dotProduct, L_e_dot]
      exact (neg_le_abs _).trans (L_wlip hK hN hα (hR t ht) hw m))
  simp only [neg_dotProduct, L_e_dot] at A B
  rw [abs_sub_le_iff]
  constructor <;> linarith



end lemmaC2

/-! ### The initial phase -/

private lemma L_Q1_le (x : Fin 8 → ℝ) (h2 : x 2 ≤ 2) (h45 : x 4 - x 5 ≤ 2) (h3 : x 3 ≤ 2)
    (h7 : x 7 ≤ 2) : Q1 N K x ≤ N + ((K : ℝ) + 3) * exp 2 := by
  have e1 : exp (x 2) ≤ exp 2 := exp_le_exp.2 h2
  have e2 : exp (x 4 - x 5) ≤ exp 2 := exp_le_exp.2 h45
  have e3 : eb8 x ≤ exp 2 := exp_le_exp.2 (max_le h3 (by norm_num))
  have e4 : ed8 x ≤ exp 2 := exp_le_exp.2 (max_le h7 (by norm_num))
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have e5 : (1 : ℝ) ≤ exp 2 := one_le_exp (by norm_num)
  have e6 := mul_le_mul_of_nonneg_left e3 hK0
  unfold Q1
  nlinarith

/-- Lemma C.2, item 2 (initial phase): after `T₀`, `b₂ = 0` and `d₂ ≤ 0`. -/
theorem lemmaC2_initial (hK : 2 ≤ K) :
    ∃ cstar : ℝ, 0 < cstar ∧ ∀ (N : ℕ) [NeZero N], K + 5 ≤ N →
      ∀ c0 c0' α : ℝ, 0 < c0' → c0' < c0 → c0 ≤ cstar / (N : ℝ) ^ 2 → 0 < α →
      ∀ s : ℝ → Fin 8 → ℝ, IsSol8 N K α s → s 0 = init8 c0 c0' →
      ∀ t ≥ T0 N K α, s t 3 = 0 ∧ s t 7 ≤ 0 := by
  refine ⟨1 / (4 * ((K : ℝ) + 1) * (1 + ((K : ℝ) + 3) * exp 2)), by positivity, ?_⟩
  intro N _ hN c0 c0' α h0 h1 hc0 hα s hs hs0
  have hC0 : 0 ≤ ((K : ℝ) + 3) * exp 2 := by positivity
  have hNr : (K : ℝ) + 5 ≤ N := by exact_mod_cast hN
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hN2 : 2 ≤ N := by omega
  have hreg := lemmaC2_region hK hN h0 h1 hα hs hs0
  have hmono := lemmaC2_mono hK hN h0 h1 hα hs hs0
  have hlip := lemmaC2_lip hK hN h0 h1 hα hs hs0
  have hRall := L_R_all hK hN h0 h1 hα hs hs0
  have hT0 : 0 < T0 N K α := by unfold T0; positivity
  have hi : ∀ m, s 0 m = init8 c0 c0' m := fun m => by rw [hs0]
  -- `c₀ ≤ 1/2`
  have hc0h : c0 ≤ 1 / 2 := by
    refine hc0.trans ?_
    have hN1 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have hc1 : 1 / (4 * ((K : ℝ) + 1) * (1 + ((K : ℝ) + 3) * exp 2)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    calc 1 / (4 * ((K : ℝ) + 1) * (1 + ((K : ℝ) + 3) * exp 2)) / (N : ℝ) ^ 2
        ≤ 1 / (4 * ((K : ℝ) + 1) * (1 + ((K : ℝ) + 3) * exp 2)) :=
          div_le_self (by positivity) hN1
      _ ≤ 1 / 2 := hc1
  -- displacement on `[0, T₀]`
  have hdisp : ∀ t ∈ Icc 0 (T0 N K α), ∀ m, |s t m - s 0 m| ≤ 1 / 2 := by
    intro t ht m
    refine (hlip 0 t le_rfl ht.1 m).trans ?_
    have hP := L_P8_le hN2 m
    have hPp := L_P8_pos hN2 m
    have h2 : (2 * K + 2) * α * P8 N m * (t - 0) ≤ (2 * K + 2) * α * (1 / N) * T0 N K α := by
      have : (0 : ℝ) ≤ (2 * K + 2) * α := by positivity
      have h' := mul_le_mul hP (by linarith [ht.2] : t - 0 ≤ T0 N K α) (by linarith [ht.1])
        (by positivity)
      have := mul_le_mul_of_nonneg_left h' this
      linarith [this]
    have h3 : (2 * K + 2) * α * (1 / N) * T0 N K α = 1 / 2 := by
      unfold T0
      have : (N : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    linarith
  -- the normalizer `Q₁` on `[0, T₀]`
  have hQ : ∀ t ∈ Icc 0 (T0 N K α), Q1 N K (s t) ≤ N + ((K : ℝ) + 3) * exp 2 := by
    intro t ht
    have d2 := abs_le.1 (hdisp t ht 2)
    have d4 := abs_le.1 (hdisp t ht 4)
    have d5 := abs_le.1 (hdisp t ht 5)
    have r := hreg t ht.1
    have i2 : s 0 2 = c0 := hi 2
    have i4 : s 0 4 = c0 := hi 4
    have i5 : s 0 5 = c0' := hi 5
    exact L_Q1_le _ (by linarith) (by linarith) (by linarith [r.2.2.2.1]) (by linarith [r.2.2.2.2.2.2.2])
  -- the decrease over `[0, T₀]`
  have hrate : c0 ≤ α * P8 N 3 / (N + ((K : ℝ) + 3) * exp 2) * T0 N K α := by
    have e : α * P8 N 3 / (N + ((K : ℝ) + 3) * exp 2) * T0 N K α =
        1 / (4 * ((K : ℝ) + 1) * ((N : ℝ) - 1) * (N + ((K : ℝ) + 3) * exp 2)) := by
      rw [L_P8_3]
      unfold T0
      have : (N : ℝ) - 1 ≠ 0 := by linarith
      have : (N : ℝ) ≠ 0 := by linarith
      have : (N : ℝ) + ((K : ℝ) + 3) * exp 2 ≠ 0 := by positivity
      have : α ≠ 0 := hα.ne'
      field_simp
    rw [e]
    refine hc0.trans ?_
    have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
    have hNC : (0 : ℝ) < (N : ℝ) + ((K : ℝ) + 3) * exp 2 := by positivity
    rw [div_div, div_le_div_iff₀ (by positivity)
      (mul_pos (mul_pos (by positivity) hN1) hNC)]
    have : ((N : ℝ) - 1) * (N + ((K : ℝ) + 3) * exp 2) ≤
        (1 + ((K : ℝ) + 3) * exp 2) * (N : ℝ) ^ 2 := by
      have := mul_nonneg hC0 (mul_nonneg (by positivity : (0 : ℝ) ≤ N) hN1.le)
      nlinarith
    have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 4 * ((K : ℝ) + 1))
    nlinarith
  have hP37 : P8 N 7 = P8 N 3 := by rw [L_P8_3, L_P8_7]
  have hspeed : ∀ t ∈ Ico 0 (T0 N K α), α * P8 N 3 / (N + ((K : ℝ) + 3) * exp 2) ≤
      α * P8 N 3 / Q1 N K (s t) := fun t ht =>
    div_le_div_of_nonneg_left (mul_nonneg hα.le (L_P8_pos hN2 3).le) (L_Q1_pos _ hN)
      (hQ t ⟨ht.1, ht.2.le⟩)
  -- `b₂`
  have hb : s (T0 N K α) 3 ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have := DFS.IsDI.dot_le (V := V8 N K α) hs (L_e 3)
      (-(α * P8 N 3 / (N + ((K : ℝ) + 3) * exp 2))) le_rfl hT0.le (fun t ht w hw => by
        simp only [L_e_dot]
        have hpos' : 0 < s t 3 := lt_of_lt_of_le hpos (hmono t _ ht.1 ht.2.le).2.1
        have h := L_w3_rate hK hN hα (hRall t ht.1) hw hpos'
        linarith [hspeed t ht])
    simp only [L_e_dot, hi 3] at this
    have i3 : init8 c0 c0' 3 = c0' := rfl
    rw [i3] at this
    nlinarith
  -- `d₂`
  have hd : s (T0 N K α) 7 ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have := DFS.IsDI.dot_le (V := V8 N K α) hs (L_e 7)
      (-(α * P8 N 3 / (N + ((K : ℝ) + 3) * exp 2))) le_rfl hT0.le (fun t ht w hw => by
        simp only [L_e_dot]
        have hpos' : 0 < s t 7 := lt_of_lt_of_le hpos (hmono t _ ht.1 ht.2.le).2.2.2
        have h := L_w7_rate hK hN hα (hRall t ht.1) hw hpos'
        rw [hP37] at h
        linarith [hspeed t ht])
    simp only [L_e_dot, hi 7] at this
    have i7 : init8 c0 c0' 7 = c0 := rfl
    rw [i7] at this
    nlinarith
  intro t ht
  have hm := hmono (T0 N K α) t hT0.le ht
  have r := hreg t (hT0.le.trans ht)
  exact ⟨le_antisymm (by linarith [hm.2.1]) r.2.2.1, by linarith [hm.2.2.2]⟩



end DFS
