import DFSLean.Defs

/-!
# Work package E: the Lyapunov estimate `lyapunov_state` (paper l.596–988, `p = 3`)

Route (one estimate covering both `u > 0` and `u = 0`). With `a = e^{x₁}`, `b = e^{y₁}`,
`s = e^u`, `κ = e^{max Cv 0}`, the two facts `E (1 - θ) ≤ κ` (`θ = 1` if `u > 0`, `E ≤ κ` if
`u = 0`) and `s ≤ E` give
  `N (N-1) (log W)' ≤ -b/D₁ - K E θ/D₄ + C/b`,  `C = 6 N³ κ`,
once `b ≥ 2 N² κ` (each `D_{2,i}` summand is then `≤ 0`). The negative terms beat `C/b` when
`b ≥ 4C + 1` and `W = b² s³ / a > 2C (2C (N+1))³`; at `u = 0` (`θ` arbitrary) one uses `s = 1`.
Constants: `B₀ = log (4C + 1)`, `CW = log (2C (2C (N+1))³)`.
-/

namespace DFS

open Real Filter Topology Set

variable {N K : ℕ}

/-- Summand of the `D_{2,i}` sum in `N (N-1) (log W)'`: nonpositive once `b` is large. -/
private lemma E_summand (n k j b E θ η κ D : ℝ) (hn : 1 ≤ n) (hj0 : 0 ≤ j) (hjk : j ≤ k)
    (hkn : k + 1 ≤ n) (hκ : 1 ≤ κ) (hE : 0 < E) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hη0 : 0 ≤ η) (hEθ : E * (1 - θ) ≤ κ) (hb : 2 * n ^ 2 * κ ≤ b) (hD : 0 < D) :
    2 * (n - 1) * ((b + n - k - 1 + j * E * (1 - θ)) / D) - 3 * (j * E * θ / D)
      - 2 * n * ((j * E * η + b) / D) ≤ 0 := by
  have hrw : 2 * (n - 1) * ((b + n - k - 1 + j * E * (1 - θ)) / D) - 3 * (j * E * θ / D)
      - 2 * n * ((j * E * η + b) / D)
      = (2 * (n - 1) * (n - k - 1) - 2 * b + 2 * (n - 1) * (j * (E * (1 - θ)))
          - 3 * (j * (E * θ)) - 2 * n * (j * (E * η))) / D := by
    field_simp
    ring
  rw [hrw]
  apply div_nonpos_of_nonpos_of_nonneg _ hD.le
  have h1 : j * (E * (1 - θ)) ≤ k * κ := by
    have : 0 ≤ E * (1 - θ) := mul_nonneg hE.le (by linarith)
    calc j * (E * (1 - θ)) ≤ k * (E * (1 - θ)) := mul_le_mul_of_nonneg_right hjk this
      _ ≤ k * κ := mul_le_mul_of_nonneg_left hEθ (by linarith)
  have h2 : 0 ≤ j * (E * θ) := mul_nonneg hj0 (mul_nonneg hE.le hθ0)
  have h3 : 0 ≤ j * (E * η) := mul_nonneg hj0 (mul_nonneg hE.le hη0)
  have h4 : (n - 1) * (j * (E * (1 - θ))) ≤ (n - 1) * (k * κ) :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  have h3' : 0 ≤ n * (j * (E * η)) := mul_nonneg (by linarith) h3
  have h5 : (n - 1) * (n - k - 1) ≤ n ^ 2 := by
    rw [sq]; exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have h6 : (n - 1) * (k * κ) ≤ n ^ 2 * κ := by
    have : (n - 1) * k ≤ n ^ 2 := by
      rw [sq]; exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right this (by linarith)
  have h7 : n ^ 2 * 1 ≤ n ^ 2 * κ := mul_le_mul_of_nonneg_left hκ (by positivity)
  linarith

/-- The algebraic core: `N (N-1) (log W)' ≤ -H - K Q θ + C / b`. -/
private lemma E_main_alg (n k b E θ η κ d1 d3 d4 S0 S1 S2 F3 : ℝ)
    (hn : 7 ≤ n) (hk1 : 1 ≤ k) (hkn : k + 5 ≤ n)
    (hκ : 1 ≤ κ) (hE : 0 < E) (hη0 : 0 ≤ η)
    (hEθ : E * (1 - θ) ≤ κ) (hb : 2 * n ^ 2 * κ ≤ b)
    (hd1 : 0 < d1) (hd3 : b ≤ d3) (hd4 : b ≤ d4)
    (hS : 2 * (n - 1) * S0 - 3 * S1 - 2 * n * S2 ≤ 0) :
    n * (n - 1) * (2 * (1 / n * ((b + n - 2) / d1 + S0 - k * E * θ / d4)) +
          -3 * (1 / (n * (n - 1)) * (S1 + k * E * θ / d4)) +
        2 * (1 / (n - 1) * (k * (n - 1) / d3 + (n - k - 1 + k * E * (1 - η)) / d4
          - b / d1 - S2)) + 0 * F3)
      ≤ -(b / d1) - k * E * θ / d4 + 6 * n ^ 3 * κ / b := by
  have hbpos : 0 < b := by
    have : 0 < 2 * n ^ 2 * κ := mul_pos (by positivity) (by linarith)
    linarith
  have hd3pos : 0 < d3 := by linarith
  have hd4pos : 0 < d4 := by linarith
  have hn1 : 0 < n - 1 := by linarith
  have step1 : ∀ X Y Z : ℝ, n * (n - 1) * (2 * (1 / n * X) + -3 * (1 / (n * (n - 1)) * Y)
      + 2 * (1 / (n - 1) * Z) + 0 * F3) = 2 * (n - 1) * X - 3 * Y + 2 * n * Z := by
    intro X Y Z
    field_simp
    ring
  rw [step1]
  have hrw : 2 * (n - 1) * ((b + n - 2) / d1 + S0 - k * E * θ / d4)
        - 3 * (S1 + k * E * θ / d4)
        + 2 * n * (k * (n - 1) / d3 + (n - k - 1 + k * E * (1 - η)) / d4 - b / d1 - S2)
      = (2 * (n - 1) * (n - 2) - 2 * b) / d1 + (2 * (n - 1) * S0 - 3 * S1 - 2 * n * S2)
        + 2 * n * k * (n - 1) / d3
        + (2 * n * (n - k - 1) + 2 * n * k * E * (1 - η) - 2 * n * k * E * θ) / d4
        - k * E * θ / d4 := by
    ring
  rw [hrw]
  -- the `D₁` term
  have hP1 : (2 * (n - 1) * (n - 2) - 2 * b) / d1 ≤ -b / d1 := by
    apply div_le_div_of_nonneg_right _ hd1.le
    have e1 : (n - 1) * (n - 2) = n ^ 2 - 3 * n + 2 := by ring
    have e2 : n ^ 2 * 1 ≤ n ^ 2 * κ := mul_le_mul_of_nonneg_left hκ (by positivity)
    linarith
  -- the `D₃` term
  have hP3 : 2 * n * k * (n - 1) / d3 ≤ 2 * n ^ 3 / b := by
    apply div_le_div₀ (by positivity) _ hbpos hd3
    have e1 : k * (n - 1) ≤ n * n := mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    have e2 : n * (k * (n - 1)) ≤ n * (n * n) := mul_le_mul_of_nonneg_left e1 (by linarith)
    have e3 : 2 * n * k * (n - 1) = 2 * (n * (k * (n - 1))) := by ring
    have e4 : n ^ 3 = n * (n * n) := by ring
    linarith
  -- the `D₄` term
  have hP4 : (2 * n * (n - k - 1) + 2 * n * k * E * (1 - η) - 2 * n * k * E * θ) / d4
      ≤ 4 * n ^ 2 * κ / b := by
    apply div_le_div₀ (by positivity) _ hbpos hd4
    have e1 : E * (1 - η) ≤ E := mul_le_of_le_one_right hE.le (by linarith)
    have e2 : n * k * (E * (1 - η)) ≤ n * k * E := mul_le_mul_of_nonneg_left e1 (by positivity)
    have e3 : n * k * (E * (1 - θ)) ≤ n * k * κ := mul_le_mul_of_nonneg_left hEθ (by positivity)
    have e4 : n * k ≤ n ^ 2 := by
      rw [sq]; exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have e5 : n * k * κ ≤ n ^ 2 * κ := mul_le_mul_of_nonneg_right e4 (by linarith)
    have e6 : n * (n - k - 1) ≤ n ^ 2 := by
      rw [sq]; exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have e7 : n ^ 2 * 1 ≤ n ^ 2 * κ := mul_le_mul_of_nonneg_left hκ (by positivity)
    linarith
  have hsum : 2 * n ^ 3 / b + 4 * n ^ 2 * κ / b ≤ 6 * n ^ 3 * κ / b := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ hbpos.le
    have : n ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have f1 : n ^ 3 * 1 ≤ n ^ 3 * κ := mul_le_mul_of_nonneg_left hκ (by positivity)
    have f2 : n ^ 2 * κ ≤ n ^ 3 * κ := mul_le_mul_of_nonneg_right this (by linarith)
    linarith
  rw [neg_div] at hP1
  linarith

/-- Contrapositive core of the `W`-estimate: if both negative terms are small then `W` is
bounded. -/
private lemma E_key (n a b s C : ℝ) (hn : 1 ≤ n) (ha : 0 < a) (hs : 1 ≤ s) (hC : 1 ≤ C)
    (hbn : n ≤ b) (hb4 : 4 * C < b) (h1 : b / (a + b + n) ≤ C / b)
    (h2 : s / (2 * (b + n)) ≤ C / b) :
    b ^ 2 * s ^ 3 / a ≤ 2 * C * (2 * C * (n + 1)) ^ 3 := by
  have hb : 0 < b := by linarith
  rw [div_le_div_iff₀ (by linarith) hb] at h1
  rw [div_le_div_iff₀ (by linarith) hb] at h2
  have hab : b + n < a := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hba : b ^ 2 ≤ 2 * C * a := by nlinarith
  have hs2 : s ≤ 2 * C * (n + 1) := by
    have e1 : n ≤ n * b := by nlinarith
    have e2 : C * (b + n) ≤ C * ((n + 1) * b) := mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
    have : s * b ≤ 2 * C * (n + 1) * b := by nlinarith
    exact le_of_mul_le_mul_right this hb
  rw [div_le_iff₀ ha]
  have hs3 : s ^ 3 ≤ (2 * C * (n + 1)) ^ 3 := pow_le_pow_left₀ (by linarith) hs2 3
  calc b ^ 2 * s ^ 3 ≤ (2 * C * a) * s ^ 3 :=
        mul_le_mul_of_nonneg_right hba (by positivity)
    _ ≤ (2 * C * a) * (2 * C * (n + 1)) ^ 3 :=
        mul_le_mul_of_nonneg_left hs3 (by positivity)
    _ = 2 * C * (2 * C * (n + 1)) ^ 3 * a := by ring

/-- The `Q`-term small forces `s` small (interior case `θ = 1`). -/
private lemma E_key2 (n k b E s d4 C : ℝ) (hk : 1 ≤ k) (hn : 0 ≤ n) (hsE : s ≤ E) (hs : 0 < s)
    (hC : 0 < C) (hb4 : 4 * C < b) (hd4 : d4 ≤ k * E + b + n) (hd4pos : 0 < d4)
    (h : k * E / d4 ≤ C / b) : s / (2 * (b + n)) ≤ C / b := by
  have hb : 0 < b := by linarith
  rw [div_le_div_iff₀ hd4pos hb] at h
  rw [div_le_div_iff₀ (by linarith) hb]
  have hkE : 0 < k * E := by nlinarith
  have hlt : k * E < b + n := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hE : 0 < E := by linarith
  have e1 : s ≤ k * E := by nlinarith
  have e2 : s * b ≤ k * E * b := mul_le_mul_of_nonneg_right e1 hb.le
  have e3 : C * d4 ≤ C * (k * E + b + n) := mul_le_mul_of_nonneg_left hd4 hC.le
  have e4 : C * (k * E) ≤ C * (b + n) := mul_le_mul_of_nonneg_left hlt.le hC.le
  nlinarith

/-- Final step: the negative terms dominate once `b` is large and `W = b² s³ / a` is large.
Either `θ = 1` (interior, the `Q`-term is available) or `s = 1` (boundary `u = 0`). -/
private lemma E_final (n k a b s E θ d1 d4 C : ℝ) (hn : 1 ≤ n) (hk : 1 ≤ k) (ha : 0 < a)
    (hs1 : 1 ≤ s) (hsE : s ≤ E) (hC1 : 1 ≤ C) (hnb : n ≤ b) (hb : 4 * C + 1 ≤ b)
    (hθ0 : 0 ≤ θ) (hθ : θ = 1 ∨ s = 1) (hd1pos : 0 < d1) (hd1le : d1 ≤ a + b + n)
    (hd4pos : 0 < d4) (hd4le : d4 ≤ k * E + b + n)
    (hW : 2 * C * (2 * C * (n + 1)) ^ 3 < b ^ 2 * s ^ 3 / a) :
    -(b / d1) - k * E * θ / d4 + C / b ≤ 0 := by
  have hbpos : 0 < b := by linarith
  have hCpos : 0 < C := by linarith
  have hEpos : 0 < E := by linarith
  by_contra hcon
  push Not at hcon
  have hQ : 0 ≤ k * E * θ / d4 :=
    div_nonneg (mul_nonneg (mul_nonneg (by linarith) hEpos.le) hθ0) hd4pos.le
  have hH : 0 ≤ b / d1 := div_nonneg hbpos.le hd1pos.le
  have h1 : b / (a + b + n) ≤ C / b := by
    calc b / (a + b + n) ≤ b / d1 := div_le_div_of_nonneg_left hbpos.le hd1pos hd1le
      _ ≤ C / b := by linarith
  have h2 : s / (2 * (b + n)) ≤ C / b := by
    rcases hθ with hθ | hs
    · subst hθ
      apply E_key2 n k b E s d4 C hk (by linarith) hsE (by linarith) hCpos (by linarith)
        hd4le hd4pos
      rw [mul_one] at hcon
      linarith
    · rw [hs, div_le_div_iff₀ (by positivity) hbpos]
      have : 2 * (b + n) ≤ C * (2 * (b + n)) := le_mul_of_one_le_left (by positivity) hC1
      linarith
  have hWle := E_key n a b s C hn ha hs1 hC1 hnb (by linarith) h1 h2
  linarith

theorem lyapunov_state (hK : 2 ≤ K) (hN : K + 5 ≤ N) (Cv : ℝ) :
    ∃ B₀ CW : ℝ, ∀ z : Fin 4 → ℝ, Good z → v z ≤ Cv → B₀ ≤ z 2 →
      CW < lin ![2, -3, 2, 0] z →
      ∀ θ η, Adm z θ η → lin ![2, -3, 2, 0] (F N K 1 θ η z) ≤ 0 := by
  have hk2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hkn : (K : ℝ) + 5 ≤ N := by exact_mod_cast hN
  have hn7 : (7 : ℝ) ≤ N := by linarith
  have hκ : 1 ≤ exp (max Cv 0) := one_le_exp (le_max_right _ _)
  have hC1 : 1 ≤ 6 * (N : ℝ) ^ 3 * exp (max Cv 0) := by
    have : (1 : ℝ) ≤ (N : ℝ) ^ 3 := one_le_pow₀ (by linarith)
    nlinarith
  refine ⟨log (4 * (6 * (N : ℝ) ^ 3 * exp (max Cv 0)) + 1),
    log (2 * (6 * (N : ℝ) ^ 3 * exp (max Cv 0))
      * (2 * (6 * (N : ℝ) ^ 3 * exp (max Cv 0)) * ((N : ℝ) + 1)) ^ 3), ?_⟩
  intro z hz hv hB hW θ η hadm
  obtain ⟨hu, -, -, -⟩ := hz
  obtain ⟨⟨hθ0, hθ1⟩, ⟨hη0, hη1⟩, hθu, -, -, -⟩ := hadm
  -- abbreviations
  generalize hCdef : 6 * (N : ℝ) ^ 3 * exp (max Cv 0) = C at hC1 hB hW
  generalize hκdef : exp (max Cv 0) = κ at hκ hCdef
  have ha : 0 < exp (z 0) := exp_pos _
  have hb : 4 * C + 1 ≤ exp (z 2) := by
    have := exp_le_exp.mpr hB
    rwa [exp_log (by linarith)] at this
  have hbpos : 0 < exp (z 2) := exp_pos _
  have hs1 : 1 ≤ exp (u z) := one_le_exp hu
  have hEpos : 0 < E z := exp_pos _
  have hsE : exp (u z) ≤ E z := by
    unfold E
    apply exp_le_exp.mpr
    rw [max_eq_left hu]
    linarith [le_max_right (v z) 0]
  have hEθ : E z * (1 - θ) ≤ κ := by
    by_cases h1 : θ = 1
    · rw [h1]; simp; linarith
    · have hu0 : u z = 0 := le_antisymm (not_lt.mp (fun h => h1 (hθu h))) hu
      have hEle : E z ≤ κ := by
        unfold E
        rw [hu0, ← hκdef]
        apply exp_le_exp.mpr
        simp only [max_self, zero_add]
        exact max_le_max hv le_rfl
      calc E z * (1 - θ) ≤ E z * 1 := mul_le_mul_of_nonneg_left (by linarith) hEpos.le
        _ ≤ κ := by linarith
  -- the denominators
  have hD1pos : 0 < D1 N z := by unfold D1; linarith
  have hD1le : D1 N z ≤ exp (z 0) + exp (z 2) + N := by unfold D1; linarith
  have hD3 : exp (z 2) ≤ D3 N z := by unfold D3; linarith
  have hD4 : exp (z 2) ≤ D4 N K z := by
    unfold D4
    have : 0 ≤ (K : ℝ) * E z := by positivity
    linarith
  have hD4le : D4 N K z ≤ K * E z + exp (z 2) + N := by unfold D4; linarith
  have hD4pos : 0 < D4 N K z := by linarith
  have hD2pos : ∀ j ∈ Finset.range K, 0 < D2 N K j z := by
    intro j hj
    have hjK : (j : ℝ) + 1 ≤ K := by
      have := Finset.mem_range.mp hj
      exact_mod_cast this
    unfold D2
    have : 0 < ((K : ℝ) - j) * exp (z 0) := mul_pos (by linarith) ha
    have : 0 ≤ (j : ℝ) * E z := by positivity
    linarith
  have hbig : 2 * (N : ℝ) ^ 2 * κ ≤ exp (z 2) := by
    have h1 : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have h2 : (N : ℝ) ^ 2 * κ ≤ (N : ℝ) ^ 3 * κ := mul_le_mul_of_nonneg_right h1 (by linarith)
    have h3 : 0 ≤ (N : ℝ) ^ 3 * κ := by positivity
    linarith
  -- the `D_{2,i}` sum is nonpositive
  have hS : 2 * ((N : ℝ) - 1)
        * ∑ j ∈ Finset.range K, (exp (z 2) + N - K - 1 + j * E z * (1 - θ)) / D2 N K j z
      - 3 * ∑ j ∈ Finset.range K, j * E z * θ / D2 N K j z
      - 2 * N * ∑ j ∈ Finset.range K, (j * E z * η + exp (z 2)) / D2 N K j z ≤ 0 := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_nonpos
    intro j hj
    have hjK : (j : ℝ) ≤ K := by
      have := Finset.mem_range.mp hj
      exact_mod_cast this.le
    exact E_summand N K j (exp (z 2)) (E z) θ η κ (D2 N K j z) (by linarith) (by positivity)
      hjK (by linarith) hκ hEpos hθ0 hθ1 hη0 hEθ hbig (hD2pos j hj)
  -- main estimate
  have hmain : (N : ℝ) * ((N : ℝ) - 1) * lin ![2, -3, 2, 0] (F N K 1 θ η z)
      ≤ -(exp (z 2) / D1 N z) - K * E z * θ / D4 N K z + C / exp (z 2) := by
    rw [← hCdef]
    simp only [lin, F, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    exact E_main_alg N K (exp (z 2)) (E z) θ η κ (D1 N z) (D3 N z) (D4 N K z) _ _ _ _ hn7
      (by linarith) hkn hκ hEpos hη0 hEθ hbig hD1pos hD3 hD4 hS
  have hNb : (N : ℝ) ≤ exp (z 2) := by
    have e1 : (N : ℝ) ≤ (N : ℝ) ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
    have e2 : (N : ℝ) ^ 2 * 1 ≤ (N : ℝ) ^ 2 * κ := mul_le_mul_of_nonneg_left hκ (by positivity)
    linarith
  have hθ' : θ = 1 ∨ exp (u z) = 1 := by
    by_cases hθ : θ = 1
    · exact Or.inl hθ
    · right
      have hu0 : u z = 0 := le_antisymm (not_lt.mp (fun h => hθ (hθu h))) hu
      rw [hu0, exp_zero]
  have hWeq : exp (lin ![2, -3, 2, 0] z) = exp (z 2) ^ 2 * exp (u z) ^ 3 / exp (z 0) := by
    have : lin ![2, -3, 2, 0] z = (z 2 + z 2) + (u z + u z + u z) - z 0 := by
      simp [lin, u]; ring
    rw [this, exp_sub, exp_add, exp_add, exp_add, exp_add]; ring
  have hW0 : 0 < 2 * C * (2 * C * ((N : ℝ) + 1)) ^ 3 := by
    apply mul_pos (by linarith)
    apply pow_pos
    apply mul_pos (by linarith)
    positivity
  have hW' := exp_lt_exp.mpr hW
  rw [exp_log hW0, hWeq] at hW'
  have hneg := E_final N K (exp (z 0)) (exp (z 2)) (exp (u z)) (E z) θ (D1 N z) (D4 N K z) C
    (by linarith) (by linarith) ha hs1 hsE hC1 hNb hb hθ0 hθ' hD1pos hD1le hD4pos hD4le hW'
  have hNN : 0 < (N : ℝ) * ((N : ℝ) - 1) := mul_pos (by linarith) (by linarith)
  by_contra hcon
  push Not at hcon
  have := mul_pos hNN hcon
  linarith




end DFS
