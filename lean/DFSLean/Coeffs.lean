import DFSLean.Defs

/-!
# Work package F1: coefficient bounds for Lemma C.4 (Thm C.5 item 4)

Paper l.1067–1173 with `α = 1`.
-/

namespace DFS
open Real Filter Topology Set
variable {N K : ℕ}

private lemma F1_lin_Xc (w : Fin 4 → ℝ) :
    lin (Xc N) w = 1 / (N:ℝ) * w 0 + ((N:ℝ) - 1) / N * w 1 := by
  simp only [lin, Xc]
  simp

/-- `X' = (1/N²) [G + Σ (Cᵢ + Aᵢ)]`, independently of `θ`. -/
private lemma F1_Xdot (hN0 : (0:ℝ) < N) (hN1 : (0:ℝ) < N - 1) (θ η : ℝ) (z : Fin 4 → ℝ) :
    lin (Xc N) (F N K 1 θ η z) = 1 / (N:ℝ) ^ 2 * ((exp (z 2) + N - 2) / D1 N z
      + ∑ j ∈ Finset.range K, (exp (z 2) + N - K - 1 + j * E z) / D2 N K j z) := by
  have hs : ∑ j ∈ Finset.range K, (exp (z 2) + (N:ℝ) - K - 1 + j * E z * (1 - θ)) / D2 N K j z
      + ∑ j ∈ Finset.range K, (j:ℝ) * E z * θ / D2 N K j z
      = ∑ j ∈ Finset.range K, (exp (z 2) + N - K - 1 + j * E z) / D2 N K j z := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [F1_lin_Xc, ← hs]
  have h0 : F N K 1 θ η z 0 = 1 / (N : ℝ) * ((exp (z 2) + (N : ℝ) - 2) / D1 N z
        + ∑ j ∈ Finset.range K,
            (exp (z 2) + (N : ℝ) - K - 1 + (j : ℝ) * E z * (1 - θ)) / D2 N K j z
        - (K : ℝ) * E z * θ / D4 N K z) := rfl
  have h1 : F N K 1 θ η z 1 = 1 / ((N : ℝ) * ((N : ℝ) - 1)) *
       (∑ j ∈ Finset.range K, (j : ℝ) * E z * θ / D2 N K j z + (K : ℝ) * E z * θ / D4 N K z) := rfl
  rw [h0, h1]
  generalize ∑ j ∈ Finset.range K, (exp (z 2) + (N : ℝ) - K - 1 + (j : ℝ) * E z * (1 - θ)) / D2 N K j z
    = S1
  generalize ∑ j ∈ Finset.range K, (j : ℝ) * E z * θ / D2 N K j z = S2
  field_simp
  ring

/-- `Y' + ã e^{Y-X} = (1/(N-1)) [K M + R + (1-η) K Q - η Σ Aᵢ]`. -/
private lemma F1_Ydot (X θ η : ℝ) (z : Fin 4 → ℝ) :
    F N K 1 θ η z 2 + exp X * (1 / D1 N z + ∑ j ∈ Finset.range K, 1 / D2 N K j z) / ((N:ℝ) - 1)
        * exp (z 2 - X)
      = 1 / ((N:ℝ) - 1) * ((K : ℝ) * ((N : ℝ) - 1) / D3 N z
        + ((N : ℝ) - K - 1 + (K : ℝ) * E z * (1 - η)) / D4 N K z
        - ∑ j ∈ Finset.range K, (j : ℝ) * E z * η / D2 N K j z) := by
  have hs2 : ∑ j ∈ Finset.range K, ((j : ℝ) * E z * η + exp (z 2)) / D2 N K j z
      = ∑ j ∈ Finset.range K, (j : ℝ) * E z * η / D2 N K j z
        + exp (z 2) * ∑ j ∈ Finset.range K, 1 / D2 N K j z := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hexp : exp X * exp (z 2 - X) = exp (z 2) := by rw [← exp_add]; ring_nf
  have h2 : F N K 1 θ η z 2 = 1 / ((N : ℝ) - 1) * ((K : ℝ) * ((N : ℝ) - 1) / D3 N z
        + ((N : ℝ) - K - 1 + (K : ℝ) * E z * (1 - η)) / D4 N K z
        - exp (z 2) / D1 N z
        - ∑ j ∈ Finset.range K, ((j : ℝ) * E z * η + exp (z 2)) / D2 N K j z) := rfl
  rw [h2, hs2]
  linear_combination ((1 / D1 N z + ∑ j ∈ Finset.range K, 1 / D2 N K j z) / ((N:ℝ) - 1)) * hexp

/-! ### Final estimates, with plain real variables

`n = N`, `k = K`, `a = e^{x₁}`, `b = e^{y₁}`, `eX = e^{X}`, `c = max Cu 0`, `CE` bounds `E`. -/

/-- Bounds for `a = X' e^{X-Y}`. -/
private lemma F1_a_bnds (n k CE c a b eX D1 S1 : ℝ) (hn : 2 ≤ n) (hk : 0 ≤ k) (hCE : 0 ≤ CE)
    (ha : 0 < a) (hb1 : 1 ≤ b) (heXhi : eX ≤ a) (heXlo : a * exp (-c) ≤ eX)
    (hD1lo : a ≤ D1) (hD1hi : D1 ≤ 3 * a) (hS10 : 0 ≤ S1)
    (hS1hi : S1 ≤ k * ((1 + n + k * CE) * b / a)) :
    exp (-c) / (3 * n ^ 2) ≤ 1 / n ^ 2 * ((b + n - 2) / D1 + S1) * (eX / b) ∧
      1 / n ^ 2 * ((b + n - 2) / D1 + S1) * (eX / b) ≤ (k + 1) * (1 + n + k * CE) / n ^ 2 := by
  have hn0 : 0 < n := by linarith
  have hb0 : 0 < b := by linarith
  have hD1 : 0 < D1 := by linarith
  have hkCE : 0 ≤ k * CE := mul_nonneg hk hCE
  have hM : 0 < 1 + n + k * CE := by linarith
  have heX0 : 0 ≤ eX := le_trans (mul_nonneg ha.le (exp_pos _).le) heXlo
  constructor
  · have hfirst : b / D1 ≤ (b + n - 2) / D1 + S1 := by
      have : b / D1 ≤ (b + n - 2) / D1 := div_le_div_of_nonneg_right (by linarith) hD1.le
      linarith
    calc exp (-c) / (3 * n ^ 2)
        = (a * exp (-c)) / (n ^ 2 * (3 * a)) := by field_simp
      _ ≤ eX / (n ^ 2 * D1) := by gcongr
      _ = 1 / n ^ 2 * (b / D1) * (eX / b) := by field_simp
      _ ≤ 1 / n ^ 2 * ((b + n - 2) / D1 + S1) * (eX / b) := by
          gcongr
  · have hfirst : (b + n - 2) / D1 ≤ (1 + n + k * CE) * b / a := by
      have h4 : n ≤ n * b := le_mul_of_one_le_right hn0.le hb1
      have h5 : k * CE ≤ k * CE * b := le_mul_of_one_le_right hkCE hb1
      exact div_le_div₀ (by positivity) (by linarith) ha hD1lo
    have hS : (b + n - 2) / D1 + S1 ≤ (k + 1) * (1 + n + k * CE) * b / a := by
      have : (k + 1) * (1 + n + k * CE) * b / a
          = (1 + n + k * CE) * b / a + k * ((1 + n + k * CE) * b / a) := by ring
      linarith
    calc 1 / n ^ 2 * ((b + n - 2) / D1 + S1) * (eX / b)
        ≤ 1 / n ^ 2 * ((k + 1) * (1 + n + k * CE) * b / a) * (a / b) := by
          gcongr
      _ = (k + 1) * (1 + n + k * CE) / n ^ 2 := by field_simp

/-- Bounds for `ã = e^{X} (1/D₁ + Σ 1/D_{2,j}) / (N-1)`. -/
private lemma F1_at_bnds (n k c a eX D1 T : ℝ) (hn : 2 ≤ n) (ha : 0 < a)
    (heXhi : eX ≤ a) (heXlo : a * exp (-c) ≤ eX) (hD1lo : a ≤ D1) (hD1hi : D1 ≤ 3 * a)
    (hT0 : 0 ≤ T) (hThi : T ≤ k * (1 / a)) :
    exp (-c) / (3 * (n - 1)) ≤ eX * (1 / D1 + T) / (n - 1) ∧
      eX * (1 / D1 + T) / (n - 1) ≤ (k + 1) / (n - 1) := by
  have hn1 : 0 < n - 1 := by linarith
  have hD1 : 0 < D1 := by linarith
  have heX0 : 0 ≤ eX := le_trans (mul_nonneg ha.le (exp_pos _).le) heXlo
  constructor
  · have h1 : 1 / (3 * a) ≤ 1 / D1 + T := by
      have := one_div_le_one_div_of_le hD1 hD1hi
      linarith
    calc exp (-c) / (3 * (n - 1))
        = a * exp (-c) * (1 / (3 * a)) / (n - 1) := by field_simp
      _ ≤ eX * (1 / D1 + T) / (n - 1) := by gcongr
  · have h1 : 1 / D1 + T ≤ (k + 1) * (1 / a) := by
      have := one_div_le_one_div_of_le ha hD1lo
      linarith
    calc eX * (1 / D1 + T) / (n - 1)
        ≤ a * ((k + 1) * (1 / a)) / (n - 1) := by gcongr
      _ = (k + 1) / (n - 1) := by field_simp

/-- Bounds for `β = e^{Y} (Y' + ã e^{Y-X})`. -/
private lemma F1_beta_bnds (n k CE a b D3 D4 P W : ℝ) (hn : k + 5 ≤ n) (hk : 0 ≤ k)
    (ha : 0 < a) (hb : 0 < b) (hbn : n ≤ b) (hD3 : D3 = b + n - 1) (hD4lo : b ≤ D4)
    (hP0 : 0 ≤ P) (hPhi : P ≤ n - k - 1 + k * CE) (hW0 : 0 ≤ W) (hWhi : W ≤ k * (k * CE / a))
    (hq : 4 * k * CE * b ≤ a) :
    k / 4 ≤ b * (1 / (n - 1) * (k * (n - 1) / D3 + P / D4 - W)) ∧
      b * (1 / (n - 1) * (k * (n - 1) / D3 + P / D4 - W))
        ≤ (k * (n - 1) + (n - k - 1) + k * CE) / (n - 1) := by
  have hn1 : 0 < n - 1 := by linarith
  have hD3pos : 0 < D3 := by rw [hD3]; linarith
  have hD4 : 0 < D4 := by linarith
  have hc0 : 0 ≤ k * (n - 1) := mul_nonneg hk hn1.le
  have h3lo : k * (n - 1) / 2 ≤ b * (k * (n - 1) / D3) := by
    rw [mul_div_assoc', le_div_iff₀ hD3pos]
    have : D3 ≤ 2 * b := by rw [hD3]; linarith
    nlinarith [mul_le_mul_of_nonneg_left this hc0]
  have h3hi : b * (k * (n - 1) / D3) ≤ k * (n - 1) := by
    rw [mul_div_assoc', div_le_iff₀ hD3pos]
    have : b ≤ D3 := by rw [hD3]; linarith
    nlinarith [mul_le_mul_of_nonneg_left this hc0]
  have h4lo : 0 ≤ b * (P / D4) := mul_nonneg hb.le (div_nonneg hP0 hD4.le)
  have h4hi : b * (P / D4) ≤ n - k - 1 + k * CE := by
    calc b * (P / D4) = P * (b / D4) := by ring
      _ ≤ P * 1 := mul_le_mul_of_nonneg_left ((div_le_one hD4).mpr hD4lo) hP0
      _ ≤ n - k - 1 + k * CE := by linarith
  have hWb : b * W ≤ k / 4 := by
    have h : k * CE * b / a ≤ 1 / 4 := by rw [div_le_iff₀ ha]; linarith
    calc b * W ≤ b * (k * (k * CE / a)) := mul_le_mul_of_nonneg_left hWhi hb.le
      _ = k * (k * CE * b / a) := by ring
      _ ≤ k * (1 / 4) := mul_le_mul_of_nonneg_left h hk
      _ = k / 4 := by ring
  have hbW0 : 0 ≤ b * W := mul_nonneg hb.le hW0
  have hβ : b * (1 / (n - 1) * (k * (n - 1) / D3 + P / D4 - W))
      = (b * (k * (n - 1) / D3) + b * (P / D4) - b * W) / (n - 1) := by ring
  rw [hβ]
  constructor
  · rw [le_div_iff₀ hn1]
    have : k ≤ k * (n - 1) := le_mul_of_one_le_right hk (by linarith)
    linarith
  · apply div_le_div_of_nonneg_right _ hn1.le
    linarith

/-! ### Pointwise statement -/

private lemma F1_pointwise (hK : 2 ≤ K) (hN : K + 5 ≤ N) (Cv Cu CZ Cu' CE : ℝ)
    (hCu' : Cu' = max Cu 0) (hCE : CE = exp (Cu' + max Cv 0))
    (z : Fin 4 → ℝ) (hG : Good z) (hv : v z ≤ Cv) (hu : u z ≤ Cu) (hZ : 2 * z 2 - z 0 ≤ CZ)
    (hB : (N:ℝ) + |CZ| + 4 * K * CE ≤ z 2) (θ η : ℝ) (hA : Adm z θ η) :
    ∃ a ∈ Icc (exp (-Cu') / (3 * (N:ℝ) ^ 2)) ((K + 1) * (1 + N + K * CE) / (N:ℝ) ^ 2),
    ∃ ã ∈ Icc (exp (-Cu') / (3 * ((N:ℝ) - 1))) ((K + 1) / ((N:ℝ) - 1)),
    ∃ β ∈ Icc ((K:ℝ) / 4) ((K * ((N:ℝ) - 1) + (N - K - 1) + K * CE) / ((N:ℝ) - 1)),
      lin (Xc N) (F N K 1 θ η z) = a * exp (z 2 - lin (Xc N) z) ∧
      F N K 1 θ η z 2 = β * exp (-z 2) - ã * exp (z 2 - lin (Xc N) z) := by
  have hK' : (2:ℝ) ≤ K := by exact_mod_cast hK
  have hN' : (K:ℝ) + 5 ≤ N := by exact_mod_cast hN
  have hN0 : (0:ℝ) < N := by linarith
  have hN1 : (0:ℝ) < N - 1 := by linarith
  have hCE0 : 0 < CE := hCE ▸ exp_pos _
  have hCuCu' : Cu ≤ Cu' := hCu' ▸ le_max_left _ _
  obtain ⟨hu0, -, hy1, -⟩ := hG
  obtain ⟨-, ⟨hη0, hη1⟩, -⟩ := hA
  -- the averaged variable `X`
  obtain ⟨X, hXdef⟩ : ∃ X, X = lin (Xc N) z := ⟨_, rfl⟩
  rw [← hXdef]
  have hXeq : X = z 0 - ((N:ℝ) - 1) / N * u z := by
    rw [hXdef, F1_lin_Xc]; simp only [u]; field_simp; ring
  have hfrac1 : ((N:ℝ) - 1) / N ≤ 1 := by rw [div_le_one hN0]; linarith
  have hfrac0 : 0 ≤ ((N:ℝ) - 1) / N := div_nonneg hN1.le hN0.le
  have hXu : ((N:ℝ) - 1) / N * u z ≤ u z := mul_le_of_le_one_left hu0 hfrac1
  have hXu0 : 0 ≤ ((N:ℝ) - 1) / N * u z := mul_nonneg hfrac0 hu0
  have heXhi : exp X ≤ exp (z 0) := exp_le_exp.mpr (by linarith)
  have heXlo : exp (z 0) * exp (-Cu') ≤ exp X := by
    rw [← exp_add]; exact exp_le_exp.mpr (by linarith)
  -- `E`
  have hE0 : 0 < E z := exp_pos _
  have hECE : E z ≤ CE := by
    rw [hCE]; unfold E; apply exp_le_exp.mpr
    have h1 : max (u z) 0 ≤ Cu' := hCu' ▸ max_le_max hu le_rfl
    have h2 : max (v z) 0 ≤ max Cv 0 := max_le_max hv le_rfl
    linarith
  -- exponentials of `x₁`, `y₁`
  have hCZabs : CZ ≤ |CZ| := le_abs_self CZ
  have habs0 : 0 ≤ |CZ| := abs_nonneg CZ
  have hKCE : 0 ≤ 4 * (K:ℝ) * CE := by positivity
  have hyx : z 2 ≤ z 0 := by linarith
  have ha0 : 0 < exp (z 0) := exp_pos _
  have hb0 : 0 < exp (z 2) := exp_pos _
  have hb1 : 1 ≤ exp (z 2) := one_le_exp hy1
  have hbN : (N:ℝ) ≤ exp (z 2) := by have := add_one_le_exp (z 2); linarith
  have hba : exp (z 2) ≤ exp (z 0) := exp_le_exp.mpr hyx
  have hexpZ : 4 * K * CE + 1 ≤ exp (z 2 - CZ) := by
    have := add_one_le_exp (z 2 - CZ); linarith
  have hq : exp (z 2) * exp (z 2 - CZ) ≤ exp (z 0) := by
    rw [← exp_add]; exact exp_le_exp.mpr (by linarith)
  have hq' : 4 * K * CE * exp (z 2) ≤ exp (z 0) := by
    linarith [mul_le_mul_of_nonneg_left hexpZ hb0.le]
  -- denominators
  have hD1lo : exp (z 0) ≤ D1 N z := by unfold D1; linarith
  have hD1hi : D1 N z ≤ 3 * exp (z 0) := by unfold D1; linarith
  have hD2lo : ∀ j ∈ Finset.range K, exp (z 0) ≤ D2 N K j z := by
    intro j hj
    have hjK' : j + 1 ≤ K := Finset.mem_range.mp hj
    have hjK : (j:ℝ) + 1 ≤ K := by exact_mod_cast hjK'
    have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
    have h1 : 0 ≤ ((K:ℝ) - j - 1) * exp (z 0) := mul_nonneg (by linarith) ha0.le
    have h2 : 0 ≤ (j:ℝ) * E z := mul_nonneg hj0 hE0.le
    unfold D2; linarith
  have hD2 : ∀ j ∈ Finset.range K, 0 < D2 N K j z := fun j hj => lt_of_lt_of_le ha0 (hD2lo j hj)
  have hKE : 0 ≤ (K:ℝ) * E z := by positivity
  have hD4lo : exp (z 2) ≤ D4 N K z := by unfold D4; linarith
  -- the sums
  set T := ∑ j ∈ Finset.range K, 1 / D2 N K j z with hT
  set W := ∑ j ∈ Finset.range K, (j : ℝ) * E z * η / D2 N K j z with hW
  set S1 := ∑ j ∈ Finset.range K, (exp (z 2) + N - K - 1 + j * E z) / D2 N K j z with hS1
  set P := (N : ℝ) - K - 1 + (K : ℝ) * E z * (1 - η) with hP
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun j hj => (one_div_pos.mpr (hD2 j hj)).le
  have hThi : T ≤ K * (1 / exp (z 0)) := by
    have := Finset.sum_le_card_nsmul (Finset.range K) (fun j => 1 / D2 N K j z) (1 / exp (z 0))
      (fun j hj => one_div_le_one_div_of_le ha0 (hD2lo j hj))
    rwa [Finset.card_range, nsmul_eq_mul] at this
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun j hj =>
    div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg j) hE0.le) hη0) (hD2 j hj).le
  have hWhi : W ≤ K * (K * CE / exp (z 0)) := by
    have := Finset.sum_le_card_nsmul (Finset.range K) (fun j => (j : ℝ) * E z * η / D2 N K j z)
      (K * CE / exp (z 0)) (fun j hj => by
        have hjK : (j:ℝ) ≤ K := by exact_mod_cast (Finset.mem_range.mp hj).le
        have hnum : (j:ℝ) * E z * η ≤ K * CE := by
          calc (j:ℝ) * E z * η ≤ (j:ℝ) * E z * 1 :=
                mul_le_mul_of_nonneg_left hη1 (mul_nonneg (Nat.cast_nonneg j) hE0.le)
            _ ≤ K * CE := by rw [mul_one]; exact mul_le_mul hjK hECE hE0.le (Nat.cast_nonneg K)
        exact div_le_div₀ (by positivity) hnum ha0 (hD2lo j hj))
    rwa [Finset.card_range, nsmul_eq_mul] at this
  have hS10 : 0 ≤ S1 := Finset.sum_nonneg fun j hj => by
    have h2 : 0 ≤ (j:ℝ) * E z := mul_nonneg (Nat.cast_nonneg j) hE0.le
    exact div_nonneg (by linarith) (hD2 j hj).le
  have hS1hi : S1 ≤ K * ((1 + N + K * CE) * exp (z 2) / exp (z 0)) := by
    have := Finset.sum_le_card_nsmul (Finset.range K)
      (fun j => (exp (z 2) + N - K - 1 + j * E z) / D2 N K j z)
      ((1 + N + K * CE) * exp (z 2) / exp (z 0)) (fun j hj => by
        have hjK : (j:ℝ) ≤ K := by exact_mod_cast (Finset.mem_range.mp hj).le
        have h2 : 0 ≤ (j:ℝ) * E z := mul_nonneg (Nat.cast_nonneg j) hE0.le
        have h3 : (j:ℝ) * E z ≤ K * CE := mul_le_mul hjK hECE hE0.le (Nat.cast_nonneg K)
        have h4 : (N:ℝ) ≤ N * exp (z 2) := le_mul_of_one_le_right hN0.le hb1
        have h5 : (K:ℝ) * CE ≤ K * CE * exp (z 2) := le_mul_of_one_le_right (by positivity) hb1
        have hnum : exp (z 2) + N - K - 1 + j * E z ≤ (1 + N + K * CE) * exp (z 2) := by
          linarith
        exact div_le_div₀ (by positivity) hnum ha0 (hD2lo j hj))
    rwa [Finset.card_range, nsmul_eq_mul] at this
  have hP0 : 0 ≤ P := by
    have : 0 ≤ (K : ℝ) * E z * (1 - η) := mul_nonneg hKE (by linarith)
    linarith
  have hPhi : P ≤ N - K - 1 + K * CE := by
    have : (K : ℝ) * E z * (1 - η) ≤ K * CE := by
      calc (K : ℝ) * E z * (1 - η) ≤ K * E z * 1 := mul_le_mul_of_nonneg_left (by linarith) hKE
        _ ≤ K * CE := by rw [mul_one]; exact mul_le_mul_of_nonneg_left hECE (Nat.cast_nonneg K)
    linarith
  -- the identities
  have hXp := F1_Xdot (K := K) hN0 hN1 θ η z
  have hYp := F1_Ydot (N := N) (K := K) X θ η z
  rw [← hT, ← hS1] at *
  rw [← hW, ← hP] at hYp
  obtain ⟨ha1, ha2⟩ := F1_a_bnds N K CE Cu' (exp (z 0)) (exp (z 2)) (exp X) (D1 N z) S1
    (by linarith) (Nat.cast_nonneg K) hCE0.le ha0 hb1 heXhi heXlo hD1lo hD1hi hS10 hS1hi
  obtain ⟨hã1, hã2⟩ := F1_at_bnds N K Cu' (exp (z 0)) (exp X) (D1 N z) T
    (by linarith) ha0 heXhi heXlo hD1lo hD1hi hT0 hThi
  obtain ⟨hβ1, hβ2⟩ := F1_beta_bnds N K CE (exp (z 0)) (exp (z 2)) (D3 N z) (D4 N K z) P W
    hN' (Nat.cast_nonneg K) ha0 hb0 hbN rfl hD4lo hP0 hPhi hW0 hWhi hq'
  refine ⟨lin (Xc N) (F N K 1 θ η z) * exp (X - z 2), ⟨?_, ?_⟩,
    exp X * (1 / D1 N z + T) / ((N:ℝ) - 1), ⟨hã1, hã2⟩,
    exp (z 2) * (F N K 1 θ η z 2 + exp X * (1 / D1 N z + T) / ((N:ℝ) - 1) * exp (z 2 - X)),
    ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hXp, exp_sub]; exact ha1
  · rw [hXp, exp_sub]; exact ha2
  · rw [hYp]; exact hβ1
  · rw [hYp]; exact hβ2
  · -- the `X` equation
    rw [mul_assoc, ← exp_add, show X - z 2 + (z 2 - X) = 0 by ring, exp_zero, mul_one]
  · -- the `Y` equation
    have h : exp (z 2) * exp (-z 2) = 1 := by rw [← exp_add]; simp
    linear_combination (-(F N K 1 θ η z 2 + exp X * (1 / D1 N z + T) / ((N:ℝ) - 1)
      * exp (z 2 - X))) * h

/-! ### Main statement -/

theorem growth_coeffs (hK : 2 ≤ K) (hN : K + 5 ≤ N) (Cv Cu CZ : ℝ) :
    ∃ B₀ aLo aHi ãLo ãHi βLo βHi : ℝ, 0 < aLo ∧ aLo ≤ aHi ∧ 0 < ãLo ∧ ãLo ≤ ãHi ∧ 0 < βLo ∧ βLo ≤ βHi ∧
      ∀ z : Fin 4 → ℝ, Good z → v z ≤ Cv → u z ≤ Cu → 2 * z 2 - z 0 ≤ CZ → B₀ ≤ z 2 →
      ∀ θ η, Adm z θ η →
        ∃ a ∈ Icc aLo aHi, ∃ ã ∈ Icc ãLo ãHi, ∃ β ∈ Icc βLo βHi,
          lin (Xc N) (F N K 1 θ η z) = a * exp (z 2 - lin (Xc N) z) ∧
          F N K 1 θ η z 2 = β * exp (-z 2) - ã * exp (z 2 - lin (Xc N) z) := by
  have hK' : (2:ℝ) ≤ K := by exact_mod_cast hK
  have hN' : (K:ℝ) + 5 ≤ N := by exact_mod_cast hN
  have hN0 : (0:ℝ) < N := by linarith
  have hN1 : (0:ℝ) < N - 1 := by linarith
  obtain ⟨Cu', hCu'⟩ : ∃ c, c = max Cu 0 := ⟨_, rfl⟩
  obtain ⟨CE, hCE⟩ : ∃ c, c = exp (Cu' + max Cv 0) := ⟨_, rfl⟩
  have hCE0 : 0 < CE := hCE ▸ exp_pos _
  have hCu'0 : 0 ≤ Cu' := hCu' ▸ le_max_right _ _
  have hexpCu : exp (-Cu') ≤ 1 := exp_le_one_iff.mpr (by linarith)
  have hexpCu0 : 0 < exp (-Cu') := exp_pos _
  have hM0 : 0 < 1 + (N:ℝ) + K * CE := by positivity
  refine ⟨N + |CZ| + 4 * K * CE, exp (-Cu') / (3 * (N:ℝ) ^ 2), (K + 1) * (1 + N + K * CE) / (N:ℝ) ^ 2,
    exp (-Cu') / (3 * ((N:ℝ) - 1)), (K + 1) / ((N:ℝ) - 1), K / 4,
    (K * ((N:ℝ) - 1) + (N - K - 1) + K * CE) / ((N:ℝ) - 1), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact div_pos hexpCu0 (by positivity)
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : 1 ≤ ((K:ℝ) + 1) * (1 + N + K * CE) := by nlinarith
    nlinarith [sq_nonneg (N:ℝ)]
  · exact div_pos hexpCu0 (by positivity)
  · rw [div_le_div_iff₀ (by positivity) hN1]
    nlinarith
  · positivity
  · rw [le_div_iff₀ hN1]
    nlinarith
  intro z hG hv hu hZ hB θ η hA
  exact F1_pointwise hK hN Cv Cu CZ Cu' CE hCu' hCE z hG hv hu hZ hB θ η hA




end DFS
