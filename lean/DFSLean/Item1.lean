import DFSLean.Basic

/-!
# Theorem C.5, item 1 (work package C): `v = y₁ - y₂` is bounded above.

Paper l.466–570. In the region `v > 0` the selection `η = 1` is forced, `E = e^{u+v}`, and
`(N-1) v' = KM + R - H - ∑ Bᵢ - 2 ∑ Aᵢ - KQ ≤ KM + R - KQ`. We use a single unified estimate
instead of the paper's two cases: with `b = e^{y₁} ≥ e^v` and `E ≥ e^v`, once `e^v ≥ 4KN`,
`K(N-1)/(b+N-1) + (N-K-1)/D₄ ≤ KE/D₄`. The barrier `IsSol.barrier` then gives the bound.
-/

noncomputable section

namespace DFS

open Real Filter Topology Set

variable {N K : ℕ}

private lemma C_F2 (α θ η : ℝ) (z : Fin 4 → ℝ) : F N K α θ η z 2 =
    α / ((N : ℝ) - 1) * ((K : ℝ) * ((N : ℝ) - 1) / D3 N z
        + ((N : ℝ) - K - 1 + (K : ℝ) * E z * (1 - η)) / D4 N K z
        - exp (z 2) / D1 N z
        - ∑ j ∈ Finset.range K, ((j : ℝ) * E z * η + exp (z 2)) / D2 N K j z) := rfl

private lemma C_F3 (α θ η : ℝ) (z : Fin 4 → ℝ) : F N K α θ η z 3 =
    α / ((N : ℝ) - 1) *
      (∑ j ∈ Finset.range K, (j : ℝ) * E z * η / D2 N K j z + (K : ℝ) * E z * η / D4 N K z) :=
  rfl

/-- The key real inequality: `K(N-1)/(b+N-1) + (N-K-1)/D₄ ≤ KE/D₄` once `b, E ≥ 4KN`. -/
private lemma C_key_v {k n b e : ℝ} (hk : 2 ≤ k) (hn : k + 5 ≤ n) (hb : 4 * k * n ≤ b)
    (he : 4 * k * n ≤ e) :
    k * (n - 1) / (b + n - 1) + (n - k - 1) / (k * e + b + n - k - 1)
      ≤ k * e / (k * e + b + n - k - 1) := by
  have hkn : 0 ≤ k * n := by nlinarith
  have hb0 : 0 ≤ b := by nlinarith
  have he0 : 0 ≤ e := by nlinarith
  have hD3 : 0 < b + n - 1 := by linarith
  have hke : 0 ≤ k * e := by nlinarith
  have hD4 : 0 < k * e + b + n - k - 1 := by linarith
  suffices h : k * (n - 1) / (b + n - 1) ≤ (k * e - (n - k - 1)) / (k * e + b + n - k - 1) by
    rw [sub_div] at h; linarith
  rw [div_le_div_iff₀ hD3 hD4]
  have h1 : 0 ≤ k * e * (b / 4 - k * (n - 1)) := mul_nonneg hke (by nlinarith)
  have h2 : 0 ≤ b * (k * e / 2 - (k * n + n)) := mul_nonneg hb0 (by nlinarith)
  have h3 : (4 * k * n) * (4 * k * n) ≤ e * b := mul_le_mul he hb (by nlinarith) he0
  have h4 : 0 ≤ k * (4 * k * n) * (4 * k * n) / 4 - (n - 1) * (n - k - 1) * (k + 1) := by
    have h5 : (n - 1) * (n - k - 1) ≤ n * n := by nlinarith
    have hk4 : 4 ≤ k * k := by nlinarith
    have h6 : k + 1 ≤ 4 * (k * (k * k)) := by nlinarith
    have h7 : (n - 1) * (n - k - 1) * (k + 1) ≤ n * n * (k + 1) :=
      mul_le_mul_of_nonneg_right h5 (by linarith)
    have h8 : n * n * (k + 1) ≤ n * n * (4 * (k * (k * k))) :=
      mul_le_mul_of_nonneg_left h6 (by nlinarith)
    have h9 : k * (4 * k * n) * (4 * k * n) / 4 = n * n * (4 * (k * (k * k))) := by ring
    linarith
  nlinarith

/-- State lemma for item 1: above the level `4KN`, `v' ≤ 0` for every admissible selection. -/
lemma C_v_state (hK : 2 ≤ K) (hN : K + 5 ≤ N) :
    ∃ C₁ : ℝ, ∀ z : Fin 4 → ℝ, Good z → C₁ < v z →
      ∀ θ η, Adm z θ η → lin ![0, 0, 1, -1] (F N K 1 θ η z) ≤ 0 := by
  have hNK : (K : ℝ) + 5 ≤ N := by exact_mod_cast hN
  have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
  refine ⟨4 * K * N, fun z hz hv θ η hadm => ?_⟩
  obtain ⟨hu0, hx2, hy1, hy2⟩ := hz
  have hv0 : 0 < v z := lt_of_le_of_lt (by positivity) hv
  have hη : η = 1 := hadm.2.2.2.2.1 hv0
  subst hη
  -- exponential bounds
  have hev : 4 * K * N ≤ exp (v z) := by
    have := add_one_le_exp (v z); linarith
  have hE : E z = exp (u z + v z) := by
    unfold E; rw [max_eq_left hu0, max_eq_left hv0.le]
  have hEv : exp (v z) ≤ E z := by
    rw [hE]; exact exp_le_exp.2 (by linarith)
  have hbv : exp (v z) ≤ exp (z 2) := by
    apply exp_le_exp.2; unfold v; linarith
  have key := C_key_v (k := (K : ℝ)) (n := (N : ℝ)) (b := exp (z 2)) (e := E z) hK2 hNK
    (hev.trans hbv) (hev.trans hEv)
  -- positivity facts
  have ha := exp_pos (z 0)
  have hb := exp_pos (z 2)
  have he : 0 < E z := exp_pos _
  have hD1 : 0 < D1 N z := by unfold D1; linarith
  have hD2 : ∀ j ∈ Finset.range K, 0 < D2 N K j z := by
    intro j hj
    have hjK : (j : ℝ) < K := by exact_mod_cast Finset.mem_range.1 hj
    have : 0 ≤ ((K : ℝ) - j) * exp (z 0) := mul_nonneg (by linarith) ha.le
    have : 0 ≤ (j : ℝ) * E z := mul_nonneg (Nat.cast_nonneg j) he.le
    unfold D2; linarith
  have hS1 : 0 ≤ ∑ j ∈ Finset.range K, ((j : ℝ) * E z * 1 + exp (z 2)) / D2 N K j z :=
    Finset.sum_nonneg fun j hj =>
      div_nonneg (by have := mul_nonneg (Nat.cast_nonneg (α := ℝ) j) he.le; linarith)
        (hD2 j hj).le
  have hS2 : 0 ≤ ∑ j ∈ Finset.range K, (j : ℝ) * E z * 1 / D2 N K j z :=
    Finset.sum_nonneg fun j hj =>
      div_nonneg (by have := mul_nonneg (Nat.cast_nonneg (α := ℝ) j) he.le; linarith)
        (hD2 j hj).le
  have hH : 0 ≤ exp (z 2) / D1 N z := div_nonneg hb.le hD1.le
  have hN1 : 0 < (N : ℝ) - 1 := by linarith
  have hlin : lin ![0, 0, 1, -1] (F N K 1 θ 1 z) = F N K 1 θ 1 z 2 - F N K 1 θ 1 z 3 := by
    simp [lin]; ring
  rw [hlin, C_F2, C_F3]
  have hD3 : D3 N z = exp (z 2) + N - 1 := rfl
  have hD4 : D4 N K z = K * E z + exp (z 2) + N - K - 1 := rfl
  rw [hD3, hD4] at *
  have hX : (K : ℝ) * ((N : ℝ) - 1) / (exp (z 2) + N - 1)
        + ((N : ℝ) - K - 1 + (K : ℝ) * E z * (1 - 1)) / (K * E z + exp (z 2) + N - K - 1)
        - exp (z 2) / D1 N z
        - ∑ j ∈ Finset.range K, ((j : ℝ) * E z * 1 + exp (z 2)) / D2 N K j z
        - (∑ j ∈ Finset.range K, (j : ℝ) * E z * 1 / D2 N K j z
            + (K : ℝ) * E z * 1 / (K * E z + exp (z 2) + N - K - 1)) ≤ 0 := by
    simp only [sub_self, mul_zero, add_zero, mul_one] at key hS1 hS2 ⊢
    linarith
  have := mul_nonpos_of_nonneg_of_nonpos (div_nonneg zero_le_one hN1.le) hX
  linarith

theorem item1 (hK : 2 ≤ K) (hN : K + 5 ≤ N) (R : ℝ) :
    ∃ Cv : ℝ, ∀ z : ℝ → Fin 4 → ℝ, IsSol N K 1 z → Init R (z 0) → ∀ t ≥ 0, v (z t) ≤ Cv := by
  obtain ⟨C₁, hC₁⟩ := C_v_state hK hN
  refine ⟨max R C₁, fun z hz hinit t ht => ?_⟩
  have hgood := hz.good hK hN hinit.1
  have hlin : ∀ s, lin ![0, 0, 1, -1] (z s) = v (z s) := fun s => by
    simp [lin, v]; ring
  have hbar := hz.barrier ![0, 0, 1, -1] C₁ (a := 0) (b := t) le_rfl
    (fun s hs hL θ η hadm => hC₁ (z s) (hgood s hs.1) (by rw [← hlin]; exact hL) θ η hadm)
    t ⟨ht, le_rfl⟩
  rw [hlin, hlin] at hbar
  have hv0 : v (z 0) ≤ R := by
    unfold v; have := hinit.2 2; have := hinit.1.2.2.2; linarith
  exact hbar.trans (max_le_max hv0 le_rfl)



end DFS
