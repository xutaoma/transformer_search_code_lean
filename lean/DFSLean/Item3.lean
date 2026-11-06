import DFSLean.Basic
import DFSLean.Item1
import DFSLean.Item2
import DFSLean.Lyapunov

/-!
# Theorem C.5, item 3 (work package C): `2y₁ - x₁` and `u = x₁ - x₂` are bounded above.

Paper l.989–1065.
* `2y₁ - x₁`: Lyapunov barrier for `log W = 2x₁ - 3x₂ + 2y₁` (`DFS.lyapunov_state`) from the time
  `T` after which `y₁ ≥ B₀` (`DFS.item2`), with `v ≤ Cv` from `DFS.item1`; on `[0, T]` the
  Lipschitz bound controls `log W`. Then `2y₁ - x₁ = log W - 3u ≤ log W`.
* `u`: in the region `u > 0` (so `θ = 1`), `u' ≤ x₁' ≤ (1/N)[G + ∑ Cᵢ - KQ]` with
  `G, Cᵢ ≤ (b + N)/a` and `KQ ≥ Ks/(Ks + b + N - K - 1)` (`s = e^u ≤ E`); this is `≤ 0` once
  `u ≥ 2y₁ - x₁ + C₂` (we use `b² ≤ e^{CZ} a`, `s ≤ a`, `b ≥ 1`). Barrier `IsSol.barrier`.
-/

noncomputable section

namespace DFS

open Real Filter Topology Set

variable {N K : ℕ}

private lemma C_F0 (α θ η : ℝ) (z : Fin 4 → ℝ) : F N K α θ η z 0 =
    α / (N : ℝ) * ((exp (z 2) + (N : ℝ) - 2) / D1 N z
        + ∑ j ∈ Finset.range K,
            (exp (z 2) + (N : ℝ) - K - 1 + (j : ℝ) * E z * (1 - θ)) / D2 N K j z
        - (K : ℝ) * E z * θ / D4 N K z) := rfl

private lemma C_F1 (α θ η : ℝ) (z : Fin 4 → ℝ) : F N K α θ η z 1 =
    α / ((N : ℝ) * ((N : ℝ) - 1)) *
       (∑ j ∈ Finset.range K, (j : ℝ) * E z * θ / D2 N K j z + (K : ℝ) * E z * θ / D4 N K z) :=
  rfl

/-- Key real inequality for the `u` bound. Here `a = e^{x₁}`, `b = e^{y₁}`, `s = e^u`,
`e = E`, `lam = e^{CZ}`; the hypothesis `hsM` says `u > CZ + log M`. -/
private lemma C_key_u {k n a b s e lam : ℝ} (hk : 2 ≤ k) (hn : k + 5 ≤ n) (ha : 0 < a)
    (hb : 1 ≤ b) (hs : 0 < s) (hsa : s ≤ a) (hse : s ≤ e) (hba : b * b ≤ lam * a)
    (hsM : 4 * ((k + 1) * (n + 1)) ^ 2 * (n + 1) * lam < s) :
    (b + n - 2) / (a + b + n - 2) + k * ((b + n - k - 1) / a)
      ≤ k * e / (k * e + b + n - k - 1) := by
  set Q := (k + 1) * (n + 1) with hQdef
  set M := 4 * Q ^ 2 * (n + 1) with hMdef
  have hk0 : 0 ≤ k := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hQ : 1 ≤ Q := by rw [hQdef]; nlinarith
  have hQ0 : 0 ≤ Q := by linarith
  have hM0 : 0 ≤ M := by rw [hMdef]; exact mul_nonneg (by positivity) (by linarith)
  have hc : 0 < b + n - k - 1 := by linarith
  have hb0 : 0 ≤ b := by linarith
  have h1 : (b + n - 2) / (a + b + n - 2) ≤ (b + n) / a := by
    rw [div_le_div_iff₀ (by linarith) ha]; nlinarith
  have h2 : k * ((b + n - k - 1) / a) ≤ k * ((b + n) / a) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) ha.le) hk0
  have h3 : k * s / (k * s + b + n - k - 1) ≤ k * e / (k * e + b + n - k - 1) := by
    have hks : 0 ≤ k * s := mul_nonneg hk0 hs.le
    have hke : 0 ≤ k * e := mul_nonneg hk0 (hs.le.trans hse)
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_nonneg (mul_nonneg hk0 hc.le) (sub_nonneg.2 hse)]
  have h4 : (k + 1) * ((b + n) / a) ≤ k * s / (k * s + b + n - k - 1) := by
    have hks : 0 ≤ k * s := mul_nonneg hk0 hs.le
    rw [← mul_div_assoc, div_le_div_iff₀ ha (by linarith)]
    have hb2 : M * (b * b) ≤ s * a := by
      calc M * (b * b) ≤ M * (lam * a) := mul_le_mul_of_nonneg_left hba hM0
        _ = (M * lam) * a := by ring
        _ ≤ s * a := mul_le_mul_of_nonneg_right hsM.le ha.le
    have hsa2 : s * a ≤ a * a := mul_le_mul_of_nonneg_right hsa ha.le
    have hb3 : 2 * Q * b ≤ a := by
      apply nonneg_le_nonneg_of_sq_le_sq ha.le
      have hid : M * (b * b) = (2 * Q * b) * (2 * Q * b) + 4 * (Q ^ 2 * (b * b) * n) := by
        rw [hMdef]; ring
      have : 0 ≤ Q ^ 2 * (b * b) * n := mul_nonneg (by positivity) hn0
      linarith
    have e1 : (k + 1) * (b + n) ≤ Q * b := by
      rw [hQdef]
      nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ k + 1) hn0) (sub_nonneg.2 hb)]
    have e2 : 0 ≤ k * s + b + n - k - 1 := by linarith
    have hQb : 0 ≤ Q * b := mul_nonneg hQ0 hb0
    calc (k + 1) * (b + n) * (k * s + b + n - k - 1)
        ≤ Q * b * (k * s + b + n) := by
          apply mul_le_mul e1 (by linarith) e2 hQb
      _ = (k * s) * (Q * b) + Q * (b * b) + Q * n * b := by ring
      _ ≤ (k * s) * (Q * b) + Q * (n + 1) * (b * b) := by
          have : Q * n * b ≤ Q * n * (b * b) :=
            mul_le_mul_of_nonneg_left (by nlinarith) (mul_nonneg hQ0 hn0)
          linarith
      _ ≤ k * s * a / 2 + k * s * a / 2 := by
          have i1 : (k * s) * (2 * Q * b) ≤ (k * s) * a := mul_le_mul_of_nonneg_left hb3 hks
          have i2 : 2 * Q * (n + 1) * (b * b) ≤ k * M * (b * b) := by
            refine mul_le_mul_of_nonneg_right ?_ (mul_self_nonneg b)
            have h2kQ : 1 ≤ 2 * k * Q := by nlinarith
            have hpos : 0 ≤ 2 * Q * (n + 1) := mul_nonneg (by linarith) (by linarith)
            have hid : k * M = 2 * Q * (n + 1) * (2 * k * Q) := by rw [hMdef]; ring
            rw [hid]
            calc 2 * Q * (n + 1) = 2 * Q * (n + 1) * 1 := by ring
              _ ≤ 2 * Q * (n + 1) * (2 * k * Q) := mul_le_mul_of_nonneg_left h2kQ hpos
          have i3 : k * (M * (b * b)) ≤ k * (s * a) := mul_le_mul_of_nonneg_left hb2 hk0
          linarith
      _ = k * s * a := by ring
  have := add_le_add h1 h2
  have h5 : (b + n) / a + k * ((b + n) / a) = (k + 1) * ((b + n) / a) := by ring
  linarith

/-- State lemma for the `u` bound: given `2y₁ - x₁ ≤ CZ`, above a level `Cu'` every admissible
velocity has `u' ≤ 0`. -/
lemma C_u_state (hK : 2 ≤ K) (hN : K + 5 ≤ N) (CZ : ℝ) :
    ∃ Cu' : ℝ, ∀ z : Fin 4 → ℝ, Good z → 2 * z 2 - z 0 ≤ CZ → Cu' < u z →
      ∀ θ η, Adm z θ η → lin ![1, -1, 0, 0] (F N K 1 θ η z) ≤ 0 := by
  have hNK : (K : ℝ) + 5 ≤ N := by exact_mod_cast hN
  have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
  set M : ℝ := 4 * (((K : ℝ) + 1) * ((N : ℝ) + 1)) ^ 2 * ((N : ℝ) + 1) with hMdef
  have hM : 0 < M := by positivity
  refine ⟨max (CZ + log M) 0, fun z hz hZ hu θ η hadm => ?_⟩
  obtain ⟨hu0, hx2, hy1, hy2⟩ := hz
  have hupos : 0 < u z := lt_of_le_of_lt (le_max_right _ _) hu
  have huM : CZ + log M < u z := lt_of_le_of_lt (le_max_left _ _) hu
  have hθ : θ = 1 := hadm.2.2.1 hupos
  subst hθ
  -- real quantities
  have ha := exp_pos (z 0)
  have hb1 : 1 ≤ exp (z 2) := one_le_exp hy1
  have hs := exp_pos (u z)
  have hsa : exp (u z) ≤ exp (z 0) := exp_le_exp.2 (by unfold u; linarith)
  have hse : exp (u z) ≤ E z := by
    unfold E; apply exp_le_exp.2
    have := le_max_left (u z) 0; have := le_max_right (v z) 0; linarith
  have hba : exp (z 2) * exp (z 2) ≤ exp CZ * exp (z 0) := by
    rw [← exp_add, ← exp_add]; exact exp_le_exp.2 (by linarith)
  have hsM : M * exp CZ < exp (u z) := by
    calc M * exp CZ = exp (CZ + log M) := by rw [exp_add, exp_log hM]; ring
      _ < exp (u z) := exp_lt_exp.2 huM
  have key := C_key_u (k := (K : ℝ)) (n := (N : ℝ)) (a := exp (z 0)) (b := exp (z 2))
    (s := exp (u z)) (e := E z) (lam := exp CZ) hK2 hNK ha hb1 hs hsa hse hba hsM
  -- positivity facts
  have he : 0 < E z := exp_pos _
  have hD2a : ∀ j ∈ Finset.range K, exp (z 0) ≤ D2 N K j z := by
    intro j hj
    have hjK : (j : ℝ) + 1 ≤ K := by
      have := Finset.mem_range.1 hj; exact_mod_cast this
    have : exp (z 0) ≤ ((K : ℝ) - j) * exp (z 0) := by
      nlinarith
    have : 0 ≤ (j : ℝ) * E z := mul_nonneg (Nat.cast_nonneg j) he.le
    unfold D2; linarith
  have hD4 : 0 < D4 N K z := by
    have : 0 ≤ (K : ℝ) * E z := mul_nonneg (Nat.cast_nonneg K) he.le
    unfold D4; linarith
  have hS1 : ∑ j ∈ Finset.range K, (exp (z 2) + (N : ℝ) - K - 1 + (j : ℝ) * E z * (1 - 1))
      / D2 N K j z ≤ K * ((exp (z 2) + (N : ℝ) - K - 1) / exp (z 0)) := by
    have : ∀ j ∈ Finset.range K, (exp (z 2) + (N : ℝ) - K - 1 + (j : ℝ) * E z * (1 - 1))
        / D2 N K j z ≤ (exp (z 2) + (N : ℝ) - K - 1) / exp (z 0) := fun j hj => by
      simp only [sub_self, mul_zero, add_zero]
      exact div_le_div_of_nonneg_left (by linarith) ha (hD2a j hj)
    refine (Finset.sum_le_sum this).trans ?_
    simp
  have hS2 : 0 ≤ ∑ j ∈ Finset.range K, (j : ℝ) * E z * 1 / D2 N K j z :=
    Finset.sum_nonneg fun j hj =>
      div_nonneg (by have := mul_nonneg (Nat.cast_nonneg (α := ℝ) j) he.le; linarith)
        ((ha.le).trans (hD2a j hj))
  have hQ : 0 ≤ (K : ℝ) * E z * 1 / D4 N K z :=
    div_nonneg (by have := mul_nonneg (Nat.cast_nonneg (α := ℝ) K) he.le; linarith) hD4.le
  have hN0 : 0 < (N : ℝ) := by linarith
  have hN1 : 0 < (N : ℝ) * ((N : ℝ) - 1) := by nlinarith
  have hlin : lin ![1, -1, 0, 0] (F N K 1 1 η z) = F N K 1 1 η z 0 - F N K 1 1 η z 1 := by
    simp [lin]; ring
  rw [hlin, C_F0, C_F1]
  have hF1 := mul_nonneg (div_nonneg zero_le_one hN1.le) (add_nonneg hS2 hQ)
  have hD1 : D1 N z = exp (z 0) + exp (z 2) + N - 2 := rfl
  have hD4' : D4 N K z = K * E z + exp (z 2) + N - K - 1 := rfl
  have hX : (exp (z 2) + (N : ℝ) - 2) / D1 N z
        + ∑ j ∈ Finset.range K,
            (exp (z 2) + (N : ℝ) - K - 1 + (j : ℝ) * E z * (1 - 1)) / D2 N K j z
        - (K : ℝ) * E z * 1 / D4 N K z ≤ 0 := by
    rw [hD1, hD4', mul_one]
    linarith
  have := mul_nonpos_of_nonneg_of_nonpos (div_nonneg zero_le_one hN0.le) hX
  linarith

theorem item3 (hK : 2 ≤ K) (hN : K + 5 ≤ N) (R : ℝ) :
    ∃ CZ Cu : ℝ, ∀ z : ℝ → Fin 4 → ℝ, IsSol N K 1 z → Init R (z 0) →
      ∀ t ≥ 0, 2 * z t 2 - z t 0 ≤ CZ ∧ u (z t) ≤ Cu := by
  obtain ⟨Cv, hCv⟩ := DFS.item1 hK hN R
  obtain ⟨B₀, CW, hW⟩ := DFS.lyapunov_state hK hN Cv
  obtain ⟨T₀, hT₀⟩ := DFS.item2 hK hN R B₀
  set T := max T₀ 0 with hTdef
  have hT0 : 0 ≤ T := le_max_right _ _
  set M₀ : ℝ := 4 * (R + (K + 2) * T) with hM₀
  set CZ := max M₀ CW with hCZ
  obtain ⟨Cu', hCu'⟩ := C_u_state hK hN CZ
  refine ⟨CZ, max R Cu', fun z hz hinit => ?_⟩
  have hgood := hz.good hK hN hinit.1
  have hK0 : (0 : ℝ) ≤ K + 2 := by positivity
  -- `log W` on `[0, T]`
  have hsmall : ∀ s, 0 ≤ s → s ≤ T → lin ![2, -3, 2, 0] (z s) ≤ M₀ := by
    intro s hs hsT
    have h0 := hz.lipschitz hK hN zero_le_one 0 (le_refl 0) hs
    have h2 := hz.lipschitz hK hN zero_le_one 2 (le_refl 0) hs
    have hx2 := (hgood s hs).2.1
    have hR0 := hinit.2 0
    have hR2 := hinit.2 2
    have hsT' : ((K : ℝ) + 2) * 1 * (s - 0) ≤ (K + 2) * T := by
      rw [mul_one, sub_zero]; exact mul_le_mul_of_nonneg_left hsT hK0
    have h0' := (abs_le.1 h0).2
    have h2' := (abs_le.1 h2).2
    simp only [lin, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [hM₀]
    linarith
  -- `log W ≤ CZ` for all `t ≥ 0`
  have hWle : ∀ t ≥ 0, lin ![2, -3, 2, 0] (z t) ≤ CZ := by
    intro t ht
    by_cases htT : t ≤ T
    · exact (hsmall t ht htT).trans (le_max_left _ _)
    · rw [not_le] at htT
      have hbar := hz.barrier ![2, -3, 2, 0] CW (a := T) (b := t) hT0
        (fun s hs hL θ η hadm =>
          hW (z s) (hgood s (hT0.trans hs.1)) (hCv z hz hinit s (hT0.trans hs.1))
            (hT₀ z hz hinit s ((le_max_left _ _).trans hs.1)).2.1 hL θ η hadm)
        t ⟨htT.le, le_rfl⟩
      exact hbar.trans (max_le_max (hsmall T hT0 le_rfl) le_rfl)
  have hZ : ∀ t ≥ 0, 2 * z t 2 - z t 0 ≤ CZ := fun t ht => by
    have h1 := hWle t ht
    have hu := (hgood t ht).1
    simp only [lin, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at h1
    unfold u at hu
    linarith
  -- `u` bound
  have hlin : ∀ s, lin ![1, -1, 0, 0] (z s) = u (z s) := fun s => by
    simp [lin, u]; ring
  intro t ht
  refine ⟨hZ t ht, ?_⟩
  have hbar := hz.barrier ![1, -1, 0, 0] Cu' (a := 0) (b := t) le_rfl
    (fun s hs hL θ η hadm =>
      hCu' (z s) (hgood s hs.1) (hZ s hs.1) (by rw [← hlin]; exact hL) θ η hadm)
    t ⟨ht, le_rfl⟩
  rw [hlin, hlin] at hbar
  have hu0 : u (z 0) ≤ R := by
    unfold u; have := hinit.2 0; have := hinit.1.2.1; linarith
  exact hbar.trans (max_le_max hu0 le_rfl)



end DFS
