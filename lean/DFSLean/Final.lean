import DFSLean.CorC3
import DFSLean.GenBound
import DFSLean.Item4
import DFSLean.LemmaC2

namespace DFS
open Real Finset Filter Topology Set
variable {N K : ℕ}

/-! ## Helper lemmas for Theorem 4.2 -/

private lemma F_proj0 (s : Fin 8 → ℝ) : proj s 0 = s 2 := by simp [proj]
private lemma F_proj1 (s : Fin 8 → ℝ) : proj s 1 = s 1 := by simp [proj]
private lemma F_proj2 (s : Fin 8 → ℝ) : proj s 2 = s 4 - s 5 := by simp [proj]
private lemma F_proj3 (s : Fin 8 → ℝ) : proj s 3 = s 6 - s 7 := by simp [proj]

private lemma F_alpha_T0 {α : ℝ} (hα : 0 < α) :
    α * T0 N K α = (N : ℝ) / (4 * ((K : ℝ) + 1)) := by
  unfold T0
  have hK : (0 : ℝ) < 4 * ((K : ℝ) + 1) := by positivity
  field_simp

/-- `|log x - log (x - c)| ≤ log 2` once `x ≥ 2c > 0`. -/
private lemma F_log_shift {x c : ℝ} (hc : 0 < c) (hx : 2 * c ≤ x) :
    |log x - log (x - c)| ≤ log 2 := by
  have h1 : 0 < x - c := by linarith
  have h2 : log (x - c) ≤ log x := Real.log_le_log h1 (by linarith)
  have h3 : log x ≤ log 2 + log (x - c) := by
    rw [← Real.log_mul (by norm_num) h1.ne']
    exact Real.log_le_log (by linarith) (by linarith)
  rw [abs_le]; constructor <;> linarith

private lemma F_P8_le (hN : 2 ≤ N) (m : Fin 8) : P8 N m ≤ 1 := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  unfold P8
  split_ifs
  · rw [div_le_one (by linarith)]; linarith
  · rw [div_le_one (by nlinarith)]; nlinarith

/-- `(αt)^{-(N-1)/N} = exp (-(L - L/N))` with `L = log (αt)`. -/
private lemma F_rpow (hN : 1 ≤ N) {x : ℝ} (hx : 0 < x) :
    x ^ (-(((N : ℝ) - 1) / N)) = exp (-(log x - log x / N)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.rpow_def_of_pos hx]
  congr 1
  field_simp

private lemma F_lip_small {K' α t P ts : ℝ} (hK : 0 ≤ K') (hP1 : P ≤ 1)
    (hαt0 : 0 ≤ α * t) (hαt : α * t ≤ ts) : K' * α * P * (t - 0) ≤ K' * ts := by
  have h1 : P * (α * t) ≤ ts := by nlinarith
  have h2 : K' * α * P * (t - 0) = K' * (P * (α * t)) := by ring
  rw [h2]; exact mul_le_mul_of_nonneg_left h1 hK

/-- Recovery of `g, d` from `g - d` and the conserved quantity `g + (n-1) d` (eq. `gd_recovery`). -/
private lemma F_recover {n g d A L : ℝ} (hn : 1 ≤ n) (h : g + (n - 1) * d = A) :
    |g - (n - 1) / n * L| ≤ |g - d - L| + |A| ∧ |d + L / n| ≤ |g - d - L| + |A| := by
  have hn0 : 0 < n := by linarith
  have e1 : g - (n - 1) / n * L = ((n - 1) * (g - d - L) + A) / n := by
    field_simp
    linear_combination h
  have e2 : d + L / n = (A - (g - d - L)) / n := by
    field_simp
    linear_combination h
  rw [e1, e2, abs_div, abs_div, abs_of_pos hn0]
  constructor
  · rw [div_le_iff₀ hn0]
    calc |(n - 1) * (g - d - L) + A| ≤ |(n - 1) * (g - d - L)| + |A| := abs_add_le _ _
      _ = (n - 1) * |g - d - L| + |A| := by rw [abs_mul, abs_of_nonneg (by linarith)]
      _ ≤ _ := by nlinarith [abs_nonneg (g - d - L), abs_nonneg A]
  · rw [div_le_iff₀ hn0]
    calc |A - (g - d - L)| ≤ |A| + |g - d - L| := abs_sub _ _
      _ ≤ _ := by nlinarith [abs_nonneg (g - d - L), abs_nonneg A]

private lemma F_exp_le {M L w x : ℝ} (h : x ≤ M - (L - w)) :
    exp x ≤ exp M * exp (-(L - w)) := by
  rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)

/-! ## Theorem 4.2 -/

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
  obtain ⟨cs0, hcs0, hinit⟩ := DFS.lemmaC2_initial hK
  refine ⟨min cs0 (1 / 2), lt_min hcs0 (by norm_num), ?_⟩
  intro N _ hN c0 c0' h0 h1 hc
  have hN2 : 2 ≤ N := by omega
  have hNr : (7 : ℝ) ≤ N := by exact_mod_cast (show 7 ≤ N by omega)
  have hNsq : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hNsq0 : (0 : ℝ) < (N : ℝ) ^ 2 := by linarith
  have hc0s : c0 ≤ cs0 / (N : ℝ) ^ 2 :=
    le_trans hc (div_le_div_of_nonneg_right (min_le_left _ _) hNsq0.le)
  have hc0h : c0 ≤ 1 / 2 := by
    have h2 : c0 ≤ (1 / 2) / (N : ℝ) ^ 2 :=
      le_trans hc (div_le_div_of_nonneg_right (min_le_right _ _) hNsq0.le)
    have h3 : (1 / 2 : ℝ) / (N : ℝ) ^ 2 ≤ 1 / 2 := div_le_self (by norm_num) hNsq
    linarith
  obtain ⟨Cv, CZ, Cu, C₁, T₁, hfour⟩ := DFS.four_parameter_log_convergence hK hN 2
  obtain ⟨Cg, hCg0, hgen⟩ := DFS.genLoss_bound hN2 Cu Cv
  obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = (N : ℝ) / (4 * ((K : ℝ) + 1)) := ⟨_, rfl⟩
  have hcpos : 0 < c := by rw [hc_def]; positivity
  obtain ⟨tstar, htstar⟩ : ∃ x : ℝ, x = max (T₁ + c) (max (2 * c) 1) := ⟨_, rfl⟩
  have ht1 : T₁ + c ≤ tstar := htstar ▸ le_max_left _ _
  have ht2 : 2 * c ≤ tstar := htstar ▸ le_trans (le_max_left _ _) (le_max_right _ _)
  have ht3 : 1 ≤ tstar := htstar ▸ le_trans (le_max_right _ _) (le_max_right _ _)
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = c0 + ((N : ℝ) - 1) * c0' := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = |C₁| + 2 * log 2 := ⟨_, rfl⟩
  have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hD0 : 0 ≤ D := by rw [hD]; have := abs_nonneg C₁; linarith
  have hC₁D : |C₁| + 2 * log 2 ≤ D := hD.ge
  obtain ⟨Cfix, hCfix⟩ : ∃ x : ℝ, x = |c0 - c0'| + 4 * ((2 * K + 2) * tstar) := ⟨_, rfl⟩
  have hCfix0 : 0 ≤ Cfix := by
    rw [hCfix]
    have := abs_nonneg (c0 - c0')
    have : (0 : ℝ) ≤ (2 * K + 2) * tstar := mul_nonneg (by positivity) (by linarith)
    linarith
  obtain ⟨C, hC⟩ : ∃ x : ℝ, x = 2 * D + |A| + ((N : ℝ) * c0 + 1) + Cfix := ⟨_, rfl⟩
  have hNc0 : 0 ≤ (N : ℝ) * c0 := mul_nonneg (by positivity) (by linarith)
  have hA0 : 0 ≤ |A| := abs_nonneg _
  have hC0 : 0 ≤ C := by rw [hC]; linarith
  refine ⟨C, Cg * (4 * exp (3 * C)), tstar, ?_⟩
  intro α hα s hs hs0
  have hT0 := hinit N hN c0 c0' α h0 h1 hc0s hα s hs hs0
  obtain ⟨hz, hzinit, hg1, κ, hκ, hg2⟩ := DFS.corC3 hK hN h0 h1 hc0h hα hs hs0 hT0
  have hreg := DFS.lemmaC2_region hK hN h0 h1 hα hs hs0
  have hlip := DFS.lemmaC2_lip hK hN h0 h1 hα hs hs0
  set T := T0 N K α with hT
  have hαT : α * T = c := by rw [hc_def]; exact F_alpha_T0 hα
  have hT0pos : 0 ≤ T := by
    by_contra hneg; rw [not_le] at hneg; nlinarith
  have hzinit' : Init 2 ((fun t => proj (s (T + t))) 0) := by
    simp only [add_zero]; exact hzinit
  obtain ⟨hv, -, hu, hrate⟩ := hfour α hα _ hz hzinit'
  have e4 : s 0 4 = c0 := by rw [hs0]; rfl
  have e5 : s 0 5 = c0' := by rw [hs0]; rfl
  have e6 : s 0 6 = c0 := by rw [hs0]; rfl
  have e7 : s 0 7 = c0 := by rw [hs0]; rfl
  have hκ' : |κ| ≤ (N : ℝ) * c0 + 1 := by
    rw [abs_le] at hκ ⊢; constructor <;> linarith
  -- basic estimates for large times (time shift `t ↦ t - T₀`)
  have key : ∀ t ≥ tstar / α, 1 ≤ α * t ∧ T ≤ t ∧
      |s t 2 - 2 * log (α * t)| ≤ D ∧ |s t 1 - 2 * log (α * t)| ≤ D ∧
      |s t 4 - s t 5 - log (α * t)| ≤ D ∧ |s t 6 - s t 7 - log (α * t)| ≤ D ∧
      |s t 4 - s t 5 - (s t 6 - s t 7)| ≤ 2 * D ∧
      s t 2 - s t 1 ≤ Cu ∧ s t 4 - s t 5 - (s t 6 - s t 7) ≤ Cv := by
    intro t ht
    have hat : tstar ≤ α * t := by
      rw [ge_iff_le, div_le_iff₀ hα] at ht; linarith [mul_comm t α]
    have hTt : T ≤ t := by
      by_contra hlt; rw [not_le] at hlt
      have := mul_lt_mul_of_pos_left hlt hα
      linarith
    have hshift : α * (t - T) = α * t - c := by rw [mul_sub, hαT]
    have ht' : t - T ≥ T₁ / α := by
      rw [ge_iff_le, div_le_iff₀ hα]; linarith [mul_comm (t - T) α]
    have hTT : T + (t - T) = t := by ring
    obtain ⟨r1, r2, r3, r4⟩ := hrate (t - T) ht'
    have hv' := hv (t - T) (by linarith)
    have hu' := (hu (t - T) (by linarith)).2
    simp only [hTT, F_proj0, F_proj1, F_proj2, F_proj3, DFS.u, DFS.v, hshift] at r1 r2 r3 r4 hv' hu'
    have hl := F_log_shift hcpos (show 2 * c ≤ α * t by linarith)
    rw [abs_le] at r1 r2 r3 r4 hl
    have hC1 := le_abs_self C₁
    refine ⟨by linarith, hTt, ?_, ?_, ?_, ?_, ?_, hu', le_trans (le_max_left _ _) hv'⟩ <;>
      rw [abs_le] <;> constructor <;> linarith
  have hpart3 : ∀ t ≥ tstar / α, |s t 4 - ((N : ℝ) - 1) / N * log (α * t)| ≤ C ∧
      |s t 6 - ((N : ℝ) - 1) / N * log (α * t)| ≤ C ∧
      |s t 5 + log (α * t) / N| ≤ C ∧ |s t 7 + log (α * t) / N| ≤ C := by
    intro t ht
    obtain ⟨-, hTt, -, -, k3, k4, -⟩ := key t ht
    have hNr1 : (1 : ℝ) ≤ N := by linarith
    obtain ⟨q1, q2⟩ := F_recover (L := log (α * t)) hNr1 ((hg1 t (le_trans hT0pos hTt)).trans hA.symm)
    obtain ⟨q3, q4⟩ := F_recover (L := log (α * t)) hNr1 (hg2 t hTt)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  refine ⟨fun t ht => ?_, fun t ht => ?_, hpart3, fun t ht => ?_⟩
  · obtain ⟨-, -, k1, k2, k3, -⟩ := key t ht
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  · by_cases hts : tstar / α ≤ t
    · have := (key t hts).2.2.2.2.2.2.1; linarith
    · rw [not_le] at hts
      have hαt : α * t ≤ tstar := by rw [lt_div_iff₀ hα] at hts; linarith [mul_comm t α]
      have hαt0 : 0 ≤ α * t := mul_nonneg hα.le ht
      have hK' : (0 : ℝ) ≤ 2 * K + 2 := by positivity
      have b : ∀ m, |s t m - s 0 m| ≤ (2 * K + 2) * tstar := fun m =>
        le_trans (hlip 0 t le_rfl ht m) (F_lip_small hK' (F_P8_le hN2 m) hαt0 hαt)
      have b4 := b 4
      have b5 := b 5
      have b6 := b 6
      have b7 := b 7
      rw [e4] at b4; rw [e5] at b5; rw [e6] at b6; rw [e7] at b7
      rw [abs_le] at b4 b5 b6 b7 ⊢
      have := le_abs_self (c0 - c0')
      have := neg_abs_le (c0 - c0')
      constructor <;> linarith
  · intro E tgt root τ hE hτ
    obtain ⟨h1t, hTt, k1, -, k3, -, -, hu', hv'⟩ := key t ht
    obtain ⟨-, -, -, q4⟩ := hpart3 t ht
    have hT0t : 0 ≤ t := le_trans hT0pos hTt
    obtain ⟨-, r1, -, -, r4, r5, -, -⟩ := hreg t hT0t
    obtain ⟨b3, d7⟩ := hT0 t hTt
    have hgl := hgen (s t) b3 d7 (by linarith) (by linarith) hu' hv' r5.le E tgt root τ hE hτ
    rw [F_rpow (by omega) (by linarith : 0 < α * t)]
    set L := log (α * t) with hLdef
    have hL : 0 ≤ L := Real.log_nonneg h1t
    have hNpos : (0 : ℝ) < N := by linarith
    have hw0 : 0 ≤ L / N := div_nonneg hL hNpos.le
    rw [abs_le] at k1 k3 q4
    have E1 := F_exp_le (M := 3 * C) (L := L) (w := L / N) (x := s t 4 - s t 5 - s t 2)
      (by linarith)
    have E2 := F_exp_le (M := 3 * C) (L := L) (w := L / N) (x := -s t 2) (by linarith)
    have E3 := F_exp_le (M := 3 * C) (L := L) (w := L / N) (x := -(s t 4 - s t 5)) (by linarith)
    have E4 := F_exp_le (M := 3 * C) (L := L) (w := L / N) (x := -(s t 4 - s t 5 + s t 7))
      (by linarith)
    calc genLoss (iota (s t)) E tgt root τ
        ≤ Cg * (exp (s t 4 - s t 5 - s t 2) + exp (-s t 2) + exp (-(s t 4 - s t 5)) +
            exp (-(s t 4 - s t 5 + s t 7))) := hgl
      _ ≤ Cg * (4 * (exp (3 * C) * exp (-(L - L / N)))) := by
        apply mul_le_mul_of_nonneg_left _ hCg0; linarith
      _ = Cg * (4 * exp (3 * C)) * exp (-(L - L / N)) := by ring



end DFS
