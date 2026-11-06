import DFSLean.Defs

noncomputable section

namespace DFS

open Real Filter Topology Set

variable {N K : ℕ}

/-! ### Unfolding the components of `F` -/

lemma A_F0 (α θ η : ℝ) (z : Fin 4 → ℝ) : F N K α θ η z 0 =
    α / (N : ℝ) * ((exp (z 2) + (N : ℝ) - 2) / D1 N z
        + ∑ j ∈ Finset.range K,
            (exp (z 2) + (N : ℝ) - K - 1 + (j : ℝ) * E z * (1 - θ)) / D2 N K j z
        - (K : ℝ) * E z * θ / D4 N K z) := rfl

lemma A_F1 (α θ η : ℝ) (z : Fin 4 → ℝ) : F N K α θ η z 1 =
    α / ((N : ℝ) * ((N : ℝ) - 1)) *
       (∑ j ∈ Finset.range K, (j : ℝ) * E z * θ / D2 N K j z + (K : ℝ) * E z * θ / D4 N K z) :=
  rfl

lemma A_F2 (α θ η : ℝ) (z : Fin 4 → ℝ) : F N K α θ η z 2 =
    α / ((N : ℝ) - 1) * ((K : ℝ) * ((N : ℝ) - 1) / D3 N z
        + ((N : ℝ) - K - 1 + (K : ℝ) * E z * (1 - η)) / D4 N K z
        - exp (z 2) / D1 N z
        - ∑ j ∈ Finset.range K, ((j : ℝ) * E z * η + exp (z 2)) / D2 N K j z) := rfl

lemma A_F3 (α θ η : ℝ) (z : Fin 4 → ℝ) : F N K α θ η z 3 =
    α / ((N : ℝ) - 1) *
      (∑ j ∈ Finset.range K, (j : ℝ) * E z * η / D2 N K j z + (K : ℝ) * E z * η / D4 N K z) :=
  rfl

lemma A_F_smul (α θ η : ℝ) (z : Fin 4 → ℝ) : F N K α θ η z = α • F N K 1 θ η z := by
  funext i
  fin_cases i
  · simp only [Pi.smul_apply, smul_eq_mul]
    erw [A_F0, A_F0]; ring
  · simp only [Pi.smul_apply, smul_eq_mul]
    erw [A_F1, A_F1]; ring
  · simp only [Pi.smul_apply, smul_eq_mul]
    erw [A_F2, A_F2]; ring
  · simp only [Pi.smul_apply, smul_eq_mul]
    erw [A_F3, A_F3]; ring

/-! ### Elementary bounds -/

lemma A_E_pos (z : Fin 4 → ℝ) : 0 < E z := exp_pos _

lemma A_one_le_E (z : Fin 4 → ℝ) : 1 ≤ E z := by
  unfold E
  rw [← exp_zero]
  exact exp_le_exp.2 (add_nonneg (le_max_right _ _) (le_max_right _ _))

lemma A_frac {n d : ℝ} (hn : 0 ≤ n) (hnd : n ≤ d) : 0 ≤ n / d ∧ n / d ≤ 1 :=
  ⟨div_nonneg hn (hn.trans hnd), div_le_one_of_le₀ hnd (hn.trans hnd)⟩

lemma A_sum_frac {f : ℕ → ℝ} (h : ∀ j ∈ Finset.range K, 0 ≤ f j ∧ f j ≤ 1) :
    0 ≤ ∑ j ∈ Finset.range K, f j ∧ ∑ j ∈ Finset.range K, f j ≤ K := by
  refine ⟨Finset.sum_nonneg (fun j hj => (h j hj).1), ?_⟩
  have := Finset.sum_le_sum (fun j hj => (h j hj).2)
  simpa using this

lemma A_scale {α d X k : ℝ} (hα : 0 ≤ α) (hd : 1 ≤ d) (hX : |X| ≤ k + 1) :
    |α / d * X| ≤ (k + 2) * α := by
  rw [abs_mul, abs_of_nonneg (div_nonneg hα (by linarith))]
  calc α / d * |X| ≤ α * (k + 1) := mul_le_mul (div_le_self hα hd) hX (abs_nonneg _) hα
    _ ≤ (k + 2) * α := by nlinarith

theorem F_bound (hK : 2 ≤ K) (hN : K + 5 ≤ N) {α θ η : ℝ} (hα : 0 ≤ α)
    (hθ : θ ∈ Icc (0 : ℝ) 1) (hη : η ∈ Icc (0 : ℝ) 1) (z : Fin 4 → ℝ) (i : Fin 4) :
    |F N K α θ η z i| ≤ (K + 2) * α := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  obtain ⟨hη0, hη1⟩ := hη
  have hNK : (K : ℝ) + 5 ≤ N := by exact_mod_cast hN
  have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have ha := exp_pos (z 0)
  have hb := exp_pos (z 2)
  have he := A_E_pos z
  -- the fractions
  have hG : 0 ≤ (exp (z 2) + (N : ℝ) - 2) / D1 N z ∧ (exp (z 2) + (N : ℝ) - 2) / D1 N z ≤ 1 :=
    A_frac (by linarith) (by unfold D1; linarith)
  have hH : 0 ≤ exp (z 2) / D1 N z ∧ exp (z 2) / D1 N z ≤ 1 :=
    A_frac hb.le (by unfold D1; linarith)
  have hjK : ∀ j ∈ Finset.range K, (j : ℝ) ≤ K := fun j hj => by
    have := Finset.mem_range.1 hj; exact_mod_cast this.le
  have hC := A_sum_frac (K := K) (f := fun j =>
      (exp (z 2) + (N : ℝ) - K - 1 + (j : ℝ) * E z * (1 - θ)) / D2 N K j z) (fun j hj => by
    have h1 := hjK j hj
    have h2 : 0 ≤ (j : ℝ) * E z := mul_nonneg (Nat.cast_nonneg j) he.le
    have h3 : 0 ≤ ((K : ℝ) - j) * exp (z 0) := mul_nonneg (by linarith) ha.le
    have h4 : 0 ≤ (j : ℝ) * E z * θ := mul_nonneg h2 hθ0
    have h5 : 0 ≤ (j : ℝ) * E z * (1 - θ) := mul_nonneg h2 (by linarith)
    have h6 : (j : ℝ) * E z * (1 - θ) = (j : ℝ) * E z - (j : ℝ) * E z * θ := by ring
    exact A_frac (by linarith) (by unfold D2; linarith))
  have hA := A_sum_frac (K := K) (f := fun j => (j : ℝ) * E z * θ / D2 N K j z) (fun j hj => by
    have h1 := hjK j hj
    have h2 : 0 ≤ (j : ℝ) * E z := mul_nonneg (Nat.cast_nonneg j) he.le
    have h3 : 0 ≤ ((K : ℝ) - j) * exp (z 0) := mul_nonneg (by linarith) ha.le
    have h4 : 0 ≤ (j : ℝ) * E z * θ := mul_nonneg h2 hθ0
    have h5 : 0 ≤ (j : ℝ) * E z * (1 - θ) := mul_nonneg h2 (by linarith)
    have h6 : (j : ℝ) * E z * (1 - θ) = (j : ℝ) * E z - (j : ℝ) * E z * θ := by ring
    exact A_frac h4 (by unfold D2; linarith))
  have hA' := A_sum_frac (K := K) (f := fun j => (j : ℝ) * E z * η / D2 N K j z) (fun j hj => by
    have h1 := hjK j hj
    have h2 : 0 ≤ (j : ℝ) * E z := mul_nonneg (Nat.cast_nonneg j) he.le
    have h3 : 0 ≤ ((K : ℝ) - j) * exp (z 0) := mul_nonneg (by linarith) ha.le
    have h4 : 0 ≤ (j : ℝ) * E z * η := mul_nonneg h2 hη0
    have h5 : 0 ≤ (j : ℝ) * E z * (1 - η) := mul_nonneg h2 (by linarith)
    have h6 : (j : ℝ) * E z * (1 - η) = (j : ℝ) * E z - (j : ℝ) * E z * η := by ring
    exact A_frac h4 (by unfold D2; linarith))
  have hB := A_sum_frac (K := K) (f := fun j => ((j : ℝ) * E z * η + exp (z 2)) / D2 N K j z)
    (fun j hj => by
    have h1 := hjK j hj
    have h2 : 0 ≤ (j : ℝ) * E z := mul_nonneg (Nat.cast_nonneg j) he.le
    have h3 : 0 ≤ ((K : ℝ) - j) * exp (z 0) := mul_nonneg (by linarith) ha.le
    have h4 : 0 ≤ (j : ℝ) * E z * η := mul_nonneg h2 hη0
    have h5 : 0 ≤ (j : ℝ) * E z * (1 - η) := mul_nonneg h2 (by linarith)
    have h6 : (j : ℝ) * E z * (1 - η) = (j : ℝ) * E z - (j : ℝ) * E z * η := by ring
    exact A_frac (by linarith) (by unfold D2; linarith))
  have hKE : 0 ≤ (K : ℝ) * E z := mul_nonneg (Nat.cast_nonneg K) he.le
  have hQ : 0 ≤ (K : ℝ) * E z * θ / D4 N K z ∧ (K : ℝ) * E z * θ / D4 N K z ≤ 1 := by
    have h4 : 0 ≤ (K : ℝ) * E z * θ := mul_nonneg hKE hθ0
    have h5 : 0 ≤ (K : ℝ) * E z * (1 - θ) := mul_nonneg hKE (by linarith)
    have h6 : (K : ℝ) * E z * (1 - θ) = (K : ℝ) * E z - (K : ℝ) * E z * θ := by ring
    exact A_frac h4 (by unfold D4; linarith)
  have hQ' : 0 ≤ (K : ℝ) * E z * η / D4 N K z ∧ (K : ℝ) * E z * η / D4 N K z ≤ 1 := by
    have h4 : 0 ≤ (K : ℝ) * E z * η := mul_nonneg hKE hη0
    have h5 : 0 ≤ (K : ℝ) * E z * (1 - η) := mul_nonneg hKE (by linarith)
    have h6 : (K : ℝ) * E z * (1 - η) = (K : ℝ) * E z - (K : ℝ) * E z * η := by ring
    exact A_frac h4 (by unfold D4; linarith)
  have hR : 0 ≤ ((N : ℝ) - K - 1 + (K : ℝ) * E z * (1 - η)) / D4 N K z ∧
      ((N : ℝ) - K - 1 + (K : ℝ) * E z * (1 - η)) / D4 N K z ≤ 1 := by
    have h4 : 0 ≤ (K : ℝ) * E z * η := mul_nonneg hKE hη0
    have h5 : 0 ≤ (K : ℝ) * E z * (1 - η) := mul_nonneg hKE (by linarith)
    have h6 : (K : ℝ) * E z * (1 - η) = (K : ℝ) * E z - (K : ℝ) * E z * η := by ring
    exact A_frac (by linarith) (by unfold D4; linarith)
  have hM : 0 ≤ (K : ℝ) * ((N : ℝ) - 1) / D3 N z ∧ (K : ℝ) * ((N : ℝ) - 1) / D3 N z ≤ K := by
    have hD3 : 0 < D3 N z := by unfold D3; linarith
    refine ⟨div_nonneg (mul_nonneg (by linarith) (by linarith)) hD3.le, ?_⟩
    rw [div_le_iff₀ hD3]
    unfold D3
    nlinarith
  have hK0 : (0 : ℝ) ≤ K := by linarith
  fin_cases i
  · erw [A_F0]
    exact A_scale hα (by linarith) (abs_le.2 ⟨by linarith, by linarith⟩)
  · erw [A_F1]
    exact A_scale hα (by nlinarith) (abs_le.2 ⟨by linarith, by linarith⟩)
  · erw [A_F2]
    exact A_scale hα (by linarith) (abs_le.2 ⟨by linarith, by linarith⟩)
  · erw [A_F3]
    exact A_scale hα (by linarith) (abs_le.2 ⟨by linarith, by linarith⟩)



/-! ### Difference quotients of linear functionals -/

lemma A_lin_abs (c v : Fin 4 → ℝ) :
    |lin c v| ≤ (|c 0| + |c 1| + |c 2| + |c 3|) * ‖v‖ := by
  have h0 : |v 0| ≤ ‖v‖ := by simpa using norm_le_pi_norm v 0
  have h1 : |v 1| ≤ ‖v‖ := by simpa using norm_le_pi_norm v 1
  have h2 : |v 2| ≤ ‖v‖ := by simpa using norm_le_pi_norm v 2
  have h3 : |v 3| ≤ ‖v‖ := by simpa using norm_le_pi_norm v 3
  unfold lin
  calc |c 0 * v 0 + c 1 * v 1 + c 2 * v 2 + c 3 * v 3|
      ≤ |c 0 * v 0| + |c 1 * v 1| + |c 2 * v 2| + |c 3 * v 3| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ = |c 0| * |v 0| + |c 1| * |v 1| + |c 2| * |v 2| + |c 3| * |v 3| := by
        simp only [abs_mul]
    _ ≤ |c 0| * ‖v‖ + |c 1| * ‖v‖ + |c 2| * ‖v‖ + |c 3| * ‖v‖ := by gcongr
    _ = (|c 0| + |c 1| + |c 2| + |c 3|) * ‖v‖ := by ring

lemma A_lin_quot (c p q w : Fin 4 → ℝ) (h : ℝ) :
    (lin c p - lin c q) / h - lin c w = lin c (h⁻¹ • (p - q) - w) := by
  simp only [lin, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

theorem IsSol.slope_lin₂ {α : ℝ} {z : ℝ → Fin 4 → ℝ} (hz : IsSol N K α z) (c d : Fin 4 → ℝ)
    {t : ℝ} (ht : 0 ≤ t) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), ∃ θ η, Adm (z t) θ η ∧
      |(lin c (z (t + h)) - lin c (z t)) / h - lin c (F N K α θ η (z t))| < ε ∧
      |(lin d (z (t + h)) - lin d (z t)) / h - lin d (F N K α θ η (z t))| < ε := by
  set Sc := |c 0| + |c 1| + |c 2| + |c 3| with hSc
  set Sd := |d 0| + |d 1| + |d 2| + |d 3| with hSd
  have hSc0 : 0 ≤ Sc := by positivity
  have hSd0 : 0 ≤ Sd := by positivity
  have hD : 0 < 1 + Sc + Sd := by linarith
  filter_upwards [hz.2 t ht (ε / (1 + Sc + Sd)) (div_pos hε hD)] with h hh
  obtain ⟨w, ⟨θ, η, hadm, rfl⟩, hw⟩ := hh
  refine ⟨θ, η, hadm, ?_, ?_⟩
  · rw [A_lin_quot]
    calc _ ≤ Sc * ‖h⁻¹ • (z (t + h) - z t) - F N K α θ η (z t)‖ := A_lin_abs _ _
      _ ≤ Sc * (ε / (1 + Sc + Sd)) := mul_le_mul_of_nonneg_left hw.le hSc0
      _ < ε := by
        rw [← mul_div_assoc, div_lt_iff₀ hD]
        nlinarith
  · rw [A_lin_quot]
    calc _ ≤ Sd * ‖h⁻¹ • (z (t + h) - z t) - F N K α θ η (z t)‖ := A_lin_abs _ _
      _ ≤ Sd * (ε / (1 + Sc + Sd)) := mul_le_mul_of_nonneg_left hw.le hSd0
      _ < ε := by
        rw [← mul_div_assoc, div_lt_iff₀ hD]
        nlinarith



lemma A_tendsto_sub (x : ℝ) : Tendsto (fun y => y - x) (𝓝[>] x) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have := ((continuous_sub_right x).tendsto x)
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact sub_pos.2 (mem_Ioi.1 hy)

/-- Right slopes of `lin c ∘ z` at `x` are eventually close to an admissible velocity. -/
lemma A_slope_ev {α : ℝ} {z : ℝ → Fin 4 → ℝ} (hz : IsSol N K α z) (c : Fin 4 → ℝ)
    {x : ℝ} (hx : 0 ≤ x) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝[>] x, ∃ θ η, Adm (z x) θ η ∧
      |slope (fun t => lin c (z t)) x y - lin c (F N K α θ η (z x))| < ε := by
  filter_upwards [(A_tendsto_sub x).eventually (IsSol.slope_lin₂ hz c c hx hε)]
    with y ⟨θ, η, hadm, h1, _⟩
  refine ⟨θ, η, hadm, ?_⟩
  have e : x + (y - x) = y := by ring
  rw [e] at h1
  rwa [slope_def_field]

/-- Fencing lemma (variant of `image_le_of_liminf_slope_right_lt_deriv_boundary'` where the slope
estimate is only required at contact points `f x = B x`). -/
lemma A_fence {f B B' : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Icc a b)) (ha : f a ≤ B a)
    (hB : ContinuousOn B (Icc a b)) (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : ∀ x ∈ Ico a b, f x = B x → ∃ r < B' x, ∃ᶠ y in 𝓝[>] x, slope f x y < r) :
    ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x := by
  change Icc a b ⊆ { x | f x ≤ B x }
  set s := { x | f x ≤ B x } ∩ Icc a b
  have A : ContinuousOn (fun x => (f x, B x)) (Icc a b) := hf.prodMk hB
  have : IsClosed s := by
    simp only [s, inter_comm]
    exact A.preimage_isClosed_of_isClosed isClosed_Icc OrderClosedTopology.isClosed_le'
  apply this.Icc_subset_of_forall_exists_gt ha
  rintro x ⟨hxB : f x ≤ B x, xab⟩ y hy
  rcases hxB.lt_or_eq with hxB | hxB
  · refine nonempty_of_mem (inter_mem ?_ (Ioc_mem_nhdsGT hy))
    have : ∀ᶠ x in 𝓝[Icc a b] x, f x < B x :=
      A x (Ico_subset_Icc_self xab) (IsOpen.mem_nhds (isOpen_lt continuous_fst continuous_snd) hxB)
    have : ∀ᶠ x in 𝓝[>] x, f x < B x := nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem xab) this
    exact this.mono fun y => le_of_lt
  · obtain ⟨r, hrB, hf'⟩ := bound x xab hxB
    have HB : ∀ᶠ z in 𝓝[>] x, r < slope B x z :=
      (hasDerivWithinAt_iff_tendsto_slope' <| lt_irrefl x).1 (hB' x xab).Ioi_of_Ici
        (Ioi_mem_nhds hrB)
    obtain ⟨z, hfz, hzB, hz⟩ : ∃ z, slope f x z < r ∧ r < slope B x z ∧ z ∈ Ioc x y :=
      hf'.and_eventually (HB.and (Ioc_mem_nhdsGT hy)) |>.exists
    refine ⟨z, ?_, hz⟩
    have := (hfz.trans hzB).le
    rwa [slope_def_field, slope_def_field, div_le_div_iff_of_pos_right (sub_pos.2 hz.1), hxB,
      sub_le_sub_iff_right] at this

lemma A_continuousOn_lin {z : ℝ → Fin 4 → ℝ} {s : Set ℝ} (hz : ContinuousOn z s)
    (c : Fin 4 → ℝ) : ContinuousOn (fun t => lin c (z t)) s := by
  have hi : ∀ i, ContinuousOn (fun t => z t i) s := fun i =>
    (continuous_apply i).comp_continuousOn hz
  unfold lin
  exact ((((hi 0).const_smul (c 0)).add ((hi 1).const_smul (c 1))).add
    ((hi 2).const_smul (c 2))).add ((hi 3).const_smul (c 3))

/-- Comparison of `lin c ∘ z` with a right-differentiable barrier `B`. -/
lemma A_cmp {α : ℝ} {z : ℝ → Fin 4 → ℝ} (hz : IsSol N K α z) (c : Fin 4 → ℝ) {a b : ℝ}
    (ha : 0 ≤ a) {B B' : ℝ → ℝ} (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x) (hfa : lin c (z a) ≤ B a)
    (bound : ∀ x ∈ Ico a b, lin c (z x) = B x →
      ∃ r < B' x, ∀ θ η, Adm (z x) θ η → lin c (F N K α θ η (z x)) ≤ r) :
    ∀ x ∈ Icc a b, lin c (z x) ≤ B x := by
  intro x hx
  refine A_fence (f := fun t => lin c (z t)) ?_ hfa hB hB' ?_ hx
  · exact A_continuousOn_lin (hz.1.mono fun t (ht : t ∈ Icc a b) => show t ∈ Ici 0 from le_trans ha ht.1) c
  · intro x hx hfx
    obtain ⟨r, hr, hall⟩ := bound x hx hfx
    refine ⟨(r + B' x) / 2, by linarith, ?_⟩
    refine Eventually.frequently ?_
    filter_upwards [A_slope_ev hz c (ha.trans hx.1) (ε := (B' x - r) / 2) (by linarith)]
      with y ⟨θ, η, hadm, hy⟩
    have := hall θ η hadm
    have := (abs_lt.1 hy).2
    linarith

/-- Linear upper bound for `lin c ∘ z` from an upper bound on the admissible velocities. -/
lemma A_upper {α : ℝ} {z : ℝ → Fin 4 → ℝ} (hz : IsSol N K α z) (c : Fin 4 → ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (M : ℝ)
    (hM : ∀ t ∈ Ico a b, ∀ θ η, Adm (z t) θ η → lin c (F N K α θ η (z t)) ≤ M) :
    ∀ t ∈ Icc a b, lin c (z t) ≤ lin c (z a) + M * (t - a) := by
  intro t ht
  refine image_le_of_liminf_slope_right_le_deriv_boundary (f := fun t => lin c (z t))
    (B := fun t => lin c (z a) + M * (t - a)) (B' := fun _ => M) ?_ (by simp) (by fun_prop) ?_ ?_ ht
  · exact A_continuousOn_lin (hz.1.mono fun t (ht : t ∈ Icc a b) => show t ∈ Ici 0 from le_trans ha ht.1) c
  · intro x _
    have := ((hasDerivWithinAt_id x (Ici x)).sub_const a).const_mul M
    simpa using this.const_add (lin c (z a))
  · intro x hx r hr
    refine Eventually.frequently ?_
    filter_upwards [A_slope_ev hz c (ha.trans hx.1) (ε := r - M) (by linarith)]
      with y ⟨θ, η, hadm, hy⟩
    have := hM x hx θ η hadm
    have := (abs_lt.1 hy).2
    linarith

theorem IsSol.barrier {α : ℝ} {z : ℝ → Fin 4 → ℝ} (hz : IsSol N K α z) (c : Fin 4 → ℝ) (L : ℝ)
    {a b : ℝ} (ha : 0 ≤ a)
    (h : ∀ t ∈ Ico a b, L < lin c (z t) →
      ∀ θ η, Adm (z t) θ η → lin c (F N K α θ η (z t)) ≤ 0) :
    ∀ t ∈ Icc a b, lin c (z t) ≤ max (lin c (z a)) L := by
  intro t ht
  set m := max (lin c (z a)) L
  have key : ∀ ε > 0, lin c (z t) ≤ m + ε * (1 + (t - a)) := by
    intro ε hε
    refine A_cmp hz c ha (B := fun x => m + ε * (1 + (x - a))) (B' := fun _ => ε)
      (by fun_prop) ?_ ?_ ?_ t ht
    · intro x _
      have := (((hasDerivWithinAt_id x (Ici x)).sub_const a).const_add 1).const_mul ε
      simpa using this.const_add m
    · simp only [sub_self, add_zero, mul_one]
      linarith [le_max_left (lin c (z a)) L]
    · intro x hx hfx
      refine ⟨0, hε, h x hx ?_⟩
      rw [hfx]
      have : 0 ≤ ε * (1 + (x - a)) := mul_nonneg hε.le (by linarith [hx.1])
      have : 0 < ε * (1 + (x - a)) := mul_pos hε (by linarith [hx.1])
      linarith [le_max_right (lin c (z a)) L]
  have hta : 0 ≤ t - a := by linarith [ht.1]
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have h1 : 0 < 1 + (t - a) := by linarith
  have := key (δ / (1 + (t - a))) (div_pos hδ h1)
  rwa [div_mul_cancel₀ _ h1.ne'] at this



lemma A_lin_neg (c w : Fin 4 → ℝ) : lin (-c) w = -lin c w := by
  simp only [lin, Pi.neg_apply]; ring

lemma A_lin_single (i : Fin 4) (w : Fin 4 → ℝ) : lin (Pi.single i 1) w = w i := by
  fin_cases i <;> simp [lin]

theorem IsSol.reach {α : ℝ} {z : ℝ → Fin 4 → ℝ} (hz : IsSol N K α z) (c : Fin 4 → ℝ)
    (L δ : ℝ) (hδ : 0 < δ) {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ t ≥ a, lin c (z t) < L →
      ∀ θ η, Adm (z t) θ η → δ ≤ lin c (F N K α θ η (z t))) :
    ∀ t ≥ a, a + (L - lin c (z a)) / δ ≤ t → L ≤ lin c (z t) := by
  intro t hta htt
  by_contra hlt
  replace hlt := lt_of_not_ge hlt
  by_cases hex : ∃ s ∈ Icc a t, L ≤ lin c (z s)
  · obtain ⟨s, hs, hLs⟩ := hex
    have key := DFS.IsSol.barrier hz (-c) (-L) (a := s) (b := t) (ha.trans hs.1)
      (fun t' ht' hlt' θ η hadm => by
        rw [A_lin_neg] at hlt' ⊢
        have := h t' (hs.1.trans ht'.1) (by linarith) θ η hadm
        linarith) t ⟨hs.2, le_rfl⟩
    rw [A_lin_neg, A_lin_neg, max_eq_right (by linarith)] at key
    linarith
  · replace hex : ∀ s ∈ Icc a t, lin c (z s) < L := fun s hs =>
      lt_of_not_ge fun h' => hex ⟨s, hs, h'⟩
    have key := A_upper hz (-c) ha (-δ) (b := t)
      (fun t' ht' θ η hadm => by
        rw [A_lin_neg]
        have := h t' ht'.1 (hex t' ⟨ht'.1, ht'.2.le⟩) θ η hadm
        linarith) t ⟨hta, le_rfl⟩
    rw [A_lin_neg, A_lin_neg] at key
    have h2 : (L - lin c (z a)) / δ ≤ t - a := by linarith
    rw [div_le_iff₀ hδ] at h2
    nlinarith



theorem IsSol.lipschitz (hK : 2 ≤ K) (hN : K + 5 ≤ N) {α : ℝ} (hα : 0 ≤ α)
    {z : ℝ → Fin 4 → ℝ} (hz : IsSol N K α z) (i : Fin 4) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    |z t i - z s i| ≤ (K + 2) * α * (t - s) := by
  have h1 := A_upper hz (Pi.single i 1) hs ((K + 2) * α) (b := t)
    (fun t' _ θ η hadm => by
      rw [A_lin_single]
      exact (le_abs_self _).trans (F_bound hK hN hα hadm.1 hadm.2.1 _ i)) t ⟨hst, le_rfl⟩
  have h2 := A_upper hz (-Pi.single i 1) hs ((K + 2) * α) (b := t)
    (fun t' _ θ η hadm => by
      rw [A_lin_neg, A_lin_single]
      exact (neg_le_abs _).trans (F_bound hK hN hα hadm.1 hadm.2.1 _ i)) t ⟨hst, le_rfl⟩
  rw [A_lin_single, A_lin_single] at h1
  rw [A_lin_neg, A_lin_neg, A_lin_single, A_lin_single] at h2
  rw [abs_le]
  constructor <;> linarith



theorem IsSol.rescale {α : ℝ} (hα : 0 < α) {z : ℝ → Fin 4 → ℝ} (hz : IsSol N K α z) :
    IsSol N K 1 (fun s => z (s / α)) := by
  refine ⟨?_, ?_⟩
  · exact hz.1.comp (continuousOn_id.div_const α)
      (fun s (hs : s ∈ Ici 0) => show s / α ∈ Ici 0 from div_nonneg hs hα.le)
  · intro t ht ε hε
    have hT : Tendsto (fun h => h / α) (𝓝[>] (0 : ℝ)) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have := (continuous_id.div_const α).tendsto (0 : ℝ)
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with h hh
        exact div_pos (mem_Ioi.1 hh) hα
    filter_upwards [hT.eventually
      (hz.2 (t / α) (div_nonneg ht hα.le) (α * ε) (mul_pos hα hε))] with h hh
    obtain ⟨w, ⟨θ, η, hadm, rfl⟩, hw⟩ := hh
    refine ⟨F N K 1 θ η (z (t / α)), ⟨θ, η, hadm, rfl⟩, ?_⟩
    have e1 : (t + h) / α = t / α + h / α := add_div t h α
    have e3 : α⁻¹ * (h / α)⁻¹ = h⁻¹ := by
      rw [inv_div, div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hα.ne', one_mul]
    have e2 : h⁻¹ • (z ((t + h) / α) - z (t / α)) - F N K 1 θ η (z (t / α)) =
        α⁻¹ • ((h / α)⁻¹ • (z (t / α + h / α) - z (t / α)) - F N K α θ η (z (t / α))) := by
      rw [e1, A_F_smul α, smul_sub α⁻¹, smul_smul, smul_smul, inv_mul_cancel₀ hα.ne', one_smul, e3]
    show ‖h⁻¹ • (z ((t + h) / α) - z (t / α)) - F N K 1 θ η (z (t / α))‖ < ε
    rw [e2, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hα]
    calc α⁻¹ * ‖(h / α)⁻¹ • (z (t / α + h / α) - z (t / α)) - F N K α θ η (z (t / α))‖
        < α⁻¹ * (α * ε) := mul_lt_mul_of_pos_left hw (inv_pos.2 hα)
      _ = ε := by field_simp



/-! ### Positivity of denominators and signs of components -/

lemma A_D1_pos (hN : K + 5 ≤ N) (z : Fin 4 → ℝ) : 0 < D1 N z := by
  have hNK : (K : ℝ) + 5 ≤ N := by exact_mod_cast hN
  unfold D1
  linarith [exp_pos (z 0), exp_pos (z 2), (Nat.cast_nonneg K : (0 : ℝ) ≤ K)]

lemma A_D2_pos (hN : K + 5 ≤ N) {j : ℕ} (hj : j < K) (z : Fin 4 → ℝ) : 0 < D2 N K j z := by
  have hNK : (K : ℝ) + 5 ≤ N := by exact_mod_cast hN
  have hjK : (j : ℝ) < K := by exact_mod_cast hj
  unfold D2
  have h1 : 0 ≤ ((K : ℝ) - j) * exp (z 0) := mul_nonneg (by linarith) (exp_pos _).le
  have h2 : 0 ≤ (j : ℝ) * E z := mul_nonneg (Nat.cast_nonneg j) (A_E_pos z).le
  linarith [exp_pos (z 2)]

lemma A_D3_pos (hN : K + 5 ≤ N) (z : Fin 4 → ℝ) : 0 < D3 N z := by
  have hNK : (K : ℝ) + 5 ≤ N := by exact_mod_cast hN
  unfold D3
  linarith [exp_pos (z 2), (Nat.cast_nonneg K : (0 : ℝ) ≤ K)]

lemma A_D4_pos (hN : K + 5 ≤ N) (z : Fin 4 → ℝ) : 0 < D4 N K z := by
  have hNK : (K : ℝ) + 5 ≤ N := by exact_mod_cast hN
  unfold D4
  have h2 : 0 ≤ (K : ℝ) * E z := mul_nonneg (Nat.cast_nonneg K) (A_E_pos z).le
  linarith [exp_pos (z 2)]

lemma A_F1_nonneg (hN : K + 5 ≤ N) {α θ : ℝ} (hα : 0 ≤ α) (hθ : 0 ≤ θ) (η : ℝ)
    (z : Fin 4 → ℝ) : 0 ≤ F N K α θ η z 1 := by
  have hNK : (K : ℝ) + 5 ≤ N := by exact_mod_cast hN
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  rw [A_F1]
  refine mul_nonneg (div_nonneg hα (mul_nonneg (by linarith) (by linarith))) (add_nonneg ?_ ?_)
  · refine Finset.sum_nonneg fun j hj => div_nonneg ?_ (A_D2_pos hN (Finset.mem_range.1 hj) z).le
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg j) (A_E_pos z).le) hθ
  · exact div_nonneg (mul_nonneg (mul_nonneg hK0 (A_E_pos z).le) hθ) (A_D4_pos hN z).le

lemma A_F3_nonneg (hN : K + 5 ≤ N) {α η : ℝ} (hα : 0 ≤ α) (hη : 0 ≤ η) (θ : ℝ)
    (z : Fin 4 → ℝ) : 0 ≤ F N K α θ η z 3 := by
  have hNK : (K : ℝ) + 5 ≤ N := by exact_mod_cast hN
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  rw [A_F3]
  refine mul_nonneg (div_nonneg hα (by linarith)) (add_nonneg ?_ ?_)
  · refine Finset.sum_nonneg fun j hj => div_nonneg ?_ (A_D2_pos hN (Finset.mem_range.1 hj) z).le
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg j) (A_E_pos z).le) hη
  · exact div_nonneg (mul_nonneg (mul_nonneg hK0 (A_E_pos z).le) hη) (A_D4_pos hN z).le

theorem IsSol.mono_x2 (hK : 2 ≤ K) (hN : K + 5 ≤ N) {z : ℝ → Fin 4 → ℝ} (hz : IsSol N K 1 z)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : z s 1 ≤ z t 1 := by
  have key := DFS.IsSol.barrier hz ![0, -1, 0, 0] (-z s 1) (a := s) (b := t) hs
    (fun t' _ _ θ η hadm => by
      have := A_F1_nonneg hN zero_le_one hadm.1.1 η (z t')
      simp [lin]
      linarith) t ⟨hst, le_rfl⟩
  simp [lin] at key
  linarith



theorem IsSol.mono_y2 (hK : 2 ≤ K) (hN : K + 5 ≤ N) {z : ℝ → Fin 4 → ℝ} (hz : IsSol N K 1 z)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : z s 3 ≤ z t 3 := by
  have key := DFS.IsSol.barrier hz ![0, 0, 0, -1] (-z s 3) (a := s) (b := t) hs
    (fun t' _ _ θ η hadm => by
      have := A_F3_nonneg hN zero_le_one hadm.2.1.1 θ (z t')
      simp [lin]
      linarith) t ⟨hst, le_rfl⟩
  simp [lin] at key
  linarith



/-- With `θ = 0`, `x₁' > 0` (the `G` term is positive, all other terms are nonnegative). -/
lemma A_F0_pos (hN : K + 5 ≤ N) {α : ℝ} (hα : 0 < α) (η : ℝ) (z : Fin 4 → ℝ) :
    0 < F N K α 0 η z 0 := by
  have hNK : (K : ℝ) + 5 ≤ N := by exact_mod_cast hN
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  rw [A_F0]
  have hG : 0 < (exp (z 2) + (N : ℝ) - 2) / D1 N z :=
    div_pos (by linarith [exp_pos (z 2)]) (A_D1_pos hN z)
  have hS : 0 ≤ ∑ j ∈ Finset.range K,
      (exp (z 2) + (N : ℝ) - K - 1 + (j : ℝ) * E z * (1 - 0)) / D2 N K j z := by
    refine Finset.sum_nonneg fun j hj => div_nonneg ?_ (A_D2_pos hN (Finset.mem_range.1 hj) z).le
    have : 0 ≤ (j : ℝ) * E z * (1 - 0) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg j) (A_E_pos z).le) (by norm_num)
    linarith [exp_pos (z 2)]
  have hQ : (K : ℝ) * E z * 0 / D4 N K z = 0 := by simp
  rw [hQ]
  exact mul_pos (div_pos hα (by linarith)) (by linarith)

/-- On `{x₁ ≥ 0, y₁ < 0}` with `η = 0`, `y₁' > 0`. -/
lemma A_F2_pos (hK : 2 ≤ K) (hN : K + 5 ≤ N) {α : ℝ} (hα : 0 < α) (θ : ℝ) (w : Fin 4 → ℝ)
    (hx1 : 0 ≤ w 0) (hy1 : w 2 < 0) : 0 < F N K α θ 0 w 2 := by
  have hNK : (K : ℝ) + 5 ≤ N := by exact_mod_cast hN
  have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have ha : 1 ≤ exp (w 0) := one_le_exp hx1
  have hb0 := exp_pos (w 2)
  have hb1 : exp (w 2) < 1 := exp_lt_one_iff.2 hy1
  have he := A_E_pos w
  rw [A_F2]
  have hD3 := A_D3_pos hN w
  have hD1 := A_D1_pos hN w
  have hT1 : (K : ℝ) / 2 ≤ (K : ℝ) * ((N : ℝ) - 1) / D3 N w := by
    rw [le_div_iff₀ hD3]
    unfold D3
    nlinarith
  have hT2 : 0 ≤ ((N : ℝ) - K - 1 + (K : ℝ) * E w * (1 - 0)) / D4 N K w := by
    refine div_nonneg ?_ (A_D4_pos hN w).le
    have : 0 ≤ (K : ℝ) * E w * (1 - 0) :=
      mul_nonneg (mul_nonneg (by linarith) he.le) (by norm_num)
    linarith
  have hT3 : exp (w 2) / D1 N w ≤ 1 / 6 := by
    rw [div_le_iff₀ hD1]
    unfold D1
    linarith
  have hT4 : ∑ j ∈ Finset.range K, ((j : ℝ) * E w * 0 + exp (w 2)) / D2 N K j w ≤ K * (1 / 6) := by
    have := Finset.sum_le_sum (s := Finset.range K)
      (f := fun (j : ℕ) => ((j : ℝ) * E w * 0 + exp (w 2)) / D2 N K j w)
      (g := fun (_ : ℕ) => (1 / 6 : ℝ))
      (fun j hj => by
        have hjK : (j : ℝ) + 1 ≤ K := by exact_mod_cast Finset.mem_range.1 hj
        rw [div_le_iff₀ (A_D2_pos hN (Finset.mem_range.1 hj) w)]
        unfold D2
        have h1 : 1 ≤ ((K : ℝ) - j) * exp (w 0) := by nlinarith
        have h2 : 0 ≤ (j : ℝ) * E w := mul_nonneg (Nat.cast_nonneg j) he.le
        simp only [mul_zero, zero_add]
        linarith)
    simpa using this
  refine mul_pos (div_pos hα (by linarith)) ?_
  linarith

/-- `u ≥ 0` persists. -/
lemma A_u_nonneg (hN : K + 5 ≤ N) {z : ℝ → Fin 4 → ℝ} (hz : IsSol N K 1 z)
    (h0 : 0 ≤ u (z 0)) : ∀ t ≥ 0, 0 ≤ u (z t) := by
  intro t ht
  have e : ∀ w, lin ![-1, 1, 0, 0] w = -u w := by intro w; simp [lin, u]; ring
  have key := DFS.IsSol.barrier hz ![-1, 1, 0, 0] 0 (a := 0) (b := t) le_rfl
    (fun t' _ hlt θ η hadm => by
      rw [e] at hlt
      have hθ : θ = 0 := hadm.2.2.2.1 (by linarith)
      subst hθ
      have h1 : F N K 1 0 η (z t') 1 = 0 := by rw [A_F1]; simp
      have h2 := A_F0_pos hN one_pos η (z t')
      simp [lin]
      linarith) t ⟨ht, le_rfl⟩
  rw [e, e, max_eq_right (by linarith)] at key
  linarith

/-- `y₁ ≥ 0` persists (given the other three invariants). -/
lemma A_y1_nonneg (hK : 2 ≤ K) (hN : K + 5 ≤ N) {z : ℝ → Fin 4 → ℝ} (hz : IsSol N K 1 z)
    (h0 : Good (z 0)) : ∀ t ≥ 0, 0 ≤ z t 2 := by
  intro t ht
  have e : ∀ w, lin ![0, 0, -1, 0] w = -w 2 := by intro w; simp [lin]
  have key := DFS.IsSol.barrier hz ![0, 0, -1, 0] 0 (a := 0) (b := t) le_rfl
    (fun t' ht' hlt θ η hadm => by
      rw [e] at hlt
      have hu := A_u_nonneg hN hz h0.1 t' ht'.1
      have hx2 := (DFS.IsSol.mono_x2 hK hN hz le_rfl ht'.1)
      have hy2 := (DFS.IsSol.mono_y2 hK hN hz le_rfl ht'.1)
      have g1 := h0.2.1
      have g3 := h0.2.2.2
      unfold u at hu
      have hη : η = 0 := hadm.2.2.2.2.2 (by unfold v; linarith)
      subst hη
      have := A_F2_pos hK hN one_pos θ (z t') (by linarith) (by linarith)
      rw [e]
      linarith) t ⟨ht, le_rfl⟩
  rw [e, e, max_eq_right (by linarith [h0.2.2.1])] at key
  linarith

theorem IsSol.good (hK : 2 ≤ K) (hN : K + 5 ≤ N) {z : ℝ → Fin 4 → ℝ} (hz : IsSol N K 1 z)
    (h0 : Good (z 0)) : ∀ t ≥ 0, Good (z t) := by
  intro t ht
  exact ⟨A_u_nonneg hN hz h0.1 t ht,
    h0.2.1.trans (DFS.IsSol.mono_x2 hK hN hz le_rfl ht),
    A_y1_nonneg hK hN hz h0 t ht,
    h0.2.2.2.trans (DFS.IsSol.mono_y2 hK hN hz le_rfl ht)⟩



end DFS
