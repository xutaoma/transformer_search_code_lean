import DFSLean.Model

/-!
# E1. Existence of solutions of differential inclusions (measure-free Filippov theorem)

Proof (no measure theory, no Arzelà–Ascoli):
* Euler sequences `y_{k+1} = y_k + τ • c (y_k)` with a selection `c y ∈ V y`, step `τ_m = 1/(m+1)`;
  the piecewise-constant interpolants `zₘ t = y_{⌊t/τ_m⌋}` satisfy `‖zₘ t - x0‖ ≤ M |t|`.
* Along an ultrafilter `U ≤ atTop` on `ℕ`, each bounded sequence `m ↦ zₘ t` converges (closed balls
  are compact); call the limit `z t`.
* `‖zₘ t - zₘ s‖ ≤ M (t - s + τ_m)`, so `z` is `M`-Lipschitz on `[0, ∞)`.
* `zₘ(t+h) - zₘ t` is `τ_m (j - i)` times the average of the Euler velocities `c (y_k)`,
  `i ≤ k < j`; by upper semicontinuity these lie in the closed convex set
  `cthickening (ε/2) (V (z t))` once `h` is small and `m` is large, hence so does the limit
  quotient `h⁻¹ • (z (t+h) - z t)`.
-/

noncomputable section
open Real Finset Filter Topology Set

namespace DFS

variable {N K : ℕ}

/-- Euler sequence with step `τ` and velocity selection `c`, started at `x0`. -/
def E1_eul {E : Type*} [AddCommGroup E] [Module ℝ E] (c : E → E) (x0 : E) (τ : ℝ) : ℕ → E
  | 0 => x0
  | k + 1 => E1_eul c x0 τ k + τ • c (E1_eul c x0 τ k)

section eul
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : E → E) (x0 : E) (τ : ℝ)

lemma E1_eul_sub {i j : ℕ} (hij : i ≤ j) :
    E1_eul c x0 τ j - E1_eul c x0 τ i = τ • ∑ k ∈ Finset.Ico i j, c (E1_eul c x0 τ k) := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    rw [Finset.sum_Ico_succ_top hij, smul_add, ← ih]
    simp only [E1_eul]
    abel

lemma E1_eul_norm_sub {M : ℝ} (hτ : 0 ≤ τ) (hc : ∀ x, ‖c x‖ ≤ M) {i j : ℕ} (hij : i ≤ j) :
    ‖E1_eul c x0 τ j - E1_eul c x0 τ i‖ ≤ τ * (M * ((j : ℝ) - i)) := by
  rw [E1_eul_sub c x0 τ hij, norm_smul, Real.norm_of_nonneg hτ]
  gcongr
  calc ‖∑ k ∈ Finset.Ico i j, c (E1_eul c x0 τ k)‖ ≤ ∑ k ∈ Finset.Ico i j, ‖c (E1_eul c x0 τ k)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.Ico i j, M := Finset.sum_le_sum fun k _ => hc _
    _ = M * ((j : ℝ) - i) := by
      rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hij]; ring

lemma E1_avg_mem {S : Set E} (hS : Convex ℝ S) (hτ : 0 < τ) {i j : ℕ} (hij : i < j)
    (hmem : ∀ k ∈ Finset.Ico i j, c (E1_eul c x0 τ k) ∈ S) :
    (τ * ((j : ℝ) - i))⁻¹ • (E1_eul c x0 τ j - E1_eul c x0 τ i) ∈ S := by
  have hji : (0 : ℝ) < (j : ℝ) - i := by
    have : (i : ℝ) < j := by exact_mod_cast hij
    linarith
  rw [E1_eul_sub c x0 τ hij.le, smul_smul, Finset.smul_sum]
  refine hS.sum_mem (fun k _ => ?_) ?_ hmem
  · exact mul_nonneg (inv_nonneg.2 (mul_nonneg hτ.le hji.le)) hτ.le
  · rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hij.le]
    field_simp

end eul

lemma E1_floor_bounds {s : ℝ} (hs : 0 ≤ s) (m : ℕ) :
    s - 1 / ((m : ℝ) + 1) < 1 / ((m : ℝ) + 1) * ⌊s * ((m : ℝ) + 1)⌋₊ ∧
    1 / ((m : ℝ) + 1) * ⌊s * ((m : ℝ) + 1)⌋₊ ≤ s := by
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have h1 := Nat.floor_le (mul_nonneg hs hm.le)
  have h2 := Nat.lt_floor_add_one (s * ((m : ℝ) + 1))
  constructor
  · rw [div_mul_eq_mul_div, one_mul, lt_div_iff₀ hm, sub_mul, div_mul_cancel₀ _ hm.ne']
    linarith
  · rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hm]
    linarith

lemma E1_tendsto_floor {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1) * ⌊s * ((m : ℝ) + 1)⌋₊) atTop (𝓝 s) := by
  have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hlow : Tendsto (fun m : ℕ => s - 1 / ((m : ℝ) + 1)) atTop (𝓝 s) := by
    simpa using (tendsto_const_nhds (x := s)).sub h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    (fun m => (E1_floor_bounds hs m).1.le) (fun m => (E1_floor_bounds hs m).2)

theorem exists_IsDI {n : ℕ} (V : (Fin n → ℝ) → Set (Fin n → ℝ)) (M : ℝ)
    (hne : ∀ x, (V x).Nonempty) (hconv : ∀ x, Convex ℝ (V x)) (hclosed : ∀ x, IsClosed (V x))
    (hbdd : ∀ x, ∀ w ∈ V x, ‖w‖ ≤ M)
    (husc : ∀ x, ∀ ε > 0, ∃ δ > 0, ∀ y, ‖y - x‖ < δ → ∀ w ∈ V y, ∃ w' ∈ V x, ‖w - w'‖ < ε)
    (x0 : Fin n → ℝ) : ∃ z : ℝ → Fin n → ℝ, IsDI V z ∧ z 0 = x0 := by
  classical
  have hM : 0 ≤ M := (norm_nonneg _).trans (hbdd x0 _ (hne x0).some_mem)
  obtain ⟨c, hc⟩ : ∃ c : (Fin n → ℝ) → (Fin n → ℝ), ∀ x, c x ∈ V x :=
    ⟨fun x => (hne x).some, fun x => (hne x).some_mem⟩
  have hcM : ∀ x, ‖c x‖ ≤ M := fun x => hbdd x _ (hc x)
  obtain ⟨τ, hτ⟩ : ∃ τ : ℕ → ℝ, ∀ m, τ m = 1 / ((m : ℝ) + 1) := ⟨_, fun _ => rfl⟩
  obtain ⟨idx, hidx⟩ : ∃ idx : ℕ → ℝ → ℕ, ∀ m s, idx m s = ⌊s * ((m : ℝ) + 1)⌋₊ :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨zs, hzs⟩ : ∃ zs : ℕ → ℝ → (Fin n → ℝ), ∀ m s, zs m s = E1_eul c x0 (τ m) (idx m s) :=
    ⟨_, fun _ _ => rfl⟩
  have hτpos : ∀ m, 0 < τ m := fun m => by rw [hτ]; positivity
  have hτ0 : Tendsto τ atTop (𝓝 0) := by
    rw [show τ = fun m : ℕ => 1 / ((m : ℝ) + 1) from funext hτ]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hfl : ∀ m s, 0 ≤ s → s - τ m < τ m * idx m s ∧ τ m * idx m s ≤ s := by
    intro m s hs; rw [hτ, hidx]; exact E1_floor_bounds hs m
  have hfloorT : ∀ s, 0 ≤ s → Tendsto (fun m => τ m * (idx m s : ℝ)) atTop (𝓝 s) := by
    intro s hs
    have : (fun m => τ m * (idx m s : ℝ)) =
        fun m : ℕ => 1 / ((m : ℝ) + 1) * ⌊s * ((m : ℝ) + 1)⌋₊ := by
      funext m; rw [hτ, hidx]
    rw [this]; exact E1_tendsto_floor hs
  set U : Ultrafilter ℕ := Ultrafilter.of (atTop : Filter ℕ) with hU_def
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  have hτ0U : Tendsto τ (U : Filter ℕ) (𝓝 0) := hτ0.mono_left hU
  -- pointwise bound
  have hbound : ∀ m t, zs m t ∈ Metric.closedBall x0 (M * |t|) := by
    intro m t
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h := E1_eul_norm_sub c x0 (τ m) (hτpos m).le hcM (Nat.zero_le (idx m t))
    have hidx' : τ m * (idx m t : ℝ) ≤ |t| := by
      have h1 : (idx m t : ℝ) ≤ |t| * ((m : ℝ) + 1) := by
        rw [hidx]
        calc (⌊t * ((m : ℝ) + 1)⌋₊ : ℝ) ≤ ⌊|t| * ((m : ℝ) + 1)⌋₊ := by
              exact_mod_cast Nat.floor_mono
                (mul_le_mul_of_nonneg_right (le_abs_self t) (by positivity))
          _ ≤ |t| * ((m : ℝ) + 1) := Nat.floor_le (by positivity)
      rw [hτ, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
      exact h1
    simp only [E1_eul, Nat.cast_zero, sub_zero] at h
    rw [hzs]
    calc ‖E1_eul c x0 (τ m) (idx m t) - x0‖ ≤ τ m * (M * idx m t) := h
      _ = M * (τ m * idx m t) := by ring
      _ ≤ M * |t| := mul_le_mul_of_nonneg_left hidx' hM
  -- pointwise limits along the ultrafilter
  have hlim : ∀ t, ∃ x, Tendsto (fun m => zs m t) (U : Filter ℕ) (𝓝 x) := by
    intro t
    obtain ⟨x, -, hx⟩ := (isCompact_closedBall x0 (M * |t|)).ultrafilter_le_nhds
      (U.map (fun m => zs m t)) (by
        rw [Ultrafilter.coe_map, le_principal_iff]
        exact Filter.mem_map.2 (Filter.univ_mem' (fun m => hbound m t)))
    exact ⟨x, by rwa [Ultrafilter.coe_map] at hx⟩
  choose z hz using hlim
  -- initial value
  have hz0 : z 0 = x0 := by
    have h0 := hz 0
    have : (fun m => zs m 0) = fun _ => x0 := by
      funext m; rw [hzs, hidx]; simp [E1_eul]
    rw [this] at h0
    exact tendsto_nhds_unique h0 tendsto_const_nhds
  -- Lipschitz bound
  have hlip : ∀ s t, 0 ≤ s → s ≤ t → ‖z t - z s‖ ≤ M * (t - s) := by
    intro s t hs hst
    have h1 : Tendsto (fun m => ‖zs m t - zs m s‖) (U : Filter ℕ) (𝓝 ‖z t - z s‖) :=
      ((hz t).sub (hz s)).norm
    have h2 : Tendsto (fun m => M * (t - s + τ m)) (U : Filter ℕ) (𝓝 (M * (t - s))) := by
      simpa using (tendsto_const_nhds.add hτ0U).const_mul M
    refine le_of_tendsto_of_tendsto' h1 h2 (fun m => ?_)
    have hle : idx m s ≤ idx m t := by
      rw [hidx, hidx]
      exact Nat.floor_mono (mul_le_mul_of_nonneg_right hst (by positivity))
    have hb := E1_eul_norm_sub c x0 (τ m) (hτpos m).le hcM hle
    have fs := hfl m s hs
    have ft := hfl m t (hs.trans hst)
    rw [hzs, hzs]
    calc ‖E1_eul c x0 (τ m) (idx m t) - E1_eul c x0 (τ m) (idx m s)‖
        ≤ τ m * (M * ((idx m t : ℝ) - idx m s)) := hb
      _ = M * (τ m * idx m t - τ m * idx m s) := by ring
      _ ≤ M * (t - s + τ m) := mul_le_mul_of_nonneg_left (by linarith) hM
  have hcont : ContinuousOn z (Ici 0) := by
    have : LipschitzOnWith (Real.toNNReal M) z (Ici 0) := by
      refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
      rw [Real.coe_toNNReal _ hM, dist_eq_norm, dist_eq_norm, Real.norm_eq_abs]
      rcases le_total x y with hxy | hxy
      · rw [norm_sub_rev, abs_of_nonpos (by linarith), neg_sub]
        exact hlip x y hx hxy
      · rw [abs_of_nonneg (by linarith)]
        exact hlip y x hy hxy
    exact this.continuousOn
  refine ⟨z, ⟨hcont, ?_⟩, hz0⟩
  -- the difference-quotient condition
  intro t ht ε hε
  obtain ⟨δ, hδ, hδV⟩ := husc (z t) (ε / 2) (by positivity)
  set S := Metric.cthickening (ε / 2) (V (z t)) with hS_def
  have hSconv : Convex ℝ S := (hconv _).cthickening _
  have hSclosed : IsClosed S := Metric.isClosed_cthickening
  have hh0 : 0 < δ / (3 * (M + 1)) := by positivity
  filter_upwards [Ioo_mem_nhdsGT hh0] with h hh
  obtain ⟨hhpos, hhlt⟩ := hh
  have hMh : M * h < δ / 3 := by
    rw [lt_div_iff₀ (by positivity)] at hhlt
    nlinarith
  have hdiff : Tendsto (fun m => τ m * ((idx m (t + h) : ℝ) - idx m t)) (U : Filter ℕ) (𝓝 h) := by
    have h1 := ((hfloorT (t + h) (by linarith)).sub (hfloorT t ht)).mono_left hU
    rw [add_sub_cancel_left] at h1
    exact h1.congr (fun m => by ring)
  have hq : Tendsto (fun m => (τ m * ((idx m (t + h) : ℝ) - idx m t))⁻¹ • (zs m (t + h) - zs m t))
      (U : Filter ℕ) (𝓝 (h⁻¹ • (z (t + h) - z t))) :=
    (hdiff.inv₀ hhpos.ne').smul ((hz (t + h)).sub (hz t))
  have hev : ∀ᶠ m in (U : Filter ℕ),
      (τ m * ((idx m (t + h) : ℝ) - idx m t))⁻¹ • (zs m (t + h) - zs m t) ∈ S := by
    have e1 : ∀ᶠ m in (U : Filter ℕ), τ m * M < δ / 3 := by
      have : Tendsto (fun m => τ m * M) (U : Filter ℕ) (𝓝 0) := by
        simpa using hτ0U.mul_const M
      exact this.eventually (gt_mem_nhds (by positivity))
    have e2 : ∀ᶠ m in (U : Filter ℕ), dist (zs m t) (z t) < δ / 3 :=
      Metric.tendsto_nhds.1 (hz t) (δ / 3) (by positivity)
    have e3 : ∀ᶠ m in (U : Filter ℕ), 0 < τ m * ((idx m (t + h) : ℝ) - idx m t) :=
      hdiff.eventually (lt_mem_nhds hhpos)
    filter_upwards [e1, e2, e3] with m h1 h2 h3
    have hpos : (0 : ℝ) < (idx m (t + h) : ℝ) - idx m t := pos_of_mul_pos_right h3 (hτpos m).le
    have hij : idx m t < idx m (t + h) := by
      have : (idx m t : ℝ) < idx m (t + h) := by linarith
      exact_mod_cast this
    rw [hzs, hzs]
    refine E1_avg_mem c x0 (τ m) hSconv (hτpos m) hij (fun k hk => ?_)
    obtain ⟨hk1, hk2⟩ := Finset.mem_Ico.1 hk
    have hdist : ‖E1_eul c x0 (τ m) k - z t‖ < δ := by
      have a1 := E1_eul_norm_sub c x0 (τ m) (hτpos m).le hcM hk1
      have fs := hfl m t ht
      have ft := hfl m (t + h) (by linarith)
      have hk' : τ m * (k : ℝ) < τ m * idx m (t + h) :=
        mul_lt_mul_of_pos_left (by exact_mod_cast hk2) (hτpos m)
      have a2 : τ m * (M * ((k : ℝ) - idx m t)) ≤ M * h + τ m * M := by
        have : τ m * ((k : ℝ) - idx m t) ≤ h + τ m := by
          rw [mul_sub]; linarith
        calc τ m * (M * ((k : ℝ) - idx m t)) = M * (τ m * ((k : ℝ) - idx m t)) := by ring
          _ ≤ M * (h + τ m) := mul_le_mul_of_nonneg_left this hM
          _ = M * h + τ m * M := by ring
      rw [hzs, dist_eq_norm] at h2
      calc ‖E1_eul c x0 (τ m) k - z t‖
          ≤ ‖E1_eul c x0 (τ m) k - E1_eul c x0 (τ m) (idx m t)‖
            + ‖E1_eul c x0 (τ m) (idx m t) - z t‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ < δ := by linarith
    obtain ⟨w', hw', hww'⟩ := hδV _ hdist _ (hc _)
    exact Metric.thickening_subset_cthickening _ _
      (Metric.mem_thickening_iff.2 ⟨w', hw', by rwa [dist_eq_norm]⟩)
  have hmem : h⁻¹ • (z (t + h) - z t) ∈ S := hSclosed.mem_of_tendsto hq hev
  obtain ⟨w, hw, hwd⟩ := Metric.mem_thickening_iff.1
    (Metric.cthickening_subset_thickening' hε (by linarith) _ hmem)
  exact ⟨w, hw, by rwa [dist_eq_norm] at hwd⟩



end DFS
