import DFSLean.Model
import DFSLean.Basic

/-!
# Package G: generic differential inclusions on `ℝⁿ`

Generalizes the Stage 1 lemmas of `DFSLean/Basic.lean` (`IsSol.slope_lin₂`, `A_upper`, `A_cmp`,
`IsSol.barrier`, `IsSol.reach`) from `Vel N K α`, `lin c` on `Fin 4 → ℝ` to an arbitrary velocity
set `V` and `c ⬝ᵥ ·` on `Fin n → ℝ`.
-/

noncomputable section

namespace DFS

open Real Finset Filter Topology Set

variable {N K : ℕ}

section generic
variable {n : ℕ} {V : (Fin n → ℝ) → Set (Fin n → ℝ)} {z : ℝ → Fin n → ℝ}

theorem IsSol_iff_IsDI {α : ℝ} {z : ℝ → Fin 4 → ℝ} : IsSol N K α z ↔ IsDI (Vel N K α) z :=
  Iff.rfl



theorem IsDI.mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {V W : E → Set E}
    {z : ℝ → E} (hVW : ∀ x, V x ⊆ W x) (hz : IsDI V z) : IsDI W z :=
  ⟨hz.1, fun t ht ε hε => (hz.2 t ht ε hε).mono fun _ ⟨w, hw, hlt⟩ => ⟨w, hVW _ hw, hlt⟩⟩



theorem IsDI.shift (hz : IsDI V z) {T : ℝ} (hT : 0 ≤ T) : IsDI V (fun t => z (T + t)) := by
  refine ⟨?_, ?_⟩
  · exact hz.1.comp (continuousOn_const.add continuousOn_id)
      (fun t (ht : t ∈ Set.Ici 0) => show T + t ∈ Set.Ici 0 from add_nonneg hT ht)
  · intro t ht ε hε
    filter_upwards [hz.2 (T + t) (add_nonneg hT ht) ε hε] with h hh
    simpa only [add_assoc] using hh



/-! ### Difference quotients of linear functionals -/

private lemma G_dot_abs (c v : Fin n → ℝ) : |c ⬝ᵥ v| ≤ (∑ i, |c i|) * ‖v‖ := by
  unfold dotProduct
  calc |∑ i, c i * v i| ≤ ∑ i, |c i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |c i| * |v i| := by simp only [abs_mul]
    _ ≤ ∑ i, |c i| * ‖v‖ := by
        gcongr with i
        simpa using norm_le_pi_norm v i
    _ = (∑ i, |c i|) * ‖v‖ := by rw [Finset.sum_mul]

private lemma G_dot_quot (c p q w : Fin n → ℝ) (h : ℝ) :
    (c ⬝ᵥ p - c ⬝ᵥ q) / h - c ⬝ᵥ w = c ⬝ᵥ (h⁻¹ • (p - q) - w) := by
  rw [dotProduct_sub, dotProduct_smul, dotProduct_sub, smul_eq_mul, div_eq_inv_mul]

theorem IsDI.slope_dot (hz : IsDI V z) (c d : Fin n → ℝ) {t : ℝ} (ht : 0 ≤ t) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), ∃ w ∈ V (z t),
      |(c ⬝ᵥ z (t + h) - c ⬝ᵥ z t) / h - c ⬝ᵥ w| < ε ∧
      |(d ⬝ᵥ z (t + h) - d ⬝ᵥ z t) / h - d ⬝ᵥ w| < ε := by
  set Sc := ∑ i, |c i| with hSc
  set Sd := ∑ i, |d i| with hSd
  have hSc0 : 0 ≤ Sc := Finset.sum_nonneg fun i _ => abs_nonneg (c i)
  have hSd0 : 0 ≤ Sd := Finset.sum_nonneg fun i _ => abs_nonneg (d i)
  have hD : 0 < 1 + Sc + Sd := by linarith
  filter_upwards [hz.2 t ht (ε / (1 + Sc + Sd)) (div_pos hε hD)] with h hh
  obtain ⟨w, hwV, hw⟩ := hh
  refine ⟨w, hwV, ?_, ?_⟩
  · rw [G_dot_quot]
    calc _ ≤ Sc * ‖h⁻¹ • (z (t + h) - z t) - w‖ := G_dot_abs _ _
      _ ≤ Sc * (ε / (1 + Sc + Sd)) := mul_le_mul_of_nonneg_left hw.le hSc0
      _ < ε := by
        rw [← mul_div_assoc, div_lt_iff₀ hD]
        nlinarith
  · rw [G_dot_quot]
    calc _ ≤ Sd * ‖h⁻¹ • (z (t + h) - z t) - w‖ := G_dot_abs _ _
      _ ≤ Sd * (ε / (1 + Sc + Sd)) := mul_le_mul_of_nonneg_left hw.le hSd0
      _ < ε := by
        rw [← mul_div_assoc, div_lt_iff₀ hD]
        nlinarith



/-- Right slopes of `c ⬝ᵥ z` at `x` are eventually close to `c ⬝ᵥ w` for some `w ∈ V (z x)`. -/
private lemma G_slope_ev (hz : IsDI V z) (c : Fin n → ℝ) {x : ℝ} (hx : 0 ≤ x) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ y in 𝓝[>] x, ∃ w ∈ V (z x), |slope (fun t => c ⬝ᵥ z t) x y - c ⬝ᵥ w| < ε := by
  filter_upwards [(A_tendsto_sub x).eventually (DFS.IsDI.slope_dot hz c c hx hε)]
    with y ⟨w, hwV, h1, _⟩
  refine ⟨w, hwV, ?_⟩
  have e : x + (y - x) = y := by ring
  rw [e] at h1
  rwa [slope_def_field]

private lemma G_continuousOn_dot {s : Set ℝ} (hz : ContinuousOn z s) (c : Fin n → ℝ) :
    ContinuousOn (fun t => c ⬝ᵥ z t) s :=
  (show Continuous fun x : Fin n → ℝ => c ⬝ᵥ x from
    continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)).comp_continuousOn hz

private lemma G_contIcc (hz : IsDI V z) (c : Fin n → ℝ) {a b : ℝ} (ha : 0 ≤ a) :
    ContinuousOn (fun t => c ⬝ᵥ z t) (Icc a b) :=
  G_continuousOn_dot (hz.1.mono fun t (ht : t ∈ Icc a b) => show t ∈ Set.Ici 0 from le_trans ha ht.1) c

/-- Comparison of `c ⬝ᵥ z` with a right-differentiable barrier `B`. -/
private lemma G_cmp (hz : IsDI V z) (c : Fin n → ℝ) {a b : ℝ}
    (ha : 0 ≤ a) {B B' : ℝ → ℝ} (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x) (hfa : c ⬝ᵥ z a ≤ B a)
    (bound : ∀ x ∈ Ico a b, c ⬝ᵥ z x = B x → ∃ r < B' x, ∀ w ∈ V (z x), c ⬝ᵥ w ≤ r) :
    ∀ x ∈ Icc a b, c ⬝ᵥ z x ≤ B x := by
  intro x hx
  refine A_fence (f := fun t => c ⬝ᵥ z t) (G_contIcc hz c ha) hfa hB hB' ?_ hx
  intro x hx hfx
  obtain ⟨r, hr, hall⟩ := bound x hx hfx
  refine ⟨(r + B' x) / 2, by linarith, ?_⟩
  refine Eventually.frequently ?_
  filter_upwards [G_slope_ev hz c (ha.trans hx.1) (ε := (B' x - r) / 2) (by linarith)]
    with y ⟨w, hwV, hy⟩
  have := hall w hwV
  have := (abs_lt.1 hy).2
  linarith

/-- Linear upper bound for `c ⬝ᵥ z` from an upper bound on the velocities (all `t ∈ Icc a b`). -/
private lemma G_upper (hz : IsDI V z) (c : Fin n → ℝ) {a b : ℝ} (ha : 0 ≤ a) (M : ℝ)
    (hM : ∀ t ∈ Ico a b, ∀ w ∈ V (z t), c ⬝ᵥ w ≤ M) :
    ∀ t ∈ Icc a b, c ⬝ᵥ z t ≤ c ⬝ᵥ z a + M * (t - a) := by
  intro t ht
  refine image_le_of_liminf_slope_right_le_deriv_boundary (f := fun t => c ⬝ᵥ z t)
    (B := fun t => c ⬝ᵥ z a + M * (t - a)) (B' := fun _ => M) (G_contIcc hz c ha) (by simp)
    (by fun_prop) ?_ ?_ ht
  · intro x _
    have := ((hasDerivWithinAt_id x (Ici x)).sub_const a).const_mul M
    simpa using this.const_add (c ⬝ᵥ z a)
  · intro x hx r hr
    refine Eventually.frequently ?_
    filter_upwards [G_slope_ev hz c (ha.trans hx.1) (ε := r - M) (by linarith)]
      with y ⟨w, hwV, hy⟩
    have := hM x hx w hwV
    have := (abs_lt.1 hy).2
    linarith

/-- Mean-value bound: velocities with `c ⬝ᵥ w ≤ M` on `[a, b)` give `c ⬝ᵥ z b ≤ c ⬝ᵥ z a + M (b - a)`. -/
theorem IsDI.dot_le (hz : IsDI V z) (c : Fin n → ℝ) (M : ℝ) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (h : ∀ t ∈ Ico a b, ∀ w ∈ V (z t), c ⬝ᵥ w ≤ M) :
    c ⬝ᵥ z b ≤ c ⬝ᵥ z a + M * (b - a) :=
  G_upper hz c ha M h b ⟨hab, le_rfl⟩



theorem IsDI.barrier (hz : IsDI V z) (c : Fin n → ℝ) (L : ℝ) {a b : ℝ} (ha : 0 ≤ a)
    (h : ∀ t ∈ Ico a b, L < c ⬝ᵥ z t → ∀ w ∈ V (z t), c ⬝ᵥ w ≤ 0) :
    ∀ t ∈ Icc a b, c ⬝ᵥ z t ≤ max (c ⬝ᵥ z a) L := by
  intro t ht
  set m := max (c ⬝ᵥ z a) L
  have key : ∀ ε > 0, c ⬝ᵥ z t ≤ m + ε * (1 + (t - a)) := by
    intro ε hε
    refine G_cmp hz c ha (B := fun x => m + ε * (1 + (x - a))) (B' := fun _ => ε)
      (by fun_prop) ?_ ?_ ?_ t ht
    · intro x _
      have := (((hasDerivWithinAt_id x (Ici x)).sub_const a).const_add 1).const_mul ε
      simpa using this.const_add m
    · simp only [sub_self, add_zero, mul_one]
      linarith [le_max_left (c ⬝ᵥ z a) L]
    · intro x hx hfx
      refine ⟨0, hε, h x hx ?_⟩
      rw [hfx]
      have : 0 < ε * (1 + (x - a)) := mul_pos hε (by linarith [hx.1])
      linarith [le_max_right (c ⬝ᵥ z a) L]
  have hta : 0 ≤ t - a := by linarith [ht.1]
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have h1 : 0 < 1 + (t - a) := by linarith
  have := key (δ / (1 + (t - a))) (div_pos hδ h1)
  rwa [div_mul_cancel₀ _ h1.ne'] at this



theorem IsDI.reach (hz : IsDI V z) (c : Fin n → ℝ) (L δ : ℝ) (hδ : 0 < δ) {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ t ≥ a, c ⬝ᵥ z t < L → ∀ w ∈ V (z t), δ ≤ c ⬝ᵥ w) :
    ∀ t ≥ a, a + (L - c ⬝ᵥ z a) / δ ≤ t → L ≤ c ⬝ᵥ z t := by
  intro t hta htt
  by_contra hlt
  replace hlt := lt_of_not_ge hlt
  by_cases hex : ∃ s ∈ Icc a t, L ≤ c ⬝ᵥ z s
  · obtain ⟨s, hs, hLs⟩ := hex
    have key := DFS.IsDI.barrier hz (-c) (-L) (a := s) (b := t) (ha.trans hs.1)
      (fun t' ht' hlt' w hw => by
        rw [neg_dotProduct] at hlt' ⊢
        have := h t' (hs.1.trans ht'.1) (by linarith) w hw
        linarith) t ⟨hs.2, le_rfl⟩
    rw [neg_dotProduct, neg_dotProduct, max_eq_right (by linarith)] at key
    linarith
  · replace hex : ∀ s ∈ Icc a t, c ⬝ᵥ z s < L := fun s hs =>
      lt_of_not_ge fun h' => hex ⟨s, hs, h'⟩
    have key := G_upper hz (-c) ha (-δ) (b := t)
      (fun t' ht' w hw => by
        rw [neg_dotProduct]
        have := h t' ht'.1 (hex t' ⟨ht'.1, ht'.2.le⟩) w hw
        linarith) t ⟨hta, le_rfl⟩
    rw [neg_dotProduct, neg_dotProduct] at key
    have h2 : (L - c ⬝ᵥ z a) / δ ≤ t - a := by linarith
    rw [div_le_iff₀ hδ] at h2
    nlinarith



end generic

end DFS

