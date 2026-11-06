import DFSLean.Defs

namespace DFS

open Real Filter Topology Set

variable {N K : ℕ}

/-! ### Helpers for Lemma C.4 (package B) -/

private lemma B_tendsto_sub (x : ℝ) : Tendsto (fun z => z - x) (𝓝[>] x) (𝓝[>] 0) := by
  have h1 : Tendsto (fun z => z - x) (𝓝[>] x) (𝓝 0) := by
    have : Tendsto (fun z => z - x) (𝓝 x) (𝓝 (x - x)) :=
      (continuous_id.sub continuous_const).tendsto x
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h1 ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact mem_Ioi.mpr (sub_pos.mpr hz)

private lemma B_freq_slope {f : ℝ → ℝ} {x g : ℝ}
    (hs : ∀ ε > 0, ∀ᶠ h in 𝓝[>] (0:ℝ), (f (x + h) - f x) / h < g + ε) :
    ∀ r, g < r → ∃ᶠ z in 𝓝[>] x, slope f x z < r := by
  intro r hr
  have h1 := (B_tendsto_sub x).eventually (hs (r - g) (sub_pos.mpr hr))
  refine (h1.mono fun z hz => ?_).frequently
  rw [slope_def_field]
  simpa using hz

/-- Barrier: if `f` is pushed down whenever it is above `L`, it stays below `L`. -/
private lemma B_barrier {f g : ℝ → ℝ} {a b L : ℝ} (hf : ContinuousOn f (Icc a b))
    (hs : ∀ x ∈ Ico a b, ∀ ε > 0, ∀ᶠ h in 𝓝[>] (0:ℝ), (f (x + h) - f x) / h < g x + ε)
    (hL : ∀ x ∈ Ico a b, L < f x → g x < 0) (ha : f a ≤ L) :
    ∀ x ∈ Icc a b, f x ≤ L := by
  intro x hx
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have key := image_le_of_liminf_slope_right_lt_deriv_boundary' (f' := g) hf
    (fun y hy => B_freq_slope (hs y hy)) (B := fun _ => L + ε / 2) (B' := fun _ => 0)
    (by linarith) continuousOn_const (fun y _ => hasDerivWithinAt_const _ _ _)
    (fun y hy hfy => hL y hy (by linarith)) hx
  linarith

/-- Linear comparison: slopes below `m` give growth at most `m`. -/
private lemma B_linear {f : ℝ → ℝ} {a b m : ℝ} (hf : ContinuousOn f (Icc a b))
    (hs : ∀ x ∈ Ico a b, ∀ ε > 0, ∀ᶠ h in 𝓝[>] (0:ℝ), (f (x + h) - f x) / h < m + ε) :
    ∀ x ∈ Icc a b, f x ≤ f a + m * (x - a) := by
  intro x hx
  refine image_le_of_liminf_slope_right_le_deriv_boundary hf (B := fun y => f a + m * (y - a))
    (B' := fun _ => m) (by simp) (by fun_prop) (fun y _ => ?_)
    (fun y hy => B_freq_slope (hs y hy)) hx
  have := (((hasDerivWithinAt_id y (Ici y)).sub_const a).const_mul m).const_add (f a)
  simpa using this

private lemma B_exp_half_lower {u v h q : ℝ} (hh : 0 < h) (hq : v - u = q * h) :
    exp (u / 2) * q / 2 ≤ (exp (v / 2) - exp (u / 2)) / h := by
  rw [le_div_iff₀ hh]
  have e : exp (v / 2) = exp (u / 2) * exp ((v - u) / 2) := by
    rw [← exp_add]; congr 1; ring
  have h1 := add_one_le_exp ((v - u) / 2)
  have h2 := exp_pos (u / 2)
  have h4 : exp (u / 2) * (v - u) = exp (u / 2) * (q * h) := by rw [hq]
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left h1 h2.le]

private lemma B_exp_half_upper {u v h : ℝ} (hh : 0 < h) :
    (exp (v / 2) - exp (u / 2)) / h ≤ exp (v / 2) * ((v - u) / h) / 2 := by
  rw [div_le_iff₀ hh]
  have e : exp (u / 2) = exp (v / 2) * exp ((u - v) / 2) := by
    rw [← exp_add]; congr 1; ring
  have h1 := add_one_le_exp ((u - v) / 2)
  have h2 := exp_pos (v / 2)
  have h3 : exp (v / 2) * ((v - u) / h) / 2 * h = exp (v / 2) * (v - u) / 2 := by
    field_simp
  rw [h3, e]
  nlinarith [mul_le_mul_of_nonneg_left h1 h2.le]


/-- Lemma C.4 (`lemma:log_growth`), two-sided bounds on `Θ = e^{2Y-X}` and on `e^{X/2}`. -/
theorem log_growth {t₀ : ℝ} {X Y : ℝ → ℝ} {aLo aHi ãLo ãHi βLo βHi c C : ℝ}
    (ha : 0 < aLo) (ha' : aLo ≤ aHi) (hã : 0 < ãLo) (hã' : ãLo ≤ ãHi)
    (hβ : 0 < βLo) (hβ' : βLo ≤ βHi)
    (hXc : ContinuousOn X (Ici t₀)) (hYc : ContinuousOn Y (Ici t₀))
    (hslope : ∀ t ≥ t₀, ∀ ε > 0, ∀ᶠ h in 𝓝[>] (0 : ℝ),
      ∃ a ∈ Icc aLo aHi, ∃ ã ∈ Icc ãLo ãHi, ∃ β ∈ Icc βLo βHi,
        |(X (t + h) - X t) / h - a * exp (Y t - X t)| < ε ∧
        |(Y (t + h) - Y t) / h - (β * exp (-Y t) - ã * exp (Y t - X t))| < ε)
    (hc : c = min (exp (2 * Y t₀ - X t₀)) (2 * βLo / (aHi + 2 * ãHi)))
    (hC : C = max (exp (2 * Y t₀ - X t₀)) (2 * βHi / (aLo + 2 * ãLo))) :
    ∀ t ≥ t₀,
      c ≤ exp (2 * Y t - X t) ∧ exp (2 * Y t - X t) ≤ C ∧
      exp (X t₀ / 2) + aLo * sqrt c / 2 * (t - t₀) ≤ exp (X t / 2) ∧
      exp (X t / 2) ≤ exp (X t₀ / 2) + aHi * sqrt C / 2 * (t - t₀) := by
  have haHi : 0 < aHi := lt_of_lt_of_le ha ha'
  have hãHi : 0 < ãHi := lt_of_lt_of_le hã hã'
  have hβHi : 0 < βHi := lt_of_lt_of_le hβ hβ'
  have hThm : 0 < 2 * βLo / (aHi + 2 * ãHi) := by positivity
  have hc0 : 0 < c := by rw [hc]; exact lt_min (exp_pos _) hThm
  have hC0 : 0 < C := by rw [hC]; exact lt_max_of_lt_left (exp_pos _)
  have hcle : c ≤ exp (2 * Y t₀ - X t₀) := hc ▸ min_le_left _ _
  have hcle' : c ≤ 2 * βLo / (aHi + 2 * ãHi) := hc ▸ min_le_right _ _
  have hCge : exp (2 * Y t₀ - X t₀) ≤ C := hC ▸ le_max_left _ _
  have hCge' : 2 * βHi / (aLo + 2 * ãLo) ≤ C := hC ▸ le_max_right _ _
  have hΘe : ∀ x, exp (Y x - X x) = exp (2 * Y x - X x) * exp (-Y x) := by
    intro x; rw [← exp_add]; congr 1; ring
  -- upper barrier for `log Θ = 2Y - X`
  have hup : ∀ t ≥ t₀, 2 * Y t - X t ≤ log C := by
    intro t ht
    refine B_barrier (f := fun s => 2 * Y s - X s)
      (g := fun s => 2 * βHi * exp (-Y s) - (aLo + 2 * ãLo) * exp (Y s - X s))
      (a := t₀) (b := t) (L := log C) ?_ ?_ ?_ ?_ t ⟨ht, le_rfl⟩
    · exact (continuousOn_const.mul (hYc.mono Icc_subset_Ici_self)).sub
        (hXc.mono Icc_subset_Ici_self)
    · intro x hx ε hε
      filter_upwards [hslope x hx.1 (ε / 3) (by positivity)] with h ⟨a, ha1, ã, hã1, β, hβ1, h1, h2⟩
      have e : (2 * Y (x + h) - X (x + h) - (2 * Y x - X x)) / h
          = 2 * ((Y (x + h) - Y x) / h) - (X (x + h) - X x) / h := by ring
      rw [e]
      have p1 := exp_pos (-Y x)
      have p2 := exp_pos (Y x - X x)
      have i1 : β * exp (-Y x) ≤ βHi * exp (-Y x) := mul_le_mul_of_nonneg_right hβ1.2 p1.le
      have i2 : ãLo * exp (Y x - X x) ≤ ã * exp (Y x - X x) :=
        mul_le_mul_of_nonneg_right hã1.1 p2.le
      have i3 : aLo * exp (Y x - X x) ≤ a * exp (Y x - X x) :=
        mul_le_mul_of_nonneg_right ha1.1 p2.le
      rw [abs_lt] at h1 h2
      linarith [h1.1, h2.2]
    · intro x hx hlt
      have hθ : C < exp (2 * Y x - X x) := by
        rw [← exp_log hC0]; exact exp_lt_exp.mpr hlt
      have hpos : 0 < aLo + 2 * ãLo := by positivity
      rw [div_le_iff₀ hpos] at hCge'
      have k1 : 2 * βHi < (aLo + 2 * ãLo) * exp (2 * Y x - X x) := by nlinarith
      have k2 := mul_lt_mul_of_pos_left k1 (exp_pos (-Y x))
      show 2 * βHi * exp (-Y x) - (aLo + 2 * ãLo) * exp (Y x - X x) < 0
      rw [hΘe x]
      nlinarith
    · exact (le_log_iff_exp_le hC0).mpr hCge
  -- lower barrier: `X - 2Y ≤ - log c`
  have hlo : ∀ t ≥ t₀, X t - 2 * Y t ≤ -log c := by
    intro t ht
    refine B_barrier (f := fun s => X s - 2 * Y s)
      (g := fun s => (aHi + 2 * ãHi) * exp (Y s - X s) - 2 * βLo * exp (-Y s))
      (a := t₀) (b := t) (L := -log c) ?_ ?_ ?_ ?_ t ⟨ht, le_rfl⟩
    · exact (hXc.mono Icc_subset_Ici_self).sub
        (continuousOn_const.mul (hYc.mono Icc_subset_Ici_self))
    · intro x hx ε hε
      filter_upwards [hslope x hx.1 (ε / 3) (by positivity)] with h ⟨a, ha1, ã, hã1, β, hβ1, h1, h2⟩
      have e : (X (x + h) - 2 * Y (x + h) - (X x - 2 * Y x)) / h
          = (X (x + h) - X x) / h - 2 * ((Y (x + h) - Y x) / h) := by ring
      rw [e]
      have p1 := exp_pos (-Y x)
      have p2 := exp_pos (Y x - X x)
      have i1 : βLo * exp (-Y x) ≤ β * exp (-Y x) := mul_le_mul_of_nonneg_right hβ1.1 p1.le
      have i2 : ã * exp (Y x - X x) ≤ ãHi * exp (Y x - X x) :=
        mul_le_mul_of_nonneg_right hã1.2 p2.le
      have i3 : a * exp (Y x - X x) ≤ aHi * exp (Y x - X x) :=
        mul_le_mul_of_nonneg_right ha1.2 p2.le
      rw [abs_lt] at h1 h2
      linarith [h1.2, h2.1]
    · intro x hx hlt
      have hθ : exp (2 * Y x - X x) < c := by
        rw [← exp_log hc0]; exact exp_lt_exp.mpr (by linarith)
      have hpos : 0 < aHi + 2 * ãHi := by positivity
      rw [le_div_iff₀ hpos] at hcle'
      have k1 : (aHi + 2 * ãHi) * exp (2 * Y x - X x) < 2 * βLo := by nlinarith
      have k2 := mul_lt_mul_of_pos_left k1 (exp_pos (-Y x))
      show (aHi + 2 * ãHi) * exp (Y x - X x) - 2 * βLo * exp (-Y x) < 0
      rw [hΘe x]
      nlinarith
    · have := (log_le_iff_le_exp hc0).mpr hcle
      show X t₀ - 2 * Y t₀ ≤ -log c
      linarith
  have hΘ : ∀ t ≥ t₀, c ≤ exp (2 * Y t - X t) ∧ exp (2 * Y t - X t) ≤ C := by
    intro t ht
    refine ⟨(log_le_iff_le_exp hc0).mp (by linarith [hlo t ht]),
      (le_log_iff_exp_le hC0).mp (hup t ht)⟩
  have hsq : ∀ x, exp (X x / 2) * exp (Y x - X x) = sqrt (exp (2 * Y x - X x)) := by
    intro x
    have : exp (2 * Y x - X x) = (exp (X x / 2) * exp (Y x - X x)) ^ 2 := by
      rw [← exp_add, sq, ← exp_add]; congr 1; ring
    rw [this, sqrt_sq (by positivity)]
  -- upper linear bound on `e^{X/2}`
  have hEup : ∀ t ≥ t₀, exp (X t / 2) ≤ exp (X t₀ / 2) + aHi * sqrt C / 2 * (t - t₀) := by
    intro t ht
    refine B_linear (f := fun s => exp (X s / 2)) (a := t₀) (b := t) (m := aHi * sqrt C / 2)
      ?_ ?_ t ⟨ht, le_rfl⟩
    · exact ((hXc.mono Icc_subset_Ici_self).div_const 2).rexp
    · intro x hx ε hε
      obtain ⟨A, hA⟩ : ∃ A, A = exp (X x / 2) := ⟨_, rfl⟩
      obtain ⟨e1, he1⟩ : ∃ e1, e1 = exp (Y x - X x) := ⟨_, rfl⟩
      have hA0 : 0 < A := hA ▸ exp_pos _
      have he10 : 0 < e1 := he1 ▸ exp_pos _
      obtain ⟨Q, hQ⟩ : ∃ Q, Q = aHi * e1 + 1 := ⟨_, rfl⟩
      obtain ⟨K, hK⟩ : ∃ K, K = A * (aHi * e1 + 1) / 2 + 1 := ⟨_, rfl⟩
      have hK0 : 0 < K := by rw [hK]; positivity
      obtain ⟨ε₁, hε₁⟩ : ∃ ε₁, ε₁ = min 1 (ε / A) := ⟨_, rfl⟩
      have hε₁0 : 0 < ε₁ := hε₁ ▸ lt_min one_pos (by positivity)
      obtain ⟨δ, hδ⟩ : ∃ δ, δ = ε / (2 * K) := ⟨_, rfl⟩
      have hδ0 : 0 < δ := by rw [hδ]; positivity
      have hev2 : ∀ᶠ h in 𝓝[>] (0:ℝ), exp (Q * h / 2) < 1 + δ := by
        have : Tendsto (fun h : ℝ => exp (Q * h / 2)) (𝓝 0) (𝓝 1) := by
          have hcont : Continuous (fun h : ℝ => exp (Q * h / 2)) := by fun_prop
          simpa using hcont.tendsto 0
        exact (this.eventually_lt_const (by linarith)).filter_mono nhdsWithin_le_nhds
      filter_upwards [hslope x hx.1 ε₁ hε₁0, hev2, self_mem_nhdsWithin]
        with h ⟨a, ha1, ã, hã1, β, hβ1, h1, h2⟩ he hh
      have hh : 0 < h := hh
      obtain ⟨q, hq⟩ : ∃ q, q = (X (x + h) - X x) / h := ⟨_, rfl⟩
      have up := B_exp_half_upper (u := X x) (v := X (x + h)) hh
      rw [← hq, ← hA] at up
      rw [← hq, ← he1] at h1
      show (exp (X (x + h) / 2) - exp (X x / 2)) / h < aHi * sqrt C / 2 + ε
      rw [← hA]
      have hXq : X (x + h) = X x + q * h := by rw [hq]; field_simp; ring
      have hEq : exp (X (x + h) / 2) = A * exp (q * h / 2) := by
        rw [hXq, hA, ← exp_add]; congr 1; ring
      rw [abs_lt] at h1
      have hqa : q < a * e1 + ε₁ := by linarith [h1.2]
      have hae : a * e1 ≤ aHi * e1 := mul_le_mul_of_nonneg_right ha1.2 he10.le
      have hε₁1 : ε₁ ≤ 1 := hε₁ ▸ min_le_left _ _
      have hε₁2 : ε₁ ≤ ε / A := hε₁ ▸ min_le_right _ _
      have hAε : A * ε₁ ≤ ε := by rwa [le_div_iff₀' hA0] at hε₁2
      have hsqC : A * e1 ≤ sqrt C := by rw [hA, he1, hsq x]; exact sqrt_le_sqrt (hΘ x hx.1).2
      have hRHS : 0 ≤ aHi * sqrt C / 2 := by positivity
      rcases le_or_gt q 0 with hq0 | hq0
      · have : exp (X (x + h) / 2) * q / 2 ≤ 0 := by
          have := exp_pos (X (x + h) / 2)
          have : exp (X (x + h) / 2) * q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos this.le hq0
          linarith
        linarith
      · have hqQ : q * h ≤ Q * h := mul_le_mul_of_nonneg_right (by linarith) hh.le
        have hexp : exp (q * h / 2) < 1 + δ :=
          lt_of_le_of_lt (exp_le_exp.mpr (by linarith)) he
        rw [hEq] at up ⊢
        have s1 : A * exp (q * h / 2) * q ≤ A * (1 + δ) * q := by
          have := mul_le_mul_of_nonneg_left hexp.le (mul_nonneg hA0.le hq0.le)
          linarith
        have s2 : A * (1 + δ) * q ≤ A * (1 + δ) * (aHi * e1 + ε₁) := by
          have : 0 ≤ A * (1 + δ) := by positivity
          exact mul_le_mul_of_nonneg_left (by linarith) this
        have s3 : δ * (A * (aHi * e1 + ε₁) / 2) < ε / 2 := by
          have k1 : A * (aHi * e1 + ε₁) / 2 < K := by
            have := mul_le_mul_of_nonneg_left hε₁1 hA0.le
            rw [hK]; nlinarith
          have k2 : δ * K = ε / 2 := by rw [hδ]; field_simp
          have k3 := mul_lt_mul_of_pos_left k1 hδ0
          linarith
        have s4 : (A * e1) * aHi ≤ sqrt C * aHi := mul_le_mul_of_nonneg_right hsqC haHi.le
        have s5 : A * (1 + δ) * (aHi * e1 + ε₁) / 2
            = (A * e1) * aHi / 2 + A * ε₁ / 2 + δ * (A * (aHi * e1 + ε₁) / 2) := by ring
        have s6 : A * exp (q * h / 2) * q / 2 ≤ A * (1 + δ) * (aHi * e1 + ε₁) / 2 := by
          linarith
        linarith
  -- lower linear bound on `e^{X/2}`
  have hElo : ∀ t ≥ t₀, exp (X t₀ / 2) + aLo * sqrt c / 2 * (t - t₀) ≤ exp (X t / 2) := by
    intro t ht
    have key := B_linear (f := fun s => -exp (X s / 2)) (a := t₀) (b := t)
      (m := -(aLo * sqrt c / 2)) ?_ ?_ t ⟨ht, le_rfl⟩
    · linarith
    · exact (((hXc.mono Icc_subset_Ici_self).div_const 2).rexp).neg
    · intro x hx ε hε
      obtain ⟨A, hA⟩ : ∃ A, A = exp (X x / 2) := ⟨_, rfl⟩
      obtain ⟨e1, he1⟩ : ∃ e1, e1 = exp (Y x - X x) := ⟨_, rfl⟩
      have hA0 : 0 < A := hA ▸ exp_pos _
      have he10 : 0 < e1 := he1 ▸ exp_pos _
      filter_upwards [hslope x hx.1 (ε / A) (by positivity), self_mem_nhdsWithin]
        with h ⟨a, ha1, ã, hã1, β, hβ1, h1, h2⟩ hh
      have hh : 0 < h := hh
      obtain ⟨q, hq⟩ : ∃ q, q = (X (x + h) - X x) / h := ⟨_, rfl⟩
      have lo := B_exp_half_lower (u := X x) (v := X (x + h)) (q := q) hh
        (by rw [hq]; field_simp)
      rw [← hA] at lo
      rw [← hq, ← he1] at h1
      show (-exp (X (x + h) / 2) - -exp (X x / 2)) / h < -(aLo * sqrt c / 2) + ε
      rw [← hA]
      rw [abs_lt] at h1
      have hsqc : sqrt c ≤ A * e1 := by rw [hA, he1, hsq x]; exact sqrt_le_sqrt (hΘ x hx.1).1
      have k1 : A * (a * e1 - ε / A) < A * q := mul_lt_mul_of_pos_left (by linarith [h1.1]) hA0
      have k2 : A * (a * e1 - ε / A) = (A * e1) * a - ε := by field_simp
      have k3 : (A * e1) * aLo ≤ (A * e1) * a := mul_le_mul_of_nonneg_left ha1.1 (by positivity)
      have k4 : sqrt c * aLo ≤ (A * e1) * aLo := mul_le_mul_of_nonneg_right hsqc ha.le
      have e : (-exp (X (x + h) / 2) - -A) / h = -((exp (X (x + h) / 2) - A) / h) := by ring
      rw [e]
      linarith
  intro t ht
  exact ⟨(hΘ t ht).1, (hΘ t ht).2, hElo t ht, hEup t ht⟩



/-- Lemma C.4, "in particular" part, with the constant uniform over initial values
`|X t₀|, |Y t₀| ≤ M` (it depends only on `t₀`, `M` and the coefficient bounds). -/
theorem log_growth_asymp {t₀ M aLo aHi ãLo ãHi βLo βHi : ℝ} (ht₀ : 1 ≤ t₀)
    (ha : 0 < aLo) (ha' : aLo ≤ aHi) (hã : 0 < ãLo) (hã' : ãLo ≤ ãHi)
    (hβ : 0 < βLo) (hβ' : βLo ≤ βHi) :
    ∃ C' : ℝ, ∀ X Y : ℝ → ℝ, ContinuousOn X (Ici t₀) → ContinuousOn Y (Ici t₀) →
      (∀ t ≥ t₀, ∀ ε > 0, ∀ᶠ h in 𝓝[>] (0 : ℝ),
        ∃ a ∈ Icc aLo aHi, ∃ ã ∈ Icc ãLo ãHi, ∃ β ∈ Icc βLo βHi,
          |(X (t + h) - X t) / h - a * exp (Y t - X t)| < ε ∧
          |(Y (t + h) - Y t) / h - (β * exp (-Y t) - ã * exp (Y t - X t))| < ε) →
      |X t₀| ≤ M → |Y t₀| ≤ M →
      ∀ t ≥ 2 * t₀, |X t - 2 * log t| ≤ C' ∧ |Y t - log t| ≤ C' := by
  have haHi : 0 < aHi := lt_of_lt_of_le ha ha'
  have hãHi : 0 < ãHi := lt_of_lt_of_le hã hã'
  have hβHi : 0 < βHi := lt_of_lt_of_le hβ hβ'
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, c₀ = min (exp (-(3 * M))) (2 * βLo / (aHi + 2 * ãHi)) := ⟨_, rfl⟩
  obtain ⟨C₀, hC₀⟩ : ∃ C₀, C₀ = max (exp (3 * M)) (2 * βHi / (aLo + 2 * ãLo)) := ⟨_, rfl⟩
  have hc₀0 : 0 < c₀ := by rw [hc₀]; exact lt_min (exp_pos _) (by positivity)
  have hC₀0 : 0 < C₀ := by rw [hC₀]; exact lt_max_of_lt_left (exp_pos _)
  obtain ⟨L₁, hL₁⟩ : ∃ L₁, L₁ = aLo * sqrt c₀ / 4 := ⟨_, rfl⟩
  obtain ⟨U₁, hU₁⟩ : ∃ U₁, U₁ = exp (M / 2) + aHi * sqrt C₀ / 2 := ⟨_, rfl⟩
  have hL₁0 : 0 < L₁ := by rw [hL₁]; have := sqrt_pos.mpr hc₀0; positivity
  have hU₁0 : 0 < U₁ := by rw [hU₁]; positivity
  refine ⟨2 * (|log L₁| + |log U₁|) + |log c₀| + |log C₀|, ?_⟩
  intro X Y hXc hYc hslope hXM hYM t ht
  obtain ⟨h1, h2, h3, h4⟩ :=
    log_growth ha ha' hã hã' hβ hβ' hXc hYc hslope rfl rfl t (by linarith)
  have hXM' := abs_le.mp hXM
  have hYM' := abs_le.mp hYM
  have hcc : c₀ ≤ min (exp (2 * Y t₀ - X t₀)) (2 * βLo / (aHi + 2 * ãHi)) := by
    rw [hc₀]; exact min_le_min (exp_le_exp.mpr (by linarith)) le_rfl
  have hCC : max (exp (2 * Y t₀ - X t₀)) (2 * βHi / (aLo + 2 * ãLo)) ≤ C₀ := by
    rw [hC₀]; exact max_le_max (exp_le_exp.mpr (by linarith)) le_rfl
  have ht0 : 0 < t := by linarith
  have ht1 : 1 ≤ t := by linarith
  have hlowE : L₁ * t ≤ exp (X t / 2) := by
    have i1 := sqrt_le_sqrt hcc
    have i2 : t / 2 ≤ t - t₀ := by linarith
    have i3 := exp_pos (X t₀ / 2)
    have i4 : aLo * sqrt c₀ / 2 * (t / 2)
        ≤ aLo * sqrt (min (exp (2 * Y t₀ - X t₀)) (2 * βLo / (aHi + 2 * ãHi))) / 2 * (t - t₀) :=
      mul_le_mul (by gcongr) i2 (by positivity) (by positivity)
    have e : L₁ * t = aLo * sqrt c₀ / 2 * (t / 2) := by rw [hL₁]; ring
    linarith
  have hupE : exp (X t / 2) ≤ U₁ * t := by
    have i1 := sqrt_le_sqrt hCC
    have i2 : exp (X t₀ / 2) ≤ exp (M / 2) := exp_le_exp.mpr (by linarith)
    have i3 : exp (M / 2) ≤ exp (M / 2) * t := le_mul_of_one_le_right (exp_pos _).le ht1
    have i4 : aHi * sqrt (max (exp (2 * Y t₀ - X t₀)) (2 * βHi / (aLo + 2 * ãLo))) / 2 * (t - t₀)
        ≤ aHi * sqrt C₀ / 2 * t :=
      mul_le_mul (by gcongr) (by linarith) (by linarith) (by positivity)
    have e : U₁ * t = exp (M / 2) * t + aHi * sqrt C₀ / 2 * t := by rw [hU₁]; ring
    linarith
  have hX1 : log L₁ + log t ≤ X t / 2 := by
    rw [← log_mul hL₁0.ne' ht0.ne', ← log_exp (X t / 2)]
    exact log_le_log (by positivity) hlowE
  have hX2 : X t / 2 ≤ log U₁ + log t := by
    rw [← log_mul hU₁0.ne' ht0.ne', ← log_exp (X t / 2)]
    exact log_le_log (exp_pos _) hupE
  have hY1 : log c₀ ≤ 2 * Y t - X t := by
    rw [← log_exp (2 * Y t - X t)]; exact log_le_log hc₀0 (hcc.trans h1)
  have hY2 : 2 * Y t - X t ≤ log C₀ := by
    rw [← log_exp (2 * Y t - X t)]; exact log_le_log (exp_pos _) (h2.trans hCC)
  have a1 := neg_abs_le (log L₁)
  have a2 := le_abs_self (log U₁)
  have a3 := neg_abs_le (log c₀)
  have a4 := le_abs_self (log C₀)
  have a5 := abs_nonneg (log L₁)
  have a6 := abs_nonneg (log U₁)
  have a7 := abs_nonneg (log c₀)
  have a8 := abs_nonneg (log C₀)
  constructor
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith




end DFS
