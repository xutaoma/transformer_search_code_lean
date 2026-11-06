import DFSLean.Existence

/-!
# E2. The scalar velocity set `V8` satisfies the hypotheses of Filippov's theorem

`g8 s σ = ∑_k ∑_v (p_{k,v}(s) - [v = y_k]) • D_{k,v}(σ)` where
`D_{k,v}(σ) = σ(c¹) • c¹ + σ(c²) • c²` (masked at the current node) with fixed vectors
`c^h = iotaT (coef_h (ctx k) v)`; the probabilities are continuous in `s` and lie in `(0, 1]`.
-/

noncomputable section
open Real Finset Filter Topology Set

namespace DFS

variable {N K : ℕ}

/-! ### Linear algebra of `iotaT` -/

/-- `iotaT` as a linear map. -/
def E2_iotaTL : Params N →ₗ[ℝ] (Fin 8 → ℝ) where
  toFun := iotaT
  map_add' f g := by
    funext m
    simp only [iotaT, pair, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r f := by
    funext m
    simp only [iotaT, pair, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

lemma E2_iotaTL_apply (f : Params N) : E2_iotaTL f = iotaT f := rfl

/-- Selected gradient of a logit, pulled back to the eight scalars. -/
def E2_D (c : Ctx N) (v : Fin N) (σ : (Fin 8 → ℝ) → ℝ) : Fin 8 → ℝ :=
  iotaT (dlogit c v (σ ∘ iotaT))

lemma E2_D_eq (c : Ctx N) (v : Fin N) (σ : (Fin 8 → ℝ) → ℝ) :
    E2_D c v σ = if v = c.cur then 0 else
      σ (iotaT (coef1 c v)) • iotaT (coef1 c v) + σ (iotaT (coef2 c v)) • iotaT (coef2 c v) := by
  unfold E2_D dlogit
  rw [← E2_iotaTL_apply]
  split_ifs
  · simp
  · simp [map_add, map_smul, E2_iotaTL_apply]

lemma E2_D_congr (c : Ctx N) (v : Fin N) {σ₁ σ₂ : (Fin 8 → ℝ) → ℝ}
    (h1 : σ₁ (iotaT (coef1 c v)) = σ₂ (iotaT (coef1 c v)))
    (h2 : σ₁ (iotaT (coef2 c v)) = σ₂ (iotaT (coef2 c v))) :
    E2_D c v σ₁ = E2_D c v σ₂ := by
  rw [E2_D_eq, E2_D_eq, h1, h2]

lemma E2_D_lin (c : Ctx N) (v : Fin N) (a b : ℝ) (σ₁ σ₂ : (Fin 8 → ℝ) → ℝ) :
    E2_D c v (fun x => a * σ₁ x + b * σ₂ x) = a • E2_D c v σ₁ + b • E2_D c v σ₂ := by
  rw [E2_D_eq, E2_D_eq, E2_D_eq]
  split_ifs
  · simp
  · simp only [add_smul, mul_smul, smul_add]
    abel

lemma E2_D_norm_le (c : Ctx N) (v : Fin N) {σ : (Fin 8 → ℝ) → ℝ}
    (hσ : ∀ x, σ x ∈ Icc (0 : ℝ) 1) :
    ‖E2_D c v σ‖ ≤ ‖iotaT (coef1 c v)‖ + ‖iotaT (coef2 c v)‖ := by
  rw [E2_D_eq]
  split_ifs
  · simp only [norm_zero]; positivity
  · refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;>
    · rw [norm_smul, Real.norm_eq_abs]
      obtain ⟨h0, h1⟩ := hσ _
      rw [abs_of_nonneg h0]
      exact mul_le_of_le_one_left (norm_nonneg _) h1

/-! ### Probabilities -/

lemma E2_prob_pos [NeZero N] (θ : Params N) (c : Ctx N) (v : Fin N) : 0 < prob θ c v :=
  div_pos (exp_pos _) (Finset.sum_pos (fun _ _ => exp_pos _) univ_nonempty)

lemma E2_prob_le_one [NeZero N] (θ : Params N) (c : Ctx N) (v : Fin N) : prob θ c v ≤ 1 := by
  unfold prob
  rw [div_le_one (Finset.sum_pos (fun _ _ => exp_pos _) univ_nonempty)]
  exact Finset.single_le_sum (f := fun w => exp (logit θ c w)) (fun _ _ => (exp_pos _).le)
    (mem_univ v)

lemma E2_abs_prob_sub_le [NeZero N] (θ : Params N) (c : Ctx N) (v y : Fin N) :
    |prob θ c v - if v = y then 1 else 0| ≤ 1 := by
  have h0 := E2_prob_pos θ c v
  have h1 := E2_prob_le_one θ c v
  rw [abs_le]
  split_ifs <;> constructor <;> linarith

lemma E2_iota_continuous : Continuous (iota : (Fin 8 → ℝ) → Params N) := by
  refine continuous_pi fun k => continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases k <;> by_cases h : i = j <;> simp [iota, sym, h] <;> exact continuous_apply _

lemma E2_head1_continuous (c : Ctx N) (v : Fin N) :
    Continuous fun θ : Params N => head1 θ c v := by
  unfold head1
  have : Continuous fun θ : Params N =>
      (c.hidden.map fun x => score1 θ x c.query • val1 x).sum :=
    continuous_list_sum _ fun x _ =>
      (by unfold score1 bil; fun_prop : Continuous fun θ => score1 θ x c.query).smul
        continuous_const
  exact (continuous_apply v).comp this

lemma E2_head2_continuous (c : Ctx N) (v : Fin N) :
    Continuous fun θ : Params N => head2 θ c v := by
  unfold head2
  have : Continuous fun θ : Params N =>
      (c.hidden.map fun x => score2 θ x c.query • val2 x).sum :=
    continuous_list_sum _ fun x _ =>
      (by unfold score2 bil; fun_prop : Continuous fun θ => score2 θ x c.query).smul
        continuous_const
  exact (continuous_apply v).comp this

lemma E2_logit_continuous (c : Ctx N) (v : Fin N) :
    Continuous fun s : Fin 8 → ℝ => logit (iota s) c v := by
  unfold logit
  split_ifs
  · exact continuous_const
  · have h1 := (E2_head1_continuous c v).comp E2_iota_continuous
    have h2 := (E2_head2_continuous c v).comp E2_iota_continuous
    exact (continuous_const.add (h1.max continuous_const)).add
      (continuous_const.add (h2.max continuous_const))

lemma E2_prob_continuous [NeZero N] (c : Ctx N) (v : Fin N) :
    Continuous fun s : Fin 8 → ℝ => prob (iota s) c v := by
  unfold prob
  refine ((E2_logit_continuous c v).rexp).div
    (continuous_finsetSum _ fun w _ => (E2_logit_continuous c w).rexp) fun s => ?_
  exact (Finset.sum_pos (fun _ _ => exp_pos _) univ_nonempty).ne'


/-! ### The explicit form of `g8` -/

section expl
variable (N K : ℕ) [NeZero N]

/-- Context of training step `k` (identity relabeling). -/
abbrev E2_cs (k : ℕ) : Ctx N := (ctx N K k).perm 1

/-- Label of training step `k` (identity relabeling). -/
abbrev E2_ys (k : ℕ) : Fin N := (1 : Equiv.Perm (Fin N)) (ylab N K k)

/-- The finite set of scalar functionals on which `g8` reads the selection. -/
def E2_F : Finset (Fin 8 → ℝ) :=
  (range (2 * K + 2)).biUnion fun k => univ.biUnion fun v =>
    {iotaT (coef1 (E2_cs N K k) v), iotaT (coef2 (E2_cs N K k) v)}

/-- Uniform bound on the logit-gradient terms. -/
def E2_B (k : ℕ) (v : Fin N) : ℝ :=
  ‖iotaT (coef1 (E2_cs N K k) v)‖ + ‖iotaT (coef2 (E2_cs N K k) v)‖

variable {N K}

lemma E2_mem_F1 {k : ℕ} (hk : k ∈ range (2 * K + 2)) (v : Fin N) :
    iotaT (coef1 (E2_cs N K k) v) ∈ E2_F N K := by
  simp only [E2_F, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
  exact ⟨k, hk, v, Finset.mem_univ _, Or.inl rfl⟩

lemma E2_mem_F2 {k : ℕ} (hk : k ∈ range (2 * K + 2)) (v : Fin N) :
    iotaT (coef2 (E2_cs N K k) v) ∈ E2_F N K := by
  simp only [E2_F, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
  exact ⟨k, hk, v, Finset.mem_univ _, Or.inr rfl⟩

lemma E2_g8_eq (s : Fin 8 → ℝ) (σ : (Fin 8 → ℝ) → ℝ) :
    g8 N K s σ = ∑ k ∈ range (2 * K + 2), ∑ v,
      (prob (iota s) (E2_cs N K k) v - if v = E2_ys N K k then 1 else 0) •
        E2_D (E2_cs N K k) v σ := by
  unfold g8
  rw [← E2_iotaTL_apply]
  simp only [gInst, gstep, map_sum, map_smul]
  rfl

lemma E2_g8_congr (s : Fin 8 → ℝ) {σ₁ σ₂ : (Fin 8 → ℝ) → ℝ}
    (h : ∀ c ∈ E2_F N K, σ₁ c = σ₂ c) : g8 N K s σ₁ = g8 N K s σ₂ := by
  rw [E2_g8_eq, E2_g8_eq]
  refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun v _ => ?_
  rw [E2_D_congr _ _ (h _ (E2_mem_F1 hk v)) (h _ (E2_mem_F2 hk v))]

lemma E2_g8_lin (s : Fin 8 → ℝ) (a b : ℝ) (σ₁ σ₂ : (Fin 8 → ℝ) → ℝ) :
    g8 N K s (fun x => a * σ₁ x + b * σ₂ x) = a • g8 N K s σ₁ + b • g8 N K s σ₂ := by
  simp only [E2_g8_eq, E2_D_lin, Finset.smul_sum, ← Finset.sum_add_distrib, smul_add]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun v _ => ?_
  rw [smul_comm a, smul_comm b]

lemma E2_g8_norm_le (s : Fin 8 → ℝ) {σ : (Fin 8 → ℝ) → ℝ} (hσ : ∀ x, σ x ∈ Icc (0 : ℝ) 1) :
    ‖g8 N K s σ‖ ≤ ∑ k ∈ range (2 * K + 2), ∑ v, E2_B N K k v := by
  rw [E2_g8_eq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  calc _ ≤ 1 * E2_B N K k v :=
        mul_le_mul (E2_abs_prob_sub_le _ _ _ _) (E2_D_norm_le _ _ hσ) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

lemma E2_g8_sub_norm_le (s s' : Fin 8 → ℝ) {σ : (Fin 8 → ℝ) → ℝ}
    (hσ : ∀ x, σ x ∈ Icc (0 : ℝ) 1) :
    ‖g8 N K s' σ - g8 N K s σ‖ ≤ ∑ k ∈ range (2 * K + 2), ∑ v,
      |prob (iota s') (E2_cs N K k) v - prob (iota s) (E2_cs N K k) v| * E2_B N K k v := by
  rw [E2_g8_eq, E2_g8_eq, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ => ?_)
  rw [← sub_smul, norm_smul, Real.norm_eq_abs]
  refine le_of_eq_of_le ?_ (mul_le_mul_of_nonneg_left (E2_D_norm_le _ _ hσ) (abs_nonneg _))
  congr 2
  ring

end expl

/-! ### Sign selection, scaling, sign stability -/

/-- The sign selection at `s`. -/
def E2_σ0 (s : Fin 8 → ℝ) : (Fin 8 → ℝ) → ℝ := fun c => if 0 < c ⬝ᵥ s then 1 else 0

lemma E2_σ0_sel (s : Fin 8 → ℝ) : Sel8 s (E2_σ0 s) := by
  intro c
  refine ⟨?_, fun h => by simp [E2_σ0, h], fun h => by simp [E2_σ0, not_lt.2 h.le]⟩
  unfold E2_σ0
  split_ifs <;> norm_num

/-- Sum of the learning-rate factors (bounds each of them). -/
def E2_Pm (N : ℕ) : ℝ := ∑ m, |P8 N m|

lemma E2_Pm_nonneg (N : ℕ) : 0 ≤ E2_Pm N := Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma E2_scale_norm_le (α : ℝ) (x : Fin 8 → ℝ) :
    ‖(fun m => -α * P8 N m * x m)‖ ≤ |α| * E2_Pm N * ‖x‖ := by
  have hP := E2_Pm_nonneg N
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun m => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg]
  have h1 : |P8 N m| ≤ E2_Pm N :=
    Finset.single_le_sum (f := fun m => |P8 N m|) (fun _ _ => abs_nonneg _) (Finset.mem_univ m)
  have h2 : |x m| ≤ ‖x‖ := by simpa using norm_le_pi_norm x m
  gcongr

lemma E2_sign_eventually (c s : Fin 8 → ℝ) :
    ∀ᶠ s' in 𝓝 s, (0 < c ⬝ᵥ s → 0 < c ⬝ᵥ s') ∧ (c ⬝ᵥ s < 0 → c ⬝ᵥ s' < 0) := by
  have hc : Continuous fun s' : Fin 8 → ℝ => c ⬝ᵥ s' := by
    simp only [dotProduct]
    fun_prop
  refine Filter.Eventually.and ?_ ?_
  · by_cases h : 0 < c ⬝ᵥ s
    · exact ((hc.tendsto s).eventually (lt_mem_nhds h)).mono fun s' hs' _ => hs'
    · exact Filter.Eventually.of_forall fun s' h' => absurd h' h
  · by_cases h : c ⬝ᵥ s < 0
    · exact ((hc.tendsto s).eventually (gt_mem_nhds h)).mono fun s' hs' _ => hs'
    · exact Filter.Eventually.of_forall fun s' h' => absurd h' h

/-! ### The six statements -/

section V8props
variable [NeZero N]

theorem V8_nonempty (α : ℝ) (s : Fin 8 → ℝ) : (V8 N K α s).Nonempty :=
  ⟨_, E2_σ0 s, E2_σ0_sel s, rfl⟩



theorem V8_convex (α : ℝ) (s : Fin 8 → ℝ) : Convex ℝ (V8 N K α s) := by
  rintro _ ⟨σ₁, h₁, rfl⟩ _ ⟨σ₂, h₂, rfl⟩ a b ha hb hab
  refine ⟨fun x => a * σ₁ x + b * σ₂ x, fun c => ⟨⟨?_, ?_⟩, fun hc => ?_, fun hc => ?_⟩, ?_⟩
  · exact add_nonneg (mul_nonneg ha (h₁ c).1.1) (mul_nonneg hb (h₂ c).1.1)
  · have e1 := mul_le_mul_of_nonneg_left (h₁ c).1.2 ha
    have e2 := mul_le_mul_of_nonneg_left (h₂ c).1.2 hb
    linarith
  · show a * σ₁ c + b * σ₂ c = 1
    rw [(h₁ c).2.1 hc, (h₂ c).2.1 hc]; linarith
  · show a * σ₁ c + b * σ₂ c = 0
    rw [(h₁ c).2.2 hc, (h₂ c).2.2 hc]; ring
  · rw [E2_g8_lin]
    funext m
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring



theorem V8_closed (α : ℝ) (s : Fin 8 → ℝ) : IsClosed (V8 N K α s) := by
  classical
  let F := E2_F N K
  let J : F → Set ℝ := fun c =>
    {x | x ∈ Icc (0 : ℝ) 1 ∧ (0 < c.1 ⬝ᵥ s → x = 1) ∧ (c.1 ⬝ᵥ s < 0 → x = 0)}
  let ext : (F → ℝ) → (Fin 8 → ℝ) → ℝ := fun τ c => if h : c ∈ F then τ ⟨c, h⟩ else E2_σ0 s c
  let G : (F → ℝ) → (Fin 8 → ℝ) := fun τ m => -α * P8 N m * g8 N K s (ext τ) m
  have hcl : ∀ (P : Prop) (r : ℝ), IsClosed {x : ℝ | P → x = r} := by
    intro P r
    by_cases hP : P
    · simp [hP]
    · simp [hP]
  have hJ : ∀ c, IsCompact (J c) := fun c =>
    isCompact_Icc.of_isClosed_subset (isClosed_Icc.inter ((hcl _ _).inter (hcl _ _)))
      fun x hx => hx.1
  have hext : ∀ c (h : c ∈ F) τ, ext τ c = τ ⟨c, h⟩ := fun c h τ => by
    simp only [ext, h, ↓reduceDIte]
  have hD : ∀ k ∈ range (2 * K + 2), ∀ v,
      Continuous fun τ => E2_D (E2_cs N K k) v (ext τ) := by
    intro k hk v
    simp only [E2_D_eq, hext _ (E2_mem_F1 hk v), hext _ (E2_mem_F2 hk v)]
    by_cases hv : v = (E2_cs N K k).cur
    · simp only [hv, ↓reduceIte]; exact continuous_const
    · simp only [hv, ↓reduceIte]
      exact ((continuous_apply _).smul continuous_const).add
        ((continuous_apply _).smul continuous_const)
  have hg : Continuous fun τ => g8 N K s (ext τ) := by
    simp only [E2_g8_eq]
    exact continuous_finsetSum _ fun k hk => continuous_finsetSum _ fun v _ =>
      by have := hD k hk v; fun_prop
  have hG : Continuous G :=
    continuous_pi fun m => continuous_const.mul ((continuous_apply m).comp hg)
  have hV : V8 N K α s = G '' Set.pi univ J := by
    ext w
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      refine ⟨fun c => σ c.1, fun c _ => hσ c.1, ?_⟩
      have := E2_g8_congr (N := N) (K := K) s (σ₁ := ext fun c => σ c.1) (σ₂ := σ)
        fun c hc => hext c hc (fun c => σ c.1)
      simp only [G, this]
    · rintro ⟨τ, hτ, rfl⟩
      refine ⟨ext τ, fun c => ?_, rfl⟩
      by_cases hc : c ∈ F
      · rw [hext c hc τ]; exact hτ ⟨c, hc⟩ (mem_univ _)
      · simp only [ext, hc, ↓reduceDIte]; exact E2_σ0_sel s c
  rw [hV]
  exact ((isCompact_univ_pi hJ).image hG).isClosed



theorem V8_bounded (α : ℝ) : ∃ M : ℝ, ∀ s, ∀ w ∈ V8 N K α s, ‖w‖ ≤ M := by
  refine ⟨|α| * E2_Pm N * ∑ k ∈ range (2 * K + 2), ∑ v, E2_B N K k v, ?_⟩
  rintro s _ ⟨σ, hσ, rfl⟩
  refine (E2_scale_norm_le α _).trans ?_
  have := E2_Pm_nonneg N
  gcongr
  exact E2_g8_norm_le s fun x => (hσ x).1



theorem V8_usc (α : ℝ) (s : Fin 8 → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s', ‖s' - s‖ < δ → ∀ w ∈ V8 N K α s', ∃ w' ∈ V8 N K α s, ‖w - w'‖ < ε := by
  classical
  have hP := E2_Pm_nonneg N
  set C := |α| * E2_Pm N + 1 with hC
  have hC0 : 0 < C := by positivity
  let Φ : (Fin 8 → ℝ) → ℝ := fun s' => ∑ k ∈ range (2 * K + 2), ∑ v,
      |prob (iota s') (E2_cs N K k) v - prob (iota s) (E2_cs N K k) v| * E2_B N K k v
  have hΦc : Continuous Φ := continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun v _ =>
    (((E2_prob_continuous _ v).sub continuous_const).abs).mul continuous_const
  have hΦ0 : Φ s = 0 := by simp [Φ]
  have hΦnn : ∀ s', 0 ≤ Φ s' := fun s' =>
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun v _ =>
      mul_nonneg (abs_nonneg _) (by unfold E2_B; positivity)
  have h1 : ∀ᶠ s' in 𝓝 s, Φ s' < ε / C :=
    (hΦc.tendsto s).eventually (gt_mem_nhds (by rw [hΦ0]; positivity))
  have h2 : ∀ᶠ s' in 𝓝 s, ∀ c ∈ E2_F N K,
      (0 < c ⬝ᵥ s → 0 < c ⬝ᵥ s') ∧ (c ⬝ᵥ s < 0 → c ⬝ᵥ s' < 0) :=
    (eventually_all_finset _).2 fun c _ => E2_sign_eventually c s
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 (h1.and h2)
  refine ⟨δ, hδ, fun s' hs' w hw => ?_⟩
  obtain ⟨hΦs', hsign⟩ := hδ' (by rwa [dist_eq_norm])
  obtain ⟨σ', hσ', rfl⟩ := hw
  let σ : (Fin 8 → ℝ) → ℝ := fun c =>
    if 0 < c ⬝ᵥ s then 1 else if c ⬝ᵥ s < 0 then 0 else σ' c
  have hσ : Sel8 s σ := by
    intro c
    refine ⟨?_, fun h => by simp [σ, h], fun h => by simp [σ, h, not_lt.2 h.le]⟩
    simp only [σ]
    split_ifs
    · norm_num
    · norm_num
    · exact (hσ' c).1
  have hagree : ∀ c ∈ E2_F N K, σ c = σ' c := by
    intro c hc
    simp only [σ]
    split_ifs with h h'
    · exact ((hσ' c).2.1 ((hsign c hc).1 h)).symm
    · exact ((hσ' c).2.2 ((hsign c hc).2 h')).symm
    · rfl
  refine ⟨_, ⟨σ, hσ, rfl⟩, ?_⟩
  rw [E2_g8_congr s hagree]
  have hsub : ((fun m => -α * P8 N m * g8 N K s' σ' m) - fun m => -α * P8 N m * g8 N K s σ' m) =
      fun m => -α * P8 N m * (g8 N K s' σ' - g8 N K s σ') m := by
    funext m
    simp only [Pi.sub_apply]
    ring
  rw [hsub]
  calc _ ≤ |α| * E2_Pm N * ‖g8 N K s' σ' - g8 N K s σ'‖ := E2_scale_norm_le _ _
    _ ≤ |α| * E2_Pm N * Φ s' := by
        gcongr
        exact E2_g8_sub_norm_le s s' fun x => (hσ' x).1
    _ ≤ C * Φ s' := by
        have := hΦnn s'
        gcongr
        linarith
    _ < C * (ε / C) := by gcongr
    _ = ε := by field_simp



/-- The eight-scalar gradient flow has a (global, Filippov) solution from every initial point. -/
theorem exists_IsSol8 (α : ℝ) (s0 : Fin 8 → ℝ) : ∃ s, IsSol8 N K α s ∧ s 0 = s0 := by
  obtain ⟨M, hM⟩ := DFS.V8_bounded (N := N) (K := K) α
  exact DFS.exists_IsDI (V8 N K α) M (DFS.V8_nonempty α) (DFS.V8_convex α)
    (DFS.V8_closed α) hM (fun x _ hε => DFS.V8_usc α x hε) s0



end V8props

end DFS
