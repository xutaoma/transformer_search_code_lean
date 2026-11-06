import DFSLean.Equivariance

/-!
# Package D: the selection gradient is the true derivative at smooth points
-/

noncomputable section

namespace DFS
open Real Finset Filter Topology Set
open DFS

variable {N K : ℕ}

/-! ### The pairing `pairL` -/

lemma D_pairL_apply (f θ : Params N) : pairL f θ = pair f θ := by
  simp [pairL, pair]

lemma D_pair_add_left (f g θ : Params N) : pair (f + g) θ = pair f θ + pair g θ := by
  simp only [pair, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma D_pair_smul_left (a : ℝ) (f θ : Params N) : pair (a • f) θ = a * pair f θ := by
  simp only [pair, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- `pairL` as a linear map in the functional. -/
def D_pairLin : Params N →ₗ[ℝ] (Params N →L[ℝ] ℝ) where
  toFun := pairL
  map_add' f g := ContinuousLinearMap.ext fun θ => by
    simp [D_pairL_apply, D_pair_add_left]
  map_smul' a f := ContinuousLinearMap.ext fun θ => by
    simp [D_pairL_apply, D_pair_smul_left]

lemma D_pairLin_apply (f : Params N) : D_pairLin f = pairL f := rfl

lemma D_pairL_add (f g : Params N) : pairL (f + g) = pairL f + pairL g :=
  map_add D_pairLin f g

lemma D_pairL_smul (a : ℝ) (f : Params N) : pairL (a • f) = a • pairL f :=
  map_smul D_pairLin a f

lemma D_pairL_zero : pairL (0 : Params N) = 0 := map_zero (D_pairLin (N := N))

lemma D_pairL_sum {ι : Type*} (s : Finset ι) (g : ι → Params N) :
    pairL (∑ i ∈ s, g i) = ∑ i ∈ s, pairL (g i) :=
  map_sum D_pairLin g s

lemma D_pair_continuous (f : Params N) : Continuous fun θ => pair f θ :=
  (pairL f).continuous.congr fun θ => D_pairL_apply f θ

/-! ### One ReLU -/

lemma D_relu_hasFDerivAt (f θ : Params N) (σ : Params N → ℝ) (hσ : Sel θ σ)
    (hf : pair f θ ≠ 0) :
    HasFDerivAt (fun θ' => max (pair f θ') 0) (σ f • pairL f) θ := by
  have hc := (D_pair_continuous f).continuousAt (x := θ)
  rcases lt_or_gt_of_ne hf with h | h
  · rw [(hσ f).2.2 h, zero_smul]
    apply (hasFDerivAt_const (0 : ℝ) θ).congr_of_eventuallyEq
    filter_upwards [hc.eventually_lt continuousAt_const h] with θ' hθ'
    exact max_eq_right hθ'.le
  · rw [(hσ f).2.1 h, one_smul]
    apply (pairL f).hasFDerivAt.congr_of_eventuallyEq
    filter_upwards [continuousAt_const.eventually_lt hc h] with θ' hθ'
    rw [max_eq_left hθ'.le, D_pairL_apply]

/-! ### Logits -/

lemma D_logit_hasFDerivAt (θ : Params N) (σ : Params N → ℝ) (hσ : Sel θ σ) (c : Ctx N)
    (v : Fin N) (hv : v ≠ c.cur → head1 θ c v ≠ 0 ∧ head2 θ c v ≠ 0) :
    HasFDerivAt (fun θ' => logit θ' c v) (pairL (dlogit c v σ)) θ := by
  by_cases hvc : v = c.cur
  · have hfun : (fun θ' => logit θ' c v) = fun _ => (0 : ℝ) := by
      funext θ'; simp [logit, hvc]
    rw [hfun]
    simp only [dlogit, ite_true, hvc, D_pairL_zero]
    exact hasFDerivAt_const 0 θ
  · obtain ⟨h1, h2⟩ := hv hvc
    rw [DFS.head1_eq_pair] at h1
    rw [DFS.head2_eq_pair] at h2
    have hfun : (fun θ' => logit θ' c v) = fun θ' =>
        (c.query 2 v + max (pair (coef1 c v) θ') 0) + (c.query 3 v + max (pair (coef2 c v) θ') 0) := by
      funext θ'; simp only [logit, hvc, ite_false, DFS.head1_eq_pair, DFS.head2_eq_pair]
    rw [hfun]
    have hd := ((D_relu_hasFDerivAt _ θ σ hσ h1).const_add (c.query 2 v)).add
      ((D_relu_hasFDerivAt _ θ σ hσ h2).const_add (c.query 3 v))
    convert hd using 1
    simp only [dlogit, hvc, ite_false, D_pairL_add, D_pairL_smul]

/-! ### One cross-entropy step -/

lemma D_step_hasFDerivAt (θ : Params N) (σ : Params N → ℝ) (hσ : Sel θ σ) (c : Ctx N)
    (y : Fin N) (hc : ∀ v, v ≠ c.cur → head1 θ c v ≠ 0 ∧ head2 θ c v ≠ 0) :
    HasFDerivAt (fun θ' => -log (prob θ' c y)) (pairL (gstep θ σ c y)) θ := by
  have : Nonempty (Fin N) := ⟨y⟩
  have hZ : ∀ θ' : Params N, 0 < ∑ w, exp (logit θ' c w) := fun θ' =>
    Finset.sum_pos (fun w _ => exp_pos _) Finset.univ_nonempty
  have hfun : (fun θ' => -log (prob θ' c y)) =
      fun θ' => -logit θ' c y + log (∑ w, exp (logit θ' c w)) := by
    funext θ'
    rw [prob, Real.log_div (exp_pos _).ne' (hZ θ').ne', Real.log_exp]; ring
  rw [hfun]
  have hl : ∀ w, HasFDerivAt (fun θ' => logit θ' c w) (pairL (dlogit c w σ)) θ :=
    fun w => D_logit_hasFDerivAt θ σ hσ c w (hc w)
  have hS : HasFDerivAt (fun θ' => ∑ w, exp (logit θ' c w))
      (∑ w, exp (logit θ c w) • pairL (dlogit c w σ)) θ :=
    HasFDerivAt.fun_sum (u := Finset.univ) (fun w _ => (hl w).exp)
  have hd := (hl y).neg.add (hS.log (hZ θ).ne')
  convert hd using 1
  apply ContinuousLinearMap.ext
  intro θ''
  simp only [gstep, D_pairL_sum, D_pairL_smul, prob]
  simp
  rw [Finset.mul_sum]
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  rw [neg_add_eq_sub]
  congr 1
  exact Finset.sum_congr rfl fun w _ => by ring

/-! ### The embedding `iota` as a continuous linear map -/

/-- `iota` as a linear map. -/
def D_iotaLin : (Fin 8 → ℝ) →ₗ[ℝ] Params N where
  toFun := iota
  map_add' s t := by
    funext k i j
    fin_cases k <;> by_cases h : i = j <;> simp [iota, sym, h]
  map_smul' a s := by
    funext k i j
    fin_cases k <;> by_cases h : i = j <;> simp [iota, sym, h]

/-- `iota` as a continuous linear map. -/
def D_iotaL : (Fin 8 → ℝ) →L[ℝ] Params N := ⟨D_iotaLin, D_iotaLin.continuous_on_pi⟩

lemma D_iotaL_apply (s : Fin 8 → ℝ) : D_iotaL (N := N) s = iota s := rfl

lemma D_pair_iota (f : Params N) (s : Fin 8 → ℝ) : pair f (iota s) = iotaT f ⬝ᵥ s := by
  have h := LinearMap.pi_apply_eq_sum_univ ((pairL f).toLinearMap ∘ₗ D_iotaLin) s
  simp only [LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply] at h
  rw [← D_pairL_apply]
  change pairL f (D_iotaLin s) = _
  rw [h, dotProduct]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hs : (fun j : Fin 8 => if m = j then (1 : ℝ) else 0) = Pi.single m 1 := by
    funext j; simp [Pi.single_apply, eq_comm]
  rw [hs, smul_eq_mul, mul_comm, iotaT, ← D_pairL_apply]
  rfl

lemma D_pairL_comp_iotaL (G : Params N) : (pairL G).comp D_iotaL = dotL (iotaT G) := by
  apply ContinuousLinearMap.ext
  intro w
  simp [D_iotaL_apply, D_pairL_apply, D_pair_iota, dotL, dotProduct]

lemma D_Sel_iota (s : Fin 8 → ℝ) (σ : (Fin 8 → ℝ) → ℝ) (hσ : Sel8 s σ) :
    Sel (iota (N := N) s) (σ ∘ iotaT) := by
  intro f
  simp only [Function.comp_apply, D_pair_iota]
  exact hσ (iotaT f)

/-! ### Main statements -/

section smooth
variable [NeZero N]

theorem lossInst_hasFDerivAt (pm : Equiv.Perm (Fin N)) (θ : Params N) (σ : Params N → ℝ)
    (hσ : Sel θ σ) (hθ : SmoothInst N K pm θ) :
    HasFDerivAt (lossInst N K pm) (pairL (gInst N K pm θ σ)) θ := by
  have h : HasFDerivAt
      (fun θ' => ∑ k ∈ range (2 * K + 2),
        -log (prob θ' ((ctx N K k).perm pm) (pm (ylab N K k))))
      (∑ k ∈ range (2 * K + 2), pairL (gstep θ σ ((ctx N K k).perm pm) (pm (ylab N K k)))) θ :=
    HasFDerivAt.fun_sum fun k hk =>
      D_step_hasFDerivAt θ σ hσ _ _ fun v hv => hθ k (Finset.mem_range.1 hk) v hv
  rw [gInst, D_pairL_sum]
  exact h



theorem lossTrain_hasFDerivAt (θ : Params N) (σ : Params N → ℝ) (hσ : Sel θ σ)
    (hθ : ∀ pm, SmoothInst N K pm θ) :
    HasFDerivAt (lossTrain N K) (pairL (gTrain N K θ σ)) θ := by
  have h : HasFDerivAt (fun θ' => ∑ pm : Equiv.Perm (Fin N), lossInst N K pm θ')
      (∑ pm : Equiv.Perm (Fin N), pairL (gInst N K pm θ σ)) θ :=
    HasFDerivAt.fun_sum fun pm _ => lossInst_hasFDerivAt pm θ σ hσ (hθ pm)
  rw [gTrain, D_pairL_smul, D_pairL_sum]
  exact h.const_mul _



theorem loss8_hasFDerivAt (s : Fin 8 → ℝ) (σ : (Fin 8 → ℝ) → ℝ) (hσ : Sel8 s σ)
    (hs : SmoothInst N K 1 (iota s)) :
    HasFDerivAt (fun s' => lossInst N K 1 (iota s')) (dotL (g8 N K s σ)) s := by
  have hg : HasFDerivAt (lossInst N K 1) (pairL (gInst N K 1 (iota s) (σ ∘ iotaT)))
      (D_iotaL s) := by
    rw [D_iotaL_apply]
    exact lossInst_hasFDerivAt 1 (iota s) (σ ∘ iotaT) (D_Sel_iota s σ hσ) hs
  have h := hg.comp s D_iotaL.hasFDerivAt
  rw [D_pairL_comp_iotaL] at h
  have hf : (fun s' => lossInst N K 1 (iota s')) = lossInst N K 1 ∘ D_iotaL := by
    funext s'; simp only [Function.comp_apply, D_iotaL_apply]
  rw [hf, g8]
  exact h



end smooth

end DFS

