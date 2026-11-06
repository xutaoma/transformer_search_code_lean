import DFSLean.Model

/-!
# Package M1: permutation equivariance (Prop. 4.1, Steps 1–4)
-/

noncomputable section

namespace DFS

open Real Finset Filter Topology Set

variable {N K : ℕ}

/-! ### Linearity of the heads in `θ` -/

private lemma M1_bil_add (x : Fin N → ℝ) (M M' : Fin N → Fin N → ℝ) (y : Fin N → ℝ) :
    bil x (M + M') y = bil x M y + bil x M' y := by
  simp only [bil, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

private lemma M1_bil_smul (x : Fin N → ℝ) (r : ℝ) (M : Fin N → Fin N → ℝ) (y : Fin N → ℝ) :
    bil x (r • M) y = r * bil x M y := by
  simp only [bil, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private lemma M1_score1_add (θ θ' : Params N) (x q : Hid N) :
    score1 (θ + θ') x q = score1 θ x q + score1 θ' x q := by
  simp only [score1, Pi.add_apply, M1_bil_add]; ring

private lemma M1_score1_smul (r : ℝ) (θ : Params N) (x q : Hid N) :
    score1 (r • θ) x q = r * score1 θ x q := by
  simp only [score1, Pi.smul_apply, M1_bil_smul]; ring

private lemma M1_score2_add (θ θ' : Params N) (x q : Hid N) :
    score2 (θ + θ') x q = score2 θ x q + score2 θ' x q := by
  simp only [score2, Pi.add_apply, M1_bil_add]; ring

private lemma M1_score2_smul (r : ℝ) (θ : Params N) (x q : Hid N) :
    score2 (r • θ) x q = r * score2 θ x q := by
  simp only [score2, Pi.smul_apply, M1_bil_smul]; ring

/-- Head 1 as a linear map in `θ`. -/
private def M1_h1L (c : Ctx N) : Params N →ₗ[ℝ] (Fin N → ℝ) where
  toFun θ := head1 θ c
  map_add' θ θ' := by
    simp only [head1, M1_score1_add, add_smul, List.sum_map_add]
  map_smul' r θ := by
    simp only [head1, M1_score1_smul, RingHom.id_apply, List.smul_sum, List.map_map,
      Function.comp_def, mul_smul]

private def M1_h2L (c : Ctx N) : Params N →ₗ[ℝ] (Fin N → ℝ) where
  toFun θ := head2 θ c
  map_add' θ θ' := by
    simp only [head2, M1_score2_add, add_smul, List.sum_map_add]
  map_smul' r θ := by
    simp only [head2, M1_score2_smul, RingHom.id_apply, List.smul_sum, List.map_map,
      Function.comp_def, mul_smul]

/-- Basis decomposition of a parameter tensor. -/
private lemma M1_basis (θ : Params N) : θ = ∑ k, ∑ i, ∑ j, θ k i j • bas k i j := by
  funext k' i' j'
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, bas]
  simp [ite_and]

private lemma M1_lin_pair (L : Params N →ₗ[ℝ] (Fin N → ℝ)) (θ : Params N) (v : Fin N) :
    L θ v = pair (fun k i j => L (bas k i j) v) θ := by
  conv_lhs => rw [M1_basis θ]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, pair]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem head1_eq_pair (θ : Params N) (c : Ctx N) (v : Fin N) : head1 θ c v = pair (coef1 c v) θ := by
  exact M1_lin_pair (M1_h1L c) θ v


theorem head2_eq_pair (θ : Params N) (c : Ctx N) (v : Fin N) : head2 θ c v = pair (coef2 c v) θ := by
  exact M1_lin_pair (M1_h2L c) θ v


/-! ### Relabeling of vertices -/

/-- Relabeling of a hidden state: every node block composed with `pm.symm`. -/
private def M1_hp (pm : Equiv.Perm (Fin N)) (x : Hid N) : Hid N := fun b i => x b (pm.symm i)

private lemma M1_oh_perm (pm : Equiv.Perm (Fin N)) (u : Fin N) :
    (fun i => oh u (pm.symm i)) = oh (pm u) := by
  funext i
  simp only [oh, Equiv.symm_apply_eq]

private lemma M1_hp_mk4 (pm : Equiv.Perm (Fin N)) (a b c d : Fin N → ℝ) :
    M1_hp pm (mk4 a b c d) =
      mk4 (fun i => a (pm.symm i)) (fun i => b (pm.symm i)) (fun i => c (pm.symm i))
        (fun i => d (pm.symm i)) := by
  funext k i
  fin_cases k <;> rfl

private lemma M1_hp_zero (pm : Equiv.Perm (Fin N)) : M1_hp pm 0 = 0 := rfl

private lemma M1_zero_comp (pm : Equiv.Perm (Fin N)) :
    (fun i => (0 : Fin N → ℝ) (pm.symm i)) = 0 := rfl

private lemma M1_hidden_perm (pm : Equiv.Perm (Fin N)) (c : Ctx N) :
    (c.perm pm).hidden = c.hidden.map (M1_hp pm) := by
  simp only [Ctx.hidden, Ctx.perm, Ctx.nodes, List.map_append, List.map_flatMap, List.flatMap_map,
    List.map_cons, List.map_nil, M1_hp_mk4, M1_oh_perm, M1_zero_comp, List.map_map]
  rw [← List.map_cons, List.zip_map, List.map_map]
  simp only [Prod.map_fst, Prod.map_snd]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  simp only [Function.comp_apply, M1_hp_mk4, M1_oh_perm, M1_zero_comp, Prod.map_fst, Prod.map_snd]

private lemma M1_query_perm (pm : Equiv.Perm (Fin N)) (c : Ctx N) :
    (c.perm pm).query = M1_hp pm c.query := by
  rw [Ctx.query, M1_hidden_perm, List.getLast?_map, ← M1_hp_zero pm, Option.getD_map]
  rfl

private lemma M1_cur_perm (pm : Equiv.Perm (Fin N)) (c : Ctx N) :
    (c.perm pm).cur = pm c.cur := by
  simp only [Ctx.cur, Ctx.nodes, Ctx.perm]
  rw [← List.getLast_map (f := pm) (l := c.root :: c.cot) (by simp)]
  simp only [List.map_cons]

private lemma M1_bil_perm (pm : Equiv.Perm (Fin N)) (x : Fin N → ℝ) (M : Fin N → Fin N → ℝ)
    (y : Fin N → ℝ) :
    bil (fun i => x (pm.symm i)) (fun i j => M (pm.symm i) (pm.symm j)) (fun j => y (pm.symm j))
      = bil x M y := by
  unfold bil
  rw [← Equiv.sum_comp pm]
  simp only [Equiv.symm_apply_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp pm]
  simp only [Equiv.symm_apply_apply]

private lemma M1_score1_perm (pm : Equiv.Perm (Fin N)) (θ : Params N) (x q : Hid N) :
    score1 (permP pm θ) (M1_hp pm x) (M1_hp pm q) = score1 θ x q := by
  exact congrArg₂ (· + ·) (M1_bil_perm pm _ _ _) (M1_bil_perm pm _ _ _)

private lemma M1_score2_perm (pm : Equiv.Perm (Fin N)) (θ : Params N) (x q : Hid N) :
    score2 (permP pm θ) (M1_hp pm x) (M1_hp pm q) = score2 θ x q := by
  exact congrArg₂ (· + ·) (M1_bil_perm pm _ _ _) (M1_bil_perm pm _ _ _)

private lemma M1_head1_perm (pm : Equiv.Perm (Fin N)) (θ : Params N) (c : Ctx N) (v : Fin N) :
    head1 (permP pm θ) (c.perm pm) (pm v) = head1 θ c v := by
  simp only [head1, M1_hidden_perm, M1_query_perm, List.map_map, Function.comp_def,
    M1_score1_perm, Pi.list_sum_apply, Pi.smul_apply, smul_eq_mul]
  simp [val1, M1_hp]

private lemma M1_head2_perm (pm : Equiv.Perm (Fin N)) (θ : Params N) (c : Ctx N) (v : Fin N) :
    head2 (permP pm θ) (c.perm pm) (pm v) = head2 θ c v := by
  simp only [head2, M1_hidden_perm, M1_query_perm, List.map_map, Function.comp_def,
    M1_score2_perm, Pi.list_sum_apply, Pi.smul_apply, smul_eq_mul]
  simp [val2, M1_hp]

private lemma M1_bas_perm (pm : Equiv.Perm (Fin N)) (k : Fin 4) (i j : Fin N) :
    bas k i j = permP pm (bas k (pm.symm i) (pm.symm j)) := by
  funext k' a b
  simp only [bas, permP, (Equiv.injective pm.symm).eq_iff]

theorem coef1_perm (pm : Equiv.Perm (Fin N)) (c : Ctx N) (v : Fin N) :
    coef1 (c.perm pm) (pm v) = permP pm (coef1 c v) := by
  funext k i j
  simp only [coef1, permP]
  rw [M1_bas_perm pm k i j, M1_head1_perm]


theorem coef2_perm (pm : Equiv.Perm (Fin N)) (c : Ctx N) (v : Fin N) :
    coef2 (c.perm pm) (pm v) = permP pm (coef2 c v) := by
  funext k i j
  simp only [coef2, permP]
  rw [M1_bas_perm pm k i j, M1_head2_perm]


/-- Step 1: the network is equivariant, `TF(Π X; π·θ) = P_π TF(X; θ)`. -/
theorem logit_perm (pm : Equiv.Perm (Fin N)) (θ : Params N) (c : Ctx N) (v : Fin N) :
    logit (permP pm θ) (c.perm pm) (pm v) = logit θ c v := by
  simp only [logit, M1_cur_perm, M1_query_perm, M1_head1_perm, M1_head2_perm,
    (Equiv.injective pm).eq_iff, M1_hp, Equiv.symm_apply_apply]


theorem prob_perm (pm : Equiv.Perm (Fin N)) (θ : Params N) (c : Ctx N) (v : Fin N) :
    prob (permP pm θ) (c.perm pm) (pm v) = prob θ c v := by
  simp only [prob]
  rw [← Equiv.sum_comp pm]
  simp only [logit_perm]


/-! ### Composition laws -/

private lemma M1_ctx_perm_mul (pm q : Equiv.Perm (Fin N)) (c : Ctx N) :
    c.perm (pm * q) = (c.perm q).perm pm := by
  simp only [Ctx.perm, List.map_map, Equiv.Perm.coe_mul, Prod.map_comp_map]
  rfl

private lemma M1_ctx_perm_one (c : Ctx N) : c.perm 1 = c := by
  cases c
  simp only [Ctx.perm, Equiv.Perm.coe_one, Prod.map_id, List.map_id, id]

private lemma M1_symm_mul_apply (pm q : Equiv.Perm (Fin N)) (i : Fin N) :
    (pm * q).symm i = q.symm (pm.symm i) := by
  rw [Equiv.symm_apply_eq]; simp

private lemma M1_permP_mul (pm q : Equiv.Perm (Fin N)) (θ : Params N) :
    permP (pm * q) θ = permP pm (permP q θ) := by
  funext k i j
  simp only [permP, M1_symm_mul_apply]

private lemma M1_permP_one (θ : Params N) : permP 1 θ = θ := by
  funext k i j
  rfl

private lemma M1_permP_inv_cancel (pm : Equiv.Perm (Fin N)) (θ : Params N) :
    permP pm (permP pm⁻¹ θ) = θ := by
  rw [← M1_permP_mul, mul_inv_cancel, M1_permP_one]

private lemma M1_permP_cancel_inv (pm : Equiv.Perm (Fin N)) (θ : Params N) :
    permP pm⁻¹ (permP pm θ) = θ := by
  rw [← M1_permP_mul, inv_mul_cancel, M1_permP_one]

/-- `permP pm` as a linear map. -/
private def M1_permL (pm : Equiv.Perm (Fin N)) : Params N →ₗ[ℝ] Params N where
  toFun := permP pm
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma M1_permL_apply (pm : Equiv.Perm (Fin N)) (θ : Params N) :
    M1_permL pm θ = permP pm θ := rfl

private lemma M1_pair_perm (pm : Equiv.Perm (Fin N)) (f θ : Params N) :
    pair (permP pm f) (permP pm θ) = pair f θ := by
  unfold pair permP
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Equiv.sum_comp pm]
  simp only [Equiv.symm_apply_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp pm]
  simp only [Equiv.symm_apply_apply]

private lemma M1_permP_iota (pm : Equiv.Perm (Fin N)) (s : Fin 8 → ℝ) :
    permP pm (iota s) = iota s := by
  funext k i j
  fin_cases k <;> simp [permP, iota, sym, (Equiv.injective pm.symm).eq_iff]

private lemma M1_dlogit_perm (pm : Equiv.Perm (Fin N)) (c : Ctx N) (w : Fin N)
    (σ : Params N → ℝ) :
    dlogit (c.perm pm) (pm w) σ = permP pm (dlogit c w (σ ∘ permP pm)) := by
  simp only [dlogit, M1_cur_perm, (Equiv.injective pm).eq_iff, coef1_perm, coef2_perm]
  split_ifs
  · rfl
  · rfl

private lemma M1_gstep_perm (pm : Equiv.Perm (Fin N)) (θ : Params N) (σ : Params N → ℝ)
    (c : Ctx N) (y : Fin N) :
    gstep (permP pm θ) σ (c.perm pm) (pm y) = permP pm (gstep θ (σ ∘ permP pm) c y) := by
  unfold gstep
  rw [← Equiv.sum_comp pm]
  simp only [prob_perm, (Equiv.injective pm).eq_iff, M1_dlogit_perm]
  rw [← M1_permL_apply, map_sum]
  simp only [map_smul, M1_permL_apply]

private lemma M1_sel_perm (pm : Equiv.Perm (Fin N)) (θ : Params N) (σ : Params N → ℝ) :
    Sel (permP pm θ) σ ↔ Sel θ (σ ∘ permP pm) := by
  constructor
  · intro h f
    have := h (permP pm f)
    rw [M1_pair_perm] at this
    exact this
  · intro h f
    have := h (permP pm⁻¹ f)
    rw [← M1_pair_perm pm, M1_permP_inv_cancel] at this
    simpa only [Function.comp_apply, M1_permP_inv_cancel] using this

section M1canon
variable [NeZero N]

private lemma M1_lossInst_mul (pm q : Equiv.Perm (Fin N)) (θ : Params N) :
    lossInst N K (pm * q) (permP pm θ) = lossInst N K q θ := by
  unfold lossInst
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [M1_ctx_perm_mul, Equiv.Perm.mul_apply, prob_perm]

/-- Eq. `loss_equivariance`. -/
theorem lossInst_perm (pm : Equiv.Perm (Fin N)) (θ : Params N) :
    lossInst N K pm (permP pm θ) = lossInst N K 1 θ := by
  simpa using M1_lossInst_mul (K := K) pm 1 θ


/-- Step 2: the averaged loss is invariant. -/
theorem lossTrain_perm (pm : Equiv.Perm (Fin N)) (θ : Params N) :
    lossTrain N K (permP pm θ) = lossTrain N K θ := by
  unfold lossTrain
  rw [← Equiv.sum_comp (Equiv.mulLeft pm)]
  simp only [Equiv.coe_mulLeft, M1_lossInst_mul]


set_option linter.unusedSectionVars false in
/-- Step 3: the fixed points of the action are exactly the eight-scalar family `F`. -/
theorem fixed_iff (θ : Params N) : (∀ pm : Equiv.Perm (Fin N), permP pm θ = θ) ↔ ∃ s, θ = iota s := by
  constructor
  · intro h
    have hinv : ∀ (pm : Equiv.Perm (Fin N)) k x y, θ k (pm x) (pm y) = θ k x y := by
      intro pm k x y
      have := congrFun (congrFun (congrFun (h pm) k) (pm x)) (pm y)
      simpa [permP] using this.symm
    have hdiag : ∀ k (i i' : Fin N), θ k i i = θ k i' i' := by
      intro k i i'
      have := hinv (Equiv.swap i i') k i i
      simpa using this.symm
    have hoff : ∀ k (i j i' j' : Fin N), i ≠ j → i' ≠ j' → θ k i j = θ k i' j' := by
      intro k i j i' j' hij hij'
      have hne : Equiv.swap i i' j ≠ i' := by
        rw [Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
        exact fun h' => hij h'.symm
      have h1 : θ k i j = θ k i' (Equiv.swap i i' j) := by
        rw [← hinv (Equiv.swap i i') k i j, Equiv.swap_apply_left]
      have h2 : θ k i' (Equiv.swap i i' j) = θ k i' j' := by
        rw [← hinv (Equiv.swap (Equiv.swap i i' j) j') k i' (Equiv.swap i i' j),
          Equiv.swap_apply_of_ne_of_ne hne.symm hij', Equiv.swap_apply_left]
      exact h1.trans h2
    classical
    let dg : Fin 4 → ℝ := fun k => if hN : Nonempty (Fin N) then θ k hN.some hN.some else 0
    let od : Fin 4 → ℝ := fun k =>
      if hp : ∃ p : Fin N × Fin N, p.1 ≠ p.2 then θ k hp.choose.1 hp.choose.2 else 0
    have key : ∀ k i j, θ k i j = sym (dg k) (od k) i j := by
      intro k i j
      by_cases hij : i = j
      · subst hij
        have hN : Nonempty (Fin N) := ⟨i⟩
        simp only [sym, ↓reduceIte, dg, hN, dite_true]
        exact hdiag k _ _
      · have hp : ∃ p : Fin N × Fin N, p.1 ≠ p.2 := ⟨(i, j), hij⟩
        simp only [sym, hij, ↓reduceIte, od, hp, dite_true]
        exact hoff k _ _ _ _ hij hp.choose_spec
    refine ⟨![dg 0, od 0, dg 1, od 1, dg 2, od 2, dg 3, od 3], ?_⟩
    funext k i j
    rw [key]
    fin_cases k <;> rfl
  · rintro ⟨s, rfl⟩ pm
    exact M1_permP_iota pm s


/-- Step 4: on `F` the averaged loss equals the loss of one instance. -/
theorem lossTrain_iota (s : Fin 8 → ℝ) : lossTrain N K (iota s) = lossInst N K 1 (iota s) := by
  unfold lossTrain
  have h : ∀ pm : Equiv.Perm (Fin N), lossInst N K pm (iota s) = lossInst N K 1 (iota s) := by
    intro pm
    conv_lhs => rw [← M1_permP_iota pm s]
    exact lossInst_perm pm (iota s)
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]
  have hN : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
  rw [← mul_assoc, one_div_mul_cancel hN, one_mul]


private lemma M1_gInst_mul (pm q : Equiv.Perm (Fin N)) (θ : Params N) (σ : Params N → ℝ) :
    gInst N K (pm * q) (permP pm θ) σ = permP pm (gInst N K q θ (σ ∘ permP pm)) := by
  unfold gInst
  conv_rhs => rw [← M1_permL_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [M1_ctx_perm_mul, Equiv.Perm.mul_apply, M1_gstep_perm, M1_permL_apply]

theorem gInst_perm (pm : Equiv.Perm (Fin N)) (θ : Params N) (σ : Params N → ℝ) :
    gInst N K pm (permP pm θ) σ = permP pm (gInst N K 1 θ (σ ∘ permP pm)) := by
  simpa using M1_gInst_mul (K := K) pm 1 θ σ


private lemma M1_gTrain_perm (pm : Equiv.Perm (Fin N)) (θ : Params N) (σ : Params N → ℝ) :
    gTrain N K (permP pm θ) σ = permP pm (gTrain N K θ (σ ∘ permP pm)) := by
  unfold gTrain
  rw [← Equiv.sum_comp (Equiv.mulLeft pm)]
  simp only [Equiv.coe_mulLeft, M1_gInst_mul]
  rw [← M1_permL_apply, map_smul, map_sum]
  simp only [M1_permL_apply]

/-- Step 3: the generalized gradient is equivariant, `∂L(π·θ) = π·∂L(θ)`. -/
theorem VelM_perm (α : ℝ) (pm : Equiv.Perm (Fin N)) (θ : Params N) :
    VelM N K α (permP pm θ) = permP pm '' VelM N K α θ := by
  ext w
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    refine ⟨-α • gTrain N K θ (σ ∘ permP pm), ⟨σ ∘ permP pm, (M1_sel_perm pm θ σ).1 hσ, rfl⟩, ?_⟩
    rw [M1_gTrain_perm, ← M1_permL_apply, ← M1_permL_apply, map_smul]
  · rintro ⟨w', ⟨τ, hτ, rfl⟩, rfl⟩
    have hτ' : (τ ∘ permP pm⁻¹) ∘ permP pm = τ := by
      funext f
      simp only [Function.comp_apply, M1_permP_cancel_inv]
    refine ⟨τ ∘ permP pm⁻¹, (M1_sel_perm pm θ _).2 (by rw [hτ']; exact hτ), ?_⟩
    rw [M1_gTrain_perm, hτ', ← M1_permL_apply, ← M1_permL_apply, map_smul]


end M1canon

end DFS
