import DFSLean.Equivariance
import DFSLean.GenericDI

/-!
# Package M2: Lemma C.1 and the flow statement of Prop. 4.1
-/

noncomputable section

namespace DFS

open Real Finset Filter Topology Set

variable {N K : ℕ}

/-! ### Entries of `iota` -/

/-- Index of the scalar sitting at entry `(k, i, j)` of `iota s`. -/
private def M2_idx (k : Fin 4) (i j : Fin N) : Fin 8 :=
  ⟨2 * k.val + (if i = j then 0 else 1), by have := k.isLt; split_ifs <;> omega⟩

private lemma M2_iota_apply (s : Fin 8 → ℝ) (k : Fin 4) (i j : Fin N) :
    iota s k i j = s (M2_idx k i j) := by
  fin_cases k <;> by_cases h : i = j <;> simp [iota, sym, M2_idx, h]

private lemma M2_idx_diag (k : Fin 4) (i : Fin N) :
    M2_idx k i i = ⟨2 * k.val, by omega⟩ := by
  ext; simp [M2_idx]

private lemma M2_idx_off (k : Fin 4) (i j : Fin N) (h : i ≠ j) :
    M2_idx k i j = ⟨2 * k.val + 1, by omega⟩ := by
  ext; simp [M2_idx, h]

private lemma M2_idx_perm (pm : Equiv.Perm (Fin N)) (k : Fin 4) (i j : Fin N) :
    M2_idx k (pm i) (pm j) = M2_idx k i j := by
  simp [M2_idx]

/-! ### Pairing with `iota` -/

private lemma M2_pair_iota (f : Params N) (s : Fin 8 → ℝ) : pair f (iota s) = iotaT f ⬝ᵥ s := by
  have h1 : ∀ k i j, f k i j * s (M2_idx k i j) =
      ∑ m, f k i j * (Pi.single m 1 : Fin 8 → ℝ) (M2_idx k i j) * s m := by
    intro k i j
    simp [Pi.single_apply]
  simp only [pair, M2_iota_apply, h1, dotProduct, iotaT, Finset.sum_mul]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]


/-! ### `iotaT` is linear and permutation invariant -/

private def M2_iotaTL : Params N →ₗ[ℝ] (Fin 8 → ℝ) where
  toFun := iotaT
  map_add' f g := by
    ext m; simp only [iotaT, pair, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c f := by
    ext m
    simp only [iotaT, pair, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc,
      RingHom.id_apply]

private lemma M2_iotaTL_apply (f : Params N) : M2_iotaTL f = iotaT f := rfl

private lemma M2_pair_permP (pm : Equiv.Perm (Fin N)) (f θ : Params N) :
    pair (permP pm f) (permP pm θ) = pair f θ := by
  simp only [pair, permP]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Fintype.sum_equiv pm.symm _ _ fun i => ?_
  exact Fintype.sum_equiv pm.symm _ _ fun j => rfl

private lemma M2_permP_iota (pm : Equiv.Perm (Fin N)) (s : Fin 8 → ℝ) :
    permP pm (iota s) = iota s := by
  ext k i j
  simp only [permP, M2_iota_apply, M2_idx_perm]

private lemma M2_iotaT_permP (pm : Equiv.Perm (Fin N)) (f : Params N) :
    iotaT (permP pm f) = iotaT f := by
  ext m
  have := M2_pair_permP pm f (iota (Pi.single m 1))
  rwa [M2_permP_iota] at this

/-! ### Linearity of the permutation action -/

private lemma M2_permP_smul (pm : Equiv.Perm (Fin N)) (c : ℝ) (X : Params N) :
    permP pm (c • X) = c • permP pm X := rfl

private lemma M2_permP_sum (pm : Equiv.Perm (Fin N)) (X : Equiv.Perm (Fin N) → Params N) :
    permP pm (∑ q, X q) = ∑ q, permP pm (X q) := by
  ext k i j; simp [permP, Finset.sum_apply]

private lemma M2_permP_permP (pm q : Equiv.Perm (Fin N)) (X : Params N) :
    permP pm (permP q X) = permP (pm * q) X := by
  ext k i j; simp [permP, Equiv.Perm.mul_def]

/-- The group average of `G` is a fixed point of the action. -/
private lemma M2_avg_fixed (G : Params N) (pm : Equiv.Perm (Fin N)) :
    permP pm ((1 / (N.factorial : ℝ)) • ∑ q : Equiv.Perm (Fin N), permP q G) =
      (1 / (N.factorial : ℝ)) • ∑ q : Equiv.Perm (Fin N), permP q G := by
  rw [M2_permP_smul, M2_permP_sum]
  congr 1
  simp only [M2_permP_permP]
  exact Equiv.sum_comp (Equiv.mulLeft pm) (fun q => permP q G)

/-- Averaging does not change the eight pulled-back scalars. -/
private lemma M2_iotaT_avg (G : Params N) :
    iotaT ((1 / (N.factorial : ℝ)) • ∑ q : Equiv.Perm (Fin N), permP q G) = iotaT G := by
  rw [← M2_iotaTL_apply, map_smul, map_sum]
  simp only [M2_iotaTL_apply, M2_iotaT_permP, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  rw [one_div_mul_cancel (by exact_mod_cast (Nat.factorial_ne_zero N)), one_smul]


/-! ### The pulled-back scalars: trace and off-diagonal sum -/

private lemma M2_iotaT_even (f : Params N) (k : Fin 4) (hm : 2 * k.val < 8) :
    iotaT f ⟨2 * k.val, hm⟩ = ∑ i, f k i i := by
  have key : ∀ k' (i j : Fin N), (M2_idx k' i j = ⟨2 * k.val, hm⟩) ↔ (k' = k ∧ i = j) := by
    intro k' i j
    by_cases hij : i = j
    · simp [M2_idx, hij, Fin.ext_iff]
    · simp only [M2_idx, hij, ite_false, Fin.mk.injEq, and_false, iff_false]
      omega
  simp only [iotaT, pair, M2_iota_apply, Pi.single_apply, key]
  rw [Fintype.sum_eq_single k]
  · simp
  · intro k' hk'; simp [hk']

private lemma M2_iotaT_odd (f : Params N) (k : Fin 4) (hm : 2 * k.val + 1 < 8) :
    iotaT f ⟨2 * k.val + 1, hm⟩ = ∑ i, ∑ j, if i = j then 0 else f k i j := by
  have key : ∀ k' (i j : Fin N), (M2_idx k' i j = ⟨2 * k.val + 1, hm⟩) ↔ (k' = k ∧ i ≠ j) := by
    intro k' i j
    by_cases hij : i = j
    · simp only [M2_idx, hij, ite_true, Fin.mk.injEq, ne_eq, not_true_eq_false, and_false,
        iff_false]
      omega
    · simp [M2_idx, hij, Fin.ext_iff]
  simp only [iotaT, pair, M2_iota_apply, Pi.single_apply, key]
  rw [Fintype.sum_eq_single k]
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : i = j <;> simp [hij]
  · intro k' hk'; simp [hk']

/-- Number of entries carrying the scalar `m`: `N` on the diagonal, `N(N-1)` off it. -/
private def M2_c (N : ℕ) (m : Fin 8) : ℝ :=
  if (m : ℕ) % 2 = 0 then (N : ℝ) else (N : ℝ) * ((N : ℝ) - 1)

private lemma M2_sum_off (i : Fin N) (c : ℝ) :
    ∑ j : Fin N, (if i = j then (0 : ℝ) else c) = ((N : ℝ) - 1) * c := by
  have h : ∀ j : Fin N, (if i = j then (0 : ℝ) else c) = c - if i = j then c else 0 := by
    intro j; split_ifs <;> ring
  simp only [h, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

private lemma M2_iotaT_iota (t : Fin 8 → ℝ) (m : Fin 8) :
    iotaT (iota (N := N) t) m = M2_c N m * t m := by
  obtain ⟨mv, hm⟩ := m
  have hk : mv / 2 < 4 := by omega
  rcases Nat.mod_two_eq_zero_or_one mv with h | h
  · have e : (⟨mv, hm⟩ : Fin 8) = ⟨2 * (⟨mv / 2, hk⟩ : Fin 4).val, by simp; omega⟩ := by
      ext; simp; omega
    rw [e, M2_iotaT_even]
    simp only [M2_iota_apply, M2_idx_diag, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, M2_c]
    simp
  · have e : (⟨mv, hm⟩ : Fin 8) = ⟨2 * (⟨mv / 2, hk⟩ : Fin 4).val + 1, by simp; omega⟩ := by
      ext; simp; omega
    rw [e, M2_iotaT_odd]
    have h2 : ∀ i j : Fin N, (if i = j then 0 else iota t ⟨mv / 2, hk⟩ i j) =
        if i = j then 0 else t ⟨2 * (⟨mv / 2, hk⟩ : Fin 4).val + 1, by simp; omega⟩ := by
      intro i j
      by_cases hij : i = j
      · simp [hij]
      · simp only [hij, ite_false, M2_iota_apply, M2_idx_off _ _ _ hij]
    simp only [h2, M2_sum_off, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, M2_c]
    simp
    ring


/-! ### The instance gradients at a point of `F` -/

private lemma M2_gInst_iota [NeZero N] (pm : Equiv.Perm (Fin N)) (s : Fin 8 → ℝ)
    (σ : (Fin 8 → ℝ) → ℝ) :
    gInst N K pm (iota s) (σ ∘ iotaT) = permP pm (gInst N K 1 (iota s) (σ ∘ iotaT)) := by
  have h := DFS.gInst_perm (K := K) pm (iota s) (σ ∘ iotaT)
  have hσ : (σ ∘ iotaT) ∘ permP pm = σ ∘ iotaT := by
    funext f; simp [M2_iotaT_permP]
  rwa [M2_permP_iota, hσ] at h

private lemma M2_c_ne_zero (hN : 2 ≤ N) (m : Fin 8) : M2_c N m ≠ 0 := by
  have h2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  unfold M2_c
  split_ifs
  · positivity
  · exact mul_ne_zero (by positivity) (by linarith)

private lemma M2_P8_eq (m : Fin 8) : P8 N m = 1 / M2_c N m := by
  unfold P8 M2_c; split_ifs <;> rfl

/-! ### Analytic properties of `iota` -/

private lemma M2_norm_iota_le (x : Fin 8 → ℝ) : ‖iota (N := N) x‖ ≤ ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun k => ?_
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun i => ?_
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun j => ?_
  rw [M2_iota_apply]
  exact norm_le_pi_norm x _

private lemma M2_iota_continuous : Continuous (iota (N := N)) := by
  refine continuous_pi fun k => continuous_pi fun i => continuous_pi fun j => ?_
  simp only [M2_iota_apply]
  exact continuous_apply _

private lemma M2_iota_quot (h : ℝ) (a b w : Fin 8 → ℝ) :
    h⁻¹ • (iota (N := N) a - iota b) - iota w = iota (h⁻¹ • (a - b) - w) := by
  ext k i j
  simp only [Pi.sub_apply, Pi.smul_apply, M2_iota_apply]

/-! ### Main statements -/

section M2
variable [NeZero N]

set_option linter.unusedSectionVars false in
theorem Sel_iota (s : Fin 8 → ℝ) (σ : (Fin 8 → ℝ) → ℝ) (hσ : Sel8 s σ) :
    Sel (iota (N := N) s) (σ ∘ iotaT) := by
  intro f
  simp only [Function.comp_apply, M2_pair_iota]
  exact hσ (iotaT f)


/-- **Lemma C.1.** On `F`, the generalized gradient of the averaged loss is
`(1/N) ∂ℓ/∂a · I + (1/(N(N-1))) ∂ℓ/∂b · E_off` (and likewise for each matrix). -/
theorem gTrain_iota (hN : 2 ≤ N) (s : Fin 8 → ℝ) (σ : (Fin 8 → ℝ) → ℝ) :
    gTrain N K (iota s) (σ ∘ iotaT) = iota (fun m => P8 N m * g8 N K s σ m) := by
  have h1 : gTrain N K (iota s) (σ ∘ iotaT) = (1 / (N.factorial : ℝ)) •
      ∑ q : Equiv.Perm (Fin N), permP q (gInst N K 1 (iota s) (σ ∘ iotaT)) := by
    unfold gTrain
    exact congrArg (fun x : Params N => (1 / (N.factorial : ℝ)) • x)
      (Finset.sum_congr rfl fun q _ => M2_gInst_iota (K := K) q s σ)
  obtain ⟨t, ht⟩ := (DFS.fixed_iff _).1 (M2_avg_fixed (gInst N K 1 (iota s) (σ ∘ iotaT)))
  rw [h1, ht]
  congr 1
  funext m
  have h3 := congrFun (M2_iotaT_avg (gInst N K 1 (iota s) (σ ∘ iotaT))) m
  rw [ht, M2_iotaT_iota] at h3
  rw [M2_P8_eq, show g8 N K s σ m = iotaT (gInst N K 1 (iota s) (σ ∘ iotaT)) m from rfl, ← h3]
  field_simp [M2_c_ne_zero hN m]


private lemma M2_isMatSol (hN : 2 ≤ N) {α : ℝ} {s : ℝ → Fin 8 → ℝ} (hs : IsSol8 N K α s) :
    IsMatSol N K α (fun t => DFS.iota (s t)) := by
  obtain ⟨hc, hd⟩ := hs
  refine ⟨M2_iota_continuous.comp_continuousOn hc, fun t ht ε hε => ?_⟩
  filter_upwards [hd t ht ε hε] with h ⟨w, hw, hlt⟩
  obtain ⟨σ, hσ, rfl⟩ := hw
  refine ⟨DFS.iota (fun m => -α * P8 N m * g8 N K (s t) σ m),
    ⟨σ ∘ iotaT, DFS.Sel_iota _ _ hσ, ?_⟩, ?_⟩
  · rw [DFS.gTrain_iota hN]
    ext k i j
    simp only [Pi.smul_apply, smul_eq_mul, M2_iota_apply]
    ring
  · rw [M2_iota_quot]
    exact (M2_norm_iota_le _).trans_lt hlt

/-- **Prop. 4.1** (flow part): a solution of the eight-scalar flow, embedded in `F`, is a solution
of the full matrix-level gradient flow. -/
theorem IsSol8.iota (hN : 2 ≤ N) {α : ℝ} {s : ℝ → Fin 8 → ℝ} (hs : IsSol8 N K α s) :
    IsMatSol N K α (fun t => iota (s t)) := by
  exact M2_isMatSol hN hs


end M2

end DFS
