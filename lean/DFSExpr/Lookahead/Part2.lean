import DFSExpr.Lookahead.Part1

/-!
# Package E, part 2: the first (softmax) layer
-/

noncomputable section

open Matrix

namespace DFSExpr

variable {N : ℕ}

/-- Scalar coordinates `ρ, χ, ζ, p₁, p₂`. -/
abbrev E_ρ : E_I N := .inr 0
abbrev E_χ : E_I N := .inr 1
abbrev E_ζ : E_I N := .inr 2
abbrev E_p1 : E_I N := .inr 3
abbrev E_p2 : E_I N := .inr 4

/-- Token embedding `Φ ∘ lookFeat`. -/
def E_emb (L : ℕ) : Tok N → Role → ℕ → E_I N → ℝ := fun t r j => E_Phi (lookFeat N L t r j)

section coords

variable (L : ℕ) (toks : List (Tok N × Role)) (j : Fin toks.length)

theorem E_X_a (v : Fin N) :
    embSeq (E_emb L) toks j (.inl (.a, v)) = if E_A toks[j.1]? = some v then 1 else 0 := by
  simp [embSeq, E_emb, E_Phi_apply, E_PhiF, E_lf_a]

theorem E_X_d (v : Fin N) :
    embSeq (E_emb L) toks j (.inl (.d, v)) = if E_D toks[j.1]? = some v then 1 else 0 := by
  simp [embSeq, E_emb, E_Phi_apply, E_PhiF, E_lf_d]

theorem E_X_g (v : Fin N) :
    embSeq (E_emb L) toks j (.inl (.gam, v)) = if E_G toks[j.1]? = some v then 1 else 0 := by
  simp [embSeq, E_emb, E_Phi_apply, E_PhiF, E_lf_g]

theorem E_X_other (B : E_Bk) (hB : B ≠ .a ∧ B ≠ .d ∧ B ≠ .gam) (v : Fin N) :
    embSeq (E_emb L) toks j (.inl (B, v)) = 0 := by
  obtain ⟨h1, h2, h3⟩ := hB
  cases B <;> simp_all [embSeq, E_emb, E_Phi_apply, E_PhiF]

theorem E_X_rho : embSeq (E_emb L) toks j E_ρ = 1 := by
  simp [embSeq, E_emb, E_Phi_apply, E_PhiF, E_lf_rho]

theorem E_X_chi :
    embSeq (E_emb L) toks j E_χ = if ((j : ℕ) + 1) % 3 = 0 then 1 else 0 := by
  simp [embSeq, E_emb, E_Phi_apply, E_PhiF, E_lf_chi]

theorem E_X_zeta :
    embSeq (E_emb L) toks j E_ζ = if E_Z toks[j.1]? = true then 1 else 0 := by
  simp [embSeq, E_emb, E_Phi_apply, E_PhiF, E_lf_zeta]

theorem E_X_p1 :
    embSeq (E_emb L) toks j E_p1 = Real.cos (((j : ℝ) + 1) * posAngle L) := by
  simp [embSeq, E_emb, E_Phi_apply, E_PhiF, E_lf_p1]

theorem E_X_p2 :
    embSeq (E_emb L) toks j E_p2 = Real.sin (((j : ℝ) + 1) * posAngle L) := by
  simp [embSeq, E_emb, E_Phi_apply, E_PhiF, E_lf_p2]

end coords

theorem E_sum_opt (o : Option (Fin N)) :
    ∑ w : Fin N, (if o = some w then (1 : ℝ) else 0) = if o.isSome = true then 1 else 0 := by
  rcases o with _ | x
  · simp
  · simp [Finset.sum_ite_eq]

/-! ### Layer-1 parameters -/

/-- Positional selector sharpness `β = 8 L² log(L/δ)`, `δ = 1/16`. -/
def E_β (L : ℕ) : ℝ := 8 * (L : ℝ) ^ 2 * Real.log (L / (1 / 16))

/-- Goal selector sharpness `log(L/δ)`. -/
def E_βg (L : ℕ) : ℝ := Real.log (L / (1 / 16))

def E_KQP (L : ℕ) : Matrix (E_I N) (E_I N) ℝ :=
  E_lr ![E_e E_p1, E_e E_p2]
      ![(E_β L * Real.cos (posAngle L)) • E_e E_p1 + (E_β L * Real.sin (posAngle L)) • E_e E_p2,
        (-(E_β L * Real.sin (posAngle L))) • E_e E_p1 + (E_β L * Real.cos (posAngle L)) • E_e E_p2]

def E_KQS (L : ℕ) : Matrix (E_I N) (E_I N) ℝ :=
  E_lr ![E_e E_p1, E_e E_p2] ![E_β L • E_e E_p1, E_β L • E_e E_p2]

def E_KQG (L : ℕ) : Matrix (E_I N) (E_I N) ℝ :=
  E_lr (fun _ : Unit => E_sv .gam) (fun _ : Unit => E_βg L • E_e E_ρ)

def E_KQ1 (L : ℕ) : Fin 3 → Matrix (E_I N) (E_I N) ℝ := ![E_KQP L, E_KQS L, E_KQG L]

/-- Values of the predecessor head. -/
def E_V1P : E_Bk → Fin N → E_I N → ℝ
  | .UP, v => (4 : ℝ) • E_e (.inl (.d, v)) - (9 : ℝ) • E_e E_ρ
  | .SP, v => (4 : ℝ) • E_e (.inl (.d, v)) - (9 : ℝ) • E_e E_ρ
  | .UM, v => (4 : ℝ) • E_e (.inl (.d, v)) - (10 : ℝ) • E_e E_ρ
  | .SM, v => (4 : ℝ) • E_e (.inl (.d, v)) - (10 : ℝ) • E_e E_ρ
  | .bP, v => (4 : ℝ) • E_e (.inl (.a, v)) - (5 : ℝ) • E_e E_ρ
  | .bM, v => (4 : ℝ) • E_e (.inl (.a, v)) - (6 : ℝ) • E_e E_ρ
  | _, _ => 0

/-- Values of the self head. -/
def E_V1S : E_Bk → Fin N → E_I N → ℝ
  | .UP, _ => (4 : ℝ) • E_e E_χ + (4 : ℝ) • E_sv .d
  | .SP, _ => (4 : ℝ) • E_e E_χ + (4 : ℝ) • E_sv .d
  | .UM, _ => (4 : ℝ) • E_e E_χ + (4 : ℝ) • E_sv .d
  | .SM, _ => (4 : ℝ) • E_e E_χ + (4 : ℝ) • E_sv .d
  | .VP, v => (4 : ℝ) • E_e (.inl (.d, v)) + (4 : ℝ) • E_e E_χ + (4 : ℝ) • E_sv .d -
      (9 : ℝ) • E_e E_ρ
  | .CP, v => (4 : ℝ) • E_e (.inl (.d, v)) + (4 : ℝ) • E_e E_χ + (4 : ℝ) • E_sv .d -
      (9 : ℝ) • E_e E_ρ
  | .VM, v => (4 : ℝ) • E_e (.inl (.d, v)) + (4 : ℝ) • E_e E_χ + (4 : ℝ) • E_sv .d -
      (10 : ℝ) • E_e E_ρ
  | .CM, v => (4 : ℝ) • E_e (.inl (.d, v)) + (4 : ℝ) • E_e E_χ + (4 : ℝ) • E_sv .d -
      (10 : ℝ) • E_e E_ρ
  | .bP, _ => (4 : ℝ) • E_sv .a
  | .bM, _ => (4 : ℝ) • E_sv .a
  | _, _ => 0

/-- Values of the goal head. -/
def E_V1G : E_Bk → Fin N → E_I N → ℝ
  | .GP, v => (4 : ℝ) • E_e (.inl (.gam, v)) - E_e E_ρ
  | .GM, v => (4 : ℝ) • E_e (.inl (.gam, v)) - (2 : ℝ) • E_e E_ρ
  | _, _ => 0

def E_V1 : Fin 3 → Matrix (E_I N) (E_I N) ℝ := fun h r =>
  match r with
  | .inl (B, v) => ![E_V1P B v, E_V1S B v, E_V1G B v] h
  | .inr _ => 0

/-- The first layer: predecessor, self and goal softmax heads. -/
def E_L1 (L : ℕ) : Layer (E_I N) := E_layer 3 Act.softmax (E_KQ1 L) E_V1

/-! ### Scores -/

section scores

variable (L : ℕ) (toks : List (Tok N × Role))

local notation "X" => embSeq (E_emb L) toks

theorem E_score_pred (i j : Fin toks.length) :
    X j ⬝ᵥ (E_KQ1 L 0 *ᵥ X i) = E_β L * Real.cos (((j : ℝ) - i + 1) * posAngle L) := by
  rw [show E_KQ1 L 0 = (E_KQP L : Matrix (E_I N) (E_I N) ℝ) from rfl, E_KQP, E_lr_score]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    add_dotProduct, smul_dotProduct, E_e_dot, E_X_p1, E_X_p2, smul_eq_mul]
  rw [show ((j : ℝ) - i + 1) * posAngle L =
      ((j : ℝ) + 1) * posAngle L - (((i : ℝ) + 1) * posAngle L - posAngle L) by ring,
    Real.cos_sub, Real.cos_sub, Real.sin_sub]
  ring_nf

theorem E_score_self (i j : Fin toks.length) :
    X j ⬝ᵥ (E_KQ1 L 1 *ᵥ X i) = E_β L * Real.cos (((j : ℝ) - i) * posAngle L) := by
  rw [show E_KQ1 L 1 = (E_KQS L : Matrix (E_I N) (E_I N) ℝ) from rfl, E_KQS, E_lr_score]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    smul_dotProduct, E_e_dot, E_X_p1, E_X_p2, smul_eq_mul]
  rw [show ((j : ℝ) - i) * posAngle L =
      ((j : ℝ) + 1) * posAngle L - ((i : ℝ) + 1) * posAngle L by ring, Real.cos_sub]
  ring

theorem E_score_goal (i j : Fin toks.length) :
    X j ⬝ᵥ (E_KQ1 L 2 *ᵥ X i) =
      E_βg L * (if (E_G toks[j.1]?).isSome = true then 1 else 0) := by
  rw [show E_KQ1 L 2 = (E_KQG L : Matrix (E_I N) (E_I N) ℝ) from rfl, E_KQG, E_lr_score]
  simp only [Finset.univ_unique, Finset.sum_singleton, E_sv_dot, smul_dotProduct, E_e_dot,
    E_X_rho, E_X_g, E_sum_opt, smul_eq_mul]
  ring

end scores

/-! ### Softmax averages -/

theorem E_smw_nonneg {T : ℕ} (s : Fin T → ℝ) (j : Fin T) : 0 ≤ softmaxW s j :=
  div_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun k _ => (Real.exp_pos _).le)

theorem E_smw_sum {T : ℕ} (s : Fin T → ℝ) (j0 : Fin T) : ∑ j, softmaxW s j = 1 := by
  have hpos : 0 < ∑ k, Real.exp (s k) :=
    Finset.sum_pos (fun k _ => Real.exp_pos _) ⟨j0, Finset.mem_univ _⟩
  simp only [softmaxW, ← Finset.sum_div]
  exact div_self hpos.ne'

theorem E_avg {T : ℕ} (w f : Fin T → ℝ) (j0 : Fin T) (δ lo hi : ℝ) (hw0 : ∀ j, 0 ≤ w j)
    (hw1 : ∑ j, w j = 1) (hsel : 1 - δ ≤ w j0) (hf : ∀ j, lo ≤ f j ∧ f j ≤ hi) :
    |∑ j, w j * f j - f j0| ≤ δ * (hi - lo) := by
  have e1 : ∑ j, w j * f j - f j0 = ∑ j, w j * (f j - f j0) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
  rw [e1]
  have hlohi : lo ≤ hi := (hf j0).1.trans (hf j0).2
  have key : ∀ j, |w j * (f j - f j0)| ≤
      (hi - lo) * w j - (if j = j0 then (hi - lo) * w j0 else 0) := by
    intro j
    by_cases hj : j = j0
    · subst hj; simp
    · simp only [hj, ↓reduceIte, sub_zero, abs_mul, abs_of_nonneg (hw0 j)]
      have h1 : |f j - f j0| ≤ hi - lo :=
        abs_sub_le_iff.2 ⟨by linarith [hf j, hf j0], by linarith [hf j, hf j0]⟩
      have := mul_le_mul_of_nonneg_left h1 (hw0 j)
      linarith
  calc |∑ j, w j * (f j - f j0)| ≤ ∑ j, |w j * (f j - f j0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ((hi - lo) * w j - if j = j0 then (hi - lo) * w j0 else 0) :=
        Finset.sum_le_sum fun j _ => key j
    _ = (hi - lo) * 1 - (hi - lo) * w j0 := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hw1, Finset.sum_ite_eq']
        simp
    _ ≤ δ * (hi - lo) := by nlinarith

/-- A softmax head whose values at the selected position `j0` are approximated. -/
theorem E_head_approx {T : ℕ} (s f : Fin T → ℝ) (j0 : Fin T) (lo hi : ℝ)
    (hsel : 1 - 1 / 16 ≤ softmaxW s j0) (hf : ∀ j, lo ≤ f j ∧ f j ≤ hi) :
    |∑ j, softmaxW s j * f j - f j0| ≤ 1 / 16 * (hi - lo) :=
  E_avg _ f j0 _ lo hi (E_smw_nonneg s) (E_smw_sum s j0) hsel hf

theorem E_head_shift {T : ℕ} (s f f' : Fin T → ℝ) (j0 : Fin T) (hf : ∀ j, f' j = f j - 1) :
    ∑ j, softmaxW s j * f' j = ∑ j, softmaxW s j * f j - 1 := by
  simp only [hf, mul_sub, mul_one, Finset.sum_sub_distrib, E_smw_sum s j0]

/-! ### Selection -/

section select

variable (L : ℕ) (toks : List (Tok N × Role))

local notation "X" => embSeq (E_emb L) toks

theorem E_sel_pred (hT : toks.length ≤ L) (i : Fin toks.length) :
    1 - 1 / 16 ≤ softmaxW (fun j => X j ⬝ᵥ (E_KQ1 L 0 *ᵥ X i)) ⟨i - 1, by omega⟩ := by
  have hs : (fun j => X j ⬝ᵥ (E_KQ1 L 0 *ᵥ X i)) =
      fun j : Fin toks.length => E_β L * Real.cos (((j : ℝ) - i + 1) * posAngle L) :=
    funext fun j => E_score_pred L toks i j
  rw [hs]
  rcases Nat.eq_zero_or_pos i.1 with h0 | hpos
  · have := pos_selector L toks.length hT (1 / 16) (E_β L) (by norm_num) (by norm_num)
      le_rfl ⟨i - 1, by omega⟩ 1 (Or.inr ⟨rfl, by simp [h0]⟩)
    convert this using 4 with j
    simp [h0]
  · have := pos_selector L toks.length hT (1 / 16) (E_β L) (by norm_num) (by norm_num)
      le_rfl ⟨i - 1, by omega⟩ 0 (Or.inl rfl)
    convert this using 4 with j
    have : ((i.1 - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    simp only [this, Nat.cast_zero, add_zero]
    ring

theorem E_sel_self (hT : toks.length ≤ L) (i : Fin toks.length) :
    1 - 1 / 16 ≤ softmaxW (fun j => X j ⬝ᵥ (E_KQ1 L 1 *ᵥ X i)) i := by
  have hs : (fun j => X j ⬝ᵥ (E_KQ1 L 1 *ᵥ X i)) =
      fun j : Fin toks.length => E_β L * Real.cos (((j : ℝ) - i) * posAngle L) :=
    funext fun j => E_score_self L toks i j
  rw [hs]
  have := pos_selector L toks.length hT (1 / 16) (E_β L) (by norm_num) (by norm_num)
      le_rfl i 0 (Or.inl rfl)
  convert this using 4 with j
  simp

theorem E_sel_goal (hL : 1 ≤ L) (hT : toks.length ≤ L) (g : Fin N) (jg : Fin toks.length)
    (hg : ∀ j : Fin toks.length, E_G toks[j.1]? = if j = jg then some g else none)
    (i : Fin toks.length) :
    1 - 1 / 16 ≤ softmaxW (fun j => X j ⬝ᵥ (E_KQ1 L 2 *ᵥ X i)) jg := by
  have hs : (fun j => X j ⬝ᵥ (E_KQ1 L 2 *ᵥ X i)) =
      fun j : Fin toks.length => if j = jg then E_βg L else 0 := by
    funext j
    rw [E_score_goal, hg j]
    split_ifs <;> simp_all
  rw [hs]
  have hgap := softmax_gap (fun j : Fin toks.length => if j = jg then E_βg L else 0) jg
    (E_βg L) (fun j hj => by simp [hj])
  refine le_trans ?_ hgap
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hexp : Real.exp (-E_βg L) = ((L : ℝ) / (1 / 16))⁻¹ := by
    rw [E_βg, Real.exp_neg, Real.exp_log (by positivity)]
  rw [hexp]
  have hT' : (toks.length : ℝ) ≤ L := by exact_mod_cast hT
  have : ((toks.length : ℝ) - 1) * ((L : ℝ) / (1 / 16))⁻¹ ≤ 1 / 16 := by
    rw [show ((L : ℝ) / (1 / 16))⁻¹ = 1 / (16 * L) by field_simp]
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

end select

/-! ### Decoding pairs -/

theorem E_decode (Y x : E_I N → ℝ) (rP rM : E_I N) (zP zM e : ℝ) (hYP : Y rP = x rP + max zP 0)
    (hYM : Y rM = x rM + max zM 0) (hxP : x rP = 0) (hxM : x rM = 0) (hzM : zM = zP - 1)
    (hz : |zP - e| ≤ 3 / 4) (b : Prop) [Decidable b] (hb : b → e = 3) (hnb : ¬b → e ≤ -1) :
    Y rP - Y rM = if b then 1 else 0 := by
  rw [hYP, hYM, hxP, hxM, hzM]
  have h := abs_le.1 hz
  split_ifs with hb'
  · have := hb hb'
    rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    ring
  · have := hnb hb'
    rw [max_eq_right (by linarith), max_eq_right (by linarith)]
    ring


/-! ### The first layer at each position -/

@[simp] theorem E_V1_0 (B : E_Bk) (v : Fin N) : E_V1 0 (.inl (B, v)) = E_V1P B v := rfl
@[simp] theorem E_V1_1 (B : E_Bk) (v : Fin N) : E_V1 1 (.inl (B, v)) = E_V1S B v := rfl
@[simp] theorem E_V1_2 (B : E_Bk) (v : Fin N) : E_V1 2 (.inl (B, v)) = E_V1G B v := rfl
@[simp] theorem E_V1_inr (h : Fin 3) (c : Fin 5) : E_V1 h (.inr c : E_I N) = 0 := rfl

theorem E_ind3 (A B C : Prop) [Decidable A] [Decidable B] [Decidable C] (h : ¬(A ∧ B ∧ C)) :
    4 * (if A then (1 : ℝ) else 0) - 9 + (4 * (if C then 1 else 0) + 4 * (if B then 1 else 0))
      ≤ -1 := by
  split_ifs <;> simp_all <;> norm_num

section layer1

variable (L : ℕ) (toks : List (Tok N × Role))

local notation "X" => embSeq (E_emb L) toks

/-- Head output of head `h` of the first layer at position `i`, coordinate `r`. -/
def E_hd1 (i : Fin toks.length) (h : Fin 3) (r : E_I N) : ℝ :=
  ∑ j, softmaxW (fun j => X j ⬝ᵥ (E_KQ1 L h *ᵥ X i)) j * (E_V1 h r ⬝ᵥ X j)

theorem E_L1_out (i : Fin toks.length) (r : E_I N) :
    (E_L1 L).apply X i r = X i r + max (E_hd1 L toks i 0 r + E_hd1 L toks i 1 r +
      E_hd1 L toks i 2 r) 0 := by
  rw [E_L1, E_layer_apply, Fin.sum_univ_three]
  simp only [E_attn_softmax, E_hd1]

theorem E_hd1_zero (i : Fin toks.length) (h : Fin 3) (r : E_I N) (hr : E_V1 h r = 0) :
    E_hd1 L toks i h r = 0 := by
  simp [E_hd1, hr]

theorem E_L1_frame (i : Fin toks.length) (r : E_I N) (hr : ∀ h, E_V1 h r = 0) :
    (E_L1 L).apply X i r = X i r :=
  E_layer_frame _ _ _ _ X i r hr

theorem E_L1_U (hT : toks.length ≤ L) (i : Fin toks.length) (v : Fin N) :
    (E_L1 L).apply X i (.inl (.UP, v)) - (E_L1 L).apply X i (.inl (.UM, v)) =
      (E_cls toks i).U v := by
  have hP := E_L1_out L toks i (.inl (.UP, v))
  have hM := E_L1_out L toks i (.inl (.UM, v))
  rw [E_hd1_zero L toks i 2 _ rfl, add_zero] at hP hM
  rw [E_cls, E_clsOf_U]
  have hj0 : i.1 - 1 < toks.length := by omega
  have a0 : |E_hd1 L toks i 0 (.inl (.UP, v)) -
      (4 * (if E_D toks[i.1 - 1]? = some v then (1 : ℝ) else 0) - 9)| ≤ 1 / 16 * (-5 - -9) := by
    have h := E_head_approx _ (fun j => E_V1 0 (.inl (.UP, v)) ⬝ᵥ X j) ⟨i - 1, hj0⟩ (-9) (-5)
      (E_sel_pred L toks hT i) (fun j => by
        simp only [E_V1_0, E_V1P, sub_dotProduct, smul_dotProduct, E_e_dot, E_X_d, E_X_rho,
          smul_eq_mul]
        split_ifs <;> norm_num)
    have f0 : E_V1 0 (.inl (.UP, v)) ⬝ᵥ X ⟨i - 1, hj0⟩ =
        4 * (if E_D toks[i.1 - 1]? = some v then (1 : ℝ) else 0) - 9 := by
      simp only [E_V1_0, E_V1P, sub_dotProduct, smul_dotProduct, E_e_dot, E_X_d, E_X_rho,
        smul_eq_mul, mul_one]
    rw [← f0]; exact h
  have a1 : |E_hd1 L toks i 1 (.inl (.UP, v)) -
      (4 * (if (i.1 + 1) % 3 = 0 then (1 : ℝ) else 0) +
        4 * (if (E_D toks[i.1]?).isSome = true then 1 else 0))| ≤ 1 / 16 * (8 - 0) := by
    have h := E_head_approx _ (fun j => E_V1 1 (.inl (.UP, v)) ⬝ᵥ X j) i 0 8
      (E_sel_self L toks hT i) (fun j => by
        simp only [E_V1_1, E_V1S, add_dotProduct, smul_dotProduct, E_e_dot, E_sv_dot, E_X_d,
          E_X_chi, smul_eq_mul, E_sum_opt]
        split_ifs <;> norm_num)
    have f1 : E_V1 1 (.inl (.UP, v)) ⬝ᵥ X i = 4 * (if (i.1 + 1) % 3 = 0 then (1 : ℝ) else 0) +
        4 * (if (E_D toks[i.1]?).isSome = true then 1 else 0) := by
      simp only [E_V1_1, E_V1S, add_dotProduct, smul_dotProduct, E_e_dot, E_sv_dot, E_X_d,
          E_X_chi, smul_eq_mul, E_sum_opt]
    rw [← f1]; exact h
  refine E_decode _ (X i) _ _ _ _
    (4 * (if E_D toks[i.1 - 1]? = some v then (1 : ℝ) else 0) - 9 +
      (4 * (if (i.1 + 1) % 3 = 0 then (1 : ℝ) else 0) +
        4 * (if (E_D toks[i.1]?).isSome = true then 1 else 0)))
    hP hM (E_X_other L toks i _ (by decide) v)
    (E_X_other L toks i _ (by decide) v) ?_ (abs_le.2 ⟨?_, ?_⟩) _ ?_ ?_
  · have e0 : E_hd1 L toks i 0 (.inl (.UM, v)) = E_hd1 L toks i 0 (.inl (.UP, v)) - 1 :=
      E_head_shift _ _ _ i (fun j => by
        simp only [E_V1_0, E_V1P, sub_dotProduct, smul_dotProduct, E_e_dot, E_X_rho,
          smul_eq_mul]
        ring)
    have e1 : E_hd1 L toks i 1 (.inl (.UM, v)) = E_hd1 L toks i 1 (.inl (.UP, v)) := rfl
    rw [e0, e1]; ring
  · linarith [(abs_le.1 a0).1, (abs_le.1 a1).1]
  · linarith [(abs_le.1 a0).2, (abs_le.1 a1).2]
  · rintro ⟨h1, h2, h3⟩
    rw [decide_eq_true_eq] at h3
    simp only [h1, h2, h3, ↓reduceIte]
    norm_num
  · intro hb
    exact E_ind3 _ _ _ fun ⟨h1, h2, h3⟩ => hb ⟨h1, h2, by simpa using h3⟩

theorem E_L1_V (hT : toks.length ≤ L) (i : Fin toks.length) (v : Fin N) :
    (E_L1 L).apply X i (.inl (.VP, v)) - (E_L1 L).apply X i (.inl (.VM, v)) =
      (E_cls toks i).V v := by
  have hP := E_L1_out L toks i (.inl (.VP, v))
  have hM := E_L1_out L toks i (.inl (.VM, v))
  rw [E_hd1_zero L toks i 2 _ rfl, add_zero, E_hd1_zero L toks i 0 _ rfl, zero_add] at hP hM
  rw [E_cls, E_clsOf_V]
  have a1 : |E_hd1 L toks i 1 (.inl (.VP, v)) -
      (4 * (if E_D toks[i.1]? = some v then (1 : ℝ) else 0) +
        4 * (if (i.1 + 1) % 3 = 0 then (1 : ℝ) else 0) +
        4 * (if (E_D toks[i.1]?).isSome = true then 1 else 0) - 9)| ≤ 1 / 16 * (3 - -9) := by
    have h := E_head_approx _ (fun j => E_V1 1 (.inl (.VP, v)) ⬝ᵥ X j) i (-9) 3
      (E_sel_self L toks hT i) (fun j => by
        simp only [E_V1_1, E_V1S, add_dotProduct, sub_dotProduct, smul_dotProduct, E_e_dot,
          E_sv_dot, E_X_d, E_X_chi, E_X_rho, smul_eq_mul, E_sum_opt]
        split_ifs <;> norm_num)
    have f1 : E_V1 1 (.inl (.VP, v)) ⬝ᵥ X i =
        4 * (if E_D toks[i.1]? = some v then (1 : ℝ) else 0) +
        4 * (if (i.1 + 1) % 3 = 0 then (1 : ℝ) else 0) +
        4 * (if (E_D toks[i.1]?).isSome = true then 1 else 0) - 9 := by
      simp only [E_V1_1, E_V1S, add_dotProduct, sub_dotProduct, smul_dotProduct, E_e_dot,
          E_sv_dot, E_X_d, E_X_chi, E_X_rho, smul_eq_mul, E_sum_opt, mul_one]
    rw [← f1]; exact h
  refine E_decode _ (X i) _ _ _ _
    (4 * (if E_D toks[i.1]? = some v then (1 : ℝ) else 0) +
        4 * (if (i.1 + 1) % 3 = 0 then (1 : ℝ) else 0) +
        4 * (if (E_D toks[i.1]?).isSome = true then 1 else 0) - 9)
    hP hM (E_X_other L toks i _ (by decide) v)
    (E_X_other L toks i _ (by decide) v) ?_ (abs_le.2 ⟨?_, ?_⟩) _ ?_ ?_
  · exact E_head_shift _ _ _ i (fun j => by
        simp only [E_V1_1, E_V1S, add_dotProduct, sub_dotProduct, smul_dotProduct, E_e_dot,
          E_X_rho, smul_eq_mul]
        ring)
  · linarith [(abs_le.1 a1).1]
  · linarith [(abs_le.1 a1).2]
  · rintro ⟨h1, h3⟩
    rw [decide_eq_true_eq] at h3
    simp only [h1, h3, ↓reduceIte, Option.isSome_some]
    norm_num
  · intro hb
    by_cases h1 : E_D toks[i.1]? = some v
    · have h3 : ¬ (i.1 + 1) % 3 = 0 := fun h3 => hb ⟨h1, by simpa using h3⟩
      simp only [h1, h3, ↓reduceIte, Option.isSome_some]
      norm_num
    · simp only [h1, ↓reduceIte]
      split_ifs <;> norm_num

theorem E_L1_b (hT : toks.length ≤ L) (i : Fin toks.length) (v : Fin N) :
    (E_L1 L).apply X i (.inl (.bP, v)) - (E_L1 L).apply X i (.inl (.bM, v)) =
      (E_cls toks i).b v := by
  have hP := E_L1_out L toks i (.inl (.bP, v))
  have hM := E_L1_out L toks i (.inl (.bM, v))
  rw [E_hd1_zero L toks i 2 _ rfl, add_zero] at hP hM
  rw [E_cls, E_clsOf_b]
  have hj0 : i.1 - 1 < toks.length := by omega
  have a0 : |E_hd1 L toks i 0 (.inl (.bP, v)) -
      (4 * (if E_A toks[i.1 - 1]? = some v then (1 : ℝ) else 0) - 5)| ≤ 1 / 16 * (-1 - -5) := by
    have h := E_head_approx _ (fun j => E_V1 0 (.inl (.bP, v)) ⬝ᵥ X j) ⟨i - 1, hj0⟩ (-5) (-1)
      (E_sel_pred L toks hT i) (fun j => by
        simp only [E_V1_0, E_V1P, sub_dotProduct, smul_dotProduct, E_e_dot, E_X_a, E_X_rho,
          smul_eq_mul]
        split_ifs <;> norm_num)
    have f0 : E_V1 0 (.inl (.bP, v)) ⬝ᵥ X ⟨i - 1, hj0⟩ =
        4 * (if E_A toks[i.1 - 1]? = some v then (1 : ℝ) else 0) - 5 := by
      simp only [E_V1_0, E_V1P, sub_dotProduct, smul_dotProduct, E_e_dot, E_X_a, E_X_rho,
        smul_eq_mul, mul_one]
    rw [← f0]; exact h
  have a1 : |E_hd1 L toks i 1 (.inl (.bP, v)) -
      4 * (if (E_A toks[i.1]?).isSome = true then (1 : ℝ) else 0)| ≤ 1 / 16 * (4 - 0) := by
    have h := E_head_approx _ (fun j => E_V1 1 (.inl (.bP, v)) ⬝ᵥ X j) i 0 4
      (E_sel_self L toks hT i) (fun j => by
        simp only [E_V1_1, E_V1S, smul_dotProduct, E_sv_dot, E_X_a, smul_eq_mul, E_sum_opt]
        split_ifs <;> norm_num)
    have f1 : E_V1 1 (.inl (.bP, v)) ⬝ᵥ X i =
        4 * (if (E_A toks[i.1]?).isSome = true then (1 : ℝ) else 0) := by
      simp only [E_V1_1, E_V1S, smul_dotProduct, E_sv_dot, E_X_a, smul_eq_mul, E_sum_opt]
    rw [← f1]; exact h
  refine E_decode _ (X i) _ _ _ _
    (4 * (if E_A toks[i.1 - 1]? = some v then (1 : ℝ) else 0) - 5 +
      4 * (if (E_A toks[i.1]?).isSome = true then (1 : ℝ) else 0))
    hP hM (E_X_other L toks i _ (by decide) v)
    (E_X_other L toks i _ (by decide) v) ?_ (abs_le.2 ⟨?_, ?_⟩) _ ?_ ?_
  · have e0 : E_hd1 L toks i 0 (.inl (.bM, v)) = E_hd1 L toks i 0 (.inl (.bP, v)) - 1 :=
      E_head_shift _ _ _ i (fun j => by
        simp only [E_V1_0, E_V1P, sub_dotProduct, smul_dotProduct, E_e_dot, E_X_rho,
          smul_eq_mul]
        ring)
    have e1 : E_hd1 L toks i 1 (.inl (.bM, v)) = E_hd1 L toks i 1 (.inl (.bP, v)) := rfl
    rw [e0, e1]; ring
  · linarith [(abs_le.1 a0).1, (abs_le.1 a1).1]
  · linarith [(abs_le.1 a0).2, (abs_le.1 a1).2]
  · rintro ⟨h1, h2⟩
    simp only [h1, h2, ↓reduceIte]
    norm_num
  · intro hb
    by_cases h1 : E_A toks[i.1 - 1]? = some v
    · have h2 : ¬ (E_A toks[i.1]?).isSome = true := fun h2 => hb ⟨h2, h1⟩
      simp only [h1, h2, ↓reduceIte]
      norm_num
    · simp only [h1, ↓reduceIte]
      split_ifs <;> norm_num

theorem E_L1_G (hL : 1 ≤ L) (hT : toks.length ≤ L) (g : Fin N) (jg : Fin toks.length)
    (hg : ∀ j : Fin toks.length, E_G toks[j.1]? = if j = jg then some g else none)
    (i : Fin toks.length) (v : Fin N) :
    (E_L1 L).apply X i (.inl (.GP, v)) - (E_L1 L).apply X i (.inl (.GM, v)) =
      if g = v then 1 else 0 := by
  have hP := E_L1_out L toks i (.inl (.GP, v))
  have hM := E_L1_out L toks i (.inl (.GM, v))
  rw [E_hd1_zero L toks i 0 _ rfl, E_hd1_zero L toks i 1 _ rfl, zero_add, zero_add] at hP hM
  have hgj := hg jg
  simp only [↓reduceIte] at hgj
  have a2 : |E_hd1 L toks i 2 (.inl (.GP, v)) -
      (4 * (if g = v then (1 : ℝ) else 0) - 1)| ≤ 1 / 16 * (3 - -1) := by
    have h := E_head_approx _ (fun j => E_V1 2 (.inl (.GP, v)) ⬝ᵥ X j) jg (-1) 3
      (E_sel_goal L toks hL hT g jg hg i) (fun j => by
        simp only [E_V1_2, E_V1G, sub_dotProduct, smul_dotProduct, E_e_dot, E_X_g, E_X_rho,
          smul_eq_mul]
        split_ifs <;> norm_num)
    have f2 : E_V1 2 (.inl (.GP, v)) ⬝ᵥ X jg = 4 * (if g = v then (1 : ℝ) else 0) - 1 := by
      simp only [E_V1_2, E_V1G, sub_dotProduct, smul_dotProduct, E_e_dot, E_X_g, E_X_rho,
        smul_eq_mul, hgj, Option.some.injEq]
    rw [← f2]; exact h
  refine E_decode _ (X i) _ _ _ _ (4 * (if g = v then (1 : ℝ) else 0) - 1)
    hP hM (E_X_other L toks i _ (by decide) v)
    (E_X_other L toks i _ (by decide) v) ?_ (abs_le.2 ⟨?_, ?_⟩) _ ?_ ?_
  · exact E_head_shift _ _ _ i (fun j => by
        simp only [E_V1_2, E_V1G, sub_dotProduct, smul_dotProduct, E_e_dot, E_X_rho,
          smul_eq_mul]
        ring)
  · linarith [(abs_le.1 a2).1]
  · linarith [(abs_le.1 a2).2]
  · intro h; simp only [h, ↓reduceIte]; norm_num
  · intro h; simp only [h, ↓reduceIte]; norm_num

theorem E_L1_S (i : Fin toks.length) (v : Fin N) :
    (E_L1 L).apply X i (.inl (.SP, v)) - (E_L1 L).apply X i (.inl (.SM, v)) =
      (E_L1 L).apply X i (.inl (.UP, v)) - (E_L1 L).apply X i (.inl (.UM, v)) := by
  rw [E_L1_out, E_L1_out, E_L1_out, E_L1_out, E_X_other L toks i .SP (by decide),
    E_X_other L toks i .SM (by decide), E_X_other L toks i .UP (by decide),
    E_X_other L toks i .UM (by decide)]
  rfl

theorem E_L1_C (i : Fin toks.length) (v : Fin N) :
    (E_L1 L).apply X i (.inl (.CP, v)) - (E_L1 L).apply X i (.inl (.CM, v)) =
      (E_L1 L).apply X i (.inl (.VP, v)) - (E_L1 L).apply X i (.inl (.VM, v)) := by
  rw [E_L1_out, E_L1_out, E_L1_out, E_L1_out, E_X_other L toks i .CP (by decide),
    E_X_other L toks i .CM (by decide), E_X_other L toks i .VP (by decide),
    E_X_other L toks i .VM (by decide)]
  rfl

theorem E_L1_frameB (i : Fin toks.length) (B : E_Bk)
    (hB : B = .a ∨ B = .Df ∨ B = .Db ∨ B = .ZP ∨ B = .ZM) (v : Fin N) :
    (E_L1 L).apply X i (.inl (B, v)) = X i (.inl (B, v)) := by
  refine E_L1_frame L toks i _ fun h => ?_
  rcases hB with rfl | rfl | rfl | rfl | rfl <;> fin_cases h <;> rfl

theorem E_L1_frameS (i : Fin toks.length) (c : Fin 5) :
    (E_L1 L).apply X i (.inr c) = X i (.inr c) :=
  E_L1_frame L toks i _ fun _ => rfl

end layer1

end DFSExpr
