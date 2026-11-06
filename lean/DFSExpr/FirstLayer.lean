import DFSExpr.Defs

noncomputable section

open Matrix

namespace DFSExpr

/-! ## Softmax concentration -/

theorem softmax_gap {T : ℕ} (s : Fin T → ℝ) (j0 : Fin T) (g : ℝ)
    (hg : ∀ j, j ≠ j0 → s j + g ≤ s j0) :
    1 - ((T : ℝ) - 1) * Real.exp (-g) ≤ softmaxW s j0 := by
  have hT : 1 ≤ T := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; exact j0.elim0)
  set e0 := Real.exp (s j0) with he0
  have he0p : 0 < e0 := Real.exp_pos _
  set x := ((T : ℝ) - 1) * Real.exp (-g) with hx
  have hx0 : 0 ≤ x := by
    have : (1 : ℝ) ≤ T := by exact_mod_cast hT
    have := Real.exp_pos (-g)
    positivity
  set S := ∑ k, Real.exp (s k) with hS
  have hSpos : 0 < S := by
    apply Finset.sum_pos (fun k _ => Real.exp_pos _) ⟨j0, Finset.mem_univ _⟩
  have hSle : S ≤ e0 * (1 + x) := by
    rw [hS, ← Finset.add_sum_erase _ _ (Finset.mem_univ j0)]
    have hle : ∑ k ∈ Finset.univ.erase j0, Real.exp (s k) ≤
        ∑ k ∈ Finset.univ.erase j0, e0 * Real.exp (-g) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' : k ≠ j0 := Finset.ne_of_mem_erase hk
      rw [he0, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith [hg k hk'])
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub hT, Nat.cast_one] at hle
    rw [hx]
    nlinarith
  unfold softmaxW
  rw [← hS, ← he0, le_div_iff₀ hSpos]
  by_cases h1 : 1 - x ≤ 0
  · nlinarith
  · replace h1 := not_le.mp h1
    calc (1 - x) * S ≤ (1 - x) * (e0 * (1 + x)) := mul_le_mul_of_nonneg_left hSle h1.le
      _ = e0 * (1 - x ^ 2) := by ring
      _ ≤ e0 := by nlinarith


/-! ## Positional selector -/

theorem pos_selector (L T : ℕ) (hT : T ≤ L) (δ β : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hβ : 8 * (L : ℝ) ^ 2 * Real.log (L / δ) ≤ β) (j0 : Fin T) (e : ℕ)
    (he : e = 0 ∨ (e = 1 ∧ (j0 : ℕ) = 0)) :
    1 - δ ≤ softmaxW (fun j : Fin T => β * Real.cos (((j : ℝ) - j0 + e) * posAngle L)) j0 := by
  have hT1 : 1 ≤ T := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; exact j0.elim0)
  have hL1 : 1 ≤ L := le_trans hT1 hT
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hTL : (T : ℝ) ≤ L := by exact_mod_cast hT
  have hT1r : (1 : ℝ) ≤ T := by exact_mod_cast hT1
  set α := posAngle L with hα
  have hαpos : 0 < α := by rw [hα, posAngle]; positivity
  have hαL : α * L = Real.pi / 4 := by
    rw [hα, posAngle]; field_simp
  have hLδ : 1 < (L : ℝ) / δ := by rw [one_lt_div hδ]; linarith
  have hlog : 0 < Real.log (L / δ) := Real.log_pos hLδ
  have hβ0 : 0 ≤ β := le_trans (by positivity) hβ
  set c := Real.cos α with hc
  -- `1 - cos α ≥ 1 / (8 L²)`
  have hcα : c ≤ 1 - 2 / Real.pi ^ 2 * α ^ 2 := by
    apply Real.cos_le_one_sub_mul_cos_sq
    rw [abs_of_pos hαpos]
    nlinarith [Real.pi_pos]
  have hα2 : 2 / Real.pi ^ 2 * α ^ 2 = 1 / (8 * (L : ℝ) ^ 2) := by
    have : α = Real.pi / (4 * L) := hα
    rw [this]; field_simp; ring
  have hgap : Real.log (L / δ) ≤ β * (1 - c) := by
    have h1 : 1 / (8 * (L : ℝ) ^ 2) ≤ 1 - c := by linarith
    calc Real.log (L / δ) = (8 * (L : ℝ) ^ 2 * Real.log (L / δ)) * (1 / (8 * (L : ℝ) ^ 2)) := by
          field_simp
      _ ≤ β * (1 - c) := by
          apply mul_le_mul hβ h1 (by positivity) hβ0
  have hc0 : 0 ≤ c := by
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le <;> nlinarith [Real.pi_pos]
  have hc1 : c ≤ 1 := Real.cos_le_one α
  -- the gap
  have key : ∀ j : Fin T, j ≠ j0 →
      β * Real.cos (((j : ℝ) - j0 + e) * α) + Real.log (L / δ) ≤
        β * Real.cos (((j0 : ℝ) - j0 + e) * α) := by
    intro j hj
    have hjT : (j : ℝ) + 1 ≤ T := by exact_mod_cast j.isLt
    have hj0T : (j0 : ℝ) + 1 ≤ T := by exact_mod_cast j0.isLt
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    have hj00 : (0 : ℝ) ≤ j0 := Nat.cast_nonneg _
    have hne : (j : ℕ) ≠ (j0 : ℕ) := fun h => hj (Fin.ext h)
    rcases he with rfl | ⟨rfl, hj0z⟩
    · simp only [sub_self, Nat.cast_zero, add_zero, zero_mul, Real.cos_zero, mul_one]
      have habs : 1 ≤ |(j : ℝ) - j0| := by
        rcases Nat.lt_or_gt_of_ne hne with h | h
        · have : (j : ℝ) + 1 ≤ j0 := by exact_mod_cast h
          rw [abs_sub_comm]; exact le_abs.mpr (Or.inl (by linarith))
        · have : (j0 : ℝ) + 1 ≤ j := by exact_mod_cast h
          exact le_abs.mpr (Or.inl (by linarith))
      have habs2 : |(j : ℝ) - j0| ≤ L := by
        rw [abs_le]; constructor <;> linarith
      have hcos : Real.cos (((j : ℝ) - j0) * α) ≤ c := by
        rw [← Real.cos_abs, abs_mul, abs_of_pos hαpos]
        apply Real.cos_le_cos_of_nonneg_of_le_pi hαpos.le
        · nlinarith [Real.pi_pos]
        · nlinarith
      nlinarith
    · have hj0z' : (j0 : ℝ) = 0 := by exact_mod_cast hj0z
      have hj1 : (1 : ℝ) ≤ j := by
        have : 1 ≤ (j : ℕ) := by omega
        exact_mod_cast this
      rw [hj0z']
      simp only [sub_zero, Nat.cast_one, zero_add, one_mul]
      have hcos : Real.cos (((j : ℝ) + 1) * α) ≤ Real.cos (2 * α) := by
        apply Real.cos_le_cos_of_nonneg_of_le_pi (by linarith)
        · nlinarith [Real.pi_pos]
        · nlinarith
      rw [Real.cos_two_mul] at hcos
      have h3 : 0 ≤ β * c * (1 - c) := by
        apply mul_nonneg (mul_nonneg hβ0 hc0); linarith
      have h4 : β * Real.cos (((j : ℝ) + 1) * α) ≤ β * (2 * c ^ 2 - 1) :=
        mul_le_mul_of_nonneg_left hcos hβ0
      nlinarith
  have hsel := softmax_gap (fun j : Fin T => β * Real.cos (((j : ℝ) - j0 + e) * α)) j0
    (Real.log (L / δ)) key
  rw [Real.exp_neg, Real.exp_log (by positivity), inv_div] at hsel
  have hfin : ((T : ℝ) - 1) * (δ / L) ≤ δ := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  linarith


variable {N : ℕ}

/-! ## The first layer -/

/-- Scale of the predecessor selector. -/
def B_beta (L : ℕ) (δ : ℝ) : ℝ := 8 * (L : ℝ) ^ 2 * Real.log (L / δ)

/-- Key-query matrix of all three heads: acts on the positional coordinates only. -/
def B_KQ (N : ℕ) (β α : ℝ) : Matrix (Coord2 N) (Coord2 N) ℝ := fun r c =>
  if r = .inr 1 then
    (if c = .inr 1 then β * Real.cos α else if c = .inr 2 then β * Real.sin α else 0)
  else if r = .inr 2 then
    (if c = .inr 1 then -(β * Real.sin α) else if c = .inr 2 then β * Real.cos α else 0)
  else 0

/-- Source coordinate of the value of head `h` (stored in block 0 of the value space). -/
def B_src (N : ℕ) (h : Fin 3) (v : Fin N) : Coord2 N :=
  if h = 0 then blk 0 v else if h = 1 then blk 3 v else .inr 0

/-- Value matrices. -/
def B_V (N : ℕ) (h : Fin 3) : Matrix (Coord2 N) (Coord2 N) ℝ := fun r c =>
  match r with
  | .inl (b, v) => if b = 0 ∧ c = B_src N h v then 1 else 0
  | .inr _ => 0

/-- Output coefficients: block 1 gets `2 head₀ - head₂`, block 2 gets `2 head₁ - head₂`. -/
def B_coef (b : Fin 4) (h : Fin 3) : ℝ :=
  if b = 1 ∧ h = 0 then 2 else if b = 2 ∧ h = 1 then 2
  else if (b = 1 ∨ b = 2) ∧ h = 2 then -1 else 0

/-- Output matrix. -/
def B_O (N : ℕ) : Matrix (Coord2 N) (Fin 3 × Coord2 N) ℝ := fun r hc =>
  match r with
  | .inl (b, v) => if hc.2 = blk 0 v then B_coef b hc.1 else 0
  | .inr _ => 0

/-- The first layer. -/
def B_layer (N L : ℕ) (δ : ℝ) : Layer (Coord2 N) where
  H := 3
  act := Act.softmax
  KQ _ := B_KQ N (B_beta L δ) (posAngle L)
  V := B_V N
  O := B_O N

lemma B_attn {T : ℕ} (A : Matrix (Coord2 N) (Coord2 N) ℝ) (X : Fin T → Coord2 N → ℝ)
    (i j : Fin T) :
    attnW Act.softmax A X i j = softmaxW (fun j => X j ⬝ᵥ (A *ᵥ X i)) j := by
  simp [attnW, Act.softmax, softmaxW]

lemma B_score (N L : ℕ) (β : ℝ) (x y : Coord2 N → ℝ) (i j : ℕ)
    (hx1 : x (.inr 1) = Real.cos (((i : ℝ) + 1) * posAngle L))
    (hx2 : x (.inr 2) = Real.sin (((i : ℝ) + 1) * posAngle L))
    (hy1 : y (.inr 1) = Real.cos (((j : ℝ) + 1) * posAngle L))
    (hy2 : y (.inr 2) = Real.sin (((j : ℝ) + 1) * posAngle L)) :
    y ⬝ᵥ (B_KQ N β (posAngle L) *ᵥ x) = β * Real.cos (((j : ℝ) - i + 1) * posAngle L) := by
  have h : ((j : ℝ) - i + 1) * posAngle L =
      (((j : ℝ) + 1) * posAngle L - ((i : ℝ) + 1) * posAngle L) + posAngle L := by ring
  rw [h, Real.cos_add, Real.cos_sub, Real.sin_sub]
  simp [dotProduct, mulVec, B_KQ, Fintype.sum_sum_type, Fin.sum_univ_three, hx1, hx2, hy1, hy2]
  ring

lemma B_V_apply (h : Fin 3) (x : Coord2 N → ℝ) (v : Fin N) :
    (B_V N h *ᵥ x) (blk 0 v) = x (B_src N h v) := by
  simp [mulVec, dotProduct, B_V]

lemma B_O_inl (F : Fin 3 × Coord2 N → ℝ) (b : Fin 4) (v : Fin N) :
    (B_O N *ᵥ F) (blk b v) = ∑ h, B_coef b h * F (h, blk 0 v) := by
  simp only [mulVec, dotProduct, B_O]
  rw [Fintype.sum_prod_type]
  simp [ite_mul]

lemma B_headOut_apply {T : ℕ} (a : Act) (A V : Matrix (Coord2 N) (Coord2 N) ℝ)
    (X : Fin T → Coord2 N → ℝ) (i : Fin T) (c : Coord2 N) :
    headOut a A V X i c = ∑ j, attnW a A X i j * (V *ᵥ X j) c := by
  simp [headOut, Finset.sum_apply]

lemma B_softmax_nonneg {T : ℕ} (s : Fin T → ℝ) (j : Fin T) : 0 ≤ softmaxW s j :=
  div_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)

lemma B_softmax_sum {T : ℕ} (s : Fin T → ℝ) (j0 : Fin T) : ∑ j, softmaxW s j = 1 := by
  simp only [softmaxW, ← Finset.sum_div]
  exact div_self (ne_of_gt (Finset.sum_pos (fun k _ => Real.exp_pos _) ⟨j0, Finset.mem_univ _⟩))

lemma B_copy {T : ℕ} (P : Fin T → ℝ) (a : Fin T → Fin N → ℝ) (j0 : Fin T) (δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ : δ < 1 / 2) (hP0 : ∀ j, 0 ≤ P j) (hP1 : ∑ j, P j = 1)
    (hPj0 : 1 - δ ≤ P j0) (ha : ∀ j, OneHotOrZero (a j)) :
    ∃ l ∈ Set.Icc (1 - 2 * δ) 1, ∀ v, max (2 * ∑ j, P j * a j v - 1) 0 = l * a j0 v := by
  have ha01 : ∀ j v, 0 ≤ a j v ∧ a j v ≤ 1 := by
    intro j v
    rcases ha j with h | ⟨u, h⟩
    · simp [h]
    · rw [h]
      by_cases hv : v = u
      · subst hv; simp
      · simp [hv]
  have hup : ∀ v, ∑ j, P j * a j v ≤ P j0 * a j0 v + δ := by
    intro v
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j0)]
    have h1 : ∑ j ∈ Finset.univ.erase j0, P j * a j v ≤ ∑ j ∈ Finset.univ.erase j0, P j :=
      Finset.sum_le_sum fun j _ => mul_le_of_le_one_right (hP0 j) (ha01 j v).2
    have h2 : ∑ j ∈ Finset.univ.erase j0, P j = 1 - P j0 := by
      rw [← hP1, ← Finset.add_sum_erase _ _ (Finset.mem_univ j0)]; ring
    linarith
  have hlow : ∀ v, P j0 * a j0 v ≤ ∑ j, P j * a j v := fun v =>
    Finset.single_le_sum (f := fun j => P j * a j v)
      (fun j _ => mul_nonneg (hP0 j) (ha01 j v).1) (Finset.mem_univ j0)
  have hle1 : ∀ v, ∑ j, P j * a j v ≤ 1 := by
    intro v
    calc ∑ j, P j * a j v ≤ ∑ j, P j :=
          Finset.sum_le_sum fun j _ => mul_le_of_le_one_right (hP0 j) (ha01 j v).2
      _ = 1 := hP1
  rcases ha j0 with h | ⟨u, h⟩
  · refine ⟨1, ⟨by linarith, le_rfl⟩, fun v => ?_⟩
    have h1 := hup v
    have h2 : a j0 v = 0 := by rw [h]; rfl
    rw [h2] at h1 ⊢
    rw [max_eq_right (by linarith)]
    ring
  · have hu : a j0 u = 1 := by rw [h]; simp
    refine ⟨2 * ∑ j, P j * a j u - 1, ⟨?_, ?_⟩, fun v => ?_⟩
    · have := hlow u; rw [hu] at this; linarith
    · linarith [hle1 u]
    · by_cases hv : v = u
      · subst hv
        have := hlow v; rw [hu] at this
        rw [hu, max_eq_left (by linarith)]
        ring
      · have h2 : a j0 v = 0 := by rw [h]; simp [hv]
        have h1 := hup v
        rw [h2] at h1 ⊢
        rw [max_eq_right (by linarith)]
        ring

lemma B_apply_eq {L : ℕ} {δ : ℝ} {T : ℕ} (X : Fin T → Coord2 N → ℝ) (i : Fin T)
    (c : Coord2 N) :
    (B_layer N L δ).apply X i c = X i c + max ((B_O N *ᵥ fun hc : Fin 3 × Coord2 N =>
      headOut Act.softmax (B_KQ N (B_beta L δ) (posAngle L)) (B_V N hc.1) X i hc.2) c) 0 :=
  rfl

/-- Block computation of the first layer at a query position `i`. -/
lemma B_out {L : ℕ} {δ : ℝ} {T : ℕ} (X : Fin T → Coord2 N → ℝ)
    (hρ : ∀ j : Fin T, X j (.inr 0) = 1) (i : Fin T) (v : Fin N) :
    let P := softmaxW (fun j => X j ⬝ᵥ (B_KQ N (B_beta L δ) (posAngle L) *ᵥ X i))
    (B_layer N L δ).apply X i (blk 0 v) = X i (blk 0 v) ∧
    (B_layer N L δ).apply X i (blk 3 v) = X i (blk 3 v) ∧
    (B_layer N L δ).apply X i (blk 1 v) =
      X i (blk 1 v) + max (2 * ∑ j, P j * X j (blk 0 v) - 1) 0 ∧
    (B_layer N L δ).apply X i (blk 2 v) =
      X i (blk 2 v) + max (2 * ∑ j, P j * X j (blk 3 v) - 1) 0 := by
  intro P
  have hH : ∀ h : Fin 3, headOut Act.softmax (B_KQ N (B_beta L δ) (posAngle L)) (B_V N h) X i
      (blk 0 v) = ∑ j, P j * X j (B_src N h v) := by
    intro h
    rw [B_headOut_apply]
    simp only [B_attn, B_V_apply]
    rfl
  have h2 : ∑ j, P j * X j (B_src N 2 v) = 1 := by
    simp only [B_src]
    simp only [Fin.reduceEq, ite_false, hρ, mul_one]
    exact B_softmax_sum _ i
  simp only [B_apply_eq, B_O_inl, Fin.sum_univ_three, hH, h2]
  simp [B_coef, B_src]
  constructor <;> ring_nf

theorem first_layer (N L : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 8) (hL : 1 ≤ L) :
    ∃ L1 : Layer (Coord2 N), L1.H = 3 ∧ L1.act = Act.softmax ∧
      (∀ h r c, |L1.KQ h r c| ≤ 8 * (L : ℝ) ^ 2 * Real.log (L / δ) + 2) ∧
      (∀ h r c, |L1.V h r c| ≤ 2) ∧ (∀ r c, |L1.O r c| ≤ 2) ∧
      ∀ (T : ℕ) (X : Fin T → Coord2 N → ℝ), T ≤ L → (∀ i : Fin T, InputShape N L i (X i)) →
        (∀ i : Fin T, (i : ℕ) = 0 → ∀ v, X i (blk 0 v) = 0 ∧ X i (blk 3 v) = 0) →
        CopyProp δ X (L1.apply X) := by
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLδ : 1 < (L : ℝ) / δ := by rw [one_lt_div hδ]; linarith
  have hβ0 : 0 ≤ B_beta L δ := by
    have := Real.log_pos hLδ
    unfold B_beta; positivity
  refine ⟨B_layer N L δ, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro h r c
    show |B_KQ N (B_beta L δ) (posAngle L) r c| ≤ B_beta L δ + 2
    have hc := Real.abs_cos_le_one (posAngle L)
    have hs := Real.abs_sin_le_one (posAngle L)
    have k1 : |B_beta L δ * Real.cos (posAngle L)| ≤ B_beta L δ := by
      rw [abs_mul, abs_of_nonneg hβ0]; nlinarith [abs_nonneg (Real.cos (posAngle L))]
    have k2 : |B_beta L δ * Real.sin (posAngle L)| ≤ B_beta L δ := by
      rw [abs_mul, abs_of_nonneg hβ0]; nlinarith [abs_nonneg (Real.sin (posAngle L))]
    unfold B_KQ
    split_ifs <;> (try simp only [abs_neg, abs_zero]) <;> linarith
  · intro h r c
    show |B_V N h r c| ≤ 2
    unfold B_V
    rcases r with ⟨b, v⟩ | k
    · dsimp only; split_ifs <;> norm_num
    · simp
  · intro r c
    show |B_O N r c| ≤ 2
    unfold B_O
    rcases r with ⟨b, v⟩ | k
    · dsimp only; split_ifs
      · unfold B_coef; split_ifs <;> norm_num
      · simp
    · simp
  · intro T X hT hX h0
    have hρ : ∀ j : Fin T, X j (.inr 0) = 1 := fun j => (hX j).2.2.2.1
    have hscore : ∀ i : Fin T,
        (fun j : Fin T => X j ⬝ᵥ (B_KQ N (B_beta L δ) (posAngle L) *ᵥ X i)) =
          fun j : Fin T => B_beta L δ * Real.cos (((j : ℝ) - i + 1) * posAngle L) := by
      intro i; funext j
      exact B_score N L _ (X i) (X j) i j (hX i).2.2.2.2.1 (hX i).2.2.2.2.2
        (hX j).2.2.2.2.1 (hX j).2.2.2.2.2
    have hoh : ∀ b : Fin 4, (b = 0 ∨ b = 3) → ∀ j : Fin T, OneHotOrZero fun v => X j (blk b v) := by
      rintro b (rfl | rfl) j
      · exact (hX j).1
      · exact (hX j).2.1
    refine ⟨fun i v => ⟨(B_out X hρ i v).1, (B_out X hρ i v).2.1⟩, ?_, ?_⟩
    · -- position 0 attends to itself, whose node blocks are zero
      intro i hi v
      have hsel : 1 - δ ≤ softmaxW (fun j => X j ⬝ᵥ (B_KQ N (B_beta L δ) (posAngle L) *ᵥ X i)) i := by
        rw [hscore i]
        have := pos_selector L T hT δ (B_beta L δ) hδ (by linarith) le_rfl i 1 (Or.inr ⟨rfl, hi⟩)
        simpa using this
      obtain ⟨hb1, hb2⟩ := (hX i).2.2.1 v
      obtain ⟨_, _, hb1', hb2'⟩ := B_out (L := L) (δ := δ) X hρ i v
      rw [hb1', hb2', hb1, hb2]
      obtain ⟨l₁, -, hl₁⟩ := B_copy _ (fun j v => X j (blk 0 v)) i δ hδ.le (by linarith)
        (B_softmax_nonneg _) (B_softmax_sum _ i) hsel (hoh 0 (Or.inl rfl))
      obtain ⟨l₂, -, hl₂⟩ := B_copy _ (fun j v => X j (blk 3 v)) i δ hδ.le (by linarith)
        (B_softmax_nonneg _) (B_softmax_sum _ i) hsel (hoh 3 (Or.inr rfl))
      rw [hl₁ v, hl₂ v, (h0 i hi v).1, (h0 i hi v).2]
      simp
    · intro i j hij
      have hsel : 1 - δ ≤ softmaxW (fun k => X k ⬝ᵥ (B_KQ N (B_beta L δ) (posAngle L) *ᵥ X i)) j := by
        rw [hscore i]
        have := pos_selector L T hT δ (B_beta L δ) hδ (by linarith) le_rfl j 0 (Or.inl rfl)
        have hij' : ((i : ℕ) : ℝ) = (j : ℝ) + 1 := by exact_mod_cast hij
        convert this using 3
        rw [hij']
        push_cast
        ring_nf
      obtain ⟨l₁, hl₁m, hl₁⟩ := B_copy _ (fun j v => X j (blk 0 v)) j δ hδ.le (by linarith)
        (B_softmax_nonneg _) (B_softmax_sum _ i) hsel (hoh 0 (Or.inl rfl))
      obtain ⟨l₂, hl₂m, hl₂⟩ := B_copy _ (fun j v => X j (blk 3 v)) j δ hδ.le (by linarith)
        (B_softmax_nonneg _) (B_softmax_sum _ i) hsel (hoh 3 (Or.inr rfl))
      refine ⟨l₁, l₂, hl₁m, hl₂m, fun v => ?_⟩
      obtain ⟨hb1, hb2⟩ := (hX i).2.2.1 v
      obtain ⟨_, _, hb1', hb2'⟩ := B_out (L := L) (δ := δ) X hρ i v
      rw [hb1', hb2', hb1, hb2, zero_add, zero_add]
      exact ⟨hl₁ v, hl₂ v⟩


end DFSExpr
