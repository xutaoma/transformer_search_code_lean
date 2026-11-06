import DFSExpr.FirstLayer
import DFSExpr.DFSTrace

noncomputable section

open Matrix

namespace DFSExpr

variable {N : ℕ}

/-! ### Generic computation of the second layer -/

theorem C_apply_eq (c₁ c₂ : ℝ) {T : ℕ} (X2 : Fin T → Coord2 N → ℝ) (i : Fin T) (c : Coord2 N) :
    (layer2 N c₁ c₂).apply X2 i c = X2 i c +
      max (∑ hc : Fin 2 × Coord2 N, (layer2 N c₁ c₂).O c hc *
        headOut Act.linear ((layer2 N c₁ c₂).KQ hc.1) ((layer2 N c₁ c₂).V hc.1) X2 i hc.2) 0 := rfl

theorem C_apply_blk2 (c₁ c₂ : ℝ) {T : ℕ} (X2 : Fin T → Coord2 N → ℝ) (i : Fin T) (u : Fin N) :
    (layer2 N c₁ c₂).apply X2 i (blk 2 u) = X2 i (blk 2 u) +
      max (headOut Act.linear ((layer2 N c₁ c₂).KQ (0 : Fin 2)) ((layer2 N c₁ c₂).V (0 : Fin 2))
        X2 i (blk 0 u)) 0 := by
  rw [C_apply_eq]
  congr 2
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_sum_type, Fin.sum_univ_four]
  simp [layer2]

theorem C_apply_blk3 (c₁ c₂ : ℝ) {T : ℕ} (X2 : Fin T → Coord2 N → ℝ) (i : Fin T) (u : Fin N) :
    (layer2 N c₁ c₂).apply X2 i (blk 3 u) = X2 i (blk 3 u) +
      max (headOut Act.linear ((layer2 N c₁ c₂).KQ (1 : Fin 2)) ((layer2 N c₁ c₂).V (1 : Fin 2))
        X2 i (blk 0 u)) 0 := by
  rw [C_apply_eq]
  congr 2
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_sum_type, Fin.sum_univ_four]
  simp [layer2]

theorem C_V0 (c₁ c₂ : ℝ) (y : Coord2 N → ℝ) (u : Fin N) :
    ((layer2 N c₁ c₂).V (0 : Fin 2) *ᵥ y) (blk 0 u) = y (blk 3 u) - y (blk 0 u) := by
  simp only [layer2, mulVec, dotProduct, Fintype.sum_prod_type,
    Fintype.sum_sum_type, Fin.sum_univ_four]
  simp
  ring

theorem C_V1 (c₁ c₂ : ℝ) (y : Coord2 N → ℝ) (u : Fin N) :
    ((layer2 N c₁ c₂).V (1 : Fin 2) *ᵥ y) (blk 0 u) = y (blk 1 u) - y (blk 0 u) := by
  simp only [layer2, mulVec, dotProduct, Fintype.sum_prod_type,
    Fintype.sum_sum_type, Fin.sum_univ_four]
  simp
  ring

theorem C_KQ0 (c₁ c₂ : ℝ) (y z : Coord2 N → ℝ) :
    y ⬝ᵥ ((layer2 N c₁ c₂).KQ (0 : Fin 2) *ᵥ z) =
      c₁ * (∑ v, y (blk 0 v)) * (∑ v, z (blk 0 v)) + c₁ * ∑ v, y (blk 2 v) * z (blk 0 v) := by
  simp only [layer2, mulVec, dotProduct, Fintype.sum_prod_type,
    Fintype.sum_sum_type, Fin.sum_univ_four]
  simp only [blk]
  simp
  have e2 : ∑ x, y (Sum.inl (2, x)) * (c₁ * z (Sum.inl (0, x))) =
      c₁ * ∑ x, y (Sum.inl (2, x)) * z (Sum.inl (0, x)) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e2, ← Finset.sum_mul, ← Finset.mul_sum]; ring

theorem C_KQ1 (c₁ c₂ : ℝ) (y z : Coord2 N → ℝ) :
    y ⬝ᵥ ((layer2 N c₁ c₂).KQ (1 : Fin 2) *ᵥ z) =
      c₂ * ∑ v, (y (blk 0 v) + y (blk 1 v)) * z (blk 0 v) := by
  simp only [layer2, mulVec, dotProduct, Fintype.sum_prod_type,
    Fintype.sum_sum_type, Fin.sum_univ_four]
  simp only [blk, Finset.mul_sum]
  simp
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring
theorem C_logit_node (Y : Coord2 N → ℝ) (u : Fin N) :
    ∑ c, R2 N c (.node u) * Y c = Y (blk 2 u) + Y (blk 3 u) := by
  simp only [R2, Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_four]
  simp

theorem C_logit_special (Y : Coord2 N → ℝ) (w : Tok N) (hw : ∀ u, w ≠ .node u) :
    ∑ c, R2 N c w * Y c = 0 := by
  cases w with
  | node u => exact absurd rfl (hw u)
  | _ => simp [R2]

/-! ### Positions of the input -/

theorem C_edgeToks_cons (e : Fin N × Fin N) (es : List (Fin N × Fin N)) :
    edgeToks (e :: es) = (.node e.1, .graph) :: (.node e.2, .graph) :: (.sep, .graph) :: edgeToks es := by
  simp [edgeToks]

theorem C_len_edgeToks (es : List (Fin N × Fin N)) : (edgeToks es).length = 3 * es.length := by
  induction es with
  | nil => simp [edgeToks]
  | cons e es ih => rw [C_edgeToks_cons]; simp [ih]; ring

theorem C_edgeToks_get (es : List (Fin N × Fin N)) (i : ℕ) (hi : i < es.length) :
    (edgeToks es)[3 * i]? = some (.node es[i].1, .graph) ∧
    (edgeToks es)[3 * i + 1]? = some (.node es[i].2, .graph) ∧
    (edgeToks es)[3 * i + 2]? = some (.sep, .graph) := by
  induction es generalizing i with
  | nil => simp at hi
  | cons e es ih =>
    rw [C_edgeToks_cons]
    cases i with
    | zero => simp
    | succ i =>
      have hi' : i < es.length := by simpa using hi
      obtain ⟨h1, h2, h3⟩ := ih i hi'
      refine ⟨?_, ?_, ?_⟩
      · rw [show 3 * (i + 1) = 3 * i + 1 + 1 + 1 by ring]; simpa using h1
      · rw [show 3 * (i + 1) + 1 = 3 * i + 1 + 1 + 1 + 1 by ring]; simpa using h2
      · rw [show 3 * (i + 1) + 2 = 3 * i + 2 + 1 + 1 + 1 by ring]; simpa using h3

theorem C_len (es : List (Fin N × Fin N)) (tgt : Fin N) (τ : List (Fin N)) :
    (dfsInput es tgt τ).length = 3 * es.length + 3 + τ.length := by
  simp [dfsInput, C_len_edgeToks]; ring

theorem C_tok_bos (es : List (Fin N × Fin N)) (tgt : Fin N) (τ : List (Fin N)) :
    (dfsInput es tgt τ)[0]? = some (.bos, .graph) := by
  simp [dfsInput]

theorem C_dfsInput_assoc (es : List (Fin N × Fin N)) (tgt : Fin N) (τ : List (Fin N)) :
    dfsInput es tgt τ = (Tok.bos, Role.graph) :: (edgeToks es ++
      ((Tok.node tgt, Role.goal) :: (Tok.rsn, Role.goal) :: τ.map fun v => (.node v, .trace))) := by
  simp [dfsInput]

theorem C_tok_edge (es : List (Fin N × Fin N)) (tgt : Fin N) (τ : List (Fin N)) (i : ℕ)
    (hi : i < es.length) :
    (dfsInput es tgt τ)[3 * i + 1]? = some (.node es[i].1, .graph) ∧
    (dfsInput es tgt τ)[3 * i + 2]? = some (.node es[i].2, .graph) ∧
    (dfsInput es tgt τ)[3 * i + 3]? = some (.sep, .graph) := by
  obtain ⟨h1, h2, h3⟩ := C_edgeToks_get es i hi
  have hl := C_len_edgeToks es
  rw [C_dfsInput_assoc]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.getElem?_cons_succ, List.getElem?_append_left (by omega)]; exact h1
  · rw [show 3 * i + 2 = (3 * i + 1) + 1 by ring, List.getElem?_cons_succ,
      List.getElem?_append_left (by omega)]; exact h2
  · rw [show 3 * i + 3 = (3 * i + 2) + 1 by ring, List.getElem?_cons_succ,
      List.getElem?_append_left (by omega)]; exact h3

theorem C_tok_tail (es : List (Fin N × Fin N)) (tgt : Fin N) (τ : List (Fin N)) (k : ℕ) :
    (dfsInput es tgt τ)[3 * es.length + 1 + k]? =
      ((Tok.node tgt, Role.goal) :: (Tok.rsn, Role.goal) :: τ.map fun v => (.node v, .trace))[k]? := by
  have hl := C_len_edgeToks es
  rw [C_dfsInput_assoc, show 3 * es.length + 1 + k = (3 * es.length + k) + 1 by ring,
    List.getElem?_cons_succ, List.getElem?_append_right (by omega)]
  congr 1; omega

theorem C_tok_goal (es : List (Fin N × Fin N)) (tgt : Fin N) (τ : List (Fin N)) :
    (dfsInput es tgt τ)[3 * es.length + 1]? = some (.node tgt, .goal) := by
  simpa using C_tok_tail es tgt τ 0

theorem C_tok_rsn (es : List (Fin N × Fin N)) (tgt : Fin N) (τ : List (Fin N)) :
    (dfsInput es tgt τ)[3 * es.length + 2]? = some (.rsn, .goal) := by
  simpa using C_tok_tail es tgt τ 1

theorem C_tok_trace (es : List (Fin N × Fin N)) (tgt : Fin N) (τ : List (Fin N)) (k : ℕ) :
    (dfsInput es tgt τ)[3 * es.length + 3 + k]? = τ[k]?.map fun v => (.node v, .trace) := by
  have := C_tok_tail es tgt τ (k + 2)
  rw [show 3 * es.length + 1 + (k + 2) = 3 * es.length + 3 + k by ring] at this
  rw [this]; simp

/-! ### DFS traces and counting -/

theorem C_zip_append (τ : List (Fin N)) (x v : Fin N) (h : τ.getLast? = some x) :
    (τ ++ [v]).zip (τ ++ [v]).tail = τ.zip τ.tail ++ [(x, v)] := by
  induction τ with
  | nil => simp at h
  | cons a l ih =>
    cases l with
    | nil => simp at h; subst h; simp
    | cons b l' =>
      have h' : (b :: l').getLast? = some x := by
        rw [List.getLast?_cons_cons] at h; exact h
      have := ih h'
      simp only [List.cons_append, List.tail_cons, List.zip_cons_cons] at this ⊢
      rw [this]

theorem C_stack_inv {E : Fin N → Fin N → Prop} {s : Fin N} {n : ℕ} {τ stk : List (Fin N)}
    (h : Run E (DFSNext E) s n τ stk) :
    τ.getLast? = stk.head? ∧ stk ≠ [] ∧ (∀ y ∈ stk, y ∈ τ) ∧ stk.Nodup ∧
      ∀ p ∈ stk.zip stk.tail, p ∉ τ.zip τ.tail := by
  induction h with
  | zero => simp
  | @fwd n τ rest x v hrun hP hE hv ih =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih
    have hx : τ.getLast? = some x := by simpa using h1
    have hxτ : x ∈ τ := h3 x (by simp)
    rw [C_zip_append τ x v hx]
    refine ⟨by simp, by simp, ?_, ?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · simp
      · exact List.mem_append_left _ (h3 y hy)
    · rw [List.nodup_cons]; exact ⟨fun hm => hv (h3 v hm), h4⟩
    · intro p hp hpτ
      simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at hp
      rcases List.mem_append.1 hpτ with hpτ | hpτ
      · rcases hp with rfl | hp
        · exact hv (List.of_mem_zip hpτ).1
        · exact h5 p (by simpa using hp) hpτ
      · rw [List.mem_singleton] at hpτ; subst hpτ
        rcases hp with h | hp
        · simp only [Prod.mk.injEq] at h; exact hv (h.1 ▸ hxτ)
        · exact hv (h3 v (List.mem_cons_of_mem _ (List.of_mem_zip hp).2))
  | @back n τ rest x v hrun hP hnot ih =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih
    have hx : τ.getLast? = some x := by simpa using h1
    have hrh : rest.head? = some v := by
      rcases hP with hP | hP
      · exact absurd hP hnot
      · exact hP.2
    obtain ⟨rest', rfl⟩ : ∃ rest', rest = v :: rest' := by
      cases rest with
      | nil => simp at hrh
      | cons a r => simp at hrh; exact ⟨r, by rw [hrh]⟩
    rw [C_zip_append τ x v hx]
    refine ⟨by simp, by simp, ?_, ?_, ?_⟩
    · intro y hy; exact List.mem_append_left _ (h3 y (List.mem_cons_of_mem _ hy))
    · exact (List.nodup_cons.1 h4).2
    · intro p hp hpτ
      rcases List.mem_append.1 hpτ with hpτ | hpτ
      · exact h5 p (by simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons]; exact Or.inr (by simpa using hp)) hpτ
      · rw [List.mem_singleton] at hpτ; subst hpτ
        have := (List.of_mem_zip hp).1
        exact (List.nodup_cons.1 h4).1 this

theorem C_parent_no_dep {E : Fin N → Fin N → Prop} {s : Fin N} {τ rest : List (Fin N)}
    {x p : Fin N} (h : DFSTrace E s τ (x :: rest)) (hp : rest.head? = some p) :
    (τ.zip τ.tail).count (x, p) = 0 := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨-, -, -, -, h5⟩ := C_stack_inv hn
  apply List.count_eq_zero_of_not_mem
  apply h5
  cases rest with
  | nil => simp at hp
  | cons a r => simp at hp; subst hp; simp

theorem C_count_eq_sum {α : Type} [DecidableEq α] [BEq α] [LawfulBEq α] (l : List α) (a : α) :
    (l.count a : ℝ) = ∑ k ∈ Finset.range l.length, if l[k]? = some a then (1 : ℝ) else 0 := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [List.count_cons, List.length_cons, Finset.sum_range_succ']
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq]
    push_cast
    rw [ih]
    congr 1
    simp [beq_iff_eq]

theorem C_count_zip {α : Type} [DecidableEq α] [BEq (α × α)] [LawfulBEq (α × α)]
    (τ : List α) (a b : α) :
    ((τ.zip τ.tail).count (a, b) : ℝ) = ∑ k ∈ Finset.range (τ.length - 1),
      if τ[k]? = some a ∧ τ[k + 1]? = some b then (1 : ℝ) else 0 := by
  induction τ with
  | nil => simp
  | cons c l ih =>
    cases l with
    | nil => simp
    | cons d l =>
      simp only [List.tail_cons, List.zip_cons_cons, List.count_cons, List.length_cons,
        Nat.add_sub_cancel] at ih ⊢
      rw [Finset.sum_range_succ']
      push_cast
      rw [ih]
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq]
      congr 1
      simp only [beq_iff_eq, Prod.ext_iff]


/-! ### Embedding of the input, as a function of `ℕ`-positions -/

/-- The embedding at an `ℕ`-position (zero past the end). -/
noncomputable def C_Xn (L : ℕ) (toks : List (Tok N × Role)) (j : ℕ) (c : Coord2 N) : ℝ :=
  match toks[j]? with
  | some p => emb2 N L p.1 p.2 j c
  | none => 0

theorem C_Xn_some {L : ℕ} {toks : List (Tok N × Role)} {j : ℕ} {p : Tok N × Role}
    (h : toks[j]? = some p) (c : Coord2 N) : C_Xn L toks j c = emb2 N L p.1 p.2 j c := by
  simp [C_Xn, h]

theorem C_embSeq_eq (L : ℕ) (toks : List (Tok N × Role)) (j : Fin toks.length) (c : Coord2 N) :
    embSeq (emb2 N L) toks j c = C_Xn L toks j c := by
  rw [C_Xn_some (List.getElem?_eq_getElem j.2)]; rfl

theorem C_emb2_node (L j : ℕ) (w v : Fin N) (r : Role) (b : Fin 4) :
    emb2 N L (.node w) r j (blk b v) =
      if w = v ∧ ((r = .trace ∧ b = 0) ∨ (r ≠ .trace ∧ b = 3)) then 1 else 0 := rfl

section
variable (L : ℕ) (es : List (Fin N × Fin N)) (tgt : Fin N) (τ : List (Fin N))

theorem C_Xn_bos (b : Fin 4) (v : Fin N) : C_Xn L (dfsInput es tgt τ) 0 (blk b v) = 0 := by
  rw [C_Xn_some (C_tok_bos es tgt τ)]; rfl

theorem C_Xn_src {i : ℕ} (hi : i < es.length) (v : Fin N) :
    C_Xn L (dfsInput es tgt τ) (3 * i + 1) (blk 0 v) = 0 ∧
    C_Xn L (dfsInput es tgt τ) (3 * i + 1) (blk 3 v) = if es[i].1 = v then 1 else 0 := by
  rw [C_Xn_some (C_tok_edge es tgt τ i hi).1, C_Xn_some (C_tok_edge es tgt τ i hi).1]
  simp [C_emb2_node]

theorem C_Xn_dst {i : ℕ} (hi : i < es.length) (v : Fin N) :
    C_Xn L (dfsInput es tgt τ) (3 * i + 2) (blk 0 v) = 0 ∧
    C_Xn L (dfsInput es tgt τ) (3 * i + 2) (blk 3 v) = if es[i].2 = v then 1 else 0 := by
  rw [C_Xn_some (C_tok_edge es tgt τ i hi).2.1, C_Xn_some (C_tok_edge es tgt τ i hi).2.1]
  simp [C_emb2_node]

theorem C_Xn_sep {i : ℕ} (hi : i < es.length) (b : Fin 4) (v : Fin N) :
    C_Xn L (dfsInput es tgt τ) (3 * i + 3) (blk b v) = 0 := by
  rw [C_Xn_some (C_tok_edge es tgt τ i hi).2.2]; rfl

theorem C_Xn_goal (v : Fin N) : C_Xn L (dfsInput es tgt τ) (3 * es.length + 1) (blk 0 v) = 0 := by
  rw [C_Xn_some (C_tok_goal es tgt τ)]; simp [C_emb2_node]

theorem C_Xn_rsn (b : Fin 4) (v : Fin N) :
    C_Xn L (dfsInput es tgt τ) (3 * es.length + 2) (blk b v) = 0 := by
  rw [C_Xn_some (C_tok_rsn es tgt τ)]; rfl

theorem C_Xn_trace0 (k : ℕ) (v : Fin N) :
    C_Xn L (dfsInput es tgt τ) (3 * es.length + 3 + k) (blk 0 v) =
      if τ[k]? = some v then 1 else 0 := by
  unfold C_Xn
  rw [C_tok_trace]
  cases h : τ[k]? with
  | none => simp
  | some w => simp [C_emb2_node]

theorem C_Xn_trace3 (k : ℕ) (v : Fin N) :
    C_Xn L (dfsInput es tgt τ) (3 * es.length + 3 + k) (blk 3 v) = 0 := by
  unfold C_Xn
  rw [C_tok_trace]
  cases h : τ[k]? with
  | none => simp
  | some w => simp [C_emb2_node]

theorem C_Xn_pre {i : ℕ} (hi : i ≤ es.length) (v : Fin N) :
    C_Xn L (dfsInput es tgt τ) (3 * i) (blk 3 v) = 0 := by
  cases i with
  | zero => exact C_Xn_bos L es tgt τ 3 v
  | succ i =>
    rw [show 3 * (i + 1) = 3 * i + 3 by ring]
    exact C_Xn_sep L es tgt τ (by omega) 3 v

theorem C_Xn_blk0_lt {j : ℕ} (hj : j < 3 * es.length + 3) (v : Fin N) :
    C_Xn L (dfsInput es tgt τ) j (blk 0 v) = 0 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · exact C_Xn_bos L es tgt τ 0 v
  · by_cases hM : j < 3 * es.length + 1
    · have hi : (j - 1) / 3 < es.length := by omega
      rcases (show j = 3 * ((j - 1) / 3) + 1 ∨ j = 3 * ((j - 1) / 3) + 2 ∨
          j = 3 * ((j - 1) / 3) + 3 by omega) with h | h | h <;> rw [h]
      · exact (C_Xn_src L es tgt τ hi v).1
      · exact (C_Xn_dst L es tgt τ hi v).1
      · exact C_Xn_sep L es tgt τ hi 0 v
    · rcases (show j = 3 * es.length + 1 ∨ j = 3 * es.length + 2 by omega) with h | h <;> rw [h]
      · exact C_Xn_goal L es tgt τ v
      · exact C_Xn_rsn L es tgt τ 0 v

end

theorem C_sum_triples (g : ℕ → ℝ) (M : ℕ) :
    ∑ j ∈ Finset.range (3 * M + 3), g j =
      g 0 + ∑ i ∈ Finset.range M, (g (3 * i + 1) + g (3 * i + 2) + g (3 * i + 3)) +
        g (3 * M + 1) + g (3 * M + 2) := by
  induction M with
  | zero => simp [Finset.sum_range_succ]
  | succ M ih =>
    rw [show 3 * (M + 1) + 3 = 3 * M + 3 + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ,
      show 3 * (M + 1) + 1 = 3 * M + 3 + 1 by ring, show 3 * (M + 1) + 2 = 3 * M + 3 + 1 + 1 by ring]
    ring

theorem C_head0 (c₁ c₂ : ℝ) {T : ℕ} (X2 : Fin T → Coord2 N → ℝ) (i : Fin T) (u : Fin N) :
    headOut Act.linear ((layer2 N c₁ c₂).KQ (0 : Fin 2)) ((layer2 N c₁ c₂).V (0 : Fin 2)) X2 i
      (blk 0 u) = ∑ j, (c₁ * (∑ v, X2 j (blk 0 v)) * (∑ v, X2 i (blk 0 v)) +
        c₁ * ∑ v, X2 j (blk 2 v) * X2 i (blk 0 v)) * (X2 j (blk 3 u) - X2 j (blk 0 u)) := by
  simp only [headOut, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, attnW, Act.linear,
    Bool.false_eq_true, ite_false, id, C_KQ0, C_V0]

theorem C_head1 (c₁ c₂ : ℝ) {T : ℕ} (X2 : Fin T → Coord2 N → ℝ) (i : Fin T) (u : Fin N) :
    headOut Act.linear ((layer2 N c₁ c₂).KQ (1 : Fin 2)) ((layer2 N c₁ c₂).V (1 : Fin 2)) X2 i
      (blk 0 u) = ∑ j, (c₂ * ∑ v, (X2 j (blk 0 v) + X2 j (blk 1 v)) * X2 i (blk 0 v)) *
        (X2 j (blk 1 u) - X2 j (blk 0 u)) := by
  simp only [headOut, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, attnW, Act.linear,
    Bool.false_eq_true, ite_false, id, C_KQ1, C_V1]

theorem C_lambdas {L : ℕ} {toks : List (Tok N × Role)} {δ : ℝ} (hδ : 0 ≤ δ)
    (X2 : Fin toks.length → Coord2 N → ℝ) (hX2 : CopyProp δ (embSeq (emb2 N L) toks) X2)
    (h0 : ∀ b v, C_Xn L toks 0 (blk b v) = 0) :
    ∃ l₁ l₂ : ℕ → ℝ, (∀ j, l₁ j ∈ Set.Icc (1 - 2 * δ) 1 ∧ l₂ j ∈ Set.Icc (1 - 2 * δ) 1) ∧
      ∀ (j : Fin toks.length) (v : Fin N),
        X2 j (blk 1 v) = l₁ j * C_Xn L toks (j - 1) (blk 0 v) ∧
        X2 j (blk 2 v) = l₂ j * C_Xn L toks (j - 1) (blk 3 v) := by
  have key : ∀ j : ℕ, ∃ a b : ℝ, (a ∈ Set.Icc (1 - 2 * δ) 1 ∧ b ∈ Set.Icc (1 - 2 * δ) 1) ∧
      ∀ (hj : j < toks.length) (v : Fin N),
        X2 ⟨j, hj⟩ (blk 1 v) = a * C_Xn L toks (j - 1) (blk 0 v) ∧
        X2 ⟨j, hj⟩ (blk 2 v) = b * C_Xn L toks (j - 1) (blk 3 v) := by
    intro j
    have h1 : (1 : ℝ) ∈ Set.Icc (1 - 2 * δ) 1 := ⟨by linarith, le_rfl⟩
    cases j with
    | zero =>
      exact ⟨1, 1, ⟨h1, h1⟩, fun hj v => by
        rw [(hX2.2.1 ⟨0, hj⟩ rfl v).1, (hX2.2.1 ⟨0, hj⟩ rfl v).2]; simp [h0]⟩
    | succ j =>
      by_cases hj : j + 1 < toks.length
      · obtain ⟨a, b, ha, hb, h⟩ := hX2.2.2 ⟨j + 1, hj⟩ ⟨j, by omega⟩ rfl
        refine ⟨a, b, ⟨ha, hb⟩, fun hj' v => ?_⟩
        rw [(h v).1, (h v).2, C_embSeq_eq, C_embSeq_eq]
        simp
      · exact ⟨1, 1, ⟨h1, h1⟩, fun hj' => absurd hj' hj⟩
  choose l₁ l₂ hl hX using key
  exact ⟨l₁, l₂, hl, fun j v => hX j j.2 v⟩

theorem C_blk03 {L : ℕ} {toks : List (Tok N × Role)} {δ : ℝ}
    (X2 : Fin toks.length → Coord2 N → ℝ) (hX2 : CopyProp δ (embSeq (emb2 N L) toks) X2)
    (j : Fin toks.length) (v : Fin N) :
    X2 j (blk 0 v) = C_Xn L toks j (blk 0 v) ∧ X2 j (blk 3 v) = C_Xn L toks j (blk 3 v) := by
  rw [(hX2.1 j v).1, (hX2.1 j v).2, C_embSeq_eq, C_embSeq_eq]; exact ⟨rfl, rfl⟩

theorem C_head0_range (c₁ c₂ : ℝ) {L : ℕ} {toks : List (Tok N × Role)} {δ : ℝ}
    (X2 : Fin toks.length → Coord2 N → ℝ) (hX2 : CopyProp δ (embSeq (emb2 N L) toks) X2)
    (i : Fin toks.length) (x : Fin N) (hq : ∀ v, X2 i (blk 0 v) = if v = x then 1 else 0)
    (l₂ : ℕ → ℝ) (hl₂ : ∀ (j : Fin toks.length) (v : Fin N),
        X2 j (blk 2 v) = l₂ j * C_Xn L toks (j - 1) (blk 3 v)) (u : Fin N) :
    headOut Act.linear ((layer2 N c₁ c₂).KQ (0 : Fin 2)) ((layer2 N c₁ c₂).V (0 : Fin 2)) X2 i
      (blk 0 u) = ∑ j ∈ Finset.range toks.length,
        c₁ * (∑ v, C_Xn L toks j (blk 0 v) + l₂ j * C_Xn L toks (j - 1) (blk 3 x)) *
          (C_Xn L toks j (blk 3 u) - C_Xn L toks j (blk 0 u)) := by
  rw [C_head0, ← Fin.sum_univ_eq_sum_range (fun j => c₁ * (∑ v, C_Xn L toks j (blk 0 v) +
      l₂ j * C_Xn L toks (j - 1) (blk 3 x)) * (C_Xn L toks j (blk 3 u) - C_Xn L toks j (blk 0 u)))]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [hq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hl₂ j x, (C_blk03 X2 hX2 j u).1, (C_blk03 X2 hX2 j u).2]
  simp only [fun v => (C_blk03 X2 hX2 j v).1]
  ring

theorem C_head1_range (c₁ c₂ : ℝ) {L : ℕ} {toks : List (Tok N × Role)} {δ : ℝ}
    (X2 : Fin toks.length → Coord2 N → ℝ) (hX2 : CopyProp δ (embSeq (emb2 N L) toks) X2)
    (i : Fin toks.length) (x : Fin N) (hq : ∀ v, X2 i (blk 0 v) = if v = x then 1 else 0)
    (l₁ : ℕ → ℝ) (hl₁ : ∀ (j : Fin toks.length) (v : Fin N),
        X2 j (blk 1 v) = l₁ j * C_Xn L toks (j - 1) (blk 0 v)) (u : Fin N) :
    headOut Act.linear ((layer2 N c₁ c₂).KQ (1 : Fin 2)) ((layer2 N c₁ c₂).V (1 : Fin 2)) X2 i
      (blk 0 u) = ∑ j ∈ Finset.range toks.length,
        c₂ * (C_Xn L toks j (blk 0 x) + l₁ j * C_Xn L toks (j - 1) (blk 0 x)) *
          (l₁ j * C_Xn L toks (j - 1) (blk 0 u) - C_Xn L toks j (blk 0 u)) := by
  rw [C_head1, ← Fin.sum_univ_eq_sum_range (fun j => c₂ * (C_Xn L toks j (blk 0 x) +
      l₁ j * C_Xn L toks (j - 1) (blk 0 x)) *
        (l₁ j * C_Xn L toks (j - 1) (blk 0 u) - C_Xn L toks j (blk 0 u)))]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [hq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hl₁ j x, hl₁ j u, (C_blk03 X2 hX2 j u).1, (C_blk03 X2 hX2 j x).1]

/-- Summand of the forward head at an `ℕ`-position. -/
noncomputable def C_g0 (L : ℕ) (c₁ : ℝ) (toks : List (Tok N × Role)) (x u : Fin N) (l₂ : ℕ → ℝ)
    (j : ℕ) : ℝ :=
  c₁ * (∑ v, C_Xn L toks j (blk 0 v) + l₂ j * C_Xn L toks (j - 1) (blk 3 x)) *
    (C_Xn L toks j (blk 3 u) - C_Xn L toks j (blk 0 u))

/-- Summand of the backtracking head at an `ℕ`-position. -/
noncomputable def C_g1 (L : ℕ) (c₂ : ℝ) (toks : List (Tok N × Role)) (x u : Fin N) (l₁ : ℕ → ℝ)
    (j : ℕ) : ℝ :=
  c₂ * (C_Xn L toks j (blk 0 x) + l₁ j * C_Xn L toks (j - 1) (blk 0 x)) *
    (l₁ j * C_Xn L toks (j - 1) (blk 0 u) - C_Xn L toks j (blk 0 u))

section
variable (L : ℕ) (es : List (Fin N × Fin N)) (tgt : Fin N) (τ : List (Fin N))

theorem C_sum_ind (k : ℕ) (hk : k < τ.length) :
    ∑ v : Fin N, (if τ[k]? = some v then (1 : ℝ) else 0) = 1 := by
  rw [List.getElem?_eq_getElem hk]
  simp

theorem C_eval_head0 (c₁ : ℝ) (x u : Fin N) (l₂ : ℕ → ℝ) :
    ∑ j ∈ Finset.range (dfsInput es tgt τ).length, C_g0 L c₁ (dfsInput es tgt τ) x u l₂ j =
      c₁ * (∑ i ∈ Finset.range es.length,
          l₂ (3 * i + 2) * (if es[i]? = some (x, u) then 1 else 0) -
        ∑ k ∈ Finset.range τ.length, if τ[k]? = some u then 1 else 0) := by
  rw [C_len, Finset.sum_range_add, C_sum_triples]
  have e0 : C_g0 L c₁ (dfsInput es tgt τ) x u l₂ 0 = 0 := by
    simp [C_g0, C_Xn_bos]
  have e1 : ∀ i ∈ Finset.range es.length,
      C_g0 L c₁ (dfsInput es tgt τ) x u l₂ (3 * i + 1) +
        C_g0 L c₁ (dfsInput es tgt τ) x u l₂ (3 * i + 2) +
        C_g0 L c₁ (dfsInput es tgt τ) x u l₂ (3 * i + 3) =
      c₁ * (l₂ (3 * i + 2) * (if es[i]? = some (x, u) then 1 else 0)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have h1 : 3 * i + 1 - 1 = 3 * i := by omega
    have h2 : 3 * i + 2 - 1 = 3 * i + 1 := by omega
    simp only [C_g0, h1, h2, (C_Xn_src L es tgt τ hi _).1, (C_Xn_src L es tgt τ hi _).2,
      (C_Xn_dst L es tgt τ hi _).1, (C_Xn_dst L es tgt τ hi _).2, C_Xn_sep L es tgt τ hi,
      C_Xn_pre L es tgt τ (le_of_lt hi), List.getElem?_eq_getElem hi, Option.some.injEq,
      Prod.ext_iff]
    simp only [Finset.sum_const_zero, mul_zero, add_zero, zero_add, sub_zero, sub_self,
      mul_ite, mul_one, ite_and]
    split_ifs <;> ring
  have e2 : C_g0 L c₁ (dfsInput es tgt τ) x u l₂ (3 * es.length + 1) = 0 := by
    have h1 : 3 * es.length + 1 - 1 = 3 * es.length := by omega
    simp [C_g0, h1, C_Xn_goal, C_Xn_pre L es tgt τ (le_refl _)]
  have e3 : C_g0 L c₁ (dfsInput es tgt τ) x u l₂ (3 * es.length + 2) = 0 := by
    simp [C_g0, C_Xn_rsn]
  have e4 : ∀ k ∈ Finset.range τ.length,
      C_g0 L c₁ (dfsInput es tgt τ) x u l₂ (3 * es.length + 3 + k) =
        -(c₁ * if τ[k]? = some u then 1 else 0) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hpre : C_Xn L (dfsInput es tgt τ) (3 * es.length + 3 + k - 1) (blk 3 x) = 0 := by
      cases k with
      | zero => exact C_Xn_rsn L es tgt τ 3 x
      | succ k =>
        rw [show 3 * es.length + 3 + (k + 1) - 1 = 3 * es.length + 3 + k by omega]
        exact C_Xn_trace3 L es tgt τ k x
    simp only [C_g0, hpre, C_Xn_trace0, C_Xn_trace3, C_sum_ind τ k hk]
    ring
  rw [e0, Finset.sum_congr rfl e1, e2, e3, Finset.sum_congr rfl e4, Finset.sum_neg_distrib,
    mul_sub, Finset.mul_sum, Finset.mul_sum]
  ring

theorem C_eval_head1 (c₂ : ℝ) (x u : Fin N) (l₁ : ℕ → ℝ) (ht : τ ≠ []) :
    ∑ j ∈ Finset.range (dfsInput es tgt τ).length, C_g1 L c₂ (dfsInput es tgt τ) x u l₁ j =
      -(c₂ * ((if τ[0]? = some x then 1 else 0) * (if τ[0]? = some u then 1 else 0))) +
      ∑ k ∈ Finset.range (τ.length - 1),
        c₂ * ((if τ[k + 1]? = some x then 1 else 0) +
            l₁ (3 * es.length + 3 + (k + 1)) * (if τ[k]? = some x then 1 else 0)) *
          (l₁ (3 * es.length + 3 + (k + 1)) * (if τ[k]? = some u then 1 else 0) -
            (if τ[k + 1]? = some u then 1 else 0)) := by
  obtain ⟨n, hn⟩ : ∃ n, τ.length = n + 1 :=
    ⟨τ.length - 1, by have := List.length_pos_iff.2 ht; omega⟩
  rw [C_len, Finset.sum_range_add]
  have e0 : ∑ j ∈ Finset.range (3 * es.length + 3), C_g1 L c₂ (dfsInput es tgt τ) x u l₁ j = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_range] at hj
    simp [C_g1, C_Xn_blk0_lt L es tgt τ hj, C_Xn_blk0_lt L es tgt τ (show j - 1 < _ by omega)]
  rw [e0, zero_add, hn, Nat.add_sub_cancel, Finset.sum_range_succ']
  have hpre0 : ∀ v, C_Xn L (dfsInput es tgt τ) (3 * es.length + 3 + 0 - 1) (blk 0 v) = 0 :=
    fun v => C_Xn_rsn L es tgt τ 0 v
  have hpre : ∀ k v, C_Xn L (dfsInput es tgt τ) (3 * es.length + 3 + (k + 1) - 1) (blk 0 v) =
      if τ[k]? = some v then 1 else 0 := by
    intro k v
    rw [show 3 * es.length + 3 + (k + 1) - 1 = 3 * es.length + 3 + k by omega, C_Xn_trace0]
  simp only [C_g1, hpre0, hpre, C_Xn_trace0]
  ring

end

/-! ### Bands of the two heads -/

theorem C_wsum_bounds (f : ℕ → ℝ) (a : ℝ) (hf : ∀ k, f k ∈ Set.Icc a 1) (P : ℕ → Prop)
    [DecidablePred P] (n : ℕ) :
    a * ∑ k ∈ Finset.range n, (if P k then (1 : ℝ) else 0) ≤
      ∑ k ∈ Finset.range n, f k * (if P k then (1 : ℝ) else 0) ∧
    ∑ k ∈ Finset.range n, f k * (if P k then (1 : ℝ) else 0) ≤
      ∑ k ∈ Finset.range n, (if P k then (1 : ℝ) else 0) := by
  constructor
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => by split_ifs <;> simp [(hf k).1]
  · exact Finset.sum_le_sum fun k _ => by split_ifs <;> simp [(hf k).2]

theorem C_A0_child (es : List (Fin N × Fin N)) (τ : List (Fin N)) (x u : Fin N) (c₁ a : ℝ)
    (μ : ℕ → ℝ) (hμ : ∀ i, μ i ∈ Set.Icc a 1) (hc₁ : 0 ≤ c₁) (hes : es.Nodup)
    (hmem : (x, u) ∈ es) (hu : u ∉ τ) :
    c₁ * a ≤ c₁ * (∑ i ∈ Finset.range es.length,
        μ i * (if es[i]? = some (x, u) then 1 else 0) -
      ∑ k ∈ Finset.range τ.length, if τ[k]? = some u then 1 else 0) := by
  have h1 : ((es.count (x, u) : ℕ) : ℝ) = 1 := by
    rw [List.count_eq_one_of_mem hes hmem]; simp
  have h2 : ((τ.count u : ℕ) : ℝ) = 0 := by rw [List.count_eq_zero.2 hu]; simp
  rw [C_count_eq_sum] at h1 h2
  have := (C_wsum_bounds μ a hμ (fun i => es[i]? = some (x, u)) es.length).1
  rw [h1] at this; rw [h2]
  apply mul_le_mul_of_nonneg_left _ hc₁
  linarith

theorem C_A0_other (es : List (Fin N × Fin N)) (τ : List (Fin N)) (x u : Fin N) (c₁ a : ℝ)
    (μ : ℕ → ℝ) (hμ : ∀ i, μ i ∈ Set.Icc a 1) (hc₁ : 0 ≤ c₁) (hes : es.Nodup)
    (hnot : ¬ ((x, u) ∈ es ∧ u ∉ τ)) :
    c₁ * (∑ i ∈ Finset.range es.length,
        μ i * (if es[i]? = some (x, u) then 1 else 0) -
      ∑ k ∈ Finset.range τ.length, if τ[k]? = some u then 1 else 0) ≤ 0 := by
  have h1 : ((es.count (x, u) : ℕ) : ℝ) ≤ 1 := by
    exact_mod_cast List.nodup_iff_count_le_one.1 hes (x, u)
  have h2 := (C_wsum_bounds μ a hμ (fun i => es[i]? = some (x, u)) es.length).2
  rw [← C_count_eq_sum] at h2
  apply mul_nonpos_of_nonneg_of_nonpos hc₁
  rw [← C_count_eq_sum]
  by_cases hm : (x, u) ∈ es
  · have hu : u ∈ τ := by by_contra h; exact hnot ⟨hm, h⟩
    have : (1 : ℝ) ≤ ((τ.count u : ℕ) : ℝ) := by
      exact_mod_cast List.count_pos_iff.2 hu
    linarith
  · have h0 : ((es.count (x, u) : ℕ) : ℝ) = 0 := by rw [List.count_eq_zero.2 hm]; simp
    have : (0 : ℝ) ≤ ((τ.count u : ℕ) : ℝ) := by positivity
    linarith

theorem C_term_ne (o1 o2 : Option (Fin N)) (x u : Fin N) (hux : u ≠ x) (lam c₂ : ℝ) :
    c₂ * ((if o2 = some x then (1 : ℝ) else 0) + lam * (if o1 = some x then 1 else 0)) *
        (lam * (if o1 = some u then 1 else 0) - (if o2 = some u then 1 else 0)) =
      c₂ * (lam * (if o1 = some u ∧ o2 = some x then 1 else 0)) -
        c₂ * (lam * (if o1 = some x ∧ o2 = some u then 1 else 0)) := by
  rcases o1 with _ | a <;> rcases o2 with _ | b <;>
    simp only [reduceCtorEq, Option.some.injEq, false_and, and_false, ite_false] <;>
    (try split_ifs) <;> first | ring1 | (exfalso; simp_all)

theorem C_term_eq (o1 o2 : Option (Fin N)) (x : Fin N) (lam c₂ : ℝ) :
    c₂ * ((if o2 = some x then (1 : ℝ) else 0) + lam * (if o1 = some x then 1 else 0)) *
        (lam * (if o1 = some x then 1 else 0) - (if o2 = some x then 1 else 0)) =
      c₂ * (lam ^ 2 * (if o1 = some x then 1 else 0) - (if o2 = some x then 1 else 0)) := by
  split_ifs <;> ring

/-- The backtracking-head value at the last position (as computed by `C_eval_head1`). -/
noncomputable def C_A1 (τ : List (Fin N)) (c₂ : ℝ) (lam : ℕ → ℝ) (x u : Fin N) : ℝ :=
  -(c₂ * ((if τ[0]? = some x then 1 else 0) * (if τ[0]? = some u then 1 else 0))) +
      ∑ k ∈ Finset.range (τ.length - 1),
        c₂ * ((if τ[k + 1]? = some x then 1 else 0) +
            lam k * (if τ[k]? = some x then 1 else 0)) *
          (lam k * (if τ[k]? = some u then 1 else 0) -
            (if τ[k + 1]? = some u then 1 else 0))

theorem C_A1_self (τ : List (Fin N)) (c₂ : ℝ) (lam : ℕ → ℝ) (x : Fin N)
    (hlam : ∀ k, lam k ∈ Set.Icc 0 1) (hc₂ : 0 ≤ c₂)
    (hlast : τ[τ.length - 1]? = some x) : C_A1 τ c₂ lam x x ≤ 0 := by
  unfold C_A1
  have hB : (if τ[0]? = some x then (1 : ℝ) else 0) * (if τ[0]? = some x then 1 else 0) =
      if τ[0]? = some x then 1 else 0 := by split_ifs <;> norm_num
  rw [hB]
  have hsum : ∑ k ∈ Finset.range (τ.length - 1),
      c₂ * ((if τ[k + 1]? = some x then (1 : ℝ) else 0) +
            lam k * (if τ[k]? = some x then 1 else 0)) *
          (lam k * (if τ[k]? = some x then 1 else 0) -
            (if τ[k + 1]? = some x then 1 else 0)) ≤
      ∑ k ∈ Finset.range (τ.length - 1),
        c₂ * ((if τ[k]? = some x then (1 : ℝ) else 0) - (if τ[k + 1]? = some x then 1 else 0)) := by
    refine Finset.sum_le_sum fun k _ => ?_
    rw [C_term_eq]
    apply mul_le_mul_of_nonneg_left _ hc₂
    have := hlam k
    have h2 : lam k ^ 2 ≤ 1 := by nlinarith [this.1, this.2]
    split_ifs <;> nlinarith
  have htel := Finset.sum_range_sub' (fun k => if τ[k]? = some x then (1 : ℝ) else 0)
    (τ.length - 1)
  rw [← Finset.mul_sum, htel, hlast] at hsum
  simp only [ite_true] at hsum
  split_ifs at hsum ⊢ <;> nlinarith

theorem C_A1_ne (τ : List (Fin N)) (c₂ δ : ℝ) (lam : ℕ → ℝ) (x u : Fin N) (hux : u ≠ x)
    (hlam : ∀ k, lam k ∈ Set.Icc (1 - 2 * δ) 1) :
    ∃ Sa Sd : ℝ, C_A1 τ c₂ lam x u = c₂ * (Sa - Sd) ∧
      (1 - 2 * δ) * ((τ.zip τ.tail).count (u, x) : ℝ) ≤ Sa ∧
      Sa ≤ ((τ.zip τ.tail).count (u, x) : ℝ) ∧
      (1 - 2 * δ) * ((τ.zip τ.tail).count (x, u) : ℝ) ≤ Sd ∧
      Sd ≤ ((τ.zip τ.tail).count (x, u) : ℝ) := by
  have ha := C_wsum_bounds lam (1 - 2 * δ) hlam
    (fun k => τ[k]? = some u ∧ τ[k + 1]? = some x) (τ.length - 1)
  have hd := C_wsum_bounds lam (1 - 2 * δ) hlam
    (fun k => τ[k]? = some x ∧ τ[k + 1]? = some u) (τ.length - 1)
  rw [← C_count_zip] at ha hd
  refine ⟨_, _, ?_, ha.1, ha.2, hd.1, hd.2⟩
  unfold C_A1
  have h0 : (if τ[0]? = some x then (1 : ℝ) else 0) * (if τ[0]? = some u then 1 else 0) = 0 := by
    split_ifs with h1 h2 <;> norm_num
    rw [h1] at h2; exact hux (Option.some.inj h2).symm
  rw [h0, mul_zero, neg_zero, zero_add, mul_sub, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [C_term_ne _ _ x u hux]

/-- The forward-head value at the last position (as computed by `C_eval_head0`). -/
noncomputable def C_A0 (es : List (Fin N × Fin N)) (τ : List (Fin N)) (c₁ : ℝ) (μ : ℕ → ℝ)
    (x u : Fin N) : ℝ :=
  c₁ * (∑ i ∈ Finset.range es.length, μ i * (if es[i]? = some (x, u) then 1 else 0) -
    ∑ k ∈ Finset.range τ.length, if τ[k]? = some u then 1 else 0)

theorem C_H0 (L : ℕ) (c₁ c₂ δ : ℝ) (es : List (Fin N × Fin N)) (tgt : Fin N) (τ : List (Fin N))
    (X2 : Fin (dfsInput es tgt τ).length → Coord2 N → ℝ)
    (hX2 : CopyProp δ (embSeq (emb2 N L) (dfsInput es tgt τ)) X2)
    (i : Fin (dfsInput es tgt τ).length) (x : Fin N)
    (hq : ∀ v, X2 i (blk 0 v) = if v = x then 1 else 0) (l₂ : ℕ → ℝ)
    (hl₂ : ∀ (j : Fin (dfsInput es tgt τ).length) (v : Fin N),
      X2 j (blk 2 v) = l₂ j * C_Xn L (dfsInput es tgt τ) (j - 1) (blk 3 v)) (u : Fin N) :
    headOut Act.linear ((layer2 N c₁ c₂).KQ (0 : Fin 2)) ((layer2 N c₁ c₂).V (0 : Fin 2)) X2 i
      (blk 0 u) = C_A0 es τ c₁ (fun j => l₂ (3 * j + 2)) x u :=
  (C_head0_range c₁ c₂ X2 hX2 i x hq l₂ hl₂ u).trans (C_eval_head0 L es tgt τ c₁ x u l₂)

theorem C_H1 (L : ℕ) (c₁ c₂ δ : ℝ) (es : List (Fin N × Fin N)) (tgt : Fin N) (τ : List (Fin N))
    (X2 : Fin (dfsInput es tgt τ).length → Coord2 N → ℝ)
    (hX2 : CopyProp δ (embSeq (emb2 N L) (dfsInput es tgt τ)) X2)
    (i : Fin (dfsInput es tgt τ).length) (x : Fin N)
    (hq : ∀ v, X2 i (blk 0 v) = if v = x then 1 else 0) (l₁ : ℕ → ℝ)
    (hl₁ : ∀ (j : Fin (dfsInput es tgt τ).length) (v : Fin N),
      X2 j (blk 1 v) = l₁ j * C_Xn L (dfsInput es tgt τ) (j - 1) (blk 0 v)) (ht : τ ≠ [])
    (u : Fin N) :
    headOut Act.linear ((layer2 N c₁ c₂).KQ (1 : Fin 2)) ((layer2 N c₁ c₂).V (1 : Fin 2)) X2 i
      (blk 0 u) = C_A1 τ c₂ (fun k => l₁ (3 * es.length + 3 + (k + 1))) x u :=
  (C_head1_range c₁ c₂ X2 hX2 i x hq l₁ hl₁ u).trans (C_eval_head1 L es tgt τ c₂ x u l₁ ht)

theorem two_layer_core (N L : ℕ) (c₁ c₂ δ : ℝ) (hc₂ : 0 < c₂) (hc : c₂ < c₁) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ (c₁ - c₂) / (4 * c₁))
    (es : List (Fin N × Fin N)) (root tgt : Fin N) (τ stk : List (Fin N))
    (hes : es.Nodup) (hτ : DFSTrace (Adj es) root τ stk) (hmv : ∃ v, DFSNext (Adj es) τ stk v)
    (X2 : Fin (dfsInput es tgt τ).length → Coord2 N → ℝ)
    (hX2 : CopyProp δ (embSeq (emb2 N L) (dfsInput es tgt τ)) X2)
    (i : Fin (dfsInput es tgt τ).length) (hi : (i : ℕ) + 1 = (dfsInput es tgt τ).length)
    (w : Tok N) (hw : IsMax (fun w => ∑ c, R2 N c w * (layer2 N c₁ c₂).apply X2 i c) w) :
    ∃ v, w = .node v ∧ DFSNext (Adj es) τ stk v := by
  obtain ⟨x, rest, rfl, hlast, -, -, hrest, hcnt⟩ := dfs_transitions hτ
  have hτne : τ ≠ [] := by rintro rfl; simp at hlast
  have htpos : 0 < τ.length := List.length_pos_iff.2 hτne
  have hlen := C_len es tgt τ
  have hc₁ : 0 < c₁ := by linarith
  have hδ4 : 4 * c₁ * δ ≤ c₁ - c₂ := by
    rw [le_div_iff₀ (by positivity)] at hδ; linarith
  have hδq : δ < 1 / 4 := by nlinarith
  obtain ⟨l₁, l₂, hl, hX⟩ := C_lambdas hδ0 X2 hX2 (C_Xn_bos L es tgt τ)
  have hiv : (i : ℕ) = 3 * es.length + 3 + (τ.length - 1) := by omega
  have hlast' : τ[τ.length - 1]? = some x := by rw [← List.getLast?_eq_getElem?]; exact hlast
  have hq : ∀ v, X2 i (blk 0 v) = if v = x then 1 else 0 := by
    intro v
    rw [(C_blk03 X2 hX2 i v).1, hiv, C_Xn_trace0, hlast']
    simp [eq_comm]
  have hq3 : ∀ v, X2 i (blk 3 v) = 0 := by
    intro v; rw [(C_blk03 X2 hX2 i v).2, hiv, C_Xn_trace3]
  have hq2 : ∀ v, X2 i (blk 2 v) = 0 := by
    intro v
    rw [(hX i v).2]
    have : C_Xn L (dfsInput es tgt τ) (↑i - 1) (blk 3 v) = 0 := by
      rcases Nat.lt_or_ge 1 τ.length with h | h
      · rw [show (i : ℕ) - 1 = 3 * es.length + 3 + (τ.length - 2) by omega, C_Xn_trace3]
      · rw [show (i : ℕ) - 1 = 3 * es.length + 2 by omega, C_Xn_rsn]
    rw [this, mul_zero]
  have hlam : ∀ k, (fun k => l₁ (3 * es.length + 3 + (k + 1))) k ∈ Set.Icc (1 - 2 * δ) 1 :=
    fun k => (hl _).1
  have hlam0 : ∀ k, (fun k => l₁ (3 * es.length + 3 + (k + 1))) k ∈ Set.Icc 0 1 :=
    fun k => ⟨by linarith [(hlam k).1], (hlam k).2⟩
  have hμ : ∀ k, (fun j => l₂ (3 * j + 2)) k ∈ Set.Icc (1 - 2 * δ) 1 := fun k => (hl _).2
  -- the logits
  have hlogit : ∀ u, (∑ c, R2 N c (.node u) * (layer2 N c₁ c₂).apply X2 i c) =
      max (C_A0 es τ c₁ (fun j => l₂ (3 * j + 2)) x u) 0 +
      max (C_A1 τ c₂ (fun k => l₁ (3 * es.length + 3 + (k + 1))) x u) 0 := by
    intro u
    rw [C_logit_node, C_apply_blk2, C_apply_blk3, hq2, hq3,
      C_H0 L c₁ c₂ δ es tgt τ X2 hX2 i x hq l₂ (fun j v => (hX j v).2) u,
      C_H1 L c₁ c₂ δ es tgt τ X2 hX2 i x hq l₁ (fun j v => (hX j v).1) hτne u]
    ring
  have hspec : ∀ w : Tok N, (∀ u, w ≠ .node u) →
      (∑ c, R2 N c w * (layer2 N c₁ c₂).apply X2 i c) = 0 :=
    fun w hw => C_logit_special _ w hw
  -- the bands
  have hA0c : ∀ u, Adj es x u → u ∉ τ →
      c₁ * (1 - 2 * δ) ≤ C_A0 es τ c₁ (fun j => l₂ (3 * j + 2)) x u :=
    fun u hu1 hu2 => C_A0_child es τ x u c₁ (1 - 2 * δ) _ hμ hc₁.le hes hu1 hu2
  have hA0o : ∀ u, ¬ (Adj es x u ∧ u ∉ τ) →
      C_A0 es τ c₁ (fun j => l₂ (3 * j + 2)) x u ≤ 0 :=
    fun u hu => C_A0_other es τ x u c₁ (1 - 2 * δ) _ hμ hc₁.le hes hu
  have hA1x : C_A1 τ c₂ (fun k => l₁ (3 * es.length + 3 + (k + 1))) x x ≤ 0 :=
    C_A1_self τ c₂ _ x hlam0 hc₂.le hlast'
  have hA1p : ∀ p, rest.head? = some p →
      c₂ * (1 - 2 * δ) ≤ C_A1 τ c₂ (fun k => l₁ (3 * es.length + 3 + (k + 1))) x p ∧
      C_A1 τ c₂ (fun k => l₁ (3 * es.length + 3 + (k + 1))) x p ≤ c₂ := by
    intro p hp
    have hpx : p ≠ x := (hrest p (List.mem_of_mem_head? hp)).2
    obtain ⟨Sa, Sd, he, h1, h2, h3, h4⟩ := C_A1_ne τ c₂ δ _ x p hpx hlam
    have hcd : (τ.zip τ.tail).count (x, p) = 0 := C_parent_no_dep hτ hp
    have hca : (τ.zip τ.tail).count (p, x) = 1 := by
      rw [(hcnt p hpx).2, hcd]; simp [hp]
    rw [hcd] at h3 h4; rw [hca] at h1 h2
    push_cast at h1 h2 h3 h4
    rw [he]
    constructor <;> nlinarith
  have hA1o : ∀ v, v ≠ x → rest.head? ≠ some v →
      C_A1 τ c₂ (fun k => l₁ (3 * es.length + 3 + (k + 1))) x v ≤ 2 * δ * c₂ := by
    intro v hvx hp
    obtain ⟨Sa, Sd, he, h1, h2, h3, h4⟩ := C_A1_ne τ c₂ δ _ x v hvx hlam
    have hca : (τ.zip τ.tail).count (v, x) = (τ.zip τ.tail).count (x, v) := by
      rw [(hcnt v hvx).2]; simp [hp]
    have hle := (hcnt v hvx).1
    rw [hca] at h1 h2
    rw [he]
    rcases (show (τ.zip τ.tail).count (x, v) = 0 ∨ (τ.zip τ.tail).count (x, v) = 1 by omega)
      with h0 | h0 <;> rw [h0] at h1 h2 h3 h4 <;> push_cast at h1 h2 h3 h4 <;> nlinarith
  -- the argmax
  by_cases hch : ∃ u, Adj es x u ∧ u ∉ τ
  · obtain ⟨u₀, hu₀a, hu₀τ⟩ := hch
    have hwge := hw (.node u₀)
    simp only at hwge
    have hℓu₀ : c₁ * (1 - 2 * δ) ≤ ∑ c, R2 N c (.node u₀) * (layer2 N c₁ c₂).apply X2 i c := by
      rw [hlogit]
      have := hA0c u₀ hu₀a hu₀τ
      have := le_max_left (C_A0 es τ c₁ (fun j => l₂ (3 * j + 2)) x u₀) 0
      have := le_max_right (C_A1 τ c₂ (fun k => l₁ (3 * es.length + 3 + (k + 1))) x u₀) 0
      linarith
    have hgap : c₂ < c₁ * (1 - 2 * δ) := by nlinarith
    cases w with
    | node v =>
      refine ⟨v, rfl, ?_⟩
      by_contra hnv
      have hnot : ¬ (Adj es x v ∧ v ∉ τ) := fun h => hnv (Or.inl h)
      have h0 := hA0o v hnot
      have h1 : C_A1 τ c₂ (fun k => l₁ (3 * es.length + 3 + (k + 1))) x v ≤ c₂ := by
        by_cases hvx : v = x
        · subst hvx; linarith
        · by_cases hp : rest.head? = some v
          · exact (hA1p v hp).2
          · have := hA1o v hvx hp; nlinarith
      rw [hlogit v, max_eq_right h0] at hwge
      have := max_le h1 hc₂.le
      linarith
    | bos => rw [hspec .bos (by intro u; simp)] at hwge; linarith
    | sep => rw [hspec .sep (by intro u; simp)] at hwge; linarith
    | rsn => rw [hspec .rsn (by intro u; simp)] at hwge; linarith
  · simp only [not_exists, not_and, not_not] at hch
    obtain ⟨v₀, hv₀⟩ := hmv
    have hp : rest.head? = some v₀ := by
      rcases hv₀ with h | h
      · exact absurd (hch v₀ h.1) h.2
      · exact h.2
    have hwge := hw (.node v₀)
    simp only at hwge
    have hℓv₀ : c₂ * (1 - 2 * δ) ≤ ∑ c, R2 N c (.node v₀) * (layer2 N c₁ c₂).apply X2 i c := by
      rw [hlogit]
      have := (hA1p v₀ hp).1
      have := le_max_right (C_A0 es τ c₁ (fun j => l₂ (3 * j + 2)) x v₀) 0
      have := le_max_left (C_A1 τ c₂ (fun k => l₁ (3 * es.length + 3 + (k + 1))) x v₀) 0
      linarith
    have hgap : 2 * δ * c₂ < c₂ * (1 - 2 * δ) := by nlinarith
    have hgap0 : 0 ≤ 2 * δ * c₂ := by positivity
    cases w with
    | node v =>
      refine ⟨v, rfl, ?_⟩
      by_cases hvv : v = v₀
      · subst hvv; exact Or.inr ⟨hch, hp⟩
      · exfalso
        have hnot : ¬ (Adj es x v ∧ v ∉ τ) := fun h => h.2 (hch v h.1)
        have h0 := hA0o v hnot
        have h1 : C_A1 τ c₂ (fun k => l₁ (3 * es.length + 3 + (k + 1))) x v ≤ 2 * δ * c₂ := by
          by_cases hvx : v = x
          · subst hvx; linarith
          · exact hA1o v hvx (by rw [hp]; exact fun h => hvv (Option.some.inj h).symm)
        rw [hlogit v, max_eq_right h0] at hwge
        have := max_le h1 hgap0
        linarith
    | bos => rw [hspec .bos (by intro u; simp)] at hwge; nlinarith
    | sep => rw [hspec .sep (by intro u; simp)] at hwge; nlinarith
    | rsn => rw [hspec .rsn (by intro u; simp)] at hwge; nlinarith


theorem C_shape (L j : ℕ) (t : Tok N) (r : Role) : InputShape N L j (emb2 N L t r j) := by
  refine ⟨?_, ?_, fun v => ?_, by simp [emb2], by simp [emb2], by simp [emb2]⟩
  · cases t with
    | node u =>
      by_cases hr : r = .trace
      · right; refine ⟨u, funext fun v => ?_⟩
        simp [C_emb2_node, hr, Pi.single_apply, eq_comm]
      · left; funext v; simp [C_emb2_node, hr]
    | _ => left; rfl
  · cases t with
    | node u =>
      by_cases hr : r = .trace
      · left; funext v; simp [C_emb2_node, hr]
      · right; refine ⟨u, funext fun v => ?_⟩
        simp [C_emb2_node, hr, Pi.single_apply, eq_comm]
    | _ => left; rfl
  · cases t with
    | node u => simp [C_emb2_node]
    | _ => exact ⟨rfl, rfl⟩

theorem two_layer_dfs (N : ℕ) (c₁ c₂ : ℝ) (hc₂ : 0 < c₂) (hc : c₂ < c₁) :
    ∃ (L : ℕ) (L1 : Layer (Coord2 N)), L ≤ 3 * N ^ 2 + 2 * N + 4 ∧ L1.H = 3 ∧
      L1.act = Act.softmax ∧
      (∀ h r c, |L1.KQ h r c| ≤ 8 * (L : ℝ) ^ 2 * Real.log (16 * L * c₁ / (c₁ - c₂)) + 2) ∧
      (∀ h r c, |L1.V h r c| ≤ 2) ∧ (∀ r c, |L1.O r c| ≤ 2) ∧
      ∀ (es : List (Fin N × Fin N)) (root tgt : Fin N) (τ stk : List (Fin N)),
        es.Nodup → DFSTrace (Adj es) root τ stk → (∃ v, DFSNext (Adj es) τ stk v) →
        ∀ w, IsMax ((⟨emb2 N L, [L1, layer2 N c₁ c₂], R2 N⟩ : TF N (Coord2 N)).logits
            (dfsInput es tgt τ)) w →
          ∃ v, w = .node v ∧ DFSNext (Adj es) τ stk v := by
  have hc₁ : 0 < c₁ := by linarith
  set δ : ℝ := (c₁ - c₂) / (16 * c₁) with hδdef
  have hδ0 : 0 < δ := div_pos (by linarith) (by positivity)
  have hδ16 : δ < 1 / 16 := by
    rw [hδdef, div_lt_iff₀ (by positivity)]; linarith
  have hδ4 : δ ≤ (c₁ - c₂) / (4 * c₁) := by
    rw [hδdef]
    exact div_le_div_of_nonneg_left (by linarith) (by positivity) (by linarith)
  set L : ℕ := 3 * N ^ 2 + 2 * N + 4 with hLdef
  have hL : 1 ≤ L := by omega
  obtain ⟨L1, hH, hact, hKQ, hV, hO, hcopy⟩ := first_layer N L δ hδ0 (by linarith) hL
  refine ⟨L, L1, le_rfl, hH, hact, ?_, hV, hO, ?_⟩
  · have hLδ : (L : ℝ) / δ = 16 * L * c₁ / (c₁ - c₂) := by
      rw [hδdef]
      have : c₁ - c₂ ≠ 0 := by linarith
      field_simp
    intro h r c
    rw [← hLδ]; exact hKQ h r c
  · intro es root tgt τ stk hes hτ hmv w hw
    have hM : es.length ≤ N ^ 2 := by
      have := hes.length_le_card
      simpa [Fintype.card_prod, Fintype.card_fin, sq] using this
    have ht : τ.length ≤ 2 * N := dfs_length hτ
    have hlen := C_len es tgt τ
    have hTL : (dfsInput es tgt τ).length ≤ L := by omega
    have hT0 : (dfsInput es tgt τ).length ≠ 0 := by omega
    set X := embSeq (emb2 N L) (dfsInput es tgt τ) with hXdef
    have hshape : ∀ j : Fin (dfsInput es tgt τ).length, InputShape N L j (X j) :=
      fun j => C_shape L j _ _
    have h0 : ∀ j : Fin (dfsInput es tgt τ).length, (j : ℕ) = 0 →
        ∀ v, X j (blk 0 v) = 0 ∧ X j (blk 3 v) = 0 := by
      intro j hj v
      rw [hXdef, C_embSeq_eq, C_embSeq_eq, hj]
      exact ⟨C_Xn_bos L es tgt τ 0 v, C_Xn_bos L es tgt τ 3 v⟩
    have hCP := hcopy _ X hTL hshape h0
    have hlog : ∀ w', (⟨emb2 N L, [L1, layer2 N c₁ c₂], R2 N⟩ : TF N (Coord2 N)).logits
        (dfsInput es tgt τ) w' = ∑ c, R2 N c w' * (layer2 N c₁ c₂).apply (L1.apply X)
          ⟨(dfsInput es tgt τ).length - 1, by omega⟩ c := by
      intro w'
      simp only [TF.logits, hT0, ↓reduceDIte, TF.run, List.foldl]
      rfl
    have hw' : IsMax (fun w => ∑ c, R2 N c w * (layer2 N c₁ c₂).apply (L1.apply X)
        ⟨(dfsInput es tgt τ).length - 1, by omega⟩ c) w := by
      intro w'
      have := hw w'
      rw [hlog, hlog] at this
      exact this
    exact two_layer_core N L c₁ c₂ δ hc₂ hc hδ0.le hδ4 es root tgt τ stk hes hτ hmv
      (L1.apply X) hCP _ (by simp only; omega) w hw'


end DFSExpr
