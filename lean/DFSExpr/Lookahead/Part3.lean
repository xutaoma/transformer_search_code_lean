import DFSExpr.Lookahead.Part2

/-!
# Package E, part 3: layout of the DFS input, sums over positions, first-layer invariant
-/

noncomputable section

open Matrix

namespace DFSExpr

variable {N : ℕ}

/-! ### Layout of `dfsInput` -/

theorem E_edgeToks_len (es : List (Fin N × Fin N)) : (edgeToks es).length = 3 * es.length := by
  induction es with
  | nil => simp [edgeToks]
  | cons e es ih => simp [edgeToks] at ih ⊢; omega

theorem E_edgeToks_get (es : List (Fin N × Fin N)) (m : ℕ) (hm : m < es.length) :
    (edgeToks es)[3 * m]? = some (.node es[m].1, .graph) ∧
    (edgeToks es)[3 * m + 1]? = some (.node es[m].2, .graph) ∧
    (edgeToks es)[3 * m + 2]? = some (.sep, .graph) := by
  induction es generalizing m with
  | nil => simp at hm
  | cons e es ih =>
    have he : edgeToks (e :: es) = [(.node e.1, .graph), (.node e.2, .graph), (.sep, .graph)] ++
        edgeToks es := by simp [edgeToks]
    rw [he]
    cases m with
    | zero => simp
    | succ m =>
      have hm' : m < es.length := by simpa using hm
      obtain ⟨h1, h2, h3⟩ := ih m hm'
      refine ⟨?_, ?_, ?_⟩
      · rw [List.getElem?_append_right (by simp)]
        simpa [show 3 * (m + 1) - 3 = 3 * m by omega] using h1
      · rw [List.getElem?_append_right (by simp; omega)]
        simpa [show 3 * (m + 1) + 1 - 3 = 3 * m + 1 by omega] using h2
      · rw [List.getElem?_append_right (by simp; omega)]
        simpa [show 3 * (m + 1) + 2 - 3 = 3 * m + 2 by omega] using h3

theorem E_G_edge (es : List (Fin N × Fin N)) (q : ℕ) : E_G (edgeToks es)[q]? = none := by
  rcases h : (edgeToks es)[q]? with _ | x
  · rfl
  · have := List.mem_of_getElem? h
    simp only [edgeToks, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at this
    obtain ⟨_, _, hx⟩ := this
    rcases hx with rfl | rfl | rfl <;> rfl

section layout

variable (es : List (Fin N × Fin N)) (tgt : Fin N) (τ : List (Fin N))

theorem E_lay_len : (dfsInput es tgt τ).length = 3 * es.length + 3 + τ.length := by
  simp [dfsInput, E_edgeToks_len]; omega

theorem E_lay_0 : (dfsInput es tgt τ)[0]? = some (.bos, .graph) := by
  simp [dfsInput]

theorem E_lay_e (q : ℕ) (hq : q < 3 * es.length) :
    (dfsInput es tgt τ)[q + 1]? = (edgeToks es)[q]? := by
  simp [dfsInput, List.getElem?_append, E_edgeToks_len]
  omega

theorem E_lay_t : (dfsInput es tgt τ)[3 * es.length + 1]? = some (.node tgt, .goal) := by
  simp [dfsInput, E_edgeToks_len]

theorem E_lay_r : (dfsInput es tgt τ)[3 * es.length + 2]? = some (.rsn, .goal) := by
  simp only [dfsInput, List.cons_append, List.append_assoc]
  rw [show 3 * es.length + 2 = (3 * es.length + 1) + 1 by omega, List.getElem?_cons_succ,
    List.getElem?_append_right (by rw [E_edgeToks_len]; omega), E_edgeToks_len,
    show 3 * es.length + 1 - 3 * es.length = 1 by omega]
  simp

theorem E_lay_tr (k : ℕ) :
    (dfsInput es tgt τ)[3 * es.length + 3 + k]? = τ[k]?.map (fun v => (.node v, .trace)) := by
  simp only [dfsInput, List.cons_append, List.append_assoc]
  rw [show 3 * es.length + 3 + k = (3 * es.length + 2 + k) + 1 by omega, List.getElem?_cons_succ,
    List.getElem?_append_right (by rw [E_edgeToks_len]; omega), E_edgeToks_len,
    show 3 * es.length + 2 + k - 3 * es.length = k + 2 by omega]
  simp

theorem E_G_pos (p : ℕ) :
    E_G (dfsInput es tgt τ)[p]? = if p = 3 * es.length + 1 then some tgt else none := by
  rcases (show p = 0 ∨ (1 ≤ p ∧ p ≤ 3 * es.length) ∨ p = 3 * es.length + 1 ∨
      p = 3 * es.length + 2 ∨ 3 * es.length + 3 ≤ p by omega) with h | h | h | h | h
  · subst h; simp [E_lay_0, E_G]
  · obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [E_lay_e es tgt τ q (by omega), if_neg (by omega)]
    exact E_G_edge es q
  · subst h; simp [E_lay_t, E_G]
  · subst h; rw [E_lay_r, if_neg (by omega)]; rfl
  · obtain ⟨k, rfl⟩ : ∃ k, p = 3 * es.length + 3 + k := ⟨p - (3 * es.length + 3), by omega⟩
    rw [E_lay_tr, if_neg (by omega)]
    cases τ[k]? <;> rfl

/-! ### Classes of the positions -/

theorem E_cls_0 : E_cls (dfsInput es tgt τ) 0 = .bos := by
  simp [E_cls, E_lay_0, E_clsOf]

theorem E_cls_src (m : ℕ) (hm : m < es.length) : E_cls (dfsInput es tgt τ) (3 * m + 1) = .other := by
  have h1 := (E_edgeToks_get es m hm).1
  have hc : ¬ ((3 * m + 1 + 1) % 3 = 0) := by omega
  simp only [E_cls, E_lay_e es tgt τ (3 * m) (by omega), h1, hc, decide_false]
  rfl

theorem E_cls_rec (m : ℕ) (hm : m < es.length) :
    E_cls (dfsInput es tgt τ) (3 * m + 2) = .rcd (some es[m].1) es[m].2 := by
  obtain ⟨h1, h2, _⟩ := E_edgeToks_get es m hm
  have hc : (3 * m + 2 + 1) % 3 = 0 := by omega
  simp only [E_cls, show 3 * m + 2 - 1 = 3 * m + 1 by omega, show 3 * m + 2 = 3 * m + 1 + 1 by omega,
    E_lay_e es tgt τ (3 * m) (by omega), E_lay_e es tgt τ (3 * m + 1) (by omega), h1, h2, hc,
    decide_true]
  rfl

theorem E_cls_sep (m : ℕ) (hm : m < es.length) : E_cls (dfsInput es tgt τ) (3 * m + 3) = .other := by
  have h3 := (E_edgeToks_get es m hm).2.2
  simp only [E_cls, show 3 * m + 3 = 3 * m + 2 + 1 by omega,
    E_lay_e es tgt τ (3 * m + 2) (by omega), h3]
  rfl

theorem E_cls_t : E_cls (dfsInput es tgt τ) (3 * es.length + 1) = .other := by
  have hc : ¬ ((3 * es.length + 1 + 1) % 3 = 0) := by omega
  simp only [E_cls, E_lay_t, hc, decide_false]
  rfl

theorem E_cls_r : E_cls (dfsInput es tgt τ) (3 * es.length + 2) = .other := by
  simp only [E_cls, E_lay_r]
  rfl

end layout

/-- Classes of the trace positions. -/
def E_trCls : List (Fin N) → Option (Fin N) → List (E_Cls N)
  | [], _ => []
  | y :: ys, o => .tr y o :: E_trCls ys (some y)

/-- Class of the `k`-th trace position, with `o` the predecessor of the first one. -/
def E_trAt (l : List (Fin N)) (o : Option (Fin N)) (k : ℕ) : E_Cls N :=
  match l[k]? with
  | some y => .tr y (if k = 0 then o else l[k - 1]?)
  | none => .other

theorem E_trAt_zero (a : Fin N) (l : List (Fin N)) (o : Option (Fin N)) :
    E_trAt (a :: l) o 0 = .tr a o := rfl

theorem E_trAt_succ (a : Fin N) (l : List (Fin N)) (o : Option (Fin N)) (k : ℕ) :
    E_trAt (a :: l) o (k + 1) = E_trAt l (some a) k := by
  cases k <;> simp [E_trAt]

theorem E_EA_map (o : Option (Fin N)) :
    E_A (o.map fun v => ((Tok.node v : Tok N), Role.trace)) = o := by
  cases o <;> rfl

theorem E_cls_tr (es : List (Fin N × Fin N)) (tgt : Fin N) (τ : List (Fin N)) (k : ℕ) :
    E_cls (dfsInput es tgt τ) (3 * es.length + 3 + k) = E_trAt τ none k := by
  have hprev : E_A (dfsInput es tgt τ)[3 * es.length + 3 + k - 1]? =
      if k = 0 then none else τ[k - 1]? := by
    rcases k with _ | k
    · simp only [show 3 * es.length + 3 + 0 - 1 = 3 * es.length + 2 by omega, E_lay_r]; rfl
    · simp only [show 3 * es.length + 3 + (k + 1) - 1 = 3 * es.length + 3 + k by omega, E_lay_tr,
        E_EA_map]
      simp
  simp only [E_cls, E_trAt, E_lay_tr]
  rcases h : τ[k]? with _ | y
  · rfl
  · simp only [Option.map_some]
    rw [← hprev]
    rfl

theorem E_trace_sum (F : E_Cls N → ℝ) : ∀ (l : List (Fin N)) (o : Option (Fin N)),
    ∑ k ∈ Finset.range l.length, F (E_trAt l o k) = ((E_trCls l o).map F).sum
  | [], o => by simp [E_trCls]
  | a :: l, o => by
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [E_trAt_succ, E_trAt_zero, E_trace_sum F l (some a), E_trCls, List.map_cons,
      List.sum_cons]
    ring

theorem E_sum3 (g : ℕ → ℝ) (M : ℕ) :
    ∑ q ∈ Finset.range (3 * M), g q =
      ∑ m ∈ Finset.range M, (g (3 * m) + g (3 * m + 1) + g (3 * m + 2)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 3 * (M + 1) = 3 * M + 1 + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

/-- **Master sum over the positions of a DFS input**: a function of the position classes that
vanishes on `other` sums to its value at BOS, over the edge records, and over the trace. -/
theorem E_master (es : List (Fin N × Fin N)) (tgt : Fin N) (τ : List (Fin N))
    (F : E_Cls N → ℝ) (hF : F .other = 0) :
    ∑ p : Fin (dfsInput es tgt τ).length, F (E_cls (dfsInput es tgt τ) p) =
      F .bos + (es.map fun e => F (.rcd (some e.1) e.2)).sum + ((E_trCls τ none).map F).sum := by
  rw [← Finset.sum_range (fun p => F (E_cls (dfsInput es tgt τ) p)), E_lay_len,
    Finset.sum_range_add, show 3 * es.length + 3 = (3 * es.length + 1) + 1 + 1 by ring,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ',
    E_sum3 (fun q => F (E_cls (dfsInput es tgt τ) (q + 1)))]
  rw [show 3 * es.length + 1 + 1 = 3 * es.length + 2 by ring, E_cls_t, E_cls_r, E_cls_0, hF]
  have hrec : ∑ m ∈ Finset.range es.length,
      (F (E_cls (dfsInput es tgt τ) (3 * m + 1)) + F (E_cls (dfsInput es tgt τ) (3 * m + 1 + 1)) +
        F (E_cls (dfsInput es tgt τ) (3 * m + 2 + 1))) =
      (es.map fun e => F (.rcd (some e.1) e.2)).sum := by
    rw [Finset.sum_range (fun m => F (E_cls (dfsInput es tgt τ) (3 * m + 1)) +
        F (E_cls (dfsInput es tgt τ) (3 * m + 1 + 1)) +
        F (E_cls (dfsInput es tgt τ) (3 * m + 2 + 1))),
      ← Fin.sum_univ_fun_getElem es (fun e => F (.rcd (some e.1) e.2))]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [show 3 * (m : ℕ) + 1 + 1 = 3 * m + 2 by ring, show 3 * (m : ℕ) + 2 + 1 = 3 * m + 3 by ring,
      E_cls_src es tgt τ m m.2, E_cls_rec es tgt τ m m.2, E_cls_sep es tgt τ m m.2, hF]
    ring
  have htr : ∑ k ∈ Finset.range τ.length, F (E_cls (dfsInput es tgt τ) (3 * es.length + 3 + k)) =
      ((E_trCls τ none).map F).sum := by
    simp only [E_cls_tr]
    exact E_trace_sum F τ none
  rw [hrec, htr]
  ring

/-! ### Trace sums -/

theorem E_tr_a (v : Fin N) : ∀ (l : List (Fin N)) (o : Option (Fin N)),
    ((E_trCls l o).map fun c => c.a v).sum = (l.count v : ℝ)
  | [], _ => by simp [E_trCls]
  | y :: l, o => by
    rw [E_trCls, List.map_cons, List.sum_cons, E_tr_a v l (some y)]
    simp only [List.count_cons, E_Cls.a, beq_iff_eq, Nat.cast_add, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero]
    ring

theorem E_tr_b_le (x : Fin N) : ∀ (l : List (Fin N)) (o : Option (Fin N)),
    ((E_trCls l o).map fun c => c.b x).sum ≤ (if o = some x then 1 else 0) + (l.count x : ℝ)
  | [], _ => by simp [E_trCls]; split_ifs <;> norm_num
  | y :: l, o => by
    have ih := E_tr_b_le x l (some y)
    have hb : (E_Cls.tr y o).b x = if o = some x then 1 else 0 := by
      rcases o with _ | p <;> simp [E_Cls.b]
    simp only [E_trCls, List.map_cons, List.sum_cons, hb, List.count_cons, beq_iff_eq,
      Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Option.some.injEq] at ih ⊢
    linarith

theorem E_trCls_some : ∀ (l : List (Fin N)) (p : Fin N),
    E_trCls l (some p) = (List.zip (p :: l) l).map (fun pq => .tr pq.2 (some pq.1))
  | [], _ => rfl
  | y :: l, p => by
    simp only [E_trCls, E_trCls_some l y, List.zip_cons_cons, List.map_cons]

theorem E_sum_count {α : Type} [DecidableEq α] (a : α) : ∀ l : List α,
    (l.map fun e => if e = a then (1 : ℝ) else 0).sum = (l.count a : ℝ)
  | [] => by simp
  | b :: l => by
    simp only [List.map_cons, List.sum_cons, E_sum_count a l, List.count_cons, beq_iff_eq,
      Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    ring

/-! ### The invariant after the first layer -/

/-- The blocks that no later layer (before the last) changes. -/
def E_Static (es : List (Fin N × Fin N)) (tgt : Fin N) (τ : List (Fin N))
    (X : Fin (dfsInput es tgt τ).length → E_I N → ℝ) : Prop :=
  ∀ (p : Fin (dfsInput es tgt τ).length) (v : Fin N),
    X p (.inl (.a, v)) = (E_cls (dfsInput es tgt τ) p).a v ∧
    X p (.inl (.UP, v)) - X p (.inl (.UM, v)) = (E_cls (dfsInput es tgt τ) p).U v ∧
    X p (.inl (.VP, v)) - X p (.inl (.VM, v)) = (E_cls (dfsInput es tgt τ) p).V v ∧
    X p (.inl (.bP, v)) - X p (.inl (.bM, v)) = (E_cls (dfsInput es tgt τ) p).b v ∧
    X p (.inl (.GP, v)) - X p (.inl (.GM, v)) = (if tgt = v then 1 else 0) ∧
    X p E_ρ = 1 ∧ X p E_ζ = (E_cls (dfsInput es tgt τ) p).z ∧
    X p (.inl (.ZP, v)) = 0 ∧ X p (.inl (.ZM, v)) = 0

/-- State after layer 1. -/
def E_Inv1 (es : List (Fin N × Fin N)) (tgt : Fin N) (τ : List (Fin N))
    (X : Fin (dfsInput es tgt τ).length → E_I N → ℝ) : Prop :=
  E_Static es tgt τ X ∧ ∀ (p : Fin (dfsInput es tgt τ).length) (v : Fin N),
    X p (.inl (.SP, v)) - X p (.inl (.SM, v)) = (E_cls (dfsInput es tgt τ) p).U v ∧
    X p (.inl (.CP, v)) - X p (.inl (.CM, v)) = (E_cls (dfsInput es tgt τ) p).V v ∧
    X p (.inl (.Df, v)) = 0 ∧ X p (.inl (.Db, v)) = 0

theorem E_L1_inv (L : ℕ) (hL : 1 ≤ L) (es : List (Fin N × Fin N)) (tgt : Fin N)
    (τ : List (Fin N)) (hT : (dfsInput es tgt τ).length ≤ L) :
    E_Inv1 es tgt τ ((E_L1 L).apply (embSeq (E_emb L) (dfsInput es tgt τ))) := by
  have hjg : 3 * es.length + 1 < (dfsInput es tgt τ).length := by rw [E_lay_len]; omega
  have hg : ∀ j : Fin (dfsInput es tgt τ).length, E_G (dfsInput es tgt τ)[j.1]? =
      if j = ⟨3 * es.length + 1, hjg⟩ then some tgt else none := by
    intro j
    rw [E_G_pos]
    simp only [Fin.ext_iff]
  refine ⟨fun p v => ⟨?_, E_L1_U L (dfsInput es tgt τ) hT p v, E_L1_V L (dfsInput es tgt τ) hT p v, E_L1_b L (dfsInput es tgt τ) hT p v,
    E_L1_G L (dfsInput es tgt τ) hL hT tgt _ hg p v, ?_, ?_, ?_, ?_⟩, fun p v => ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [E_L1_frameB L (dfsInput es tgt τ) p .a (by simp), E_X_a, E_cls, E_clsOf_a]
  · rw [E_L1_frameS, E_X_rho]
  · rw [E_L1_frameS, E_X_zeta, E_cls, E_clsOf_z]
  · rw [E_L1_frameB L (dfsInput es tgt τ) p .ZP (by simp), E_X_other L (dfsInput es tgt τ) p .ZP (by decide)]
  · rw [E_L1_frameB L (dfsInput es tgt τ) p .ZM (by simp), E_X_other L (dfsInput es tgt τ) p .ZM (by decide)]
  · rw [E_L1_S, E_L1_U L (dfsInput es tgt τ) hT p v]
  · rw [E_L1_C, E_L1_V L (dfsInput es tgt τ) hT p v]
  · rw [E_L1_frameB L (dfsInput es tgt τ) p .Df (by simp), E_X_other L (dfsInput es tgt τ) p .Df (by decide)]
  · rw [E_L1_frameB L (dfsInput es tgt τ) p .Db (by simp), E_X_other L (dfsInput es tgt τ) p .Db (by decide)]

end DFSExpr
