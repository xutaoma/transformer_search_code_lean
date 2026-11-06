import DFSLean.Model

namespace DFS
open Real Finset Filter Topology Set
variable {N K : ℕ}

/-! ## Basic evaluations -/

private lemma T_bil_oh (x y : Fin N) (M : Fin N → Fin N → ℝ) : bil (oh x) M (oh y) = M x y := by
  simp [bil, oh]

private lemma T_bil_zero (M : Fin N → Fin N → ℝ) (y : Fin N → ℝ) : bil 0 M y = 0 := by
  simp [bil]

@[simp] private lemma T_mk4_0 (a b c d : Fin N → ℝ) : mk4 a b c d 0 = a := rfl
@[simp] private lemma T_mk4_1 (a b c d : Fin N → ℝ) : mk4 a b c d 1 = b := rfl
@[simp] private lemma T_mk4_2 (a b c d : Fin N → ℝ) : mk4 a b c d 2 = c := rfl
@[simp] private lemma T_mk4_3 (a b c d : Fin N → ℝ) : mk4 a b c d 3 = d := rfl

/-! ## The query -/

private lemma T_last_aux (cot : List (Fin N)) : ∀ (root : Fin N) (b0 : Fin N → ℝ), ∃ b,
    ((cot.zip (root :: cot)).map (fun p => mk4 (oh p.1) (oh p.2) 0 0)).getLast?.getD
        (mk4 (oh root) b0 0 0)
      = mk4 (oh ((root :: cot).getLast (List.cons_ne_nil _ _))) b 0 0 := by
  induction cot with
  | nil => intro root b0; exact ⟨b0, by simp⟩
  | cons n rest ih =>
    intro root b0
    obtain ⟨b, hb⟩ := ih n (oh root)
    refine ⟨b, ?_⟩
    simp only [List.zip_cons_cons, List.map_cons, List.getLast?_cons, Option.getD_some,
      List.getLast_cons_cons]
    exact hb

private lemma T_query (c : Ctx N) : ∃ b, c.query = mk4 (oh c.cur) b 0 0 := by
  obtain ⟨b, hb⟩ := T_last_aux c.cot c.root 0
  refine ⟨b, ?_⟩
  unfold Ctx.query Ctx.hidden
  rw [List.getLast?_append]
  simp only [List.getLast?_append, List.getLast?_cons, List.getLast?_nil, Option.getD_none,
    Option.getD_some, Option.some_or]
  have hcur : c.cur = (c.root :: c.cot).getLast (List.cons_ne_nil _ _) := rfl
  have hn : c.nodes = c.root :: c.cot := rfl
  rw [hcur, ← hb, hn]
  generalize (List.map (fun p => mk4 (oh p.1) (oh p.2) 0 0) (c.cot.zip (c.root :: c.cot))).getLast?
    = o
  cases o <;> rfl

private lemma T_query0 (c : Ctx N) : c.query 0 = oh c.cur := by
  obtain ⟨b, hb⟩ := T_query c; rw [hb]; rfl

private lemma T_query2 (c : Ctx N) : c.query 2 = 0 := by
  obtain ⟨b, hb⟩ := T_query c; rw [hb]; rfl

private lemma T_query3 (c : Ctx N) : c.query 3 = 0 := by
  obtain ⟨b, hb⟩ := T_query c; rw [hb]; rfl

theorem logit_of_ne (θ : Params N) (c : Ctx N) (v : Fin N) (hv : v ≠ c.cur) :
    logit θ c v = max (head1 θ c v) 0 + max (head2 θ c v) 0 := by
  simp [logit, hv, T_query2, T_query3]



/-! ## Splitting the sum over the hidden states -/

private lemma T_hidden_sum (F : Hid N → ℝ) (c : Ctx N) :
    (c.hidden.map F).sum = F (mk4 0 0 0 0)
      + (c.edges.map fun e => F (mk4 0 0 0 (oh e.1)) + F (mk4 0 0 (oh e.1) (oh e.2))
          + F (mk4 0 0 (oh e.2) 0)).sum
      + (F (mk4 0 0 0 (oh c.tgt)) + F (mk4 0 0 (oh c.tgt) 0) + F (mk4 (oh c.root) 0 0 0))
      + ((c.cot.zip c.nodes).map fun p => F (mk4 (oh p.1) (oh p.2) 0 0)).sum := by
  have hE : ∀ E : List (Fin N × Fin N),
      ((E.flatMap fun e => [mk4 0 0 0 (oh e.1), mk4 0 0 (oh e.1) (oh e.2), mk4 0 0 (oh e.2) 0]).map
        F).sum = (E.map fun e => F (mk4 0 0 0 (oh e.1)) + F (mk4 0 0 (oh e.1) (oh e.2))
          + F (mk4 0 0 (oh e.2) 0)).sum := by
    intro E
    induction E with
    | nil => simp
    | cons e E ih => simp [List.flatMap_cons, ih]; ring
  simp only [Ctx.hidden, List.map_append, List.sum_append, hE, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.map_map, Function.comp_def]
  ring

private lemma T_head_apply (f : Hid N → ℝ) (g : Hid N → Fin N → ℝ) (l : List (Hid N)) (v : Fin N) :
    (l.map fun x => f x • g x).sum v = (l.map fun x => f x * g x v).sum := by
  rw [Pi.list_sum_apply, List.map_map]
  rfl

private lemma T_zip_fst (cot : List (Fin N)) : ∀ (root : Fin N) (g : Fin N → ℝ),
    ((cot.zip (root :: cot)).map fun p => g p.1).sum = (cot.map g).sum := by
  induction cot with
  | nil => intro root g; simp
  | cons n rest ih => intro root g; simp only [List.zip_cons_cons, List.map_cons, List.sum_cons, ih]

private lemma T_sum_map_neg {α : Type*} (l : List α) (f : α → ℝ) :
    (l.map fun x => -f x).sum = -(l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-! ## General parameters -/

private lemma T_head1_eq (θ : Params N) (c : Ctx N) (v : Fin N) :
    head1 θ c v = (c.edges.map fun e => θ 1 e.1 c.cur * oh e.2 v).sum
      - θ 0 c.root c.cur * oh c.root v
      - ((c.cot.zip c.nodes).map fun p => θ 0 p.1 c.cur * oh p.1 v).sum := by
  unfold head1
  rw [T_head_apply, T_hidden_sum]
  simp only [score1, val1, T_mk4_0, T_mk4_2, T_mk4_3, T_query0, T_bil_oh, T_bil_zero,
    Pi.sub_apply, Pi.zero_apply, zero_add, add_zero, sub_zero, zero_sub, mul_zero, zero_mul,
    mul_neg, T_sum_map_neg]
  ring

private lemma T_head2_eq (θ : Params N) (c : Ctx N) (v : Fin N) :
    head2 θ c v = -(θ 2 c.root c.cur * oh c.root v)
      + ((c.cot.zip c.nodes).map fun p =>
          (θ 2 p.1 c.cur + θ 3 p.2 c.cur) * (oh p.2 v - oh p.1 v)).sum := by
  unfold head2
  rw [T_head_apply, T_hidden_sum]
  simp only [score2, val2, T_mk4_0, T_mk4_1, T_query0, T_bil_oh, T_bil_zero,
    Pi.sub_apply, Pi.zero_apply, zero_add, add_zero, sub_zero, zero_sub, mul_zero,
    mul_neg, List.map_const', List.sum_replicate, smul_zero]

/-! ## Permutation-invariant parameters -/

private lemma T_iota0 (s : Fin 8 → ℝ) (x y : Fin N) :
    iota s 0 x y = if x = y then s 0 else s 1 := rfl
private lemma T_iota1 (s : Fin 8 → ℝ) (x y : Fin N) :
    iota s 1 x y = if x = y then s 2 else s 3 := rfl
private lemma T_iota2 (s : Fin 8 → ℝ) (x y : Fin N) :
    iota s 2 x y = if x = y then s 4 else s 5 := rfl
private lemma T_iota3 (s : Fin 8 → ℝ) (x y : Fin N) :
    iota s 3 x y = if x = y then s 6 else s 7 := rfl

private lemma T_edge_sum (E : List (Fin N × Fin N)) (w v : Fin N) (p q : ℝ) :
    (E.map fun e => (if e.1 = w then p else q) * oh e.2 v).sum
      = q * ((E.filter fun e => e.2 = v).length : ℝ)
        + (p - q) * ((E.filter fun e => e = (w, v)).length : ℝ) := by
  induction E with
  | nil => simp
  | cons e E ih =>
    obtain ⟨a, b⟩ := e
    rw [List.map_cons, List.sum_cons, ih, List.filter_cons, List.filter_cons]
    simp only [Prod.mk.injEq, oh]
    rcases eq_or_ne b v with rfl | hb
    · by_cases ha : a = w <;> simp [ha] <;> ring
    · by_cases ha : a = w <;> simp [ha, hb, hb.symm]

private lemma T_node_sum (L : List (Fin N)) (w v : Fin N) (p q : ℝ) :
    (L.map fun n => (if n = w then p else q) * oh n v).sum
      = (L.count v : ℝ) * (if v = w then p else q) := by
  induction L with
  | nil => simp
  | cons n L ih =>
    rw [List.map_cons, List.sum_cons, ih, List.count_cons]
    simp only [oh]
    by_cases hn : v = n
    · subst hn; simp; split_ifs <;> ring
    · simp [hn, Ne.symm hn]

/-- Forward head (Table 1): `(head₁)_v = b₂ d_v^in + (a₂ - b₂)·[n_t → v] - m_v·A₁[v, n_t]`. -/
theorem head1_iota (s : Fin 8 → ℝ) (c : Ctx N) (v : Fin N) :
    head1 (iota s) c v =
      s 3 * c.din v + (s 2 - s 3) * c.ecnt c.cur v - c.mcnt v * (if v = c.cur then s 0 else s 1) := by
  have hn : c.nodes = c.root :: c.cot := rfl
  rw [T_head1_eq, hn, T_zip_fst c.cot c.root (fun n => iota s 0 n c.cur * oh n v)]
  simp only [T_iota0, T_iota1]
  have h1 := T_edge_sum c.edges c.cur v (s 2) (s 3)
  have h2 := T_node_sum (c.root :: c.cot) c.cur v (s 0) (s 1)
  rw [List.map_cons, List.sum_cons] at h2
  rw [h1, Ctx.din, Ctx.ecnt, Ctx.mcnt, hn]
  linarith



/-- Telescoping of the backtracking-head sum over the CoT transitions. -/
private lemma T_tele (s : Fin 8 → ℝ) (w v : Fin N) (hv : v ≠ w) (cot : List (Fin N)) :
    ∀ root : Fin N,
    ((cot.zip (root :: cot)).map fun p =>
        ((if p.1 = w then s 4 else s 5) + (if p.2 = w then s 6 else s 7)) * (oh p.2 v - oh p.1 v)).sum
      = (s 5 + s 7) * (oh root v - oh ((root :: cot).getLast (List.cons_ne_nil _ _)) v)
        + (s 4 - s 5) * (((cot.zip (root :: cot)).filter fun p => p.2 = v ∧ p.1 = w).length : ℝ)
        - (s 6 - s 7) * (((cot.zip (root :: cot)).filter fun p => p.2 = w ∧ p.1 = v).length : ℝ) := by
  induction cot with
  | nil => intro root; simp
  | cons n rest ih =>
    intro root
    rw [List.zip_cons_cons, List.map_cons, List.sum_cons, ih n, List.getLast_cons_cons]
    clear ih
    simp only [← List.countP_eq_length_filter, List.countP_cons]
    generalize (n :: rest).getLast _ = L
    generalize List.countP (fun p => decide (p.2 = v ∧ p.1 = w)) (rest.zip (n :: rest)) = A
    generalize List.countP (fun p => decide (p.2 = w ∧ p.1 = v)) (rest.zip (n :: rest)) = B
    simp only [oh]
    generalize (if v = L then (1 : ℝ) else 0) = I
    push_cast
    simp only [decide_eq_true_eq, @eq_comm _ root v, @eq_comm _ n v]
    by_cases h1 : n = w <;> by_cases h2 : root = w <;> by_cases h3 : v = n <;>
      by_cases h4 : v = root <;> simp_all <;> ring

/-- Backtracking head (Table 2, `v ≠ n_t`):
`(head₂)_v = (g₁ - d₁) A_{v→n_t} - (g₂ - d₂) A_{n_t→v} + d₂·[v = n_Root]`. -/
theorem head2_iota (s : Fin 8 → ℝ) (c : Ctx N) (v : Fin N) (hv : v ≠ c.cur) :
    head2 (iota s) c v =
      (s 4 - s 5) * c.trans v c.cur - (s 6 - s 7) * c.trans c.cur v +
        (if v = c.root then s 7 else 0) := by
  have hn : c.nodes = c.root :: c.cot := rfl
  have hcur : c.cur = (c.root :: c.cot).getLast (List.cons_ne_nil _ _) := rfl
  rw [T_head2_eq]
  simp only [T_iota2, T_iota3]
  rw [hn, T_tele s c.cur v hv c.cot c.root, ← hcur, Ctx.trans, Ctx.trans, hn]
  simp only [oh, hv, ite_false]
  by_cases h : v = c.root
  · have hr : c.root ≠ c.cur := h ▸ hv
    simp only [h, ite_true, hr, ite_false]
    ring
  · simp only [h, ite_false]
    ring



end DFS
