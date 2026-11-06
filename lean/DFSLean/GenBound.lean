import DFSLean.Tables

/-!
# Package S: DFS traces and the generalization loss (proof of Thm 4.2, second part)

* `S_Inv`: the DFS invariant along a valid prefix `l` with state `(S, V) = dstate r l`:
  the stack is `n_t :: rest`, has no duplicates and lies in `V`; `V` is the set of nodes of
  `r :: l`; `|l| + |S| + 1 = 2|V|`; every transition count `A_{x→y} ≤ 1`; and
  `A_{x→y} + B_{x,y}` is symmetric, where `B_{x,y}` counts adjacent stack pairs `(x, y)`
  (`x` directly above `y`). Consequences: `A_{p→n_t} = 1`, `A_{n_t→p} = 0` for the stack parent `p`,
  and `A_{w→n_t} = A_{n_t→w}` for every other `w`.
* `trace_length_le`: from `|l| + |S| + 1 = 2|V| ≤ 2N`, `|S| ≥ 1`.
* `genLoss_bound`: per step, `-log ∑_{C_t} p ≤ N e^{B - L}` (`log x ≤ x - 1`) with `L` a lower bound
  on one admissible logit and `B` an upper bound on all non-admissible ones.
-/

namespace DFS
open Real Finset Filter Topology Set
variable {N K : ℕ}

/-- Current node `(r :: l).getLast`. -/
def S_cur (r : Fin N) (l : List (Fin N)) : Fin N := (r :: l).getLast (List.cons_ne_nil _ _)

/-- Transition counts `A_{x → y}` (as in `Ctx.trans`). -/
def S_A (r : Fin N) (l : List (Fin N)) (x y : Fin N) : ℕ :=
  ((l.zip (r :: l)).filter fun p => p.2 = x ∧ p.1 = y).length

/-- Count of adjacent stack pairs `(x, y)` (`x` directly above `y`). -/
def S_B (S : List (Fin N)) (x y : Fin N) : ℕ := (S.zip S.tail).count (x, y)

lemma S_ctx_cur (E : List (Fin N × Fin N)) (tgt r : Fin N) (l : List (Fin N)) :
    (⟨E, tgt, r, l⟩ : Ctx N).cur = S_cur r l := rfl

lemma S_ctx_trans (E : List (Fin N × Fin N)) (tgt r : Fin N) (l : List (Fin N)) (x y : Fin N) :
    (⟨E, tgt, r, l⟩ : Ctx N).trans x y = (S_A r l x y : ℝ) := rfl

lemma S_cur_snoc (r : Fin N) (l : List (Fin N)) (w : Fin N) : S_cur r (l ++ [w]) = w := by
  unfold S_cur
  simp

lemma S_zip_snoc (l : List (Fin N)) (w : Fin N) : ∀ r : Fin N,
    (l ++ [w]).zip (r :: (l ++ [w])) = l.zip (r :: l) ++ [(w, S_cur r l)] := by
  induction l with
  | nil => intro r; rfl
  | cons a l ih =>
    intro r
    show (a, r) :: (l ++ [w]).zip (a :: (l ++ [w])) = (a, r) :: (l.zip (a :: l) ++ _)
    rw [ih a]
    congr 3

lemma S_A_snoc (r : Fin N) (l : List (Fin N)) (w x y : Fin N) :
    S_A r (l ++ [w]) x y = S_A r l x y + if S_cur r l = x ∧ w = y then 1 else 0 := by
  unfold S_A
  rw [S_zip_snoc, List.filter_append, List.length_append]
  congr 1
  by_cases h : S_cur r l = x ∧ w = y
  · simp [h]
  · simp only [List.filter_cons, List.filter_nil, h]
    simp

lemma S_A_not_mem (r : Fin N) (l : List (Fin N)) (x w : Fin N) (hw : w ∉ l) :
    S_A r l x w = 0 := by
  unfold S_A
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  rintro ⟨a, b⟩ hab
  have := (List.of_mem_zip hab).1
  simp only [decide_eq_true_eq, not_and]
  intro _ h; subst h; exact hw this

lemma S_dstate_snoc (r : Fin N) (l : List (Fin N)) (w : Fin N) :
    dstate r (l ++ [w]) = dstep (dstate r l) w := by
  simp [dstate, List.foldl_append]

lemma S_B_cons (S : List (Fin N)) (a x y : Fin N) (hS : S ≠ []) :
    S_B (a :: S) x y = S_B S x y + if (a, S.head hS) = (x, y) then 1 else 0 := by
  obtain ⟨b, S', rfl⟩ := List.exists_cons_of_ne_nil hS
  simp [S_B, List.count_cons]

lemma S_B_top (S : List (Fin N)) (a x : Fin N) (hS : (a :: S).Nodup) : S_B (a :: S) x a = 0 := by
  unfold S_B
  rw [List.count_eq_zero]
  intro h
  have := (List.of_mem_zip h).2
  exact (List.nodup_cons.1 hS).1 this

lemma S_B_cur (S : List (Fin N)) (a w : Fin N) (hS : (a :: S).Nodup) :
    S_B (a :: S) a w = if S.head? = some w then 1 else 0 := by
  cases S with
  | nil => simp [S_B]
  | cons p S' =>
    rw [S_B_cons _ _ _ _ (List.cons_ne_nil _ _)]
    have h0 : S_B (p :: S') a w = 0 := by
      unfold S_B
      rw [List.count_eq_zero]
      intro h
      exact (List.nodup_cons.1 hS).1 (List.of_mem_zip h).1
    simp [h0]


/-- The DFS invariant for a valid prefix `l` from `r` with state `(S, V)`. -/
structure S_Inv (r : Fin N) (l : List (Fin N)) (S : List (Fin N)) (V : Finset (Fin N)) : Prop where
  stk : ∃ rest, S = S_cur r l :: rest
  nodup : S.Nodup
  sub : ∀ x ∈ S, x ∈ V
  vis : ∀ x, x ∈ V ↔ x ∈ r :: l
  len : l.length + S.length + 1 = 2 * V.card
  le1 : ∀ x y, S_A r l x y ≤ 1
  bal : ∀ x y, S_A r l x y + S_B S x y = S_A r l y x + S_B S y x

lemma S_Inv_nil (r : Fin N) : S_Inv r [] (dstate r []).1 (dstate r []).2 := by
  refine ⟨⟨[], rfl⟩, by simp [dstate], by simp [dstate], by simp [dstate], by simp [dstate],
    fun x y => by simp [S_A], fun x y => by simp [S_A, S_B, dstate]⟩

lemma S_Inv_step (E : List (Fin N × Fin N)) (r : Fin N) (l : List (Fin N)) (w : Fin N)
    (h : S_Inv r l (dstate r l).1 (dstate r l).2) (hw : w ∈ adm E r l) :
    S_Inv r (l ++ [w]) (dstate r (l ++ [w])).1 (dstate r (l ++ [w])).2 := by
  rw [S_dstate_snoc]
  unfold adm unvis at hw
  rcases hst : dstate r l with ⟨S, V⟩
  rw [hst] at h hw
  obtain ⟨⟨rest, hS⟩, hnd, hsub, hvis, hlen, hle1, hbal⟩ := h
  simp only at hS hnd hsub hvis hlen hle1 hbal hw
  set c := S_cur r l with hc
  by_cases hwV : w ∈ V
  · -- backtrack
    have hun : ¬ (children E (S.headD r) \ V).Nonempty := by
      intro hne
      simp only [hne, ↓reduceIte] at hw
      exact (Finset.mem_sdiff.1 hw).2 hwV
    simp only [hun, ↓reduceIte] at hw
    subst hS
    rcases rest with _ | ⟨p, rest'⟩
    · simp at hw
    simp only [Finset.mem_singleton] at hw
    subst hw
    have hst' : dstep (c :: w :: rest', V) w = (w :: rest', V) := by simp [dstep, hwV]
    rw [hst']
    dsimp only
    have hcw : S_A r l c w = 0 := by
      have h1 := hbal c w
      have h2 : S_B (c :: w :: rest') c w = 1 := by rw [S_B_cur _ _ _ hnd]; simp
      have h3 : S_B (c :: w :: rest') w c = 0 := S_B_top _ _ _ hnd
      have h4 := hle1 w c
      omega
    refine ⟨⟨rest', by rw [S_cur_snoc]⟩, hnd.of_cons, fun x hx => hsub x (List.mem_cons_of_mem _ hx),
      fun x => ?_, ?_, fun x y => ?_, fun x y => ?_⟩
    · rw [hvis x]
      have hw' := (hvis w).1 hwV
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hw' ⊢
      constructor
      · tauto
      · rintro (h | h | rfl)
        exacts [Or.inl h, Or.inr h, hw']
    · simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢
      omega
    · rw [S_A_snoc]
      have := hle1 x y
      split_ifs with hxy
      · have h0 : S_A r l x y = 0 := by rw [← hxy.1, ← hxy.2]; exact hcw
        omega
      · omega
    · have hb : ∀ a b, S_B (c :: w :: rest') a b =
          S_B (w :: rest') a b + if (c, w) = (a, b) then 1 else 0 := fun a b =>
        S_B_cons _ _ _ _ (List.cons_ne_nil _ _)
      have := hbal x y
      rw [hb, hb] at this
      rw [S_A_snoc, S_A_snoc]
      simp only [Prod.mk.injEq] at this
      split_ifs at this ⊢ <;> omega
  · -- push
    have hst' : dstep (S, V) w = (w :: S, insert w V) := by simp [dstep, hwV]
    rw [hst']
    dsimp only
    have hwS : w ∉ S := fun h => hwV (hsub w h)
    have hwl : w ∉ l := fun h => hwV ((hvis w).2 (List.mem_cons_of_mem _ h))
    refine ⟨⟨S, by rw [S_cur_snoc]⟩, List.nodup_cons.2 ⟨hwS, hnd⟩, fun x hx => ?_,
      fun x => ?_, ?_, fun x y => ?_, fun x y => ?_⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hsub x hx)
    · rw [Finset.mem_insert, hvis x]
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
      tauto
    · rw [Finset.card_insert_of_notMem hwV]
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢
      omega
    · rw [S_A_snoc]
      have := hle1 x y
      split_ifs with hxy
      · obtain ⟨rfl, rfl⟩ := hxy; rw [S_A_not_mem _ _ _ _ hwl]
      · omega
    · have hne : S ≠ [] := by rw [hS]; exact List.cons_ne_nil _ _
      have hhd : S.head hne = c := by subst hS; rfl
      rw [S_B_cons _ _ _ _ hne, S_B_cons _ _ _ _ hne, hhd, S_A_snoc, S_A_snoc]
      have := hbal x y
      simp only [Prod.mk.injEq]
      split_ifs <;> omega

/-- The invariant holds along every prefix of a valid trace. -/
lemma S_Inv_take (E : List (Fin N × Fin N)) (tgt root : Fin N) (τ : List (Fin N))
    (hτ : ValidTrace E tgt root τ) :
    ∀ k ≤ τ.length, S_Inv root (τ.take k) (dstate root (τ.take k)).1 (dstate root (τ.take k)).2 := by
  intro k
  induction k with
  | zero => intro _; simpa using S_Inv_nil root
  | succ k ih =>
    intro hk
    have hk' : k < τ.length := hk
    have htake : τ.take (k + 1) = τ.take k ++ [τ[k]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk']; rfl
    rw [htake]
    exact S_Inv_step E root _ _ (ih hk'.le) (hτ k hk').2

/-! Sanity checks of the DFS definitions on a 3-vertex star `0 → 1, 0 → 2`. -/

example : (dstate (0 : Fin 3) [1, 0, 2]).1 = [2, 0] := by decide
example : adm ([(0, 1), (0, 2)] : List (Fin 3 × Fin 3)) 0 [1] = {0} := by decide
example : adm ([(0, 1), (0, 2)] : List (Fin 3 × Fin 3)) 0 [1, 0] = {2} := by decide
example : ValidTrace ([(0, 1), (0, 2)] : List (Fin 3 × Fin 3)) 2 0 [1, 0] := by
  unfold ValidTrace NonTerm; decide
example : S_A (0 : Fin 3) [1, 0] 0 1 = 1 ∧ S_A (0 : Fin 3) [1, 0] 1 0 = 1 ∧
    S_A (0 : Fin 3) [1, 0, 2] 0 2 = 1 ∧ S_A (0 : Fin 3) [1, 0, 2] 2 0 = 0 := by decide

/-- Stack parent: `A_{p → n_t} = 1`, `A_{n_t → p} = 0`. -/
lemma S_par {r : Fin N} {l S : List (Fin N)} {V : Finset (Fin N)} (h : S_Inv r l S V) {p : Fin N}
    {rest : List (Fin N)} (hS : S = S_cur r l :: p :: rest) :
    S_A r l p (S_cur r l) = 1 ∧ S_A r l (S_cur r l) p = 0 := by
  have hnd := h.nodup
  rw [hS] at hnd
  have h1 := h.bal (S_cur r l) p
  rw [hS, S_B_cur _ _ _ hnd, S_B_top _ _ _ hnd] at h1
  have h2 := h.le1 p (S_cur r l)
  simp at h1
  omega

/-- Any other vertex: `A_{w → n_t} = A_{n_t → w}`. -/
lemma S_nonpar {r : Fin N} {l S : List (Fin N)} {V : Finset (Fin N)} (h : S_Inv r l S V) {w : Fin N}
    (hw : ∀ p rest, S = S_cur r l :: p :: rest → w ≠ p) :
    S_A r l w (S_cur r l) = S_A r l (S_cur r l) w := by
  obtain ⟨rest, hS⟩ := h.stk
  have hnd := h.nodup
  rw [hS] at hnd
  have h1 := h.bal w (S_cur r l)
  rw [hS, S_B_cur _ _ _ hnd, S_B_top _ _ _ hnd] at h1
  have : ¬ rest.head? = some w := by
    intro hh
    rcases rest with _ | ⟨p, rest'⟩
    · simp at hh
    · simp at hh; exact hw p rest' hS hh.symm
  simp only [this, ↓reduceIte] at h1
  omega

/-- A valid DFS trace on `N` vertices has at most `2(N-1)` steps. -/
theorem trace_length_le (E : List (Fin N × Fin N)) (tgt root : Fin N) (τ : List (Fin N))
    (hτ : ValidTrace E tgt root τ) : τ.length ≤ 2 * (N - 1) := by
  have h := S_Inv_take E tgt root τ hτ τ.length le_rfl
  rw [List.take_length] at h
  obtain ⟨⟨rest, hS⟩, -, -, -, hlen, -, -⟩ := h
  have hcard : (dstate root τ).2.card ≤ N := by
    simpa using Finset.card_le_univ (dstate root τ).2
  rw [hS] at hlen
  simp only [List.length_cons] at hlen
  omega



/-! ### Logits at `θ = iota s` -/

lemma S_mem_children (E : List (Fin N × Fin N)) (n v : Fin N) :
    v ∈ children E n ↔ (n, v) ∈ E := by
  simp [children]

lemma S_ecnt (E : List (Fin N × Fin N)) (hE : E.Nodup) (tgt r : Fin N) (l : List (Fin N))
    (x v : Fin N) : (⟨E, tgt, r, l⟩ : Ctx N).ecnt x v = if (x, v) ∈ E then 1 else 0 := by
  unfold Ctx.ecnt
  have h : (E.filter fun e => decide (e = (x, v))) = E.filter (fun e => e == (x, v)) :=
    List.filter_congr (fun e _ => rfl)
  rw [h, ← List.count_eq_length_filter, hE.count]
  split_ifs <;> simp

lemma S_mcnt (E : List (Fin N × Fin N)) (tgt r : Fin N) (l : List (Fin N)) (v : Fin N) :
    (⟨E, tgt, r, l⟩ : Ctx N).mcnt v = ((r :: l).count v : ℝ) := rfl

lemma S_logit (s : Fin 8 → ℝ) (hs3 : s 3 = 0) (c : Ctx N) (v : Fin N) (hv : v ≠ c.cur) :
    logit (iota s) c v = max (s 2 * c.ecnt c.cur v - c.mcnt v * s 1) 0 +
      max ((s 4 - s 5) * c.trans v c.cur - (s 6 - s 7) * c.trans c.cur v +
        (if v = c.root then s 7 else 0)) 0 := by
  rw [DFS.logit_of_ne _ _ _ hv, DFS.head1_iota, DFS.head2_iota _ _ _ hv, ite_eq_right_of_eq_false _ _ (eq_false hv), hs3]
  simp

lemma S_h2_le (y1 y2 t Cv : ℝ) (a b : ℕ) (ha : a ≤ 1) (hb : b ≤ 1) (hy1 : 0 ≤ y1)
    (hv : y1 - y2 ≤ Cv) (ht : t ≤ 0) : max (y1 * a - y2 * b + t) 0 ≤ y1 + max Cv 0 := by
  have hM := le_max_left Cv 0
  have hM0 := le_max_right Cv 0
  apply max_le _ (by linarith)
  interval_cases a <;> interval_cases b <;>
    simp only [Nat.cast_zero, Nat.cast_one, mul_zero, mul_one] <;> linarith

lemma S_h2_le' (y1 y2 t Cv : ℝ) (a : ℕ) (ha : a ≤ 1)
    (hv : y1 - y2 ≤ Cv) (ht : t ≤ 0) : max (y1 * a - y2 * a + t) 0 ≤ max Cv 0 := by
  have hM := le_max_left Cv 0
  have hM0 := le_max_right Cv 0
  apply max_le _ hM0
  interval_cases a <;>
    simp only [Nat.cast_zero, Nat.cast_one, mul_zero, mul_one] <;> linarith

lemma S_h1_le (s1 s2 e m : ℝ) (he : e = 0 ∨ e = 1) (hm : m = 0 ∧ e = 0 ∨ 1 ≤ m) (hs1 : 0 < s1)
    (hu : 0 ≤ s2 - s1) : max (s2 * e - m * s1) 0 ≤ s2 - s1 := by
  apply max_le _ hu
  rcases hm with ⟨rfl, rfl⟩ | hm
  · simp; linarith
  · rcases he with rfl | rfl <;> nlinarith

/-- Generic softmax bound: `-log ∑_{C} p ≤ N e^{B - L}`. -/
lemma S_adm_le (θ : Params N) (c : Ctx N) (C : Finset (Fin N)) (v₀ : Fin N) (hv₀ : v₀ ∈ C)
    (B L : ℝ) (hB : ∀ w ∉ C, logit θ c w ≤ B) (hL : L ≤ logit θ c v₀) :
    admLoss θ c C ≤ N * exp (B - L) := by
  unfold admLoss prob
  rw [← Finset.sum_div]
  set X := ∑ v ∈ C, exp (logit θ c v) with hXdef
  set Z := ∑ w, exp (logit θ c w) with hZdef
  have hX : exp L ≤ X :=
    (exp_le_exp.2 hL).trans (Finset.single_le_sum (fun _ _ => (exp_pos _).le) hv₀)
  have hXpos : 0 < X := (exp_pos L).trans_le hX
  have hsplit : Z = (∑ w ∈ univ \ C, exp (logit θ c w)) + X :=
    (Finset.sum_sdiff (Finset.subset_univ C)).symm
  have hY : ∑ w ∈ univ \ C, exp (logit θ c w) ≤ N * exp B := by
    calc ∑ w ∈ univ \ C, exp (logit θ c w) ≤ ∑ w ∈ univ \ C, exp B :=
          Finset.sum_le_sum (fun w hw => exp_le_exp.2 (hB w (Finset.mem_sdiff.1 hw).2))
      _ = ((Finset.univ \ C).card : ℝ) * exp B := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ N * exp B := by
          gcongr
          have := Finset.card_le_univ (Finset.univ \ C)
          simp only [Fintype.card_fin] at this
          exact_mod_cast this
  have hY0 : 0 ≤ ∑ w ∈ univ \ C, exp (logit θ c w) :=
    Finset.sum_nonneg (fun _ _ => (exp_pos _).le)
  have hZpos : 0 < Z := by rw [hsplit]; linarith
  rw [← Real.log_inv, inv_div]
  calc log (Z / X) ≤ Z / X - 1 := Real.log_le_sub_one_of_pos (div_pos hZpos hXpos)
    _ = (∑ w ∈ univ \ C, exp (logit θ c w)) / X := by
        rw [hsplit]; field_simp; ring
    _ ≤ (N * exp B) / exp L := div_le_div₀ (by positivity) hY (exp_pos _) hX
    _ = N * exp (B - L) := by rw [exp_sub]; ring

/-- Explicit logits at `iota s` for a context with prefix `l`, `v ≠ n_t`. -/
lemma S_logit' (s : Fin 8 → ℝ) (hs3 : s 3 = 0) (E : List (Fin N × Fin N)) (hE : E.Nodup)
    (tgt root : Fin N) (l : List (Fin N)) (v : Fin N) (hv : v ≠ S_cur root l) :
    logit (iota s) ⟨E, tgt, root, l⟩ v =
      max (s 2 * (if (S_cur root l, v) ∈ E then 1 else 0) - ((root :: l).count v : ℝ) * s 1) 0 +
      max ((s 4 - s 5) * (S_A root l v (S_cur root l) : ℝ) -
        (s 6 - s 7) * (S_A root l (S_cur root l) v : ℝ) + (if v = root then s 7 else 0)) 0 := by
  rw [S_logit s hs3 (⟨E, tgt, root, l⟩ : Ctx N) v hv, S_ctx_cur, S_ecnt E hE, S_mcnt]
  rfl

/-- Per-step bound. -/
lemma S_step (Cu Cv : ℝ) (s : Fin 8 → ℝ) (hs3 : s 3 = 0) (hs7 : s 7 ≤ 0) (hs1 : 0 < s 1)
    (hu : 0 ≤ s 2 - s 1) (hCu : s 2 - s 1 ≤ Cu) (hCv : s 4 - s 5 - (s 6 - s 7) ≤ Cv)
    (hy1 : 0 ≤ s 4 - s 5) (E : List (Fin N × Fin N)) (tgt root : Fin N) (l : List (Fin N))
    (hE : E.Nodup) (h : S_Inv root l (dstate root l).1 (dstate root l).2) (w : Fin N)
    (hw : w ∈ adm E root l) :
    admLoss (iota s) ⟨E, tgt, root, l⟩ (adm E root l) ≤
      N * exp (Cu + max Cv 0) * (exp (s 4 - s 5 - s 2) + exp (-s 2) + exp (-(s 4 - s 5)) +
        exp (-(s 4 - s 5 + s 7))) := by
  set cu := S_cur root l with hcu
  set M := max Cv 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hCu0 : 0 ≤ Cu := hu.trans hCu
  obtain ⟨rest, hS⟩ := h.stk
  have hcuV : cu ∈ (dstate root l).2 := h.sub cu (by rw [hS]; exact List.mem_cons_self)
  have hunv : unvis E root l = children E cu \ (dstate root l).2 := by
    unfold unvis; rw [hS]; rfl
  have hcur0 : logit (iota s) ⟨E, tgt, root, l⟩ cu = 0 := by
    unfold logit; rw [ite_eq_left_of_eq_true _ _ (eq_true (S_ctx_cur E tgt root l).symm)]
  have hh1 : ∀ v, v ∉ unvis E root l →
      max (s 2 * (if (cu, v) ∈ E then 1 else 0) - ((root :: l).count v : ℝ) * s 1) 0 ≤
        s 2 - s 1 := by
    intro v hv
    apply S_h1_le _ _ _ _ (by split_ifs <;> simp) _ hs1 hu
    by_cases hvV : v ∈ (dstate root l).2
    · right
      have : 0 < (root :: l).count v := List.count_pos_iff.2 ((h.vis v).1 hvV)
      exact_mod_cast this
    · left
      have hc0 : (root :: l).count v = 0 := List.count_eq_zero.2 (fun hm => hvV ((h.vis v).2 hm))
      have hE0 : (cu, v) ∉ E := by
        intro hm
        apply hv
        rw [hunv, Finset.mem_sdiff, S_mem_children]
        exact ⟨hm, hvV⟩
      simp [hc0, hE0]
  have ht : ∀ v : Fin N, (if v = root then s 7 else 0) ≤ 0 := fun v => by
    split_ifs <;> linarith
  have hh2 : ∀ v, max ((s 4 - s 5) * (S_A root l v cu : ℝ) - (s 6 - s 7) * (S_A root l cu v : ℝ) +
      (if v = root then s 7 else 0)) 0 ≤ (s 4 - s 5) + M := fun v =>
    S_h2_le _ _ _ _ _ _ (h.le1 _ _) (h.le1 _ _) hy1 hCv (ht v)
  have hh2' : ∀ v, (∀ p rest', (dstate root l).1 = cu :: p :: rest' → v ≠ p) →
      max ((s 4 - s 5) * (S_A root l v cu : ℝ) - (s 6 - s 7) * (S_A root l cu v : ℝ) +
        (if v = root then s 7 else 0)) 0 ≤ M := by
    intro v hv
    rw [S_nonpar h hv]
    exact S_h2_le' _ _ _ _ _ (h.le1 _ _) hCv (ht v)
  have hQ1 : 0 < exp (s 4 - s 5 - s 2) := exp_pos _
  have hQ2 : 0 < exp (-s 2) := exp_pos _
  have hQ3 : 0 < exp (-(s 4 - s 5)) := exp_pos _
  have hQ4 : 0 < exp (-(s 4 - s 5 + s 7)) := exp_pos _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  by_cases hne : (unvis E root l).Nonempty
  · have hadm : adm E root l = unvis E root l := by simp [adm, hne]
    rw [hadm]
    obtain ⟨v₀, hv₀⟩ := hne
    have hv₀' := hv₀
    rw [hunv, Finset.mem_sdiff, S_mem_children] at hv₀'
    have hv₀c : v₀ ≠ cu := fun he => hv₀'.2 (he ▸ hcuV)
    have hc0 : (root :: l).count v₀ = 0 :=
      List.count_eq_zero.2 (fun hm => hv₀'.2 ((h.vis v₀).2 hm))
    refine (S_adm_le _ _ _ v₀ hv₀ (Cu + (s 4 - s 5 + M)) (s 2) ?_ ?_).trans ?_
    · intro v hv
      by_cases hvc : v = cu
      · rw [hvc, hcur0]; linarith
      · rw [S_logit' s hs3 E hE tgt root l v hvc]
        have := hh1 v hv
        have := hh2 v
        linarith
    · rw [S_logit' s hs3 E hE tgt root l v₀ hv₀c, ite_eq_left_of_eq_true _ _ (eq_true hv₀'.1), hc0]
      simp only [mul_one, Nat.cast_zero, zero_mul, sub_zero]
      have := le_max_left (s 2) 0
      have := le_max_right ((s 4 - s 5) * (S_A root l v₀ cu : ℝ) - (s 6 - s 7) * (S_A root l cu v₀ : ℝ) +
        (if v₀ = root then s 7 else 0)) 0
      linarith
    · have : exp (Cu + (s 4 - s 5 + M) - s 2) = exp (Cu + M) * exp (s 4 - s 5 - s 2) := by
        rw [← exp_add]; ring_nf
      rw [this]
      have h0 : 0 ≤ (N : ℝ) * exp (Cu + M) := by positivity
      nlinarith
  · rcases rest with _ | ⟨p, rest'⟩
    · unfold adm at hw
      simp only [hne, ↓reduceIte, hS] at hw
      simp at hw
    have hadm : adm E root l = {p} := by
      unfold adm
      simp only [hne, ↓reduceIte, hS]
    rw [hadm]
    have hnd := h.nodup
    rw [hS] at hnd
    have hpc : p ≠ cu := fun he => (List.nodup_cons.1 hnd).1 (he ▸ List.mem_cons_self)
    obtain ⟨hp1, hp0⟩ := S_par h hS
    refine (S_adm_le _ _ _ p (Finset.mem_singleton_self p) (Cu + M)
      (s 4 - s 5 + if p = root then s 7 else 0) ?_ ?_).trans ?_
    · intro v hv
      rw [Finset.mem_singleton] at hv
      by_cases hvc : v = cu
      · rw [hvc, hcur0]; linarith
      · rw [S_logit' s hs3 E hE tgt root l v hvc]
        have := hh1 v (fun hm => hne ⟨v, hm⟩)
        have := hh2' v (fun p' rest'' h' => by
          rw [hS] at h'
          simp only [List.cons.injEq] at h'
          rw [← h'.2.1]; exact hv)
        linarith
    · rw [S_logit' s hs3 E hE tgt root l p hpc, hp1, hp0]
      simp only [Nat.cast_one, Nat.cast_zero, mul_one, mul_zero, sub_zero]
      have := le_max_left (s 4 - s 5 + if p = root then s 7 else 0) 0
      have := le_max_right (s 2 * (if (cu, p) ∈ E then 1 else 0) - ((root :: l).count p : ℝ) * s 1) 0
      linarith
    · have h0 : 0 ≤ (N : ℝ) * exp (Cu + M) := by positivity
      have : exp (Cu + M - (s 4 - s 5 + if p = root then s 7 else 0)) =
          exp (Cu + M) * exp (-(s 4 - s 5 + if p = root then s 7 else 0)) := by
        rw [← exp_add]; ring_nf
      rw [this]
      split_ifs
      · nlinarith
      · have : exp (-(s 4 - s 5 + 0)) = exp (-(s 4 - s 5)) := by ring_nf
        rw [this]
        nlinarith

/-- Generalization loss bound in terms of the scalars (eq. `gen_normalizer` and Cases 1–3). -/
theorem genLoss_bound (hN : 2 ≤ N) (Cu Cv : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : Fin 8 → ℝ, s 3 = 0 → s 7 ≤ 0 → 0 < s 1 → 0 ≤ s 2 - s 1 →
      s 2 - s 1 ≤ Cu → s 4 - s 5 - (s 6 - s 7) ≤ Cv → 0 ≤ s 4 - s 5 →
      ∀ (E : List (Fin N × Fin N)) (tgt root : Fin N) (τ : List (Fin N)), E.Nodup →
        ValidTrace E tgt root τ →
        genLoss (iota s) E tgt root τ ≤
          C * (exp (s 4 - s 5 - s 2) + exp (-s 2) + exp (-(s 4 - s 5)) +
            exp (-(s 4 - s 5 + s 7))) := by
  refine ⟨2 * N * (N * exp (Cu + max Cv 0)), by positivity, ?_⟩
  intro s hs3 hs7 hs1 hu hCu hCv hy1 E tgt root τ hE hτ
  set Q := exp (s 4 - s 5 - s 2) + exp (-s 2) + exp (-(s 4 - s 5)) + exp (-(s 4 - s 5 + s 7))
    with hQ
  have hQ0 : 0 ≤ Q := by positivity
  unfold genLoss
  have hstep : ∀ k ∈ range τ.length,
      admLoss (iota s) ⟨E, tgt, root, τ.take k⟩ (adm E root (τ.take k)) ≤
        N * exp (Cu + max Cv 0) * Q := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    exact S_step Cu Cv s hs3 hs7 hs1 hu hCu hCv hy1 E tgt root _ hE
      (S_Inv_take E tgt root τ hτ k hk'.le) _ (hτ k hk').2
  have hlen : (τ.length : ℝ) ≤ 2 * N := by
    have := DFS.trace_length_le E tgt root τ hτ
    have : τ.length ≤ 2 * N := by omega
    exact_mod_cast this
  calc ∑ k ∈ range τ.length, admLoss (iota s) ⟨E, tgt, root, τ.take k⟩ (adm E root (τ.take k))
      ≤ ∑ k ∈ range τ.length, N * exp (Cu + max Cv 0) * Q := Finset.sum_le_sum hstep
    _ = τ.length * (N * exp (Cu + max Cv 0) * Q) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ 2 * N * (N * exp (Cu + max Cv 0) * Q) := by
        gcongr
    _ = 2 * N * (N * exp (Cu + max Cv 0)) * Q := by ring



end DFS
