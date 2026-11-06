import DFSLean.Tables
import DFSLean.Equivariance

/-!
# Package C: gradient of the canonical loss on the region `R'` (Lemma C.2, Step 2)
-/

noncomputable section

namespace DFS
open Real Finset Filter Topology Set
open DFS

variable {N K : ℕ}

/-! ### Linearity of the pull-back `iotaT` -/

lemma C_pair_add (f g θ : Params N) : pair (f + g) θ = pair f θ + pair g θ := by
  simp only [pair, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma C_pair_smul (a : ℝ) (f θ : Params N) : pair (a • f) θ = a * pair f θ := by
  simp only [pair, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

lemma C_pair_zero (θ : Params N) : pair 0 θ = 0 := by
  simp [pair]

lemma C_iotaT_add (f g : Params N) : iotaT (f + g) = iotaT f + iotaT g := by
  funext m; simp only [iotaT, Pi.add_apply, C_pair_add]

lemma C_iotaT_smul (a : ℝ) (f : Params N) : iotaT (a • f) = a • iotaT f := by
  funext m; simp only [iotaT, Pi.smul_apply, smul_eq_mul, C_pair_smul]

lemma C_iotaT_zero : iotaT (0 : Params N) = 0 := by
  funext m; simp only [iotaT, C_pair_zero, Pi.zero_apply]

lemma C_iotaT_sum {ι : Type*} (s : Finset ι) (f : ι → Params N) :
    iotaT (∑ i ∈ s, f i) = ∑ i ∈ s, iotaT (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [C_iotaT_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, C_iotaT_add, ih]

/-! ### Coefficient vectors of the two heads -/

lemma C_iotaT_coef1 (c : Ctx N) (v : Fin N) (hv : v ≠ c.cur) :
    iotaT (coef1 c v) = ![0, -c.mcnt v, c.ecnt c.cur v, c.din v - c.ecnt c.cur v, 0, 0, 0, 0] := by
  funext m
  simp only [iotaT]
  rw [← DFS.head1_eq_pair, DFS.head1_iota]
  fin_cases m <;> simp [hv, sub_eq_add_neg]

lemma C_iotaT_coef2 (c : Ctx N) (v : Fin N) (hv : v ≠ c.cur) :
    iotaT (coef2 c v) = ![0, 0, 0, 0, c.trans v c.cur, -c.trans v c.cur, -c.trans c.cur v,
      c.trans c.cur v + if v = c.root then 1 else 0] := by
  funext m
  simp only [iotaT]
  rw [← DFS.head2_eq_pair, DFS.head2_iota _ _ _ hv]
  fin_cases m <;> simp


/-! ### Pull-back of the step gradient -/

lemma C_iotaT_dlogit (c : Ctx N) (v : Fin N) (σ : (Fin 8 → ℝ) → ℝ) :
    iotaT (dlogit c v (σ ∘ iotaT)) = if v = c.cur then 0 else
      σ (iotaT (coef1 c v)) • iotaT (coef1 c v) + σ (iotaT (coef2 c v)) • iotaT (coef2 c v) := by
  unfold dlogit
  split_ifs
  · exact C_iotaT_zero
  · rw [C_iotaT_add, C_iotaT_smul, C_iotaT_smul]; rfl

lemma C_iotaT_gstep (θ : Params N) (σ : (Fin 8 → ℝ) → ℝ) (c : Ctx N) (y : Fin N) :
    iotaT (gstep θ (σ ∘ iotaT) c y) =
      ∑ v, prob θ c v • iotaT (dlogit c v (σ ∘ iotaT)) - iotaT (dlogit c y (σ ∘ iotaT)) := by
  unfold gstep
  rw [C_iotaT_sum]
  simp only [C_iotaT_smul]
  simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-! ### Graph statistics as list counts -/

lemma C_mcnt (c : Ctx N) (v : Fin N) : c.mcnt v = ((c.root :: c.cot).count v : ℝ) := rfl

lemma C_ecnt (c : Ctx N) (x v : Fin N) : c.ecnt x v = (c.edges.count (x, v) : ℝ) := by
  simp only [Ctx.ecnt, List.count_eq_countP, List.countP_eq_length_filter]
  congr 2

lemma C_din (c : Ctx N) (v : Fin N) :
    c.din v = (c.edges.countP (fun e => decide (e.2 = v)) : ℝ) := by
  simp only [Ctx.din, List.countP_eq_length_filter]

lemma C_trans (c : Ctx N) (x y : Fin N) :
    c.trans x y = ((c.cot.zip (c.root :: c.cot)).count (y, x) : ℝ) := by
  simp only [Ctx.trans, Ctx.nodes, List.count_eq_countP, List.countP_eq_length_filter]
  congr 2
  apply List.filter_congr
  intro p _
  rcases p with ⟨a, b⟩
  by_cases h1 : b = x <;> by_cases h2 : a = y <;> simp [h1, h2]

lemma C_cur (c : Ctx N) : c.cur = c.cot.getLastD c.root := by
  unfold Ctx.cur Ctx.nodes; exact List.getLast_eq_getLastD _

lemma C_perm_one (c : Ctx N) : c.perm 1 = c := by
  cases c; simp [Ctx.perm]

/-! ### Vertices `nd N a` -/

section canon
variable [NeZero N]

lemma C_nd_val {a : ℕ} (ha : a < N) : (nd N a).val = a := by
  simp [nd, Nat.mod_eq_of_lt ha]

lemma C_nd_eq_iff {a b : ℕ} (ha : a < N) (hb : b < N) : nd N a = nd N b ↔ a = b := by
  rw [Fin.ext_iff, C_nd_val ha, C_nd_val hb]

lemma C_nd_self (v : Fin N) : nd N v.val = v := by
  ext; simp [nd]

lemma C_count_cons {a b : ℕ} (ha : a < N) (hb : b < N) (l : List (Fin N)) :
    (nd N a :: l).count (nd N b) = l.count (nd N b) + if a = b then 1 else 0 := by
  rw [List.count_cons]; simp [C_nd_eq_iff ha hb]

lemma C_count_cons2 {a a' b b' : ℕ} (ha : a < N) (ha' : a' < N) (hb : b < N) (hb' : b' < N)
    (l : List (Fin N × Fin N)) :
    ((nd N a, nd N a') :: l).count (nd N b, nd N b') =
      l.count (nd N b, nd N b') + if a = b ∧ a' = b' then 1 else 0 := by
  rw [List.count_cons]; simp [C_nd_eq_iff ha hb, C_nd_eq_iff ha' hb']

/-! ### The canonical lists -/

/-- `[2, 1, 3, 1, …, j+1, 1]` (paper labels), i.e. `[1, 0, 2, 0, …, j, 0]` as `Fin` indices. -/
def C_L (N : ℕ) [NeZero N] (j : ℕ) : List (Fin N) :=
  (List.range j).flatMap (fun i => [nd N (i + 1), nd N 0])

/-- The CoT steps inside `C_L`. -/
def C_S (N : ℕ) [NeZero N] (j : ℕ) : List (Fin N × Fin N) :=
  (List.range j).flatMap (fun i => [(nd N (i + 1), nd N 0), (nd N 0, nd N (i + 1))])

lemma C_L_zero : C_L N 0 = [] := by simp [C_L]

lemma C_L_succ (j : ℕ) : C_L N (j + 1) = C_L N j ++ [nd N (j + 1), nd N 0] := by
  simp [C_L, List.range_succ, List.flatMap_append]

lemma C_S_zero : C_S N 0 = [] := by simp [C_S]

lemma C_S_succ (j : ℕ) :
    C_S N (j + 1) = C_S N j ++ [(nd N (j + 1), nd N 0), (nd N 0, nd N (j + 1))] := by
  simp [C_S, List.range_succ, List.flatMap_append]

lemma C_L_length (j : ℕ) : (C_L N j).length = 2 * j := by
  induction j with
  | zero => simp [C_L_zero]
  | succ j ih => rw [C_L_succ, List.length_append, ih]; simp; ring

lemma C_L_getLastD (j : ℕ) : (C_L N j).getLastD (nd N 0) = nd N 0 := by
  cases j with
  | zero => simp [C_L_zero]
  | succ j =>
    rw [C_L_succ, show C_L N j ++ [nd N (j + 1), nd N 0] = (C_L N j ++ [nd N (j + 1)]) ++ [nd N 0]
      by simp, List.getLastD_concat]

lemma C_L_prefix {j K : ℕ} (h : j ≤ K) : ∃ R, C_L N K = C_L N j ++ R := by
  induction K, h using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ K hK ih =>
    obtain ⟨R, hR⟩ := ih
    exact ⟨R ++ [nd N (K + 1), nd N 0], by rw [C_L_succ, hR]; simp⟩

lemma C_count_L {j b : ℕ} (hj : j < N) (hb : b < N) :
    (C_L N j).count (nd N b) = (if b = 0 then j else 0) + (if 1 ≤ b ∧ b ≤ j then 1 else 0) := by
  induction j with
  | zero => simp only [C_L_zero, List.count_nil]; split_ifs <;> omega
  | succ j ih =>
    rw [C_L_succ, List.count_append, ih (by omega), C_count_cons (by omega) hb,
      C_count_cons (by omega) hb, List.count_nil]
    split_ifs <;> omega

lemma C_count_S {j a b : ℕ} (hj : j < N) (ha : a < N) (hb : b < N) :
    (C_S N j).count (nd N a, nd N b) =
      (if b = 0 ∧ 1 ≤ a ∧ a ≤ j then 1 else 0) + (if a = 0 ∧ 1 ≤ b ∧ b ≤ j then 1 else 0) := by
  induction j with
  | zero => simp only [C_S_zero, List.count_nil]; split_ifs <;> omega
  | succ j ih =>
    rw [C_S_succ, List.count_append, ih (by omega), C_count_cons2 (by omega) (by omega) ha hb,
      C_count_cons2 (by omega) (by omega) ha hb, List.count_nil]
    split_ifs <;> omega

lemma C_zip_append {α : Type*} (r : α) (l m : List α) :
    (l ++ m).zip (r :: (l ++ m)) = l.zip (r :: l) ++ m.zip (l.getLastD r :: m) := by
  induction l generalizing r with
  | nil => simp
  | cons x l ih => simp only [List.cons_append, List.zip_cons_cons, ih, List.getLastD_cons]

lemma C_zip_L (j : ℕ) : (C_L N j).zip (nd N 0 :: C_L N j) = C_S N j := by
  induction j with
  | zero => simp [C_L_zero, C_S_zero]
  | succ j ih => rw [C_L_succ, C_zip_append, ih, C_L_getLastD, C_S_succ]; simp


/-! ### The canonical edge list -/

lemma C_count_M {n a b : ℕ} (hn : n < N) (ha : a < N) (hb : b < N) :
    ((List.range n).map (fun j => (nd N 0, nd N (j + 1)))).count (nd N a, nd N b) =
      if a = 0 ∧ 1 ≤ b ∧ b ≤ n then 1 else 0 := by
  induction n with
  | zero => simp only [List.range_zero, List.map_nil, List.count_nil]; split_ifs <;> omega
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.count_append, ih (by omega), List.map_singleton,
      C_count_cons2 (by omega) (by omega) ha hb, List.count_nil]
    split_ifs <;> omega

lemma C_countP_M {n b : ℕ} (hn : n < N) (hb : b < N) :
    ((List.range n).map (fun j => (nd N 0, nd N (j + 1)))).countP (fun e => decide (e.2 = nd N b)) =
      if 1 ≤ b ∧ b ≤ n then 1 else 0 := by
  induction n with
  | zero => simp only [List.range_zero, List.map_nil, List.countP_nil]; split_ifs <;> omega
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.countP_append, ih (by omega), List.map_singleton,
      List.countP_cons, List.countP_nil]
    simp only [decide_eq_true_eq, C_nd_eq_iff (show n + 1 < N by omega) hb]
    split_ifs <;> omega

lemma C_count_E0 (hN : K + 5 ≤ N) {a b : ℕ} (ha : a < N) (hb : b < N) :
    (E0 N K).count (nd N a, nd N b) =
      (if a = 0 ∧ 1 ≤ b ∧ b ≤ K then 1 else 0) + (if a = N - 2 ∧ b = N - 3 then 1 else 0) +
        (if a = N - 3 ∧ b = N - 4 then 1 else 0) + (if a = N - 4 ∧ b = 0 then 1 else 0) := by
  rw [E0, List.count_append, C_count_M (by omega) ha hb, C_count_cons2 (by omega) (by omega) ha hb,
    C_count_cons2 (by omega) (by omega) ha hb, C_count_cons2 (by omega) (by omega) ha hb,
    List.count_nil]
  split_ifs <;> omega

lemma C_countP_E0 (hN : K + 5 ≤ N) {b : ℕ} (hb : b < N) :
    (E0 N K).countP (fun e => decide (e.2 = nd N b)) =
      (if 1 ≤ b ∧ b ≤ K then 1 else 0) + (if b = N - 3 then 1 else 0) +
        (if b = N - 4 then 1 else 0) + (if b = 0 then 1 else 0) := by
  rw [E0, List.countP_append, C_countP_M (by omega) hb]
  simp only [List.countP_cons, List.countP_nil, decide_eq_true_eq,
    C_nd_eq_iff (show N - 3 < N by omega) hb, C_nd_eq_iff (show N - 4 < N by omega) hb,
    C_nd_eq_iff (show 0 < N by omega) hb]
  split_ifs <;> omega

/-! ### The canonical contexts -/

lemma C_tau0 : tau0 N K = nd N 0 :: (C_L N K ++ [nd N (N - 4)]) := by
  simp [tau0, C_L]

lemma C_take_odd {j : ℕ} (hj : j ≤ K) : (tau0 N K).take (2 * j + 1) = nd N 0 :: C_L N j := by
  obtain ⟨R, hR⟩ := C_L_prefix (N := N) hj
  rw [C_tau0, hR, List.take_succ_cons, List.append_assoc, List.take_left' (C_L_length j)]

lemma C_take_even {j : ℕ} (hj : j < K) :
    (tau0 N K).take (2 * j + 2) = nd N 0 :: (C_L N j ++ [nd N (j + 1)]) := by
  obtain ⟨R, hR⟩ := C_L_prefix (N := N) (show j + 1 ≤ K by omega)
  rw [C_tau0, hR, C_L_succ, List.take_succ_cons]
  simp [List.take_append, C_L_length]

lemma C_ylab_zero : ylab N K 0 = nd N 0 := by
  simp [ylab, tau0]

lemma C_ylab_odd {j : ℕ} (hj : j < K) : ylab N K (2 * j + 1) = nd N (j + 1) := by
  obtain ⟨R, hR⟩ := C_L_prefix (N := N) (show j + 1 ≤ K by omega)
  rw [ylab, C_tau0, hR, C_L_succ]
  simp [List.getD_eq_getElem?_getD, C_L_length]

lemma C_ylab_even {j : ℕ} (hj : j < K) : ylab N K (2 * j + 2) = nd N 0 := by
  obtain ⟨R, hR⟩ := C_L_prefix (N := N) (show j + 1 ≤ K by omega)
  rw [ylab, C_tau0, hR, C_L_succ]
  simp [List.getD_eq_getElem?_getD, C_L_length]

lemma C_ylab_last : ylab N K (2 * K + 1) = nd N (N - 4) := by
  rw [ylab, C_tau0]
  simp [List.getD_eq_getElem?_getD, C_L_length]

lemma C_cot_zero : (ctx N K 0).cot = [nd N (N - 3), nd N (N - 4)] := by
  simp [ctx]

lemma C_cot_odd {j : ℕ} (hj : j ≤ K) :
    (ctx N K (2 * j + 1)).cot = nd N (N - 3) :: nd N (N - 4) :: nd N 0 :: C_L N j := by
  simp [ctx, C_take_odd hj]

lemma C_cot_even {j : ℕ} (hj : j < K) :
    (ctx N K (2 * j + 2)).cot =
      nd N (N - 3) :: nd N (N - 4) :: nd N 0 :: (C_L N j ++ [nd N (j + 1)]) := by
  simp [ctx, C_take_even hj]

lemma C_root (k : ℕ) : (ctx N K k).root = nd N (N - 2) := rfl
lemma C_edges (k : ℕ) : (ctx N K k).edges = E0 N K := rfl

lemma C_cur_zero : (ctx N K 0).cur = nd N (N - 4) := by
  rw [C_cur, C_cot_zero]; simp

lemma C_cur_odd {j : ℕ} (hj : j ≤ K) : (ctx N K (2 * j + 1)).cur = nd N 0 := by
  rw [C_cur, C_cot_odd hj]; simp only [List.getLastD_cons]; exact C_L_getLastD j

lemma C_cur_even {j : ℕ} (hj : j < K) : (ctx N K (2 * j + 2)).cur = nd N (j + 1) := by
  rw [C_cur, C_cot_even hj]; simp only [List.getLastD_cons]; exact List.getLastD_concat

lemma C_zip_zero :
    (ctx N K 0).cot.zip ((ctx N K 0).root :: (ctx N K 0).cot) =
      [(nd N (N - 3), nd N (N - 2)), (nd N (N - 4), nd N (N - 3))] := by
  rw [C_cot_zero, C_root]; rfl

lemma C_zip_odd {j : ℕ} (hj : j ≤ K) :
    (ctx N K (2 * j + 1)).cot.zip ((ctx N K (2 * j + 1)).root :: (ctx N K (2 * j + 1)).cot) =
      (nd N (N - 3), nd N (N - 2)) :: (nd N (N - 4), nd N (N - 3)) :: (nd N 0, nd N (N - 4)) ::
        C_S N j := by
  rw [C_cot_odd hj, C_root]
  simp only [List.zip_cons_cons, C_zip_L]

lemma C_zip_even {j : ℕ} (hj : j < K) :
    (ctx N K (2 * j + 2)).cot.zip ((ctx N K (2 * j + 2)).root :: (ctx N K (2 * j + 2)).cot) =
      (nd N (N - 3), nd N (N - 2)) :: (nd N (N - 4), nd N (N - 3)) :: (nd N 0, nd N (N - 4)) ::
        (C_S N j ++ [(nd N (j + 1), nd N 0)]) := by
  rw [C_cot_even hj, C_root]
  simp only [List.zip_cons_cons]
  rw [C_zip_append, C_zip_L, C_L_getLastD]
  rfl

end canon

/-! ### Logit and selected logit gradient of one vertex, from its graph statistics -/

/-- Logit of a non-current vertex with statistics `(m_v, [n_t → v], d_v, A_{v→n_t}, A_{n_t→v})`
and root flag `r`. -/
def C_lg (s : Fin 8 → ℝ) (mc ec di tvc tcv r : ℝ) : ℝ :=
  max (s 3 * di + (s 2 - s 3) * ec - mc * s 1) 0 + max ((s 4 - s 5) * tvc - (s 6 - s 7) * tcv + r * s 7) 0

/-- Coefficient vector of head 1. -/
def C_v1 (mc ec di : ℝ) : Fin 8 → ℝ := ![0, -mc, ec, di - ec, 0, 0, 0, 0]

/-- Coefficient vector of head 2. -/
def C_v2 (tvc tcv r : ℝ) : Fin 8 → ℝ := ![0, 0, 0, 0, tvc, -tvc, -tcv, tcv + r]

/-- Selected gradient of the logit. -/
def C_dv (σ : (Fin 8 → ℝ) → ℝ) (mc ec di tvc tcv r : ℝ) : Fin 8 → ℝ :=
  σ (C_v1 mc ec di) • C_v1 mc ec di + σ (C_v2 tvc tcv r) • C_v2 tvc tcv r

lemma C_vert (s : Fin 8 → ℝ) (σ : (Fin 8 → ℝ) → ℝ) (c : Ctx N) (v : Fin N) (hv : v ≠ c.cur)
    {mc ec di tvc tcv r : ℝ} (h1 : c.mcnt v = mc) (h2 : c.ecnt c.cur v = ec) (h3 : c.din v = di)
    (h4 : c.trans v c.cur = tvc) (h5 : c.trans c.cur v = tcv)
    (h6 : (if v = c.root then (1 : ℝ) else 0) = r) :
    logit (iota s) c v = C_lg s mc ec di tvc tcv r ∧
      iotaT (dlogit c v (σ ∘ iotaT)) = C_dv σ mc ec di tvc tcv r := by
  constructor
  · rw [DFS.logit_of_ne _ _ _ hv, DFS.head1_iota, DFS.head2_iota _ _ _ hv, ite_eq_right hv, h1, h2, h3,
      h4, h5, ← h6, C_lg]
    congr 2
    split_ifs <;> ring
  · rw [C_iotaT_dlogit, ite_eq_right hv, C_iotaT_coef1 _ _ hv, C_iotaT_coef2 _ _ hv, h1, h2, h3, h4, h5, h6]
    rfl

lemma C_vert_cur (θ : Params N) (σ : (Fin 8 → ℝ) → ℝ) (c : Ctx N) :
    exp (logit θ c c.cur) = 1 ∧ iotaT (dlogit c c.cur (σ ∘ iotaT)) = 0 := by
  constructor
  · simp [logit]
  · rw [C_iotaT_dlogit, ite_eq_left rfl]

/-! ### The seven vertex types on `R'` -/

/-- Basis vector of `a₂`. -/
def C_e2 : Fin 8 → ℝ := ![0, 0, 1, 0, 0, 0, 0, 0]
/-- Coefficient vector of `g₁ - d₁`. -/
def C_ep : Fin 8 → ℝ := ![0, 0, 0, 0, 1, -1, 0, 0]

section types
variable {s : Fin 8 → ℝ} {σ : (Fin 8 → ℝ) → ℝ}

lemma C_dot8 (a : Fin 8 → ℝ) (s : Fin 8 → ℝ) :
    a ⬝ᵥ s = a 0 * s 0 + a 1 * s 1 + a 2 * s 2 + a 3 * s 3 + a 4 * s 4 + a 5 * s 5 + a 6 * s 6 +
      a 7 * s 7 := by
  simp [dotProduct, Fin.sum_univ_eight]

lemma C_v2_zero : C_v2 0 0 0 = 0 := by
  funext i; fin_cases i <;> simp [C_v2]

lemma C_v1_zero : C_v1 0 0 0 = 0 := by
  funext i; fin_cases i <;> simp [C_v1]

/-- Unvisited child of the current node (logit `a₂`). -/
lemma C_T_u (hσ : Sel8 s σ) (ha2 : 0 < s 2) :
    exp (C_lg s 0 1 1 0 0 0) = exp (s 2) ∧ C_dv σ 0 1 1 0 0 0 = C_e2 := by
  have hv : C_v1 0 1 1 = C_e2 := by funext i; fin_cases i <;> simp [C_v1, C_e2]
  constructor
  · simp [C_lg, ha2.le]
  · have h1 : σ C_e2 = 1 := (hσ C_e2).2.1 (by rw [C_dot8]; simp [C_e2]; exact ha2)
    simp [C_dv, hv, h1, C_v2_zero]

/-- Tree child of the current node (logit `u₊ + v₊`). -/
lemma C_T_t :
    exp (C_lg s 1 1 1 1 1 0) = E8 s ∧ C_dv σ 1 1 1 1 1 0 = σ cu8 • cu8 + σ cv8 • cv8 := by
  have h1 : C_v1 1 1 1 = cu8 := by funext i; fin_cases i <;> simp [C_v1, cu8]
  have h2 : C_v2 1 1 0 = cv8 := by funext i; fin_cases i <;> simp [C_v2, cv8]
  constructor
  · simp only [C_lg, E8]; congr 3 <;> ring
  · simp [C_dv, h1, h2]

/-- Stack parent of the current node (logit `g₁ - d₁`). -/
lemma C_T_p (hσ : Sel8 s σ) (hb1 : 0 < s 1) (hb2 : s 3 < s 1) (hy : 0 < s 4 - s 5) {mc : ℝ}
    (hmc : 1 ≤ mc) :
    exp (C_lg s mc 0 1 1 0 0) = exp (s 4 - s 5) ∧ C_dv σ mc 0 1 1 0 0 = C_ep := by
  have h2 : C_v2 1 0 0 = C_ep := by funext i; fin_cases i <;> simp [C_v2, C_ep]
  have hneg : s 3 - mc * s 1 < 0 := by nlinarith
  constructor
  · simp only [C_lg]
    rw [max_eq_right (by linarith), max_eq_left (by linarith)]
    congr 1; ring
  · have e1 : σ (C_v1 mc 0 1) = 0 := (hσ _).2.2 (by rw [C_dot8]; simp [C_v1]; linarith)
    have e2 : σ C_ep = 1 := (hσ _).2.1 (by rw [C_dot8]; simp [C_ep]; linarith)
    simp [C_dv, e1, h2, e2]

/-- Visited vertex that is neither parent, tree child nor root (logit `0`). -/
lemma C_T_v (hσ : Sel8 s σ) (hb2 : s 3 < s 1) :
    exp (C_lg s 1 0 1 0 0 0) = 1 ∧ C_dv σ 1 0 1 0 0 0 = 0 := by
  constructor
  · simp only [C_lg]
    rw [max_eq_right (by linarith), max_eq_right (by linarith)]; simp
  · have e1 : σ (C_v1 1 0 1) = 0 := (hσ _).2.2 (by rw [C_dot8]; simp [C_v1]; linarith)
    simp [C_dv, e1, C_v2_zero]

/-- The root (logit `(d₂)₊`). -/
lemma C_T_r (hσ : Sel8 s σ) (hb1 : 0 < s 1) :
    exp (C_lg s 1 0 0 0 0 1) = ed8 s ∧ C_dv σ 1 0 0 0 0 1 = σ cd8 • cd8 := by
  have h2 : C_v2 0 0 1 = cd8 := by funext i; fin_cases i <;> simp [C_v2, cd8]
  constructor
  · simp only [C_lg, ed8]
    rw [max_eq_right (by linarith)]; congr 1; simp
  · have e1 : σ (C_v1 1 0 0) = 0 := (hσ _).2.2 (by rw [C_dot8]; simp [C_v1]; linarith)
    simp [C_dv, e1, h2]

/-- Unvisited non-child with in-degree one (logit `(b₂)₊`). -/
lemma C_T_b :
    exp (C_lg s 0 0 1 0 0 0) = eb8 s ∧ C_dv σ 0 0 1 0 0 0 = σ cb8 • cb8 := by
  have h1 : C_v1 0 0 1 = cb8 := by funext i; fin_cases i <;> simp [C_v1, cb8]
  constructor
  · simp [C_lg, eb8]
  · simp [C_dv, h1, C_v2_zero]

/-- Isolated unvisited vertex or the target (logit `0`). -/
lemma C_T_0 : exp (C_lg s 0 0 0 0 0 0) = 1 ∧ C_dv σ 0 0 0 0 0 0 = 0 := by
  constructor
  · simp [C_lg]
  · simp [C_dv, C_v1_zero, C_v2_zero]

end types


/-! ### Splitting a sum over the vertices into the vertex classes -/

lemma C_sum_decomp [NeZero N] {M : Type*} [AddCommMonoid M] (hN : K + 5 ≤ N) (F : Fin N → M) :
    ∑ v, F v = F (nd N 0) + ∑ m ∈ range K, F (nd N (m + 1)) +
      ∑ i ∈ Ico (K + 1) (N - 4), F (nd N i) + F (nd N (N - 4)) + F (nd N (N - 3)) +
      F (nd N (N - 2)) + F (nd N (N - 1)) := by
  have h0 : ∑ v, F v = ∑ i ∈ range N, F (nd N i) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => F (nd N i))]; simp [C_nd_self]
  rw [h0, ← Finset.sum_range_add_sum_Ico _ (show N - 4 ≤ N by omega),
    ← Finset.sum_range_add_sum_Ico _ (show K + 1 ≤ N - 4 by omega), Finset.sum_range_succ',
    Finset.sum_Ico_eq_sum_range (m := N - 4), show N - (N - 4) = 4 by omega]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [show N - 4 + 1 = N - 3 by omega, show N - 4 + 2 = N - 2 by omega,
    show N - 4 + 3 = N - 1 by omega, add_zero]
  abel


/-! ### Vertex values and the two sums of a step -/

/-- `exp` of the logit of `v` is `X` and the selected logit gradient of `v` is `D`. -/
def C_V (s : Fin 8 → ℝ) (σ : (Fin 8 → ℝ) → ℝ) (c : Ctx N) (v : Fin N) (X : ℝ) (D : Fin 8 → ℝ) :
    Prop :=
  exp (logit (iota s) c v) = X ∧ iotaT (dlogit c v (σ ∘ iotaT)) = D

lemma C_comb {s : Fin 8 → ℝ} {σ : (Fin 8 → ℝ) → ℝ} {c : Ctx N} {v : Fin N} {L X : ℝ}
    {Dv D : Fin 8 → ℝ} (h : logit (iota s) c v = L ∧ iotaT (dlogit c v (σ ∘ iotaT)) = Dv)
    (hT : exp L = X ∧ Dv = D) : C_V s σ c v X D :=
  ⟨by rw [h.1, hT.1], by rw [h.2, hT.2]⟩

lemma C_V_cur (s : Fin 8 → ℝ) (σ : (Fin 8 → ℝ) → ℝ) {c : Ctx N} {v : Fin N} (hv : v = c.cur) :
    C_V s σ c v 1 0 := by
  subst hv; exact C_vert_cur _ _ _

/-- Splitting a sum over the children at `j`. -/
lemma C_sum_ite2 {M : Type*} [AddCommGroup M] [Module ℝ M] {j : ℕ} (hj : j ≤ K) (a b : M) :
    ∑ m ∈ range K, (if m < j then a else b) = (j : ℝ) • a + ((K : ℝ) - j) • b := by
  rw [← Finset.sum_range_add_sum_Ico _ hj,
    Finset.sum_congr rfl (fun m hm => ite_eq_left (Finset.mem_range.1 hm)),
    Finset.sum_congr rfl (fun m hm => ite_eq_right (by have := (Finset.mem_Ico.1 hm).1; omega))]
  rw [Finset.sum_const, Finset.sum_const, Finset.card_range, Nat.card_Ico,
    ← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ, Nat.cast_sub hj]

lemma C_iotaT_gstep' (s : Fin 8 → ℝ) (σ : (Fin 8 → ℝ) → ℝ) (c : Ctx N) (y : Fin N) {Z : ℝ}
    {P Dy : Fin 8 → ℝ} (hZ : ∑ v, exp (logit (iota s) c v) = Z)
    (hP : ∑ v, exp (logit (iota s) c v) • iotaT (dlogit c v (σ ∘ iotaT)) = P)
    (hy : iotaT (dlogit c y (σ ∘ iotaT)) = Dy) :
    iotaT (gstep (iota s) (σ ∘ iotaT) c y) = Z⁻¹ • P - Dy := by
  rw [C_iotaT_gstep, hy, ← hP, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [smul_smul, prob, hZ, div_eq_inv_mul]

section canon2
variable [NeZero N]

/-- A vertex `nd N b` of a canonical-type context, from its list statistics. -/
lemma C_vert_nd (s : Fin 8 → ℝ) (σ : (Fin 8 → ℝ) → ℝ) (c : Ctx N) {cu : ℕ}
    (hcu : c.cur = nd N cu) (hroot : c.root = nd N (N - 2)) (hedges : c.edges = E0 N K)
    {nodes : List (Fin N)} (hnodes : c.root :: c.cot = nodes)
    {steps : List (Fin N × Fin N)} (hsteps : c.cot.zip (c.root :: c.cot) = steps)
    {b : ℕ} (hb : b < N) (hbc : b ≠ cu) (hcuN : cu < N) (hN2 : 2 ≤ N)
    {mc ec di tvc tcv r : ℝ}
    (h1 : (nodes.count (nd N b) : ℝ) = mc) (h2 : ((E0 N K).count (nd N cu, nd N b) : ℝ) = ec)
    (h3 : ((E0 N K).countP (fun e => decide (e.2 = nd N b)) : ℝ) = di)
    (h4 : (steps.count (nd N cu, nd N b) : ℝ) = tvc) (h5 : (steps.count (nd N b, nd N cu) : ℝ) = tcv)
    (h6 : (if b = N - 2 then (1 : ℝ) else 0) = r) :
    logit (iota s) c (nd N b) = C_lg s mc ec di tvc tcv r ∧
      iotaT (dlogit c (nd N b) (σ ∘ iotaT)) = C_dv σ mc ec di tvc tcv r := by
  have hv : nd N b ≠ c.cur := by rw [hcu, Ne, C_nd_eq_iff hb hcuN]; exact hbc
  apply C_vert s σ c _ hv
  · rw [C_mcnt, hnodes]; exact h1
  · rw [C_ecnt, hcu, hedges]; exact h2
  · rw [C_din, hedges]; exact h3
  · rw [C_trans, hsteps, hcu]; exact h4
  · rw [C_trans, hsteps, hcu]; exact h5
  · simp only [hroot, C_nd_eq_iff hb (show N - 2 < N by omega)]; exact h6

/-- The two sums of a step (normalizer and unnormalized expected logit gradient), split into the
vertex classes; the isolated vertices and the target always have logit `0` and gradient `0`. -/
lemma C_sums (s : Fin 8 → ℝ) (σ : (Fin 8 → ℝ) → ℝ) (c : Ctx N) (hN : K + 5 ≤ N)
    {X0 X4 X3 X2 : ℝ} {D0 D4 D3 D2 : Fin 8 → ℝ} (Xc : ℕ → ℝ) (Dc : ℕ → Fin 8 → ℝ)
    (h0 : C_V s σ c (nd N 0) X0 D0) (hc : ∀ m < K, C_V s σ c (nd N (m + 1)) (Xc m) (Dc m))
    (ho : ∀ i, K + 1 ≤ i → i < N - 4 → C_V s σ c (nd N i) 1 0)
    (h4 : C_V s σ c (nd N (N - 4)) X4 D4) (h3 : C_V s σ c (nd N (N - 3)) X3 D3)
    (h2 : C_V s σ c (nd N (N - 2)) X2 D2) (h1 : C_V s σ c (nd N (N - 1)) 1 0) :
    ∑ v, exp (logit (iota s) c v) =
        X0 + ∑ m ∈ range K, Xc m + ((N : ℝ) - K - 5) + X4 + X3 + X2 + 1 ∧
      ∑ v, exp (logit (iota s) c v) • iotaT (dlogit c v (σ ∘ iotaT)) =
        X0 • D0 + ∑ m ∈ range K, Xc m • Dc m + X4 • D4 + X3 • D3 + X2 • D2 := by
  have hcard : ((Finset.Ico (K + 1) (N - 4)).card : ℝ) = (N : ℝ) - K - 5 := by
    rw [Nat.card_Ico]
    have h : ((N - 4 - (K + 1) : ℕ) : ℝ) + K + 5 = N := by
      exact_mod_cast (by omega : N - 4 - (K + 1) + K + 5 = N)
    linarith
  have hc1 : ∑ m ∈ range K, exp (logit (iota s) c (nd N (m + 1))) = ∑ m ∈ range K, Xc m :=
    Finset.sum_congr rfl (fun m hm => (hc m (Finset.mem_range.1 hm)).1)
  have ho1 : ∑ i ∈ Finset.Ico (K + 1) (N - 4), exp (logit (iota s) c (nd N i)) =
      ∑ i ∈ Finset.Ico (K + 1) (N - 4), (1 : ℝ) :=
    Finset.sum_congr rfl (fun i hi => (ho i (Finset.mem_Ico.1 hi).1 (Finset.mem_Ico.1 hi).2).1)
  have hc2 : ∑ m ∈ range K, exp (logit (iota s) c (nd N (m + 1))) •
      iotaT (dlogit c (nd N (m + 1)) (σ ∘ iotaT)) = ∑ m ∈ range K, Xc m • Dc m :=
    Finset.sum_congr rfl (fun m hm => by
      rw [(hc m (Finset.mem_range.1 hm)).1, (hc m (Finset.mem_range.1 hm)).2])
  have ho2 : ∑ i ∈ Finset.Ico (K + 1) (N - 4), exp (logit (iota s) c (nd N i)) •
      iotaT (dlogit c (nd N i) (σ ∘ iotaT)) = 0 :=
    Finset.sum_eq_zero (fun i hi => by
      rw [(ho i (Finset.mem_Ico.1 hi).1 (Finset.mem_Ico.1 hi).2).2, smul_zero])
  constructor
  · rw [C_sum_decomp hN, h0.1, h4.1, h3.1, h2.1, h1.1, hc1, ho1, Finset.sum_const, nsmul_eq_mul,
      mul_one, hcard]
  · rw [C_sum_decomp hN, h0.1, h4.1, h3.1, h2.1, h1.1, h0.2, h4.2, h3.2, h2.2, h1.2, hc2, ho2]
    simp

end canon2

/-- Evaluates a list statistic of a vertex of a canonical context. -/
macro "C_ev" : tactic => `(tactic| (
  (try simp (disch := omega) only [C_count_cons, C_count_cons2, C_count_L, C_count_S, C_count_E0,
    C_countP_E0, List.count_nil, List.count_append, List.cons_append, List.nil_append]) <;>
  (try simp (disch := omega) only [ite_eq_left, ite_eq_right, true_and, and_true]) <;>
  (try norm_num)))


/-! ### Odd steps `k = 2j + 1` (Cases 2 and 4: current node `1`, `j` tree children done) -/

section odd
variable [NeZero N] {s : Fin 8 → ℝ} {σ : (Fin 8 → ℝ) → ℝ}

lemma C_nodes_odd {j : ℕ} (hj : j ≤ K) :
    (ctx N K (2 * j + 1)).root :: (ctx N K (2 * j + 1)).cot =
      nd N (N - 2) :: nd N (N - 3) :: nd N (N - 4) :: nd N 0 :: C_L N j := by
  rw [C_root, C_cot_odd hj]

lemma C_odd_V (hσ : Sel8 s σ) (hb1 : 0 < s 1) (hb2 : s 3 < s 1) (ha2 : 0 < s 2)
    (hy : 0 < s 4 - s 5) (hN : K + 5 ≤ N) {j : ℕ} (hj : j ≤ K) :
    (∀ m < j, C_V s σ (ctx N K (2 * j + 1)) (nd N (m + 1)) (E8 s) (σ cu8 • cu8 + σ cv8 • cv8)) ∧
    (∀ m, j ≤ m → m < K → C_V s σ (ctx N K (2 * j + 1)) (nd N (m + 1)) (exp (s 2)) C_e2) ∧
    (∀ i, K + 1 ≤ i → i < N - 4 → C_V s σ (ctx N K (2 * j + 1)) (nd N i) 1 0) ∧
    C_V s σ (ctx N K (2 * j + 1)) (nd N (N - 4)) (exp (s 4 - s 5)) C_ep ∧
    C_V s σ (ctx N K (2 * j + 1)) (nd N (N - 3)) 1 0 ∧
    C_V s σ (ctx N K (2 * j + 1)) (nd N (N - 2)) (ed8 s) (σ cd8 • cd8) ∧
    C_V s σ (ctx N K (2 * j + 1)) (nd N (N - 1)) 1 0 := by
  have V := fun b (hb : b < N) (hb0 : b ≠ 0) {mc ec di tvc tcv r : ℝ} =>
    C_vert_nd (K := K) (mc := mc) (ec := ec) (di := di) (tvc := tvc) (tcv := tcv) (r := r) s σ
      (ctx N K (2 * j + 1)) (C_cur_odd hj) (C_root _) (C_edges _)
      (C_nodes_odd hj) (C_zip_odd hj) hb hb0 (by omega) (by omega)
  refine ⟨fun m hm => ?_, fun m hm hmK => ?_, fun i hi1 hi2 => ?_, ?_, ?_, ?_, ?_⟩
  · refine C_comb (V (m + 1) (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_) C_T_t <;> (clear V; C_ev)
  · refine C_comb (V (m + 1) (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_) (C_T_u hσ ha2) <;> (clear V; C_ev)
  · refine C_comb (V i (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_) C_T_0 <;> (clear V; C_ev)
  · refine C_comb (V (N - 4) (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_) (C_T_p hσ hb1 hb2 hy le_rfl) <;> (clear V; C_ev)
  · refine C_comb (V (N - 3) (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_) (C_T_v hσ hb2) <;> (clear V; C_ev)
  · refine C_comb (V (N - 2) (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_) (C_T_r hσ hb1) <;> (clear V; C_ev)
  · refine C_comb (V (N - 1) (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_) C_T_0 <;> (clear V; C_ev)

lemma C_odd_sums (hσ : Sel8 s σ) (hb1 : 0 < s 1) (hb2 : s 3 < s 1) (ha2 : 0 < s 2)
    (hy : 0 < s 4 - s 5) (hN : K + 5 ≤ N) {j : ℕ} (hj : j ≤ K) :
    ∑ v, exp (logit (iota s) (ctx N K (2 * j + 1)) v) = Q2 N K s j ∧
    ∑ v, exp (logit (iota s) (ctx N K (2 * j + 1)) v) •
        iotaT (dlogit (ctx N K (2 * j + 1)) v (σ ∘ iotaT)) =
      (j : ℝ) • (E8 s • (σ cu8 • cu8 + σ cv8 • cv8)) + ((K : ℝ) - j) • (exp (s 2) • C_e2) +
        exp (s 4 - s 5) • C_ep + ed8 s • (σ cd8 • cd8) := by
  obtain ⟨ht, hu, ho, h4, h3, h2, h1⟩ := C_odd_V hσ hb1 hb2 ha2 hy hN hj
  have hc : ∀ m < K, C_V s σ (ctx N K (2 * j + 1)) (nd N (m + 1))
      (if m < j then E8 s else exp (s 2)) (if m < j then σ cu8 • cu8 + σ cv8 • cv8 else C_e2) := by
    intro m hm
    by_cases hmj : m < j
    · rw [ite_eq_left hmj, ite_eq_left hmj]; exact ht m hmj
    · rw [ite_eq_right hmj, ite_eq_right hmj]; exact hu m (by omega) hm
  obtain ⟨hZ, hP⟩ := C_sums s σ _ hN _ _ (C_V_cur s σ (C_cur_odd hj).symm) hc ho h4 h3 h2 h1
  constructor
  · rw [hZ, C_sum_ite2 hj, Q2]; simp only [smul_eq_mul]; ring
  · rw [hP]
    have e : ∀ m ∈ range K, (if m < j then E8 s else exp (s 2)) •
        (if m < j then σ cu8 • cu8 + σ cv8 • cv8 else C_e2) =
        if m < j then E8 s • (σ cu8 • cu8 + σ cv8 • cv8) else exp (s 2) • C_e2 :=
      fun m _ => by split_ifs <;> rfl
    rw [Finset.sum_congr rfl e, C_sum_ite2 hj]
    simp only [smul_zero, zero_add, add_zero]

end odd

/-! ### The per-step gradient vectors (summands of eqs. `grad_R_a1` – `grad_R_d2`) -/

section vecs
variable (N K : ℕ) (s : Fin 8 → ℝ) (σ : (Fin 8 → ℝ) → ℝ)

/-- Case 1 (step `N-2 → 1`, paper labels). -/
def C_G1 : Fin 8 → ℝ :=
  ![0, 0, -1 + exp (s 2) / Q1 N K s, eb8 s * σ cb8 * ((K : ℝ) / Q1 N K s),
    exp (s 4 - s 5) / Q1 N K s, -(exp (s 4 - s 5) / Q1 N K s), 0, ed8 s * σ cd8 * (1 / Q1 N K s)]

/-- Case 2 (step `1 → j+2`, paper labels). -/
def C_G2 (j : ℕ) : Fin 8 → ℝ :=
  ![0, -((j : ℝ) * E8 s * σ cu8 / Q2 N K s j),
    -1 + (((K : ℝ) - j) * exp (s 2) + (j : ℝ) * E8 s * σ cu8) / Q2 N K s j, 0,
    ((j : ℝ) * E8 s * σ cv8 + exp (s 4 - s 5)) / Q2 N K s j,
    -(((j : ℝ) * E8 s * σ cv8 + exp (s 4 - s 5)) / Q2 N K s j),
    -((j : ℝ) * E8 s * σ cv8 / Q2 N K s j),
    (j : ℝ) * E8 s * σ cv8 / Q2 N K s j + ed8 s * σ cd8 * (1 / Q2 N K s j)]

/-- Case 3 (step `j+2 → 1`, paper labels). -/
def C_G3 (j : ℕ) : Fin 8 → ℝ :=
  ![0, 0, 0, eb8 s * σ cb8 * (((K : ℝ) - 1 - j) / Q3 N K s j), -1 + exp (s 4 - s 5) / Q3 N K s j,
    -(-1 + exp (s 4 - s 5) / Q3 N K s j), 0, ed8 s * σ cd8 * (1 / Q3 N K s j)]

/-- Case 4 (step `1 → N-2`, paper labels). -/
def C_G4 : Fin 8 → ℝ :=
  ![0, -((K : ℝ) * E8 s * σ cu8 / Q4 N K s), (K : ℝ) * E8 s * σ cu8 / Q4 N K s, 0,
    -1 + ((K : ℝ) * E8 s * σ cv8 + exp (s 4 - s 5)) / Q4 N K s,
    -(-1 + ((K : ℝ) * E8 s * σ cv8 + exp (s 4 - s 5)) / Q4 N K s),
    -((K : ℝ) * E8 s * σ cv8 / Q4 N K s),
    (K : ℝ) * E8 s * σ cv8 / Q4 N K s + ed8 s * σ cd8 * (1 / Q4 N K s)]

end vecs

section cases24
variable [NeZero N] {s : Fin 8 → ℝ} {σ : (Fin 8 → ℝ) → ℝ}

lemma C_case2 (hσ : Sel8 s σ) (hb1 : 0 < s 1) (hb2 : s 3 < s 1) (ha2 : 0 < s 2)
    (hy : 0 < s 4 - s 5) (hN : K + 5 ≤ N) {j : ℕ} (hj : j < K) :
    iotaT (gstep (iota s) (σ ∘ iotaT) (ctx N K (2 * j + 1)) (ylab N K (2 * j + 1))) =
      C_G2 N K s σ j := by
  obtain ⟨hZ, hP⟩ := C_odd_sums hσ hb1 hb2 ha2 hy hN hj.le
  rw [C_ylab_odd hj,
    C_iotaT_gstep' s σ _ _ hZ hP ((C_odd_V hσ hb1 hb2 ha2 hy hN hj.le).2.1 j le_rfl hj).2]
  funext i
  fin_cases i <;> simp [C_G2, cu8, cv8, cd8, C_e2, C_ep] <;> ring

lemma C_case4 (hσ : Sel8 s σ) (hb1 : 0 < s 1) (hb2 : s 3 < s 1) (ha2 : 0 < s 2)
    (hy : 0 < s 4 - s 5) (hN : K + 5 ≤ N) :
    iotaT (gstep (iota s) (σ ∘ iotaT) (ctx N K (2 * K + 1)) (ylab N K (2 * K + 1))) =
      C_G4 N K s σ := by
  obtain ⟨hZ, hP⟩ := C_odd_sums hσ hb1 hb2 ha2 hy hN (le_refl K)
  have hQ : Q2 N K s K = Q4 N K s := by simp only [Q2, Q4]; ring
  rw [hQ] at hZ
  rw [C_ylab_last,
    C_iotaT_gstep' s σ _ _ hZ hP (C_odd_V hσ hb1 hb2 ha2 hy hN (le_refl K)).2.2.2.1.2]
  funext i
  fin_cases i <;> simp [C_G4, cu8, cv8, cd8, C_e2, C_ep] <;> ring

end cases24

/-! ### Even steps `k = 2j + 2` (Case 3: current node `j + 2`, paper labels) -/

section even
variable [NeZero N] {s : Fin 8 → ℝ} {σ : (Fin 8 → ℝ) → ℝ}

lemma C_nodes_even {j : ℕ} (hj : j < K) :
    (ctx N K (2 * j + 2)).root :: (ctx N K (2 * j + 2)).cot =
      nd N (N - 2) :: nd N (N - 3) :: nd N (N - 4) :: nd N 0 :: (C_L N j ++ [nd N (j + 1)]) := by
  rw [C_root, C_cot_even hj]

lemma C_even_V (hσ : Sel8 s σ) (hb1 : 0 < s 1) (hb2 : s 3 < s 1)
    (hy : 0 < s 4 - s 5) (hN : K + 5 ≤ N) {j : ℕ} (hj : j < K) :
    C_V s σ (ctx N K (2 * j + 2)) (nd N 0) (exp (s 4 - s 5)) C_ep ∧
    (∀ m < j, C_V s σ (ctx N K (2 * j + 2)) (nd N (m + 1)) 1 0) ∧
    (∀ m, j < m → m < K → C_V s σ (ctx N K (2 * j + 2)) (nd N (m + 1)) (eb8 s) (σ cb8 • cb8)) ∧
    (∀ i, K + 1 ≤ i → i < N - 4 → C_V s σ (ctx N K (2 * j + 2)) (nd N i) 1 0) ∧
    C_V s σ (ctx N K (2 * j + 2)) (nd N (N - 4)) 1 0 ∧
    C_V s σ (ctx N K (2 * j + 2)) (nd N (N - 3)) 1 0 ∧
    C_V s σ (ctx N K (2 * j + 2)) (nd N (N - 2)) (ed8 s) (σ cd8 • cd8) ∧
    C_V s σ (ctx N K (2 * j + 2)) (nd N (N - 1)) 1 0 := by
  have V := fun b (hb : b < N) (hb0 : b ≠ j + 1) {mc ec di tvc tcv r : ℝ} =>
    C_vert_nd (K := K) (mc := mc) (ec := ec) (di := di) (tvc := tvc) (tcv := tcv) (r := r) s σ
      (ctx N K (2 * j + 2)) (C_cur_even hj) (C_root _) (C_edges _)
      (C_nodes_even hj) (C_zip_even hj) hb hb0 (by omega) (by omega)
  have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by have := (Nat.cast_nonneg (α := ℝ) j); linarith
  refine ⟨?_, fun m hm => ?_, fun m hm hmK => ?_, fun i hi1 hi2 => ?_, ?_, ?_, ?_, ?_⟩
  · refine C_comb (V 0 (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_) (C_T_p hσ hb1 hb2 hy hj1) <;>
      (clear V; C_ev)
  · refine C_comb (V (m + 1) (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_) (C_T_v hσ hb2) <;> (clear V; C_ev)
  · refine C_comb (V (m + 1) (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_) C_T_b <;> (clear V; C_ev)
  · refine C_comb (V i (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_) C_T_0 <;> (clear V; C_ev)
  · refine C_comb (V (N - 4) (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_) (C_T_v hσ hb2) <;> (clear V; C_ev)
  · refine C_comb (V (N - 3) (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_) (C_T_v hσ hb2) <;> (clear V; C_ev)
  · refine C_comb (V (N - 2) (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_) (C_T_r hσ hb1) <;> (clear V; C_ev)
  · refine C_comb (V (N - 1) (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_) C_T_0 <;> (clear V; C_ev)


lemma C_case3 (hσ : Sel8 s σ) (hb1 : 0 < s 1) (hb2 : s 3 < s 1)
    (hy : 0 < s 4 - s 5) (hN : K + 5 ≤ N) {j : ℕ} (hj : j < K) :
    iotaT (gstep (iota s) (σ ∘ iotaT) (ctx N K (2 * j + 2)) (ylab N K (2 * j + 2))) =
      C_G3 N K s σ j := by
  obtain ⟨h0, hv, hb, ho, h4, h3, h2, h1⟩ := C_even_V hσ hb1 hb2 hy hN hj
  have hc : ∀ m < K, C_V s σ (ctx N K (2 * j + 2)) (nd N (m + 1))
      (if m < j + 1 then 1 else eb8 s) (if m < j + 1 then 0 else σ cb8 • cb8) := by
    intro m hm
    by_cases hmj : m < j + 1
    · rw [ite_eq_left hmj, ite_eq_left hmj]
      by_cases hmj' : m < j
      · exact hv m hmj'
      · exact C_V_cur s σ (by rw [C_cur_even hj, show m = j by omega])
    · rw [ite_eq_right hmj, ite_eq_right hmj]; exact hb m (by omega) hm
  obtain ⟨hZ, hP⟩ := C_sums s σ _ hN _ _ h0 hc ho h4 h3 h2 h1
  have e : ∀ m ∈ range K, (if m < j + 1 then 1 else eb8 s) •
      (if m < j + 1 then (0 : Fin 8 → ℝ) else σ cb8 • cb8) =
      if m < j + 1 then 0 else eb8 s • (σ cb8 • cb8) :=
    fun m _ => by split_ifs <;> simp
  rw [Finset.sum_congr rfl e, C_sum_ite2 (show j + 1 ≤ K by omega)] at hP
  rw [C_sum_ite2 (show j + 1 ≤ K by omega)] at hZ
  have hQ : exp (s 4 - s 5) + ((((j + 1 : ℕ) : ℝ)) • (1 : ℝ) + ((K : ℝ) - ((j + 1 : ℕ) : ℝ)) • eb8 s) +
      ((N : ℝ) - K - 5) + 1 + 1 + ed8 s + 1 = Q3 N K s j := by
    simp only [Q3, smul_eq_mul]; push_cast; ring
  rw [hQ] at hZ
  rw [C_ylab_even hj, C_iotaT_gstep' s σ _ _ hZ hP h0.2]
  funext i
  fin_cases i <;> simp [C_G3, cb8, cd8, C_ep] <;> ring

end even

/-! ### Step `k = 0` (Case 1: current node `N - 2`, paper labels) -/

section zero
variable [NeZero N] {s : Fin 8 → ℝ} {σ : (Fin 8 → ℝ) → ℝ}

lemma C_nodes_zero :
    (ctx N K 0).root :: (ctx N K 0).cot = nd N (N - 2) :: nd N (N - 3) :: nd N (N - 4) :: [] := by
  rw [C_root, C_cot_zero]

lemma C_zero_V (hσ : Sel8 s σ) (hb1 : 0 < s 1) (hb2 : s 3 < s 1) (ha2 : 0 < s 2)
    (hy : 0 < s 4 - s 5) (hN : K + 5 ≤ N) :
    C_V s σ (ctx N K 0) (nd N 0) (exp (s 2)) C_e2 ∧
    (∀ m < K, C_V s σ (ctx N K 0) (nd N (m + 1)) (eb8 s) (σ cb8 • cb8)) ∧
    (∀ i, K + 1 ≤ i → i < N - 4 → C_V s σ (ctx N K 0) (nd N i) 1 0) ∧
    C_V s σ (ctx N K 0) (nd N (N - 3)) (exp (s 4 - s 5)) C_ep ∧
    C_V s σ (ctx N K 0) (nd N (N - 2)) (ed8 s) (σ cd8 • cd8) ∧
    C_V s σ (ctx N K 0) (nd N (N - 1)) 1 0 := by
  have V := fun b (hb : b < N) (hb0 : b ≠ N - 4) {mc ec di tvc tcv r : ℝ} =>
    C_vert_nd (K := K) (mc := mc) (ec := ec) (di := di) (tvc := tvc) (tcv := tcv) (r := r) s σ
      (ctx N K 0) C_cur_zero (C_root _) (C_edges _) C_nodes_zero C_zip_zero hb hb0 (by omega)
      (by omega)
  refine ⟨?_, fun m hm => ?_, fun i hi1 hi2 => ?_, ?_, ?_, ?_⟩
  · refine C_comb (V 0 (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_) (C_T_u hσ ha2) <;> (clear V; C_ev)
  · refine C_comb (V (m + 1) (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_) C_T_b <;> (clear V; C_ev)
  · refine C_comb (V i (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_) C_T_0 <;> (clear V; C_ev)
  · refine C_comb (V (N - 3) (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_) (C_T_p hσ hb1 hb2 hy le_rfl) <;>
      (clear V; C_ev)
  · refine C_comb (V (N - 2) (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_) (C_T_r hσ hb1) <;> (clear V; C_ev)
  · refine C_comb (V (N - 1) (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_) C_T_0 <;> (clear V; C_ev)

lemma C_case1 (hσ : Sel8 s σ) (hb1 : 0 < s 1) (hb2 : s 3 < s 1) (ha2 : 0 < s 2)
    (hy : 0 < s 4 - s 5) (hN : K + 5 ≤ N) :
    iotaT (gstep (iota s) (σ ∘ iotaT) (ctx N K 0) (ylab N K 0)) = C_G1 N K s σ := by
  obtain ⟨h0, hb, ho, h3, h2, h1⟩ := C_zero_V hσ hb1 hb2 ha2 hy hN
  obtain ⟨hZ, hP⟩ := C_sums s σ _ hN (fun _ => eb8 s) (fun _ => σ cb8 • cb8) h0 hb ho
    (C_V_cur s σ C_cur_zero.symm) h3 h2 h1
  rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ] at hZ hP
  have hQ : exp (s 2) + (K : ℝ) • eb8 s + ((N : ℝ) - K - 5) + 1 + exp (s 4 - s 5) + ed8 s + 1 =
      Q1 N K s := by
    simp only [Q1, smul_eq_mul]; ring
  rw [hQ] at hZ
  rw [C_ylab_zero, C_iotaT_gstep' s σ _ _ hZ hP h0.2]
  funext i
  fin_cases i <;> simp [C_G1, cb8, cd8, C_e2, C_ep] <;> ring

end zero

/-! ### Assembly over the `2K + 2` steps -/

lemma C_range_split {M : Type*} [AddCommMonoid M] (f : ℕ → M) (K : ℕ) :
    ∑ k ∈ range (2 * K + 2), f k =
      f 0 + ∑ j ∈ range K, f (2 * j + 1) + ∑ j ∈ range K, f (2 * j + 2) + f (2 * K + 1) := by
  induction K with
  | zero => simp [Finset.sum_range_succ]
  | succ K ih =>
    rw [show 2 * (K + 1) + 2 = 2 * K + 2 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ, Finset.sum_range_succ,
      show 2 * (K + 1) + 1 = 2 * K + 2 + 1 by ring, show 2 * K + 2 = 2 * K + 2 by rfl]
    abel

lemma C_g8_split [NeZero N] {s : Fin 8 → ℝ} {σ : (Fin 8 → ℝ) → ℝ} (hσ : Sel8 s σ)
    (hb1 : 0 < s 1) (hb2 : s 3 < s 1) (ha2 : 0 < s 2) (hy : 0 < s 4 - s 5) (hN : K + 5 ≤ N) :
    g8 N K s σ = C_G1 N K s σ + ∑ j ∈ range K, C_G2 N K s σ j + ∑ j ∈ range K, C_G3 N K s σ j +
      C_G4 N K s σ := by
  unfold g8 gInst
  rw [C_iotaT_sum]
  simp only [C_perm_one, Equiv.Perm.coe_one, id]
  rw [C_range_split, C_case1 hσ hb1 hb2 ha2 hy hN, C_case4 hσ hb1 hb2 ha2 hy hN,
    Finset.sum_congr rfl (fun j hj => C_case2 hσ hb1 hb2 ha2 hy hN (Finset.mem_range.1 hj)),
    Finset.sum_congr rfl (fun j hj => C_case3 hσ hb1 hb2 hy hN (Finset.mem_range.1 hj))]


/-! ### The main statements -/

section main
variable [NeZero N]

set_option linter.unusedVariables false in
/-- Eqs. `grad_R_a1` – `grad_R_d2`, with `σ cu8, σ cv8, σ cb8, σ cd8` the selected values of
`𝟙{u ≥ 0}, 𝟙{v ≥ 0}, 𝟙{b₂ ≥ 0}, 𝟙{d₂ ≥ 0}`, on `R' = {b₁ > 0, b₂ < b₁, a₂ > 0, g₁ - d₁ > 0}`. -/
theorem g8_on_R (hK : 2 ≤ K) (hN : K + 5 ≤ N) (s : Fin 8 → ℝ) (σ : (Fin 8 → ℝ) → ℝ)
    (hσ : Sel8 s σ) (hb1 : 0 < s 1) (hb2 : s 3 < s 1) (ha2 : 0 < s 2) (hy : 0 < s 4 - s 5) :
    g8 N K s σ = ![0,
      -(∑ j ∈ range K, (j : ℝ) * E8 s * σ cu8 / Q2 N K s j) - (K : ℝ) * E8 s * σ cu8 / Q4 N K s,
      -1 + exp (s 2) / Q1 N K s
        + ∑ j ∈ range K, (-1 + (((K : ℝ) - j) * exp (s 2) + (j : ℝ) * E8 s * σ cu8) / Q2 N K s j)
        + (K : ℝ) * E8 s * σ cu8 / Q4 N K s,
      eb8 s * σ cb8 * ((K : ℝ) / Q1 N K s + ∑ j ∈ range K, ((K : ℝ) - 1 - j) / Q3 N K s j),
      exp (s 4 - s 5) / Q1 N K s
        + ∑ j ∈ range K, ((j : ℝ) * E8 s * σ cv8 + exp (s 4 - s 5)) / Q2 N K s j
        + ∑ j ∈ range K, (-1 + exp (s 4 - s 5) / Q3 N K s j)
        - 1 + ((K : ℝ) * E8 s * σ cv8 + exp (s 4 - s 5)) / Q4 N K s,
      -(exp (s 4 - s 5) / Q1 N K s
        + ∑ j ∈ range K, ((j : ℝ) * E8 s * σ cv8 + exp (s 4 - s 5)) / Q2 N K s j
        + ∑ j ∈ range K, (-1 + exp (s 4 - s 5) / Q3 N K s j)
        - 1 + ((K : ℝ) * E8 s * σ cv8 + exp (s 4 - s 5)) / Q4 N K s),
      -(∑ j ∈ range K, (j : ℝ) * E8 s * σ cv8 / Q2 N K s j) - (K : ℝ) * E8 s * σ cv8 / Q4 N K s,
      (∑ j ∈ range K, (j : ℝ) * E8 s * σ cv8 / Q2 N K s j) + (K : ℝ) * E8 s * σ cv8 / Q4 N K s
        + ed8 s * σ cd8 * (1 / Q1 N K s + ∑ j ∈ range K, 1 / Q2 N K s j
            + ∑ j ∈ range K, 1 / Q3 N K s j + 1 / Q4 N K s)] := by
  rw [C_g8_split hσ hb1 hb2 ha2 hy hN]
  funext i
  simp only [Pi.add_apply, Finset.sum_apply]
  fin_cases i <;>
    simp [C_G1, C_G2, C_G3, C_G4, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      Finset.mul_sum, mul_add] <;> ring



end main

/-! ### Each step contributes at most `1` in absolute value to each partial derivative -/

lemma C_bd_frac {a Q : ℝ} (hQ : 0 < Q) (h0 : 0 ≤ a) (h1 : a ≤ Q) : |a / Q| ≤ 1 := by
  rw [abs_le]
  exact ⟨by have := div_nonneg h0 hQ.le; linarith, (div_le_one hQ).2 h1⟩

lemma C_bd_frac' {a Q : ℝ} (hQ : 0 < Q) (h0 : 0 ≤ a) (h1 : a ≤ Q) : |-1 + a / Q| ≤ 1 := by
  rw [abs_le]
  exact ⟨by have := div_nonneg h0 hQ.le; linarith, by have := (div_le_one hQ).2 h1; linarith⟩

section bounds
variable {s : Fin 8 → ℝ} {σ : (Fin 8 → ℝ) → ℝ}

lemma C_sel01 (hσ : Sel8 s σ) (c : Fin 8 → ℝ) : 0 ≤ σ c ∧ σ c ≤ 1 := (hσ c).1

lemma C_mul_sel {x : ℝ} (hσ : Sel8 s σ) (c : Fin 8 → ℝ) (hx : 0 ≤ x) :
    0 ≤ x * σ c ∧ x * σ c ≤ x :=
  ⟨mul_nonneg hx (C_sel01 hσ c).1, mul_le_of_le_one_right hx (C_sel01 hσ c).2⟩

lemma C_G1_bd (hσ : Sel8 s σ) (hN : K + 5 ≤ N) (i : Fin 8) : |C_G1 N K s σ i| ≤ 1 := by
  have hN' : (K : ℝ) + 5 ≤ N := by exact_mod_cast hN
  have h2 := exp_pos (s 2); have hy := exp_pos (s 4 - s 5)
  have hd : 0 < ed8 s := exp_pos _; have hb : 0 < eb8 s := exp_pos _
  have hKb : 0 ≤ (K : ℝ) * eb8 s := by positivity
  have hQ : 0 < Q1 N K s := by unfold Q1; linarith
  have hQ' : Q1 N K s = exp (s 2) + exp (s 4 - s 5) + ed8 s + (K : ℝ) * eb8 s + ((N : ℝ) - K - 3) := by
    unfold Q1; ring
  obtain ⟨b0, b1⟩ := C_mul_sel hσ cb8 hKb
  obtain ⟨d0, d1⟩ := C_mul_sel hσ cd8 hd.le
  fin_cases i
  · show |(0 : ℝ)| ≤ 1; simp
  · show |(0 : ℝ)| ≤ 1; simp
  · show |-1 + exp (s 2) / Q1 N K s| ≤ 1; exact C_bd_frac' hQ h2.le (by linarith)
  · show |eb8 s * σ cb8 * ((K : ℝ) / Q1 N K s)| ≤ 1
    rw [show eb8 s * σ cb8 * ((K : ℝ) / Q1 N K s) = (K : ℝ) * eb8 s * σ cb8 / Q1 N K s by ring]
    exact C_bd_frac hQ b0 (by linarith)
  · show |exp (s 4 - s 5) / Q1 N K s| ≤ 1; exact C_bd_frac hQ hy.le (by linarith)
  · show |-(exp (s 4 - s 5) / Q1 N K s)| ≤ 1
    rw [abs_neg]; exact C_bd_frac hQ hy.le (by linarith)
  · show |(0 : ℝ)| ≤ 1; simp
  · show |ed8 s * σ cd8 * (1 / Q1 N K s)| ≤ 1
    rw [show ed8 s * σ cd8 * (1 / Q1 N K s) = ed8 s * σ cd8 / Q1 N K s by ring]
    exact C_bd_frac hQ d0 (by linarith)

lemma C_G2_bd (hσ : Sel8 s σ) (hN : K + 5 ≤ N) {j : ℕ} (hj : j ≤ K) (i : Fin 8) :
    |C_G2 N K s σ j i| ≤ 1 := by
  have hN' : (K : ℝ) + 5 ≤ N := by exact_mod_cast hN
  have hj' : (j : ℝ) ≤ K := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have h2 := exp_pos (s 2); have hy := exp_pos (s 4 - s 5)
  have hd : 0 < ed8 s := exp_pos _; have hE : 0 < E8 s := exp_pos _
  have hKj : 0 ≤ ((K : ℝ) - j) * exp (s 2) := mul_nonneg (by linarith) h2.le
  have hjE : 0 ≤ (j : ℝ) * E8 s := by positivity
  have hQ' : Q2 N K s j = ((K : ℝ) - j) * exp (s 2) + (j : ℝ) * E8 s + exp (s 4 - s 5) + 1 +
      ed8 s + ((N : ℝ) - K - 3) := by unfold Q2; ring
  have hQ : 0 < Q2 N K s j := by rw [hQ']; linarith
  obtain ⟨u0, u1⟩ := C_mul_sel hσ cu8 hjE
  obtain ⟨v0, v1⟩ := C_mul_sel hσ cv8 hjE
  obtain ⟨d0, d1⟩ := C_mul_sel hσ cd8 hd.le
  fin_cases i
  · show |(0 : ℝ)| ≤ 1; simp
  · show |-((j : ℝ) * E8 s * σ cu8 / Q2 N K s j)| ≤ 1
    rw [abs_neg]; exact C_bd_frac hQ u0 (by linarith)
  · show |-1 + (((K : ℝ) - j) * exp (s 2) + (j : ℝ) * E8 s * σ cu8) / Q2 N K s j| ≤ 1
    exact C_bd_frac' hQ (by linarith) (by linarith)
  · show |(0 : ℝ)| ≤ 1; simp
  · show |((j : ℝ) * E8 s * σ cv8 + exp (s 4 - s 5)) / Q2 N K s j| ≤ 1
    exact C_bd_frac hQ (by linarith) (by linarith)
  · show |-(((j : ℝ) * E8 s * σ cv8 + exp (s 4 - s 5)) / Q2 N K s j)| ≤ 1
    rw [abs_neg]; exact C_bd_frac hQ (by linarith) (by linarith)
  · show |-((j : ℝ) * E8 s * σ cv8 / Q2 N K s j)| ≤ 1
    rw [abs_neg]; exact C_bd_frac hQ v0 (by linarith)
  · show |(j : ℝ) * E8 s * σ cv8 / Q2 N K s j + ed8 s * σ cd8 * (1 / Q2 N K s j)| ≤ 1
    rw [show (j : ℝ) * E8 s * σ cv8 / Q2 N K s j + ed8 s * σ cd8 * (1 / Q2 N K s j) =
      ((j : ℝ) * E8 s * σ cv8 + ed8 s * σ cd8) / Q2 N K s j by ring]
    exact C_bd_frac hQ (by linarith) (by linarith)

lemma C_G3_bd (hσ : Sel8 s σ) (hN : K + 5 ≤ N) {j : ℕ} (hj : j < K) (i : Fin 8) :
    |C_G3 N K s σ j i| ≤ 1 := by
  have hN' : (K : ℝ) + 5 ≤ N := by exact_mod_cast hN
  have hj' : (j : ℝ) + 1 ≤ K := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hy := exp_pos (s 4 - s 5)
  have hd : 0 < ed8 s := exp_pos _; have hb : 0 < eb8 s := exp_pos _
  have hKb : 0 ≤ ((K : ℝ) - 1 - j) * eb8 s := mul_nonneg (by linarith) hb.le
  have hQ' : Q3 N K s j = exp (s 4 - s 5) + 2 + ed8 s + (j : ℝ) + ((K : ℝ) - 1 - j) * eb8 s +
      ((N : ℝ) - K - 3) := by unfold Q3; ring
  have hQ : 0 < Q3 N K s j := by rw [hQ']; linarith
  obtain ⟨b0, b1⟩ := C_mul_sel hσ cb8 hKb
  obtain ⟨d0, d1⟩ := C_mul_sel hσ cd8 hd.le
  fin_cases i
  · show |(0 : ℝ)| ≤ 1; simp
  · show |(0 : ℝ)| ≤ 1; simp
  · show |(0 : ℝ)| ≤ 1; simp
  · show |eb8 s * σ cb8 * (((K : ℝ) - 1 - j) / Q3 N K s j)| ≤ 1
    rw [show eb8 s * σ cb8 * (((K : ℝ) - 1 - j) / Q3 N K s j) =
      ((K : ℝ) - 1 - j) * eb8 s * σ cb8 / Q3 N K s j by ring]
    exact C_bd_frac hQ b0 (by linarith)
  · show |-1 + exp (s 4 - s 5) / Q3 N K s j| ≤ 1
    exact C_bd_frac' hQ hy.le (by linarith)
  · show |-(-1 + exp (s 4 - s 5) / Q3 N K s j)| ≤ 1
    rw [abs_neg]; exact C_bd_frac' hQ hy.le (by linarith)
  · show |(0 : ℝ)| ≤ 1; simp
  · show |ed8 s * σ cd8 * (1 / Q3 N K s j)| ≤ 1
    rw [show ed8 s * σ cd8 * (1 / Q3 N K s j) = ed8 s * σ cd8 / Q3 N K s j by ring]
    exact C_bd_frac hQ d0 (by linarith)

lemma C_G4_bd (hσ : Sel8 s σ) (hN : K + 5 ≤ N) (i : Fin 8) : |C_G4 N K s σ i| ≤ 1 := by
  have hN' : (K : ℝ) + 5 ≤ N := by exact_mod_cast hN
  have hy := exp_pos (s 4 - s 5)
  have hd : 0 < ed8 s := exp_pos _; have hE : 0 < E8 s := exp_pos _
  have hKE : 0 ≤ (K : ℝ) * E8 s := by positivity
  have hQ' : Q4 N K s = (K : ℝ) * E8 s + exp (s 4 - s 5) + 1 + ed8 s + ((N : ℝ) - K - 3) := by
    unfold Q4; ring
  have hQ : 0 < Q4 N K s := by rw [hQ']; linarith
  obtain ⟨u0, u1⟩ := C_mul_sel hσ cu8 hKE
  obtain ⟨v0, v1⟩ := C_mul_sel hσ cv8 hKE
  obtain ⟨d0, d1⟩ := C_mul_sel hσ cd8 hd.le
  fin_cases i
  · show |(0 : ℝ)| ≤ 1; simp
  · show |-((K : ℝ) * E8 s * σ cu8 / Q4 N K s)| ≤ 1
    rw [abs_neg]; exact C_bd_frac hQ u0 (by linarith)
  · show |(K : ℝ) * E8 s * σ cu8 / Q4 N K s| ≤ 1
    exact C_bd_frac hQ u0 (by linarith)
  · show |(0 : ℝ)| ≤ 1; simp
  · show |-1 + ((K : ℝ) * E8 s * σ cv8 + exp (s 4 - s 5)) / Q4 N K s| ≤ 1
    exact C_bd_frac' hQ (by linarith) (by linarith)
  · show |-(-1 + ((K : ℝ) * E8 s * σ cv8 + exp (s 4 - s 5)) / Q4 N K s)| ≤ 1
    rw [abs_neg]; exact C_bd_frac' hQ (by linarith) (by linarith)
  · show |-((K : ℝ) * E8 s * σ cv8 / Q4 N K s)| ≤ 1
    rw [abs_neg]; exact C_bd_frac hQ v0 (by linarith)
  · show |(K : ℝ) * E8 s * σ cv8 / Q4 N K s + ed8 s * σ cd8 * (1 / Q4 N K s)| ≤ 1
    rw [show (K : ℝ) * E8 s * σ cv8 / Q4 N K s + ed8 s * σ cd8 * (1 / Q4 N K s) =
      ((K : ℝ) * E8 s * σ cv8 + ed8 s * σ cd8) / Q4 N K s by ring]
    exact C_bd_frac hQ (by linarith) (by linarith)

end bounds

section main2
variable [NeZero N]

set_option linter.unusedVariables false in
/-- Eq. `grad_bound`: on `R'` every partial derivative is at most `2K + 2` in absolute value. -/
theorem g8_bound_on_R (hK : 2 ≤ K) (hN : K + 5 ≤ N) (s : Fin 8 → ℝ) (σ : (Fin 8 → ℝ) → ℝ)
    (hσ : Sel8 s σ) (hb1 : 0 < s 1) (hb2 : s 3 < s 1) (ha2 : 0 < s 2) (hy : 0 < s 4 - s 5)
    (m : Fin 8) : |g8 N K s σ m| ≤ 2 * K + 2 := by
  rw [C_g8_split hσ hb1 hb2 ha2 hy hN]
  simp only [Pi.add_apply, Finset.sum_apply]
  have h2 : |∑ j ∈ range K, C_G2 N K s σ j m| ≤ K := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum (fun j hj => C_G2_bd hσ hN (Finset.mem_range.1 hj).le m)).trans ?_
    simp
  have h3 : |∑ j ∈ range K, C_G3 N K s σ j m| ≤ K := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum (fun j hj => C_G3_bd hσ hN (Finset.mem_range.1 hj) m)).trans ?_
    simp
  have h1 := C_G1_bd hσ hN m
  have h4 := C_G4_bd hσ hN m
  calc _ ≤ |C_G1 N K s σ m + ∑ j ∈ range K, C_G2 N K s σ j m + ∑ j ∈ range K, C_G3 N K s σ j m| +
        |C_G4 N K s σ m| := abs_add_le _ _
    _ ≤ |C_G1 N K s σ m + ∑ j ∈ range K, C_G2 N K s σ j m| + |∑ j ∈ range K, C_G3 N K s σ j m| +
        |C_G4 N K s σ m| := by gcongr; exact abs_add_le _ _
    _ ≤ |C_G1 N K s σ m| + |∑ j ∈ range K, C_G2 N K s σ j m| + |∑ j ∈ range K, C_G3 N K s σ j m| +
        |C_G4 N K s σ m| := by gcongr; exact abs_add_le _ _
    _ ≤ 2 * K + 2 := by linarith



end main2

end DFS
