import DFSExpr.Lookahead.Part5

/-!
# Package E: the `k`-layer look-ahead transformer (Lemma `lem:k-layer-lookahead`)

Construction (0-indexed positions, `J = k - 3`), coordinates `E_I N = (E_Bk × Fin N) ⊕ Fin 5`
(19 node blocks and 5 scalars, width `19 N + 5`):
* layer 1 (`E_L1`, softmax, 3 heads): predecessor / self / goal selectors, exact pair decoding;
* layer 2 (`E_L2`, linear, 4 heads): one-step memories and the DFS forward/backtrack scores;
* layers `3 … k-1` (`E_Lp`, linear, 2 heads): doubling of the memories;
* layer `k` (`E_Lk`, linear, 4 heads): eligibility `E_v = [v unvisited child ∧ F_v > 0]`;
* readout `4 E_v + Df_v + Db_v + (N-1-v)/(4N)`, specials `-1`.
Parts 1–5 contain the analysis; this file assembles the theorem.
-/

noncomputable section

open Matrix

namespace DFSExpr

variable {N : ℕ}

open Classical

/-! ### A uniform bound on the memories -/

/-- `P_0 = 1 + N²`, `P_{j+1} = P_j + N² P_j²`. -/
def E_P (N : ℕ) : ℕ → ℕ
  | 0 => 1 + N ^ 2
  | j + 1 => E_P N j + N ^ 2 * E_P N j ^ 2

theorem E_mem_le (es : List (Fin N × Fin N)) (hlen : es.length ≤ N ^ 2) :
    ∀ j u w, mem es j u w ≤ E_P N j
  | 0, u, w => by
    simp only [mem, E_P]
    have := List.countP_le_length (p := fun f : Fin N × Fin N => decide (f.1 = u ∧ f.2 = w))
      (l := es)
    split_ifs <;> omega
  | j + 1, u, w => by
    simp only [mem, E_P]
    have h1 := E_mem_le es hlen j u w
    have h2 : (es.map fun f => mem es j u f.1 * mem es j f.1 w).sum ≤
        es.length * (E_P N j * E_P N j) := by
      have := List.sum_le_length_nsmul (es.map fun f => mem es j u f.1 * mem es j f.1 w)
        (E_P N j * E_P N j) (by
          intro y hy
          obtain ⟨f, _, rfl⟩ := List.mem_map.1 hy
          exact Nat.mul_le_mul (E_mem_le es hlen j _ _) (E_mem_le es hlen j _ _))
      simpa using this
    have h3 : es.length * (E_P N j * E_P N j) ≤ N ^ 2 * E_P N j ^ 2 := by
      rw [sq (E_P N j)]; exact Nat.mul_le_mul_right _ hlen
    omega

/-- The constant `B = N² P_J`. -/
def E_B (N J : ℕ) : ℝ := ((N ^ 2 * E_P N J : ℕ) : ℝ)

/-! ### Eligibility -/

theorem E_Eval (es : List (Fin N × Fin N)) (hes : es.Nodup) (hM : es.length ≤ N ^ 2) (J : ℕ)
    (tgt x v : Fin N) (τ : List (Fin N)) :
    max ((es.map fun e => (mem es J e.2 tgt : ℝ) * (if e.2 = v then 1 else 0)).sum +
          E_B N J * (es.count (x, v) : ℝ) - 2 * E_B N J * (τ.count v : ℝ) - E_B N J) 0 -
      max ((es.map fun e => (mem es J e.2 tgt : ℝ) * (if e.2 = v then 1 else 0)).sum +
          E_B N J * (es.count (x, v) : ℝ) - 2 * E_B N J * (τ.count v : ℝ) - E_B N J - 1) 0 =
      if (x, v) ∈ es ∧ v ∉ τ ∧ ReachLE (Adj es) (2 ^ J) v tgt then 1 else 0 := by
  set Fv := (es.map fun e => (mem es J e.2 tgt : ℝ) * (if e.2 = v then 1 else 0)).sum with hFv
  set B := E_B N J
  have hB0 : 0 ≤ B := by simp only [B, E_B]; positivity
  have hF0 : 0 ≤ Fv := List.sum_nonneg fun a ha => by
    obtain ⟨e, _, rfl⟩ := List.mem_map.1 ha
    split_ifs <;> positivity
  have hFB : Fv ≤ B := by
    have h := List.sum_le_length_nsmul
      (es.map fun e => (mem es J e.2 tgt : ℝ) * (if e.2 = v then 1 else 0)) (E_P N J : ℝ) (by
        intro a ha
        obtain ⟨e, _, rfl⟩ := List.mem_map.1 ha
        have : (mem es J e.2 tgt : ℝ) ≤ E_P N J := by exact_mod_cast E_mem_le es hM J _ _
        split_ifs
        · rw [mul_one]; exact this
        · rw [mul_zero]; positivity)
    simp only [List.length_map, nsmul_eq_mul] at h
    have hM' : (es.length : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hM
    have : (es.length : ℝ) * (E_P N J : ℝ) ≤ (N : ℝ) ^ 2 * (E_P N J : ℝ) :=
      mul_le_mul_of_nonneg_right hM' (by positivity)
    simp only [B, E_B]
    push_cast
    linarith
  have hFeq : Fv = (mem es J v tgt : ℝ) * (es.map fun e => if e.2 = v then (1 : ℝ) else 0).sum := by
    rw [hFv, ← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun e _ => ?_
    split_ifs with h
    · rw [h]
    · simp
  have hc1 : es.count (x, v) ≤ 1 := List.nodup_iff_count_le_one.1 hes _
  have hdec : ∀ z : ℝ, z ≤ 0 → max z 0 - max (z - 1) 0 = 0 := fun z hz => by
    rw [max_eq_right hz, max_eq_right (by linarith)]; ring
  have hm0 : (0 : ℝ) ≤ τ.count v := by positivity
  by_cases hxv : (x, v) ∈ es
  · have hc : es.count (x, v) = 1 := le_antisymm hc1 (List.count_pos_iff.2 hxv)
    by_cases hvt : v ∈ τ
    · have : 1 ≤ τ.count v := List.count_pos_iff.2 hvt
      have h' : (1 : ℝ) ≤ τ.count v := by exact_mod_cast this
      rw [if_neg (by tauto), hc, hdec]
      push_cast
      nlinarith
    · have hct : τ.count v = 0 := List.count_eq_zero.2 hvt
      rw [hc, hct]
      simp only [Nat.cast_one, mul_one, Nat.cast_zero, mul_zero, sub_zero, add_sub_cancel_right]
      by_cases hR : ReachLE (Adj es) (2 ^ J) v tgt
      · rw [if_pos (show (x, v) ∈ es ∧ v ∉ τ ∧ ReachLE (Adj es) (2 ^ J) v tgt from
          ⟨hxv, hvt, hR⟩)]
        have hmem : (1 : ℝ) ≤ mem es J v tgt := by
          exact_mod_cast (mem_support es J v tgt).2 hR
        have hcnt : (1 : ℝ) ≤ (es.map fun e => if e.2 = v then (1 : ℝ) else 0).sum := by
          rw [← E_countP_cast (fun e : Fin N × Fin N => e.2 = v)]
          have : 0 < es.countP (fun e => decide (e.2 = v)) :=
            List.countP_pos_iff.2 ⟨(x, v), hxv, by simp⟩
          exact_mod_cast this
        have : 1 ≤ Fv := by rw [hFeq]; nlinarith
        rw [max_eq_left (by linarith), max_eq_left (by linarith)]
        ring
      · rw [if_neg (by tauto)]
        have hmem : mem es J v tgt = 0 := by
          by_contra h
          exact hR ((mem_support es J v tgt).1 (Nat.pos_of_ne_zero h))
        have : Fv = 0 := by rw [hFeq, hmem]; simp
        rw [this]; norm_num
  · have hc : es.count (x, v) = 0 := List.count_eq_zero.2 hxv
    rw [if_neg (by tauto), hc, hdec]
    push_cast
    nlinarith

/-! ### Tie-breaking -/

/-- Tie-breaking term `(N - 1 - v)/(4N)`. -/
def E_tb (v : Fin N) : ℝ := ((N : ℝ) - 1 - v) / (4 * N)

theorem E_tb_bounds (v : Fin N) : 0 ≤ E_tb v ∧ E_tb v < 1 / 4 := by
  have hv : (v : ℝ) + 1 ≤ N := by exact_mod_cast v.2
  have hN : (0 : ℝ) < N := by linarith [(Nat.cast_nonneg v.1 : (0 : ℝ) ≤ v)]
  have hv0 : (0 : ℝ) ≤ v := Nat.cast_nonneg _
  refine ⟨div_nonneg (by linarith) (by positivity), ?_⟩
  rw [E_tb, div_lt_iff₀ (by positivity)]
  linarith

theorem E_tb_anti (v w : Fin N) (h : v < w) : E_tb w < E_tb v := by
  have hv : (w : ℝ) + 1 ≤ N := by exact_mod_cast w.2
  have hvw : (v : ℝ) < w := by exact_mod_cast h
  have hN : (0 : ℝ) < N := by linarith [(Nat.cast_nonneg v.1 : (0 : ℝ) ≤ v)]
  unfold E_tb
  apply div_lt_div_of_pos_right _ (by positivity)
  linarith

/-! ### Bands of the logits -/

theorem E_band (es : List (Fin N × Fin N)) (τ rest : List (Fin N)) (x : Fin N)
    (R : Fin N → Prop) (ℓ : Tok N → ℝ)
    (hnode : ∀ v, ℓ (.node v) =
      4 * (if (x, v) ∈ es ∧ v ∉ τ ∧ R v then 1 else 0) +
        (if (x, v) ∈ es ∧ v ∉ τ then 2 else 0) + (if rest.head? = some v then 1 else 0) + E_tb v)
    (hspec : ∀ t : Tok N, (∀ v, t ≠ .node v) → ℓ t = -1)
    (hpar : ∀ v, rest.head? = some v → v ∈ τ)
    (hmv : ∃ v, DFSNext (Adj es) τ (x :: rest) v) (w : Tok N) (hw : IsMax ℓ w) :
    ∃ v, w = .node v ∧
      (((Adj es x v ∧ v ∉ τ ∧ R v) ∧ ∀ w, Adj es x w ∧ w ∉ τ ∧ R w → v ≤ w) ∨
      ((¬ ∃ w, Adj es x w ∧ w ∉ τ ∧ R w) ∧ (Adj es x v ∧ v ∉ τ) ∧
          ∀ w, Adj es x w ∧ w ∉ τ → v ≤ w) ∨
      ((∀ w, Adj es x w → w ∈ τ) ∧ rest.head? = some v)) := by
  -- logits of eligible / unvisited / other vertices
  have hel : ∀ v, (x, v) ∈ es ∧ v ∉ τ ∧ R v → ℓ (.node v) = 6 + E_tb v := by
    intro v hv
    have hp : ¬ rest.head? = some v := fun h => hv.2.1 (hpar v h)
    rw [hnode, if_pos hv, if_pos (show (x, v) ∈ es ∧ v ∉ τ from ⟨hv.1, hv.2.1⟩), if_neg hp]; ring
  have hun : ∀ v, (x, v) ∈ es ∧ v ∉ τ → ¬ R v → ℓ (.node v) = 2 + E_tb v := by
    intro v hv hR
    have hp : ¬ rest.head? = some v := fun h => hv.2 (hpar v h)
    rw [hnode, if_neg (show ¬((x, v) ∈ es ∧ v ∉ τ ∧ R v) from fun h => hR h.2.2), if_pos hv,
      if_neg hp]; ring
  have hot : ∀ v, ¬ ((x, v) ∈ es ∧ v ∉ τ) →
      ℓ (.node v) = (if rest.head? = some v then 1 else 0) + E_tb v := by
    intro v hv
    rw [hnode, if_neg (show ¬((x, v) ∈ es ∧ v ∉ τ ∧ R v) from fun h => hv ⟨h.1, h.2.1⟩),
      if_neg hv]; ring
  have hle : ∀ v, ¬ ((x, v) ∈ es ∧ v ∉ τ ∧ R v) → ℓ (.node v) < 13 / 4 := by
    intro v hv
    rw [hnode, if_neg hv]
    have := (E_tb_bounds v).2
    split_ifs <;> linarith
  have hnn : 0 ≤ ℓ (.node x) := by
    rw [hnode]
    have := (E_tb_bounds x).1
    split_ifs <;> linarith
  -- the maximizer is a vertex
  rcases w with u | _ | _ | _
  rotate_left
  · have := hw (.node x); rw [hspec .bos (fun v h => by cases h)] at this; linarith
  · have := hw (.node x); rw [hspec .sep (fun v h => by cases h)] at this; linarith
  · have := hw (.node x); rw [hspec .rsn (fun v h => by cases h)] at this; linarith
  refine ⟨u, rfl, ?_⟩
  by_cases hE : ∃ v, Adj es x v ∧ v ∉ τ ∧ R v
  · left
    obtain ⟨v0, hv0⟩ := hE
    have h0 := hw (.node v0)
    rw [hel v0 hv0] at h0
    have hu : (x, u) ∈ es ∧ u ∉ τ ∧ R u := by
      by_contra h
      have := hle u h
      have := (E_tb_bounds v0).1
      linarith
    refine ⟨hu, fun w' hw' => ?_⟩
    by_contra hlt
    push_neg at hlt
    have h1 := hw (.node w')
    rw [hel w' hw', hel u hu] at h1
    have := E_tb_anti w' u hlt
    linarith
  · by_cases hU : ∃ v, Adj es x v ∧ v ∉ τ
    · right; left
      obtain ⟨v0, hv0⟩ := hU
      have h0 := hw (.node v0)
      rw [hun v0 hv0 (fun hR => hE ⟨v0, hv0.1, hv0.2, hR⟩)] at h0
      have hu : (x, u) ∈ es ∧ u ∉ τ := by
        by_contra h
        rw [hot u h] at h0
        have := (E_tb_bounds u).2
        have := (E_tb_bounds v0).1
        split_ifs at h0 <;> linarith
      refine ⟨hE, hu, fun w' hw' => ?_⟩
      by_contra hlt
      push_neg at hlt
      have h1 := hw (.node w')
      rw [hun w' hw' (fun hR => hE ⟨w', hw'.1, hw'.2, hR⟩),
        hun u hu (fun hR => hE ⟨u, hu.1, hu.2, hR⟩)] at h1
      have := E_tb_anti w' u hlt
      linarith
    · right; right
      have hall : ∀ w, Adj es x w → w ∈ τ := fun w hw' => by
        by_contra h; exact hU ⟨w, hw', h⟩
      obtain ⟨v0, hv0⟩ := hmv
      rcases hv0 with hv0 | hv0
      · exact absurd ⟨v0, hv0⟩ hU
      refine ⟨hall, ?_⟩
      have h0 := hw (.node v0)
      have hnu : ∀ v, ¬ ((x, v) ∈ es ∧ v ∉ τ) := fun v h => hU ⟨v, h⟩
      rw [hot v0 (hnu v0), if_pos hv0.2, hot u (hnu u)] at h0
      by_contra hp
      rw [if_neg hp] at h0
      have := (E_tb_bounds u).2
      have := (E_tb_bounds v0).1
      linarith

/-! ### The transformer -/

/-- Positional-encoding length `L = 3N² + 2N + 4` (bounds every valid input length). -/
def E_Lpos (N : ℕ) : ℕ := 3 * N ^ 2 + 2 * N + 4

/-- Readout rows. -/
def E_Rrow : Tok N → E_I N → ℝ
  | .node v => (4 : ℝ) • E_e (.inl (.ZP, v)) - (4 : ℝ) • E_e (.inl (.ZM, v)) +
      E_e (.inl (.Df, v)) + E_e (.inl (.Db, v)) + E_tb v • E_e E_ρ
  | _ => -E_e E_ρ

def E_R : Matrix (E_I N) (Tok N) ℝ := fun c w => E_Rrow w c

/-- The `k`-layer look-ahead transformer. -/
def E_tf (k N : ℕ) : TF N (E_I N) where
  emb := E_emb (E_Lpos N)
  layers := [E_L1 (E_Lpos N), E_L2] ++ List.replicate (k - 3) E_Lp ++ [E_Lk (E_B N (k - 3))]
  R := E_R

theorem E_correct (k : ℕ) (es : List (Fin N × Fin N)) (root tgt : Fin N)
    (τ stk : List (Fin N)) (hes : es.Nodup) (hτ : DFSTrace (Adj es) root τ stk)
    (hmv : ∃ v, DFSNext (Adj es) τ stk v) (w : Tok N)
    (hw : IsMax ((E_tf k N).logits (dfsInput es tgt τ)) w) :
    ∃ v, w = .node v ∧ LookMove (1 + 2 ^ (k - 3)) (Adj es) tgt τ stk v := by
  obtain ⟨x, rest, rfl, hx, -, -, hrest, htr⟩ := dfs_transitions hτ
  have hM : es.length ≤ N ^ 2 := by
    have := hes.length_le_card
    simpa [Fintype.card_prod, sq] using this
  have ht := dfs_length hτ
  have hT : (dfsInput es tgt τ).length ≤ E_Lpos N := by
    rw [E_lay_len, E_Lpos]; nlinarith
  have hL : 1 ≤ E_Lpos N := by unfold E_Lpos; omega
  have hxr : rest.head? ≠ some x := fun h => (hrest x (List.mem_of_mem_head? h)).2 rfl
  have h1 := E_L1_inv (E_Lpos N) hL es tgt τ hT
  have h2 := E_L2_inv h1 hes x hx rest (fun v hv => (htr v hv).2) hxr
  have hJ := E_fold_inv (k - 3) 0 _ h2
  rw [zero_add] at hJ
  set XJ := (List.replicate (k - 3) E_Lp).foldl (fun X l => l.apply X)
    (E_L2.apply ((E_L1 (E_Lpos N)).apply (embSeq (E_emb (E_Lpos N)) (dfsInput es tgt τ))))
    with hXJ
  set Xk := (E_Lk (E_B N (k - 3))).apply XJ with hXk
  have hrun : (E_tf k N).run (dfsInput es tgt τ) = Xk := by
    simp only [TF.run, E_tf, List.foldl_append, List.foldl_cons, List.foldl_nil, hXk, hXJ]
  have hlog : ∀ w', (E_tf k N).logits (dfsInput es tgt τ) w' =
      E_Rrow w' ⬝ᵥ Xk (E_last es tgt τ) := by
    intro w'
    unfold TF.logits
    rw [dif_neg (by rw [E_lay_len]; omega), hrun]
    rfl
  have hρ : Xk (E_last es tgt τ) E_ρ = 1 := by
    rw [hXk, E_Lk_frameS]; exact (hJ.1 _ x).2.2.2.2.2.1
  have hDf : ∀ v, Xk (E_last es tgt τ) (.inl (.Df, v)) =
      if (x, v) ∈ es ∧ v ∉ τ then 2 else 0 := fun v => by
    rw [hXk, E_Lk_frame _ _ _ .Df (by decide)]; exact (hJ.2.2 v).1
  have hDb : ∀ v, Xk (E_last es tgt τ) (.inl (.Db, v)) =
      if rest.head? = some v then 1 else 0 := fun v => by
    rw [hXk, E_Lk_frame _ _ _ .Db (by decide)]; exact (hJ.2.2 v).2
  have hZ : ∀ v, Xk (E_last es tgt τ) (.inl (.ZP, v)) - Xk (E_last es tgt τ) (.inl (.ZM, v)) =
      if (x, v) ∈ es ∧ v ∉ τ ∧ ReachLE (Adj es) (2 ^ (k - 3)) v tgt then 1 else 0 := fun v => by
    rw [hXk, E_Lk_Z hJ x hx _ v, E_Eval es hes hM (k - 3) tgt x v τ]
  have hnode : ∀ v, (E_tf k N).logits (dfsInput es tgt τ) (.node v) =
      4 * (if (x, v) ∈ es ∧ v ∉ τ ∧ ReachLE (Adj es) (1 + 2 ^ (k - 3) - 1) v tgt then 1 else 0) +
        (if (x, v) ∈ es ∧ v ∉ τ then 2 else 0) + (if rest.head? = some v then 1 else 0) +
        E_tb v := by
    intro v
    rw [hlog, Nat.add_sub_cancel_left, ← hZ, ← hDf, ← hDb]
    simp only [E_Rrow, add_dotProduct, sub_dotProduct, smul_dotProduct, E_e_dot, smul_eq_mul, hρ]
    ring
  have hspec : ∀ t : Tok N, (∀ v, t ≠ .node v) →
      (E_tf k N).logits (dfsInput es tgt τ) t = -1 := by
    intro t ht
    rw [hlog]
    cases t with
    | node v => exact absurd rfl (ht v)
    | _ => simp [E_Rrow, neg_dotProduct, hρ]
  exact E_band es τ rest x _ _ hnode hspec (fun v h => (hrest v (List.mem_of_mem_head? h)).1)
    hmv w hw

/-- **Lemma `lem:k-layer-lookahead` / Thm. `thm:exponential-depth-advantage`.** -/
theorem lookahead_transformer (k N : ℕ) (hk : 3 ≤ k) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (tf : TF N ι) (L : ℕ)
      (Φ : (FeatIx N → ℝ) →ₗ[ℝ] (ι → ℝ)),
      Fintype.card ι ≤ 32 * N + 8 ∧ tf.layers.length = k ∧
      (∀ l ∈ tf.layers, l.H ≤ 4 ∧ (l.act = Act.softmax ∨ l.act = Act.linear)) ∧
      (∀ t r j, tf.emb t r j = Φ (lookFeat N L t r j)) ∧
      ∀ (es : List (Fin N × Fin N)) (root tgt : Fin N) (τ stk : List (Fin N)),
        es.Nodup → DFSTrace (Adj es) root τ stk → (∃ v, DFSNext (Adj es) τ stk v) →
        ∀ w, IsMax (tf.logits (dfsInput es tgt τ)) w →
          ∃ v, w = .node v ∧ LookMove (1 + 2 ^ (k - 3)) (Adj es) tgt τ stk v := by
  refine ⟨E_I N, inferInstance, inferInstance, E_tf k N, E_Lpos N, E_Phi, ?_, ?_, ?_,
    fun t r j => rfl, fun es root tgt τ stk hes hτ hmv w hw =>
      E_correct k es root tgt τ stk hes hτ hmv w hw⟩
  · rw [E_card]; omega
  · simp [E_tf]; omega
  · intro l hl
    have hl' : l = E_L1 (E_Lpos N) ∨ l = E_L2 ∨ l = E_Lp ∨ l = E_Lk (E_B N (k - 3)) := by
      simp only [E_tf, List.mem_append, List.mem_cons, List.mem_replicate, List.not_mem_nil,
        or_false] at hl
      tauto
    rcases hl' with rfl | rfl | rfl | rfl
    · exact ⟨show 3 ≤ 4 by omega, Or.inl rfl⟩
    · exact ⟨le_refl _, Or.inr rfl⟩
    · exact ⟨show 2 ≤ 4 by omega, Or.inr rfl⟩
    · exact ⟨le_refl _, Or.inr rfl⟩


end DFSExpr

