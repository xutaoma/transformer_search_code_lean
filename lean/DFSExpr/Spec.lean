import DFSExpr.Defs

/-!
# Frozen statements (specification)

Every result of the formalization, stated against `DFSExpr.Defs`, with `sorry`.
The proofs live in the other files of `DFSExpr` under the same names without the `Spec.` prefix;
`DFSExpr/SpecCheck.lean` checks that each proved theorem has exactly the type stated here.
Nothing in the library depends on this file.
-/

noncomputable section

open Matrix

namespace DFSExpr.Spec

variable {N : ℕ}

/-! ## A. One-layer lower bound (Thm. `thm:lower_bound`, Cor. `cor:dense_graph_lower_bound`) -/

/-- **Theorem `thm:lower_bound`.** A one-layer transformer (any element-wise attention activation
`φ`, normalized or not, `H` heads, width `d`, value dimension `dv ≤ d`, `p`-bit fixed-point
accumulation of attention sums with `p ≥ log₂ T`, `T = 3M + 2`, arbitrary rounding elsewhere)
that is correct on every valid instance of the unique outgoing-child task with vertex set `[N]` and exactly `M` distinct edges has `M ≤ 4 H d p`.
Correct = every maximizer of the logits is the target of the unique edge out of `q`. -/
theorem one_layer_lower_bound {M d H dk dv p : ℕ} (tf : OneLayerTF N d H dk dv)
    (φ : ℝ → ℝ) (normalized : Bool) (rd : Rounding H dk dv d) (hrd : rd.IsFixed p)
    (hdv : dv ≤ d) (hp : 3 * M + 2 ≤ 2 ^ p)
    (hM : 1 ≤ M) (hN : 3 * ⌈Real.sqrt M⌉₊ + 1 ≤ N)
    (hcorr : ∀ (es : List (Fin N × Fin N)) (q t : Fin N), es.length = M → es.Nodup →
      es.countP (fun e => e.1 = q) = 1 → (q, t) ∈ es →
      ∀ w, IsMax (tf.logitsRd φ normalized rd (childInput es q)) w → w = .node t) :
    M ≤ 4 * H * d * p := by
  sorry

/-- **Corollary `cor:dense_graph_lower_bound`, first part.** With `m_N = ⌊(N-1)/3⌋` and
`M_N = m_N²` edges: `Hdp = Ω(N²)`, explicitly `N² ≤ 144 H d p`. -/
theorem dense_lower_bound {d H dk dv p : ℕ} (tf : OneLayerTF N d H dk dv)
    (φ : ℝ → ℝ) (normalized : Bool) (rd : Rounding H dk dv d) (hrd : rd.IsFixed p)
    (hdv : dv ≤ d) (hN : 4 ≤ N)
    (hp : 3 * ((N - 1) / 3) ^ 2 + 2 ≤ 2 ^ p)
    (hcorr : ∀ (es : List (Fin N × Fin N)) (q t : Fin N), es.length = ((N - 1) / 3) ^ 2 →
      es.Nodup → es.countP (fun e => e.1 = q) = 1 → (q, t) ∈ es →
      ∀ w, IsMax (tf.logitsRd φ normalized rd (childInput es q)) w → w = .node t) :
    N ^ 2 ≤ 144 * H * d * p := by
  sorry

/-- **Corollary `cor:dense_graph_lower_bound`, second part.** A one-layer transformer whose
prediction is a valid first DFS move on every nonterminated initial state
(prompt `<s>, edges, n_Tar, <r>, n_Root`) of every graph on `[N]` with `M_N` distinct edges has
`N² ≤ 144 H d p` (`p ≥ log₂ T`, `T = 3 M_N + 4`). -/
theorem dfs_lower_bound {d H dk dv p : ℕ} (tf : OneLayerTF N d H dk dv)
    (φ : ℝ → ℝ) (normalized : Bool) (rd : Rounding H dk dv d) (hrd : rd.IsFixed p)
    (hdv : dv ≤ d) (hN : 4 ≤ N)
    (hp : 3 * ((N - 1) / 3) ^ 2 + 4 ≤ 2 ^ p)
    (hcorr : ∀ (es : List (Fin N × Fin N)) (root tgt : Fin N),
      es.length = ((N - 1) / 3) ^ 2 → es.Nodup → Nonterm (Adj es) tgt [root] [root] →
      ∀ w, IsMax (tf.logitsRd φ normalized rd (dfsInput es tgt [root])) w →
        ∃ v, w = .node v ∧ DFSNext (Adj es) [root] [root] v) :
    N ^ 2 ≤ 144 * H * d * p := by
  sorry

/-! ## B. Softmax selectors and the first layer (Lemma `lem:first-layer-softmax-copy-relu`) -/

/-- Softmax concentration: if the score at `j0` beats every other score by `g`, the weight on
`j0` is at least `1 - (T-1) e^{-g}`. -/
theorem softmax_gap {T : ℕ} (s : Fin T → ℝ) (j0 : Fin T) (g : ℝ)
    (hg : ∀ j, j ≠ j0 → s j + g ≤ s j0) :
    1 - ((T : ℝ) - 1) * Real.exp (-g) ≤ softmaxW s j0 := by
  sorry

/-- Positional softmax selector (Step 1 of the proof of Lemma `lem:first-layer-softmax-copy-relu`):
with `α = π/(4L)`, `T ≤ L` positions and `β ≥ 8L² log(L/δ)`, the scores `β cos((j - j0 + e)α)`
put weight `≥ 1 - δ` on position `j0`, where `e = 0`, or `e = 1` and `j0 = 0` (position 1 attends
to itself). -/
theorem pos_selector (L T : ℕ) (hT : T ≤ L) (δ β : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hβ : 8 * (L : ℝ) ^ 2 * Real.log (L / δ) ≤ β) (j0 : Fin T) (e : ℕ)
    (he : e = 0 ∨ (e = 1 ∧ (j0 : ℕ) = 0)) :
    1 - δ ≤ softmaxW (fun j : Fin T => β * Real.cos (((j : ℝ) - j0 + e) * posAngle L)) j0 := by
  sorry

/-- **Lemma `lem:first-layer-softmax-copy-relu`** (predecessor-copy layer). For every
`δ ∈ (0, 1/8)` and `L ≥ 1` there is a softmax layer with 3 heads on the `4N + 3` coordinates whose
key-query entries have magnitude `≤ 8 L² log(L/δ) + 2` and value/output entries magnitude `≤ 2`, such that on every input of length `≤ L` of the
shape of App. `app:token_embeddings` (blocks 1, 4 one-hot or zero, blocks 2, 3 zero, `ρ = 1`,
`p_i = (cos iα, sin iα)`, `α = π/(4L)`, position 1 with zero node blocks) it copies block 1 of the
preceding token into block 2 and block 4 into block 3, scaled by factors in `[1 - 2δ, 1]`, with
exact supports. -/
theorem first_layer (N L : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 8) (hL : 1 ≤ L) :
    ∃ L1 : Layer (Coord2 N), L1.H = 3 ∧ L1.act = Act.softmax ∧
      (∀ h r c, |L1.KQ h r c| ≤ 8 * (L : ℝ) ^ 2 * Real.log (L / δ) + 2) ∧
      (∀ h r c, |L1.V h r c| ≤ 2) ∧ (∀ r c, |L1.O r c| ≤ 2) ∧
      ∀ (T : ℕ) (X : Fin T → Coord2 N → ℝ), T ≤ L → (∀ i : Fin T, InputShape N L i (X i)) →
        (∀ i : Fin T, (i : ℕ) = 0 → ∀ v, X i (blk 0 v) = 0 ∧ X i (blk 3 v) = 0) →
        CopyProp δ X (L1.apply X) := by
  sorry

/-! ## C. DFS traces and the two-layer construction (Thm. `thm:two_layer_dfs`) -/

/-- Structure of a valid DFS trace `τ = [n₀, …, n_t]` with stack `x :: rest`: the current node
`x` is the last element of `τ`; there are no self-transitions; the stack below `x` consists of
visited vertices other than `x`; and for `v ≠ x`, among the transitions `(n_{k-1}, n_k)` there is at
most one departure `x → v`, and the arrivals `v → x` are the departures plus one tree-edge arrival
from the stack parent (completed excursions pair up). -/
theorem dfs_transitions {E : Fin N → Fin N → Prop} {s : Fin N} {τ stk : List (Fin N)}
    (h : DFSTrace E s τ stk) :
    ∃ x rest, stk = x :: rest ∧ τ.getLast? = some x ∧ τ.head? = some s ∧
      (∀ v, (v, v) ∉ τ.zip τ.tail) ∧ (∀ y ∈ rest, y ∈ τ ∧ y ≠ x) ∧
      ∀ v, v ≠ x → (τ.zip τ.tail).count (x, v) ≤ 1 ∧
        (τ.zip τ.tail).count (v, x) =
          (τ.zip τ.tail).count (x, v) + (if rest.head? = some v then 1 else 0) := by
  sorry

/-- A valid DFS trace on `N` vertices has at most `2N` entries (`T_cot ≤ poly(N)`). -/
theorem dfs_length {E : Fin N → Fin N → Prop} {s : Fin N} {τ stk : List (Fin N)}
    (h : DFSTrace E s τ stk) : τ.length ≤ 2 * N := by
  sorry

/-- **Second layer of Thm. `thm:two_layer_dfs`.** If the first-layer output `X2` satisfies the
conclusion of Lemma `lem:first-layer-softmax-copy-relu` with `δ ≤ (c₁ - c₂)/(4c₁)`
(eq. `eq:delta_margin`), then on every valid DFS trace (of a graph with distinct edges) from which a
DFS move exists, every maximizer of the logits of the second layer `layer2 c₁ c₂` with readout `W_R`
at the last position is a valid DFS move. -/
theorem two_layer_core (N L : ℕ) (c₁ c₂ δ : ℝ) (hc₂ : 0 < c₂) (hc : c₂ < c₁) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ (c₁ - c₂) / (4 * c₁))
    (es : List (Fin N × Fin N)) (root tgt : Fin N) (τ stk : List (Fin N))
    (hes : es.Nodup) (hτ : DFSTrace (Adj es) root τ stk) (hmv : ∃ v, DFSNext (Adj es) τ stk v)
    (X2 : Fin (dfsInput es tgt τ).length → Coord2 N → ℝ)
    (hX2 : CopyProp δ (embSeq (emb2 N L) (dfsInput es tgt τ)) X2)
    (i : Fin (dfsInput es tgt τ).length) (hi : (i : ℕ) + 1 = (dfsInput es tgt τ).length)
    (w : Tok N) (hw : IsMax (fun w => ∑ c, R2 N c w * (layer2 N c₁ c₂).apply X2 i c) w) :
    ∃ v, w = .node v ∧ DFSNext (Adj es) τ stk v := by
  sorry

/-- **Theorem `thm:two_layer_dfs`.** For all `c₁ > c₂ > 0` there is a two-layer transformer with
the token embedding of App. `app:token_embeddings` (width `4N + 3`), a first layer with 3 softmax
heads and polynomially bounded parameters (Lemma `lem:first-layer-softmax-copy-relu` with
`δ = (c₁ - c₂)/(16 c₁)`), and the second layer `layer2 c₁ c₂` with readout `W_R`, such that for every
graph on `[N]` and every valid DFS trace from which a DFS move exists, every maximizer of the
next-token logits is a valid DFS move. -/
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
  sorry

/-! ## D. Distance-minimizing look-ahead: efficiency (Lemma `lem:lookahead-efficiency`) -/

/-- **Lemma `lem:lookahead-efficiency`.** For `L ≥ 1` and `n ≥ 2`, the worst-case efficiency of the
distance-minimizing `L`-look-ahead policy is `(L+1)/(2n-L-3)` if `n ≥ L + 2` and `1` otherwise. -/
theorem dm_efficiency (L n : ℕ) (hL : 1 ≤ L) (hn : 2 ≤ n) : WorstEff L n (effVal L n) := by
  sorry

/-- **Corollary `cor:k-layer-efficiency`** (`L = 1 + 2^{k-3}`). -/
theorem k_layer_efficiency (k n : ℕ) (hk : 3 ≤ k) (hn : 2 ≤ n) :
    WorstEff (1 + 2 ^ (k - 3)) n
      (if 2 ^ (k - 3) + 3 ≤ n then ((2 : ℝ) ^ (k - 3) + 2) / (2 * (n : ℝ) - 2 ^ (k - 3) - 4)
       else 1) := by
  sorry

/-! ## E. The `k`-layer look-ahead construction (Lemma `lem:k-layer-lookahead`,
Thm. `thm:exponential-depth-advantage`) -/

/-- Support invariant `eq:lookahead-support-invariant`: the memory `mem es j u` is positive exactly
on the vertices within distance `2^j` of `u`. -/
theorem mem_support (es : List (Fin N × Fin N)) (j : ℕ) (u w : Fin N) :
    0 < mem es j u w ↔ ReachLE (Adj es) (2 ^ j) u w := by
  sorry

/-- **Lemma `lem:k-layer-lookahead` / Thm. `thm:exponential-depth-advantage`.** For every `k ≥ 3`
there is a `k`-layer transformer with unmasked softmax or linear attention, at most 4 heads per
layer, width `≤ 32N + 8`, whose token embedding is a linear image of the features `lookFeat`
(node one-hot blocks, constant, period-three indicator, BOS indicator, positional encoding), such
that on every valid DFS trace of a graph with distinct edges from which a DFS move exists, every
maximizer of the next-token logits is the `L`-look-ahead DFS move, `L = 1 + 2^{k-3}`. -/
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
  sorry

end DFSExpr.Spec
