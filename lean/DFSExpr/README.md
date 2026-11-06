# DFS paper: Lean 4 formalization of Section 3 (Expressivity)

Machine-checked proofs of every theorem, lemma and corollary of Section 3 of the paper and its appendix.
Lean `v4.36.0-rc2`, Mathlib commit `e75a902d` (see `../lakefile.toml`, `../lake-manifest.json`).

**Status: complete.** No `sorry` in any proof file. Every theorem depends only on Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`), checked with `#print axioms`. The one exception is precision
(bit-width) for the two constructions, which is not formalized (see below).

## Build
Build from the parent folder `lean/`, which builds this library, `DFSLean` and `SpecCheck` (see `../README.md`):
```bash
cd lean
lake exe cache get   # prebuilt Mathlib (cache.mathlib.org)
lake build
```
`SpecCheck` (`SpecCheck.lean` in this folder) checks that each proved theorem has exactly the type of its frozen statement in `Spec.lean`,
and prints the axioms of the main results. `Spec.lean` is the only file that contains `sorry`. It is the
specification the proofs were written against, and nothing depends on it.

## Main results (namespace `DFSExpr`)
| Lean | Paper | Statement (informal) |
|---|---|---|
| `one_layer_lower_bound` | Thm `thm:lower_bound` | Correct on all unique-outgoing-child instances with M edges ⇒ `M ≤ 4·H·d·p` |
| `dense_lower_bound` | Cor `cor:dense_graph_lower_bound` (1st part) | `M_N = ⌊(N−1)/3⌋²` edges ⇒ `N² ≤ 144·H·d·p` |
| `dfs_lower_bound` | Cor `cor:dense_graph_lower_bound` (DFS part) | Valid first DFS move on all nonterminated initial states ⇒ `N² ≤ 144·H·d·p` |
| `first_layer` (+ `pos_selector`, `softmax_gap`) | Lemma `lem:first-layer-softmax-copy-relu` | 3 softmax heads, width 4N+3, explicit β = 8L²log(L/δ); copies with factors in [1−2δ,1], exact supports |
| `two_layer_core` | Thm `thm:two_layer_dfs` (second layer) | Any first layer with the copy property and δ ≤ (c₁−c₂)/(4c₁) + the explicit second layer ⇒ every argmax is a valid DFS move |
| `two_layer_dfs` | Thm `thm:two_layer_dfs` | ∃ 2-layer transformer (paper's embedding, first layer of the Lemma, second layer eq. `eq:second_layer_weight_kq_ov`) correct on every graph and every valid DFS trace |
| `lookahead_transformer` (+ `mem_support`) | Lemma `lem:k-layer-lookahead`, Thm `thm:exponential-depth-advantage` | ∀ k ≥ 3, ∃ k-layer transformer, ≤ 4 heads/layer, width 19N+5 (≤ 32N+8), embedding linear in the paper's features, whose argmax is the L-look-ahead DFS move, L = 1 + 2^(k−3) |
| `dm_efficiency` | Lemma `lem:lookahead-efficiency` | Worst-case efficiency of distance-minimizing L-look-ahead DFS is (L+1)/(2n−L−3) for n ≥ L+2 and 1 otherwise, including tight instances |
| `k_layer_efficiency` | Cor `cor:k-layer-efficiency` | The same with L = 1 + 2^(k−3) |
| `dfs_transitions`, `dfs_length` | used in the proofs | Structure of DFS traces (excursions pair up); a valid trace has ≤ 2N−1 nodes |

## Modelling choices
- **Tokens and embeddings** (`Defs.lean`): vocabulary `node v`, `<s>`, `<e>`, `<r>`. The embedding depends on the
  token, its *role* (graph / goal / trace) and its position. The paper's embedding is role-dependent: edge
  endpoints and the target use block 4, root and CoT tokens use block 1. For the lower bound, an arbitrary role- and
  position-dependent embedding only enlarges the class of models.
- **Transformer** (`Layer`, `TF`): the architecture of Sec. 2 with unmasked attention, `X + ReLU(W_O[heads])`,
  element-wise activation φ (softmax = `exp` normalized, linear = `id` unnormalized), and logits `W_Rᵀ x_T` at the
  last position. "Prediction is correct" means *every* maximizer of the logits over the whole vocabulary is
  correct.
- **Precision model of the lower bound** (`OneLayerTF.logitsRd`, `Rounding`): there is one rounding map per site and
  coordinate. Only the attention weights and the summands of attention numerators are required to be p-bit fixed
  point (`|mantissa| ≤ 2^p`, resolution per head/coordinate). Partial sums are exact, and `p ≥ log₂ T`. All
  other roundings (W_K, W_Q, W_V, W_O, head outputs) are arbitrary maps. This contains the paper's model, so the
  lower bounds are at least as strong as stated.
- **DFS** (`DFSNext`, `Run`, `DFSTrace`): a move goes to an unvisited child of the current node, or, if there is
  none, back to the stack parent. Graphs are edge lists, and the constructions assume distinct edges (`es.Nodup`).
  This assumption is necessary for the two-layer theorem: a duplicated edge breaks it.
- **Stronger than the paper:**
  - The upper-bound theorems hold on *every* valid DFS trace from which a move exists. They do not require the
    current node to differ from the target, and they allow traces that pass through the target.
  - The lower bounds assume correctness only on the hard instances: graphs with exactly M (resp. M_N) edges, and
    nonterminated initial states for the DFS version.
  - The constants are explicit.

## Not formalized
- **Bit precision of the constructions.** The two-layer and look-ahead theorems are proved in exact real
  arithmetic. Heads per layer, width and depth are formalized. For the two-layer construction the first-layer
  parameter magnitudes are bounded (`|KQ| ≤ 8L²log(L/δ)+2`, `|V|, |O| ≤ 2`, `L = 3N²+2N+4`, i.e. poly(N)). There is
  no fixed-point execution model, and the look-ahead theorem states no magnitude bound. So the separation "one
  layer needs Ω(N²) bits, two layers suffice with O(N log N)" is formalized as two theorems in different numeric
  models: rounded for the lower bound, exact for the construction.
- The informal remark in App. `app:token_embeddings` that exact visited-set representation needs `mp = Ω(N)`.

## Files
`Defs.lean` definitions · `Spec.lean` frozen statements · `LowerBound.lean` Thm/Cor lower bound ·
`FirstLayer.lean` softmax selector and Lemma first layer · `DFSTrace.lean` DFS trace structure · `TwoLayer.lean`
Thm two-layer · `Efficiency.lean` Lemma/Cor efficiency · `Memory.lean` support invariant · `Lookahead/Part1–5.lean`,
`Lookahead.lean` k-layer construction (coordinates `(Fin 19-block × Fin N) ⊕ 5 scalars`; layer 1 softmax with
3 heads, then linear layers with 4, 2, …, 2, 4 heads; the paper's construction with δ = 1/16) ·
`SpecCheck.lean` statement and axiom check.
