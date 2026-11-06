import Mathlib

/-!
# DFS paper, Section 3 (Expressivity): definitions

Everything the frozen statements in `DFSExpr/Spec.lean` refer to.
Paper sources: `content/expressivity.tex`, `content/setting.tex`,
`content/appendix/proof_expressivity.tex`.

Conventions
* Vertices are `Fin N` (the paper's `[N]`, shifted to `0, …, N-1`).
* Positions are 0-indexed: the token at Lean position `j` is the paper's position `j + 1`.
* Hidden states are row-indexed: a sequence of length `T` is `Fin T → ι → ℝ`, where `ι` is a
  finite type of coordinates (the paper's `ℝ^d` with `d = Fintype.card ι`).
-/

noncomputable section

open Matrix

namespace DFSExpr

/-! ## Tokens, roles, prompts -/

/-- Token vocabulary `𝒜`: the `N` vertex tokens and the special tokens `<s>`, `<e>`, `<r>`. -/
inductive Tok (N : ℕ) where
  | node (v : Fin N)
  | bos
  | sep
  | rsn
  deriving DecidableEq, Fintype

/-- The role of a token in the input, which the token embedding may depend on
(App. `app:token_embeddings`: edge endpoints and the task target put their one-hot vector in one
block, root and CoT tokens in another). `graph`: `<s>` and the edge list; `goal`: the target
`n_Tar` and `<r>`; `trace`: the root and the CoT tokens. -/
inductive Role where
  | graph
  | goal
  | trace
  deriving DecidableEq

variable {N : ℕ}

/-- Edge segment `s₁, t₁, <e>, …, s_M, t_M, <e>` of a prompt. -/
def edgeToks (es : List (Fin N × Fin N)) : List (Tok N × Role) :=
  es.flatMap fun e => [(.node e.1, .graph), (.node e.2, .graph), (.sep, .graph)]

/-- Prompt of the unique outgoing-child task: `<s>, s₁, t₁, <e>, …, s_M, t_M, <e>, q`. -/
def childInput (es : List (Fin N × Fin N)) (q : Fin N) : List (Tok N × Role) :=
  (.bos, .graph) :: edgeToks es ++ [(.node q, .trace)]

/-- Input of the DFS next-step task: the prompt `<s>, edges, n_Tar, <r>, n_Root` followed by the
CoT tokens. `τ = [n₀, n₁, …, n_t]` is the trace including the root `n₀ = n_Root`. -/
def dfsInput (es : List (Fin N × Fin N)) (tgt : Fin N) (τ : List (Fin N)) :
    List (Tok N × Role) :=
  (.bos, .graph) :: edgeToks es ++ [(.node tgt, .goal), (.rsn, .goal)] ++
    τ.map fun v => (.node v, .trace)

/-- `w` maximizes the logit vector `ℓ` (over the whole vocabulary). -/
def IsMax (ℓ : Tok N → ℝ) (w : Tok N) : Prop := ∀ w', ℓ w' ≤ ℓ w

/-! ## Graphs and depth-first search -/

/-- Edge relation of an edge list. -/
def Adj (es : List (Fin N × Fin N)) (u v : Fin N) : Prop := (u, v) ∈ es

/-- `ReachLE E r v w`: there is a path from `v` to `w` with at most `r` edges
(`dist_G(v, w) ≤ r`; zero-length paths allowed). -/
def ReachLE (E : Fin N → Fin N → Prop) : ℕ → Fin N → Fin N → Prop
  | 0, v, w => v = w
  | r + 1, v, w => ReachLE E r v w ∨ ∃ u, E v u ∧ ReachLE E r u w

/-- `IsDist E v w d`: `dist_G(v, w) = d`. -/
def IsDist (E : Fin N → Fin N → Prop) (v w : Fin N) (d : ℕ) : Prop :=
  ReachLE E d v w ∧ ∀ r < d, ¬ ReachLE E r v w

/-- Valid DFS moves (Sec. 2) at a state with trace `τ` (visited set = elements of `τ`) and DFS
stack `stk` (head = current node): an unvisited child of the current node, or, if there is none,
the parent of the current node in the stack. -/
def DFSNext (E : Fin N → Fin N → Prop) (τ : List (Fin N)) : List (Fin N) → Fin N → Prop
  | [], _ => False
  | x :: rest, v => (E x v ∧ v ∉ τ) ∨ ((∀ w, E x w → w ∈ τ) ∧ rest.head? = some v)

/-- Runs of a search policy `P` (a relation "from trace `τ` and stack `stk` the policy may move to
`v`") from the root `s`. `Run E P s n τ stk`: after `n` moves the trace is `τ` (root first) and the
stack is `stk` (current node first). A move to an unvisited child pushes it, any other move pops
the current node. -/
inductive Run (E : Fin N → Fin N → Prop) (P : List (Fin N) → List (Fin N) → Fin N → Prop)
    (s : Fin N) : ℕ → List (Fin N) → List (Fin N) → Prop
  | zero : Run E P s 0 [s] [s]
  | fwd {n : ℕ} {τ rest : List (Fin N)} {x v : Fin N} :
      Run E P s n τ (x :: rest) → P τ (x :: rest) v → E x v → v ∉ τ →
      Run E P s (n + 1) (τ ++ [v]) (v :: x :: rest)
  | back {n : ℕ} {τ rest : List (Fin N)} {x v : Fin N} :
      Run E P s n τ (x :: rest) → P τ (x :: rest) v → ¬ (E x v ∧ v ∉ τ) →
      Run E P s (n + 1) (τ ++ [v]) rest

/-- A valid DFS trace from the root `s`, with its DFS stack. -/
def DFSTrace (E : Fin N → Fin N → Prop) (s : Fin N) (τ stk : List (Fin N)) : Prop :=
  ∃ n, Run E (DFSNext E) s n τ stk

/-- A state is nonterminated (Sec. 3): the current node is not the target and DFS has a valid
next move. -/
def Nonterm (E : Fin N → Fin N → Prop) (tgt : Fin N) (τ stk : List (Fin N)) : Prop :=
  τ.getLast? ≠ some tgt ∧ ∃ v, DFSNext E τ stk v

/-- `L`-look-ahead DFS (Def. `def:L-lookahead-dfs`), children ordered by increasing label:
move to the first unvisited child `v` with `dist(v, g) ≤ L - 1` if there is one; otherwise to the
first unvisited child; otherwise back to the stack parent. -/
def LookMove (L : ℕ) (E : Fin N → Fin N → Prop) (g : Fin N) (τ : List (Fin N)) :
    List (Fin N) → Fin N → Prop
  | [], _ => False
  | x :: rest, v =>
    ((E x v ∧ v ∉ τ ∧ ReachLE E (L - 1) v g) ∧
        ∀ w, E x w ∧ w ∉ τ ∧ ReachLE E (L - 1) w g → v ≤ w) ∨
    ((¬ ∃ w, E x w ∧ w ∉ τ ∧ ReachLE E (L - 1) w g) ∧ (E x v ∧ v ∉ τ) ∧
        ∀ w, E x w ∧ w ∉ τ → v ≤ w) ∨
    ((∀ w, E x w → w ∈ τ) ∧ rest.head? = some v)

/-- `ReachAvoid E τ r v w`: a path from `v` to `w` with at most `r` edges all of whose vertices
lie outside the visited set `τ` (so `d_S(v, w) ≤ r`, `S = τ`). -/
def ReachAvoid (E : Fin N → Fin N → Prop) (τ : List (Fin N)) : ℕ → Fin N → Fin N → Prop
  | 0, v, w => v = w ∧ v ∉ τ
  | r + 1, v, w => ReachAvoid E τ r v w ∨ (v ∉ τ ∧ ∃ u, E v u ∧ ReachAvoid E τ r u w)

/-- Distance-minimizing `L`-look-ahead DFS (Def. `def:distance-minimizing-lookahead`): if some
unvisited child `v` has `d_S(v, g) ≤ L - 1`, move to one minimizing `d_S(v, g)`, ties broken by
increasing label; otherwise the ordinary DFS rule (first unvisited child, else backtrack). -/
def DMMove (L : ℕ) (E : Fin N → Fin N → Prop) (g : Fin N) (τ : List (Fin N)) :
    List (Fin N) → Fin N → Prop
  | [], _ => False
  | x :: rest, v =>
    ((E x v ∧ v ∉ τ ∧ ReachAvoid E τ (L - 1) v g) ∧
        ∀ w, E x w ∧ w ∉ τ ∧ ReachAvoid E τ (L - 1) w g →
          (∀ r, ReachAvoid E τ r w g → ReachAvoid E τ r v g) ∧
          ((∀ r, ReachAvoid E τ r v g → ReachAvoid E τ r w g) → v ≤ w)) ∨
    ((¬ ∃ w, E x w ∧ w ∉ τ ∧ ReachAvoid E τ (L - 1) w g) ∧ (E x v ∧ v ∉ τ) ∧
        ∀ w, E x w ∧ w ∉ τ → v ≤ w) ∨
    ((∀ w, E x w → w ∈ τ) ∧ rest.head? = some v)

/-- `MovesTo E P s g m`: following `P` from `s`, the current node is `g` after `m` moves and at no
earlier time ("number of CoT moves before reaching `g`"). -/
def MovesTo (E : Fin N → Fin N → Prop) (P : List (Fin N) → List (Fin N) → Fin N → Prop)
    (s g : Fin N) (m : ℕ) : Prop :=
  (∃ τ stk, Run E P s m τ stk ∧ τ.getLast? = some g) ∧
  ∀ m' < m, ∀ τ stk, Run E P s m' τ stk → τ.getLast? ≠ some g

/-- The worst-case efficiency `min dist(n_s, g) / #moves` of the distance-minimizing
`L`-look-ahead policy, over all instances with exactly `n` vertices reachable from `n_s` and a
reachable target `g ≠ n_s`, equals `e`: every instance is reached, with ratio `≥ e`, and some
instance attains `e`. -/
def WorstEff (L n : ℕ) (e : ℝ) : Prop :=
  (∀ (M : ℕ) (E : Fin M → Fin M → Prop) (s g : Fin M) (d : ℕ),
      {v | Relation.ReflTransGen E s v}.ncard = n → g ≠ s → Relation.ReflTransGen E s g →
      IsDist E s g d →
      (∃ m, MovesTo E (DMMove L E g) s g m) ∧
      ∀ m, MovesTo E (DMMove L E g) s g m → e ≤ (d : ℝ) / m) ∧
  (∃ (M : ℕ) (E : Fin M → Fin M → Prop) (s g : Fin M) (d m : ℕ),
      {v | Relation.ReflTransGen E s v}.ncard = n ∧ g ≠ s ∧ Relation.ReflTransGen E s g ∧
      IsDist E s g d ∧ MovesTo E (DMMove L E g) s g m ∧ (d : ℝ) / m = e)

/-- The value in Lemma `lem:lookahead-efficiency`. -/
def effVal (L n : ℕ) : ℝ :=
  if L + 2 ≤ n then ((L : ℝ) + 1) / (2 * (n : ℝ) - L - 3) else 1

/-! ## Transformers (exact real arithmetic), Sec. 2 -/

/-- Element-wise attention activation `φ`, optionally normalized over the keys. -/
structure Act where
  φ : ℝ → ℝ
  normalized : Bool

/-- Column-wise softmax attention. -/
def Act.softmax : Act := ⟨Real.exp, true⟩

/-- Linear (unnormalized, `φ(x) = x`) attention. -/
def Act.linear : Act := ⟨id, false⟩

/-- One attention layer with `H` heads on hidden coordinates `ι`. `KQ h = W_Kᵀ W_Q` is the
aggregated key-query matrix (score of key `x_j` for query `x_i` is `x_jᵀ KQ x_i`), `V h` the value
matrix (value dimension ≤ width; values are zero-padded to `ι`), `O` the output projection. -/
structure Layer (ι : Type) where
  H : ℕ
  act : Act
  KQ : Fin H → Matrix ι ι ℝ
  V : Fin H → Matrix ι ι ℝ
  O : Matrix ι (Fin H × ι) ℝ

variable {ι : Type} [Fintype ι]

/-- Attention weight of key position `j` for query position `i` (unmasked attention). -/
def attnW (a : Act) (A : Matrix ι ι ℝ) {T : ℕ} (X : Fin T → ι → ℝ) (i j : Fin T) : ℝ :=
  if a.normalized then a.φ (X j ⬝ᵥ (A *ᵥ X i)) / ∑ k, a.φ (X k ⬝ᵥ (A *ᵥ X i))
  else a.φ (X j ⬝ᵥ (A *ᵥ X i))

/-- Output of one head at query position `i`: `Σ_j w_{ij} V x_j`. -/
def headOut (a : Act) (A V : Matrix ι ι ℝ) {T : ℕ} (X : Fin T → ι → ℝ) (i : Fin T) : ι → ℝ :=
  ∑ j, attnW a A X i j • (V *ᵥ X j)

/-- `X ↦ X + ReLU(W_O [Head₁(X); …; Head_H(X)])`. -/
def Layer.apply (l : Layer ι) {T : ℕ} (X : Fin T → ι → ℝ) : Fin T → ι → ℝ :=
  fun i c => X i c + max ((l.O *ᵥ fun hc => headOut l.act (l.KQ hc.1) (l.V hc.1) X i hc.2) c) 0

/-- A transformer: token embedding (depending on token, role and 0-indexed position; this
includes any positional encoding), layers, readout `W_R`. -/
structure TF (N : ℕ) (ι : Type) where
  emb : Tok N → Role → ℕ → ι → ℝ
  layers : List (Layer ι)
  R : Matrix ι (Tok N) ℝ

/-- Embedded input sequence. -/
def embSeq (emb : Tok N → Role → ℕ → ι → ℝ) (toks : List (Tok N × Role)) :
    Fin toks.length → ι → ℝ :=
  fun j => emb toks[j].1 toks[j].2 j

/-- Hidden states after all layers. -/
def TF.run (tf : TF N ι) (toks : List (Tok N × Role)) : Fin toks.length → ι → ℝ :=
  tf.layers.foldl (fun X l => l.apply X) (embSeq tf.emb toks)

/-- Next-token logits `W_Rᵀ x_T` at the last position. -/
def TF.logits (tf : TF N ι) (toks : List (Tok N × Role)) (w : Tok N) : ℝ :=
  if h : toks.length = 0 then 0
  else ∑ c, tf.R c w * tf.run toks ⟨toks.length - 1, by omega⟩ c

/-- Softmax weights of a score vector. -/
def softmaxW {T : ℕ} (s : Fin T → ℝ) (j : Fin T) : ℝ := Real.exp (s j) / ∑ k, Real.exp (s k)

/-- Angle of the sinusoidal positional encoding, `α = π / (4 L_max)`. -/
def posAngle (L : ℕ) : ℝ := Real.pi / (4 * L)

/-! ## The two-layer construction (Thm. `thm:two_layer_dfs`) -/

/-- Coordinates of the two-layer construction (`d = 4N + 3`): four node blocks
`(b, v)` (`b = 0, 1, 2, 3` are the paper's blocks 1–4), then `ρ = 1` and the positional encoding
`p = (cos, sin)`. -/
abbrev Coord2 (N : ℕ) := (Fin 4 × Fin N) ⊕ Fin 3

/-- Node-block coordinate `(b, v)`. -/
abbrev blk (b : Fin 4) (v : Fin N) : Coord2 N := .inl (b, v)

/-- Token embedding of App. `app:token_embeddings` with the constant coordinate and the
sinusoidal positional encoding `p_i = (cos iα, sin iα)`, `α = π/(4L)`, of
Lemma `lem:first-layer-softmax-copy-relu` (paper position `i = j + 1`): edge endpoints and the
target place their one-hot vector in block 4, root and CoT tokens in block 1, special tokens
are zero. -/
def emb2 (N L : ℕ) (t : Tok N) (r : Role) (j : ℕ) : Coord2 N → ℝ
  | .inl (b, v) =>
    match t with
    | .node u => if u = v ∧ ((r = .trace ∧ b = 0) ∨ (r ≠ .trace ∧ b = 3)) then 1 else 0
    | _ => 0
  | .inr c =>
    if c = 0 then 1
    else if c = 1 then Real.cos (((j : ℝ) + 1) * posAngle L)
    else Real.sin (((j : ℝ) + 1) * posAngle L)

/-- A node block is a one-hot vector or zero. -/
def OneHotOrZero (f : Fin N → ℝ) : Prop := f = 0 ∨ ∃ u, f = Pi.single u 1

/-- Input shape required by Lemma `lem:first-layer-softmax-copy-relu` at 0-indexed position `j`:
blocks 1 and 4 one-hot or zero, blocks 2 and 3 zero, `ρ = 1`, `p = p_{j+1}`. -/
def InputShape (N L : ℕ) (j : ℕ) (x : Coord2 N → ℝ) : Prop :=
  OneHotOrZero (fun v => x (blk 0 v)) ∧ OneHotOrZero (fun v => x (blk 3 v)) ∧
  (∀ v, x (blk 1 v) = 0 ∧ x (blk 2 v) = 0) ∧ x (.inr 0) = 1 ∧
  x (.inr 1) = Real.cos (((j : ℝ) + 1) * posAngle L) ∧
  x (.inr 2) = Real.sin (((j : ℝ) + 1) * posAngle L)

/-- Conclusion of Lemma `lem:first-layer-softmax-copy-relu` for an input `X` and the first-layer
output `X2`: blocks 1 and 4 are unchanged; at every position `i ≥ 1` block 2 is `λ₁ ·` (block 1 of
the predecessor) and block 3 is `λ₂ ·` (block 4 of the predecessor) with `λ₁, λ₂ ∈ [1-2δ, 1]`;
at position 0 (`<s>`, no predecessor) blocks 2 and 3 are zero. -/
def CopyProp (δ : ℝ) {T : ℕ} (X X2 : Fin T → Coord2 N → ℝ) : Prop :=
  (∀ i v, X2 i (blk 0 v) = X i (blk 0 v) ∧ X2 i (blk 3 v) = X i (blk 3 v)) ∧
  (∀ i : Fin T, (i : ℕ) = 0 → ∀ v, X2 i (blk 1 v) = 0 ∧ X2 i (blk 2 v) = 0) ∧
  (∀ i j : Fin T, (i : ℕ) = j + 1 → ∃ l₁ l₂ : ℝ,
      l₁ ∈ Set.Icc (1 - 2 * δ) 1 ∧ l₂ ∈ Set.Icc (1 - 2 * δ) 1 ∧
      ∀ v, X2 i (blk 1 v) = l₁ * X j (blk 0 v) ∧ X2 i (blk 2 v) = l₂ * X j (blk 3 v))

/-- Second layer, eq. `eq:second_layer_weight_kq_ov`: two linear-attention heads.
Head 0 (forward): `W_KQ = [[c₁E,0,0,0],[0,0,0,0],[c₁I,0,0,0],[0,0,0,0]]`, value `-a + d`.
Head 1 (backtracking): `W_KQ = [[c₂I,0,0,0],[c₂I,0,0,0],0,0]`, value `-a + b`.
Values are stored in block 1 of the (zero-padded) value space; `W_O` writes head 0 to block 3 and
head 1 to block 4. All matrices vanish on `ρ` and the positional coordinates. -/
def layer2 (N : ℕ) (c₁ c₂ : ℝ) : Layer (Coord2 N) where
  H := 2
  act := Act.linear
  KQ h := fun r c =>
    match r, c with
    | .inl (br, u), .inl (bc, v) =>
      if h = 0 then
        (if br = 0 ∧ bc = 0 then c₁ else if br = 2 ∧ bc = 0 ∧ u = v then c₁ else 0)
      else (if (br = 0 ∨ br = 1) ∧ bc = 0 ∧ u = v then c₂ else 0)
    | _, _ => 0
  V h := fun r c =>
    match r, c with
    | .inl (br, u), .inl (bc, v) =>
      if br = 0 ∧ u = v then
        (if bc = 0 then -1 else if (h = 0 ∧ bc = 3) ∨ (h = 1 ∧ bc = 1) then 1 else 0)
      else 0
    | _, _ => 0
  O := fun r hc =>
    match r, hc.2 with
    | .inl (br, u), .inl (bc, v) =>
      if bc = 0 ∧ u = v ∧ ((hc.1 = 0 ∧ br = 2) ∨ (hc.1 = 1 ∧ br = 3)) then 1 else 0
    | _, _ => 0

/-- Readout `W_R = (0 0 I I)ᵀ`, zero columns for the special tokens. -/
def R2 (N : ℕ) : Matrix (Coord2 N) (Tok N) ℝ := fun r t =>
  match r, t with
  | .inl (b, v), .node u => if (b = 2 ∨ b = 3) ∧ u = v then 1 else 0
  | _, _ => 0

/-! ## The `k`-layer look-ahead construction (Lemma `lem:k-layer-lookahead`) -/

/-- Input features `η_i = (a_i, d_i, γ_i, ρ_i, χ_i, ζ_i, p_i)`: three node blocks `(b, v)` with
`b = 0, 1, 2` for `a, d, γ`, then `ρ, χ, ζ, p₁, p₂`. -/
abbrev FeatIx (N : ℕ) := (Fin 3 × Fin N) ⊕ Fin 5

/-- The features of Lemma `lem:k-layer-lookahead` (paper position `i = j + 1`): `a` = node one-hot
at root/CoT positions, `d` = node one-hot at edge endpoints and the task target, `γ = e_g` at the
task target only, `ρ = 1`, `χ = 𝟙{i ≡ 0 mod 3}`, `ζ` = BOS indicator, `p_i = (cos iα, sin iα)`. -/
def lookFeat (N L : ℕ) (t : Tok N) (r : Role) (j : ℕ) : FeatIx N → ℝ
  | .inl (b, v) =>
    match t with
    | .node u =>
      if u = v ∧ ((b = 0 ∧ r = .trace) ∨ (b = 1 ∧ r ≠ .trace) ∨ (b = 2 ∧ r = .goal)) then 1
      else 0
    | _ => 0
  | .inr c =>
    if c = 0 then 1
    else if c = 1 then (if (j + 1) % 3 = 0 then 1 else 0)
    else if c = 2 then (if t = .bos then 1 else 0)
    else if c = 3 then Real.cos (((j : ℝ) + 1) * posAngle L)
    else Real.sin (((j : ℝ) + 1) * posAngle L)

/-- Decoded reachability memories of Lemma `lem:k-layer-lookahead` as functions of a vertex:
`mem es 0 u = e_u + Σ_{(u→w)∈E} e_w` and
`mem es (j+1) u = mem es j u + Σ_{f=(a,b)∈E} (mem es j u)[a] · mem es j a`
(eqs. `eq:lookahead-initialization-source`, `eq:lookahead-doubling`; the source memory of a record
`(u, v)` is `mem es j u`, its child memory is `mem es j v`). -/
def mem (es : List (Fin N × Fin N)) : ℕ → Fin N → Fin N → ℕ
  | 0, u, w => (if w = u then 1 else 0) + es.countP (fun f => f.1 = u ∧ f.2 = w)
  | j + 1, u, w => mem es j u w + (es.map fun f => mem es j u f.1 * mem es j f.1 w).sum

/-! ## One-layer transformers with `p`-bit precision (Thm. `thm:lower_bound`) -/

/-- `p`-bit fixed-point numbers with resolution `ε`: `k ε` with an integer mantissa `|k| ≤ 2^p`. -/
def FixedPt (p : ℕ) (ε : ℝ) : Set ℝ := {x | ∃ k : ℤ, |k| ≤ 2 ^ p ∧ x = k * ε}

/-- A one-layer transformer of the architecture of Sec. 2 with `H` heads, width `d`,
key-query dimension `dk` and value dimension `dv`. -/
structure OneLayerTF (N d H dk dv : ℕ) where
  emb : Tok N → Role → ℕ → Fin d → ℝ
  Q : Fin H → Matrix (Fin dk) (Fin d) ℝ
  K : Fin H → Matrix (Fin dk) (Fin d) ℝ
  V : Fin H → Matrix (Fin dv) (Fin d) ℝ
  O : Matrix (Fin d) (Fin H × Fin dv) ℝ
  R : Matrix (Fin d) (Tok N) ℝ

variable {d H dk dv : ℕ}

/-- Rounding maps of a finite-precision evaluation of a one-layer transformer, one per coordinate
and site: `K h a`, `Q h a`, `V h c` round the coordinates produced by `W_K`, `W_Q`, `W_V` of head `h`,
`wt h` the attention weights `w_j = φ(score_j)` of head `h`, `sum h c` the summands
`w_j (W_V x_j)_c` of the attention numerators, `head h c` the head outputs, `O a` the coordinates
produced by `W_O`. -/
structure Rounding (H dk dv d : ℕ) where
  K : Fin H → Fin dk → ℝ → ℝ
  Q : Fin H → Fin dk → ℝ → ℝ
  V : Fin H → Fin dv → ℝ → ℝ
  wt : Fin H → ℝ → ℝ
  sum : Fin H → Fin dv → ℝ → ℝ
  head : Fin H → Fin dv → ℝ → ℝ
  O : Fin d → ℝ → ℝ

/-- `p`-bit fixed-point accumulation (Def. "p-bit precision", following Sanford et al.): every
attention weight and every summand of an attention numerator is rounded to a `p`-bit fixed-point
number (with a resolution that may depend on the head and the coordinate). The other rounding maps
are unrestricted (any number format), which only enlarges the class of models. -/
def Rounding.IsFixed (rd : Rounding H dk dv d) (p : ℕ) : Prop :=
  (∀ h, ∃ ε : ℝ, ∀ x, rd.wt h x ∈ FixedPt p ε) ∧
  (∀ h c, ∃ ε : ℝ, ∀ x, rd.sum h c x ∈ FixedPt p ε)

/-- Logits at the last position, evaluated with the rounding maps `rd`; numerators and
normalizers are accumulated exactly (the fixed-point convention of Def. "p-bit precision": partial
sums of `p`-bit fixed-point numbers are exact). `φ` is the element-wise attention activation,
`normalized` selects normalized attention. -/
def OneLayerTF.logitsRd (tf : OneLayerTF N d H dk dv) (φ : ℝ → ℝ) (normalized : Bool)
    (rd : Rounding H dk dv d) (toks : List (Tok N × Role)) (w : Tok N) : ℝ :=
  let T := toks.length
  let x : ℕ → Fin d → ℝ := fun j =>
    match toks[j]? with
    | some tr => tf.emb tr.1 tr.2 j
    | none => 0
  let xT := x (T - 1)
  let head : Fin H → Fin dv → ℝ := fun h =>
    let q : Fin dk → ℝ := fun a => rd.Q h a ((tf.Q h *ᵥ xT) a)
    let wt : ℕ → ℝ := fun j => rd.wt h (φ (∑ a, rd.K h a ((tf.K h *ᵥ x j) a) * q a))
    let num : Fin dv → ℝ := fun c =>
      ∑ j ∈ Finset.range T, rd.sum h c (wt j * rd.V h c ((tf.V h *ᵥ x j) c))
    fun c => rd.head h c (if normalized then num c / ∑ j ∈ Finset.range T, wt j else num c)
  let x2 : Fin d → ℝ := fun a =>
    xT a + max (rd.O a ((tf.O *ᵥ fun hc : Fin H × Fin dv => head hc.1 hc.2) a)) 0
  ∑ a, tf.R a w * x2 a

end DFSExpr
