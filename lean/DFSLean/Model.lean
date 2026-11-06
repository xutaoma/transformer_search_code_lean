import DFSLean.Defs

/-!
# Stages 2–4: the second-layer transformer, the training loss, the scalar flow, DFS traces

Everything here is a definition (no theorems). Paper references are to `learning_dynamics.tex`
(Sec. 4), `expressivity.tex` (Sec. 3) and `appendix/proof_learning_dynamics.tex` (App. C).

Modelling choices (see README):
* **δ = 0 idealization.** The first layer is taken to copy one-hot vectors exactly, so the hidden
  states entering layer 2 are those of eq. `hidden_state_after_first_layer` (Sec. 3).
* Vertices are `Fin N`; paper vertex `k ∈ [N]` is `Fin` index `k - 1`.
* The second layer is literal: two linear-attention heads (`φ(x) = x`, unnormalized, attending to all
  positions), values `W_V`, routing `W_O`, ReLU, residual, dynamic readout `W_R(n_t)` (Sec. 4).
* **Generalized gradients by activation selection.** Each ReLU argument is a linear functional `f`
  of the parameters. A selection `σ` assigns to every functional a value in `[0,1]`, equal to `1`
  where `f > 0` and `0` where `f < 0`; identical functionals get the same value. The selection
  gradients form a convex set containing Clarke's generalized gradient, so the solution notions
  below include all Filippov/Clarke gradient-flow solutions. For the eight-scalar flow the set is
  exactly the Filippov set wherever `b₁ ≠ 0` (true along the trajectory); at the matrix level it can
  be strictly larger (functionals that are multiples of each other get independent selections).
-/

noncomputable section
open Real Finset Filter Topology Set

namespace DFS

/-! ## Generic differential inclusions (measure-free, as in Stage 1) -/

/-- `z` solves `ż ∈ V(z)` on `[0, ∞)`: continuous, and at every `t ≥ 0` the right difference
quotients approach `V (z t)`. (Stage 1's `IsSol N K α` is `IsDI (Vel N K α)`.) -/
def IsDI {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : E → Set E) (z : ℝ → E) :
    Prop :=
  ContinuousOn z (Ici 0) ∧
  ∀ t ≥ (0 : ℝ), ∀ ε > 0, ∀ᶠ h in 𝓝[>] (0 : ℝ), ∃ w ∈ V (z t), ‖h⁻¹ • (z (t + h) - z t) - w‖ < ε

/-! ## The second layer -/

/-- Second-layer trainable parameters `θ = (A₁, A₂, B₁, B₂)`: `θ k i j` is entry `(i, j)` of the
`k`-th matrix, `k = 0, 1, 2, 3` ↦ `A₁, A₂, B₁, B₂`. -/
abbrev Params (N : ℕ) := Fin 4 → Fin N → Fin N → ℝ

/-- Hidden state of one token entering layer 2: four node blocks `(a, b, c, d)`. -/
abbrev Hid (N : ℕ) := Fin 4 → Fin N → ℝ

variable {N : ℕ}

/-- One-hot vector of a vertex. -/
def oh (v : Fin N) : Fin N → ℝ := fun i => if i = v then 1 else 0

/-- A hidden state with blocks `a, b, c, d`. -/
def mk4 (a b c d : Fin N → ℝ) : Hid N := ![a, b, c, d]

/-- A path-finding prompt (edge list, target, root) together with a CoT prefix
`cot = [n₁, …, n_t]`; the root `n₀` is the last prompt token. -/
structure Ctx (N : ℕ) where
  edges : List (Fin N × Fin N)
  tgt : Fin N
  root : Fin N
  cot : List (Fin N)

namespace Ctx

/-- The trace including the root: `[n₀, n₁, …, n_t]`. -/
def nodes (c : Ctx N) : List (Fin N) := c.root :: c.cot

/-- The current node `n_t`. -/
def cur (c : Ctx N) : Fin N := c.nodes.getLast (List.cons_ne_nil _ _)

/-- Hidden states entering layer 2 (Sec. 3, eq. `hidden_state_after_first_layer`, δ = 0):
`<s>`; for each edge `s_i, t_i, <e>`; then `n_Tar, <r>, n_Root`; then the CoT tokens
`n_k ↦ (n_k, n_{k-1}, 0, 0)`. -/
def hidden (c : Ctx N) : List (Hid N) :=
  [mk4 0 0 0 0] ++
  c.edges.flatMap (fun e => [mk4 0 0 0 (oh e.1), mk4 0 0 (oh e.1) (oh e.2), mk4 0 0 (oh e.2) 0]) ++
  [mk4 0 0 0 (oh c.tgt), mk4 0 0 (oh c.tgt) 0, mk4 (oh c.root) 0 0 0] ++
  (c.cot.zip c.nodes).map (fun p => mk4 (oh p.1) (oh p.2) 0 0)

/-- The query: the hidden state of the last token. -/
def query (c : Ctx N) : Hid N := c.hidden.getLast?.getD 0

/-- Relabel all vertices by a permutation. -/
def perm (pm : Equiv.Perm (Fin N)) (c : Ctx N) : Ctx N :=
  ⟨c.edges.map (Prod.map pm pm), pm c.tgt, pm c.root, c.cot.map pm⟩

end Ctx

/-- Bilinear form `xᵀ M y`. -/
def bil (x : Fin N → ℝ) (M : Fin N → Fin N → ℝ) (y : Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * M i j * y j

/-- Score of key `x` for query `q` in head 1: `xᵀ W_KQ^{(2,1)} q = aₓᵀ A₁ a_q + cₓᵀ A₂ a_q`. -/
def score1 (θ : Params N) (x q : Hid N) : ℝ := bil (x 0) (θ 0) (q 0) + bil (x 2) (θ 1) (q 0)

/-- Score in head 2: `xᵀ W_KQ^{(2,2)} q = aₓᵀ B₁ a_q + bₓᵀ B₂ a_q`. -/
def score2 (θ : Params N) (x q : Hid N) : ℝ := bil (x 0) (θ 2) (q 0) + bil (x 1) (θ 3) (q 0)

/-- Value of head 1: `W_V^{(2,1)} x = -a + d`. -/
def val1 (x : Hid N) : Fin N → ℝ := x 3 - x 0

/-- Value of head 2: `W_V^{(2,2)} x = -a + b`. -/
def val2 (x : Hid N) : Fin N → ℝ := x 1 - x 0

/-- Output of head 1 at the query (linear attention over all positions). -/
def head1 (θ : Params N) (c : Ctx N) : Fin N → ℝ :=
  (c.hidden.map fun x => score1 θ x c.query • val1 x).sum

/-- Output of head 2 at the query. -/
def head2 (θ : Params N) (c : Ctx N) : Fin N → ℝ :=
  (c.hidden.map fun x => score2 θ x c.query • val2 x).sum

/-- Vertex logits: `W_O` routes head 1 to block `c` and head 2 to block `d`, then ReLU and the
residual; the dynamic readout `W_R(n_t) = (0, 0, D, D)ᵀ` sums blocks `c, d` and zeroes `n_t`. -/
def logit (θ : Params N) (c : Ctx N) (v : Fin N) : ℝ :=
  if v = c.cur then 0
  else (c.query 2 v + max (head1 θ c v) 0) + (c.query 3 v + max (head2 θ c v) 0)

/-- Softmax over the `N` vertex tokens. -/
def prob (θ : Params N) (c : Ctx N) (v : Fin N) : ℝ :=
  exp (logit θ c v) / ∑ w, exp (logit θ c w)

/-- Admissible-set loss `-log ∑_{v ∈ C} p_θ(v)`. -/
def admLoss (θ : Params N) (c : Ctx N) (C : Finset (Fin N)) : ℝ := -log (∑ v ∈ C, prob θ c v)

/-! ## Linear-functional structure and selection gradients -/

/-- Frobenius pairing `⟨f, θ⟩`. -/
def pair (f θ : Params N) : ℝ := ∑ k, ∑ i, ∑ j, f k i j * θ k i j

/-- The pairing as a continuous linear map. -/
def pairL (f : Params N) : Params N →L[ℝ] ℝ :=
  ∑ k, ∑ i, ∑ j, f k i j •
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) j).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Fin N → ℝ) i).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => Fin N → Fin N → ℝ) k)))

/-- Basis tensor `e_{k,i,j}`. -/
def bas (k : Fin 4) (i j : Fin N) : Params N :=
  fun k' i' j' => if k' = k ∧ i' = i ∧ j' = j then 1 else 0

/-- Coefficient tensor of the (linear) head-1 output at vertex `v`. -/
def coef1 (c : Ctx N) (v : Fin N) : Params N := fun k i j => head1 (bas k i j) c v

/-- Coefficient tensor of the head-2 output at vertex `v`. -/
def coef2 (c : Ctx N) (v : Fin N) : Params N := fun k i j => head2 (bas k i j) c v

/-- Admissible activation selection at `θ`, keyed by the ReLU argument's functional. -/
def Sel (θ : Params N) (σ : Params N → ℝ) : Prop :=
  ∀ f, σ f ∈ Icc (0 : ℝ) 1 ∧ (0 < pair f θ → σ f = 1) ∧ (pair f θ < 0 → σ f = 0)

/-- Selected gradient of the logit at `v`. -/
def dlogit (c : Ctx N) (v : Fin N) (σ : Params N → ℝ) : Params N :=
  if v = c.cur then 0 else σ (coef1 c v) • coef1 c v + σ (coef2 c v) • coef2 c v

/-- Selected gradient of the cross-entropy step loss `-log p_θ(y)`. -/
def gstep (θ : Params N) (σ : Params N → ℝ) (c : Ctx N) (y : Fin N) : Params N :=
  ∑ v, (prob θ c v - if v = y then 1 else 0) • dlogit c v σ

/-! ## Training data (Sec. 4) -/

section canonical
variable (N K : ℕ) [NeZero N]

/-- Paper vertex `k + 1` as an element of `Fin N`. -/
def nd (k : ℕ) : Fin N := Fin.ofNat N k

/-- Skeleton edges `E₀`: `1 → i` (`2 ≤ i ≤ K+1`), `N-1 → N-2`, `N-2 → N-3`, `N-3 → 1`. -/
def E0 : List (Fin N × Fin N) :=
  (List.range K).map (fun j => (nd N 0, nd N (j + 1))) ++
    [(nd N (N - 2), nd N (N - 3)), (nd N (N - 3), nd N (N - 4)), (nd N (N - 4), nd N 0)]

/-- Training trace `τ₀ = 1 → 2 → 1 → 3 → 1 → ⋯ → K+1 → 1 → N-3` (length `2K + 2`). -/
def tau0 : List (Fin N) :=
  nd N 0 :: (List.range K).flatMap (fun j => [nd N (j + 1), nd N 0]) ++ [nd N (N - 4)]

/-- Context of training step `k`: prompt `(E₀, n_Tar = N, n_Root = N-1)`, CoT
`τ_pre ++ τ₀[:k]` with `τ_pre = N-2 → N-3`. -/
def ctx (k : ℕ) : Ctx N :=
  ⟨E0 N K, nd N (N - 1), nd N (N - 2), [nd N (N - 3), nd N (N - 4)] ++ (tau0 N K).take k⟩

/-- Label of training step `k`: `τ₀[k]`. -/
def ylab (k : ℕ) : Fin N := (tau0 N K).getD k (nd N 0)

/-- Cross-entropy loss of the instance relabeled by `π`, `ℓ_{π(τ_Prompt), π(τ_pre), π(τ₀)}`. -/
def lossInst (pm : Equiv.Perm (Fin N)) (θ : Params N) : ℝ :=
  ∑ k ∈ range (2 * K + 2), -log (prob θ ((ctx N K k).perm pm) (pm (ylab N K k)))

/-- Training loss: permutation average (eq. `permutation_loss`). -/
def lossTrain (θ : Params N) : ℝ :=
  (1 / (N.factorial : ℝ)) * ∑ pm : Equiv.Perm (Fin N), lossInst N K pm θ

/-- Selected gradient of `lossInst π`. -/
def gInst (pm : Equiv.Perm (Fin N)) (θ : Params N) (σ : Params N → ℝ) : Params N :=
  ∑ k ∈ range (2 * K + 2), gstep θ σ ((ctx N K k).perm pm) (pm (ylab N K k))

/-- Selected gradient of `lossTrain`. -/
def gTrain (θ : Params N) (σ : Params N → ℝ) : Params N :=
  (1 / (N.factorial : ℝ)) • ∑ pm : Equiv.Perm (Fin N), gInst N K pm θ σ

/-- No ReLU argument of instance `pm` vanishes at `θ` (the loss is smooth near `θ`). -/
def SmoothInst (pm : Equiv.Perm (Fin N)) (θ : Params N) : Prop :=
  ∀ k < 2 * K + 2, ∀ v, v ≠ ((ctx N K k).perm pm).cur →
    head1 θ ((ctx N K k).perm pm) v ≠ 0 ∧ head2 θ ((ctx N K k).perm pm) v ≠ 0

/-- Velocity set of the matrix-level gradient flow `θ̇ ∈ -α ∂ lossTrain(θ)`. -/
def VelM (α : ℝ) (θ : Params N) : Set (Params N) :=
  {w | ∃ σ, Sel θ σ ∧ w = -α • gTrain N K θ σ}

/-- Matrix-level gradient-flow solution (Filippov/Clarke sense, measure-free form). -/
def IsMatSol (α : ℝ) (θ : ℝ → Params N) : Prop := IsDI (VelM N K α) θ

end canonical

/-! ## The eight scalars (Prop. 4.1, Lemma C.1) -/

/-- The matrix `x I + y E_off`. -/
def sym (x y : ℝ) : Fin N → Fin N → ℝ := fun i j => if i = j then x else y

/-- Embedding of the eight scalars `s = (a₁, b₁, a₂, b₂, g₁, d₁, g₂, d₂)` as the permutation-invariant
parameters `A₁ = a₁I + b₁E_off, A₂ = a₂I + b₂E_off, B₁ = g₁I + d₁E_off, B₂ = g₂I + d₂E_off`. -/
def iota (s : Fin 8 → ℝ) : Params N :=
  ![sym (s 0) (s 1), sym (s 2) (s 3), sym (s 4) (s 5), sym (s 6) (s 7)]

/-- Permutation action `π · θ = (P_π A P_πᵀ)_k`. -/
def permP (pm : Equiv.Perm (Fin N)) (θ : Params N) : Params N :=
  fun k i j => θ k (pm.symm i) (pm.symm j)

/-- Pull-back of a functional along `iota` (its coefficient vector on the eight scalars). -/
def iotaT (f : Params N) : Fin 8 → ℝ := fun m => pair f (iota (Pi.single m 1))

/-- Admissible selection for the scalar loss, keyed by the scalar functional. -/
def Sel8 (s : Fin 8 → ℝ) (σ : (Fin 8 → ℝ) → ℝ) : Prop :=
  ∀ c, σ c ∈ Icc (0 : ℝ) 1 ∧ (0 < c ⬝ᵥ s → σ c = 1) ∧ (c ⬝ᵥ s < 0 → σ c = 0)

/-- Learning-rate normalization of Lemma C.1: `1/N` for `a, g`, `1/(N(N-1))` for `b, d`. -/
def P8 (N : ℕ) (m : Fin 8) : ℝ := if (m : ℕ) % 2 = 0 then 1 / (N : ℝ) else 1 / ((N : ℝ) * (N - 1))

/-- The continuous linear functional `w ↦ c ⬝ᵥ w` on `ℝ⁸`. -/
def dotL (c : Fin 8 → ℝ) : (Fin 8 → ℝ) →L[ℝ] ℝ :=
  ∑ m, c m • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 8 => ℝ) m

section scalar
variable (N K : ℕ) [NeZero N]

/-- Selected gradient of the single-instance loss as a function of the eight scalars. -/
def g8 (s : Fin 8 → ℝ) (σ : (Fin 8 → ℝ) → ℝ) : Fin 8 → ℝ :=
  iotaT (gInst N K 1 (iota s) (σ ∘ iotaT))

/-- Velocity set of the scalar flow (eq. `scalar_flow`): `ṡ_m ∈ -α P8_m (∂ℓ)_m`. -/
def V8 (α : ℝ) (s : Fin 8 → ℝ) : Set (Fin 8 → ℝ) :=
  {w | ∃ σ, Sel8 s σ ∧ w = fun m => -α * P8 N m * g8 N K s σ m}

/-- Solution of the eight-scalar gradient flow. -/
def IsSol8 (α : ℝ) (s : ℝ → Fin 8 → ℝ) : Prop := IsDI (V8 N K α) s

end scalar

/-- Initialization (eq. `initialization`): `a₁ = b₁ = a₂ = g₁ = g₂ = d₂ = c₀`, `b₂ = d₁ = c₀'`. -/
def init8 (c0 c0' : ℝ) : Fin 8 → ℝ := ![c0, c0, c0, c0', c0, c0', c0, c0]

/-- Length of the initial phase `T₀ = N / (4 (K+1) α)` (Lemma C.2). -/
def T0 (N K : ℕ) (α : ℝ) : ℝ := (N : ℝ) / (4 * ((K : ℝ) + 1) * α)

/-- Aggregation to the four variables `(x₁, x₂, y₁, y₂) = (a₂, b₁, g₁ - d₁, g₂ - d₂)` (Cor. C.3). -/
def proj (s : Fin 8 → ℝ) : Fin 4 → ℝ := ![s 2, s 1, s 4 - s 5, s 6 - s 7]

/-! ### Quantities in the gradient formulas of Lemma C.2 (on the region `R`) -/

section gradR
variable (N K : ℕ) (s : Fin 8 → ℝ)

/-- `E = exp (u₊ + v₊)` with `u = a₂ - b₁`, `v = g₁ - d₁ - g₂ + d₂`. -/
def E8 : ℝ := exp (max (s 2 - s 1) 0 + max (s 4 - s 5 - (s 6 - s 7)) 0)
/-- `e^{(b₂)₊}`. -/
def eb8 : ℝ := exp (max (s 3) 0)
/-- `e^{(d₂)₊}`. -/
def ed8 : ℝ := exp (max (s 7) 0)
/-- `D₁` (Case 1 normalizer). -/
def Q1 : ℝ := exp (s 2) + exp (s 4 - s 5) + ed8 s + (K : ℝ) * eb8 s + (N : ℝ) - K - 3
/-- `D_{2,i}` with `j = i - 1` (Case 2 normalizer). -/
def Q2 (j : ℕ) : ℝ :=
  ((K : ℝ) - j) * exp (s 2) + (j : ℝ) * E8 s + exp (s 4 - s 5) + 1 + ed8 s + (N : ℝ) - K - 3
/-- `D_{3,i}` with `j = i - 1` (Case 3 normalizer). -/
def Q3 (j : ℕ) : ℝ :=
  exp (s 4 - s 5) + 2 + ed8 s + (j : ℝ) + ((K : ℝ) - 1 - j) * eb8 s + (N : ℝ) - K - 3
/-- `D₄` (Case 4 normalizer). -/
def Q4 : ℝ := (K : ℝ) * E8 s + exp (s 4 - s 5) + 1 + ed8 s + (N : ℝ) - K - 3

end gradR

/-- Functional `u = a₂ - b₁`. -/
def cu8 : Fin 8 → ℝ := ![0, -1, 1, 0, 0, 0, 0, 0]
/-- Functional `v = g₁ - d₁ - g₂ + d₂`. -/
def cv8 : Fin 8 → ℝ := ![0, 0, 0, 0, 1, -1, -1, 1]
/-- Functional `b₂`. -/
def cb8 : Fin 8 → ℝ := ![0, 0, 0, 1, 0, 0, 0, 0]
/-- Functional `d₂`. -/
def cd8 : Fin 8 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 1]

/-! ## Graph statistics of a context (node-logit tables) -/

namespace Ctx
/-- In-degree of `v` in the prompt's edge list. -/
def din (c : Ctx N) (v : Fin N) : ℝ := ((c.edges.filter fun e => e.2 = v).length : ℝ)
/-- Number of listed edges `x → v`. -/
def ecnt (c : Ctx N) (x v : Fin N) : ℝ := ((c.edges.filter fun e => e = (x, v)).length : ℝ)
/-- Number of occurrences `m_v` of `v` in `(n₀, …, n_t)`. -/
def mcnt (c : Ctx N) (v : Fin N) : ℝ := (c.nodes.count v : ℝ)
/-- Number `A_{x→y}` of CoT steps `x → y`. -/
def trans (c : Ctx N) (x y : Fin N) : ℝ :=
  (((c.cot.zip c.nodes).filter fun p => p.2 = x ∧ p.1 = y).length : ℝ)
end Ctx

/-! ## DFS traces on general graphs (Sec. 3 and the generalization loss of Sec. 4) -/

/-- Children of `n` in the edge list. -/
def children (E : List (Fin N × Fin N)) (n : Fin N) : Finset (Fin N) :=
  ((E.filter fun e => e.1 = n).map Prod.snd).toFinset

/-- One DFS step on `(stack, visited)`: a new vertex is pushed, a visited one is a backtrack. -/
def dstep (st : List (Fin N) × Finset (Fin N)) (w : Fin N) : List (Fin N) × Finset (Fin N) :=
  if w ∈ st.2 then (st.1.tail, st.2) else (w :: st.1, insert w st.2)

/-- DFS state `(stack, visited)` after the CoT prefix `τ` from `root`; the stack head is the current
node, the next entry its stack parent. -/
def dstate (root : Fin N) (τ : List (Fin N)) : List (Fin N) × Finset (Fin N) :=
  τ.foldl dstep ([root], {root})

/-- Unvisited children of the current node. -/
def unvis (E : List (Fin N × Fin N)) (root : Fin N) (τ : List (Fin N)) : Finset (Fin N) :=
  children E ((dstate root τ).1.headD root) \ (dstate root τ).2

/-- Admissible DFS moves `C_t`: the unvisited children if any, else the stack parent. -/
def adm (E : List (Fin N × Fin N)) (root : Fin N) (τ : List (Fin N)) : Finset (Fin N) :=
  if (unvis E root τ).Nonempty then unvis E root τ
  else match (dstate root τ).1 with
    | _ :: p :: _ => {p}
    | _ => ∅

/-- DFS has a valid next move: the current node is not the target, and it has an unvisited child
or a stack parent. -/
def NonTerm (E : List (Fin N × Fin N)) (tgt root : Fin N) (τ : List (Fin N)) : Prop :=
  (dstate root τ).1.headD root ≠ tgt ∧ ((unvis E root τ).Nonempty ∨ 2 ≤ (dstate root τ).1.length)

/-- `τ = [n₁, …, n_T]` is a valid DFS trace from `root`, nonterminated before each step. -/
def ValidTrace (E : List (Fin N × Fin N)) (tgt root : Fin N) (τ : List (Fin N)) : Prop :=
  ∀ k (hk : k < τ.length), NonTerm E tgt root (τ.take k) ∧ τ[k] ∈ adm E root (τ.take k)

/-- Generalization loss of one graph and trace: `∑_t -log ∑_{v ∈ C_t} p_θ(v; τ_Prompt, τ[:t-1])`.
`ℒ_gen` is the supremum of this over all edge sets (`E.Nodup`) and valid traces. -/
def genLoss (θ : Params N) (E : List (Fin N × Fin N)) (tgt root : Fin N) (τ : List (Fin N)) : ℝ :=
  ∑ k ∈ range τ.length, admLoss θ ⟨E, tgt, root, τ.take k⟩ (adm E root (τ.take k))

end DFS
