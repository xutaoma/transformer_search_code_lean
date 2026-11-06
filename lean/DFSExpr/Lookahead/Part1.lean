import DFSExpr.FirstLayer
import DFSExpr.DFSTrace
import DFSExpr.Memory

/-!
# Package E, part 1: coordinates, generic layer lemmas, features, position classes
-/

noncomputable section

open Matrix

namespace DFSExpr

/-- Names of the `N`-coordinate blocks of the look-ahead construction. -/
inductive E_Bk where
  | a | d | gam | bP | bM | UP | UM | VP | VM | GP | GM | SP | SM | CP | CM | Df | Db | ZP | ZM
  deriving DecidableEq

instance E_instFintypeBk : Fintype E_Bk where
  elems := ⟨↑[E_Bk.a, .d, .gam, .bP, .bM, .UP, .UM, .VP, .VM, .GP, .GM, .SP, .SM, .CP, .CM, .Df, .Db,
    .ZP, .ZM], by decide⟩
  complete := by intro x; cases x <;> decide

/-- Coordinates: 19 node blocks and the scalars `ρ, χ, ζ, p₁, p₂` (indices `0, …, 4`). -/
abbrev E_I (N : ℕ) := (E_Bk × Fin N) ⊕ Fin 5

theorem E_card_EB : Fintype.card E_Bk = 19 := rfl

theorem E_card (N : ℕ) : Fintype.card (E_I N) = 19 * N + 5 := by
  simp [E_I, Fintype.card_sum, Fintype.card_prod, E_card_EB]

variable {N : ℕ}

/-! ### Basic functionals -/

/-- Basis vector. -/
def E_e (c : E_I N) : E_I N → ℝ := Pi.single c 1

@[simp] theorem E_e_dot (c : E_I N) (x : E_I N → ℝ) : E_e c ⬝ᵥ x = x c := by
  simp [E_e, single_dotProduct]

/-- Decoding functional of a pair of blocks. -/
def E_pv (P M : E_Bk) (v : Fin N) : E_I N → ℝ := E_e (.inl (P, v)) - E_e (.inl (M, v))

@[simp] theorem E_pv_dot (P M : E_Bk) (v : Fin N) (x : E_I N → ℝ) :
    E_pv P M v ⬝ᵥ x = x (.inl (P, v)) - x (.inl (M, v)) := by
  simp [E_pv, sub_dotProduct]

/-- Sum functional of a block. -/
def E_sv (B : E_Bk) : E_I N → ℝ := ∑ w : Fin N, E_e (.inl (B, w))

@[simp] theorem E_sv_dot (B : E_Bk) (x : E_I N → ℝ) :
    E_sv B ⬝ᵥ x = ∑ w : Fin N, x (.inl (B, w)) := by
  simp [E_sv, sum_dotProduct]

/-- Low-rank key-query matrix `Σ_w k_w q_wᵀ`. -/
def E_lr {κ : Type} [Fintype κ] (k q : κ → E_I N → ℝ) : Matrix (E_I N) (E_I N) ℝ :=
  fun r c => ∑ w : κ, k w r * q w c

theorem E_lr_score {κ : Type} [Fintype κ] (k q : κ → E_I N → ℝ) (x y : E_I N → ℝ) :
    y ⬝ᵥ (E_lr k q *ᵥ x) = ∑ w : κ, (k w ⬝ᵥ y) * (q w ⬝ᵥ x) := by
  have h1 : y ᵥ* E_lr k q = ∑ w : κ, (k w ⬝ᵥ y) • q w := by
    funext c
    simp only [vecMul, dotProduct, E_lr, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun w _ => Finset.sum_congr rfl (fun r _ => by ring))
  rw [dotProduct_mulVec, h1, sum_dotProduct]
  simp [smul_dotProduct]

/-! ### Generic layers whose output projection sums the heads -/

/-- A layer whose output projection adds up the heads coordinatewise. -/
def E_layer (H : ℕ) (act : Act) (KQ V : Fin H → Matrix (E_I N) (E_I N) ℝ) : Layer (E_I N) where
  H := H
  act := act
  KQ := KQ
  V := V
  O := fun r hc => if hc.2 = r then 1 else 0

theorem E_layer_apply (H : ℕ) (act : Act) (KQ V : Fin H → Matrix (E_I N) (E_I N) ℝ) {T : ℕ}
    (X : Fin T → E_I N → ℝ) (i : Fin T) (r : E_I N) :
    (E_layer H act KQ V).apply X i r =
      X i r + max (∑ h : Fin H, ∑ j : Fin T, attnW act (KQ h) X i j * (V h r ⬝ᵥ X j)) 0 := by
  simp only [Layer.apply]
  congr 2
  show ∑ hc : Fin H × E_I N, (if hc.2 = r then (1:ℝ) else 0) * _ = _
  rw [Fintype.sum_prod_type]
  simp only [ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, headOut, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  rfl

theorem E_layer_frame (H : ℕ) (act : Act) (KQ V : Fin H → Matrix (E_I N) (E_I N) ℝ) {T : ℕ}
    (X : Fin T → E_I N → ℝ) (i : Fin T) (r : E_I N) (hr : ∀ h, V h r = 0) :
    (E_layer H act KQ V).apply X i r = X i r := by
  rw [E_layer_apply]
  simp [hr]

theorem E_attn_linear (A : Matrix (E_I N) (E_I N) ℝ) {T : ℕ} (X : Fin T → E_I N → ℝ) (i j : Fin T) :
    attnW Act.linear A X i j = X j ⬝ᵥ (A *ᵥ X i) := by
  simp [attnW, Act.linear]

theorem E_attn_softmax (A : Matrix (E_I N) (E_I N) ℝ) {T : ℕ} (X : Fin T → E_I N → ℝ) (i j : Fin T) :
    attnW Act.softmax A X i j = softmaxW (fun j => X j ⬝ᵥ (A *ᵥ X i)) j := by
  simp [attnW, Act.softmax, softmaxW]

/-! ### Embedding -/

/-- The embedding map on features: `a, d, γ` into their blocks, scalars into the scalars. -/
def E_PhiF (η : FeatIx N → ℝ) : E_I N → ℝ
  | .inl (.a, v) => η (.inl (0, v))
  | .inl (.d, v) => η (.inl (1, v))
  | .inl (.gam, v) => η (.inl (2, v))
  | .inl (_, _) => 0
  | .inr c => η (.inr c)

def E_Phi : (FeatIx N → ℝ) →ₗ[ℝ] (E_I N → ℝ) where
  toFun := E_PhiF
  map_add' η η' := by
    funext r
    rcases r with ⟨B, v⟩ | c
    · cases B <;> simp [E_PhiF]
    · simp [E_PhiF]
  map_smul' s η := by
    funext r
    rcases r with ⟨B, v⟩ | c
    · cases B <;> simp [E_PhiF]
    · simp [E_PhiF]

theorem E_Phi_apply (η : FeatIx N → ℝ) (r : E_I N) : E_Phi η r = E_PhiF η r := rfl

/-! ### Token features -/

/-- Trace node (`a` block). -/
def E_A : Option (Tok N × Role) → Option (Fin N)
  | some (.node y, .trace) => some y
  | _ => none

/-- Graph/goal node (`d` block). -/
def E_D : Option (Tok N × Role) → Option (Fin N)
  | some (.node y, .graph) => some y
  | some (.node y, .goal) => some y
  | _ => none

/-- Goal node (`γ` block). -/
def E_G : Option (Tok N × Role) → Option (Fin N)
  | some (.node y, .goal) => some y
  | _ => none

/-- BOS indicator. -/
def E_Z : Option (Tok N × Role) → Bool
  | some (.bos, _) => true
  | _ => false

theorem E_lf_a (L : ℕ) (t : Tok N) (r : Role) (j : ℕ) (v : Fin N) :
    lookFeat N L t r j (.inl (0, v)) = if E_A (some (t, r)) = some v then 1 else 0 := by
  cases t <;> cases r <;> simp [lookFeat, E_A]

theorem E_lf_d (L : ℕ) (t : Tok N) (r : Role) (j : ℕ) (v : Fin N) :
    lookFeat N L t r j (.inl (1, v)) = if E_D (some (t, r)) = some v then 1 else 0 := by
  cases t <;> cases r <;> simp [lookFeat, E_D]

theorem E_lf_g (L : ℕ) (t : Tok N) (r : Role) (j : ℕ) (v : Fin N) :
    lookFeat N L t r j (.inl (2, v)) = if E_G (some (t, r)) = some v then 1 else 0 := by
  cases t <;> cases r <;> simp [lookFeat, E_G]

theorem E_lf_rho (L : ℕ) (t : Tok N) (r : Role) (j : ℕ) :
    lookFeat N L t r j (.inr 0) = 1 := by
  simp [lookFeat]

theorem E_lf_chi (L : ℕ) (t : Tok N) (r : Role) (j : ℕ) :
    lookFeat N L t r j (.inr 1) = if (j + 1) % 3 = 0 then 1 else 0 := by
  simp [lookFeat]

theorem E_lf_zeta (L : ℕ) (t : Tok N) (r : Role) (j : ℕ) :
    lookFeat N L t r j (.inr 2) = if E_Z (some (t, r)) = true then 1 else 0 := by
  cases t <;> simp [lookFeat, E_Z]

theorem E_lf_p1 (L : ℕ) (t : Tok N) (r : Role) (j : ℕ) :
    lookFeat N L t r j (.inr 3) = Real.cos (((j : ℝ) + 1) * posAngle L) := by
  simp [lookFeat]

theorem E_lf_p2 (L : ℕ) (t : Tok N) (r : Role) (j : ℕ) :
    lookFeat N L t r j (.inr 4) = Real.sin (((j : ℝ) + 1) * posAngle L) := by
  simp [lookFeat]

/-! ### Position classes -/

/-- Class of a position after the first layer: BOS, edge record (with the source if the
predecessor carries a node), trace position (with the predecessor's trace node), other. -/
inductive E_Cls (N : ℕ) where
  | bos
  | rcd (x : Option (Fin N)) (y : Fin N)
  | tr (y : Fin N) (o : Option (Fin N))
  | other

namespace E_Cls

def U : E_Cls N → Fin N → ℝ
  | .rcd (some x) _, v => if x = v then 1 else 0
  | _, _ => 0

def V : E_Cls N → Fin N → ℝ
  | .rcd _ y, v => if y = v then 1 else 0
  | _, _ => 0

def a : E_Cls N → Fin N → ℝ
  | .tr y _, v => if y = v then 1 else 0
  | _, _ => 0

def b : E_Cls N → Fin N → ℝ
  | .tr _ (some p), v => if p = v then 1 else 0
  | _, _ => 0

def z : E_Cls N → ℝ
  | .bos => 1
  | _ => 0

def S (es : List (Fin N × Fin N)) (j : ℕ) : E_Cls N → Fin N → ℝ
  | .rcd (some x) _, v => (mem es j x v : ℝ)
  | _, _ => 0

def C (es : List (Fin N × Fin N)) (j : ℕ) : E_Cls N → Fin N → ℝ
  | .rcd _ y, v => (mem es j y v : ℝ)
  | _, _ => 0

end E_Cls

/-- Class from the predecessor token, the current token and the period-three indicator. -/
def E_clsOf (p c : Option (Tok N × Role)) (χ : Bool) : E_Cls N :=
  match c with
  | some (.bos, _) => .bos
  | some (.node y, .trace) => .tr y (E_A p)
  | some (.node y, _) => if χ then .rcd (E_D p) y else .other
  | _ => .other

/-- Class of position `p` of a token list. -/
def E_cls (toks : List (Tok N × Role)) (p : ℕ) : E_Cls N :=
  E_clsOf toks[p - 1]? toks[p]? (decide ((p + 1) % 3 = 0))

theorem E_clsOf_U (p c : Option (Tok N × Role)) (χ : Bool) (v : Fin N) :
    (E_clsOf p c χ).U v =
      if E_D p = some v ∧ (E_D c).isSome = true ∧ χ = true then 1 else 0 := by
  rcases hD : E_D p with _ | x
  · rcases c with _ | ⟨t, r⟩
    · simp [E_clsOf, E_Cls.U, E_D]
    · cases t <;> cases r <;> cases χ <;> simp only [E_clsOf, hD] <;> simp [E_Cls.U, E_D]
  · rcases c with _ | ⟨t, r⟩
    · simp [E_clsOf, E_Cls.U, E_D]
    · cases t <;> cases r <;> cases χ <;> simp only [E_clsOf, hD] <;> simp [E_Cls.U, E_D]

theorem E_clsOf_V (p c : Option (Tok N × Role)) (χ : Bool) (v : Fin N) :
    (E_clsOf p c χ).V v = if E_D c = some v ∧ χ = true then 1 else 0 := by
  rcases c with _ | ⟨t, r⟩
  · simp [E_clsOf, E_Cls.V, E_D]
  · cases t <;> cases r <;> cases χ <;> simp [E_clsOf, E_Cls.V, E_D]

theorem E_clsOf_a (p c : Option (Tok N × Role)) (χ : Bool) (v : Fin N) :
    (E_clsOf p c χ).a v = if E_A c = some v then 1 else 0 := by
  rcases c with _ | ⟨t, r⟩
  · simp [E_clsOf, E_Cls.a, E_A]
  · cases t <;> cases r <;> cases χ <;> simp [E_clsOf, E_Cls.a, E_A]

theorem E_clsOf_b (p c : Option (Tok N × Role)) (χ : Bool) (v : Fin N) :
    (E_clsOf p c χ).b v = if (E_A c).isSome = true ∧ E_A p = some v then 1 else 0 := by
  rcases hA : E_A p with _ | x
  · rcases c with _ | ⟨t, r⟩
    · simp [E_clsOf, E_Cls.b, E_A]
    · cases t <;> cases r <;> cases χ <;> simp only [E_clsOf, hA] <;> simp [E_Cls.b, E_A]
  · rcases c with _ | ⟨t, r⟩
    · simp [E_clsOf, E_Cls.b, E_A]
    · cases t <;> cases r <;> cases χ <;> simp only [E_clsOf, hA] <;> simp [E_Cls.b, E_A]

theorem E_clsOf_z (p c : Option (Tok N × Role)) (χ : Bool) :
    (E_clsOf p c χ).z = if E_Z c = true then 1 else 0 := by
  rcases c with _ | ⟨t, r⟩
  · simp [E_clsOf, E_Cls.z, E_Z]
  · cases t <;> cases r <;> cases χ <;> simp [E_clsOf, E_Cls.z, E_Z]

end DFSExpr
