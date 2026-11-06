import DFSExpr.Lookahead.Part3

/-!
# Package E, part 4: the second layer (one-step memories, DFS scores)
-/

noncomputable section

open Matrix

namespace DFSExpr

variable {N : ℕ}

/-! ### Generic facts -/

theorem E_lin_out (H : ℕ) (KQ V : Fin H → Matrix (E_I N) (E_I N) ℝ) {T : ℕ}
    (X : Fin T → E_I N → ℝ) (i : Fin T) (r : E_I N) :
    (E_layer H Act.linear KQ V).apply X i r =
      X i r + max (∑ h : Fin H, ∑ j : Fin T, (X j ⬝ᵥ (KQ h *ᵥ X i)) * (V h r ⬝ᵥ X j)) 0 := by
  rw [E_layer_apply]
  simp only [E_attn_linear]

theorem E_lin_single (H : ℕ) (KQ V : Fin H → Matrix (E_I N) (E_I N) ℝ) {T : ℕ}
    (X : Fin T → E_I N → ℝ) (i : Fin T) (r : E_I N) (h0 : Fin H)
    (hV : ∀ h, h ≠ h0 → V h r = 0) :
    (E_layer H Act.linear KQ V).apply X i r =
      X i r + max (∑ j : Fin T, (X j ⬝ᵥ (KQ h0 *ᵥ X i)) * (V h0 r ⬝ᵥ X j)) 0 := by
  rw [E_lin_out, Finset.sum_eq_single h0]
  · intro h _ hh
    simp [hV h hh]
  · simp

theorem E_trCls_congr (F G : E_Cls N → ℝ) (h : ∀ y o, F (.tr y o) = G (.tr y o)) :
    ∀ (l : List (Fin N)) (o : Option (Fin N)),
      ((E_trCls l o).map F).sum = ((E_trCls l o).map G).sum
  | [], _ => rfl
  | y :: l, o => by
    simp only [E_trCls, List.map_cons, List.sum_cons, h, E_trCls_congr F G h l]

theorem E_trCls_zero (F : E_Cls N → ℝ) (h : ∀ y o, F (.tr y o) = 0) (l : List (Fin N))
    (o : Option (Fin N)) : ((E_trCls l o).map F).sum = 0 := by
  rw [E_trCls_congr F (fun _ => 0) h]
  simp

theorem E_countP_cast {α : Type} (P : α → Prop) [DecidablePred P] : ∀ l : List α,
    ((l.countP (fun a => decide (P a)) : ℕ) : ℝ) = (l.map fun a => if P a then (1 : ℝ) else 0).sum
  | [] => by simp
  | b :: l => by
    rw [List.countP_cons, List.map_cons, List.sum_cons, Nat.cast_add, E_countP_cast P l]
    by_cases hb : P b <;> simp [hb] <;> ring

theorem E_sum_map_sub {α : Type} (f g : α → ℝ) : ∀ l : List α,
    (l.map fun a => f a - g a).sum = (l.map f).sum - (l.map g).sum
  | [] => by simp
  | b :: l => by simp only [List.map_cons, List.sum_cons, E_sum_map_sub f g l]; ring

theorem E_ind_mul (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P then (1 : ℝ) else 0) * (if Q then 1 else 0) = if P ∧ Q then 1 else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

theorem E_mem0_cast (es : List (Fin N × Fin N)) (x v : Fin N) :
    ((mem es 0 x v : ℕ) : ℝ) = (if x = v then 1 else 0) +
      (es.map fun e => (if x = e.1 then (1 : ℝ) else 0) * (if e.2 = v then 1 else 0)).sum := by
  simp only [mem, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [E_countP_cast (fun f : Fin N × Fin N => f.1 = x ∧ f.2 = v)]
  congr 1
  · by_cases h : x = v <;> simp [h, eq_comm]
  · congr 1
    refine List.map_congr_left fun e _ => ?_
    rw [E_ind_mul]
    by_cases h1 : e.1 = x
    · simp [h1]
    · have h1' : ¬ x = e.1 := fun h => h1 h.symm
      simp [h1, h1']

theorem E_memS_cast (es : List (Fin N × Fin N)) (j : ℕ) (x v : Fin N) :
    ((mem es (j + 1) x v : ℕ) : ℝ) = (mem es j x v : ℝ) +
      (es.map fun e => (mem es j x e.1 : ℝ) * (mem es j e.1 v : ℝ)).sum := by
  simp only [mem, Nat.cast_add, Nat.cast_list_sum, List.map_map]
  congr 2
  refine List.map_congr_left fun e _ => ?_
  simp

/-! ### Invariant accessors -/

section access

variable {es : List (Fin N × Fin N)} {tgt : Fin N} {τ : List (Fin N)}
  {X : Fin (dfsInput es tgt τ).length → E_I N → ℝ}

theorem E_St_a (hX : E_Static es tgt τ X) (p v) :
    X p (.inl (.a, v)) = (E_cls (dfsInput es tgt τ) p).a v := (hX p v).1
theorem E_St_U (hX : E_Static es tgt τ X) (p v) :
    X p (.inl (.UP, v)) - X p (.inl (.UM, v)) = (E_cls (dfsInput es tgt τ) p).U v := (hX p v).2.1
theorem E_St_V (hX : E_Static es tgt τ X) (p v) :
    X p (.inl (.VP, v)) - X p (.inl (.VM, v)) = (E_cls (dfsInput es tgt τ) p).V v :=
  (hX p v).2.2.1
theorem E_St_b (hX : E_Static es tgt τ X) (p v) :
    X p (.inl (.bP, v)) - X p (.inl (.bM, v)) = (E_cls (dfsInput es tgt τ) p).b v :=
  (hX p v).2.2.2.1
theorem E_St_G (hX : E_Static es tgt τ X) (p v) :
    X p (.inl (.GP, v)) - X p (.inl (.GM, v)) = if tgt = v then 1 else 0 :=
  (hX p v).2.2.2.2.1
theorem E_St_rho (hX : E_Static es tgt τ X) (p) [NeZero N] : X p E_ρ = 1 :=
  (hX p 0).2.2.2.2.2.1
theorem E_St_zeta (hX : E_Static es tgt τ X) (p) [NeZero N] :
    X p E_ζ = (E_cls (dfsInput es tgt τ) p).z := (hX p 0).2.2.2.2.2.2.1
theorem E_St_ZP (hX : E_Static es tgt τ X) (p v) : X p (.inl (.ZP, v)) = 0 :=
  (hX p v).2.2.2.2.2.2.2.1
theorem E_St_ZM (hX : E_Static es tgt τ X) (p v) : X p (.inl (.ZM, v)) = 0 :=
  (hX p v).2.2.2.2.2.2.2.2

end access

theorem E_Static_frame {es : List (Fin N × Fin N)} {tgt : Fin N} {τ : List (Fin N)}
    {X Y : Fin (dfsInput es tgt τ).length → E_I N → ℝ} (hX : E_Static es tgt τ X)
    (hB : ∀ p v (B : E_Bk), B ∈ [E_Bk.a, .UP, .UM, .VP, .VM, .bP, .bM, .GP, .GM, .ZP, .ZM] →
      Y p (.inl (B, v)) = X p (.inl (B, v)))
    (hS : ∀ p c, Y p (.inr c) = X p (.inr c)) : E_Static es tgt τ Y := by
  intro p v
  have := hX p v
  rw [hB p v .a (by simp), hB p v .UP (by simp), hB p v .UM (by simp), hB p v .VP (by simp),
    hB p v .VM (by simp), hB p v .bP (by simp), hB p v .bM (by simp), hB p v .GP (by simp),
    hB p v .GM (by simp), hB p v .ZP (by simp), hB p v .ZM (by simp), hS p 0, hS p 2]
  exact this

/-! ### Layer 2 -/

def E_KQ2a : Matrix (E_I N) (E_I N) ℝ := E_lr (fun w : Fin N => E_pv .UP .UM w) (fun w => E_pv .UP .UM w)
def E_KQ2b : Matrix (E_I N) (E_I N) ℝ := E_lr (fun w : Fin N => E_pv .UP .UM w) (fun w => E_pv .VP .VM w)
def E_KQ2c : Matrix (E_I N) (E_I N) ℝ :=
  E_lr (fun w : Fin N => E_pv .UP .UM w + E_sv .a) (fun w => E_e (.inl (.a, w)))
def E_KQ2d : Matrix (E_I N) (E_I N) ℝ :=
  E_lr (fun w : Fin N => E_e (.inl (.a, w)) + E_pv .bP .bM w) (fun w => E_e (.inl (.a, w)))

def E_KQ2 : Fin 4 → Matrix (E_I N) (E_I N) ℝ := ![E_KQ2a, E_KQ2b, E_KQ2c, E_KQ2d]

def E_V2 : Fin 4 → Matrix (E_I N) (E_I N) ℝ := fun h r =>
  match r with
  | .inl (.SP, v) => if h = 0 then E_pv .VP .VM v else 0
  | .inl (.CP, v) => if h = 1 then E_pv .VP .VM v else 0
  | .inl (.Df, v) => if h = 2 then (2 : ℝ) • (E_pv .VP .VM v - E_e (.inl (.a, v))) else 0
  | .inl (.Db, v) => if h = 3 then E_pv .bP .bM v - E_e (.inl (.a, v)) else 0
  | _ => 0

/-- The second layer: source/child neighbours and the two DFS heads. -/
def E_L2 : Layer (E_I N) := E_layer 4 Act.linear E_KQ2 E_V2

theorem E_L2_frame {T : ℕ} (X : Fin T → E_I N → ℝ) (p : Fin T) (r : E_I N)
    (hr : ∀ h, E_V2 h r = 0) : E_L2.apply X p r = X p r :=
  E_layer_frame _ _ _ _ X p r hr

theorem E_V2_zero (h : Fin 4) (B : E_Bk) (hB : B ≠ .SP ∧ B ≠ .CP ∧ B ≠ .Df ∧ B ≠ .Db) (v : Fin N) :
    E_V2 h (.inl (B, v)) = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  cases B <;> first | rfl | exact absurd rfl ‹_›

/-- The class functions of the sums of layer 2. -/
def E_F2S (Up : Fin N → ℝ) (v : Fin N) (c : E_Cls N) : ℝ := (∑ w, c.U w * Up w) * c.V v

theorem E_F2S_rcd (Up : Fin N → ℝ) (v x y : Fin N) :
    E_F2S Up v (.rcd (some x) y) = Up x * (if y = v then 1 else 0) := by
  simp [E_F2S, E_Cls.U, E_Cls.V, Finset.sum_ite_eq]

theorem E_sum_F2S (es : List (Fin N × Fin N)) (tgt : Fin N) (τ : List (Fin N))
    (Up : Fin N → ℝ) (v : Fin N) :
    ∑ s : Fin (dfsInput es tgt τ).length, E_F2S Up v (E_cls (dfsInput es tgt τ) s) =
      (es.map fun e => Up e.1 * (if e.2 = v then 1 else 0)).sum := by
  rw [E_master es tgt τ _ (by simp [E_F2S, E_Cls.U]),
    E_trCls_zero _ (fun y o => by simp [E_F2S, E_Cls.U])]
  simp only [E_F2S_rcd]
  simp [E_F2S, E_Cls.U]

section L2

variable {es : List (Fin N × Fin N)} {tgt : Fin N} {τ : List (Fin N)}
  {X : Fin (dfsInput es tgt τ).length → E_I N → ℝ}

theorem E_L2_S (hX : E_Inv1 es tgt τ X) (p : Fin (dfsInput es tgt τ).length) (v : Fin N) :
    E_L2.apply X p (.inl (.SP, v)) - E_L2.apply X p (.inl (.SM, v)) =
      (E_cls (dfsInput es tgt τ) p).S es 0 v := by
  rw [E_L2, E_lin_single _ _ _ X p _ 0 (fun h hh => by simp [E_V2, hh]),
    E_layer_frame _ _ _ _ X p _ (fun h => E_V2_zero h .SM (by decide) v)]
  have hsum : ∑ s, (X s ⬝ᵥ (E_KQ2 0 *ᵥ X p)) * (E_V2 0 (.inl (.SP, v)) ⬝ᵥ X s) =
      ∑ s : Fin (dfsInput es tgt τ).length,
        E_F2S (E_cls (dfsInput es tgt τ) p).U v (E_cls (dfsInput es tgt τ) s) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [show E_KQ2 0 = (E_KQ2a : Matrix (E_I N) (E_I N) ℝ) from rfl, E_KQ2a, E_lr_score,
      E_pv_dot, E_St_U hX.1, E_V2, ↓reduceIte, E_St_V hX.1, E_F2S]
  rw [hsum, E_sum_F2S, show ∀ a b c : ℝ, a + b - c = (a - c) + b from fun a b c => by ring,
    (hX.2 p v).1]
  rcases E_cls (dfsInput es tgt τ) p with _ | ⟨_ | x, y⟩ | ⟨y, o⟩ | _ <;>
    simp only [E_Cls.U, E_Cls.S, zero_mul, List.map_const', List.sum_replicate, smul_zero,
      max_self, add_zero]
  rw [E_mem0_cast, max_eq_left]
  exact List.sum_nonneg fun a ha => by
    obtain ⟨e, _, rfl⟩ := List.mem_map.1 ha
    split_ifs <;> norm_num

theorem E_L2_C (hX : E_Inv1 es tgt τ X) (p : Fin (dfsInput es tgt τ).length) (v : Fin N) :
    E_L2.apply X p (.inl (.CP, v)) - E_L2.apply X p (.inl (.CM, v)) =
      (E_cls (dfsInput es tgt τ) p).C es 0 v := by
  rw [E_L2, E_lin_single _ _ _ X p _ 1 (fun h hh => by simp [E_V2, hh]),
    E_layer_frame _ _ _ _ X p _ (fun h => E_V2_zero h .CM (by decide) v)]
  have hsum : ∑ s, (X s ⬝ᵥ (E_KQ2 1 *ᵥ X p)) * (E_V2 1 (.inl (.CP, v)) ⬝ᵥ X s) =
      ∑ s : Fin (dfsInput es tgt τ).length,
        E_F2S (E_cls (dfsInput es tgt τ) p).V v (E_cls (dfsInput es tgt τ) s) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [show E_KQ2 1 = (E_KQ2b : Matrix (E_I N) (E_I N) ℝ) from rfl, E_KQ2b, E_lr_score,
      E_pv_dot, E_St_U hX.1, E_V2, ↓reduceIte, E_St_V hX.1, E_F2S]
  rw [hsum, E_sum_F2S, show ∀ a b c : ℝ, a + b - c = (a - c) + b from fun a b c => by ring,
    (hX.2 p v).2.1]
  rcases E_cls (dfsInput es tgt τ) p with _ | ⟨x, y⟩ | ⟨y, o⟩ | _ <;>
    simp only [E_Cls.V, E_Cls.C, zero_mul, List.map_const', List.sum_replicate, smul_zero,
      max_self, add_zero]
  rw [E_mem0_cast, max_eq_left]
  exact List.sum_nonneg fun a ha => by
    obtain ⟨e, _, rfl⟩ := List.mem_map.1 ha
    split_ifs <;> norm_num

end L2

/-! ### The last position -/

/-- The last (query) position. -/
def E_last (es : List (Fin N × Fin N)) (tgt : Fin N) (τ : List (Fin N)) :
    Fin (dfsInput es tgt τ).length :=
  ⟨(dfsInput es tgt τ).length - 1, by rw [E_lay_len]; omega⟩

theorem E_cls_last (es : List (Fin N × Fin N)) (tgt : Fin N) (τ : List (Fin N)) (x : Fin N)
    (hx : τ.getLast? = some x) :
    ∃ o, E_cls (dfsInput es tgt τ) (E_last es tgt τ) = .tr x o := by
  have ht : 0 < τ.length := by
    rcases τ with _ | ⟨a, l⟩
    · simp at hx
    · simp
  have hlast : ((E_last es tgt τ) : ℕ) = 3 * es.length + 3 + (τ.length - 1) := by
    simp only [E_last, E_lay_len]; omega
  have hget : τ[τ.length - 1]? = some x := by rw [← List.getLast?_eq_getElem?]; exact hx
  rw [hlast, E_cls_tr]
  simp only [E_trAt, hget]
  exact ⟨_, rfl⟩

theorem E_Al (x : Fin N) (o : Option (Fin N)) (w : Fin N) :
    (E_Cls.tr x o).a w = if x = w then 1 else 0 := rfl

theorem E_sum_Al (f : Fin N → ℝ) (x : Fin N) :
    ∑ w, f w * (if x = w then 1 else 0) = f x := by
  simp [mul_ite, Finset.sum_ite_eq]

theorem E_ind_db (x v p q : Fin N) (hxv : x ≠ v) :
    ((if q = x then (1 : ℝ) else 0) + (if p = x then 1 else 0)) *
        ((if p = v then 1 else 0) - (if q = v then 1 else 0)) =
      (if (p, q) = (v, x) then 1 else 0) - (if (p, q) = (x, v) then 1 else 0) := by
  by_cases hp : p = v <;> by_cases hq : q = x <;> by_cases hp' : p = x <;>
    by_cases hq' : q = v <;> simp_all

section L2last

variable {es : List (Fin N × Fin N)} {tgt : Fin N} {τ : List (Fin N)}
  {X : Fin (dfsInput es tgt τ).length → E_I N → ℝ}

/-- Class function of the forward DFS head. -/
def E_FDf (Al : Fin N → ℝ) (v : Fin N) (c : E_Cls N) : ℝ :=
  (∑ w, (c.U w + ∑ w', c.a w') * Al w) * (2 * (c.V v - c.a v))

theorem E_L2_Df (hX : E_Inv1 es tgt τ X) (hes : es.Nodup) (x : Fin N) (hx : τ.getLast? = some x)
    (v : Fin N) :
    E_L2.apply X (E_last es tgt τ) (.inl (.Df, v)) = if (x, v) ∈ es ∧ v ∉ τ then 2 else 0 := by
  obtain ⟨o, ho⟩ := E_cls_last es tgt τ x hx
  rw [E_L2, E_lin_single _ _ _ X _ _ 2 (fun h hh => by simp [E_V2, hh]), (hX.2 _ v).2.2.1,
    zero_add]
  have hsum : ∑ s, (X s ⬝ᵥ (E_KQ2 2 *ᵥ X (E_last es tgt τ))) * (E_V2 2 (.inl (.Df, v)) ⬝ᵥ X s) =
      ∑ s : Fin (dfsInput es tgt τ).length,
        E_FDf (E_cls (dfsInput es tgt τ) (E_last es tgt τ)).a v (E_cls (dfsInput es tgt τ) s) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [show E_KQ2 2 = (E_KQ2c : Matrix (E_I N) (E_I N) ℝ) from rfl, E_KQ2c, E_lr_score,
      E_pv_dot, add_dotProduct, E_sv_dot, E_e_dot, E_St_U hX.1, E_St_a hX.1, E_V2, ↓reduceIte,
      smul_dotProduct, sub_dotProduct, E_St_V hX.1, E_FDf, smul_eq_mul]
  rw [hsum, ho, E_master es tgt τ _ (by simp [E_FDf, E_Cls.U, E_Cls.a, E_Cls.V]),
    E_trCls_congr _ (fun c => -2 * c.a v) (fun y o => by
      simp only [E_FDf, E_Al, E_Cls.U, E_Cls.V, zero_add, E_sum_Al, E_Cls.a]
      simp [Finset.sum_ite_eq]
      split_ifs <;> norm_num),
    List.sum_map_mul_left, E_tr_a]
  have hrec : ∀ e : Fin N × Fin N, E_FDf (fun w => (E_Cls.tr x o).a w) v (.rcd (some e.1) e.2) =
      2 * (if e = (x, v) then 1 else 0) := by
    intro e
    simp only [E_FDf, E_Al, E_Cls.U, E_Cls.V, E_Cls.a, add_zero, sub_zero, E_sum_Al]
    by_cases h1 : e.1 = x <;> by_cases h2 : e.2 = v <;>
      simp [h1, h2, Prod.ext_iff, eq_comm]
  simp only [hrec, List.sum_map_mul_left, E_sum_count]
  have hbos : E_FDf (fun w => (E_Cls.tr x o).a w) v .bos = 0 := by
    simp [E_FDf, E_Cls.U, E_Cls.a, E_Cls.V]
  rw [hbos]
  have hc1 : es.count (x, v) ≤ 1 := List.nodup_iff_count_le_one.1 hes _
  by_cases hm : (x, v) ∈ es
  · have : es.count (x, v) = 1 := le_antisymm hc1 (List.count_pos_iff.2 hm)
    by_cases hv : v ∈ τ
    · have : 1 ≤ τ.count v := List.count_pos_iff.2 hv
      have h' : (1 : ℝ) ≤ τ.count v := by exact_mod_cast this
      simp only [hm, hv, not_true_eq_false, and_false, ↓reduceIte]
      rw [max_eq_right]
      push_cast [*]
      linarith
    · have : τ.count v = 0 := List.count_eq_zero.2 hv
      simp only [hm, hv, not_false_eq_true, and_self, ↓reduceIte]
      rw [max_eq_left] <;> push_cast [*] <;> norm_num
  · have : es.count (x, v) = 0 := List.count_eq_zero.2 hm
    simp only [hm, false_and, ↓reduceIte]
    rw [max_eq_right]
    push_cast [*]
    have : (0 : ℝ) ≤ τ.count v := by positivity
    linarith

/-- Class function of the backtracking head. -/
def E_FDb (Al : Fin N → ℝ) (v : Fin N) (c : E_Cls N) : ℝ :=
  (∑ w, (c.a w + c.b w) * Al w) * (c.b v - c.a v)

theorem E_L2_Db (hX : E_Inv1 es tgt τ X) (x : Fin N) (hx : τ.getLast? = some x)
    (rest : List (Fin N))
    (htr : ∀ v, v ≠ x → (τ.zip τ.tail).count (v, x) =
      (τ.zip τ.tail).count (x, v) + (if rest.head? = some v then 1 else 0))
    (hxr : rest.head? ≠ some x) (v : Fin N) :
    E_L2.apply X (E_last es tgt τ) (.inl (.Db, v)) = if rest.head? = some v then 1 else 0 := by
  obtain ⟨o, ho⟩ := E_cls_last es tgt τ x hx
  rw [E_L2, E_lin_single _ _ _ X _ _ 3 (fun h hh => by simp [E_V2, hh]), (hX.2 _ v).2.2.2,
    zero_add]
  have hsum : ∑ s, (X s ⬝ᵥ (E_KQ2 3 *ᵥ X (E_last es tgt τ))) * (E_V2 3 (.inl (.Db, v)) ⬝ᵥ X s) =
      ∑ s : Fin (dfsInput es tgt τ).length,
        E_FDb (E_cls (dfsInput es tgt τ) (E_last es tgt τ)).a v (E_cls (dfsInput es tgt τ) s) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [show E_KQ2 3 = (E_KQ2d : Matrix (E_I N) (E_I N) ℝ) from rfl, E_KQ2d, E_lr_score,
      E_pv_dot, add_dotProduct, E_e_dot, E_St_b hX.1, E_St_a hX.1, E_V2, ↓reduceIte,
      sub_dotProduct, E_FDb]
  have hrest : ∀ y o', E_FDb (fun w => (E_Cls.tr x o).a w) v (.tr y o') =
      ((E_Cls.tr y o').a x + (E_Cls.tr y o').b x) * ((E_Cls.tr y o').b v - (E_Cls.tr y o').a v) := by
    intro y o'
    simp only [E_FDb, E_Al, E_sum_Al]
  rw [hsum, ho, E_master es tgt τ _ (by simp [E_FDb, E_Cls.b, E_Cls.a])]
  have hbos : E_FDb (fun w => (E_Cls.tr x o).a w) v .bos = 0 := by
    simp [E_FDb, E_Cls.b, E_Cls.a]
  have hrec : ∀ e : Fin N × Fin N, E_FDb (fun w => (E_Cls.tr x o).a w) v (.rcd (some e.1) e.2) = 0 := by
    intro e; simp [E_FDb, E_Cls.b, E_Cls.a]
  simp only [hbos, hrec, List.map_const', List.sum_replicate, smul_zero, zero_add]
  by_cases hvx : v = x
  · subst hvx
    rw [E_trCls_congr _ (fun c => c.b v - c.a v) (fun y o' => by
      rw [hrest]
      rcases o' with _ | p <;> simp only [E_Cls.a, E_Cls.b] <;> split_ifs <;> norm_num)]
    rw [if_neg hxr, max_eq_right]
    have h1 := E_tr_b_le v τ none
    have h2 := E_tr_a v τ none
    simp only [reduceCtorEq, ↓reduceIte, zero_add] at h1
    rw [E_sum_map_sub]
    linarith
  · rcases τ with _ | ⟨y0, ys⟩
    · simp at hx
    · simp only [E_trCls, List.map_cons, List.sum_cons, E_trCls_some, List.map_map]
      have h0 : E_FDb (fun w => (E_Cls.tr x o).a w) v (.tr y0 none) = 0 := by
        rw [hrest]
        simp only [E_Cls.a, E_Cls.b, add_zero, zero_sub]
        by_cases h : y0 = x
        · subst h; simp [Ne.symm hvx]
        · simp [h]
      rw [h0, zero_add]
      have hz : ∀ pq ∈ List.zip (y0 :: ys) ys, ((E_FDb (fun w => (E_Cls.tr x o).a w) v) ∘
          (fun pq => E_Cls.tr pq.2 (some pq.1))) pq =
          (if pq = (v, x) then 1 else 0) - (if pq = (x, v) then 1 else 0) := by
        rintro ⟨p, q⟩ _
        rw [Function.comp_apply, hrest]
        simp only [E_Cls.a, E_Cls.b]
        exact E_ind_db x v p q (Ne.symm hvx)
      rw [List.map_congr_left hz, E_sum_map_sub (fun pq => if pq = (v, x) then (1:ℝ) else 0)
        (fun pq => if pq = (x, v) then (1:ℝ) else 0), E_sum_count, E_sum_count]
      have := htr v hvx
      simp only [List.tail_cons] at this
      rw [this, max_eq_left]
      · split_ifs <;> push_cast <;> ring
      · split_ifs <;> push_cast <;> linarith

end L2last

end DFSExpr
