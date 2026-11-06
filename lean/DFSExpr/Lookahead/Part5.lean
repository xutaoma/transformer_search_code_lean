import DFSExpr.Lookahead.Part4

/-!
# Package E, part 5: propagation layers and the final layer
-/

noncomputable section

open Matrix

namespace DFSExpr

variable {N : ℕ}

/-- State after layer 2 and `j` propagation layers. -/
def E_InvM (es : List (Fin N × Fin N)) (tgt : Fin N) (τ : List (Fin N)) (j : ℕ)
    (Df Db : Fin N → ℝ) (X : Fin (dfsInput es tgt τ).length → E_I N → ℝ) : Prop :=
  E_Static es tgt τ X ∧
  (∀ (p : Fin (dfsInput es tgt τ).length) (v : Fin N),
    X p (.inl (.SP, v)) - X p (.inl (.SM, v)) = (E_cls (dfsInput es tgt τ) p).S es j v ∧
    X p (.inl (.CP, v)) - X p (.inl (.CM, v)) = (E_cls (dfsInput es tgt τ) p).C es j v) ∧
  ∀ v, X (E_last es tgt τ) (.inl (.Df, v)) = Df v ∧ X (E_last es tgt τ) (.inl (.Db, v)) = Db v

theorem E_L2_inv {es : List (Fin N × Fin N)} {tgt : Fin N} {τ : List (Fin N)}
    {X : Fin (dfsInput es tgt τ).length → E_I N → ℝ} (hX : E_Inv1 es tgt τ X) (hes : es.Nodup)
    (x : Fin N) (hx : τ.getLast? = some x) (rest : List (Fin N))
    (htr : ∀ v, v ≠ x → (τ.zip τ.tail).count (v, x) =
      (τ.zip τ.tail).count (x, v) + (if rest.head? = some v then 1 else 0))
    (hxr : rest.head? ≠ some x) :
    E_InvM es tgt τ 0 (fun v => if (x, v) ∈ es ∧ v ∉ τ then 2 else 0)
      (fun v => if rest.head? = some v then 1 else 0) (E_L2.apply X) := by
  refine ⟨E_Static_frame hX.1 (fun p v B hB => E_L2_frame X p _
      (fun h => E_V2_zero h B (by revert hB; cases B <;> decide) v))
      (fun p c => E_L2_frame X p _ (fun h => rfl)),
    fun p v => ⟨E_L2_S hX p v, E_L2_C hX p v⟩,
    fun v => ⟨E_L2_Df hX hes x hx v, E_L2_Db hX x hx rest htr hxr v⟩⟩

/-! ### Propagation layers -/

def E_KQpa : Matrix (E_I N) (E_I N) ℝ := E_lr (fun w : Fin N => E_pv .UP .UM w) (fun w => E_pv .SP .SM w)
def E_KQpb : Matrix (E_I N) (E_I N) ℝ := E_lr (fun w : Fin N => E_pv .UP .UM w) (fun w => E_pv .CP .CM w)
def E_KQp : Fin 2 → Matrix (E_I N) (E_I N) ℝ := ![E_KQpa, E_KQpb]

def E_Vp : Fin 2 → Matrix (E_I N) (E_I N) ℝ := fun h r =>
  match r with
  | .inl (.SP, v) => if h = 0 then E_pv .SP .SM v else 0
  | .inl (.CP, v) => if h = 1 then E_pv .SP .SM v else 0
  | _ => 0

/-- A propagation (doubling) layer. -/
def E_Lp : Layer (E_I N) := E_layer 2 Act.linear E_KQp E_Vp

theorem E_Vp_zero (h : Fin 2) (B : E_Bk) (hB : B ≠ .SP ∧ B ≠ .CP) (v : Fin N) :
    E_Vp h (.inl (B, v)) = 0 := by
  obtain ⟨h1, h2⟩ := hB
  cases B <;> first | rfl | exact absurd rfl ‹_›

/-- Class function of the propagation sums. -/
def E_FP (Qp : Fin N → ℝ) (es : List (Fin N × Fin N)) (j : ℕ) (v : Fin N) (c : E_Cls N) : ℝ :=
  (∑ w, c.U w * Qp w) * c.S es j v

theorem E_sum_FP (es : List (Fin N × Fin N)) (tgt : Fin N) (τ : List (Fin N))
    (Qp : Fin N → ℝ) (j : ℕ) (v : Fin N) :
    ∑ s : Fin (dfsInput es tgt τ).length, E_FP Qp es j v (E_cls (dfsInput es tgt τ) s) =
      (es.map fun e => Qp e.1 * (mem es j e.1 v : ℝ)).sum := by
  rw [E_master es tgt τ _ (by simp [E_FP, E_Cls.U]),
    E_trCls_zero _ (fun y o => by simp [E_FP, E_Cls.U])]
  have h : ∀ e : Fin N × Fin N, E_FP Qp es j v (.rcd (some e.1) e.2) = Qp e.1 * mem es j e.1 v := by
    intro e; simp [E_FP, E_Cls.U, E_Cls.S, Finset.sum_ite_eq]
  simp only [h]
  simp [E_FP, E_Cls.U]

theorem E_Lp_inv {es : List (Fin N × Fin N)} {tgt : Fin N} {τ : List (Fin N)} {j : ℕ}
    {Df Db : Fin N → ℝ} {X : Fin (dfsInput es tgt τ).length → E_I N → ℝ}
    (hX : E_InvM es tgt τ j Df Db X) : E_InvM es tgt τ (j + 1) Df Db (E_Lp.apply X) := by
  have hfr : ∀ p v (B : E_Bk), B ≠ .SP ∧ B ≠ .CP → E_Lp.apply X p (.inl (B, v)) = X p (.inl (B, v)) :=
    fun p v B hB => E_layer_frame _ _ _ _ X p _ (fun h => E_Vp_zero h B hB v)
  have hS : ∀ p v, X p (.inl (.SP, v)) - X p (.inl (.SM, v)) =
      (E_cls (dfsInput es tgt τ) p).S es j v := fun p v => (hX.2.1 p v).1
  have hC : ∀ p v, X p (.inl (.CP, v)) - X p (.inl (.CM, v)) =
      (E_cls (dfsInput es tgt τ) p).C es j v := fun p v => (hX.2.1 p v).2
  refine ⟨E_Static_frame hX.1 (fun p v B hB => hfr p v B (by revert hB; cases B <;> decide))
      (fun p c => E_layer_frame _ _ _ _ X p _ (fun h => rfl)), fun p v => ⟨?_, ?_⟩,
    fun v => ⟨by rw [hfr _ v .Df (by decide)]; exact (hX.2.2 v).1,
      by rw [hfr _ v .Db (by decide)]; exact (hX.2.2 v).2⟩⟩
  · rw [E_Lp, E_lin_single _ _ _ X p _ 0 (fun h hh => by simp [E_Vp, hh]),
      E_layer_frame _ _ _ _ X p _ (fun h => E_Vp_zero h .SM (by decide) v)]
    have hsum : ∑ s, (X s ⬝ᵥ (E_KQp 0 *ᵥ X p)) * (E_Vp 0 (.inl (.SP, v)) ⬝ᵥ X s) =
        ∑ s : Fin (dfsInput es tgt τ).length,
          E_FP ((E_cls (dfsInput es tgt τ) p).S es j) es j v (E_cls (dfsInput es tgt τ) s) := by
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [show E_KQp 0 = (E_KQpa : Matrix (E_I N) (E_I N) ℝ) from rfl, E_KQpa, E_lr_score,
        E_pv_dot, E_St_U hX.1, E_Vp, ↓reduceIte, hS, E_FP]
    rw [hsum, E_sum_FP, show ∀ a b c : ℝ, a + b - c = (a - c) + b from fun a b c => by ring, hS]
    rcases E_cls (dfsInput es tgt τ) p with _ | ⟨_ | x, y⟩ | ⟨y, o⟩ | _ <;>
      simp only [E_Cls.S, zero_mul, List.map_const', List.sum_replicate, smul_zero,
        max_self, add_zero]
    rw [E_memS_cast, max_eq_left]
    exact List.sum_nonneg fun a ha => by
      obtain ⟨e, _, rfl⟩ := List.mem_map.1 ha
      positivity
  · rw [E_Lp, E_lin_single _ _ _ X p _ 1 (fun h hh => by simp [E_Vp, hh]),
      E_layer_frame _ _ _ _ X p _ (fun h => E_Vp_zero h .CM (by decide) v)]
    have hsum : ∑ s, (X s ⬝ᵥ (E_KQp 1 *ᵥ X p)) * (E_Vp 1 (.inl (.CP, v)) ⬝ᵥ X s) =
        ∑ s : Fin (dfsInput es tgt τ).length,
          E_FP ((E_cls (dfsInput es tgt τ) p).C es j) es j v (E_cls (dfsInput es tgt τ) s) := by
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [show E_KQp 1 = (E_KQpb : Matrix (E_I N) (E_I N) ℝ) from rfl, E_KQpb, E_lr_score,
        E_pv_dot, E_St_U hX.1, E_Vp, ↓reduceIte, hS, hC, E_FP]
    rw [hsum, E_sum_FP, show ∀ a b c : ℝ, a + b - c = (a - c) + b from fun a b c => by ring, hC]
    rcases E_cls (dfsInput es tgt τ) p with _ | ⟨x, y⟩ | ⟨y, o⟩ | _ <;>
      simp only [E_Cls.C, zero_mul, List.map_const', List.sum_replicate, smul_zero,
        max_self, add_zero]
    rw [E_memS_cast, max_eq_left]
    exact List.sum_nonneg fun a ha => by
      obtain ⟨e, _, rfl⟩ := List.mem_map.1 ha
      positivity

theorem E_fold_inv {es : List (Fin N × Fin N)} {tgt : Fin N} {τ : List (Fin N)}
    {Df Db : Fin N → ℝ} (n : ℕ) : ∀ (j : ℕ) (X : Fin (dfsInput es tgt τ).length → E_I N → ℝ),
    E_InvM es tgt τ j Df Db X →
      E_InvM es tgt τ (j + n) Df Db ((List.replicate n E_Lp).foldl (fun X l => l.apply X) X) := by
  induction n with
  | zero => intro j X hX; simpa using hX
  | succ n ih =>
    intro j X hX
    rw [List.replicate_succ, List.foldl_cons, show j + (n + 1) = (j + 1) + n by ring]
    exact ih (j + 1) _ (E_Lp_inv hX)

/-! ### The final layer -/

def E_KQka : Matrix (E_I N) (E_I N) ℝ := E_lr (fun w : Fin N => E_pv .CP .CM w) (fun w => E_pv .GP .GM w)
def E_KQkb : Matrix (E_I N) (E_I N) ℝ :=
  E_lr (fun w : Fin N => E_pv .UP .UM w) (fun w => E_e (.inl (.a, w)))
def E_KQkc : Matrix (E_I N) (E_I N) ℝ := E_lr (fun _ : Unit => E_e (E_ρ : E_I N)) (fun _ => E_e E_ρ)
def E_KQkd : Matrix (E_I N) (E_I N) ℝ := E_lr (fun _ : Unit => E_e (E_ζ : E_I N)) (fun _ => E_e E_ρ)
def E_KQk : Fin 4 → Matrix (E_I N) (E_I N) ℝ := ![E_KQka, E_KQkb, E_KQkc, E_KQkd]

def E_VkP (B : ℝ) (v : Fin N) : Fin 4 → E_I N → ℝ :=
  ![E_pv .VP .VM v, B • E_pv .VP .VM v, (-2 * B) • E_e (.inl (.a, v)), (-B) • E_e E_ρ]
def E_VkM (B : ℝ) (v : Fin N) : Fin 4 → E_I N → ℝ :=
  ![E_pv .VP .VM v, B • E_pv .VP .VM v, (-2 * B) • E_e (.inl (.a, v)), (-B - 1) • E_e E_ρ]

def E_Vk (B : ℝ) : Fin 4 → Matrix (E_I N) (E_I N) ℝ := fun h r =>
  match r with
  | .inl (.ZP, v) => E_VkP B v h
  | .inl (.ZM, v) => E_VkM B v h
  | _ => 0

/-- The final layer: goal reachability, adjacency, visited counts, constant. -/
def E_Lk (B : ℝ) : Layer (E_I N) := E_layer 4 Act.linear E_KQk (E_Vk B)

theorem E_Vk_zero (B : ℝ) (h : Fin 4) (C : E_Bk) (hC : C ≠ .ZP ∧ C ≠ .ZM) (v : Fin N) :
    E_Vk B h (.inl (C, v)) = 0 := by
  obtain ⟨h1, h2⟩ := hC
  cases C <;> first | rfl | exact absurd rfl ‹_›

def E_Fk0 (es : List (Fin N × Fin N)) (J : ℕ) (tgt v : Fin N) (c : E_Cls N) : ℝ :=
  (∑ w, c.C es J w * (if tgt = w then 1 else 0)) * c.V v
def E_Fk1 (Al : Fin N → ℝ) (B : ℝ) (v : Fin N) (c : E_Cls N) : ℝ :=
  (∑ w, c.U w * Al w) * (B * c.V v)
def E_Fk2 (B : ℝ) (v : Fin N) (c : E_Cls N) : ℝ := (-2 * B) * c.a v
def E_Fk3 (K : ℝ) (c : E_Cls N) : ℝ := c.z * K

theorem E_Lk_Z {es : List (Fin N × Fin N)} {tgt : Fin N} {τ : List (Fin N)} {J : ℕ}
    {Df Db : Fin N → ℝ} {X : Fin (dfsInput es tgt τ).length → E_I N → ℝ}
    (hX : E_InvM es tgt τ J Df Db X) (x : Fin N) (hx : τ.getLast? = some x) (B : ℝ)
    (v : Fin N) :
    (E_Lk B).apply X (E_last es tgt τ) (.inl (.ZP, v)) -
        (E_Lk B).apply X (E_last es tgt τ) (.inl (.ZM, v)) =
      max ((es.map fun e => (mem es J e.2 tgt : ℝ) * (if e.2 = v then 1 else 0)).sum +
          B * (es.count (x, v) : ℝ) - 2 * B * (τ.count v : ℝ) - B) 0 -
        max ((es.map fun e => (mem es J e.2 tgt : ℝ) * (if e.2 = v then 1 else 0)).sum +
          B * (es.count (x, v) : ℝ) - 2 * B * (τ.count v : ℝ) - B - 1) 0 := by
  obtain ⟨o, ho⟩ := E_cls_last es tgt τ x hx
  have hρ : ∀ p, X p E_ρ = 1 := fun p => (hX.1 p v).2.2.2.2.2.1
  have hζ : ∀ p, X p E_ζ = (E_cls (dfsInput es tgt τ) p).z := fun p => (hX.1 p v).2.2.2.2.2.2.1
  have hSC := hX.2.1
  have hC : ∀ p w, X p (.inl (.CP, w)) - X p (.inl (.CM, w)) =
      (E_cls (dfsInput es tgt τ) p).C es J w := fun p w => (hSC p w).2
  -- the four head sums
  have s0 : ∀ r : E_Bk, (r = .ZP ∨ r = .ZM) →
      ∑ s, (X s ⬝ᵥ (E_KQk 0 *ᵥ X (E_last es tgt τ))) * (E_Vk B 0 (.inl (r, v)) ⬝ᵥ X s) =
        (es.map fun e => (mem es J e.2 tgt : ℝ) * (if e.2 = v then 1 else 0)).sum := by
    intro r hr
    have : ∑ s, (X s ⬝ᵥ (E_KQk 0 *ᵥ X (E_last es tgt τ))) * (E_Vk B 0 (.inl (r, v)) ⬝ᵥ X s) =
        ∑ s : Fin (dfsInput es tgt τ).length, E_Fk0 es J tgt v (E_cls (dfsInput es tgt τ) s) := by
      refine Finset.sum_congr rfl fun s _ => ?_
      rcases hr with rfl | rfl <;>
      simp only [show E_KQk 0 = (E_KQka : Matrix (E_I N) (E_I N) ℝ) from rfl, E_KQka, E_lr_score,
        E_pv_dot, hC, E_St_G hX.1, E_Vk, E_VkP, E_VkM, Matrix.cons_val_zero, E_St_V hX.1, E_Fk0]
    rw [this, E_master es tgt τ _ (by simp [E_Fk0, E_Cls.C]),
      E_trCls_zero _ (fun y o => by simp [E_Fk0, E_Cls.C])]
    have h : ∀ e : Fin N × Fin N, E_Fk0 es J tgt v (.rcd (some e.1) e.2) =
        (mem es J e.2 tgt : ℝ) * (if e.2 = v then 1 else 0) := by
      intro e; simp only [E_Fk0, E_Cls.C, E_Cls.V, E_sum_Al]
    simp only [h]
    simp [E_Fk0, E_Cls.C]
  have s1 : ∀ r : E_Bk, (r = .ZP ∨ r = .ZM) →
      ∑ s, (X s ⬝ᵥ (E_KQk 1 *ᵥ X (E_last es tgt τ))) * (E_Vk B 1 (.inl (r, v)) ⬝ᵥ X s) =
        B * (es.count (x, v) : ℝ) := by
    intro r hr
    have : ∑ s, (X s ⬝ᵥ (E_KQk 1 *ᵥ X (E_last es tgt τ))) * (E_Vk B 1 (.inl (r, v)) ⬝ᵥ X s) =
        ∑ s : Fin (dfsInput es tgt τ).length, E_Fk1 (E_cls (dfsInput es tgt τ) (E_last es tgt τ)).a B v (E_cls (dfsInput es tgt τ) s) := by
      refine Finset.sum_congr rfl fun s _ => ?_
      rcases hr with rfl | rfl <;>
      simp only [show E_KQk 1 = (E_KQkb : Matrix (E_I N) (E_I N) ℝ) from rfl, E_KQkb, E_lr_score,
        E_pv_dot, E_e_dot, E_St_U hX.1, E_St_a hX.1, E_Vk, E_VkP, E_VkM, Matrix.cons_val_one,
        Matrix.cons_val_zero, smul_dotProduct, E_St_V hX.1, E_Fk1, smul_eq_mul]
    rw [this, ho, E_master es tgt τ _ (by simp [E_Fk1, E_Cls.U]),
      E_trCls_zero _ (fun y o => by simp [E_Fk1, E_Cls.U])]
    have h : ∀ e : Fin N × Fin N, E_Fk1 (fun w => (E_Cls.tr x o).a w) B v (.rcd (some e.1) e.2) =
        B * (if e = (x, v) then 1 else 0) := by
      intro e
      simp only [E_Fk1, E_Cls.U, E_Cls.V, E_Al, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte]
      by_cases h1 : e.1 = x <;> by_cases h2 : e.2 = v <;> simp [h1, h2, Prod.ext_iff, eq_comm]
    simp only [h, List.sum_map_mul_left, E_sum_count]
    simp [E_Fk1, E_Cls.U]
  have s2 : ∀ r : E_Bk, (r = .ZP ∨ r = .ZM) →
      ∑ s, (X s ⬝ᵥ (E_KQk 2 *ᵥ X (E_last es tgt τ))) * (E_Vk B 2 (.inl (r, v)) ⬝ᵥ X s) =
        -2 * B * (τ.count v : ℝ) := by
    intro r hr
    have : ∑ s, (X s ⬝ᵥ (E_KQk 2 *ᵥ X (E_last es tgt τ))) * (E_Vk B 2 (.inl (r, v)) ⬝ᵥ X s) =
        ∑ s : Fin (dfsInput es tgt τ).length, E_Fk2 B v (E_cls (dfsInput es tgt τ) s) := by
      refine Finset.sum_congr rfl fun s _ => ?_
      rcases hr with rfl | rfl <;>
      simp only [show E_KQk 2 = (E_KQkc : Matrix (E_I N) (E_I N) ℝ) from rfl, E_KQkc, E_lr_score,
        E_e_dot, hρ, E_Vk, E_VkP, E_VkM, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
        smul_dotProduct, E_St_a hX.1, E_Fk2, smul_eq_mul, Finset.univ_unique,
        Finset.sum_singleton, one_mul]
    rw [this, E_master es tgt τ _ (by simp [E_Fk2, E_Cls.a])]
    have h1 : ((E_trCls τ none).map (E_Fk2 B v)).sum = -2 * B * (τ.count v : ℝ) := by
      rw [show (E_Fk2 B v : E_Cls N → ℝ) = fun c => (-2 * B) * c.a v from rfl,
        List.sum_map_mul_left, E_tr_a]
    rw [h1]
    simp [E_Fk2, E_Cls.a]
  have s3 : ∀ (r : E_Bk) (K : ℝ), (E_Vk B 3 (.inl (r, v)) = K • E_e E_ρ) →
      ∑ s, (X s ⬝ᵥ (E_KQk 3 *ᵥ X (E_last es tgt τ))) * (E_Vk B 3 (.inl (r, v)) ⬝ᵥ X s) = K := by
    intro r K hr
    have : ∑ s, (X s ⬝ᵥ (E_KQk 3 *ᵥ X (E_last es tgt τ))) * (E_Vk B 3 (.inl (r, v)) ⬝ᵥ X s) =
        ∑ s : Fin (dfsInput es tgt τ).length, E_Fk3 K (E_cls (dfsInput es tgt τ) s) := by
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [show E_KQk 3 = (E_KQkd : Matrix (E_I N) (E_I N) ℝ) from rfl, E_KQkd, E_lr_score,
        E_e_dot, hρ, hζ, hr, smul_dotProduct, E_Fk3, smul_eq_mul, Finset.univ_unique,
        Finset.sum_singleton, mul_one]
    rw [this, E_master es tgt τ _ (by simp [E_Fk3, E_Cls.z]),
      E_trCls_zero _ (fun y o => by simp [E_Fk3, E_Cls.z])]
    simp [E_Fk3, E_Cls.z]
  rw [E_Lk, E_lin_out, E_lin_out, Fin.sum_univ_four, Fin.sum_univ_four, E_St_ZP hX.1, E_St_ZM hX.1,
    s0 .ZP (Or.inl rfl), s0 .ZM (Or.inr rfl), s1 .ZP (Or.inl rfl), s1 .ZM (Or.inr rfl),
    s2 .ZP (Or.inl rfl), s2 .ZM (Or.inr rfl), s3 .ZP (-B) rfl, s3 .ZM (-B - 1) rfl]
  ring_nf

theorem E_Lk_frame (B : ℝ) {T : ℕ} (X : Fin T → E_I N → ℝ) (p : Fin T) (C : E_Bk)
    (hC : C ≠ .ZP ∧ C ≠ .ZM) (v : Fin N) :
    (E_Lk B).apply X p (.inl (C, v)) = X p (.inl (C, v)) :=
  E_layer_frame _ _ _ _ X p _ (fun h => E_Vk_zero B h C hC v)

theorem E_Lk_frameS (B : ℝ) {T : ℕ} (X : Fin T → E_I N → ℝ) (p : Fin T) (c : Fin 5) :
    (E_Lk B).apply X p (.inr c) = X p (.inr c) :=
  E_layer_frame _ _ _ _ X p _ (fun h => rfl)

end DFSExpr
