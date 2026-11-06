import DFSExpr.Defs

/-!
# Package E1: support invariant of the look-ahead memories

`mem_support` (`eq:lookahead-support-invariant`): `mem es j u w > 0 ↔ dist(u, w) ≤ 2^j`.
-/

noncomputable section

open Matrix

namespace DFSExpr

variable {N : ℕ}

/-! ### General facts about `ReachLE` -/

theorem E1_reach_succ {E : Fin N → Fin N → Prop} {r : ℕ} {v w : Fin N}
    (h : ReachLE E r v w) : ReachLE E (r + 1) v w :=
  Or.inl h

theorem E1_reach_mono {E : Fin N → Fin N → Prop} {r r' : ℕ} (hr : r ≤ r') {v w : Fin N}
    (h : ReachLE E r v w) : ReachLE E r' v w := by
  induction hr with
  | refl => exact h
  | step _ ih => exact E1_reach_succ ih

theorem E1_reach_refl (E : Fin N → Fin N → Prop) (r : ℕ) (v : Fin N) : ReachLE E r v v :=
  E1_reach_mono (Nat.zero_le r) (show ReachLE E 0 v v from rfl)

/-- Concatenation of paths. -/
theorem E1_reach_trans {E : Fin N → Fin N → Prop} {r r' : ℕ} {u a w : Fin N}
    (h₁ : ReachLE E r u a) (h₂ : ReachLE E r' a w) : ReachLE E (r + r') u w := by
  induction r generalizing u with
  | zero =>
    have : u = a := h₁
    subst this
    simpa using h₂
  | succ r ih =>
    rw [show r + 1 + r' = (r + r') + 1 by omega]
    rcases h₁ with h | ⟨x, hx, h⟩
    · exact E1_reach_succ (ih h)
    · exact Or.inr ⟨x, hx, ih h⟩

/-- A nonempty path starts with an edge. -/
theorem E1_reach_out {E : Fin N → Fin N → Prop} {r : ℕ} {u w : Fin N}
    (h : ReachLE E r u w) (huw : u ≠ w) : ∃ b, E u b := by
  induction r with
  | zero => exact absurd h huw
  | succ r ih =>
    rcases h with h | ⟨x, hx, _⟩
    · exact ih h
    · exact ⟨x, hx⟩

/-- Splitting a path of length `≤ r + r'`: either it has length `≤ r`, or its first `r` edges end at
a vertex `a` with an outgoing edge, from which the rest has length `≤ r'`. -/
theorem E1_reach_split {E : Fin N → Fin N → Prop} {r r' : ℕ} {u w : Fin N}
    (h : ReachLE E (r + r') u w) :
    ReachLE E r u w ∨ ∃ a b, E a b ∧ ReachLE E r u a ∧ ReachLE E r' a w := by
  induction r generalizing u with
  | zero =>
    by_cases huw : u = w
    · exact Or.inl huw
    · obtain ⟨b, hb⟩ := E1_reach_out h huw
      exact Or.inr ⟨u, b, hb, rfl, by simpa using h⟩
  | succ r ih =>
    rw [show r + 1 + r' = (r + r') + 1 by omega] at h
    rcases h with h | ⟨x, hx, h⟩
    · rcases ih h with h' | ⟨a, b, hab, h1, h2⟩
      · exact Or.inl (E1_reach_succ h')
      · exact Or.inr ⟨a, b, hab, E1_reach_succ h1, h2⟩
    · rcases ih h with h' | ⟨a, b, hab, h1, h2⟩
      · exact Or.inl (Or.inr ⟨x, hx, h'⟩)
      · exact Or.inr ⟨a, b, hab, Or.inr ⟨x, hx, h1⟩, h2⟩

/-- Doubling step: `dist ≤ 2r` iff `dist ≤ r`, or the path passes after `≤ r` edges through
the source of some edge from which the target is within `r`. -/
theorem E1_reach_double {E : Fin N → Fin N → Prop} {r : ℕ} {u w : Fin N} :
    ReachLE E (r + r) u w ↔
      ReachLE E r u w ∨ ∃ a b, E a b ∧ ReachLE E r u a ∧ ReachLE E r a w := by
  constructor
  · exact E1_reach_split
  · rintro (h | ⟨a, _, _, h1, h2⟩)
    · exact E1_reach_mono (Nat.le_add_right r r) h
    · exact E1_reach_trans h1 h2

/-! ### Positivity of the memories -/

theorem E1_mem_zero_pos (es : List (Fin N × Fin N)) (u w : Fin N) :
    0 < mem es 0 u w ↔ w = u ∨ (u, w) ∈ es := by
  simp only [mem]
  constructor
  · intro h
    by_cases hwu : w = u
    · exact Or.inl hwu
    · right
      rw [ite_eq_right hwu, zero_add, List.countP_pos_iff] at h
      obtain ⟨f, hf, hp⟩ := h
      simp only [decide_eq_true_eq] at hp
      obtain ⟨h1, h2⟩ := hp
      have : f = (u, w) := Prod.ext h1 h2
      exact this ▸ hf
  · rintro (h | h)
    · rw [ite_eq_left h]; omega
    · have : 0 < es.countP (fun f => decide (f.1 = u ∧ f.2 = w)) :=
        List.countP_pos_iff.2 ⟨(u, w), h, by simp⟩
      omega

theorem E1_mem_succ_pos (es : List (Fin N × Fin N)) (j : ℕ) (u w : Fin N) :
    0 < mem es (j + 1) u w ↔
      0 < mem es j u w ∨ ∃ f ∈ es, 0 < mem es j u f.1 ∧ 0 < mem es j f.1 w := by
  simp only [mem]
  rw [Nat.add_pos_iff_pos_or_pos, List.sum_pos_iff_exists_pos_nat]
  apply or_congr Iff.rfl
  simp only [List.mem_map]
  constructor
  · rintro ⟨x, ⟨f, hf, rfl⟩, hx⟩
    exact ⟨f, hf, Nat.pos_of_mul_pos_right hx, Nat.pos_of_mul_pos_left hx⟩
  · rintro ⟨f, hf, h1, h2⟩
    exact ⟨_, ⟨f, hf, rfl⟩, Nat.mul_pos h1 h2⟩

/-- Support invariant `eq:lookahead-support-invariant`: the memory `mem es j u` is positive exactly
on the vertices within distance `2^j` of `u`. -/
theorem mem_support (es : List (Fin N × Fin N)) (j : ℕ) (u w : Fin N) :
    0 < mem es j u w ↔ ReachLE (Adj es) (2 ^ j) u w := by
  induction j generalizing u w with
  | zero =>
    rw [E1_mem_zero_pos, pow_zero]
    show w = u ∨ (u, w) ∈ es ↔ u = w ∨ ∃ x, (u, x) ∈ es ∧ x = w
    constructor
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr ⟨w, h, rfl⟩
    · rintro (h | ⟨x, hx, rfl⟩)
      · exact Or.inl h.symm
      · exact Or.inr hx
  | succ j ih =>
    rw [E1_mem_succ_pos, pow_succ, mul_two, E1_reach_double, ih]
    apply or_congr Iff.rfl
    constructor
    · rintro ⟨f, hf, h1, h2⟩
      exact ⟨f.1, f.2, hf, (ih u f.1).1 h1, (ih f.1 w).1 h2⟩
    · rintro ⟨a, b, hab, h1, h2⟩
      exact ⟨(a, b), hab, (ih u a).2 h1, (ih a w).2 h2⟩


end DFSExpr

