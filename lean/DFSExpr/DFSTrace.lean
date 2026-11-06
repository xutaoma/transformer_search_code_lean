import DFSExpr.Defs

/-!
# Package C0: structure of valid DFS traces

Proofs of `dfs_transitions` and `dfs_length`, by induction on `Run` with a stronger
invariant over the whole DFS stack.
-/

noncomputable section

open Matrix

namespace DFSExpr

variable {N : ℕ}

/-- Stack-balance invariant (package C0). For a list of transitions `P` and a stack segment
`y :: rest` whose element directly above `y` is `above`: for every `v ≠ y`, `y` departs to `v` at
most once, and arrivals into `y` from `v` plus `[v = above]` equal departures `y → v` plus
`[v = rest.head]`. -/
def C0_SI (P : List (Fin N × Fin N)) : Option (Fin N) → List (Fin N) → Prop
  | _, [] => True
  | above, y :: rest =>
    (∀ v, v ≠ y → P.count (y, v) ≤ 1 ∧
      P.count (v, y) + (if above = some v then 1 else 0) =
        P.count (y, v) + (if rest.head? = some v then 1 else 0)) ∧
    C0_SI P (some y) rest

theorem C0_SI_append (P : List (Fin N × Fin N)) (a b : Fin N) :
    ∀ (above : Option (Fin N)) (stk : List (Fin N)), a ∉ stk → b ∉ stk →
      C0_SI P above stk → C0_SI (P ++ [(a, b)]) above stk
  | _, [], _, _, _ => trivial
  | above, y :: rest, ha, hb, ⟨h1, h2⟩ => by
    simp only [List.mem_cons, not_or] at ha hb
    refine ⟨fun v hv => ?_, C0_SI_append P a b (some y) rest ha.2 hb.2 h2⟩
    have e1 : (P ++ [(a, b)]).count (y, v) = P.count (y, v) := by
      simp [ha.1]
    have e2 : (P ++ [(a, b)]).count (v, y) = P.count (v, y) := by
      simp [hb.1]
    rw [e1, e2]
    exact h1 v hv

theorem C0_zip_append {α : Type*} : ∀ (τ : List α) (x v : α), τ.getLast? = some x →
    (τ ++ [v]).zip (τ ++ [v]).tail = τ.zip τ.tail ++ [(x, v)]
  | [], _, _, h => by simp at h
  | [a], x, v, h => by simp at h; subst h; simp
  | a :: b :: t, x, v, h => by
    have ih := C0_zip_append (b :: t) x v (by simpa using h)
    simp only [List.cons_append, List.tail_cons, List.zip_cons_cons] at ih ⊢
    rw [ih]

theorem C0_mem_zip {α : Type*} {τ : List α} {a b : α} (h : (a, b) ∈ τ.zip τ.tail) :
    a ∈ τ ∧ b ∈ τ := by
  have := List.of_mem_zip h
  exact ⟨this.1, List.mem_of_mem_tail this.2⟩

theorem C0_back_head {E : Fin N → Fin N → Prop} {τ rest : List (Fin N)} {x v : Fin N}
    (hP : DFSNext E τ (x :: rest) v) (hn : ¬ (E x v ∧ v ∉ τ)) : rest.head? = some v := by
  rcases hP with h | h
  · exact absurd h hn
  · exact h.2

theorem C0_count_zero_left {τ : List (Fin N)} {a : Fin N} (ha : a ∉ τ) (b : Fin N) :
    (τ.zip τ.tail).count (a, b) = 0 :=
  List.count_eq_zero.2 fun h => ha (C0_mem_zip h).1

theorem C0_count_zero_right {τ : List (Fin N)} {b : Fin N} (hb : b ∉ τ) (a : Fin N) :
    (τ.zip τ.tail).count (a, b) = 0 :=
  List.count_eq_zero.2 fun h => hb (C0_mem_zip h).2

/-- The main invariant of DFS runs (package C0). -/
theorem C0_inv {E : Fin N → Fin N → Prop} {s : Fin N} {n : ℕ} {τ stk : List (Fin N)}
    (h : Run E (DFSNext E) s n τ stk) :
    (∃ x rest, stk = x :: rest ∧ τ.getLast? = some x) ∧ τ.head? = some s ∧
      (∀ y ∈ stk, y ∈ τ) ∧ stk.Nodup ∧ (∀ v, (v, v) ∉ τ.zip τ.tail) ∧
      C0_SI (τ.zip τ.tail) none stk ∧ τ.length + stk.length = 2 * τ.toFinset.card := by
  induction h with
  | zero =>
    refine ⟨⟨s, [], rfl, rfl⟩, rfl, by simp, by simp, by simp, ?_, by simp⟩
    simp [C0_SI]
  | @fwd n τ rest x v hr hP hE hv ih =>
    obtain ⟨⟨x', rest', hstk, hlast⟩, hhead, hsub, hnd, hself, hSI, hlen⟩ := ih
    obtain ⟨rfl, rfl⟩ := List.cons.inj hstk
    have hxτ : x ∈ τ := hsub x (by simp)
    have hzip := C0_zip_append τ x v hlast
    have hxv : x ≠ v := fun h => hv (h ▸ hxτ)
    have hvrest : v ∉ rest := fun h => hv (hsub v (by simp [h]))
    have hxrest : x ∉ rest := (List.nodup_cons.1 hnd).1
    refine ⟨⟨v, x :: rest, rfl, by simp⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · cases τ with
      | nil => simp at hhead
      | cons a t => simpa using hhead
    · intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · simp
      · exact List.mem_append_left _ (hsub y (by simpa using hy))
    · exact List.nodup_cons.2 ⟨fun h => hv (hsub v h), hnd⟩
    · rw [hzip]
      intro w hw
      simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at hw
      rcases hw with hw | ⟨rfl, rfl⟩
      · exact hself w hw
      · exact hxv rfl
    · rw [hzip]
      obtain ⟨hx1, hx2⟩ := hSI
      refine ⟨fun w hw => ?_, fun w hw => ?_, C0_SI_append _ x v (some x) rest hxrest hvrest hx2⟩
      · have e1 := C0_count_zero_left hv w
        have e2 := C0_count_zero_right hv w
        simp [e1, e2, List.count_singleton, hxv]
      · obtain ⟨h1, h2⟩ := hx1 w hw
        have e3 := C0_count_zero_right hv x
        by_cases hwv : w = v
        · subst hwv
          have e4 := C0_count_zero_left hv x
          simp [e3, e4, hw] at h2 ⊢
          exact h2
        · simp [Ne.symm hwv, Ne.symm hxv] at h2 ⊢
          exact ⟨h1, h2⟩
    · have hvτ : v ∉ τ.toFinset := by simpa using hv
      rw [List.toFinset_append, List.length_append]
      simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, List.length_cons,
        List.length_nil]
      rw [Finset.union_singleton, Finset.card_insert_of_notMem hvτ]
      simp only [List.length_cons] at hlen
      omega
  | @back n τ rest x v hr hP hn ih =>
    obtain ⟨⟨x', rest', hstk, hlast⟩, hhead, hsub, hnd, hself, hSI, hlen⟩ := ih
    obtain ⟨rfl, rfl⟩ := List.cons.inj hstk
    have hrh := C0_back_head hP hn
    obtain ⟨rest, rfl⟩ : ∃ rest', rest = v :: rest' := by
      cases rest with
      | nil => simp at hrh
      | cons a t => simp at hrh; exact ⟨t, by rw [hrh]⟩
    have hzip := C0_zip_append τ x v hlast
    have hvτ : v ∈ τ := hsub v (by simp)
    have hxv : x ≠ v := fun h => (List.nodup_cons.1 hnd).1 (by simp [h])
    have hxrest : x ∉ rest := fun h => (List.nodup_cons.1 hnd).1 (by simp [h])
    have hvrest : v ∉ rest := (List.nodup_cons.1 (List.nodup_cons.1 hnd).2).1
    refine ⟨⟨v, rest, rfl, by simp⟩, ?_, ?_, (List.nodup_cons.1 hnd).2, ?_, ?_, ?_⟩
    · cases τ with
      | nil => simp at hhead
      | cons a t => simpa using hhead
    · intro y hy
      exact List.mem_append_left _ (hsub y (by simp [hy]))
    · rw [hzip]
      intro w hw
      simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at hw
      rcases hw with hw | ⟨rfl, rfl⟩
      · exact hself w hw
      · exact hxv rfl
    · rw [hzip]
      obtain ⟨-, hv1, hv2⟩ := hSI
      refine ⟨fun w hw => ?_, C0_SI_append _ x v (some v) rest hxrest hvrest hv2⟩
      obtain ⟨h1, h2⟩ := hv1 w hw
      simp [List.count_singleton, Ne.symm hw, hxv] at h2 ⊢
      exact ⟨h1, h2⟩
    · have hvτ' : v ∈ τ.toFinset := by simpa using hvτ
      rw [List.toFinset_append, List.length_append]
      simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, List.length_cons,
        List.length_nil]
      rw [Finset.union_singleton, Finset.insert_eq_of_mem hvτ']
      simp only [List.length_cons] at hlen
      omega

theorem dfs_transitions {E : Fin N → Fin N → Prop} {s : Fin N} {τ stk : List (Fin N)}
    (h : DFSTrace E s τ stk) :
    ∃ x rest, stk = x :: rest ∧ τ.getLast? = some x ∧ τ.head? = some s ∧
      (∀ v, (v, v) ∉ τ.zip τ.tail) ∧ (∀ y ∈ rest, y ∈ τ ∧ y ≠ x) ∧
      ∀ v, v ≠ x → (τ.zip τ.tail).count (x, v) ≤ 1 ∧
        (τ.zip τ.tail).count (v, x) =
          (τ.zip τ.tail).count (x, v) + (if rest.head? = some v then 1 else 0) := by
  obtain ⟨n, hr⟩ := h
  obtain ⟨⟨x, rest, rfl, hlast⟩, hhead, hsub, hnd, hself, hSI, -⟩ := C0_inv hr
  refine ⟨x, rest, rfl, hlast, hhead, hself,
    fun y hy => ⟨hsub y (by simp [hy]), ?_⟩, fun v hv => ?_⟩
  · rintro rfl
    exact (List.nodup_cons.1 hnd).1 hy
  · obtain ⟨h1, h2⟩ := hSI.1 v hv
    simp only [reduceCtorEq, ite_false, add_zero] at h2
    exact ⟨h1, h2⟩


theorem dfs_length {E : Fin N → Fin N → Prop} {s : Fin N} {τ stk : List (Fin N)}
    (h : DFSTrace E s τ stk) : τ.length ≤ 2 * N := by
  obtain ⟨n, hr⟩ := h
  obtain ⟨⟨x, rest, rfl, -⟩, -, -, -, -, -, hlen⟩ := C0_inv hr
  have hc : τ.toFinset.card ≤ N := by
    simpa using Finset.card_le_univ τ.toFinset
  simp only [List.length_cons] at hlen
  omega


end DFSExpr
