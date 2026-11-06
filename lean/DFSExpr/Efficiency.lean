import DFSExpr.Defs

/-!
# Package D: efficiency of distance-minimizing look-ahead DFS
(Lemma `lem:lookahead-efficiency`, Cor. `cor:k-layer-efficiency`).
-/

noncomputable section

open Matrix

namespace DFSExpr

variable {M : ℕ}

/-! ## Reachability basics -/

lemma D_reachLE_mono {E : Fin M → Fin M → Prop} {r : ℕ} {v w : Fin M}
    (h : ReachLE E r v w) : ReachLE E (r + 1) v w := Or.inl h

lemma D_reachLE_mono' {E : Fin M → Fin M → Prop} {r r' : ℕ} {v w : Fin M}
    (h : ReachLE E r v w) (hr : r ≤ r') : ReachLE E r' v w := by
  induction hr with
  | refl => exact h
  | step _ ih => exact D_reachLE_mono ih

lemma D_reachLE_trans {E : Fin M → Fin M → Prop} {a b : ℕ} {u v w : Fin M}
    (h1 : ReachLE E a u v) (h2 : ReachLE E b v w) : ReachLE E (a + b) u w := by
  induction a generalizing u with
  | zero =>
    simp only [ReachLE] at h1
    subst h1
    exact D_reachLE_mono' h2 (by omega)
  | succ a ih =>
    rcases h1 with h1 | ⟨x, hx, h1⟩
    · exact D_reachLE_mono' (ih h1) (by omega)
    · have := ih h1
      rw [show a + 1 + b = (a + b) + 1 by omega]
      exact Or.inr ⟨x, hx, this⟩

lemma D_reachLE_edge {E : Fin M → Fin M → Prop} {r : ℕ} {u v w : Fin M}
    (he : E u v) (h : ReachLE E r v w) : ReachLE E (r + 1) u w := Or.inr ⟨v, he, h⟩

lemma D_reachLE_rtg {E : Fin M → Fin M → Prop} {r : ℕ} {v w : Fin M}
    (h : ReachLE E r v w) : Relation.ReflTransGen E v w := by
  induction r generalizing v with
  | zero => simp only [ReachLE] at h; subst h; exact Relation.ReflTransGen.refl
  | succ r ih =>
    rcases h with h | ⟨u, hu, h⟩
    · exact ih h
    · exact Relation.ReflTransGen.head hu (ih h)

lemma D_ra_mono {E : Fin M → Fin M → Prop} {τ : List (Fin M)} {r r' : ℕ} {v w : Fin M}
    (h : ReachAvoid E τ r v w) (hr : r ≤ r') : ReachAvoid E τ r' v w := by
  induction hr with
  | refl => exact h
  | step _ ih => exact Or.inl ih

lemma D_ra_reachLE {E : Fin M → Fin M → Prop} {τ : List (Fin M)} {r : ℕ} {v w : Fin M}
    (h : ReachAvoid E τ r v w) : ReachLE E r v w := by
  induction r generalizing v with
  | zero => exact h.1
  | succ r ih =>
    rcases h with h | ⟨_, u, hu, h⟩
    · exact Or.inl (ih h)
    · exact Or.inr ⟨u, hu, ih h⟩

lemma D_ra_not_mem {E : Fin M → Fin M → Prop} {τ : List (Fin M)} {r : ℕ} {v w : Fin M}
    (h : ReachAvoid E τ r v w) : v ∉ τ := by
  induction r with
  | zero => exact h.2
  | succ r ih =>
    rcases h with h | ⟨hv, _⟩
    · exact ih h
    · exact hv

/-- A path of length `≤ r` avoids every vertex of `τ` that cannot reach the goal within `r`. -/
lemma D_ra_of_reachLE {E : Fin M → Fin M → Prop} {τ : List (Fin M)} {r : ℕ} {v w : Fin M}
    (hτ : ∀ y ∈ τ, ¬ ReachLE E r y w) (h : ReachLE E r v w) : ReachAvoid E τ r v w := by
  induction r generalizing v with
  | zero =>
    refine ⟨h, fun hv => hτ v hv h⟩
  | succ r ih =>
    have hτ' : ∀ y ∈ τ, ¬ ReachLE E r y w := fun y hy hr => hτ y hy (Or.inl hr)
    rcases h with h' | ⟨u, hu, h'⟩
    · exact Or.inl (ih hτ' h')
    · exact Or.inr ⟨fun hv => hτ v hv (Or.inr ⟨u, hu, h'⟩), u, hu, ih hτ' h'⟩

/-! ## The DM policy is a DFS policy and deterministic -/

lemma D_dm_dfs {L : ℕ} {E : Fin M → Fin M → Prop} {g : Fin M} {τ stk : List (Fin M)} {v : Fin M}
    (h : DMMove L E g τ stk v) : DFSNext E τ stk v := by
  cases stk with
  | nil => exact h.elim
  | cons x rest =>
    rcases h with ⟨⟨h1, h2, _⟩, _⟩ | ⟨_, ⟨h1, h2⟩, _⟩ | h
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr h

/-! ## Run invariants -/

/-- The stack, read from the bottom, is a path in `E` from the root `s`. -/
def D_StkPath (E : Fin M → Fin M → Prop) (s : Fin M) : List (Fin M) → Prop
  | [] => False
  | [x] => x = s
  | x :: y :: rest => E y x ∧ D_StkPath E s (y :: rest)

lemma D_stkPath_reachLE {E : Fin M → Fin M → Prop} {s : Fin M} :
    ∀ {x : Fin M} {rest : List (Fin M)}, D_StkPath E s (x :: rest) →
      ReachLE E rest.length s x
  | x, [], h => by simp only [D_StkPath] at h; subst h; rfl
  | x, y :: rest, h => by
    obtain ⟨hyx, h⟩ := h
    have := D_stkPath_reachLE h
    have h2 : ReachLE E 1 y x := Or.inr ⟨x, hyx, rfl⟩
    simpa using D_reachLE_trans this h2

lemma D_stkPath_pot {E : Fin M → Fin M → Prop} {s : Fin M} (φ : Fin M → ℕ)
    (hφ : ∀ a b, E a b → φ b = φ a + 1) :
    ∀ {x : Fin M} {rest : List (Fin M)}, D_StkPath E s (x :: rest) →
      φ x = φ s + rest.length
  | x, [], h => by simp only [D_StkPath] at h; subst h; simp
  | x, y :: rest, h => by
    obtain ⟨hyx, h⟩ := h
    have := D_stkPath_pot φ hφ h
    rw [hφ _ _ hyx, this]
    simp; omega

lemma D_toFinset_append_single (τ : List (Fin M)) (v : Fin M) :
    (τ ++ [v]).toFinset = insert v τ.toFinset := by
  ext a; simp

/-- Invariants of a DFS run. -/
def D_Inv (E : Fin M → Fin M → Prop) (s : Fin M) (τ stk : List (Fin M)) : Prop :=
  ∃ x rest, stk = x :: rest ∧ τ.getLast? = some x ∧ D_StkPath E s stk ∧ s ∈ τ ∧
    (∀ y ∈ stk, y ∈ τ) ∧ (∀ y ∈ τ, Relation.ReflTransGen E s y) ∧
    (∀ y ∈ τ, y ∉ stk → ∀ w, E y w → w ∈ τ) ∧
    (∀ y ∈ τ, y = s ∨ ∃ x ∈ τ, E x y) ∧
    stk.length + τ.length = 2 * τ.toFinset.card

lemma D_run_inv {E : Fin M → Fin M → Prop} {P : List (Fin M) → List (Fin M) → Fin M → Prop}
    (hP : ∀ τ stk v, P τ stk v → DFSNext E τ stk v) {s : Fin M} {m : ℕ}
    {τ stk : List (Fin M)} (h : Run E P s m τ stk) :
    D_Inv E s τ stk ∧ τ.length = m + 1 := by
  induction h with
  | zero =>
    refine ⟨⟨s, [], rfl, rfl, rfl, by simp, by simp, ?_, ?_, ?_, by simp⟩, rfl⟩
    · intro y hy; simp at hy; subst hy; exact Relation.ReflTransGen.refl
    · intro y hy hy'; exact absurd hy hy'
    · intro y hy; simp at hy; exact Or.inl hy
  | @fwd n τ rest x v hrun hPv hE hv ih =>
    obtain ⟨⟨x', rest', hstk, hlast, hpath, hs, hsub, hreach, hfin, hpar, hcnt⟩, hlen⟩ := ih
    obtain ⟨rfl, rfl⟩ := List.cons.inj hstk
    refine ⟨⟨v, x :: rest, rfl, by simp, ⟨hE, hpath⟩, by simp [hs], ?_, ?_, ?_, ?_, ?_⟩,
      by simp [hlen]⟩
    · intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | rfl | hy
      · simp
      · simp [hsub y (by simp)]
      · simp [hsub y (by simp [hy])]
    · intro y hy
      simp only [List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · exact hreach y hy
      · exact Relation.ReflTransGen.tail (hreach x (hsub x (by simp))) hE
    · intro y hy hy' w hw
      simp only [List.mem_append, List.mem_singleton] at hy
      simp only [List.mem_cons, not_or] at hy'
      rcases hy with hy | rfl
      · exact List.mem_append_left _ (hfin y hy (by simp [hy'.2.1, hy'.2.2]) w hw)
      · exact absurd rfl hy'.1
    · intro y hy
      simp only [List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · rcases hpar y hy with h | ⟨z, hz, hzy⟩
        · exact Or.inl h
        · exact Or.inr ⟨z, List.mem_append_left _ hz, hzy⟩
      · exact Or.inr ⟨x, List.mem_append_left _ (hsub x (by simp)), hE⟩
    · rw [D_toFinset_append_single, Finset.card_insert_of_notMem (by simpa using hv)]
      simp only [List.length_cons, List.length_append, List.length_nil] at hcnt ⊢
      omega
  | @back n τ rest x v hrun hPv hE ih =>
    obtain ⟨⟨x', rest', hstk, hlast, hpath, hs, hsub, hreach, hfin, hpar, hcnt⟩, hlen⟩ := ih
    obtain ⟨rfl, rfl⟩ := List.cons.inj hstk
    have hd := hP _ _ _ hPv
    rcases hd with hd | ⟨hall, hhead⟩
    · exact absurd hd hE
    cases rest with
    | nil => simp at hhead
    | cons y rest =>
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    have hyτ : y ∈ τ := hsub y (by simp)
    obtain ⟨_, hpath'⟩ := hpath
    refine ⟨⟨y, rest, rfl, by simp, hpath', by simp [hs], ?_, ?_, ?_, ?_, ?_⟩, by simp [hlen]⟩
    · intro z hz; exact List.mem_append_left _ (hsub z (by simp [hz]))
    · intro z hz
      simp only [List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | rfl
      · exact hreach z hz
      · exact hreach z hyτ
    · intro z hz hz' w hw
      have hzτ : z ∈ τ := by
        simp only [List.mem_append, List.mem_singleton] at hz
        rcases hz with hz | rfl
        · exact hz
        · exact hyτ
      by_cases hzx : z = x
      · subst hzx; exact List.mem_append_left _ (hall w hw)
      · refine List.mem_append_left _ (hfin z hzτ ?_ w hw)
        simp only [List.mem_cons, not_or] at hz' ⊢
        exact ⟨hzx, hz'⟩
    · intro z hz
      have hzτ : z ∈ τ := by
        simp only [List.mem_append, List.mem_singleton] at hz
        rcases hz with hz | rfl
        · exact hz
        · exact hyτ
      rcases hpar z hzτ with h | ⟨w, hw, hwz⟩
      · exact Or.inl h
      · exact Or.inr ⟨w, List.mem_append_left _ hw, hwz⟩
    · rw [D_toFinset_append_single, Finset.card_insert_of_mem (by simpa using hyτ)]
      simp only [List.length_cons, List.length_append, List.length_nil] at hcnt ⊢
      omega

/-! ## Existence of moves -/

lemma D_dm_exists_case1 {L : ℕ} {E : Fin M → Fin M → Prop} {g x : Fin M} {τ : List (Fin M)}
    (h : ∃ w, E x w ∧ w ∉ τ ∧ ReachAvoid E τ (L - 1) w g) :
    ∃ v, (E x v ∧ v ∉ τ ∧ ReachAvoid E τ (L - 1) v g) ∧
      ∀ w, E x w ∧ w ∉ τ ∧ ReachAvoid E τ (L - 1) w g →
        (∀ r, ReachAvoid E τ r w g → ReachAvoid E τ r v g) ∧
        ((∀ r, ReachAvoid E τ r v g → ReachAvoid E τ r w g) → v ≤ w) := by
  classical
  have hex : ∃ r, ∃ w, (E x w ∧ w ∉ τ ∧ ReachAvoid E τ (L - 1) w g) ∧ ReachAvoid E τ r w g := by
    obtain ⟨w, hw⟩ := h
    exact ⟨L - 1, w, hw, hw.2.2⟩
  obtain ⟨w0, hw0, hr0⟩ := Nat.find_spec hex
  have hex2 : ∃ k, ∃ w : Fin M, w.val = k ∧
      ((E x w ∧ w ∉ τ ∧ ReachAvoid E τ (L - 1) w g) ∧ ReachAvoid E τ (Nat.find hex) w g) :=
    ⟨w0.val, w0, rfl, hw0, hr0⟩
  obtain ⟨v, hvk, hvQ⟩ := Nat.find_spec hex2
  refine ⟨v, hvQ.1, fun w hw => ⟨fun r hr => ?_, fun hvw => ?_⟩⟩
  · have : Nat.find hex ≤ r := Nat.find_min' hex ⟨w, hw, hr⟩
    exact D_ra_mono hvQ.2 this
  · have := Nat.find_min' hex2 ⟨w, rfl, hw, hvw _ hvQ.2⟩
    rw [Fin.le_def]
    omega

lemma D_exists_min {E : Fin M → Fin M → Prop} {x : Fin M} {τ : List (Fin M)}
    (h : ∃ w, E x w ∧ w ∉ τ) : ∃ v, (E x v ∧ v ∉ τ) ∧ ∀ w, E x w ∧ w ∉ τ → v ≤ w := by
  classical
  have hex2 : ∃ k, ∃ w : Fin M, w.val = k ∧ (E x w ∧ w ∉ τ) := by
    obtain ⟨w, hw⟩ := h
    exact ⟨w.val, w, rfl, hw⟩
  obtain ⟨v, hvk, hvQ⟩ := Nat.find_spec hex2
  refine ⟨v, hvQ, fun w hw => ?_⟩
  have := Nat.find_min' hex2 ⟨w, rfl, hw⟩
  rw [Fin.le_def]
  omega

lemma D_run_step {L : ℕ} {E : Fin M → Fin M → Prop} {s g : Fin M} {m : ℕ} {τ : List (Fin M)}
    {x : Fin M} {rest : List (Fin M)} (h : Run E (DMMove L E g) s m τ (x :: rest)) {v : Fin M}
    (hv : DMMove L E g τ (x :: rest) v) :
    ∃ stk', Run E (DMMove L E g) s (m + 1) (τ ++ [v]) stk' := by
  by_cases hc : E x v ∧ v ∉ τ
  · exact ⟨_, Run.fwd h hv hc.1 hc.2⟩
  · exact ⟨_, Run.back h hv hc⟩

/-- Progress: while the goal is unvisited, the policy has a move. -/
lemma D_dm_progress {L : ℕ} {E : Fin M → Fin M → Prop} {s g : Fin M} {m : ℕ}
    {τ stk : List (Fin M)} (h : Run E (DMMove L E g) s m τ stk) (hg : g ∉ τ)
    (hreach : Relation.ReflTransGen E s g) :
    ∃ v stk', Run E (DMMove L E g) s (m + 1) (τ ++ [v]) stk' := by
  obtain ⟨⟨x, rest, rfl, hlast, hpath, hs, hsub, hreach', hfin, hpar, hcnt⟩, _⟩ :=
    D_run_inv (fun _ _ _ => D_dm_dfs) h
  suffices hv : ∃ v, DMMove L E g τ (x :: rest) v by
    obtain ⟨v, hv⟩ := hv
    exact ⟨v, D_run_step h hv⟩
  by_cases h1 : ∃ w, E x w ∧ w ∉ τ
  · by_cases h2 : ∃ w, E x w ∧ w ∉ τ ∧ ReachAvoid E τ (L - 1) w g
    · obtain ⟨v, hv⟩ := D_dm_exists_case1 h2
      exact ⟨v, Or.inl hv⟩
    · obtain ⟨v, hv⟩ := D_exists_min h1
      exact ⟨v, Or.inr (Or.inl ⟨h2, hv⟩)⟩
  · push Not at h1
    cases rest with
    | cons y rest => exact ⟨y, Or.inr (Or.inr ⟨h1, rfl⟩)⟩
    | nil =>
      exfalso
      simp only [D_StkPath] at hpath
      subst hpath
      have hall : ∀ z, Relation.ReflTransGen E x z → z ∈ τ := by
        intro z hz
        induction hz with
        | refl => exact hs
        | @tail b c _ hbc ih =>
          by_cases hb : b ∈ [x]
          · simp only [List.mem_singleton] at hb
            subst hb
            exact h1 c hbc
          · exact hfin b ih hb c hbc
      exact hg (hall g hreach)

lemma D_card_le {E : Fin M → Fin M → Prop} {s : Fin M} {τ : List (Fin M)}
    (hreach : ∀ y ∈ τ, Relation.ReflTransGen E s y) :
    τ.toFinset.card ≤ {v | Relation.ReflTransGen E s v}.ncard := by
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  intro y hy
  exact hreach y (by simpa using hy)

/-- The policy eventually reaches every reachable goal. -/
lemma D_dm_reaches {L : ℕ} {E : Fin M → Fin M → Prop} {s g : Fin M} (hgs : g ≠ s)
    (hreach : Relation.ReflTransGen E s g) :
    ∃ m τ stk, Run E (DMMove L E g) s m τ stk ∧ τ.getLast? = some g := by
  have key : ∀ k, (∃ m τ stk, Run E (DMMove L E g) s m τ stk ∧ τ.getLast? = some g) ∨
      (∃ τ stk, Run E (DMMove L E g) s k τ stk ∧ g ∉ τ) := by
    intro k
    induction k with
    | zero => exact Or.inr ⟨[s], [s], Run.zero, by simpa using hgs⟩
    | succ k ih =>
      rcases ih with ih | ⟨τ, stk, hrun, hg⟩
      · exact Or.inl ih
      · obtain ⟨v, stk', hrun'⟩ := D_dm_progress hrun hg hreach
        by_cases hv : v = g
        · subst hv
          exact Or.inl ⟨_, _, _, hrun', by simp⟩
        · exact Or.inr ⟨_, _, hrun', by simp [hg, Ne.symm hv]⟩
  rcases key (2 * {v | Relation.ReflTransGen E s v}.ncard) with h | ⟨τ, stk, hrun, _⟩
  · exact h
  · exfalso
    obtain ⟨⟨x, rest, rfl, -, -, -, -, hreach', -, -, hcnt⟩, hlen⟩ :=
      D_run_inv (fun _ _ _ => D_dm_dfs) hrun
    have := D_card_le hreach'
    simp only [List.length_cons] at hcnt
    omega

lemma D_movesTo_of_exists {E : Fin M → Fin M → Prop}
    {P : List (Fin M) → List (Fin M) → Fin M → Prop} {s g : Fin M}
    (h : ∃ m τ stk, Run E P s m τ stk ∧ τ.getLast? = some g) : ∃ m, MovesTo E P s g m := by
  classical
  exact ⟨Nat.find h, Nat.find_spec h,
    fun m' hm' τ stk hrun hlast => Nat.find_min h hm' ⟨τ, stk, hrun, hlast⟩⟩

/-- Upper bound on the number of moves at any time the current node is the goal. -/
lemma D_bound {E : Fin M → Fin M → Prop} {P : List (Fin M) → List (Fin M) → Fin M → Prop}
    (hP : ∀ τ stk v, P τ stk v → DFSNext E τ stk v) {s g : Fin M} {n d m : ℕ}
    {τ stk : List (Fin M)} (hn : {v | Relation.ReflTransGen E s v}.ncard = n)
    (hd : IsDist E s g d) (hrun : Run E P s m τ stk) (hlast : τ.getLast? = some g) :
    d ≤ m ∧ m + d + 2 ≤ 2 * n := by
  obtain ⟨⟨x, rest, rfl, hlast', hpath, -, -, hreach', -, -, hcnt⟩, hlen⟩ := D_run_inv hP hrun
  rw [hlast] at hlast'
  obtain rfl : g = x := Option.some.inj hlast'
  have hr := D_stkPath_reachLE hpath
  have hdr : d ≤ rest.length := by
    by_contra hc
    exact hd.2 _ (by omega) hr
  have h1 := D_card_le hreach'
  have h2 := List.toFinset_card_le τ
  simp only [List.length_cons] at hcnt
  omega

/-- If `dist(s, g) = d ≤ L`, the policy reaches `g` after exactly `d` moves. -/
lemma D_direct {L : ℕ} {E : Fin M → Fin M → Prop} {s g : Fin M} {d : ℕ}
    (hd : IsDist E s g d) (hdL : d ≤ L) :
    ∃ τ stk, Run E (DMMove L E g) s d τ stk ∧ τ.getLast? = some g := by
  have key : ∀ t ≤ d, ∃ τ x rest, Run E (DMMove L E g) s t τ (x :: rest) ∧
      τ.getLast? = some x ∧ (∀ y ∈ τ, ReachLE E t s y) ∧ ReachLE E (d - t) x g := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨[s], s, [], Run.zero, rfl, ?_, hd.1⟩
      intro y hy
      simp only [List.mem_singleton] at hy
      subst hy
      rfl
    | succ t ih =>
      intro ht
      obtain ⟨τ, x, rest, hrun, hlast, hτ, hxg⟩ := ih (by omega)
      have hxτ : x ∈ τ := List.mem_of_getLast? hlast
      have hτ' : ∀ y ∈ τ, ¬ ReachLE E (d - t - 1) y g := by
        intro y hy hyg
        exact hd.2 (t + (d - t - 1)) (by omega) (D_reachLE_trans (hτ y hy) hyg)
      rw [show d - t = (d - t - 1) + 1 by omega] at hxg
      rcases hxg with hxg | ⟨u, hxu, hug⟩
      · exact absurd hxg (hτ' x hxτ)
      have hra : ReachAvoid E τ (d - t - 1) u g := D_ra_of_reachLE hτ' hug
      have hqual : E x u ∧ u ∉ τ ∧ ReachAvoid E τ (L - 1) u g :=
        ⟨hxu, D_ra_not_mem hra, D_ra_mono hra (by omega)⟩
      obtain ⟨v, hv1, hv2⟩ := D_dm_exists_case1 ⟨u, hqual⟩
      have hrav : ReachAvoid E τ (d - t - 1) v g := (hv2 u hqual).1 _ hra
      refine ⟨τ ++ [v], v, x :: rest, Run.fwd hrun (Or.inl ⟨hv1, hv2⟩) hv1.1 hv1.2.1,
        by simp, ?_, ?_⟩
      · intro y hy
        simp only [List.mem_append, List.mem_singleton] at hy
        rcases hy with hy | rfl
        · exact D_reachLE_mono (hτ y hy)
        · exact D_reachLE_trans (hτ x hxτ) (show ReachLE E 1 x y from Or.inr ⟨y, hv1.1, rfl⟩)
      · rw [show d - (t + 1) = d - t - 1 by omega]
        exact D_ra_reachLE hrav
  obtain ⟨τ, x, rest, hrun, hlast, -, hxg⟩ := key d le_rfl
  simp only [Nat.sub_self, ReachLE] at hxg
  subst hxg
  exact ⟨τ, _, hrun, hlast⟩

lemma D_dist_pos {E : Fin M → Fin M → Prop} {s g : Fin M} {d : ℕ} (hgs : g ≠ s)
    (hd : IsDist E s g d) : 1 ≤ d := by
  rcases Nat.eq_zero_or_pos d with rfl | h
  · exact absurd hd.1.symm hgs
  · exact h

lemma D_moves_eq {L : ℕ} {E : Fin M → Fin M → Prop} {s g : Fin M} {n d m : ℕ}
    (hn : {v | Relation.ReflTransGen E s v}.ncard = n) (hd : IsDist E s g d) (hdL : d ≤ L)
    (hm : MovesTo E (DMMove L E g) s g m) : m = d := by
  obtain ⟨⟨τ, stk, hrun, hlast⟩, hmin⟩ := hm
  have h1 := (D_bound (fun _ _ _ => D_dm_dfs) hn hd hrun hlast).1
  obtain ⟨τ', stk', hrun', hlast'⟩ := D_direct hd hdL
  by_contra hne
  exact hmin d (by omega) τ' stk' hrun' hlast'

lemma D_effVal_le_one (L n : ℕ) : effVal L n ≤ 1 := by
  unfold effVal
  split_ifs with h
  · have h' : ((L : ℝ) + 2) ≤ n := by exact_mod_cast h
    rw [div_le_one (by linarith)]
    linarith
  · exact le_rfl

/-- First half of `WorstEff`. -/
lemma D_part1 {L n : ℕ} {E : Fin M → Fin M → Prop} {s g : Fin M} {d : ℕ}
    (hn : {v | Relation.ReflTransGen E s v}.ncard = n) (hgs : g ≠ s)
    (hreach : Relation.ReflTransGen E s g) (hd : IsDist E s g d) :
    (∃ m, MovesTo E (DMMove L E g) s g m) ∧
      ∀ m, MovesTo E (DMMove L E g) s g m → effVal L n ≤ (d : ℝ) / m := by
  refine ⟨D_movesTo_of_exists (D_dm_reaches hgs hreach), fun m hm => ?_⟩
  have hd1 := D_dist_pos hgs hd
  by_cases hdL : d ≤ L
  · rw [D_moves_eq hn hd hdL hm, div_self (by exact_mod_cast (by omega : d ≠ 0))]
    exact D_effVal_le_one L n
  · obtain ⟨⟨τ, stk, hrun, hlast⟩, -⟩ := hm
    obtain ⟨h1, h2⟩ := D_bound (fun _ _ _ => D_dm_dfs) hn hd hrun hlast
    have hLn : L + 2 ≤ n := by omega
    unfold effVal
    simp only [hLn, ↓reduceIte]
    have hdR : (L : ℝ) + 1 ≤ d := by exact_mod_cast (by omega : L + 1 ≤ d)
    have hmR : (d : ℝ) ≤ m := by exact_mod_cast h1
    have h2R : (m : ℝ) + d + 2 ≤ 2 * n := by exact_mod_cast h2
    have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd1
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith

/-! ## The tight instance: a distracting chain `0 → 1 → … → c` and the target path
`0 → c+1 → … → n-1` (`c = n - L - 2`). -/

/-- Edges of the tight instance. -/
def D_tE (n c : ℕ) (a b : Fin n) : Prop :=
  (b.val = a.val + 1 ∧ a.val ≠ c) ∨ (a.val = 0 ∧ b.val = c + 1)

/-- Depth in the tight instance (a tree). -/
def D_dep {n : ℕ} (c : ℕ) (a : Fin n) : ℕ := if a.val ≤ c then a.val else a.val - c

lemma D_dep_edge {n c : ℕ} (a b : Fin n) (h : D_tE n c a b) : D_dep c b = D_dep c a + 1 := by
  unfold D_dep
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> split_ifs <;> omega

lemma D_dep_reach {n c r : ℕ} {a b : Fin n} (h : ReachLE (D_tE n c) r a b) :
    D_dep c b ≤ D_dep c a + r := by
  induction r generalizing a with
  | zero => simp only [ReachLE] at h; subst h; simp
  | succ r ih =>
    rcases h with h | ⟨u, hu, h⟩
    · have := ih h; omega
    · have := ih h; have := D_dep_edge _ _ hu; omega

lemma D_t_reach_all {n c : ℕ} (s : Fin n) (hs : s.val = 0) (k : Fin n) :
    Relation.ReflTransGen (D_tE n c) s k := by
  obtain ⟨k, hk⟩ := k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · have : s = ⟨0, hk⟩ := Fin.ext hs
      rw [this]
    · by_cases hkc : k = c + 1
      · subst hkc
        exact Relation.ReflTransGen.single (Or.inr ⟨hs, rfl⟩)
      · exact Relation.ReflTransGen.tail (ih (k - 1) (by omega) (by omega))
          (Or.inl ⟨by simp; omega, by simp; omega⟩)

lemma D_t_ncard {n c : ℕ} (s : Fin n) (hs : s.val = 0) :
    {v | Relation.ReflTransGen (D_tE n c) s v}.ncard = n := by
  have : {v | Relation.ReflTransGen (D_tE n c) s v} = Set.univ :=
    Set.eq_univ_of_forall (fun k => D_t_reach_all s hs k)
  rw [this, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

lemma D_t_path {n c L : ℕ} (hcL : c + L + 2 = n) (g : Fin n) (hg : g.val = n - 1) :
    ∀ j ≤ L, ∀ y : Fin n, y.val = n - 1 - j → ReachLE (D_tE n c) j y g := by
  intro j
  induction j with
  | zero =>
    intro _ y hy
    exact Fin.ext (by omega)
  | succ j ih =>
    intro hj y hy
    exact Or.inr ⟨⟨n - 1 - j, by omega⟩, Or.inl ⟨by simp; omega, by omega⟩,
      ih (by omega) _ rfl⟩

lemma D_t_dist {n c L : ℕ} (hcL : c + L + 2 = n) (s g : Fin n) (hs : s.val = 0)
    (hg : g.val = n - 1) : IsDist (D_tE n c) s g (L + 1) := by
  refine ⟨Or.inr ⟨⟨c + 1, by omega⟩, Or.inr ⟨hs, rfl⟩, D_t_path hcL g hg L le_rfl _ ?_⟩, ?_⟩
  · simp; omega
  · intro r hr h
    have := D_dep_reach h
    simp only [D_dep] at this
    split_ifs at this <;> omega

/-- In the tight instance, the target branch is entered only after the whole distracting chain
has been explored. -/
lemma D_t_J {n c L : ℕ} (hL : 1 ≤ L) (hcL : c + L + 2 = n) (s g : Fin n) (hs0 : s.val = 0)
    (hg : g.val = n - 1) {m : ℕ} {τ stk : List (Fin n)}
    (h : Run (D_tE n c) (DMMove L (D_tE n c) g) s m τ stk) :
    ∀ y ∈ τ, y.val = c + 1 → ∀ k : Fin n, k.val ≤ c → k ∈ τ := by
  induction h with
  | zero =>
    intro y hy hyc
    simp only [List.mem_singleton] at hy
    subst hy
    omega
  | @fwd m τ rest x v hrun hPv hE hv ih =>
    intro y hy hyc k hk
    simp only [List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | rfl
    · exact List.mem_append_left _ (ih y hy hyc k hk)
    apply List.mem_append_left
    obtain ⟨⟨x', rest', hstk, -, hpath, hs, -, -, hfin, -, -⟩, -⟩ :=
      D_run_inv (fun _ _ _ => D_dm_dfs) hrun
    obtain ⟨rfl, rfl⟩ := List.cons.inj hstk
    have hx0 : x.val = 0 := by
      rcases hE with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · omega
      · exact h1
    by_cases hc0 : c = 0
    · have : k = s := Fin.ext (by omega)
      rw [this]
      exact hs
    have h1τ : (⟨1, by omega⟩ : Fin n) ∈ τ := by
      by_contra h1
      rcases hPv with ⟨⟨_, _, hra⟩, _⟩ | ⟨_, _, hmin⟩ | ⟨hall, _⟩
      · have := D_dep_reach (D_ra_reachLE hra)
        simp only [D_dep] at this
        split_ifs at this <;> omega
      · have := hmin ⟨1, by omega⟩ ⟨Or.inl ⟨by simp [hx0], by omega⟩, h1⟩
        rw [Fin.le_def] at this
        simp at this
        omega
      · exact hv (hall _ hE)
    have hrest : rest = [] := by
      have := D_stkPath_pot (D_dep c) D_dep_edge hpath
      simp only [D_dep] at this
      split_ifs at this <;> first | omega | (apply List.eq_nil_of_length_eq_zero; omega)
    subst hrest
    have hchain : ∀ j, 1 ≤ j → (hj : j ≤ c) → (⟨j, by omega⟩ : Fin n) ∈ τ := by
      intro j
      induction j with
      | zero => intro h; omega
      | succ j ih =>
        intro _ hj
        rcases Nat.eq_zero_or_pos j with rfl | hjpos
        · exact h1τ
        · have hjτ := ih hjpos (by omega)
          refine hfin _ hjτ ?_ _ (Or.inl ⟨rfl, by simp; omega⟩)
          simp only [List.mem_singleton]
          intro heq
          have := congrArg Fin.val heq
          simp at this
          omega
    rcases Nat.eq_zero_or_pos k.val with hk0 | hkpos
    · have : k = s := Fin.ext (by omega)
      rw [this]
      exact hs
    · have := hchain k.val hkpos hk
      exact this
  | @back m τ rest x v hrun hPv hE ih =>
    intro y hy hyc k hk
    obtain ⟨⟨x', rest', hstk, -, -, -, hsub, -, -, -, -⟩, -⟩ :=
      D_run_inv (fun _ _ _ => D_dm_dfs) hrun
    obtain ⟨rfl, rfl⟩ := List.cons.inj hstk
    have hvτ : v ∈ τ := by
      rcases D_dm_dfs hPv with hd | ⟨_, hhead⟩
      · exact absurd hd hE
      · exact hsub v (List.mem_cons_of_mem _ (List.mem_of_head? hhead))
    have hyτ : y ∈ τ := by
      simp only [List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · exact hy
      · exact hvτ
    exact List.mem_append_left _ (ih y hyτ hyc k hk)

/-- In the tight instance, the goal is reached after exactly `2n - L - 3` moves. -/
lemma D_t_moves {n c L : ℕ} (hL : 1 ≤ L) (hcL : c + L + 2 = n) (s g : Fin n) (hs0 : s.val = 0)
    (hg : g.val = n - 1) {m : ℕ} (hm : MovesTo (D_tE n c) (DMMove L (D_tE n c) g) s g m) :
    m + L + 3 = 2 * n := by
  obtain ⟨⟨τ, stk, hrun, hlast⟩, -⟩ := hm
  obtain ⟨⟨x, rest, rfl, hlast', hpath, -, -, -, -, hpar, hcnt⟩, hlen⟩ :=
    D_run_inv (fun _ _ _ => D_dm_dfs) hrun
  rw [hlast] at hlast'
  obtain rfl : g = x := Option.some.inj hlast'
  have hgτ : g ∈ τ := List.mem_of_getLast? hlast
  have hdepth := D_stkPath_pot (D_dep c) D_dep_edge hpath
  simp only [D_dep] at hdepth
  have hrl : rest.length = L + 1 := by split_ifs at hdepth <;> omega
  have hdown : ∀ j ≤ L, ∀ y : Fin n, y.val = n - 1 - j → y ∈ τ := by
    intro j
    induction j with
    | zero =>
      intro _ y hy
      have : y = g := Fin.ext (by omega)
      rw [this]; exact hgτ
    | succ j ih =>
      intro hj y hy
      have hz := ih (by omega) ⟨n - 1 - j, by omega⟩ rfl
      rcases hpar _ hz with hzs | ⟨w, hw, hwz⟩
      · have := congrArg Fin.val hzs
        simp at this
        omega
      · have : w = y := by
          rcases hwz with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Fin.ext (by simp at h1; omega)
          · simp at h2; omega
        rw [← this]; exact hw
  have hJ := D_t_J hL hcL s g hs0 hg hrun
  have hall : ∀ k : Fin n, k ∈ τ := by
    intro k
    by_cases hk : k.val ≤ c
    · exact hJ ⟨c + 1, by omega⟩ (hdown L le_rfl _ (by simp; omega)) rfl k hk
    · exact hdown (n - 1 - k.val) (by omega) k (by omega)
  have huniv : τ.toFinset = Finset.univ :=
    Finset.eq_univ_of_forall (fun k => List.mem_toFinset.mpr (hall k))
  rw [huniv, Finset.card_univ, Fintype.card_fin] at hcnt
  simp only [List.length_cons] at hcnt
  omega

/-! ## The star instance (ratio one) -/

def D_sE (n : ℕ) (a b : Fin n) : Prop := a.val = 0 ∧ b.val ≠ 0

lemma D_s_ncard {n : ℕ} (s : Fin n) (hs : s.val = 0) :
    {v | Relation.ReflTransGen (D_sE n) s v}.ncard = n := by
  have : {v | Relation.ReflTransGen (D_sE n) s v} = Set.univ := by
    refine Set.eq_univ_of_forall (fun k => ?_)
    by_cases hk : k.val = 0
    · have : k = s := Fin.ext (by omega)
      rw [this]
      exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨hs, hk⟩
  rw [this, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

/-! ## Main theorems -/

/-- **Lemma `lem:lookahead-efficiency`.** For `L ≥ 1` and `n ≥ 2`, the worst-case efficiency of the
distance-minimizing `L`-look-ahead policy is `(L+1)/(2n-L-3)` if `n ≥ L + 2` and `1` otherwise. -/
theorem dm_efficiency (L n : ℕ) (hL : 1 ≤ L) (hn : 2 ≤ n) : WorstEff L n (effVal L n) := by
  refine ⟨fun M E s g d hcard hgs hreach hd => D_part1 hcard hgs hreach hd, ?_⟩
  by_cases hLn : L + 2 ≤ n
  · set c := n - L - 2 with _hc
    have hcL : c + L + 2 = n := by omega
    let s : Fin n := ⟨0, by omega⟩
    let g : Fin n := ⟨n - 1, by omega⟩
    have hcard := D_t_ncard (c := c) s rfl
    have hgs : g ≠ s := fun h => by have := congrArg Fin.val h; simp [s, g] at this; omega
    have hdist := D_t_dist hcL s g rfl rfl
    have hreach := D_t_reach_all (c := c) s rfl g
    obtain ⟨m, hm⟩ := (D_part1 (L := L) hcard hgs hreach hdist).1
    have hmn := D_t_moves hL hcL s g rfl rfl hm
    refine ⟨n, D_tE n c, s, g, L + 1, m, hcard, hgs, hreach, hdist, hm, ?_⟩
    unfold effVal
    simp only [hLn, ↓reduceIte]
    have hmR : (m : ℝ) + L + 3 = 2 * n := by exact_mod_cast hmn
    push_cast
    congr 1
    linarith
  · let s : Fin n := ⟨0, by omega⟩
    let g : Fin n := ⟨1, by omega⟩
    have hcard := D_s_ncard s rfl
    have hgs : g ≠ s := fun h => by have := congrArg Fin.val h; simp [s, g] at this
    have hdist : IsDist (D_sE n) s g 1 := by
      refine ⟨Or.inr ⟨g, ⟨rfl, by simp [g]⟩, rfl⟩, fun r hr h => ?_⟩
      obtain rfl : r = 0 := by omega
      exact hgs h.symm
    have hreach : Relation.ReflTransGen (D_sE n) s g := Relation.ReflTransGen.single ⟨rfl, by simp [g]⟩
    obtain ⟨m, hm⟩ := (D_part1 (L := L) hcard hgs hreach hdist).1
    have hm1 := D_moves_eq hcard hdist hL hm
    refine ⟨n, D_sE n, s, g, 1, m, hcard, hgs, hreach, hdist, hm, ?_⟩
    unfold effVal
    simp [hLn, hm1]


/-- **Corollary `cor:k-layer-efficiency`** (`L = 1 + 2^{k-3}`). -/
theorem k_layer_efficiency (k n : ℕ) (hk : 3 ≤ k) (hn : 2 ≤ n) :
    WorstEff (1 + 2 ^ (k - 3)) n
      (if 2 ^ (k - 3) + 3 ≤ n then ((2 : ℝ) ^ (k - 3) + 2) / (2 * (n : ℝ) - 2 ^ (k - 3) - 4)
       else 1) := by
  have h := dm_efficiency (1 + 2 ^ (k - 3)) n (Nat.le_add_right _ _) hn
  convert h using 1
  unfold effVal
  have hiff : (2 ^ (k - 3) + 3 ≤ n) ↔ (1 + 2 ^ (k - 3) + 2 ≤ n) := by omega
  by_cases hc : 2 ^ (k - 3) + 3 ≤ n
  · have hc' := hiff.mp hc
    simp only [hc, hc', ↓reduceIte]
    push_cast
    congr 1 <;> ring
  · have hc' : ¬ (1 + 2 ^ (k - 3) + 2 ≤ n) := fun h => hc (hiff.mpr h)
    simp only [hc, hc', ↓reduceIte]


end DFSExpr
