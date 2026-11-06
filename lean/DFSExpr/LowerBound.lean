import DFSExpr.Defs

noncomputable section

open Matrix

namespace DFSExpr

variable {N : ℕ}

/-! ### Normal form of `logitsRd` -/

section NormalForm

variable {d H dk dv : ℕ}

/-- Embedded token at position `j` (zero outside the input). -/
def A_x (tf : OneLayerTF N d H dk dv) (toks : List (Tok N × Role)) (j : ℕ) : Fin d → ℝ :=
  match toks[j]? with
  | some tr => tf.emb tr.1 tr.2 j
  | none => 0

/-- Rounded attention weight of a key `xj` for the query `xT`. -/
def A_wt (tf : OneLayerTF N d H dk dv) (φ : ℝ → ℝ) (rd : Rounding H dk dv d) (h : Fin H)
    (xT xj : Fin d → ℝ) : ℝ :=
  rd.wt h (φ (∑ a, rd.K h a ((tf.K h *ᵥ xj) a) * rd.Q h a ((tf.Q h *ᵥ xT) a)))

/-- Rounded numerator summand. -/
def A_term (tf : OneLayerTF N d H dk dv) (φ : ℝ → ℝ) (rd : Rounding H dk dv d) (h : Fin H)
    (xT xj : Fin d → ℝ) (c : Fin dv) : ℝ :=
  rd.sum h c (A_wt tf φ rd h xT xj * rd.V h c ((tf.V h *ᵥ xj) c))

/-- The logits as a function of the last embedding and the accumulated numerators/normalizers. -/
def A_out (tf : OneLayerTF N d H dk dv) (normalized : Bool) (rd : Rounding H dk dv d)
    (xT : Fin d → ℝ) (num : Fin H → Fin dv → ℝ) (den : Fin H → ℝ) (w : Tok N) : ℝ :=
  ∑ a, tf.R a w * (xT a + max (rd.O a ((tf.O *ᵥ fun hc : Fin H × Fin dv =>
    rd.head hc.1 hc.2 (if normalized then num hc.1 hc.2 / den hc.1 else num hc.1 hc.2)) a)) 0)

lemma A_logitsRd_eq (tf : OneLayerTF N d H dk dv) (φ : ℝ → ℝ) (normalized : Bool)
    (rd : Rounding H dk dv d) (toks : List (Tok N × Role)) (T : ℕ) (hT : toks.length = T)
    (xT : Fin d → ℝ) (hxT : A_x tf toks (T - 1) = xT) (w : Tok N) :
    tf.logitsRd φ normalized rd toks w =
      A_out tf normalized rd xT
        (fun h c => ∑ j ∈ Finset.range T, A_term tf φ rd h xT (A_x tf toks j) c)
        (fun h => ∑ j ∈ Finset.range T, A_wt tf φ rd h xT (A_x tf toks j)) w := by
  subst hT hxT
  rfl

end NormalForm


/-! ### Positions of the prompt -/

section Lists

/-- The prompt `<s>, edges, suffix`. -/
def A_inp (es : List (Fin N × Fin N)) (suf : List (Tok N × Role)) : List (Tok N × Role) :=
  (Tok.bos, Role.graph) :: edgeToks es ++ suf

lemma A_edgeToks_cons (e : Fin N × Fin N) (es : List (Fin N × Fin N)) :
    edgeToks (e :: es) = (Tok.node e.1, Role.graph) :: (Tok.node e.2, Role.graph) ::
      (Tok.sep, Role.graph) :: edgeToks es := by
  simp [edgeToks]

lemma A_edgeToks_length (es : List (Fin N × Fin N)) : (edgeToks es).length = 3 * es.length := by
  induction es with
  | nil => simp [edgeToks]
  | cons e es ih => rw [A_edgeToks_cons]; simp [ih]; ring

lemma A_edgeToks_src (es1 es2 : List (Fin N × Fin N)) (h : es1.map Prod.fst = es2.map Prod.fst)
    (suf : List (Tok N × Role)) (j : ℕ) (hj : ∀ k < es1.length, j ≠ 3 * k + 1) :
    (edgeToks es1 ++ suf)[j]? = (edgeToks es2 ++ suf)[j]? := by
  induction es1 generalizing es2 j with
  | nil =>
    cases es2 with
    | nil => rfl
    | cons e es => simp at h
  | cons e1 r1 ih =>
    cases es2 with
    | nil => simp at h
    | cons e2 r2 =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [A_edgeToks_cons, A_edgeToks_cons]
      match j, hj with
      | 0, _ => simp [h1]
      | 1, hj => exact absurd rfl (hj 0 (by simp))
      | 2, _ => simp
      | j + 3, hj =>
        simp only [List.cons_append, List.getElem?_cons_succ]
        apply ih r2 h2 j
        intro k hk hjk
        exact hj (k + 1) (by simp; omega) (by omega)

lemma A_edgeToks_tgt (es : List (Fin N × Fin N)) (suf : List (Tok N × Role)) (k : ℕ)
    (s t : Fin N) (h : es[k]? = some (s, t)) :
    (edgeToks es ++ suf)[3 * k + 1]? = some (Tok.node t, Role.graph) := by
  induction es generalizing k with
  | nil => simp at h
  | cons e r ih =>
    rw [A_edgeToks_cons]
    cases k with
    | zero => simp at h; simp [h]
    | succ k =>
      simp only [List.getElem?_cons_succ] at h
      have : 3 * (k + 1) + 1 = (3 * k + 1) + 3 := by ring
      rw [this]
      simp only [List.cons_append, List.getElem?_cons_succ]
      exact ih k h

lemma A_edgeToks_suf (es : List (Fin N × Fin N)) (suf : List (Tok N × Role)) (j : ℕ)
    (hj : 3 * es.length ≤ j) :
    (edgeToks es ++ suf)[j]? = suf[j - 3 * es.length]? := by
  rw [List.getElem?_append_right (by rw [A_edgeToks_length]; exact hj), A_edgeToks_length]

lemma A_inp_length (es : List (Fin N × Fin N)) (suf : List (Tok N × Role)) :
    (A_inp es suf).length = 3 * es.length + 1 + suf.length := by
  simp [A_inp, A_edgeToks_length]; ring

lemma A_inp_zero (es : List (Fin N × Fin N)) (suf : List (Tok N × Role)) :
    (A_inp es suf)[0]? = some (Tok.bos, Role.graph) := by
  simp [A_inp]

lemma A_inp_succ (es : List (Fin N × Fin N)) (suf : List (Tok N × Role)) (j : ℕ) :
    (A_inp es suf)[j + 1]? = (edgeToks es ++ suf)[j]? := by
  simp [A_inp]

end Lists

section XLemmas

variable {d H dk dv : ℕ}

lemma A_x_congr (tf : OneLayerTF N d H dk dv) (toks1 toks2 : List (Tok N × Role)) (j : ℕ)
    (h : toks1[j]? = toks2[j]?) : A_x tf toks1 j = A_x tf toks2 j := by
  simp only [A_x, h]

lemma A_x_some (tf : OneLayerTF N d H dk dv) (toks : List (Tok N × Role)) (j : ℕ)
    (tr : Tok N × Role) (h : toks[j]? = some tr) : A_x tf toks j = tf.emb tr.1 tr.2 j := by
  simp only [A_x, h]

end XLemmas

/-! ### Counting -/

lemma A_sum_split (M T : ℕ) (hT : 3 * M ≤ T) (G : ℕ → ℝ) :
    ∑ j ∈ Finset.range T, G j =
      ∑ k : Fin M, G (3 * k + 2) +
        ∑ j ∈ Finset.range T \ (Finset.univ.image fun k : Fin M => 3 * (k : ℕ) + 2), G j := by
  have hsub : (Finset.univ.image fun k : Fin M => 3 * (k : ℕ) + 2) ⊆ Finset.range T := by
    intro j hj
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hj
    obtain ⟨k, rfl⟩ := hj
    have := k.2
    simp only [Finset.mem_range]; omega
  rw [← Finset.sum_sdiff hsub, Finset.sum_image]
  · ring
  · intro a _ b _ hab
    exact Fin.ext (by simp only at hab; omega)

lemma A_sum_fixed {M p : ℕ} {ε : ℝ} (u : Fin M → ℝ) (hu : ∀ k, u k ∈ FixedPt p ε) :
    ∃ z : ℤ, |z| ≤ M * 2 ^ p ∧ ∑ k, u k = z * ε := by
  simp only [FixedPt, Set.mem_ofPred_eq] at hu
  choose z hz hzu using hu
  refine ⟨∑ k, z k, ?_, ?_⟩
  · calc |∑ k, z k| ≤ ∑ k, |z k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin M, (2 : ℤ) ^ p := Finset.sum_le_sum fun k _ => hz k
      _ = M * 2 ^ p := by simp
  · rw [Finset.sum_congr rfl fun k _ => hzu k]; push_cast; rw [Finset.sum_mul]

lemma A_card_S (M p : ℕ) (ε : ℝ) (hp : 2 * M + 1 ≤ 2 ^ p) :
    ((Finset.Icc (-((M : ℤ) * 2 ^ p)) ((M : ℤ) * 2 ^ p)).image
      fun z : ℤ => (z : ℝ) * ε).card ≤ 2 ^ (2 * p) := by
  refine (Finset.card_image_le).trans ?_
  rw [Int.card_Icc]
  have h1 : ((M : ℤ) * 2 ^ p + 1 - -((M : ℤ) * 2 ^ p)).toNat = 2 * M * 2 ^ p + 1 := by
    have : (M : ℤ) * 2 ^ p + 1 - -((M : ℤ) * 2 ^ p) = ((2 * M * 2 ^ p + 1 : ℕ) : ℤ) := by
      push_cast; ring
    rw [this, Int.toNat_natCast]
  rw [h1, two_mul p, pow_add]
  have h2 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  calc 2 * M * 2 ^ p + 1 ≤ (2 * M + 1) * 2 ^ p := by nlinarith
    _ ≤ 2 ^ p * 2 ^ p := Nat.mul_le_mul_right _ hp

/-! ### The core counting argument -/

section Core

variable {d H dk dv : ℕ}

/-- Alice's message: the numerators and normalizers accumulated over her positions. -/
def A_msg (tf : OneLayerTF N d H dk dv) (φ : ℝ → ℝ) (rd : Rounding H dk dv d) (xT : Fin d → ℝ) {M : ℕ}
    (y : Fin M → Fin d → ℝ) : Fin H × Option (Fin dv) → ℝ := fun hc =>
  match hc.2 with
  | some c => ∑ k, A_term tf φ rd hc.1 xT (y k) c
  | none => ∑ k, A_wt tf φ rd hc.1 xT (y k)

/-- Core of the reduction: a family of prompts `<s>, edges, suffix` indexed by Alice's input `f`
and Bob's index `i`, where the sources depend only on `i`, the target of record `k` only on
`f k`, and the correct answer at `(f, i)` determines `f i`. -/
theorem A_core {M p : ℕ} (tf : OneLayerTF N d H dk dv)
    (φ : ℝ → ℝ) (normalized : Bool) (rd : Rounding H dk dv d)
    (hrd : rd.IsFixed p) (hdv : dv ≤ d) (hp : 2 * M + 1 ≤ 2 ^ p)
    (suf : List (Tok N × Role)) (hsuf : suf ≠ [])
    (es : (Fin M → Bool) → Fin M → List (Fin N × Fin N))
    (hlen : ∀ f i, (es f i).length = M)
    (hsrc : ∀ f f' i, (es f i).map Prod.fst = (es f' i).map Prod.fst)
    (g : Fin M → Bool → Fin N)
    (htgt : ∀ f i (k : Fin M), ∃ s, (es f i)[(k : ℕ)]? = some (s, g k (f k)))
    (hg : ∀ k b b', g k b = g k b' → b = b')
    (hcorr : ∀ f i w, IsMax (tf.logitsRd φ normalized rd (A_inp (es f i) suf)) w →
      w = .node (g i (f i))) :
    M ≤ 4 * H * d * p := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · simp [hM]
  have : Nonempty (Tok N) := ⟨.bos⟩
  -- the width is positive
  have hd : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · exfalso
      subst hd
      have := hcorr (fun _ => false) ⟨0, hM⟩ .bos (fun w' => by simp [OneLayerTF.logitsRd])
      cases this
    · exact hd
  have hsl : 1 ≤ suf.length := by
    rcases suf with _ | ⟨a, s⟩
    · exact absurd rfl hsuf
    · simp
  have hLlen : ∀ f i, (A_inp (es f i) suf).length = 3 * M + 1 + suf.length := by
    intro f i; rw [A_inp_length, hlen]
  -- the last token is public
  have hxT : ∀ f i, A_x tf (A_inp (es f i) suf) (3 * M + 1 + suf.length - 1) =
      A_x tf (A_inp (es (fun _ => false) ⟨0, hM⟩) suf) (3 * M + 1 + suf.length - 1) := by
    intro f i
    apply A_x_congr
    have : 3 * M + 1 + suf.length - 1 = (3 * M + suf.length - 1) + 1 := by omega
    rw [this, A_inp_succ, A_inp_succ, A_edgeToks_suf _ _ _ (by rw [hlen]; omega),
      A_edgeToks_suf _ _ _ (by rw [hlen]; omega), hlen, hlen]
  set xT := A_x tf (A_inp (es (fun _ => false) ⟨0, hM⟩) suf) (3 * M + 1 + suf.length - 1)
    with hxTdef
  -- Alice's positions
  have hAx : ∀ f i (k : Fin M), A_x tf (A_inp (es f i) suf) (3 * k + 2) =
      tf.emb (.node (g k (f k))) .graph (3 * k + 2) := by
    intro f i k
    obtain ⟨s, hs⟩ := htgt f i k
    refine A_x_some tf _ _ (Tok.node (g k (f k)), Role.graph) ?_
    rw [show 3 * (k : ℕ) + 2 = (3 * k + 1) + 1 by ring, A_inp_succ]
    exact A_edgeToks_tgt _ _ _ _ _ hs
  -- Bob's positions
  have hBx : ∀ f f' i j, j ∉ (Finset.univ.image fun k : Fin M => 3 * (k : ℕ) + 2) →
      A_x tf (A_inp (es f i) suf) j = A_x tf (A_inp (es f' i) suf) j := by
    intro f f' i j hj
    apply A_x_congr
    rcases j with _ | j
    · rw [A_inp_zero, A_inp_zero]
    · rw [A_inp_succ, A_inp_succ]
      apply A_edgeToks_src _ _ (hsrc f f' i)
      intro k hk hjk
      apply hj
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨k, by rw [hlen] at hk; exact hk⟩, by simp only; omega⟩
  -- the message
  let msg : (Fin M → Bool) → Fin H × Option (Fin dv) → ℝ := fun f =>
    A_msg tf φ rd xT (fun k => tf.emb (.node (g k (f k))) .graph (3 * k + 2))
  have hlog : ∀ f f', msg f = msg f' → ∀ i w,
      tf.logitsRd φ normalized rd (A_inp (es f i) suf) w =
        tf.logitsRd φ normalized rd (A_inp (es f' i) suf) w := by
    intro f f' hff' i w
    rw [A_logitsRd_eq tf φ normalized rd _ _ (hLlen f i) xT (hxT f i),
      A_logitsRd_eq tf φ normalized rd _ _ (hLlen f' i) xT (hxT f' i)]
    have key : ∀ F : (Fin d → ℝ) → ℝ,
        ∑ k : Fin M, F (tf.emb (.node (g k (f k))) .graph (3 * k + 2)) =
          ∑ k : Fin M, F (tf.emb (.node (g k (f' k))) .graph (3 * k + 2)) →
        ∑ j ∈ Finset.range (3 * M + 1 + suf.length), F (A_x tf (A_inp (es f i) suf) j) =
          ∑ j ∈ Finset.range (3 * M + 1 + suf.length), F (A_x tf (A_inp (es f' i) suf) j) := by
      intro F hF
      rw [A_sum_split M _ (by omega) (fun j => F (A_x tf (A_inp (es f i) suf) j)),
        A_sum_split M _ (by omega) (fun j => F (A_x tf (A_inp (es f' i) suf) j))]
      simp only [hAx]
      rw [hF]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [hBx f f' i j (Finset.mem_sdiff.1 hj).2]
    congr 1
    · funext h c
      exact key (fun x => A_term tf φ rd h xT x c) (congrFun hff' (h, some c))
    · funext h
      exact key (fun x => A_wt tf φ rd h xT x) (congrFun hff' (h, none))
  have hinj : Function.Injective msg := by
    intro f f' hff'
    funext i
    obtain ⟨w, hw⟩ := Finite.exists_max (tf.logitsRd φ normalized rd (A_inp (es f i) suf))
    have h1 := hcorr f i w hw
    have h2 := hcorr f' i w (fun w' => by
      rw [← hlog f f' hff' i w', ← hlog f f' hff' i w]; exact hw w')
    rw [h1] at h2
    exact hg i _ _ (Tok.node.inj h2)
  -- counting: each message coordinate lies in its own finite set of fixed-point values
  obtain ⟨hwt, hsum⟩ := hrd
  choose εw hεw using hwt
  choose εs hεs using hsum
  let εc : Fin H × Option (Fin dv) → ℝ := fun hc =>
    match hc.2 with
    | some c => εs hc.1 c
    | none => εw hc.1
  let S : Fin H × Option (Fin dv) → Finset ℝ := fun hc =>
    (Finset.Icc (-((M : ℤ) * 2 ^ p)) ((M : ℤ) * 2 ^ p)).image fun z : ℤ => (z : ℝ) * εc hc
  have hmemS : ∀ hc (u : Fin M → ℝ), (∀ k, u k ∈ FixedPt p (εc hc)) → ∑ k, u k ∈ S hc := by
    intro hc u hu
    obtain ⟨z, hz, hsum⟩ := A_sum_fixed u hu
    rw [hsum, Finset.mem_image]
    exact ⟨z, Finset.mem_Icc.2 (abs_le.1 hz), rfl⟩
  have hmem : ∀ f hc, msg f hc ∈ S hc := by
    intro f ⟨h, c⟩
    cases c with
    | some c => exact hmemS (h, some c) _ fun k => hεs h c _
    | none => exact hmemS (h, none) _ fun k => hεw h _
  have hcard : (Finset.univ : Finset (Fin M → Bool)).card ≤ (Fintype.piFinset S).card :=
    Finset.card_le_card_of_injOn msg (fun f _ => Fintype.mem_piFinset.2 (hmem f))
      hinj.injOn
  have hprod : (Fintype.piFinset S).card ≤ (2 ^ (2 * p)) ^ (H * (dv + 1)) := by
    rw [Fintype.card_piFinset]
    calc ∏ hc, (S hc).card ≤ (2 ^ (2 * p)) ^ (Finset.univ : Finset (Fin H × Option (Fin dv))).card :=
          Finset.prod_le_pow_card _ _ _ fun hc _ => A_card_S M p (εc hc) hp
      _ = _ := by
          rw [Finset.card_univ, Fintype.card_prod, Fintype.card_option, Fintype.card_fin,
            Fintype.card_fin]
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hcard
  have h2 : 2 ^ M ≤ 2 ^ (2 * p * (H * (dv + 1))) := by
    calc 2 ^ M ≤ (2 ^ (2 * p)) ^ (H * (dv + 1)) := hcard.trans hprod
      _ = _ := by rw [← pow_mul]
  have h3 : M ≤ 2 * p * (H * (dv + 1)) := (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
  calc M ≤ 2 * p * (H * (dv + 1)) := h3
    _ ≤ 2 * p * (H * (2 * d)) := by gcongr; omega
    _ = 4 * H * d * p := by ring

end Core

/-! ### The hard family (row–column encoding) -/

section Family

variable {m M : ℕ}

lemma A_m_pos (hMm : M ≤ m * m) (k : Fin M) : 0 < m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; have := k.2; simp at hMm; omega
  · exact h

/-- The query vertex `q = 0`. -/
def A_q (hN : 3 * m + 1 ≤ N) : Fin N := ⟨0, by omega⟩

/-- Source of record `k` when Bob's index is `i`: `q` for the selected record, else the row
vertex `a_{k / m} = 1 + k / m`. -/
def A_src (hMm : M ≤ m * m) (hN : 3 * m + 1 ≤ N) (i k : Fin M) : Fin N :=
  if k = i then A_q hN
  else ⟨1 + k / m, by have := Nat.div_lt_of_lt_mul (lt_of_lt_of_le k.2 hMm); omega⟩

/-- Target of record `k` with Alice's bit `b`: `b_{k % m, b} = 1 + m + 2 (k % m) + b`. -/
def A_tgt (hMm : M ≤ m * m) (hN : 3 * m + 1 ≤ N) (k : Fin M) (b : Bool) : Fin N :=
  ⟨1 + m + 2 * (k % m) + (if b then 1 else 0), by
    have := Nat.mod_lt k (A_m_pos hMm k); split <;> omega⟩

/-- The edge list of the hard instance `(f, i)`. -/
def A_es (hMm : M ≤ m * m) (hN : 3 * m + 1 ≤ N) (f : Fin M → Bool) (i : Fin M) :
    List (Fin N × Fin N) :=
  List.ofFn fun k => (A_src hMm hN i k, A_tgt hMm hN k (f k))

variable (hMm : M ≤ m * m) (hN : 3 * m + 1 ≤ N)

lemma A_es_length (f : Fin M → Bool) (i : Fin M) : (A_es hMm hN f i).length = M := by
  simp [A_es]

lemma A_es_src (f f' : Fin M → Bool) (i : Fin M) :
    (A_es hMm hN f i).map Prod.fst = (A_es hMm hN f' i).map Prod.fst := by
  simp [A_es, List.map_ofFn, Function.comp_def]

lemma A_es_get (f : Fin M → Bool) (i k : Fin M) :
    (A_es hMm hN f i)[(k : ℕ)]? = some (A_src hMm hN i k, A_tgt hMm hN k (f k)) := by
  simp [A_es]

lemma A_tgt_inj (k : Fin M) (b b' : Bool) (h : A_tgt hMm hN k b = A_tgt hMm hN k b') :
    b = b' := by
  simp only [A_tgt, Fin.mk.injEq] at h
  cases b <;> cases b' <;> simp_all

lemma A_tgt_ne_q (k : Fin M) (b : Bool) : A_tgt hMm hN k b ≠ A_q hN := by
  simp [A_tgt, A_q, Fin.ext_iff]

lemma A_src_eq_q (i k : Fin M) (h : A_src hMm hN i k = A_q hN) : k = i := by
  by_contra hk
  simp [A_src, hk, A_q, Fin.ext_iff] at h

lemma A_es_nodup (f : Fin M → Bool) (i : Fin M) : (A_es hMm hN f i).Nodup := by
  rw [A_es, List.nodup_ofFn]
  intro k k' hkk
  simp only [Prod.mk.injEq] at hkk
  obtain ⟨hs, ht⟩ := hkk
  have hm := A_m_pos hMm k
  have hmod : (k : ℕ) % m = k' % m := by
    simp only [A_tgt, Fin.mk.injEq] at ht
    split at ht <;> split at ht <;> omega
  by_cases hki : k = i
  · by_cases hk'i : k' = i
    · rw [hki, hk'i]
    · rw [hki] at hs
      have := A_src_eq_q hMm hN i k' (by rw [← hs]; simp [A_src])
      exact absurd this hk'i
  · by_cases hk'i : k' = i
    · rw [hk'i] at hs
      have := A_src_eq_q hMm hN i k (by rw [hs]; simp [A_src])
      exact absurd this hki
    · simp only [A_src, hki, hk'i, ite_false, Fin.mk.injEq] at hs
      apply Fin.ext
      have h1 := Nat.div_add_mod (k : ℕ) m
      have h2 := Nat.div_add_mod (k' : ℕ) m
      have h3 : (k : ℕ) / m = k' / m := by omega
      rw [← h1, ← h2, h3, hmod]

lemma A_es_mem (f : Fin M → Bool) (i : Fin M) :
    (A_q hN, A_tgt hMm hN i (f i)) ∈ A_es hMm hN f i := by
  rw [A_es, List.mem_ofFn]
  exact ⟨i, by simp [A_src]⟩

lemma A_es_q_eq (f : Fin M → Bool) (i : Fin M) (v : Fin N)
    (h : (A_q hN, v) ∈ A_es hMm hN f i) : v = A_tgt hMm hN i (f i) := by
  rw [A_es, List.mem_ofFn] at h
  obtain ⟨k, hk⟩ := h
  simp only [Prod.mk.injEq] at hk
  obtain ⟨h1, h2⟩ := hk
  have := A_src_eq_q hMm hN i k h1
  subst this
  exact h2.symm

lemma A_es_countP (f : Fin M → Bool) (i : Fin M) :
    (A_es hMm hN f i).countP (fun e => e.1 = A_q hN) = 1 := by
  rw [List.countP_congr (q := fun e => e == (A_q hN, A_tgt hMm hN i (f i)))]
  · exact List.count_eq_one_of_mem (A_es_nodup hMm hN f i) (A_es_mem hMm hN f i)
  · intro e he
    simp only [decide_eq_true_eq, beq_iff_eq]
    constructor
    · intro h1
      obtain ⟨s, t⟩ := e
      simp only at h1
      subst h1
      rw [A_es_q_eq hMm hN f i t he]
    · rintro rfl; rfl

end Family

/-- The lower bound on the hard family, for an arbitrary public suffix. -/
theorem A_family {M d H dk dv p m : ℕ} (tf : OneLayerTF N d H dk dv)
    (φ : ℝ → ℝ) (normalized : Bool) (rd : Rounding H dk dv d)
    (hrd : rd.IsFixed p) (hdv : dv ≤ d) (hp : 2 * M + 1 ≤ 2 ^ p)
    (hMm : M ≤ m * m) (hN : 3 * m + 1 ≤ N) (suf : List (Tok N × Role)) (hsuf : suf ≠ [])
    (hcorr : ∀ f i w, IsMax (tf.logitsRd φ normalized rd (A_inp (A_es hMm hN f i) suf)) w →
      w = .node (A_tgt hMm hN i (f i))) :
    M ≤ 4 * H * d * p :=
  A_core tf φ normalized rd hrd hdv hp suf hsuf (A_es hMm hN) (A_es_length hMm hN)
    (A_es_src hMm hN) (A_tgt hMm hN) (fun f i k => ⟨_, A_es_get hMm hN f i k⟩)
    (A_tgt_inj hMm hN) hcorr

/-! ### The theorems -/

/-- **Theorem `thm:lower_bound`.** -/
theorem one_layer_lower_bound {M d H dk dv p : ℕ} (tf : OneLayerTF N d H dk dv)
    (φ : ℝ → ℝ) (normalized : Bool) (rd : Rounding H dk dv d) (hrd : rd.IsFixed p)
    (hdv : dv ≤ d) (hp : 3 * M + 2 ≤ 2 ^ p)
    (hM : 1 ≤ M) (hN : 3 * ⌈Real.sqrt M⌉₊ + 1 ≤ N)
    (hcorr : ∀ (es : List (Fin N × Fin N)) (q t : Fin N), es.length = M → es.Nodup →
      es.countP (fun e => e.1 = q) = 1 → (q, t) ∈ es →
      ∀ w, IsMax (tf.logitsRd φ normalized rd (childInput es q)) w → w = .node t) :
    M ≤ 4 * H * d * p := by
  have hMm : M ≤ ⌈Real.sqrt M⌉₊ * ⌈Real.sqrt M⌉₊ := by
    have h1 : Real.sqrt M ≤ ⌈Real.sqrt M⌉₊ := Nat.le_ceil _
    have h2 : (M : ℝ) ≤ (⌈Real.sqrt M⌉₊ : ℝ) * ⌈Real.sqrt M⌉₊ := by
      calc (M : ℝ) = Real.sqrt M * Real.sqrt M := (Real.mul_self_sqrt (Nat.cast_nonneg _)).symm
        _ ≤ _ := mul_le_mul h1 h1 (Real.sqrt_nonneg _) (Nat.cast_nonneg _)
    exact_mod_cast h2
  refine A_family tf φ normalized rd hrd hdv (by omega) hMm hN [(.node (A_q hN), .trace)]
    (by simp) ?_
  intro f i w hw
  exact hcorr (A_es hMm hN f i) (A_q hN) (A_tgt hMm hN i (f i)) (A_es_length hMm hN f i)
    (A_es_nodup hMm hN f i) (A_es_countP hMm hN f i) (A_es_mem hMm hN f i) w hw


/-- **Corollary `cor:dense_graph_lower_bound`, first part.** -/
theorem dense_lower_bound {d H dk dv p : ℕ} (tf : OneLayerTF N d H dk dv)
    (φ : ℝ → ℝ) (normalized : Bool) (rd : Rounding H dk dv d) (hrd : rd.IsFixed p)
    (hdv : dv ≤ d) (hN : 4 ≤ N)
    (hp : 3 * ((N - 1) / 3) ^ 2 + 2 ≤ 2 ^ p)
    (hcorr : ∀ (es : List (Fin N × Fin N)) (q t : Fin N), es.length = ((N - 1) / 3) ^ 2 →
      es.Nodup → es.countP (fun e => e.1 = q) = 1 → (q, t) ∈ es →
      ∀ w, IsMax (tf.logitsRd φ normalized rd (childInput es q)) w → w = .node t) :
    N ^ 2 ≤ 144 * H * d * p := by
  have hm1 : 1 ≤ (N - 1) / 3 := by omega
  have hceil : ⌈Real.sqrt (((N - 1) / 3) ^ 2 : ℕ)⌉₊ = (N - 1) / 3 := by
    rw [Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg _), Nat.ceil_natCast]
  have h := one_layer_lower_bound (M := ((N - 1) / 3) ^ 2) tf φ normalized rd hrd hdv hp
    (Nat.one_le_pow _ _ hm1) (by rw [hceil]; omega) hcorr
  have h6 : N ≤ 6 * ((N - 1) / 3) := by omega
  have h36 : N ^ 2 ≤ 36 * ((N - 1) / 3) ^ 2 := by
    calc N ^ 2 ≤ (6 * ((N - 1) / 3)) ^ 2 := Nat.pow_le_pow_left h6 2
      _ = 36 * ((N - 1) / 3) ^ 2 := by ring
  calc N ^ 2 ≤ 36 * ((N - 1) / 3) ^ 2 := h36
    _ ≤ 36 * (4 * H * d * p) := Nat.mul_le_mul_left _ h
    _ = 144 * H * d * p := by ring


/-- **Corollary `cor:dense_graph_lower_bound`, second part (DFS).** -/
theorem dfs_lower_bound {d H dk dv p : ℕ} (tf : OneLayerTF N d H dk dv)
    (φ : ℝ → ℝ) (normalized : Bool) (rd : Rounding H dk dv d) (hrd : rd.IsFixed p)
    (hdv : dv ≤ d) (hN : 4 ≤ N)
    (hp : 3 * ((N - 1) / 3) ^ 2 + 4 ≤ 2 ^ p)
    (hcorr : ∀ (es : List (Fin N × Fin N)) (root tgt : Fin N),
      es.length = ((N - 1) / 3) ^ 2 → es.Nodup → Nonterm (Adj es) tgt [root] [root] →
      ∀ w, IsMax (tf.logitsRd φ normalized rd (dfsInput es tgt [root])) w →
        ∃ v, w = .node v ∧ DFSNext (Adj es) [root] [root] v) :
    N ^ 2 ≤ 144 * H * d * p := by
  have hm1 : 1 ≤ (N - 1) / 3 := by omega
  have hMm : ((N - 1) / 3) ^ 2 ≤ (N - 1) / 3 * ((N - 1) / 3) := le_of_eq (sq _)
  have hN' : 3 * ((N - 1) / 3) + 1 ≤ N := by omega
  let a₁ : Fin N := ⟨1, by omega⟩
  have hp' : 2 * ((N - 1) / 3) ^ 2 + 1 ≤ 2 ^ p := by omega
  have h := A_family tf φ normalized rd hrd hdv hp' hMm hN'
    [(.node a₁, .goal), (.rsn, .goal), (.node (A_q hN'), .trace)] (by simp) (by
      intro f i w hw
      have hin : dfsInput (A_es hMm hN' f i) a₁ [A_q hN'] = A_inp (A_es hMm hN' f i)
          [(.node a₁, .goal), (.rsn, .goal), (.node (A_q hN'), .trace)] := by
        simp [dfsInput, A_inp]
      have hnt : Nonterm (Adj (A_es hMm hN' f i)) a₁ [A_q hN'] [A_q hN'] := by
        refine ⟨by simp [A_q, a₁, Fin.ext_iff], A_tgt hMm hN' i (f i), Or.inl ⟨?_, ?_⟩⟩
        · exact A_es_mem hMm hN' f i
        · simpa using A_tgt_ne_q hMm hN' i (f i)
      obtain ⟨v, rfl, hv⟩ := hcorr (A_es hMm hN' f i) (A_q hN') a₁ (A_es_length hMm hN' f i)
        (A_es_nodup hMm hN' f i) hnt w (by rw [hin]; exact hw)
      simp only [DFSNext] at hv
      rcases hv with ⟨hadj, _⟩ | ⟨_, hnone⟩
      · rw [A_es_q_eq hMm hN' f i v hadj]
      · simp at hnone)
  have h6 : N ≤ 6 * ((N - 1) / 3) := by omega
  have h36 : N ^ 2 ≤ 36 * ((N - 1) / 3) ^ 2 := by
    calc N ^ 2 ≤ (6 * ((N - 1) / 3)) ^ 2 := Nat.pow_le_pow_left h6 2
      _ = 36 * ((N - 1) / 3) ^ 2 := by ring
  calc N ^ 2 ≤ 36 * ((N - 1) / 3) ^ 2 := h36
    _ ≤ 36 * (4 * H * d * p) := Nat.mul_le_mul_left _ h
    _ = 144 * H * d * p := by ring


end DFSExpr
