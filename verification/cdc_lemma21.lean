import Mathlib

namespace CDC

/-- A finite loopless multigraph. Parallel edges ARE allowed (two distinct edges
may share both endpoints); `fst`/`snd` is an arbitrary orientation and every
notion below is symmetric in it. -/
structure MG (V E : Type*) where
  fst : E → V
  snd : E → V
  loopless : ∀ e, fst e ≠ snd e

namespace MG

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

/-- `v` is an endpoint of `e`. -/
def Inc (G : MG V E) (e : E) (v : V) : Prop := v = G.fst e ∨ v = G.snd e

instance decInc (G : MG V E) (e : E) (v : V) : Decidable (G.Inc e v) := by
  unfold Inc; infer_instance

/-- The endpoint of `e` other than `v` (junk if `v` is not an endpoint of `e`). -/
def other (G : MG V E) (e : E) (v : V) : V := if v = G.fst e then G.snd e else G.fst e

variable {G : MG V E}

lemma other_ne {e : E} {v : V} (h : G.Inc e v) : G.other e v ≠ v := by
  unfold Inc at h; unfold other
  rcases h with h | h <;> subst h <;> split_ifs with hh
  all_goals first
    | exact Ne.symm (G.loopless e) | exact (G.loopless e)
    | exact absurd hh.symm (G.loopless e) | exact absurd rfl hh

/-- If `v` is an endpoint of `e` then the endpoints of `e` are exactly `v` and `other e v`. -/
lemma inc_iff {e : E} {v : V} (h : G.Inc e v) (x : V) :
    G.Inc e x ↔ (x = v ∨ x = G.other e v) := by
  unfold Inc at h ⊢; unfold other
  rcases h with h | h <;> subst h <;> split_ifs with hh
  all_goals first
    | tauto | exact absurd hh (G.loopless e)
    | exact absurd hh.symm (G.loopless e) | exact absurd rfl hh

lemma inc_other {e : E} {v : V} (h : G.Inc e v) : G.Inc e (G.other e v) :=
  (inc_iff h _).2 (Or.inr rfl)

lemma other_other {e : E} {v : V} (h : G.Inc e v) : G.other e (G.other e v) = v := by
  unfold Inc at h; unfold other
  rcases h with h | h <;> subst h <;> split_ifs with h1 h2 <;> simp_all [G.loopless e]

/-! ### Walks

A walk is a start vertex `u` together with a list of edges; the walk visits
`u`, then `other e₀ u`, and so on. -/

/-- Endpoint of the walk starting at `u` and following the edge list. -/
def walkEnd (G : MG V E) : V → List E → V
  | u, [] => u
  | u, e :: es => walkEnd G (G.other e u) es

/-- The edge list really is a walk from `u`: each edge meets the running vertex. -/
def IsWalk (G : MG V E) : V → List E → Prop
  | _, [] => True
  | u, e :: es => G.Inc e u ∧ IsWalk G (G.other e u) es

@[simp] lemma walkEnd_nil (u : V) : G.walkEnd u [] = u := rfl
@[simp] lemma walkEnd_cons (u : V) (e : E) (es : List E) :
    G.walkEnd u (e :: es) = G.walkEnd (G.other e u) es := rfl
@[simp] lemma isWalk_nil (u : V) : G.IsWalk u [] := trivial
@[simp] lemma isWalk_cons (u : V) (e : E) (es : List E) :
    G.IsWalk u (e :: es) ↔ (G.Inc e u ∧ G.IsWalk (G.other e u) es) := Iff.rfl

lemma walkEnd_append (u : V) (es fs : List E) :
    G.walkEnd u (es ++ fs) = G.walkEnd (G.walkEnd u es) fs := by
  induction es generalizing u with
  | nil => simp
  | cons e es ih => simp [ih]

lemma isWalk_append (u : V) (es fs : List E) :
    G.IsWalk u (es ++ fs) ↔ (G.IsWalk u es ∧ G.IsWalk (G.walkEnd u es) fs) := by
  induction es generalizing u with
  | nil => simp
  | cons e es ih => simp [ih, and_assoc]

/-- Extending a walk by one further edge at its far end. -/
lemma isWalk_concat (u : V) (es : List E) (e : E) :
    G.IsWalk u (es ++ [e]) ↔ (G.IsWalk u es ∧ G.Inc e (G.walkEnd u es)) := by
  rw [isWalk_append]; simp [IsWalk]

/-! ### Incidence counts and degrees -/

/-- How many edges of the list `es` are incident to `x` (with multiplicity). -/
def cnt (G : MG V E) (es : List E) (x : V) : ℕ := es.countP (fun e => G.Inc e x)

/-- Degree of `x` in the edge set `S`. -/
def deg (G : MG V E) (S : Finset E) (x : V) : ℕ := (S.filter (fun e => G.Inc e x)).card

/-- **Handshake / parity along a walk.** A vertex meets an odd number of a walk's
edges exactly when it is one of the walk's two (distinct) endpoints. -/
lemma cnt_parity (u : V) (es : List E) (hw : G.IsWalk u es) (x : V) :
    (G.cnt es x) % 2
      = ((if x = u then 1 else 0) + (if x = G.walkEnd u es then 1 else 0)) % 2 := by
  induction es generalizing u with
  | nil => simp only [cnt, List.countP_nil, walkEnd_nil]; split_ifs <;> simp
  | cons e es ih =>
      obtain ⟨he, hw'⟩ := hw
      have hne : G.other e u ≠ u := other_ne he
      have hc : G.cnt (e :: es) x = (if G.Inc e x then 1 else 0) + G.cnt es x := by
        simp only [cnt, List.countP_cons, decide_eq_true_eq]; omega
      have IH := ih (G.other e u) hw'
      have key : ((if G.Inc e x then 1 else 0) + (if x = G.other e u then 1 else 0)) % 2
          = (if x = u then 1 else 0) % 2 := by
        by_cases h1 : x = u
        · have hi : G.Inc e x := h1 ▸ he
          have h2 : ¬ (x = G.other e u) := by rw [h1]; exact fun hh => hne hh.symm
          simp [hi, h1, h2, he, Ne.symm hne]
        · by_cases h2 : x = G.other e u
          · have hi : G.Inc e x := h2 ▸ inc_other he
            simp [hi, h1, h2, inc_other he, hne]
          · have hi : ¬ G.Inc e x := fun hh => by
              rcases (inc_iff he x).1 hh with h | h
              · exact h1 h
              · exact h2 h
            simp [hi, h1, h2]
      rw [hc, walkEnd_cons]
      omega

/-- For a repetition-free edge list, the list count agrees with the degree in the
corresponding edge set. -/
lemma cnt_eq_deg {es : List E} (h : es.Nodup) (x : V) :
    G.cnt es x = G.deg es.toFinset x := by
  unfold cnt deg
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (h.filter _),
      List.toFinset_filter]
  simp

/-! ### The crux: an edge set with all degrees 0 or 2 is a disjoint union of cycles -/

section Crux
variable [Fintype E]

/-- A trail of `G` inside the edge set `S`: a walk from `u` whose edges are
distinct and all lie in `S`. -/
def IsTrailIn (G : MG V E) (S : Finset E) (u : V) (es : List E) : Prop :=
  G.IsWalk u es ∧ es.Nodup ∧ ∀ e ∈ es, e ∈ S

variable {G : MG V E}

lemma IsTrailIn.toFinset_subset {S : Finset E} {u : V} {es : List E}
    (h : G.IsTrailIn S u es) : es.toFinset ⊆ S := fun e he => h.2.2 e (List.mem_toFinset.1 he)

lemma IsTrailIn.length_le {S : Finset E} {u : V} {es : List E}
    (h : G.IsTrailIn S u es) : es.length ≤ S.card := by
  have := Finset.card_le_card h.toFinset_subset
  rwa [List.toFinset_card_of_nodup h.2.1] at this

/-- **A nonempty edge set with all degrees 0 or 2 contains a closed trail.**

Take a trail inside `S` of maximal length. It cannot be extended, so its far end
`w` has all of its `S`-edges already used; hence `deg S w = cnt es w`. By the
parity lemma `cnt es w` is odd unless the trail is closed — but `deg S w` is even.
So the maximal trail is closed. -/
theorem exists_closed_trail (G : MG V E) (S : Finset E)
    (hS : ∀ x, G.deg S x = 0 ∨ G.deg S x = 2) (hne : S.Nonempty) :
    ∃ (u : V) (es : List E), G.IsTrailIn S u es ∧ es ≠ [] ∧ G.walkEnd u es = u := by
  classical
  set P : ℕ → Prop := fun n => ∃ (u : V) (es : List E), G.IsTrailIn S u es ∧ es.length = n
    with hPdef
  obtain ⟨e₀, he₀⟩ := hne
  have hP1 : P 1 := by
    refine ⟨G.fst e₀, [e₀], ⟨⟨Or.inl rfl, trivial⟩, by simp, ?_⟩, rfl⟩
    intro e he; simp only [List.mem_singleton] at he; exact he ▸ he₀
  have hbdd : ∀ n, P n → n ≤ S.card := by rintro n ⟨u, es, ht, rfl⟩; exact ht.length_le
  -- a maximal achievable length
  set T : Finset ℕ := (Finset.range (S.card + 1)).filter P with hTdef
  have h1T : 1 ∈ T := by
    simp only [hTdef, Finset.mem_filter, Finset.mem_range]
    exact ⟨by have := hbdd 1 hP1; omega, hP1⟩
  have hTne : T.Nonempty := ⟨1, h1T⟩
  set n := T.max' hTne with hn
  have hnT : n ∈ T := T.max'_mem hTne
  have hPn : P n := (Finset.mem_filter.1 hnT).2
  have hmax : ∀ m, P m → m ≤ n := by
    intro m hm
    refine Finset.le_max' T m ?_
    simp only [hTdef, Finset.mem_filter, Finset.mem_range]
    exact ⟨by have := hbdd m hm; omega, hm⟩
  obtain ⟨u, es, ht, hlen⟩ := hPn
  have hn1 : 1 ≤ n := hmax 1 hP1
  have hesne : es ≠ [] := by
    intro h; rw [h] at hlen; simp at hlen; omega
  refine ⟨u, es, ht, hesne, ?_⟩
  set w := G.walkEnd u es with hw
  -- no unused S-edge at w, else we could extend the trail
  have hstuck : ∀ e ∈ S, G.Inc e w → e ∈ es := by
    intro e heS hinc
    by_contra hmem
    have hlong : P (n + 1) := by
      refine ⟨u, es ++ [e], ⟨?_, ?_, ?_⟩, by
        simp only [List.length_append, List.length_singleton, hlen]⟩
      · exact (isWalk_concat u es e).2 ⟨ht.1, hinc⟩
      · rw [List.nodup_append]
        refine ⟨ht.2.1, List.nodup_singleton e, ?_⟩
        intro a ha b hb
        simp only [List.mem_singleton] at hb
        subst hb; rintro rfl; exact hmem ha
      · intro f hf
        rcases List.mem_append.1 hf with h | h
        · exact ht.2.2 f h
        · simp only [List.mem_singleton] at h; exact h ▸ heS
    have := hmax (n + 1) hlong; omega
  -- hence deg S w is computed by the trail itself
  have hfilter : S.filter (fun e => G.Inc e w) = es.toFinset.filter (fun e => G.Inc e w) := by
    ext e
    simp only [Finset.mem_filter, List.mem_toFinset]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨hstuck e h1 h2, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨ht.2.2 e h1, h2⟩
  have hdegw : G.deg S w = G.cnt es w := by
    rw [cnt_eq_deg ht.2.1]; unfold deg; rw [hfilter]
  -- parity: w is an endpoint, so cnt es w is odd unless w = u
  have hpar := cnt_parity u es ht.1 w
  have heven : G.deg S w % 2 = 0 := by rcases hS w with h | h <;> omega
  rw [hdegw] at heven
  rw [heven, ← hw, if_pos rfl] at hpar
  by_contra hcl
  rw [if_neg hcl] at hpar
  omega

/-! ### Degrees behave well under subsets -/

lemma deg_mono (G : MG V E) {S T : Finset E} (h : S ⊆ T) (x : V) : G.deg S x ≤ G.deg T x :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

lemma deg_sdiff_add (G : MG V E) {C S : Finset E} (h : C ⊆ S) (x : V) :
    G.deg (S \ C) x + G.deg C x = G.deg S x := by
  classical
  have hfs : (S \ C).filter (fun e => G.Inc e x)
      = S.filter (fun e => G.Inc e x) \ C.filter (fun e => G.Inc e x) := by
    ext e; simp only [Finset.mem_filter, Finset.mem_sdiff]; tauto
  unfold deg
  rw [hfs, Finset.card_sdiff_add_card_eq_card (Finset.filter_subset_filter _ h)]

/-! ### Cycles

A **cycle** of a multigraph is the edge set of a nonempty closed trail on which
every vertex has degree `0` or `2`; equivalently, a connected `2`-regular edge
set. Two parallel edges form a cycle (a digon), exactly as the paper requires —
this is precisely what Mathlib's `SimpleGraph.Walk.IsCycle` (length ≥ 3) cannot
express. -/
def IsCyc (G : MG V E) (C : Finset E) : Prop :=
  C.Nonempty ∧ (∀ x, G.deg C x = 0 ∨ G.deg C x = 2) ∧
    ∃ (u : V) (es : List E), G.IsWalk u es ∧ es.Nodup ∧ G.walkEnd u es = u ∧ es.toFinset = C

/-- Every nonempty `0`-or-`2`-degree edge set contains a cycle. -/
theorem exists_cyc_subset (G : MG V E) (S : Finset E)
    (hS : ∀ x, G.deg S x = 0 ∨ G.deg S x = 2) (hne : S.Nonempty) :
    ∃ C ⊆ S, G.IsCyc C := by
  obtain ⟨u, es, ht, hesne, hcl⟩ := exists_closed_trail G S hS hne
  refine ⟨es.toFinset, ht.toFinset_subset, ?_, ?_, u, es, ht.1, ht.2.1, hcl, rfl⟩
  · obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil es hesne
    exact ⟨e, List.mem_toFinset.2 he⟩
  · intro x
    have hd : G.deg es.toFinset x = G.cnt es x := (cnt_eq_deg ht.2.1 x).symm
    have hpar := cnt_parity u es ht.1 x
    rw [hcl] at hpar
    have heven : G.cnt es x % 2 = 0 := by
      rcases (by by_cases h : x = u <;> simp [h] : ((if x = u then 1 else 0) +
        (if x = u then 1 else 0)) % 2 = 0) with h
      omega
    have hle : G.deg es.toFinset x ≤ G.deg S x := deg_mono G ht.toFinset_subset x
    rcases hS x with h | h <;> omega

/-- **THE CRUX (cycle decomposition).** An edge set in which every vertex has
degree `0` or `2` is a disjoint union of cycles: there is a family `F` of cycles
such that every edge of `S` lies in exactly one member of `F` and no other edge
lies in any member. -/
theorem exists_cycle_decomposition (G : MG V E) (S : Finset E)
    (hS : ∀ x, G.deg S x = 0 ∨ G.deg S x = 2) :
    ∃ F : Finset (Finset E), (∀ C ∈ F, G.IsCyc C) ∧
      ∀ e : E, (F.filter (fun C => e ∈ C)).card = if e ∈ S then 1 else 0 := by
  classical
  induction hcard : S.card using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact ⟨∅, by simp, by simp⟩
    obtain ⟨C, hCS, hC⟩ := exists_cyc_subset G S hS hne
    obtain ⟨e₁, he₁⟩ := hC.1
    -- the rest still has all degrees 0 or 2
    have hS' : ∀ x, G.deg (S \ C) x = 0 ∨ G.deg (S \ C) x = 2 := by
      intro x
      have h1 := deg_sdiff_add G hCS x
      rcases hS x with h | h <;> rcases hC.2.1 x with h' | h' <;> omega
    have hlt : (S \ C).card < n := by
      subst hcard
      exact Finset.card_lt_card ⟨Finset.sdiff_subset,
        fun hsub => absurd (hsub (hCS he₁)) (by simp [he₁])⟩
    obtain ⟨F, hFcyc, hFcnt⟩ := ih (S \ C).card hlt (S \ C) hS' rfl
    -- C is not already in F
    have hCF : C ∉ F := by
      intro hmem
      have : (F.filter (fun D => e₁ ∈ D)).card ≠ 0 := by
        refine Finset.card_ne_zero_of_mem (Finset.mem_filter.2 ⟨hmem, he₁⟩)
      rw [hFcnt e₁] at this
      simp [Finset.mem_sdiff, he₁] at this
    refine ⟨insert C F, ?_, ?_⟩
    · intro D hD
      rcases Finset.mem_insert.1 hD with rfl | hD
      · exact hC
      · exact hFcyc D hD
    · intro e
      rw [Finset.filter_insert]
      by_cases hec : e ∈ C
      · rw [if_pos hec, Finset.card_insert_of_notMem (fun h => hCF (Finset.mem_filter.1 h).1),
          hFcnt e, if_pos (hCS hec)]
        simp [Finset.mem_sdiff, hec]
      · rw [if_neg hec, hFcnt e]
        by_cases heS : e ∈ S <;> simp [Finset.mem_sdiff, heS, hec]

/-! ### Cycle double covers -/

/-- A **cycle double cover**: a multiset of cycles covering every edge of `G`
exactly twice. (A multiset, not a set: the same edge set may legitimately occur
twice in the cover.) -/
def IsCDC (G : MG V E) (𝒞 : Multiset (Finset E)) : Prop :=
  (∀ C ∈ 𝒞, G.IsCyc C) ∧ ∀ e : E, Multiset.countP (fun C => e ∈ C) 𝒞 = 2

private lemma countP_finset_sum {ι α : Type*} [DecidableEq ι] (t : Finset ι)
    (m : ι → Multiset α) (p : α → Prop) [DecidablePred p] :
    Multiset.countP p (∑ i ∈ t, m i) = ∑ i ∈ t, Multiset.countP p (m i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Multiset.countP_add, ih]

/-- **LEMMA 2.1.**  Let `G` be a loopless multigraph and let every edge `e` carry a
two-element set `P e ⊆ Γ`, such that for every vertex `v` and every `s ∈ Γ` the
number of edges at `v` whose set contains `s` is `0` or `2`.  Then `G` has a cycle
double cover.

Proof, following the paper: put `M s = {e | s ∈ P e}`.  By hypothesis every vertex
has degree `0` or `2` in `M s`, so `M s` is a disjoint union of cycles
(`exists_cycle_decomposition`).  Every edge lies in exactly two of the `M s`, since
`|P e| = 2`.  Taking all the cycles of all the `M s`, with multiplicity, covers each
edge exactly twice. -/
theorem lemma21 (G : MG V E) {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (P : E → Finset Γ) (hcard : ∀ e, (P e).card = 2)
    (hloc : ∀ (v : V) (s : Γ),
      G.deg (Finset.univ.filter (fun e => s ∈ P e)) v = 0 ∨
      G.deg (Finset.univ.filter (fun e => s ∈ P e)) v = 2) :
    ∃ 𝒞 : Multiset (Finset E), G.IsCDC 𝒞 := by
  classical
  set M : Γ → Finset E := fun s => Finset.univ.filter (fun e => s ∈ P e) with hM
  have hmemM : ∀ (s : Γ) (e : E), e ∈ M s ↔ s ∈ P e := by
    intro s e; simp [hM]
  -- decompose each `M s` into cycles
  have hdec : ∀ s : Γ, ∃ F : Finset (Finset E), (∀ C ∈ F, G.IsCyc C) ∧
      ∀ e : E, (F.filter (fun C => e ∈ C)).card = if e ∈ M s then 1 else 0 :=
    fun s => exists_cycle_decomposition G (M s) (fun x => hloc x s)
  choose F hFcyc hFcnt using hdec
  refine ⟨∑ s : Γ, (F s).val, ?_, ?_⟩
  · intro C hC
    rw [Multiset.mem_sum] at hC
    obtain ⟨s, -, hs⟩ := hC
    exact hFcyc s C hs
  · intro e
    rw [countP_finset_sum]
    have hstep : ∀ s : Γ, Multiset.countP (fun C => e ∈ C) (F s).val
        = if s ∈ P e then 1 else 0 := by
      intro s
      have : Multiset.countP (fun C => e ∈ C) (F s).val
          = ((F s).filter (fun C => e ∈ C)).card := by
        rw [Multiset.countP_eq_card_filter]; rfl
      rw [this, hFcnt s e]
      simp [hmemM s e]
    simp only [hstep]
    rw [← Finset.sum_filter]
    have hfe : (Finset.univ.filter (fun s => s ∈ P e)) = P e := by ext s; simp
    rw [hfe, Finset.sum_const, smul_eq_mul, mul_one, hcard e]

/-- The paper's exact setting: a **loopless cubic** multigraph with such a family
`P` has a cycle double cover.  (Note the proof of Lemma 2.1 never uses cubicity —
it is only needed to *produce* the family `P`, which is Lemma 2.2's job.) -/
theorem lemma21_cubic (G : MG V E) {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (_hcubic : ∀ v : V, G.deg Finset.univ v = 3)
    (P : E → Finset Γ) (hcard : ∀ e, (P e).card = 2)
    (hloc : ∀ (v : V) (s : Γ),
      G.deg (Finset.univ.filter (fun e => s ∈ P e)) v = 0 ∨
      G.deg (Finset.univ.filter (fun e => s ∈ P e)) v = 2) :
    ∃ 𝒞 : Multiset (Finset E), G.IsCDC 𝒞 :=
  lemma21 G P hcard hloc

end Crux
end MG
end CDC

/-! ### Sanity check: the definitions are not vacuous, and a digon IS a cycle

Two parallel edges between two vertices form a cycle here — exactly as the paper
requires, and exactly what `SimpleGraph.Walk.IsCycle` (length ≥ 3) cannot express. -/

namespace Digon

/-- Two vertices, two parallel edges between them. -/
def D : CDC.MG (Fin 2) (Fin 2) where
  fst := fun _ => 0
  snd := fun _ => 1
  loopless := by decide

example : ∀ x, D.deg Finset.univ x = 2 := by decide

/-- The digon's whole edge set is a cycle. -/
theorem digon_isCyc : D.IsCyc Finset.univ := by
  refine ⟨⟨0, Finset.mem_univ 0⟩, by decide, 0, [0, 1], ⟨by decide, by decide, trivial⟩,
    by decide, by decide, by decide⟩

/-- End-to-end: Lemma 2.1 really fires. Give both edges of the digon the set
`P e = {0,1} ⊆ Fin 2`; the hypotheses hold, so the digon has a cycle double
cover. (Guards against the hypotheses of `lemma21` being vacuous.) -/
theorem digon_has_cdc : ∃ 𝒞 : Multiset (Finset (Fin 2)), D.IsCDC 𝒞 :=
  CDC.MG.lemma21 D (Γ := Fin 2) (fun _ => Finset.univ) (by decide) (by decide)

end Digon

#print axioms Digon.digon_isCyc
#print axioms Digon.digon_has_cdc
#print axioms CDC.MG.cnt_parity
#print axioms CDC.MG.exists_closed_trail
#print axioms CDC.MG.exists_cyc_subset
#print axioms CDC.MG.exists_cycle_decomposition
#print axioms CDC.MG.lemma21
#print axioms CDC.MG.lemma21_cubic
