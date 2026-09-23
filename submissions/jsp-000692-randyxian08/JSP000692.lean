import Mathlib

/-!
JSP-000692 / Erdos 836: BOTH questions, on shared definitions.
COMPLETE CANDIDATE SOURCE; compilation status is in verification/status.json.
This standalone file is generated from the eight module files.
-/

/- ===== Module: Hypergraph ===== -/

set_option autoImplicit false

/-!
JSP-000692 / Erdős 836: definitions and elementary structural lemmas.
Authoring status: NOT COMPILED in this environment.
Shared definitions; all counts below refer to active vertices.
-/

namespace JSP692

abbrev Hypergraph (V : Type*) := Finset (Finset V)

variable {V : Type*} [DecidableEq V]

def Uniform (H : Hypergraph V) (r : ℕ) : Prop :=
  ∀ e ∈ H, e.card = r

def Intersecting (H : Hypergraph V) : Prop :=
  ∀ e ∈ H, ∀ f ∈ H, (e ∩ f).Nonempty

def Proper {C : Type*} (H : Hypergraph V) (c : V → C) : Prop :=
  ∀ e ∈ H, ∃ u ∈ e, ∃ v ∈ e, c u ≠ c v

def Mono {C : Type*} (e : Finset V) (c : V → C) : Prop :=
  ∃ b : C, ∀ x ∈ e, c x = b

def ThreeChromatic (H : Hypergraph V) : Prop :=
  (∃ c : V → Fin 3, Proper H c) ∧ ¬ (∃ c : V → Bool, Proper H c)

/-- The union of the edges, not the ambient vertex type. -/
def support (H : Hypergraph V) : Finset V := H.biUnion id

theorem not_proper_of_mono {C : Type*} {H : Hypergraph V} {c : V → C}
    {e : Finset V} (he : e ∈ H) (hm : Mono e c) : ¬ Proper H c := by
  rintro hp
  obtain ⟨b, hb⟩ := hm
  obtain ⟨u, hu, v, hv, huv⟩ := hp e he
  exact huv ((hb u hu).trans (hb v hv).symm)

/-- Every transversal contains an edge in a non-two-colorable hypergraph. -/
theorem transversal_contains_edge {H : Hypergraph V}
    (hn : ¬ ∃ c : V → Bool, Proper H c)
    (S : Finset V) (hit : ∀ e ∈ H, (e ∩ S).Nonempty) :
    ∃ e ∈ H, e ⊆ S := by
  classical
  by_contra h
  apply hn
  refine ⟨fun x => decide (x ∈ S), ?_⟩
  intro e he
  obtain ⟨u, hu⟩ := hit e he
  have hue := (Finset.mem_inter.mp hu).1
  have huS := (Finset.mem_inter.mp hu).2
  have hout : ∃ v ∈ e, v ∉ S := by
    by_contra hv
    apply h
    refine ⟨e, he, ?_⟩
    intro v hve
    by_contra hvS
    exact hv ⟨v, hve, hvS⟩
  obtain ⟨v, hve, hvS⟩ := hout
  refine ⟨u, hue, v, hve, ?_⟩
  simp [huS, hvS]

/-- Intersecting uniform hypergraphs of rank at least two are 3-colorable. -/
theorem threeColorable_of_intersecting {H : Hypergraph V} {r : ℕ}
    (hr : 2 ≤ r) (hu : Uniform H r) (hi : Intersecting H) :
    ∃ c : V → Fin 3, Proper H c := by
  classical
  by_cases hH : H.Nonempty
  · obtain ⟨e, he⟩ := hH
    have hepos : 0 < e.card := by rw [hu e he]; omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hepos
    have hrest : (e.erase x).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem hx, hu e he]
      omega
    let c : V → Fin 3 := fun v => if v = x then 0 else if v ∈ e then 1 else 2
    refine ⟨c, ?_⟩
    intro f hf
    by_cases hfe : f = e
    · subst f
      obtain ⟨y, hy⟩ := hrest
      have hyx := (Finset.mem_erase.mp hy).1
      have hye := (Finset.mem_erase.mp hy).2
      refine ⟨x, hx, y, hye, ?_⟩
      simp [c, hyx, hye]
    · have hout : ∃ w ∈ f, w ∉ e := by
        by_contra h
        have hsub : f ⊆ e := by
          intro w hw
          by_contra hwe
          exact h ⟨w, hw, hwe⟩
        apply hfe
        apply Finset.eq_of_subset_of_card_le hsub
        rw [hu e he, hu f hf]
      obtain ⟨w, hwf, hwe⟩ := hout
      obtain ⟨v, hv⟩ := hi f hf e he
      have hvf := (Finset.mem_inter.mp hv).1
      have hve := (Finset.mem_inter.mp hv).2
      have hwx : w ≠ x := by
        intro hwx
        exact hwe (hwx.symm ▸ hx)
      refine ⟨v, hvf, w, hwf, ?_⟩
      by_cases hvx : v = x
      · simp [c, hvx, hwx, hwe]
      · simp [c, hvx, hve, hwx, hwe]
  · have hEmpty : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hH
    refine ⟨fun _ => 0, ?_⟩
    simp [Proper, hEmpty]

end JSP692

/- ===== Module: SplitGadget ===== -/

set_option autoImplicit false

/-!
A generic reduction from all vertex colorings to colorings of the core only.
No conclusion about an infinite family is inferred from a finite test.
Authoring status: NOT COMPILED in this environment.
-/

namespace JSP692

variable {X Y : Type*} [DecidableEq X] [DecidableEq Y] [Fintype Y]

structure SplitGadget (X Y : Type*) where
  core : Finset (Finset X)
  left : Y → Finset X
  right : Y → Finset X

def liftCore (s : Finset X) : Finset (X ⊕ Y) := s.image Sum.inl

def leftEdge (d : SplitGadget X Y) (y : Y) : Finset (X ⊕ Y) :=
  insert (Sum.inr y) (liftCore (d.left y))

def rightEdge (d : SplitGadget X Y) (y : Y) : Finset (X ⊕ Y) :=
  insert (Sum.inr y) (liftCore (d.right y))

def SplitGadget.graph (d : SplitGadget X Y) : Hypergraph (X ⊕ Y) :=
  d.core.image liftCore ∪ Finset.univ.biUnion (fun y => {leftEdge d y, rightEdge d y})

/-- Every core coloring either contains a monochromatic core edge, or has
oppositely monochromatic halves at some split vertex. -/
def SplitGadget.CoreObstructs (d : SplitGadget X Y) : Prop :=
  ∀ c : X → Bool,
    (∃ e ∈ d.core, Mono e c) ∨
    ∃ y : Y, ∃ b : Bool,
      (∀ x ∈ d.left y, c x = b) ∧
      (∀ x ∈ d.right y, c x = !b)

theorem coreEdge_mem (d : SplitGadget X Y) {e : Finset X} (he : e ∈ d.core) :
    liftCore e ∈ d.graph := by
  apply Finset.mem_union.mpr
  exact Or.inl (Finset.mem_image.mpr ⟨e, he, rfl⟩)

theorem leftEdge_mem (d : SplitGadget X Y) (y : Y) : leftEdge d y ∈ d.graph := by
  apply Finset.mem_union.mpr
  apply Or.inr
  exact Finset.mem_biUnion.mpr ⟨y, Finset.mem_univ y, by simp⟩

theorem rightEdge_mem (d : SplitGadget X Y) (y : Y) : rightEdge d y ∈ d.graph := by
  apply Finset.mem_union.mpr
  apply Or.inr
  exact Finset.mem_biUnion.mpr ⟨y, Finset.mem_univ y, by simp⟩

theorem mono_liftCore {C : Type*} {s : Finset X} {c : X ⊕ Y → C}
    (h : Mono s (fun x => c (Sum.inl x))) : Mono (liftCore s) c := by
  obtain ⟨b, hb⟩ := h
  refine ⟨b, ?_⟩
  intro v hv
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
  exact hb x hx

theorem mono_insert_liftCore {C : Type*} {s : Finset X} {c : X ⊕ Y → C}
    {y : Y} {b : C} (hy : c (Sum.inr y) = b)
    (hs : ∀ x ∈ s, c (Sum.inl x) = b) :
    Mono (insert (Sum.inr y) (liftCore s)) c := by
  refine ⟨b, ?_⟩
  intro v hv
  rcases Finset.mem_insert.mp hv with hv | hv
  · simpa [hv] using hy
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    exact hs x hx

/-- This is the soundness theorem used for the reduced finite certificates. -/
theorem not_twoColorable_of_coreObstructs (d : SplitGadget X Y)
    (hd : d.CoreObstructs) : ¬ ∃ c : X ⊕ Y → Bool, Proper d.graph c := by
  classical
  rintro ⟨c, hc⟩
  rcases hd (fun x => c (Sum.inl x)) with hcore | hsplit
  · obtain ⟨e, he, hm⟩ := hcore
    exact not_proper_of_mono (coreEdge_mem d he) (mono_liftCore hm) hc
  · obtain ⟨y, b, hleft, hright⟩ := hsplit
    have hcolor : c (Sum.inr y) = b ∨ c (Sum.inr y) = !b := by
      cases b <;> cases c (Sum.inr y) <;> simp
    rcases hcolor with hcolor | hcolor
    · exact not_proper_of_mono (leftEdge_mem d y)
        (mono_insert_liftCore hcolor hleft) hc
    · exact not_proper_of_mono (rightEdge_mem d y)
        (mono_insert_liftCore hcolor hright) hc

end JSP692

/- ===== Module: AlonCore ===== -/

set_option autoImplicit false

/-!
Uniformity and non-two-colourability of Alon's all-ranks construction.
The remaining properties are proved in AlonGeometry and AlonGrowth.
Authoring status: NOT COMPILED in this environment.
-/
namespace JSP692

variable {X Y : Type*} [DecidableEq X] [DecidableEq Y] [Fintype Y]

/-- The obstruction argument only uses a finite core and all balanced splits. -/
theorem coreObstructs_of_balanced_splits (d : SplitGadget X Y)
    (S : Finset X) (m : ℕ) (hsize : S.card = 2 * m)
    (hcore : ∀ e, e ∈ d.core ↔ e ⊆ S ∧ e.card = m + 1)
    (hsplit : ∀ A : Finset X, A ⊆ S → A.card = m →
      ∃ y : Y,
        (d.left y = A ∧ d.right y = S \ A) ∨
        (d.left y = S \ A ∧ d.right y = A)) : d.CoreObstructs := by
  classical
  intro c
  let R : Finset X := S.filter (fun x => c x = false)
  let B : Finset X := S \ R
  have hRS : R ⊆ S := Finset.filter_subset _ _
  have hBS : B ⊆ S := Finset.sdiff_subset
  have hRcolor : ∀ x ∈ R, c x = false := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have hBcolor : ∀ x ∈ B, c x = true := by
    intro x hx
    have hxS := (Finset.mem_sdiff.mp hx).1
    have hxR := (Finset.mem_sdiff.mp hx).2
    cases hcx : c x with
    | false => exact False.elim (hxR (Finset.mem_filter.mpr ⟨hxS, hcx⟩))
    | true => rfl
  by_cases hlargeR : m + 1 ≤ R.card
  · obtain ⟨e, heR, hecard⟩ := Finset.exists_subset_card_eq hlargeR
    exact Or.inl ⟨e, (hcore e).mpr ⟨heR.trans hRS, hecard⟩,
      false, fun x hx => hRcolor x (heR hx)⟩
  by_cases hlargeB : m + 1 ≤ B.card
  · obtain ⟨e, heB, hecard⟩ := Finset.exists_subset_card_eq hlargeB
    exact Or.inl ⟨e, (hcore e).mpr ⟨heB.trans hBS, hecard⟩,
      true, fun x hx => hBcolor x (heB hx)⟩
  have hsum : B.card + R.card = S.card :=
    Finset.card_sdiff_add_card_eq_card hRS
  have hRcard : R.card = m := by omega
  obtain ⟨y, horient⟩ := hsplit R hRS hRcard
  apply Or.inr
  rcases horient with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · refine ⟨y, false, ?_, ?_⟩
    · simpa only [hl] using hRcolor
    · simpa only [hr, Bool.not_false] using hBcolor
  · refine ⟨y, true, ?_, ?_⟩
    · simpa only [hl] using hBcolor
    · simpa only [hr, Bool.not_true] using hRcolor

/-- The chosen representative of an unordered balanced partition contains p. -/
abbrev BalancedLabels [Fintype X] (m : ℕ) (p : X) :=
  {A : Finset X // A.card = m ∧ p ∈ A}

def canonicalGadget [Fintype X] (m : ℕ) (p : X) :
    SplitGadget X (BalancedLabels m p) where
  core := (Finset.univ : Finset X).powersetCard (m + 1)
  left := fun A => A.val
  right := fun A => Finset.univ \ A.val

/-- This is an all-ranks theorem, not a test of finitely many ranks. -/
theorem canonical_coreObstructs [Fintype X] (m : ℕ) (p : X)
    (hsize : Fintype.card X = 2 * m) : (canonicalGadget m p).CoreObstructs := by
  classical
  apply coreObstructs_of_balanced_splits (canonicalGadget m p) Finset.univ m
  · simpa using hsize
  · intro e
    exact Finset.mem_powersetCard
  · intro A hA hcard
    by_cases hp : p ∈ A
    · refine ⟨⟨A, hcard, hp⟩, Or.inl ?_⟩
      exact ⟨rfl, rfl⟩
    · have hcomp : ((Finset.univ : Finset X) \ A).card = m := by
        have hs := Finset.card_sdiff_add_card_eq_card hA
        rw [Finset.card_univ, hsize, hcard] at hs
        omega
      have hpcomp : p ∈ (Finset.univ : Finset X) \ A := by simp [hp]
      refine ⟨⟨Finset.univ \ A, hcomp, hpcomp⟩, Or.inr ?_⟩
      constructor
      · rfl
      · change (Finset.univ : Finset X) \ (Finset.univ \ A) = A
        ext x
        simp

theorem canonical_not_twoColorable [Fintype X] (m : ℕ) (p : X)
    (hsize : Fintype.card X = 2 * m) :
    ¬ ∃ c : X ⊕ BalancedLabels m p → Bool, Proper (canonicalGadget m p).graph c :=
  not_twoColorable_of_coreObstructs _ (canonical_coreObstructs m p hsize)

lemma liftCore_card (s : Finset X) : (liftCore (Y := Y) s).card = s.card := by
  apply Finset.card_image_of_injective
  intro a b hab
  exact Sum.inl.inj hab

lemma insert_liftCore_card (s : Finset X) (y : Y) :
    (insert (Sum.inr y) (liftCore (Y := Y) s)).card = s.card + 1 := by
  have hy : Sum.inr y ∉ liftCore (Y := Y) s := by simp [liftCore]
  rw [Finset.card_insert_of_notMem hy, liftCore_card]

theorem graph_uniform (d : SplitGadget X Y) (r : ℕ)
    (hcore : ∀ e ∈ d.core, e.card = r)
    (hl : ∀ y, (d.left y).card + 1 = r)
    (hr : ∀ y, (d.right y).card + 1 = r) : Uniform d.graph r := by
  intro e he
  change e ∈ d.core.image liftCore ∪
    Finset.univ.biUnion (fun y => {leftEdge d y, rightEdge d y}) at he
  rcases Finset.mem_union.mp he with he | he
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp he
    rw [liftCore_card, hcore s hs]
  · obtain ⟨y, _, he⟩ := Finset.mem_biUnion.mp he
    have he' : e = leftEdge d y ∨ e = rightEdge d y := by simpa using he
    rcases he' with rfl | rfl
    · change (insert (Sum.inr y) (liftCore (d.left y))).card = r
      rw [insert_liftCore_card, hl]
    · change (insert (Sum.inr y) (liftCore (d.right y))).card = r
      rw [insert_liftCore_card, hr]

theorem canonical_uniform [Fintype X] (m : ℕ) (p : X)
    (hsize : Fintype.card X = 2 * m) : Uniform (canonicalGadget m p).graph (m + 1) := by
  apply graph_uniform
  · intro e he
    exact (Finset.mem_powersetCard.mp he).2
  · intro y
    change y.val.card + 1 = m + 1
    rw [y.property.1]
  · intro y
    change ((Finset.univ : Finset X) \ y.val).card + 1 = m + 1
    have hs := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ y.val)
    rw [Finset.card_univ, hsize, y.property.1] at hs
    omega

end JSP692

/- ===== Module: AlonGeometry ===== -/

set_option autoImplicit false

/-!
All-parameter intersection, three-colourability, and active-vertex coverage
for Alon's construction. Each label is the half of a balanced partition
containing a fixed point p, so complementary halves share ONE new vertex.
-/

namespace JSP692

section Lifting
variable {X Y : Type*} [DecidableEq X] [DecidableEq Y]

@[simp] theorem inl_mem_liftCore (x : X) (s : Finset X) :
    Sum.inl x ∈ liftCore (Y := Y) s ↔ x ∈ s := by
  simp [liftCore]

/-- A common core vertex remains a common vertex after lifting and adding labels. -/
theorem intersect_of_core {a b : Finset X} {e f : Finset (X ⊕ Y)}
    (hab : (a ∩ b).Nonempty)
    (ha : liftCore a ⊆ e) (hb : liftCore b ⊆ f) :
    (e ∩ f).Nonempty := by
  obtain ⟨x, hx⟩ := hab
  refine ⟨Sum.inl x, Finset.mem_inter.mpr ⟨ha ?_, hb ?_⟩⟩
  · exact (inl_mem_liftCore x a).mpr (Finset.mem_inter.mp hx).1
  · exact (inl_mem_liftCore x b).mpr (Finset.mem_inter.mp hx).2

end Lifting

section Canonical
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {m : ℕ} {p : X}

/-- The other half of a balanced partition has the same cardinality. -/
theorem canonical_complement_card (hsize : Fintype.card X = 2 * m)
    (y : BalancedLabels m p) :
    ((Finset.univ : Finset X) \ y.val).card = m := by
  have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ y.val)
  rw [Finset.card_univ, hsize, y.property.1] at h
  omega

/-- Every constructed edge is a core edge or one of the two edges of a label. -/
theorem canonical_edge_cases {e : Finset (X ⊕ BalancedLabels m p)}
    (he : e ∈ (canonicalGadget m p).graph) :
    (∃ a : Finset X, a.card = m + 1 ∧ e = liftCore a) ∨
      ∃ y : BalancedLabels m p,
        e = leftEdge (canonicalGadget m p) y ∨
        e = rightEdge (canonicalGadget m p) y := by
  classical
  change e ∈ (canonicalGadget m p).core.image liftCore ∪
    Finset.univ.biUnion (fun y =>
      {leftEdge (canonicalGadget m p) y, rightEdge (canonicalGadget m p) y}) at he
  rcases Finset.mem_union.mp he with he | he
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    exact Or.inl ⟨a, (Finset.mem_powersetCard.mp ha).2, rfl⟩
  · obtain ⟨y, _, hy⟩ := Finset.mem_biUnion.mp he
    exact Or.inr ⟨y, by simpa only [Finset.mem_insert, Finset.mem_singleton] using hy⟩

theorem canonical_core_core (hsize : Fintype.card X = 2 * m)
    {a b : Finset X} (ha : a.card = m + 1) (hb : b.card = m + 1) :
    (liftCore (Y := BalancedLabels m p) a ∩ liftCore b).Nonempty := by
  have h : (a ∩ b).Nonempty :=
    Finset.inter_nonempty_of_card_lt_card_add_card
      (Finset.subset_univ a) (Finset.subset_univ b) (by
        rw [Finset.card_univ, hsize, ha, hb]
        omega)
  exact intersect_of_core h (fun _ hv => hv) (fun _ hv => hv)

theorem canonical_core_left (hsize : Fintype.card X = 2 * m)
    {a : Finset X} (ha : a.card = m + 1) (y : BalancedLabels m p) :
    (liftCore a ∩ leftEdge (canonicalGadget m p) y).Nonempty := by
  have h : (a ∩ y.val).Nonempty :=
    Finset.inter_nonempty_of_card_lt_card_add_card
      (Finset.subset_univ a) (Finset.subset_univ y.val) (by
        rw [Finset.card_univ, hsize, ha, y.property.1]
        omega)
  apply intersect_of_core h (fun _ hv => hv)
  intro v hv
  exact Finset.mem_insert_of_mem hv

theorem canonical_core_right (hsize : Fintype.card X = 2 * m)
    {a : Finset X} (ha : a.card = m + 1) (y : BalancedLabels m p) :
    (liftCore a ∩ rightEdge (canonicalGadget m p) y).Nonempty := by
  have h : (a ∩ ((Finset.univ : Finset X) \ y.val)).Nonempty :=
    Finset.inter_nonempty_of_card_lt_card_add_card
      (Finset.subset_univ a) (Finset.subset_univ _) (by
        rw [Finset.card_univ, hsize, ha, canonical_complement_card hsize y]
        omega)
  apply intersect_of_core h (fun _ hv => hv)
  intro v hv
  exact Finset.mem_insert_of_mem hv

/-- Two chosen representatives both contain the distinguished core point. -/
theorem canonical_left_left (y z : BalancedLabels m p) :
    (leftEdge (canonicalGadget m p) y ∩
      leftEdge (canonicalGadget m p) z).Nonempty := by
  apply intersect_of_core (a := y.val) (b := z.val)
    ⟨p, Finset.mem_inter.mpr ⟨y.property.2, z.property.2⟩⟩
  · intro v hv
    exact Finset.mem_insert_of_mem hv
  · intro v hv
    exact Finset.mem_insert_of_mem hv

/-- Disjoint opposite halves must belong to the same balanced partition. -/
theorem canonical_left_right (y z : BalancedLabels m p) :
    (leftEdge (canonicalGadget m p) y ∩
      rightEdge (canonicalGadget m p) z).Nonempty := by
  classical
  by_cases h : (y.val ∩ ((Finset.univ : Finset X) \ z.val)).Nonempty
  · apply intersect_of_core h
    · intro v hv
      exact Finset.mem_insert_of_mem hv
    · intro v hv
      exact Finset.mem_insert_of_mem hv
  · have hsub : y.val ⊆ z.val := by
      intro x hx
      by_contra hxz
      exact h ⟨x, Finset.mem_inter.mpr
        ⟨hx, Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxz⟩⟩⟩
    have heq : y.val = z.val := Finset.eq_of_subset_of_card_le hsub (by
      rw [y.property.1, z.property.1])
    have hyz : y = z := Subtype.ext heq
    subst z
    refine ⟨Sum.inr y, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_self _ _

/-- Opposite representatives avoid p, so two such halves cannot be disjoint. -/
theorem canonical_right_right (hm : 0 < m) (hsize : Fintype.card X = 2 * m)
    (y z : BalancedLabels m p) :
    (rightEdge (canonicalGadget m p) y ∩
      rightEdge (canonicalGadget m p) z).Nonempty := by
  have hsub (w : BalancedLabels m p) :
      (Finset.univ : Finset X) \ w.val ⊆ Finset.univ.erase p := by
    intro x hx
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ x⟩
    intro hxp
    exact (Finset.mem_sdiff.mp hx).2 (hxp.symm ▸ w.property.2)
  have h : (((Finset.univ : Finset X) \ y.val) ∩
      (Finset.univ \ z.val)).Nonempty :=
    Finset.inter_nonempty_of_card_lt_card_add_card (hsub y) (hsub z) (by
      rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ,
        hsize, canonical_complement_card hsize y, canonical_complement_card hsize z]
      omega)
  apply intersect_of_core h
  · intro v hv
    exact Finset.mem_insert_of_mem hv
  · intro v hv
    exact Finset.mem_insert_of_mem hv

/-- Alon's construction is intersecting at every positive half-rank. -/
theorem canonical_intersecting (hm : 0 < m) (hsize : Fintype.card X = 2 * m) :
    Intersecting (canonicalGadget m p).graph := by
  intro e he f hf
  rcases canonical_edge_cases he with ⟨a, ha, rfl⟩ | ⟨y, he⟩
  · rcases canonical_edge_cases hf with ⟨b, hb, rfl⟩ | ⟨z, hf⟩
    · exact canonical_core_core hsize ha hb
    · rcases hf with rfl | rfl
      · exact canonical_core_left hsize ha z
      · exact canonical_core_right hsize ha z
  · rcases he with rfl | rfl
    · rcases canonical_edge_cases hf with ⟨b, hb, rfl⟩ | ⟨z, hf⟩
      · simpa only [Finset.inter_comm] using canonical_core_left hsize hb y
      · rcases hf with rfl | rfl
        · exact canonical_left_left y z
        · exact canonical_left_right y z
    · rcases canonical_edge_cases hf with ⟨b, hb, rfl⟩ | ⟨z, hf⟩
      · simpa only [Finset.inter_comm] using canonical_core_right hsize hb y
      · rcases hf with rfl | rfl
        · simpa only [Finset.inter_comm] using canonical_left_right z y
        · exact canonical_right_right hm hsize y z

/-- Both colourability directions are included: the chromatic number is EXACTLY 3. -/
theorem canonical_threeChromatic (hm : 0 < m) (hsize : Fintype.card X = 2 * m) :
    ThreeChromatic (canonicalGadget m p).graph := by
  exact ⟨threeColorable_of_intersecting (r := m + 1) (by omega)
      (canonical_uniform m p hsize) (canonical_intersecting hm hsize),
    canonical_not_twoColorable m p hsize⟩

/-- Every ambient vertex occurs in an edge. No isolated vertices pad the count. -/
theorem canonical_support_eq_univ (hm : 0 < m) (hsize : Fintype.card X = 2 * m) :
    support (canonicalGadget m p).graph = Finset.univ := by
  classical
  ext v
  constructor
  · intro _
    exact Finset.mem_univ v
  · intro _
    change v ∈ (canonicalGadget m p).graph.biUnion id
    rcases v with x | y
    · obtain ⟨s, hxs, hsU, hscard⟩ :=
        Finset.exists_subsuperset_card_eq
          (s := {x}) (t := (Finset.univ : Finset X)) (n := m + 1)
          (Finset.subset_univ _) (by simp) (by
            rw [Finset.card_univ, hsize]
            omega)
      have hs : s ∈ (canonicalGadget m p).core :=
        Finset.mem_powersetCard.mpr ⟨hsU, hscard⟩
      refine Finset.mem_biUnion.mpr ⟨liftCore s, coreEdge_mem _ hs, ?_⟩
      exact (inl_mem_liftCore x s).mpr (hxs (Finset.mem_singleton_self x))
    · refine Finset.mem_biUnion.mpr
        ⟨leftEdge (canonicalGadget m p) y, leftEdge_mem _ y, ?_⟩
      exact Finset.mem_insert_self _ _

end Canonical
end JSP692

/- ===== Module: Relabel ===== -/

set_option autoImplicit false

/-! Transport to Fin n without changing edges, colours, or vertex coverage. -/
namespace JSP692

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

def relabel (e : V ≃ W) (H : Hypergraph V) : Hypergraph W :=
  H.image (fun a => a.image e)

theorem uniform_relabel (e : V ≃ W) {H : Hypergraph V} {r : ℕ}
    (hu : Uniform H r) : Uniform (relabel e H) r := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  rw [Finset.card_image_of_injective b e.injective, hu b hb]

theorem intersecting_relabel (e : V ≃ W) {H : Hypergraph V}
    (hi : Intersecting H) : Intersecting (relabel e H) := by
  intro a ha b hb
  obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨x, hx⟩ := hi a' ha' b' hb'
  exact ⟨e x, Finset.mem_inter.mpr
    ⟨Finset.mem_image.mpr ⟨x, (Finset.mem_inter.mp hx).1, rfl⟩,
     Finset.mem_image.mpr ⟨x, (Finset.mem_inter.mp hx).2, rfl⟩⟩⟩

theorem proper_relabel_iff {C : Type*} (e : V ≃ W)
    (H : Hypergraph V) (c : W → C) :
    Proper (relabel e H) c ↔ Proper H (fun v => c (e v)) := by
  constructor
  · intro h a ha
    have hamem : a.image e ∈ relabel e H := Finset.mem_image.mpr ⟨a, ha, rfl⟩
    obtain ⟨u, hu, v, hv, hne⟩ := h (a.image e) hamem
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨x, hx, y, hy, hne⟩
  · intro h a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨x, hx, y, hy, hne⟩ := h b hb
    exact ⟨e x, Finset.mem_image.mpr ⟨x, hx, rfl⟩,
      e y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, hne⟩

theorem threeChromatic_relabel (e : V ≃ W) {H : Hypergraph V}
    (h : ThreeChromatic H) : ThreeChromatic (relabel e H) := by
  constructor
  · obtain ⟨c, hc⟩ := h.1
    refine ⟨fun w => c (e.symm w), (proper_relabel_iff e H _).mpr ?_⟩
    simpa only [Equiv.symm_apply_apply] using hc
  · rintro ⟨c, hc⟩
    exact h.2 ⟨fun v => c (e v), (proper_relabel_iff e H c).mp hc⟩

theorem support_relabel_eq_univ [Fintype V] [Fintype W]
    (e : V ≃ W) {H : Hypergraph V} (h : support H = Finset.univ) :
    support (relabel e H) = Finset.univ := by
  classical
  ext w
  constructor
  · intro _
    exact Finset.mem_univ w
  · intro _
    have hx : e.symm w ∈ support H := by rw [h]; exact Finset.mem_univ _
    obtain ⟨a, ha, hxa⟩ := Finset.mem_biUnion.mp hx
    refine Finset.mem_biUnion.mpr
      ⟨a.image e, Finset.mem_image.mpr ⟨a, ha, rfl⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨e.symm w, hxa, e.apply_symm_apply w⟩

end JSP692

/- ===== Module: AlonGrowth ===== -/

set_option autoImplicit false

/-!
Exponential activity in every rank, with an explicit injection of Boolean
vectors into balanced partitions. No isolated vertices and no asymptotic
estimate are assumed. The cubic estimate at the end is proved by induction.
-/

namespace JSP692

/-- m+1 disjoint pairs, with the distinguished pair indexed by none. -/
abbrev AlonCore (m : ℕ) := Option (Fin m) × Bool

def alonPoint (m : ℕ) : AlonCore m := (none, false)

abbrev AlonLabels (m : ℕ) := BalancedLabels (m + 1) (alonPoint m)
abbrev AlonVertex (m : ℕ) := AlonCore m ⊕ AlonLabels m

def alonGraph (m : ℕ) : Hypergraph (AlonVertex m) :=
  (canonicalGadget (m + 1) (alonPoint m)).graph

theorem alon_core_card (m : ℕ) : Fintype.card (AlonCore m) = 2 * (m + 1) := by
  simp [AlonCore, Nat.mul_comm]

/-- Choose one point from each pair; the distinguished choice is fixed. -/
def selectedHalf (m : ℕ) (b : Fin m → Bool) : Finset (AlonCore m) :=
  insert (alonPoint m) (Finset.univ.image (fun i : Fin m => (some i, b i)))

theorem selectedHalf_card (m : ℕ) (b : Fin m → Bool) :
    (selectedHalf m b).card = m + 1 := by
  have hn : alonPoint m ∉
      (Finset.univ : Finset (Fin m)).image (fun i => (some i, b i)) := by
    simp [alonPoint]
  have hinj : Function.Injective (fun i : Fin m => (some i, b i)) := by
    intro i j hij
    exact Option.some.inj (congrArg Prod.fst hij)
  rw [selectedHalf, Finset.card_insert_of_notMem hn,
    Finset.card_image_of_injective _ hinj]
  simp

theorem selectedHalf_contains_point (m : ℕ) (b : Fin m → Bool) :
    alonPoint m ∈ selectedHalf m b :=
  Finset.mem_insert_self _ _

def selectedLabel (m : ℕ) (b : Fin m → Bool) : AlonLabels m :=
  ⟨selectedHalf m b, selectedHalf_card m b, selectedHalf_contains_point m b⟩

theorem selectedHalf_injective (m : ℕ) : Function.Injective (selectedHalf m) := by
  intro b c heq
  funext i
  have hi : (some i, b i) ∈ selectedHalf m b :=
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  rw [heq] at hi
  rcases Finset.mem_insert.mp hi with hi | hi
  · have hbad : (some i : Option (Fin m)) = none := congrArg Prod.fst hi
    cases hbad
  · obtain ⟨j, _, hji⟩ := Finset.mem_image.mp hi
    have h : j = i := Option.some.inj (congrArg Prod.fst hji)
    subst j
    exact (congrArg Prod.snd hji).symm

theorem selectedLabel_injective (m : ℕ) : Function.Injective (selectedLabel m) := by
  intro b c heq
  apply selectedHalf_injective m
  exact congrArg Subtype.val heq

/-- There are at least 2^m genuine partition vertices. -/
theorem alon_labels_lower_bound (m : ℕ) : 2 ^ m ≤ Fintype.card (AlonLabels m) := by
  have h := Fintype.card_le_of_injective (selectedLabel m) (selectedLabel_injective m)
  simpa using h

theorem alon_vertex_lower_bound (m : ℕ) : 2 ^ m ≤ Fintype.card (AlonVertex m) := by
  have h := alon_labels_lower_bound m
  simp only [AlonVertex, Fintype.card_sum]
  omega

theorem alon_uniform (m : ℕ) : Uniform (alonGraph m) (m + 2) :=
  canonical_uniform (m + 1) (alonPoint m) (alon_core_card m)

theorem alon_intersecting (m : ℕ) : Intersecting (alonGraph m) :=
  canonical_intersecting (m := m + 1) (p := alonPoint m) (by omega) (alon_core_card m)

theorem alon_threeChromatic (m : ℕ) : ThreeChromatic (alonGraph m) :=
  canonical_threeChromatic (m := m + 1) (p := alonPoint m) (by omega) (alon_core_card m)

theorem alon_support_eq_univ (m : ℕ) : support (alonGraph m) = Finset.univ :=
  canonical_support_eq_univ (m := m + 1) (p := alonPoint m) (by omega) (alon_core_card m)

/-- Relabel by a genuine equivalence; no extra ambient vertices are introduced. -/
noncomputable def alonFin (m : ℕ) :
    Hypergraph (Fin (Fintype.card (AlonVertex m))) :=
  relabel (Fintype.equivFin (AlonVertex m)) (alonGraph m)

theorem alonFin_uniform (m : ℕ) : Uniform (alonFin m) (m + 2) :=
  uniform_relabel (Fintype.equivFin (AlonVertex m)) (alon_uniform m)

theorem alonFin_intersecting (m : ℕ) : Intersecting (alonFin m) :=
  intersecting_relabel (Fintype.equivFin (AlonVertex m)) (alon_intersecting m)

theorem alonFin_threeChromatic (m : ℕ) : ThreeChromatic (alonFin m) :=
  threeChromatic_relabel (Fintype.equivFin (AlonVertex m)) (alon_threeChromatic m)

theorem alonFin_support_eq_univ (m : ℕ) : support (alonFin m) = Finset.univ :=
  support_relabel_eq_univ (Fintype.equivFin (AlonVertex m)) (alon_support_eq_univ m)

theorem alonFin_active_card (m : ℕ) :
    (support (alonFin m)).card = Fintype.card (AlonVertex m) := by
  rw [alonFin_support_eq_univ, Finset.card_univ, Fintype.card_fin]

theorem alonFin_active_lower_bound (m : ℕ) :
    2 ^ m ≤ (support (alonFin m)).card := by
  rw [alonFin_active_card]
  exact alon_vertex_lower_bound m

/-- A construction in EVERY rank r >= 2, not a finite collection of examples. -/
theorem alon_for_every_rank (r : ℕ) (hr : 2 ≤ r) :
    ∃ n : ℕ, ∃ H : Hypergraph (Fin n),
      Uniform H r ∧ ThreeChromatic H ∧ Intersecting H ∧
      support H = Finset.univ ∧ 2 ^ (r - 2) ≤ (support H).card := by
  refine ⟨Fintype.card (AlonVertex (r - 2)), alonFin (r - 2), ?_,
    alonFin_threeChromatic _, alonFin_intersecting _, alonFin_support_eq_univ _,
    alonFin_active_lower_bound _⟩
  have h := alonFin_uniform (r - 2)
  simpa only [Nat.sub_add_cancel hr] using h

/-- Elementary exponential growth: no Stirling formula or imported asymptotic
claim is needed. The chosen base case is 14^3 <= 2^12. -/
theorem cubic_le_two_pow (k : ℕ) : (k + 14) ^ 3 ≤ 2 ^ (k + 12) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    calc
      (k + 1 + 14) ^ 3 ≤ 2 * (k + 14) ^ 3 := by
        nlinarith [Nat.zero_le (k ^ 3), Nat.zero_le (k ^ 2)]
      _ ≤ 2 * 2 ^ (k + 12) := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (k + 1 + 12) := by
        rw [show k + 1 + 12 = (k + 12) + 1 by omega, pow_succ]
        ring

/-- Explicitly outrun ANY real quadratic coefficient after ANY rank threshold. -/
theorem alon_exceeds_every_quadratic (C : ℝ) (R : ℕ) :
    ∃ m : ℕ, R ≤ m + 2 ∧
      C * ((m + 2 : ℕ) : ℝ) ^ 2 < ((support (alonFin m)).card : ℝ) := by
  obtain ⟨k, hk⟩ := exists_nat_gt C
  let m : ℕ := k + R + 12
  have hpoly : (m + 2) ^ 3 ≤ 2 ^ m := by
    simpa only [m, Nat.add_assoc] using cubic_le_two_pow (k + R)
  have hnk : k < m + 2 := by dsimp [m]; omega
  have hrk : (k : ℝ) < ((m + 2 : ℕ) : ℝ) := by exact_mod_cast hnk
  have hC : C < ((m + 2 : ℕ) : ℝ) := hk.trans hrk
  have hpos : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) ^ 2 := by positivity
  have hpolyR : (((m + 2 : ℕ) : ℝ)) ^ 3 ≤ ((2 ^ m : ℕ) : ℝ) := by
    exact_mod_cast hpoly
  have hcountR : ((2 ^ m : ℕ) : ℝ) ≤ ((support (alonFin m)).card : ℝ) := by
    exact_mod_cast alonFin_active_lower_bound m
  refine ⟨m, by dsimp [m]; omega, ?_⟩
  calc
    C * ((m + 2 : ℕ) : ℝ) ^ 2 <
        ((m + 2 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) ^ 2 :=
      mul_lt_mul_of_pos_right hC hpos
    _ = ((m + 2 : ℕ) : ℝ) ^ 3 := by ring
    _ ≤ ((2 ^ m : ℕ) : ℝ) := hpolyR
    _ ≤ ((support (alonFin m)).card : ℝ) := hcountR

end JSP692

/- ===== Module: LinearIntersection ===== -/

set_option autoImplicit false

/-!
# A linear intersection bound for Erdős 836, question 2 (JSP-000692)

All mathematical steps in this file have proof bodies. No extra hypotheses
asserting the desired combinatorial bound are used.

AUTHORING STATUS: complete candidate proof; NOT COMPILED in this environment.
The accompanying MATHEMATICS.md gives the full extremal-colouring argument.
-/

open scoped BigOperators

namespace JSP692

/-- A square zero-one matrix with at most s ones in every row and at most s
zeros in every column has order at most 2s. -/
theorem square_matrix_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (P : α → β → Prop)
    [∀ a b, Decidable (P a b)] {n s : ℕ}
    (ha : A.card = n) (hb : B.card = n) (hn : 0 < n)
    (hrow : ∀ a ∈ A, (B.filter (P a)).card ≤ s)
    (hcol : ∀ b ∈ B, (A.filter (fun a => ¬ P a b)).card ≤ s) :
    n ≤ 2 * s := by
  classical
  have hones : (∑ a ∈ A, (B.filter (P a)).card) ≤ n * s := by
    calc
      (∑ a ∈ A, (B.filter (P a)).card) ≤ ∑ _a ∈ A, s :=
        Finset.sum_le_sum (fun a hA => hrow a hA)
      _ = n * s := by simp [ha]
  have htranspose :
      (∑ a ∈ A, (B.filter (fun b => ¬ P a b)).card) =
        ∑ b ∈ B, (A.filter (fun a => ¬ P a b)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have hzeros :
      (∑ a ∈ A, (B.filter (fun b => ¬ P a b)).card) ≤ n * s := by
    rw [htranspose]
    calc
      (∑ b ∈ B, (A.filter (fun a => ¬ P a b)).card) ≤ ∑ _b ∈ B, s :=
        Finset.sum_le_sum (fun b hB => hcol b hB)
      _ = n * s := by simp [hb]
  have htotal :
      (∑ a ∈ A, (B.filter (P a)).card) +
        (∑ a ∈ A, (B.filter (fun b => ¬ P a b)).card) = n * n := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ a ∈ A, ((B.filter (P a)).card +
          (B.filter (fun b => ¬ P a b)).card)) = ∑ _a ∈ A, B.card := by
        apply Finset.sum_congr rfl
        intro a haA
        exact Finset.card_filter_add_card_filter_not (s := B) (p := P a)
      _ = n * n := by simp [ha, hb]
  by_contra h
  have hlt : 2 * s < n := Nat.lt_of_not_ge h
  have hprod : n * (2 * s) < n * n := Nat.mul_lt_mul_of_pos_left hlt hn
  nlinarith

section Finite

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A vertex set containing the prescribed edge E and no other edge. -/
def OnlyEdge (H : Hypergraph V) (E R : Finset V) : Prop :=
  E ⊆ R ∧ ∀ f ∈ H, f ⊆ R → f = E

/-- Maximize the size of a set containing just one prescribed edge.
Every vertex outside it creates another edge when added. -/
theorem exists_maximal_only_edge {H : Hypergraph V} {r : ℕ}
    (hu : Uniform H r) {E : Finset V} (hE : E ∈ H) :
    ∃ R : Finset V, OnlyEdge H E R ∧
      ∀ y ∉ R, ∃ f ∈ H, f ≠ E ∧ f ⊆ insert y R := by
  classical
  let candidates : Finset (Finset V) :=
    Finset.univ.filter (OnlyEdge H E)
  have hstart : OnlyEdge H E E := by
    refine ⟨fun _ hv => hv, ?_⟩
    intro f hf hfE
    apply Finset.eq_of_subset_of_card_le hfE
    rw [hu E hE, hu f hf]
  have hEmem : E ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hstart
  obtain ⟨R, hRmem, hmax⟩ :=
    Finset.exists_max_image candidates Finset.card ⟨E, hEmem⟩
  have hR : OnlyEdge H E R := (Finset.mem_filter.mp hRmem).2
  refine ⟨R, hR, ?_⟩
  intro y hy
  by_contra hfail
  have hnew : OnlyEdge H E (insert y R) := by
    refine ⟨fun v hv => Finset.mem_insert_of_mem (hR.1 hv), ?_⟩
    intro f hf hfsub
    by_contra hne
    exact hfail ⟨f, hf, hne, hfsub⟩
  have hnewmem : insert y R ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hnew
  have hbad := hmax (insert y R) hnewmem
  rw [Finset.card_insert_of_notMem hy] at hbad
  omega

/-- An independent set cannot be a transversal in a non-two-colorable
hypergraph. This is used with R \ {x}. -/
theorem edge_disjoint_of_independent {H : Hypergraph V}
    (hn : ¬ ∃ c : V → Bool, Proper H c) (S : Finset V)
    (hind : ∀ f ∈ H, ¬ f ⊆ S) :
    ∃ g ∈ H, Disjoint g S := by
  classical
  by_contra hfail
  have hhit : ∀ f ∈ H, (f ∩ S).Nonempty := by
    intro f hf
    by_contra hempty
    apply hfail
    refine ⟨f, hf, Finset.disjoint_left.mpr ?_⟩
    intro v hvf hvS
    exact hempty ⟨v, Finset.mem_inter.mpr ⟨hvf, hvS⟩⟩
  obtain ⟨f, hf, hfS⟩ := transversal_contains_edge hn S hhit
  exact hind f hf hfS

/-- Removing x from a set containing exactly E leaves an independent set.
The resulting opposite-colour edge meets the original set exactly at x. -/
theorem edge_meets_only_set_at_point {H : Hypergraph V}
    (hi : Intersecting H) (hn : ¬ ∃ c : V → Bool, Proper H c)
    {E R : Finset V} (hE : E ∈ H) (hR : OnlyEdge H E R)
    {x : V} (hx : x ∈ E) :
    ∃ g ∈ H, g ∩ R = {x} := by
  classical
  have hind : ∀ f ∈ H, ¬ f ⊆ R.erase x := by
    intro f hf hfsub
    have hfR : f ⊆ R := hfsub.trans (Finset.erase_subset x R)
    have hfe : f = E := hR.2 f hf hfR
    have hxerase : x ∈ R.erase x := hfsub (hfe.symm ▸ hx)
    exact (Finset.mem_erase.mp hxerase).1 rfl
  obtain ⟨g, hg, hd⟩ := edge_disjoint_of_independent hn (R.erase x) hind
  have hsubset : g ∩ R ⊆ {x} := by
    intro v hv
    obtain ⟨hvg, hvR⟩ := Finset.mem_inter.mp hv
    apply Finset.mem_singleton.mpr
    by_contra hvx
    exact (Finset.disjoint_left.mp hd) hvg (Finset.mem_erase.mpr ⟨hvx, hvR⟩)
  obtain ⟨v, hv⟩ := hi g hg E hE
  have hvg : v ∈ g := (Finset.mem_inter.mp hv).1
  have hvR : v ∈ R := hR.1 (Finset.mem_inter.mp hv).2
  have hvx : v = x :=
    Finset.mem_singleton.mp (hsubset (Finset.mem_inter.mpr ⟨hvg, hvR⟩))
  have hxgR : x ∈ g ∩ R := by
    simpa only [hvx] using Finset.mem_inter.mpr ⟨hvg, hvR⟩
  refine ⟨g, hg, le_antisymm hsubset ?_⟩
  intro v hv
  have hvx : v = x := Finset.mem_singleton.mp hv
  simpa only [hvx] using hxgR

/-- The principal bound. If every intersection of DISTINCT edges has size
at most s, then the uniformity r satisfies r ≤ 2s+1. -/
theorem rank_le_twice_intersection_bound_add_one {H : Hypergraph V} {r s : ℕ}
    (hr : 2 ≤ r) (hu : Uniform H r) (hi : Intersecting H)
    (hn : ¬ ∃ c : V → Bool, Proper H c)
    (hs : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ s) :
    r ≤ 2 * s + 1 := by
  classical
  have hH : H.Nonempty := by
    by_contra hnone
    apply hn
    refine ⟨fun _ => false, ?_⟩
    intro e he
    exact False.elim (hnone ⟨e, he⟩)
  obtain ⟨E, hE⟩ := hH
  obtain ⟨R, hR, hmax⟩ := exists_maximal_only_edge hu hE

  -- For every x in E choose an edge g(x) meeting R only at x.
  have hchooseG : ∀ x : V, ∃ g : Finset V,
      x ∈ E → g ∈ H ∧ g ∩ R = {x} := by
    intro x
    by_cases hx : x ∈ E
    · obtain ⟨g, hg, hgR⟩ := edge_meets_only_set_at_point hi hn hE hR hx
      exact ⟨g, fun _ => ⟨hg, hgR⟩⟩
    · exact ⟨∅, fun h => False.elim (hx h)⟩
  choose g hg using hchooseG

  -- For every y outside R choose the new edge created by adding y.
  have hchooseF : ∀ y : V, ∃ f : Finset V,
      y ∉ R → f ∈ H ∧ f ≠ E ∧ f ⊆ insert y R := by
    intro y
    by_cases hy : y ∉ R
    · obtain ⟨f, hf, hfE, hfsub⟩ := hmax y hy
      exact ⟨f, fun _ => ⟨hf, hfE, hfsub⟩⟩
    · exact ⟨∅, fun h => False.elim (hy h)⟩
  choose f hf using hchooseF

  have hEpos : 0 < E.card := by rw [hu E hE]; omega
  obtain ⟨x₀, hx₀⟩ := Finset.card_pos.mp hEpos
  have hg₀H : g x₀ ∈ H := (hg x₀ hx₀).1
  have hg₀R : g x₀ ∩ R = {x₀} := (hg x₀ hx₀).2
  have hx₀g : x₀ ∈ g x₀ := by
    have h : x₀ ∈ g x₀ ∩ R := by rw [hg₀R]; simp
    exact (Finset.mem_inter.mp h).1
  let A : Finset V := E.erase x₀
  let B : Finset V := (g x₀).erase x₀
  have hAcard : A.card = r - 1 := by
    dsimp [A]
    rw [Finset.card_erase_of_mem hx₀, hu E hE]
  have hBcard : B.card = r - 1 := by
    dsimp [B]
    rw [Finset.card_erase_of_mem hx₀g, hu (g x₀) hg₀H]
  have hBout : ∀ y ∈ B, y ∉ R := by
    intro y hy hyR
    have hy' : y ∈ (g x₀).erase x₀ := hy
    have hyg := (Finset.mem_erase.mp hy').2
    have hyne := (Finset.mem_erase.mp hy').1
    have hmem : y ∈ g x₀ ∩ R := Finset.mem_inter.mpr ⟨hyg, hyR⟩
    rw [hg₀R] at hmem
    exact hyne (Finset.mem_singleton.mp hmem)

  -- Rows of the matrix P(x,y) := y ∈ g(x) have at most s ones.
  have hrow : ∀ x ∈ A, (B.filter (fun y => y ∈ g x)).card ≤ s := by
    intro x hx
    have hx' : x ∈ E.erase x₀ := hx
    have hxE := (Finset.mem_erase.mp hx').2
    have hxne := (Finset.mem_erase.mp hx').1
    have hgxH : g x ∈ H := (hg x hxE).1
    have hgxR : g x ∩ R = {x} := (hg x hxE).2
    have hgne : g x ≠ g x₀ := by
      intro heq
      have hmem : x ∈ g x ∩ R := by rw [hgxR]; simp
      rw [heq, hg₀R] at hmem
      exact hxne (Finset.mem_singleton.mp hmem)
    have hsub : B.filter (fun y => y ∈ g x) ⊆ g x ∩ g x₀ := by
      intro y hy
      obtain ⟨hyB, hyg⟩ := Finset.mem_filter.mp hy
      have hy' : y ∈ (g x₀).erase x₀ := hyB
      exact Finset.mem_inter.mpr ⟨hyg, (Finset.mem_erase.mp hy').2⟩
    exact (Finset.card_le_card hsub).trans (hs (g x) hgxH (g x₀) hg₀H hgne)

  -- If y ∉ g(x), the intersection of f(y) and g(x) must be x.
  -- Consequently all zeros in column y are indexed by E ∩ f(y).
  have hcol : ∀ y ∈ B, (A.filter (fun x => y ∉ g x)).card ≤ s := by
    intro y hyB
    have hyR : y ∉ R := hBout y hyB
    obtain ⟨hfyH, hfyE, hfysub⟩ := hf y hyR
    have hsub : A.filter (fun x => y ∉ g x) ⊆ E ∩ f y := by
      intro x hx
      obtain ⟨hxA, hynot⟩ := Finset.mem_filter.mp hx
      have hx' : x ∈ E.erase x₀ := hxA
      have hxE := (Finset.mem_erase.mp hx').2
      have hgxH : g x ∈ H := (hg x hxE).1
      have hgxR : g x ∩ R = {x} := (hg x hxE).2
      obtain ⟨z, hz⟩ := hi (f y) hfyH (g x) hgxH
      have hzf : z ∈ f y := (Finset.mem_inter.mp hz).1
      have hzg : z ∈ g x := (Finset.mem_inter.mp hz).2
      have hzR : z ∈ R := by
        rcases Finset.mem_insert.mp (hfysub hzf) with hzy | hzR
        · exact False.elim (hynot (hzy ▸ hzg))
        · exact hzR
      have hzx : z = x := by
        have hmem : z ∈ g x ∩ R := Finset.mem_inter.mpr ⟨hzg, hzR⟩
        rw [hgxR] at hmem
        exact Finset.mem_singleton.mp hmem
      exact Finset.mem_inter.mpr ⟨hxE, hzx ▸ hzf⟩
    exact (Finset.card_le_card hsub).trans (hs E hE (f y) hfyH hfyE.symm)

  have hpositive : 0 < r - 1 := by omega
  have hmatrix : r - 1 ≤ 2 * s :=
    square_matrix_bound A B (fun x y => y ∈ g x)
      hAcard hBcard hpositive hrow hcol
  omega

/-- A distinct pair of edges has intersection size at least (r-1)/2.
The integral form avoids all rounding conventions. -/
theorem large_intersection_nat {H : Hypergraph V} {r : ℕ}
    (hr : 2 ≤ r) (hu : Uniform H r) (hi : Intersecting H)
    (hn : ¬ ∃ c : V → Bool, Proper H c) :
    ∃ e ∈ H, ∃ f ∈ H, e ≠ f ∧ r ≤ 2 * (e ∩ f).card + 1 := by
  classical
  by_contra hfail
  have hs : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ (r - 2) / 2 := by
    intro e he f hf hne
    have hnot : ¬ r ≤ 2 * (e ∩ f).card + 1 := by
      intro hbound
      exact hfail ⟨e, he, f, hf, hne, hbound⟩
    omega
  have hbad := rank_le_twice_intersection_bound_add_one hr hu hi hn hs
  omega

/-- A universal constant valid even at the Fano-plane boundary r=3. -/
theorem large_intersection_one_third {H : Hypergraph V} {r : ℕ}
    (hr : 2 ≤ r) (hu : Uniform H r) (hi : Intersecting H)
    (hn : ¬ ∃ c : V → Bool, Proper H c) :
    ∃ e ∈ H, ∃ f ∈ H, e ≠ f ∧
      (r : ℝ) / 3 ≤ ((e ∩ f).card : ℝ) := by
  obtain ⟨e, he, f, hf, hne, hbound⟩ := large_intersection_nat hr hu hi hn
  have hpos : 0 < (e ∩ f).card := Finset.card_pos.mpr (hi e he f hf)
  have hnat : r ≤ 3 * (e ∩ f).card := by omega
  have hreal : (r : ℝ) ≤ 3 * ((e ∩ f).card : ℝ) := by exact_mod_cast hnat
  refine ⟨e, he, f, hf, hne, ?_⟩
  linarith

/-- The requested linear-intersection assertion, with all quantifiers present.
Only the second question of JSP-000692 / Erdős 836 is asserted here. -/
theorem jsp000692_question_two :
    ∃ C : ℝ, 0 < C ∧
      ∀ r : ℕ, 2 ≤ r →
      ∀ n : ℕ, ∀ H : Hypergraph (Fin n),
        Uniform H r → ThreeChromatic H → Intersecting H →
        ∃ e ∈ H, ∃ f ∈ H, e ≠ f ∧
          C * (r : ℝ) ≤ ((e ∩ f).card : ℝ) := by
  refine ⟨1 / 3, by norm_num, ?_⟩
  intro r hr n H hu hc hi
  obtain ⟨e, he, f, hf, hne, hbound⟩ :=
    large_intersection_one_third hr hu hi hc.2
  refine ⟨e, he, f, hf, hne, ?_⟩
  nlinarith

end Finite
end JSP692

/- ===== Module: Complete ===== -/

set_option autoImplicit false

/-!
Both questions of JSP-000692 / Erdős 836 in one final theorem.
Question 1 counts support H (the union of all edges), never a padded ambient set.
The counterexamples additionally satisfy support H = univ.
Question 2 requires DISTINCT edges and a single positive real constant.
-/

namespace JSP692

/-- A putative eventual quadratic bound, uniform over all eligible hypergraphs. -/
def QuadraticVertexBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ R : ℕ,
    ∀ r : ℕ, 2 ≤ r → R ≤ r →
    ∀ n : ℕ, ∀ H : Hypergraph (Fin n),
      Uniform H r → ThreeChromatic H → Intersecting H →
      ((support H).card : ℝ) ≤ C * (r : ℝ) ^ 2

/-- The linear-intersection assertion, with the constant outside all other
quantifiers and the distinctness condition explicit. -/
def LinearIntersectionAssertion : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ r : ℕ, 2 ≤ r →
    ∀ n : ℕ, ∀ H : Hypergraph (Fin n),
      Uniform H r → ThreeChromatic H → Intersecting H →
      ∃ e ∈ H, ∃ f ∈ H, e ≠ f ∧
        C * (r : ℝ) ≤ ((e ∩ f).card : ℝ)

/-- Arbitrarily high-rank counterexamples to every quadratic coefficient.
This is stronger than a single witness with more than r^2 ambient vertices. -/
theorem quadratic_counterexamples (C : ℝ) (R : ℕ) :
    ∃ r : ℕ, 2 ≤ r ∧ R ≤ r ∧
      ∃ n : ℕ, ∃ H : Hypergraph (Fin n),
        Uniform H r ∧ ThreeChromatic H ∧ Intersecting H ∧
        support H = Finset.univ ∧
        C * (r : ℝ) ^ 2 < ((support H).card : ℝ) := by
  obtain ⟨m, hmR, hbig⟩ := alon_exceeds_every_quadratic C R
  exact ⟨m + 2, by omega, hmR, Fintype.card (AlonVertex m), alonFin m,
    alonFin_uniform m, alonFin_threeChromatic m, alonFin_intersecting m,
    alonFin_support_eq_univ m, hbig⟩

/-- Question 1: NO, even when isolated vertices are forbidden. -/
theorem jsp000692_question_one : ¬ QuadraticVertexBound := by
  rintro ⟨C, _hC, R, hbound⟩
  obtain ⟨r, hr, hR, n, H, hu, hc, hi, _hfull, hbig⟩ :=
    quadratic_counterexamples C R
  exact (not_le_of_gt hbig) (hbound r hr hR n H hu hc hi)

/-- Question 2: YES, with the explicit universal constant 1/3. -/
theorem jsp000692_question_two_assertion : LinearIntersectionAssertion :=
  jsp000692_question_two

/-- The complete pair of answers, on the SAME definitions of eligible
hypergraph, colourability, active vertices, and edge intersection. -/
theorem jsp000692_complete : ¬ QuadraticVertexBound ∧ LinearIntersectionAssertion :=
  ⟨jsp000692_question_one, jsp000692_question_two_assertion⟩

/-- Fully expanded alternative final theorem for statement-to-problem review. -/
theorem jsp000692_complete_explicit :
    (∀ C : ℝ, ∀ R : ℕ,
      ∃ r : ℕ, 2 ≤ r ∧ R ≤ r ∧
        ∃ n : ℕ, ∃ H : Hypergraph (Fin n),
          Uniform H r ∧ ThreeChromatic H ∧ Intersecting H ∧
          support H = Finset.univ ∧
          C * (r : ℝ) ^ 2 < ((support H).card : ℝ)) ∧
    (∀ r : ℕ, 2 ≤ r →
      ∀ n : ℕ, ∀ H : Hypergraph (Fin n),
        Uniform H r → ThreeChromatic H → Intersecting H →
        ∃ e ∈ H, ∃ f ∈ H, e ≠ f ∧
          (r : ℝ) / 3 ≤ ((e ∩ f).card : ℝ)) := by
  constructor
  · exact quadratic_counterexamples
  · intro r hr n H hu hc hi
    exact large_intersection_one_third hr hu hi hc.2

end JSP692

#print axioms JSP692.not_proper_of_mono
#print axioms JSP692.transversal_contains_edge
#print axioms JSP692.threeColorable_of_intersecting
#print axioms JSP692.coreEdge_mem
#print axioms JSP692.leftEdge_mem
#print axioms JSP692.rightEdge_mem
#print axioms JSP692.mono_liftCore
#print axioms JSP692.mono_insert_liftCore
#print axioms JSP692.not_twoColorable_of_coreObstructs
#print axioms JSP692.coreObstructs_of_balanced_splits
#print axioms JSP692.canonical_coreObstructs
#print axioms JSP692.canonical_not_twoColorable
#print axioms JSP692.liftCore_card
#print axioms JSP692.insert_liftCore_card
#print axioms JSP692.graph_uniform
#print axioms JSP692.canonical_uniform
#print axioms JSP692.inl_mem_liftCore
#print axioms JSP692.intersect_of_core
#print axioms JSP692.canonical_complement_card
#print axioms JSP692.canonical_edge_cases
#print axioms JSP692.canonical_core_core
#print axioms JSP692.canonical_core_left
#print axioms JSP692.canonical_core_right
#print axioms JSP692.canonical_left_left
#print axioms JSP692.canonical_left_right
#print axioms JSP692.canonical_right_right
#print axioms JSP692.canonical_intersecting
#print axioms JSP692.canonical_threeChromatic
#print axioms JSP692.canonical_support_eq_univ
#print axioms JSP692.uniform_relabel
#print axioms JSP692.intersecting_relabel
#print axioms JSP692.proper_relabel_iff
#print axioms JSP692.threeChromatic_relabel
#print axioms JSP692.support_relabel_eq_univ
#print axioms JSP692.alon_core_card
#print axioms JSP692.selectedHalf_card
#print axioms JSP692.selectedHalf_contains_point
#print axioms JSP692.selectedHalf_injective
#print axioms JSP692.selectedLabel_injective
#print axioms JSP692.alon_labels_lower_bound
#print axioms JSP692.alon_vertex_lower_bound
#print axioms JSP692.alon_uniform
#print axioms JSP692.alon_intersecting
#print axioms JSP692.alon_threeChromatic
#print axioms JSP692.alon_support_eq_univ
#print axioms JSP692.alonFin_uniform
#print axioms JSP692.alonFin_intersecting
#print axioms JSP692.alonFin_threeChromatic
#print axioms JSP692.alonFin_support_eq_univ
#print axioms JSP692.alonFin_active_card
#print axioms JSP692.alonFin_active_lower_bound
#print axioms JSP692.alon_for_every_rank
#print axioms JSP692.cubic_le_two_pow
#print axioms JSP692.alon_exceeds_every_quadratic
#print axioms JSP692.square_matrix_bound
#print axioms JSP692.exists_maximal_only_edge
#print axioms JSP692.edge_disjoint_of_independent
#print axioms JSP692.edge_meets_only_set_at_point
#print axioms JSP692.rank_le_twice_intersection_bound_add_one
#print axioms JSP692.large_intersection_nat
#print axioms JSP692.large_intersection_one_third
#print axioms JSP692.jsp000692_question_two
#print axioms JSP692.quadratic_counterexamples
#print axioms JSP692.jsp000692_question_one
#print axioms JSP692.jsp000692_question_two_assertion
#print axioms JSP692.jsp000692_complete
#print axioms JSP692.jsp000692_complete_explicit
