import JSP692.SplitGadget

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
