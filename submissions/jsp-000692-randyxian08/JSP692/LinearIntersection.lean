import JSP692.Hypergraph

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
