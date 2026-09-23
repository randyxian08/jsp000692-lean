import JSP692.AlonGeometry
import JSP692.Relabel

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
