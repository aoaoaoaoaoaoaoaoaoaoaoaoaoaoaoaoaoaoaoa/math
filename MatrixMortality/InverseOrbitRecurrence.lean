import MatrixMortality.ShearEuclidean

/-!
# Bounded inverse recurrence forces a target stabilizer

An infinite sequence of distinct group elements cannot carry one rational
projective target through a bounded set of primitive integral rays unless two
orbit states coincide.  Their quotient is then a nonidentity element of the
target stabilizer.  Consequently every infinite inverse normal-form path at a
target with trivial stabilizer has unbounded primitive height.
-/

set_option autoImplicit false

namespace MatrixMortality.InverseOrbitRecurrence

/-- Integral homogeneous pairs whose maximum-coordinate height is bounded. -/
def integralPairBox (bound : ℕ) : Set ShearEuclidean.IntegralPair :=
  {pair | ShearEuclidean.pairHeight pair ≤ bound}

/-- Every bounded integral-pair box is finite. -/
theorem integralPairBox_finite (bound : ℕ) :
    (integralPairBox bound).Finite := by
  apply (Set.finite_Icc (-(bound : ℤ)) (bound : ℤ)).prod
      (Set.finite_Icc (-(bound : ℤ)) (bound : ℤ)) |>.subset
  rintro ⟨first, second⟩ pair_bounded
  have first_bounded : first.natAbs ≤ bound := by
    exact (le_max_left first.natAbs second.natAbs).trans pair_bounded
  have second_bounded : second.natAbs ≤ bound := by
    exact (le_max_right first.natAbs second.natAbs).trans pair_bounded
  have first_cast_bounded : (first.natAbs : ℤ) ≤ bound := by
    exact_mod_cast first_bounded
  have second_cast_bounded : (second.natAbs : ℤ) ≤ bound := by
    exact_mod_cast second_bounded
  constructor
  · constructor
    · calc
        -(bound : ℤ) ≤ -(first.natAbs : ℤ) := neg_le_neg first_cast_bounded
        _ = -|first| := by simp
        _ ≤ first := neg_abs_le first
    · exact Int.le_natAbs.trans first_cast_bounded
  · constructor
    · calc
        -(bound : ℤ) ≤ -(second.natAbs : ℤ) := neg_le_neg second_cast_bounded
        _ = -|second| := by simp
        _ ≤ second := neg_abs_le second
    · exact Int.le_natAbs.trans second_cast_bounded

/-- A coprime integral representative of one rational projective ray. -/
def PrimitivePair :=
  {pair : ShearEuclidean.IntegralPair // IsCoprime pair.1 pair.2}

/-- Maximum-coordinate height of a primitive integral ray representative. -/
def primitiveHeight (pair : PrimitivePair) : ℕ :=
  ShearEuclidean.pairHeight pair.1

/-- Rational projective point represented by a primitive integral pair. -/
noncomputable def primitivePoint (pair : PrimitivePair) : ProjectiveLine.Point ℚ :=
  ProjectiveLine.ofPair (pair.1.1 : ℚ) (pair.1.2 : ℚ)

/-- Primitive ray representatives of height at most the supplied bound. -/
def primitivePairBox (bound : ℕ) : Set PrimitivePair :=
  {pair | primitiveHeight pair ≤ bound}

/-- Every bounded primitive-ray box is finite. -/
theorem primitivePairBox_finite (bound : ℕ) :
    (primitivePairBox bound).Finite := by
  change (Subtype.val ⁻¹' integralPairBox bound).Finite
  exact (integralPairBox_finite bound).preimage
    (Set.injOn_of_injective Subtype.val_injective)

/-- A collision of two distinct group elements on one point produces a
nonidentity element of that point's stabilizer. -/
theorem exists_nontrivial_stabilizer_of_orbit_collision
    {G X : Type*} [Group G] [MulAction G X]
    {target : X} {left right : G}
    (distinct : left ≠ right)
    (collision : left • target = right • target) :
    ∃ stabilizer : G, stabilizer ≠ 1 ∧ stabilizer • target = target := by
  refine ⟨right⁻¹ * left, ?_, ?_⟩
  · intro quotient_one
    apply distinct
    calc
      left = right * (right⁻¹ * left) := by group
      _ = right := by rw [quotient_one]; simp
  · rw [mul_smul, collision, inv_smul_smul]

/-- Infinitely many distinct orbit prefixes represented inside one bounded
primitive-height box force a nontrivial target stabilizer. -/
theorem exists_nontrivial_stabilizer_of_bounded_primitive_orbit
    {G : Type*} [Group G] [MulAction G (ProjectiveLine.Point ℚ)]
    (target : ProjectiveLine.Point ℚ)
    (orbitPrefix : ℕ → G) (orbitPrefix_injective : Function.Injective orbitPrefix)
    (state : ℕ → PrimitivePair)
    (realizes : ∀ index, orbitPrefix index • target = primitivePoint (state index))
    (bound : ℕ) (bounded : ∀ index, primitiveHeight (state index) ≤ bound) :
    ∃ stabilizer : G, stabilizer ≠ 1 ∧ stabilizer • target = target := by
  have maps_into : Set.MapsTo state Set.univ (primitivePairBox bound) := by
    intro index _
    exact bounded index
  obtain ⟨left, _, right, _, indices_ne, states_eq⟩ :=
    Set.infinite_univ.exists_ne_map_eq_of_mapsTo maps_into
      (primitivePairBox_finite bound)
  have prefixes_ne : orbitPrefix left ≠ orbitPrefix right :=
    orbitPrefix_injective.ne indices_ne
  have collision : orbitPrefix left • target = orbitPrefix right • target := by
    calc
      orbitPrefix left • target = primitivePoint (state left) := realizes left
      _ = primitivePoint (state right) := by rw [states_eq]
      _ = orbitPrefix right • target := (realizes right).symm
  exact exists_nontrivial_stabilizer_of_orbit_collision prefixes_ne collision

/-- At a target with trivial stabilizer, every infinite sequence of distinct
normal-form prefixes has unbounded primitive height. -/
theorem primitiveHeight_unbounded_of_stabilizer_trivial
    {G : Type*} [Group G] [MulAction G (ProjectiveLine.Point ℚ)]
    (target : ProjectiveLine.Point ℚ)
    (orbitPrefix : ℕ → G) (orbitPrefix_injective : Function.Injective orbitPrefix)
    (state : ℕ → PrimitivePair)
    (realizes : ∀ index, orbitPrefix index • target = primitivePoint (state index))
    (stabilizer_trivial : ∀ element : G, element • target = target → element = 1) :
    ∀ bound, ∃ index, bound < primitiveHeight (state index) := by
  intro bound
  by_contra no_escape
  push Not at no_escape
  obtain ⟨stabilizer, stabilizer_ne, fixed⟩ :=
    exists_nontrivial_stabilizer_of_bounded_primitive_orbit target orbitPrefix
      orbitPrefix_injective state realizes bound no_escape
  exact stabilizer_ne (stabilizer_trivial stabilizer fixed)

end MatrixMortality.InverseOrbitRecurrence
