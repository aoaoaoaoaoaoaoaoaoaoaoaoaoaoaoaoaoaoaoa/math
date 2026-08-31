import Mathlib.Data.Int.Interval
import MatrixMortality.ShearEuclidean

/-!
# Bounded inverse recurrence forces a target stabilizer

An infinite sequence of distinct group elements cannot carry one rational
projective target through a bounded set of primitive integral rays unless two
orbit states coincide.  Their quotient is then a nonidentity element of the
target stabilizer.  Consequently every infinite inverse normal-form path at a
target with trivial stabilizer has unbounded primitive height.  The explicit
integer cube sharpens this to a finite escape horizon: among
`(2 * H + 1) ^ 2 + 1` distinct prefixes, either some state has height above
`H` or two states expose a nontrivial target stabilizer.
-/

set_option autoImplicit false

namespace MatrixMortality.InverseOrbitRecurrence

/-- Integral homogeneous pairs whose maximum-coordinate height is bounded. -/
def integralPairBox (bound : ℕ) : Set ShearEuclidean.IntegralPair :=
  {pair | ShearEuclidean.pairHeight pair ≤ bound}

/-- The explicit finite integer square containing every pair of height at most
the supplied bound. -/
def integralPairCube (bound : ℕ) : Finset ShearEuclidean.IntegralPair :=
  @Finset.Icc ℤ Int.instLinearOrder.toPreorder Int.instLocallyFiniteOrder
      (-(bound : ℤ)) (bound : ℤ) ×ˢ
    @Finset.Icc ℤ Int.instLinearOrder.toPreorder Int.instLocallyFiniteOrder
      (-(bound : ℤ)) (bound : ℤ)

/-- The integer cube of radius `bound` contains exactly `(2 * bound + 1)²`
pairs. -/
theorem integralPairCube_card (bound : ℕ) :
    (integralPairCube bound).card = (2 * bound + 1) ^ 2 := by
  have interval_card :
      (Finset.Icc (-(bound : ℤ)) (bound : ℤ)).card = 2 * bound + 1 := by
    rw [Int.card_Icc]
    omega
  simp [integralPairCube, interval_card, pow_two]

/-- Every integral pair of maximum-coordinate height at most `bound` lies in
the explicit integer cube of radius `bound`. -/
theorem mem_integralPairCube_of_pairHeight_le
    {pair : ShearEuclidean.IntegralPair} {bound : ℕ}
    (bounded : ShearEuclidean.pairHeight pair ≤ bound) :
    pair ∈ integralPairCube bound := by
  simp only [integralPairCube, Finset.mem_product]
  have first_bounded : pair.1.natAbs ≤ bound :=
    (le_max_left pair.1.natAbs pair.2.natAbs).trans bounded
  have second_bounded : pair.2.natAbs ≤ bound :=
    (le_max_right pair.1.natAbs pair.2.natAbs).trans bounded
  have first_cast_bounded : (pair.1.natAbs : ℤ) ≤ bound := by
    exact_mod_cast first_bounded
  have second_cast_bounded : (pair.2.natAbs : ℤ) ≤ bound := by
    exact_mod_cast second_bounded
  constructor
  · rw [Finset.mem_Icc]
    constructor
    · calc
        -(bound : ℤ) ≤ -(pair.1.natAbs : ℤ) := neg_le_neg first_cast_bounded
        _ = -|pair.1| := by simp
        _ ≤ pair.1 := neg_abs_le pair.1
    · exact Int.le_natAbs.trans first_cast_bounded
  · rw [Finset.mem_Icc]
    constructor
    · calc
        -(bound : ℤ) ≤ -(pair.2.natAbs : ℤ) := neg_le_neg second_cast_bounded
        _ = -|pair.2| := by simp
        _ ≤ pair.2 := neg_abs_le pair.2
    · exact Int.le_natAbs.trans second_cast_bounded

/-- Every bounded integral-pair box is finite. -/
theorem integralPairBox_finite (bound : ℕ) :
    (integralPairBox bound).Finite := by
  exact (integralPairCube bound).finite_toSet.subset fun _ bounded ↦
    mem_integralPairCube_of_pairHeight_le bounded

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

/-- A bounded window longer than the explicit integer cube already produces a
nonidentity target stabilizer.  Unlike the infinite pigeonhole theorem above,
this gives a finite search horizon of `(2 * bound + 1)² + 1` prefixes. -/
theorem exists_nontrivial_stabilizer_of_bounded_prefix_window
    {G : Type*} [Group G] [MulAction G (ProjectiveLine.Point ℚ)]
    (target : ProjectiveLine.Point ℚ) (bound : ℕ)
    (orbitPrefix : Fin ((2 * bound + 1) ^ 2 + 1) → G)
    (orbitPrefix_injective : Function.Injective orbitPrefix)
    (state : Fin ((2 * bound + 1) ^ 2 + 1) → PrimitivePair)
    (realizes : ∀ index, orbitPrefix index • target = primitivePoint (state index))
    (bounded : ∀ index, primitiveHeight (state index) ≤ bound) :
    ∃ stabilizer : G, stabilizer ≠ 1 ∧ stabilizer • target = target := by
  let indices : Finset (Fin ((2 * bound + 1) ^ 2 + 1)) := Finset.univ
  have maps_to :
      ∀ index ∈ indices, (state index).1 ∈ integralPairCube bound := by
    intro index _
    exact mem_integralPairCube_of_pairHeight_le (bounded index)
  have cube_smaller : (integralPairCube bound).card < indices.card := by
    simp [indices, integralPairCube_card]
  obtain ⟨left, _, right, _, indices_ne, states_eq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to cube_smaller maps_to
  have prefixes_ne : orbitPrefix left ≠ orbitPrefix right :=
    orbitPrefix_injective.ne indices_ne
  have collision : orbitPrefix left • target = orbitPrefix right • target := by
    calc
      orbitPrefix left • target = primitivePoint (state left) := realizes left
      _ = primitivePoint (state right) := by
        congr 1
        exact Subtype.ext states_eq
      _ = orbitPrefix right • target := (realizes right).symm
  exact exists_nontrivial_stabilizer_of_orbit_collision prefixes_ne collision

/-- Trivial target stabilizer forces an escape above `bound` within the first
`(2 * bound + 1)² + 1` distinct normal-form prefixes. -/
theorem bounded_prefix_window_escape_of_stabilizer_trivial
    {G : Type*} [Group G] [MulAction G (ProjectiveLine.Point ℚ)]
    (target : ProjectiveLine.Point ℚ) (bound : ℕ)
    (orbitPrefix : Fin ((2 * bound + 1) ^ 2 + 1) → G)
    (orbitPrefix_injective : Function.Injective orbitPrefix)
    (state : Fin ((2 * bound + 1) ^ 2 + 1) → PrimitivePair)
    (realizes : ∀ index, orbitPrefix index • target = primitivePoint (state index))
    (stabilizer_trivial : ∀ element : G, element • target = target → element = 1) :
    ∃ index, bound < primitiveHeight (state index) := by
  by_contra no_escape
  push Not at no_escape
  obtain ⟨stabilizer, stabilizer_ne, fixed⟩ :=
    exists_nontrivial_stabilizer_of_bounded_prefix_window target bound orbitPrefix
      orbitPrefix_injective state realizes no_escape
  exact stabilizer_ne (stabilizer_trivial stabilizer fixed)

end MatrixMortality.InverseOrbitRecurrence
