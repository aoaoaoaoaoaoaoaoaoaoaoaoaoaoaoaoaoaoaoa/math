import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases

/-!
# Positive free cancellation and quotient-blind boundaries

Three positive letters generate the binary free group as a monoid, so positivity alone does not
exclude free cancellation. Quotient-blind fixed boundaries nevertheless fail: accepting one group
element and its square forces acceptance of a nonempty positive identity spelling.
-/

namespace MatrixMortality

namespace PositiveFreeCancellation

/-! ## A three-positive-letter cover of the binary free group -/

/-- Positive generators `x`, `y`, and the formal inverse of `xy`. -/
inductive TriangleLetter
  | x
  | y
  | z
  deriving DecidableEq

/-- Group value of a positive triangle letter. -/
def triangleGenerator : TriangleLetter → FreeGroup Bool
  | .x => FreeGroup.of false
  | .y => FreeGroup.of true
  | .z => (FreeGroup.of true)⁻¹ * (FreeGroup.of false)⁻¹

/-- Evaluation of a positive triangle word in the binary free group. -/
def triangleEvaluate (word : List TriangleLetter) : FreeGroup Bool :=
  (word.map triangleGenerator).prod

@[simp]
theorem triangleEvaluate_nil : triangleEvaluate [] = 1 := by
  simp [triangleEvaluate]

@[simp]
theorem triangleEvaluate_cons (letter : TriangleLetter) (word : List TriangleLetter) :
    triangleEvaluate (letter :: word) = triangleGenerator letter * triangleEvaluate word := by
  simp [triangleEvaluate]

@[simp]
theorem triangleEvaluate_append (left right : List TriangleLetter) :
    triangleEvaluate (left ++ right) = triangleEvaluate left * triangleEvaluate right := by
  simp [triangleEvaluate]

/-- Each cyclic positive triple is a nonempty spelling of the group identity. -/
theorem triangle_relations :
    triangleEvaluate [.x, .y, .z] = 1 ∧
      triangleEvaluate [.y, .z, .x] = 1 ∧
      triangleEvaluate [.z, .x, .y] = 1 := by
  simp [triangleEvaluate, triangleGenerator, mul_assoc]

/-- Every binary free-group element has a positive spelling over three letters. -/
theorem triangleEvaluate_surjective : Function.Surjective triangleEvaluate := by
  intro element
  induction element using FreeGroup.induction_on with
  | of bit =>
      cases bit
      · refine ⟨[.x], ?_⟩
        simp [triangleGenerator]
      · refine ⟨[.y], ?_⟩
        simp [triangleGenerator]
  | inv_of bit _ =>
      cases bit
      · refine ⟨[.y, .z], ?_⟩
        simp [triangleGenerator]
      · refine ⟨[.z, .x], ?_⟩
        simp [triangleGenerator, mul_assoc]
  | mul left right left_spelling right_spelling =>
      rcases left_spelling with ⟨left_word, left_eq⟩
      rcases right_spelling with ⟨right_word, right_eq⟩
      exact ⟨left_word ++ right_word, by simp [left_eq, right_eq]⟩
  | C1 => exact ⟨[], triangleEvaluate_nil⟩

/-! ## Exact affine exponent slices -/

/-- Signed weight recording one `x`, no `y`, and minus one `z`. -/
def triangleWeight : TriangleLetter → ℤ
  | .x => 1
  | .y => 0
  | .z => -1

/-- Total signed weight of a positive triangle word. -/
def triangleWordWeight (word : List TriangleLetter) : ℤ :=
  (word.map triangleWeight).sum

@[simp]
theorem triangleWordWeight_append (left right : List TriangleLetter) :
    triangleWordWeight (left ++ right) =
      triangleWordWeight left + triangleWordWeight right := by
  simp [triangleWordWeight]

/-- Exponent homomorphism which counts the first binary free generator and ignores the second. -/
def firstExponentHom : FreeGroup Bool →* Multiplicative ℤ :=
  FreeGroup.lift fun bit => Multiplicative.ofAdd (if bit then 0 else 1)

/-- First-generator exponent of a binary free-group element. -/
def firstExponent (element : FreeGroup Bool) : ℤ :=
  Multiplicative.toAdd (firstExponentHom element)

@[simp]
theorem firstExponent_one : firstExponent (1 : FreeGroup Bool) = 0 := by
  simp [firstExponent]

@[simp]
theorem firstExponent_mul (left right : FreeGroup Bool) :
    firstExponent (left * right) = firstExponent left + firstExponent right := by
  simp [firstExponent]

@[simp]
theorem firstExponent_inv (element : FreeGroup Bool) :
    firstExponent element⁻¹ = -firstExponent element := by
  simp [firstExponent]

@[simp]
theorem firstExponent_of (bit : Bool) :
    firstExponent (FreeGroup.of bit) = if bit then 0 else 1 := by
  simp [firstExponent, firstExponentHom]

/-- Positive triangle evaluation transports the signed word weight exactly to the affine group
exponent. -/
theorem firstExponent_triangleEvaluate (word : List TriangleLetter) :
    firstExponent (triangleEvaluate word) = triangleWordWeight word := by
  induction word with
  | nil => simp [triangleWordWeight]
  | cons letter word induction =>
      cases letter <;>
        simp [triangleWordWeight, triangleWeight, triangleGenerator, induction]

/-- Positive words and free-group elements on one prescribed affine exponent slice. -/
def TriangleWeightSlice (weight : ℤ) :=
  {word : List TriangleLetter // triangleWordWeight word = weight}

/-- Binary free-group elements on one prescribed first-generator exponent slice. -/
def FirstExponentSlice (weight : ℤ) :=
  {element : FreeGroup Bool // firstExponent element = weight}

/-- Evaluation restricts from one positive signed-weight slice to the matching group slice. -/
def triangleSliceEvaluate (weight : ℤ) :
    TriangleWeightSlice weight → FirstExponentSlice weight :=
  fun word =>
    ⟨triangleEvaluate word.1, firstExponent_triangleEvaluate word.1 ▸ word.property⟩

/-- Every element of an affine free-group exponent slice has a positive spelling on the exact
matching signed-weight slice. -/
theorem triangleSliceEvaluate_surjective (weight : ℤ) :
    Function.Surjective (triangleSliceEvaluate weight) := by
  intro element
  obtain ⟨word, word_eq⟩ := triangleEvaluate_surjective element.1
  have word_weight : triangleWordWeight word = weight := by
    rw [← firstExponent_triangleEvaluate, word_eq]
    exact element.property
  exact ⟨⟨word, word_weight⟩, Subtype.ext word_eq⟩

/-- The three-letter identity spelling has zero affine weight. -/
theorem triangle_identity_weight : triangleWordWeight [.x, .y, .z] = 0 := by
  rfl

/-- Appending the positive identity triangle changes neither group value nor affine weight. -/
theorem triangle_identity_padding (word : List TriangleLetter) :
    triangleEvaluate (word ++ [.x, .y, .z]) = triangleEvaluate word ∧
      triangleWordWeight (word ++ [.x, .y, .z]) = triangleWordWeight word := by
  constructor
  · simp [triangle_relations.1]
  · simp [triangle_identity_weight]

/-! ## Quotient-blind boundary collapse -/

/-- Evaluation of a positive word in an arbitrary monoid. -/
def positiveEvaluate {S G : Type*} [Monoid G] (generator : S → G) (word : List S) : G :=
  (word.map generator).prod

@[simp]
theorem positiveEvaluate_nil {S G : Type*} [Monoid G] (generator : S → G) :
    positiveEvaluate generator [] = 1 := by
  simp [positiveEvaluate]

@[simp]
theorem positiveEvaluate_cons {S G : Type*} [Monoid G] (generator : S → G)
    (letter : S) (word : List S) :
    positiveEvaluate generator (letter :: word) =
      generator letter * positiveEvaluate generator word := by
  simp [positiveEvaluate]

@[simp]
theorem positiveEvaluate_append {S G : Type*} [Monoid G] (generator : S → G)
    (left right : List S) :
    positiveEvaluate generator (left ++ right) =
      positiveEvaluate generator left * positiveEvaluate generator right := by
  simp [positiveEvaluate]

/-! ## Invertible positive fibre spans -/

/-- Linear span of all states reached by positive spellings of one group element. -/
def positiveFibreSpan
    {K S G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (generator : S → G) (transition : S → V ≃ₗ[K] V) (seed : V) (value : G) :
    Submodule K V :=
  Submodule.span K {point | ∃ word : List S,
    positiveEvaluate generator word = value ∧
      positiveEvaluate transition word seed = point}

/-- Prefixing positive spellings maps a fibre span into the correspondingly translated fibre
span. -/
theorem positiveFibreSpan_word_map_le
    {K S G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (generator : S → G) (transition : S → V ≃ₗ[K] V) (seed : V)
    (prefixWord : List S) (value : G) :
    (positiveFibreSpan generator transition seed value).map
        (positiveEvaluate transition prefixWord).toLinearMap ≤
      positiveFibreSpan generator transition seed
        (positiveEvaluate generator prefixWord * value) := by
  rw [Submodule.map_le_iff_le_comap]
  refine Submodule.span_le.mpr ?_
  rintro point ⟨word, word_value, point_eq⟩
  change positiveEvaluate transition prefixWord point ∈
    positiveFibreSpan generator transition seed
      (positiveEvaluate generator prefixWord * value)
  apply Submodule.subset_span
  refine ⟨prefixWord ++ word, ?_, ?_⟩
  · simp only [positiveEvaluate_append, word_value]
  · simp only [positiveEvaluate_append]
    change positiveEvaluate transition prefixWord
      (positiveEvaluate transition word seed) = positiveEvaluate transition prefixWord point
    rw [point_eq]

/-- When positive evaluation surjects onto a group and every transition is invertible, prefixing
maps each fibre span exactly onto the translated fibre span. The reverse inclusion uses a
positive spelling of the semantic inverse and finite-dimensional rank. -/
theorem positiveFibreSpan_word_map_eq
    {K S G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (generator : S → G) (transition : S → V ≃ₗ[K] V) (seed : V)
    (surjective : Function.Surjective (positiveEvaluate generator))
    (prefixWord : List S) (value : G) :
    (positiveFibreSpan generator transition seed value).map
        (positiveEvaluate transition prefixWord).toLinearMap =
      positiveFibreSpan generator transition seed
        (positiveEvaluate generator prefixWord * value) := by
  let source := positiveFibreSpan generator transition seed value
  let target := positiveFibreSpan generator transition seed
    (positiveEvaluate generator prefixWord * value)
  have forward :
      source.map (positiveEvaluate transition prefixWord).toLinearMap ≤ target :=
    positiveFibreSpan_word_map_le generator transition seed prefixWord value
  obtain ⟨inverseWord, inverseWord_value⟩ :=
    surjective (positiveEvaluate generator prefixWord)⁻¹
  have reverse :
      target.map (positiveEvaluate transition inverseWord).toLinearMap ≤ source := by
    simpa only [target, source, inverseWord_value, inv_mul_cancel_left] using
      positiveFibreSpan_word_map_le generator transition seed inverseWord
        (positiveEvaluate generator prefixWord * value)
  apply Submodule.eq_of_le_of_finrank_le forward
  calc
    Module.finrank K target =
        Module.finrank K
          (target.map (positiveEvaluate transition inverseWord).toLinearMap) :=
      (LinearEquiv.finrank_map_eq (positiveEvaluate transition inverseWord) target).symm
    _ ≤ Module.finrank K source := Submodule.finrank_mono reverse
    _ = Module.finrank K
        (source.map (positiveEvaluate transition prefixWord).toLinearMap) :=
      (LinearEquiv.finrank_map_eq (positiveEvaluate transition prefixWord) source).symm

/-- The inverse linear transition maps a translated fibre span back to its source. This is a
group-orbit statement about subspaces; it does not assert that an inverse transition is a
positive generator. -/
theorem positiveFibreSpan_word_symm_map_eq
    {K S G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (generator : S → G) (transition : S → V ≃ₗ[K] V) (seed : V)
    (surjective : Function.Surjective (positiveEvaluate generator))
    (word : List S) (value : G) :
    (positiveFibreSpan generator transition seed
        (positiveEvaluate generator word * value)).map
        (positiveEvaluate transition word).symm.toLinearMap =
      positiveFibreSpan generator transition seed value := by
  apply (Submodule.map_symm_eq_iff (positiveEvaluate transition word)).mpr
  exact positiveFibreSpan_word_map_eq generator transition seed surjective word value

/-- A positive spelling identifies its fibre span with the image of the identity-fibre span. -/
theorem positiveFibreSpan_eq_word_map_identity
    {K S G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (generator : S → G) (transition : S → V ≃ₗ[K] V) (seed : V)
    (surjective : Function.Surjective (positiveEvaluate generator))
    (word : List S) (value : G) (word_value : positiveEvaluate generator word = value) :
    positiveFibreSpan generator transition seed value =
      (positiveFibreSpan generator transition seed 1).map
        (positiveEvaluate transition word).toLinearMap := by
  symm
  simpa only [word_value, mul_one] using
    positiveFibreSpan_word_map_eq generator transition seed surjective word 1

/-- All semantic fibres have the same linear dimension. -/
theorem positiveFibreSpan_finrank_eq_identity
    {K S G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (generator : S → G) (transition : S → V ≃ₗ[K] V) (seed : V)
    (surjective : Function.Surjective (positiveEvaluate generator)) (value : G) :
    Module.finrank K (positiveFibreSpan generator transition seed value) =
      Module.finrank K (positiveFibreSpan generator transition seed 1) := by
  obtain ⟨word, word_value⟩ := surjective value
  rw [positiveFibreSpan_eq_word_map_identity generator transition seed surjective word value
    word_value]
  exact LinearEquiv.finrank_map_eq (positiveEvaluate transition word)
    (positiveFibreSpan generator transition seed 1)

/-- A nonzero seed makes every fibre span nonzero. -/
theorem positiveFibreSpan_ne_bot
    {K S G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (generator : S → G) (transition : S → V ≃ₗ[K] V) (seed : V)
    (surjective : Function.Surjective (positiveEvaluate generator)) (seed_ne : seed ≠ 0)
    (value : G) :
    positiveFibreSpan generator transition seed value ≠ ⊥ := by
  obtain ⟨word, word_value⟩ := surjective value
  have reached_mem :
      positiveEvaluate transition word seed ∈
        positiveFibreSpan generator transition seed value := by
    apply Submodule.subset_span
    exact ⟨word, word_value, rfl⟩
  intro fibre_bot
  rw [fibre_bot] at reached_mem
  exact seed_ne ((positiveEvaluate transition word).injective (by simpa using reached_mem))

/-- A boundary vanishes on every spelling of one semantic fibre exactly when its fibre span lies
in the boundary kernel. -/
theorem positiveFibre_vanishes_iff_span_le_ker
    {K S G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (generator : S → G) (transition : S → V ≃ₗ[K] V) (seed : V)
    (boundary : V →ₗ[K] K) (value : G) :
    (∀ word : List S, positiveEvaluate generator word = value →
        boundary (positiveEvaluate transition word seed) = 0) ↔
      positiveFibreSpan generator transition seed value ≤ LinearMap.ker boundary := by
  constructor
  · intro vanishes
    refine Submodule.span_le.mpr ?_
    rintro point ⟨word, word_value, point_eq⟩
    apply LinearMap.mem_ker.mpr
    rw [← point_eq]
    exact vanishes word word_value
  · intro span_le word word_value
    apply LinearMap.mem_ker.mp
    apply span_le
    apply Submodule.subset_span
    exact ⟨word, word_value, rfl⟩

/-- In dimension three, a nonzero fibre annihilated by a nonzero scalar boundary has dimension
one or two. -/
theorem positiveFibreSpan_finrank_one_or_two
    {K S G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (generator : S → G) (transition : S → V ≃ₗ[K] V) (seed : V)
    (boundary : V →ₗ[K] K) (surjective : Function.Surjective (positiveEvaluate generator))
    (seed_ne : seed ≠ 0) (boundary_ne : boundary ≠ 0)
    (dimension_three : Module.finrank K V = 3) (value : G)
    (vanishes : ∀ word : List S, positiveEvaluate generator word = value →
      boundary (positiveEvaluate transition word seed) = 0) :
    Module.finrank K (positiveFibreSpan generator transition seed value) = 1 ∨
      Module.finrank K (positiveFibreSpan generator transition seed value) = 2 := by
  let fibre := positiveFibreSpan generator transition seed value
  have fibre_ne_bot : fibre ≠ ⊥ :=
    positiveFibreSpan_ne_bot generator transition seed surjective seed_ne value
  have fibre_le_ker : fibre ≤ LinearMap.ker boundary :=
    (positiveFibre_vanishes_iff_span_le_ker generator transition seed boundary value).mp vanishes
  have fibre_ne_top : fibre ≠ ⊤ := by
    intro fibre_top
    have kernel_top : LinearMap.ker boundary = ⊤ := by
      apply top_unique
      simpa only [fibre_top] using fibre_le_ker
    exact boundary_ne (LinearMap.ker_eq_top.mp kernel_top)
  have positive_rank : 1 ≤ Module.finrank K fibre :=
    Submodule.one_le_finrank_iff.mpr fibre_ne_bot
  have rank_lt_three : Module.finrank K fibre < 3 := by
    simpa only [dimension_three] using Submodule.finrank_lt fibre_ne_top
  obtain ⟨offset, rank_eq⟩ := Nat.exists_eq_add_of_le positive_rank
  have offset_le_one : offset ≤ 1 := by omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp offset_le_one with offset_zero | offset_one
  · left
    simpa only [offset_zero, add_zero] using rank_eq
  · right
    simpa only [offset_one] using rank_eq

/-- A nonzero scalar boundary on a three-dimensional space has a two-dimensional kernel. -/
theorem linearFunctional_ker_finrank_eq_two
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (boundary : V →ₗ[K] K) (boundary_ne : boundary ≠ 0)
    (dimension_three : Module.finrank K V = 3) :
    Module.finrank K (LinearMap.ker boundary) = 2 := by
  have exists_visible : ∃ point : V, boundary point ≠ 0 := by
    by_contra no_visible
    have all_zero : ∀ point : V, boundary point = 0 := by
      intro point
      by_contra point_ne
      exact no_visible ⟨point, point_ne⟩
    apply boundary_ne
    ext point
    exact all_zero point
  obtain ⟨visible, visible_ne⟩ := exists_visible
  have boundary_surjective : Function.Surjective boundary := by
    intro scalar
    refine ⟨(scalar / boundary visible) • visible, ?_⟩
    simp only [LinearMap.map_smul_of_tower, smul_eq_mul]
    exact div_mul_cancel₀ scalar visible_ne
  have rank_nullity := boundary.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top_of_surjective boundary boundary_surjective,
    finrank_top, Module.finrank_self, dimension_three] at rank_nullity
  omega

/-- In the rank-two branch, fibrewise vanishing identifies the fibre span with a rank-two
boundary kernel. -/
theorem positiveFibreSpan_eq_ker_of_finrank_two
    {K S G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (generator : S → G) (transition : S → V ≃ₗ[K] V) (seed : V)
    (boundary : V →ₗ[K] K) (value : G)
    (boundary_ne : boundary ≠ 0) (dimension_three : Module.finrank K V = 3)
    (fibre_two : Module.finrank K (positiveFibreSpan generator transition seed value) = 2)
    (vanishes : ∀ word : List S, positiveEvaluate generator word = value →
      boundary (positiveEvaluate transition word seed) = 0) :
    positiveFibreSpan generator transition seed value = LinearMap.ker boundary := by
  apply Submodule.eq_of_le_of_finrank_le
    ((positiveFibre_vanishes_iff_span_le_ker generator transition seed boundary value).mp
      vanishes)
  rw [fibre_two, linearFunctional_ker_finrank_eq_two boundary boundary_ne dimension_three]

/-! ## Identity-word orbit algebra -/

/-- Linear span of the transition operators carried by positive semantic identity words. -/
def positiveIdentityOperatorSpan
    {K S G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (generator : S → G) (transition : S → V ≃ₗ[K] V) :
    Submodule K (Module.End K V) :=
  Submodule.span K {operator | ∃ word : List S,
    positiveEvaluate generator word = 1 ∧
      (positiveEvaluate transition word).toLinearMap = operator}

/-- Each positive identity-word transition belongs to the identity-operator span. -/
theorem positiveIdentityOperatorSpan_transition_mem
    {K S G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (generator : S → G) (transition : S → V ≃ₗ[K] V) (word : List S)
    (word_identity : positiveEvaluate generator word = 1) :
    (positiveEvaluate transition word).toLinearMap ∈
      positiveIdentityOperatorSpan generator transition := by
  apply Submodule.subset_span
  exact ⟨word, word_identity, rfl⟩

/-- The identity endomorphism belongs to the identity-operator span. -/
theorem positiveIdentityOperatorSpan_one_mem
    {K S G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (generator : S → G) (transition : S → V ≃ₗ[K] V) :
    (1 : Module.End K V) ∈ positiveIdentityOperatorSpan generator transition := by
  have identity_mem := positiveIdentityOperatorSpan_transition_mem generator transition []
    (positiveEvaluate_nil generator)
  convert identity_mem using 1
  ext point
  change point = point
  rfl

/-- The identity-operator span is closed under operator composition. -/
theorem positiveIdentityOperatorSpan_mul_mem
    {K S G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (generator : S → G) (transition : S → V ≃ₗ[K] V)
    {left right : Module.End K V}
    (left_mem : left ∈ positiveIdentityOperatorSpan generator transition)
    (right_mem : right ∈ positiveIdentityOperatorSpan generator transition) :
    left * right ∈ positiveIdentityOperatorSpan generator transition := by
  induction left_mem using Submodule.span_induction with
  | mem leftOperator left_generator =>
      rcases left_generator with ⟨leftWord, left_identity, rfl⟩
      induction right_mem using Submodule.span_induction with
      | mem rightOperator right_generator =>
          rcases right_generator with ⟨rightWord, right_identity, rfl⟩
          apply Submodule.subset_span
          refine ⟨leftWord ++ rightWord, ?_, ?_⟩
          · simp only [positiveEvaluate_append, left_identity, right_identity, mul_one]
          · rw [positiveEvaluate_append]
            rfl
      | zero => simp
      | add first second _ _ first_mem second_mem =>
          rw [mul_add]
          exact Submodule.add_mem _ first_mem second_mem
      | smul scalar operator _ operator_mem =>
          rw [mul_smul_comm]
          exact Submodule.smul_mem _ scalar operator_mem
  | zero => simp
  | add first second _ _ first_mem second_mem =>
      rw [add_mul]
      exact Submodule.add_mem _ first_mem second_mem
  | smul scalar operator _ operator_mem =>
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ scalar operator_mem

/-- Unital operator algebra generated linearly by positive semantic identity words. -/
def positiveIdentityAlgebra
    {K S G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (generator : S → G) (transition : S → V ≃ₗ[K] V) :
    Subalgebra K (Module.End K V) where
  carrier := positiveIdentityOperatorSpan generator transition
  mul_mem' := positiveIdentityOperatorSpan_mul_mem generator transition
  one_mem' := positiveIdentityOperatorSpan_one_mem generator transition
  add_mem' := (positiveIdentityOperatorSpan generator transition).add_mem
  zero_mem' := (positiveIdentityOperatorSpan generator transition).zero_mem
  algebraMap_mem' := fun scalar => by
    rw [Algebra.algebraMap_eq_smul_one]
    exact (positiveIdentityOperatorSpan generator transition).smul_mem scalar
      (positiveIdentityOperatorSpan_one_mem generator transition)

/-- The identity fibre is exactly the orbit of the seed under the identity-word operator
algebra. -/
theorem positiveIdentityAlgebra_map_apply_eq_fibre
    {K S G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (generator : S → G) (transition : S → V ≃ₗ[K] V) (seed : V) :
    (positiveIdentityAlgebra generator transition).toSubmodule.map (LinearMap.applyₗ seed) =
      positiveFibreSpan generator transition seed 1 := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    intro operator operator_mem
    change operator seed ∈ positiveFibreSpan generator transition seed 1
    change operator ∈ positiveIdentityOperatorSpan generator transition at operator_mem
    induction operator_mem using Submodule.span_induction with
    | mem identityOperator identity_generator =>
        rcases identity_generator with ⟨word, word_identity, rfl⟩
        apply Submodule.subset_span
        exact ⟨word, word_identity, rfl⟩
    | zero => simp
    | add first second _ _ first_mem second_mem =>
        simpa only [LinearMap.add_apply] using Submodule.add_mem _ first_mem second_mem
    | smul scalar operator _ operator_mem =>
        simpa only [LinearMap.smul_apply] using Submodule.smul_mem _ scalar operator_mem
  · refine Submodule.span_le.mpr ?_
    rintro point ⟨word, word_identity, rfl⟩
    refine ⟨(positiveEvaluate transition word).toLinearMap, ?_, ?_⟩
    · change (positiveEvaluate transition word).toLinearMap ∈
        positiveIdentityOperatorSpan generator transition
      exact positiveIdentityOperatorSpan_transition_mem generator transition word word_identity
    · rfl

/-! ## Triangle-cover Grassmannian orbit -/

/-- Each triangle transition maps one semantic fibre span exactly onto the left-translated
fibre span. -/
theorem triangleFibreSpan_letter_map_eq
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (transition : TriangleLetter → V ≃ₗ[K] V) (seed : V)
    (letter : TriangleLetter) (value : FreeGroup Bool) :
    (positiveFibreSpan triangleGenerator transition seed value).map
        (transition letter).toLinearMap =
      positiveFibreSpan triangleGenerator transition seed (triangleGenerator letter * value) := by
  simpa only [positiveEvaluate_cons, positiveEvaluate_nil, mul_one] using
    positiveFibreSpan_word_map_eq triangleGenerator transition seed
      triangleEvaluate_surjective [letter] value

/-- The inverse of each triangle transition gives the reverse group-orbit edge on fibre spans.
This inverse edge is not asserted to be a positive matrix generator. -/
theorem triangleFibreSpan_letter_symm_map_eq
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (transition : TriangleLetter → V ≃ₗ[K] V) (seed : V)
    (letter : TriangleLetter) (value : FreeGroup Bool) :
    (positiveFibreSpan triangleGenerator transition seed
        (triangleGenerator letter * value)).map (transition letter).symm.toLinearMap =
      positiveFibreSpan triangleGenerator transition seed value := by
  simpa only [positiveEvaluate_cons, positiveEvaluate_nil, mul_one] using
    positiveFibreSpan_word_symm_map_eq triangleGenerator transition seed
      triangleEvaluate_surjective [letter] value

/-- A nonempty positive alphabet surjecting onto a group has a nonempty identity spelling. -/
theorem exists_nonempty_positive_identity {S G : Type*} [Nonempty S] [Group G]
    (generator : S → G) (surjective : Function.Surjective (positiveEvaluate generator)) :
    ∃ word : List S, word ≠ [] ∧ positiveEvaluate generator word = 1 := by
  let letter : S := Classical.choice (inferInstance : Nonempty S)
  obtain ⟨tail, tail_eq⟩ := surjective (generator letter)⁻¹
  refine ⟨letter :: tail, by simp, ?_⟩
  rw [positiveEvaluate_cons, tail_eq, mul_inv_cancel]

/-- If fixed group boundaries accept an element and its square, they accept the identity. -/
theorem boundary_eq_of_accept_element_and_square
    {G L : Type*} [Group G] [Group L]
    (upper lower : G →* L) (left right left' right' : L) (element : G)
    (accept_element :
      left * upper element * right = left' * lower element * right')
    (accept_square :
      left * upper (element * element) * right =
        left' * lower (element * element) * right') :
    left * right = left' * right' := by
  let U := upper element
  let V := lower element
  let A := left⁻¹ * left'
  let B := right' * right⁻¹
  have accept_element' : left * U * right = left' * V * right' := by
    exact accept_element
  have accept_square' :
      left * (U * U) * right = left' * (V * V) * right' := by
    simpa [U, V] using accept_square
  have first : U = A * V * B := by
    calc
      U = left⁻¹ * (left * U * right) * right⁻¹ := by group
      _ = left⁻¹ * (left' * V * right') * right⁻¹ := by
        rw [accept_element']
      _ = A * V * B := by simp [A, B]; group
  have second : U * U = A * (V * V) * B := by
    calc
      U * U = left⁻¹ * (left * (U * U) * right) * right⁻¹ := by group
      _ = left⁻¹ * (left' * (V * V) * right') * right⁻¹ := by
        rw [accept_square']
      _ = A * (V * V) * B := by simp [A, B]; group
  have middle : V * B * A * V = V * V := by
    calc
      V * B * A * V = A⁻¹ * ((A * V * B) * (A * V * B)) * B⁻¹ := by group
      _ = A⁻¹ * (U * U) * B⁻¹ := by rw [← first]
      _ = A⁻¹ * (A * (V * V) * B) * B⁻¹ := by rw [second]
      _ = V * V := by group
  have BA : B * A = 1 := by
    calc
      B * A = V⁻¹ * (V * B * A * V) * V⁻¹ := by group
      _ = V⁻¹ * (V * V) * V⁻¹ := by rw [middle]
      _ = 1 := by group
  have B_eq : B = A⁻¹ := by
    calc
      B = B * (A * A⁻¹) := by simp
      _ = (B * A) * A⁻¹ := by group
      _ = A⁻¹ := by rw [BA]; simp
  have AB : A * B = 1 := by rw [B_eq, mul_inv_cancel]
  calc
    left * right = left * (A * B) * right := by rw [AB]; simp
    _ = left' * right' := by simp [A, B]; group

/-- A quotient-blind boundary equation which accepts one element and its square necessarily has a
nonempty positive false witness whenever the positive evaluation surjects onto the group. -/
theorem exists_nonempty_identity_witness
    {S G L : Type*} [Nonempty S] [Group G] [Group L]
    (generator : S → G) (surjective : Function.Surjective (positiveEvaluate generator))
    (upper lower : G →* L) (left right left' right' : L) (element : G)
    (accept_element :
      left * upper element * right = left' * lower element * right')
    (accept_square :
      left * upper (element * element) * right =
        left' * lower (element * element) * right') :
    ∃ word : List S,
      word ≠ [] ∧
        positiveEvaluate generator word = 1 ∧
        left * upper (positiveEvaluate generator word) * right =
          left' * lower (positiveEvaluate generator word) * right' := by
  obtain ⟨word, word_ne, word_eq⟩ :=
    exists_nonempty_positive_identity generator surjective
  have boundary_eq := boundary_eq_of_accept_element_and_square
    upper lower left right left' right' element accept_element accept_square
  refine ⟨word, word_ne, word_eq, ?_⟩
  simp [word_eq, boundary_eq]

/-! ## Finite spelling fibres pump semantic identity loops -/

/-- An injective transition over a finite invariant semantic fibre eventually returns every
point of that fibre to itself. -/
theorem finiteFibre_identity_pumps
    {X Y : Type*} (project : X → Y) (transition : X → X) (semantic : Y → Y)
    (commutes : ∀ point, project (transition point) = semantic (project point))
    (transition_injective : Function.Injective transition) (value : Y)
    (semantic_fixed : semantic value = value) (point : X) (point_mem : project point = value)
    [Finite {candidate // project candidate = value}] :
    ∃ period : Nat, 0 < period ∧ transition^[period] point = point := by
  have orbit_mem : ∀ time : Nat, project (transition^[time] point) = value := by
    intro time
    induction time with
    | zero => simpa using point_mem
    | succ time induction =>
        have iterate_succ :
            transition^[time.succ] point = transition (transition^[time] point) := by
          simpa [Nat.succ_eq_add_one, Nat.add_comm] using
            Function.iterate_add_apply transition 1 time point
        rw [iterate_succ, commutes, induction, semantic_fixed]
  let orbit : Nat → {candidate // project candidate = value} :=
    fun time => ⟨transition^[time] point, orbit_mem time⟩
  obtain ⟨first, second, distinct, collision⟩ :=
    Finite.exists_ne_map_eq_of_infinite orbit
  have collision_value :
      transition^[first] point = transition^[second] point :=
    congrArg Subtype.val collision
  rcases Nat.lt_or_gt_of_ne distinct with first_lt_second | second_lt_first
  · refine ⟨second - first, Nat.sub_pos_of_lt first_lt_second, ?_⟩
    apply (transition_injective.iterate first)
    calc
      transition^[first] (transition^[second - first] point) =
          transition^[first + (second - first)] point := by
        rw [Function.iterate_add_apply]
      _ = transition^[second] point := by rw [Nat.add_sub_of_le first_lt_second.le]
      _ = transition^[first] point := collision_value.symm
  · refine ⟨first - second, Nat.sub_pos_of_lt second_lt_first, ?_⟩
    apply (transition_injective.iterate second)
    calc
      transition^[second] (transition^[first - second] point) =
          transition^[second + (first - second)] point := by
        rw [Function.iterate_add_apply]
      _ = transition^[first] point := by rw [Nat.add_sub_of_le second_lt_first.le]
      _ = transition^[second] point := collision_value

/-! ## A singular one-coordinate lift absorbs quotient identities -/

/-- A noninjective lift of an injective quotient action with one-dimensional quotient kernel has
the same kernel as the quotient map. -/
theorem singularLift_kernel_eq_quotientKernel
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V]
    (quotient : V →ₗ[K] W) (lift : V →ₗ[K] V) (quotientAction : W →ₗ[K] W)
    (compatible : quotient.comp lift = quotientAction.comp quotient)
    (quotientAction_injective : Function.Injective quotientAction)
    (lift_singular : ¬Function.Injective lift)
    (kernel_one : Module.finrank K (LinearMap.ker quotient) = 1) :
    LinearMap.ker lift = LinearMap.ker quotient := by
  have kernel_le : LinearMap.ker lift ≤ LinearMap.ker quotient := by
    intro point point_mem
    have compatible_point :
        quotient (lift point) = quotientAction (quotient point) := by
      simpa using LinearMap.congr_fun compatible point
    have quotientAction_zero : quotientAction (quotient point) = 0 := by
      calc
        quotientAction (quotient point) = quotient (lift point) := compatible_point.symm
        _ = 0 := by rw [LinearMap.mem_ker.mp point_mem]; simp
    exact LinearMap.mem_ker.mpr <| quotientAction_injective (by simpa using quotientAction_zero)
  have lift_kernel_ne_bot : LinearMap.ker lift ≠ ⊥ := by
    intro kernel_bot
    exact lift_singular (LinearMap.ker_eq_bot.mp kernel_bot)
  apply Submodule.eq_of_le_of_finrank_le kernel_le
  rw [kernel_one]
  exact Submodule.one_le_finrank_iff.mpr lift_kernel_ne_bot

/-- After a singular one-coordinate lift, every later quotient-identity factor is absorbed as an
equality of complete linear maps. -/
theorem singularLift_absorbs_quotientIdentity
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V]
    (quotient : V →ₗ[K] W) (lift quotientIdentity : V →ₗ[K] V)
    (quotientAction : W →ₗ[K] W)
    (compatible : quotient.comp lift = quotientAction.comp quotient)
    (quotientAction_injective : Function.Injective quotientAction)
    (lift_singular : ¬Function.Injective lift)
    (kernel_one : Module.finrank K (LinearMap.ker quotient) = 1)
    (identity_downstairs : quotient.comp quotientIdentity = quotient) :
    lift.comp quotientIdentity = lift := by
  have kernel_eq := singularLift_kernel_eq_quotientKernel quotient lift quotientAction compatible
    quotientAction_injective lift_singular kernel_one
  ext point
  change lift (quotientIdentity point) = lift point
  have identity_point : quotient (quotientIdentity point) = quotient point := by
    simpa using LinearMap.congr_fun identity_downstairs point
  have difference_mem : quotientIdentity point - point ∈ LinearMap.ker quotient := by
    apply LinearMap.mem_ker.mpr
    rw [quotient.map_sub, identity_point, sub_self]
  have difference_killed : lift (quotientIdentity point - point) = 0 := by
    apply LinearMap.mem_ker.mp
    rw [kernel_eq]
    exact difference_mem
  exact sub_eq_zero.mp (by simpa only [lift.map_sub] using difference_killed)

/-! ## The forbidden-triple zero support has rank six -/

open scoped Matrix

/-- Forced Hankel shape for the language avoiding `xyz`, `yzx`, and `zxy`. The first three rows
are one-letter prefixes and the last three are two-letter prefixes; columns have the same order. -/
def forbiddenTripleSupportMatrix {K : Type*} [Zero K]
    (a b c d e f g h i : K) : Matrix (Fin 6) (Fin 6) K :=
  !![0, 0, 0, 0, a, 0;
     0, 0, 0, 0, 0, b;
     0, 0, 0, c, 0, 0;
     0, 0, d, 0, 0, e;
     f, 0, 0, g, 0, 0;
     0, h, 0, 0, i, 0]

/-- Six private support entries force the forbidden-triple Hankel rows to be independent over
every field; the three remaining nonzero slots are unrestricted. -/
theorem forbiddenTripleSupport_rows_linearIndependent
    {K : Type*} [Field K] (a b c d e f g h i : K)
    (a_ne : a ≠ 0) (b_ne : b ≠ 0) (c_ne : c ≠ 0)
    (d_ne : d ≠ 0) (f_ne : f ≠ 0) (h_ne : h ≠ 0) :
    LinearIndependent K (fun row => forbiddenTripleSupportMatrix a b c d e f g h i row) := by
  rw [Fintype.linearIndependent_iff]
  intro coefficients combination_zero index
  have column_zero := congrFun combination_zero 0
  have column_one := congrFun combination_zero 1
  have column_two := congrFun combination_zero 2
  simp [forbiddenTripleSupportMatrix, Fin.sum_univ_succ] at column_zero
  simp [forbiddenTripleSupportMatrix, Fin.sum_univ_succ] at column_one
  simp [forbiddenTripleSupportMatrix, Fin.sum_univ_succ] at column_two
  have coefficient_four : coefficients 4 = 0 :=
    column_zero.resolve_right f_ne
  have coefficient_five : coefficients 5 = 0 :=
    column_one.resolve_right h_ne
  have coefficient_three : coefficients 3 = 0 :=
    column_two.resolve_right d_ne
  have column_three := congrFun combination_zero 3
  have column_four := congrFun combination_zero 4
  have column_five := congrFun combination_zero 5
  norm_num [forbiddenTripleSupportMatrix, Matrix.cons_val_three, Fin.sum_univ_succ,
    coefficient_three, coefficient_four, coefficient_five] at column_three
  norm_num [forbiddenTripleSupportMatrix, Matrix.cons_val_four, Fin.sum_univ_succ,
    coefficient_three, coefficient_four, coefficient_five] at column_four
  norm_num [forbiddenTripleSupportMatrix, Fin.sum_univ_succ,
    coefficient_three, coefficient_four, coefficient_five] at column_five
  have row_zero_five : ![(0 : K), 0, 0, 0, a, 0] (5 : Fin 6) = 0 := rfl
  have row_one_five : ![(0 : K), 0, 0, 0, 0, b] (5 : Fin 6) = b := rfl
  have row_two_five : ![(0 : K), 0, 0, c, 0, 0] (5 : Fin 6) = 0 := rfl
  have row_three_five : ![(0 : K), 0, d, 0, 0, e] (5 : Fin 6) = e := rfl
  have row_four_five : ![f, (0 : K), 0, g, 0, 0] (5 : Fin 6) = 0 := rfl
  have row_five_five : ![(0 : K), h, 0, 0, i, 0] (5 : Fin 6) = 0 := rfl
  rw [row_zero_five, row_one_five, row_two_five, row_three_five,
    row_four_five, row_five_five] at column_five
  simp only [mul_zero, zero_add, add_zero] at column_five
  change coefficients 2 * c + coefficients 4 * g = 0 at column_three
  change coefficients 0 * a + coefficients 5 * i = 0 at column_four
  change coefficients 1 * b + coefficients 3 * e = 0 at column_five
  simp [coefficient_four] at column_three
  simp [coefficient_five] at column_four
  simp [coefficient_three] at column_five
  have coefficient_two : coefficients 2 = 0 :=
    column_three.resolve_right c_ne
  have coefficient_zero : coefficients 0 = 0 :=
    column_four.resolve_right a_ne
  have coefficient_one : coefficients 1 = 0 :=
    column_five.resolve_right b_ne
  fin_cases index
  · exact coefficient_zero
  · exact coefficient_one
  · exact coefficient_two
  · exact coefficient_three
  · exact coefficient_four
  · exact coefficient_five

/-- Every exact representation of the forced forbidden-triple support has at least six states. -/
theorem six_le_card_of_forbiddenTripleSupport
    {K State : Type*} [Field K] [Fintype State]
    (rows : Fin 6 → State → K) (columns : Fin 6 → State → K)
    (a b c d e f g h i : K)
    (coefficient_eq :
      (fun row column => dotProduct (rows row) (columns column)) =
        forbiddenTripleSupportMatrix a b c d e f g h i)
    (a_ne : a ≠ 0) (b_ne : b ≠ 0) (c_ne : c ≠ 0)
    (d_ne : d ≠ 0) (f_ne : f ≠ 0) (h_ne : h ≠ 0) :
    6 ≤ Fintype.card State := by
  let probe : (State → K) →ₗ[K] (Fin 6 → K) :=
    { toFun := fun vector column => dotProduct vector (columns column)
      map_add' := by
        intro left right
        funext column
        exact add_dotProduct left right (columns column)
      map_smul' := by
        intro scalar vector
        funext column
        exact smul_dotProduct scalar vector (columns column) }
  have probe_row (row : Fin 6) :
      probe (rows row) = forbiddenTripleSupportMatrix a b c d e f g h i row := by
    funext column
    exact congrFun (congrFun coefficient_eq row) column
  have row_independent : LinearIndependent K rows := by
    rw [Fintype.linearIndependent_iff]
    intro coefficients combination_zero index
    have support_independent := forbiddenTripleSupport_rows_linearIndependent
      a b c d e f g h i a_ne b_ne c_ne d_ne f_ne h_ne
    rw [Fintype.linearIndependent_iff] at support_independent
    apply support_independent coefficients ?_ index
    calc
      ∑ row, coefficients row • forbiddenTripleSupportMatrix a b c d e f g h i row =
          ∑ row, coefficients row • probe (rows row) := by
        apply Finset.sum_congr rfl
        intro row _
        rw [probe_row]
      _ = probe (∑ row, coefficients row • rows row) := by
        simp
      _ = 0 := by rw [combination_zero]; exact probe.map_zero
  simpa [Module.finrank_fintype_fun_eq_card] using
    row_independent.fintype_card_le_finrank

end PositiveFreeCancellation

end MatrixMortality
