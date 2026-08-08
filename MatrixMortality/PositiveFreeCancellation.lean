import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Tactic.Group

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
  | C1 => exact ⟨[], triangleEvaluate_nil⟩
  | Cp bit =>
      cases bit
      · refine ⟨[.x], ?_⟩
        change triangleEvaluate [.x] = FreeGroup.of false
        simp [triangleGenerator]
      · refine ⟨[.y], ?_⟩
        change triangleEvaluate [.y] = FreeGroup.of true
        simp [triangleGenerator]
  | Ci bit _ =>
      cases bit
      · refine ⟨[.y, .z], ?_⟩
        change triangleEvaluate [.y, .z] = (FreeGroup.of false)⁻¹
        simp [triangleGenerator, mul_assoc]
      · refine ⟨[.z, .x], ?_⟩
        change triangleEvaluate [.z, .x] = (FreeGroup.of true)⁻¹
        simp [triangleGenerator, mul_assoc]
  | Cm left right left_spelling right_spelling =>
      rcases left_spelling with ⟨left_word, left_eq⟩
      rcases right_spelling with ⟨right_word, right_eq⟩
      exact ⟨left_word ++ right_word, by simp [left_eq, right_eq]⟩

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

end PositiveFreeCancellation

end MatrixMortality
