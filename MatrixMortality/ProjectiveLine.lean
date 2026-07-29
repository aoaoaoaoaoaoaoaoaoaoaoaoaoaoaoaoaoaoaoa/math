import MatrixMortality.MatrixSemigroup

/-!
# The projective line as one affine chart and infinity

`Option K` is the canonical affine-chart presentation of `ℙ¹(K)`: `some z` denotes `[z:1]`
and `none` denotes `[1:0]`. The total matrix action below never divides at a pole. Its weight
records the nonzero homogeneous scalar discarded by projectivization.
-/

namespace MatrixMortality.ProjectiveLine

open scoped Matrix

noncomputable section

/-- Affine-chart presentation of the projective line; `none` is infinity. -/
abbrev Point (K : Type*) := Option K

/-- Canonical homogeneous representative of an affine point or infinity. -/
def ray {R : Type*} [Zero R] [One R] : Point R → Fin 2 → R
  | some z => ![z, 1]
  | none => ![1, 0]

/-- Affine numerator of a `2 × 2` matrix at `[z:1]`. -/
def numerator {R : Type*} [Semiring R] (matrix : Square (Fin 2) R) (z : R) : R :=
  matrix 0 0 * z + matrix 0 1

/-- Affine denominator of a `2 × 2` matrix at `[z:1]`. -/
def denominator {R : Type*} [Semiring R] (matrix : Square (Fin 2) R) (z : R) : R :=
  matrix 1 0 * z + matrix 1 1

/-- Total projective action of a matrix. A zero denominator produces infinity. -/
noncomputable def act {K : Type*} [Field K]
    (matrix : Square (Fin 2) K) (point : Point K) : Point K := by
  classical
  cases point with
  | some z =>
      exact if denominator matrix z = 0 then none
        else some (numerator matrix z / denominator matrix z)
  | none =>
      exact if matrix 1 0 = 0 then none
        else some (matrix 0 0 / matrix 1 0)

/-- Homogeneous scalar discarded by `act`. It is nonzero when the matrix is a unit. -/
noncomputable def weight {K : Type*} [Field K]
    (matrix : Square (Fin 2) K) (point : Point K) : K := by
  classical
  cases point with
  | some z =>
      exact if denominator matrix z = 0 then numerator matrix z
        else denominator matrix z
  | none =>
      exact if matrix 1 0 = 0 then matrix 0 0 else matrix 1 0

theorem ray_ne_zero {K : Type*} [Semiring K] [Nontrivial K] (point : Point K) :
    ray point ≠ 0 := by
  cases point with
  | none =>
      intro ray_zero
      have := congrFun ray_zero 0
      change (1 : K) = 0 at this
      exact one_ne_zero this
  | some z =>
      intro ray_zero
      have := congrFun ray_zero 1
      change (1 : K) = 0 at this
      exact one_ne_zero this

theorem mulVec_ray_some {R : Type*} [CommSemiring R]
    (matrix : Square (Fin 2) R) (z : R) :
    matrix *ᵥ ray (some z) = ![numerator matrix z, denominator matrix z] := by
  ext i
  fin_cases i <;>
    simp [ray, numerator, denominator, Matrix.mulVec, Matrix.dotProduct,
      Fin.sum_univ_succ]

theorem mulVec_ray_none {R : Type*} [CommSemiring R]
    (matrix : Square (Fin 2) R) :
    matrix *ᵥ ray none = ![matrix 0 0, matrix 1 0] := by
  ext i
  fin_cases i <;>
    simp [ray, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ]

/-- Every matrix acts on a projective ray by its total action and homogeneous weight. -/
theorem mulVec_ray_act
    {K : Type*} [Field K] (matrix : Square (Fin 2) K) (point : Point K) :
    matrix *ᵥ ray point = weight matrix point • ray (act matrix point) := by
  cases point with
  | none =>
      by_cases bottom_left_zero : matrix 1 0 = 0
      · rw [mulVec_ray_none]
        ext i
        fin_cases i <;>
          simp [act, weight, bottom_left_zero, ray]
      · rw [mulVec_ray_none]
        ext i
        fin_cases i <;>
          simp [act, weight, bottom_left_zero, ray]
        field_simp
  | some z =>
      by_cases denominator_zero : denominator matrix z = 0
      · rw [mulVec_ray_some]
        ext i
        fin_cases i <;>
          simp [act, weight, denominator_zero, ray]
      · rw [mulVec_ray_some]
        ext i
        fin_cases i <;>
          simp [act, weight, denominator_zero, ray]
        field_simp

/-- The projective weight of a unit is never zero. -/
theorem weight_ne_zero
    {K : Type*} [Field K] (matrix : Square (Fin 2) K) (matrix_unit : IsUnit matrix)
    (point : Point K) :
    weight matrix point ≠ 0 := by
  intro weight_zero
  have image_zero : matrix *ᵥ ray point = 0 := by
    rw [mulVec_ray_act matrix point, weight_zero, zero_smul]
  apply ray_ne_zero point
  apply Matrix.mulVec_injective_iff_isUnit.mpr matrix_unit
  simpa using image_zero

/-- Every word over unit matrices accumulates a nonzero projective weight. -/
theorem rayWeight_ne_zero
    {Label K : Type*} [Field K]
    (generators : Label → Square (Fin 2) K)
    (generator_unit : ∀ label, IsUnit (generators label))
    (word : List Label) (point : Point K) :
    rayWeight (fun label => act (generators label))
        (fun label => weight (generators label)) word point ≠ 0 := by
  induction word with
  | nil => simp [rayWeight]
  | cons label tail induction =>
      simp only [rayWeight]
      exact mul_ne_zero induction
        (weight_ne_zero (generators label) (generator_unit label)
          (rayState (fun label => act (generators label)) tail point))

/-- The covector `(1,-1)` cuts out exactly the finite projective point one. -/
theorem targetOne_iff {K : Type*} [Field K] (point : Point K) :
    ![1, -1] ⬝ᵥ ray point = 0 ↔ point = some 1 := by
  cases point with
  | none =>
      constructor
      · norm_num [ray, Matrix.dotProduct, Fin.sum_univ_succ]
      · intro impossible
        cases impossible
  | some z =>
      norm_num [ray, Matrix.dotProduct, Fin.sum_univ_succ]
      constructor
      · intro difference_zero
        exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using difference_zero)
      · rintro rfl
        simp

/-- A unit matrix word is cut by `(1,-1)` exactly when its projective orbit reaches one. -/
theorem targetOne_word_iff
    {Label K : Type*} [Field K]
    (generators : Label → Square (Fin 2) K)
    (generator_unit : ∀ label, IsUnit (generators label))
    (word : List Label) (point : Point K) :
    ![1, -1] ⬝ᵥ
        (wordProduct generators word *ᵥ ray point) = 0 ↔
      rayState (fun label => act (generators label)) word point = some 1 := by
  rw [wordProduct_mulVec_ray_action generators ray
    (fun label => act (generators label))
    (fun label => weight (generators label))
    (fun label state =>
      mulVec_ray_act (generators label) state)
    word point]
  rw [Matrix.dotProduct_smul]
  have accumulated_ne :=
    rayWeight_ne_zero generators generator_unit word point
  simpa [smul_eq_mul, accumulated_ne] using
    targetOne_iff
      (rayState (fun label => act (generators label)) word point)

end
end MatrixMortality.ProjectiveLine
