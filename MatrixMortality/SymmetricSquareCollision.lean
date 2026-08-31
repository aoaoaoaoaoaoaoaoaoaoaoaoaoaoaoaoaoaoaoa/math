import MatrixMortality.MatrixSemigroup

/-!
# Symmetric-square projective collision

The covariant symmetric square sends a homogeneous pair `(x, y)` to the Veronese vector
`(x², xy, y²)`.  A tangent row at one Veronese vector evaluates another to the square of their
projective cross determinant.  Thus projective collision becomes one exact scalar zero test in
three coordinates, with an integral gap away from zero.

The determinant of three Veronese columns also factors into the three pairwise cross
determinants.  Consequently a singular three-column carrier contains at most two pairwise
distinct projective rays.  These identities supply a collision detector and a fork obstruction;
they do not supply a directional inverse parser or a mortality compiler.
-/

namespace MatrixMortality.SymmetricSquareCollision

open scoped Matrix

/-- Homogeneous pairs on which the binary covariant acts. -/
abbrev Pair (R : Type*) := Fin 2 → R

/-- Symmetric-square coordinate triples. -/
abbrev Triple (R : Type*) := Fin 3 → R

/-- The quadratic Veronese embedding `(x,y) ↦ (x²,xy,y²)`. -/
def veronese {R : Type*} [CommRing R] (vector : Pair R) : Triple R :=
  ![vector 0 ^ 2, vector 0 * vector 1, vector 1 ^ 2]

/-- The covariant symmetric-square representation in the Veronese basis. -/
def symmetricSquare {R : Type*} [CommRing R]
    (matrix : Square (Fin 2) R) : Square (Fin 3) R :=
  !![matrix 0 0 ^ 2, 2 * matrix 0 0 * matrix 0 1, matrix 0 1 ^ 2;
     matrix 0 0 * matrix 1 0,
       matrix 0 0 * matrix 1 1 + matrix 0 1 * matrix 1 0,
       matrix 0 1 * matrix 1 1;
     matrix 1 0 ^ 2, 2 * matrix 1 0 * matrix 1 1, matrix 1 1 ^ 2]

/-- The alternating determinant of two homogeneous pairs. -/
def crossDet {R : Type*} [CommRing R] (left right : Pair R) : R :=
  left 0 * right 1 - left 1 * right 0

/-- The tangent covector to the Veronese cone at `veronese vector`, up to sign. -/
def tangentRow {R : Type*} [CommRing R] (vector : Pair R) : Triple R :=
  ![vector 1 ^ 2, -(2 * vector 0 * vector 1), vector 0 ^ 2]

/-- The scalar obtained by testing a Veronese vector against a tangent row. -/
def tangentValue {R : Type*} [CommRing R] (left right : Pair R) : R :=
  dotProduct (tangentRow left) (veronese right)

/-- Three Veronese vectors arranged as columns. -/
def veroneseColumns {R : Type*} [CommRing R]
    (first second third : Pair R) : Square (Fin 3) R :=
  fun row column => ![veronese first, veronese second, veronese third] column row

/-- A fixed three-state leakage between binary changes of projective coordinates. -/
def leakedVeroneseColumns {R : Type*} [CommRing R]
    (post : Square (Fin 2) R) (leakage : Square (Fin 3) R)
    (pre : Square (Fin 2) R) (first second third : Pair R) : Square (Fin 3) R :=
  symmetricSquare post * leakage * symmetricSquare pre *
    veroneseColumns first second third

/-- The symmetric-square matrix sends each Veronese vector to the Veronese vector of its image. -/
theorem symmetricSquare_mulVec_veronese {R : Type*} [CommRing R]
    (matrix : Square (Fin 2) R) (vector : Pair R) :
    symmetricSquare matrix *ᵥ veronese vector = veronese (matrix *ᵥ vector) := by
  funext i
  fin_cases i <;>
    simp [symmetricSquare, veronese, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    ring

/-- Symmetric square respects matrix multiplication. -/
theorem symmetricSquare_mul {R : Type*} [CommRing R]
    (left right : Square (Fin 2) R) :
    symmetricSquare (left * right) = symmetricSquare left * symmetricSquare right := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symmetricSquare, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

@[simp]
theorem symmetricSquare_one {R : Type*} [CommRing R] :
    symmetricSquare (1 : Square (Fin 2) R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symmetricSquare]

/-- Symmetric square as a multiplicative representation. -/
def symmetricSquareHom (R : Type*) [CommRing R] :
    Square (Fin 2) R →* Square (Fin 3) R where
  toFun := symmetricSquare
  map_one' := symmetricSquare_one
  map_mul' := symmetricSquare_mul

/-- Applying symmetric square generatorwise agrees with applying it after the whole word. -/
theorem wordProduct_symmetricSquare {R α : Type*} [CommRing R]
    (generators : α → Square (Fin 2) R) (word : List α) :
    wordProduct (symmetricSquare ∘ generators) word =
      symmetricSquare (wordProduct generators word) := by
  exact wordProduct_map (symmetricSquareHom R) generators word

/-- The determinant character of the symmetric square is the third power. -/
theorem symmetricSquare_det {R : Type*} [CommRing R]
    (matrix : Square (Fin 2) R) :
    (symmetricSquare matrix).det = matrix.det ^ 3 := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two]
  simp [symmetricSquare]
  ring

/-- A nonsingular binary matrix has a nonsingular three-coordinate symmetric square. -/
theorem symmetricSquare_det_ne_zero {K : Type*} [Field K]
    {matrix : Square (Fin 2) K} (det_ne_zero : matrix.det ≠ 0) :
    (symmetricSquare matrix).det ≠ 0 := by
  rw [symmetricSquare_det]
  exact pow_ne_zero 3 det_ne_zero

/-- The three-coordinate cost is exact: a nonsingular binary input yields rank three. -/
theorem symmetricSquare_rank_eq_three {K : Type*} [Field K]
    {matrix : Square (Fin 2) K} (det_ne_zero : matrix.det ≠ 0) :
    (symmetricSquare matrix).rank = 3 := by
  apply Matrix.rank_of_isUnit
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  exact symmetricSquare_det_ne_zero det_ne_zero

/-- The tangent test is exactly the square of the projective cross determinant. -/
theorem tangentValue_eq_crossDet_sq {R : Type*} [CommRing R]
    (left right : Pair R) :
    tangentValue left right = crossDet left right ^ 2 := by
  simp [tangentValue, tangentRow, veronese, crossDet, dotProduct, Fin.sum_univ_succ]
  ring

@[simp]
theorem tangentValue_self {R : Type*} [CommRing R] (vector : Pair R) :
    tangentValue vector vector = 0 := by
  rw [tangentValue_eq_crossDet_sq]
  simp only [crossDet]
  ring

/-- A binary matrix scales the cross determinant by its determinant. -/
theorem crossDet_mulVec {R : Type*} [CommRing R]
    (matrix : Square (Fin 2) R) (left right : Pair R) :
    crossDet (matrix *ᵥ left) (matrix *ᵥ right) =
      matrix.det * crossDet left right := by
  rw [Matrix.det_fin_two]
  simp [crossDet, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- Simultaneous binary transport scales the tangent test by the squared determinant. -/
theorem tangentValue_mulVec {R : Type*} [CommRing R]
    (matrix : Square (Fin 2) R) (left right : Pair R) :
    tangentValue (matrix *ᵥ left) (matrix *ᵥ right) =
      matrix.det ^ 2 * tangentValue left right := by
  rw [tangentValue_eq_crossDet_sq, crossDet_mulVec, tangentValue_eq_crossDet_sq]
  ring

/-- A word of symmetric-square generators tests binary endpoint collision by one scalar square. -/
theorem wordTangentValue_eq_crossDet_sq {R α : Type*} [CommRing R]
    (generators : α → Square (Fin 2) R) (word : List α) (target source : Pair R) :
    dotProduct (tangentRow target)
        (wordProduct (symmetricSquare ∘ generators) word *ᵥ veronese source) =
      crossDet target (wordProduct generators word *ᵥ source) ^ 2 := by
  rw [wordProduct_symmetricSquare, symmetricSquare_mulVec_veronese]
  exact tangentValue_eq_crossDet_sq target (wordProduct generators word *ᵥ source)

/-- Over the integers, the tangent scalar vanishes exactly at projective collision. -/
theorem tangentValue_int_eq_zero_iff (left right : Pair ℤ) :
    tangentValue left right = 0 ↔ crossDet left right = 0 := by
  rw [tangentValue_eq_crossDet_sq, sq_eq_zero_iff]

/-- The three-state word coefficient vanishes exactly at integer projective endpoint collision. -/
theorem wordTangentValue_int_eq_zero_iff {α : Type*}
    (generators : α → Square (Fin 2) ℤ) (word : List α) (target source : Pair ℤ) :
    dotProduct (tangentRow target)
        (wordProduct (symmetricSquare ∘ generators) word *ᵥ veronese source) = 0 ↔
      crossDet target (wordProduct generators word *ᵥ source) = 0 := by
  rw [wordTangentValue_eq_crossDet_sq, sq_eq_zero_iff]

/-- A noncollision over the integer lattice has a discrete tangent gap of at least one. -/
theorem one_le_tangentValue_int_of_crossDet_ne_zero (left right : Pair ℤ)
    (cross_ne_zero : crossDet left right ≠ 0) :
    1 ≤ tangentValue left right := by
  rw [tangentValue_eq_crossDet_sq, one_le_sq_iff_one_le_abs]
  exact Int.one_le_abs cross_ne_zero

/-- Three Veronese columns have the Vandermonde determinant given by pairwise cross determinants. -/
theorem veroneseColumns_det {R : Type*} [CommRing R] (first second third : Pair R) :
    (veroneseColumns first second third).det =
      crossDet first second * crossDet first third * crossDet second third := by
  rw [Matrix.det_fin_three]
  simp [veroneseColumns, veronese, crossDet]
  ring

/-- Fixed leakage and binary coordinate changes multiply the three-ray determinant character. -/
theorem leakedVeroneseColumns_det
    {R : Type*} [CommRing R]
    (post : Square (Fin 2) R) (leakage : Square (Fin 3) R)
    (pre : Square (Fin 2) R) (first second third : Pair R) :
    (leakedVeroneseColumns post leakage pre first second third).det =
      post.det ^ 3 * leakage.det * pre.det ^ 3 *
        crossDet first second * crossDet first third * crossDet second third := by
  rw [leakedVeroneseColumns, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul,
    symmetricSquare_det, symmetricSquare_det, veroneseColumns_det]
  ring

/-- Full-rank fixed leakage cannot collapse three pairwise distinct rays into a plane. -/
theorem leakedVeroneseColumns_det_ne_zero
    {R : Type*} [CommRing R] [IsDomain R]
    {post : Square (Fin 2) R} {leakage : Square (Fin 3) R}
    {pre : Square (Fin 2) R} {first second third : Pair R}
    (post_ne_zero : post.det ≠ 0) (leakage_ne_zero : leakage.det ≠ 0)
    (pre_ne_zero : pre.det ≠ 0)
    (first_second_distinct : crossDet first second ≠ 0)
    (first_third_distinct : crossDet first third ≠ 0)
    (second_third_distinct : crossDet second third ≠ 0) :
    (leakedVeroneseColumns post leakage pre first second third).det ≠ 0 := by
  rw [leakedVeroneseColumns_det]
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero (pow_ne_zero 3 post_ne_zero) leakage_ne_zero)
            (pow_ne_zero 3 pre_ne_zero))
          first_second_distinct)
        first_third_distinct)
      second_third_distinct

/-- If a fixed leakage sends three distinct rays into a plane, that leakage is singular. -/
theorem leakage_det_eq_zero_of_three_distinct_carrier
    {R : Type*} [CommRing R] [IsDomain R]
    {post : Square (Fin 2) R} {leakage : Square (Fin 3) R}
    {pre : Square (Fin 2) R} {first second third : Pair R}
    (post_ne_zero : post.det ≠ 0) (pre_ne_zero : pre.det ≠ 0)
    (first_second_distinct : crossDet first second ≠ 0)
    (first_third_distinct : crossDet first third ≠ 0)
    (second_third_distinct : crossDet second third ≠ 0)
    (carrier_singular :
      (leakedVeroneseColumns post leakage pre first second third).det = 0) :
    leakage.det = 0 := by
  by_contra leakage_ne_zero
  exact leakedVeroneseColumns_det_ne_zero post_ne_zero leakage_ne_zero pre_ne_zero
    first_second_distinct first_third_distinct second_third_distinct carrier_singular

/-- Three singular Veronese columns contain a projectively colliding pair. -/
theorem exists_pairwise_crossDet_eq_zero_of_veroneseColumns_det_eq_zero
    {R : Type*} [CommRing R] [IsDomain R] (first second third : Pair R)
    (singular : (veroneseColumns first second third).det = 0) :
    crossDet first second = 0 ∨ crossDet first third = 0 ∨ crossDet second third = 0 := by
  rw [veroneseColumns_det, mul_eq_zero, mul_eq_zero] at singular
  rcases singular with (collision | collision) | collision
  · exact Or.inl collision
  · exact Or.inr (Or.inl collision)
  · exact Or.inr (Or.inr collision)

/-- Once two rays are distinct, any third ray in their singular Veronese carrier repeats one. -/
theorem crossDet_first_third_eq_zero_or_second_third_eq_zero_of_det_eq_zero
    {R : Type*} [CommRing R] [IsDomain R] (first second third : Pair R)
    (first_second_distinct : crossDet first second ≠ 0)
    (singular : (veroneseColumns first second third).det = 0) :
    crossDet first third = 0 ∨ crossDet second third = 0 := by
  rcases exists_pairwise_crossDet_eq_zero_of_veroneseColumns_det_eq_zero
      first second third singular with collision | collision | collision
  · exact False.elim (first_second_distinct collision)
  · exact Or.inl collision
  · exact Or.inr collision

end MatrixMortality.SymmetricSquareCollision
