import MatrixMortality.MatrixSemigroup

/-!
# Rank-one matrix algebra

This file owns the source-independent algebra of column-row outer products.
-/

namespace MatrixMortality

open scoped Matrix

variable {ι κ μ 𝕜 : Type*} [Fintype ι] [Field 𝕜]

theorem mul_outer (matrix : Matrix κ ι 𝕜) (column : ι → 𝕜) (row : μ → 𝕜) :
    matrix * Matrix.vecMulVec column row = Matrix.vecMulVec (matrix *ᵥ column) row := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.mulVec, Matrix.vecMulVec_apply, Matrix.dotProduct]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem outer_mul (column : κ → 𝕜) (row : ι → 𝕜) (matrix : Matrix ι μ 𝕜) :
    Matrix.vecMulVec column row * matrix = Matrix.vecMulVec column (row ᵥ* matrix) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMul, Matrix.vecMulVec_apply, Matrix.dotProduct]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem outer_mul_outer (column row nextColumn nextRow : ι → 𝕜) :
    Matrix.vecMulVec column row * Matrix.vecMulVec nextColumn nextRow =
      (row ⬝ᵥ nextColumn) • Matrix.vecMulVec column nextRow := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.dotProduct,
    Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem vecMul_outer (active column row : ι → 𝕜) :
    active ᵥ* Matrix.vecMulVec column row = (active ⬝ᵥ column) • row := by
  ext j
  simp only [Matrix.vecMul, Matrix.vecMulVec_apply, Matrix.dotProduct,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  simp only [mul_assoc]

theorem vecMul_mul_outer
    (active : ι → 𝕜) (matrix : Square ι 𝕜) (column row : ι → 𝕜) :
    active ᵥ* (matrix * Matrix.vecMulVec column row) =
      (active ᵥ* matrix ⬝ᵥ column) • row := by
  rw [← Matrix.vecMul_vecMul, vecMul_outer]

omit [Fintype ι] in
theorem outer_ne_zero {column row : ι → 𝕜} (column_ne : column ≠ 0) (row_ne : row ≠ 0) :
    Matrix.vecMulVec column row ≠ 0 := by
  intro outer_zero
  apply column_ne
  funext i
  by_contra column_i_ne
  apply row_ne
  funext j
  by_contra row_j_ne
  have entry_zero := congr_fun (congr_fun outer_zero i) j
  simp only [Matrix.vecMulVec_apply, Pi.zero_apply] at entry_zero
  exact (mul_ne_zero column_i_ne row_j_ne) entry_zero

theorem unit_mulVec_ne_zero [DecidableEq ι] {matrix : Square ι 𝕜} {column : ι → 𝕜}
    (matrix_unit : IsUnit matrix) (column_ne : column ≠ 0) :
    matrix *ᵥ column ≠ 0 := by
  intro product_zero
  rcases matrix_unit.exists_left_inv with ⟨inverse, inverse_mul⟩
  apply column_ne
  calc
    column = 1 *ᵥ column := by simp
    _ = (inverse * matrix) *ᵥ column := by rw [inverse_mul]
    _ = inverse *ᵥ matrix *ᵥ column := by rw [Matrix.mulVec_mulVec]
    _ = 0 := by rw [product_zero]; simp

theorem vecMul_unit_ne_zero [DecidableEq ι] {row : ι → 𝕜} {matrix : Square ι 𝕜}
    (row_ne : row ≠ 0) (matrix_unit : IsUnit matrix) :
    row ᵥ* matrix ≠ 0 := by
  intro product_zero
  obtain ⟨inverse, matrix_inverse⟩ := matrix_unit.exists_right_inv
  apply row_ne
  calc
    row = row ᵥ* 1 := by simp
    _ = row ᵥ* (matrix * inverse) := by rw [matrix_inverse]
    _ = (row ᵥ* matrix) ᵥ* inverse := by rw [Matrix.vecMul_vecMul]
    _ = 0 := by rw [product_zero]; simp

end MatrixMortality
