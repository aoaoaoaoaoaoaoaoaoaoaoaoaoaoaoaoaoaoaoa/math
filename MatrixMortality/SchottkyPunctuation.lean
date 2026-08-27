import Mathlib.Data.Matrix.Kronecker
import MatrixMortality.TerminalTile

namespace MatrixMortality.SchottkyPunctuation

open scoped Matrix Kronecker

variable {R : Type*} [CommRing R]

/-- Integral left-right action on the four-dimensional matrix lattice. -/
def leftRight (A B : Matrix (Fin 2) (Fin 2) R) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) R :=
  B.adjugateᵀ ⊗ₖ A

/-- Vectorized matrix unit `E₁₂`. -/
def equalityColumn : Fin 2 × Fin 2 → R := fun index =>
  if index.1 = 1 ∧ index.2 = 0 then 1 else 0

/-- Trace covector on the matrix lattice. -/
def equalityRow : Fin 2 × Fin 2 → R := fun index =>
  if index.1 = index.2 then 1 else 0

/-- The homogeneous equality detector is the determinant of the first columns. -/
theorem equalityCoefficient (A B : Matrix (Fin 2) (Fin 2) R) :
    equalityRow ⬝ᵥ leftRight A B *ᵥ equalityColumn =
      A 1 0 * B 0 0 - A 0 0 * B 1 0 := by
  simp [equalityRow, equalityColumn, leftRight, Matrix.dotProduct, Matrix.mulVec,
    Matrix.kronecker_apply, Matrix.adjugate_fin_two, Matrix.transpose_apply,
    Matrix.vecHead, Matrix.vecTail, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

/-- Left-right actions compose covariantly in both group coordinates. -/
theorem leftRight_mul (A₁ A₂ B₁ B₂ : Matrix (Fin 2) (Fin 2) R) :
    leftRight A₁ B₁ * leftRight A₂ B₂ = leftRight (A₁ * A₂) (B₁ * B₂) := by
  rw [leftRight, leftRight, leftRight]
  rw [← Matrix.mul_kronecker_mul]
  rw [Matrix.adjugate_mul_distrib, Matrix.transpose_mul]

/-- Unimodular pairs act by unimodular four-dimensional matrices. -/
theorem leftRight_det (A B : Matrix (Fin 2) (Fin 2) R)
    (detA : A.det = 1) (detB : B.det = 1) :
    (leftRight A B).det = 1 := by
  rw [leftRight, Matrix.det_kronecker, Matrix.det_transpose, Matrix.det_adjugate,
    detA, detB]
  norm_num

end MatrixMortality.SchottkyPunctuation
