import MatrixMortality.ChangedSeparatorRealization
import MatrixMortality.ThreeStepRealization

/-!
# Fixed chart for the asymmetric eight-state return

The chart uses the old paired data roles, an asymmetric separator row, and a rescaled toggle.
All coordinates use the operation-only fraction interface so the same expressions can later
be evaluated in certified unreduced fractions. The fixed column section avoids rank tests.
-/

namespace MatrixMortality.AsymmetricSeparatorRealization

open scoped Matrix
open ChangedSeparatorRealization (chainDataB chainDataC chainTailColumn)

section Arithmetic

variable {R : Type*} [FractionArithmetic R]

/-- Twice the common phase slope plus one. -/
def tailParameter (q : R) : R := 2 * q + 1

/-- The body code forced by the asymmetric separator ratio. -/
def lowerCode (q K : R) : R := (K + 48 - q * (K - 27)) / 3

/-- Scale of the rank-one return separator. -/
def separatorScale (ρ q : R) : R := 6 / (tailParameter q * (3 * ρ - 1))

/-- Reciprocal of the surviving transition eigenvalue. -/
def tailScale (ρ q : R) : R := 3 * ρ + 1 + ρ * separatorScale ρ q

/-- Denominator of the rescaled toggle. -/
def toggleDenominator (ρ q K : R) : R :=
  K * ((tailParameter q - 2) * ρ - tailParameter q) + 26 * tailParameter q + 72

/-- Zeroth-return scaling needed to reduce the transient to seven states. -/
def toggleScale (ρ q K : R) : R :=
  K * (tailParameter q * (27 * ρ ^ 3 - 1) + 18 * ρ ^ 2 + 6 * ρ) /
    toggleDenominator ρ q K

/-- The two phase slots deliberately have different tail values. -/
def separatorRow (q : R) : Fin 4 → R := ![1, 16 + 9 * q, q, q]

/-- Rank-one return separator, written without requiring laws of fraction syntax. -/
def separator (ρ q : R) : Square (Fin 4) R :=
  Matrix.of fun row column =>
    separatorScale ρ q * chainTailColumn ρ row * separatorRow q column

/-- Four-term contraction also evaluates in the operation-only fraction interpreter. -/
def contractFour {m n : Type*} (left : Matrix m (Fin 4) R)
    (right : Matrix (Fin 4) n R) : Matrix m n R :=
  Matrix.of fun row column => left row 0 * right 0 column + left row 1 * right 1 column +
    left row 2 * right 2 column + left row 3 * right 3 column

/-- Two-term contraction for the two nilpotent chains. -/
def contractTwo {m n : Type*} (left : Matrix m (Fin 2) R)
    (right : Matrix (Fin 2) n R) : Matrix m n R :=
  Matrix.of fun row column => left row 0 * right 0 column + left row 1 * right 1 column

/-- Fixed section using columns zero and two. -/
def columnSection (matrix : Square (Fin 4) R) : Matrix (Fin 4) (Fin 2) R :=
  Matrix.of fun row => ![matrix row 0, matrix row 2]

/-- The zeroth moment after subtracting the extrapolated geometric tail. -/
def residualZero (ρ q K : R) : Square (Fin 4) R :=
  Matrix.of fun row column =>
    toggleScale ρ q K * (Equiv.swap (1 : Fin 4) 3).permMatrix R row column -
      tailScale ρ q ^ 2 * separator ρ q row column

/-- The first exceptional moment after subtracting the geometric tail. -/
def residualOne (ρ q : R) : Square (Fin 4) R :=
  Matrix.of fun row column =>
    chainDataB ρ row column - tailScale ρ q * separator ρ q row column

/-- The final exceptional moment after subtracting the geometric tail. -/
def residualTwo (ρ q K : R) : Square (Fin 4) R :=
  chainDataC (lowerCode q K) K - separator ρ q

/-- A fixed left inverse for the last residual's selected columns. -/
def sectionInverse (ρ q : R) : Matrix (Fin 2) (Fin 4) R :=
  !![0, 0, -q / 3, (3 * ρ - tailParameter q) / 6;
     0, 0, 1 / 3, ρ]

/-- Input at the beginning of the two length-three chains. -/
def inputTwo (ρ q K : R) : Matrix (Fin 2) (Fin 4) R :=
  !![1, 16 + 9 * q + K * (3 * ρ - tailParameter q) / 6, 0, (3 * ρ - 1) / 2;
     0, ρ * K, 1, 3 * ρ]

/-- Input at the middle depth, obtained by the fixed left inverse. -/
def inputOne (ρ q K : R) : Matrix (Fin 2) (Fin 4) R :=
  contractFour (sectionInverse ρ q)
    (residualOne ρ q - contractTwo (columnSection (residualOne ρ q)) (inputTwo ρ q K))

/-- Zeroth residual left after assigning the two nonstatic input depths. -/
def staticResidual (ρ q K : R) : Square (Fin 4) R :=
  residualZero ρ q K - contractTwo (columnSection (residualZero ρ q K)) (inputTwo ρ q K) -
    contractTwo (columnSection (residualOne ρ q)) (inputOne ρ q K)

/-- A fixed preimage of the separator column under the final data role. -/
def kernelColumn (ρ : R) : Fin 4 → R := ![(3 * ρ - 1) / 6, 0, ρ, -(1 / 3)]

/-- The remaining static input uses the last interface coordinate. -/
def staticRow (ρ q K : R) : Fin 4 → R := ![0, 0, 0, toggleScale ρ q K]

/-- The static output is selected by the fixed kernel column, without choosing a pivot. -/
def staticColumn (ρ q K : R) : Fin 4 → R :=
  fun row => -3 / toggleScale ρ q K *
    (staticResidual ρ q K row 0 * kernelColumn ρ 0 +
     staticResidual ρ q K row 1 * kernelColumn ρ 1 +
     staticResidual ρ q K row 2 * kernelColumn ρ 2 +
     staticResidual ρ q K row 3 * kernelColumn ρ 3)

/-- Input at the last nilpotent depth after removing the static residual. -/
def inputZero (ρ q K : R) : Matrix (Fin 2) (Fin 4) R :=
  contractFour (sectionInverse ρ q) (staticResidual ρ q K -
    Matrix.of fun row column => staticColumn ρ q K row * staticRow ρ q K column)

/-- The eight-state input; its last row extrapolates the separator to time zero. -/
def input (ρ q K : R) : Matrix (Fin 8) (Fin 4) R :=
  ThreeStepRealization.input (inputZero ρ q K) (inputOne ρ q K) (inputTwo ρ q K)
    (staticRow ρ q K) (fun column => tailScale ρ q ^ 2 * separatorScale ρ q * separatorRow q column)

/-- The eight-state output uses the fixed residual columns and the separator column. -/
def output (ρ q K : R) : Matrix (Fin 4) (Fin 8) R :=
  ThreeStepRealization.output (columnSection (residualZero ρ q K))
    (columnSection (residualOne ρ q)) (columnSection (residualTwo ρ q K))
    (staticColumn ρ q K) (chainTailColumn ρ)

/-- Transition of the fixed chart. -/
def transition (ρ q : R) : Square (Fin 8) R :=
  ThreeStepRealization.transition (1 / tailScale ρ q)

end Arithmetic

section Factorization

variable (ρ q K : ℚ)

theorem contractFour_eq_mul {m n : Type*}
    (left : Matrix m (Fin 4) ℚ) (right : Matrix (Fin 4) n ℚ) :
    contractFour left right = left * right := by
  ext row column
  simp [contractFour, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

theorem contractTwo_eq_mul {m n : Type*}
    (left : Matrix m (Fin 2) ℚ) (right : Matrix (Fin 2) n ℚ) :
    contractTwo left right = left * right := by
  ext row column
  simp [contractTwo, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The selected columns factor the last residual uniformly. -/
theorem factor_two (parameter_ne_zero : tailParameter q ≠ 0)
    (width_ne_zero : 3 * ρ - 1 ≠ 0) :
    residualTwo ρ q K = columnSection (residualTwo ρ q K) * inputTwo ρ q K := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [residualTwo, columnSection, inputTwo, chainDataC, lowerCode, separator,
      separatorScale, chainTailColumn, separatorRow, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp [parameter_ne_zero, width_ne_zero] <;>
    simp only [tailParameter] <;>
    ring

/-- The middle residual fits the same two chains after removing their first contribution. -/
theorem factor_one (parameter_ne_zero : tailParameter q ≠ 0)
    (width_ne_zero : 3 * ρ - 1 ≠ 0) :
    residualOne ρ q = columnSection (residualOne ρ q) * inputTwo ρ q K +
      columnSection (residualTwo ρ q K) * inputOne ρ q K := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [inputOne, contractFour, contractTwo, sectionInverse, residualOne, residualTwo,
      columnSection, inputTwo, chainDataB, chainDataC, lowerCode, separator, tailScale,
      separatorScale, chainTailColumn, separatorRow, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp [parameter_ne_zero, width_ne_zero] <;>
    simp only [tailParameter] <;>
    ring

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in
/-- The remaining zeroth residual needs only the one static state. -/
theorem factor_zero (parameter_ne_zero : tailParameter q ≠ 0)
    (width_ne_zero : 3 * ρ - 1 ≠ 0)
    (denominator_ne_zero : toggleDenominator ρ q K ≠ 0)
    (toggle_ne_zero : toggleScale ρ q K ≠ 0) :
    residualZero ρ q K = columnSection (residualZero ρ q K) * inputTwo ρ q K +
      columnSection (residualOne ρ q) * inputOne ρ q K +
      columnSection (residualTwo ρ q K) * inputZero ρ q K +
      Matrix.vecMulVec (staticColumn ρ q K) (staticRow ρ q K) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [inputZero, staticColumn, staticRow, kernelColumn, staticResidual, inputOne,
      contractFour, contractTwo, sectionInverse, residualZero, residualOne, residualTwo,
      columnSection, inputTwo, chainDataB, chainDataC, lowerCode, separator, tailScale,
      separatorScale, chainTailColumn, separatorRow, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.vecMulVec, Equiv.Perm.permMatrix, PEquiv.toMatrix, Equiv.swap_apply_def] <;>
    field_simp [parameter_ne_zero, width_ne_zero, toggle_ne_zero] <;>
    simp only [toggleScale] <;>
    field_simp [denominator_ne_zero] <;>
    simp only [tailParameter, toggleDenominator] <;>
    ring

end Factorization

end MatrixMortality.AsymmetricSeparatorRealization
