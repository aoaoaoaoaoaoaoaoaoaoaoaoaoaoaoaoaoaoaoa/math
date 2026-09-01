import MatrixMortality.MatrixSemigroup
import Mathlib.Tactic

/-!
# Entrywise denominator clearing for finite rational matrices

The product of all entry denominators clears a finite rational matrix.  Scaling each generator
independently by this positive integer preserves its zero-product language.
-/

namespace MatrixMortality
namespace RationalMatrixClearing

/-- Product of every entry denominator in a finite rational matrix. -/
def matrixDenominator {m n : Type*} [Fintype m] [Fintype n]
    (matrix : Matrix m n ℚ) : Nat :=
  ∏ row, ∏ column, (matrix row column).den

theorem entryDenominator_dvd_matrixDenominator {m n : Type*}
    [Fintype m] [Fintype n] (matrix : Matrix m n ℚ) (row : m) (column : n) :
    (matrix row column).den ∣ matrixDenominator matrix := by
  have divides_row :
      (matrix row column).den ∣ ∏ nextColumn, (matrix row nextColumn).den :=
    Finset.dvd_prod_of_mem (fun nextColumn => (matrix row nextColumn).den)
      (Finset.mem_univ column)
  exact divides_row.trans
    (Finset.dvd_prod_of_mem
      (fun nextRow => ∏ nextColumn, (matrix nextRow nextColumn).den)
      (Finset.mem_univ row))

theorem matrixDenominator_ne_zero {m n : Type*} [Fintype m] [Fintype n]
    (matrix : Matrix m n ℚ) : matrixDenominator matrix ≠ 0 := by
  rw [matrixDenominator, Finset.prod_ne_zero_iff]
  intro row _
  rw [Finset.prod_ne_zero_iff]
  exact fun column _ => (matrix row column).den_nz

/-- Integer matrix obtained by clearing every rational entry with one positive common scale. -/
def clearRationalMatrix {m n : Type*} [Fintype m] [Fintype n]
    (matrix : Matrix m n ℚ) : Matrix m n ℤ :=
  fun row column =>
    ((matrixDenominator matrix / (matrix row column).den : Nat) : ℤ) *
      (matrix row column).num

/-- Casting the cleared matrix back to `ℚ` is multiplication by its denominator product. -/
theorem castMatrix_clearRationalMatrix {m n : Type*} [Fintype m] [Fintype n]
    (matrix : Matrix m n ℚ) :
    castMatrix (clearRationalMatrix matrix) = (matrixDenominator matrix : ℚ) • matrix := by
  ext row column
  have denominator_dvd := entryDenominator_dvd_matrixDenominator matrix row column
  have denominator_cast_ne : ((matrix row column).den : ℚ) ≠ 0 := by
    exact_mod_cast (matrix row column).den_nz
  change
    ((((matrixDenominator matrix / (matrix row column).den : Nat) : ℤ) *
        (matrix row column).num : ℤ) : ℚ) =
      (matrixDenominator matrix : ℚ) * matrix row column
  have cast_product :
      ((((matrixDenominator matrix / (matrix row column).den : Nat) : ℤ) *
          (matrix row column).num : ℤ) : ℚ) =
        (matrixDenominator matrix / (matrix row column).den : ℕ) *
          ((matrix row column).num : ℚ) := by
    simp only [Int.cast_mul, Int.cast_natCast]
  rw [cast_product]
  calc
    ((matrixDenominator matrix / (matrix row column).den : Nat) : ℚ) *
          ((matrix row column).num : ℚ) =
        (matrixDenominator matrix : ℚ) *
          ((matrix row column).num : ℚ) / (matrix row column).den := by
      rw [Nat.cast_div denominator_dvd denominator_cast_ne]
      ring
    _ = (matrixDenominator matrix : ℚ) * matrix row column := by
      calc
        (matrixDenominator matrix : ℚ) * ((matrix row column).num : ℚ) /
              (matrix row column).den =
            (matrixDenominator matrix : ℚ) *
              (((matrix row column).num : ℚ) / (matrix row column).den) := by ring
        _ = (matrixDenominator matrix : ℚ) * matrix row column := by
          rw [Rat.num_div_den]

/-- Clear every generator independently. -/
def clearRationalFamily {α ι : Type*} [Fintype ι]
    (generators : α → Square ι ℚ) : α → Square ι ℤ :=
  clearRationalMatrix ∘ generators

theorem castMatrix_clearRationalFamily {α ι : Type*} [Fintype ι]
    (generators : α → Square ι ℚ) :
    castMatrix ∘ clearRationalFamily generators =
      fun label => (matrixDenominator (generators label) : ℚ) • generators label := by
  funext label
  exact castMatrix_clearRationalMatrix (generators label)

/-- Independent positive denominator clearing preserves mortality. -/
theorem clearRationalFamily_mortal_iff {α ι : Type*}
    [Fintype ι] [DecidableEq ι] (generators : α → Square ι ℚ) :
    IsMortal (clearRationalFamily generators) ↔ IsMortal generators := by
  rw [← isMortal_cast_iff (clearRationalFamily generators),
    castMatrix_clearRationalFamily,
    isMortal_smulMatrix_iff (fun label => (matrixDenominator (generators label) : ℚ))
      (fun label => by exact_mod_cast matrixDenominator_ne_zero (generators label))]

end RationalMatrixClearing
end MatrixMortality
