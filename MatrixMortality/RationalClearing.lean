import Mathlib.LinearAlgebra.Matrix.Integer
import MatrixMortality.MatrixSemigroup

/-!
# Rational matrix denominator clearing

The canonical integer numerator of each rational generator differs from that generator by its
nonzero matrix denominator. Independent generator scaling therefore preserves mortality.
-/

namespace MatrixMortality

open scoped Matrix

/-- Clear every rational generator by its canonical positive matrix denominator. -/
def clearRationalFamily
    {α ι : Type*} [Fintype ι]
    (generators : α → Square ι ℚ) : α → Square ι ℤ :=
  fun label => (generators label).num

theorem castMatrix_num_eq_den_smul
    {ι : Type*} [Fintype ι]
    (matrix : Square ι ℚ) :
    castMatrix matrix.num = (matrix.den : ℚ) • matrix := by
  ext row column
  change (matrix.num row column : ℚ) = (matrix.den : ℚ) * matrix row column
  rw [← Matrix.num_div_den matrix]
  field_simp [matrix.den_ne_zero]

theorem castMatrix_clearRationalFamily
    {α ι : Type*} [Fintype ι]
    (generators : α → Square ι ℚ) :
    castMatrix ∘ clearRationalFamily generators =
      fun label => ((generators label).den : ℚ) • generators label := by
  funext label
  exact castMatrix_num_eq_den_smul (generators label)

/-- Canonical entrywise denominator clearing preserves every zero product exactly. -/
theorem clearRationalFamily_isMortal_iff
    {α ι : Type*} [Fintype ι] [DecidableEq ι]
    (generators : α → Square ι ℚ) :
    IsMortal (clearRationalFamily generators) ↔ IsMortal generators := by
  rw [← isMortal_cast_iff (clearRationalFamily generators),
    castMatrix_clearRationalFamily generators]
  apply isMortal_smulMatrix_iff
  intro label
  exact_mod_cast (generators label).den_ne_zero

end MatrixMortality
