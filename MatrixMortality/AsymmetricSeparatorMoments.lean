import MatrixMortality.AsymmetricSeparatorRegularity

/-!
# Returns of the asymmetric chart

The fixed residual factorizations give the toggle and two data roles at times zero, one,
and two. Every later return is a nonzero scalar multiple of the asymmetric separator.
-/

namespace MatrixMortality.AsymmetricSeparatorRealization

open scoped Matrix
open ChangedSeparatorRealization (chainDataB chainDataC chainTailColumn)

variable (ρ q K : ℚ)

/-- Extrapolated geometric contribution at time zero. -/
private theorem geometric_outer :
    Matrix.vecMulVec (chainTailColumn ρ)
        (fun column => tailScale ρ q ^ 2 * separatorScale ρ q * separatorRow q column) =
      tailScale ρ q ^ 2 • separator ρ q := by
  ext row column
  simp [Matrix.vecMulVec, separator, smul_eq_mul]
  ring

/-- The first return is the nonzero rescaled toggle. -/
theorem moment_zero (regular : RegularChart ρ q K) :
    output ρ q K * input ρ q K =
      toggleScale ρ q K • pairedToggleMatrix ℚ := by
  rw [output, input, ThreeStepRealization.moment_zero, geometric_outer]
  rw [← factor_zero ρ q K regular.parameter_ne_zero regular.width_ne_zero
    regular.denominator_ne_zero regular.toggle_ne_zero]
  rw [pairedToggleMatrix_eq_permMatrix]
  ext row column
  simp [residualZero, smul_eq_mul]

/-- At time one the return is the unchanged paired `b` role. -/
theorem moment_one (regular : RegularChart ρ q K) :
    output ρ q K * transition ρ q * input ρ q K = chainDataB ρ := by
  rw [output, input, transition, ThreeStepRealization.moment_one, geometric_outer,
    smul_smul, ← factor_one ρ q K regular.parameter_ne_zero regular.width_ne_zero]
  have scalar : (1 / tailScale ρ q) * tailScale ρ q ^ 2 = tailScale ρ q := by
    field_simp
  rw [scalar]
  ext row column
  simp [residualOne, smul_eq_mul]

/-- At time two the return is the unchanged paired `c` role. -/
theorem moment_two (regular : RegularChart ρ q K) :
    output ρ q K * transition ρ q ^ 2 * input ρ q K = chainDataC (lowerCode q K) K := by
  rw [output, input, transition, ThreeStepRealization.moment_two, geometric_outer,
    smul_smul, ← factor_two ρ q K regular.parameter_ne_zero regular.width_ne_zero]
  have scalar : (1 / tailScale ρ q) ^ 2 * tailScale ρ q ^ 2 = 1 := by
    field_simp [regular.tail_ne_zero]
  rw [scalar, one_smul]
  simp [residualTwo]

/-- Every later return lies on the same separator ray. -/
theorem moment_add_three (n : Nat) :
    output ρ q K * transition ρ q ^ (n + 3) * input ρ q K =
      ((1 / tailScale ρ q) ^ (n + 3) * tailScale ρ q ^ 2) • separator ρ q := by
  rw [output, input, transition, ThreeStepRealization.moment_add_three, geometric_outer,
    smul_smul]

/-- The tail's scalar never vanishes on the source locus. -/
theorem tail_scalar_ne_zero (regular : RegularChart ρ q K) (n : Nat) :
    (1 / tailScale ρ q) ^ (n + 3) * tailScale ρ q ^ 2 ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (one_div_ne_zero regular.tail_ne_zero))
    (pow_ne_zero _ regular.tail_ne_zero)

/-- All transition-only words are nonzero. -/
theorem transition_pow_ne_zero (regular : RegularChart ρ q K) (n : Nat) :
    transition ρ q ^ n ≠ 0 :=
  ThreeStepRealization.transition_pow_ne_zero (1 / tailScale ρ q)
    (one_div_ne_zero regular.tail_ne_zero) n

end MatrixMortality.AsymmetricSeparatorRealization
