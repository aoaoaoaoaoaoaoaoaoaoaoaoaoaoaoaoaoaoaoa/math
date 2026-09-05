import MatrixMortality.AsymmetricSeparatorRealization

/-!
# Regularity of the asymmetric chart

The source slope and scale bounds exclude every denominator and every vanishing role scale.
These estimates are independent of the word decoder.
-/

namespace MatrixMortality.AsymmetricSeparatorRealization

variable (ρ q K : ℚ)

/-- Above unit width and below slope `-3/2`, the tail reciprocal is positive. -/
theorem tailScale_pos (width : 27 ≤ ρ) (slope : q < -3 / 2) :
    0 < tailScale ρ q := by
  have parameter_lt : tailParameter q < -2 := by
    dsimp [tailParameter]
    linarith
  have width_factor_pos : 0 < 3 * ρ - 1 := by linarith
  have denominator_lt : tailParameter q * (3 * ρ - 1) < -2 * (3 * ρ - 1) :=
    mul_lt_mul_of_pos_right parameter_lt width_factor_pos
  have denominator_neg : tailParameter q * (3 * ρ - 1) < 0 := by
    nlinarith
  have correction_gt : -2 < 6 * ρ / (tailParameter q * (3 * ρ - 1)) := by
    refine (lt_div_iff_of_neg denominator_neg).2 ?_
    nlinarith
  have correction : ρ * separatorScale ρ q =
      6 * ρ / (tailParameter q * (3 * ρ - 1)) := by
    simp [separatorScale, mul_div_assoc, mul_comm]
  dsimp [tailScale]
  rw [correction]
  linarith

/-- The toggle denominator is strictly negative on the source scale range. -/
theorem toggleDenominator_neg (width : 27 ≤ ρ) (slope : q < -3 / 2)
    (scale : 27 < K) : toggleDenominator ρ q K < 0 := by
  have parameter_lt : tailParameter q < -2 := by
    dsimp [tailParameter]
    linarith
  have coefficient_lt :
      (tailParameter q - 2) * ρ - tailParameter q < 2 - 4 * ρ := by
    nlinarith
  have coefficient_neg : (tailParameter q - 2) * ρ - tailParameter q < 0 := by
    linarith
  have scaled_lt := mul_lt_mul_of_neg_right scale coefficient_neg
  dsimp [toggleDenominator]
  nlinarith

/-- The toggle numerator has the same strict sign as its denominator. -/
theorem toggleNumerator_neg (width : 27 ≤ ρ) (slope : q < -3 / 2) :
    tailParameter q * (27 * ρ ^ 3 - 1) + 18 * ρ ^ 2 + 6 * ρ < 0 := by
  have parameter_lt : tailParameter q < -2 := by
    dsimp [tailParameter]
    linarith
  have width_pos : 0 < ρ := by linarith
  have square_ge : ρ ≤ ρ ^ 2 := by nlinarith
  have cube_ge : ρ ^ 2 ≤ ρ ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_left square_ge width_pos.le]
  have cubic_factor_pos : 0 < 27 * ρ ^ 3 - 1 := by nlinarith
  have product_lt := mul_lt_mul_of_pos_right parameter_lt cubic_factor_pos
  nlinarith

/-- The rescaled toggle cannot create or destroy zero products. -/
theorem toggleScale_pos (width : 27 ≤ ρ) (slope : q < -3 / 2)
    (scale : 27 < K) : 0 < toggleScale ρ q K := by
  have scale_pos : 0 < K := by linarith
  have numerator_neg := mul_neg_of_pos_of_neg scale_pos (toggleNumerator_neg ρ q width slope)
  exact div_pos_of_neg_of_neg numerator_neg (toggleDenominator_neg ρ q K width slope scale)

/-- All rational identities and all physical-return scalings are defined on this locus. -/
structure RegularChart : Prop where
  parameter_ne_zero : tailParameter q ≠ 0
  width_ne_zero : 3 * ρ - 1 ≠ 0
  denominator_ne_zero : toggleDenominator ρ q K ≠ 0
  toggle_ne_zero : toggleScale ρ q K ≠ 0
  tail_ne_zero : tailScale ρ q ≠ 0

/-- The source's strict scale and slope inequalities imply chart regularity. -/
theorem regularChart (width : 27 ≤ ρ) (slope : q < -3 / 2) (scale : 27 < K) :
    RegularChart ρ q K where
  parameter_ne_zero := by
    have parameter_lt : tailParameter q < -2 := by dsimp [tailParameter]; linarith
    linarith
  width_ne_zero := by linarith
  denominator_ne_zero := (toggleDenominator_neg ρ q K width slope scale).ne
  toggle_ne_zero := (toggleScale_pos ρ q K width slope scale).ne'
  tail_ne_zero := (tailScale_pos ρ q width slope).ne'

end MatrixMortality.AsymmetricSeparatorRealization
