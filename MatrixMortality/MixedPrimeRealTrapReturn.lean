import Mathlib.Analysis.SpecificLimits.Basic
import MatrixMortality.MixedPrimeRealTrapExcursion

/-!
# Exact secondary-wall to odd-denominator return cycles

A two-parameter rational family alternates between the active secondary wall and an odd
normalized denominator. One lower predecessor and one middle predecessor close the orbit, all
states satisfy the five-adic guard, and fixed middle depth yields infinitely many distinct cycles
whose wall mantissas converge to `9/10`.
-/

namespace MatrixMortality.MixedPrimeDebt

open PadicValuation
open PeriodicShell
open Filter
open scoped Topology

private local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
private local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Three-power scale of the lower return depth. -/
def wallOddLargeThreePower (depth : ℕ) : ℕ := 3 ^ (depth - 3)

/-- Two-power scale of the lower return depth. -/
def wallOddLargeTwoPower (depth : ℕ) : ℕ := 2 ^ (depth - 1)

/-- Three-power scale of the middle return depth. -/
def wallOddMiddleThreePower (depth : ℕ) : ℕ := 3 ^ (depth - 2)

/-- Two-power scale of the middle return depth. -/
def wallOddMiddleTwoPower (depth : ℕ) : ℕ := 2 ^ (depth - 2)

/-- Odd half-denominator shared by the raw wall and odd-denominator mantissas. -/
def wallOddCycleHalfDenominator (lowerDepth middleDepth : ℕ) : ℕ :=
  25 * wallOddLargeThreePower lowerDepth * wallOddMiddleThreePower middleDepth -
    wallOddLargeTwoPower lowerDepth * wallOddMiddleTwoPower middleDepth

/-- Raw numerator of the secondary-wall mantissa. -/
def wallOddCycleWallNumerator (lowerDepth middleDepth : ℕ) : ℕ :=
  3 * wallOddMiddleThreePower middleDepth *
    (15 * wallOddLargeThreePower lowerDepth + wallOddLargeTwoPower lowerDepth)

/-- Raw numerator of the odd-denominator mantissa. -/
def wallOddCycleOddNumerator (lowerDepth middleDepth : ℕ) : ℕ :=
  3 * wallOddLargeThreePower lowerDepth *
    (5 * wallOddMiddleThreePower middleDepth + 3 * wallOddMiddleTwoPower middleDepth)

/-- Secondary-wall mantissa of the lower-middle return cycle. -/
def wallOddCycleWallMantissa (lowerDepth middleDepth : ℕ) : ℚ :=
  wallOddCycleWallNumerator lowerDepth middleDepth /
    (2 * wallOddCycleHalfDenominator lowerDepth middleDepth)

/-- Odd-denominator mantissa of the lower-middle return cycle. -/
def wallOddCycleOddMantissa (lowerDepth middleDepth : ℕ) : ℚ :=
  wallOddCycleOddNumerator lowerDepth middleDepth /
    wallOddCycleHalfDenominator lowerDepth middleDepth

private def primitiveFractionPair (numerator denominator : ℕ) : ℕ × ℕ :=
  (numerator / Nat.gcd numerator denominator,
    denominator / Nat.gcd numerator denominator)

/-- Reduced numerator and odd half-denominator of the wall mantissa. -/
def wallOddCycleWallPair (lowerDepth middleDepth : ℕ) : ℕ × ℕ :=
  primitiveFractionPair (wallOddCycleWallNumerator lowerDepth middleDepth)
    (wallOddCycleHalfDenominator lowerDepth middleDepth)

/-- Reduced numerator and denominator of the odd-denominator mantissa. -/
def wallOddCycleOddPair (lowerDepth middleDepth : ℕ) : ℕ × ℕ :=
  primitiveFractionPair (wallOddCycleOddNumerator lowerDepth middleDepth)
    (wallOddCycleHalfDenominator lowerDepth middleDepth)

private theorem two_pow_six_add_le_three_pow_four_add (offset : ℕ) :
    2 ^ (6 + offset) ≤ 3 ^ (4 + offset) := by
  induction offset with
  | zero => norm_num
  | succ offset induction =>
      rw [Nat.add_succ, Nat.add_succ, pow_succ, pow_succ]
      exact (Nat.mul_le_mul_right 2 induction).trans
        (Nat.mul_le_mul_left (3 ^ (4 + offset)) (by norm_num))

private theorem wallOdd_largeTwo_le_largeThree
    {depth : ℕ} (depth_lower : 7 ≤ depth) :
    wallOddLargeTwoPower depth ≤ wallOddLargeThreePower depth := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le depth_lower
  simp only [wallOddLargeTwoPower, wallOddLargeThreePower]
  have left_exponent : 7 + offset - 1 = 6 + offset := by omega
  have right_exponent : 7 + offset - 3 = 4 + offset := by omega
  rw [left_exponent, right_exponent]
  exact two_pow_six_add_le_three_pow_four_add offset

private theorem wallOdd_middleTwo_le_middleThree (depth : ℕ) :
    wallOddMiddleTwoPower depth ≤ wallOddMiddleThreePower depth := by
  simp only [wallOddMiddleTwoPower, wallOddMiddleThreePower]
  exact Nat.pow_le_pow_left (by norm_num) _

private theorem wallOdd_fiveMiddleThree_lt_twentySevenMiddleTwo
    {depth : ℕ} (depth_lower : 2 ≤ depth) (depth_upper : depth ≤ 6) :
    5 * wallOddMiddleThreePower depth < 27 * wallOddMiddleTwoPower depth := by
  interval_cases depth <;> norm_num [wallOddMiddleThreePower, wallOddMiddleTwoPower]

private theorem wallOdd_halfDenominator_data
    {lowerDepth middleDepth : ℕ} (lowerDepth_lower : 7 ≤ lowerDepth) :
    wallOddLargeTwoPower lowerDepth * wallOddMiddleTwoPower middleDepth <
        25 * wallOddLargeThreePower lowerDepth * wallOddMiddleThreePower middleDepth ∧
      wallOddCycleHalfDenominator lowerDepth middleDepth +
          wallOddLargeTwoPower lowerDepth * wallOddMiddleTwoPower middleDepth =
        25 * wallOddLargeThreePower lowerDepth * wallOddMiddleThreePower middleDepth := by
  have q_le_p := wallOdd_largeTwo_le_largeThree lowerDepth_lower
  have e_le_r := wallOdd_middleTwo_le_middleThree middleDepth
  have product_le :
      wallOddLargeTwoPower lowerDepth * wallOddMiddleTwoPower middleDepth ≤
        wallOddLargeThreePower lowerDepth * wallOddMiddleThreePower middleDepth :=
    Nat.mul_le_mul q_le_p e_le_r
  have product_positive :
      0 < wallOddLargeThreePower lowerDepth * wallOddMiddleThreePower middleDepth := by
    simp [wallOddLargeThreePower, wallOddMiddleThreePower]
  have strict :
      wallOddLargeTwoPower lowerDepth * wallOddMiddleTwoPower middleDepth <
        25 * wallOddLargeThreePower lowerDepth * wallOddMiddleThreePower middleDepth := by
    nlinarith
  exact ⟨strict, Nat.sub_add_cancel strict.le⟩

private theorem wallOdd_halfDenominator_pos
    {lowerDepth middleDepth : ℕ} (lowerDepth_lower : 7 ≤ lowerDepth) :
    0 < wallOddCycleHalfDenominator lowerDepth middleDepth := by
  have strict := (wallOdd_halfDenominator_data
    (middleDepth := middleDepth) lowerDepth_lower).1
  exact Nat.sub_pos_of_lt strict

private theorem primitiveFractionPair_data
    {numerator denominator : ℕ} (denominator_pos : 0 < denominator) :
    let pair := primitiveFractionPair numerator denominator
    pair.1.Coprime pair.2 ∧
      numerator = pair.1 * Nat.gcd numerator denominator ∧
      denominator = pair.2 * Nat.gcd numerator denominator ∧
      (numerator : ℚ) / denominator = (pair.1 : ℚ) / pair.2 := by
  let common := Nat.gcd numerator denominator
  have common_pos : 0 < common := Nat.gcd_pos_of_pos_right numerator denominator_pos
  have numerator_eq : numerator = numerator / common * common :=
    (Nat.div_mul_cancel (Nat.gcd_dvd_left numerator denominator)).symm
  have denominator_eq : denominator = denominator / common * common :=
    (Nat.div_mul_cancel (Nat.gcd_dvd_right numerator denominator)).symm
  have denominator_quotient_pos : 0 < denominator / common :=
    Nat.div_pos (Nat.gcd_le_right numerator denominator_pos) common_pos
  refine ⟨?_, numerator_eq, denominator_eq, ?_⟩
  · simpa only [primitiveFractionPair] using
      Nat.coprime_div_gcd_div_gcd common_pos
  · simp only [primitiveFractionPair]
    have denominator_ne_rat : (denominator : ℚ) ≠ 0 := by
      exact_mod_cast denominator_pos.ne'
    have quotient_ne_rat : ((denominator / common : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast denominator_quotient_pos.ne'
    apply (div_eq_div_iff denominator_ne_rat quotient_ne_rat).2
    exact_mod_cast (show numerator * (denominator / common) =
      numerator / common * denominator by
        calc
          numerator * (denominator / common) =
              (numerator / common * common) * (denominator / common) := by
            rw [← numerator_eq]
          _ = numerator / common * (denominator / common * common) := by ring
          _ = numerator / common * denominator :=
            congrArg (fun value => numerator / common * value) denominator_eq.symm)

private theorem wallOdd_wall_bounds_nat
    {lowerDepth middleDepth : ℕ} (lowerDepth_lower : 7 ≤ lowerDepth) :
    18 * wallOddCycleHalfDenominator lowerDepth middleDepth <
        10 * wallOddCycleWallNumerator lowerDepth middleDepth ∧
      wallOddCycleWallNumerator lowerDepth middleDepth ≤
        2 * wallOddCycleHalfDenominator lowerDepth middleDepth := by
  have q_le_p := wallOdd_largeTwo_le_largeThree lowerDepth_lower
  have e_le_r := wallOdd_middleTwo_le_middleThree middleDepth
  have denominator_eq := (wallOdd_halfDenominator_data
    (middleDepth := middleDepth) lowerDepth_lower).2
  have qr_le_pr :
      wallOddLargeTwoPower lowerDepth * wallOddMiddleThreePower middleDepth ≤
        wallOddLargeThreePower lowerDepth * wallOddMiddleThreePower middleDepth :=
    Nat.mul_le_mul_right _ q_le_p
  have qe_le_pr :
      wallOddLargeTwoPower lowerDepth * wallOddMiddleTwoPower middleDepth ≤
        wallOddLargeThreePower lowerDepth * wallOddMiddleThreePower middleDepth :=
    Nat.mul_le_mul q_le_p e_le_r
  have three_qr_two_qe_le :
      3 * (wallOddLargeTwoPower lowerDepth * wallOddMiddleThreePower middleDepth) +
          2 * (wallOddLargeTwoPower lowerDepth * wallOddMiddleTwoPower middleDepth) ≤
        5 * (wallOddLargeThreePower lowerDepth * wallOddMiddleThreePower middleDepth) := by
    omega
  simp only [wallOddCycleHalfDenominator, wallOddCycleWallNumerator] at denominator_eq ⊢
  constructor
  · have q_pos : 0 < wallOddLargeTwoPower lowerDepth := by simp [wallOddLargeTwoPower]
    have r_pos : 0 < wallOddMiddleThreePower middleDepth := by simp [wallOddMiddleThreePower]
    have e_pos : 0 < wallOddMiddleTwoPower middleDepth := by simp [wallOddMiddleTwoPower]
    nlinarith
  · ring_nf at three_qr_two_qe_le ⊢
    omega

private theorem wallOdd_odd_bounds_nat
    {lowerDepth middleDepth : ℕ} (lowerDepth_lower : 7 ≤ lowerDepth)
    (middleDepth_lower : 2 ≤ middleDepth) (middleDepth_upper : middleDepth ≤ 6) :
    2 * wallOddCycleHalfDenominator lowerDepth middleDepth <
        3 * wallOddCycleOddNumerator lowerDepth middleDepth ∧
      wallOddCycleOddNumerator lowerDepth middleDepth ≤
        wallOddCycleHalfDenominator lowerDepth middleDepth := by
  have q_le_p := wallOdd_largeTwo_le_largeThree lowerDepth_lower
  have e_le_r := wallOdd_middleTwo_le_middleThree middleDepth
  have five_r_lt :=
    wallOdd_fiveMiddleThree_lt_twentySevenMiddleTwo middleDepth_lower middleDepth_upper
  have pe_le_pr :
      wallOddLargeThreePower lowerDepth * wallOddMiddleTwoPower middleDepth ≤
        wallOddLargeThreePower lowerDepth * wallOddMiddleThreePower middleDepth :=
    Nat.mul_le_mul_left _ e_le_r
  have qe_le_pr :
      wallOddLargeTwoPower lowerDepth * wallOddMiddleTwoPower middleDepth ≤
        wallOddLargeThreePower lowerDepth * wallOddMiddleThreePower middleDepth :=
    Nat.mul_le_mul q_le_p e_le_r
  have upper_aux :
      9 * (wallOddLargeThreePower lowerDepth * wallOddMiddleTwoPower middleDepth) +
          wallOddLargeTwoPower lowerDepth * wallOddMiddleTwoPower middleDepth ≤
        10 * (wallOddLargeThreePower lowerDepth * wallOddMiddleThreePower middleDepth) := by
    omega
  have lower_aux :
      5 * (wallOddLargeThreePower lowerDepth * wallOddMiddleThreePower middleDepth) <
        27 * (wallOddLargeThreePower lowerDepth * wallOddMiddleTwoPower middleDepth) := by
    have p_pos : 0 < wallOddLargeThreePower lowerDepth := by simp [wallOddLargeThreePower]
    nlinarith
  have denominator_eq := (wallOdd_halfDenominator_data
    (middleDepth := middleDepth) lowerDepth_lower).2
  simp only [wallOddCycleHalfDenominator, wallOddCycleOddNumerator] at denominator_eq ⊢
  constructor
  · ring_nf at lower_aux ⊢
    omega
  · ring_nf at upper_aux ⊢
    omega

/-- The wall member lies in the active lower-predecessor mantissa interval. -/
theorem wallOddCycleWallMantissa_normalized
    {lowerDepth middleDepth : ℕ} (lowerDepth_lower : 7 ≤ lowerDepth) :
    9 / 10 < wallOddCycleWallMantissa lowerDepth middleDepth ∧
      wallOddCycleWallMantissa lowerDepth middleDepth ≤ 1 := by
  have denominator_pos := wallOdd_halfDenominator_pos
    (middleDepth := middleDepth) lowerDepth_lower
  have bounds := wallOdd_wall_bounds_nat
    (middleDepth := middleDepth) lowerDepth_lower
  have denominator_pos_rat :
      (0 : ℚ) < 2 * wallOddCycleHalfDenominator lowerDepth middleDepth := by
    exact_mod_cast Nat.mul_pos (by norm_num : 0 < 2) denominator_pos
  constructor
  · rw [wallOddCycleWallMantissa, lt_div_iff₀ denominator_pos_rat]
    have lower_rat :
        ((18 * wallOddCycleHalfDenominator lowerDepth middleDepth : ℕ) : ℚ) <
          10 * wallOddCycleWallNumerator lowerDepth middleDepth := by
      exact_mod_cast bounds.1
    norm_num at lower_rat ⊢
    nlinarith
  · rw [wallOddCycleWallMantissa, div_le_one denominator_pos_rat]
    exact_mod_cast bounds.2

/-- The odd-denominator member is a normalized real-trap mantissa. -/
theorem wallOddCycleOddMantissa_normalized
    {lowerDepth middleDepth : ℕ} (lowerDepth_lower : 7 ≤ lowerDepth)
    (middleDepth_lower : 2 ≤ middleDepth) (middleDepth_upper : middleDepth ≤ 6) :
    2 / 3 < wallOddCycleOddMantissa lowerDepth middleDepth ∧
      wallOddCycleOddMantissa lowerDepth middleDepth ≤ 1 := by
  have denominator_pos := wallOdd_halfDenominator_pos
    (middleDepth := middleDepth) lowerDepth_lower
  have bounds := wallOdd_odd_bounds_nat lowerDepth_lower middleDepth_lower middleDepth_upper
  have denominator_pos_rat :
      (0 : ℚ) < wallOddCycleHalfDenominator lowerDepth middleDepth := by
    exact_mod_cast denominator_pos
  constructor
  · rw [wallOddCycleOddMantissa, lt_div_iff₀ denominator_pos_rat]
    have lower_rat :
        ((2 * wallOddCycleHalfDenominator lowerDepth middleDepth : ℕ) : ℚ) <
          3 * wallOddCycleOddNumerator lowerDepth middleDepth := by
      exact_mod_cast bounds.1
    norm_num at lower_rat ⊢
    nlinarith
  · rw [wallOddCycleOddMantissa, div_le_one denominator_pos_rat]
    exact_mod_cast bounds.2

/-- Among depths three through six, both displayed mantissas are normalized exactly at lower
depth six and middle depths four through six. -/
theorem wallOddCycle_smallDepth_normalized_iff
    {lowerDepth middleDepth : ℕ} (lowerDepth_lower : 3 ≤ lowerDepth)
    (lowerDepth_upper : lowerDepth ≤ 6) (middleDepth_lower : 2 ≤ middleDepth)
    (middleDepth_upper : middleDepth ≤ 6) :
    ((9 / 10 < wallOddCycleWallMantissa lowerDepth middleDepth ∧
        wallOddCycleWallMantissa lowerDepth middleDepth ≤ 1) ∧
      (2 / 3 < wallOddCycleOddMantissa lowerDepth middleDepth ∧
        wallOddCycleOddMantissa lowerDepth middleDepth ≤ 1)) ↔
      lowerDepth = 6 ∧ 4 ≤ middleDepth := by
  interval_cases lowerDepth <;> interval_cases middleDepth <;>
    norm_num [wallOddCycleWallMantissa, wallOddCycleOddMantissa,
      wallOddCycleWallNumerator, wallOddCycleOddNumerator,
      wallOddCycleHalfDenominator, wallOddLargeThreePower,
      wallOddLargeTwoPower, wallOddMiddleThreePower, wallOddMiddleTwoPower]

/-- The odd-denominator member is the exact normalized lower predecessor of the wall member. -/
theorem wallOddCycleOddMantissa_eq_lower
    {lowerDepth middleDepth : ℕ} (lowerDepth_lower : 7 ≤ lowerDepth) :
    wallOddCycleOddMantissa lowerDepth middleDepth =
      (wallOddLargeThreePower lowerDepth : ℚ) / wallOddLargeTwoPower lowerDepth *
        (10 * wallOddCycleWallMantissa lowerDepth middleDepth - 9) := by
  have denominator_ne : (wallOddCycleHalfDenominator lowerDepth middleDepth : ℚ) ≠ 0 := by
    exact_mod_cast (wallOdd_halfDenominator_pos
      (middleDepth := middleDepth) lowerDepth_lower).ne'
  have q_ne : (wallOddLargeTwoPower lowerDepth : ℚ) ≠ 0 := by simp [wallOddLargeTwoPower]
  have denominator_eq_nat := (wallOdd_halfDenominator_data
    (middleDepth := middleDepth) lowerDepth_lower).2
  have denominator_eq_rat :
      (wallOddCycleHalfDenominator lowerDepth middleDepth : ℚ) +
          wallOddLargeTwoPower lowerDepth * wallOddMiddleTwoPower middleDepth =
        25 * wallOddLargeThreePower lowerDepth * wallOddMiddleThreePower middleDepth := by
    exact_mod_cast denominator_eq_nat
  rw [wallOddCycleWallMantissa, wallOddCycleOddMantissa]
  field_simp
  simp only [wallOddCycleWallNumerator, wallOddCycleOddNumerator]
  push_cast
  nlinarith [denominator_eq_rat]

/-- The wall member is the exact normalized middle predecessor of the odd-denominator member. -/
theorem wallOddCycleWallMantissa_eq_middle
    {lowerDepth middleDepth : ℕ} (lowerDepth_lower : 7 ≤ lowerDepth) :
    wallOddCycleWallMantissa lowerDepth middleDepth =
      (wallOddMiddleThreePower middleDepth : ℚ) / (2 * wallOddMiddleTwoPower middleDepth) *
        (5 * wallOddCycleOddMantissa lowerDepth middleDepth - 3) := by
  have denominator_ne : (wallOddCycleHalfDenominator lowerDepth middleDepth : ℚ) ≠ 0 := by
    exact_mod_cast (wallOdd_halfDenominator_pos
      (middleDepth := middleDepth) lowerDepth_lower).ne'
  have e_ne : (wallOddMiddleTwoPower middleDepth : ℚ) ≠ 0 := by
    simp [wallOddMiddleTwoPower]
  have denominator_eq_nat := (wallOdd_halfDenominator_data
    (middleDepth := middleDepth) lowerDepth_lower).2
  have denominator_eq_rat :
      (wallOddCycleHalfDenominator lowerDepth middleDepth : ℚ) +
          wallOddLargeTwoPower lowerDepth * wallOddMiddleTwoPower middleDepth =
        25 * wallOddLargeThreePower lowerDepth * wallOddMiddleThreePower middleDepth := by
    exact_mod_cast denominator_eq_nat
  rw [wallOddCycleWallMantissa, wallOddCycleOddMantissa]
  field_simp
  simp only [wallOddCycleWallNumerator, wallOddCycleOddNumerator]
  push_cast
  nlinarith [denominator_eq_rat]

private theorem wallOdd_largeThree_odd (depth : ℕ) : Odd (wallOddLargeThreePower depth) := by
  exact (by norm_num : Odd 3).pow

private theorem wallOdd_middleThree_odd (depth : ℕ) : Odd (wallOddMiddleThreePower depth) := by
  exact (by norm_num : Odd 3).pow

private theorem wallOdd_largeTwo_even
    {depth : ℕ} (depth_lower : 2 ≤ depth) : Even (wallOddLargeTwoPower depth) := by
  unfold wallOddLargeTwoPower
  exact even_two.pow_of_ne_zero (by omega)

/-- The shared raw half-denominator is odd. -/
theorem wallOddCycleHalfDenominator_odd
    {lowerDepth middleDepth : ℕ} (lowerDepth_lower : 7 ≤ lowerDepth) :
    Odd (wallOddCycleHalfDenominator lowerDepth middleDepth) := by
  have subtraction_le := (wallOdd_halfDenominator_data
    (middleDepth := middleDepth) lowerDepth_lower).1.le
  have left_odd :
      Odd (25 * wallOddLargeThreePower lowerDepth * wallOddMiddleThreePower middleDepth) :=
    ((by norm_num : Odd 25).mul (wallOdd_largeThree_odd lowerDepth)).mul
      (wallOdd_middleThree_odd middleDepth)
  have right_even :
      Even (wallOddLargeTwoPower lowerDepth * wallOddMiddleTwoPower middleDepth) :=
    (wallOdd_largeTwo_even (by omega : 2 ≤ lowerDepth)).mul_right _
  exact Nat.Odd.sub_even subtraction_le left_odd right_even

/-- The raw secondary-wall numerator is odd. -/
theorem wallOddCycleWallNumerator_odd
    {lowerDepth middleDepth : ℕ} (lowerDepth_lower : 7 ≤ lowerDepth) :
    Odd (wallOddCycleWallNumerator lowerDepth middleDepth) := by
  have q_even : Even (wallOddLargeTwoPower lowerDepth) :=
    wallOdd_largeTwo_even (by omega)
  have inside_odd :
      Odd (15 * wallOddLargeThreePower lowerDepth + wallOddLargeTwoPower lowerDepth) :=
    ((by norm_num : Odd 15).mul (wallOdd_largeThree_odd lowerDepth)).add_even q_even
  exact ((by norm_num : Odd 3).mul (wallOdd_middleThree_odd middleDepth)).mul inside_odd

private theorem wallOddCycle_raw_fiveCoprime
    {lowerDepth middleDepth : ℕ} (lowerDepth_lower : 7 ≤ lowerDepth) :
    Nat.Coprime 5 (wallOddCycleWallNumerator lowerDepth middleDepth) ∧
      Nat.Coprime 5 (wallOddCycleOddNumerator lowerDepth middleDepth) ∧
      Nat.Coprime 5 (wallOddCycleHalfDenominator lowerDepth middleDepth) := by
  have five_three : Nat.Coprime 5 3 := by norm_num
  have five_two : Nat.Coprime 5 2 := by norm_num
  have five_p : Nat.Coprime 5 (wallOddLargeThreePower lowerDepth) :=
    five_three.pow_right _
  have five_q : Nat.Coprime 5 (wallOddLargeTwoPower lowerDepth) :=
    five_two.pow_right _
  have five_r : Nat.Coprime 5 (wallOddMiddleThreePower middleDepth) :=
    five_three.pow_right _
  have five_e : Nat.Coprime 5 (wallOddMiddleTwoPower middleDepth) :=
    five_two.pow_right _
  have five_qe : Nat.Coprime 5
      (wallOddLargeTwoPower lowerDepth * wallOddMiddleTwoPower middleDepth) :=
    five_q.mul_right five_e
  have denominator_eq := (wallOdd_halfDenominator_data
    (middleDepth := middleDepth) lowerDepth_lower).2
  have five_denominator : Nat.Coprime 5
      (wallOddCycleHalfDenominator lowerDepth middleDepth) := by
    apply Nat.prime_five.coprime_iff_not_dvd.mpr
    intro five_dvd_denominator
    have five_dvd_total : 5 ∣
        wallOddCycleHalfDenominator lowerDepth middleDepth +
          wallOddLargeTwoPower lowerDepth * wallOddMiddleTwoPower middleDepth := by
      rw [denominator_eq]
      simpa only [mul_assoc] using
        dvd_mul_of_dvd_left (by norm_num : 5 ∣ 25)
          (wallOddLargeThreePower lowerDepth * wallOddMiddleThreePower middleDepth)
    have five_dvd_qe :
        5 ∣ wallOddLargeTwoPower lowerDepth * wallOddMiddleTwoPower middleDepth :=
      (Nat.dvd_add_iff_right five_dvd_denominator).mpr five_dvd_total
    exact (Nat.prime_five.coprime_iff_not_dvd.mp five_qe) five_dvd_qe
  have five_wall_inside : Nat.Coprime 5
      (15 * wallOddLargeThreePower lowerDepth + wallOddLargeTwoPower lowerDepth) := by
    apply Nat.prime_five.coprime_iff_not_dvd.mpr
    intro five_dvd_inside
    have five_dvd_first : 5 ∣ 15 * wallOddLargeThreePower lowerDepth :=
      dvd_mul_of_dvd_left (by norm_num : 5 ∣ 15) _
    have five_dvd_q : 5 ∣ wallOddLargeTwoPower lowerDepth :=
      (Nat.dvd_add_iff_right five_dvd_first).mpr five_dvd_inside
    exact (Nat.prime_five.coprime_iff_not_dvd.mp five_q) five_dvd_q
  have five_wall : Nat.Coprime 5 (wallOddCycleWallNumerator lowerDepth middleDepth) := by
    simpa only [wallOddCycleWallNumerator] using
      (five_three.mul_right five_r).mul_right five_wall_inside
  have five_odd_inside : Nat.Coprime 5
      (5 * wallOddMiddleThreePower middleDepth + 3 * wallOddMiddleTwoPower middleDepth) := by
    apply Nat.prime_five.coprime_iff_not_dvd.mpr
    intro five_dvd_inside
    have five_dvd_first : 5 ∣ 5 * wallOddMiddleThreePower middleDepth :=
      dvd_mul_right 5 _
    have five_three_e : Nat.Coprime 5 (3 * wallOddMiddleTwoPower middleDepth) :=
      five_three.mul_right five_e
    have five_dvd_three_e : 5 ∣ 3 * wallOddMiddleTwoPower middleDepth :=
      (Nat.dvd_add_iff_right five_dvd_first).mpr five_dvd_inside
    exact (Nat.prime_five.coprime_iff_not_dvd.mp five_three_e) five_dvd_three_e
  have five_odd : Nat.Coprime 5 (wallOddCycleOddNumerator lowerDepth middleDepth) := by
    simpa only [wallOddCycleOddNumerator] using
      (five_three.mul_right five_p).mul_right five_odd_inside
  exact ⟨five_wall, five_odd, five_denominator⟩

private theorem natCast_fiveUnit
    {value : ℕ} (five_coprime : Nat.Coprime 5 value) :
    IsUnit 5 (value : ℚ) := by
  have value_not_dvd_nat : ¬5 ∣ value :=
    Nat.prime_five.coprime_iff_not_dvd.mp five_coprime
  have value_not_dvd_int : ¬(5 : ℤ) ∣ (value : ℤ) := by
    exact_mod_cast value_not_dvd_nat
  simpa using intCast_isUnit_of_not_dvd (prime := 5) value_not_dvd_int

/-- The secondary-wall mantissa is a five-adic unit. -/
theorem wallOddCycleWallMantissa_fiveUnit
    {lowerDepth middleDepth : ℕ} (lowerDepth_lower : 7 ≤ lowerDepth) :
    IsUnit 5 (wallOddCycleWallMantissa lowerDepth middleDepth) := by
  obtain ⟨five_wall, _, five_denominator⟩ :=
    wallOddCycle_raw_fiveCoprime (middleDepth := middleDepth) lowerDepth_lower
  have two_unit : IsUnit 5 (2 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  simpa [wallOddCycleWallMantissa] using
    div_hasValue (natCast_fiveUnit five_wall)
      (mul_hasValue two_unit (natCast_fiveUnit five_denominator))

/-- The odd-denominator mantissa is a five-adic unit. -/
theorem wallOddCycleOddMantissa_fiveUnit
    {lowerDepth middleDepth : ℕ} (lowerDepth_lower : 7 ≤ lowerDepth) :
    IsUnit 5 (wallOddCycleOddMantissa lowerDepth middleDepth) := by
  obtain ⟨_, five_odd, five_denominator⟩ :=
    wallOddCycle_raw_fiveCoprime (middleDepth := middleDepth) lowerDepth_lower
  exact div_hasValue (natCast_fiveUnit five_odd) (natCast_fiveUnit five_denominator)

/-- The reduced wall coordinate satisfies every secondary-wall invariant. -/
theorem wallOddCycleWallPair_isLowerWallMantissa
    {lowerDepth middleDepth : ℕ} (lowerDepth_lower : 7 ≤ lowerDepth) :
    IsLowerWallMantissa (wallOddCycleWallPair lowerDepth middleDepth).1
      (wallOddCycleWallPair lowerDepth middleDepth).2 := by
  let numerator := wallOddCycleWallNumerator lowerDepth middleDepth
  let denominator := wallOddCycleHalfDenominator lowerDepth middleDepth
  let pair := wallOddCycleWallPair lowerDepth middleDepth
  let common := Nat.gcd numerator denominator
  have denominator_pos : 0 < denominator :=
    wallOdd_halfDenominator_pos (middleDepth := middleDepth) lowerDepth_lower
  have numerator_pos : 0 < numerator := by
    simp [numerator, wallOddCycleWallNumerator, wallOddMiddleThreePower,
      wallOddLargeThreePower, wallOddLargeTwoPower]
  have pair_data := primitiveFractionPair_data
    (numerator := numerator) (denominator := denominator) denominator_pos
  have pair_data' :
      pair.1.Coprime pair.2 ∧
        numerator = pair.1 * common ∧
        denominator = pair.2 * common ∧
        (numerator : ℚ) / denominator = (pair.1 : ℚ) / pair.2 := by
    simpa only [pair, common, wallOddCycleWallPair, numerator, denominator] using pair_data
  obtain ⟨pair_coprime, numerator_eq, denominator_eq, _⟩ := pair_data'
  have common_pos : 0 < common := Nat.gcd_pos_of_pos_right numerator denominator_pos
  have raw_odd_numerator := wallOddCycleWallNumerator_odd
    (middleDepth := middleDepth) lowerDepth_lower
  have raw_odd_denominator := wallOddCycleHalfDenominator_odd
    (middleDepth := middleDepth) lowerDepth_lower
  have pair_odd_numerator : Odd pair.1 :=
    Odd.of_dvd_nat raw_odd_numerator ⟨common, numerator_eq⟩
  have pair_odd_denominator : Odd pair.2 :=
    Odd.of_dvd_nat raw_odd_denominator ⟨common, denominator_eq⟩
  have reduced : pair.1.Coprime (2 * pair.2) :=
    pair_odd_numerator.coprime_two_right.mul_right pair_coprime
  obtain ⟨five_raw_numerator, _, five_raw_denominator⟩ :=
    wallOddCycle_raw_fiveCoprime (middleDepth := middleDepth) lowerDepth_lower
  have five_numerator : Nat.Coprime 5 pair.1 :=
    five_raw_numerator.of_dvd_right ⟨common, numerator_eq⟩
  have five_denominator : Nat.Coprime 5 pair.2 :=
    five_raw_denominator.of_dvd_right ⟨common, denominator_eq⟩
  have raw_bounds := wallOdd_wall_bounds_nat
    (middleDepth := middleDepth) lowerDepth_lower
  have lower : 18 * pair.2 < 10 * pair.1 := by
    apply (Nat.mul_lt_mul_right common_pos).mp
    calc
      (18 * pair.2) * common = 18 * denominator := by rw [denominator_eq]; ring
      _ < 10 * numerator := raw_bounds.1
      _ = (10 * pair.1) * common := by rw [numerator_eq]; ring
  have upper : pair.1 ≤ 2 * pair.2 := by
    apply Nat.le_of_mul_le_mul_right (c := common) _ common_pos
    calc
      pair.1 * common = numerator := numerator_eq.symm
      _ ≤ 2 * denominator := raw_bounds.2
      _ = (2 * pair.2) * common := by rw [denominator_eq]; ring
  exact ⟨reduced, pair_odd_denominator, five_numerator, five_denominator, lower, upper⟩

/-- The raw wall mantissa equals the value of its reduced secondary-wall pair. -/
theorem wallOddCycleWallMantissa_eq_pairValue
    {lowerDepth middleDepth : ℕ} (lowerDepth_lower : 7 ≤ lowerDepth) :
    wallOddCycleWallMantissa lowerDepth middleDepth =
      lowerWallValue (wallOddCycleWallPair lowerDepth middleDepth) := by
  let numerator := wallOddCycleWallNumerator lowerDepth middleDepth
  let denominator := wallOddCycleHalfDenominator lowerDepth middleDepth
  have denominator_pos : 0 < denominator :=
    wallOdd_halfDenominator_pos (middleDepth := middleDepth) lowerDepth_lower
  have pair_data := primitiveFractionPair_data
    (numerator := numerator) (denominator := denominator) denominator_pos
  have value_eq := pair_data.2.2.2
  change (numerator : ℚ) / (2 * denominator) =
    ((primitiveFractionPair numerator denominator).1 : ℚ) /
      (2 * (primitiveFractionPair numerator denominator).2)
  calc
    (numerator : ℚ) / (2 * denominator) = ((numerator : ℚ) / denominator) / 2 := by
      ring
    _ = (((primitiveFractionPair numerator denominator).1 : ℚ) /
        (primitiveFractionPair numerator denominator).2) / 2 := by rw [value_eq]
    _ = ((primitiveFractionPair numerator denominator).1 : ℚ) /
        (2 * (primitiveFractionPair numerator denominator).2) := by ring

/-- The reduced odd member has an odd denominator, is five-adically primitive, and remains in
the normalized mantissa interval. -/
theorem wallOddCycleOddPair_data
    {lowerDepth middleDepth : ℕ} (lowerDepth_lower : 7 ≤ lowerDepth)
    (middleDepth_lower : 2 ≤ middleDepth) (middleDepth_upper : middleDepth ≤ 6) :
    let pair := wallOddCycleOddPair lowerDepth middleDepth
    pair.1.Coprime pair.2 ∧ Odd pair.2 ∧
      Nat.Coprime 5 pair.1 ∧ Nat.Coprime 5 pair.2 ∧
      2 * pair.2 < 3 * pair.1 ∧ pair.1 ≤ pair.2 ∧
      wallOddCycleOddMantissa lowerDepth middleDepth = (pair.1 : ℚ) / pair.2 := by
  let numerator := wallOddCycleOddNumerator lowerDepth middleDepth
  let denominator := wallOddCycleHalfDenominator lowerDepth middleDepth
  let pair := wallOddCycleOddPair lowerDepth middleDepth
  let common := Nat.gcd numerator denominator
  have denominator_pos : 0 < denominator :=
    wallOdd_halfDenominator_pos (middleDepth := middleDepth) lowerDepth_lower
  have pair_data := primitiveFractionPair_data
    (numerator := numerator) (denominator := denominator) denominator_pos
  have pair_data' :
      pair.1.Coprime pair.2 ∧
        numerator = pair.1 * common ∧
        denominator = pair.2 * common ∧
        (numerator : ℚ) / denominator = (pair.1 : ℚ) / pair.2 := by
    simpa only [pair, common, wallOddCycleOddPair, numerator, denominator] using pair_data
  obtain ⟨pair_coprime, numerator_eq, denominator_eq, value_eq⟩ := pair_data'
  have common_pos : 0 < common := Nat.gcd_pos_of_pos_right numerator denominator_pos
  have raw_odd_denominator := wallOddCycleHalfDenominator_odd
    (middleDepth := middleDepth) lowerDepth_lower
  have pair_odd_denominator : Odd pair.2 :=
    Odd.of_dvd_nat raw_odd_denominator ⟨common, denominator_eq⟩
  obtain ⟨_, five_raw_numerator, five_raw_denominator⟩ :=
    wallOddCycle_raw_fiveCoprime (middleDepth := middleDepth) lowerDepth_lower
  have five_numerator : Nat.Coprime 5 pair.1 :=
    five_raw_numerator.of_dvd_right ⟨common, numerator_eq⟩
  have five_denominator : Nat.Coprime 5 pair.2 :=
    five_raw_denominator.of_dvd_right ⟨common, denominator_eq⟩
  have raw_bounds := wallOdd_odd_bounds_nat
    lowerDepth_lower middleDepth_lower middleDepth_upper
  have lower : 2 * pair.2 < 3 * pair.1 := by
    apply (Nat.mul_lt_mul_right common_pos).mp
    calc
      (2 * pair.2) * common = 2 * denominator := by rw [denominator_eq]; ring
      _ < 3 * numerator := raw_bounds.1
      _ = (3 * pair.1) * common := by rw [numerator_eq]; ring
  have upper : pair.1 ≤ pair.2 := by
    apply Nat.le_of_mul_le_mul_right (c := common) _ common_pos
    calc
      pair.1 * common = numerator := numerator_eq.symm
      _ ≤ denominator := raw_bounds.2
      _ = pair.2 * common := denominator_eq
  have raw_value_eq :
      wallOddCycleOddMantissa lowerDepth middleDepth = (pair.1 : ℚ) / pair.2 := by
    simpa only [wallOddCycleOddMantissa, numerator, denominator] using value_eq
  exact ⟨pair_coprime, pair_odd_denominator, five_numerator, five_denominator,
    lower, upper, raw_value_eq⟩

/-- The wall mantissa has rational two-adic value exactly minus one before or after reduction. -/
theorem wallOddCycleWallMantissa_twoValue
    {lowerDepth middleDepth : ℕ} (lowerDepth_lower : 7 ≤ lowerDepth) :
    HasValue 2 (wallOddCycleWallMantissa lowerDepth middleDepth) (-1) := by
  have numerator_odd := wallOddCycleWallNumerator_odd
    (middleDepth := middleDepth) lowerDepth_lower
  have numerator_ne : wallOddCycleWallNumerator lowerDepth middleDepth ≠ 0 := by
    intro numerator_zero
    rw [numerator_zero] at numerator_odd
    simp at numerator_odd
  have numerator_unit :
      IsUnit 2 (wallOddCycleWallNumerator lowerDepth middleDepth : ℚ) := by
    refine ⟨by exact_mod_cast numerator_ne, ?_⟩
    rw [padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd numerator_odd.not_two_dvd_nat]
    norm_num
  have half_odd := wallOddCycleHalfDenominator_odd
    (middleDepth := middleDepth) lowerDepth_lower
  have half_ne : wallOddCycleHalfDenominator lowerDepth middleDepth ≠ 0 := by
    intro half_zero
    rw [half_zero] at half_odd
    simp at half_odd
  have half_unit :
      IsUnit 2 (wallOddCycleHalfDenominator lowerDepth middleDepth : ℚ) := by
    refine ⟨by exact_mod_cast half_ne, ?_⟩
    rw [padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd half_odd.not_two_dvd_nat]
    norm_num
  have two_value : HasValue 2 (2 : ℚ) 1 := by
    simpa using (primePower_hasValue (prime := 2) 1)
  simpa [wallOddCycleWallMantissa] using
    div_hasValue numerator_unit (mul_hasValue two_value half_unit)

private theorem wallOdd_largeThree_succ
    {depth : ℕ} (depth_lower : 3 ≤ depth) :
    wallOddLargeThreePower (depth + 1) = 3 * wallOddLargeThreePower depth := by
  simp only [wallOddLargeThreePower]
  rw [show depth + 1 - 3 = (depth - 3) + 1 by omega, pow_succ]
  ring

private theorem wallOdd_largeTwo_succ
    {depth : ℕ} (depth_lower : 1 ≤ depth) :
    wallOddLargeTwoPower (depth + 1) = 2 * wallOddLargeTwoPower depth := by
  simp only [wallOddLargeTwoPower]
  rw [show depth + 1 - 1 = (depth - 1) + 1 by omega, pow_succ]
  ring

/-- At fixed middle depth, increasing the lower depth strictly decreases the wall mantissa. -/
theorem wallOddCycleWallMantissa_succ_lt
    {lowerDepth middleDepth : ℕ} (lowerDepth_lower : 7 ≤ lowerDepth) :
    wallOddCycleWallMantissa (lowerDepth + 1) middleDepth <
      wallOddCycleWallMantissa lowerDepth middleDepth := by
  have p_succ := wallOdd_largeThree_succ (by omega : 3 ≤ lowerDepth)
  have q_succ := wallOdd_largeTwo_succ (by omega : 1 ≤ lowerDepth)
  have denominator_pos := wallOdd_halfDenominator_pos
    (middleDepth := middleDepth) lowerDepth_lower
  have next_denominator_pos := wallOdd_halfDenominator_pos
    (middleDepth := middleDepth) (by omega : 7 ≤ lowerDepth + 1)
  have denominator_eq := (wallOdd_halfDenominator_data
    (middleDepth := middleDepth) lowerDepth_lower).2
  have next_denominator_eq := (wallOdd_halfDenominator_data
    (middleDepth := middleDepth) (by omega : 7 ≤ lowerDepth + 1)).2
  have gap_positive :
      0 < 15 * wallOddLargeThreePower lowerDepth * wallOddLargeTwoPower lowerDepth *
        wallOddMiddleThreePower middleDepth *
          (5 * wallOddMiddleThreePower middleDepth +
            3 * wallOddMiddleTwoPower middleDepth) := by
    simp [wallOddLargeThreePower, wallOddLargeTwoPower, wallOddMiddleThreePower,
      wallOddMiddleTwoPower]
  have denominator_eq_rat :
      (wallOddCycleHalfDenominator lowerDepth middleDepth : ℚ) =
        25 * wallOddLargeThreePower lowerDepth * wallOddMiddleThreePower middleDepth -
          wallOddLargeTwoPower lowerDepth * wallOddMiddleTwoPower middleDepth := by
    have cast_eq :
        (wallOddCycleHalfDenominator lowerDepth middleDepth : ℚ) +
            wallOddLargeTwoPower lowerDepth * wallOddMiddleTwoPower middleDepth =
          25 * wallOddLargeThreePower lowerDepth *
            wallOddMiddleThreePower middleDepth := by
      exact_mod_cast denominator_eq
    linarith
  have next_denominator_eq_rat :
      (wallOddCycleHalfDenominator (lowerDepth + 1) middleDepth : ℚ) =
        25 * (3 * wallOddLargeThreePower lowerDepth) *
            wallOddMiddleThreePower middleDepth -
          (2 * wallOddLargeTwoPower lowerDepth) *
            wallOddMiddleTwoPower middleDepth := by
    have cast_eq :
        (wallOddCycleHalfDenominator (lowerDepth + 1) middleDepth : ℚ) +
            wallOddLargeTwoPower (lowerDepth + 1) *
              wallOddMiddleTwoPower middleDepth =
          25 * wallOddLargeThreePower (lowerDepth + 1) *
            wallOddMiddleThreePower middleDepth := by
      exact_mod_cast next_denominator_eq
    rw [p_succ, q_succ] at cast_eq
    norm_num at cast_eq
    linarith
  have cross_gap_rat :
      (wallOddCycleWallNumerator lowerDepth middleDepth : ℚ) *
          wallOddCycleHalfDenominator (lowerDepth + 1) middleDepth =
        wallOddCycleWallNumerator (lowerDepth + 1) middleDepth *
            wallOddCycleHalfDenominator lowerDepth middleDepth +
          15 * wallOddLargeThreePower lowerDepth * wallOddLargeTwoPower lowerDepth *
            wallOddMiddleThreePower middleDepth *
              (5 * wallOddMiddleThreePower middleDepth +
                3 * wallOddMiddleTwoPower middleDepth) := by
    rw [denominator_eq_rat, next_denominator_eq_rat]
    simp only [wallOddCycleWallNumerator]
    rw [p_succ, q_succ]
    push_cast
    ring
  have gap_positive_rat :
      (0 : ℚ) <
        15 * wallOddLargeThreePower lowerDepth * wallOddLargeTwoPower lowerDepth *
          wallOddMiddleThreePower middleDepth *
            (5 * wallOddMiddleThreePower middleDepth +
              3 * wallOddMiddleTwoPower middleDepth) := by
    exact_mod_cast gap_positive
  have cross_lt_rat :
      (wallOddCycleWallNumerator (lowerDepth + 1) middleDepth : ℚ) *
          wallOddCycleHalfDenominator lowerDepth middleDepth <
        wallOddCycleWallNumerator lowerDepth middleDepth *
          wallOddCycleHalfDenominator (lowerDepth + 1) middleDepth := by
    nlinarith [cross_gap_rat, gap_positive_rat]
  have current_denominator_pos_rat :
      (0 : ℚ) < 2 * wallOddCycleHalfDenominator lowerDepth middleDepth := by
    exact_mod_cast Nat.mul_pos (by norm_num : 0 < 2) denominator_pos
  have next_denominator_pos_rat :
      (0 : ℚ) < 2 * wallOddCycleHalfDenominator (lowerDepth + 1) middleDepth := by
    exact_mod_cast Nat.mul_pos (by norm_num : 0 < 2) next_denominator_pos
  simp only [wallOddCycleWallMantissa]
  rw [div_lt_div_iff₀ next_denominator_pos_rat current_denominator_pos_rat]
  nlinarith [cross_lt_rat]

/-- Fixed middle depth gives a strictly decreasing, hence repetition-free, wall family. -/
theorem wallOddCycleWallMantissa_strictAnti (middleDepth : ℕ) :
    StrictAnti (fun offset : ℕ =>
      wallOddCycleWallMantissa (7 + offset) middleDepth) := by
  apply strictAnti_nat_of_succ_lt
  intro offset
  simpa only [Nat.add_assoc] using
    wallOddCycleWallMantissa_succ_lt
      (middleDepth := middleDepth) (by omega : 7 ≤ 7 + offset)

private theorem wallOdd_lower_band_scale_cancel
    {depth : ℕ} (depth_lower : 3 ≤ depth) :
    (3 / 10 : ℚ) * (2 / 3 : ℚ) ^ depth *
        ((wallOddLargeThreePower depth : ℚ) / wallOddLargeTwoPower depth) = 1 / 45 := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le depth_lower
  simp only [wallOddLargeThreePower, wallOddLargeTwoPower]
  simp only [Nat.add_sub_cancel_left, pow_add, div_pow]
  norm_num
  field_simp
  rw [show 2 + offset = offset + 2 by omega, pow_add]
  norm_num
  ring

private theorem wallOdd_middle_band_scale_cancel
    {depth : ℕ} (depth_lower : 2 ≤ depth) :
    (3 / 10 : ℚ) * (2 / 3 : ℚ) ^ depth *
        ((wallOddMiddleThreePower depth : ℚ) /
          (2 * wallOddMiddleTwoPower depth)) = 1 / 15 := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le depth_lower
  simp only [wallOddMiddleThreePower, wallOddMiddleTwoPower]
  simp only [Nat.add_sub_cancel_left, pow_add, div_pow]
  norm_num
  field_simp
  norm_num

/-- The lower-depth band point is exactly the lower predecessor of the wall mantissa. -/
theorem realTrapBandPoint_wallOddCycleOdd_eq_lowerPredecessor
    {lowerDepth middleDepth : ℕ} (lowerDepth_lower : 7 ≤ lowerDepth) :
    realTrapBandPoint lowerDepth (wallOddCycleOddMantissa lowerDepth middleDepth) =
      2 * wallOddCycleWallMantissa lowerDepth middleDepth / 9 := by
  rw [realTrapBandPoint,
    wallOddCycleOddMantissa_eq_lower lowerDepth_lower]
  rw [← mul_assoc, wallOdd_lower_band_scale_cancel (by omega : 3 ≤ lowerDepth)]
  ring

/-- The middle-depth band point is exactly the middle predecessor of the odd mantissa. -/
theorem realTrapBandPoint_wallOddCycleWall_eq_middlePredecessor
    {lowerDepth middleDepth : ℕ} (lowerDepth_lower : 7 ≤ lowerDepth)
    (middleDepth_lower : 2 ≤ middleDepth) :
    realTrapBandPoint middleDepth (wallOddCycleWallMantissa lowerDepth middleDepth) =
      wallOddCycleOddMantissa lowerDepth middleDepth / 3 := by
  rw [realTrapBandPoint,
    wallOddCycleWallMantissa_eq_middle lowerDepth_lower]
  rw [← mul_assoc, wallOdd_middle_band_scale_cancel middleDepth_lower]
  ring

/-- The long wait sends the middle-depth member to the lower-depth member exactly. -/
theorem wallOddCycle_firstStep
    {lowerDepth middleDepth : ℕ} (lowerDepth_lower : 7 ≤ lowerDepth)
    (middleDepth_lower : 2 ≤ middleDepth) :
    shellStep (lowerDepth - 1)
        (realTrapBandPoint middleDepth
          (wallOddCycleWallMantissa lowerDepth middleDepth)) =
      realTrapBandPoint lowerDepth
        (wallOddCycleOddMantissa lowerDepth middleDepth) := by
  rw [realTrapBandPoint_wallOddCycleWall_eq_middlePredecessor
    lowerDepth_lower middleDepth_lower]
  simpa [Nat.sub_add_cancel (by omega : 1 ≤ lowerDepth)] using
    shellStep_middlePredecessor (lowerDepth - 1)
      (wallOddCycleOddMantissa lowerDepth middleDepth)

/-- The short wait returns the lower-depth member to the middle-depth member exactly. -/
theorem wallOddCycle_secondStep
    {lowerDepth middleDepth : ℕ} (lowerDepth_lower : 7 ≤ lowerDepth)
    (middleDepth_lower : 2 ≤ middleDepth) :
    shellStep (middleDepth - 2)
        (realTrapBandPoint lowerDepth
          (wallOddCycleOddMantissa lowerDepth middleDepth)) =
      realTrapBandPoint middleDepth
        (wallOddCycleWallMantissa lowerDepth middleDepth) := by
  rw [realTrapBandPoint_wallOddCycleOdd_eq_lowerPredecessor lowerDepth_lower]
  simpa [Nat.sub_add_cancel middleDepth_lower] using
    shellStep_lowerPredecessor (middleDepth - 2)
      (wallOddCycleWallMantissa lowerDepth middleDepth)

/-- The two exact waits close the wall-to-odd return cycle. -/
theorem wallOddCycle_shellRun
    {lowerDepth middleDepth : ℕ} (lowerDepth_lower : 7 ≤ lowerDepth)
    (middleDepth_lower : 2 ≤ middleDepth) :
    shellRun [lowerDepth - 1, middleDepth - 2]
        (realTrapBandPoint middleDepth
          (wallOddCycleWallMantissa lowerDepth middleDepth)) =
      realTrapBandPoint middleDepth
        (wallOddCycleWallMantissa lowerDepth middleDepth) := by
  rw [shellRun_cons, shellRun_singleton,
    wallOddCycle_firstStep lowerDepth_lower middleDepth_lower,
    wallOddCycle_secondStep lowerDepth_lower middleDepth_lower]

/-- Every phase of the wall-to-odd return cycle satisfies the five-adic shell guard. -/
theorem wallOddCycle_shellPrefixesUnit
    {lowerDepth middleDepth : ℕ} (lowerDepth_lower : 7 ≤ lowerDepth)
    (middleDepth_lower : 2 ≤ middleDepth) :
    ∀ front back,
      [lowerDepth - 1, middleDepth - 2] = front ++ back →
        IsUnit 5
          (shellRun front
            (realTrapBandPoint middleDepth
              (wallOddCycleWallMantissa lowerDepth middleDepth))) := by
  apply (shellPrefixesUnit_iff [lowerDepth - 1, middleDepth - 2]
    (realTrapBandPoint middleDepth
      (wallOddCycleWallMantissa lowerDepth middleDepth))).2
  rw [wallOddCycle_shellRun lowerDepth_lower middleDepth_lower]
  rw [realTrapBandPoint_wallOddCycleWall_eq_middlePredecessor
    lowerDepth_lower middleDepth_lower]
  have three_unit : IsUnit 5 (3 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  exact div_hasValue (wallOddCycleOddMantissa_fiveUnit lowerDepth_lower) three_unit

/-- At the exceptional lower depth six, middle depths four through six still give reduced wall
coordinates. -/
theorem wallOddCycle_depthSix_wallPair_isLowerWallMantissa
    {middleDepth : ℕ} (middleDepth_lower : 4 ≤ middleDepth)
    (middleDepth_upper : middleDepth ≤ 6) :
    IsLowerWallMantissa (wallOddCycleWallPair 6 middleDepth).1
      (wallOddCycleWallPair 6 middleDepth).2 := by
  interval_cases middleDepth
  · change IsLowerWallMantissa 621 313
    exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · change IsLowerWallMantissa 35397 17969
    exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · change IsLowerWallMantissa 106191 54163
    exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The exceptional raw wall mantissa equals the value of its reduced wall pair. -/
theorem wallOddCycle_depthSix_wallMantissa_eq_pairValue
    {middleDepth : ℕ} (middleDepth_lower : 4 ≤ middleDepth)
    (middleDepth_upper : middleDepth ≤ 6) :
    wallOddCycleWallMantissa 6 middleDepth =
      lowerWallValue (wallOddCycleWallPair 6 middleDepth) := by
  interval_cases middleDepth <;>
    norm_num [wallOddCycleWallMantissa, wallOddCycleWallPair,
      primitiveFractionPair, lowerWallValue, wallOddCycleWallNumerator,
      wallOddCycleHalfDenominator, wallOddLargeThreePower,
      wallOddLargeTwoPower, wallOddMiddleThreePower, wallOddMiddleTwoPower]

/-- At the exceptional lower depth six, the odd partners reduce to primitive odd-denominator
five-adic-unit coordinates in the normalized interval. -/
theorem wallOddCycle_depthSix_oddPair_data
    {middleDepth : ℕ} (middleDepth_lower : 4 ≤ middleDepth)
    (middleDepth_upper : middleDepth ≤ 6) :
    let pair := wallOddCycleOddPair 6 middleDepth
    pair.1.Coprime pair.2 ∧ Odd pair.2 ∧
      Nat.Coprime 5 pair.1 ∧ Nat.Coprime 5 pair.2 ∧
      2 * pair.2 < 3 * pair.1 ∧ pair.1 ≤ pair.2 ∧
      wallOddCycleOddMantissa 6 middleDepth = (pair.1 : ℚ) / pair.2 := by
  interval_cases middleDepth <;>
    norm_num [wallOddCycleOddPair, primitiveFractionPair,
      wallOddCycleOddMantissa, wallOddCycleOddNumerator,
      wallOddCycleHalfDenominator, wallOddLargeThreePower,
      wallOddLargeTwoPower, wallOddMiddleThreePower, wallOddMiddleTwoPower]

/-- The exceptional odd partners remain five-adic units. -/
theorem wallOddCycle_depthSix_oddMantissa_fiveUnit
    {middleDepth : ℕ} (middleDepth_lower : 4 ≤ middleDepth)
    (middleDepth_upper : middleDepth ≤ 6) :
    IsUnit 5 (wallOddCycleOddMantissa 6 middleDepth) := by
  have raw_coprime :
      Nat.Coprime 5 (wallOddCycleOddNumerator 6 middleDepth) ∧
        Nat.Coprime 5 (wallOddCycleHalfDenominator 6 middleDepth) := by
    interval_cases middleDepth <;>
      norm_num [wallOddCycleOddNumerator, wallOddCycleHalfDenominator,
        wallOddLargeThreePower, wallOddLargeTwoPower, wallOddMiddleThreePower,
        wallOddMiddleTwoPower]
  exact div_hasValue (natCast_fiveUnit raw_coprime.1)
    (natCast_fiveUnit raw_coprime.2)

/-- At lower depth six, the lower band state is still the exact lower predecessor. -/
theorem realTrapBandPoint_wallOddCycleOdd_depthSix_eq_lowerPredecessor
    {middleDepth : ℕ} (middleDepth_lower : 4 ≤ middleDepth)
    (middleDepth_upper : middleDepth ≤ 6) :
    realTrapBandPoint 6 (wallOddCycleOddMantissa 6 middleDepth) =
      2 * wallOddCycleWallMantissa 6 middleDepth / 9 := by
  interval_cases middleDepth <;>
    norm_num [realTrapBandPoint, wallOddCycleOddMantissa,
      wallOddCycleWallMantissa, wallOddCycleOddNumerator,
      wallOddCycleWallNumerator, wallOddCycleHalfDenominator,
      wallOddLargeThreePower, wallOddLargeTwoPower, wallOddMiddleThreePower,
      wallOddMiddleTwoPower]

/-- At lower depth six, the middle band state is still the exact middle predecessor. -/
theorem realTrapBandPoint_wallOddCycleWall_depthSix_eq_middlePredecessor
    {middleDepth : ℕ} (middleDepth_lower : 4 ≤ middleDepth)
    (middleDepth_upper : middleDepth ≤ 6) :
    realTrapBandPoint middleDepth (wallOddCycleWallMantissa 6 middleDepth) =
      wallOddCycleOddMantissa 6 middleDepth / 3 := by
  interval_cases middleDepth <;>
    norm_num [realTrapBandPoint, wallOddCycleOddMantissa,
      wallOddCycleWallMantissa, wallOddCycleOddNumerator,
      wallOddCycleWallNumerator, wallOddCycleHalfDenominator,
      wallOddLargeThreePower, wallOddLargeTwoPower, wallOddMiddleThreePower,
      wallOddMiddleTwoPower]

/-- The exceptional long wait sends the middle-depth member to the depth-six member. -/
theorem wallOddCycle_depthSix_firstStep
    {middleDepth : ℕ} (middleDepth_lower : 4 ≤ middleDepth)
    (middleDepth_upper : middleDepth ≤ 6) :
    shellStep 5
        (realTrapBandPoint middleDepth
          (wallOddCycleWallMantissa 6 middleDepth)) =
      realTrapBandPoint 6 (wallOddCycleOddMantissa 6 middleDepth) := by
  rw [realTrapBandPoint_wallOddCycleWall_depthSix_eq_middlePredecessor
    middleDepth_lower middleDepth_upper]
  simpa using shellStep_middlePredecessor 5
    (wallOddCycleOddMantissa 6 middleDepth)

/-- The exceptional short wait returns the depth-six member to the middle-depth member. -/
theorem wallOddCycle_depthSix_secondStep
    {middleDepth : ℕ} (middleDepth_lower : 4 ≤ middleDepth)
    (middleDepth_upper : middleDepth ≤ 6) :
    shellStep (middleDepth - 2)
        (realTrapBandPoint 6 (wallOddCycleOddMantissa 6 middleDepth)) =
      realTrapBandPoint middleDepth (wallOddCycleWallMantissa 6 middleDepth) := by
  rw [realTrapBandPoint_wallOddCycleOdd_depthSix_eq_lowerPredecessor
    middleDepth_lower middleDepth_upper]
  simpa [Nat.sub_add_cancel (by omega : 2 ≤ middleDepth)] using
    shellStep_lowerPredecessor (middleDepth - 2)
      (wallOddCycleWallMantissa 6 middleDepth)

/-- The exceptional two waits close exactly. -/
theorem wallOddCycle_depthSix_shellRun
    {middleDepth : ℕ} (middleDepth_lower : 4 ≤ middleDepth)
    (middleDepth_upper : middleDepth ≤ 6) :
    shellRun [5, middleDepth - 2]
        (realTrapBandPoint middleDepth
          (wallOddCycleWallMantissa 6 middleDepth)) =
      realTrapBandPoint middleDepth (wallOddCycleWallMantissa 6 middleDepth) := by
  rw [shellRun_cons, shellRun_singleton,
    wallOddCycle_depthSix_firstStep middleDepth_lower middleDepth_upper,
    wallOddCycle_depthSix_secondStep middleDepth_lower middleDepth_upper]

/-- Every phase of an exceptional depth-six cycle satisfies the five-adic guard. -/
theorem wallOddCycle_depthSix_shellPrefixesUnit
    {middleDepth : ℕ} (middleDepth_lower : 4 ≤ middleDepth)
    (middleDepth_upper : middleDepth ≤ 6) :
    ∀ front back,
      [5, middleDepth - 2] = front ++ back →
        IsUnit 5
          (shellRun front
            (realTrapBandPoint middleDepth
              (wallOddCycleWallMantissa 6 middleDepth))) := by
  apply (shellPrefixesUnit_iff [5, middleDepth - 2]
    (realTrapBandPoint middleDepth
      (wallOddCycleWallMantissa 6 middleDepth))).2
  rw [wallOddCycle_depthSix_shellRun middleDepth_lower middleDepth_upper]
  rw [realTrapBandPoint_wallOddCycleWall_depthSix_eq_middlePredecessor
    middleDepth_lower middleDepth_upper]
  have three_unit : IsUnit 5 (3 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  exact div_hasValue
    (wallOddCycle_depthSix_oddMantissa_fiveUnit middleDepth_lower middleDepth_upper)
    three_unit

/-- Ratio of the large two-power and three-power scales at depth `7 + offset`. -/
def wallOddCycleDepthRatio (offset : ℕ) : ℚ :=
  64 / 81 * (2 / 3) ^ offset

/-- Wall mantissa as a rational curve in the depth ratio. -/
def wallOddCycleWallCurve (middleDepth : ℕ) (ratio : ℚ) : ℚ :=
  3 * wallOddMiddleThreePower middleDepth * (15 + ratio) /
    (2 * (25 * wallOddMiddleThreePower middleDepth -
      ratio * wallOddMiddleTwoPower middleDepth))

private theorem wallOddCycleDepthRatio_eq (offset : ℕ) :
    wallOddCycleDepthRatio offset =
      (wallOddLargeTwoPower (7 + offset) : ℚ) /
        wallOddLargeThreePower (7 + offset) := by
  simp only [wallOddCycleDepthRatio, wallOddLargeTwoPower, wallOddLargeThreePower]
  simp only [show 7 + offset - 1 = 6 + offset by omega,
    show 7 + offset - 3 = 4 + offset by omega, pow_add, div_pow]
  norm_num
  field_simp

/-- The depth-indexed wall family is exactly the displayed rational curve. -/
theorem wallOddCycleWallMantissa_eq_wallCurve
    (offset middleDepth : ℕ) :
    wallOddCycleWallMantissa (7 + offset) middleDepth =
      wallOddCycleWallCurve middleDepth (wallOddCycleDepthRatio offset) := by
  have lowerDepth_lower : 7 ≤ 7 + offset := by omega
  have denominator_eq_nat := (wallOdd_halfDenominator_data
    (middleDepth := middleDepth) lowerDepth_lower).2
  have denominator_eq_rat :
      (wallOddCycleHalfDenominator (7 + offset) middleDepth : ℚ) =
        25 * wallOddLargeThreePower (7 + offset) *
            wallOddMiddleThreePower middleDepth -
          wallOddLargeTwoPower (7 + offset) * wallOddMiddleTwoPower middleDepth := by
    have cast_eq :
        (wallOddCycleHalfDenominator (7 + offset) middleDepth : ℚ) +
            wallOddLargeTwoPower (7 + offset) * wallOddMiddleTwoPower middleDepth =
          25 * wallOddLargeThreePower (7 + offset) *
            wallOddMiddleThreePower middleDepth := by
      exact_mod_cast denominator_eq_nat
    linarith
  have p_ne : (wallOddLargeThreePower (7 + offset) : ℚ) ≠ 0 := by
    simp [wallOddLargeThreePower]
  have denominator_ne :
      (wallOddCycleHalfDenominator (7 + offset) middleDepth : ℚ) ≠ 0 := by
    exact_mod_cast (wallOdd_halfDenominator_pos
      (middleDepth := middleDepth) lowerDepth_lower).ne'
  rw [wallOddCycleWallMantissa, wallOddCycleWallCurve,
    wallOddCycleDepthRatio_eq, denominator_eq_rat]
  simp only [wallOddCycleWallNumerator]
  push_cast
  field_simp

/-- The depth ratio tends to zero. -/
theorem wallOddCycleDepthRatio_tendsto :
    Tendsto wallOddCycleDepthRatio atTop (nhds 0) := by
  have powers :
      Tendsto (fun offset : ℕ => (2 / 3 : ℚ) ^ offset) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  change Tendsto (fun offset : ℕ => (64 / 81 : ℚ) * (2 / 3) ^ offset)
    atTop (nhds 0)
  simpa only [mul_zero] using powers.const_mul (64 / 81 : ℚ)

/-- At every fixed middle depth, the wall mantissas converge to `9/10`. -/
theorem wallOddCycleWallMantissa_tendsto_nineTenths (middleDepth : ℕ) :
    Tendsto (fun offset => wallOddCycleWallMantissa (7 + offset) middleDepth)
      atTop (nhds (9 / 10)) := by
  have ratio_limit := wallOddCycleDepthRatio_tendsto
  have numerator_limit :
      Tendsto
        (fun offset =>
          3 * (wallOddMiddleThreePower middleDepth : ℚ) *
            (15 + wallOddCycleDepthRatio offset))
        atTop (nhds (3 * wallOddMiddleThreePower middleDepth * (15 + 0))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.add ratio_limit)
  have denominator_limit :
      Tendsto
        (fun offset =>
          2 * (25 * (wallOddMiddleThreePower middleDepth : ℚ) -
            wallOddCycleDepthRatio offset * wallOddMiddleTwoPower middleDepth))
        atTop
          (nhds (2 * (25 * wallOddMiddleThreePower middleDepth -
            0 * wallOddMiddleTwoPower middleDepth))) :=
    tendsto_const_nhds.mul
      (tendsto_const_nhds.sub
        (ratio_limit.mul_const (wallOddMiddleTwoPower middleDepth : ℚ)))
  have denominator_limit_ne :
      (2 : ℚ) * (25 * wallOddMiddleThreePower middleDepth -
        0 * wallOddMiddleTwoPower middleDepth) ≠ 0 := by
    simp [wallOddMiddleThreePower]
  have quotient_limit := numerator_limit.div denominator_limit denominator_limit_ne
  rw [show (9 / 10 : ℚ) =
    (3 * wallOddMiddleThreePower middleDepth * (15 + 0)) /
      (2 * (25 * wallOddMiddleThreePower middleDepth -
        0 * wallOddMiddleTwoPower middleDepth)) by
          have middle_power_ne :
              (wallOddMiddleThreePower middleDepth : ℚ) ≠ 0 := by
            simp [wallOddMiddleThreePower]
          field_simp
          ring]
  apply quotient_limit.congr
  intro offset
  rw [Pi.div_apply, wallOddCycleWallMantissa_eq_wallCurve,
    wallOddCycleWallCurve]

/-- The lower-depth states accumulate at the excluded lower endpoint of the real trap. -/
theorem wallOddCycleLowerState_tendsto_oneFifth (middleDepth : ℕ) :
    Tendsto
      (fun offset => realTrapBandPoint (7 + offset)
        (wallOddCycleOddMantissa (7 + offset) middleDepth))
      atTop (nhds (1 / 5)) := by
  have wall_limit := wallOddCycleWallMantissa_tendsto_nineTenths middleDepth
  have scaled_limit := wall_limit.const_mul (2 / 9 : ℚ)
  rw [show (1 / 5 : ℚ) = (2 / 9) * (9 / 10) by norm_num]
  apply scaled_limit.congr
  intro offset
  rw [realTrapBandPoint_wallOddCycleOdd_eq_lowerPredecessor
    (by omega : 7 ≤ 7 + offset)]
  ring

/-- The displayed pair is the unique rational solution of the lower-middle cycle equations. -/
theorem wallOddCycleMantissas_unique
    {lowerDepth middleDepth : ℕ} (lowerDepth_lower : 7 ≤ lowerDepth)
    {wall odd : ℚ}
    (odd_eq : odd =
      (wallOddLargeThreePower lowerDepth : ℚ) /
        wallOddLargeTwoPower lowerDepth * (10 * wall - 9))
    (wall_eq : wall =
      (wallOddMiddleThreePower middleDepth : ℚ) /
        (2 * wallOddMiddleTwoPower middleDepth) * (5 * odd - 3)) :
    wall = wallOddCycleWallMantissa lowerDepth middleDepth ∧
      odd = wallOddCycleOddMantissa lowerDepth middleDepth := by
  have q_ne : (wallOddLargeTwoPower lowerDepth : ℚ) ≠ 0 := by
    simp [wallOddLargeTwoPower]
  have e_ne : (wallOddMiddleTwoPower middleDepth : ℚ) ≠ 0 := by
    simp [wallOddMiddleTwoPower]
  have h_ne : (wallOddCycleHalfDenominator lowerDepth middleDepth : ℚ) ≠ 0 := by
    exact_mod_cast (wallOdd_halfDenominator_pos
      (middleDepth := middleDepth) lowerDepth_lower).ne'
  have denominator_eq_nat := (wallOdd_halfDenominator_data
    (middleDepth := middleDepth) lowerDepth_lower).2
  have denominator_eq_rat :
      (wallOddCycleHalfDenominator lowerDepth middleDepth : ℚ) =
        25 * wallOddLargeThreePower lowerDepth *
            wallOddMiddleThreePower middleDepth -
          wallOddLargeTwoPower lowerDepth * wallOddMiddleTwoPower middleDepth := by
    have cast_eq :
        (wallOddCycleHalfDenominator lowerDepth middleDepth : ℚ) +
            wallOddLargeTwoPower lowerDepth * wallOddMiddleTwoPower middleDepth =
          25 * wallOddLargeThreePower lowerDepth *
            wallOddMiddleThreePower middleDepth := by
      exact_mod_cast denominator_eq_nat
    linarith
  have wall_forced :
      wall = wallOddCycleWallMantissa lowerDepth middleDepth := by
    have odd_cross := odd_eq
    have wall_cross := wall_eq
    field_simp [q_ne] at odd_cross
    field_simp [e_ne] at wall_cross
    have eliminated :
        (50 * (wallOddLargeThreePower lowerDepth : ℚ) *
              wallOddMiddleThreePower middleDepth -
            2 * wallOddLargeTwoPower lowerDepth *
              wallOddMiddleTwoPower middleDepth) * wall =
          3 * wallOddMiddleThreePower middleDepth *
            (15 * wallOddLargeThreePower lowerDepth +
              wallOddLargeTwoPower lowerDepth) := by
      linear_combination
        -(5 * (wallOddMiddleThreePower middleDepth : ℚ)) * odd_cross -
          (wallOddLargeTwoPower lowerDepth : ℚ) * wall_cross
    rw [wallOddCycleWallMantissa, wallOddCycleWallNumerator]
    push_cast
    apply (eq_div_iff (mul_ne_zero (by norm_num : (2 : ℚ) ≠ 0) h_ne)).2
    have twice_denominator :
        (2 : ℚ) * wallOddCycleHalfDenominator lowerDepth middleDepth =
          50 * wallOddLargeThreePower lowerDepth *
              wallOddMiddleThreePower middleDepth -
            2 * wallOddLargeTwoPower lowerDepth *
              wallOddMiddleTwoPower middleDepth := by
      nlinarith [denominator_eq_rat]
    rw [twice_denominator]
    simpa only [mul_comm] using eliminated
  refine ⟨wall_forced, ?_⟩
  rw [wall_forced] at odd_eq
  exact odd_eq.trans (wallOddCycleOddMantissa_eq_lower lowerDepth_lower).symm

/-- The exceptional depth-six pair is also the unique solution of its two cycle equations. -/
theorem wallOddCycle_depthSix_mantissas_unique
    {middleDepth : ℕ} (middleDepth_lower : 4 ≤ middleDepth)
    (middleDepth_upper : middleDepth ≤ 6) {wall odd : ℚ}
    (odd_eq : odd =
      (wallOddLargeThreePower 6 : ℚ) / wallOddLargeTwoPower 6 *
        (10 * wall - 9))
    (wall_eq : wall =
      (wallOddMiddleThreePower middleDepth : ℚ) /
        (2 * wallOddMiddleTwoPower middleDepth) * (5 * odd - 3)) :
    wall = wallOddCycleWallMantissa 6 middleDepth ∧
      odd = wallOddCycleOddMantissa 6 middleDepth := by
  interval_cases middleDepth
  · norm_num [wallOddLargeThreePower, wallOddLargeTwoPower,
      wallOddMiddleThreePower, wallOddMiddleTwoPower,
      wallOddCycleWallMantissa, wallOddCycleOddMantissa,
      wallOddCycleWallNumerator, wallOddCycleOddNumerator,
      wallOddCycleHalfDenominator] at odd_eq wall_eq ⊢
    constructor <;> linarith
  · norm_num [wallOddLargeThreePower, wallOddLargeTwoPower,
      wallOddMiddleThreePower, wallOddMiddleTwoPower,
      wallOddCycleWallMantissa, wallOddCycleOddMantissa,
      wallOddCycleWallNumerator, wallOddCycleOddNumerator,
      wallOddCycleHalfDenominator] at odd_eq wall_eq ⊢
    constructor <;> linarith
  · norm_num [wallOddLargeThreePower, wallOddLargeTwoPower,
      wallOddMiddleThreePower, wallOddMiddleTwoPower,
      wallOddCycleWallMantissa, wallOddCycleOddMantissa,
      wallOddCycleWallNumerator, wallOddCycleOddNumerator,
      wallOddCycleHalfDenominator] at odd_eq wall_eq ⊢
    constructor <;> linarith

end MatrixMortality.MixedPrimeDebt
