import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Field.Basic
import MatrixMortality.CubicContinuantTransversePump
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Separator-source decoding for the transverse cubic pump

The projectively free binary pump is invisible after the fixed suffix reaches its common ray,
but its action on the original separator source retains the complete bit string. A modulo-197
certificate recovers the number of true letters from the source coordinate; a narrow real shell
then recovers the number of false letters. The affine address completes the decoding.
-/

namespace MatrixMortality.CubicReturn.NonPure

open scoped Matrix

local instance sourceDecoderPrime197 : Fact (Nat.Prime 197) := ⟨by norm_num⟩

mutual
  /-- Numerator of the affine pump address under a denominator integral at `197`. -/
  def falseWaitFirstHitBinaryAffineNumerator : List Bool → ℕ
    | [] => 0
    | false :: bits =>
        1712 * falseWaitFirstHitBinaryAffineDenominator bits +
          9 * falseWaitFirstHitBinaryAffineNumerator bits
    | true :: bits =>
        857689 * falseWaitFirstHitBinaryAffineDenominator bits +
          1773 * falseWaitFirstHitBinaryAffineNumerator bits

  /-- Denominator paired with `falseWaitFirstHitBinaryAffineNumerator`. -/
  def falseWaitFirstHitBinaryAffineDenominator : List Bool → ℕ
    | [] => 1
    | false :: bits => 5625 * falseWaitFirstHitBinaryAffineDenominator bits
    | true :: bits => 3024000 * falseWaitFirstHitBinaryAffineDenominator bits
end

/-- Reduction modulo `197` of the affine pump address. -/
def falseWaitFirstHitBinaryAffineResidue : List Bool → ZMod 197
  | [] => 0
  | false :: bits => 88 + 29 * falseWaitFirstHitBinaryAffineResidue bits
  | true :: _ => 66

/-- Every integral affine denominator is positive. -/
theorem falseWaitFirstHitBinaryAffineDenominator_pos (bits : List Bool) :
    0 < falseWaitFirstHitBinaryAffineDenominator bits := by
  induction bits with
  | nil => norm_num [falseWaitFirstHitBinaryAffineDenominator]
  | cons bit bits induction =>
      cases bit <;>
        simp only [falseWaitFirstHitBinaryAffineDenominator] <;>
        positivity

/-- The integral numerator and denominator recover the rational affine address exactly. -/
theorem falseWaitFirstHitBinaryAffineCode_eq_fraction (bits : List Bool) :
    falseWaitFirstHitBinaryAffineCode bits =
      falseWaitFirstHitBinaryAffineNumerator bits /
        falseWaitFirstHitBinaryAffineDenominator bits := by
  induction bits with
  | nil => norm_num [falseWaitFirstHitBinaryAffineCode,
      falseWaitFirstHitBinaryAffineNumerator,
      falseWaitFirstHitBinaryAffineDenominator]
  | cons bit bits induction =>
      have denominator_ne :
          (falseWaitFirstHitBinaryAffineDenominator bits : ℚ) ≠ 0 := by
        exact_mod_cast ne_of_gt (falseWaitFirstHitBinaryAffineDenominator_pos bits)
      cases bit <;>
        simp only [falseWaitFirstHitBinaryAffineCode,
          falseWaitFirstHitBinaryAffineNumerator,
          falseWaitFirstHitBinaryAffineDenominator,
          falseWaitFirstHitBinaryDigit, falseWaitFirstHitBinaryRatio] <;>
        rw [induction] <;>
        push_cast <;>
        field_simp [denominator_ne] <;>
        ring

/-- Every address denominator is nonzero modulo `197`. -/
theorem falseWaitFirstHitBinaryAffineDenominator_mod197_ne_zero (bits : List Bool) :
    (falseWaitFirstHitBinaryAffineDenominator bits : ZMod 197) ≠ 0 := by
  induction bits with
  | nil => norm_num [falseWaitFirstHitBinaryAffineDenominator]
  | cons bit bits induction =>
      cases bit <;>
        simp only [falseWaitFirstHitBinaryAffineDenominator, Nat.cast_mul] <;>
        exact mul_ne_zero (by decide) induction

/-- The recursive residue is the quotient of the integral numerator and denominator. -/
theorem falseWaitFirstHitBinaryAffineNumerator_mod197
    (bits : List Bool) :
    (falseWaitFirstHitBinaryAffineNumerator bits : ZMod 197) =
      falseWaitFirstHitBinaryAffineResidue bits *
        falseWaitFirstHitBinaryAffineDenominator bits := by
  induction bits with
  | nil => norm_num [falseWaitFirstHitBinaryAffineNumerator,
      falseWaitFirstHitBinaryAffineDenominator,
      falseWaitFirstHitBinaryAffineResidue]
  | cons bit bits induction =>
      cases bit
      · simp only [falseWaitFirstHitBinaryAffineNumerator,
          falseWaitFirstHitBinaryAffineDenominator,
          falseWaitFirstHitBinaryAffineResidue, Nat.cast_add, Nat.cast_mul]
        rw [induction]
        have digit_relation :
            (1712 : ZMod 197) = 5625 * 88 := by decide
        have ratio_relation :
            (9 : ZMod 197) = 5625 * 29 := by decide
        norm_num only [Nat.cast_ofNat]
        rw [digit_relation, ratio_relation]
        ring
      · simp only [falseWaitFirstHitBinaryAffineNumerator,
          falseWaitFirstHitBinaryAffineDenominator,
          falseWaitFirstHitBinaryAffineResidue, Nat.cast_add, Nat.cast_mul]
        rw [induction]
        have digit_relation :
            (857689 : ZMod 197) = 3024000 * 66 := by decide
        have ratio_zero : (1773 : ZMod 197) = 0 := by decide
        norm_num only [Nat.cast_ofNat]
        rw [digit_relation, ratio_zero, zero_mul, add_zero]
        ring

/-- Every residue belongs to one of the two period-49 orbits about the fixed point `25`. -/
theorem falseWaitFirstHitBinaryAffineResidue_orbit (bits : List Bool) :
    (falseWaitFirstHitBinaryAffineResidue bits - 25) ^ 49 = 1 ∨
      (falseWaitFirstHitBinaryAffineResidue bits - 25) ^ 49 = -1 := by
  induction bits with
  | nil =>
      left
      exact (show ((0 : ZMod 197) - 25) ^ 49 = 1 by decide)
  | cons bit bits induction =>
      cases bit
      · have recurrence :
            falseWaitFirstHitBinaryAffineResidue (false :: bits) - 25 =
              29 * (falseWaitFirstHitBinaryAffineResidue bits - 25) := by
          simp only [falseWaitFirstHitBinaryAffineResidue]
          calc
            88 + 29 * falseWaitFirstHitBinaryAffineResidue bits - 25 =
                63 + 29 * falseWaitFirstHitBinaryAffineResidue bits := by ring
            _ = 29 * falseWaitFirstHitBinaryAffineResidue bits - 725 := by
              rw [show (63 : ZMod 197) = -725 by decide]
              abel
            _ = 29 * (falseWaitFirstHitBinaryAffineResidue bits - 25) := by
              simp only [mul_sub]
              ring
        rw [recurrence, mul_pow]
        have period : (29 : ZMod 197) ^ 49 = 1 := by decide
        rw [period, one_mul]
        exact induction
      · right
        exact (show ((66 : ZMod 197) - 25) ^ 49 = -1 by decide)

/-- The address residue never equals the separator-source offset `11/123 = 109 mod 197`. -/
theorem falseWaitFirstHitBinaryAffineResidue_ne_source (bits : List Bool) :
    falseWaitFirstHitBinaryAffineResidue bits ≠ (109 : ZMod 197) := by
  intro residue_eq
  have orbit := falseWaitFirstHitBinaryAffineResidue_orbit bits
  rw [residue_eq] at orbit
  exact orbit.elim
    (show ((109 : ZMod 197) - 25) ^ 49 ≠ 1 by decide)
    (show ((109 : ZMod 197) - 25) ^ 49 ≠ -1 by decide)

private theorem falseWaitFirstHitBinarySourceDifference_mod197_ne_zero
    (bits : List Bool) :
    ((123 : ZMod 197) * falseWaitFirstHitBinaryAffineResidue bits - 11) ≠ 0 := by
  intro difference_zero
  have scaled_eq :
      (123 : ZMod 197) * falseWaitFirstHitBinaryAffineResidue bits = 11 :=
    sub_eq_zero.mp difference_zero
  have residue_eq :
      falseWaitFirstHitBinaryAffineResidue bits = (109 : ZMod 197) := by
    calc
      falseWaitFirstHitBinaryAffineResidue bits =
          (189 * 123 : ZMod 197) * falseWaitFirstHitBinaryAffineResidue bits := by
            rw [show (189 * 123 : ZMod 197) = 1 by decide]
            simp
      _ = 189 *
          (123 * falseWaitFirstHitBinaryAffineResidue bits) := by ring
      _ = 189 * 11 := by rw [scaled_eq]
      _ = 109 := by decide
  exact falseWaitFirstHitBinaryAffineResidue_ne_source bits residue_eq

/-- The cleared numerator of `A(bits) - 11/123` is a `197`-adic unit. -/
theorem falseWaitFirstHitBinarySourceDifference_not_dvd (bits : List Bool) :
    ¬(197 : ℤ) ∣
      123 * falseWaitFirstHitBinaryAffineNumerator bits -
        11 * falseWaitFirstHitBinaryAffineDenominator bits := by
  intro divides
  obtain ⟨quotient, difference_eq⟩ := divides
  have difference_cast_zero :
      ((123 * falseWaitFirstHitBinaryAffineNumerator bits -
          11 * falseWaitFirstHitBinaryAffineDenominator bits : ℤ) : ZMod 197) = 0 := by
    rw [difference_eq]
    push_cast
    rw [show (197 : ZMod 197) = 0 by decide, zero_mul]
  have denominator_ne :=
    falseWaitFirstHitBinaryAffineDenominator_mod197_ne_zero bits
  have numerator_relation :=
    falseWaitFirstHitBinaryAffineNumerator_mod197 bits
  have factorization :
      ((123 * falseWaitFirstHitBinaryAffineNumerator bits -
          11 * falseWaitFirstHitBinaryAffineDenominator bits : ℤ) : ZMod 197) =
        falseWaitFirstHitBinaryAffineDenominator bits *
          (123 * falseWaitFirstHitBinaryAffineResidue bits - 11) := by
    push_cast
    rw [numerator_relation]
    ring
  rw [factorization, mul_eq_zero] at difference_cast_zero
  exact difference_cast_zero.elim denominator_ne
    (falseWaitFirstHitBinarySourceDifference_mod197_ne_zero bits)

private theorem falseWaitFirstHitBinaryAffineDenominator_not_dvd (bits : List Bool) :
    ¬(197 : ℤ) ∣ (falseWaitFirstHitBinaryAffineDenominator bits : ℤ) := by
  intro divides
  obtain ⟨quotient, denominator_eq⟩ := divides
  have denominator_cast_zero :
      (falseWaitFirstHitBinaryAffineDenominator bits : ZMod 197) = 0 := by
    calc
      (falseWaitFirstHitBinaryAffineDenominator bits : ZMod 197) =
          ((falseWaitFirstHitBinaryAffineDenominator bits : ℤ) : ZMod 197) := by
            norm_num
      _ = ((197 * quotient : ℤ) : ZMod 197) := by rw [denominator_eq]
      _ = 0 := by
        push_cast
        rw [show (197 : ZMod 197) = 0 by decide, zero_mul]
  exact falseWaitFirstHitBinaryAffineDenominator_mod197_ne_zero bits
    denominator_cast_zero

/-- The affine address differs from the separator offset by a `197`-adic unit. -/
theorem falseWaitFirstHitBinaryAffineCode_sub_source_val197 (bits : List Bool) :
    padicValRat 197
      (falseWaitFirstHitBinaryAffineCode bits - 11 / 123) = 0 := by
  let numerator : ℤ :=
    123 * falseWaitFirstHitBinaryAffineNumerator bits -
      11 * falseWaitFirstHitBinaryAffineDenominator bits
  let denominator : ℤ :=
    123 * falseWaitFirstHitBinaryAffineDenominator bits
  have numerator_not_dvd : ¬(197 : ℤ) ∣ numerator := by
    simpa [numerator] using falseWaitFirstHitBinarySourceDifference_not_dvd bits
  have numerator_ne : numerator ≠ 0 := by
    intro numerator_zero
    apply numerator_not_dvd
    rw [numerator_zero]
    exact dvd_zero _
  have denominator_not_dvd : ¬(197 : ℤ) ∣ denominator := by
    intro denominator_dvd
    have prime_dvd : (197 : ℤ) ∣ 123 ∨
        (197 : ℤ) ∣ (falseWaitFirstHitBinaryAffineDenominator bits : ℤ) :=
      (Prime.dvd_mul (by norm_num : Prime (197 : ℤ))).mp denominator_dvd
    exact prime_dvd.elim (by norm_num)
      (falseWaitFirstHitBinaryAffineDenominator_not_dvd bits)
  have denominator_ne : denominator ≠ 0 := by
    intro denominator_zero
    apply denominator_not_dvd
    rw [denominator_zero]
    exact dvd_zero _
  have fraction_eq :
      falseWaitFirstHitBinaryAffineCode bits - 11 / 123 =
        (numerator : ℚ) / denominator := by
    rw [falseWaitFirstHitBinaryAffineCode_eq_fraction]
    dsimp [numerator, denominator]
    have affine_denominator_ne :
        (falseWaitFirstHitBinaryAffineDenominator bits : ℚ) ≠ 0 := by
      exact_mod_cast ne_of_gt (falseWaitFirstHitBinaryAffineDenominator_pos bits)
    push_cast
    field_simp [affine_denominator_ne]
  have numerator_val : padicValRat 197 (numerator : ℚ) = 0 := by
    rw [padicValRat.of_int]
    exact_mod_cast padicValInt.eq_zero_of_not_dvd numerator_not_dvd
  have denominator_val : padicValRat 197 (denominator : ℚ) = 0 := by
    rw [padicValRat.of_int]
    exact_mod_cast padicValInt.eq_zero_of_not_dvd denominator_not_dvd
  rw [fraction_eq, padicValRat.div (by exact_mod_cast numerator_ne)
    (by exact_mod_cast denominator_ne), numerator_val, denominator_val]
  norm_num

/-- No affine address equals the separator-source offset. -/
theorem falseWaitFirstHitBinaryAffineCode_ne_source (bits : List Bool) :
    falseWaitFirstHitBinaryAffineCode bits ≠ 11 / 123 := by
  intro address_eq
  have denominator_ne :
      (falseWaitFirstHitBinaryAffineDenominator bits : ℚ) ≠ 0 := by
    exact_mod_cast ne_of_gt (falseWaitFirstHitBinaryAffineDenominator_pos bits)
  have cleared_zero :
      (123 * falseWaitFirstHitBinaryAffineNumerator bits -
          11 * falseWaitFirstHitBinaryAffineDenominator bits : ℤ) = 0 := by
    rw [falseWaitFirstHitBinaryAffineCode_eq_fraction] at address_eq
    field_simp [denominator_ne] at address_eq
    have natural_eq :
        123 * falseWaitFirstHitBinaryAffineNumerator bits =
          11 * falseWaitFirstHitBinaryAffineDenominator bits := by
      have reversed :
          falseWaitFirstHitBinaryAffineNumerator bits * 123 =
            falseWaitFirstHitBinaryAffineDenominator bits * 11 := by
        exact_mod_cast address_eq
      simpa [mul_comm] using reversed
    exact sub_eq_zero.mpr (by exact_mod_cast natural_eq)
  apply falseWaitFirstHitBinarySourceDifference_not_dvd bits
  rw [cleared_zero]
  exact dvd_zero _

/-- Lower edge of the nonempty affine-address shell above the separator offset. -/
def falseWaitFirstHitBinarySourceShellLower : ℚ :=
  3439607 / 17712000

/-- Upper edge of the nonempty affine-address shell above the separator offset. -/
def falseWaitFirstHitBinarySourceShellUpper : ℚ :=
  49936 / 230625

/-- Every nonempty affine address lies in one narrow positive shell above `11/123`. -/
theorem falseWaitFirstHitBinaryAffineCode_sub_source_shell
    {bits : List Bool} (bits_ne_nil : bits ≠ []) :
    falseWaitFirstHitBinarySourceShellLower ≤
        falseWaitFirstHitBinaryAffineCode bits - 11 / 123 ∧
      falseWaitFirstHitBinaryAffineCode bits - 11 / 123 ≤
        falseWaitFirstHitBinarySourceShellUpper := by
  cases bits with
  | nil => exact (bits_ne_nil rfl).elim
  | cons bit bits =>
      rcases falseWaitFirstHitBinaryAffineCode_bounds bits with
        ⟨tail_nonnegative, tail_le_one⟩
      cases bit <;>
        norm_num [falseWaitFirstHitBinaryAffineCode,
          falseWaitFirstHitBinaryDigit, falseWaitFirstHitBinaryRatio,
          falseWaitFirstHitBinarySourceShellLower,
          falseWaitFirstHitBinarySourceShellUpper] <;>
        constructor <;> linarith

/-- The shell is narrower than one factor of the false-letter denominator. -/
theorem falseWaitFirstHitBinarySourceShell_separated :
    falseWaitFirstHitBinarySourceShellUpper <
      625 * falseWaitFirstHitBinarySourceShellLower := by
  norm_num [falseWaitFirstHitBinarySourceShellLower,
    falseWaitFirstHitBinarySourceShellUpper]

private theorem falseWaitFirstHitBinaryRatio_ne_zero (bit : Bool) :
    falseWaitFirstHitBinaryRatio bit ≠ 0 := by
  cases bit <;> norm_num [falseWaitFirstHitBinaryRatio]

/-- The accumulated transverse ratio is positive. -/
theorem falseWaitFirstHitBinaryRatioProduct_pos (bits : List Bool) :
    0 < (bits.map falseWaitFirstHitBinaryRatio).prod := by
  apply List.prod_pos
  intro ratio ratio_mem
  obtain ⟨bit, _, rfl⟩ := List.mem_map.mp ratio_mem
  exact (falseWaitFirstHitBinaryRatio_mem_unit bit).1

/-- The accumulated transverse ratio is nonzero. -/
theorem falseWaitFirstHitBinaryRatioProduct_ne_zero (bits : List Bool) :
    (bits.map falseWaitFirstHitBinaryRatio).prod ≠ 0 :=
  ne_of_gt (falseWaitFirstHitBinaryRatioProduct_pos bits)

/-- The accumulated ratio depends only on the two letter counts. -/
theorem falseWaitFirstHitBinaryRatioProduct_eq_counts (bits : List Bool) :
    (bits.map falseWaitFirstHitBinaryRatio).prod =
      (1 / 625 : ℚ) ^ bits.count false *
        (197 / 336000 : ℚ) ^ bits.count true := by
  induction bits with
  | nil => norm_num
  | cons bit bits induction =>
      cases bit <;>
        simp [falseWaitFirstHitBinaryRatio, induction, pow_succ'] <;>
        ring

private theorem falseWaitFirstHitBinaryVal197_unit
    (value : ℕ) (not_dvd : ¬197 ∣ value) :
    padicValRat 197 (value : ℚ) = 0 := by
  rw [padicValRat.of_nat]
  exact_mod_cast padicValNat.eq_zero_of_not_dvd not_dvd

/-- A true pump letter contributes one `197`-adic unit to the transverse ratio; a false letter
contributes none. -/
theorem falseWaitFirstHitBinaryRatio_val197 (bit : Bool) :
    padicValRat 197 (falseWaitFirstHitBinaryRatio bit) = if bit then 1 else 0 := by
  cases bit
  · have denominator_val : padicValRat 197 (625 : ℚ) = 0 :=
      falseWaitFirstHitBinaryVal197_unit 625 (by norm_num)
    rw [falseWaitFirstHitBinaryRatio,
      padicValRat.div (by norm_num) (by norm_num), padicValRat.one,
      denominator_val]
    norm_num
  · have numerator_val : padicValRat 197 (197 : ℚ) = 1 :=
      padicValRat.self (p := 197) (by norm_num)
    have denominator_val : padicValRat 197 (336000 : ℚ) = 0 :=
      falseWaitFirstHitBinaryVal197_unit 336000 (by norm_num)
    rw [falseWaitFirstHitBinaryRatio,
      padicValRat.div (by norm_num) (by norm_num), numerator_val,
      denominator_val]
    norm_num

/-- The `197`-adic valuation of the accumulated ratio is the number of true letters. -/
theorem falseWaitFirstHitBinaryRatioProduct_val197 (bits : List Bool) :
    padicValRat 197 (bits.map falseWaitFirstHitBinaryRatio).prod =
      (bits.count true : ℤ) := by
  induction bits with
  | nil => norm_num
  | cons bit bits induction =>
      rw [List.map_cons, List.prod_cons,
        padicValRat.mul (falseWaitFirstHitBinaryRatio_ne_zero bit)
          (falseWaitFirstHitBinaryRatioProduct_ne_zero bits),
        falseWaitFirstHitBinaryRatio_val197, induction]
      cases bit <;> simp
      ring

/-- Projective coordinate observed after the normalized pump word acts on the original
separator source. -/
def falseWaitFirstHitBinarySourceCoordinate (bits : List Bool) : ℚ :=
  (11 / 123 - falseWaitFirstHitBinaryAffineCode bits.reverse) /
    (bits.map falseWaitFirstHitBinaryRatio).prod

/-- The separator-source coordinate has valuation minus the number of true letters. -/
theorem falseWaitFirstHitBinarySourceCoordinate_val197 (bits : List Bool) :
    padicValRat 197 (falseWaitFirstHitBinarySourceCoordinate bits) =
      -(bits.count true : ℤ) := by
  have address_unit :=
    falseWaitFirstHitBinaryAffineCode_sub_source_val197 bits.reverse
  have numerator_ne :
      11 / 123 - falseWaitFirstHitBinaryAffineCode bits.reverse ≠ 0 := by
    intro numerator_zero
    apply falseWaitFirstHitBinaryAffineCode_ne_source bits.reverse
    linarith
  rw [falseWaitFirstHitBinarySourceCoordinate,
    padicValRat.div numerator_ne
      (falseWaitFirstHitBinaryRatioProduct_ne_zero bits)]
  have numerator_val :
      padicValRat 197
          (11 / 123 - falseWaitFirstHitBinaryAffineCode bits.reverse) = 0 := by
    rw [show 11 / 123 - falseWaitFirstHitBinaryAffineCode bits.reverse =
      -(falseWaitFirstHitBinaryAffineCode bits.reverse - 11 / 123) by ring,
      padicValRat.neg, address_unit]
  rw [numerator_val, falseWaitFirstHitBinaryRatioProduct_val197]
  ring

/-- The empty word has positive separator-source coordinate. -/
theorem falseWaitFirstHitBinarySourceCoordinate_nil_pos :
    0 < falseWaitFirstHitBinarySourceCoordinate [] := by
  norm_num [falseWaitFirstHitBinarySourceCoordinate,
    falseWaitFirstHitBinaryAffineCode]

/-- Every nonempty word has negative separator-source coordinate. -/
theorem falseWaitFirstHitBinarySourceCoordinate_neg
    {bits : List Bool} (bits_ne_nil : bits ≠ []) :
    falseWaitFirstHitBinarySourceCoordinate bits < 0 := by
  have reverse_ne : bits.reverse ≠ [] := by
    simpa using bits_ne_nil
  rcases falseWaitFirstHitBinaryAffineCode_sub_source_shell reverse_ne with
    ⟨lower, _⟩
  have shell_positive : 0 < falseWaitFirstHitBinarySourceShellLower := by
    norm_num [falseWaitFirstHitBinarySourceShellLower]
  have numerator_negative :
      11 / 123 - falseWaitFirstHitBinaryAffineCode bits.reverse < 0 := by
    linarith
  rw [falseWaitFirstHitBinarySourceCoordinate]
  exact div_neg_of_neg_of_pos numerator_negative
    (falseWaitFirstHitBinaryRatioProduct_pos bits)

private theorem falseWaitFirstHitBinaryShellPower_injective
    {leftMagnitude rightMagnitude : ℚ} {leftPower rightPower : ℕ}
    (leftShell : falseWaitFirstHitBinarySourceShellLower ≤ leftMagnitude ∧
      leftMagnitude ≤ falseWaitFirstHitBinarySourceShellUpper)
    (rightShell : falseWaitFirstHitBinarySourceShellLower ≤ rightMagnitude ∧
      rightMagnitude ≤ falseWaitFirstHitBinarySourceShellUpper)
    (power_eq :
      leftMagnitude * (1 / 625 : ℚ) ^ rightPower =
        rightMagnitude * (1 / 625 : ℚ) ^ leftPower) :
    leftPower = rightPower := by
  rcases leftShell with ⟨left_lower, left_upper⟩
  rcases rightShell with ⟨right_lower, right_upper⟩
  have shell_positive : 0 < falseWaitFirstHitBinarySourceShellLower := by
    norm_num [falseWaitFirstHitBinarySourceShellLower]
  have left_positive : 0 < leftMagnitude := shell_positive.trans_le left_lower
  have right_positive : 0 < rightMagnitude := shell_positive.trans_le right_lower
  have separated := falseWaitFirstHitBinarySourceShell_separated
  apply le_antisymm
  · by_contra not_le
    have right_lt_left : rightPower < leftPower := Nat.lt_of_not_ge not_le
    obtain ⟨gap, leftPower_eq⟩ := Nat.exists_eq_add_of_lt right_lt_left
    have common_ne : (1 / 625 : ℚ) ^ rightPower ≠ 0 :=
      pow_ne_zero _ (by norm_num)
    have reduced :
        leftMagnitude = rightMagnitude * (1 / 625 : ℚ) ^ (gap + 1) := by
      apply mul_right_cancel₀ common_ne
      have leftPower_eq' : leftPower = rightPower + (gap + 1) := by omega
      have specialized := power_eq
      rw [leftPower_eq', pow_add] at specialized
      calc
        leftMagnitude * (1 / 625 : ℚ) ^ rightPower =
            rightMagnitude *
              ((1 / 625 : ℚ) ^ rightPower * (1 / 625 : ℚ) ^ (gap + 1)) :=
          specialized
        _ = (rightMagnitude * (1 / 625 : ℚ) ^ (gap + 1)) *
            (1 / 625 : ℚ) ^ rightPower := by ring
    have gap_power_le_one : (1 / 625 : ℚ) ^ gap ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    rw [pow_succ'] at reduced
    have scaled_le : rightMagnitude * (1 / 625 : ℚ) ^ gap ≤ rightMagnitude :=
      by simpa using
        mul_le_mul_of_nonneg_left gap_power_le_one (le_of_lt right_positive)
    norm_num at reduced
    nlinarith
  · by_contra not_le
    have left_lt_right : leftPower < rightPower := Nat.lt_of_not_ge not_le
    obtain ⟨gap, rightPower_eq⟩ := Nat.exists_eq_add_of_lt left_lt_right
    have common_ne : (1 / 625 : ℚ) ^ leftPower ≠ 0 :=
      pow_ne_zero _ (by norm_num)
    have reduced :
        rightMagnitude = leftMagnitude * (1 / 625 : ℚ) ^ (gap + 1) := by
      apply mul_right_cancel₀ common_ne
      have rightPower_eq' : rightPower = leftPower + (gap + 1) := by omega
      have specialized := power_eq
      rw [rightPower_eq', pow_add] at specialized
      calc
        rightMagnitude * (1 / 625 : ℚ) ^ leftPower =
            leftMagnitude *
              ((1 / 625 : ℚ) ^ leftPower * (1 / 625 : ℚ) ^ (gap + 1)) :=
          specialized.symm
        _ = (leftMagnitude * (1 / 625 : ℚ) ^ (gap + 1)) *
            (1 / 625 : ℚ) ^ leftPower := by ring
    have gap_power_le_one : (1 / 625 : ℚ) ^ gap ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    rw [pow_succ'] at reduced
    have scaled_le : leftMagnitude * (1 / 625 : ℚ) ^ gap ≤ leftMagnitude :=
      by simpa using
        mul_le_mul_of_nonneg_left gap_power_le_one (le_of_lt left_positive)
    norm_num at reduced
    nlinarith

/-- The original separator-source coordinate decodes the complete binary pump word. -/
theorem falseWaitFirstHitBinarySourceCoordinate_injective :
    Function.Injective falseWaitFirstHitBinarySourceCoordinate := by
  intro left right coordinate_eq
  cases left with
  | nil =>
      cases right with
      | nil => rfl
      | cons bit bits =>
          have positive := falseWaitFirstHitBinarySourceCoordinate_nil_pos
          have negative := falseWaitFirstHitBinarySourceCoordinate_neg
            (bits := bit :: bits) (by simp)
          rw [coordinate_eq] at positive
          linarith
  | cons leftBit leftBits =>
      cases right with
      | nil =>
          have negative := falseWaitFirstHitBinarySourceCoordinate_neg
            (bits := leftBit :: leftBits) (by simp)
          have positive := falseWaitFirstHitBinarySourceCoordinate_nil_pos
          rw [coordinate_eq] at negative
          linarith
      | cons rightBit rightBits =>
          let leftWord := leftBit :: leftBits
          let rightWord := rightBit :: rightBits
          have true_count_eq : leftWord.count true = rightWord.count true := by
            have valuation_eq := congrArg (padicValRat 197) coordinate_eq
            rw [falseWaitFirstHitBinarySourceCoordinate_val197,
              falseWaitFirstHitBinarySourceCoordinate_val197] at valuation_eq
            exact_mod_cast neg_injective valuation_eq
          let leftMagnitude :=
            falseWaitFirstHitBinaryAffineCode leftWord.reverse - 11 / 123
          let rightMagnitude :=
            falseWaitFirstHitBinaryAffineCode rightWord.reverse - 11 / 123
          have leftShell :
              falseWaitFirstHitBinarySourceShellLower ≤ leftMagnitude ∧
                leftMagnitude ≤ falseWaitFirstHitBinarySourceShellUpper := by
            exact falseWaitFirstHitBinaryAffineCode_sub_source_shell (by
              simp [leftWord])
          have rightShell :
              falseWaitFirstHitBinarySourceShellLower ≤ rightMagnitude ∧
                rightMagnitude ≤ falseWaitFirstHitBinarySourceShellUpper := by
            exact falseWaitFirstHitBinaryAffineCode_sub_source_shell (by
              simp [rightWord])
          have ratio_cross :
              leftMagnitude *
                  (rightWord.map falseWaitFirstHitBinaryRatio).prod =
                rightMagnitude *
                  (leftWord.map falseWaitFirstHitBinaryRatio).prod := by
            have left_ratio_ne :=
              falseWaitFirstHitBinaryRatioProduct_ne_zero leftWord
            have right_ratio_ne :=
              falseWaitFirstHitBinaryRatioProduct_ne_zero rightWord
            have raw_cross :=
              (div_eq_div_iff left_ratio_ne right_ratio_ne).mp coordinate_eq
            dsimp [leftWord, rightWord, falseWaitFirstHitBinarySourceCoordinate,
              leftMagnitude, rightMagnitude] at raw_cross ⊢
            calc
              (falseWaitFirstHitBinaryAffineCode (leftBit :: leftBits).reverse - 11 / 123) *
                    (List.map falseWaitFirstHitBinaryRatio (rightBit :: rightBits)).prod =
                  -((11 / 123 -
                        falseWaitFirstHitBinaryAffineCode (leftBit :: leftBits).reverse) *
                    (List.map falseWaitFirstHitBinaryRatio (rightBit :: rightBits)).prod) := by
                      ring
              _ = -((11 / 123 -
                        falseWaitFirstHitBinaryAffineCode (rightBit :: rightBits).reverse) *
                    (List.map falseWaitFirstHitBinaryRatio (leftBit :: leftBits)).prod) := by
                      rw [raw_cross]
              _ = (falseWaitFirstHitBinaryAffineCode (rightBit :: rightBits).reverse - 11 / 123) *
                    (List.map falseWaitFirstHitBinaryRatio (leftBit :: leftBits)).prod := by
                      ring
          have false_power_cross :
              leftMagnitude * (1 / 625 : ℚ) ^ rightWord.count false =
                rightMagnitude * (1 / 625 : ℚ) ^ leftWord.count false := by
            rw [falseWaitFirstHitBinaryRatioProduct_eq_counts,
              falseWaitFirstHitBinaryRatioProduct_eq_counts,
              true_count_eq] at ratio_cross
            have common_ne :
                (197 / 336000 : ℚ) ^ rightWord.count true ≠ 0 :=
              pow_ne_zero _ (by norm_num)
            apply mul_right_cancel₀ common_ne
            simpa only [mul_assoc] using ratio_cross
          have false_count_eq : leftWord.count false = rightWord.count false :=
            falseWaitFirstHitBinaryShellPower_injective leftShell rightShell
              false_power_cross
          have ratio_eq :
              (leftWord.map falseWaitFirstHitBinaryRatio).prod =
                (rightWord.map falseWaitFirstHitBinaryRatio).prod := by
            rw [falseWaitFirstHitBinaryRatioProduct_eq_counts,
              falseWaitFirstHitBinaryRatioProduct_eq_counts,
              true_count_eq, false_count_eq]
          have magnitude_eq : leftMagnitude = rightMagnitude := by
            rw [ratio_eq] at ratio_cross
            exact mul_right_cancel₀
              (falseWaitFirstHitBinaryRatioProduct_ne_zero rightWord) ratio_cross
          have code_eq :
              falseWaitFirstHitBinaryAffineCode leftWord.reverse =
                falseWaitFirstHitBinaryAffineCode rightWord.reverse := by
            dsimp [leftMagnitude, rightMagnitude] at magnitude_eq
            linarith
          have reverse_eq : leftWord.reverse = rightWord.reverse :=
            falseWaitFirstHitBinaryAffineCode_injective code_eq
          exact List.reverse_injective reverse_eq

/-- Original separator source in the common-ray chart. -/
def falseWaitFirstHitBinarySourceChartVector : Fin 2 → ℚ :=
  ![11, -123]

/-- The common-ray basis sends the chart source back to the physical separator source. -/
theorem falseWaitFirstHitBinaryBasis_sourceChart :
    falseWaitFirstHitBinaryBasis *ᵥ falseWaitFirstHitBinarySourceChartVector =
      falseWaitSeparatorColumn := by
  ext coordinate
  fin_cases coordinate <;>
    norm_num [falseWaitFirstHitBinaryBasis,
      falseWaitFirstHitBinarySourceChartVector, falseWaitSeparatorColumn,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Exact normalized source image carrying the affine address and ratio. -/
theorem falseWaitFirstHitBinaryNormalizedLoop_source (bits : List Bool) :
    wordProduct falseWaitFirstHitBinaryNormalizedLoop bits *ᵥ
        falseWaitFirstHitBinarySourceChartVector =
      ![11 - 123 * falseWaitFirstHitBinaryAffineCode bits.reverse,
        -123 * (bits.map falseWaitFirstHitBinaryRatio).prod] := by
  rcases falseWaitFirstHitBinaryNormalizedLoop_product_entries bits with
    ⟨upper_left, lower_left, lower_right, upper_right⟩
  ext coordinate
  fin_cases coordinate <;>
    simp [Matrix.mulVec, dotProduct, falseWaitFirstHitBinarySourceChartVector,
      Fin.sum_univ_succ, upper_left, lower_left, lower_right, upper_right] <;>
    ring

/-- The rational decoder is the negative quotient of the two normalized source entries. -/
theorem falseWaitFirstHitBinarySourceCoordinate_eq_entries (bits : List Bool) :
    falseWaitFirstHitBinarySourceCoordinate bits =
      -((wordProduct falseWaitFirstHitBinaryNormalizedLoop bits *ᵥ
          falseWaitFirstHitBinarySourceChartVector) 0 /
        (wordProduct falseWaitFirstHitBinaryNormalizedLoop bits *ᵥ
          falseWaitFirstHitBinarySourceChartVector) 1) := by
  rw [falseWaitFirstHitBinaryNormalizedLoop_source]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [falseWaitFirstHitBinarySourceCoordinate]
  have ratio_ne := falseWaitFirstHitBinaryRatioProduct_ne_zero bits
  field_simp [ratio_ne]

/-- Distinct normalized binary pump words give distinct projective images of the original
separator source. -/
theorem falseWaitFirstHitBinaryNormalizedLoop_source_projectively_injective
    {left right : List Bool} {scale : ℚ}
    (projective_eq :
      wordProduct falseWaitFirstHitBinaryNormalizedLoop left *ᵥ
          falseWaitFirstHitBinarySourceChartVector =
        scale •
          (wordProduct falseWaitFirstHitBinaryNormalizedLoop right *ᵥ
            falseWaitFirstHitBinarySourceChartVector)) :
    left = right := by
  let leftSource :=
    wordProduct falseWaitFirstHitBinaryNormalizedLoop left *ᵥ
      falseWaitFirstHitBinarySourceChartVector
  let rightSource :=
    wordProduct falseWaitFirstHitBinaryNormalizedLoop right *ᵥ
      falseWaitFirstHitBinarySourceChartVector
  have left_lower :
      leftSource 1 = -123 * (left.map falseWaitFirstHitBinaryRatio).prod := by
    dsimp [leftSource]
    rw [falseWaitFirstHitBinaryNormalizedLoop_source]
    rfl
  have right_lower :
      rightSource 1 = -123 * (right.map falseWaitFirstHitBinaryRatio).prod := by
    dsimp [rightSource]
    rw [falseWaitFirstHitBinaryNormalizedLoop_source]
    rfl
  have left_lower_ne : leftSource 1 ≠ 0 := by
    rw [left_lower]
    exact mul_ne_zero (by norm_num)
      (falseWaitFirstHitBinaryRatioProduct_ne_zero left)
  have right_lower_ne : rightSource 1 ≠ 0 := by
    rw [right_lower]
    exact mul_ne_zero (by norm_num)
      (falseWaitFirstHitBinaryRatioProduct_ne_zero right)
  have lower_eq := congrFun projective_eq 1
  simp only [Pi.smul_apply, smul_eq_mul] at lower_eq
  change leftSource 1 = scale * rightSource 1 at lower_eq
  have scale_ne : scale ≠ 0 := by
    intro scale_zero
    rw [scale_zero, zero_mul] at lower_eq
    exact left_lower_ne lower_eq
  apply falseWaitFirstHitBinarySourceCoordinate_injective
  rw [falseWaitFirstHitBinarySourceCoordinate_eq_entries,
    falseWaitFirstHitBinarySourceCoordinate_eq_entries]
  change -(leftSource 0 / leftSource 1) = -(rightSource 0 / rightSource 1)
  have upper_eq := congrFun projective_eq 0
  simp only [Pi.smul_apply, smul_eq_mul] at upper_eq
  change leftSource 0 = scale * rightSource 0 at upper_eq
  rw [upper_eq, lower_eq]
  field_simp [scale_ne, right_lower_ne]

/-- Physical pump action on the separator source is the normalized source action in the
common-ray chart, up to the explicit nonzero scale product. -/
theorem falseWaitFirstHitBinaryEncoding_source_chart (bits : List Bool) :
    falseWaitFirstHitBinaryBasisInverse *ᵥ
        (wordProduct falseWaitReturn (falseWaitFirstHitBinaryEncoding bits) *ᵥ
          falseWaitSeparatorColumn) =
      (bits.map falseWaitFirstHitBinaryScale).prod •
        (wordProduct falseWaitFirstHitBinaryNormalizedLoop bits *ᵥ
          falseWaitFirstHitBinarySourceChartVector) := by
  rw [← falseWaitFirstHitBinaryBasis_sourceChart,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    falseWaitFirstHitBinaryEncoding_chart, Matrix.smul_mulVec]

/-- The physical binary pump monoid acts projectively faithfully on the original separator
source, before the ray-reaching suffix erases its transverse coordinate. -/
theorem falseWaitFirstHitBinaryEncoding_source_projectively_injective
    {left right : List Bool} {scale : ℚ}
    (projective_eq :
      wordProduct falseWaitReturn (falseWaitFirstHitBinaryEncoding left) *ᵥ
          falseWaitSeparatorColumn =
        scale •
          (wordProduct falseWaitReturn (falseWaitFirstHitBinaryEncoding right) *ᵥ
            falseWaitSeparatorColumn)) :
    left = right := by
  have charted := congrArg
    (fun source => falseWaitFirstHitBinaryBasisInverse *ᵥ source)
    projective_eq
  rw [Matrix.mulVec_smul, falseWaitFirstHitBinaryEncoding_source_chart,
    falseWaitFirstHitBinaryEncoding_source_chart] at charted
  let leftScale := (left.map falseWaitFirstHitBinaryScale).prod
  let rightScale := (right.map falseWaitFirstHitBinaryScale).prod
  let leftSource :=
    wordProduct falseWaitFirstHitBinaryNormalizedLoop left *ᵥ
      falseWaitFirstHitBinarySourceChartVector
  let rightSource :=
    wordProduct falseWaitFirstHitBinaryNormalizedLoop right *ᵥ
      falseWaitFirstHitBinarySourceChartVector
  have leftScale_ne : leftScale ≠ 0 :=
    falseWaitFirstHitBinaryEncoding_scale_ne_zero left
  have normalized_eq :
      leftSource = (scale * rightScale / leftScale) • rightSource := by
    ext coordinate
    have entry_eq := congrFun charted coordinate
    simp only [Pi.smul_apply, smul_eq_mul,
      leftScale, rightScale, leftSource, rightSource] at entry_eq ⊢
    calc
      (wordProduct falseWaitFirstHitBinaryNormalizedLoop left *ᵥ
          falseWaitFirstHitBinarySourceChartVector) coordinate =
          leftScale⁻¹ *
            (leftScale *
              (wordProduct falseWaitFirstHitBinaryNormalizedLoop left *ᵥ
                falseWaitFirstHitBinarySourceChartVector) coordinate) := by
        field_simp
      _ = leftScale⁻¹ *
          (scale *
            (rightScale *
              (wordProduct falseWaitFirstHitBinaryNormalizedLoop right *ᵥ
                falseWaitFirstHitBinarySourceChartVector) coordinate)) := by
        rw [entry_eq]
      _ = scale * rightScale / leftScale *
          (wordProduct falseWaitFirstHitBinaryNormalizedLoop right *ᵥ
            falseWaitFirstHitBinarySourceChartVector) coordinate := by ring
  exact falseWaitFirstHitBinaryNormalizedLoop_source_projectively_injective normalized_eq

end MatrixMortality.CubicReturn.NonPure
