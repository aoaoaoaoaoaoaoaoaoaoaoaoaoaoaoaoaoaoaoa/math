import MatrixMortality.CubicContinuantFreeSourceStabilizer

/-!
# A one-wait decoder for the free cubic source stabilizers

Appending wait one after the fixed source-side suffix moves the observed source off the
stabilized ray.  In the common-ray chart, every transverse binary word then acts on the fixed
coordinate `-26658067 / 399826944`.  A modulo-197 unit certificate and a narrow positive shell
recover both letter counts; affine-address injectivity recovers the complete word.
-/

namespace MatrixMortality.CubicReturn.NonPure

open scoped Matrix

local instance oneProbePrime197 : Fact (Nat.Prime 197) := ⟨by norm_num⟩

/-- Common-ray coordinate exposed by appending wait one after the safe source suffix. -/
def falseWaitOneProbeOffset : ℚ := -26658067 / 399826944

/-- The one-wait probe in the common-ray chart, normalized to lower coordinate one. -/
def falseWaitOneProbeChartVector : Fin 2 → ℚ := ![falseWaitOneProbeOffset, 1]

/-- Physical transverse encoding followed by the safe suffix and the one-wait probe. -/
def falseWaitOneProbeWord (bits : List Bool) : List Nat :=
  falseWaitFirstHitBinaryEncoding bits ++
    (falseWaitNonacceptingMergeShort ++ [1])

/-- The free source-return prefix followed by one probed transverse binary address. -/
def falseWaitReadableSourceMemoryWord (bits : List Bool) : List Nat :=
  falseWaitFreeSourceReturnWord ++ falseWaitOneProbeWord bits

/-- The readable-memory word is exactly the free stabilizer followed by one positive wait. -/
theorem falseWaitReadableSourceMemoryWord_eq_stabilizer_append_one (bits : List Bool) :
    falseWaitReadableSourceMemoryWord bits =
      falseWaitFreeSourceStabilizerWord bits ++ [1] := by
  simp [falseWaitReadableSourceMemoryWord, falseWaitOneProbeWord,
    falseWaitFreeSourceStabilizerWord, List.append_assoc]

/-- Exact physical probe source in the common-ray chart. -/
theorem falseWaitOneProbe_source_chart :
    falseWaitFirstHitBinaryBasisInverse *ᵥ
        (wordProduct falseWaitReturn (falseWaitNonacceptingMergeShort ++ [1]) *ᵥ
          falseWaitSeparatorColumn) =
      (30220007956807680000 : ℚ) • falseWaitOneProbeChartVector := by
  ext coordinate
  fin_cases coordinate <;>
    norm_num [falseWaitNonacceptingMergeShort, falseWaitOneProbeChartVector,
      falseWaitOneProbeOffset, falseWaitFirstHitBinaryBasisInverse,
      falseWaitSeparatorColumn, wordProduct_cons, wordProduct_nil,
      falseWaitReturn_eq_state, falseWaitReturnOfState, cubicDefectState,
      CubicDefectState.next, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

/-- The physical one-wait probe is the displayed chart vector transported back through the
common-ray basis. -/
theorem falseWaitOneProbe_source_basis :
    wordProduct falseWaitReturn (falseWaitNonacceptingMergeShort ++ [1]) *ᵥ
        falseWaitSeparatorColumn =
      (30220007956807680000 : ℚ) •
        (falseWaitFirstHitBinaryBasis *ᵥ falseWaitOneProbeChartVector) := by
  have charted := congrArg
    (fun source => falseWaitFirstHitBinaryBasis *ᵥ source)
    falseWaitOneProbe_source_chart
  rw [Matrix.mulVec_mulVec,
    falseWaitFirstHitBinaryBasis_inverse_right, Matrix.one_mulVec,
    Matrix.mulVec_smul] at charted
  exact charted

/-- Rational coordinate of a transverse word acting on the one-wait probe. -/
def falseWaitOneProbeCoordinate (bits : List Bool) : ℚ :=
  (falseWaitOneProbeOffset +
      falseWaitFirstHitBinaryAffineCode bits.reverse) /
    (bits.map falseWaitFirstHitBinaryRatio).prod

/-- The affine-address residue never cancels the one-wait offset modulo `197`. -/
theorem falseWaitOneProbeAffineResidue_ne_target (bits : List Bool) :
    falseWaitFirstHitBinaryAffineResidue bits ≠ (114 : ZMod 197) := by
  intro residue_eq
  have orbit := falseWaitFirstHitBinaryAffineResidue_orbit bits
  rw [residue_eq] at orbit
  exact orbit.elim
    (show ((114 : ZMod 197) - 25) ^ 49 ≠ 1 by decide)
    (show ((114 : ZMod 197) - 25) ^ 49 ≠ -1 by decide)

private theorem oneProbeClearedNumerator_mod197_ne_zero (bits : List Bool) :
    ((399826944 : ZMod 197) *
          falseWaitFirstHitBinaryAffineResidue bits - 26658067) ≠ 0 := by
  intro difference_zero
  have scaled_eq :
      (399826944 : ZMod 197) *
          falseWaitFirstHitBinaryAffineResidue bits = 26658067 :=
    sub_eq_zero.mp difference_zero
  have residue_eq :
      falseWaitFirstHitBinaryAffineResidue bits = (114 : ZMod 197) := by
    calc
      falseWaitFirstHitBinaryAffineResidue bits =
          (48 * 399826944 : ZMod 197) *
            falseWaitFirstHitBinaryAffineResidue bits := by
              rw [show (48 * 399826944 : ZMod 197) = 1 by decide]
              simp
      _ = 48 *
          (399826944 * falseWaitFirstHitBinaryAffineResidue bits) := by ring
      _ = 48 * 26658067 := by rw [scaled_eq]
      _ = 114 := by decide
  exact falseWaitOneProbeAffineResidue_ne_target bits residue_eq

/-- The cleared numerator of the probed affine address is not divisible by `197`. -/
theorem falseWaitOneProbeAffineNumerator_not_dvd (bits : List Bool) :
    ¬(197 : ℤ) ∣
      399826944 * falseWaitFirstHitBinaryAffineNumerator bits -
        26658067 * falseWaitFirstHitBinaryAffineDenominator bits := by
  intro divides
  obtain ⟨quotient, difference_eq⟩ := divides
  have difference_cast_zero :
      ((399826944 * falseWaitFirstHitBinaryAffineNumerator bits -
          26658067 * falseWaitFirstHitBinaryAffineDenominator bits : ℤ) :
        ZMod 197) = 0 := by
    rw [difference_eq]
    push_cast
    rw [show (197 : ZMod 197) = 0 by decide, zero_mul]
  have denominator_ne :=
    falseWaitFirstHitBinaryAffineDenominator_mod197_ne_zero bits
  have numerator_relation :=
    falseWaitFirstHitBinaryAffineNumerator_mod197 bits
  have factorization :
      ((399826944 * falseWaitFirstHitBinaryAffineNumerator bits -
          26658067 * falseWaitFirstHitBinaryAffineDenominator bits : ℤ) :
        ZMod 197) =
      falseWaitFirstHitBinaryAffineDenominator bits *
        (399826944 * falseWaitFirstHitBinaryAffineResidue bits - 26658067) := by
    push_cast
    rw [numerator_relation]
    ring
  rw [factorization, mul_eq_zero] at difference_cast_zero
  exact difference_cast_zero.elim denominator_ne
    (oneProbeClearedNumerator_mod197_ne_zero bits)

private theorem oneProbeAffineDenominator_not_dvd (bits : List Bool) :
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

/-- The probed affine numerator is a `197`-adic unit. -/
theorem falseWaitOneProbeAffineNumerator_val197 (bits : List Bool) :
    padicValRat 197
      (falseWaitOneProbeOffset + falseWaitFirstHitBinaryAffineCode bits) = 0 := by
  let numerator : ℤ :=
    399826944 * falseWaitFirstHitBinaryAffineNumerator bits -
      26658067 * falseWaitFirstHitBinaryAffineDenominator bits
  let denominator : ℤ :=
    399826944 * falseWaitFirstHitBinaryAffineDenominator bits
  have numerator_not_dvd : ¬(197 : ℤ) ∣ numerator := by
    simpa [numerator] using falseWaitOneProbeAffineNumerator_not_dvd bits
  have numerator_ne : numerator ≠ 0 := by
    intro numerator_zero
    apply numerator_not_dvd
    rw [numerator_zero]
    exact dvd_zero _
  have denominator_not_dvd : ¬(197 : ℤ) ∣ denominator := by
    intro denominator_dvd
    have prime_dvd : (197 : ℤ) ∣ 399826944 ∨
        (197 : ℤ) ∣ (falseWaitFirstHitBinaryAffineDenominator bits : ℤ) :=
      (Prime.dvd_mul (by norm_num : Prime (197 : ℤ))).mp denominator_dvd
    exact prime_dvd.elim (by norm_num) (oneProbeAffineDenominator_not_dvd bits)
  have denominator_ne : denominator ≠ 0 := by
    intro denominator_zero
    apply denominator_not_dvd
    rw [denominator_zero]
    exact dvd_zero _
  have fraction_eq :
      falseWaitOneProbeOffset + falseWaitFirstHitBinaryAffineCode bits =
        (numerator : ℚ) / denominator := by
    rw [falseWaitFirstHitBinaryAffineCode_eq_fraction]
    dsimp [falseWaitOneProbeOffset, numerator, denominator]
    have affine_denominator_ne :
        (falseWaitFirstHitBinaryAffineDenominator bits : ℚ) ≠ 0 := by
      exact_mod_cast ne_of_gt (falseWaitFirstHitBinaryAffineDenominator_pos bits)
    push_cast
    field_simp [affine_denominator_ne]
    ring
  have numerator_val : padicValRat 197 (numerator : ℚ) = 0 := by
    rw [padicValRat.of_int]
    exact_mod_cast padicValInt.eq_zero_of_not_dvd numerator_not_dvd
  have denominator_val : padicValRat 197 (denominator : ℚ) = 0 := by
    rw [padicValRat.of_int]
    exact_mod_cast padicValInt.eq_zero_of_not_dvd denominator_not_dvd
  rw [fraction_eq, padicValRat.div (by exact_mod_cast numerator_ne)
    (by exact_mod_cast denominator_ne), numerator_val, denominator_val]
  norm_num

/-- The probed affine numerator never vanishes. -/
theorem falseWaitOneProbeAffineNumerator_ne (bits : List Bool) :
    falseWaitOneProbeOffset + falseWaitFirstHitBinaryAffineCode bits ≠ 0 := by
  intro sum_zero
  have affine_denominator_ne :
      (falseWaitFirstHitBinaryAffineDenominator bits : ℚ) ≠ 0 := by
    exact_mod_cast ne_of_gt (falseWaitFirstHitBinaryAffineDenominator_pos bits)
  have cleared_zero :
      (399826944 * falseWaitFirstHitBinaryAffineNumerator bits -
          26658067 * falseWaitFirstHitBinaryAffineDenominator bits : ℤ) = 0 := by
    rw [falseWaitOneProbeOffset,
      falseWaitFirstHitBinaryAffineCode_eq_fraction] at sum_zero
    field_simp [affine_denominator_ne] at sum_zero
    norm_num at sum_zero
    have rational_eq :
        (399826944 * falseWaitFirstHitBinaryAffineNumerator bits : ℕ) =
          26658067 * falseWaitFirstHitBinaryAffineDenominator bits := by
      exact_mod_cast (show
        (399826944 * falseWaitFirstHitBinaryAffineNumerator bits : ℚ) =
          26658067 * falseWaitFirstHitBinaryAffineDenominator bits by
            linarith [sum_zero])
    have natural_eq :
        399826944 * falseWaitFirstHitBinaryAffineNumerator bits =
          26658067 * falseWaitFirstHitBinaryAffineDenominator bits := by
      exact rational_eq
    exact sub_eq_zero.mpr (by exact_mod_cast natural_eq)
  apply falseWaitOneProbeAffineNumerator_not_dvd bits
  rw [cleared_zero]
  exact dvd_zero _

/-- The one-wait source coordinate has valuation minus the number of true letters. -/
theorem falseWaitOneProbeCoordinate_val197 (bits : List Bool) :
    padicValRat 197 (falseWaitOneProbeCoordinate bits) =
      -(bits.count true : ℤ) := by
  have numerator_val := falseWaitOneProbeAffineNumerator_val197 bits.reverse
  have numerator_ne :
      falseWaitOneProbeOffset +
          falseWaitFirstHitBinaryAffineCode bits.reverse ≠ 0 :=
    falseWaitOneProbeAffineNumerator_ne bits.reverse
  rw [falseWaitOneProbeCoordinate,
    padicValRat.div numerator_ne
      (falseWaitFirstHitBinaryRatioProduct_ne_zero bits),
    numerator_val, falseWaitFirstHitBinaryRatioProduct_val197]
  ring

/-- Lower edge of the positive shell exposed by every nonempty probed address. -/
def falseWaitOneProbeShellLower : ℚ :=
  falseWaitOneProbeOffset + 122527 / 432000

/-- Upper edge of the positive shell exposed by every nonempty probed address. -/
def falseWaitOneProbeShellUpper : ℚ :=
  falseWaitOneProbeOffset + 1712 / 5625 + 1 / 625

/-- Every nonempty probed affine numerator lies in one narrow positive shell. -/
theorem falseWaitOneProbeAffineNumerator_shell
    {bits : List Bool} (bits_ne_nil : bits ≠ []) :
    falseWaitOneProbeShellLower ≤
        falseWaitOneProbeOffset + falseWaitFirstHitBinaryAffineCode bits ∧
      falseWaitOneProbeOffset + falseWaitFirstHitBinaryAffineCode bits ≤
        falseWaitOneProbeShellUpper := by
  cases bits with
  | nil => exact (bits_ne_nil rfl).elim
  | cons bit bits =>
      rcases falseWaitFirstHitBinaryAffineCode_bounds bits with
        ⟨tail_nonnegative, tail_le_one⟩
      cases bit <;>
        norm_num [falseWaitOneProbeShellLower, falseWaitOneProbeShellUpper,
          falseWaitOneProbeOffset, falseWaitFirstHitBinaryAffineCode,
          falseWaitFirstHitBinaryDigit, falseWaitFirstHitBinaryRatio] <;>
        constructor <;> linarith

/-- The probed shell is narrower than one factor of the false-letter denominator. -/
theorem falseWaitOneProbeShell_separated :
    falseWaitOneProbeShellUpper < 625 * falseWaitOneProbeShellLower := by
  norm_num [falseWaitOneProbeShellLower, falseWaitOneProbeShellUpper,
    falseWaitOneProbeOffset]

/-- The empty probed coordinate is negative. -/
theorem falseWaitOneProbeCoordinate_nil_neg :
    falseWaitOneProbeCoordinate [] < 0 := by
  norm_num [falseWaitOneProbeCoordinate, falseWaitOneProbeOffset,
    falseWaitFirstHitBinaryAffineCode]

/-- Every nonempty probed coordinate is positive. -/
theorem falseWaitOneProbeCoordinate_pos
    {bits : List Bool} (bits_ne_nil : bits ≠ []) :
    0 < falseWaitOneProbeCoordinate bits := by
  have reverse_ne : bits.reverse ≠ [] := by simpa using bits_ne_nil
  rcases falseWaitOneProbeAffineNumerator_shell reverse_ne with ⟨lower, _⟩
  have shell_positive : 0 < falseWaitOneProbeShellLower := by
    norm_num [falseWaitOneProbeShellLower, falseWaitOneProbeOffset]
  have numerator_positive :
      0 < falseWaitOneProbeOffset +
        falseWaitFirstHitBinaryAffineCode bits.reverse :=
    shell_positive.trans_le lower
  rw [falseWaitOneProbeCoordinate]
  exact div_pos numerator_positive (falseWaitFirstHitBinaryRatioProduct_pos bits)

private theorem oneProbeShellPower_injective
    {leftMagnitude rightMagnitude : ℚ} {leftPower rightPower : ℕ}
    (leftShell : falseWaitOneProbeShellLower ≤ leftMagnitude ∧
      leftMagnitude ≤ falseWaitOneProbeShellUpper)
    (rightShell : falseWaitOneProbeShellLower ≤ rightMagnitude ∧
      rightMagnitude ≤ falseWaitOneProbeShellUpper)
    (power_eq :
      leftMagnitude * (1 / 625 : ℚ) ^ rightPower =
        rightMagnitude * (1 / 625 : ℚ) ^ leftPower) :
    leftPower = rightPower := by
  rcases leftShell with ⟨left_lower, left_upper⟩
  rcases rightShell with ⟨right_lower, right_upper⟩
  have shell_positive : 0 < falseWaitOneProbeShellLower := by
    norm_num [falseWaitOneProbeShellLower, falseWaitOneProbeOffset]
  have left_positive : 0 < leftMagnitude := shell_positive.trans_le left_lower
  have right_positive : 0 < rightMagnitude := shell_positive.trans_le right_lower
  have separated := falseWaitOneProbeShell_separated
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

/-- The one-wait coordinate decodes the complete transverse binary address. -/
theorem falseWaitOneProbeCoordinate_injective :
    Function.Injective falseWaitOneProbeCoordinate := by
  intro left right coordinate_eq
  cases left with
  | nil =>
      cases right with
      | nil => rfl
      | cons bit bits =>
          have negative := falseWaitOneProbeCoordinate_nil_neg
          have positive := falseWaitOneProbeCoordinate_pos
            (bits := bit :: bits) (by simp)
          rw [coordinate_eq] at negative
          linarith
  | cons leftBit leftBits =>
      cases right with
      | nil =>
          have positive := falseWaitOneProbeCoordinate_pos
            (bits := leftBit :: leftBits) (by simp)
          have negative := falseWaitOneProbeCoordinate_nil_neg
          rw [coordinate_eq] at positive
          linarith
      | cons rightBit rightBits =>
          let leftWord := leftBit :: leftBits
          let rightWord := rightBit :: rightBits
          have true_count_eq : leftWord.count true = rightWord.count true := by
            have valuation_eq := congrArg (padicValRat 197) coordinate_eq
            rw [falseWaitOneProbeCoordinate_val197,
              falseWaitOneProbeCoordinate_val197] at valuation_eq
            exact_mod_cast neg_injective valuation_eq
          let leftMagnitude :=
            falseWaitOneProbeOffset +
              falseWaitFirstHitBinaryAffineCode leftWord.reverse
          let rightMagnitude :=
            falseWaitOneProbeOffset +
              falseWaitFirstHitBinaryAffineCode rightWord.reverse
          have leftShell :
              falseWaitOneProbeShellLower ≤ leftMagnitude ∧
                leftMagnitude ≤ falseWaitOneProbeShellUpper := by
            exact falseWaitOneProbeAffineNumerator_shell (by simp [leftWord])
          have rightShell :
              falseWaitOneProbeShellLower ≤ rightMagnitude ∧
                rightMagnitude ≤ falseWaitOneProbeShellUpper := by
            exact falseWaitOneProbeAffineNumerator_shell (by simp [rightWord])
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
            simpa [leftWord, rightWord, falseWaitOneProbeCoordinate,
              leftMagnitude, rightMagnitude] using raw_cross
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
            oneProbeShellPower_injective leftShell rightShell false_power_cross
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

/-- Exact normalized one-wait probe image carrying the new address coordinate. -/
theorem falseWaitOneProbeNormalizedLoop_source (bits : List Bool) :
    wordProduct falseWaitFirstHitBinaryNormalizedLoop bits *ᵥ
        falseWaitOneProbeChartVector =
      ![falseWaitOneProbeOffset +
          falseWaitFirstHitBinaryAffineCode bits.reverse,
        (bits.map falseWaitFirstHitBinaryRatio).prod] := by
  rcases falseWaitFirstHitBinaryNormalizedLoop_product_entries bits with
    ⟨upper_left, lower_left, lower_right, upper_right⟩
  ext coordinate
  fin_cases coordinate
  · simp [Matrix.mulVec, dotProduct, falseWaitOneProbeChartVector,
      Fin.sum_univ_succ, upper_left, upper_right]
  · simp [Matrix.mulVec, dotProduct, falseWaitOneProbeChartVector,
      Fin.sum_univ_succ, lower_left, lower_right]

/-- The decoder is the quotient of the two normalized one-wait source entries. -/
theorem falseWaitOneProbeCoordinate_eq_entries (bits : List Bool) :
    falseWaitOneProbeCoordinate bits =
      (wordProduct falseWaitFirstHitBinaryNormalizedLoop bits *ᵥ
          falseWaitOneProbeChartVector) 0 /
        (wordProduct falseWaitFirstHitBinaryNormalizedLoop bits *ᵥ
          falseWaitOneProbeChartVector) 1 := by
  rw [falseWaitOneProbeNormalizedLoop_source]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl

/-- Distinct binary addresses give distinct projective images of the one-wait probe. -/
theorem falseWaitOneProbeNormalizedLoop_source_projectively_injective
    {left right : List Bool} {scale : ℚ}
    (projective_eq :
      wordProduct falseWaitFirstHitBinaryNormalizedLoop left *ᵥ
          falseWaitOneProbeChartVector =
        scale •
          (wordProduct falseWaitFirstHitBinaryNormalizedLoop right *ᵥ
            falseWaitOneProbeChartVector)) :
    left = right := by
  let leftSource :=
    wordProduct falseWaitFirstHitBinaryNormalizedLoop left *ᵥ
      falseWaitOneProbeChartVector
  let rightSource :=
    wordProduct falseWaitFirstHitBinaryNormalizedLoop right *ᵥ
      falseWaitOneProbeChartVector
  have left_lower :
      leftSource 1 = (left.map falseWaitFirstHitBinaryRatio).prod := by
    dsimp [leftSource]
    rw [falseWaitOneProbeNormalizedLoop_source]
    rfl
  have right_lower :
      rightSource 1 = (right.map falseWaitFirstHitBinaryRatio).prod := by
    dsimp [rightSource]
    rw [falseWaitOneProbeNormalizedLoop_source]
    rfl
  have left_lower_ne : leftSource 1 ≠ 0 := by
    rw [left_lower]
    exact falseWaitFirstHitBinaryRatioProduct_ne_zero left
  have right_lower_ne : rightSource 1 ≠ 0 := by
    rw [right_lower]
    exact falseWaitFirstHitBinaryRatioProduct_ne_zero right
  have lower_eq := congrFun projective_eq 1
  simp only [Pi.smul_apply, smul_eq_mul] at lower_eq
  change leftSource 1 = scale * rightSource 1 at lower_eq
  have scale_ne : scale ≠ 0 := by
    intro scale_zero
    rw [scale_zero, zero_mul] at lower_eq
    exact left_lower_ne lower_eq
  apply falseWaitOneProbeCoordinate_injective
  rw [falseWaitOneProbeCoordinate_eq_entries,
    falseWaitOneProbeCoordinate_eq_entries]
  change leftSource 0 / leftSource 1 = rightSource 0 / rightSource 1
  have upper_eq := congrFun projective_eq 0
  simp only [Pi.smul_apply, smul_eq_mul] at upper_eq
  change leftSource 0 = scale * rightSource 0 at upper_eq
  rw [upper_eq, lower_eq]
  field_simp [scale_ne, right_lower_ne]

/-- Physical one-wait probe action is its normalized chart action times the explicit nonzero
physical scales. -/
theorem falseWaitOneProbeWord_source_chart (bits : List Bool) :
    falseWaitFirstHitBinaryBasisInverse *ᵥ
        (wordProduct falseWaitReturn (falseWaitOneProbeWord bits) *ᵥ
          falseWaitSeparatorColumn) =
      (30220007956807680000 *
          (bits.map falseWaitFirstHitBinaryScale).prod : ℚ) •
        (wordProduct falseWaitFirstHitBinaryNormalizedLoop bits *ᵥ
          falseWaitOneProbeChartVector) := by
  have normalized :
      falseWaitFirstHitBinaryBasisInverse *ᵥ
            (wordProduct falseWaitReturn (falseWaitFirstHitBinaryEncoding bits) *ᵥ
              (falseWaitFirstHitBinaryBasis *ᵥ falseWaitOneProbeChartVector)) =
        (bits.map falseWaitFirstHitBinaryScale).prod •
          (wordProduct falseWaitFirstHitBinaryNormalizedLoop bits *ᵥ
            falseWaitOneProbeChartVector) := by
    calc
      falseWaitFirstHitBinaryBasisInverse *ᵥ
            (wordProduct falseWaitReturn (falseWaitFirstHitBinaryEncoding bits) *ᵥ
              (falseWaitFirstHitBinaryBasis *ᵥ falseWaitOneProbeChartVector)) =
          (falseWaitFirstHitBinaryBasisInverse *
              wordProduct falseWaitReturn (falseWaitFirstHitBinaryEncoding bits) *
            falseWaitFirstHitBinaryBasis) *ᵥ falseWaitOneProbeChartVector := by
              simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = ((bits.map falseWaitFirstHitBinaryScale).prod •
            wordProduct falseWaitFirstHitBinaryNormalizedLoop bits) *ᵥ
          falseWaitOneProbeChartVector := by
            rw [falseWaitFirstHitBinaryEncoding_chart]
      _ = (bits.map falseWaitFirstHitBinaryScale).prod •
          (wordProduct falseWaitFirstHitBinaryNormalizedLoop bits *ᵥ
            falseWaitOneProbeChartVector) := by rw [Matrix.smul_mulVec]
  rw [falseWaitOneProbeWord, wordProduct_append,
    ← Matrix.mulVec_mulVec, falseWaitOneProbe_source_basis,
    Matrix.mulVec_smul, Matrix.mulVec_smul, normalized, smul_smul]

/-- The physical one-wait probe reads the complete transverse binary address projectively. -/
theorem falseWaitOneProbeWord_source_projectively_injective
    {left right : List Bool} {scale : ℚ}
    (projective_eq :
      wordProduct falseWaitReturn (falseWaitOneProbeWord left) *ᵥ
          falseWaitSeparatorColumn =
        scale •
          (wordProduct falseWaitReturn (falseWaitOneProbeWord right) *ᵥ
            falseWaitSeparatorColumn)) :
    left = right := by
  have charted := congrArg
    (fun source => falseWaitFirstHitBinaryBasisInverse *ᵥ source)
    projective_eq
  rw [Matrix.mulVec_smul, falseWaitOneProbeWord_source_chart,
    falseWaitOneProbeWord_source_chart] at charted
  let leftScale : ℚ :=
    30220007956807680000 *
      (left.map falseWaitFirstHitBinaryScale).prod
  let rightScale : ℚ :=
    30220007956807680000 *
      (right.map falseWaitFirstHitBinaryScale).prod
  let leftSource :=
    wordProduct falseWaitFirstHitBinaryNormalizedLoop left *ᵥ
      falseWaitOneProbeChartVector
  let rightSource :=
    wordProduct falseWaitFirstHitBinaryNormalizedLoop right *ᵥ
      falseWaitOneProbeChartVector
  have leftScale_ne : leftScale ≠ 0 :=
    mul_ne_zero (by norm_num)
      (falseWaitFirstHitBinaryEncoding_scale_ne_zero left)
  have normalized_eq :
      leftSource = (scale * rightScale / leftScale) • rightSource := by
    ext coordinate
    have entry_eq := congrFun charted coordinate
    simp only [Pi.smul_apply, smul_eq_mul, leftScale, rightScale,
      leftSource, rightSource] at entry_eq ⊢
    calc
      (wordProduct falseWaitFirstHitBinaryNormalizedLoop left *ᵥ
            falseWaitOneProbeChartVector) coordinate =
          leftScale⁻¹ *
            (leftScale *
              (wordProduct falseWaitFirstHitBinaryNormalizedLoop left *ᵥ
                falseWaitOneProbeChartVector) coordinate) := by
            field_simp
      _ = leftScale⁻¹ *
          (scale *
            (rightScale *
              (wordProduct falseWaitFirstHitBinaryNormalizedLoop right *ᵥ
                falseWaitOneProbeChartVector) coordinate)) := by
            rw [entry_eq]
      _ = scale * rightScale / leftScale *
          (wordProduct falseWaitFirstHitBinaryNormalizedLoop right *ᵥ
            falseWaitOneProbeChartVector) coordinate := by ring
  exact falseWaitOneProbeNormalizedLoop_source_projectively_injective normalized_eq

/-- Every wait in a physically probed binary address is strictly positive. -/
theorem falseWaitOneProbeWord_positive (bits : List Bool) :
    ∀ wait ∈ falseWaitOneProbeWord bits, 0 < wait := by
  intro wait membership
  simp only [falseWaitOneProbeWord, List.mem_append] at membership
  rcases membership with encoded | suffix
  · exact falseWaitFirstHitBinaryEncoding_positive bits wait encoded
  · simp [falseWaitNonacceptingMergeShort] at suffix
    omega

/-- The physically probed address has exact length `7+4|β|`. -/
theorem falseWaitOneProbeWord_length (bits : List Bool) :
    (falseWaitOneProbeWord bits).length = 7 + 4 * bits.length := by
  rw [falseWaitOneProbeWord, List.length_append,
    falseWaitFirstHitBinaryEncoding_length]
  norm_num [falseWaitNonacceptingMergeShort]
  omega

/-- Every wait in the complete readable source-memory word is strictly positive. -/
theorem falseWaitReadableSourceMemoryWord_positive (bits : List Bool) :
    ∀ wait ∈ falseWaitReadableSourceMemoryWord bits, 0 < wait := by
  intro wait membership
  rw [falseWaitReadableSourceMemoryWord, List.mem_append] at membership
  exact membership.elim
    (falseWaitFreeSourceReturnWord_positive wait)
    (falseWaitOneProbeWord_positive bits wait)

/-- The complete readable source-memory word has exact length `71,192+4|β|`. -/
theorem falseWaitReadableSourceMemoryWord_length (bits : List Bool) :
    (falseWaitReadableSourceMemoryWord bits).length = 71192 + 4 * bits.length := by
  rw [falseWaitReadableSourceMemoryWord, List.length_append,
    falseWaitFreeSourceReturnWord_length, falseWaitOneProbeWord_length]
  omega

/-- The readable-memory spelling factors through its fixed invertible return prefix. -/
theorem falseWaitReadableSourceMemoryWord_source_factor (bits : List Bool) :
    wordProduct falseWaitReturn (falseWaitReadableSourceMemoryWord bits) *ᵥ
        falseWaitSeparatorColumn =
      wordProduct falseWaitReturn falseWaitFreeSourceReturnWord *ᵥ
        (wordProduct falseWaitReturn (falseWaitOneProbeWord bits) *ᵥ
          falseWaitSeparatorColumn) := by
  rw [falseWaitReadableSourceMemoryWord, wordProduct_append,
    Matrix.mulVec_mulVec]

/-- A single positive wait makes the previously hidden free source-stabilizer address
projectively observable. -/
theorem falseWaitReadableSourceMemoryWord_source_projectively_injective
    {left right : List Bool} {scale : ℚ}
    (projective_eq :
      wordProduct falseWaitReturn (falseWaitReadableSourceMemoryWord left) *ᵥ
          falseWaitSeparatorColumn =
        scale •
          (wordProduct falseWaitReturn (falseWaitReadableSourceMemoryWord right) *ᵥ
            falseWaitSeparatorColumn)) :
    left = right := by
  let returnProduct :=
    wordProduct falseWaitReturn falseWaitFreeSourceReturnWord
  have returnUnit : IsUnit returnProduct :=
    falseWaitReturn_wordProduct_isUnit_of_positive _
      falseWaitFreeSourceReturnWord_positive
  rw [falseWaitReadableSourceMemoryWord_source_factor,
    falseWaitReadableSourceMemoryWord_source_factor,
    ← Matrix.mulVec_smul] at projective_eq
  have afterReturn := (Matrix.mulVec_injective_of_isUnit returnUnit) projective_eq
  exact falseWaitOneProbeWord_source_projectively_injective afterReturn

end MatrixMortality.CubicReturn.NonPure
