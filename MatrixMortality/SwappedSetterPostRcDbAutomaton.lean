import MatrixMortality.SwappedSetterEmptyFrontChamber
import MatrixMortality.SwappedSetterDeletionCContraction

set_option autoImplicit false

/-!
# Post-`R_c;D_b` intercept automaton

The canonical empty-front backward ray can cross the singleton-`D_c` contraction chamber
through the literal block `R_c;D_b`.  After that contraction, the apparent real-height gap
around one is not uniformly large, but the physical spelling still leaves a narrower forbidden
band. This module records the exact post-contraction intercept and the affine automaton carried
by every subsequent physical upper spelling.

The result is conditional on the literal canonical `R_c;D_b` pullback followed by `D_c`.  It
does not prove that this block is forced, that the displayed backward ray is reachable from the
encoded entry, or that any target is a pole.
-/

namespace MatrixMortality.SwappedSetterPostRcDbChamber

open SwappedSetterMultitransfer SwappedSetterThresholdCarry
  SwappedSetterEmptyFrontRay SwappedSetterEmptyFrontChamber

private def seedEightGapCore (scale upperPrefix : ℤ) : ℤ :=
  (2430 * scale ^ 7 - 19926 * scale ^ 6 + 18495 * scale ^ 5 -
      5535 * scale ^ 4 + 948 * scale ^ 3 - 24 * scale ^ 2 -
      8 * scale) * upperPrefix -
    1944 * scale ^ 6 - 46980 * scale ^ 5 + 30240 * scale ^ 4 -
      6138 * scale ^ 3 + 570 * scale ^ 2 - 52 * scale + 4

private theorem seedEightGapCore_pos
    {scale upperPrefix : ℤ} (scale_large : 243 ≤ scale)
    (prefix_lower : 9 * scale ≤ 2 * upperPrefix + 1) :
    0 < seedEightGapCore scale upperPrefix := by
  let shifted := scale - 243
  let coefficient :=
    2430 * scale ^ 7 - 19926 * scale ^ 6 + 18495 * scale ^ 5 -
      5535 * scale ^ 4 + 948 * scale ^ 3 - 24 * scale ^ 2 -
      8 * scale
  let minimum :=
    21870 * shifted ^ 8 + 42333516 * shifted ^ 7 +
      35850247569 * shifted ^ 6 + 17348266662408 * shifted ^ 5 +
      5246795667226572 * shifted ^ 4 + 1015561565717150184 * shifted ^ 3 +
      122854877195152259793 * shifted ^ 2 +
      8492478881097612563364 * shifted + 256831646286783676488524
  have shifted_nonneg : 0 ≤ shifted := by
    simp only [shifted]
    omega
  have coefficient_pos : 0 < coefficient := by
    have expansion : coefficient =
        2430 * shifted ^ 7 + 4113504 * shifted ^ 6 +
          2984236857 * shifted ^ 5 + 1202747850630 * shifted ^ 4 +
          290843602620888 * shifted ^ 3 + 42197624620284828 * shifted ^ 2 +
          3401231842810017361 * shifted + 117489719209532645502 := by
      simp only [coefficient, shifted]
      ring
    rw [expansion]
    positivity
  have minimum_pos : 0 < minimum := by
    simp only [minimum]
    positivity
  have gap_nonneg : 0 ≤ 2 * upperPrefix - 9 * scale + 1 := by omega
  have decomposition :
      2 * seedEightGapCore scale upperPrefix =
        coefficient * (2 * upperPrefix - 9 * scale + 1) + minimum := by
    simp only [seedEightGapCore, coefficient, minimum, shifted]
    ring
  have product_nonneg :
      0 ≤ coefficient * (2 * upperPrefix - 9 * scale + 1) :=
    mul_nonneg coefficient_pos.le gap_nonneg
  nlinarith

/-- Every width-at-least-six empty-front `D_b` antecedent lies above `8ρ²`. -/
theorem emptyFrontSeed_gt_eight_widthScale_sq
    {offset : Nat} (offset_five : 5 ≤ offset) {upperPrefix : ℤ}
    (prefix_lower :
      (3 : ℤ) ^ (offset + 2) ≤ 2 * upperPrefix + 1) :
    (8 * widthScale (offset + 1) ^ 2 : ℚ) <
      emptyFrontSeed offset upperPrefix := by
  let scale : ℤ := 3 ^ offset
  have scale_large : 243 ≤ scale := by
    have power_bound : 3 ^ 5 ≤ 3 ^ offset :=
      Nat.pow_le_pow_right (by norm_num) offset_five
    have power_bound_int : (243 : ℤ) ≤ (3 : ℤ) ^ offset := by
      norm_num at power_bound
      exact_mod_cast power_bound
    simpa only [scale] using power_bound_int
  have scale_three : 3 ≤ scale := by omega
  have prefix_lower' : 9 * scale ≤ 2 * upperPrefix + 1 := by
    simpa [scale, pow_add, mul_comm, mul_left_comm, mul_assoc] using prefix_lower
  have denominator_core_pos :=
    emptyFrontSeedDenominatorCore_pos scale_three prefix_lower'
  have gap_core_pos := seedEightGapCore_pos scale_large prefix_lower'
  have head_pos : 0 < terminalDiscrepancy (offset + 1) := by
    simp only [terminalDiscrepancy, widthScale, pow_succ]
    have power_pos : (0 : ℤ) < 3 ^ offset := by positivity
    nlinarith
  have width_scale_eq : widthScale (offset + 1) = 3 * scale := by
    simp only [widthScale, scale, pow_succ]
    ring
  have denominator_eq :
      deletionBInverseDenominator offset upperPrefix =
        -2 * terminalDiscrepancy (offset + 1) *
          emptyFrontSeedDenominatorCore scale upperPrefix := by
    simp only [deletionBInverseDenominator, setterMarker,
      secondDeletionInverseNumerator, firstDeletionInverseNumerator,
      firstDeletionInverseDenominator, firstDeletionResidual,
      secondDeletionGapCore, terminalDiscrepancy, centeredCoefficient,
      width_scale_eq]
    simp only [emptyFrontSeedDenominatorCore]
    ring
  have eight_gap_eq :
      deletionBInverseNumerator offset upperPrefix -
          8 * widthScale (offset + 1) ^ 2 *
            deletionBInverseDenominator offset upperPrefix =
        -terminalDiscrepancy (offset + 1) *
          seedEightGapCore scale upperPrefix := by
    simp only [deletionBInverseNumerator, deletionBCofactor,
      deletionBInverseDenominator, setterMarker,
      secondDeletionInverseNumerator, firstDeletionInverseNumerator,
      firstDeletionInverseDenominator, firstDeletionResidual,
      secondDeletionGapCore, terminalDiscrepancy, centeredCoefficient,
      width_scale_eq]
    simp only [seedEightGapCore]
    ring
  have denominator_neg :
      deletionBInverseDenominator offset upperPrefix < 0 := by
    rw [denominator_eq]
    nlinarith
  have eight_gap_neg :
      deletionBInverseNumerator offset upperPrefix -
          8 * widthScale (offset + 1) ^ 2 *
            deletionBInverseDenominator offset upperPrefix < 0 := by
    rw [eight_gap_eq]
    nlinarith
  have denominator_neg_rat :
      (deletionBInverseDenominator offset upperPrefix : ℚ) < 0 := by
    exact_mod_cast denominator_neg
  unfold emptyFrontSeed
  apply (lt_div_iff_of_neg denominator_neg_rat).2
  exact_mod_cast (by nlinarith [eight_gap_neg] :
    deletionBInverseNumerator offset upperPrefix <
      8 * widthScale (offset + 1) ^ 2 *
        deletionBInverseDenominator offset upperPrefix)

/-! ## The exact post-contraction intercept -/

/-- Scale quotient `3^(width-6)` used to align the post-contraction numerator with the lower
spelling. -/
def chamberQuotient (width : Nat) : ℤ :=
  3 ^ (width - 6)

/-- Carrier after pulling the canonical `R_c;D_b` image through singleton `D_c`. -/
def postRcDbCarrier (width : Nat) (seed : ℚ) : ℚ :=
  let image := canonicalRcDbBackward width seed
  deletionCSuccessorSlope width ((image - 1) / image)

/-- Boundary intercept left for the upper spelling after the canonical `R_c;D_b,D_c`
pullback. -/
def postRcDbIntercept (width : Nat) (seed : ℚ) : ℚ :=
  setterMarker width * chamberRadius width * postRcDbCarrier width seed /
    (terminalDiscrepancy width + chamberRadius width * postRcDbCarrier width seed)

/-- Positive affine denominator of the canonical `R_c;D_b` pullback. -/
def rcDbTime (width : Nat) (seed : ℚ) : ℚ :=
  terminalDiscrepancy width + chamberRadius width * seed

/-- Doubled numerator-minus-denominator gap of the canonical `R_c;D_b` pullback. -/
def rcDbGap (width : Nat) (seed : ℚ) : ℚ :=
  (widthScale width - 9) * rcDbTime width seed -
    54 * widthScale width * terminalDiscrepancy width * setterMarker width

/-- Doubled lower code of the canonical `R_c;D_b` block. -/
def rcDbLowerDouble (width : Nat) : ℚ :=
  90 * widthScale width ^ 2 - 9 * widthScale width + 7

/-- Denominator of the closed post-`D_c` intercept. -/
def postRcDbInterceptDenominator (width : Nat) (seed : ℚ) : ℚ :=
  (chamberRadius width ^ 2 + 2 * chamberRadius width) * rcDbGap width seed +
    6 * setterMarker width * rcDbLowerDouble width * rcDbTime width seed

/-- Closed rational form of the post-`D_c` boundary intercept. -/
def closedPostRcDbIntercept (width : Nat) (seed : ℚ) : ℚ :=
  setterMarker width * chamberRadius width ^ 2 * rcDbGap width seed /
    postRcDbInterceptDenominator width seed

/-- Width scale factored at the width-six chamber base. -/
theorem widthScale_eq_729_mul_chamberQuotient
    {width : Nat} (width_large : 6 ≤ width) :
    widthScale width = 729 * chamberQuotient width := by
  have width_eq : width = (width - 6) + 6 := by omega
  change (3 : ℤ) ^ width = 729 * 3 ^ (width - 6)
  rw [width_eq, pow_add]
  norm_num
  ring

/-- The width-shift chamber quotient is positive. -/
theorem chamberQuotient_pos (width : Nat) :
    (0 : ℤ) < chamberQuotient width := by
  simp [chamberQuotient]

private theorem rcDbLowerDouble_pos
    {width : Nat} (width_two : 2 ≤ width) :
    (0 : ℚ) < rcDbLowerDouble width := by
  have scale_nine : (9 : ℚ) ≤ widthScale width := by
    have power_bound : 3 ^ 2 ≤ 3 ^ width :=
      Nat.pow_le_pow_right (by norm_num) width_two
    norm_num [widthScale] at power_bound ⊢
    exact_mod_cast power_bound
  simp only [rcDbLowerDouble]
  nlinarith [sq_nonneg ((widthScale width : ℚ) - 1)]

private theorem backwardBlock_eq_over_time
    {width : Nat} {punctuated lower power current : ℚ}
    (lower_ne : lower ≠ 0) (time_ne : rcDbTime width current ≠ 0) :
    backwardBlock width punctuated lower power current =
      (punctuated * rcDbTime width current -
          terminalDiscrepancy width * setterMarker width * power) /
        (lower * rcDbTime width current) := by
  have centered_cast :
      (centeredCoefficient width : ℚ) = 2 - widthScale width := by
    simp [centeredCoefficient]
  have radius_cast :
      (chamberRadius width : ℚ) = widthScale width - 2 := by
    simp [chamberRadius]
  have denominator_eq :
      (centeredCoefficient width : ℚ) * current - terminalDiscrepancy width =
        -rcDbTime width current := by
    simp only [rcDbTime]
    rw [centered_cast, radius_cast]
    ring
  simp only [backwardBlock]
  rw [denominator_eq]
  field_simp [lower_ne, time_ne]
  ring

private theorem canonicalRcDbBackward_eq_one_add
    {width : Nat} (width_two : 2 ≤ width) {seed : ℚ}
    (time_ne : rcDbTime width seed ≠ 0) :
    canonicalRcDbBackward width seed =
      1 + rcDbGap width seed /
        (rcDbLowerDouble width * rcDbTime width seed) := by
  have lower_formula := canonicalRcDb_lowerCode width_two
  have upper_formula := canonicalRcDb_upperCode width
  have power_formula := canonicalRcDb_upperPower width
  have lower_formula_rat :
      (swappedLowerCode width (canonicalRcDbBody width)
          [.rule .c, .erase .b] : ℚ) =
        rcDbLowerDouble width / 2 := by
    apply (eq_div_iff (by norm_num : (2 : ℚ) ≠ 0)).2
    have lower_cast :
        (2 : ℚ) * swappedLowerCode width (canonicalRcDbBody width)
            [.rule .c, .erase .b] =
          90 * widthScale width ^ 2 - 9 * widthScale width + 7 := by
      exact_mod_cast lower_formula
    simpa only [rcDbLowerDouble, mul_comm] using lower_cast
  have upper_formula_rat :
      (swappedUpperCode width [.rule .c, .erase .b] : ℚ) =
        45 * widthScale width ^ 2 - 4 * widthScale width - 1 := by
    exact_mod_cast upper_formula
  have power_formula_rat :
      (upperPower width [.rule .c, .erase .b] : ℚ) =
        27 * widthScale width := by
    exact_mod_cast power_formula
  have lower_double_ne : rcDbLowerDouble width ≠ 0 :=
    (rcDbLowerDouble_pos width_two).ne'
  have lower_ne :
      (swappedLowerCode width (canonicalRcDbBody width)
        [.rule .c, .erase .b] : ℚ) ≠ 0 := by
    rw [lower_formula_rat]
    exact div_ne_zero lower_double_ne (by norm_num)
  simp only [canonicalRcDbBackward]
  rw [backwardBlock_eq_over_time lower_ne time_ne]
  rw [lower_formula_rat, upper_formula_rat, power_formula_rat]
  simp only [rcDbGap]
  field_simp [time_ne, lower_double_ne]
  simp only [rcDbLowerDouble]
  ring

private theorem intercept_of_carrier_eq
    {marker radius terminal gap carrierDenominator closedDenominator : ℚ}
    (carrier_denominator_ne : carrierDenominator ≠ 0)
    (intercept_denominator_ne :
      terminal + radius * (terminal * radius * gap / carrierDenominator) ≠ 0)
    (closed_denominator_ne : closedDenominator ≠ 0)
    (closed_denominator_eq :
      closedDenominator = carrierDenominator + radius ^ 2 * gap) :
    marker * radius * (terminal * radius * gap / carrierDenominator) /
        (terminal + radius * (terminal * radius * gap / carrierDenominator)) =
      marker * radius ^ 2 * gap / closedDenominator := by
  rw [closed_denominator_eq]
  have expanded_closed_ne :
      carrierDenominator + radius ^ 2 * gap ≠ 0 := by
    rwa [← closed_denominator_eq]
  have terminal_ne : terminal ≠ 0 := by
    intro terminal_zero
    rw [terminal_zero] at intercept_denominator_ne
    simp at intercept_denominator_ne
  field_simp [carrier_denominator_ne, intercept_denominator_ne,
    expanded_closed_ne, terminal_ne]

private theorem postRcDbCarrier_eq_closed
    {width : Nat} (width_two : 2 ≤ width) {seed : ℚ}
    (time_ne : rcDbTime width seed ≠ 0)
    (image_ne : canonicalRcDbBackward width seed ≠ 0) :
    postRcDbCarrier width seed =
      terminalDiscrepancy width * chamberRadius width * rcDbGap width seed /
        (2 * chamberRadius width * rcDbGap width seed +
          6 * setterMarker width * rcDbLowerDouble width *
            rcDbTime width seed) := by
  have lower_double_ne : rcDbLowerDouble width ≠ 0 :=
    (rcDbLowerDouble_pos width_two).ne'
  have time_product_ne :
      rcDbLowerDouble width * rcDbTime width seed ≠ 0 :=
    mul_ne_zero lower_double_ne time_ne
  have image_eq :
      canonicalRcDbBackward width seed =
        (rcDbGap width seed +
            rcDbLowerDouble width * rcDbTime width seed) /
          (rcDbLowerDouble width * rcDbTime width seed) := by
    rw [canonicalRcDbBackward_eq_one_add width_two time_ne]
    field_simp [time_product_ne]
    ring
  have numerator_ne :
      rcDbGap width seed + rcDbLowerDouble width * rcDbTime width seed ≠ 0 := by
    intro numerator_zero
    rw [image_eq, numerator_zero] at image_ne
    exact image_ne (zero_div _)
  have epsilon_eq :
      (canonicalRcDbBackward width seed - 1) /
          canonicalRcDbBackward width seed =
        rcDbGap width seed /
          (rcDbGap width seed +
            rcDbLowerDouble width * rcDbTime width seed) := by
    rw [image_eq]
    field_simp [time_product_ne, numerator_ne]
    ring
  simp only [postRcDbCarrier]
  rw [epsilon_eq]
  simp only [deletionCSuccessorSlope]
  field_simp [numerator_ne]
  ring

private theorem postRcDbIntercept_eq_closed
    {width : Nat} (width_two : 2 ≤ width) {seed : ℚ}
    (time_ne : rcDbTime width seed ≠ 0)
    (image_ne : canonicalRcDbBackward width seed ≠ 0)
    (carrier_closed_denominator_ne :
      2 * chamberRadius width * rcDbGap width seed +
          6 * setterMarker width * rcDbLowerDouble width *
            rcDbTime width seed ≠ 0)
    (intercept_denominator_ne :
      terminalDiscrepancy width +
          chamberRadius width * postRcDbCarrier width seed ≠ 0)
    (closed_denominator_ne : postRcDbInterceptDenominator width seed ≠ 0) :
    postRcDbIntercept width seed = closedPostRcDbIntercept width seed := by
  have carrier_eq :
      postRcDbCarrier width seed =
        terminalDiscrepancy width * chamberRadius width * rcDbGap width seed /
          (2 * chamberRadius width * rcDbGap width seed +
            6 * setterMarker width * rcDbLowerDouble width *
              rcDbTime width seed) := by
    exact postRcDbCarrier_eq_closed width_two time_ne image_ne
  rw [carrier_eq] at intercept_denominator_ne
  rw [postRcDbIntercept, carrier_eq, closedPostRcDbIntercept]
  apply intercept_of_carrier_eq carrier_closed_denominator_ne
    intercept_denominator_ne closed_denominator_ne
  simp only [postRcDbInterceptDenominator]
  ring

/-- Every width-at-least-six scale is at least `3^6`. -/
theorem widthScale_ge_729
    {width : Nat} (width_large : 6 ≤ width) :
    (729 : ℚ) ≤ widthScale width := by
  have power_bound : 3 ^ 6 ≤ 3 ^ width :=
    Nat.pow_le_pow_right (by norm_num) width_large
  norm_num [widthScale] at power_bound ⊢
  exact_mod_cast power_bound

private theorem rcDbTime_pos
    {width : Nat} (width_large : 6 ≤ width) {seed : ℚ}
    (seed_lower : (8 * widthScale width ^ 2 : ℚ) < seed) :
    0 < rcDbTime width seed := by
  have scale_large := widthScale_ge_729 width_large
  simp only [rcDbTime, terminalDiscrepancy, chamberRadius]
  push_cast
  nlinarith [sq_nonneg (widthScale width : ℚ)]

private theorem rcDbGap_pos
    {width : Nat} (width_large : 6 ≤ width) {seed : ℚ}
    (seed_lower : (8 * widthScale width ^ 2 : ℚ) < seed) :
    0 < rcDbGap width seed := by
  let ρ : ℚ := widthScale width
  let shifted := ρ - 729
  have scale_large : (729 : ℚ) ≤ ρ := by
    simpa only [ρ] using widthScale_ge_729 width_large
  have shifted_nonneg : 0 ≤ shifted := by
    simp only [shifted]
    linarith
  have base_polynomial_pos :
      0 < 8 * ρ ^ 4 - 628 * ρ ^ 3 + 527 * ρ ^ 2 - 100 * ρ + 9 := by
    have expansion :
        8 * ρ ^ 4 - 628 * ρ ^ 3 + 527 * ρ ^ 2 - 100 * ρ + 9 =
          8 * shifted ^ 4 + 22700 * shifted ^ 3 +
            24136259 * shifted ^ 2 + 11396989070 * shifted +
              2016416221272 := by
      simp only [shifted]
      ring
    rw [expansion]
    positivity
  have base_eq :
      (ρ - 9) * ((5 * ρ - 1) + (ρ - 2) * (8 * ρ ^ 2)) -
          54 * ρ * (5 * ρ - 1) * (2 * ρ - 1) =
        8 * ρ ^ 4 - 628 * ρ ^ 3 + 527 * ρ ^ 2 - 100 * ρ + 9 := by
    ring
  have coefficient_pos : 0 < ρ - 9 := by linarith
  simp only [rcDbGap, rcDbTime, terminalDiscrepancy, setterMarker,
    chamberRadius]
  push_cast
  change 0 <
    (ρ - 9) * ((5 * ρ - 1) + (ρ - 2) * seed) -
      54 * ρ * (5 * ρ - 1) * (2 * ρ - 1)
  rw [← base_eq] at base_polynomial_pos
  nlinarith [mul_pos coefficient_pos (sub_pos.mpr seed_lower)]

private theorem postRcDb_positive_data
    {width : Nat} (width_large : 6 ≤ width) {seed : ℚ}
    (seed_lower : (8 * widthScale width ^ 2 : ℚ) < seed) :
    0 < rcDbTime width seed ∧
      0 < rcDbGap width seed ∧
      0 < 2 * chamberRadius width * rcDbGap width seed +
        6 * setterMarker width * rcDbLowerDouble width * rcDbTime width seed ∧
      0 < postRcDbInterceptDenominator width seed := by
  have width_two : 2 ≤ width := by omega
  have scale_large := widthScale_ge_729 width_large
  have time_pos := rcDbTime_pos width_large seed_lower
  have gap_pos := rcDbGap_pos width_large seed_lower
  have lower_double_pos := rcDbLowerDouble_pos width_two
  have radius_pos : (0 : ℚ) < chamberRadius width := by
    simp only [chamberRadius]
    push_cast
    linarith
  have marker_pos : (0 : ℚ) < setterMarker width := by
    simp only [setterMarker]
    push_cast
    linarith
  have carrier_denominator_pos :
      0 < 2 * chamberRadius width * rcDbGap width seed +
        6 * setterMarker width * rcDbLowerDouble width * rcDbTime width seed := by
    positivity
  have intercept_denominator_pos :
      0 < postRcDbInterceptDenominator width seed := by
    simp only [postRcDbInterceptDenominator]
    positivity
  exact ⟨time_pos, gap_pos, carrier_denominator_pos, intercept_denominator_pos⟩

/-- The intercept obtained from the literal canonical `R_c;D_b` pullback and singleton
`D_c` contraction has the stated closed form. -/
theorem postRcDbIntercept_eq_closed_of_seed
    {width : Nat} (width_large : 6 ≤ width) {seed : ℚ}
    (seed_lower : (8 * widthScale width ^ 2 : ℚ) < seed) :
    postRcDbIntercept width seed = closedPostRcDbIntercept width seed := by
  have width_two : 2 ≤ width := by omega
  obtain ⟨time_pos, gap_pos, carrier_denominator_pos, closed_denominator_pos⟩ :=
    postRcDb_positive_data width_large seed_lower
  have image_above : 1 < canonicalRcDbBackward width seed := by
    rw [canonicalRcDbBackward_eq_one_add width_two time_pos.ne']
    have lower_double_pos := rcDbLowerDouble_pos width_two
    have quotient_pos :
        0 < rcDbGap width seed /
          (rcDbLowerDouble width * rcDbTime width seed) := by positivity
    linarith
  have carrier_pos : 0 < postRcDbCarrier width seed := by
    rw [postRcDbCarrier_eq_closed width_two time_pos.ne' (by linarith)]
    have scale_large := widthScale_ge_729 width_large
    have terminal_pos : (0 : ℚ) < terminalDiscrepancy width := by
      simp only [terminalDiscrepancy]
      push_cast
      linarith
    have radius_pos : (0 : ℚ) < chamberRadius width := by
      simp only [chamberRadius]
      push_cast
      linarith
    exact div_pos (mul_pos (mul_pos terminal_pos radius_pos) gap_pos)
      carrier_denominator_pos
  have scale_large := widthScale_ge_729 width_large
  have intercept_denominator_pos :
      0 < terminalDiscrepancy width +
        chamberRadius width * postRcDbCarrier width seed := by
    have terminal_pos : (0 : ℚ) < terminalDiscrepancy width := by
      simp only [terminalDiscrepancy]
      push_cast
      linarith
    have radius_pos : (0 : ℚ) < chamberRadius width := by
      simp only [chamberRadius]
      push_cast
      linarith
    positivity
  exact postRcDbIntercept_eq_closed width_two time_pos.ne' (by linarith)
    carrier_denominator_pos.ne' intercept_denominator_pos.ne'
    closed_denominator_pos.ne'

private theorem postRcDb_lower_cross_pos
    {width : Nat} (width_large : 6 ≤ width) {seed : ℚ}
    (seed_lower : (8 * widthScale width ^ 2 : ℚ) < seed) :
    0 < 5 * setterMarker width * chamberRadius width ^ 2 * rcDbGap width seed -
      6 * chamberQuotient width * postRcDbInterceptDenominator width seed := by
  let q : ℚ := chamberQuotient width
  let ρ : ℚ := widthScale width
  let shifted := q - 1
  have scale_eq : ρ = 729 * q := by
    have integer_eq := widthScale_eq_729_mul_chamberQuotient width_large
    simp only [ρ, q]
    exact_mod_cast integer_eq
  have q_pos : 0 < q := by
    simp only [q]
    exact_mod_cast chamberQuotient_pos width
  have q_one : 1 ≤ q := by
    have q_int_pos := chamberQuotient_pos width
    have q_int_one : (1 : ℤ) ≤ chamberQuotient width := by omega
    simp only [q]
    exact_mod_cast q_int_one
  have shifted_nonneg : 0 ≤ shifted := by
    simp only [shifted]
    linarith
  let coefficientCore : ℚ :=
    34609563684 * q ^ 4 - 5577827589 * q ^ 3 +
      27381969 * q ^ 2 - 45332 * q + 20
  have coefficientCore_pos : 0 < coefficientCore := by
    have expansion : coefficientCore =
        34609563684 * shifted ^ 4 + 132860427147 * shifted ^ 3 +
          190951281306 * shifted ^ 2 + 121759490575 * shifted +
            29059072752 := by
      simp only [coefficientCore, shifted]
      ring
    rw [expansion]
    positivity
  let baseCore : ℚ :=
    107267632692255371808 * q ^ 7 -
      107564664965490585432 * q ^ 6 +
      774527229391188240 * q ^ 5 - 1960971292187127 * q ^ 4 +
      2098602404784 * q ^ 3 - 1000407429 * q ^ 2 +
      205712 * q - 20
  have baseCore_pos : 0 < baseCore := by
    have expansion : baseCore =
        107267632692255371808 * shifted ^ 7 +
          643308763880297017224 * shifted ^ 6 +
          1608006823973810483616 * shifted ^ 5 +
          2144767844922242985873 * shifted ^ 4 +
          1610811275426471843316 * shifted ^ 3 +
          646883824815969593049 * shifted ^ 2 +
          109350237608437887962 * shifted + 475536082465990536 := by
      simp only [baseCore, shifted]
      ring
    rw [expansion]
    positivity
  have seed_gap_pos : 0 < seed - 8 * ρ ^ 2 := by
    simpa only [ρ] using sub_pos.mpr seed_lower
  have scale_minus_two_pos : 0 < 729 * q - 2 := by linarith
  have coefficient_pos :
      0 < 9 * (729 * q - 2) * coefficientCore := by positivity
  have decomposition :
      5 * (2 * ρ - 1) * (ρ - 2) ^ 2 *
            ((ρ - 9) * ((5 * ρ - 1) + (ρ - 2) * seed) -
              54 * ρ * (5 * ρ - 1) * (2 * ρ - 1)) -
          6 * q *
            (((ρ - 2) ^ 2 + 2 * (ρ - 2)) *
                ((ρ - 9) * ((5 * ρ - 1) + (ρ - 2) * seed) -
                  54 * ρ * (5 * ρ - 1) * (2 * ρ - 1)) +
              6 * (2 * ρ - 1) *
                (90 * ρ ^ 2 - 9 * ρ + 7) *
                  ((5 * ρ - 1) + (ρ - 2) * seed)) =
        9 * (729 * q - 2) * coefficientCore * (seed - 8 * ρ ^ 2) +
          9 * baseCore := by
    simp only [coefficientCore, baseCore]
    rw [scale_eq]
    ring
  have cross_pos :
      0 < 5 * (2 * ρ - 1) * (ρ - 2) ^ 2 *
            ((ρ - 9) * ((5 * ρ - 1) + (ρ - 2) * seed) -
              54 * ρ * (5 * ρ - 1) * (2 * ρ - 1)) -
          6 * q *
            (((ρ - 2) ^ 2 + 2 * (ρ - 2)) *
                ((ρ - 9) * ((5 * ρ - 1) + (ρ - 2) * seed) -
                  54 * ρ * (5 * ρ - 1) * (2 * ρ - 1)) +
              6 * (2 * ρ - 1) *
                (90 * ρ ^ 2 - 9 * ρ + 7) *
                  ((5 * ρ - 1) + (ρ - 2) * seed)) := by
    rw [decomposition]
    positivity
  simp only [postRcDbInterceptDenominator, rcDbGap, rcDbTime,
    rcDbLowerDouble, terminalDiscrepancy, setterMarker, chamberRadius]
  push_cast
  change 0 < 5 * (2 * ρ - 1) * (ρ - 2) ^ 2 *
            ((ρ - 9) * ((5 * ρ - 1) + (ρ - 2) * seed) -
              54 * ρ * (5 * ρ - 1) * (2 * ρ - 1)) -
          6 * q *
            (((ρ - 2) ^ 2 + 2 * (ρ - 2)) *
                ((ρ - 9) * ((5 * ρ - 1) + (ρ - 2) * seed) -
                  54 * ρ * (5 * ρ - 1) * (2 * ρ - 1)) +
              6 * (2 * ρ - 1) *
                (90 * ρ ^ 2 - 9 * ρ + 7) *
                  ((5 * ρ - 1) + (ρ - 2) * seed))
  exact cross_pos

/-- The canonical post-`D_c` intercept is uniformly above `6·3^(width-6)/5`. -/
theorem six_fifths_chamberQuotient_lt_postRcDbIntercept
    {width : Nat} (width_large : 6 ≤ width) {seed : ℚ}
    (seed_lower : (8 * widthScale width ^ 2 : ℚ) < seed) :
    (6 : ℚ) * chamberQuotient width / 5 < postRcDbIntercept width seed := by
  rw [postRcDbIntercept_eq_closed_of_seed width_large seed_lower,
    closedPostRcDbIntercept]
  have denominator_pos :=
    (postRcDb_positive_data width_large seed_lower).2.2.2
  apply (lt_div_iff₀ denominator_pos).2
  have cross_pos := postRcDb_lower_cross_pos width_large seed_lower
  nlinarith

/-- Seed-independent upper envelope for the canonical post-contraction intercept. -/
def postRcDbCeiling (width : Nat) : ℚ :=
  setterMarker width * chamberRadius width ^ 2 * (widthScale width - 9) /
    (((chamberRadius width ^ 2 + 2 * chamberRadius width) *
        (widthScale width - 9)) +
      6 * setterMarker width * rcDbLowerDouble width)

private theorem postRcDbIntercept_lt_ceiling
    {width : Nat} (width_large : 6 ≤ width) {seed : ℚ}
    (seed_lower : (8 * widthScale width ^ 2 : ℚ) < seed) :
    postRcDbIntercept width seed < postRcDbCeiling width := by
  have width_two : 2 ≤ width := by omega
  have scale_large := widthScale_ge_729 width_large
  have scale_pos : (0 : ℚ) < widthScale width := by linarith
  have terminal_pos : (0 : ℚ) < terminalDiscrepancy width := by
    simp only [terminalDiscrepancy]
    push_cast
    linarith
  have marker_pos : (0 : ℚ) < setterMarker width := by
    simp only [setterMarker]
    push_cast
    linarith
  have radius_pos : (0 : ℚ) < chamberRadius width := by
    simp only [chamberRadius]
    push_cast
    linarith
  have scale_minus_nine_pos : (0 : ℚ) < widthScale width - 9 := by linarith
  have lower_double_pos := rcDbLowerDouble_pos width_two
  obtain ⟨time_pos, gap_pos, _, denominator_pos⟩ :=
    postRcDb_positive_data width_large seed_lower
  have gap_upper :
      rcDbGap width seed < (widthScale width - 9) * rcDbTime width seed := by
    simp only [rcDbGap]
    nlinarith [mul_pos
      (mul_pos (mul_pos (by positivity : (0 : ℚ) < 54) scale_pos) terminal_pos)
      marker_pos]
  let ceilingDenominator : ℚ :=
    (chamberRadius width ^ 2 + 2 * chamberRadius width) *
        (widthScale width - 9) +
      6 * setterMarker width * rcDbLowerDouble width
  have ceiling_denominator_pos : 0 < ceilingDenominator := by
    simp only [ceilingDenominator]
    positivity
  rw [postRcDbIntercept_eq_closed_of_seed width_large seed_lower,
    closedPostRcDbIntercept, postRcDbCeiling]
  apply (div_lt_div_iff₀ denominator_pos ceiling_denominator_pos).2
  have difference_eq :
      setterMarker width * chamberRadius width ^ 2 *
            (widthScale width - 9) * postRcDbInterceptDenominator width seed -
          setterMarker width * chamberRadius width ^ 2 * rcDbGap width seed *
            ceilingDenominator =
        setterMarker width * chamberRadius width ^ 2 *
          (6 * setterMarker width * rcDbLowerDouble width) *
            ((widthScale width - 9) * rcDbTime width seed -
              rcDbGap width seed) := by
    simp only [postRcDbInterceptDenominator, ceilingDenominator]
    ring
  have difference_pos :
      0 < setterMarker width * chamberRadius width ^ 2 *
          (6 * setterMarker width * rcDbLowerDouble width) *
            ((widthScale width - 9) * rcDbTime width seed -
              rcDbGap width seed) := by positivity
  nlinarith [difference_eq, difference_pos]

/-- The chamber quotient is at least three from width seven onward. -/
theorem chamberQuotient_ge_three
    {width : Nat} (width_seven : 7 ≤ width) :
    (3 : ℚ) ≤ chamberQuotient width := by
  have exponent_pos : 0 < width - 6 := by omega
  obtain ⟨predecessor, exponent_eq⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt exponent_pos)
  have quotient_bound_int : (3 : ℤ) ≤ chamberQuotient width := by
    simp only [chamberQuotient, exponent_eq, pow_succ]
    have power_pos : (0 : ℤ) < 3 ^ predecessor := by positivity
    nlinarith
  exact_mod_cast quotient_bound_int

private theorem postRcDbCeiling_lt_sevenPlus_cap
    {width : Nat} (width_seven : 7 ≤ width) :
    postRcDbCeiling width <
      14 * chamberQuotient width / 9 -
        terminalDiscrepancy width / (9 * widthScale width - 1) := by
  let q : ℚ := chamberQuotient width
  let ρ : ℚ := widthScale width
  let shifted := q - 3
  have scale_eq : ρ = 729 * q := by
    have integer_eq := widthScale_eq_729_mul_chamberQuotient (by omega : 6 ≤ width)
    simp only [ρ, q]
    exact_mod_cast integer_eq
  have q_three : 3 ≤ q := by
    simpa only [q] using chamberQuotient_ge_three width_seven
  have shifted_nonneg : 0 ≤ shifted := by
    simp only [shifted]
    linarith
  let denominatorCore : ℚ :=
    139600516203 * q ^ 3 - 116739873 * q ^ 2 + 37908 * q - 14
  have denominatorCore_pos : 0 < denominatorCore := by
    have expansion : denominatorCore =
        139600516203 * shifted ^ 3 + 1256287905954 * shifted ^ 2 +
          3768513536151 * shifted + 3768163392334 := by
      simp only [denominatorCore, shifted]
      ring
    rw [expansion]
    positivity
  let gapCore : ℚ :=
    852372341099658 * q ^ 5 - 2192343328123632 * q ^ 4 +
      2043489315879 * q ^ 3 - 270348921 * q ^ 2 - 76447 * q - 9
  have gapCore_pos : 0 < gapCore := by
    have expansion : gapCore =
        852372341099658 * shifted ^ 5 + 10593241788371238 * shifted ^ 4 +
          50407434250801515 * shifted ^ 3 +
          111772383511725522 * shifted ^ 2 +
          108492891297367994 * shifted + 29601841087361796 := by
      simp only [gapCore, shifted]
      ring
    rw [expansion]
    positivity
  let outerDenominator : ℚ := 6561 * q - 1
  have outer_denominator_pos : 0 < outerDenominator := by
    simp only [outerDenominator]
    linarith
  have ceiling_denominator_eq :
      ((ρ - 2) ^ 2 + 2 * (ρ - 2)) * (ρ - 9) +
          6 * (2 * ρ - 1) * (90 * ρ ^ 2 - 9 * ρ + 7) =
        3 * denominatorCore := by
    simp only [denominatorCore]
    rw [scale_eq]
    ring
  have rational_identity :
      14 * q / 9 - (3645 * q - 1) / outerDenominator -
          ((1458 * q - 1) * (729 * q - 2) ^ 2 * (729 * q - 9) /
            (3 * denominatorCore)) =
        2 * gapCore / (9 * outerDenominator * denominatorCore) := by
    field_simp [outer_denominator_pos.ne', denominatorCore_pos.ne']
    simp only [outerDenominator, gapCore, denominatorCore]
    ring
  have gap_identity :
      14 * q / 9 - (5 * ρ - 1) / (9 * ρ - 1) -
          ((2 * ρ - 1) * (ρ - 2) ^ 2 * (ρ - 9) /
            (((ρ - 2) ^ 2 + 2 * (ρ - 2)) * (ρ - 9) +
              6 * (2 * ρ - 1) * (90 * ρ ^ 2 - 9 * ρ + 7))) =
        2 * gapCore / (9 * outerDenominator * denominatorCore) := by
    rw [ceiling_denominator_eq, scale_eq]
    convert rational_identity using 1
    ring
  have gap_pos :
      0 < 2 * gapCore / (9 * outerDenominator * denominatorCore) := by positivity
  simp only [postRcDbCeiling, terminalDiscrepancy, setterMarker,
    chamberRadius, rcDbLowerDouble]
  push_cast
  change
    (2 * ρ - 1) * (ρ - 2) ^ 2 * (ρ - 9) /
          (((ρ - 2) ^ 2 + 2 * (ρ - 2)) * (ρ - 9) +
            6 * (2 * ρ - 1) * (90 * ρ ^ 2 - 9 * ρ + 7)) <
      14 * q / 9 - (5 * ρ - 1) / (9 * ρ - 1)
  rw [← sub_pos]
  rw [gap_identity]
  exact gap_pos

private theorem postRcDbCeiling_width_six :
    postRcDbCeiling 6 <
      2 - terminalDiscrepancy 6 / (9 * widthScale 6 - 1) := by
  norm_num [postRcDbCeiling, terminalDiscrepancy, setterMarker,
    chamberRadius, rcDbLowerDouble, widthScale]

/-- The canonical post-contraction intercept has the width-six ceiling needed by the
critical `R_b` spelling, and a stronger quotient-scaled ceiling from width seven onward. -/
theorem postRcDbIntercept_upper
    {width : Nat} (width_large : 6 ≤ width) {seed : ℚ}
    (seed_lower : (8 * widthScale width ^ 2 : ℚ) < seed) :
    (width = 6 ∧ postRcDbIntercept width seed <
        2 - terminalDiscrepancy width / (9 * widthScale width - 1)) ∨
      (7 ≤ width ∧ postRcDbIntercept width seed <
        14 * chamberQuotient width / 9 -
          terminalDiscrepancy width / (9 * widthScale width - 1)) := by
  have below_ceiling := postRcDbIntercept_lt_ceiling width_large seed_lower
  rcases eq_or_lt_of_le width_large with width_eq | width_seven
  · subst width
    exact Or.inl ⟨rfl, below_ceiling.trans postRcDbCeiling_width_six⟩
  · exact Or.inr ⟨width_seven,
      below_ceiling.trans (postRcDbCeiling_lt_sevenPlus_cap width_seven)⟩

/-! ## The post-contraction affine automaton -/

/-- Affine numerator update contributed by one physical role letter. -/
def advanceIntercept (width : Nat) (letter : TagLetter) (intercept : ℚ) : ℚ :=
  match letter with
  | .b => 9 * widthScale width * intercept + terminalDiscrepancy width
  | .c => 3 * intercept - chamberRadius width

/-- Upper spelling scale traversed by a physical block. -/
def interceptPower (width : Nat) : List NearyTile → ℚ
  | [] => 1
  | tile :: rest =>
      (match tile.letter with
        | .b => 9 * widthScale width
        | .c => 3) * interceptPower width rest

/-- Final affine numerator obtained by traversing a physical block. -/
def walkIntercept (width : Nat) : List NearyTile → ℚ → ℚ
  | [], intercept => intercept
  | tile :: rest, intercept =>
      walkIntercept width rest (advanceIntercept width tile.letter intercept)

/-- Upper-code numerator after replacing the marker-ray intercept by `intercept`. -/
def carriedUpper (width : Nat) (block : List NearyTile) (intercept : ℚ) : ℚ :=
  swappedUpperCode width block -
    setterMarker width * upperPower width block +
      intercept * upperPower width block

/-- Fixed margin preserved by every `b`-update. -/
def interceptMargin (width : Nat) : ℚ :=
  terminalDiscrepancy width / (9 * widthScale width - 1)

/-- The affine `b`-update fixed margin is positive from width six onward. -/
theorem interceptMargin_pos
    {width : Nat} (width_large : 6 ≤ width) :
    0 < interceptMargin width := by
  have scale_large := widthScale_ge_729 width_large
  have terminal_pos : (0 : ℚ) < terminalDiscrepancy width := by
    simp only [terminalDiscrepancy]
    push_cast
    linarith
  have denominator_pos : (0 : ℚ) < 9 * widthScale width - 1 := by linarith
  exact div_pos terminal_pos denominator_pos

private theorem interceptMargin_fixed
    {width : Nat} (width_large : 6 ≤ width) :
    9 * widthScale width * interceptMargin width - terminalDiscrepancy width =
      interceptMargin width := by
  have scale_large := widthScale_ge_729 width_large
  have denominator_pos : (0 : ℚ) < 9 * widthScale width - 1 := by linarith
  simp only [interceptMargin]
  field_simp [denominator_pos.ne']
  ring

private theorem upperLength_cons (width : Nat) (tile : NearyTile)
    (rest : List NearyTile) :
    upperLength width (tile :: rest) =
      (match tile.letter with | .b => width + 2 | .c => 1) +
        upperLength width rest := by
  rw [upperLength, upperLength, spell_nearyUpper, spell_nearyUpper]
  simp only [List.map_cons]
  rw [tagEncode_cons, List.length_append]
  cases tile.letter <;> simp [tagCode]

private theorem upperPower_cons (width : Nat) (tile : NearyTile)
    (rest : List NearyTile) :
    upperPower width (tile :: rest) =
      (match tile.letter with
        | .b => 9 * widthScale width
        | .c => 3) * upperPower width rest := by
  rw [upperPower, upperPower, upperLength_cons, pow_add]
  cases tile.letter
  · norm_num [widthScale, pow_add, pow_succ]
    ring
  · norm_num [widthScale, pow_add, pow_succ]

private theorem swappedUpperCode_cons (width : Nat) (tile : NearyTile)
    (rest : List NearyTile) :
    swappedUpperCode width (tile :: rest) =
      (3 : ℤ) ^ (upperLength width rest + width + 1) *
          ternaryCode ((tagCode width tile.letter).map not) +
        swappedUpperCode width rest := by
  rw [swappedUpperCode, swappedUpperCode, spell_nearyUpper, spell_nearyUpper]
  simp only [List.map_cons, tagEncode_cons]
  rw [List.append_assoc, List.map_append, ternaryCode_append, List.length_map]
  push_cast
  simp only [List.length_append, nearyMarker, List.length_cons,
    List.length_replicate, upperLength, spell_nearyUpper]
  ring

private theorem swappedUpperCode_cons_c (width : Nat) {tile : NearyTile}
    (tile_c : tile.letter = .c) (rest : List NearyTile) :
    swappedUpperCode width (tile :: rest) =
      3 * widthScale width * upperPower width rest +
        swappedUpperCode width rest := by
  rw [swappedUpperCode_cons, tile_c]
  norm_num [tagCode, ternaryCode, ternaryDigit, upperPower, widthScale,
    pow_add, pow_succ]
  ring

private theorem swappedUpperCode_cons_b (width : Nat) {tile : NearyTile}
    (tile_b : tile.letter = .b) (rest : List NearyTile) :
    swappedUpperCode width (tile :: rest) =
      3 * widthScale width * (6 * widthScale width - 2) *
          upperPower width rest + swappedUpperCode width rest := by
  rw [swappedUpperCode_cons, tile_b]
  have tag_eq :
      (ternaryCode ((tagCode width .b).map not) : ℤ) =
        6 * widthScale width - 2 := by
    have power_pos : 0 < 3 ^ width := pow_pos (by omega) width
    have two_le : 2 ≤ 6 * 3 ^ width := by omega
    calc
      (ternaryCode ((tagCode width .b).map not) : ℤ) =
          ((6 * 3 ^ width - 2 : Nat) : ℤ) := by
            exact_mod_cast swappedCode_tagCode_b width
      _ = 6 * (3 : ℤ) ^ width - 2 := by
        rw [Nat.cast_sub two_le]
        norm_num
      _ = 6 * widthScale width - 2 := by rw [widthScale]
  rw [tag_eq]
  norm_num [upperPower, widthScale, pow_add, pow_succ]
  ring

private theorem swappedUpperCode_nil (width : Nat) :
    swappedUpperCode width [] = setterMarker width := by
  have natural_eq := swappedCode_nearyMarker width
  have power_pos : 0 < 3 ^ width := pow_pos (by omega) width
  have one_le : 1 ≤ 2 * 3 ^ width := by omega
  rw [swappedUpperCode]
  change (ternaryCode ((nearyMarker width).map not) : ℤ) = setterMarker width
  calc
    (ternaryCode ((nearyMarker width).map not) : ℤ) =
        ((2 * 3 ^ width - 1 : Nat) : ℤ) := by exact_mod_cast natural_eq
    _ = 2 * (3 : ℤ) ^ width - 1 := by
      rw [Nat.cast_sub one_le]
      norm_num
    _ = setterMarker width := by rw [setterMarker, widthScale]

private theorem carriedUpper_cons (width : Nat) (tile : NearyTile)
    (rest : List NearyTile) (intercept : ℚ) :
    carriedUpper width (tile :: rest) intercept =
      carriedUpper width rest
        (advanceIntercept width tile.letter intercept) := by
  cases letter_eq : tile.letter with
  | c =>
      simp only [carriedUpper, advanceIntercept]
      rw [swappedUpperCode_cons_c width letter_eq, upperPower_cons, letter_eq]
      push_cast
      simp only [setterMarker, chamberRadius]
      push_cast
      ring
  | b =>
      simp only [carriedUpper, advanceIntercept]
      rw [swappedUpperCode_cons_b width letter_eq, upperPower_cons, letter_eq]
      push_cast
      simp only [setterMarker, terminalDiscrepancy]
      push_cast
      ring

private theorem carriedUpper_nil (width : Nat) (intercept : ℚ) :
    carriedUpper width [] intercept = intercept := by
  simp [carriedUpper, swappedUpperCode_nil, upperPower, upperLength, spell]

/-- The physical upper spelling carries precisely the two-state affine automaton. -/
theorem carriedUpper_eq_walkIntercept
    (width : Nat) (block : List NearyTile) (intercept : ℚ) :
    carriedUpper width block intercept = walkIntercept width block intercept := by
  induction block generalizing intercept with
  | nil => exact carriedUpper_nil width intercept
  | cons tile rest induction =>
      rw [carriedUpper_cons]
      exact induction _

/-- The recursive automaton scale is the physical upper spelling power. -/
theorem interceptPower_eq_upperPower
    (width : Nat) (block : List NearyTile) :
    interceptPower width block = upperPower width block := by
  induction block with
  | nil => rfl
  | cons tile rest induction =>
      rw [interceptPower, upperPower_cons, induction]
      push_cast
      cases tile.letter <;> norm_num

/-- Pulling a physical block backward from a carrier with boundary intercept `intercept`
divides the automaton numerator by the physical lower code. -/
theorem backwardBlock_eq_walkIntercept
    {width : Nat} {body : List TagLetter} {block : List NearyTile}
    {current intercept : ℚ}
    (lower_ne : (swappedLowerCode width body block : ℚ) ≠ 0)
    (carrier_denominator_ne :
      terminalDiscrepancy width + chamberRadius width * current ≠ 0)
    (intercept_eq : intercept =
      setterMarker width * chamberRadius width * current /
        (terminalDiscrepancy width + chamberRadius width * current)) :
    backwardBlock width
        (swappedUpperCode width block)
        (swappedLowerCode width body block)
        (upperPower width block) current =
      walkIntercept width block intercept /
        swappedLowerCode width body block := by
  rw [backwardBlock_eq_sub_correction lower_ne carrier_denominator_ne]
  rw [← carriedUpper_eq_walkIntercept]
  simp only [carriedUpper, blockCorrection]
  rw [intercept_eq]
  field_simp [carrier_denominator_ne, lower_ne]
  ring

/-- Every physical upper spelling scale is positive. -/
theorem interceptPower_pos (width : Nat) (block : List NearyTile) :
    0 < interceptPower width block := by
  induction block with
  | nil => norm_num [interceptPower]
  | cons tile rest induction =>
      rw [interceptPower]
      have scale_pos : (0 : ℚ) < widthScale width := by simp [widthScale]
      cases tile.letter <;> positivity

private theorem walkIntercept_potential_nonneg
    {width : Nat} (width_large : 6 ≤ width) (origin current scale : ℚ)
    (scale_pos : 0 < scale)
    (potential_nonneg :
      0 ≤ 2 * current - (2 * origin + 1) * scale - chamberRadius width)
    (rest : List NearyTile) :
    0 ≤ 2 * walkIntercept width rest current -
      (2 * origin + 1) * (scale * interceptPower width rest) -
        chamberRadius width := by
  have scale_large := widthScale_ge_729 width_large
  have width_scale_pos : (0 : ℚ) < widthScale width := by linarith
  have radius_pos : (0 : ℚ) < chamberRadius width := by
    simp only [chamberRadius]
    push_cast
    linarith
  induction rest generalizing current scale with
  | nil => simpa [walkIntercept, interceptPower] using potential_nonneg
  | cons tile rest induction =>
      cases letter_eq : tile.letter with
      | c =>
          have next_potential_nonneg :
              0 ≤ 2 * advanceIntercept width .c current -
                (2 * origin + 1) * (scale * 3) - chamberRadius width := by
            have recurrence :
                2 * advanceIntercept width .c current -
                      (2 * origin + 1) * (scale * 3) - chamberRadius width =
                  3 * (2 * current - (2 * origin + 1) * scale -
                    chamberRadius width) := by
              simp only [advanceIntercept]
              ring
            rw [recurrence]
            positivity
          have preserved := induction (advanceIntercept width .c current)
            (scale * 3) (by positivity) next_potential_nonneg
          rw [walkIntercept, interceptPower, letter_eq]
          simpa only [mul_assoc] using preserved
      | b =>
          have next_potential_nonneg :
              0 ≤ 2 * advanceIntercept width .b current -
                (2 * origin + 1) *
                  (scale * (9 * widthScale width)) - chamberRadius width := by
            have recurrence :
                2 * advanceIntercept width .b current -
                      (2 * origin + 1) *
                        (scale * (9 * widthScale width)) - chamberRadius width =
                  9 * widthScale width *
                    (2 * current - (2 * origin + 1) * scale -
                      chamberRadius width + widthScale width - 1) := by
              simp only [advanceIntercept, terminalDiscrepancy, chamberRadius]
              push_cast
              ring
            rw [recurrence]
            have inner_nonneg :
                0 ≤ 2 * current - (2 * origin + 1) * scale -
                  chamberRadius width + widthScale width - 1 := by
              nlinarith
            exact mul_nonneg (by positivity) inner_nonneg
          have preserved := induction (advanceIntercept width .b current)
            (scale * (9 * widthScale width)) (by positivity) next_potential_nonneg
          rw [walkIntercept, interceptPower, letter_eq]
          simpa only [mul_assoc] using preserved

private theorem walkIntercept_margin
    {width : Nat} (width_large : 6 ≤ width) (ceiling current scale : ℚ)
    (scale_pos : 0 < scale)
    (margin :
      interceptMargin width < ceiling * scale - current)
    (rest : List NearyTile) :
    interceptMargin width <
      ceiling * (scale * interceptPower width rest) -
        walkIntercept width rest current := by
  have scale_large := widthScale_ge_729 width_large
  have width_scale_pos : (0 : ℚ) < widthScale width := by linarith
  have radius_pos : (0 : ℚ) < chamberRadius width := by
    simp only [chamberRadius]
    push_cast
    linarith
  have fixed_positive := interceptMargin_pos width_large
  have fixed_point := interceptMargin_fixed width_large
  induction rest generalizing current scale with
  | nil => simpa [walkIntercept, interceptPower] using margin
  | cons tile rest induction =>
      cases letter_eq : tile.letter with
      | c =>
          have recurrence :
              ceiling * (scale * 3) - advanceIntercept width .c current =
                3 * (ceiling * scale - current) + chamberRadius width := by
            simp only [advanceIntercept]
            ring
          have next_margin :
              interceptMargin width <
                ceiling * (scale * 3) - advanceIntercept width .c current := by
            rw [recurrence]
            nlinarith
          have preserved := induction (advanceIntercept width .c current)
            (scale * 3) (by positivity) next_margin
          rw [walkIntercept, interceptPower, letter_eq]
          simpa only [mul_assoc] using preserved
      | b =>
          have recurrence :
              ceiling * (scale * (9 * widthScale width)) -
                  advanceIntercept width .b current =
                9 * widthScale width * (ceiling * scale - current) -
                  terminalDiscrepancy width := by
            simp only [advanceIntercept]
            ring
          have scaled_margin := mul_lt_mul_of_pos_left margin
            (show (0 : ℚ) < 9 * widthScale width by positivity)
          have next_margin :
              interceptMargin width <
                ceiling * (scale * (9 * widthScale width)) -
                  advanceIntercept width .b current := by
            rw [recurrence, ← fixed_point]
            exact sub_lt_sub_right scaled_margin _
          have preserved := induction (advanceIntercept width .b current)
            (scale * (9 * widthScale width)) (by positivity) next_margin
          rw [walkIntercept, interceptPower, letter_eq]
          simpa only [mul_assoc] using preserved

private theorem walkIntercept_preserves_negative
    {width : Nat} (width_large : 6 ≤ width) {current : ℚ}
    (current_negative : current < -1) (rest : List NearyTile) :
    walkIntercept width rest current < -1 := by
  have scale_large := widthScale_ge_729 width_large
  induction rest generalizing current with
  | nil => simpa [walkIntercept] using current_negative
  | cons tile rest induction =>
      apply induction
      cases tile.letter with
      | c =>
          simp only [advanceIntercept, chamberRadius]
          push_cast
          linarith
      | b =>
          simp only [advanceIntercept, terminalDiscrepancy]
          push_cast
          nlinarith

/-- A `c`-leading block sends any sufficiently small intercept to a negative numerator. -/
theorem cLeading_walkIntercept_negative
    {width : Nat} (width_large : 6 ≤ width) {intercept : ℚ}
    (intercept_small :
      intercept < (chamberRadius width - 1) / 3)
    {tile : NearyTile} (tile_c : tile.letter = .c)
    (rest : List NearyTile) :
    walkIntercept width (tile :: rest) intercept < 0 := by
  have first_negative :
      advanceIntercept width tile.letter intercept < -1 := by
    rw [tile_c]
    simp only [advanceIntercept]
    linarith
  rw [walkIntercept]
  exact (walkIntercept_preserves_negative width_large first_negative rest).trans
    (by norm_num)

/-- A `b`-leading block amplifies the initial intercept by more than one half of its upper
spelling scale. -/
theorem bLeading_walkIntercept_lower
    {width : Nat} (width_large : 6 ≤ width) (intercept : ℚ)
    {tile : NearyTile} (tile_b : tile.letter = .b)
    (rest : List NearyTile) :
    (intercept + 1 / 2) * interceptPower width (tile :: rest) <
      walkIntercept width (tile :: rest) intercept := by
  have scale_large := widthScale_ge_729 width_large
  have radius_pos : (0 : ℚ) < chamberRadius width := by
    simp only [chamberRadius]
    push_cast
    linarith
  let firstScale : ℚ := 9 * widthScale width
  let firstIntercept := advanceIntercept width tile.letter intercept
  have first_scale_pos : 0 < firstScale := by
    simp only [firstScale]
    positivity
  have first_potential :
      0 ≤ 2 * firstIntercept - (2 * intercept + 1) * firstScale -
        chamberRadius width := by
    simp only [firstIntercept, firstScale]
    rw [tile_b]
    simp only [advanceIntercept, terminalDiscrepancy, chamberRadius]
    push_cast
    ring_nf
    positivity
  have potential := walkIntercept_potential_nonneg width_large
    intercept firstIntercept firstScale first_scale_pos first_potential rest
  dsimp only [firstIntercept] at potential
  rw [tile_b] at potential
  rw [walkIntercept, interceptPower, tile_b]
  simp only [firstScale] at potential ⊢
  have scaled_identity :
      2 * ((intercept + 1 / 2) *
          (9 * widthScale width * interceptPower width rest)) =
        (2 * intercept + 1) *
          (9 * widthScale width * interceptPower width rest) := by ring
  nlinarith

/-- A `b`-leading block preserves any affine ceiling with the canonical fixed-point margin. -/
theorem bLeading_walkIntercept_upper
    {width : Nat} (width_large : 6 ≤ width) {intercept ceiling : ℚ}
    (intercept_upper :
      intercept < ceiling - interceptMargin width)
    {tile : NearyTile} (tile_b : tile.letter = .b)
    (rest : List NearyTile) :
    walkIntercept width (tile :: rest) intercept <
      ceiling * interceptPower width (tile :: rest) := by
  have scale_large := widthScale_ge_729 width_large
  have fixed_positive := interceptMargin_pos width_large
  let firstScale : ℚ := 9 * widthScale width
  let firstIntercept := advanceIntercept width tile.letter intercept
  have first_scale_pos : 0 < firstScale := by
    simp only [firstScale]
    positivity
  have first_margin :
      interceptMargin width < ceiling * firstScale - firstIntercept := by
    simp only [firstScale, firstIntercept]
    rw [tile_b]
    simp only [advanceIntercept]
    have fixed_point := interceptMargin_fixed width_large
    have scaled_upper := mul_lt_mul_of_pos_left intercept_upper
      (show (0 : ℚ) < 9 * widthScale width by positivity)
    rw [← fixed_point]
    nlinarith
  have preserved := walkIntercept_margin width_large ceiling firstIntercept
    firstScale first_scale_pos first_margin rest
  dsimp only [firstIntercept] at preserved
  rw [tile_b] at preserved
  rw [walkIntercept, interceptPower, tile_b]
  simp only [firstScale] at preserved ⊢
  nlinarith

/-- The carrier after the literal canonical `R_c;D_b;D_c` history is positive for every
physical empty-front seed bound. -/
theorem postRcDbCarrier_pos_of_seed
    {width : Nat} (width_large : 6 ≤ width) {seed : ℚ}
    (seed_lower : (8 * widthScale width ^ 2 : ℚ) < seed) :
    0 < postRcDbCarrier width seed := by
  have width_two : 2 ≤ width := by omega
  obtain ⟨time_pos, gap_pos, carrier_denominator_pos, _⟩ :=
    postRcDb_positive_data width_large seed_lower
  have image_above : 1 < canonicalRcDbBackward width seed := by
    rw [canonicalRcDbBackward_eq_one_add width_two time_pos.ne']
    have lower_double_pos := rcDbLowerDouble_pos width_two
    have quotient_pos :
        0 < rcDbGap width seed /
          (rcDbLowerDouble width * rcDbTime width seed) := by positivity
    linarith
  rw [postRcDbCarrier_eq_closed width_two time_pos.ne' (by linarith)]
  have scale_large := widthScale_ge_729 width_large
  have terminal_pos : (0 : ℚ) < terminalDiscrepancy width := by
    simp only [terminalDiscrepancy]
    push_cast
    linarith
  have radius_pos : (0 : ℚ) < chamberRadius width := by
    simp only [chamberRadius]
    push_cast
    linarith
  exact div_pos (mul_pos (mul_pos terminal_pos radius_pos) gap_pos)
    carrier_denominator_pos

/-- The boundary denominator after the literal canonical history is positive. -/
theorem postRcDbCarrier_denominator_pos_of_seed
    {width : Nat} (width_large : 6 ≤ width) {seed : ℚ}
    (seed_lower : (8 * widthScale width ^ 2 : ℚ) < seed) :
    0 < terminalDiscrepancy width +
      chamberRadius width * postRcDbCarrier width seed := by
  have scale_large := widthScale_ge_729 width_large
  have terminal_pos : (0 : ℚ) < terminalDiscrepancy width := by
    simp only [terminalDiscrepancy]
    push_cast
    linarith
  have radius_pos : (0 : ℚ) < chamberRadius width := by
    simp only [chamberRadius]
    push_cast
    linarith
  have carrier_pos := postRcDbCarrier_pos_of_seed width_large seed_lower
  positivity

end MatrixMortality.SwappedSetterPostRcDbChamber
