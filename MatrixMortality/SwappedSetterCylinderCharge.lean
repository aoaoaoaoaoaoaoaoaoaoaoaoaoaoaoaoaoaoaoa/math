import MatrixMortality.SwappedSetterReachableCylinder

/-!
# Exact target charge behind the swapped-setter predecessor cylinder
-/

namespace MatrixMortality.SwappedSetterCylinderCharge

open PadicValuation SwappedSetterMultitransfer SwappedSetterHistory
  SwappedSetterThresholdCarry SwappedSetterCarrierGap SwappedSetterCarrierResonance
  SwappedSetterPredecessorCylinder SwappedSetterBackwardResonance
  SwappedSetterSequentialDoubleDeletion

private instance factPrimeThree : Fact (Nat.Prime 3) :=
  ⟨by norm_num⟩

/-- Exact quotient carried by a target after its full erasure tail is stripped. -/
def erasureTailCharge (width : Nat) (body : List TagLetter)
    (target front : List NearyTile) (numerator denominator : ℤ) : ℤ :=
  denominator *
      (signedSwappedCode (spell (nearyUpper width) target ++ [true]) + 1) -
    numerator *
      (signedSwappedCode (spell (nearyLower width body) front) + 1)

/-- Last-resonance residual whose deep divisibility defines the predecessor cylinder. -/
def predecessorCylinder (width : Nat) (body : List TagLetter)
    (block : List NearyTile) (scaleDepth : Nat)
    (numerator denominator : ℤ) : ℤ :=
  swappedUpperCode width block * denominator -
      swappedLowerCode width body block * numerator -
    3 ^ scaleDepth * terminalDiscrepancy width * denominator

private theorem signedSwappedCode_replicate_false (length : Nat) :
    signedSwappedCode (List.replicate length false) = (3 : ℤ) ^ length - 1 := by
  induction length with
  | zero => rfl
  | succ length induction =>
      rw [List.replicate_succ', signedSwappedCode_append, induction, pow_succ]
      norm_num [signedSwappedCode, ternaryCode, ternaryDigit]
      ring

private theorem spell_nearyLower_erase_map
    (width : Nat) (body letters : List TagLetter) :
    spell (nearyLower width body) (letters.map NearyTile.erase) =
      List.replicate letters.length false := by
  induction letters with
  | nil => rfl
  | cons letter letters induction =>
      change nearyLower width body (.erase letter) ++
          spell (nearyLower width body) (letters.map NearyTile.erase) = _
      rw [induction]
      cases letter <;> simp [nearyLower, List.replicate_succ]

/-- A full erasure-tail threshold factors its primitive gap by the marker power, with the
quotient still carrying the exact discarded target prefixes. -/
theorem erasureTail_threshold_gap_eq_charge
    {width : Nat} (body : List TagLetter) {target front : List NearyTile}
    {letters : List TagLetter} (letters_length : letters.length = width)
    (target_eq : target = front ++ letters.map NearyTile.erase)
    {numerator denominator : ℤ}
    (threshold :
      denominator * swappedUpperCode width target =
        numerator * swappedLowerCode width body target) :
    denominator - numerator =
      (3 : ℤ) ^ width *
        erasureTailCharge width body target front numerator denominator := by
  have upper_factorization :
      spell (nearyUpper width) target ++ nearyMarker width =
        (spell (nearyUpper width) target ++ [true]) ++
          List.replicate width false := by
    simp [nearyMarker, List.append_assoc]
  have lower_factorization :
      spell (nearyLower width body) target =
        spell (nearyLower width body) front ++ List.replicate width false := by
    rw [target_eq, spell_append, spell_nearyLower_erase_map, letters_length]
  have upper_code_eq :
      swappedUpperCode width target =
        (3 : ℤ) ^ width *
            signedSwappedCode (spell (nearyUpper width) target ++ [true]) +
          ((3 : ℤ) ^ width - 1) := by
    rw [swappedUpperCode]
    change signedSwappedCode
      (spell (nearyUpper width) target ++ nearyMarker width) = _
    rw [upper_factorization, signedSwappedCode_append,
      signedSwappedCode_replicate_false]
    simp
  have lower_code_eq :
      swappedLowerCode width body target =
        (3 : ℤ) ^ width *
            signedSwappedCode (spell (nearyLower width body) front) +
          ((3 : ℤ) ^ width - 1) := by
    rw [swappedLowerCode]
    change signedSwappedCode (spell (nearyLower width body) target) = _
    rw [lower_factorization, signedSwappedCode_append,
      signedSwappedCode_replicate_false]
    simp
  rw [upper_code_eq, lower_code_eq] at threshold
  simp only [erasureTailCharge]
  linear_combination -threshold

/-- The peeled quotient determines the literal balanced carry left after consuming the matched
full erasure tail; the carry is exactly `(3^width−1)` times that quotient. -/
theorem erasureTail_threshold_suffixCarry
    {width : Nat} (body : List TagLetter) {target front : List NearyTile}
    {letters : List TagLetter} (letters_length : letters.length = width)
    (target_eq : target = front ++ letters.map NearyTile.erase)
    {numerator denominator : ℤ}
    (threshold :
      denominator * swappedUpperCode width target =
        numerator * swappedLowerCode width body target) :
    SuffixCarry denominator numerator
      (List.replicate width false) (List.replicate width false)
      (((3 : ℤ) ^ width - 1) *
        erasureTailCharge width body target front numerator denominator) := by
  have upper_factorization :
      spell (nearyUpper width) target ++ nearyMarker width =
        (spell (nearyUpper width) target ++ [true]) ++
          List.replicate width false := by
    simp [nearyMarker, List.append_assoc]
  have lower_factorization :
      spell (nearyLower width body) target =
        spell (nearyLower width body) front ++ List.replicate width false := by
    rw [target_eq, spell_append, spell_nearyLower_erase_map, letters_length]
  have cross :
      denominator * signedSwappedCode
          ((spell (nearyUpper width) target ++ [true]) ++
            List.replicate width false) =
        numerator * signedSwappedCode
          (spell (nearyLower width body) front ++ List.replicate width false) := by
    rw [← upper_factorization, ← lower_factorization]
    simpa [swappedUpperCode, swappedLowerCode, signedSwappedCode,
      List.map_append] using threshold
  have suffix := suffixCarry_of_crossProduct (by simp) cross
  have gap_eq :=
    erasureTail_threshold_gap_eq_charge body letters_length target_eq threshold
  have carry_eq :
      numerator * signedSwappedCode (spell (nearyLower width body) front) -
          denominator *
            signedSwappedCode (spell (nearyUpper width) target ++ [true]) =
        ((3 : ℤ) ^ width - 1) *
          erasureTailCharge width body target front numerator denominator := by
    simp only [erasureTailCharge] at gap_eq ⊢
    linear_combination gap_eq
  simpa [carry_eq] using suffix

/-- At exact last-step resonance, the normalized successor gap is the predecessor-cylinder
residual multiplied by `−3μ`. -/
theorem normalizedTransition_gap_transport
    {width scaleDepth : Nat} (body : List TagLetter) (block : List NearyTile)
    {numerator denominator nextNumerator nextDenominator scale : ℤ}
    (length_eq : upperLength width block = scaleDepth + 1)
    (numerator_eq :
      nextCarrierNumerator width body block numerator denominator =
        scale * nextNumerator)
    (denominator_eq :
      nextCarrierDenominator width body block numerator denominator =
        scale * nextDenominator) :
    scale * (nextDenominator - nextNumerator) =
      -3 * setterMarker width *
        predecessorCylinder width body block scaleDepth numerator denominator := by
  have raw_gap := nextCarrier_gap width body block numerator denominator
  rw [denominator_eq, numerator_eq, length_eq, pow_succ] at raw_gap
  simp only [predecessorCylinder]
  linear_combination raw_gap

private theorem setterMarker_ne_zero (width : Nat) : setterMarker width ≠ 0 := by
  have scale_pos : (0 : ℤ) < widthScale width := by simp [widthScale]
  simp [setterMarker]
  omega

/-- The represented integral denominator transports the live centered denominator across one
physical block by the unreduced carrier denominator. -/
theorem represented_blockStep_denominator_transport
    (width : Nat) (body : List TagLetter) (block : List NearyTile)
    (state : CenteredState) {numerator denominator : ℤ}
    (represented : RepresentsDefectRatio width state numerator denominator) :
    (denominator : ℚ) * (blockStep width body block state).y =
      state.y * nextCarrierDenominator width body block numerator denominator := by
  rw [RepresentsDefectRatio] at represented
  rw [blockStep_y, poleResidual_eq_ordinaryDefect]
  simp only [nextCarrierDenominator]
  push_cast
  linear_combination
    -(swappedLowerCode width body block : ℚ) * represented

/-- A live successor and a nonzero represented predecessor denominator force the predecessor
state itself to be live. -/
theorem represented_blockStep_predecessor_y_ne
    (width : Nat) (body : List TagLetter) (block : List NearyTile)
    (state : CenteredState) {numerator denominator : ℤ}
    (represented : RepresentsDefectRatio width state numerator denominator)
    (denominator_ne : denominator ≠ 0)
    (successor_y_ne : (blockStep width body block state).y ≠ 0) :
    state.y ≠ 0 := by
  intro state_y_zero
  have transport :=
    represented_blockStep_denominator_transport width body block state represented
  rw [state_y_zero, zero_mul] at transport
  have denominator_cast_ne : (denominator : ℚ) ≠ 0 := by exact_mod_cast denominator_ne
  exact successor_y_ne <|
    (mul_eq_zero.mp transport).resolve_left denominator_cast_ne

private theorem not_dvd_three_of_intCast_isUnit {value : ℤ}
    (unit : IsUnit 3 (value : ℚ)) : ¬(3 : ℤ) ∣ value := by
  intro divides
  have valuation_zero : padicValInt 3 value = 0 := by
    have rational_valuation_zero := unit.2
    rw [padicValRat.of_int] at rational_valuation_zero
    exact_mod_cast rational_valuation_zero
  rw [padicValInt.eq_zero_iff] at valuation_zero
  rcases valuation_zero with prime_one | value_zero | not_dvd
  · norm_num at prime_one
  · exact unit.1 (by exact_mod_cast value_zero)
  · exact not_dvd divides

/-- A primitive deep predecessor cylinder cannot lie on the infinite projective ray. -/
theorem predecessorCylinder_predecessorDenominator_ne
    {width scaleDepth : Nat} (width_two : 2 ≤ width)
    (body : List TagLetter) {block : List NearyTile}
    (role_block : IsRoleBlock block) {numerator denominator quotient : ℤ}
    (primitive : IsCoprime numerator denominator)
    (cylinder_eq :
      predecessorCylinder width body block scaleDepth numerator denominator =
        3 ^ (scaleDepth + width - 1) * quotient) :
    denominator ≠ 0 := by
  intro denominator_zero
  subst denominator
  have lower_not_dvd : ¬(3 : ℤ) ∣ swappedLowerCode width body block :=
    not_dvd_three_of_intCast_isUnit <|
      roleBlock_lower_isUnit width body role_block
  have numerator_not_dvd : ¬(3 : ℤ) ∣ numerator := by
    intro numerator_dvd
    have three_unit := primitive.isUnit_of_dvd' numerator_dvd (dvd_zero 3)
    rw [Int.isUnit_iff] at three_unit
    omega
  have exponent_pos : 0 < scaleDepth + width - 1 := by omega
  have power_dvd : (3 : ℤ) ∣ 3 ^ (scaleDepth + width - 1) :=
    dvd_pow_self 3 (Nat.ne_of_gt exponent_pos)
  have product_dvd :
      (3 : ℤ) ∣ 3 ^ (scaleDepth + width - 1) * quotient :=
    dvd_mul_of_dvd_left power_dvd quotient
  simp only [predecessorCylinder, mul_zero, sub_zero] at cylinder_eq
  rw [← cylinder_eq] at product_dvd
  have lower_numerator_dvd :
      (3 : ℤ) ∣ swappedLowerCode width body block * numerator := by
    exact dvd_neg.mp <| by simpa only [zero_sub] using product_dvd
  rcases (by norm_num : Prime (3 : ℤ)).dvd_mul.mp lower_numerator_dvd with
    lower_dvd | numerator_dvd
  · exact lower_not_dvd lower_dvd
  · exact numerator_not_dvd numerator_dvd

/-- A primitive pair with a numerator containing `3^(width−1)`, `width≥2`, has nonzero
denominator. -/
theorem primitiveDeepNumerator_denominator_ne
    {width : Nat} (width_two : 2 ≤ width)
    {numerator denominator quotient : ℤ}
    (primitive : IsCoprime numerator denominator)
    (numerator_eq : numerator = 3 ^ (width - 1) * quotient) :
    denominator ≠ 0 := by
  intro denominator_zero
  subst denominator
  have exponent_pos : 0 < width - 1 := by omega
  have numerator_dvd : (3 : ℤ) ∣ numerator := by
    rw [numerator_eq]
    exact dvd_mul_of_dvd_left
      (dvd_pow_self 3 (Nat.ne_of_gt exponent_pos)) quotient
  have three_unit := primitive.isUnit_of_dvd' numerator_dvd (dvd_zero 3)
  rw [Int.isUnit_iff] at three_unit
  omega

/-- The cylinder center is exactly the projective preimage of the gap-zero ray. -/
theorem normalizedTransition_gap_zero_iff_predecessorCylinder_zero
    {width scaleDepth : Nat} (body : List TagLetter) (block : List NearyTile)
    {numerator denominator nextNumerator nextDenominator scale : ℤ}
    (scale_ne : scale ≠ 0)
    (length_eq : upperLength width block = scaleDepth + 1)
    (numerator_eq :
      nextCarrierNumerator width body block numerator denominator =
        scale * nextNumerator)
    (denominator_eq :
      nextCarrierDenominator width body block numerator denominator =
        scale * nextDenominator) :
    nextDenominator - nextNumerator = 0 ↔
      predecessorCylinder width body block scaleDepth numerator denominator = 0 := by
  have transport := normalizedTransition_gap_transport body block length_eq
    numerator_eq denominator_eq
  constructor
  · intro gap_zero
    rw [gap_zero, mul_zero] at transport
    have coefficient_ne : -3 * setterMarker width ≠ 0 :=
      mul_ne_zero (by norm_num) (setterMarker_ne_zero width)
    exact (mul_eq_zero.mp transport.symm).resolve_left coefficient_ne
  · intro cylinder_zero
    rw [cylinder_zero, mul_zero] at transport
    exact (mul_eq_zero.mp transport).resolve_left scale_ne

private theorem integer_hasValue_factor
    {value : ℤ} {depth : Nat} (shell : HasValue 3 (value : ℚ) depth) :
    ∃ unit : ℤ, value = 3 ^ depth * unit ∧ ¬(3 : ℤ) ∣ unit := by
  have valuation_eq : padicValInt 3 value = depth := by
    have rational_eq := shell.2
    rw [padicValRat.of_int] at rational_eq
    exact_mod_cast rational_eq
  have power_divides : (3 : ℤ) ^ depth ∣ value :=
    (padicValInt_dvd_iff depth value).mpr (Or.inr valuation_eq.ge)
  obtain ⟨unit, value_eq⟩ := power_divides
  refine ⟨unit, value_eq, ?_⟩
  intro three_divides
  obtain ⟨factor, unit_eq⟩ := three_divides
  have deeper_divides : (3 : ℤ) ^ (depth + 1) ∣ value := by
    refine ⟨factor, ?_⟩
    rw [value_eq, unit_eq, pow_succ]
    ring
  have deeper_bound := (padicValInt_dvd_iff (depth + 1) value).mp deeper_divides
  have value_ne : value ≠ 0 := by exact_mod_cast shell.1
  have depth_le := deeper_bound.resolve_left value_ne
  rw [valuation_eq] at depth_le
  omega

private theorem setterMarker_coprime_three
    {width : Nat} (width_pos : 0 < width) :
    IsCoprime (setterMarker width) (3 : ℤ) := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt width_pos)
  refine ⟨-1, 2 * (3 : ℤ) ^ offset, ?_⟩
  simp [setterMarker, widthScale, pow_succ]
  ring

/-- At a resonant normalized transition, the deep cylinder quotient and the exact successor-gap
quotient are the same nonzero ancestry charge up to normalization and the marker unit. -/
theorem resonantTransition_gap_charge
    {width scaleDepth : Nat} (width_two : 2 ≤ width)
    (body : List TagLetter) (block : List NearyTile)
    {numerator denominator nextNumerator nextDenominator scale : ℤ}
    (scale_shell : HasValue 3 (scale : ℚ) scaleDepth)
    (length_eq : upperLength width block = scaleDepth + 1)
    (numerator_eq :
      nextCarrierNumerator width body block numerator denominator =
        scale * nextNumerator)
    (denominator_eq :
      nextCarrierDenominator width body block numerator denominator =
        scale * nextDenominator)
    {gapCharge : ℤ}
    (gap_eq :
      nextDenominator - nextNumerator = 3 ^ width * gapCharge)
    (nonterminal : nextDenominator - nextNumerator ≠ 0) :
    ∃ scaleUnit cylinderQuotient : ℤ,
      scale = 3 ^ scaleDepth * scaleUnit ∧
        ¬(3 : ℤ) ∣ scaleUnit ∧
        predecessorCylinder width body block scaleDepth numerator denominator =
          3 ^ (scaleDepth + width - 1) * cylinderQuotient ∧
        setterMarker width * cylinderQuotient =
          -scaleUnit * gapCharge ∧
        gapCharge ≠ 0 ∧
        cylinderQuotient ≠ 0 := by
  obtain ⟨scaleUnit, scale_eq, scaleUnit_not_dvd⟩ :=
    integer_hasValue_factor scale_shell
  let cylinder :=
    predecessorCylinder width body block scaleDepth numerator denominator
  have transport := normalizedTransition_gap_transport body block length_eq
    numerator_eq denominator_eq
  rw [scale_eq, gap_eq] at transport
  have exponent_eq :
      scaleDepth + width = (scaleDepth + width - 1) + 1 := by omega
  have power_eq :
      (3 : ℤ) ^ (scaleDepth + width) =
        3 * 3 ^ (scaleDepth + width - 1) := by
    calc
      (3 : ℤ) ^ (scaleDepth + width) =
          3 ^ ((scaleDepth + width - 1) + 1) :=
            congrArg (fun exponent : Nat => (3 : ℤ) ^ exponent) exponent_eq
      _ = 3 ^ (scaleDepth + width - 1) * 3 := by rw [pow_succ]
      _ = 3 * 3 ^ (scaleDepth + width - 1) := mul_comm _ _
  have cancelled :
      (3 : ℤ) ^ (scaleDepth + width - 1) * scaleUnit * gapCharge =
        -setterMarker width * cylinder := by
    apply mul_left_cancel₀ (show (3 : ℤ) ≠ 0 by norm_num)
    calc
      3 * ((3 : ℤ) ^ (scaleDepth + width - 1) * scaleUnit * gapCharge) =
          (3 : ℤ) ^ (scaleDepth + width) * scaleUnit * gapCharge := by
            rw [power_eq]
            ring
      _ = (3 : ℤ) ^ scaleDepth * scaleUnit *
          (3 ^ width * gapCharge) := by rw [pow_add]; ring
      _ = -3 * setterMarker width *
          predecessorCylinder width body block scaleDepth numerator denominator := transport
      _ = -3 * setterMarker width * cylinder := by rfl
      _ = 3 * (-setterMarker width * cylinder) := by ring
  have cylinder_divisible :
      (3 : ℤ) ^ (scaleDepth + width - 1) ∣ cylinder := by
    have product_divisible :
        (3 : ℤ) ^ (scaleDepth + width - 1) ∣ setterMarker width * cylinder := by
      exact dvd_neg.mp ⟨scaleUnit * gapCharge, by
        simpa [mul_assoc] using cancelled.symm⟩
    have power_marker_coprime :
        IsCoprime ((3 : ℤ) ^ (scaleDepth + width - 1)) (setterMarker width) :=
      (setterMarker_coprime_three (by omega)).symm.pow_left
    exact power_marker_coprime.dvd_of_dvd_mul_left product_divisible
  obtain ⟨cylinderQuotient, cylinder_eq⟩ := cylinder_divisible
  have quotient_eq :
      scaleUnit * gapCharge = -setterMarker width * cylinderQuotient := by
    apply mul_left_cancel₀
      (pow_ne_zero (scaleDepth + width - 1) (show (3 : ℤ) ≠ 0 by norm_num))
    calc
      (3 : ℤ) ^ (scaleDepth + width - 1) * (scaleUnit * gapCharge) =
          (3 : ℤ) ^ (scaleDepth + width - 1) * scaleUnit * gapCharge := by ring
      _ = -setterMarker width * cylinder := cancelled
      _ = (3 : ℤ) ^ (scaleDepth + width - 1) *
          (-setterMarker width * cylinderQuotient) := by rw [cylinder_eq]; ring
  have gapCharge_ne : gapCharge ≠ 0 := by
    intro gapCharge_zero
    rw [gapCharge_zero, mul_zero] at gap_eq
    exact nonterminal gap_eq
  have cylinderQuotient_ne : cylinderQuotient ≠ 0 := by
    intro cylinderQuotient_zero
    rw [cylinderQuotient_zero, mul_zero] at quotient_eq
    rcases mul_eq_zero.mp quotient_eq with scaleUnit_zero | gapCharge_zero
    · exact scaleUnit_not_dvd (scaleUnit_zero ▸ dvd_zero 3)
    · exact gapCharge_ne gapCharge_zero
  refine ⟨scaleUnit, cylinderQuotient, scale_eq, scaleUnit_not_dvd, cylinder_eq,
    ?_, gapCharge_ne, cylinderQuotient_ne⟩
  linear_combination quotient_eq

/-- A full target tail instantiates the abstract gap charge by the exact discarded target
prefixes. -/
theorem resonantTransition_erasureTail_charge
    {width scaleDepth : Nat} (width_two : 2 ≤ width)
    (body : List TagLetter) (block : List NearyTile)
    {numerator denominator nextNumerator nextDenominator scale : ℤ}
    (scale_shell : HasValue 3 (scale : ℚ) scaleDepth)
    (length_eq : upperLength width block = scaleDepth + 1)
    (numerator_eq :
      nextCarrierNumerator width body block numerator denominator =
        scale * nextNumerator)
    (denominator_eq :
      nextCarrierDenominator width body block numerator denominator =
        scale * nextDenominator)
    {target : List NearyTile} (target_tail : HasErasureTail width target)
    (threshold :
      nextDenominator * swappedUpperCode width target =
        nextNumerator * swappedLowerCode width body target)
    (nonterminal : nextDenominator - nextNumerator ≠ 0) :
    ∃ (front : List NearyTile) (letters : List TagLetter)
        (scaleUnit cylinderQuotient : ℤ),
      letters.length = width ∧
        target = front ++ letters.map NearyTile.erase ∧
        scale = 3 ^ scaleDepth * scaleUnit ∧
        ¬(3 : ℤ) ∣ scaleUnit ∧
        predecessorCylinder width body block scaleDepth numerator denominator =
          3 ^ (scaleDepth + width - 1) * cylinderQuotient ∧
        setterMarker width * cylinderQuotient =
          -scaleUnit *
            erasureTailCharge width body target front nextNumerator nextDenominator ∧
        erasureTailCharge width body target front nextNumerator nextDenominator ≠ 0 ∧
        cylinderQuotient ≠ 0 := by
  obtain ⟨front, letters, letters_length, target_eq⟩ := target_tail
  have gap_eq :=
    erasureTail_threshold_gap_eq_charge body letters_length target_eq threshold
  obtain ⟨scaleUnit, cylinderQuotient, scale_eq, scaleUnit_not_dvd,
      cylinder_eq, charge_eq, targetCharge_ne, cylinderQuotient_ne⟩ :=
    resonantTransition_gap_charge width_two body block scale_shell length_eq
      numerator_eq denominator_eq gap_eq nonterminal
  exact ⟨front, letters, scaleUnit, cylinderQuotient, letters_length, target_eq,
    scale_eq, scaleUnit_not_dvd, cylinder_eq, charge_eq, targetCharge_ne,
    cylinderQuotient_ne⟩

/-- Residual whose deep divisibility pulls a normalized successor numerator backward. -/
def backwardNumeratorCylinder (width : Nat) (body : List TagLetter)
    (block : List NearyTile) (upperDepth : Nat)
    (numerator denominator : ℤ) : ℤ :=
  swappedUpperCode width block * denominator -
      swappedLowerCode width body block * numerator -
    setterMarker width * 3 ^ upperDepth * denominator

private theorem terminalDiscrepancy_coprime_three
    {width : Nat} (width_pos : 0 < width) :
    IsCoprime (terminalDiscrepancy width) (3 : ℤ) := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt width_pos)
  refine ⟨-1, 5 * (3 : ℤ) ^ offset, ?_⟩
  simp [terminalDiscrepancy, widthScale, pow_succ]
  ring

/-- Deep successor-numerator charge is transported exactly to the backward cylinder through
the normalization unit and the fixed terminal unit. -/
theorem resonantTransition_deepNumerator_charge
    {width upperDepth : Nat} (width_two : 2 ≤ width)
    (body : List TagLetter) (block : List NearyTile)
    {numerator denominator nextNumerator scale numeratorCharge : ℤ}
    (scale_shell : HasValue 3 (scale : ℚ) upperDepth)
    (length_eq : upperLength width block = upperDepth)
    (numerator_eq :
      nextCarrierNumerator width body block numerator denominator =
        scale * nextNumerator)
    (nextNumerator_eq :
      nextNumerator = 3 ^ (width - 1) * numeratorCharge)
    (nextNumerator_ne : nextNumerator ≠ 0) :
    ∃ scaleUnit cylinderQuotient : ℤ,
      scale = 3 ^ upperDepth * scaleUnit ∧
        ¬(3 : ℤ) ∣ scaleUnit ∧
        backwardNumeratorCylinder width body block upperDepth numerator denominator =
          3 ^ (upperDepth + width - 1) * cylinderQuotient ∧
        scaleUnit * numeratorCharge =
          terminalDiscrepancy width * cylinderQuotient ∧
        numeratorCharge ≠ 0 ∧
        cylinderQuotient ≠ 0 := by
  obtain ⟨scaleUnit, scale_eq, scaleUnit_not_dvd⟩ :=
    integer_hasValue_factor scale_shell
  let cylinder :=
    backwardNumeratorCylinder width body block upperDepth numerator denominator
  have transport :
      scale * nextNumerator = terminalDiscrepancy width * cylinder := by
    rw [← numerator_eq, nextCarrierNumerator, length_eq]
    simp only [cylinder, backwardNumeratorCylinder]
    ring
  rw [scale_eq, nextNumerator_eq] at transport
  have exponent_eq : upperDepth + (width - 1) = upperDepth + width - 1 := by omega
  have combined :
      (3 : ℤ) ^ (upperDepth + width - 1) * scaleUnit * numeratorCharge =
        terminalDiscrepancy width * cylinder := by
    calc
      (3 : ℤ) ^ (upperDepth + width - 1) * scaleUnit * numeratorCharge =
          (3 : ℤ) ^ (upperDepth + (width - 1)) * scaleUnit * numeratorCharge := by
            rw [exponent_eq]
      _ = (3 : ℤ) ^ upperDepth * scaleUnit *
          (3 ^ (width - 1) * numeratorCharge) := by rw [pow_add]; ring
      _ = terminalDiscrepancy width * cylinder := transport
  have cylinder_divisible :
      (3 : ℤ) ^ (upperDepth + width - 1) ∣ cylinder := by
    have product_divisible :
        (3 : ℤ) ^ (upperDepth + width - 1) ∣
          terminalDiscrepancy width * cylinder :=
      ⟨scaleUnit * numeratorCharge, by simpa [mul_assoc] using combined.symm⟩
    have power_terminal_coprime :
        IsCoprime ((3 : ℤ) ^ (upperDepth + width - 1))
          (terminalDiscrepancy width) :=
      (terminalDiscrepancy_coprime_three (by omega)).symm.pow_left
    exact power_terminal_coprime.dvd_of_dvd_mul_left product_divisible
  obtain ⟨cylinderQuotient, cylinder_eq⟩ := cylinder_divisible
  have charge_eq :
      scaleUnit * numeratorCharge =
        terminalDiscrepancy width * cylinderQuotient := by
    apply mul_left_cancel₀
      (pow_ne_zero (upperDepth + width - 1) (show (3 : ℤ) ≠ 0 by norm_num))
    calc
      (3 : ℤ) ^ (upperDepth + width - 1) *
          (scaleUnit * numeratorCharge) =
        (3 : ℤ) ^ (upperDepth + width - 1) * scaleUnit * numeratorCharge := by ring
      _ = terminalDiscrepancy width * cylinder := combined
      _ = (3 : ℤ) ^ (upperDepth + width - 1) *
          (terminalDiscrepancy width * cylinderQuotient) := by rw [cylinder_eq]; ring
  have numeratorCharge_ne : numeratorCharge ≠ 0 := by
    intro charge_zero
    rw [charge_zero, mul_zero] at nextNumerator_eq
    exact nextNumerator_ne nextNumerator_eq
  have cylinderQuotient_ne : cylinderQuotient ≠ 0 := by
    intro quotient_zero
    rw [quotient_zero, mul_zero] at charge_eq
    rcases mul_eq_zero.mp charge_eq with scaleUnit_zero | charge_zero
    · exact scaleUnit_not_dvd (scaleUnit_zero ▸ dvd_zero 3)
    · exact numeratorCharge_ne charge_zero
  exact ⟨scaleUnit, cylinderQuotient, scale_eq, scaleUnit_not_dvd, cylinder_eq,
    charge_eq, numeratorCharge_ne, cylinderQuotient_ne⟩

/-- For a literal `D_c`, the backward numerator cylinder is the full marker power times the
affine gap quotient `2q-d`. -/
theorem literalDeletionC_backwardNumeratorCylinder_eq
    {width : Nat} (body : List TagLetter)
    {numerator denominator gapCharge : ℤ}
    (gap_eq : denominator - numerator = 3 ^ width * gapCharge) :
    backwardNumeratorCylinder width body [.erase .c] 1 numerator denominator =
      3 ^ width * (2 * gapCharge - denominator) := by
  simp [backwardNumeratorCylinder, swappedUpperCode_singleton_c,
    swappedLowerCode_singleton, setterMarker, terminalDiscrepancy, widthScale]
  linear_combination 2 * gap_eq

/-- The middle literal deletion in the three-block frontier transports its deep numerator
quotient to the exact affine predecessor-gap charge. -/
theorem literalDeletionC_deepNumerator_gap_charge
    {width : Nat} (width_two : 2 ≤ width) (body : List TagLetter)
    {numerator denominator nextNumerator scale gapCharge numeratorCharge : ℤ}
    (scale_shell : HasValue 3 (scale : ℚ) 1)
    (numerator_eq :
      nextCarrierNumerator width body [.erase .c] numerator denominator =
        scale * nextNumerator)
    (gap_eq : denominator - numerator = 3 ^ width * gapCharge)
    (nextNumerator_eq :
      nextNumerator = 3 ^ (width - 1) * numeratorCharge)
    (nextNumerator_ne : nextNumerator ≠ 0) :
    ∃ scaleUnit : ℤ,
      scale = 3 * scaleUnit ∧
        ¬(3 : ℤ) ∣ scaleUnit ∧
        scaleUnit * numeratorCharge =
          terminalDiscrepancy width * (2 * gapCharge - denominator) ∧
        numeratorCharge ≠ 0 := by
  obtain ⟨scaleUnit, cylinderQuotient, scale_eq, scaleUnit_not_dvd,
      cylinder_eq, charge_eq, numeratorCharge_ne, _⟩ :=
    resonantTransition_deepNumerator_charge width_two body [.erase .c]
      scale_shell (upperLength_singleton_erase_c width) numerator_eq nextNumerator_eq
      nextNumerator_ne
  have literal_eq :=
    literalDeletionC_backwardNumeratorCylinder_eq body gap_eq
  rw [cylinder_eq] at literal_eq
  have power_ne : (3 : ℤ) ^ width ≠ 0 :=
    pow_ne_zero width (by norm_num)
  have quotient_eq : cylinderQuotient = 2 * gapCharge - denominator := by
    apply mul_left_cancel₀ power_ne
    simpa using literal_eq
  refine ⟨scaleUnit, ?_, scaleUnit_not_dvd, ?_, numeratorCharge_ne⟩
  · simpa using scale_eq
  · simpa [quotient_eq] using charge_eq

/-- The completed local prefix before a prospective target pole is live at every product
boundary. -/
structure LiveThreeBlockPrefix (width : Nat) (body : List TagLetter)
    (precedingBlock : List NearyTile) (origin : CenteredState) : Prop where
  origin_y_ne : origin.y ≠ 0
  antecedent_y_ne : (blockStep width body precedingBlock origin).y ≠ 0
  previous_y_ne :
    (blockStep width body [.erase .c]
      (blockStep width body precedingBlock origin)).y ≠ 0
  current_y_ne :
    (blockStep width body [.erase .c]
      (blockStep width body [.erase .c]
        (blockStep width body precedingBlock origin))).y ≠ 0

/-- Exact nonzero charge chain carried by one arbitrary physical block and two following
singleton deletions into a full-tail pole. -/
structure ThreeBlockChargeWitness
    (width : Nat) (body : List TagLetter) (precedingBlock target : List NearyTile)
    (originNumerator originDenominator
      antecedentNumerator antecedentDenominator antecedentScale
      previousNumerator previousDenominator previousScale
      currentNumerator currentDenominator currentScale : ℤ) where
  /-- Target prefix before the matched full erasure tail. -/
  front : List NearyTile
  /-- Erased letters comprising the matched target tail. -/
  letters : List TagLetter
  /-- Three-adic depth discarded at the initial physical block. -/
  initialDepth : Nat
  /-- Unit cofactor of the initial normalization scale. -/
  initialUnit : ℤ
  /-- Unit cofactor of the first singleton-deletion normalization scale. -/
  middleUnit : ℤ
  /-- Unit cofactor of the second singleton-deletion normalization scale. -/
  currentUnit : ℤ
  /-- Quotient of the initial predecessor cylinder by its forced power of three. -/
  initialCylinderQuotient : ℤ
  /-- Full-gap quotient after the initial physical block. -/
  antecedentGapCharge : ℤ
  /-- Deep-numerator quotient after the first singleton deletion. -/
  previousNumeratorCharge : ℤ
  /-- Peeled target-prefix charge after the second singleton deletion. -/
  targetCharge : ℤ
  letters_length : letters.length = width
  target_eq : target = front ++ letters.map NearyTile.erase
  initial_length_eq : upperLength width precedingBlock = initialDepth + 1
  initial_scale_eq : antecedentScale = 3 ^ initialDepth * initialUnit
  middle_scale_eq : previousScale = 3 * middleUnit
  current_scale_eq : currentScale = currentUnit
  initialUnit_not_dvd : ¬(3 : ℤ) ∣ initialUnit
  middleUnit_not_dvd : ¬(3 : ℤ) ∣ middleUnit
  currentUnit_not_dvd : ¬(3 : ℤ) ∣ currentUnit
  antecedent_gap_eq :
    antecedentDenominator - antecedentNumerator =
      3 ^ width * antecedentGapCharge
  previous_numerator_eq :
    previousNumerator = 3 ^ (width - 1) * previousNumeratorCharge
  current_gap_eq :
    currentDenominator - currentNumerator = 3 ^ width * targetCharge
  targetCharge_eq :
    targetCharge =
      erasureTailCharge width body target front currentNumerator currentDenominator
  target_suffixCarry :
    SuffixCarry currentDenominator currentNumerator
      (List.replicate width false) (List.replicate width false)
      (((3 : ℤ) ^ width - 1) * targetCharge)
  originDenominator_ne : originDenominator ≠ 0
  antecedentDenominator_ne : antecedentDenominator ≠ 0
  previousDenominator_ne : previousDenominator ≠ 0
  currentDenominator_ne : currentDenominator ≠ 0
  initial_cylinder_eq :
    predecessorCylinder width body precedingBlock initialDepth
        originNumerator originDenominator =
      3 ^ (initialDepth + width - 1) * initialCylinderQuotient
  initial_charge_eq :
    setterMarker width * initialCylinderQuotient =
      -initialUnit * antecedentGapCharge
  middle_charge_eq :
    middleUnit * previousNumeratorCharge =
      terminalDiscrepancy width *
        (2 * antecedentGapCharge - antecedentDenominator)
  final_charge_eq :
    currentUnit * targetCharge =
      2 * setterMarker width * previousNumeratorCharge
  initialCylinderQuotient_ne : initialCylinderQuotient ≠ 0
  antecedentGapCharge_ne : antecedentGapCharge ≠ 0
  previousNumeratorCharge_ne : previousNumeratorCharge ≠ 0
  targetCharge_ne : targetCharge ≠ 0

/-- Eliminating both interior charges braids the reachable predecessor cylinder directly into
the literal balanced carry left by the target's matched erasure tail. -/
theorem ThreeBlockChargeWitness.braidedCarry_eq
    {width : Nat} {body : List TagLetter} {precedingBlock target : List NearyTile}
    {originNumerator originDenominator
      antecedentNumerator antecedentDenominator antecedentScale
      previousNumerator previousDenominator previousScale
      currentNumerator currentDenominator currentScale : ℤ}
    (witness : ThreeBlockChargeWitness width body precedingBlock target
      originNumerator originDenominator
      antecedentNumerator antecedentDenominator antecedentScale
      previousNumerator previousDenominator previousScale
      currentNumerator currentDenominator currentScale) :
    witness.initialUnit * witness.middleUnit * witness.currentUnit *
        (((3 : ℤ) ^ width - 1) * witness.targetCharge) =
      -2 * setterMarker width * terminalDiscrepancy width *
        ((3 : ℤ) ^ width - 1) *
        (2 * setterMarker width * witness.initialCylinderQuotient +
          witness.initialUnit * antecedentDenominator) := by
  calc
    witness.initialUnit * witness.middleUnit * witness.currentUnit *
          (((3 : ℤ) ^ width - 1) * witness.targetCharge) =
        witness.initialUnit * witness.middleUnit * ((3 : ℤ) ^ width - 1) *
          (witness.currentUnit * witness.targetCharge) := by ring
    _ = witness.initialUnit * witness.middleUnit * ((3 : ℤ) ^ width - 1) *
          (2 * setterMarker width * witness.previousNumeratorCharge) := by
            rw [witness.final_charge_eq]
    _ = 2 * setterMarker width * witness.initialUnit * ((3 : ℤ) ^ width - 1) *
          (witness.middleUnit * witness.previousNumeratorCharge) := by ring
    _ = 2 * setterMarker width * witness.initialUnit * ((3 : ℤ) ^ width - 1) *
          (terminalDiscrepancy width *
            (2 * witness.antecedentGapCharge - antecedentDenominator)) := by
              rw [witness.middle_charge_eq]
    _ = -2 * setterMarker width * terminalDiscrepancy width *
          ((3 : ℤ) ^ width - 1) *
          (2 * setterMarker width * witness.initialCylinderQuotient +
            witness.initialUnit * antecedentDenominator) := by
            linear_combination
              4 * setterMarker width * terminalDiscrepancy width *
                ((3 : ℤ) ^ width - 1) * witness.initial_charge_eq

/-- A nonterminal full-tail pole after `w;D_c;D_c` either halts or carries one exact nonzero
charge through the initial cylinder, middle deep numerator, and peeled target prefixes. The
same survivor automatically certifies every local product boundary as live. -/
theorem erasureTailPole_threeBlock_charge_frontier
    {width : Nat} (width_two : 2 ≤ width) (body : List TagLetter)
    (body_long : width - 1 ≤ body.length)
    {precedingBlock : List NearyTile} (preceding_role : IsRoleBlock precedingBlock)
    (origin : CenteredState)
    {originNumerator originDenominator
      antecedentNumerator antecedentDenominator antecedentScale
      previousNumerator previousDenominator previousScale
      currentNumerator currentDenominator currentScale : ℤ}
    (origin_represented :
      RepresentsDefectRatio width origin originNumerator originDenominator)
    (origin_primitive : IsCoprime originNumerator originDenominator)
    (antecedent_primitive : IsCoprime antecedentNumerator antecedentDenominator)
    (previous_primitive : IsCoprime previousNumerator previousDenominator)
    (current_primitive : IsCoprime currentNumerator currentDenominator)
    (antecedent_scale_ne : antecedentScale ≠ 0)
    (antecedent_numerator_eq :
      nextCarrierNumerator width body precedingBlock originNumerator originDenominator =
        antecedentScale * antecedentNumerator)
    (antecedent_denominator_eq :
      nextCarrierDenominator width body precedingBlock originNumerator originDenominator =
        antecedentScale * antecedentDenominator)
    (previous_scale_ne : previousScale ≠ 0)
    (previous_numerator_eq :
      nextCarrierNumerator width body [.erase .c]
          antecedentNumerator antecedentDenominator =
        previousScale * previousNumerator)
    (previous_denominator_eq :
      nextCarrierDenominator width body [.erase .c]
          antecedentNumerator antecedentDenominator =
        previousScale * previousDenominator)
    (current_scale_ne : currentScale ≠ 0)
    (current_numerator_eq :
      nextCarrierNumerator width body [.erase .c]
          previousNumerator previousDenominator =
        currentScale * currentNumerator)
    (current_denominator_eq :
      nextCarrierDenominator width body [.erase .c]
          previousNumerator previousDenominator =
        currentScale * currentDenominator)
    {target : List NearyTile} (target_tail : HasErasureTail width target)
    (current_y_ne :
      (blockStep width body [.erase .c]
        (blockStep width body [.erase .c]
          (blockStep width body precedingBlock origin))).y ≠ 0)
    (pole :
      poleResidual width body target
        (blockStep width body [.erase .c]
          (blockStep width body [.erase .c]
            (blockStep width body precedingBlock origin))) = 0)
    (nonterminal : currentDenominator - currentNumerator ≠ 0) :
    TagHaltsFrom width (tagOutput body) (body.drop (width - 1) ++ [.b]) ∨
      ∃ _ : ThreeBlockChargeWitness width body precedingBlock target
        originNumerator originDenominator
        antecedentNumerator antecedentDenominator antecedentScale
        previousNumerator previousDenominator previousScale
        currentNumerator currentDenominator currentScale,
        LiveThreeBlockPrefix width body precedingBlock origin := by
  have antecedent_raw_represented :=
    blockStep_represents_nextCarrier width body precedingBlock origin
      originNumerator originDenominator origin_represented
  rw [antecedent_numerator_eq, antecedent_denominator_eq] at antecedent_raw_represented
  have antecedent_represented :
      RepresentsDefectRatio width (blockStep width body precedingBlock origin)
        antecedentNumerator antecedentDenominator :=
    RepresentsDefectRatio.of_common_scale antecedent_scale_ne antecedent_raw_represented
  have previous_raw_represented :=
    blockStep_represents_nextCarrier width body [.erase .c]
      (blockStep width body precedingBlock origin)
      antecedentNumerator antecedentDenominator antecedent_represented
  rw [previous_numerator_eq, previous_denominator_eq] at previous_raw_represented
  have previous_represented :
      RepresentsDefectRatio width
        (blockStep width body [.erase .c]
          (blockStep width body precedingBlock origin))
        previousNumerator previousDenominator :=
    RepresentsDefectRatio.of_common_scale previous_scale_ne previous_raw_represented
  have current_raw_represented :=
    blockStep_represents_nextCarrier width body [.erase .c]
      (blockStep width body [.erase .c]
        (blockStep width body precedingBlock origin))
      previousNumerator previousDenominator previous_represented
  rw [current_numerator_eq, current_denominator_eq] at current_raw_represented
  have current_represented :
      RepresentsDefectRatio width
        (blockStep width body [.erase .c]
          (blockStep width body [.erase .c]
            (blockStep width body precedingBlock origin)))
        currentNumerator currentDenominator :=
    RepresentsDefectRatio.of_common_scale current_scale_ne current_raw_represented
  have threshold := threshold_crossProduct_of_pole width_two body target
    (blockStep width body [.erase .c]
      (blockStep width body [.erase .c]
        (blockStep width body precedingBlock origin)))
    current_y_ne current_represented pole
  have current_gap_divisible :
      widthScale width ∣ currentDenominator - currentNumerator := by
    simpa [widthScale] using
      erasureTail_threshold_dvd_gap body target_tail threshold
  have currentDenominator_ne : currentDenominator ≠ 0 := by
    have denominator_unit :=
      primitiveCongruent_denominator_isUnit (by omega) current_primitive
        current_gap_divisible
    exact_mod_cast denominator_unit.1
  obtain ⟨currentDepth, current_shell, current_length_eq⟩ :=
    primitiveDivisibleSuccessor_forces_lastStep_resonance width_two body
      (show IsRoleBlock ([.erase .c] : List NearyTile) from ⟨[], .c, rfl⟩)
      previous_primitive current_primitive current_scale_ne nonterminal
      current_gap_divisible current_numerator_eq current_denominator_eq
  have currentDepth_zero : currentDepth = 0 := by
    rw [upperLength_singleton_erase_c] at current_length_eq
    omega
  subst currentDepth
  obtain ⟨front, letters, currentUnit, finalCylinderQuotient,
      letters_length, target_eq, current_scale_eq, currentUnit_not_dvd,
      final_cylinder_eq, final_charge_raw, targetCharge_ne,
      finalCylinderQuotient_ne⟩ :=
    resonantTransition_erasureTail_charge width_two body [.erase .c]
      current_shell current_length_eq current_numerator_eq current_denominator_eq
      target_tail threshold nonterminal
  have final_cylinder_simplified :
      predecessorCylinder width body [.erase .c] 0
          previousNumerator previousDenominator = -2 * previousNumerator := by
    simp [predecessorCylinder, swappedUpperCode_singleton_c,
      swappedLowerCode_singleton]
  have previousNumerator_ne : previousNumerator ≠ 0 := by
    intro previousNumerator_zero
    rw [final_cylinder_simplified, previousNumerator_zero, mul_zero] at final_cylinder_eq
    simp only [zero_add] at final_cylinder_eq
    have power_ne : (3 : ℤ) ^ (width - 1) ≠ 0 :=
      pow_ne_zero (width - 1) (by norm_num)
    exact finalCylinderQuotient_ne <|
      (mul_eq_zero.mp final_cylinder_eq.symm).resolve_left power_ne
  have previousNumerator_divisible :
      (3 : ℤ) ^ (width - 1) ∣ previousNumerator :=
    literalDeletionC_divisibleSuccessor_numerator width_two body previous_primitive
      current_primitive current_scale_ne nonterminal current_gap_divisible
      current_numerator_eq current_denominator_eq
  have previousNumerator_divisible_for_resonance := previousNumerator_divisible
  obtain ⟨previousNumeratorCharge, previousNumerator_eq⟩ :=
    previousNumerator_divisible
  have previousDenominator_ne : previousDenominator ≠ 0 :=
    primitiveDeepNumerator_denominator_ne width_two previous_primitive
      previousNumerator_eq
  have previous_y_ne :
      (blockStep width body [.erase .c]
        (blockStep width body precedingBlock origin)).y ≠ 0 :=
    represented_blockStep_predecessor_y_ne width body [.erase .c]
      (blockStep width body [.erase .c]
        (blockStep width body precedingBlock origin))
      previous_represented previousDenominator_ne current_y_ne
  have previousNumeratorCharge_ne : previousNumeratorCharge ≠ 0 := by
    intro charge_zero
    rw [charge_zero, mul_zero] at previousNumerator_eq
    exact previousNumerator_ne previousNumerator_eq
  have finalCylinderQuotient_eq :
      finalCylinderQuotient = -2 * previousNumeratorCharge := by
    rw [final_cylinder_simplified, previousNumerator_eq] at final_cylinder_eq
    simp only [zero_add] at final_cylinder_eq
    apply mul_left_cancel₀
      (pow_ne_zero (width - 1) (show (3 : ℤ) ≠ 0 by norm_num))
    calc
      (3 : ℤ) ^ (width - 1) * finalCylinderQuotient =
          -2 * ((3 : ℤ) ^ (width - 1) * previousNumeratorCharge) :=
        final_cylinder_eq.symm
      _ = (3 : ℤ) ^ (width - 1) * (-2 * previousNumeratorCharge) := by ring
  rcases sequentialDoubleDeletionC_erasureTailPole_forces_halt_or_nonzeroPredecessorGap
      width_two body body_long (blockStep width body precedingBlock origin)
      antecedent_represented antecedent_primitive previous_primitive current_primitive
      previous_scale_ne previous_numerator_eq previous_denominator_eq current_scale_ne
      current_numerator_eq current_denominator_eq target_tail current_y_ne pole nonterminal with
    halts | ⟨antecedent_gap_ne, antecedent_gap_divisible⟩
  · exact Or.inl halts
  · have antecedent_power_divisible :
        (3 : ℤ) ^ width ∣ antecedentDenominator - antecedentNumerator := by
      simpa [widthScale] using antecedent_gap_divisible
    obtain ⟨antecedentGapCharge, antecedent_gap_eq⟩ := antecedent_power_divisible
    obtain ⟨initialDepth, initial_shell, initial_length_eq⟩ :=
      primitiveDivisibleSuccessor_forces_lastStep_resonance width_two body preceding_role
        origin_primitive antecedent_primitive antecedent_scale_ne antecedent_gap_ne
        antecedent_gap_divisible antecedent_numerator_eq antecedent_denominator_eq
    obtain ⟨initialUnit, initialCylinderQuotient, initial_scale_eq,
        initialUnit_not_dvd, initial_cylinder_eq, initial_charge_eq,
        antecedentGapCharge_ne, initialCylinderQuotient_ne⟩ :=
      resonantTransition_gap_charge width_two body precedingBlock initial_shell
        initial_length_eq antecedent_numerator_eq antecedent_denominator_eq
        antecedent_gap_eq antecedent_gap_ne
    have originDenominator_ne : originDenominator ≠ 0 :=
      predecessorCylinder_predecessorDenominator_ne width_two body preceding_role
        origin_primitive initial_cylinder_eq
    have antecedentDenominator_ne : antecedentDenominator ≠ 0 := by
      have denominator_unit :=
        primitiveCongruent_denominator_isUnit (by omega) antecedent_primitive
          antecedent_gap_divisible
      exact_mod_cast denominator_unit.1
    have antecedent_y_ne :
        (blockStep width body precedingBlock origin).y ≠ 0 :=
      represented_blockStep_predecessor_y_ne width body [.erase .c]
        (blockStep width body precedingBlock origin)
        antecedent_represented antecedentDenominator_ne previous_y_ne
    have origin_y_ne : origin.y ≠ 0 :=
      represented_blockStep_predecessor_y_ne width body precedingBlock origin
        origin_represented originDenominator_ne antecedent_y_ne
    obtain ⟨previousDepth, previous_shell, previous_length_eq, _⟩ :=
      primitiveDeepNumeratorSuccessor_forces_previousResonance width_two body
        (show IsRoleBlock ([.erase .c] : List NearyTile) from ⟨[], .c, rfl⟩)
        antecedent_primitive previous_primitive previous_scale_ne previousNumerator_ne
        previousNumerator_divisible_for_resonance previous_numerator_eq previous_denominator_eq
    have previousDepth_one : previousDepth = 1 := by
      rw [upperLength_singleton_erase_c] at previous_length_eq
      omega
    subst previousDepth
    obtain ⟨middleUnit, middle_scale_eq, middleUnit_not_dvd, middle_charge_eq, _⟩ :=
      literalDeletionC_deepNumerator_gap_charge width_two body previous_shell
        previous_numerator_eq antecedent_gap_eq previousNumerator_eq previousNumerator_ne
    let targetCharge :=
      erasureTailCharge width body target front currentNumerator currentDenominator
    have current_gap_eq :
        currentDenominator - currentNumerator = 3 ^ width * targetCharge :=
      erasureTail_threshold_gap_eq_charge body letters_length target_eq threshold
    have target_suffixCarry :
        SuffixCarry currentDenominator currentNumerator
          (List.replicate width false) (List.replicate width false)
          (((3 : ℤ) ^ width - 1) * targetCharge) :=
      erasureTail_threshold_suffixCarry body letters_length target_eq threshold
    have final_charge_eq :
        currentUnit * targetCharge =
          2 * setterMarker width * previousNumeratorCharge := by
      rw [finalCylinderQuotient_eq] at final_charge_raw
      linear_combination final_charge_raw
    let witness : ThreeBlockChargeWitness width body precedingBlock target
        originNumerator originDenominator
        antecedentNumerator antecedentDenominator antecedentScale
        previousNumerator previousDenominator previousScale
        currentNumerator currentDenominator currentScale := {
      front := front
      letters := letters
      initialDepth := initialDepth
      initialUnit := initialUnit
      middleUnit := middleUnit
      currentUnit := currentUnit
      initialCylinderQuotient := initialCylinderQuotient
      antecedentGapCharge := antecedentGapCharge
      previousNumeratorCharge := previousNumeratorCharge
      targetCharge := targetCharge
      letters_length := letters_length
      target_eq := target_eq
      initial_length_eq := initial_length_eq
      initial_scale_eq := initial_scale_eq
      middle_scale_eq := middle_scale_eq
      current_scale_eq := by simpa using current_scale_eq
      initialUnit_not_dvd := initialUnit_not_dvd
      middleUnit_not_dvd := middleUnit_not_dvd
      currentUnit_not_dvd := currentUnit_not_dvd
      antecedent_gap_eq := antecedent_gap_eq
      previous_numerator_eq := previousNumerator_eq
      current_gap_eq := current_gap_eq
      targetCharge_eq := rfl
      target_suffixCarry := target_suffixCarry
      originDenominator_ne := originDenominator_ne
      antecedentDenominator_ne := antecedentDenominator_ne
      previousDenominator_ne := previousDenominator_ne
      currentDenominator_ne := currentDenominator_ne
      initial_cylinder_eq := initial_cylinder_eq
      initial_charge_eq := initial_charge_eq
      middle_charge_eq := middle_charge_eq
      final_charge_eq := final_charge_eq
      initialCylinderQuotient_ne := initialCylinderQuotient_ne
      antecedentGapCharge_ne := antecedentGapCharge_ne
      previousNumeratorCharge_ne := previousNumeratorCharge_ne
      targetCharge_ne := by exact targetCharge_ne }
    exact Or.inr ⟨witness, ⟨origin_y_ne, antecedent_y_ne, previous_y_ne,
      current_y_ne⟩⟩

end MatrixMortality.SwappedSetterCylinderCharge
