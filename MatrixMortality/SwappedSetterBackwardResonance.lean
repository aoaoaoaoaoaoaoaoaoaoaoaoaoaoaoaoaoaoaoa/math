import MatrixMortality.SwappedSetterPredecessorCylinder

/-!
# Backward numerator resonance for the swapped setter
-/

namespace MatrixMortality.SwappedSetterBackwardResonance

open PadicValuation SwappedSetterMultitransfer SwappedSetterHistory
  SwappedSetterThresholdCarry SwappedSetterCarrierGap SwappedSetterPredecessorCylinder

private instance factPrimeThree : Fact (Nat.Prime 3) :=
  ⟨by norm_num⟩

private theorem centeredCoefficient_isUnit
    {width : Nat} (width_pos : 0 < width) :
    IsUnit 3 (centeredCoefficient width : ℚ) := by
  apply intCast_isUnit_of_not_dvd
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt width_pos)
  intro divides
  obtain ⟨factor, factor_eq⟩ := divides
  simp [centeredCoefficient, widthScale, pow_succ] at factor_eq
  omega

private theorem terminalDiscrepancy_isUnit
    {width : Nat} (width_pos : 0 < width) :
    IsUnit 3 (terminalDiscrepancy width : ℚ) := by
  apply intCast_isUnit_of_not_dvd
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt width_pos)
  intro divides
  obtain ⟨factor, factor_eq⟩ := divides
  simp [terminalDiscrepancy, widthScale, pow_succ] at factor_eq
  omega

private theorem terminalDiscrepancy_coprime_three
    {width : Nat} (width_pos : 0 < width) :
    IsCoprime (terminalDiscrepancy width) (3 : ℤ) := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt width_pos)
  refine ⟨-1, 5 * (3 : ℤ) ^ offset, ?_⟩
  simp [terminalDiscrepancy, widthScale, pow_succ]
  ring

private theorem setterMarker_isUnit
    {width : Nat} (width_pos : 0 < width) :
    IsUnit 3 (setterMarker width : ℚ) := by
  apply intCast_isUnit_of_not_dvd
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt width_pos)
  intro divides
  obtain ⟨factor, factor_eq⟩ := divides
  simp [setterMarker, widthScale, pow_succ] at factor_eq
  omega

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

private theorem three_dvd_of_deep_power
    {width : Nat} (width_two : 2 ≤ width) {value : ℤ}
    (divides : (3 : ℤ) ^ (width - 1) ∣ value) :
    (3 : ℤ) ∣ value := by
  have exponent_pos : 0 < width - 1 := by omega
  have three_dvd_power : (3 : ℤ) ∣ 3 ^ (width - 1) := by
    exact dvd_pow_self 3 (Nat.ne_of_gt exponent_pos)
  exact three_dvd_power.trans divides

private theorem intPower_dvd_of_hasValue
    {value : ℤ} {depth : Nat} (shell : HasValue 3 (value : ℚ) depth) :
    (3 : ℤ) ^ depth ∣ value := by
  have valuation_eq : padicValInt 3 value = depth := by
    have rational_eq := shell.2
    rw [padicValRat.of_int] at rational_eq
    exact_mod_cast rational_eq
  exact (padicValInt_dvd_iff depth value).mpr (Or.inr valuation_eq.ge)

private theorem deepNumeratorSuccessor_predecessorDenominator_isUnit
    {width : Nat} (width_two : 2 ≤ width)
    (body : List TagLetter) {block : List NearyTile} (role_block : IsRoleBlock block)
    {numerator denominator nextNumerator nextDenominator scale : ℤ}
    (primitive : IsCoprime numerator denominator)
    (next_numerator_divisible : (3 : ℤ) ^ (width - 1) ∣ nextNumerator)
    (numerator_eq :
      nextCarrierNumerator width body block numerator denominator =
        scale * nextNumerator)
    (denominator_eq :
      nextCarrierDenominator width body block numerator denominator =
        scale * nextDenominator) :
    IsUnit 3 (denominator : ℚ) := by
  have next_numerator_dvd : (3 : ℤ) ∣ nextNumerator :=
    three_dvd_of_deep_power width_two next_numerator_divisible
  apply intCast_isUnit_of_not_dvd
  intro denominator_dvd
  have numerator_not_dvd : ¬(3 : ℤ) ∣ numerator := by
    intro numerator_dvd
    have three_unit := primitive.isUnit_of_dvd' numerator_dvd denominator_dvd
    rw [Int.isUnit_iff] at three_unit
    omega
  have lower_unit := roleBlock_lower_isUnit width body role_block
  have lower_not_dvd := not_dvd_three_of_intCast_isUnit lower_unit
  let residual : ℤ :=
    swappedUpperCode width block * denominator -
      swappedLowerCode width body block * numerator
  have residual_not_dvd : ¬(3 : ℤ) ∣ residual := by
    intro residual_dvd
    have upper_product_dvd :
        (3 : ℤ) ∣ swappedUpperCode width block * denominator :=
      dvd_mul_of_dvd_right denominator_dvd _
    have lower_product_dvd :
        (3 : ℤ) ∣ swappedLowerCode width body block * numerator := by
      have difference_dvd := upper_product_dvd.sub residual_dvd
      simpa [residual] using difference_dvd
    rcases (by norm_num : Prime (3 : ℤ)).dvd_mul.mp lower_product_dvd with
      lower_dvd | numerator_dvd
    · exact lower_not_dvd lower_dvd
    · exact numerator_not_dvd numerator_dvd
  have width_pos : 0 < width := by omega
  have centered_unit := centeredCoefficient_isUnit width_pos
  have centered_not_dvd := not_dvd_three_of_intCast_isUnit centered_unit
  have scale_not_dvd : ¬(3 : ℤ) ∣ scale := by
    intro scale_dvd
    have right_dvd : (3 : ℤ) ∣ scale * nextDenominator :=
      dvd_mul_of_dvd_left scale_dvd _
    rw [nextCarrierDenominator] at denominator_eq
    have left_dvd :
        (3 : ℤ) ∣ centeredCoefficient width * residual := by
      rw [denominator_eq]
      exact right_dvd
    rcases (by norm_num : Prime (3 : ℤ)).dvd_mul.mp left_dvd with
      centered_dvd | residual_dvd
    · exact centered_not_dvd centered_dvd
    · exact residual_not_dvd residual_dvd
  have upper_power_dvd :
      (3 : ℤ) ∣ 3 ^ upperLength width block := by
    have upper_pos : 0 < upperLength width block := by
      obtain ⟨front, letter, rfl⟩ := role_block
      rw [upperLength, spell_append]
      apply List.length_pos_of_ne_nil
      apply List.append_ne_nil_of_right_ne_nil
      simpa [spell] using nearyUpper_ne_nil width (.erase letter)
    exact dvd_pow_self 3 (Nat.ne_of_gt upper_pos)
  have shifted_dvd :
      (3 : ℤ) ∣ setterMarker width * 3 ^ upperLength width block * denominator :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_right upper_power_dvd _) _
  have bracket_not_dvd :
      ¬(3 : ℤ) ∣
        (swappedUpperCode width block -
            setterMarker width * 3 ^ upperLength width block) * denominator -
          swappedLowerCode width body block * numerator := by
    intro bracket_dvd
    have bracket_eq :
        (swappedUpperCode width block -
            setterMarker width * 3 ^ upperLength width block) * denominator -
            swappedLowerCode width body block * numerator =
          residual -
            setterMarker width * 3 ^ upperLength width block * denominator := by
      simp [residual]
      ring
    rw [bracket_eq] at bracket_dvd
    have residual_dvd := bracket_dvd.add shifted_dvd
    have cancellation :
        residual - setterMarker width * 3 ^ upperLength width block * denominator +
            setterMarker width * 3 ^ upperLength width block * denominator =
          residual := by ring
    rw [cancellation] at residual_dvd
    exact residual_not_dvd residual_dvd
  have terminal_unit := terminalDiscrepancy_isUnit width_pos
  have terminal_not_dvd := not_dvd_three_of_intCast_isUnit terminal_unit
  have raw_numerator_not_dvd :
      ¬(3 : ℤ) ∣ nextCarrierNumerator width body block numerator denominator := by
    rw [nextCarrierNumerator]
    intro raw_dvd
    rcases (by norm_num : Prime (3 : ℤ)).dvd_mul.mp raw_dvd with
      terminal_dvd | bracket_dvd
    · exact terminal_not_dvd terminal_dvd
    · exact bracket_not_dvd bracket_dvd
  have right_dvd : (3 : ℤ) ∣ scale * nextNumerator :=
    dvd_mul_of_dvd_right next_numerator_dvd scale
  rw [← numerator_eq] at right_dvd
  exact raw_numerator_not_dvd right_dvd

/-- A nonzero primitive successor whose numerator contains `3^(width-1)` can only arise when
the previous block discards exactly its complete upper-length power of three. -/
theorem primitiveDeepNumeratorSuccessor_forces_previousResonance
    {width : Nat} (width_two : 2 ≤ width)
    (body : List TagLetter) {block : List NearyTile} (role_block : IsRoleBlock block)
    {numerator denominator nextNumerator nextDenominator scale : ℤ}
    (primitive : IsCoprime numerator denominator)
    (next_primitive : IsCoprime nextNumerator nextDenominator)
    (scale_ne : scale ≠ 0)
    (next_numerator_ne : nextNumerator ≠ 0)
    (next_numerator_divisible : (3 : ℤ) ^ (width - 1) ∣ nextNumerator)
    (numerator_eq :
      nextCarrierNumerator width body block numerator denominator =
        scale * nextNumerator)
    (denominator_eq :
      nextCarrierDenominator width body block numerator denominator =
        scale * nextDenominator) :
    ∃ scaleDepth : Nat,
      HasValue 3 (scale : ℚ) scaleDepth ∧
        upperLength width block = scaleDepth ∧
          (3 : ℤ) ^ (scaleDepth + width - 1) ∣
            swappedUpperCode width block * denominator -
                swappedLowerCode width body block * numerator -
              setterMarker width * 3 ^ scaleDepth * denominator := by
  have next_numerator_dvd : (3 : ℤ) ∣ nextNumerator :=
    three_dvd_of_deep_power width_two next_numerator_divisible
  have next_denominator_not_dvd : ¬(3 : ℤ) ∣ nextDenominator := by
    intro next_denominator_dvd
    have three_unit :=
      next_primitive.isUnit_of_dvd' next_numerator_dvd next_denominator_dvd
    rw [Int.isUnit_iff] at three_unit
    omega
  have next_denominator_unit : IsUnit 3 (nextDenominator : ℚ) :=
    intCast_isUnit_of_not_dvd next_denominator_not_dvd
  have denominator_unit :=
    deepNumeratorSuccessor_predecessorDenominator_isUnit width_two body role_block
      primitive next_numerator_divisible numerator_eq denominator_eq
  let scaleDepth := padicValInt 3 scale
  let numeratorDepth := padicValInt 3 nextNumerator
  have scale_shell : HasValue 3 (scale : ℚ) scaleDepth := by
    constructor
    · exact_mod_cast scale_ne
    · rw [padicValRat.of_int]
  have next_numerator_shell :
      HasValue 3 (nextNumerator : ℚ) numeratorDepth := by
    constructor
    · exact_mod_cast next_numerator_ne
    · rw [padicValRat.of_int]
  have numerator_depth_deep : width - 1 ≤ numeratorDepth := by
    have valuation_bound :=
      (padicValInt_dvd_iff (width - 1) nextNumerator).mp next_numerator_divisible
    exact valuation_bound.resolve_left next_numerator_ne
  have width_pos : 0 < width := by omega
  have centered_unit := centeredCoefficient_isUnit width_pos
  have terminal_unit := terminalDiscrepancy_isUnit width_pos
  have marker_unit := setterMarker_isUnit width_pos
  let residual : ℚ :=
    swappedUpperCode width block * denominator -
      swappedLowerCode width body block * numerator
  have residual_eq :
      (centeredCoefficient width : ℚ) * residual =
        scale * nextDenominator := by
    rw [nextCarrierDenominator] at denominator_eq
    have casted :
        (centeredCoefficient width : ℚ) *
            (swappedUpperCode width block * denominator -
              swappedLowerCode width body block * numerator) =
          scale * nextDenominator := by
      exact_mod_cast denominator_eq
    simpa [residual] using casted
  have residual_shell : HasValue 3 residual scaleDepth := by
    have quotient_shell :=
      div_hasValue (mul_hasValue scale_shell next_denominator_unit) centered_unit
    have residual_division :
        residual = (scale * nextDenominator) / centeredCoefficient width := by
      apply (eq_div_iff centered_unit.1).mpr
      simpa [mul_comm] using residual_eq
    simpa [residual_division] using quotient_shell
  have shifted_shell :
      HasValue 3
        ((setterMarker width : ℚ) * 3 ^ upperLength width block * denominator)
        (upperLength width block : Nat) := by
    simpa using mul_hasValue
      (mul_hasValue marker_unit
        (primePower_hasValue (prime := 3) (upperLength width block))) denominator_unit
  let numeratorCore : ℚ :=
    residual - setterMarker width * 3 ^ upperLength width block * denominator
  have numerator_core_eq :
      (terminalDiscrepancy width : ℚ) * numeratorCore =
        scale * nextNumerator := by
    rw [nextCarrierNumerator] at numerator_eq
    have casted :
        (terminalDiscrepancy width : ℚ) *
            ((swappedUpperCode width block -
                setterMarker width * 3 ^ upperLength width block) * denominator -
              swappedLowerCode width body block * numerator) =
          scale * nextNumerator := by
      exact_mod_cast numerator_eq
    calc
      (terminalDiscrepancy width : ℚ) * numeratorCore =
          terminalDiscrepancy width *
            ((swappedUpperCode width block -
                setterMarker width * 3 ^ upperLength width block) * denominator -
              swappedLowerCode width body block * numerator) := by
            dsimp [numeratorCore, residual]
            ring
      _ = scale * nextNumerator := casted
  have numerator_core_shell :
      HasValue 3 numeratorCore (scaleDepth + numeratorDepth : Nat) := by
    have quotient_shell := div_hasValue
      (mul_hasValue scale_shell next_numerator_shell) terminal_unit
    have core_division :
        numeratorCore = (scale * nextNumerator) / terminalDiscrepancy width := by
      apply (eq_div_iff terminal_unit.1).mpr
      simpa [mul_comm] using numerator_core_eq
    simpa [core_division] using quotient_shell
  have length_eq : upperLength width block = scaleDepth := by
    by_contra length_ne
    have summand_valuations_ne :
        padicValRat 3 residual ≠
          padicValRat 3
            ((setterMarker width : ℚ) * 3 ^ upperLength width block * denominator) := by
      rw [residual_shell.2, shifted_shell.2]
      intro cast_eq
      apply length_ne
      exact_mod_cast cast_eq.symm
    have forced_shell :
        HasValue 3 numeratorCore
          (min scaleDepth (upperLength width block) : Nat) := by
      simpa [numeratorCore, residual_shell.2, shifted_shell.2] using
        sub_hasValue_min residual_shell.1 shifted_shell.1 summand_valuations_ne
    have valuation_eq := numerator_core_shell.2.symm.trans forced_shell.2
    have numerator_depth_pos : 0 < numeratorDepth := by omega
    have minimum_lt :
        min scaleDepth (upperLength width block) < scaleDepth + numeratorDepth := by
      exact lt_of_le_of_lt (min_le_left _ _)
        (Nat.lt_add_of_pos_right numerator_depth_pos)
    have valuation_ne :
        ((scaleDepth + numeratorDepth : Nat) : ℤ) ≠
          (min scaleDepth (upperLength width block) : Nat) := by
      exact_mod_cast ne_of_gt minimum_lt
    exact valuation_ne valuation_eq
  have scale_divisible : (3 : ℤ) ^ scaleDepth ∣ scale :=
    intPower_dvd_of_hasValue scale_shell
  have product_divisible :
      (3 : ℤ) ^ (scaleDepth + width - 1) ∣ scale * nextNumerator := by
    have multiplied := mul_dvd_mul scale_divisible next_numerator_divisible
    have exponent_eq : scaleDepth + width - 1 = scaleDepth + (width - 1) := by omega
    rw [exponent_eq, pow_add]
    exact multiplied
  have raw_numerator_eq :
      nextCarrierNumerator width body block numerator denominator =
        terminalDiscrepancy width *
          (swappedUpperCode width block * denominator -
              swappedLowerCode width body block * numerator -
            setterMarker width * 3 ^ scaleDepth * denominator) := by
    rw [nextCarrierNumerator, length_eq]
    ring
  rw [← numerator_eq, raw_numerator_eq] at product_divisible
  have power_terminal_coprime :
      IsCoprime ((3 : ℤ) ^ (scaleDepth + width - 1))
        (terminalDiscrepancy width) :=
    (terminalDiscrepancy_coprime_three width_pos).symm.pow_left
  have cylinder_divisible :=
    power_terminal_coprime.dvd_of_dvd_mul_left product_divisible
  exact ⟨scaleDepth, scale_shell, length_eq, cylinder_divisible⟩

private theorem literalDeletionC_predecessorGap_of_cylinder
    {width scaleDepth : Nat} (body : List TagLetter)
    {numerator denominator : ℤ}
    (length_eq : upperLength width [.erase .c] = scaleDepth)
    (cylinder_divisible :
      (3 : ℤ) ^ (scaleDepth + width - 1) ∣
        swappedUpperCode width [.erase .c] * denominator -
            swappedLowerCode width body [.erase .c] * numerator -
          setterMarker width * 3 ^ scaleDepth * denominator) :
    widthScale width ∣ denominator - numerator := by
  have scaleDepth_one : scaleDepth = 1 := by
    rw [upperLength_singleton_erase_c] at length_eq
    omega
  subst scaleDepth
  have physical_core_eq :
      swappedUpperCode width [.erase .c] * denominator -
            swappedLowerCode width body [.erase .c] * numerator -
          setterMarker width * 3 ^ 1 * denominator =
        2 * (denominator - numerator) - widthScale width * denominator := by
    rw [swappedUpperCode_singleton_c, swappedLowerCode_singleton]
    simp [terminalDiscrepancy, setterMarker]
    ring
  have core_divisible :
      widthScale width ∣
        2 * (denominator - numerator) - widthScale width * denominator := by
    have normalized := cylinder_divisible
    rw [upperLength_singleton_erase_c,
      show 1 + width - 1 = width by omega, ← widthScale, physical_core_eq] at normalized
    exact normalized
  have scale_product_divisible :
      widthScale width ∣ widthScale width * denominator :=
    dvd_mul_right _ _
  have twice_gap_divisible : widthScale width ∣ 2 * (denominator - numerator) := by
    have combined := core_divisible.add scale_product_divisible
    have cancellation :
        2 * (denominator - numerator) - widthScale width * denominator +
            widthScale width * denominator =
          2 * (denominator - numerator) := by ring
    rw [cancellation] at combined
    exact combined
  have scale_two_coprime : IsCoprime (widthScale width) (2 : ℤ) := by
    simpa [widthScale] using (by norm_num : IsCoprime (3 : ℤ) 2).pow_left (m := width)
  exact scale_two_coprime.dvd_of_dvd_mul_left twice_gap_divisible

/-- For a literal `D_c`, the backward numerator cylinder is exactly the full predecessor-gap
congruence. -/
theorem literalDeletionC_deepNumeratorSuccessor_forces_predecessorGap
    {width : Nat} (width_two : 2 ≤ width) (body : List TagLetter)
    {numerator denominator nextNumerator nextDenominator scale : ℤ}
    (primitive : IsCoprime numerator denominator)
    (next_primitive : IsCoprime nextNumerator nextDenominator)
    (scale_ne : scale ≠ 0)
    (next_numerator_ne : nextNumerator ≠ 0)
    (next_numerator_divisible : (3 : ℤ) ^ (width - 1) ∣ nextNumerator)
    (numerator_eq :
      nextCarrierNumerator width body [.erase .c] numerator denominator =
        scale * nextNumerator)
    (denominator_eq :
      nextCarrierDenominator width body [.erase .c] numerator denominator =
        scale * nextDenominator) :
    widthScale width ∣ denominator - numerator := by
  have role_block : IsRoleBlock ([.erase .c] : List NearyTile) :=
    ⟨[], .c, by simp⟩
  obtain ⟨scaleDepth, _, length_eq, cylinder_divisible⟩ :=
    primitiveDeepNumeratorSuccessor_forces_previousResonance width_two body role_block
      primitive next_primitive scale_ne next_numerator_ne next_numerator_divisible
      numerator_eq denominator_eq
  exact literalDeletionC_predecessorGap_of_cylinder body length_eq cylinder_divisible

/-- A represented zero numerator is the ordinary reset ray; after literal `D_c`, any physical
pole has equal upper and lower target codes. -/
theorem zeroNumerator_literalDeletionC_pole_forces_terminal
    {width : Nat} (width_two : 2 ≤ width) (body : List TagLetter)
    (previous : CenteredState) {denominator : ℤ}
    (denominator_ne : denominator ≠ 0)
    (represented : RepresentsDefectRatio width previous 0 denominator)
    {target : List NearyTile}
    (current_y_ne : (blockStep width body [.erase .c] previous).y ≠ 0)
    (pole : poleResidual width body target
      (blockStep width body [.erase .c] previous) = 0) :
    swappedUpperCode width target = swappedLowerCode width body target := by
  have raw_represented := blockStep_represents_nextCarrier width body [.erase .c] previous
    0 denominator represented
  let common : ℤ :=
    centeredCoefficient width * terminalDiscrepancy width * denominator
  have common_ne : common ≠ 0 := by
    have scale_ge_nat : 3 ^ 2 ≤ 3 ^ width :=
      Nat.pow_le_pow_right (by norm_num) width_two
    have scale_ge : (9 : ℤ) ≤ widthScale width := by
      have casted : ((3 ^ 2 : Nat) : ℤ) ≤ ((3 ^ width : Nat) : ℤ) := by
        exact_mod_cast scale_ge_nat
      simpa [widthScale] using casted
    have centered_ne : centeredCoefficient width ≠ 0 := by
      simp [centeredCoefficient]
      omega
    have terminal_ne : terminalDiscrepancy width ≠ 0 := by
      simp [terminalDiscrepancy]
      omega
    exact mul_ne_zero (mul_ne_zero centered_ne terminal_ne) denominator_ne
  have numerator_eq :
      nextCarrierNumerator width body [.erase .c] 0 denominator = common := by
    simp [nextCarrierNumerator, swappedUpperCode_singleton_c,
      swappedLowerCode_singleton, upperLength_singleton_erase_c, common]
    simp [centeredCoefficient, terminalDiscrepancy, setterMarker, widthScale]
    ring
  have denominator_eq :
      nextCarrierDenominator width body [.erase .c] 0 denominator = common := by
    simp [nextCarrierDenominator, swappedUpperCode_singleton_c,
      swappedLowerCode_singleton, common]
    ring
  rw [numerator_eq, denominator_eq] at raw_represented
  have current_represented :
      RepresentsDefectRatio width (blockStep width body [.erase .c] previous) 1 1 := by
    exact RepresentsDefectRatio.of_common_scale common_ne (by simpa using raw_represented)
  have threshold := threshold_crossProduct_of_pole width_two body target
    (blockStep width body [.erase .c] previous) current_y_ne current_represented pole
  simpa using threshold

/-- The zero-numerator fork is a genuine Neary terminal match and therefore a source halt. -/
theorem zeroNumerator_literalDeletionC_pole_halts
    {width : Nat} (width_two : 2 ≤ width) (body : List TagLetter)
    (body_long : width - 1 ≤ body.length)
    (previous : CenteredState) {denominator : ℤ}
    (denominator_ne : denominator ≠ 0)
    (represented : RepresentsDefectRatio width previous 0 denominator)
    {target : List NearyTile}
    (current_y_ne : (blockStep width body [.erase .c] previous).y ≠ 0)
    (pole : poleResidual width body target
      (blockStep width body [.erase .c] previous) = 0) :
    TagHaltsFrom width (tagOutput body) (body.drop (width - 1) ++ [.b]) := by
  have terminal := zeroNumerator_literalDeletionC_pole_forces_terminal width_two body previous
    denominator_ne represented current_y_ne pole
  apply tagHaltsFrom_of_swappedTernaryCode_eq width body (by omega) body_long target
  change
    (ternaryCode ((spell (nearyUpper width) target ++ nearyMarker width).map not) : ℤ) =
      ternaryCode ((spell (nearyLower width body) target).map not) at terminal
  exact_mod_cast terminal

/-- Pulling a nonterminal full-tail pole backward across a final literal `D_c` either exposes a
genuine terminal match at the zero carrier or forces the preceding block's complete upper
power into its normalization scale. -/
theorem erasureTailPole_previousBlock_resonance_or_halts
    {width : Nat} (width_two : 2 ≤ width) (body : List TagLetter)
    (body_long : width - 1 ≤ body.length)
    {previousBlock : List NearyTile} (previous_role : IsRoleBlock previousBlock)
    (antecedent : CenteredState)
    {antecedentNumerator antecedentDenominator
      previousNumerator previousDenominator previousScale
      currentNumerator currentDenominator currentScale : ℤ}
    (antecedent_represented :
      RepresentsDefectRatio width antecedent antecedentNumerator antecedentDenominator)
    (antecedent_primitive :
      IsCoprime antecedentNumerator antecedentDenominator)
    (previous_primitive : IsCoprime previousNumerator previousDenominator)
    (current_primitive : IsCoprime currentNumerator currentDenominator)
    (previous_scale_ne : previousScale ≠ 0)
    (previous_numerator_eq :
      nextCarrierNumerator width body previousBlock
          antecedentNumerator antecedentDenominator =
        previousScale * previousNumerator)
    (previous_denominator_eq :
      nextCarrierDenominator width body previousBlock
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
    {target : List NearyTile}
    (target_tail : HasErasureTail width target)
    (current_y_ne :
      (blockStep width body [.erase .c]
        (blockStep width body previousBlock antecedent)).y ≠ 0)
    (pole :
      poleResidual width body target
        (blockStep width body [.erase .c]
          (blockStep width body previousBlock antecedent)) = 0)
    (nonterminal : currentDenominator - currentNumerator ≠ 0) :
    TagHaltsFrom width (tagOutput body) (body.drop (width - 1) ++ [.b]) ∨
      ∃ scaleDepth : Nat,
        HasValue 3 (previousScale : ℚ) scaleDepth ∧
          upperLength width previousBlock = scaleDepth ∧
            (3 : ℤ) ^ (scaleDepth + width - 1) ∣
              swappedUpperCode width previousBlock * antecedentDenominator -
                  swappedLowerCode width body previousBlock * antecedentNumerator -
                setterMarker width * 3 ^ scaleDepth * antecedentDenominator := by
  have previous_raw_represented :=
    blockStep_represents_nextCarrier width body previousBlock antecedent
      antecedentNumerator antecedentDenominator antecedent_represented
  rw [previous_numerator_eq, previous_denominator_eq] at previous_raw_represented
  have previous_represented :
      RepresentsDefectRatio width (blockStep width body previousBlock antecedent)
        previousNumerator previousDenominator :=
    RepresentsDefectRatio.of_common_scale previous_scale_ne previous_raw_represented
  have previous_numerator_divisible :
      (3 : ℤ) ^ (width - 1) ∣ previousNumerator :=
    literalDeletionC_erasureTailPole_forces_numeratorDivisible width_two body
      (blockStep width body previousBlock antecedent) previous_represented
      previous_primitive current_primitive current_scale_ne current_numerator_eq
      current_denominator_eq target_tail current_y_ne pole nonterminal
  by_cases previous_numerator_zero : previousNumerator = 0
  · have previous_denominator_unit : IsUnit previousDenominator := by
      apply previous_primitive.symm.isUnit_of_dvd
      rw [previous_numerator_zero]
      exact dvd_zero _
    have previous_denominator_ne : previousDenominator ≠ 0 := by
      rw [Int.isUnit_iff] at previous_denominator_unit
      omega
    exact Or.inl <| zeroNumerator_literalDeletionC_pole_halts width_two body body_long
      (blockStep width body previousBlock antecedent) previous_denominator_ne (by
        simpa [previous_numerator_zero] using previous_represented) current_y_ne pole
  · exact Or.inr <|
      primitiveDeepNumeratorSuccessor_forces_previousResonance width_two body previous_role
        antecedent_primitive previous_primitive previous_scale_ne previous_numerator_zero
        previous_numerator_divisible previous_numerator_eq previous_denominator_eq

/-- Across two final literal `D_c` blocks, a nonterminal full-tail pole either is already a
genuine terminal match or forces the carrier before the pair to be one modulo the full marker
power. -/
theorem doubleLiteralDeletionC_erasureTailPole_forces_halt_or_predecessorGap
    {width : Nat} (width_two : 2 ≤ width) (body : List TagLetter)
    (body_long : width - 1 ≤ body.length) (antecedent : CenteredState)
    {antecedentNumerator antecedentDenominator
      previousNumerator previousDenominator previousScale
      currentNumerator currentDenominator currentScale : ℤ}
    (antecedent_represented :
      RepresentsDefectRatio width antecedent antecedentNumerator antecedentDenominator)
    (antecedent_primitive :
      IsCoprime antecedentNumerator antecedentDenominator)
    (previous_primitive : IsCoprime previousNumerator previousDenominator)
    (current_primitive : IsCoprime currentNumerator currentDenominator)
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
    {target : List NearyTile}
    (target_tail : HasErasureTail width target)
    (current_y_ne :
      (blockStep width body [.erase .c]
        (blockStep width body [.erase .c] antecedent)).y ≠ 0)
    (pole :
      poleResidual width body target
        (blockStep width body [.erase .c]
          (blockStep width body [.erase .c] antecedent)) = 0)
    (nonterminal : currentDenominator - currentNumerator ≠ 0) :
    TagHaltsFrom width (tagOutput body) (body.drop (width - 1) ++ [.b]) ∨
      widthScale width ∣ antecedentDenominator - antecedentNumerator := by
  have role_block : IsRoleBlock ([.erase .c] : List NearyTile) :=
    ⟨[], .c, by simp⟩
  rcases erasureTailPole_previousBlock_resonance_or_halts width_two body body_long
      role_block antecedent antecedent_represented antecedent_primitive previous_primitive
      current_primitive previous_scale_ne previous_numerator_eq previous_denominator_eq
      current_scale_ne current_numerator_eq current_denominator_eq target_tail current_y_ne
      pole nonterminal with
    halts | ⟨scaleDepth, _, length_eq, cylinder_divisible⟩
  · exact Or.inl halts
  · exact Or.inr <|
      literalDeletionC_predecessorGap_of_cylinder body length_eq cylinder_divisible

end MatrixMortality.SwappedSetterBackwardResonance
