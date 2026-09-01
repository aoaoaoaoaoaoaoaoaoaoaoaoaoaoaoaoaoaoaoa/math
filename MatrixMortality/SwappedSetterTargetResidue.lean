import MatrixMortality.SwappedSetterTargetMultiplier

namespace MatrixMortality.SwappedSetterTargetResidue

open SwappedSetterMultitransfer SwappedSetterThresholdCarry SwappedSetterCarrierGap
  SwappedSetterCylinderCharge SwappedSetterTargetMultiplier
  SwappedSetterTargetMultiplier.ThreeBlockChargeWitness

private theorem signedSwappedCode_append_true_add_one_mod_three
    (word : List Bool) :
    signedSwappedCode (word ++ [true]) + 1 ≡ 2 [ZMOD 3] := by
  rw [Int.modEq_iff_dvd]
  rw [signedSwappedCode_append]
  have singleton_code : signedSwappedCode [true] = 1 := by
    norm_num [signedSwappedCode, ternaryCode, ternaryDigit]
  rw [singleton_code]
  refine ⟨-signedSwappedCode word, ?_⟩
  norm_num
  ring

private theorem signedSwappedCode_append_false_add_one_mod_three
    (word : List Bool) :
    signedSwappedCode (word ++ [false]) + 1 ≡ 0 [ZMOD 3] := by
  rw [Int.modEq_iff_dvd]
  rw [signedSwappedCode_append]
  have singleton_code : signedSwappedCode [false] = 2 := by
    norm_num [signedSwappedCode, ternaryCode, ternaryDigit]
  rw [singleton_code]
  refine ⟨-(signedSwappedCode word + 1), ?_⟩
  norm_num
  ring

private theorem spell_nearyLower_nonempty_ends_false
    (width : Nat) (body : List TagLetter) {front : List NearyTile}
    (front_ne : front ≠ []) :
    ∃ stem, spell (nearyLower width body) front = stem ++ [false] := by
  induction front using List.reverseRecOn with
  | nil => exact False.elim (front_ne rfl)
  | append_singleton front tile =>
      cases tile with
      | erase letter =>
          refine ⟨spell (nearyLower width body) front, ?_⟩
          cases letter <;> simp [spell, nearyLower]
      | rule letter =>
          cases letter with
          | b =>
              refine ⟨spell (nearyLower width body) front ++ [true, true], ?_⟩
              simp [spell, nearyLower, List.append_assoc]
          | c =>
              refine ⟨spell (nearyLower width body) front ++
                [true] ++ tagEncode width body ++ [true], ?_⟩
              simp [spell, nearyLower, List.append_assoc]

private theorem primitive_denominator_not_dvd_three_of_gap
    {width : Nat} (width_pos : 0 < width)
    {numerator denominator charge : ℤ}
    (primitive : IsCoprime numerator denominator)
    (gap_eq : denominator - numerator = 3 ^ width * charge) :
    ¬(3 : ℤ) ∣ denominator := by
  have power_dvd : (3 : ℤ) ∣ 3 ^ width :=
    dvd_pow_self 3 (Nat.ne_of_gt width_pos)
  have gap_dvd : (3 : ℤ) ∣ denominator - numerator := by
    rw [gap_eq]
    exact dvd_mul_of_dvd_left power_dvd charge
  intro denominator_dvd
  have numerator_dvd : (3 : ℤ) ∣ numerator := by
    have difference := denominator_dvd.sub gap_dvd
    simpa only [sub_sub_cancel] using difference
  have three_unit := primitive.isUnit_of_dvd' numerator_dvd denominator_dvd
  rw [Int.isUnit_iff] at three_unit
  omega

/-- The peeled target charge is forced to be a three-adic unit. The upper discarded prefix
ends in `true`, whereas every nonempty lower prefix ends in `false`; the empty lower prefix is
the only second case, and it has the same conclusion. -/
theorem erasureTailCharge_not_dvd_three
    {width : Nat} (width_pos : 0 < width) (body : List TagLetter)
    (target front : List NearyTile) {numerator denominator : ℤ}
    (primitive : IsCoprime numerator denominator)
    (gap_eq :
      denominator - numerator =
        3 ^ width *
          erasureTailCharge width body target front numerator denominator) :
    ¬(3 : ℤ) ∣
      erasureTailCharge width body target front numerator denominator := by
  let charge := erasureTailCharge width body target front numerator denominator
  have denominator_not_dvd : ¬(3 : ℤ) ∣ denominator :=
    primitive_denominator_not_dvd_three_of_gap width_pos primitive gap_eq
  have power_dvd : (3 : ℤ) ∣ 3 ^ width :=
    dvd_pow_self 3 (Nat.ne_of_gt width_pos)
  have gap_dvd : (3 : ℤ) ∣ denominator - numerator := by
    rw [gap_eq]
    exact dvd_mul_of_dvd_left power_dvd charge
  have denominator_numerator_mod : denominator ≡ numerator [ZMOD 3] := by
    rw [Int.modEq_iff_dvd]
    simpa only [neg_sub] using (dvd_neg.mpr gap_dvd)
  have upper_mod :
      signedSwappedCode (spell (nearyUpper width) target ++ [true]) + 1 ≡
        2 [ZMOD 3] :=
    signedSwappedCode_append_true_add_one_mod_three _
  intro charge_dvd
  have charge_zero : charge ≡ 0 [ZMOD 3] := charge_dvd.modEq_zero_int
  by_cases front_empty : front = []
  · subst front
    have lower_mod :
        signedSwappedCode (spell (nearyLower width body) []) + 1 ≡ 1 [ZMOD 3] := by
      norm_num [signedSwappedCode, spell]
    have raw_mod :=
      ((Int.ModEq.refl denominator).mul upper_mod).sub
        ((Int.ModEq.refl numerator).mul lower_mod)
    have target_mod : charge ≡ denominator [ZMOD 3] := by
      have reduced_mod :
          denominator * 2 - numerator * 1 ≡ denominator [ZMOD 3] := by
        have reduced :=
          ((Int.ModEq.refl (2 * denominator)).sub denominator_numerator_mod).symm
        have rhs_eq : 2 * denominator - denominator = denominator := by ring
        rw [rhs_eq] at reduced
        simpa [mul_comm] using reduced
      have charge_raw_mod :
          charge ≡ denominator * 2 - numerator * 1 [ZMOD 3] := by
        simpa [charge, erasureTailCharge] using raw_mod
      exact charge_raw_mod.trans reduced_mod
    have denominator_zero : denominator ≡ 0 [ZMOD 3] :=
      target_mod.symm.trans charge_zero
    have denominator_dvd : (3 : ℤ) ∣ denominator := by
      rw [Int.modEq_iff_dvd] at denominator_zero
      exact dvd_neg.mp (by simpa using denominator_zero)
    exact denominator_not_dvd denominator_dvd
  · obtain ⟨lowerPrefix, lower_eq⟩ :=
      spell_nearyLower_nonempty_ends_false width body front_empty
    have lower_mod :
        signedSwappedCode (spell (nearyLower width body) front) + 1 ≡ 0 [ZMOD 3] := by
      rw [lower_eq]
      exact signedSwappedCode_append_false_add_one_mod_three lowerPrefix
    have raw_mod :=
      ((Int.ModEq.refl denominator).mul upper_mod).sub
        ((Int.ModEq.refl numerator).mul lower_mod)
    have target_mod : charge ≡ 2 * denominator [ZMOD 3] := by
      simpa [charge, erasureTailCharge, mul_comm] using raw_mod
    have product_zero : 2 * denominator ≡ 0 [ZMOD 3] :=
      target_mod.symm.trans charge_zero
    have product_dvd : (3 : ℤ) ∣ 2 * denominator := by
      rw [Int.modEq_iff_dvd] at product_zero
      exact dvd_neg.mp (by simpa using product_zero)
    rcases (by norm_num : Prime (3 : ℤ)).dvd_mul.mp product_dvd with
      three_dvd_two | denominator_dvd
    · norm_num at three_dvd_two
    · exact denominator_not_dvd denominator_dvd

theorem witness_targetCharge_not_dvd_three
    {width : Nat} (width_pos : 0 < width) {body : List TagLetter}
    {precedingBlock target : List NearyTile}
    {originNumerator originDenominator
      antecedentNumerator antecedentDenominator antecedentScale
      previousNumerator previousDenominator previousScale
      currentNumerator currentDenominator currentScale : ℤ}
    (witness : ThreeBlockChargeWitness width body precedingBlock target
      originNumerator originDenominator
      antecedentNumerator antecedentDenominator antecedentScale
      previousNumerator previousDenominator previousScale
      currentNumerator currentDenominator currentScale)
    (current_primitive : IsCoprime currentNumerator currentDenominator) :
    ¬(3 : ℤ) ∣ witness.targetCharge := by
  have gap_eq :
      currentDenominator - currentNumerator =
        3 ^ width * erasureTailCharge width body target witness.front
          currentNumerator currentDenominator := by
    simpa only [← witness.targetCharge_eq] using witness.current_gap_eq
  have target_not_dvd :=
    erasureTailCharge_not_dvd_three width_pos body target witness.front
      current_primitive gap_eq
  simpa only [← witness.targetCharge_eq] using target_not_dvd

theorem witness_previousNumeratorCharge_not_dvd_three
    {width : Nat} (width_pos : 0 < width) {body : List TagLetter}
    {precedingBlock target : List NearyTile}
    {originNumerator originDenominator
      antecedentNumerator antecedentDenominator antecedentScale
      previousNumerator previousDenominator previousScale
      currentNumerator currentDenominator currentScale : ℤ}
    (witness : ThreeBlockChargeWitness width body precedingBlock target
      originNumerator originDenominator
      antecedentNumerator antecedentDenominator antecedentScale
      previousNumerator previousDenominator previousScale
      currentNumerator currentDenominator currentScale)
    (current_primitive : IsCoprime currentNumerator currentDenominator) :
    ¬(3 : ℤ) ∣ witness.previousNumeratorCharge := by
  have target_not_dvd :=
    witness_targetCharge_not_dvd_three width_pos witness current_primitive
  intro previous_dvd
  have rhs_dvd :
      (3 : ℤ) ∣ 2 * setterMarker width * witness.previousNumeratorCharge :=
    dvd_mul_of_dvd_right previous_dvd (2 * setterMarker width)
  rw [← witness.final_charge_eq] at rhs_dvd
  rcases (by norm_num : Prime (3 : ℤ)).dvd_mul.mp rhs_dvd with
    current_unit_dvd | target_dvd
  · exact witness.currentUnit_not_dvd current_unit_dvd
  · exact target_not_dvd target_dvd

theorem witness_middleAffineCharge_not_dvd_three
    {width : Nat} (width_pos : 0 < width) {body : List TagLetter}
    {precedingBlock target : List NearyTile}
    {originNumerator originDenominator
      antecedentNumerator antecedentDenominator antecedentScale
      previousNumerator previousDenominator previousScale
      currentNumerator currentDenominator currentScale : ℤ}
    (witness : ThreeBlockChargeWitness width body precedingBlock target
      originNumerator originDenominator
      antecedentNumerator antecedentDenominator antecedentScale
      previousNumerator previousDenominator previousScale
      currentNumerator currentDenominator currentScale)
    (current_primitive : IsCoprime currentNumerator currentDenominator) :
    ¬(3 : ℤ) ∣
      2 * witness.antecedentGapCharge - antecedentDenominator := by
  have previous_not_dvd :=
    witness_previousNumeratorCharge_not_dvd_three width_pos witness current_primitive
  intro affine_dvd
  have rhs_dvd :
      (3 : ℤ) ∣ terminalDiscrepancy width *
        (2 * witness.antecedentGapCharge - antecedentDenominator) :=
    dvd_mul_of_dvd_right affine_dvd (terminalDiscrepancy width)
  rw [← witness.middle_charge_eq] at rhs_dvd
  rcases (by norm_num : Prime (3 : ℤ)).dvd_mul.mp rhs_dvd with
    middle_unit_dvd | previous_dvd
  · exact witness.middleUnit_not_dvd middle_unit_dvd
  · exact previous_not_dvd previous_dvd

/-- At a primitive full-tail pole, both the literal first-mismatch discrepancy and its
predecessor-cylinder braid residual are three-adic units. -/
theorem witness_prefixDiscrepancy_and_braidResidual_not_dvd_three
    {width : Nat} (width_pos : 0 < width) {body : List TagLetter}
    {precedingBlock target : List NearyTile}
    {originNumerator originDenominator
      antecedentNumerator antecedentDenominator antecedentScale
      previousNumerator previousDenominator previousScale
      currentNumerator currentDenominator currentScale : ℤ}
    (witness : ThreeBlockChargeWitness width body precedingBlock target
      originNumerator originDenominator
      antecedentNumerator antecedentDenominator antecedentScale
      previousNumerator previousDenominator previousScale
      currentNumerator currentDenominator currentScale)
    (current_primitive : IsCoprime currentNumerator currentDenominator)
    (threshold :
      currentDenominator * swappedUpperCode width target =
        currentNumerator * swappedLowerCode width body target) :
    ¬(3 : ℤ) ∣ targetPrefixDiscrepancy width body target witness.front ∧
      ¬(3 : ℤ) ∣
        predecessorBraidResidual width witness.initialUnit
          witness.initialCylinderQuotient antecedentDenominator := by
  obtain ⟨multiplier, properties, -⟩ :=
    existsUnique_targetMultiplier_braid width_pos current_primitive threshold witness
  have prefix_not_dvd :
      ¬(3 : ℤ) ∣ targetPrefixDiscrepancy width body target witness.front :=
    targetPrefixDiscrepancy_not_dvd_three width body target witness.front
  have residual_not_dvd :=
    predecessorBraidResidual_not_dvd_three witness properties.2.2.2.2.2.2
  exact ⟨prefix_not_dvd, residual_not_dvd⟩

/-- The first unequal discarded ternary digit fixes the charge residue. An empty lower prefix
gives `q ≡ d`; every nonempty lower prefix ends in `false` and gives `q ≡ −d`. -/
theorem erasureTailCharge_front_residue
    {width : Nat} (width_pos : 0 < width) (body : List TagLetter)
    (target front : List NearyTile) {numerator denominator : ℤ}
    (gap_eq :
      denominator - numerator =
        3 ^ width *
          erasureTailCharge width body target front numerator denominator) :
    (front = [] ∧
        erasureTailCharge width body target front numerator denominator ≡
          denominator [ZMOD 3]) ∨
      (front ≠ [] ∧
        erasureTailCharge width body target front numerator denominator ≡
          2 * denominator [ZMOD 3]) := by
  let charge := erasureTailCharge width body target front numerator denominator
  have power_dvd : (3 : ℤ) ∣ 3 ^ width :=
    dvd_pow_self 3 (Nat.ne_of_gt width_pos)
  have gap_dvd : (3 : ℤ) ∣ denominator - numerator := by
    rw [gap_eq]
    exact dvd_mul_of_dvd_left power_dvd charge
  have denominator_numerator_mod : denominator ≡ numerator [ZMOD 3] := by
    rw [Int.modEq_iff_dvd]
    simpa only [neg_sub] using (dvd_neg.mpr gap_dvd)
  have upper_mod :
      signedSwappedCode (spell (nearyUpper width) target ++ [true]) + 1 ≡
        2 [ZMOD 3] :=
    signedSwappedCode_append_true_add_one_mod_three _
  by_cases front_empty : front = []
  · subst front
    apply Or.inl
    refine ⟨rfl, ?_⟩
    have lower_mod :
        signedSwappedCode (spell (nearyLower width body) []) + 1 ≡ 1 [ZMOD 3] := by
      norm_num [signedSwappedCode, spell]
    have raw_mod :=
      ((Int.ModEq.refl denominator).mul upper_mod).sub
        ((Int.ModEq.refl numerator).mul lower_mod)
    have reduced_mod :
        denominator * 2 - numerator * 1 ≡ denominator [ZMOD 3] := by
      have reduced :=
        ((Int.ModEq.refl (2 * denominator)).sub denominator_numerator_mod).symm
      have rhs_eq : 2 * denominator - denominator = denominator := by ring
      rw [rhs_eq] at reduced
      simpa [mul_comm] using reduced
    have charge_raw_mod :
        erasureTailCharge width body target [] numerator denominator ≡
          denominator * 2 - numerator * 1 [ZMOD 3] := by
      simpa [erasureTailCharge] using raw_mod
    exact charge_raw_mod.trans reduced_mod
  · apply Or.inr
    refine ⟨front_empty, ?_⟩
    obtain ⟨lowerStem, lower_eq⟩ :=
      spell_nearyLower_nonempty_ends_false width body front_empty
    have lower_mod :
        signedSwappedCode (spell (nearyLower width body) front) + 1 ≡ 0 [ZMOD 3] := by
      rw [lower_eq]
      exact signedSwappedCode_append_false_add_one_mod_three lowerStem
    have raw_mod :=
      ((Int.ModEq.refl denominator).mul upper_mod).sub
        ((Int.ModEq.refl numerator).mul lower_mod)
    simpa [erasureTailCharge, mul_comm] using raw_mod

private theorem deletionC_middle_denominator_coordinate
    {width : Nat} (width_pos : 0 < width) (body : List TagLetter)
    {antecedentNumerator antecedentDenominator previousDenominator previousScale
      middleUnit antecedentGapCharge : ℤ}
    (scale_eq : previousScale = 3 * middleUnit)
    (denominator_eq :
      nextCarrierDenominator width body [.erase .c]
          antecedentNumerator antecedentDenominator =
        previousScale * previousDenominator)
    (gap_eq :
      antecedentDenominator - antecedentNumerator =
        3 ^ width * antecedentGapCharge) :
    middleUnit * previousDenominator =
      centeredCoefficient width *
        ((5 * 3 ^ (width - 1) - 1) * antecedentDenominator +
          2 * 3 ^ (width - 1) * antecedentGapCharge) := by
  have power_eq : (3 : ℤ) ^ width = 3 * 3 ^ (width - 1) := by
    calc
      (3 : ℤ) ^ width = 3 ^ ((width - 1) + 1) := by
        congr 1
        omega
      _ = 3 ^ (width - 1) * 3 := pow_succ _ _
      _ = 3 * 3 ^ (width - 1) := mul_comm _ _
  have raw_denominator_eq :
      nextCarrierDenominator width body [.erase .c]
          antecedentNumerator antecedentDenominator =
        3 *
          (centeredCoefficient width *
            ((5 * 3 ^ (width - 1) - 1) * antecedentDenominator +
              2 * 3 ^ (width - 1) * antecedentGapCharge)) := by
    simp only [nextCarrierDenominator, swappedUpperCode_singleton_c,
      swappedLowerCode_singleton]
    simp only [centeredCoefficient, terminalDiscrepancy, widthScale] at gap_eq ⊢
    rw [power_eq] at gap_eq ⊢
    linear_combination
      2 * (2 - 3 * (3 : ℤ) ^ (width - 1)) * gap_eq
  apply mul_left_cancel₀ (show (3 : ℤ) ≠ 0 by norm_num)
  calc
    3 * (middleUnit * previousDenominator) =
        previousScale * previousDenominator := by rw [scale_eq]; ring
    _ = nextCarrierDenominator width body [.erase .c]
        antecedentNumerator antecedentDenominator := denominator_eq.symm
    _ = _ := raw_denominator_eq

private theorem deletionC_final_denominator_coordinate
    {width : Nat} (body : List TagLetter)
    {previousNumerator previousDenominator currentDenominator currentScale
      currentUnit previousNumeratorCharge : ℤ}
    (scale_eq : currentScale = currentUnit)
    (denominator_eq :
      nextCarrierDenominator width body [.erase .c]
          previousNumerator previousDenominator =
        currentScale * currentDenominator)
    (deep_numerator_eq :
      previousNumerator = 3 ^ (width - 1) * previousNumeratorCharge) :
    currentUnit * currentDenominator =
      centeredCoefficient width *
        (terminalDiscrepancy width * previousDenominator -
          2 * 3 ^ (width - 1) * previousNumeratorCharge) := by
  rw [← scale_eq, ← denominator_eq]
  simp only [nextCarrierDenominator, swappedUpperCode_singleton_c,
    swappedLowerCode_singleton]
  rw [deep_numerator_eq]
  ring

/-- The target's first unequal discarded digit determines the only two possible initial-gap
residues. If the matched erasure tail is the whole target, then `3 ∣ q₀`; otherwise
`q₀ ≡ d₀ (mod 3)`. -/
theorem witness_front_gap_residue_fork
    {width : Nat} (width_two : 2 ≤ width) {body : List TagLetter}
    {precedingBlock target : List NearyTile}
    {originNumerator originDenominator
      antecedentNumerator antecedentDenominator antecedentScale
      previousNumerator previousDenominator previousScale
      currentNumerator currentDenominator currentScale : ℤ}
    (witness : ThreeBlockChargeWitness width body precedingBlock target
      originNumerator originDenominator
      antecedentNumerator antecedentDenominator antecedentScale
      previousNumerator previousDenominator previousScale
      currentNumerator currentDenominator currentScale)
    (previous_denominator_eq :
      nextCarrierDenominator width body [.erase .c]
          antecedentNumerator antecedentDenominator =
        previousScale * previousDenominator)
    (current_denominator_eq :
      nextCarrierDenominator width body [.erase .c]
          previousNumerator previousDenominator =
        currentScale * currentDenominator) :
    (witness.front = [] ∧ (3 : ℤ) ∣ witness.antecedentGapCharge) ∨
      (witness.front ≠ [] ∧
        witness.antecedentGapCharge ≡ antecedentDenominator [ZMOD 3]) := by
  have width_pos : 0 < width := by omega
  have predecessor_power_pos : 0 < width - 1 := by omega
  have predecessor_power_dvd : (3 : ℤ) ∣ 3 ^ (width - 1) :=
    dvd_pow_self 3 (Nat.ne_of_gt predecessor_power_pos)
  have predecessor_power_mod : (3 : ℤ) ^ (width - 1) ≡ 0 [ZMOD 3] :=
    predecessor_power_dvd.modEq_zero_int
  have width_power_dvd : (3 : ℤ) ∣ 3 ^ width :=
    dvd_pow_self 3 (Nat.ne_of_gt width_pos)
  have scale_mod : widthScale width ≡ 0 [ZMOD 3] := by
    simpa only [widthScale] using width_power_dvd.modEq_zero_int
  have centered_mod : centeredCoefficient width ≡ 2 [ZMOD 3] := by
    have raw := (Int.ModEq.refl (2 : ℤ)).sub scale_mod
    simpa only [centeredCoefficient] using raw.trans (by norm_num)
  have terminal_mod : terminalDiscrepancy width ≡ 2 [ZMOD 3] := by
    have raw := ((Int.ModEq.refl (5 : ℤ)).mul scale_mod).sub
      (Int.ModEq.refl (1 : ℤ))
    simpa only [terminalDiscrepancy] using raw.trans (by norm_num)
  have marker_mod : setterMarker width ≡ 2 [ZMOD 3] := by
    have raw := ((Int.ModEq.refl (2 : ℤ)).mul scale_mod).sub
      (Int.ModEq.refl (1 : ℤ))
    simpa only [setterMarker] using raw.trans (by norm_num)
  have middle_denominator_eq :=
    deletionC_middle_denominator_coordinate width_pos body witness.middle_scale_eq
      previous_denominator_eq witness.antecedent_gap_eq
  have final_denominator_eq :=
    deletionC_final_denominator_coordinate body witness.current_scale_eq
      current_denominator_eq witness.previous_numerator_eq
  have five_predecessor_sub_one_mod :
      5 * (3 : ℤ) ^ (width - 1) - 1 ≡ 2 [ZMOD 3] := by
    have raw := ((Int.ModEq.refl (5 : ℤ)).mul predecessor_power_mod).sub
      (Int.ModEq.refl (1 : ℤ))
    exact raw.trans (by norm_num)
  have middle_inner_mod :
      (5 * 3 ^ (width - 1) - 1) * antecedentDenominator +
          2 * 3 ^ (width - 1) * witness.antecedentGapCharge ≡
        2 * antecedentDenominator [ZMOD 3] := by
    have first := five_predecessor_sub_one_mod.mul
      (Int.ModEq.refl antecedentDenominator)
    have second := ((Int.ModEq.refl (2 : ℤ)).mul predecessor_power_mod).mul
      (Int.ModEq.refl witness.antecedentGapCharge)
    simpa using first.add second
  have middle_denominator_mod :
      witness.middleUnit * previousDenominator ≡
        antecedentDenominator [ZMOD 3] := by
    rw [middle_denominator_eq]
    have raw := centered_mod.mul middle_inner_mod
    exact raw.trans (by
      rw [Int.modEq_iff_dvd]
      refine ⟨-antecedentDenominator, by ring⟩)
  have final_inner_mod :
      terminalDiscrepancy width * previousDenominator -
          2 * 3 ^ (width - 1) * witness.previousNumeratorCharge ≡
        2 * previousDenominator [ZMOD 3] := by
    have first := terminal_mod.mul (Int.ModEq.refl previousDenominator)
    have second := ((Int.ModEq.refl (2 : ℤ)).mul predecessor_power_mod).mul
      (Int.ModEq.refl witness.previousNumeratorCharge)
    simpa using first.sub second
  have final_denominator_mod :
      witness.currentUnit * currentDenominator ≡
        previousDenominator [ZMOD 3] := by
    rw [final_denominator_eq]
    have raw := centered_mod.mul final_inner_mod
    exact raw.trans (by
      rw [Int.modEq_iff_dvd]
      refine ⟨-previousDenominator, by ring⟩)
  have denominator_product_mod :
      witness.middleUnit * witness.currentUnit * currentDenominator ≡
        antecedentDenominator [ZMOD 3] := by
    have scaled_final := (Int.ModEq.refl witness.middleUnit).mul final_denominator_mod
    have scaled_final' :
        witness.middleUnit * (witness.currentUnit * currentDenominator) ≡
          witness.middleUnit * previousDenominator [ZMOD 3] := by
      simpa using scaled_final
    have scaled_final'' :
        witness.middleUnit * witness.currentUnit * currentDenominator ≡
          witness.middleUnit * previousDenominator [ZMOD 3] := by
      simpa [mul_assoc] using scaled_final'
    exact scaled_final''.trans middle_denominator_mod
  have charge_product_eq :
      witness.middleUnit * witness.currentUnit * witness.targetCharge =
        2 * setterMarker width * terminalDiscrepancy width *
          (2 * witness.antecedentGapCharge - antecedentDenominator) := by
    calc
      witness.middleUnit * witness.currentUnit * witness.targetCharge =
          witness.middleUnit * (witness.currentUnit * witness.targetCharge) := by ring
      _ = witness.middleUnit *
          (2 * setterMarker width * witness.previousNumeratorCharge) := by
            rw [witness.final_charge_eq]
      _ = 2 * setterMarker width *
          (witness.middleUnit * witness.previousNumeratorCharge) := by ring
      _ = 2 * setterMarker width * terminalDiscrepancy width *
          (2 * witness.antecedentGapCharge - antecedentDenominator) := by
            rw [witness.middle_charge_eq]
            ring
  have charge_coefficient_mod :
      2 * setterMarker width * terminalDiscrepancy width ≡ 2 [ZMOD 3] := by
    have raw := ((Int.ModEq.refl (2 : ℤ)).mul marker_mod).mul terminal_mod
    exact raw.trans (by norm_num)
  have affine_mod :
      2 * witness.antecedentGapCharge - antecedentDenominator ≡
        2 * witness.antecedentGapCharge - antecedentDenominator [ZMOD 3] :=
    Int.ModEq.refl _
  have charge_product_mod :
      witness.middleUnit * witness.currentUnit * witness.targetCharge ≡
        witness.antecedentGapCharge + antecedentDenominator [ZMOD 3] := by
    rw [charge_product_eq]
    have raw := charge_coefficient_mod.mul affine_mod
    exact raw.trans (by
      rw [Int.modEq_iff_dvd]
      refine ⟨antecedentDenominator - witness.antecedentGapCharge, by ring⟩)
  have current_gap_erasure :
      currentDenominator - currentNumerator =
        3 ^ width * erasureTailCharge width body target witness.front
          currentNumerator currentDenominator := by
    rw [← witness.targetCharge_eq]
    exact witness.current_gap_eq
  have target_residue :=
    erasureTailCharge_front_residue
      (numerator := currentNumerator) (denominator := currentDenominator)
      width_pos body target witness.front current_gap_erasure
  rcases target_residue with ⟨front_empty, target_mod⟩ | ⟨front_ne, target_mod⟩
  · apply Or.inl
    refine ⟨front_empty, ?_⟩
    rw [← witness.targetCharge_eq] at target_mod
    have scaled_target :=
      (Int.ModEq.refl (witness.middleUnit * witness.currentUnit)).mul target_mod
    have scaled_target' :
        witness.middleUnit * witness.currentUnit * witness.targetCharge ≡
          witness.middleUnit * witness.currentUnit * currentDenominator [ZMOD 3] := by
      simpa [mul_assoc] using scaled_target
    have gap_zero_mod : witness.antecedentGapCharge ≡ 0 [ZMOD 3] := by
      have combined :
          witness.antecedentGapCharge + antecedentDenominator ≡
            antecedentDenominator [ZMOD 3] :=
        charge_product_mod.symm.trans <|
          scaled_target'.trans denominator_product_mod
      simpa using combined.sub (Int.ModEq.refl antecedentDenominator)
    rw [Int.modEq_iff_dvd] at gap_zero_mod
    exact dvd_neg.mp (by simpa using gap_zero_mod)
  · apply Or.inr
    refine ⟨front_ne, ?_⟩
    rw [← witness.targetCharge_eq] at target_mod
    have scaled_target :=
      (Int.ModEq.refl (witness.middleUnit * witness.currentUnit)).mul target_mod
    have scaled_target' :
        witness.middleUnit * witness.currentUnit * witness.targetCharge ≡
          2 * (witness.middleUnit * witness.currentUnit * currentDenominator) [ZMOD 3] := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using scaled_target
    have twice_denominator_mod :
        2 * (witness.middleUnit * witness.currentUnit * currentDenominator) ≡
          2 * antecedentDenominator [ZMOD 3] :=
      (Int.ModEq.refl (2 : ℤ)).mul denominator_product_mod
    have combined :
        witness.antecedentGapCharge + antecedentDenominator ≡
          2 * antecedentDenominator [ZMOD 3] :=
      charge_product_mod.symm.trans <|
        scaled_target'.trans twice_denominator_mod
    have reduced := combined.sub (Int.ModEq.refl antecedentDenominator)
    have rhs_eq : 2 * antecedentDenominator - antecedentDenominator =
        antecedentDenominator := by ring
    rw [rhs_eq] at reduced
    simpa using reduced

private theorem initial_denominator_coordinate
    {width initialDepth : Nat} (width_pos : 0 < width)
    (body : List TagLetter) (block : List NearyTile)
    {originNumerator originDenominator antecedentDenominator antecedentScale
      initialUnit initialCylinderQuotient : ℤ}
    (scale_eq : antecedentScale = 3 ^ initialDepth * initialUnit)
    (cylinder_eq :
      predecessorCylinder width body block initialDepth
          originNumerator originDenominator =
        3 ^ (initialDepth + width - 1) * initialCylinderQuotient)
    (denominator_eq :
      nextCarrierDenominator width body block originNumerator originDenominator =
        antecedentScale * antecedentDenominator) :
    initialUnit * antecedentDenominator =
      centeredCoefficient width *
        (terminalDiscrepancy width * originDenominator +
          3 ^ (width - 1) * initialCylinderQuotient) := by
  have exponent_eq :
      initialDepth + width - 1 = initialDepth + (width - 1) := by omega
  have raw_denominator_eq :
      nextCarrierDenominator width body block originNumerator originDenominator =
        3 ^ initialDepth *
          (centeredCoefficient width *
            (terminalDiscrepancy width * originDenominator +
              3 ^ (width - 1) * initialCylinderQuotient)) := by
    rw [nextCarrierDenominator]
    rw [predecessorCylinder, exponent_eq, pow_add] at cylinder_eq
    simp only [centeredCoefficient, terminalDiscrepancy,
      widthScale] at cylinder_eq ⊢
    linear_combination (2 - (3 : ℤ) ^ width) * cylinder_eq
  apply mul_left_cancel₀
    (pow_ne_zero initialDepth (show (3 : ℤ) ≠ 0 by norm_num))
  calc
    3 ^ initialDepth * (initialUnit * antecedentDenominator) =
        antecedentScale * antecedentDenominator := by rw [scale_eq]; ring
    _ = nextCarrierDenominator width body block originNumerator originDenominator :=
      denominator_eq.symm
    _ = _ := raw_denominator_eq

/-- Pushing the first-mismatch fork through the initial cylinder gives the corresponding
residue of the reachable cylinder quotient itself. -/
theorem witness_front_initialCylinder_residue_fork
    {width : Nat} (width_two : 2 ≤ width) {body : List TagLetter}
    {precedingBlock target : List NearyTile}
    {originNumerator originDenominator
      antecedentNumerator antecedentDenominator antecedentScale
      previousNumerator previousDenominator previousScale
      currentNumerator currentDenominator currentScale : ℤ}
    (witness : ThreeBlockChargeWitness width body precedingBlock target
      originNumerator originDenominator
      antecedentNumerator antecedentDenominator antecedentScale
      previousNumerator previousDenominator previousScale
      currentNumerator currentDenominator currentScale)
    (antecedent_denominator_eq :
      nextCarrierDenominator width body precedingBlock originNumerator originDenominator =
        antecedentScale * antecedentDenominator)
    (previous_denominator_eq :
      nextCarrierDenominator width body [.erase .c]
          antecedentNumerator antecedentDenominator =
        previousScale * previousDenominator)
    (current_denominator_eq :
      nextCarrierDenominator width body [.erase .c]
          previousNumerator previousDenominator =
        currentScale * currentDenominator) :
    (witness.front = [] ∧ (3 : ℤ) ∣ witness.initialCylinderQuotient) ∨
      (witness.front ≠ [] ∧
        witness.initialCylinderQuotient ≡ originDenominator [ZMOD 3]) := by
  have width_pos : 0 < width := by omega
  have gap_fork := witness_front_gap_residue_fork width_two witness
    previous_denominator_eq current_denominator_eq
  have initial_denominator_eq :=
    initial_denominator_coordinate width_pos body precedingBlock
      witness.initial_scale_eq witness.initial_cylinder_eq antecedent_denominator_eq
  have predecessor_power_pos : 0 < width - 1 := by omega
  have predecessor_power_dvd : (3 : ℤ) ∣ 3 ^ (width - 1) :=
    dvd_pow_self 3 (Nat.ne_of_gt predecessor_power_pos)
  have predecessor_power_mod : (3 : ℤ) ^ (width - 1) ≡ 0 [ZMOD 3] :=
    predecessor_power_dvd.modEq_zero_int
  have width_power_dvd : (3 : ℤ) ∣ 3 ^ width :=
    dvd_pow_self 3 (Nat.ne_of_gt width_pos)
  have scale_mod : widthScale width ≡ 0 [ZMOD 3] := by
    simpa only [widthScale] using width_power_dvd.modEq_zero_int
  have centered_mod : centeredCoefficient width ≡ 2 [ZMOD 3] := by
    have raw := (Int.ModEq.refl (2 : ℤ)).sub scale_mod
    simpa only [centeredCoefficient] using raw.trans (by norm_num)
  have terminal_mod : terminalDiscrepancy width ≡ 2 [ZMOD 3] := by
    have raw := ((Int.ModEq.refl (5 : ℤ)).mul scale_mod).sub
      (Int.ModEq.refl (1 : ℤ))
    simpa only [terminalDiscrepancy] using raw.trans (by norm_num)
  have initial_inner_mod :
      terminalDiscrepancy width * originDenominator +
          3 ^ (width - 1) * witness.initialCylinderQuotient ≡
        2 * originDenominator [ZMOD 3] := by
    have first := terminal_mod.mul (Int.ModEq.refl originDenominator)
    have second := predecessor_power_mod.mul
      (Int.ModEq.refl witness.initialCylinderQuotient)
    simpa using first.add second
  have initial_denominator_mod :
      witness.initialUnit * antecedentDenominator ≡
        originDenominator [ZMOD 3] := by
    rw [initial_denominator_eq]
    have raw := centered_mod.mul initial_inner_mod
    exact raw.trans (by
      rw [Int.modEq_iff_dvd]
      refine ⟨-originDenominator, by ring⟩)
  have cylinder_gap_mod :
      witness.initialCylinderQuotient ≡
        witness.initialUnit * witness.antecedentGapCharge [ZMOD 3] := by
    rw [Int.modEq_iff_dvd]
    have difference_eq :
        witness.initialUnit * witness.antecedentGapCharge -
            witness.initialCylinderQuotient =
          -2 * widthScale width * witness.initialCylinderQuotient := by
      have charge_eq := witness.initial_charge_eq
      simp only [setterMarker] at charge_eq
      linear_combination charge_eq
    rw [difference_eq]
    have scale_dvd : (3 : ℤ) ∣ widthScale width := by
      simpa only [widthScale] using width_power_dvd
    have product_dvd := dvd_mul_of_dvd_left scale_dvd
      (-2 * witness.initialCylinderQuotient)
    simpa only [mul_assoc, mul_comm, mul_left_comm] using product_dvd
  rcases gap_fork with ⟨front_empty, gap_dvd⟩ | ⟨front_ne, gap_mod⟩
  · apply Or.inl
    refine ⟨front_empty, ?_⟩
    have gap_zero : witness.antecedentGapCharge ≡ 0 [ZMOD 3] :=
      gap_dvd.modEq_zero_int
    have scaled_gap := (Int.ModEq.refl witness.initialUnit).mul gap_zero
    have cylinder_zero : witness.initialCylinderQuotient ≡ 0 [ZMOD 3] :=
      cylinder_gap_mod.trans <| by simpa using scaled_gap
    rw [Int.modEq_iff_dvd] at cylinder_zero
    exact dvd_neg.mp (by simpa using cylinder_zero)
  · apply Or.inr
    refine ⟨front_ne, ?_⟩
    have scaled_gap := (Int.ModEq.refl witness.initialUnit).mul gap_mod
    have scaled_gap' :
        witness.initialUnit * witness.antecedentGapCharge ≡
          witness.initialUnit * antecedentDenominator [ZMOD 3] := by
      simpa using scaled_gap
    exact cylinder_gap_mod.trans <| scaled_gap'.trans initial_denominator_mod

end MatrixMortality.SwappedSetterTargetResidue
