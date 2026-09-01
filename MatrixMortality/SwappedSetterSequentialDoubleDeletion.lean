import MatrixMortality.SwappedSetterBackwardResonance

/-!
# Sequential distinguished deletion extinction
-/

namespace MatrixMortality.SwappedSetterSequentialDoubleDeletion

open SwappedSetterMultitransfer SwappedSetterHistory SwappedSetterThresholdCarry
  SwappedSetterCarrierGap SwappedSetterBackwardResonance

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

private theorem signedSwappedCode_append_true (headWord : List Bool) :
    signedSwappedCode (headWord ++ [true]) =
      3 * signedSwappedCode headWord + 1 := by
  rw [signedSwappedCode_append]
  norm_num [signedSwappedCode, ternaryCode, ternaryDigit]

private theorem not_three_dvd_signedSwappedCode_of_ne_nil
    {word : List Bool} (word_ne : word ≠ []) :
    ¬(3 : ℤ) ∣ signedSwappedCode word := by
  induction word using List.reverseRecOn with
  | nil => exact (word_ne rfl).elim
  | append_singleton headWord bit =>
      intro divides
      obtain ⟨factor, factor_eq⟩ := divides
      rw [signedSwappedCode_append] at factor_eq
      cases bit <;>
        norm_num [signedSwappedCode, ternaryCode, ternaryDigit] at factor_eq <;>
        omega

private theorem halfScale_nonneg (width : Nat) : 0 ≤ halfScale width := by
  induction width with
  | zero => rfl
  | succ width induction =>
      simp [halfScale]
      omega

private theorem doubleDeletion_denominator_gt_markerProduct
    {offset : Nat} (offset_pos : 0 < offset) :
    setterMarker (offset + 1) * (widthScale (offset + 1) - 1) <
      distinguishedDoubleDeletionCDenominator offset := by
  have scale_ge : (9 : ℤ) ≤ widthScale (offset + 1) := by
    have exponent_le : 2 ≤ offset + 1 := by omega
    have power_le : (3 : Nat) ^ 2 ≤ 3 ^ (offset + 1) :=
      Nat.pow_le_pow_right (by norm_num) exponent_le
    have casted : ((3 ^ 2 : Nat) : ℤ) ≤ ((3 ^ (offset + 1) : Nat) : ℤ) := by
      exact_mod_cast power_le
    simpa [widthScale] using casted
  have half_pos : 0 < halfScale offset := by
    rw [widthScale_succ_eq_six_halfScale_add_three] at scale_ge
    omega
  rw [setterMarker, widthScale_succ_eq_six_halfScale_add_three]
  simp [distinguishedDoubleDeletionCDenominator]
  nlinarith [sq_nonneg (halfScale offset),
    mul_pos half_pos (sq_pos_of_pos half_pos)]

private theorem threshold_reduced_prefix_equation
    {offset : Nat} (body : List TagLetter) {target : List NearyTile}
    (target_tail : HasErasureTail (offset + 1) target)
    (threshold :
      distinguishedDoubleDeletionCDenominator offset *
          swappedUpperCode (offset + 1) target =
        distinguishedDoubleDeletionCNumerator offset *
          swappedLowerCode (offset + 1) body target) :
    ∃ upperPrefix lowerPrefix : List Bool,
      upperPrefix = spell (nearyUpper (offset + 1)) target ++ [true] ∧
        distinguishedDoubleDeletionCDenominator offset *
              signedSwappedCode upperPrefix -
            distinguishedDoubleDeletionCNumerator offset *
              signedSwappedCode lowerPrefix =
          setterMarker (offset + 1) * (widthScale (offset + 1) - 1) := by
  obtain ⟨front, letters, letters_length, target_eq⟩ := target_tail
  let upperPrefix := spell (nearyUpper (offset + 1)) target ++ [true]
  let lowerPrefix := spell (nearyLower (offset + 1) body) front
  have upper_factorization :
      spell (nearyUpper (offset + 1)) target ++ nearyMarker (offset + 1) =
        upperPrefix ++ List.replicate (offset + 1) false := by
    simp [upperPrefix, nearyMarker, List.append_assoc]
  have lower_factorization :
      spell (nearyLower (offset + 1) body) target =
        lowerPrefix ++ List.replicate (offset + 1) false := by
    rw [target_eq, spell_append, spell_nearyLower_erase_map, letters_length]
  have upper_code_eq :
      swappedUpperCode (offset + 1) target =
        widthScale (offset + 1) * signedSwappedCode upperPrefix +
          (widthScale (offset + 1) - 1) := by
    rw [swappedUpperCode]
    change signedSwappedCode
        (spell (nearyUpper (offset + 1)) target ++ nearyMarker (offset + 1)) = _
    rw [upper_factorization, signedSwappedCode_append,
      signedSwappedCode_replicate_false]
    simp [widthScale]
  have lower_code_eq :
      swappedLowerCode (offset + 1) body target =
        widthScale (offset + 1) * signedSwappedCode lowerPrefix +
          (widthScale (offset + 1) - 1) := by
    rw [swappedLowerCode]
    change signedSwappedCode (spell (nearyLower (offset + 1) body) target) = _
    rw [lower_factorization, signedSwappedCode_append,
      signedSwappedCode_replicate_false]
    simp [widthScale]
  rw [upper_code_eq, lower_code_eq] at threshold
  have scale_ne : widthScale (offset + 1) ≠ 0 := by simp [widthScale]
  have expanded :
      widthScale (offset + 1) *
          (distinguishedDoubleDeletionCDenominator offset *
                signedSwappedCode upperPrefix -
              distinguishedDoubleDeletionCNumerator offset *
                signedSwappedCode lowerPrefix -
            setterMarker (offset + 1) * (widthScale (offset + 1) - 1)) = 0 := by
    have gap := distinguishedDoubleDeletionC_gap offset
    linear_combination threshold + (widthScale (offset + 1) - 1) * gap
  have reduced :
      distinguishedDoubleDeletionCDenominator offset *
            signedSwappedCode upperPrefix -
          distinguishedDoubleDeletionCNumerator offset *
            signedSwappedCode lowerPrefix =
        setterMarker (offset + 1) * (widthScale (offset + 1) - 1) := by
    have bracket_zero := (mul_eq_zero.mp expanded).resolve_left scale_ne
    linarith
  exact ⟨upperPrefix, lowerPrefix, rfl, reduced⟩

/-- The primitive carrier after two sequential distinguished `D_c` transfers cannot meet any
target threshold with a full erasure tail. -/
theorem distinguishedDoubleDeletionC_avoids_erasureTail_threshold
    {offset : Nat} (offset_pos : 0 < offset) (body : List TagLetter)
    {target : List NearyTile} (target_tail : HasErasureTail (offset + 1) target)
    (threshold :
      distinguishedDoubleDeletionCDenominator offset *
          swappedUpperCode (offset + 1) target =
        distinguishedDoubleDeletionCNumerator offset *
          swappedLowerCode (offset + 1) body target) : False := by
  obtain ⟨upperPrefix, lowerPrefix, upperPrefix_eq, reduced⟩ :=
    threshold_reduced_prefix_equation body target_tail threshold
  have upper_mod :
      ∃ quotient : ℤ, signedSwappedCode upperPrefix = 3 * quotient + 1 := by
    refine ⟨signedSwappedCode (spell (nearyUpper (offset + 1)) target), ?_⟩
    rw [upperPrefix_eq, signedSwappedCode_append_true]
  let half := halfScale offset
  have denominator_mod :
      ∃ quotient : ℤ,
        distinguishedDoubleDeletionCDenominator offset = 3 * quotient + 1 := by
    refine ⟨60 * half ^ 3 + 40 * half ^ 2 + 7 * half, ?_⟩
    simp [distinguishedDoubleDeletionCDenominator, half]
    ring
  have numerator_mod :
      ∃ quotient : ℤ,
        distinguishedDoubleDeletionCNumerator offset = 3 * quotient + 1 := by
    refine ⟨60 * half ^ 3 + 64 * half ^ 2 + 29 * half + 5, ?_⟩
    simp [distinguishedDoubleDeletionCNumerator, half]
    ring
  have marker_mod :
      ∃ quotient : ℤ, setterMarker (offset + 1) = 3 * quotient - 1 := by
    refine ⟨2 * widthScale offset, ?_⟩
    simp [setterMarker, widthScale, pow_succ]
    ring
  have scale_sub_mod :
      ∃ quotient : ℤ, widthScale (offset + 1) - 1 = 3 * quotient - 1 := by
    refine ⟨widthScale offset, ?_⟩
    simp [widthScale, pow_succ]
    ring
  obtain ⟨upperQuotient, upper_eq⟩ := upper_mod
  obtain ⟨denominatorQuotient, denominator_eq⟩ := denominator_mod
  obtain ⟨numeratorQuotient, numerator_eq⟩ := numerator_mod
  obtain ⟨markerQuotient, marker_eq⟩ := marker_mod
  obtain ⟨scaleQuotient, scale_eq⟩ := scale_sub_mod
  have lower_divisible : (3 : ℤ) ∣ signedSwappedCode lowerPrefix := by
    rw [upper_eq, denominator_eq, numerator_eq, marker_eq, scale_eq] at reduced
    refine ⟨3 * denominatorQuotient * upperQuotient + denominatorQuotient +
        upperQuotient - numeratorQuotient * signedSwappedCode lowerPrefix -
        3 * markerQuotient * scaleQuotient + markerQuotient + scaleQuotient, ?_⟩
    linear_combination -reduced
  have lower_nil : lowerPrefix = [] := by
    by_contra lower_ne
    exact not_three_dvd_signedSwappedCode_of_ne_nil lower_ne lower_divisible
  have lower_zero : signedSwappedCode lowerPrefix = 0 := by
    simp [lower_nil, signedSwappedCode]
  rw [lower_zero, mul_zero, sub_zero] at reduced
  have upper_positive : 0 < signedSwappedCode upperPrefix := by
    rw [upperPrefix_eq, signedSwappedCode_append_true]
    have code_nonneg : 0 ≤ signedSwappedCode
        (spell (nearyUpper (offset + 1)) target) := by
      simp [signedSwappedCode]
    linarith
  have denominator_positive : 0 < distinguishedDoubleDeletionCDenominator offset := by
    have half_nonneg := halfScale_nonneg offset
    simp [distinguishedDoubleDeletionCDenominator]
    nlinarith [sq_nonneg (halfScale offset)]
  have product_ge :
      distinguishedDoubleDeletionCDenominator offset ≤
        distinguishedDoubleDeletionCDenominator offset *
          signedSwappedCode upperPrefix := by
    nlinarith
  have denominator_gt := doubleDeletion_denominator_gt_markerProduct offset_pos
  nlinarith

private theorem RepresentsDefectRatio.scaleState
    {width : Nat} {state : CenteredState} {numerator denominator : ℤ}
    (scalar : ℚ) (represented :
      RepresentsDefectRatio width state numerator denominator) :
    RepresentsDefectRatio width (scaleState scalar state) numerator denominator := by
  rw [RepresentsDefectRatio, ordinaryDefect] at represented ⊢
  simp only [scaleState_x, scaleState_y]
  linear_combination scalar * represented

@[simp] private theorem rawHeadState_singleton_c_eq_distinguishedReset (width : Nat) :
    rawHeadState width [.erase .c] = distinguishedReset width := by
  ext <;>
    simp [rawHeadState, distinguishedReset, swappedUpperCode_singleton_c]

/-- A primitive represented carrier with zero gap lies on the distinguished raw-head ray. -/
theorem primitiveGapZero_state_eq_scale_rawHead
    {width : Nat} (state : CenteredState) {numerator denominator : ℤ}
    (represented : RepresentsDefectRatio width state numerator denominator)
    (primitive : IsCoprime numerator denominator)
    (gap_zero : denominator - numerator = 0) :
    ∃ scale : ℚ,
      state = scaleState scale (rawHeadState width [.erase .c]) := by
  have denominator_eq : denominator = numerator := sub_eq_zero.mp gap_zero
  subst denominator
  have numerator_unit : IsUnit numerator := primitive.isUnit_of_dvd (dvd_refl numerator)
  have numerator_ne : numerator ≠ 0 := by
    rw [Int.isUnit_iff] at numerator_unit
    omega
  have numerator_ne_rat : (numerator : ℚ) ≠ 0 := by exact_mod_cast numerator_ne
  have carrier_eq :
      (terminalDiscrepancy width : ℚ) * ordinaryDefect width state =
        centeredCoefficient width * state.y := by
    apply mul_right_cancel₀ numerator_ne_rat
    calc
      ((terminalDiscrepancy width : ℚ) * ordinaryDefect width state) * numerator =
          terminalDiscrepancy width * ordinaryDefect width state * numerator := by ring
      _ = centeredCoefficient width * state.y * numerator := represented
      _ = (centeredCoefficient width * state.y) * numerator := by ring
  have coefficient_eq :
      (terminalDiscrepancy width : ℚ) - centeredCoefficient width =
        3 * setterMarker width := by
    simp [centeredCoefficient, terminalDiscrepancy, setterMarker, widthScale]
    ring
  have residual_eq :
      ((terminalDiscrepancy width : ℚ) - centeredCoefficient width) * state.y -
          terminalDiscrepancy width * centeredCoefficient width *
            setterMarker width * state.x = 0 := by
    rw [ordinaryDefect] at carrier_eq
    linear_combination carrier_eq
  have factored :
      (setterMarker width : ℚ) *
          (3 * state.y -
            centeredCoefficient width * terminalDiscrepancy width * state.x) = 0 := by
    calc
      (setterMarker width : ℚ) *
          (3 * state.y -
            centeredCoefficient width * terminalDiscrepancy width * state.x) =
        ((terminalDiscrepancy width : ℚ) - centeredCoefficient width) * state.y -
          terminalDiscrepancy width * centeredCoefficient width *
            setterMarker width * state.x := by rw [coefficient_eq]; ring
      _ = 0 := residual_eq
  have marker_ne : (setterMarker width : ℚ) ≠ 0 := by
    have scale_pos : (0 : ℤ) < widthScale width := by simp [widthScale]
    have marker_pos : (0 : ℤ) < setterMarker width := by
      simp [setterMarker]
      omega
    exact_mod_cast ne_of_gt marker_pos
  have ray_eq :
      3 * state.y =
        centeredCoefficient width * terminalDiscrepancy width * state.x := by
    exact sub_eq_zero.mp <| (mul_eq_zero.mp factored).resolve_left marker_ne
  refine ⟨state.x / 3, ?_⟩
  apply CenteredState.ext
  · simp [scaleState, rawHeadState]
  · change state.y =
      state.x / 3 *
        (centeredCoefficient width * swappedUpperCode width [.erase .c])
    rw [swappedUpperCode_singleton_c]
    linarith

/-- A zero-gap carrier followed by two sequential singleton `D_c` transfers cannot hit a
full-erasure-tail threshold. -/
theorem gapZero_sequentialDoubleDeletionC_avoids_erasureTail_pole
    {offset : Nat} (offset_pos : 0 < offset) (body : List TagLetter)
    (antecedent : CenteredState) {numerator denominator : ℤ}
    (represented : RepresentsDefectRatio (offset + 1) antecedent numerator denominator)
    (primitive : IsCoprime numerator denominator)
    (gap_zero : denominator - numerator = 0)
    {target : List NearyTile} (target_tail : HasErasureTail (offset + 1) target)
    (current_y_ne :
      (blockStep (offset + 1) body [.erase .c]
        (blockStep (offset + 1) body [.erase .c] antecedent)).y ≠ 0)
    (pole :
      poleResidual (offset + 1) body target
        (blockStep (offset + 1) body [.erase .c]
          (blockStep (offset + 1) body [.erase .c] antecedent)) = 0) : False := by
  obtain ⟨scale, state_eq⟩ :=
    primitiveGapZero_state_eq_scale_rawHead antecedent represented primitive gap_zero
  have current_eq :
      blockStep (offset + 1) body [.erase .c]
          (blockStep (offset + 1) body [.erase .c] antecedent) =
        scaleState scale
          (blockStep (offset + 1) body [.erase .c]
            (blockStep (offset + 1) body [.erase .c]
              (distinguishedReset (offset + 1)))) := by
    rw [state_eq, rawHeadState_singleton_c_eq_distinguishedReset,
      blockStep_scale, blockStep_scale]
  have canonical_represented := distinguishedDoubleDeletionC_represents offset body
  have current_represented :
      RepresentsDefectRatio (offset + 1)
        (blockStep (offset + 1) body [.erase .c]
          (blockStep (offset + 1) body [.erase .c] antecedent))
        (distinguishedDoubleDeletionCNumerator offset)
        (distinguishedDoubleDeletionCDenominator offset) := by
    rw [current_eq]
    exact RepresentsDefectRatio.scaleState scale canonical_represented
  have threshold := threshold_crossProduct_of_pole (show 2 ≤ offset + 1 by omega) body target
    (blockStep (offset + 1) body [.erase .c]
      (blockStep (offset + 1) body [.erase .c] antecedent))
    current_y_ne current_represented pole
  exact distinguishedDoubleDeletionC_avoids_erasureTail_threshold offset_pos body target_tail
    threshold

/-- The two-deletion pullback has no zero-gap survivor: it halts or exposes a nonzero full-gap
predecessor. -/
theorem sequentialDoubleDeletionC_erasureTailPole_forces_halt_or_nonzeroPredecessorGap
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
    {target : List NearyTile} (target_tail : HasErasureTail width target)
    (current_y_ne :
      (blockStep width body [.erase .c]
        (blockStep width body [.erase .c] antecedent)).y ≠ 0)
    (pole :
      poleResidual width body target
        (blockStep width body [.erase .c]
          (blockStep width body [.erase .c] antecedent)) = 0)
    (nonterminal : currentDenominator - currentNumerator ≠ 0) :
    TagHaltsFrom width (tagOutput body) (body.drop (width - 1) ++ [.b]) ∨
      antecedentDenominator - antecedentNumerator ≠ 0 ∧
        widthScale width ∣ antecedentDenominator - antecedentNumerator := by
  rcases doubleLiteralDeletionC_erasureTailPole_forces_halt_or_predecessorGap width_two body
      body_long antecedent antecedent_represented antecedent_primitive previous_primitive
      current_primitive previous_scale_ne previous_numerator_eq previous_denominator_eq
      current_scale_ne current_numerator_eq current_denominator_eq target_tail current_y_ne
      pole nonterminal with
    halts | gap_divisible
  · exact Or.inl halts
  · by_cases gap_zero : antecedentDenominator - antecedentNumerator = 0
    · obtain ⟨offset, width_eq⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : width ≠ 0)
      subst width
      exact False.elim <|
        gapZero_sequentialDoubleDeletionC_avoids_erasureTail_pole (by omega) body antecedent
          antecedent_represented antecedent_primitive gap_zero target_tail current_y_ne pole
    · exact Or.inr ⟨gap_zero, gap_divisible⟩

end MatrixMortality.SwappedSetterSequentialDoubleDeletion
