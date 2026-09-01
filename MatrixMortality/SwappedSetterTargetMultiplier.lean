import MatrixMortality.SwappedSetterCylinderCharge

/-!
# Primitive target multiplier and prefix-discrepancy braid
-/

namespace MatrixMortality.SwappedSetterTargetMultiplier

open SwappedSetterMultitransfer SwappedSetterThresholdCarry
  SwappedSetterCylinderCharge

/-- Difference of the lower and upper prefixes left after a full target erasure tail is peeled. -/
def targetPrefixDiscrepancy (width : Nat) (body : List TagLetter)
    (target front : List NearyTile) : ℤ :=
  signedSwappedCode (spell (nearyLower width body) front) -
    signedSwappedCode (spell (nearyUpper width) target ++ [true])

/-- Initial carrier combination braided into the peeled target-prefix discrepancy. -/
def predecessorBraidResidual (width : Nat)
    (initialUnit initialCylinderQuotient antecedentDenominator : ℤ) : ℤ :=
  2 * setterMarker width * initialCylinderQuotient +
    initialUnit * antecedentDenominator

/-- A primitive cross-product pair divides both target coordinates by one common multiplier. -/
theorem primitive_crossProduct_factor
    {numerator denominator upper lower : ℤ}
    (primitive : IsCoprime numerator denominator)
    (cross : denominator * upper = numerator * lower) :
    ∃ multiplier : ℤ,
      upper = multiplier * numerator ∧ lower = multiplier * denominator := by
  obtain ⟨left, right, bezout⟩ := primitive
  refine ⟨left * upper + right * lower, ?_, ?_⟩
  · calc
      upper = (left * numerator + right * denominator) * upper := by rw [bezout]; ring
      _ = (left * upper + right * lower) * numerator := by
        linear_combination right * cross
  · calc
      lower = (left * numerator + right * denominator) * lower := by rw [bezout]; ring
      _ = (left * upper + right * lower) * denominator := by
        linear_combination -left * cross

/-- The common multiplier of a primitive cross-product pair is unique. -/
theorem primitive_crossProduct_factor_unique
    {numerator denominator upper lower multiplier₁ multiplier₂ : ℤ}
    (primitive : IsCoprime numerator denominator)
    (first :
      upper = multiplier₁ * numerator ∧ lower = multiplier₁ * denominator)
    (second :
      upper = multiplier₂ * numerator ∧ lower = multiplier₂ * denominator) :
    multiplier₁ = multiplier₂ := by
  obtain ⟨left, right, bezout⟩ := primitive
  calc
    multiplier₁ = multiplier₁ * (left * numerator + right * denominator) := by
      rw [bezout]
      ring
    _ = left * upper + right * lower := by rw [first.1, first.2]; ring
    _ = multiplier₂ * (left * numerator + right * denominator) := by
      rw [second.1, second.2]
      ring
    _ = multiplier₂ := by rw [bezout]; ring

private theorem power_mul_sub_one_not_dvd_three
    {width : Nat} (width_pos : 0 < width) (value : ℤ) :
    ¬(3 : ℤ) ∣ 3 ^ width * value - 1 := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt width_pos)
  intro divides
  obtain ⟨factor, factor_eq⟩ := divides
  rw [pow_succ] at factor_eq
  have three_dvd_one : (3 : ℤ) ∣ 1 := by
    refine ⟨3 ^ offset * value - factor, ?_⟩
    linear_combination -factor_eq
  norm_num at three_dvd_one

/-- A primitive full-tail threshold has a nonzero three-adic-unit multiplier, and the peeled
prefix discrepancy is exactly that multiplier times the target charge. -/
theorem erasureTail_primitive_targetMultiplier
    {width : Nat} (width_pos : 0 < width) (body : List TagLetter)
    {target front : List NearyTile} {letters : List TagLetter}
    (letters_length : letters.length = width)
    (target_eq : target = front ++ letters.map NearyTile.erase)
    {numerator denominator targetCharge : ℤ}
    (primitive : IsCoprime numerator denominator)
    (threshold :
      denominator * swappedUpperCode width target =
        numerator * swappedLowerCode width body target)
    (gap_eq : denominator - numerator = 3 ^ width * targetCharge) :
    ∃ multiplier : ℤ,
      multiplier ≠ 0 ∧
        ¬(3 : ℤ) ∣ multiplier ∧
        swappedUpperCode width target = multiplier * numerator ∧
        swappedLowerCode width body target = multiplier * denominator ∧
        targetPrefixDiscrepancy width body target front =
          multiplier * targetCharge := by
  obtain ⟨multiplier, upper_eq, lower_eq⟩ :=
    primitive_crossProduct_factor primitive threshold
  have upper_code_eq :
      swappedUpperCode width target =
        (3 : ℤ) ^ width *
            (signedSwappedCode (spell (nearyUpper width) target ++ [true]) + 1) - 1 :=
    swappedUpperCode_markerTail_factorization width target
  have lower_code_eq :
      swappedLowerCode width body target =
        (3 : ℤ) ^ width *
            (signedSwappedCode (spell (nearyLower width body) front) + 1) - 1 :=
    erasureTail_swappedLowerCode_factorization body letters_length target_eq
  have multiplier_not_dvd : ¬(3 : ℤ) ∣ multiplier := by
    intro multiplier_dvd
    have upper_dvd : (3 : ℤ) ∣ swappedUpperCode width target := by
      rw [upper_eq]
      exact dvd_mul_of_dvd_left multiplier_dvd numerator
    rw [upper_code_eq] at upper_dvd
    exact power_mul_sub_one_not_dvd_three width_pos _ upper_dvd
  have multiplier_ne : multiplier ≠ 0 := fun multiplier_zero =>
    multiplier_not_dvd (multiplier_zero ▸ dvd_zero 3)
  have prefix_eq :
      targetPrefixDiscrepancy width body target front =
        multiplier * targetCharge := by
    simp only [targetPrefixDiscrepancy]
    rw [upper_code_eq] at upper_eq
    rw [lower_code_eq] at lower_eq
    have scale_ne : (3 : ℤ) ^ width ≠ 0 := pow_ne_zero _ (by norm_num)
    apply mul_left_cancel₀ scale_ne
    linear_combination lower_eq - upper_eq + multiplier * gap_eq
  exact ⟨multiplier, multiplier_ne, multiplier_not_dvd, upper_eq, lower_eq, prefix_eq⟩

/-- The primitive full-tail target multiplier is unique. -/
theorem erasureTail_primitive_targetMultiplier_unique
    {width : Nat} (width_pos : 0 < width) (body : List TagLetter)
    {target front : List NearyTile} {letters : List TagLetter}
    (letters_length : letters.length = width)
    (target_eq : target = front ++ letters.map NearyTile.erase)
    {numerator denominator targetCharge : ℤ}
    (primitive : IsCoprime numerator denominator)
    (threshold :
      denominator * swappedUpperCode width target =
        numerator * swappedLowerCode width body target)
    (gap_eq : denominator - numerator = 3 ^ width * targetCharge) :
    ∃! multiplier : ℤ,
      multiplier ≠ 0 ∧
        ¬(3 : ℤ) ∣ multiplier ∧
        swappedUpperCode width target = multiplier * numerator ∧
        swappedLowerCode width body target = multiplier * denominator ∧
        targetPrefixDiscrepancy width body target front =
          multiplier * targetCharge := by
  obtain ⟨multiplier, multiplier_ne, multiplier_not_dvd, upper_eq, lower_eq, prefix_eq⟩ :=
    erasureTail_primitive_targetMultiplier width_pos body letters_length target_eq
      primitive threshold gap_eq
  refine ⟨multiplier,
    ⟨multiplier_ne, multiplier_not_dvd, upper_eq, lower_eq, prefix_eq⟩, ?_⟩
  intro candidate candidate_properties
  exact primitive_crossProduct_factor_unique primitive
    ⟨candidate_properties.2.2.1, candidate_properties.2.2.2.1⟩
    ⟨upper_eq, lower_eq⟩

private theorem spell_nearyUpper_erase_map
    (width : Nat) (letters : List TagLetter) :
    spell (nearyUpper width) (letters.map NearyTile.erase) =
      tagEncode width letters := by
  rw [spell_nearyUpper]
  simp [List.map_map, Function.comp_def, NearyTile.letter]

/-- When the matched erasure tail is the entire target, the unique primitive multiplier divides
the lower tail code, exposes one tag-code discrepancy, and bounds the denominator. -/
theorem erasureTarget_primitive_targetMultiplier_unique
    {width : Nat} (width_pos : 0 < width) (body : List TagLetter)
    (letters : List TagLetter) (letters_length : letters.length = width)
    {numerator denominator targetCharge : ℤ}
    (primitive : IsCoprime numerator denominator)
    (threshold :
      denominator * swappedUpperCode width (letters.map NearyTile.erase) =
        numerator * swappedLowerCode width body (letters.map NearyTile.erase))
    (gap_eq : denominator - numerator = 3 ^ width * targetCharge) :
    ∃! multiplier : ℤ,
      multiplier ≠ 0 ∧
        ¬(3 : ℤ) ∣ multiplier ∧
        swappedUpperCode width (letters.map NearyTile.erase) =
          multiplier * numerator ∧
        swappedLowerCode width body (letters.map NearyTile.erase) =
          (3 : ℤ) ^ width - 1 ∧
        (3 : ℤ) ^ width - 1 = multiplier * denominator ∧
        targetPrefixDiscrepancy width body (letters.map NearyTile.erase) [] =
          -signedSwappedCode (tagEncode width letters ++ [true]) ∧
        -signedSwappedCode (tagEncode width letters ++ [true]) =
          multiplier * targetCharge ∧
        multiplier ∣ (3 : ℤ) ^ width - 1 ∧
        |denominator| ≤ (3 : ℤ) ^ width - 1 := by
  have lower_code_eq :
      swappedLowerCode width body (letters.map NearyTile.erase) =
        (3 : ℤ) ^ width - 1 := by
    have factorization :=
      erasureTail_swappedLowerCode_factorization body letters_length
        (target := letters.map NearyTile.erase) (front := []) (by simp)
    simpa [spell, signedSwappedCode, ternaryCode] using factorization
  have prefix_discrepancy_eq :
      targetPrefixDiscrepancy width body (letters.map NearyTile.erase) [] =
        -signedSwappedCode (tagEncode width letters ++ [true]) := by
    rw [targetPrefixDiscrepancy, spell_nearyUpper_erase_map]
    simp [spell, signedSwappedCode, ternaryCode]
  obtain ⟨multiplier, multiplier_properties, multiplier_unique⟩ :=
    erasureTail_primitive_targetMultiplier_unique width_pos body letters_length
      (target := letters.map NearyTile.erase) (front := []) (by simp)
      primitive threshold gap_eq
  have lower_multiplier_eq :
      (3 : ℤ) ^ width - 1 = multiplier * denominator := by
    rw [← lower_code_eq]
    exact multiplier_properties.2.2.2.1
  have prefix_multiplier_eq :
      -signedSwappedCode (tagEncode width letters ++ [true]) =
        multiplier * targetCharge := by
    rw [← prefix_discrepancy_eq]
    exact multiplier_properties.2.2.2.2
  have multiplier_dvd : multiplier ∣ (3 : ℤ) ^ width - 1 :=
    ⟨denominator, lower_multiplier_eq⟩
  have power_sub_one_nonneg : 0 ≤ (3 : ℤ) ^ width - 1 := by
    obtain ⟨offset, rfl⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt width_pos)
    rw [pow_succ]
    have power_pos : (0 : ℤ) < 3 ^ offset := pow_pos (by norm_num) offset
    nlinarith
  have denominator_abs_le : |denominator| ≤ (3 : ℤ) ^ width - 1 := by
    have multiplier_abs_ge : (1 : ℤ) ≤ |multiplier| :=
      Int.one_le_abs multiplier_properties.1
    have denominator_abs_nonneg : (0 : ℤ) ≤ |denominator| := abs_nonneg denominator
    have scaled_abs_le : |denominator| ≤ |multiplier| * |denominator| := by
      nlinarith
    calc
      |denominator| ≤ |multiplier| * |denominator| := scaled_abs_le
      _ = |multiplier * denominator| := (abs_mul multiplier denominator).symm
      _ = |(3 : ℤ) ^ width - 1| := by rw [lower_multiplier_eq]
      _ = (3 : ℤ) ^ width - 1 := abs_of_nonneg power_sub_one_nonneg
  refine ⟨multiplier,
    ⟨multiplier_properties.1, multiplier_properties.2.1,
      multiplier_properties.2.2.1, lower_code_eq, lower_multiplier_eq,
      prefix_discrepancy_eq, prefix_multiplier_eq, multiplier_dvd,
      denominator_abs_le⟩, ?_⟩
  intro candidate candidate_properties
  apply multiplier_unique candidate
  refine ⟨candidate_properties.1, candidate_properties.2.1,
    candidate_properties.2.2.1, ?_, ?_⟩
  · rw [lower_code_eq]
    exact candidate_properties.2.2.2.2.1
  · rw [prefix_discrepancy_eq]
    exact candidate_properties.2.2.2.2.2.2.1

/-- The unique target multiplier turns the three-block charge braid into one nonzero literal
prefix-discrepancy equation. -/
theorem ThreeBlockChargeWitness.existsUnique_targetMultiplier_braid
    {width : Nat} (width_pos : 0 < width)
    {body : List TagLetter} {precedingBlock target : List NearyTile}
    {originNumerator originDenominator
      antecedentNumerator antecedentDenominator antecedentScale
      previousNumerator previousDenominator previousScale
      currentNumerator currentDenominator currentScale : ℤ}
    (current_primitive : IsCoprime currentNumerator currentDenominator)
    (threshold :
      currentDenominator * swappedUpperCode width target =
        currentNumerator * swappedLowerCode width body target)
    (witness : ThreeBlockChargeWitness width body precedingBlock target
      originNumerator originDenominator
      antecedentNumerator antecedentDenominator antecedentScale
      previousNumerator previousDenominator previousScale
      currentNumerator currentDenominator currentScale) :
    ∃! multiplier : ℤ,
      multiplier ≠ 0 ∧
        ¬(3 : ℤ) ∣ multiplier ∧
        swappedUpperCode width target = multiplier * currentNumerator ∧
        swappedLowerCode width body target = multiplier * currentDenominator ∧
        targetPrefixDiscrepancy width body target witness.front =
          multiplier * witness.targetCharge ∧
        targetPrefixDiscrepancy width body target witness.front ≠ 0 ∧
        witness.initialUnit * witness.middleUnit * witness.currentUnit *
            targetPrefixDiscrepancy width body target witness.front =
          -2 * setterMarker width * terminalDiscrepancy width *
            multiplier *
            predecessorBraidResidual width witness.initialUnit
              witness.initialCylinderQuotient antecedentDenominator := by
  obtain ⟨multiplier, properties, multiplier_unique⟩ :=
    erasureTail_primitive_targetMultiplier_unique width_pos body witness.letters_length
      witness.target_eq current_primitive threshold witness.current_gap_eq
  have braid := witness.braidedCarry_eq
  have tail_factor_ne : (3 : ℤ) ^ width - 1 ≠ 0 := by
    have power_gt : (1 : ℤ) < 3 ^ width := by
      obtain ⟨offset, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt width_pos)
      rw [pow_succ]
      have power_pos : (0 : ℤ) < 3 ^ offset := pow_pos (by norm_num) offset
      nlinarith
    omega
  have charge_braid :
      witness.initialUnit * witness.middleUnit * witness.currentUnit *
          witness.targetCharge =
        -2 * setterMarker width * terminalDiscrepancy width *
          predecessorBraidResidual width witness.initialUnit
            witness.initialCylinderQuotient antecedentDenominator := by
    simp only [predecessorBraidResidual]
    apply mul_left_cancel₀ tail_factor_ne
    calc
      ((3 : ℤ) ^ width - 1) *
          (witness.initialUnit * witness.middleUnit * witness.currentUnit *
            witness.targetCharge) =
        witness.initialUnit * witness.middleUnit * witness.currentUnit *
          (((3 : ℤ) ^ width - 1) * witness.targetCharge) := by ring
      _ = -2 * setterMarker width * terminalDiscrepancy width *
          ((3 : ℤ) ^ width - 1) *
          (2 * setterMarker width * witness.initialCylinderQuotient +
            witness.initialUnit * antecedentDenominator) := braid
      _ = ((3 : ℤ) ^ width - 1) *
          (-2 * setterMarker width * terminalDiscrepancy width *
            (2 * setterMarker width * witness.initialCylinderQuotient +
              witness.initialUnit * antecedentDenominator)) := by ring
  have prefix_ne :
      targetPrefixDiscrepancy width body target witness.front ≠ 0 := by
    intro prefix_zero
    have prefix_eq := properties.2.2.2.2
    rw [prefix_zero] at prefix_eq
    have charge_zero : witness.targetCharge = 0 :=
      (mul_eq_zero.mp prefix_eq.symm).resolve_left properties.1
    exact witness.targetCharge_ne charge_zero
  have prefix_braid :
      witness.initialUnit * witness.middleUnit * witness.currentUnit *
          targetPrefixDiscrepancy width body target witness.front =
        -2 * setterMarker width * terminalDiscrepancy width *
          multiplier *
          predecessorBraidResidual width witness.initialUnit
            witness.initialCylinderQuotient antecedentDenominator := by
    rw [properties.2.2.2.2]
    linear_combination multiplier * charge_braid
  refine ⟨multiplier,
    ⟨properties.1, properties.2.1, properties.2.2.1, properties.2.2.2.1,
      properties.2.2.2.2, prefix_ne, prefix_braid⟩, ?_⟩
  intro candidate candidate_properties
  exact multiplier_unique candidate
    ⟨candidate_properties.1, candidate_properties.2.1,
      candidate_properties.2.2.1, candidate_properties.2.2.2.1,
      candidate_properties.2.2.2.2.1⟩

private theorem mul_not_dvd_three
    {left right : ℤ} (left_not_dvd : ¬(3 : ℤ) ∣ left)
    (right_not_dvd : ¬(3 : ℤ) ∣ right) :
    ¬(3 : ℤ) ∣ left * right := by
  intro product_dvd
  rcases (by norm_num : Prime (3 : ℤ)).dvd_mul.mp product_dvd with
    left_dvd | right_dvd
  · exact left_not_dvd left_dvd
  · exact right_not_dvd right_dvd

private theorem signedSwappedCode_append_true_mod_three
    (word : List Bool) :
    signedSwappedCode (word ++ [true]) ≡ 1 [ZMOD 3] := by
  rw [Int.modEq_iff_dvd, signedSwappedCode_append]
  have singleton_code : signedSwappedCode [true] = 1 := by
    norm_num [signedSwappedCode, ternaryCode, ternaryDigit]
  rw [singleton_code]
  refine ⟨-signedSwappedCode word, ?_⟩
  norm_num

private theorem signedSwappedCode_append_false_mod_three
    (word : List Bool) :
    signedSwappedCode (word ++ [false]) ≡ 2 [ZMOD 3] := by
  rw [Int.modEq_iff_dvd, signedSwappedCode_append]
  have singleton_code : signedSwappedCode [false] = 2 := by
    norm_num [signedSwappedCode, ternaryCode, ternaryDigit]
  rw [singleton_code]
  refine ⟨-signedSwappedCode word, ?_⟩
  norm_num

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

/-- The terminal unequal digit makes every peeled target-prefix discrepancy a three-adic unit,
independently of any carrier or pole equation. -/
theorem targetPrefixDiscrepancy_not_dvd_three
    (width : Nat) (body : List TagLetter) (target front : List NearyTile) :
    ¬(3 : ℤ) ∣ targetPrefixDiscrepancy width body target front := by
  have upper_mod :
      signedSwappedCode (spell (nearyUpper width) target ++ [true]) ≡
        1 [ZMOD 3] :=
    signedSwappedCode_append_true_mod_three _
  by_cases front_empty : front = []
  · subst front
    have discrepancy_mod :
        targetPrefixDiscrepancy width body target [] ≡ 2 [ZMOD 3] := by
      simp only [targetPrefixDiscrepancy]
      have lower_zero : signedSwappedCode (spell (nearyLower width body) []) = 0 := by
        norm_num [spell, signedSwappedCode, ternaryCode]
      rw [lower_zero]
      exact (Int.ModEq.refl (0 : ℤ)).sub upper_mod |>.trans (by norm_num)
    intro discrepancy_dvd
    have two_zero : (2 : ℤ) ≡ 0 [ZMOD 3] :=
      discrepancy_mod.symm.trans discrepancy_dvd.modEq_zero_int
    rw [Int.modEq_iff_dvd] at two_zero
    norm_num at two_zero
  · obtain ⟨stem, lower_eq⟩ :=
      spell_nearyLower_nonempty_ends_false width body front_empty
    have lower_mod :
        signedSwappedCode (spell (nearyLower width body) front) ≡ 2 [ZMOD 3] := by
      rw [lower_eq]
      exact signedSwappedCode_append_false_mod_three stem
    have discrepancy_mod :
        targetPrefixDiscrepancy width body target front ≡ 1 [ZMOD 3] := by
      simp only [targetPrefixDiscrepancy]
      exact lower_mod.sub upper_mod |>.trans (by norm_num)
    intro discrepancy_dvd
    have one_zero : (1 : ℤ) ≡ 0 [ZMOD 3] :=
      discrepancy_mod.symm.trans discrepancy_dvd.modEq_zero_int
    rw [Int.modEq_iff_dvd] at one_zero
    norm_num at one_zero

/-- The literal prefix braid forces its initial predecessor-cylinder residual to be a
three-adic unit. -/
theorem ThreeBlockChargeWitness.predecessorBraidResidual_not_dvd_three
    {width : Nat} {body : List TagLetter}
    {precedingBlock target : List NearyTile}
    {originNumerator originDenominator
      antecedentNumerator antecedentDenominator antecedentScale
      previousNumerator previousDenominator previousScale
      currentNumerator currentDenominator currentScale multiplier : ℤ}
    (witness : ThreeBlockChargeWitness width body precedingBlock target
      originNumerator originDenominator
      antecedentNumerator antecedentDenominator antecedentScale
      previousNumerator previousDenominator previousScale
      currentNumerator currentDenominator currentScale)
    (braid :
      witness.initialUnit * witness.middleUnit * witness.currentUnit *
          targetPrefixDiscrepancy width body target witness.front =
        -2 * setterMarker width * terminalDiscrepancy width * multiplier *
          predecessorBraidResidual width witness.initialUnit
            witness.initialCylinderQuotient antecedentDenominator) :
    ¬(3 : ℤ) ∣
      predecessorBraidResidual width witness.initialUnit
        witness.initialCylinderQuotient antecedentDenominator := by
  have coefficient_not_dvd :
      ¬(3 : ℤ) ∣ witness.initialUnit * witness.middleUnit * witness.currentUnit :=
    mul_not_dvd_three
      (mul_not_dvd_three witness.initialUnit_not_dvd witness.middleUnit_not_dvd)
      witness.currentUnit_not_dvd
  have discrepancy_not_dvd :=
    targetPrefixDiscrepancy_not_dvd_three width body target witness.front
  intro residual_dvd
  have product_dvd :
      (3 : ℤ) ∣
        witness.initialUnit * witness.middleUnit * witness.currentUnit *
          targetPrefixDiscrepancy width body target witness.front := by
    rw [braid]
    exact dvd_mul_of_dvd_right residual_dvd _
  rcases (by norm_num : Prime (3 : ℤ)).dvd_mul.mp product_dvd with
    coefficient_dvd | discrepancy_dvd
  · exact coefficient_not_dvd coefficient_dvd
  · exact discrepancy_not_dvd discrepancy_dvd

end MatrixMortality.SwappedSetterTargetMultiplier
