import MatrixMortality.SwappedSetterPostRcDbAutomaton

set_option autoImplicit false

/-!
# Post-`R_c;D_b` physical chamber

After the literal canonical `R_c;D_b` pullback and singleton `D_c`, the affine intercept
automaton and exact ternary spelling cylinders exclude every next physical block from the
singleton-`D_c` contraction chamber. The result does not force that canonical history, prove
encoded-entry reachability, or establish a pole.
-/

namespace MatrixMortality.SwappedSetterPostRcDbChamber

open SwappedSetterMultitransfer SwappedSetterThresholdCarry
  SwappedSetterEmptyFrontRay SwappedSetterEmptyFrontChamber

/-! ## Physical spelling chambers -/

/-- Every nonempty physical lower spelling has positive swapped ternary code. -/
theorem physicalLowerCode_pos
    (width : Nat) (body : List TagLetter) (tile : NearyTile)
    (rest : List NearyTile) :
    (0 : ℚ) < swappedLowerCode width body (tile :: rest) := by
  let word := swappedPhysicalLowerWord width body (tile :: rest)
  have word_nonempty := swappedPhysicalLowerWord_nonempty width body tile rest
  have code_bound := ternaryCode_lower_bound word word_nonempty
  have code_pos : 0 < ternaryCode word :=
    lt_of_lt_of_le (pow_pos (by norm_num) (word.length - 1)) code_bound
  have code_pos_int : (0 : ℤ) < ternaryCode word := by exact_mod_cast code_pos
  have code_pos_rat : (0 : ℚ) < (ternaryCode word : ℤ) := by exact_mod_cast code_pos_int
  simpa only [swappedLowerCode, swappedPhysicalLowerWord, word] using code_pos_rat

private theorem chamberBasePower_eq
    (width : Nat) (block : List NearyTile) :
    chamberQuotient width * interceptPower width block =
      (3 : ℚ) ^ (upperLength width block + (width - 6)) := by
  rw [interceptPower_eq_upperPower]
  simp only [chamberQuotient, upperPower]
  push_cast
  rw [← pow_add]
  congr 1
  omega

private theorem lowerCode_short
    (width : Nat) (body : List TagLetter)
    (tile : NearyTile) (rest : List NearyTile)
    (length_short :
      (swappedPhysicalLowerWord width body (tile :: rest)).length ≤
        upperLength width (tile :: rest) + (width - 6)) :
    (swappedLowerCode width body (tile :: rest) : ℚ) <
      chamberQuotient width * interceptPower width (tile :: rest) := by
  let word := swappedPhysicalLowerWord width body (tile :: rest)
  have code_lt := ternaryCode_lt_pow_length word
  have power_le :
      3 ^ word.length ≤
        3 ^ (upperLength width (tile :: rest) + (width - 6)) :=
    Nat.pow_le_pow_right (by norm_num) length_short
  have natural_bound :
      ternaryCode word <
        3 ^ (upperLength width (tile :: rest) + (width - 6)) :=
    code_lt.trans_le power_le
  have rational_bound :
      ((ternaryCode word : ℤ) : ℚ) <
        (3 : ℚ) ^ (upperLength width (tile :: rest) + (width - 6)) := by
    exact_mod_cast natural_bound
  rw [← chamberBasePower_eq width] at rational_bound
  simpa only [swappedLowerCode, swappedPhysicalLowerWord, word] using rational_bound

private theorem lowerCode_long
    (width : Nat) (body : List TagLetter)
    (tile : NearyTile) (rest : List NearyTile)
    (length_long :
      upperLength width (tile :: rest) + (width - 6) + 2 ≤
        (swappedPhysicalLowerWord width body (tile :: rest)).length) :
    (3 : ℚ) * chamberQuotient width * interceptPower width (tile :: rest) ≤
      (swappedLowerCode width body (tile :: rest) : ℚ) := by
  let word := swappedPhysicalLowerWord width body (tile :: rest)
  have word_nonempty := swappedPhysicalLowerWord_nonempty width body tile rest
  have length_long' :
      upperLength width (tile :: rest) + (width - 6) + 2 ≤ word.length := by
    simpa only [word] using length_long
  have exponent_le :
      upperLength width (tile :: rest) + (width - 6) + 1 ≤
        word.length - 1 := by omega
  have power_le :
      3 ^ (upperLength width (tile :: rest) + (width - 6) + 1) ≤
        3 ^ (word.length - 1) :=
    Nat.pow_le_pow_right (by norm_num) exponent_le
  have natural_bound :
      3 ^ (upperLength width (tile :: rest) + (width - 6) + 1) ≤
        ternaryCode word :=
    power_le.trans (ternaryCode_lower_bound word word_nonempty)
  have rational_bound :
      (3 : ℚ) ^ (upperLength width (tile :: rest) + (width - 6) + 1) ≤
        ((ternaryCode word : ℤ) : ℚ) := by
    exact_mod_cast natural_bound
  have power_eq :
      (3 : ℚ) ^ (upperLength width (tile :: rest) + (width - 6) + 1) =
        3 * (chamberQuotient width *
          interceptPower width (tile :: rest)) := by
    rw [pow_succ, chamberBasePower_eq width]
    ring
  rw [power_eq] at rational_bound
  simpa only [swappedLowerCode, swappedPhysicalLowerWord, word, mul_assoc] using rational_bound

private theorem eraseCritical_lowerCode
    (width : Nat) (body : List TagLetter)
    (letter : TagLetter) (rest : List NearyTile)
    (length_critical :
      (swappedPhysicalLowerWord width body (.erase letter :: rest)).length =
        upperLength width (.erase letter :: rest) + (width - 6) + 1) :
    (2 : ℚ) * chamberQuotient width * interceptPower width (.erase letter :: rest) ≤
      (swappedLowerCode width body (.erase letter :: rest) : ℚ) := by
  obtain ⟨tail, word_eq⟩ :=
    swappedPhysicalLowerWord_erase_prefix width body letter rest
  have tail_length :
      tail.length = upperLength width (.erase letter :: rest) + (width - 6) := by
    rw [word_eq] at length_critical
    simp only [List.length_cons] at length_critical
    omega
  have code_formula :
      ternaryCode (true :: tail) = 2 * 3 ^ tail.length + ternaryCode tail := by
    rw [ternaryCode_cons]
    simp only [ternaryDigit]
    ring
  have natural_bound : 2 * 3 ^ tail.length ≤ ternaryCode (true :: tail) := by
    rw [code_formula]
    omega
  have rational_bound :
      (2 : ℚ) * 3 ^ tail.length ≤ ((ternaryCode (true :: tail) : ℤ) : ℚ) := by
    exact_mod_cast natural_bound
  rw [tail_length, ← chamberBasePower_eq width] at rational_bound
  have lower_code_eq :
      (swappedLowerCode width body (.erase letter :: rest) : ℚ) =
        ((ternaryCode (true :: tail) : ℤ) : ℚ) := by
    change ((ternaryCode (swappedPhysicalLowerWord width body
      (.erase letter :: rest)) : ℤ) : ℚ) = _
    rw [word_eq]
  rw [lower_code_eq]
  simpa only [mul_assoc] using rational_bound

private theorem ruleBCritical_lowerCode
    (width : Nat) (body : List TagLetter)
    (rest : List NearyTile)
    (length_critical :
      (swappedPhysicalLowerWord width body (.rule .b :: rest)).length =
        upperLength width (.rule .b :: rest) + (width - 6) + 1) :
    (14 : ℚ) * chamberQuotient width * interceptPower width (.rule .b :: rest) ≤
      9 * (swappedLowerCode width body (.rule .b :: rest) : ℚ) ∧
    3 * (swappedLowerCode width body (.rule .b :: rest) : ℚ) <
      5 * chamberQuotient width * interceptPower width (.rule .b :: rest) := by
  obtain ⟨tail, word_eq⟩ := swappedPhysicalLowerWord_rule_b_prefix width body rest
  have tail_length :
      tail.length + 2 = upperLength width (.rule .b :: rest) + (width - 6) := by
    rw [word_eq] at length_critical
    simp only [List.length_cons] at length_critical
    omega
  have code_formula :
      ternaryCode (false :: false :: true :: tail) =
        14 * 3 ^ tail.length + ternaryCode tail := by
    simp only [ternaryCode_cons, List.length_cons, ternaryDigit, pow_succ]
    ring
  have tail_code_upper := ternaryCode_lt_pow_length tail
  have base_power_eq :
      chamberQuotient width * interceptPower width (.rule .b :: rest) =
        9 * (3 : ℚ) ^ tail.length := by
    rw [chamberBasePower_eq width, ← tail_length, pow_add]
    norm_num
    ring
  constructor
  · have natural_bound :
        14 * 3 ^ tail.length ≤ ternaryCode (false :: false :: true :: tail) := by
      rw [code_formula]
      omega
    have rational_bound :
        (14 : ℚ) * 3 ^ tail.length ≤
          ((ternaryCode (false :: false :: true :: tail) : ℤ) : ℚ) := by
      exact_mod_cast natural_bound
    have lower_code_eq :
        (swappedLowerCode width body (.rule .b :: rest) : ℚ) =
          ((ternaryCode (false :: false :: true :: tail) : ℤ) : ℚ) := by
      change ((ternaryCode (swappedPhysicalLowerWord width body
        (.rule .b :: rest)) : ℤ) : ℚ) = _
      rw [word_eq]
    rw [lower_code_eq]
    nlinarith [base_power_eq]
  · have natural_bound :
        ternaryCode (false :: false :: true :: tail) < 15 * 3 ^ tail.length := by
      rw [code_formula]
      omega
    have rational_bound :
        ((ternaryCode (false :: false :: true :: tail) : ℤ) : ℚ) <
          (15 : ℚ) * 3 ^ tail.length := by
      exact_mod_cast natural_bound
    have lower_code_eq :
        (swappedLowerCode width body (.rule .b :: rest) : ℚ) =
          ((ternaryCode (false :: false :: true :: tail) : ℤ) : ℚ) := by
      change ((ternaryCode (swappedPhysicalLowerWord width body
        (.rule .b :: rest)) : ℤ) : ℚ) = _
      rw [word_eq]
    rw [lower_code_eq]
    nlinarith [base_power_eq]

/-- A `b`-leading lower spelling lies in one of the four quotient-scaled length and prefix
chambers. -/
theorem bLeading_lowerCode_partition
    (width : Nat) (body : List TagLetter) {tile : NearyTile}
    (tile_b : tile.letter = .b) (rest : List NearyTile) :
    let lower : ℚ := swappedLowerCode width body (tile :: rest)
    let base : ℚ := chamberQuotient width * interceptPower width (tile :: rest)
    lower < base ∨ 3 * base ≤ lower ∨ 2 * base ≤ lower ∨
      (14 * base ≤ 9 * lower ∧ 3 * lower < 5 * base) := by
  dsimp only
  let cut := upperLength width (tile :: rest) + (width - 6)
  let lowerWord := swappedPhysicalLowerWord width body (tile :: rest)
  by_cases short : lowerWord.length ≤ cut
  · exact Or.inl (by
      simpa only [cut, lowerWord] using lowerCode_short width body tile rest short)
  · by_cases long : cut + 2 ≤ lowerWord.length
    · exact Or.inr (Or.inl (by
        simpa only [cut, lowerWord, mul_assoc] using
          lowerCode_long width body tile rest long))
    · have critical : lowerWord.length = cut + 1 := by omega
      cases tile with
      | erase letter =>
          exact Or.inr (Or.inr (Or.inl (by
            simpa only [cut, lowerWord, mul_assoc] using
              eraseCritical_lowerCode width body letter rest critical)))
      | rule letter =>
          cases letter with
          | c => simp [NearyTile.letter] at tile_b
          | b =>
              exact Or.inr (Or.inr (Or.inr (by
                simpa only [cut, lowerWord, mul_assoc] using
                  ruleBCritical_lowerCode width body rest critical)))

/-- Backward slope of a next physical block after the literal canonical
`R_c;D_b;D_c` history. -/
def postRcDbPhysicalSlope (width : Nat) (seed : ℚ) (body : List TagLetter)
    (block : List NearyTile) : ℚ :=
  backwardBlock width
    (swappedUpperCode width block)
    (swappedLowerCode width body block)
    (upperPower width block) (postRcDbCarrier width seed)

private theorem postRcDbPhysicalSlope_eq_walk
    {width : Nat} (width_large : 6 ≤ width) {seed : ℚ}
    (seed_lower : (8 * widthScale width ^ 2 : ℚ) < seed)
    (body : List TagLetter) (tile : NearyTile) (rest : List NearyTile) :
    postRcDbPhysicalSlope width seed body (tile :: rest) =
      walkIntercept width (tile :: rest) (postRcDbIntercept width seed) /
        swappedLowerCode width body (tile :: rest) := by
  have lower_pos := physicalLowerCode_pos width body tile rest
  have denominator_pos :=
    postRcDbCarrier_denominator_pos_of_seed width_large seed_lower
  apply backwardBlock_eq_walkIntercept lower_pos.ne' denominator_pos.ne'
  rfl

private theorem postRcDbIntercept_lt_c_cut
    {width : Nat} (width_large : 6 ≤ width) {seed : ℚ}
    (seed_lower : (8 * widthScale width ^ 2 : ℚ) < seed) :
    postRcDbIntercept width seed < (chamberRadius width - 1) / 3 := by
  have upper := postRcDbIntercept_upper width_large seed_lower
  rcases upper with ⟨width_eq, upper⟩ | ⟨width_seven, upper⟩
  · subst width
    norm_num [chamberRadius, terminalDiscrepancy, widthScale] at upper ⊢
    nlinarith
  · have q_three := chamberQuotient_ge_three width_seven
    have scale_eq : (widthScale width : ℚ) = 729 * chamberQuotient width := by
      have integer_eq := widthScale_eq_729_mul_chamberQuotient width_large
      exact_mod_cast integer_eq
    have margin_pos := interceptMargin_pos width_large
    simp only [interceptMargin] at margin_pos
    simp only [chamberRadius]
    push_cast
    rw [scale_eq]
    nlinarith

/-- Every `c`-leading next physical block has negative backward slope after the literal
canonical `R_c;D_b;D_c` history. -/
theorem cLeading_postRcDbPhysicalSlope_negative
    {width : Nat} (width_large : 6 ≤ width) {seed : ℚ}
    (seed_lower : (8 * widthScale width ^ 2 : ℚ) < seed)
    (body : List TagLetter) {tile : NearyTile}
    (tile_c : tile.letter = .c) (rest : List NearyTile) :
    postRcDbPhysicalSlope width seed body (tile :: rest) < 0 := by
  have lower_pos := physicalLowerCode_pos width body tile rest
  have numerator_neg := cLeading_walkIntercept_negative width_large
    (postRcDbIntercept_lt_c_cut width_large seed_lower) tile_c rest
  rw [postRcDbPhysicalSlope_eq_walk width_large seed_lower]
  exact div_neg_of_neg_of_pos numerator_neg lower_pos

/-- A `b`-leading next block lies below one or above a width-uniform positive gap. -/
theorem bLeading_postRcDbPhysicalSlope_classification
    {width : Nat} (width_large : 6 ≤ width) {seed : ℚ}
    (seed_lower : (8 * widthScale width ^ 2 : ℚ) < seed)
    (body : List TagLetter) {tile : NearyTile}
    (tile_b : tile.letter = .b) (rest : List NearyTile) :
    (width = 6 ∧
      (postRcDbPhysicalSlope width seed body (tile :: rest) < 1 ∨
        (51 : ℚ) / 50 < postRcDbPhysicalSlope width seed body (tile :: rest))) ∨
    (7 ≤ width ∧
      (postRcDbPhysicalSlope width seed body (tile :: rest) < 1 ∨
        (6 : ℚ) / 5 < postRcDbPhysicalSlope width seed body (tile :: rest))) := by
  let intercept := postRcDbIntercept width seed
  let power := interceptPower width (tile :: rest)
  let numerator := walkIntercept width (tile :: rest) intercept
  let lower : ℚ := swappedLowerCode width body (tile :: rest)
  have power_pos : 0 < power := interceptPower_pos width (tile :: rest)
  have lower_pos : 0 < lower := physicalLowerCode_pos width body tile rest
  have intercept_lower :
      (6 : ℚ) * chamberQuotient width / 5 < intercept :=
    six_fifths_chamberQuotient_lt_postRcDbIntercept width_large seed_lower
  have numerator_affine_lower :
      (intercept + 1 / 2) * power < numerator :=
    bLeading_walkIntercept_lower width_large intercept tile_b rest
  have lower_partition := bLeading_lowerCode_partition width body tile_b rest
  have slope_eq :
      postRcDbPhysicalSlope width seed body (tile :: rest) = numerator / lower := by
    simpa only [intercept, numerator, lower] using
      postRcDbPhysicalSlope_eq_walk width_large seed_lower body tile rest
  have upper := postRcDbIntercept_upper width_large seed_lower
  rcases upper with ⟨width_eq, intercept_upper⟩ | ⟨width_seven, intercept_upper⟩
  · subst width
    have intercept_upper' : intercept < 2 - interceptMargin 6 := by
      simpa only [intercept, interceptMargin] using intercept_upper
    have numerator_upper : numerator < 2 * power :=
      bLeading_walkIntercept_upper (by norm_num) intercept_upper' tile_b rest
    norm_num [chamberQuotient] at intercept_lower lower_partition
    have scaled_intercept_lower :=
      mul_lt_mul_of_pos_right intercept_lower power_pos
    have numerator_lower : (17 : ℚ) / 10 * power < numerator := by
      nlinarith
    refine Or.inl ⟨rfl, ?_⟩
    rcases lower_partition with short | long | criticalErase | criticalRule
    · exact Or.inr (by
        rw [slope_eq]
        apply (lt_div_iff₀ lower_pos).2
        nlinarith)
    · exact Or.inl (by
        rw [slope_eq]
        apply (div_lt_iff₀ lower_pos).2
        nlinarith)
    · exact Or.inl (by
        rw [slope_eq]
        apply (div_lt_iff₀ lower_pos).2
        nlinarith)
    · exact Or.inr (by
        rw [slope_eq]
        apply (lt_div_iff₀ lower_pos).2
        nlinarith [criticalRule.2])
  · have intercept_upper' :
        intercept < 14 * chamberQuotient width / 9 - interceptMargin width := by
      simpa only [intercept, interceptMargin] using intercept_upper
    have numerator_upper :
        numerator < 14 * chamberQuotient width / 9 * power :=
      bLeading_walkIntercept_upper width_large intercept_upper' tile_b rest
    have quotient_pos : (0 : ℚ) < chamberQuotient width := by
      exact_mod_cast chamberQuotient_pos width
    have base_pos :
        0 < (chamberQuotient width : ℚ) * power :=
      mul_pos quotient_pos power_pos
    have scaled_intercept_lower :=
      mul_lt_mul_of_pos_right intercept_lower power_pos
    have numerator_lower :
        (6 : ℚ) / 5 * chamberQuotient width * power < numerator := by
      nlinarith
    refine Or.inr ⟨width_seven, ?_⟩
    rcases lower_partition with short | long | criticalErase | criticalRule
    · exact Or.inr (by
        rw [slope_eq]
        apply (lt_div_iff₀ lower_pos).2
        nlinarith)
    · exact Or.inl (by
        rw [slope_eq]
        apply (div_lt_iff₀ lower_pos).2
        nlinarith)
    · exact Or.inl (by
        rw [slope_eq]
        apply (div_lt_iff₀ lower_pos).2
        nlinarith)
    · exact Or.inl (by
        rw [slope_eq]
        apply (div_lt_iff₀ lower_pos).2
        nlinarith [criticalRule.1])

private theorem deletionCChamberCeiling_width_six :
    (chamberRadius 6 : ℚ) / (chamberRadius 6 - 3) < (51 : ℚ) / 50 := by
  norm_num [chamberRadius, widthScale]

private theorem deletionCChamberCeiling_lt_six_fifths
    {width : Nat} (width_large : 6 ≤ width) :
    (chamberRadius width : ℚ) / (chamberRadius width - 3) < (6 : ℚ) / 5 := by
  have scale_large := widthScale_ge_729 width_large
  have denominator_pos : (0 : ℚ) < chamberRadius width - 3 := by
    simp only [chamberRadius]
    push_cast
    linarith
  apply (div_lt_iff₀ denominator_pos).2
  simp only [chamberRadius]
  push_cast
  linarith

/-- No next physical block re-enters the singleton-`D_c` contraction chamber after the
literal canonical `R_c;D_b;D_c` history. This theorem assumes that history; it does not force
it from an arbitrary chamber entry. -/
theorem postRcDbPhysicalSlope_avoids_deletionCChamber
    {width : Nat} (width_large : 6 ≤ width) {seed : ℚ}
    (seed_lower : (8 * widthScale width ^ 2 : ℚ) < seed)
    (body : List TagLetter) (tile : NearyTile) (rest : List NearyTile) :
    ¬(1 < postRcDbPhysicalSlope width seed body (tile :: rest) ∧
      postRcDbPhysicalSlope width seed body (tile :: rest) <
        (chamberRadius width : ℚ) / (chamberRadius width - 3)) := by
  intro chamber
  cases letter_eq : tile.letter with
  | c =>
      have negative := cLeading_postRcDbPhysicalSlope_negative
        width_large seed_lower body letter_eq rest
      linarith
  | b =>
      have classification := bLeading_postRcDbPhysicalSlope_classification
        width_large seed_lower body letter_eq rest
      rcases classification with ⟨width_eq, below | above⟩ |
        ⟨width_seven, below | above⟩
      · linarith
      · subst width
        nlinarith [deletionCChamberCeiling_width_six]
      · linarith
      · nlinarith [deletionCChamberCeiling_lt_six_fifths
          (show 6 ≤ width by omega)]

/-- Every physical empty target of width at least six supplies the seed hypothesis for the
conditional canonical post-`D_c` no-reentry theorem. -/
theorem physicalEmptyTarget_postRcDb_avoids_deletionCChamber
    {offset : Nat} (offset_five : 5 ≤ offset) {letters : List TagLetter}
    (letters_length : letters.length = offset + 1)
    (body : List TagLetter) (tile : NearyTile) (rest : List NearyTile) :
    let upperPrefix :=
      signedSwappedCode (tagEncode (offset + 1) letters ++ [true])
    ¬(1 < postRcDbPhysicalSlope (offset + 1)
          (emptyFrontSeed offset upperPrefix) body (tile :: rest) ∧
      postRcDbPhysicalSlope (offset + 1)
          (emptyFrontSeed offset upperPrefix) body (tile :: rest) <
        (chamberRadius (offset + 1) : ℚ) /
          (chamberRadius (offset + 1) - 3)) := by
  dsimp only
  have width_large : 6 ≤ offset + 1 := by omega
  have prefix_lower := emptyTarget_upperPrefix_lower letters_length
  have seed_lower :=
    emptyFrontSeed_gt_eight_widthScale_sq offset_five prefix_lower
  exact postRcDbPhysicalSlope_avoids_deletionCChamber width_large seed_lower
    body tile rest

end MatrixMortality.SwappedSetterPostRcDbChamber
