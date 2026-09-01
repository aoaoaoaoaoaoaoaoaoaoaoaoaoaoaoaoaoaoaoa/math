import MatrixMortality.SwappedSetterPostRcDbChamber

set_option autoImplicit false

/-!
# Universal contraction-chamber entry gap

A compiler-emitted swapped ternary role block can enter the singleton-`D_c` contraction
chamber from above the terminal ray only with a tightly matched upper/lower spelling. The
relative carrier gap is then smaller than `1/(80ρ)`, uniformly over the complete role word.

The theorem classifies a local projective entry. It proves neither encoded-entry reachability,
existence of a chamber entry, a target pole, nor post-contraction no-reentry.
-/

namespace MatrixMortality.SwappedSetterUniversalEntryGap

open SwappedSetterMultitransfer SwappedSetterEmptyFrontRay
  SwappedSetterEmptyFrontChamber SwappedSetterPostRcDbChamber

private theorem swappedPhysicalUpperWord_starts_false (width : Nat) (block : List NearyTile) :
    ∃ tail, swappedPhysicalUpperWord width block = false :: tail := by
  cases block with
  | nil =>
      exact ⟨List.replicate width true, by simp [swappedPhysicalUpperWord, spell, nearyMarker]⟩
  | cons tile rest =>
      cases tile <;> cases ‹TagLetter› <;>
        simp [swappedPhysicalUpperWord_cons, NearyTile.letter, tagCode]

private theorem ternaryCode_spread
    {left right : List Bool} (length_eq : left.length = right.length) :
    2 * ternaryCode left < 2 * ternaryCode right + 3 ^ left.length := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => norm_num [ternaryCode]
      | cons rightBit rightTail => simp at length_eq
  | cons leftBit leftTail induction =>
      cases right with
      | nil => simp at length_eq
      | cons rightBit rightTail =>
          simp only [List.length_cons, Nat.succ.injEq] at length_eq
          have tail_bound := induction length_eq
          have power_eq : 3 ^ leftTail.length = 3 ^ rightTail.length := by
            rw [length_eq]
          rw [ternaryCode_cons, ternaryCode_cons, List.length_cons, pow_succ]
          rw [power_eq]
          cases leftBit <;> cases rightBit <;> simp only [ternaryDigit] <;> omega

private theorem ternaryCode_scale_le_twice_add_one (word : List Bool) :
    3 ^ word.length ≤ 2 * ternaryCode word + 1 := by
  induction word with
  | nil => norm_num
  | cons bit word induction =>
      rw [ternaryCode_cons]
      simp only [List.length_cons, pow_succ]
      have digit_pos : 1 ≤ ternaryDigit bit := by
        cases bit <;> norm_num [ternaryDigit]
      nlinarith [mul_le_mul_of_nonneg_left digit_pos
        (show 0 ≤ 2 * 3 ^ word.length by positivity)]

private theorem swappedPhysicalUpperWord_predecessorPower
    (width : Nat) (block : List NearyTile) :
    3 ^ ((swappedPhysicalUpperWord width block).length - 1) =
      3 ^ width * 3 ^ upperLength width block := by
  rw [swappedPhysicalUpperWord_length]
  have exponent_eq : upperLength width block + width + 1 - 1 =
      width + upperLength width block := by omega
  rw [exponent_eq, pow_add]

private theorem prefixCode_lower
    {width : Nat} (width_pos : 0 < width) :
    40 * 3 ^ width <
      ternaryCode (false :: (tagCode width .b).map not ++ [false]) := by
  obtain ⟨offset, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt width_pos)
  let tail := List.replicate offset true ++ [false, false]
  have word_eq :
      false :: (tagCode (offset + 1) .b).map not ++ [false] =
        false :: false :: true :: tail := by
    simp only [tail, tagCode, List.map_append, List.map_cons, Bool.not_true,
      Bool.not_false, List.map_replicate]
    simp [List.replicate_succ]
  rw [word_eq]
  have code_eq :
      ternaryCode (false :: false :: true :: tail) =
        14 * 3 ^ tail.length + ternaryCode tail := by
    simp only [ternaryCode_cons, List.length_cons, ternaryDigit, pow_succ]
    ring
  rw [code_eq]
  have tail_length : tail.length = offset + 2 := by simp [tail]
  rw [tail_length]
  have tail_power : 3 ^ (offset + 2) = 3 * 3 ^ (offset + 1) := by
    rw [pow_succ]
    ring
  rw [tail_power]
  change
    40 * 3 ^ (offset + 1) <
      14 * (3 * 3 ^ (offset + 1)) + ternaryCode tail
  have scale_pos : 0 < 3 ^ (offset + 1) := pow_pos (by omega) _
  have tail_nonneg : 0 ≤ ternaryCode tail := Nat.zero_le _
  nlinarith

private theorem equalLength_false_lt_true
    (leftTail rightTail : List Bool)
    (length_eq : (false :: leftTail).length = (true :: rightTail).length) :
    ternaryCode (false :: leftTail) < ternaryCode (true :: rightTail) := by
  simp only [List.length_cons, Nat.succ.injEq] at length_eq
  have left_bound := ternaryCode_lt_pow_length leftTail
  have power_eq : 3 ^ leftTail.length = 3 ^ rightTail.length := by rw [length_eq]
  rw [ternaryCode_cons, ternaryCode_cons, power_eq]
  simp only [ternaryDigit]
  omega

private theorem equalLength_111_lt_112
    (leftTail rightTail : List Bool)
    (length_eq :
      (false :: false :: false :: leftTail).length =
        (false :: false :: true :: rightTail).length) :
    ternaryCode (false :: false :: false :: leftTail) <
      ternaryCode (false :: false :: true :: rightTail) := by
  simp only [List.length_cons, Nat.succ.injEq] at length_eq
  have left_bound := ternaryCode_lt_pow_length leftTail
  have power_eq : 3 ^ leftTail.length = 3 ^ rightTail.length := by rw [length_eq]
  rw [ternaryCode_cons, ternaryCode_cons, ternaryCode_cons,
    ternaryCode_cons, ternaryCode_cons, ternaryCode_cons, power_eq]
  simp only [List.length_cons, ternaryDigit, pow_succ]
  omega

private theorem bodyTail_nonempty
    {width : Nat} (width_large : 6 ≤ width) {bodyTail : List TagLetter}
    (body_long : width - 1 ≤ (TagLetter.b :: bodyTail).length) :
    bodyTail ≠ [] := by
  intro body_nil
  subst bodyTail
  simp at body_long
  omega

private theorem encodedBodyTail_starts_false
    (width : Nat) {bodyTail : List TagLetter} (bodyTail_nonempty : bodyTail ≠ []) :
    ∃ tail, (tagEncode width bodyTail).map not = false :: tail := by
  cases bodyTail with
  | nil => contradiction
  | cons letter bodyTail =>
      cases letter <;>
        simp [tagEncode_cons, tagCode, List.map_append]

private theorem swappedPhysicalLowerWord_rule_c_prefix_three
    {width : Nat} (width_pos : 0 < width) {body : List TagLetter}
    (body_head : body.head? = some .b) (rest : List NearyTile) :
    ∃ tail,
      swappedPhysicalLowerWord width body (.rule .c :: rest) =
        false :: false :: true :: tail := by
  cases body with
  | nil => simp at body_head
  | cons letter bodyTail =>
      simp only [List.head?_cons, Option.some.injEq] at body_head
      subst letter
      obtain ⟨offset, rfl⟩ :=
        Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt width_pos)
      refine ⟨List.replicate offset true ++
        false :: (tagEncode offset.succ bodyTail ++ [true, false]).map not ++
          swappedPhysicalLowerWord offset.succ (.b :: bodyTail) rest, ?_⟩
      simp [swappedPhysicalLowerWord_cons, nearyLower, tagEncode_cons, tagCode,
        List.replicate_succ, List.map_append]

private theorem equalLength_cLeading_codeGap
    {width : Nat} (width_large : 6 ≤ width) {body : List TagLetter}
    (body_long : width - 1 ≤ body.length) (body_head : body.head? = some .b)
    {tile : NearyTile} (tile_c : tile.letter = .c) (rest : List NearyTile)
    (length_eq :
      (swappedPhysicalLowerWord width body (tile :: rest)).length =
        (swappedPhysicalUpperWord width (tile :: rest)).length)
    (code_gt :
      ternaryCode (swappedPhysicalLowerWord width body (tile :: rest)) <
        ternaryCode (swappedPhysicalUpperWord width (tile :: rest))) :
    80 * 3 ^ width *
        (ternaryCode (swappedPhysicalUpperWord width (tile :: rest)) -
          ternaryCode (swappedPhysicalLowerWord width body (tile :: rest))) <
      ternaryCode (swappedPhysicalLowerWord width body (tile :: rest)) := by
  cases tile with
  | erase letter =>
      have upper_false := swappedPhysicalUpperWord_starts_false width (.erase letter :: rest)
      obtain ⟨upperTail, upper_eq⟩ := upper_false
      have lower_eq :
          swappedPhysicalLowerWord width body (.erase letter :: rest) =
            true :: swappedPhysicalLowerWord width body rest := by
        simp [swappedPhysicalLowerWord_cons, nearyLower]
      have tail_length : upperTail.length = (swappedPhysicalLowerWord width body rest).length := by
        rw [upper_eq, lower_eq] at length_eq
        simpa using length_eq.symm
      have forbidden := equalLength_false_lt_true upperTail
        (swappedPhysicalLowerWord width body rest) (by simpa using tail_length)
      rw [upper_eq, lower_eq] at code_gt
      exact False.elim (Nat.lt_asymm code_gt forbidden)
  | rule letter =>
      cases letter with
      | b => simp [NearyTile.letter] at tile_c
      | c =>
          cases body with
          | nil => simp at body_head
          | cons bodyFirst bodyTail =>
              simp only [List.head?_cons, Option.some.injEq] at body_head
              subst bodyFirst
              have bodyTail_ne := bodyTail_nonempty width_large body_long
              cases rest with
              | nil =>
                  simp [swappedPhysicalUpperWord, swappedPhysicalLowerWord, spell,
                    nearyUpper, nearyLower, tagEncode_cons, tagCode, nearyMarker] at length_eq
              | cons second tail =>
                  cases secondLetter : second.letter with
                  | c =>
                      obtain ⟨upperRest, upperRest_eq⟩ :=
                        swappedPhysicalUpperWord_starts_false width tail
                      have upper_eq :
                          swappedPhysicalUpperWord width (.rule .c :: second :: tail) =
                            false :: false :: false :: upperRest := by
                        rw [swappedPhysicalUpperWord_cons, swappedPhysicalUpperWord_cons,
                          secondLetter, upperRest_eq]
                        simp [NearyTile.letter, tagCode]
                      obtain ⟨lowerRest, lower_eq⟩ :=
                        swappedPhysicalLowerWord_rule_c_prefix_three (body := .b :: bodyTail)
                          (show 0 < width by omega) (by rfl) (second :: tail)
                      have prefix_lengths :
                          (false :: false :: false :: upperRest).length =
                            (false :: false :: true :: lowerRest).length := by
                        rw [← upper_eq, ← lower_eq]
                        exact length_eq.symm
                      rw [upper_eq, lower_eq] at code_gt
                      have forbidden := equalLength_111_lt_112 upperRest _ prefix_lengths
                      exact False.elim (Nat.lt_asymm code_gt forbidden)
                  | b =>
                      obtain ⟨upperTail, upperTail_eq⟩ :=
                        swappedPhysicalUpperWord_starts_false width tail
                      obtain ⟨encodedTail, encodedTail_eq⟩ :=
                        encodedBodyTail_starts_false width bodyTail_ne
                      let shared : List Bool :=
                        false :: ((tagCode width .b).map not ++ [false])
                      have upper_eq :
                          swappedPhysicalUpperWord width (.rule .c :: second :: tail) =
                            shared ++ upperTail := by
                        simp only [shared]
                        rw [swappedPhysicalUpperWord_cons, swappedPhysicalUpperWord_cons,
                          secondLetter, upperTail_eq]
                        simp [NearyTile.letter, tagCode, List.append_assoc]
                      have lower_eq :
                          swappedPhysicalLowerWord width (.b :: bodyTail)
                              (.rule .c :: second :: tail) =
                            shared ++
                              (encodedTail ++
                                (false :: true ::
                                  swappedPhysicalLowerWord width (.b :: bodyTail)
                                    (second :: tail))) := by
                        simp only [shared]
                        rw [swappedPhysicalLowerWord_cons]
                        simp [nearyLower, tagEncode_cons, tagCode, List.map_append,
                          encodedTail_eq, List.append_assoc]
                      let lowerTail : List Bool :=
                        encodedTail ++
                          (false :: true ::
                            swappedPhysicalLowerWord width (.b :: bodyTail) (second :: tail))
                      have tail_length : upperTail.length = lowerTail.length := by
                        rw [upper_eq, lower_eq] at length_eq
                        simp only [List.length_append] at length_eq
                        simp only [lowerTail, List.length_append,
                          List.length_cons] at length_eq ⊢
                        omega
                      have prefix_pos : 40 * 3 ^ width < ternaryCode shared := by
                        simpa [shared, List.append_assoc] using
                          (prefixCode_lower (show 0 < width by omega))
                      have spread := ternaryCode_spread tail_length
                      have upper_code_eq :
                          ternaryCode
                              (swappedPhysicalUpperWord width (.rule .c :: second :: tail)) =
                            ternaryCode shared * 3 ^ lowerTail.length +
                              ternaryCode upperTail := by
                        rw [upper_eq, ternaryCode_append, tail_length]
                        ring
                      have lower_code_eq :
                          ternaryCode
                              (swappedPhysicalLowerWord width (.b :: bodyTail)
                                (.rule .c :: second :: tail)) =
                            ternaryCode shared * 3 ^ lowerTail.length +
                              ternaryCode lowerTail := by
                        rw [lower_eq, ternaryCode_append]
                        simp only [lowerTail]
                        ring
                      have prefix_scaled :
                          40 * 3 ^ width * 3 ^ lowerTail.length <
                            ternaryCode shared * 3 ^ lowerTail.length :=
                        mul_lt_mul_of_pos_right prefix_pos (pow_pos (by omega) _)
                      have tail_gap :
                          2 * (ternaryCode upperTail - ternaryCode lowerTail) <
                            3 ^ lowerTail.length := by
                        rw [tail_length] at spread
                        omega
                      have gap_eq :
                          ternaryCode
                              (swappedPhysicalUpperWord width (.rule .c :: second :: tail)) -
                              ternaryCode
                                (swappedPhysicalLowerWord width (.b :: bodyTail)
                                  (.rule .c :: second :: tail)) =
                            ternaryCode upperTail - ternaryCode lowerTail := by
                        rw [upper_code_eq, lower_code_eq]
                        omega
                      rw [gap_eq, lower_code_eq]
                      calc
                        80 * 3 ^ width *
                            (ternaryCode upperTail - ternaryCode lowerTail) =
                            (40 * 3 ^ width) *
                              (2 * (ternaryCode upperTail - ternaryCode lowerTail)) := by
                                ring
                        _ < (40 * 3 ^ width) * 3 ^ lowerTail.length :=
                          (Nat.mul_lt_mul_left
                            (show 0 < 40 * 3 ^ width by positivity)).2 tail_gap
                        _ < ternaryCode shared * 3 ^ lowerTail.length := prefix_scaled
                        _ ≤ ternaryCode shared * 3 ^ lowerTail.length +
                            ternaryCode lowerTail := Nat.le_add_right _ _

private theorem shortLower_backwardBlock_above_seven_fifths
    {width : Nat} (width_large : 6 ≤ width) {body : List TagLetter}
    (tile : NearyTile) (rest : List NearyTile) {current : ℚ}
    (current_above : (terminalDiscrepancy width : ℚ) < current)
    (length_short :
      (swappedPhysicalLowerWord width body (tile :: rest)).length <
        (swappedPhysicalUpperWord width (tile :: rest)).length) :
    (7 : ℚ) / 5 <
      backwardBlock width
        (swappedUpperCode width (tile :: rest))
        (swappedLowerCode width body (tile :: rest))
        (upperPower width (tile :: rest)) current := by
  let upper := swappedPhysicalUpperWord width (tile :: rest)
  let lower := swappedPhysicalLowerWord width body (tile :: rest)
  let power : Nat := 3 ^ upperLength width (tile :: rest)
  let scale : Nat := 3 ^ width
  let upperCode := ternaryCode upper
  let lowerCode := ternaryCode lower
  have scale_large : 729 ≤ scale := by
    simp only [scale]
    have power_bound : 3 ^ 6 ≤ 3 ^ width :=
      Nat.pow_le_pow_right (by norm_num) width_large
    norm_num at power_bound ⊢
    exact power_bound
  have scale_pos : 0 < scale := pow_pos (by omega) width
  have power_pos_nat : 0 < power := by simp [power]
  have power_pos : (0 : ℚ) < power := by exact_mod_cast power_pos_nat
  have lower_nonempty : lower ≠ [] := by
    simpa only [lower, swappedPhysicalLowerWord, swappedPhysicalLowerWord] using
      swappedPhysicalLowerWord_nonempty width body tile rest
  have lower_pos_nat : 0 < lowerCode :=
    lt_of_lt_of_le (pow_pos (by omega) (lower.length - 1))
      (ternaryCode_lower_bound lower lower_nonempty)
  have lower_pos : (0 : ℚ) < lowerCode := by exact_mod_cast lower_pos_nat
  have upper_scale_bound := ternaryCode_scale_le_twice_add_one upper
  have predecessor_power := swappedPhysicalUpperWord_predecessorPower width (tile :: rest)
  have upper_length_pos : 0 < upper.length := by
    simp [upper, swappedPhysicalUpperWord_length]
  have upper_power_eq :
      3 ^ upper.length = 3 * scale * power := by
    have full_power : 3 ^ upper.length = 3 * 3 ^ (upper.length - 1) := by
      obtain ⟨predecessor, upper_eq⟩ :=
        Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt upper_length_pos)
      rw [upper_eq, Nat.succ_sub_one, pow_succ]
      ring
    rw [full_power, predecessor_power]
    simp only [scale, power]
    ring
  have upper_code_bound :
      3 * scale * power ≤ 2 * upperCode + 1 := by
    rw [← upper_power_eq]
    exact upper_scale_bound
  have length_short' : lower.length < upper.length := by
    simpa only [lower, upper] using length_short
  have exponent_le : lower.length ≤ upper.length - 1 := by omega
  have lower_power_le : 3 ^ lower.length ≤ 3 ^ (upper.length - 1) :=
    Nat.pow_le_pow_right (by norm_num) exponent_le
  have lower_code_upper : lowerCode < scale * power := by
    have code_bound := ternaryCode_lt_pow_length lower
    rw [predecessor_power] at lower_power_le
    simp only [power]
    exact code_bound.trans_le lower_power_le
  obtain ⟨correction_pos, correction_lt⟩ :=
    blockCorrection_pos_lt_three width_large current_above
  have upper_code_bound_rat :
      3 * (scale : ℚ) * power ≤ 2 * upperCode + 1 := by
    exact_mod_cast upper_code_bound
  have lower_code_upper_rat :
      (lowerCode : ℚ) < scale * power := by
    exact_mod_cast lower_code_upper
  have numerator_bound :
      (7 : ℚ) / 5 * lowerCode <
        upperCode - blockCorrection width current * power := by
    have scale_large_rat : (729 : ℚ) ≤ scale := by exact_mod_cast scale_large
    have power_one_nat : 1 ≤ power := Nat.one_le_iff_ne_zero.mpr power_pos_nat.ne'
    have power_one : (1 : ℚ) ≤ power := by exact_mod_cast power_one_nat
    have scale_thirty_five : (35 : ℚ) < scale := by linarith
    have scale_power_gap :
        35 * (power : ℚ) < scale * power :=
      mul_lt_mul_of_pos_right scale_thirty_five power_pos
    have correction_scaled :
        blockCorrection width current * power < 3 * power :=
      mul_lt_mul_of_pos_right correction_lt power_pos
    nlinarith
  have lower_code_cast :
      (swappedLowerCode width body (tile :: rest) : ℚ) = lowerCode := by
    simp only [swappedLowerCode, lowerCode, lower, swappedPhysicalLowerWord]
    norm_num
  have upper_code_cast :
      (swappedUpperCode width (tile :: rest) : ℚ) = upperCode := by
    simp only [swappedUpperCode, upperCode, upper, swappedPhysicalUpperWord]
    norm_num
  have lower_actual_pos :
      (0 : ℚ) < swappedLowerCode width body (tile :: rest) := by
    rw [lower_code_cast]
    exact lower_pos
  have denominator_pos :
      (0 : ℚ) < terminalDiscrepancy width + chamberRadius width * current := by
    have scale_large_rat : (729 : ℚ) ≤ widthScale width := by
      have power_bound : 3 ^ 6 ≤ 3 ^ width :=
        Nat.pow_le_pow_right (by norm_num) width_large
      norm_num [widthScale] at power_bound ⊢
      exact_mod_cast power_bound
    have terminal_pos : (0 : ℚ) < terminalDiscrepancy width := by
      simp only [terminalDiscrepancy]
      push_cast
      linarith
    have radius_pos : (0 : ℚ) < chamberRadius width := by
      simp only [chamberRadius]
      push_cast
      linarith
    have current_pos : (0 : ℚ) < current := terminal_pos.trans current_above
    positivity
  have denominator_ne := denominator_pos.ne'
  rw [backwardBlock_eq_sub_correction lower_actual_pos.ne' denominator_ne,
    lower_code_cast, upper_code_cast]
  have actual_power_cast :
      (upperPower width (tile :: rest) : ℚ) = power := by
    simp [upperPower, power]
  rw [actual_power_cast]
  exact (lt_div_iff₀ lower_pos).2 numerator_bound

private theorem chamberCeiling_lt_seven_fifths
    {width : Nat} (width_large : 6 ≤ width) :
    (chamberRadius width : ℚ) / (chamberRadius width - 3) < (7 : ℚ) / 5 := by
  have scale_large : (729 : ℚ) ≤ widthScale width := by
    have power_bound : 3 ^ 6 ≤ 3 ^ width :=
      Nat.pow_le_pow_right (by norm_num) width_large
    norm_num [widthScale] at power_bound ⊢
    exact_mod_cast power_bound
  have denominator_pos : (0 : ℚ) < chamberRadius width - 3 := by
    simp only [chamberRadius]
    push_cast
    linarith
  apply (div_lt_iff₀ denominator_pos).2
  simp only [chamberRadius]
  push_cast
  linarith

/-- Boundary intercept after pulling a near-diagonal carrier through singleton `D_c`. -/
def postDeletionCIntercept (width : Nat) (epsilon : ℚ) : ℚ :=
  setterMarker width * chamberRadius width ^ 2 * epsilon /
    (6 * setterMarker width +
      (chamberRadius width ^ 2 + 2 * chamberRadius width -
        6 * setterMarker width) * epsilon)

private theorem postDeletionCIntercept_identity
    {marker radius terminal epsilon : ℚ}
    (terminal_ne : terminal ≠ 0)
    (carrier_denominator_ne :
      6 * marker + (2 * radius - 6 * marker) * epsilon ≠ 0)
    (intercept_denominator_ne :
      6 * marker +
        (radius ^ 2 + 2 * radius - 6 * marker) * epsilon ≠ 0)
    (boundary_denominator_ne :
      terminal + radius *
        (terminal * radius * epsilon /
          (6 * marker + (2 * radius - 6 * marker) * epsilon)) ≠ 0) :
    marker * radius ^ 2 * epsilon /
        (6 * marker +
          (radius ^ 2 + 2 * radius - 6 * marker) * epsilon) =
      marker * radius *
          (terminal * radius * epsilon /
            (6 * marker + (2 * radius - 6 * marker) * epsilon)) /
        (terminal + radius *
          (terminal * radius * epsilon /
            (6 * marker + (2 * radius - 6 * marker) * epsilon))) := by
  let carrierDenominator :=
    6 * marker + (2 * radius - 6 * marker) * epsilon
  let interceptDenominator :=
    6 * marker +
      (radius ^ 2 + 2 * radius - 6 * marker) * epsilon
  have denominator_sum :
      interceptDenominator = carrierDenominator + radius ^ 2 * epsilon := by
    simp only [interceptDenominator, carrierDenominator]
    ring
  have boundary_eq :
      terminal + radius *
          (terminal * radius * epsilon / carrierDenominator) =
        terminal * interceptDenominator / carrierDenominator := by
    rw [denominator_sum]
    field_simp [show carrierDenominator ≠ 0 by
      simpa only [carrierDenominator] using carrier_denominator_ne]
  have boundary_ne :
      terminal * interceptDenominator / carrierDenominator ≠ 0 := by
    rw [← boundary_eq]
    simpa only [carrierDenominator] using boundary_denominator_ne
  change
    marker * radius ^ 2 * epsilon / interceptDenominator =
      marker * radius *
          (terminal * radius * epsilon / carrierDenominator) /
        (terminal + radius *
          (terminal * radius * epsilon / carrierDenominator))
  rw [boundary_eq]
  field_simp [terminal_ne,
    show carrierDenominator ≠ 0 by
      simpa only [carrierDenominator] using carrier_denominator_ne,
    show interceptDenominator ≠ 0 by
      simpa only [interceptDenominator] using intercept_denominator_ne,
    boundary_ne]

/-- The closed intercept is the boundary coordinate of the exact post-`D_c` carrier. -/
theorem postDeletionCIntercept_eq_carrierBoundary
    {width : Nat} (width_large : 6 ≤ width) {epsilon : ℚ}
    (epsilon_pos : 0 < epsilon)
    (epsilon_upper : epsilon < 1 / (80 * widthScale width)) :
    postDeletionCIntercept width epsilon =
      setterMarker width * chamberRadius width *
          deletionCSuccessorSlope width epsilon /
        (terminalDiscrepancy width +
          chamberRadius width * deletionCSuccessorSlope width epsilon) := by
  have scale_large : (729 : ℚ) ≤ widthScale width := by
    have power_bound : 3 ^ 6 ≤ 3 ^ width :=
      Nat.pow_le_pow_right (by norm_num) width_large
    norm_num [widthScale] at power_bound ⊢
    exact_mod_cast power_bound
  have scale_pos : (0 : ℚ) < widthScale width := by linarith
  have radius_pos : (0 : ℚ) < chamberRadius width := by
    simp only [chamberRadius]
    push_cast
    linarith
  have marker_pos : (0 : ℚ) < setterMarker width := by
    simp only [setterMarker]
    push_cast
    linarith
  have terminal_pos : (0 : ℚ) < terminalDiscrepancy width := by
    simp only [terminalDiscrepancy]
    push_cast
    linarith
  have coefficient_pos :
      (0 : ℚ) < chamberRadius width ^ 2 + 2 * chamberRadius width -
        6 * setterMarker width := by
    have scale_fourteen : (14 : ℚ) ≤ widthScale width := by linarith
    have product_nonneg :
        (0 : ℚ) ≤ ((widthScale width : ℚ) - 14) * widthScale width :=
      mul_nonneg (sub_nonneg.mpr scale_fourteen) scale_pos.le
    simp only [chamberRadius, setterMarker]
    push_cast
    nlinarith
  have carrier_denominator_pos :
      0 < 6 * setterMarker width +
        (2 * chamberRadius width - 6 * setterMarker width) * epsilon := by
    have epsilon_cross :
        80 * widthScale width * epsilon < 1 := by
      have denominator_pos : (0 : ℚ) < 80 * widthScale width := by positivity
      have crossed := (lt_div_iff₀ denominator_pos).mp epsilon_upper
      nlinarith
    simp only [chamberRadius, setterMarker]
    push_cast
    nlinarith
  have intercept_denominator_pos :
      0 < 6 * setterMarker width +
        (chamberRadius width ^ 2 + 2 * chamberRadius width -
          6 * setterMarker width) * epsilon := by positivity
  have carrier_pos : 0 < deletionCSuccessorSlope width epsilon := by
    simp only [deletionCSuccessorSlope]
    exact div_pos (mul_pos (mul_pos terminal_pos radius_pos) epsilon_pos)
      carrier_denominator_pos
  have boundary_denominator_pos :
      0 < terminalDiscrepancy width +
        chamberRadius width * deletionCSuccessorSlope width epsilon := by positivity
  simp only [postDeletionCIntercept, deletionCSuccessorSlope]
  exact postDeletionCIntercept_identity terminal_pos.ne'
    carrier_denominator_pos.ne' intercept_denominator_pos.ne'
    boundary_denominator_pos.ne'

/-- Every gap below `1/(80ρ)` leaves its post-`D_c` intercept below
`8·3^(width-6)/5`. -/
theorem postDeletionCIntercept_pos_lt_eight_fifths
    {width : Nat} (width_large : 6 ≤ width) {epsilon : ℚ}
    (epsilon_pos : 0 < epsilon)
    (epsilon_upper : epsilon < 1 / (80 * widthScale width)) :
    0 < postDeletionCIntercept width epsilon ∧
      postDeletionCIntercept width epsilon <
        8 * chamberQuotient width / 5 := by
  let rho : ℚ := widthScale width
  let radius : ℚ := chamberRadius width
  let marker : ℚ := setterMarker width
  let quotient : ℚ := chamberQuotient width
  have rho_large : (729 : ℚ) ≤ rho := by
    have power_bound : 3 ^ 6 ≤ 3 ^ width :=
      Nat.pow_le_pow_right (by norm_num) width_large
    norm_num [rho, widthScale] at power_bound ⊢
    exact_mod_cast power_bound
  have rho_pos : 0 < rho := by linarith
  have radius_pos : 0 < radius := by
    simp only [radius, chamberRadius]
    push_cast
    linarith
  have marker_pos : 0 < marker := by
    simp only [marker, setterMarker]
    push_cast
    linarith
  have quotient_pos : 0 < quotient := by
    simp only [quotient]
    exact_mod_cast chamberQuotient_pos width
  have rho_eq : rho = 729 * quotient := by
    simp only [rho, quotient]
    exact_mod_cast widthScale_eq_729_mul_chamberQuotient width_large
  have coefficient_pos :
      0 < radius ^ 2 + 2 * radius - 6 * marker := by
    have rho_fourteen : (14 : ℚ) ≤ rho := by linarith
    have product_nonneg : 0 ≤ (rho - 14) * rho :=
      mul_nonneg (sub_nonneg.mpr rho_fourteen) rho_pos.le
    simp only [radius, marker, chamberRadius, setterMarker]
    push_cast
    nlinarith
  have denominator_pos :
      0 < 6 * marker +
        (radius ^ 2 + 2 * radius - 6 * marker) * epsilon := by positivity
  have numerator_pos : 0 < marker * radius ^ 2 * epsilon := by positivity
  constructor
  · simp only [postDeletionCIntercept]
    exact div_pos numerator_pos denominator_pos
  · have epsilon_numerator_bound :
        marker * radius ^ 2 * epsilon <
          marker * radius ^ 2 * (1 / (80 * rho)) :=
      mul_lt_mul_of_pos_left (by simpa only [rho] using epsilon_upper)
        (mul_pos marker_pos (sq_pos_of_pos radius_pos))
    have radius_lt : radius < rho := by
      simp only [radius, chamberRadius, rho]
      push_cast
      linarith
    have radius_sq_lt : radius ^ 2 < rho ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr radius_lt) (add_pos radius_pos rho_pos)]
    have comparison :
        radius ^ 2 / (80 * rho) < 48 * quotient / 5 := by
      have comparison_cross :
          radius ^ 2 < (48 * quotient / 5) * (80 * rho) := by
        rw [rho_eq] at radius_sq_lt ⊢
        have quotient_sq_pos : 0 < quotient ^ 2 := sq_pos_of_pos quotient_pos
        nlinarith
      exact (div_lt_iff₀ (mul_pos (by norm_num) rho_pos)).2 comparison_cross
    have marker_comparison :
        marker * radius ^ 2 * (1 / (80 * rho)) <
          (8 * quotient / 5) * (6 * marker) := by
      have scaled := mul_lt_mul_of_pos_left comparison marker_pos
      calc
        marker * radius ^ 2 * (1 / (80 * rho)) =
            marker * (radius ^ 2 / (80 * rho)) := by ring
        _ < marker * (48 * quotient / 5) := scaled
        _ = (8 * quotient / 5) * (6 * marker) := by ring
    have denominator_lower :
        6 * marker < 6 * marker +
          (radius ^ 2 + 2 * radius - 6 * marker) * epsilon := by
      nlinarith [mul_pos coefficient_pos epsilon_pos]
    have target_pos : 0 < 8 * quotient / 5 := by positivity
    have target_scaled := mul_lt_mul_of_pos_left denominator_lower target_pos
    simp only [postDeletionCIntercept]
    apply (div_lt_iff₀ denominator_pos).2
    exact epsilon_numerator_bound.trans
      (marker_comparison.trans target_scaled)

private theorem longLower_physicalBackwardBlock_below_one
    {width : Nat} (width_large : 6 ≤ width) {body : List TagLetter}
    (tile : NearyTile) (rest : List NearyTile) {current : ℚ}
    (current_above : (terminalDiscrepancy width : ℚ) < current)
    (length_long :
      (swappedPhysicalUpperWord width (tile :: rest)).length <
        (swappedPhysicalLowerWord width body (tile :: rest)).length) :
    backwardBlock width
        (swappedUpperCode width (tile :: rest))
        (swappedLowerCode width body (tile :: rest))
        (upperPower width (tile :: rest)) current < 1 := by
  let upper := swappedPhysicalUpperWord width (tile :: rest)
  let lower := swappedPhysicalLowerWord width body (tile :: rest)
  have lower_nonempty : lower ≠ [] := by
    simpa only [lower, swappedPhysicalLowerWord, swappedPhysicalLowerWord] using
      swappedPhysicalLowerWord_nonempty width body tile rest
  have lower_code_bound := ternaryCode_lower_bound lower lower_nonempty
  have length_long' : upper.length < lower.length := by
    simpa only [upper, lower] using length_long
  have exponent_le : upper.length ≤ lower.length - 1 := by omega
  have power_le : 3 ^ upper.length ≤ 3 ^ (lower.length - 1) :=
    Nat.pow_le_pow_right (by norm_num) exponent_le
  have upper_length_pos : 0 < upper.length := by simp [upper, swappedPhysicalUpperWord_length]
  have full_power : 3 ^ upper.length =
      3 * 3 ^ width * 3 ^ upperLength width (tile :: rest) := by
    have successor_power : 3 ^ upper.length = 3 * 3 ^ (upper.length - 1) := by
      obtain ⟨predecessor, upper_eq⟩ :=
        Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt upper_length_pos)
      rw [upper_eq, Nat.succ_sub_one, pow_succ]
      ring
    rw [successor_power, swappedPhysicalUpperWord_predecessorPower]
    ring
  have lower_long_nat :
      3 * 3 ^ width * 3 ^ upperLength width (tile :: rest) ≤ ternaryCode lower := by
    rw [← full_power]
    exact power_le.trans lower_code_bound
  have lower_long :
      3 * (widthScale width : ℚ) * upperPower width (tile :: rest) ≤
        swappedLowerCode width body (tile :: rest) := by
    have cast_bound :
        (3 : ℤ) * 3 ^ width * 3 ^ upperLength width (tile :: rest) ≤
          ternaryCode lower := by exact_mod_cast lower_long_nat
    have lower_cast :
        swappedLowerCode width body (tile :: rest) = (ternaryCode lower : ℤ) := by
      simp only [swappedLowerCode, lower, swappedPhysicalLowerWord]
    rw [lower_cast]
    simp only [widthScale, upperPower]
    exact_mod_cast cast_bound
  have lower_pos :
      (0 : ℚ) < swappedLowerCode width body (tile :: rest) := by
    have lower_pos_nat : 0 < ternaryCode lower :=
      lt_of_lt_of_le (pow_pos (by omega) (lower.length - 1)) lower_code_bound
    have lower_cast :
        (swappedLowerCode width body (tile :: rest) : ℚ) = ternaryCode lower := by
      simp only [swappedLowerCode, lower, swappedPhysicalLowerWord]
      norm_num
    rw [lower_cast]
    exact_mod_cast lower_pos_nat
  have upperPower_pos :
      (0 : ℚ) < upperPower width (tile :: rest) := by
    simp [upperPower]
  have upper_bound_int :=
    (swappedUpperCode_cylinder (show 0 < width by omega) (tile :: rest)).2
  have upper_bound :
      (swappedUpperCode width (tile :: rest) : ℚ) <
        2 * widthScale width * upperPower width (tile :: rest) := by
    exact_mod_cast upper_bound_int
  exact longLower_backwardBlock_below_one width_large current_above
    lower_pos upperPower_pos lower_long upper_bound

/-- Every compiler-emitted physical block entering the singleton-`D_c` contraction chamber
from above the terminal ray has a uniformly tiny relative gap. -/
theorem physicalBackwardBlock_chamber_epsilon_lt
    {width : Nat} (width_large : 6 ≤ width) {body : List TagLetter}
    (body_long : width - 1 ≤ body.length) (body_head : body.head? = some .b)
    (tile : NearyTile) (rest : List NearyTile) {current : ℚ}
    (current_above : (terminalDiscrepancy width : ℚ) < current)
    (chamber :
      1 < backwardBlock width
          (swappedUpperCode width (tile :: rest))
          (swappedLowerCode width body (tile :: rest))
          (upperPower width (tile :: rest)) current ∧
        backwardBlock width
          (swappedUpperCode width (tile :: rest))
          (swappedLowerCode width body (tile :: rest))
          (upperPower width (tile :: rest)) current <
          (chamberRadius width : ℚ) / (chamberRadius width - 3)) :
    (backwardBlock width
          (swappedUpperCode width (tile :: rest))
          (swappedLowerCode width body (tile :: rest))
          (upperPower width (tile :: rest)) current - 1) /
        backwardBlock width
          (swappedUpperCode width (tile :: rest))
          (swappedLowerCode width body (tile :: rest))
          (upperPower width (tile :: rest)) current <
      1 / (80 * widthScale width) := by
  let block := tile :: rest
  let image := backwardBlock width
    (swappedUpperCode width block) (swappedLowerCode width body block)
    (upperPower width block) current
  let upper := swappedPhysicalUpperWord width block
  let lower := swappedPhysicalLowerWord width body block
  have image_chamber :
      1 < image ∧ image <
        (chamberRadius width : ℚ) / (chamberRadius width - 3) := by
    simpa only [image, block] using chamber
  by_cases length_short : lower.length < upper.length
  · have above := shortLower_backwardBlock_above_seven_fifths width_large
      tile rest current_above (by simpa only [lower, upper, block] using length_short)
    have ceiling := chamberCeiling_lt_seven_fifths width_large
    change (7 : ℚ) / 5 < image at above
    linarith
  · by_cases length_long : upper.length < lower.length
    · have below := longLower_physicalBackwardBlock_below_one width_large
        tile rest current_above (by simpa only [lower, upper, block] using length_long)
      change image < 1 at below
      linarith
    · have length_eq : lower.length = upper.length := by omega
      have tile_c : tile.letter = .c := by
        cases letter_eq : tile.letter with
        | b =>
            have excluded :=
              bLeading_physicalBackwardBlock_avoids_deletionCChamber
                width_large body letter_eq rest current_above
            exact False.elim (excluded (by simpa only [image, block] using image_chamber))
        | c => rfl
      have lower_nonempty : lower ≠ [] := by
        simpa only [lower, swappedPhysicalLowerWord, swappedPhysicalLowerWord, block] using
          swappedPhysicalLowerWord_nonempty width body tile rest
      have lower_pos_nat : 0 < ternaryCode lower :=
        lt_of_lt_of_le (pow_pos (by omega) (lower.length - 1))
          (ternaryCode_lower_bound lower lower_nonempty)
      have lower_pos : (0 : ℚ) < ternaryCode lower := by exact_mod_cast lower_pos_nat
      have lower_code_cast :
          (swappedLowerCode width body block : ℚ) = ternaryCode lower := by
        simp only [swappedLowerCode, lower, swappedPhysicalLowerWord, block]
        norm_num
      have upper_code_cast :
          (swappedUpperCode width block : ℚ) = ternaryCode upper := by
        simp only [swappedUpperCode, upper, swappedPhysicalUpperWord, block]
        norm_num
      have power_pos : (0 : ℚ) < upperPower width block := by simp [upperPower]
      obtain ⟨correction_pos, -⟩ :=
        blockCorrection_pos_lt_three width_large current_above
      have terminal_denominator_pos :
          (0 : ℚ) < terminalDiscrepancy width + chamberRadius width * current := by
        have scale_large : (729 : ℚ) ≤ widthScale width := by
          have power_bound : 3 ^ 6 ≤ 3 ^ width :=
            Nat.pow_le_pow_right (by norm_num) width_large
          norm_num [widthScale] at power_bound ⊢
          exact_mod_cast power_bound
        have terminal_pos : (0 : ℚ) < terminalDiscrepancy width := by
          simp only [terminalDiscrepancy]
          push_cast
          linarith
        have radius_pos : (0 : ℚ) < chamberRadius width := by
          simp only [chamberRadius]
          push_cast
          linarith
        have current_pos : (0 : ℚ) < current := terminal_pos.trans current_above
        positivity
      have image_eq :
          image =
            ((ternaryCode upper : ℚ) -
                blockCorrection width current * upperPower width block) /
              ternaryCode lower := by
        simp only [image]
        rw [backwardBlock_eq_sub_correction
          (by rw [lower_code_cast]; exact lower_pos.ne')
          terminal_denominator_pos.ne', lower_code_cast, upper_code_cast]
      have code_gt_rat : (ternaryCode lower : ℚ) < ternaryCode upper := by
        have crossed := (lt_div_iff₀ lower_pos).mp (by
          rw [image_eq] at image_chamber
          exact image_chamber.1)
        nlinarith [mul_pos correction_pos power_pos]
      have code_gt : ternaryCode lower < ternaryCode upper := by
        exact_mod_cast code_gt_rat
      have code_gap := equalLength_cLeading_codeGap width_large body_long body_head
        tile_c rest (by simpa only [lower, upper, block] using length_eq) (by
          simpa only [lower, upper, block] using code_gt)
      have scale_pos_int : (0 : ℤ) < widthScale width := by simp [widthScale]
      have scale_pos : (0 : ℚ) < widthScale width := by exact_mod_cast scale_pos_int
      have code_gap_rat :
          80 * (widthScale width : ℚ) *
              ((ternaryCode upper : ℚ) - ternaryCode lower) <
            ternaryCode lower := by
        have code_gap_int :
            (80 : ℤ) * 3 ^ width *
                ((ternaryCode upper - ternaryCode lower : Nat) : ℤ) <
              ternaryCode lower := by exact_mod_cast code_gap
        have sub_cast :
            ((ternaryCode upper - ternaryCode lower : Nat) : ℤ) =
              (ternaryCode upper : ℤ) - ternaryCode lower := by
          rw [Nat.cast_sub code_gt.le]
        rw [sub_cast] at code_gap_int
        have cast_gap :
            (80 : ℚ) * ((3 ^ width : Nat) : ℚ) *
                ((ternaryCode upper : ℚ) - ternaryCode lower) <
              ternaryCode lower := by exact_mod_cast code_gap_int
        change
          (80 : ℚ) * ((3 ^ width : Nat) : ℚ) *
              ((ternaryCode upper : ℚ) - ternaryCode lower) <
            ternaryCode lower
        exact cast_gap
      have code_ratio_gap :
          (ternaryCode upper : ℚ) / ternaryCode lower - 1 <
            1 / (80 * widthScale width) := by
        have denominator_pos : (0 : ℚ) < 80 * widthScale width := by positivity
        rw [show (ternaryCode upper : ℚ) / ternaryCode lower - 1 =
          ((ternaryCode upper : ℚ) - ternaryCode lower) /
            ternaryCode lower by field_simp [lower_pos.ne']]
        exact (div_lt_div_iff₀ lower_pos denominator_pos).2 (by nlinarith)
      have image_lt_code_ratio :
          image < (ternaryCode upper : ℚ) / ternaryCode lower := by
        rw [image_eq]
        exact (div_lt_div_iff_of_pos_right lower_pos).2
          (by nlinarith [mul_pos correction_pos power_pos])
      have image_pos : 0 < image := by linarith [image_chamber.1]
      have epsilon_lt_gap : (image - 1) / image < image - 1 := by
        rw [div_lt_iff₀ image_pos]
        nlinarith [image_chamber.1]
      change (image - 1) / image < 1 / (80 * widthScale width)
      linarith

/-- A physical chamber entry leaves a positive post-`D_c` boundary intercept below
`8·3^(width-6)/5`. -/
theorem physicalBackwardBlock_postDeletionCIntercept_bound
    {width : Nat} (width_large : 6 ≤ width) {body : List TagLetter}
    (body_long : width - 1 ≤ body.length) (body_head : body.head? = some .b)
    (tile : NearyTile) (rest : List NearyTile) {current : ℚ}
    (current_above : (terminalDiscrepancy width : ℚ) < current)
    (chamber :
      1 < backwardBlock width
          (swappedUpperCode width (tile :: rest))
          (swappedLowerCode width body (tile :: rest))
          (upperPower width (tile :: rest)) current ∧
        backwardBlock width
          (swappedUpperCode width (tile :: rest))
          (swappedLowerCode width body (tile :: rest))
          (upperPower width (tile :: rest)) current <
          (chamberRadius width : ℚ) / (chamberRadius width - 3)) :
    0 < postDeletionCIntercept width
        ((backwardBlock width
            (swappedUpperCode width (tile :: rest))
            (swappedLowerCode width body (tile :: rest))
            (upperPower width (tile :: rest)) current - 1) /
          backwardBlock width
            (swappedUpperCode width (tile :: rest))
            (swappedLowerCode width body (tile :: rest))
            (upperPower width (tile :: rest)) current) ∧
      postDeletionCIntercept width
          ((backwardBlock width
              (swappedUpperCode width (tile :: rest))
              (swappedLowerCode width body (tile :: rest))
              (upperPower width (tile :: rest)) current - 1) /
            backwardBlock width
              (swappedUpperCode width (tile :: rest))
              (swappedLowerCode width body (tile :: rest))
              (upperPower width (tile :: rest)) current) <
        8 * chamberQuotient width / 5 := by
  let image := backwardBlock width
    (swappedUpperCode width (tile :: rest))
    (swappedLowerCode width body (tile :: rest))
    (upperPower width (tile :: rest)) current
  have image_pos : 0 < image := by
    change 0 < backwardBlock width
      (swappedUpperCode width (tile :: rest))
      (swappedLowerCode width body (tile :: rest))
      (upperPower width (tile :: rest)) current
    linarith [chamber.1]
  have epsilon_pos : 0 < (image - 1) / image := by
    exact div_pos (sub_pos.mpr (by simpa only [image] using chamber.1)) image_pos
  have epsilon_upper :
      (image - 1) / image < 1 / (80 * widthScale width) := by
    simpa only [image] using
      physicalBackwardBlock_chamber_epsilon_lt width_large body_long body_head
        tile rest current_above chamber
  simpa only [image] using
    postDeletionCIntercept_pos_lt_eight_fifths width_large epsilon_pos epsilon_upper

end MatrixMortality.SwappedSetterUniversalEntryGap
