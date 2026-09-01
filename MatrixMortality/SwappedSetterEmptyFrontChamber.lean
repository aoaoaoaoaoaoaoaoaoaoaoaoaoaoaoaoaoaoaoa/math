import MatrixMortality.SwappedSetterEmptyFrontRay

set_option autoImplicit false

/-!
# Empty-front backward chamber

The local `D_b;D_c;D_c` rays begin above the terminal discrepancy. Pulling one
further physical block backward can enter the thin `D_c`-contraction chamber
only through a `c`-leading block. The exceptional canonical `R_c;D_b` pullback
has a sharper near-diagonal gap. This module records those cuts and the exact
successor formula; it does not assert global entry reachability or a pole.
-/

namespace MatrixMortality.SwappedSetterEmptyFrontChamber

open SwappedSetterMultitransfer SwappedSetterThresholdCarry
  SwappedSetterEmptyFrontRay

/-- Rational carrier represented by the local `D_b` antecedent. -/
def emptyFrontSeed (offset : Nat) (upperPrefix : ℤ) : ℚ :=
  deletionBInverseNumerator offset upperPrefix /
    deletionBInverseDenominator offset upperPrefix

/-- Exact inverse projective action of one physical block. -/
def backwardBlock (width : Nat) (punctuated lower upperPower current : ℚ) : ℚ :=
  punctuated / lower +
    terminalDiscrepancy width * setterMarker width * upperPower /
      (lower * (centeredCoefficient width * current - terminalDiscrepancy width))

/-- Image of the ordinary reset under the corresponding forward block. -/
def entryThreshold (width : Nat) (punctuated upperPower : ℚ) : ℚ :=
  terminalDiscrepancy width *
      (punctuated - setterMarker width * upperPower) /
    (centeredCoefficient width * punctuated)

/-- Positive magnitude of the centered coefficient. -/
def chamberRadius (width : Nat) : ℤ :=
  widthScale width - 2

/-- Positive correction subtracted from a normalized upper code above the terminal ray. -/
def blockCorrection (width : Nat) (current : ℚ) : ℚ :=
  terminalDiscrepancy width * setterMarker width /
    (terminalDiscrepancy width + chamberRadius width * current)

/-- Canonical minimum-length compiler body for the exceptional `R_c;D_b` backward block. -/
def canonicalRcDbBody (width : Nat) : List TagLetter :=
  .b :: List.replicate (width - 2) .c

/-- Backward image through the exceptional `R_c;D_b` block against its canonical body. -/
def canonicalRcDbBackward (width : Nat) (current : ℚ) : ℚ :=
  backwardBlock width
    (swappedUpperCode width [.rule .c, .erase .b])
    (swappedLowerCode width (canonicalRcDbBody width) [.rule .c, .erase .b])
    (upperPower width [.rule .c, .erase .b]) current

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

private theorem ternaryCode_replicate_true (count : Nat) :
    ternaryCode (List.replicate count true) = 3 ^ count - 1 := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ, ternaryCode_cons, List.length_replicate,
        induction, pow_succ]
      simp only [ternaryDigit]
      omega

private theorem twice_ternaryCode_replicate_false (count : Nat) :
    2 * ternaryCode (List.replicate count false) = 3 ^ count - 1 := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ, ternaryCode_cons, List.length_replicate, pow_succ]
      simp only [ternaryDigit]
      omega

private theorem tagEncode_replicate_c (width count : Nat) :
    tagEncode width (List.replicate count .c) = List.replicate count true := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ, tagEncode_cons, induction]
      simp [tagCode, List.replicate_succ]

private theorem tagEncode_length_ge (width : Nat) (letters : List TagLetter) :
    letters.length ≤ (tagEncode width letters).length := by
  induction letters with
  | nil => rfl
  | cons letter letters induction =>
      rw [tagEncode_cons, List.length_append, List.length_cons]
      have code_nonempty : 0 < (tagCode width letter).length := by
        cases letter <;> simp [tagCode]
      omega

private def physicalUpperWord (width : Nat) (block : List NearyTile) : List Bool :=
  (spell (nearyUpper width) block ++ nearyMarker width).map not

private def physicalLowerWord (width : Nat) (body : List TagLetter)
    (block : List NearyTile) : List Bool :=
  (spell (nearyLower width body) block).map not

@[simp] private theorem physicalUpperWord_length (width : Nat) (block : List NearyTile) :
    (physicalUpperWord width block).length = upperLength width block + width + 1 := by
  simp [physicalUpperWord, upperLength, nearyMarker]
  omega

private theorem physicalUpperWord_cons (width : Nat) (tile : NearyTile)
    (rest : List NearyTile) :
    physicalUpperWord width (tile :: rest) =
      (tagCode width tile.letter).map not ++ physicalUpperWord width rest := by
  rw [physicalUpperWord, physicalUpperWord, spell_nearyUpper, spell_nearyUpper]
  simp only [List.map_cons, tagEncode_cons]
  rw [List.append_assoc, List.map_append]

private theorem physicalLowerWord_cons (width : Nat) (body : List TagLetter)
    (tile : NearyTile) (rest : List NearyTile) :
    physicalLowerWord width body (tile :: rest) =
      (nearyLower width body tile).map not ++ physicalLowerWord width body rest := by
  simp [physicalLowerWord, spell, List.map_append]

private theorem physicalUpperWord_b_prefix
    {width : Nat} (width_pos : 0 < width) {tile : NearyTile}
    (tile_b : tile.letter = .b) (rest : List NearyTile) :
    ∃ tail, physicalUpperWord width (tile :: rest) = false :: true :: tail := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt width_pos)
  refine ⟨List.replicate offset true ++ false :: physicalUpperWord offset.succ rest, ?_⟩
  rw [physicalUpperWord_cons, tile_b]
  simp [tagCode, List.replicate_succ]

private theorem physicalUpperWord_b_prefix_three
    {width : Nat} (width_two : 2 ≤ width) {tile : NearyTile}
    (tile_b : tile.letter = .b) (rest : List NearyTile) :
    ∃ tail,
      physicalUpperWord width (tile :: rest) = false :: true :: true :: tail := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le width_two
  refine ⟨List.replicate offset true ++ false :: physicalUpperWord (2 + offset) rest, ?_⟩
  rw [physicalUpperWord_cons, tile_b]
  simp [tagCode, List.replicate_add]

private theorem physicalLowerWord_erase_prefix
    (width : Nat) (body : List TagLetter) (letter : TagLetter)
    (rest : List NearyTile) :
    ∃ tail, physicalLowerWord width body (.erase letter :: rest) = true :: tail := by
  exact ⟨physicalLowerWord width body rest,
    by simp [physicalLowerWord_cons, nearyLower]⟩

private theorem physicalLowerWord_rule_b_prefix
    (width : Nat) (body : List TagLetter) (rest : List NearyTile) :
    ∃ tail,
      physicalLowerWord width body (.rule .b :: rest) =
        false :: false :: true :: tail := by
  exact ⟨physicalLowerWord width body rest,
    by simp [physicalLowerWord_cons, nearyLower]⟩

private theorem physicalLowerWord_nonempty
    (width : Nat) (body : List TagLetter) (tile : NearyTile)
    (rest : List NearyTile) :
    physicalLowerWord width body (tile :: rest) ≠ [] := by
  intro word_nil
  have mapped_nil :
      List.map not
          (nearyLower width body tile ++ spell (nearyLower width body) rest) = [] := by
    simpa [physicalLowerWord, spell] using word_nil
  have spelling_nil :
      nearyLower width body tile ++ spell (nearyLower width body) rest = [] :=
    List.map_eq_nil_iff.mp mapped_nil
  exact nearyLower_ne_nil width body tile (List.append_eq_nil_iff.mp spelling_nil).1

private theorem equalLength_erase_upper_lt_lower
    (upperTail lowerTail : List Bool)
    (length_eq : (false :: true :: upperTail).length = (true :: lowerTail).length) :
    ternaryCode (false :: true :: upperTail) < ternaryCode (true :: lowerTail) := by
  have tail_length : upperTail.length + 1 = lowerTail.length := by
    simp only [List.length_cons] at length_eq
    omega
  have upper_tail_bound := ternaryCode_lt_pow_length upperTail
  have lower_power_pos : 0 < 3 ^ lowerTail.length := pow_pos (by omega) _
  have upper_eq :
      ternaryCode (false :: true :: upperTail) =
        5 * 3 ^ upperTail.length + ternaryCode upperTail := by
    simp only [ternaryCode_cons, List.length_cons, ternaryDigit, pow_succ]
    ring
  have lower_eq :
      ternaryCode (true :: lowerTail) =
        2 * 3 ^ lowerTail.length + ternaryCode lowerTail := by
    rw [ternaryCode_cons]
    simp only [ternaryDigit]
    ring
  have power_eq : 3 ^ lowerTail.length = 3 * 3 ^ upperTail.length := by
    rw [← tail_length, pow_succ]
    ring
  rw [upper_eq, lower_eq, power_eq]
  omega

private theorem equalLength_ruleB_gap
    (upperTail lowerTail : List Bool)
    (length_eq :
      (false :: true :: true :: upperTail).length =
        (false :: false :: true :: lowerTail).length) :
    3 ^ ((false :: true :: true :: upperTail).length - 1) +
        6 * ternaryCode (false :: false :: true :: lowerTail) ≤
      6 * ternaryCode (false :: true :: true :: upperTail) := by
  have tail_length : upperTail.length = lowerTail.length := by
    simp only [List.length_cons] at length_eq
    omega
  have upper_tail_lower : 0 ≤ ternaryCode upperTail := Nat.zero_le _
  have lower_tail_bound := ternaryCode_lt_pow_length lowerTail
  have power_pos : 0 < 3 ^ lowerTail.length := pow_pos (by omega) _
  have upper_eq :
      ternaryCode (false :: true :: true :: upperTail) =
        17 * 3 ^ upperTail.length + ternaryCode upperTail := by
    simp only [ternaryCode_cons, List.length_cons, ternaryDigit, pow_succ]
    ring
  have lower_eq :
      ternaryCode (false :: false :: true :: lowerTail) =
        14 * 3 ^ lowerTail.length + ternaryCode lowerTail := by
    simp only [ternaryCode_cons, List.length_cons, ternaryDigit, pow_succ]
    ring
  have head_power :
      3 ^ ((false :: true :: true :: upperTail).length - 1) =
        9 * 3 ^ lowerTail.length := by
    simp only [List.length_cons]
    rw [tail_length]
    simp only [Nat.add_sub_cancel, pow_succ]
    ring
  rw [upper_eq, lower_eq, head_power, tail_length]
  omega

private theorem physicalUpper_predecessorPower
    (width : Nat) (block : List NearyTile) :
    (3 : ℤ) ^ ((physicalUpperWord width block).length - 1) =
      widthScale width * upperPower width block := by
  rw [physicalUpperWord_length]
  have exponent_eq : upperLength width block + width + 1 - 1 =
      width + upperLength width block := by omega
  rw [exponent_eq, pow_add]
  simp only [widthScale, upperPower]

private theorem bLeading_code_lower
    {width : Nat} (width_pos : 0 < width) {tile : NearyTile}
    (tile_b : tile.letter = .b) (rest : List NearyTile) :
    5 * widthScale width * upperPower width (tile :: rest) ≤
      3 * swappedUpperCode width (tile :: rest) := by
  obtain ⟨tail, upper_eq⟩ :=
    physicalUpperWord_b_prefix width_pos tile_b rest
  have tail_code_nonneg : 0 ≤ ternaryCode tail := Nat.zero_le _
  have upper_formula :
      ternaryCode (false :: true :: tail) =
        5 * 3 ^ tail.length + ternaryCode tail := by
    simp only [ternaryCode_cons, List.length_cons, ternaryDigit, pow_succ]
    ring
  have power_eq :
      3 ^ ((physicalUpperWord width (tile :: rest)).length - 1) =
        3 * 3 ^ tail.length := by
    rw [upper_eq]
    simp only [List.length_cons, Nat.add_sub_cancel, pow_succ]
    ring
  have natural_bound :
      5 * 3 ^ ((physicalUpperWord width (tile :: rest)).length - 1) ≤
        3 * ternaryCode (physicalUpperWord width (tile :: rest)) := by
    rw [power_eq, upper_eq, upper_formula]
    omega
  have integer_bound :
      5 * (3 : ℤ) ^ ((physicalUpperWord width (tile :: rest)).length - 1) ≤
        3 * (ternaryCode (physicalUpperWord width (tile :: rest)) : ℤ) := by
    exact_mod_cast natural_bound
  rw [physicalUpper_predecessorPower] at integer_bound
  simpa only [swappedUpperCode, physicalUpperWord, mul_assoc] using integer_bound

private theorem lowerCode_pos
    (width : Nat) (body : List TagLetter) (tile : NearyTile)
    (rest : List NearyTile) :
    (0 : ℤ) < swappedLowerCode width body (tile :: rest) := by
  have word_nonempty := physicalLowerWord_nonempty width body tile rest
  have code_bound := ternaryCode_lower_bound
    (physicalLowerWord width body (tile :: rest)) word_nonempty
  have code_pos : 0 < ternaryCode (physicalLowerWord width body (tile :: rest)) :=
    lt_of_lt_of_le
      (pow_pos (by norm_num)
        ((physicalLowerWord width body (tile :: rest)).length - 1))
      code_bound
  simpa only [swappedLowerCode, physicalLowerWord] using (show
    (0 : ℤ) < (ternaryCode (physicalLowerWord width body (tile :: rest)) : ℤ) by
      exact_mod_cast code_pos)

/-- Exact punctuated upper code of the exceptional `R_c;D_b` block. -/
theorem canonicalRcDb_upperCode (width : Nat) :
    swappedUpperCode width [.rule .c, .erase .b] =
      45 * widthScale width ^ 2 - 4 * widthScale width - 1 := by
  simp [swappedUpperCode, spell, nearyUpper, tagCode, nearyMarker,
    ternaryCode_append, ternaryCode_cons, ternaryDigit, widthScale,
    List.map_append]
  rw [ternaryCode_replicate_true]
  have one_le : 1 ≤ 3 ^ width := by
    have power_pos : 0 < 3 ^ width := pow_pos (by norm_num) width
    omega
  rw [Nat.cast_sub one_le]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  ring

/-- Exact lower code of `R_c;D_b` against its canonical equal-length body. -/
theorem canonicalRcDb_lowerCode
    {width : Nat} (width_two : 2 ≤ width) :
    2 * swappedLowerCode width (canonicalRcDbBody width)
        [.rule .c, .erase .b] =
      90 * widthScale width ^ 2 - 9 * widthScale width + 7 := by
  simp [swappedLowerCode, spell, nearyLower, canonicalRcDbBody,
    tagEncode_cons, tagCode, tagEncode_replicate_c, ternaryCode_append,
    ternaryCode_cons, ternaryDigit, List.map_append, widthScale]
  rw [ternaryCode_replicate_true]
  have one_le : 1 ≤ 3 ^ width := by
    have power_pos : 0 < 3 ^ width := pow_pos (by norm_num) width
    omega
  rw [Nat.cast_sub one_le]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  have exponent₁ : width + (width - 2 + 3 + 1) + 1 = 2 * width + 3 := by omega
  have exponent₂ : width + (width - 2 + 3 + 1) = 2 * width + 2 := by omega
  have exponent₃ : width - 2 + 3 + 1 = width + 2 := by omega
  have exponent₄ : width - 2 + 3 = width + 1 := by omega
  rw [exponent₁, exponent₂, exponent₃, exponent₄]
  have false_code := twice_ternaryCode_replicate_false (width - 2)
  have exponent₅ : width - 2 + 2 = width := by omega
  have power_factor_nat : 9 * 3 ^ (width - 2) = 3 ^ width := by
    calc
      9 * 3 ^ (width - 2) = 3 ^ (width - 2) * 3 ^ 2 := by norm_num; ring
      _ = 3 ^ (width - 2 + 2) := by rw [← pow_add]
      _ = 3 ^ width := by rw [exponent₅]
  have square_power : (3 : ℤ) ^ (width * 2) = ((3 : ℤ) ^ width) ^ 2 := by
    rw [pow_mul]
  have power₁ :
      (3 : ℤ) ^ (2 * width + 3) = 27 * ((3 : ℤ) ^ width) ^ 2 := by
    rw [show 2 * width = width * 2 by omega, pow_add, square_power]
    norm_num
    ring
  have power₂ :
      (3 : ℤ) ^ (2 * width + 2) = 9 * ((3 : ℤ) ^ width) ^ 2 := by
    rw [show 2 * width = width * 2 by omega, pow_add, square_power]
    norm_num
    ring
  have power₃ : (3 : ℤ) ^ (width + 2) = 9 * 3 ^ width := by
    rw [pow_add]
    norm_num
    ring
  have power₄ : (3 : ℤ) ^ (width + 1) = 3 * 3 ^ width := by
    rw [pow_succ]
    ring
  rw [power₁, power₂, power₃, power₄]
  have small_one_le : 1 ≤ 3 ^ (width - 2) := by
    have power_pos : 0 < 3 ^ (width - 2) := pow_pos (by norm_num) _
    omega
  have false_code_cast := congrArg (fun value : Nat => (value : ℤ)) false_code
  have false_code_int :
      2 * (ternaryCode (List.replicate (width - 2) false) : ℤ) =
        (3 : ℤ) ^ (width - 2) - 1 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub small_one_le,
      Nat.cast_pow, Nat.cast_one] using false_code_cast
  have power_factor : (9 : ℤ) * 3 ^ (width - 2) = 3 ^ width := by
    exact_mod_cast power_factor_nat
  linear_combination
    27 * false_code_int + 3 * power_factor + 72 * square_power

@[simp] theorem canonicalRcDb_upperPower (width : Nat) :
    upperPower width [.rule .c, .erase .b] = 27 * widthScale width := by
  simp [upperPower, upperLength, spell, nearyUpper, tagCode, widthScale,
    pow_succ]
  ring

/-- Every length-`offset+1` empty target supplies the polynomial lower bound used by the
entry-ray chamber. -/
theorem emptyTarget_upperPrefix_lower
    {offset : Nat} {letters : List TagLetter}
    (letters_length : letters.length = offset + 1) :
    (3 : ℤ) ^ (offset + 2) ≤
      2 * signedSwappedCode (tagEncode (offset + 1) letters ++ [true]) + 1 := by
  let word := (tagEncode (offset + 1) letters ++ [true]).map not
  have length_bound : offset + 2 ≤ word.length := by
    simp only [word, List.length_map, List.length_append, List.length_singleton]
    have encoded_bound := tagEncode_length_ge (offset + 1) letters
    omega
  have power_bound : 3 ^ (offset + 2) ≤ 3 ^ word.length :=
    Nat.pow_le_pow_right (by norm_num) length_bound
  have code_bound := ternaryCode_scale_le_twice_add_one word
  have natural_bound : 3 ^ (offset + 2) ≤ 2 * ternaryCode word + 1 :=
    power_bound.trans code_bound
  change
    (3 : ℤ) ^ (offset + 2) ≤
      2 * (ternaryCode ((tagEncode (offset + 1) letters ++ [true]).map not) : ℤ) + 1
  exact_mod_cast natural_bound

private def seedDenominatorCore (scale upperPrefix : ℤ) : ℤ :=
  (135 * scale ^ 5 - 207 * scale ^ 4 + 168 * scale ^ 3 -
      72 * scale ^ 2 + 8 * scale) * upperPrefix -
    108 * scale ^ 4 + 558 * scale ^ 3 - 330 * scale ^ 2 +
      64 * scale - 4

private def seedHeadGapCore (scale upperPrefix : ℤ) : ℤ :=
  (21870 * scale ^ 7 - 53784 * scale ^ 6 + 49167 * scale ^ 5 -
      21357 * scale ^ 4 + 4596 * scale ^ 3 - 408 * scale ^ 2 +
      8 * scale) * upperPrefix -
    17496 * scale ^ 6 + 36612 * scale ^ 5 - 34236 * scale ^ 4 +
      14094 * scale ^ 3 - 2586 * scale ^ 2 + 196 * scale - 4

private theorem seedDenominatorCore_pos
    {scale upperPrefix : ℤ} (scale_three : 3 ≤ scale)
    (prefix_lower : 9 * scale ≤ 2 * upperPrefix + 1) :
    0 < seedDenominatorCore scale upperPrefix := by
  let shifted := scale - 3
  let coefficient :=
    135 * scale ^ 5 - 207 * scale ^ 4 + 168 * scale ^ 3 -
      72 * scale ^ 2 + 8 * scale
  let minimum :=
    1215 * shifted ^ 6 + 19872 * shifted ^ 5 + 135558 * shifted ^ 4 +
      494616 * shifted ^ 3 + 1020111 * shifted ^ 2 +
      1129728 * shifted + 525772
  have shifted_nonneg : 0 ≤ shifted := by
    simp only [shifted]
    omega
  have coefficient_pos : 0 < coefficient := by
    have expansion : coefficient =
        135 * shifted ^ 5 + 1818 * shifted ^ 4 + 9834 * shifted ^ 3 +
          26712 * shifted ^ 2 + 36431 * shifted + 19950 := by
      simp only [coefficient, shifted]
      ring
    rw [expansion]
    positivity
  have minimum_pos : 0 < minimum := by
    simp only [minimum]
    positivity
  have gap_nonneg : 0 ≤ 2 * upperPrefix - 9 * scale + 1 := by
    omega
  have decomposition :
      2 * seedDenominatorCore scale upperPrefix =
        coefficient * (2 * upperPrefix - 9 * scale + 1) + minimum := by
    simp only [seedDenominatorCore, coefficient, minimum, shifted]
    ring
  have product_nonneg :
      0 ≤ coefficient * (2 * upperPrefix - 9 * scale + 1) :=
    mul_nonneg coefficient_pos.le gap_nonneg
  nlinarith

private theorem seedHeadGapCore_pos
    {scale upperPrefix : ℤ} (scale_three : 3 ≤ scale)
    (prefix_lower : 9 * scale ≤ 2 * upperPrefix + 1) :
    0 < seedHeadGapCore scale upperPrefix := by
  let shifted := scale - 3
  let coefficient :=
    21870 * scale ^ 7 - 53784 * scale ^ 6 + 49167 * scale ^ 5 -
      21357 * scale ^ 4 + 4596 * scale ^ 3 - 408 * scale ^ 2 +
      8 * scale
  let minimum :=
    196830 * shifted ^ 8 + 4217994 * shifted ^ 7 +
      39438009 * shifted ^ 6 + 210122100 * shifted ^ 5 +
      697672764 * shifted ^ 4 + 1478078598 * shifted ^ 3 +
      1950888921 * shifted ^ 2 + 1466351196 * shifted + 480394540
  have shifted_nonneg : 0 ≤ shifted := by
    simp only [shifted]
    omega
  have coefficient_pos : 0 < coefficient := by
    have expansion : coefficient =
        21870 * shifted ^ 7 + 405486 * shifted ^ 6 +
          3214485 * shifted ^ 5 + 14122458 * shifted ^ 4 +
          37131432 * shifted ^ 3 + 58417818 * shifted ^ 2 +
          50913269 * shifted + 18959262 := by
      simp only [coefficient, shifted]
      ring
    rw [expansion]
    positivity
  have minimum_pos : 0 < minimum := by
    simp only [minimum]
    positivity
  have gap_nonneg : 0 ≤ 2 * upperPrefix - 9 * scale + 1 := by
    omega
  have decomposition :
      2 * seedHeadGapCore scale upperPrefix =
        coefficient * (2 * upperPrefix - 9 * scale + 1) + minimum := by
    simp only [seedHeadGapCore, coefficient, minimum, shifted]
    ring
  have product_nonneg :
      0 ≤ coefficient * (2 * upperPrefix - 9 * scale + 1) :=
    mul_nonneg coefficient_pos.le gap_nonneg
  nlinarith

/-- Every local empty-front `D_b` antecedent lies above the fixed terminal discrepancy. -/
theorem emptyFrontSeed_above_terminal
    {offset : Nat} (offset_pos : 0 < offset) {upperPrefix : ℤ}
    (prefix_lower :
      (3 : ℤ) ^ (offset + 2) ≤ 2 * upperPrefix + 1) :
    (terminalDiscrepancy (offset + 1) : ℚ) <
      emptyFrontSeed offset upperPrefix := by
  let scale : ℤ := 3 ^ offset
  have scale_three : 3 ≤ scale := by
    obtain ⟨predecessor, rfl⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt offset_pos)
    simp only [scale, pow_succ]
    have power_pos : (0 : ℤ) < 3 ^ predecessor := by positivity
    nlinarith
  have prefix_lower' : 9 * scale ≤ 2 * upperPrefix + 1 := by
    simpa [scale, pow_add, mul_comm, mul_left_comm, mul_assoc] using prefix_lower
  have denominator_core_pos :=
    seedDenominatorCore_pos scale_three prefix_lower'
  have head_gap_core_pos := seedHeadGapCore_pos scale_three prefix_lower'
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
          seedDenominatorCore scale upperPrefix := by
    simp only [deletionBInverseDenominator, setterMarker,
      secondDeletionInverseNumerator, firstDeletionInverseNumerator,
      firstDeletionInverseDenominator, firstDeletionResidual,
      secondDeletionGapCore, terminalDiscrepancy, centeredCoefficient,
      width_scale_eq]
    simp only [seedDenominatorCore]
    ring
  have head_gap_eq :
      deletionBInverseNumerator offset upperPrefix -
          terminalDiscrepancy (offset + 1) *
            deletionBInverseDenominator offset upperPrefix =
        -terminalDiscrepancy (offset + 1) *
          seedHeadGapCore scale upperPrefix := by
    simp only [deletionBInverseNumerator, deletionBCofactor,
      deletionBInverseDenominator, setterMarker,
      secondDeletionInverseNumerator, firstDeletionInverseNumerator,
      firstDeletionInverseDenominator, firstDeletionResidual,
      secondDeletionGapCore, terminalDiscrepancy, centeredCoefficient,
      width_scale_eq]
    simp only [seedHeadGapCore]
    ring
  have denominator_neg :
      deletionBInverseDenominator offset upperPrefix < 0 := by
    rw [denominator_eq]
    nlinarith
  have head_gap_neg :
      deletionBInverseNumerator offset upperPrefix -
          terminalDiscrepancy (offset + 1) *
            deletionBInverseDenominator offset upperPrefix < 0 := by
    rw [head_gap_eq]
    nlinarith
  have denominator_neg_rat :
      (deletionBInverseDenominator offset upperPrefix : ℚ) < 0 := by
    exact_mod_cast denominator_neg
  unfold emptyFrontSeed
  apply (lt_div_iff_of_neg denominator_neg_rat).2
  exact_mod_cast (by nlinarith [head_gap_neg] :
    deletionBInverseNumerator offset upperPrefix <
      terminalDiscrepancy (offset + 1) *
        deletionBInverseDenominator offset upperPrefix)

/-- Every physical empty target supplies a seed above the terminal discrepancy. -/
theorem physicalEmptyFrontSeed_above_terminal
    {offset : Nat} (offset_pos : 0 < offset) {letters : List TagLetter}
    (letters_length : letters.length = offset + 1) :
    (terminalDiscrepancy (offset + 1) : ℚ) <
      emptyFrontSeed offset
        (signedSwappedCode (tagEncode (offset + 1) letters ++ [true])) :=
  emptyFrontSeed_above_terminal offset_pos
    (emptyTarget_upperPrefix_lower letters_length)

theorem centeredCoefficient_eq_neg_chamberRadius (width : Nat) :
    centeredCoefficient width = -chamberRadius width := by
  simp [centeredCoefficient, chamberRadius]

private theorem widthScale_large
    {width : Nat} (width_large : 6 ≤ width) :
    (729 : ℚ) ≤ widthScale width := by
  have power_bound : 3 ^ 6 ≤ 3 ^ width :=
    Nat.pow_le_pow_right (by norm_num) width_large
  norm_num [widthScale] at power_bound ⊢
  exact_mod_cast power_bound

private theorem terminalRay_denominator_pos
    {width : Nat} (width_large : 6 ≤ width) {current : ℚ}
    (current_above : (terminalDiscrepancy width : ℚ) < current) :
    (0 : ℚ) < terminalDiscrepancy width + chamberRadius width * current := by
  have scale_large := widthScale_large width_large
  have head_pos : (0 : ℚ) < terminalDiscrepancy width := by
    simp only [terminalDiscrepancy]
    push_cast
    linarith
  have radius_pos : (0 : ℚ) < chamberRadius width := by
    simp only [chamberRadius]
    push_cast
    linarith
  have current_pos : (0 : ℚ) < current := head_pos.trans current_above
  positivity

/-- Above the terminal ray, the normalized code correction lies strictly between zero and
three. -/
theorem blockCorrection_pos_lt_three
    {width : Nat} (width_large : 6 ≤ width) {current : ℚ}
    (current_above : (terminalDiscrepancy width : ℚ) < current) :
    0 < blockCorrection width current ∧ blockCorrection width current < 3 := by
  have scale_large := widthScale_large width_large
  have scale_pos : (0 : ℚ) < widthScale width := lt_of_lt_of_le (by norm_num) scale_large
  have radius_pos : (0 : ℚ) < chamberRadius width := by
    simp only [chamberRadius]
    push_cast
    linarith
  have head_pos : (0 : ℚ) < terminalDiscrepancy width := by
    simp only [terminalDiscrepancy]
    push_cast
    linarith
  have marker_pos : (0 : ℚ) < setterMarker width := by
    simp only [setterMarker]
    push_cast
    linarith
  have denominator_pos := terminalRay_denominator_pos width_large current_above
  constructor
  · exact div_pos (mul_pos head_pos marker_pos) denominator_pos
  · rw [blockCorrection, div_lt_iff₀ denominator_pos]
    simp only [terminalDiscrepancy, setterMarker, chamberRadius] at current_above ⊢
    push_cast at current_above ⊢
    nlinarith

/-- Pulling a block backward above the terminal ray subtracts its positive code correction. -/
theorem backwardBlock_eq_sub_correction
    {width : Nat} {punctuated lower upperPower current : ℚ}
    (lower_ne : lower ≠ 0)
    (denominator_ne :
      terminalDiscrepancy width + chamberRadius width * current ≠ 0) :
    backwardBlock width punctuated lower upperPower current =
      (punctuated - blockCorrection width current * upperPower) / lower := by
  rw [backwardBlock, blockCorrection, centeredCoefficient_eq_neg_chamberRadius]
  simp only [Int.cast_neg]
  have centered_denominator_eq :
      -(chamberRadius width : ℚ) * current - terminalDiscrepancy width =
        -(terminalDiscrepancy width + chamberRadius width * current) := by
    ring
  rw [centered_denominator_eq]
  have neg_denominator_ne :
      -(terminalDiscrepancy width + chamberRadius width * current) ≠ 0 :=
    neg_ne_zero.mpr denominator_ne
  field_simp [lower_ne, denominator_ne, neg_denominator_ne]
  ring

/-- A short lower spelling and a `b`-prefix code force the backward image above the
`D_c`-contraction chamber. -/
theorem bPrefix_short_backwardBlock_above_chamber
    {width : Nat} (width_large : 6 ≤ width)
    {punctuated lower upperPower current : ℚ}
    (current_above : (terminalDiscrepancy width : ℚ) < current)
    (lower_pos : 0 < lower) (upperPower_pos : 0 < upperPower)
    (lower_short : lower < widthScale width * upperPower)
    (b_prefix : 5 * widthScale width * upperPower ≤ 3 * punctuated) :
    (chamberRadius width : ℚ) / (chamberRadius width - 3) <
      backwardBlock width punctuated lower upperPower current := by
  obtain ⟨correction_pos, correction_lt⟩ :=
    blockCorrection_pos_lt_three width_large current_above
  have scale_large := widthScale_large width_large
  have scale_pos : (0 : ℚ) < widthScale width := lt_of_lt_of_le (by norm_num) scale_large
  have radius_pos : (0 : ℚ) < chamberRadius width := by
    simp only [chamberRadius]
    push_cast
    linarith
  have radius_sub_pos : (0 : ℚ) < chamberRadius width - 3 := by
    simp only [chamberRadius]
    push_cast
    linarith
  have denominator_ne := (terminalRay_denominator_pos width_large current_above).ne'
  rw [backwardBlock_eq_sub_correction lower_pos.ne' denominator_ne]
  have numerator_lower :
      (5 * widthScale width / 3 - 3) * upperPower <
        punctuated - blockCorrection width current * upperPower := by
    nlinarith
  have scaled_numerator_lower :
      ((chamberRadius width : ℚ) / (chamberRadius width - 3)) * lower <
        punctuated - blockCorrection width current * upperPower := by
    have chamber_bound :
        (chamberRadius width : ℚ) / (chamberRadius width - 3) *
            widthScale width <
          5 * widthScale width / 3 - 3 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ radius_sub_pos]
      simp only [chamberRadius]
      push_cast
      nlinarith
    have chamber_pos :
        (0 : ℚ) < (chamberRadius width : ℚ) / (chamberRadius width - 3) :=
      div_pos radius_pos radius_sub_pos
    nlinarith [mul_lt_mul_of_pos_left lower_short chamber_pos,
      mul_lt_mul_of_pos_right chamber_bound upperPower_pos]
  exact (lt_div_iff₀ lower_pos).2 scaled_numerator_lower

/-- A lower spelling at least one ternary place longer than the upper spelling forces the
backward image below one. -/
theorem longLower_backwardBlock_below_one
    {width : Nat} (width_large : 6 ≤ width)
    {punctuated lower upperPower current : ℚ}
    (current_above : (terminalDiscrepancy width : ℚ) < current)
    (lower_pos : 0 < lower) (upperPower_pos : 0 < upperPower)
    (lower_long : 3 * widthScale width * upperPower ≤ lower)
    (upper_bound : punctuated < 2 * widthScale width * upperPower) :
    backwardBlock width punctuated lower upperPower current < 1 := by
  obtain ⟨correction_pos, _⟩ :=
    blockCorrection_pos_lt_three width_large current_above
  have denominator_ne := (terminalRay_denominator_pos width_large current_above).ne'
  rw [backwardBlock_eq_sub_correction lower_pos.ne' denominator_ne]
  apply (div_lt_iff₀ lower_pos).2
  nlinarith [mul_pos correction_pos upperPower_pos]

/-- An equal-length erasure prefix forces the backward image below one. -/
theorem erasePrefix_backwardBlock_below_one
    {width : Nat} (width_large : 6 ≤ width)
    {punctuated lower upperPower current : ℚ}
    (current_above : (terminalDiscrepancy width : ℚ) < current)
    (lower_pos : 0 < lower) (upperPower_pos : 0 < upperPower)
    (erase_prefix : punctuated ≤ lower) :
    backwardBlock width punctuated lower upperPower current < 1 := by
  obtain ⟨correction_pos, _⟩ :=
    blockCorrection_pos_lt_three width_large current_above
  have denominator_ne := (terminalRay_denominator_pos width_large current_above).ne'
  rw [backwardBlock_eq_sub_correction lower_pos.ne' denominator_ne]
  apply (div_lt_iff₀ lower_pos).2
  nlinarith [mul_pos correction_pos upperPower_pos]

/-- An equal-length `R_b` prefix forces the backward image above the
`D_c`-contraction chamber. -/
theorem ruleBPrefix_backwardBlock_above_chamber
    {width : Nat} (width_large : 6 ≤ width)
    {punctuated lower upperPower current : ℚ}
    (current_above : (terminalDiscrepancy width : ℚ) < current)
    (lower_pos : 0 < lower) (upperPower_pos : 0 < upperPower)
    (equal_length_upper : lower < 3 * widthScale width * upperPower)
    (rule_b_gap : widthScale width * upperPower ≤ 6 * (punctuated - lower)) :
    (chamberRadius width : ℚ) / (chamberRadius width - 3) <
      backwardBlock width punctuated lower upperPower current := by
  obtain ⟨_, correction_lt⟩ :=
    blockCorrection_pos_lt_three width_large current_above
  have scale_large := widthScale_large width_large
  have scale_pos : (0 : ℚ) < widthScale width := lt_of_lt_of_le (by norm_num) scale_large
  have radius_pos : (0 : ℚ) < chamberRadius width := by
    simp only [chamberRadius]
    push_cast
    linarith
  have radius_sub_pos : (0 : ℚ) < chamberRadius width - 3 := by
    simp only [chamberRadius]
    push_cast
    linarith
  have denominator_ne := (terminalRay_denominator_pos width_large current_above).ne'
  rw [backwardBlock_eq_sub_correction lower_pos.ne' denominator_ne]
  have gap_lower :
      (widthScale width / 6 - 3) * upperPower <
        punctuated - blockCorrection width current * upperPower - lower := by
    nlinarith
  have chamber_gap_bound :
      3 / ((chamberRadius width : ℚ) - 3) *
          (3 * widthScale width * upperPower) <
        (widthScale width / 6 - 3) * upperPower := by
    have coefficient_bound :
        9 * widthScale width / ((chamberRadius width : ℚ) - 3) <
          widthScale width / 6 - 3 := by
      rw [div_lt_iff₀ radius_sub_pos]
      simp only [chamberRadius]
      push_cast
      nlinarith
    calc
      3 / ((chamberRadius width : ℚ) - 3) *
          (3 * widthScale width * upperPower) =
          (9 * widthScale width / ((chamberRadius width : ℚ) - 3)) *
            upperPower := by ring
      _ < (widthScale width / 6 - 3) * upperPower :=
        mul_lt_mul_of_pos_right coefficient_bound upperPower_pos
  have chamber_gap :
      3 / ((chamberRadius width : ℚ) - 3) * lower <
        punctuated - blockCorrection width current * upperPower - lower := by
    have coefficient_pos :
        (0 : ℚ) < 3 / ((chamberRadius width : ℚ) - 3) :=
      div_pos (by norm_num) radius_sub_pos
    nlinarith [mul_lt_mul_of_pos_left equal_length_upper coefficient_pos,
      chamber_gap_bound]
  apply (lt_div_iff₀ lower_pos).2
  have chamber_identity :
      (chamberRadius width : ℚ) / (chamberRadius width - 3) =
        1 + 3 / (chamberRadius width - 3) := by
    field_simp [radius_sub_pos.ne']
    ring
  rw [chamber_identity]
  nlinarith

/-- No physical block whose first role has letter `b` can pull an empty-front seed into the
`D_c`-contraction chamber. Thus every chamber-entering block is `c`-leading. -/
theorem bLeading_physicalBackwardBlock_avoids_deletionCChamber
    {width : Nat} (width_large : 6 ≤ width) (body : List TagLetter)
    {tile : NearyTile} (tile_b : tile.letter = .b) (rest : List NearyTile)
    {current : ℚ} (current_above : (terminalDiscrepancy width : ℚ) < current) :
    ¬(1 < backwardBlock width
          (swappedUpperCode width (tile :: rest))
          (swappedLowerCode width body (tile :: rest))
          (upperPower width (tile :: rest)) current ∧
      backwardBlock width
          (swappedUpperCode width (tile :: rest))
          (swappedLowerCode width body (tile :: rest))
          (upperPower width (tile :: rest)) current <
        (chamberRadius width : ℚ) / (chamberRadius width - 3)) := by
  intro chamber
  let upper := physicalUpperWord width (tile :: rest)
  let lower := physicalLowerWord width body (tile :: rest)
  have width_pos : 0 < width := by omega
  have width_two : 2 ≤ width := by omega
  have lower_nonempty : lower ≠ [] :=
    physicalLowerWord_nonempty width body tile rest
  have lower_pos :
      (0 : ℚ) < swappedLowerCode width body (tile :: rest) := by
    exact_mod_cast lowerCode_pos width body tile rest
  have upperPower_pos : (0 : ℚ) < upperPower width (tile :: rest) := by
    simp [upperPower]
  by_cases lower_shorter : lower.length < upper.length
  · have exponent_le : lower.length ≤ upper.length - 1 := by omega
    have power_le : 3 ^ lower.length ≤ 3 ^ (upper.length - 1) :=
      Nat.pow_le_pow_right (by norm_num) exponent_le
    have lower_code_lt : ternaryCode lower < 3 ^ (upper.length - 1) :=
      (ternaryCode_lt_pow_length lower).trans_le power_le
    have lower_short_int :
        swappedLowerCode width body (tile :: rest) <
          widthScale width * upperPower width (tile :: rest) := by
      have cast_bound :
          (ternaryCode lower : ℤ) < (3 : ℤ) ^ (upper.length - 1) := by
        exact_mod_cast lower_code_lt
      rw [show upper = physicalUpperWord width (tile :: rest) by rfl,
        physicalUpper_predecessorPower] at cast_bound
      simpa only [swappedLowerCode, lower, physicalLowerWord] using cast_bound
    have lower_short :
        (swappedLowerCode width body (tile :: rest) : ℚ) <
          widthScale width * upperPower width (tile :: rest) := by
      exact_mod_cast lower_short_int
    have b_prefix_int := bLeading_code_lower width_pos tile_b rest
    have b_prefix :
        5 * (widthScale width : ℚ) * upperPower width (tile :: rest) ≤
          3 * swappedUpperCode width (tile :: rest) := by
      exact_mod_cast b_prefix_int
    have above := bPrefix_short_backwardBlock_above_chamber width_large
      current_above lower_pos upperPower_pos lower_short b_prefix
    linarith
  · by_cases lower_longer : upper.length < lower.length
    · have exponent_le : upper.length ≤ lower.length - 1 := by omega
      have power_le : 3 ^ upper.length ≤ 3 ^ (lower.length - 1) :=
        Nat.pow_le_pow_right (by norm_num) exponent_le
      have lower_code_ge : 3 ^ upper.length ≤ ternaryCode lower :=
        power_le.trans (ternaryCode_lower_bound lower lower_nonempty)
      have lower_long_int :
          3 * widthScale width * upperPower width (tile :: rest) ≤
            swappedLowerCode width body (tile :: rest) := by
        have cast_bound :
            (3 : ℤ) ^ upper.length ≤ (ternaryCode lower : ℤ) := by
          exact_mod_cast lower_code_ge
        have power_eq :
            (3 : ℤ) ^ upper.length =
              3 * widthScale width * upperPower width (tile :: rest) := by
          calc
            (3 : ℤ) ^ upper.length =
                3 * 3 ^ (upper.length - 1) := by
                  have upper_nonempty : 0 < upper.length := by
                    simp [upper, physicalUpperWord_length]
                  obtain ⟨predecessor, upper_length⟩ :=
                    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt upper_nonempty)
                  rw [upper_length, Nat.succ_sub_one, pow_succ]
                  ring
            _ = 3 * widthScale width * upperPower width (tile :: rest) := by
              rw [show upper = physicalUpperWord width (tile :: rest) by rfl,
                physicalUpper_predecessorPower]
              ring
        rw [power_eq] at cast_bound
        simpa only [swappedLowerCode, lower, physicalLowerWord] using cast_bound
      have lower_long :
          3 * (widthScale width : ℚ) * upperPower width (tile :: rest) ≤
            swappedLowerCode width body (tile :: rest) := by
        exact_mod_cast lower_long_int
      have upper_bound_int :=
        (swappedUpperCode_cylinder width_pos (tile :: rest)).2
      have upper_bound :
          (swappedUpperCode width (tile :: rest) : ℚ) <
            2 * widthScale width * upperPower width (tile :: rest) := by
        exact_mod_cast upper_bound_int
      have below := longLower_backwardBlock_below_one width_large current_above
        lower_pos upperPower_pos lower_long upper_bound
      linarith
    · have length_eq : lower.length = upper.length := by omega
      cases tile with
      | erase letter =>
          obtain ⟨upperTail, upper_eq⟩ :=
            physicalUpperWord_b_prefix width_pos tile_b rest
          obtain ⟨lowerTail, lower_eq⟩ :=
            physicalLowerWord_erase_prefix width body letter rest
          have prefix_length_eq :
              (false :: true :: upperTail).length = (true :: lowerTail).length := by
            rw [← upper_eq, ← lower_eq]
            exact length_eq.symm
          have code_lt :=
            equalLength_erase_upper_lt_lower upperTail lowerTail prefix_length_eq
          have erase_prefix_int :
              swappedUpperCode width (.erase letter :: rest) ≤
                swappedLowerCode width body (.erase letter :: rest) := by
            have cast_lt :
                (ternaryCode (false :: true :: upperTail) : ℤ) <
                  ternaryCode (true :: lowerTail) := by
              exact_mod_cast code_lt
            rw [← upper_eq, ← lower_eq] at cast_lt
            simpa only [swappedUpperCode, swappedLowerCode,
              physicalUpperWord, physicalLowerWord] using cast_lt.le
          have erase_prefix :
              (swappedUpperCode width (.erase letter :: rest) : ℚ) ≤
                swappedLowerCode width body (.erase letter :: rest) := by
            exact_mod_cast erase_prefix_int
          have below := erasePrefix_backwardBlock_below_one width_large current_above
            lower_pos upperPower_pos erase_prefix
          linarith
      | rule letter =>
          cases letter with
          | c => simp [NearyTile.letter] at tile_b
          | b =>
              obtain ⟨upperTail, upper_eq⟩ :=
                physicalUpperWord_b_prefix_three width_two tile_b rest
              obtain ⟨lowerTail, lower_eq⟩ :=
                physicalLowerWord_rule_b_prefix width body rest
              have prefix_length_eq :
                  (false :: true :: true :: upperTail).length =
                    (false :: false :: true :: lowerTail).length := by
                rw [← upper_eq, ← lower_eq]
                exact length_eq.symm
              have code_gap :=
                equalLength_ruleB_gap upperTail lowerTail prefix_length_eq
              have rule_b_gap_int :
                  widthScale width * upperPower width (.rule .b :: rest) ≤
                    6 * (swappedUpperCode width (.rule .b :: rest) -
                      swappedLowerCode width body (.rule .b :: rest)) := by
                have cast_gap :
                    (3 : ℤ) ^
                          ((false :: true :: true :: upperTail).length - 1) +
                        6 * (ternaryCode
                          (false :: false :: true :: lowerTail) : ℤ) ≤
                      6 * (ternaryCode
                        (false :: true :: true :: upperTail) : ℤ) := by
                  exact_mod_cast code_gap
                rw [← upper_eq, ← lower_eq,
                  physicalUpper_predecessorPower] at cast_gap
                simp only [swappedUpperCode, swappedLowerCode,
                  physicalUpperWord, physicalLowerWord] at cast_gap ⊢
                linarith
              have rule_b_gap :
                  (widthScale width : ℚ) * upperPower width (.rule .b :: rest) ≤
                    6 * (swappedUpperCode width (.rule .b :: rest) -
                      swappedLowerCode width body (.rule .b :: rest)) := by
                exact_mod_cast rule_b_gap_int
              have lower_code_lt := ternaryCode_lt_pow_length lower
              have equal_length_upper_int :
                  swappedLowerCode width body (.rule .b :: rest) <
                    3 * widthScale width * upperPower width (.rule .b :: rest) := by
                have cast_lt :
                    (ternaryCode lower : ℤ) < (3 : ℤ) ^ upper.length := by
                  have cast_raw :
                      (ternaryCode lower : ℤ) < (3 : ℤ) ^ lower.length := by
                    exact_mod_cast lower_code_lt
                  simpa only [length_eq] using cast_raw
                have power_eq :
                    (3 : ℤ) ^ upper.length =
                      3 * widthScale width * upperPower width (.rule .b :: rest) := by
                  have upper_nonempty : 0 < upper.length := by
                    simp [upper, physicalUpperWord_length]
                  obtain ⟨predecessor, upper_length⟩ :=
                    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt upper_nonempty)
                  calc
                    (3 : ℤ) ^ upper.length = 3 ^ predecessor * 3 := by
                      rw [upper_length, pow_succ]
                    _ = 3 * 3 ^ (upper.length - 1) := by
                      rw [upper_length, Nat.succ_sub_one]
                      ring
                    _ = 3 *
                        (widthScale width * upperPower width (.rule .b :: rest)) := by
                      rw [show upper = physicalUpperWord width (.rule .b :: rest) by rfl,
                        physicalUpper_predecessorPower]
                    _ = 3 * widthScale width * upperPower width (.rule .b :: rest) := by
                      ring
                rw [power_eq] at cast_lt
                simpa only [swappedLowerCode, lower, physicalLowerWord] using cast_lt
              have equal_length_upper :
                  (swappedLowerCode width body (.rule .b :: rest) : ℚ) <
                    3 * widthScale width * upperPower width (.rule .b :: rest) := by
                exact_mod_cast equal_length_upper_int
              have above := ruleBPrefix_backwardBlock_above_chamber width_large
                current_above lower_pos upperPower_pos equal_length_upper rule_b_gap
              linarith

/-- If the canonical `R_c;D_b` pullback is above one, its near-diagonal gap is smaller than
`1/(80ρ)`. This is the history-sensitive estimate missing from the false universal two-block
norm claim. -/
theorem canonicalRcDbBackward_epsilon_lt
    {width : Nat} (width_large : 6 ≤ width) {current : ℚ}
    (current_above : (terminalDiscrepancy width : ℚ) < current)
    (image_above : 1 < canonicalRcDbBackward width current) :
    (canonicalRcDbBackward width current - 1) /
        canonicalRcDbBackward width current <
      1 / (80 * widthScale width) := by
  let block : List NearyTile := [.rule .c, .erase .b]
  let body := canonicalRcDbBody width
  let image := canonicalRcDbBackward width current
  have width_two : 2 ≤ width := by omega
  have lower_pos :
      (0 : ℚ) < swappedLowerCode width body block := by
    exact_mod_cast lowerCode_pos width body (.rule .c) [.erase .b]
  have upperPower_pos : (0 : ℚ) < upperPower width block := by
    simp [block, upperPower]
  have correction_pos :=
    (blockCorrection_pos_lt_three width_large current_above).1
  have denominator_ne :=
    (terminalRay_denominator_pos width_large current_above).ne'
  have image_eq :
      image =
        ((swappedUpperCode width block : ℚ) -
            blockCorrection width current * upperPower width block) /
          swappedLowerCode width body block := by
    simpa only [image, canonicalRcDbBackward, block, body] using
      backwardBlock_eq_sub_correction
        (width := width) (current := current)
        (punctuated := swappedUpperCode width block)
        (lower := swappedLowerCode width body block)
        (upperPower := upperPower width block) lower_pos.ne' denominator_ne
  have image_lt_codeRatio :
      image < (swappedUpperCode width block : ℚ) /
        swappedLowerCode width body block := by
    rw [image_eq]
    apply (div_lt_div_iff_of_pos_right lower_pos).2
    nlinarith [mul_pos correction_pos upperPower_pos]
  have image_pos : 0 < image := by
    change 1 < image at image_above
    linarith
  have epsilon_lt_gap : (image - 1) / image < image - 1 := by
    rw [div_lt_iff₀ image_pos]
    nlinarith [image_above]
  have scale_pos_int : (0 : ℤ) < widthScale width := by simp [widthScale]
  have lower_formula := canonicalRcDb_lowerCode width_two
  have upper_formula := canonicalRcDb_upperCode width
  have code_bound_int :
      80 * widthScale width *
          (swappedUpperCode width block - swappedLowerCode width body block) <
        swappedLowerCode width body block := by
    simp only [block, body] at lower_formula upper_formula ⊢
    nlinarith [sq_nonneg (widthScale width)]
  have code_bound :
      80 * (widthScale width : ℚ) *
          ((swappedUpperCode width block : ℚ) -
            swappedLowerCode width body block) <
        swappedLowerCode width body block := by
    exact_mod_cast code_bound_int
  have scale_pos : (0 : ℚ) < widthScale width := by exact_mod_cast scale_pos_int
  have codeRatio_gap_bound :
      (swappedUpperCode width block : ℚ) /
            swappedLowerCode width body block - 1 <
        1 / (80 * widthScale width) := by
    have quotient_gap :
        (swappedUpperCode width block : ℚ) /
              swappedLowerCode width body block - 1 =
          ((swappedUpperCode width block : ℚ) -
              swappedLowerCode width body block) /
            swappedLowerCode width body block := by
      field_simp [lower_pos.ne']
    rw [quotient_gap]
    apply (div_lt_div_iff₀ lower_pos (mul_pos (by norm_num) scale_pos)).2
    nlinarith [code_bound]
  change (image - 1) / image < 1 / (80 * widthScale width)
  nlinarith [image_lt_codeRatio, epsilon_lt_gap, codeRatio_gap_bound]

/-- The inverse block crosses zero exactly at its ordinary-entry threshold. -/
theorem backwardBlock_factor_entryThreshold
    {width : Nat} {punctuated lower upperPower current : ℚ}
    (centered_ne : (centeredCoefficient width : ℚ) ≠ 0)
    (punctuated_ne : punctuated ≠ 0) (lower_ne : lower ≠ 0)
    (current_ne :
      centeredCoefficient width * current - terminalDiscrepancy width ≠ 0) :
    backwardBlock width punctuated lower upperPower current =
      centeredCoefficient width * punctuated *
          (current - entryThreshold width punctuated upperPower) /
        (lower *
          (centeredCoefficient width * current - terminalDiscrepancy width)) := by
  simp only [backwardBlock, entryThreshold]
  field_simp [centered_ne, punctuated_ne, lower_ne, current_ne]
  ring

/-- Exact slope after pulling a positive near-diagonal carrier through `D_c`. -/
def deletionCSuccessorSlope (width : Nat) (epsilon : ℚ) : ℚ :=
  terminalDiscrepancy width * chamberRadius width * epsilon /
    (6 * setterMarker width +
      (2 * chamberRadius width - 6 * setterMarker width) * epsilon)

theorem deletionCSuccessorSlope_eq
    {width : Nat} {numerator denominator : ℚ}
    (numerator_ne : numerator ≠ 0) :
    deletionCSuccessorSlope width ((numerator - denominator) / numerator) =
      terminalDiscrepancy width * chamberRadius width *
          (numerator - denominator) /
        (2 * chamberRadius width * (numerator - denominator) +
          6 * setterMarker width * denominator) := by
  simp only [deletionCSuccessorSlope]
  field_simp [numerator_ne]
  ring

end MatrixMortality.SwappedSetterEmptyFrontChamber
