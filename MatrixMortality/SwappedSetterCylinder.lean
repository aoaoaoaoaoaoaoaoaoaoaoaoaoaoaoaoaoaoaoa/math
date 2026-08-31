import MatrixMortality.SwappedSetterMultitransfer

/-!
# Compiler cylinder for swapped multi-transfer poles

The first multi-transfer gate leaves two all-`c` middle-letter shapes. A compiler-emitted
body begins in `b` and has enough encoded length to make every `R_c` occurrence in either
shape overshoot the target-pole interval. The resulting theorem removes all rule-bearing
phases and leaves only the literal blocks `D_c²` and `D_c^(β+1)`.
-/

namespace MatrixMortality.SwappedSetterMultitransfer

/-- Upper power of a punctuated swapped role block. -/
def upperPower (width : Nat) (block : List NearyTile) : ℤ :=
  3 ^ upperLength width block

private theorem upperLength_cons (width : Nat) (tile : NearyTile)
    (rest : List NearyTile) :
    upperLength width (tile :: rest) =
      (match tile.letter with | .b => width + 2 | .c => 1) +
        upperLength width rest := by
  rw [upperLength, upperLength, spell_nearyUpper, spell_nearyUpper]
  simp only [List.map_cons]
  rw [tagEncode_cons, List.length_append]
  cases tile.letter <;> simp [tagCode]

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
  simp only [List.length_append, nearyMarker, List.length_cons, List.length_replicate,
    upperLength, spell_nearyUpper]
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

/-- Every punctuated swapped upper role code lies in its full first-role cylinder. -/
theorem swappedUpperCode_cylinder
    {width : Nat} (width_pos : 0 < width) (block : List NearyTile) :
    widthScale width * upperPower width block ≤ swappedUpperCode width block ∧
      swappedUpperCode width block <
        2 * widthScale width * upperPower width block := by
  have scale_ge_nat : 3 ≤ 3 ^ width := by
    obtain ⟨offset, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt width_pos)
    rw [pow_succ]
    have power_pos : 0 < 3 ^ offset := pow_pos (by omega) offset
    nlinarith
  have scale_ge : (3 : ℤ) ≤ widthScale width := by
    have casted : ((3 : Nat) : ℤ) ≤ ((3 ^ (width : Nat) : Nat) : ℤ) := by
      exact_mod_cast scale_ge_nat
    simpa [widthScale] using casted
  induction block with
  | nil =>
      have marker_eq : swappedUpperCode width [] = setterMarker width := by
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
      rw [marker_eq]
      have power_nil : upperPower width [] = 1 := rfl
      rw [power_nil]
      simp only [mul_one]
      simp only [setterMarker]
      omega
  | cons tile rest induction =>
      have power_pos : (0 : ℤ) < upperPower width rest := by
        simp [upperPower]
      rcases induction with ⟨lower, upper⟩
      cases tile with
      | rule letter =>
          cases letter with
          | c =>
              rw [swappedUpperCode_cons_c width rfl,
                upperPower_cons]
              simp only [NearyTile.letter]
              constructor <;> nlinarith
          | b =>
              rw [swappedUpperCode_cons_b width rfl,
                upperPower_cons]
              simp only [NearyTile.letter]
              constructor <;> nlinarith [mul_pos (sub_pos.mpr (by linarith :
                (2 : ℤ) < widthScale width)) power_pos]
      | erase letter =>
          cases letter with
          | c =>
              rw [swappedUpperCode_cons_c width rfl,
                upperPower_cons]
              simp only [NearyTile.letter]
              constructor <;> nlinarith
          | b =>
              rw [swappedUpperCode_cons_b width rfl,
                upperPower_cons]
              simp only [NearyTile.letter]
              constructor <;> nlinarith [mul_pos (sub_pos.mpr (by linarith :
                (2 : ℤ) < widthScale width)) power_pos]

private theorem swappedUpperCode_mod_three
    {width : Nat} (width_pos : 0 < width) (block : List NearyTile) :
    swappedUpperCode width block ≡ 2 [ZMOD 3] := by
  induction block with
  | nil =>
      have marker_eq : swappedUpperCode width [] = setterMarker width := by
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
      obtain ⟨offset, rfl⟩ :=
        Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt width_pos)
      have scale_zero : widthScale offset.succ ≡ 0 [ZMOD 3] := by
        simpa [widthScale, pow_succ, mul_comm] using
          (Int.ModEq.refl ((3 : ℤ) ^ offset)).mul
            (by norm_num : (3 : ℤ) ≡ 0 [ZMOD 3])
      rw [marker_eq, setterMarker]
      exact (((Int.ModEq.refl (2 : ℤ)).mul scale_zero).sub
        (Int.ModEq.refl 1)).trans (by norm_num)
  | cons tile rest induction =>
      cases tile_letter : tile.letter with
      | c =>
          rw [swappedUpperCode_cons_c _ tile_letter]
          have leading_zero :
              3 * widthScale width * upperPower width rest ≡ 0 [ZMOD 3] := by
            simpa using
              (((by norm_num : (3 : ℤ) ≡ 0 [ZMOD 3]).mul
                (Int.ModEq.refl (widthScale width))).mul
                  (Int.ModEq.refl (upperPower width rest)))
          simpa using leading_zero.add induction
      | b =>
          rw [swappedUpperCode_cons_b _ tile_letter]
          have leading_zero :
              3 * widthScale width * (6 * widthScale width - 2) *
                  upperPower width rest ≡ 0 [ZMOD 3] := by
            simpa using
              ((((by norm_num : (3 : ℤ) ≡ 0 [ZMOD 3]).mul
                (Int.ModEq.refl (widthScale width))).mul
                  (Int.ModEq.refl (6 * widthScale width - 2))).mul
                    (Int.ModEq.refl (upperPower width rest)))
          simpa using leading_zero.add induction

/-- Relative mismatch between the marker ray and a punctuated swapped upper code. -/
def firstMismatch (width : Nat) (block : List NearyTile) : ℚ :=
  (setterMarker width * upperPower width block - swappedUpperCode width block) /
    swappedUpperCode width block

private theorem firstMismatch_cons_c_lower
    {width : Nat} (width_pos : 0 < width) {tile : NearyTile}
    (tile_c : tile.letter = .c) (rest : List NearyTile) :
    ((widthScale width : ℚ) - 3) / (5 * widthScale width) <
      firstMismatch width (tile :: rest) := by
  have scale_ge_nat : 3 ≤ 3 ^ width := by
    obtain ⟨offset, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt width_pos)
    rw [pow_succ]
    have power_pos : 0 < 3 ^ offset := pow_pos (by omega) offset
    nlinarith
  have scale_ge_int : (3 : ℤ) ≤ widthScale width := by
    have casted : ((3 : Nat) : ℤ) ≤ ((3 ^ width : Nat) : ℤ) := by
      exact_mod_cast scale_ge_nat
    simpa [widthScale] using casted
  have scale_pos : (0 : ℚ) < (widthScale width : ℚ) := by
    exact_mod_cast lt_of_lt_of_le (by omega : (0 : ℤ) < 3) scale_ge_int
  have power_pos : (0 : ℤ) < upperPower width rest := by
    simp [upperPower]
  obtain ⟨rest_lower, rest_upper⟩ :=
    swappedUpperCode_cylinder width_pos rest
  have rest_upper_rat :
      (swappedUpperCode width rest : ℚ) <
        2 * widthScale width * upperPower width rest := by
    exact_mod_cast rest_upper
  have rest_lower_rat :
      (widthScale width : ℚ) * upperPower width rest ≤
        swappedUpperCode width rest := by
    exact_mod_cast rest_lower
  have first_pos : (0 : ℤ) < swappedUpperCode width (tile :: rest) := by
    rw [swappedUpperCode_cons_c width tile_c]
    nlinarith [mul_pos (show (0 : ℤ) < 3 * widthScale width by positivity) power_pos]
  rw [firstMismatch, upperPower_cons, tile_c,
    swappedUpperCode_cons_c width tile_c]
  simp only
  push_cast
  have power_pos_rat : (0 : ℚ) < upperPower width rest := by
    exact_mod_cast power_pos
  have rest_pos : (0 : ℚ) < swappedUpperCode width rest :=
    lt_of_lt_of_le (mul_pos scale_pos power_pos_rat) rest_lower_rat
  have denominator_pos :
      (0 : ℚ) <
        3 * widthScale width * upperPower width rest +
          swappedUpperCode width rest := by positivity
  apply (div_lt_div_iff₀ (mul_pos (by norm_num) scale_pos)
    denominator_pos).2
  rw [setterMarker]
  push_cast
  have gap_pos :
      (0 : ℚ) <
        2 * widthScale width * upperPower width rest -
          swappedUpperCode width rest := sub_pos.mpr rest_upper_rat
  have factor_pos : (0 : ℚ) < 6 * widthScale width - 3 := by
    have scale_ge_rat : (3 : ℚ) ≤ widthScale width := by
      exact_mod_cast scale_ge_int
    linarith
  nlinarith [mul_pos factor_pos gap_pos]

private theorem firstMismatch_cons_b_upper
    {width : Nat} (width_pos : 0 < width) {tile : NearyTile}
    (tile_b : tile.letter = .b) (rest : List NearyTile) :
    firstMismatch width (tile :: rest) <
      -(2 / (9 * widthScale width : ℚ)) := by
  have scale_pos_int : (0 : ℤ) < widthScale width := by
    simp [widthScale]
  have scale_pos : (0 : ℚ) < (widthScale width : ℚ) := by
    exact_mod_cast scale_pos_int
  have power_pos : (0 : ℤ) < upperPower width rest := by
    simp [upperPower]
  obtain ⟨rest_lower, rest_upper⟩ :=
    swappedUpperCode_cylinder width_pos rest
  have rest_lower_rat :
      (widthScale width : ℚ) * upperPower width rest ≤
        swappedUpperCode width rest := by
    exact_mod_cast rest_lower
  have first_pos : (0 : ℤ) < swappedUpperCode width (tile :: rest) := by
    rw [swappedUpperCode_cons_b width tile_b]
    have scaled_tag_pos : (0 : ℤ) < 6 * widthScale width - 2 := by
      rw [widthScale]
      have power_ge : (1 : ℤ) ≤ (3 : ℤ) ^ width := one_le_pow₀ (by norm_num)
      nlinarith
    have leading_pos :
        (0 : ℤ) <
          3 * widthScale width * (6 * widthScale width - 2) *
            upperPower width rest := by positivity
    nlinarith
  rw [firstMismatch, upperPower_cons, tile_b,
    swappedUpperCode_cons_b width tile_b]
  simp only
  push_cast
  have power_pos_rat : (0 : ℚ) < upperPower width rest := by
    exact_mod_cast power_pos
  have rest_pos : (0 : ℚ) < swappedUpperCode width rest :=
    lt_of_lt_of_le (mul_pos scale_pos power_pos_rat) rest_lower_rat
  have denominator_pos :
      (0 : ℚ) <
        3 * widthScale width * (6 * widthScale width - 2) *
            upperPower width rest + swappedUpperCode width rest := by
    have scaled_tag_pos : (0 : ℚ) < 6 * widthScale width - 2 := by
      have scale_one : (1 : ℚ) ≤ widthScale width := by
        exact_mod_cast (show (1 : ℤ) ≤ widthScale width by
          exact one_le_pow₀ (by norm_num))
      linarith
    positivity
  rw [neg_div']
  apply (div_lt_div_iff₀ denominator_pos
    (mul_pos (by norm_num) scale_pos)).2
  rw [setterMarker]
  push_cast
  have factor_pos : (0 : ℚ) < 9 * widthScale width - 2 := by
    have scale_one : (1 : ℚ) ≤ widthScale width := by
      exact_mod_cast (show (1 : ℤ) ≤ widthScale width by
        exact one_le_pow₀ (by norm_num))
    linarith
  have first_term_nonpos :
      ((9 * (widthScale width : ℚ) - 2) *
          ((widthScale width : ℚ) * (upperPower width rest : ℚ) -
            (swappedUpperCode width rest : ℚ))) ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt factor_pos)
      (sub_nonpos.mpr rest_lower_rat)
  nlinarith [mul_pos scale_pos power_pos_rat]

private theorem length_le_tagEncode (width : Nat) (word : List TagLetter) :
    word.length ≤ (tagEncode width word).length := by
  induction word with
  | nil => simp
  | cons letter word induction =>
      rw [tagEncode_cons, List.length_cons, List.length_append]
      have code_pos : 0 < (tagCode width letter).length := by
        cases letter <;> simp [tagCode]
      omega

private theorem tagEncode_length_of_head_b
    {width : Nat} {body : List TagLetter}
    (body_long : width - 1 ≤ body.length)
    (body_head : body.head? = some .b) :
    2 * width ≤ (tagEncode width body).length := by
  cases body with
  | nil => simp at body_head
  | cons letter tail =>
      simp only [List.head?_cons, Option.some.injEq] at body_head
      subst letter
      rw [tagEncode_cons, List.length_append]
      have tail_bound := length_le_tagEncode width tail
      simp [tagCode] at body_long ⊢
      omega

private theorem word_length_le_lower_length
    (width : Nat) (body : List TagLetter) (block : List NearyTile) :
    block.length ≤ (spell (nearyLower width body) block).length := by
  induction block with
  | nil => simp [spell]
  | cons tile block induction =>
      have tile_length : 0 < (nearyLower width body tile).length :=
        List.length_pos_of_ne_nil (nearyLower_ne_nil width body tile)
      change (tile :: block).length ≤
        (nearyLower width body tile ++ spell (nearyLower width body) block).length
      simp only [List.length_cons, List.length_append]
      omega

private theorem lowerLength_of_rule_c_mem
    {width : Nat} {body : List TagLetter} {block : List NearyTile}
    (body_long : width - 1 ≤ body.length)
    (body_head : body.head? = some .b)
    (rule_member : .rule .c ∈ block) :
    block.length + 2 * width + 2 ≤
      (spell (nearyLower width body) block).length := by
  induction block with
  | nil => simp at rule_member
  | cons tile block induction =>
      simp only [List.mem_cons] at rule_member
      change (tile :: block).length + 2 * width + 2 ≤
        (nearyLower width body tile ++ spell (nearyLower width body) block).length
      simp only [List.length_cons, List.length_append]
      rcases rule_member with rfl | rule_member
      · have body_encoded := tagEncode_length_of_head_b body_long body_head
        have block_bound := word_length_le_lower_length width body block
        simp only [nearyLower, List.length_append, List.length_cons, List.length_nil]
        omega
      · have tail_bound := induction rule_member
        have tile_length : 0 < (nearyLower width body tile).length :=
          List.length_pos_of_ne_nil (nearyLower_ne_nil width body tile)
        omega

private theorem swappedLowerCode_rule_c_lower
    {width : Nat} {body : List TagLetter} {block : List NearyTile}
    (body_long : width - 1 ≤ body.length)
    (body_head : body.head? = some .b)
    (rule_member : .rule .c ∈ block) :
    (3 : ℤ) ^ (block.length + 2 * width + 1) ≤
      swappedLowerCode width body block := by
  let lowerWord := (spell (nearyLower width body) block).map not
  have length_bound := lowerLength_of_rule_c_mem body_long body_head rule_member
  have lower_nonempty : lowerWord ≠ [] := by
    intro lower_nil
    have length_zero : lowerWord.length = 0 := by simp [lower_nil]
    simp only [lowerWord, List.length_map] at length_zero
    omega
  have code_bound := ternaryCode_lower_bound lowerWord lower_nonempty
  have exponent_bound : block.length + 2 * width + 1 ≤ lowerWord.length - 1 := by
    simp only [lowerWord, List.length_map]
    omega
  have power_bound :
      3 ^ (block.length + 2 * width + 1) ≤ 3 ^ (lowerWord.length - 1) :=
    Nat.pow_le_pow_right (by norm_num) exponent_bound
  have natural_bound :
      3 ^ (block.length + 2 * width + 1) ≤ ternaryCode lowerWord :=
    power_bound.trans code_bound
  rw [swappedLowerCode]
  change
    ((3 ^ (block.length + 2 * width + 1) : Nat) : ℤ) ≤
      (ternaryCode lowerWord : ℤ)
  exact_mod_cast natural_bound

private theorem upperLength_of_all_c
    {width count : Nat} {block : List NearyTile}
    (letters : block.map NearyTile.letter = List.replicate count .c) :
    upperLength width block = count := by
  rw [upperLength, spell_nearyUpper, letters]
  simp [tagEncode, spell, tagCode]

/-- Normalized denominator discrepancy after one positive swapped-setter transfer. -/
def transferDiscrepancy (width : Nat) (body : List TagLetter)
    (first middle : List NearyTile) : ℚ :=
  ((blockCoefficient width body middle : ℚ) * swappedUpperCode width first +
      terminalDiscrepancy width * setterMarker width *
        swappedLowerCode width body middle * upperPower width first) /
    (centeredCoefficient width * swappedUpperCode width first *
      (3 : ℚ) ^ (upperLength width middle - 1))

/-- Express the normalized transfer discrepancy through the incoming relative mismatch. -/
theorem transferDiscrepancy_eq
    {width : Nat} (width_large : 3 ≤ width) (body : List TagLetter)
    (first middle : List NearyTile) :
    transferDiscrepancy width body first middle =
      (swappedUpperCode width middle : ℚ) /
          (3 : ℚ) ^ (upperLength width middle - 1) -
        terminalDiscrepancy width * swappedLowerCode width body middle *
            firstMismatch width first /
          ((widthScale width - 2 : ℤ) *
            (3 : ℚ) ^ (upperLength width middle - 1)) := by
  have width_pos : 0 < width := by omega
  have first_bounds := swappedUpperCode_cylinder width_pos first
  have first_power_pos : (0 : ℤ) < upperPower width first := by
    simp [upperPower]
  have first_pos_int : (0 : ℤ) < swappedUpperCode width first := by
    nlinarith [mul_pos (show (0 : ℤ) < widthScale width by simp [widthScale])
      first_power_pos]
  have first_pos : (0 : ℚ) < swappedUpperCode width first := by
    exact_mod_cast first_pos_int
  have centered_ne : (centeredCoefficient width : ℚ) ≠ 0 := by
    have scale_ge_nat : 3 ^ 3 ≤ 3 ^ width :=
      Nat.pow_le_pow_right (by norm_num) width_large
    have scale_ge : (27 : ℤ) ≤ widthScale width := by
      have casted : ((3 ^ 3 : Nat) : ℤ) ≤ ((3 ^ width : Nat) : ℤ) := by
        exact_mod_cast scale_ge_nat
      simpa [widthScale] using casted
    have : (centeredCoefficient width : ℤ) < 0 := by
      simp only [centeredCoefficient]
      omega
    exact_mod_cast ne_of_lt this
  have scale_minus_two_ne : (((widthScale width - 2 : ℤ) : ℚ)) ≠ 0 := by
    have scale_ge_nat : 3 ^ 3 ≤ 3 ^ width :=
      Nat.pow_le_pow_right (by norm_num) width_large
    have scale_ge : (27 : ℤ) ≤ widthScale width := by
      have casted : ((3 ^ 3 : Nat) : ℤ) ≤ ((3 ^ width : Nat) : ℤ) := by
        exact_mod_cast scale_ge_nat
      simpa [widthScale] using casted
    exact_mod_cast (show (widthScale width - 2 : ℤ) ≠ 0 by omega)
  have power_ne : (3 : ℚ) ^ (upperLength width middle - 1) ≠ 0 := by positivity
  rw [transferDiscrepancy, firstMismatch]
  field_simp [centered_ne, scale_minus_two_ne, ne_of_gt first_pos, power_ne]
  simp only [blockCoefficient, centeredCoefficient]
  push_cast
  ring

private theorem word_length_le_upperLength
    (width : Nat) (block : List NearyTile) :
    block.length ≤ upperLength width block := by
  rw [upperLength]
  induction block with
  | nil => simp [spell]
  | cons tile block induction =>
      have tile_length : 0 < (nearyUpper width tile).length :=
        List.length_pos_of_ne_nil (nearyUpper_ne_nil width tile)
      change (tile :: block).length ≤
        (nearyUpper width tile ++ spell (nearyUpper width) block).length
      simp only [List.length_cons, List.length_append]
      omega

private theorem swappedUpperCode_pos
    {width : Nat} (width_pos : 0 < width) (block : List NearyTile) :
    0 < swappedUpperCode width block := by
  have bounds := swappedUpperCode_cylinder width_pos block
  have scale_pos : (0 : ℤ) < widthScale width := by simp [widthScale]
  have power_pos : (0 : ℤ) < upperPower width block := by
    simp [upperPower]
  nlinarith [mul_pos scale_pos power_pos]

private theorem swappedLowerCode_pos_of_nonempty
    {width : Nat} {body : List TagLetter} {block : List NearyTile}
    (block_nonempty : block ≠ []) :
    0 < swappedLowerCode width body block := by
  let lowerWord := (spell (nearyLower width body) block).map not
  have block_length_pos : 0 < block.length := List.length_pos_of_ne_nil block_nonempty
  have length_bound := word_length_le_lower_length width body block
  have lower_nonempty : lowerWord ≠ [] := by
    intro lower_nil
    have length_zero : lowerWord.length = 0 := by simp [lower_nil]
    simp only [lowerWord, List.length_map] at length_zero
    omega
  have code_bound := ternaryCode_lower_bound lowerWord lower_nonempty
  have code_pos : 0 < ternaryCode lowerWord :=
    lt_of_lt_of_le (pow_pos (by norm_num) (lowerWord.length - 1)) code_bound
  rw [swappedLowerCode]
  change (0 : ℤ) < (ternaryCode lowerWord : ℤ)
  exact_mod_cast code_pos

/-- A following pole is exactly the normalized transfer-discrepancy equation. -/
theorem transferDiscrepancy_pole_equation
    {width : Nat} (width_large : 3 ≤ width) (body : List TagLetter)
    (first : List NearyTile) {middle target : List NearyTile}
    (middle_nonempty : middle ≠ [])
    (pole :
      (blockCoefficient width body target : ℚ) *
          nextY (blockCoefficient width body middle) (centeredCoupling width)
            (swappedLowerCode width body middle) (upperPower width first)
            (centeredCoefficient width * swappedUpperCode width first) +
        centeredCoupling width * swappedLowerCode width body target *
          nextX (3 ^ upperLength width middle)
            (centeredCoefficient width * swappedUpperCode width first) = 0) :
    (blockCoefficient width body target : ℚ) *
          transferDiscrepancy width body first middle +
        3 * terminalDiscrepancy width * setterMarker width *
          swappedLowerCode width body target = 0 := by
  have width_pos : 0 < width := by omega
  have scale_ge_nat : 3 ^ 3 ≤ 3 ^ width :=
    Nat.pow_le_pow_right (by norm_num) width_large
  have scale_ge_int : (27 : ℤ) ≤ widthScale width := by
    have casted : ((3 ^ 3 : Nat) : ℤ) ≤ ((3 ^ width : Nat) : ℤ) := by
      exact_mod_cast scale_ge_nat
    simpa [widthScale] using casted
  have centered_neg_int : centeredCoefficient width < 0 := by
    simp only [centeredCoefficient]
    omega
  have centered_ne : (centeredCoefficient width : ℚ) ≠ 0 := by
    exact_mod_cast ne_of_lt centered_neg_int
  have first_pos_int := swappedUpperCode_pos width_pos first
  have first_pos : (0 : ℚ) < swappedUpperCode width first := by
    exact_mod_cast first_pos_int
  have middle_length_pos : 0 < upperLength width middle :=
    (List.length_pos_of_ne_nil middle_nonempty).trans_le
      (word_length_le_upperLength width middle)
  have middle_power_eq :
      (3 : ℚ) ^ upperLength width middle =
        3 * (3 : ℚ) ^ (upperLength width middle - 1) := by
    obtain ⟨offset, length_eq⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt middle_length_pos)
    rw [length_eq, Nat.succ_sub_one, pow_succ]
    ring
  have middle_power_pos :
      (0 : ℚ) < (3 : ℚ) ^ (upperLength width middle - 1) := by positivity
  have middle_power_ne :
      (3 : ℚ) ^ (upperLength width middle - 1) ≠ 0 :=
    ne_of_gt middle_power_pos
  have pole_factor :
      (blockCoefficient width body target : ℚ) *
            nextY (blockCoefficient width body middle) (centeredCoupling width)
              (swappedLowerCode width body middle) (upperPower width first)
              (centeredCoefficient width * swappedUpperCode width first) +
          centeredCoupling width * swappedLowerCode width body target *
            nextX (3 ^ upperLength width middle)
              (centeredCoefficient width * swappedUpperCode width first) =
        (centeredCoefficient width : ℚ) *
          ((centeredCoefficient width : ℚ) * swappedUpperCode width first *
            (3 : ℚ) ^ (upperLength width middle - 1)) *
          ((blockCoefficient width body target : ℚ) *
              transferDiscrepancy width body first middle +
            3 * terminalDiscrepancy width * setterMarker width *
              swappedLowerCode width body target) := by
    rw [transferDiscrepancy]
    field_simp [centered_ne, ne_of_gt first_pos, middle_power_ne]
    rw [middle_power_eq]
    norm_num [nextX, nextY, centeredCoupling]
    ring
  have factor_zero :
      (centeredCoefficient width : ℚ) *
          ((centeredCoefficient width : ℚ) * swappedUpperCode width first *
            (3 : ℚ) ^ (upperLength width middle - 1)) *
          ((blockCoefficient width body target : ℚ) *
              transferDiscrepancy width body first middle +
            3 * terminalDiscrepancy width * setterMarker width *
              swappedLowerCode width body target) = 0 := by
    rw [← pole_factor]
    exact pole
  rcases mul_eq_zero.mp factor_zero with leading_zero | normalized_zero
  · rcases mul_eq_zero.mp leading_zero with centered_zero | denominator_zero
    · exact False.elim (centered_ne centered_zero)
    · have denominator_ne :
          (centeredCoefficient width : ℚ) * swappedUpperCode width first *
              (3 : ℚ) ^ (upperLength width middle - 1) ≠ 0 := by
        exact mul_ne_zero (mul_ne_zero centered_ne (ne_of_gt first_pos)) middle_power_ne
      exact False.elim (denominator_ne denominator_zero)
  · exact normalized_zero

/-- A following physical role pole forces the transfer discrepancy into `(0,3μ)`. -/
theorem transferDiscrepancy_pole_interval
    {width : Nat} (width_large : 3 ≤ width) (body : List TagLetter)
    (first : List NearyTile) {middle target : List NearyTile}
    (middle_nonempty : middle ≠ []) (target_nonempty : target ≠ [])
    (pole :
      (blockCoefficient width body target : ℚ) *
          nextY (blockCoefficient width body middle) (centeredCoupling width)
            (swappedLowerCode width body middle) (upperPower width first)
            (centeredCoefficient width * swappedUpperCode width first) +
        centeredCoupling width * swappedLowerCode width body target *
          nextX (3 ^ upperLength width middle)
            (centeredCoefficient width * swappedUpperCode width first) = 0) :
    0 < transferDiscrepancy width body first middle ∧
      transferDiscrepancy width body first middle <
        3 * setterMarker width := by
  have width_pos : 0 < width := by omega
  have scale_ge_nat : 3 ^ 3 ≤ 3 ^ width :=
    Nat.pow_le_pow_right (by norm_num) width_large
  have scale_ge_int : (27 : ℤ) ≤ widthScale width := by
    have casted : ((3 ^ 3 : Nat) : ℤ) ≤ ((3 ^ width : Nat) : ℤ) := by
      exact_mod_cast scale_ge_nat
    simpa [widthScale] using casted
  have centered_neg_int : centeredCoefficient width < 0 := by
    simp only [centeredCoefficient]
    omega
  have centered_neg : (centeredCoefficient width : ℚ) < 0 := by
    exact_mod_cast centered_neg_int
  have marker_pos_int : (0 : ℤ) < setterMarker width := by
    simp only [setterMarker]
    omega
  have marker_pos : (0 : ℚ) < setterMarker width := by
    exact_mod_cast marker_pos_int
  have terminal_pos_int : (0 : ℤ) < terminalDiscrepancy width := by
    simp only [terminalDiscrepancy]
    omega
  have terminal_pos : (0 : ℚ) < terminalDiscrepancy width := by
    exact_mod_cast terminal_pos_int
  have target_upper_pos_int := swappedUpperCode_pos width_pos target
  have target_upper_pos : (0 : ℚ) < swappedUpperCode width target := by
    exact_mod_cast target_upper_pos_int
  have target_lower_pos_int :=
    swappedLowerCode_pos_of_nonempty (width := width) (body := body) target_nonempty
  have target_lower_pos : (0 : ℚ) < swappedLowerCode width body target := by
    exact_mod_cast target_lower_pos_int
  have normalized_pole :=
    transferDiscrepancy_pole_equation width_large body first middle_nonempty pole
  have target_coefficient_neg :
      (blockCoefficient width body target : ℚ) < 0 := by
    rw [blockCoefficient]
    push_cast
    have centered_upper_neg :
        (centeredCoefficient width : ℚ) * swappedUpperCode width target < 0 :=
      mul_neg_of_neg_of_pos centered_neg target_upper_pos
    have terminal_lower_pos :
        (0 : ℚ) < terminalDiscrepancy width * swappedLowerCode width body target :=
      mul_pos terminal_pos target_lower_pos
    linarith
  have coupling_tail_pos :
      (0 : ℚ) < 3 * terminalDiscrepancy width * setterMarker width *
        swappedLowerCode width body target := by positivity
  have discrepancy_pos :
      0 < transferDiscrepancy width body first middle := by
    by_contra not_pos
    have discrepancy_nonpos :
        transferDiscrepancy width body first middle ≤ 0 := le_of_not_gt not_pos
    have product_nonneg :
        0 ≤ (blockCoefficient width body target : ℚ) *
          transferDiscrepancy width body first middle :=
      mul_nonneg_of_nonpos_of_nonpos (le_of_lt target_coefficient_neg) discrepancy_nonpos
    linarith
  have benchmark_eq :
      (blockCoefficient width body target : ℚ) * (3 * setterMarker width) +
          3 * terminalDiscrepancy width * setterMarker width *
            swappedLowerCode width body target =
        3 * setterMarker width * centeredCoefficient width *
          swappedUpperCode width target := by
    rw [blockCoefficient]
    push_cast
    ring
  have benchmark_neg :
      (blockCoefficient width body target : ℚ) * (3 * setterMarker width) +
          3 * terminalDiscrepancy width * setterMarker width *
            swappedLowerCode width body target < 0 := by
    rw [benchmark_eq]
    exact mul_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg (mul_pos (by norm_num) marker_pos) centered_neg)
      target_upper_pos
  have discrepancy_lt :
      transferDiscrepancy width body first middle < 3 * setterMarker width := by
    by_contra not_lt
    have threshold_le :
        3 * setterMarker width ≤ transferDiscrepancy width body first middle :=
      le_of_not_gt not_lt
    have product_le :
        (blockCoefficient width body target : ℚ) *
            transferDiscrepancy width body first middle ≤
          (blockCoefficient width body target : ℚ) * (3 * setterMarker width) :=
      mul_le_mul_of_nonpos_left threshold_le (le_of_lt target_coefficient_neg)
    linarith
  exact ⟨discrepancy_pos, discrepancy_lt⟩

private theorem power_rule_c_factor
    {width count : Nat} (count_pos : 0 < count) :
    (((3 : ℤ) ^ (count + 2 * width + 1) : ℤ) : ℚ) =
      9 * (widthScale width : ℚ) ^ 2 * (3 : ℚ) ^ (count - 1) := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt count_pos)
  simp only [Nat.succ_sub_one, widthScale]
  push_cast
  rw [show offset + 1 + 2 * width + 1 = 2 + 2 * width + offset by omega,
    pow_add, pow_add]
  ring

private theorem swappedLowerCode_rule_c_normalized_lower
    {width count : Nat} {body : List TagLetter} {block : List NearyTile}
    (body_long : width - 1 ≤ body.length)
    (body_head : body.head? = some .b)
    (letters : block.map NearyTile.letter = List.replicate count .c)
    (rule_member : .rule .c ∈ block) :
    9 * (widthScale width : ℚ) ^ 2 * (3 : ℚ) ^ (count - 1) ≤
      swappedLowerCode width body block := by
  have length_eq : block.length = count := by
    have lengths := congrArg List.length letters
    simpa using lengths
  have count_pos : 0 < count := by
    have block_nonempty : block ≠ [] := by
      intro block_nil
      simp [block_nil] at rule_member
    rw [← length_eq]
    exact List.length_pos_of_ne_nil block_nonempty
  have lower_bound := swappedLowerCode_rule_c_lower body_long body_head rule_member
  rw [length_eq] at lower_bound
  have lower_bound_rat :
      (((3 : ℤ) ^ (count + 2 * width + 1) : ℤ) : ℚ) ≤
        swappedLowerCode width body block := by
    exact_mod_cast lower_bound
  rw [power_rule_c_factor count_pos] at lower_bound_rat
  exact lower_bound_rat

private theorem swappedUpperCode_all_c_upper
    {width count : Nat} (width_pos : 0 < width) (count_pos : 0 < count)
    {block : List NearyTile}
    (letters : block.map NearyTile.letter = List.replicate count .c) :
    (swappedUpperCode width block : ℚ) <
      6 * widthScale width * (3 : ℚ) ^ (count - 1) := by
  have count_eq := upperLength_of_all_c (width := width) letters
  have bounds := (swappedUpperCode_cylinder width_pos block).2
  rw [upperPower, count_eq] at bounds
  have power_eq :
      ((3 : ℤ) ^ count : ℤ) =
        3 * (3 : ℤ) ^ (count - 1) := by
    obtain ⟨offset, rfl⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt count_pos)
    rw [Nat.succ_sub_one, pow_succ]
    ring
  rw [power_eq] at bounds
  have bound_normalize :
      2 * widthScale width * (3 * (3 : ℤ) ^ (count - 1)) =
        6 * widthScale width * (3 : ℤ) ^ (count - 1) := by ring
  rw [bound_normalize] at bounds
  exact_mod_cast bounds

private theorem transferDiscrepancy_nonpos_of_first_c
    {width count : Nat} (width_large : 3 ≤ width)
    {body : List TagLetter}
    (body_long : width - 1 ≤ body.length)
    (body_head : body.head? = some .b)
    {firstTile : NearyTile} (first_c : firstTile.letter = .c)
    (firstRest : List NearyTile) {middle : List NearyTile}
    (middle_letters :
      middle.map NearyTile.letter = List.replicate count .c)
    (rule_member : .rule .c ∈ middle) :
    transferDiscrepancy width body (firstTile :: firstRest) middle ≤ 0 := by
  have width_pos : 0 < width := by omega
  have scale_ge_nat : 3 ^ 3 ≤ 3 ^ width :=
    Nat.pow_le_pow_right (by norm_num) width_large
  have scale_ge_int : (27 : ℤ) ≤ widthScale width := by
    have casted : ((3 ^ 3 : Nat) : ℤ) ≤ ((3 ^ width : Nat) : ℤ) := by
      exact_mod_cast scale_ge_nat
    simpa [widthScale] using casted
  have scale_ge : (27 : ℚ) ≤ widthScale width := by
    exact_mod_cast scale_ge_int
  have scale_pos : (0 : ℚ) < widthScale width := by linarith
  have difference_pos : (0 : ℚ) < (widthScale width : ℚ) - 3 := by linarith
  have divisor_pos : (0 : ℚ) < (widthScale width : ℚ) - 2 := by linarith
  have terminal_pos : (0 : ℚ) < terminalDiscrepancy width := by
    rw [terminalDiscrepancy]
    push_cast
    linarith
  have count_pos : 0 < count := by
    have middle_nonempty : middle ≠ [] := by
      intro middle_nil
      simp [middle_nil] at rule_member
    have lengths := congrArg List.length middle_letters
    simp only [List.length_map, List.length_replicate] at lengths
    rw [← lengths]
    exact List.length_pos_of_ne_nil middle_nonempty
  have power_pos : (0 : ℚ) < (3 : ℚ) ^ (count - 1) := by positivity
  have middle_upper :=
    swappedUpperCode_all_c_upper width_pos count_pos middle_letters
  have middle_lower :=
    swappedLowerCode_rule_c_normalized_lower body_long body_head middle_letters
      rule_member
  have mismatch_lower :=
    firstMismatch_cons_c_lower width_pos first_c firstRest
  have mismatch_pos :
      0 < firstMismatch width (firstTile :: firstRest) :=
    lt_trans (div_pos difference_pos (mul_pos (by norm_num) scale_pos)) mismatch_lower
  have arithmetic_core :
      (30 : ℚ) * ((widthScale width : ℚ) - 2) <
        9 * terminalDiscrepancy width * ((widthScale width : ℚ) - 3) := by
    rw [terminalDiscrepancy]
    push_cast
    nlinarith [sq_nonneg ((widthScale width : ℚ) - 27)]
  have upper_scaled :
      ((widthScale width : ℚ) - 2) * swappedUpperCode width middle <
        ((widthScale width : ℚ) - 2) *
          (6 * widthScale width * (3 : ℚ) ^ (count - 1)) :=
    mul_lt_mul_of_pos_left middle_upper divisor_pos
  have core_scaled :=
    mul_lt_mul_of_pos_right arithmetic_core (mul_pos scale_pos power_pos)
  have first_bridge :
      ((widthScale width : ℚ) - 2) *
          (6 * widthScale width * (3 : ℚ) ^ (count - 1)) <
        (9 / 5 : ℚ) * terminalDiscrepancy width * widthScale width *
          (3 : ℚ) ^ (count - 1) * ((widthScale width : ℚ) - 3) := by
    nlinarith [core_scaled]
  have mismatch_scaled :
      (widthScale width : ℚ) - 3 <
        5 * widthScale width * firstMismatch width (firstTile :: firstRest) := by
    simpa [mul_comm] using
      (div_lt_iff₀ (mul_pos (by norm_num) scale_pos)).mp mismatch_lower
  have bridge_factor_pos :
      (0 : ℚ) <
        (9 / 5 : ℚ) * terminalDiscrepancy width * widthScale width *
          (3 : ℚ) ^ (count - 1) := by positivity
  have second_bridge_raw :=
    mul_lt_mul_of_pos_left mismatch_scaled bridge_factor_pos
  have second_bridge :
      (9 / 5 : ℚ) * terminalDiscrepancy width * widthScale width *
            (3 : ℚ) ^ (count - 1) * ((widthScale width : ℚ) - 3) <
        9 * terminalDiscrepancy width * (widthScale width : ℚ) ^ 2 *
          (3 : ℚ) ^ (count - 1) *
            firstMismatch width (firstTile :: firstRest) := by
    nlinarith [second_bridge_raw]
  have lower_scaled := mul_le_mul_of_nonneg_right middle_lower
    (le_of_lt <| mul_pos terminal_pos mismatch_pos)
  have third_bridge :
      9 * terminalDiscrepancy width * (widthScale width : ℚ) ^ 2 *
            (3 : ℚ) ^ (count - 1) *
              firstMismatch width (firstTile :: firstRest) ≤
        terminalDiscrepancy width * swappedLowerCode width body middle *
          firstMismatch width (firstTile :: firstRest) := by
    nlinarith [lower_scaled]
  have coefficient_domination :
      ((widthScale width : ℚ) - 2) * swappedUpperCode width middle <
        terminalDiscrepancy width * swappedLowerCode width body middle *
          firstMismatch width (firstTile :: firstRest) :=
    upper_scaled.trans (first_bridge.trans (second_bridge.trans_le third_bridge))
  have discrepancy_eq :=
    transferDiscrepancy_eq width_large body (firstTile :: firstRest) middle
  rw [upperLength_of_all_c (width := width) middle_letters] at discrepancy_eq
  push_cast at discrepancy_eq
  rw [discrepancy_eq]
  apply sub_nonpos.mpr
  apply (div_le_div_iff₀ power_pos (mul_pos divisor_pos power_pos)).2
  have domination_scaled :=
    mul_le_mul_of_nonneg_right (le_of_lt coefficient_domination) (le_of_lt power_pos)
  nlinarith [domination_scaled]

private theorem transferDiscrepancy_large_of_first_b
    {width count : Nat} (width_large : 3 ≤ width)
    {body : List TagLetter}
    (body_long : width - 1 ≤ body.length)
    (body_head : body.head? = some .b)
    {firstTile : NearyTile} (first_b : firstTile.letter = .b)
    (firstRest : List NearyTile) {middle : List NearyTile}
    (middle_letters :
      middle.map NearyTile.letter = List.replicate count .c)
    (rule_member : .rule .c ∈ middle) :
    3 * setterMarker width <
      transferDiscrepancy width body (firstTile :: firstRest) middle := by
  have width_pos : 0 < width := by omega
  have scale_ge_nat : 3 ^ 3 ≤ 3 ^ width :=
    Nat.pow_le_pow_right (by norm_num) width_large
  have scale_ge_int : (27 : ℤ) ≤ widthScale width := by
    have casted : ((3 ^ 3 : Nat) : ℤ) ≤ ((3 ^ width : Nat) : ℤ) := by
      exact_mod_cast scale_ge_nat
    simpa [widthScale] using casted
  have scale_ge : (27 : ℚ) ≤ widthScale width := by
    exact_mod_cast scale_ge_int
  have scale_pos : (0 : ℚ) < widthScale width := by linarith
  have divisor_pos : (0 : ℚ) < (widthScale width : ℚ) - 2 := by linarith
  have marker_pos : (0 : ℚ) < setterMarker width := by
    rw [setterMarker]
    push_cast
    linarith
  have terminal_pos : (0 : ℚ) < terminalDiscrepancy width := by
    rw [terminalDiscrepancy]
    push_cast
    linarith
  have count_pos : 0 < count := by
    have middle_nonempty : middle ≠ [] := by
      intro middle_nil
      simp [middle_nil] at rule_member
    have lengths := congrArg List.length middle_letters
    simp only [List.length_map, List.length_replicate] at lengths
    rw [← lengths]
    exact List.length_pos_of_ne_nil middle_nonempty
  have power_pos : (0 : ℚ) < (3 : ℚ) ^ (count - 1) := by positivity
  have middle_upper_pos_int := swappedUpperCode_pos width_pos middle
  have middle_upper_pos : (0 : ℚ) < swappedUpperCode width middle := by
    exact_mod_cast middle_upper_pos_int
  have middle_lower :=
    swappedLowerCode_rule_c_normalized_lower body_long body_head middle_letters
      rule_member
  have mismatch_upper := firstMismatch_cons_b_upper width_pos first_b firstRest
  have reverse_mismatch_lower :
      2 / (9 * widthScale width : ℚ) <
        -firstMismatch width (firstTile :: firstRest) := by
    linarith
  have reverse_mismatch_pos :
      0 < -firstMismatch width (firstTile :: firstRest) :=
    lt_trans (div_pos (by norm_num) (mul_pos (by norm_num) scale_pos))
      reverse_mismatch_lower
  have arithmetic_core :
      (3 : ℚ) * setterMarker width * ((widthScale width : ℚ) - 2) <
        2 * terminalDiscrepancy width * widthScale width := by
    rw [setterMarker, terminalDiscrepancy]
    push_cast
    nlinarith [sq_nonneg ((widthScale width : ℚ) - 27)]
  have core_scaled :=
    mul_lt_mul_of_pos_right arithmetic_core power_pos
  have first_bridge :
      (3 : ℚ) * setterMarker width * ((widthScale width : ℚ) - 2) *
            (3 : ℚ) ^ (count - 1) <
        2 * terminalDiscrepancy width * widthScale width *
          (3 : ℚ) ^ (count - 1) := by
    exact core_scaled
  have mismatch_scaled :
      (2 : ℚ) < 9 * widthScale width *
        (-firstMismatch width (firstTile :: firstRest)) := by
    simpa [mul_comm] using
      (div_lt_iff₀ (mul_pos (by norm_num) scale_pos)).mp reverse_mismatch_lower
  have bridge_factor_pos :
      (0 : ℚ) < terminalDiscrepancy width * widthScale width *
        (3 : ℚ) ^ (count - 1) := by positivity
  have second_bridge_raw :=
    mul_lt_mul_of_pos_left mismatch_scaled bridge_factor_pos
  have second_bridge :
      2 * terminalDiscrepancy width * widthScale width *
            (3 : ℚ) ^ (count - 1) <
        9 * terminalDiscrepancy width * (widthScale width : ℚ) ^ 2 *
          (3 : ℚ) ^ (count - 1) *
            (-firstMismatch width (firstTile :: firstRest)) := by
    nlinarith [second_bridge_raw]
  have lower_scaled := mul_le_mul_of_nonneg_right middle_lower
    (le_of_lt <| mul_pos terminal_pos reverse_mismatch_pos)
  have third_bridge :
      9 * terminalDiscrepancy width * (widthScale width : ℚ) ^ 2 *
            (3 : ℚ) ^ (count - 1) *
              (-firstMismatch width (firstTile :: firstRest)) ≤
        terminalDiscrepancy width * swappedLowerCode width body middle *
          (-firstMismatch width (firstTile :: firstRest)) := by
    nlinarith [lower_scaled]
  have coefficient_domination :
      (3 : ℚ) * setterMarker width * ((widthScale width : ℚ) - 2) *
            (3 : ℚ) ^ (count - 1) <
        terminalDiscrepancy width * swappedLowerCode width body middle *
          (-firstMismatch width (firstTile :: firstRest)) :=
    first_bridge.trans (second_bridge.trans_le third_bridge)
  have quotient_large :
      (3 : ℚ) * setterMarker width <
        terminalDiscrepancy width * swappedLowerCode width body middle *
            (-firstMismatch width (firstTile :: firstRest)) /
          (((widthScale width : ℚ) - 2) * (3 : ℚ) ^ (count - 1)) := by
    apply (lt_div_iff₀ (mul_pos divisor_pos power_pos)).2
    simpa [mul_assoc] using coefficient_domination
  have upper_quotient_pos :
      (0 : ℚ) < swappedUpperCode width middle / (3 : ℚ) ^ (count - 1) :=
    div_pos middle_upper_pos power_pos
  have sign_eq :
      terminalDiscrepancy width * swappedLowerCode width body middle *
            (-firstMismatch width (firstTile :: firstRest)) /
          (((widthScale width : ℚ) - 2) * (3 : ℚ) ^ (count - 1)) =
        -(terminalDiscrepancy width * swappedLowerCode width body middle *
            firstMismatch width (firstTile :: firstRest) /
          (((widthScale width : ℚ) - 2) * (3 : ℚ) ^ (count - 1))) := by
    ring
  have discrepancy_eq :=
    transferDiscrepancy_eq width_large body (firstTile :: firstRest) middle
  rw [upperLength_of_all_c (width := width) middle_letters] at discrepancy_eq
  push_cast at discrepancy_eq
  rw [discrepancy_eq, sub_eq_add_neg, ← sign_eq]
  linarith

/-- Under the compiler body envelope, an all-`c` middle block containing `R_c` cannot
reach any physical nonempty role pole. A `c`-leading first block gives discrepancy `Δ≤0`;
a `b`-leading first block gives `Δ>3μ`; every target pole requires `0<Δ<3μ`. -/
theorem ruleBearing_allC_avoids_pole
    {width count : Nat} (width_large : 3 ≤ width)
    {body : List TagLetter}
    (body_long : width - 1 ≤ body.length)
    (body_head : body.head? = some .b)
    {first middle target : List NearyTile}
    (first_block : IsRoleBlock first)
    (middle_letters :
      middle.map NearyTile.letter = List.replicate count .c)
    (rule_member : .rule .c ∈ middle)
    (target_block : IsRoleBlock target)
    (pole :
      (blockCoefficient width body target : ℚ) *
          nextY (blockCoefficient width body middle) (centeredCoupling width)
            (swappedLowerCode width body middle) ((3 : ℚ) ^ upperLength width first)
            (centeredCoefficient width * swappedUpperCode width first) +
        centeredCoupling width * swappedLowerCode width body target *
          nextX (3 ^ upperLength width middle)
            (centeredCoefficient width * swappedUpperCode width first) = 0) : False := by
  have first_nonempty : first ≠ [] := by
    obtain ⟨front, letter, rfl⟩ := first_block
    simp
  have middle_nonempty : middle ≠ [] := by
    intro middle_nil
    simp [middle_nil] at rule_member
  have target_nonempty : target ≠ [] := by
    obtain ⟨front, letter, rfl⟩ := target_block
    simp
  have interval_pole :
      (blockCoefficient width body target : ℚ) *
            nextY (blockCoefficient width body middle) (centeredCoupling width)
              (swappedLowerCode width body middle) (upperPower width first)
              (centeredCoefficient width * swappedUpperCode width first) +
          centeredCoupling width * swappedLowerCode width body target *
            nextX (3 ^ upperLength width middle)
              (centeredCoefficient width * swappedUpperCode width first) = 0 := by
    simpa [upperPower] using pole
  have interval := transferDiscrepancy_pole_interval width_large body first
    middle_nonempty target_nonempty interval_pole
  cases first with
  | nil => exact False.elim (first_nonempty rfl)
  | cons firstTile firstRest =>
      cases first_letter : firstTile.letter with
      | b =>
          have above := transferDiscrepancy_large_of_first_b width_large body_long
            body_head first_letter firstRest middle_letters rule_member
          linarith
      | c =>
          have below := transferDiscrepancy_nonpos_of_first_c width_large body_long
            body_head first_letter firstRest middle_letters rule_member
          linarith

private theorem eq_replicate_erase_c_of_no_rule
    {count : Nat} {block : List NearyTile}
    (letters : block.map NearyTile.letter = List.replicate count .c)
    (rule_absent : .rule .c ∉ block) :
    block = List.replicate count (.erase .c) := by
  induction block generalizing count with
  | nil =>
      have count_zero : count = 0 := by
        have lengths := congrArg List.length letters
        simpa using lengths.symm
      subst count
      rfl
  | cons tile block induction =>
      cases count with
      | zero => simp at letters
      | succ count =>
          simp only [List.map_cons, List.replicate_succ, List.cons.injEq] at letters
          obtain ⟨tile_letter, block_letters⟩ := letters
          cases tile with
          | rule letter =>
              simp only [NearyTile.letter] at tile_letter
              subst letter
              exact False.elim (rule_absent (by simp))
          | erase letter =>
              simp only [NearyTile.letter] at tile_letter
              subst letter
              rw [List.replicate_succ, List.cons.injEq]
              refine ⟨rfl, induction block_letters ?_⟩
              intro member
              exact rule_absent (by simp [member])

private theorem firstTwo_cMiddle_pole_forces_all_erasure
    {width : Nat} (width_large : 3 ≤ width)
    {body : List TagLetter}
    (body_long : width - 1 ≤ body.length)
    (body_head : body.head? = some .b)
    {first middle target : List NearyTile}
    (first_block : IsRoleBlock first)
    (middle_shape :
      middle.map NearyTile.letter = [.c, .c] ∨
        middle.map NearyTile.letter = List.replicate (width + 1) .c)
    (target_block : IsRoleBlock target)
    (pole :
      (blockCoefficient width body target : ℚ) *
          nextY (blockCoefficient width body middle) (centeredCoupling width)
            (swappedLowerCode width body middle) ((3 : ℚ) ^ upperLength width first)
            (centeredCoefficient width * swappedUpperCode width first) +
        centeredCoupling width * swappedLowerCode width body target *
          nextX (3 ^ upperLength width middle)
            (centeredCoefficient width * swappedUpperCode width first) = 0) :
    middle = [.erase .c, .erase .c] ∨
      middle = List.replicate (width + 1) (.erase .c) := by
  by_cases rule_member : .rule .c ∈ middle
  · rcases middle_shape with two_c | long_c
    · exact False.elim <| ruleBearing_allC_avoids_pole width_large body_long
        body_head first_block (count := 2) (by simpa using two_c) rule_member
        target_block pole
    · exact False.elim <| ruleBearing_allC_avoids_pole width_large body_long
        body_head first_block long_c rule_member target_block pole
  · rcases middle_shape with two_c | long_c
    · left
      simpa using eq_replicate_erase_c_of_no_rule (count := 2)
        (by simpa using two_c) rule_member
    · right
      exact eq_replicate_erase_c_of_no_rule long_c rule_member

/-- In the compiler body envelope, every expected-shell first multi-transfer pole has one
of two literal middle blocks: `D_c²` toward a depth-one target, or `D_c^(β+1)` toward a
singleton target. The third branch of the raw trichotomy is discharged by the
singleton-`D_b` extinction theorem. -/
theorem firstMultiTransfer_pole_forces_all_erasure
    {width firstDepth middleDepth targetDepth : Nat}
    (width_large : 3 ≤ width)
    {body : List TagLetter}
    (body_long : width - 1 ≤ body.length)
    (body_head : body.head? = some .b)
    {first middle target : List NearyTile}
    (first_block : IsRoleBlock first)
    (middle_shell : HasPoleShell width middle middleDepth)
    (target_shell : HasPoleShell width target targetDepth)
    (first_nontrivial : 1 < firstDepth)
    (firstDepth_eq : firstDepth = upperLength width first)
    (middleCoefficient_shell :
      MatrixMortality.PadicValuation.HasValue 3
        (blockCoefficient width body middle : ℚ) middleDepth)
    (middleLower_unit :
      MatrixMortality.PadicValuation.IsUnit 3
        (swappedLowerCode width body middle : ℚ))
    (targetCoefficient_shell :
      MatrixMortality.PadicValuation.HasValue 3
        (blockCoefficient width body target : ℚ) targetDepth)
    (targetLower_unit :
      MatrixMortality.PadicValuation.IsUnit 3
        (swappedLowerCode width body target : ℚ))
    (pole :
      (blockCoefficient width body target : ℚ) *
          nextY (blockCoefficient width body middle) (centeredCoupling width)
            (swappedLowerCode width body middle) ((3 : ℚ) ^ upperLength width first)
            (centeredCoefficient width * swappedUpperCode width first) +
        centeredCoupling width * swappedLowerCode width body target *
          nextX (3 ^ upperLength width middle)
            (centeredCoefficient width * swappedUpperCode width first) = 0) :
    (middle = [.erase .c, .erase .c] ∧ targetDepth = 1) ∨
      (middle = List.replicate (width + 1) (.erase .c) ∧ targetDepth = width) := by
  have gate_pole :
      (blockCoefficient width body target : ℚ) *
            nextY (blockCoefficient width body middle) (centeredCoupling width)
              (swappedLowerCode width body middle) ((3 : ℚ) ^ firstDepth)
              (centeredCoefficient width * swappedUpperCode width first) +
          centeredCoupling width * swappedLowerCode width body target *
            nextX (3 ^ upperLength width middle)
              (centeredCoefficient width * swappedUpperCode width first) = 0 := by
    simpa [firstDepth_eq] using pole
  have gate := firstMultiTransfer_trichotomy_of_pole width_large first_block middle_shell
    target_shell first_nontrivial firstDepth_eq (swappedUpperCode_mod_three (by omega) first)
    middleCoefficient_shell
    middleLower_unit targetCoefficient_shell targetLower_unit gate_pole
  rcases gate with two_c | long_c | singleton_b
  · obtain ⟨middle_letters, targetDepth_one⟩ := two_c
    have survivors := firstTwo_cMiddle_pole_forces_all_erasure width_large body_long
      body_head first_block (Or.inl middle_letters) target_shell.1 pole
    rcases survivors with middle_eq | impossible_eq
    · exact Or.inl ⟨middle_eq, targetDepth_one⟩
    · have middle_length_two : middle.length = 2 := by
        have lengths := congrArg List.length middle_letters
        simpa using lengths
      have middle_length_long : middle.length = width + 1 := by
        rw [impossible_eq, List.length_replicate]
      omega
  · obtain ⟨middle_letters, targetDepth_width⟩ := long_c
    have survivors := firstTwo_cMiddle_pole_forces_all_erasure width_large body_long
      body_head first_block (Or.inr middle_letters) target_shell.1 pole
    rcases survivors with impossible_eq | middle_eq
    · have middle_length_two : middle.length = 2 := by
        rw [impossible_eq]
        simp
      have middle_length_long : middle.length = width + 1 := by
        have lengths := congrArg List.length middle_letters
        simpa using lengths
      omega
    · exact Or.inr ⟨middle_eq, targetDepth_width⟩
  · obtain ⟨first_letters, middle_eq, targetDepth_width⟩ := singleton_b
    have target_singleton : ∃ letter, target = [.erase letter] := by
      rcases target_shell with ⟨target_block, target_single | target_multi⟩
      · obtain ⟨target_length, _⟩ := target_single
        obtain ⟨front, letter, target_eq⟩ := target_block
        have front_nil : front = [] := by
          apply List.eq_nil_of_length_eq_zero
          simpa [target_eq] using target_length
        subst front
        exact ⟨letter, target_eq⟩
      · obtain ⟨_, targetDepth_one⟩ := target_multi
        omega
    obtain ⟨targetLetter, target_eq⟩ := target_singleton
    subst middle
    subst target
    have forbidden_pole : False :=
      twoC_then_singletonB_avoids_singleton_pole width_large body first_letters targetLetter
        (by
          simpa [blockCoefficient_singleton,
            swappedLowerCode_singleton] using pole)
    exact False.elim forbidden_pole

end MatrixMortality.SwappedSetterMultitransfer
