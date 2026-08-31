import MatrixMortality.SwappedSetterAllErasure

/-!
# Double-deletion extinction for the swapped setter

The last expected-shell first multi-transfer survivor is the literal middle block `D_c²`.
Its normalized pole equation forces the following physical lower-to-upper code ratio into
`(2/3,3/4)`. Nonzero ternary length and prefix chambers exclude that interval for every role
block emitted against a compiler body beginning in `b`. This closes the entire first
multi-transfer front.
-/

namespace MatrixMortality.SwappedSetterMultitransfer

private theorem firstMismatch_upper
    {width : Nat} (width_pos : 0 < width) (first : List NearyTile) :
    firstMismatch width first < 1 := by
  obtain ⟨first_lower, _⟩ := swappedUpperCode_cylinder width_pos first
  have scale_pos : (0 : ℤ) < widthScale width := by simp [widthScale]
  have power_pos : (0 : ℤ) < upperPower width first := by simp [upperPower]
  have first_pos_int : (0 : ℤ) < swappedUpperCode width first :=
    lt_of_lt_of_le (mul_pos scale_pos power_pos) first_lower
  have first_pos : (0 : ℚ) < swappedUpperCode width first := by
    exact_mod_cast first_pos_int
  have lower_rat :
      (widthScale width : ℚ) * upperPower width first ≤
        swappedUpperCode width first := by
    exact_mod_cast first_lower
  have marker_lt :
      (setterMarker width : ℚ) < 2 * widthScale width := by
    rw [setterMarker]
    push_cast
    linarith
  rw [firstMismatch]
  apply (div_lt_iff₀ first_pos).2
  nlinarith [mul_lt_mul_of_pos_right marker_lt
    (show (0 : ℚ) < upperPower width first by exact_mod_cast power_pos)]

private theorem firstMismatch_lower
    {width : Nat} (width_pos : 0 < width) (first : List NearyTile) :
    -(1 / (2 * widthScale width : ℚ)) < firstMismatch width first := by
  obtain ⟨_, first_upper⟩ := swappedUpperCode_cylinder width_pos first
  have scale_pos : (0 : ℤ) < widthScale width := by simp [widthScale]
  have power_pos : (0 : ℤ) < upperPower width first := by simp [upperPower]
  have first_pos_int : (0 : ℤ) < swappedUpperCode width first := by
    have lower := (swappedUpperCode_cylinder width_pos first).1
    exact lt_of_lt_of_le (mul_pos scale_pos power_pos) lower
  have first_pos : (0 : ℚ) < swappedUpperCode width first := by
    exact_mod_cast first_pos_int
  have upper_rat :
      (swappedUpperCode width first : ℚ) <
        2 * widthScale width * upperPower width first := by
    exact_mod_cast first_upper
  have scale_pos_rat : (0 : ℚ) < widthScale width := by exact_mod_cast scale_pos
  have power_pos_rat : (0 : ℚ) < upperPower width first := by exact_mod_cast power_pos
  rw [firstMismatch, show -(1 / (2 * widthScale width : ℚ)) =
    (-1) / (2 * widthScale width) by ring]
  apply (div_lt_div_iff₀ (mul_pos (by norm_num) scale_pos_rat) first_pos).2
  rw [setterMarker]
  push_cast
  have scale_one_int : (1 : ℤ) ≤ widthScale width := by
    exact one_le_pow₀ (by norm_num)
  have scale_one : (1 : ℚ) ≤ widthScale width := by exact_mod_cast scale_one_int
  have marker_pos : (0 : ℚ) < 2 * widthScale width - 1 := by linarith
  have scaled := mul_lt_mul_of_pos_left upper_rat marker_pos
  nlinarith

/-- Exact normalized discrepancy of the literal `D_c²` transfer. -/
theorem allDeletionC_double_transferDiscrepancy
    {width : Nat} (width_large : 3 ≤ width) (body : List TagLetter)
    (first : List NearyTile) :
    transferDiscrepancy width body first [.erase .c, .erase .c] =
      (14 * widthScale width - 1) / 3 -
        8 * terminalDiscrepancy width * firstMismatch width first /
          (3 * (widthScale width - 2)) := by
  have discrepancy_eq := transferDiscrepancy_eq width_large body first
    [.erase .c, .erase .c]
  have upper_eq := swappedUpperCode_double_c
    (width := width) (block := [.erase .c, .erase .c]) (by rfl)
  have lower_eq := allDeletionC_lowerCode width body 2
  have lower_eq' :
      swappedLowerCode width body [.erase .c, .erase .c] = 8 := by
    simpa using lower_eq
  rw [upperLength_double_c (width := width) (block := [.erase .c, .erase .c]) (by rfl),
    upper_eq, lower_eq'] at discrepancy_eq
  norm_num at discrepancy_eq ⊢
  rw [discrepancy_eq]
  ring

private theorem doubleDiscrepancy_ratio_thresholds
    {width : Nat} (width_large : 6 ≤ width) (body : List TagLetter)
    (first : List NearyTile) :
    6 * terminalDiscrepancy width * setterMarker width /
          (3 * (widthScale width - 2) + 2 * terminalDiscrepancy width) <
        transferDiscrepancy width body first [.erase .c, .erase .c] ∧
      transferDiscrepancy width body first [.erase .c, .erase .c] <
        9 * terminalDiscrepancy width * setterMarker width /
          (4 * (widthScale width - 2) + 3 * terminalDiscrepancy width) := by
  have scale_ge_nat : 3 ^ 6 ≤ 3 ^ width :=
    Nat.pow_le_pow_right (by norm_num) width_large
  have scale_ge_int : (729 : ℤ) ≤ widthScale width := by
    have casted : ((3 ^ 6 : Nat) : ℤ) ≤ ((3 ^ width : Nat) : ℤ) := by
      exact_mod_cast scale_ge_nat
    simpa [widthScale] using casted
  have scale_ge : (729 : ℚ) ≤ widthScale width := by exact_mod_cast scale_ge_int
  have scale_pos : (0 : ℚ) < widthScale width := by linarith
  have difference_pos : (0 : ℚ) < (widthScale width : ℚ) - 2 := by linarith
  have terminal_pos : (0 : ℚ) < terminalDiscrepancy width := by
    rw [terminalDiscrepancy]
    push_cast
    linarith
  have marker_pos : (0 : ℚ) < setterMarker width := by
    rw [setterMarker]
    push_cast
    linarith
  have mismatch_upper := firstMismatch_upper (show 0 < width by omega) first
  have mismatch_lower := firstMismatch_lower (show 0 < width by omega) first
  have discrepancy_eq := allDeletionC_double_transferDiscrepancy
    (show 3 ≤ width by omega) body first
  have discrepancy_lower :
      (14 * (widthScale width : ℚ) - 1) / 3 -
          8 * terminalDiscrepancy width /
            (3 * (widthScale width - 2)) <
        transferDiscrepancy width body first [.erase .c, .erase .c] := by
    rw [discrepancy_eq]
    have coefficient_pos :
        (0 : ℚ) < 8 * terminalDiscrepancy width /
          (3 * (widthScale width - 2)) := by positivity
    have scaled := mul_lt_mul_of_pos_left mismatch_upper coefficient_pos
    have product_eq :
        8 * terminalDiscrepancy width * firstMismatch width first /
              (3 * (widthScale width - 2)) =
            (8 * terminalDiscrepancy width /
              (3 * (widthScale width - 2))) * firstMismatch width first := by ring
    rw [product_eq]
    nlinarith
  have discrepancy_upper :
      transferDiscrepancy width body first [.erase .c, .erase .c] <
        (14 * (widthScale width : ℚ) - 1) / 3 +
          4 * terminalDiscrepancy width /
            (3 * widthScale width * (widthScale width - 2)) := by
    rw [discrepancy_eq]
    have coefficient_pos :
        (0 : ℚ) < 8 * terminalDiscrepancy width /
          (3 * (widthScale width - 2)) := by positivity
    have scaled := mul_lt_mul_of_pos_left mismatch_lower coefficient_pos
    have product_eq :
        8 * terminalDiscrepancy width * firstMismatch width first /
              (3 * (widthScale width - 2)) =
            (8 * terminalDiscrepancy width /
              (3 * (widthScale width - 2))) * firstMismatch width first := by ring
    rw [product_eq]
    have lower_fraction_eq :
        (8 * terminalDiscrepancy width /
            (3 * (widthScale width - 2))) *
              (-(1 / (2 * widthScale width : ℚ))) =
          -(4 * terminalDiscrepancy width /
            (3 * widthScale width * (widthScale width - 2))) := by
      field_simp [ne_of_gt scale_pos, ne_of_gt difference_pos]
      norm_num
    rw [lower_fraction_eq] at scaled
    nlinarith
  constructor
  · have arithmetic :
        6 * terminalDiscrepancy width * setterMarker width /
              (3 * (widthScale width - 2) + 2 * terminalDiscrepancy width) <
            (14 * (widthScale width : ℚ) - 1) / 3 -
              8 * terminalDiscrepancy width /
                (3 * (widthScale width - 2)) := by
      rw [terminalDiscrepancy, setterMarker]
      push_cast
      have left_denominator_pos :
          (0 : ℚ) < 3 * ((widthScale width : ℚ) - 2) +
            2 * (5 * widthScale width - 1) := by linarith
      have lower_denominator_pos :
          (0 : ℚ) < 3 * ((widthScale width : ℚ) - 2) := by positivity
      have lower_formula :
          (14 * (widthScale width : ℚ) - 1) / 3 -
                8 * (5 * widthScale width - 1) /
                  (3 * (widthScale width - 2)) =
            (((widthScale width : ℚ) - 2) *
                (14 * widthScale width - 1) -
              8 * (5 * widthScale width - 1)) /
                (3 * (widthScale width - 2)) := by
        field_simp [ne_of_gt difference_pos]
      rw [lower_formula]
      apply (div_lt_div_iff₀ left_denominator_pos lower_denominator_pos).2
      have shifted_pos :
          (0 : ℚ) <
            2 * ((widthScale width : ℚ) - 729) ^ 3 +
              3851 * ((widthScale width : ℚ) - 729) ^ 2 +
              2426524 * ((widthScale width : ℚ) - 729) + 497197639 := by
        positivity
      nlinarith [shifted_pos]
    calc
      6 * terminalDiscrepancy width * setterMarker width /
            (3 * (widthScale width - 2) + 2 * terminalDiscrepancy width) <
          (14 * (widthScale width : ℚ) - 1) / 3 -
            8 * terminalDiscrepancy width /
              (3 * (widthScale width - 2)) := arithmetic
      _ < transferDiscrepancy width body first [.erase .c, .erase .c] := discrepancy_lower
  · have arithmetic :
        (14 * (widthScale width : ℚ) - 1) / 3 +
              4 * terminalDiscrepancy width /
                (3 * widthScale width * (widthScale width - 2)) <
            9 * terminalDiscrepancy width * setterMarker width /
              (4 * (widthScale width - 2) + 3 * terminalDiscrepancy width) := by
      rw [terminalDiscrepancy, setterMarker]
      push_cast
      have right_denominator_pos :
          (0 : ℚ) < 4 * ((widthScale width : ℚ) - 2) +
            3 * (5 * widthScale width - 1) := by linarith
      have upper_denominator_pos :
          (0 : ℚ) < 3 * widthScale width * ((widthScale width : ℚ) - 2) := by
        positivity
      have upper_formula :
          (14 * (widthScale width : ℚ) - 1) / 3 +
                4 * (5 * widthScale width - 1) /
                  (3 * widthScale width * (widthScale width - 2)) =
            ((widthScale width : ℚ) * (widthScale width - 2) *
                (14 * widthScale width - 1) +
              4 * (5 * widthScale width - 1)) /
                (3 * widthScale width * (widthScale width - 2)) := by
        field_simp [ne_of_gt scale_pos, ne_of_gt difference_pos]
      rw [upper_formula]
      apply (div_lt_div_iff₀ upper_denominator_pos right_denominator_pos).2
      have shifted_pos :
          (0 : ℚ) <
            4 * ((widthScale width : ℚ) - 729) ^ 4 +
              11640 * ((widthScale width : ℚ) - 729) ^ 3 +
              12701764 * ((widthScale width : ℚ) - 729) ^ 2 +
              6159980280 * ((widthScale width : ℚ) - 729) + 1120243808188 := by
        positivity
      nlinarith [shifted_pos]
    calc
      transferDiscrepancy width body first [.erase .c, .erase .c] <
          (14 * (widthScale width : ℚ) - 1) / 3 +
            4 * terminalDiscrepancy width /
              (3 * widthScale width * (widthScale width - 2)) := discrepancy_upper
      _ < 9 * terminalDiscrepancy width * setterMarker width /
            (4 * (widthScale width - 2) + 3 * terminalDiscrepancy width) := arithmetic

private theorem swappedLowerCode_pos
    (width : Nat) (body : List TagLetter) {block : List NearyTile}
    (block_nonempty : block ≠ []) :
    (0 : ℤ) < swappedLowerCode width body block := by
  let lowerWord := (spell (nearyLower width body) block).map not
  have lower_nonempty : lowerWord ≠ [] := by
    cases block with
    | nil => contradiction
    | cons tile rest =>
        intro lower_nil
        have mapped_nil :
            List.map not
                (nearyLower width body tile ++ spell (nearyLower width body) rest) = [] := by
          simpa [lowerWord, spell] using lower_nil
        have spelling_nil :
            nearyLower width body tile ++ spell (nearyLower width body) rest = [] :=
          List.map_eq_nil_iff.mp mapped_nil
        exact nearyLower_ne_nil width body tile (List.append_eq_nil_iff.mp spelling_nil).1
  have code_bound := ternaryCode_lower_bound lowerWord lower_nonempty
  have code_pos : 0 < ternaryCode lowerWord :=
    lt_of_lt_of_le (pow_pos (by norm_num) (lowerWord.length - 1)) code_bound
  rw [swappedLowerCode]
  change (0 : ℤ) < (ternaryCode lowerWord : ℤ)
  exact_mod_cast code_pos

/-- A `D_c²` transfer followed by a physical pole forces the target code ratio into
the open chamber `(2/3,3/4)`. -/
theorem doubleDeletion_pole_targetRatio
    {width : Nat} (width_large : 6 ≤ width) (body : List TagLetter)
    (first : List NearyTile) {target : List NearyTile}
    (target_nonempty : target ≠ [])
    (pole :
      (blockCoefficient width body target : ℚ) *
          nextY (blockCoefficient width body [.erase .c, .erase .c])
            (centeredCoupling width)
            (swappedLowerCode width body [.erase .c, .erase .c])
            (upperPower width first)
            (centeredCoefficient width * swappedUpperCode width first) +
        centeredCoupling width * swappedLowerCode width body target *
          nextX (3 ^ upperLength width [.erase .c, .erase .c])
            (centeredCoefficient width * swappedUpperCode width first) = 0) :
    (2 / 3 : ℚ) <
          swappedLowerCode width body target / swappedUpperCode width target ∧
      (swappedLowerCode width body target : ℚ) /
          swappedUpperCode width target < 3 / 4 := by
  have width_pos : 0 < width := by omega
  have scale_ge_nat : 3 ^ 6 ≤ 3 ^ width :=
    Nat.pow_le_pow_right (by norm_num) width_large
  have scale_ge_int : (729 : ℤ) ≤ widthScale width := by
    have casted : ((3 ^ 6 : Nat) : ℤ) ≤ ((3 ^ width : Nat) : ℤ) := by
      exact_mod_cast scale_ge_nat
    simpa [widthScale] using casted
  have scale_ge : (729 : ℚ) ≤ widthScale width := by exact_mod_cast scale_ge_int
  have difference_pos : (0 : ℚ) < (widthScale width : ℚ) - 2 := by linarith
  have terminal_pos : (0 : ℚ) < terminalDiscrepancy width := by
    rw [terminalDiscrepancy]
    push_cast
    linarith
  have marker_pos : (0 : ℚ) < setterMarker width := by
    rw [setterMarker]
    push_cast
    linarith
  have target_upper_lower := (swappedUpperCode_cylinder width_pos target).1
  have target_upper_pos_int : (0 : ℤ) < swappedUpperCode width target := by
    exact lt_of_lt_of_le
      (mul_pos (show (0 : ℤ) < widthScale width by simp [widthScale])
        (show (0 : ℤ) < upperPower width target by simp [upperPower]))
      target_upper_lower
  have target_upper_pos : (0 : ℚ) < swappedUpperCode width target := by
    exact_mod_cast target_upper_pos_int
  have target_lower_pos_int := swappedLowerCode_pos width body target_nonempty
  have target_lower_pos : (0 : ℚ) < swappedLowerCode width body target := by
    exact_mod_cast target_lower_pos_int
  have interval := transferDiscrepancy_pole_interval (show 3 ≤ width by omega)
    body first (middle := [.erase .c, .erase .c]) (by simp) target_nonempty pole
  have normalized := transferDiscrepancy_pole_equation (show 3 ≤ width by omega)
    body first (middle := [.erase .c, .erase .c]) (target := target) (by simp) pole
  rw [blockCoefficient] at normalized
  push_cast at normalized
  have pole_ratio :
      transferDiscrepancy width body first [.erase .c, .erase .c] *
            ((widthScale width : ℚ) - 2) * swappedUpperCode width target =
        terminalDiscrepancy width *
          (3 * setterMarker width -
            transferDiscrepancy width body first [.erase .c, .erase .c]) *
          swappedLowerCode width body target := by
    rw [centeredCoefficient] at normalized
    push_cast at normalized
    linarith
  have right_factor_pos :
      (0 : ℚ) < terminalDiscrepancy width *
        (3 * setterMarker width -
          transferDiscrepancy width body first [.erase .c, .erase .c]) :=
    mul_pos terminal_pos (sub_pos.mpr interval.2)
  have ratio_eq :
      (swappedLowerCode width body target : ℚ) / swappedUpperCode width target =
        (transferDiscrepancy width body first [.erase .c, .erase .c] *
            ((widthScale width : ℚ) - 2)) /
          (terminalDiscrepancy width *
            (3 * setterMarker width -
              transferDiscrepancy width body first [.erase .c, .erase .c])) := by
    apply (div_eq_div_iff (ne_of_gt target_upper_pos) (ne_of_gt right_factor_pos)).2
    linarith
  obtain ⟨threshold_lower, threshold_upper⟩ :=
    doubleDiscrepancy_ratio_thresholds width_large body first
  constructor
  · rw [ratio_eq]
    apply (div_lt_div_iff₀ (by norm_num : (0 : ℚ) < 3) right_factor_pos).2
    have threshold_denominator_pos :
        (0 : ℚ) < 3 * ((widthScale width : ℚ) - 2) +
          2 * terminalDiscrepancy width := by positivity
    have threshold_cross :=
      (div_lt_iff₀ threshold_denominator_pos).mp threshold_lower
    nlinarith [mul_pos terminal_pos marker_pos]
  · rw [ratio_eq]
    apply (div_lt_div_iff₀ right_factor_pos (by norm_num : (0 : ℚ) < 4)).2
    have threshold_denominator_pos :
        (0 : ℚ) < 4 * ((widthScale width : ℚ) - 2) +
          3 * terminalDiscrepancy width := by positivity
    have threshold_cross :=
      (lt_div_iff₀ threshold_denominator_pos).mp threshold_upper
    nlinarith [mul_pos terminal_pos marker_pos]


private def upperWord (width : Nat) (block : List NearyTile) : List Bool :=
  (spell (nearyUpper width) block ++ nearyMarker width).map not

private def lowerWord (width : Nat) (body : List TagLetter)
    (block : List NearyTile) : List Bool :=
  (spell (nearyLower width body) block).map not

@[simp] private theorem upperWord_length (width : Nat) (block : List NearyTile) :
    (upperWord width block).length = upperLength width block + width + 1 := by
  simp [upperWord, upperLength, nearyMarker]
  omega

@[simp] private theorem lowerWord_length (width : Nat) (body : List TagLetter)
    (block : List NearyTile) :
    (lowerWord width body block).length =
      (spell (nearyLower width body) block).length := by
  simp [lowerWord]

private theorem upperWord_cons (width : Nat) (tile : NearyTile)
    (rest : List NearyTile) :
    upperWord width (tile :: rest) =
      (tagCode width tile.letter).map not ++ upperWord width rest := by
  rw [upperWord, upperWord, spell_nearyUpper, spell_nearyUpper]
  simp only [List.map_cons, tagEncode_cons]
  rw [List.append_assoc, List.map_append]

private theorem lowerWord_cons (width : Nat) (body : List TagLetter)
    (tile : NearyTile) (rest : List NearyTile) :
    lowerWord width body (tile :: rest) =
      (nearyLower width body tile).map not ++ lowerWord width body rest := by
  simp [lowerWord, spell, List.map_append]

private theorem upperWord_starts_false (width : Nat) (block : List NearyTile) :
    ∃ tail, upperWord width block = false :: tail := by
  cases block with
  | nil =>
      exact ⟨List.replicate width true, by simp [upperWord, spell, nearyMarker]⟩
  | cons tile rest =>
      cases tile <;> cases ‹TagLetter› <;>
        simp [upperWord_cons, NearyTile.letter, tagCode]

private theorem upperWord_cons_b_prefix_two
    {width : Nat} (width_pos : 0 < width) {tile : NearyTile}
    (tile_b : tile.letter = .b) (rest : List NearyTile) :
    ∃ tail, upperWord width (tile :: rest) = false :: true :: tail := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt width_pos)
  refine ⟨List.replicate offset true ++ false :: upperWord offset.succ rest, ?_⟩
  rw [upperWord_cons, tile_b]
  simp [tagCode, List.replicate_succ]

private theorem upperWord_cons_b_prefix_three
    {width : Nat} (width_two : 2 ≤ width) {tile : NearyTile}
    (tile_b : tile.letter = .b) (rest : List NearyTile) :
    ∃ tail, upperWord width (tile :: rest) = false :: true :: true :: tail := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le width_two
  refine ⟨List.replicate offset true ++ false :: upperWord (2 + offset) rest, ?_⟩
  rw [upperWord_cons, tile_b]
  simp [tagCode, List.replicate_add]

private theorem upperWord_cons_c_prefix_two
    {width : Nat} {tile : NearyTile} (tile_c : tile.letter = .c)
    (rest : List NearyTile) :
    ∃ tail, upperWord width (tile :: rest) = false :: false :: tail := by
  obtain ⟨tail, rest_eq⟩ := upperWord_starts_false width rest
  refine ⟨tail, ?_⟩
  rw [upperWord_cons, tile_c, rest_eq]
  rfl

private theorem lowerWord_cons_erase_prefix
    (width : Nat) (body : List TagLetter) (letter : TagLetter)
    (rest : List NearyTile) :
    ∃ tail, lowerWord width body (.erase letter :: rest) = true :: tail := by
  exact ⟨lowerWord width body rest, by simp [lowerWord_cons, nearyLower]⟩

private theorem lowerWord_cons_rule_b_prefix
    (width : Nat) (body : List TagLetter) (rest : List NearyTile) :
    ∃ tail,
      lowerWord width body (.rule .b :: rest) = false :: false :: true :: tail := by
  exact ⟨lowerWord width body rest, by simp [lowerWord_cons, nearyLower]⟩

private theorem lowerWord_cons_rule_c_prefix
    {width : Nat} (width_pos : 0 < width) {body : List TagLetter}
    (body_head : body.head? = some .b) (rest : List NearyTile) :
    ∃ tail,
      lowerWord width body (.rule .c :: rest) = false :: false :: true :: tail := by
  cases body with
  | nil => simp at body_head
  | cons letter bodyTail =>
      simp only [List.head?_cons, Option.some.injEq] at body_head
      subst letter
      obtain ⟨offset, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt width_pos)
      refine ⟨List.replicate offset true ++
        false :: (tagEncode offset.succ bodyTail ++ [true, false]).map not ++
          lowerWord offset.succ (.b :: bodyTail) rest, ?_⟩
      simp [lowerWord_cons, nearyLower, tagEncode_cons, tagCode,
        List.replicate_succ, List.map_append]

private theorem code_equal_false_true (upperTail lowerTail : List Bool)
    (length_eq : (false :: upperTail).length = (true :: lowerTail).length) :
    3 * ternaryCode (false :: upperTail) <
      4 * ternaryCode (true :: lowerTail) := by
  simp only [List.length_cons, Nat.succ.injEq] at length_eq
  have upper_bound := ternaryCode_lt_pow_length upperTail
  have power_pos : 0 < 3 ^ lowerTail.length := pow_pos (by omega) _
  have upper_eq :
      ternaryCode (false :: upperTail) =
        3 ^ upperTail.length + ternaryCode upperTail := by
    rw [ternaryCode_cons]
    simp only [ternaryDigit, mul_one]
  have lower_eq :
      ternaryCode (true :: lowerTail) =
        2 * 3 ^ lowerTail.length + ternaryCode lowerTail := by
    rw [ternaryCode_cons]
    simp only [ternaryDigit]
    omega
  have power_eq : 3 ^ upperTail.length = 3 ^ lowerTail.length := by rw [length_eq]
  rw [upper_eq, lower_eq, power_eq]
  omega

private theorem code_adjacent_upper_twelve (upperTail lower : List Bool)
    (length_eq : (false :: true :: upperTail).length = lower.length + 1) :
    3 * ternaryCode lower <
      2 * ternaryCode (false :: true :: upperTail) := by
  have lower_length : lower.length = upperTail.length + 1 := by
    simp only [List.length_cons] at length_eq
    omega
  have lower_bound := ternaryCode_lt_pow_length lower
  rw [lower_length, pow_succ] at lower_bound
  have upper_power_pos : 0 < 3 ^ upperTail.length := pow_pos (by omega) _
  have upper_eq :
      ternaryCode (false :: true :: upperTail) =
        5 * 3 ^ upperTail.length + ternaryCode upperTail := by
    simp only [ternaryCode_cons, List.length_cons, ternaryDigit, pow_succ]
    ring
  rw [upper_eq]
  omega

private theorem code_equal_122_112 (upperTail lowerTail : List Bool)
    (length_eq :
      (false :: true :: true :: upperTail).length =
        (false :: false :: true :: lowerTail).length) :
    3 * ternaryCode (false :: true :: true :: upperTail) <
      4 * ternaryCode (false :: false :: true :: lowerTail) := by
  have tail_length : upperTail.length = lowerTail.length := by
    simp only [List.length_cons] at length_eq
    omega
  have upper_bound := ternaryCode_lt_pow_length upperTail
  have lower_power_pos : 0 < 3 ^ lowerTail.length := pow_pos (by omega) _
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
  have power_eq : 3 ^ upperTail.length = 3 ^ lowerTail.length := by rw [tail_length]
  rw [upper_eq, lower_eq, power_eq]
  omega

private theorem code_adjacent_11_112 (upperTail lowerTail : List Bool)
    (length_eq :
      (false :: false :: upperTail).length =
        (false :: false :: true :: lowerTail).length + 1) :
    3 * ternaryCode (false :: false :: true :: lowerTail) <
      2 * ternaryCode (false :: false :: upperTail) := by
  have tail_length : upperTail.length = lowerTail.length + 2 := by
    simp only [List.length_cons] at length_eq
    omega
  have lower_bound := ternaryCode_lt_pow_length lowerTail
  have lower_power_pos : 0 < 3 ^ lowerTail.length := pow_pos (by omega) _
  have upper_eq :
      ternaryCode (false :: false :: upperTail) =
        4 * 3 ^ upperTail.length + ternaryCode upperTail := by
    simp only [ternaryCode_cons, List.length_cons, ternaryDigit, pow_succ]
    ring
  have lower_eq :
      ternaryCode (false :: false :: true :: lowerTail) =
        14 * 3 ^ lowerTail.length + ternaryCode lowerTail := by
    simp only [ternaryCode_cons, List.length_cons, ternaryDigit, pow_succ]
    ring
  have power_eq : 3 ^ upperTail.length = 9 * 3 ^ lowerTail.length := by
    rw [tail_length, pow_add]
    norm_num
    ring
  rw [upper_eq, lower_eq, power_eq]
  omega

private theorem code_equal_11_112 (upperTail lowerTail : List Bool)
    (length_eq :
      (false :: false :: upperTail).length =
        (false :: false :: true :: lowerTail).length) :
    3 * ternaryCode (false :: false :: upperTail) <
      4 * ternaryCode (false :: false :: true :: lowerTail) := by
  have tail_length : upperTail.length = lowerTail.length + 1 := by
    simp only [List.length_cons] at length_eq
    omega
  have upper_bound := ternaryCode_lt_pow_length upperTail
  have lower_power_pos : 0 < 3 ^ lowerTail.length := pow_pos (by omega) _
  have upper_eq :
      ternaryCode (false :: false :: upperTail) =
        4 * 3 ^ upperTail.length + ternaryCode upperTail := by
    simp only [ternaryCode_cons, List.length_cons, ternaryDigit, pow_succ]
    ring
  have lower_eq :
      ternaryCode (false :: false :: true :: lowerTail) =
        14 * 3 ^ lowerTail.length + ternaryCode lowerTail := by
    simp only [ternaryCode_cons, List.length_cons, ternaryDigit, pow_succ]
    ring
  have power_eq : 3 ^ upperTail.length = 3 * 3 ^ lowerTail.length := by
    rw [tail_length, pow_succ]
    ring
  rw [upper_eq, lower_eq, power_eq]
  omega

private theorem adjacent_code_of_ends_erase
    {width : Nat} (width_pos : 0 < width) {body : List TagLetter}
    (body_head : body.head? = some .b) (front : List NearyTile)
    (finalLetter : TagLetter)
    (adjacent :
      (lowerWord width body (front ++ [.erase finalLetter])).length + 1 =
        (upperWord width (front ++ [.erase finalLetter])).length) :
    3 * ternaryCode (lowerWord width body (front ++ [.erase finalLetter])) <
      2 * ternaryCode (upperWord width (front ++ [.erase finalLetter])) := by
  revert adjacent
  induction front with
  | nil =>
      intro adjacent
      cases finalLetter <;>
        simp [upperWord, lowerWord, spell, nearyUpper, nearyLower, tagCode,
          nearyMarker] at adjacent <;>
        omega
  | cons tile front induction =>
      intro adjacent
      let tailBlock := front ++ [.erase finalLetter]
      change
        3 * ternaryCode (lowerWord width body (tile :: tailBlock)) <
          2 * ternaryCode (upperWord width (tile :: tailBlock))
      cases tile with
      | erase letter =>
          cases letter with
          | b =>
              obtain ⟨upperTail, upper_eq⟩ :=
                upperWord_cons_b_prefix_two width_pos
                  (tile := .erase .b) rfl tailBlock
              have length_eq :
                  (false :: true :: upperTail).length =
                    (lowerWord width body (.erase .b :: tailBlock)).length + 1 := by
                rw [← upper_eq]
                exact adjacent.symm
              rw [upper_eq]
              exact code_adjacent_upper_twelve upperTail _ length_eq
          | c =>
              have upper_eq :
                  upperWord width (.erase .c :: tailBlock) =
                    false :: upperWord width tailBlock := by
                simp [upperWord_cons, NearyTile.letter, tagCode]
              have lower_eq :
                  lowerWord width body (.erase .c :: tailBlock) =
                    true :: lowerWord width body tailBlock := by
                simp [lowerWord_cons, nearyLower]
              have tail_adjacent :
                  (lowerWord width body tailBlock).length + 1 =
                    (upperWord width tailBlock).length := by
                change
                  (lowerWord width body (.erase .c :: tailBlock)).length + 1 =
                    (upperWord width (.erase .c :: tailBlock)).length at adjacent
                rw [upper_eq, lower_eq] at adjacent
                simp only [List.length_cons] at adjacent
                omega
              have tail_cut := induction tail_adjacent
              change
                3 * ternaryCode (lowerWord width body tailBlock) <
                  2 * ternaryCode (upperWord width tailBlock) at tail_cut
              have power_eq :
                  3 ^ (upperWord width tailBlock).length =
                    3 * 3 ^ (lowerWord width body tailBlock).length := by
                rw [← tail_adjacent, pow_succ]
                ring
              change
                3 * ternaryCode (lowerWord width body (.erase .c :: tailBlock)) <
                  2 * ternaryCode (upperWord width (.erase .c :: tailBlock))
              rw [upper_eq, lower_eq, ternaryCode_cons, ternaryCode_cons]
              simp only [ternaryDigit, mul_one]
              rw [power_eq]
              omega
      | rule letter =>
          cases letter with
          | b =>
              obtain ⟨upperTail, upper_eq⟩ :=
                upperWord_cons_b_prefix_two width_pos
                  (tile := .rule .b) rfl tailBlock
              have length_eq :
                  (false :: true :: upperTail).length =
                    (lowerWord width body (.rule .b :: tailBlock)).length + 1 := by
                rw [← upper_eq]
                exact adjacent.symm
              rw [upper_eq]
              exact code_adjacent_upper_twelve upperTail _ length_eq
          | c =>
              obtain ⟨upperTail, upper_eq⟩ :=
                upperWord_cons_c_prefix_two (tile := .rule .c) rfl tailBlock
              obtain ⟨lowerTail, lower_eq⟩ :=
                lowerWord_cons_rule_c_prefix width_pos body_head tailBlock
              have length_eq :
                  (false :: false :: upperTail).length =
                    (false :: false :: true :: lowerTail).length + 1 := by
                rw [← upper_eq, ← lower_eq]
                exact adjacent.symm
              rw [upper_eq, lower_eq]
              exact code_adjacent_11_112 upperTail lowerTail length_eq

private theorem equal_code_of_nonempty
    {width : Nat} (width_two : 2 ≤ width) {body : List TagLetter}
    (body_head : body.head? = some .b) {block : List NearyTile}
    (block_nonempty : block ≠ [])
    (length_eq : (lowerWord width body block).length = (upperWord width block).length) :
    3 * ternaryCode (upperWord width block) <
      4 * ternaryCode (lowerWord width body block) := by
  have width_pos : 0 < width := lt_of_lt_of_le (by norm_num) width_two
  cases block with
  | nil => contradiction
  | cons tile rest =>
      cases tile with
      | erase letter =>
          obtain ⟨upperTail, upper_eq⟩ := upperWord_starts_false width (.erase letter :: rest)
          obtain ⟨lowerTail, lower_eq⟩ :=
            lowerWord_cons_erase_prefix width body letter rest
          have lengths :
              (false :: upperTail).length = (true :: lowerTail).length := by
            rw [← upper_eq, ← lower_eq]
            exact length_eq.symm
          rw [upper_eq, lower_eq]
          exact code_equal_false_true upperTail lowerTail lengths
      | rule letter =>
          cases letter with
          | b =>
              obtain ⟨upperTail, upper_eq⟩ :=
                upperWord_cons_b_prefix_three width_two
                  (tile := .rule .b) rfl rest
              obtain ⟨lowerTail, lower_eq⟩ :=
                lowerWord_cons_rule_b_prefix width body rest
              have lengths :
                  (false :: true :: true :: upperTail).length =
                    (false :: false :: true :: lowerTail).length := by
                rw [← upper_eq, ← lower_eq]
                exact length_eq.symm
              rw [upper_eq, lower_eq]
              exact code_equal_122_112 upperTail lowerTail lengths
          | c =>
              obtain ⟨upperTail, upper_eq⟩ :=
                upperWord_cons_c_prefix_two (tile := .rule .c) rfl rest
              obtain ⟨lowerTail, lower_eq⟩ :=
                lowerWord_cons_rule_c_prefix width_pos body_head rest
              have lengths :
                  (false :: false :: upperTail).length =
                    (false :: false :: true :: lowerTail).length := by
                rw [← upper_eq, ← lower_eq]
                exact length_eq.symm
              rw [upper_eq, lower_eq]
              exact code_equal_11_112 upperTail lowerTail lengths

private theorem ratio_length_dichotomy
    {upper lower : List Bool} (upper_nonempty : upper ≠ [])
    (lower_nonempty : lower ≠ [])
    (ratio_lower : 2 * ternaryCode upper < 3 * ternaryCode lower)
    (ratio_upper : 4 * ternaryCode lower < 3 * ternaryCode upper) :
    lower.length + 1 = upper.length ∨ lower.length = upper.length := by
  have upper_code_lower := ternaryCode_lower_bound upper upper_nonempty
  have upper_code_upper := ternaryCode_lt_pow_length upper
  have lower_code_lower := ternaryCode_lower_bound lower lower_nonempty
  have lower_code_upper := ternaryCode_lt_pow_length lower
  have lower_length_le : lower.length ≤ upper.length := by
    by_contra not_le
    have exponent_le : upper.length ≤ lower.length - 1 := by omega
    have power_le : 3 ^ upper.length ≤ 3 ^ (lower.length - 1) :=
      Nat.pow_le_pow_right (by norm_num) exponent_le
    omega
  have upper_length_le : upper.length ≤ lower.length + 1 := by
    by_contra not_le
    have exponent_le : lower.length + 1 ≤ upper.length - 1 := by omega
    have power_le : 3 ^ (lower.length + 1) ≤ 3 ^ (upper.length - 1) :=
      Nat.pow_le_pow_right (by norm_num) exponent_le
    have power_succ : 3 ^ (lower.length + 1) = 3 * 3 ^ lower.length := by
      rw [pow_succ]
      ring
    omega
  omega

/-- A physical swapped Neary role block never has lower-to-upper code ratio in
the open chamber `(2/3,3/4)` when the compiler body begins in `b`. -/
theorem roleBlock_avoids_middle_ratio
    {width : Nat} (width_two : 2 ≤ width) {body : List TagLetter}
    (body_head : body.head? = some .b) {target : List NearyTile}
    (target_block : IsRoleBlock target) :
    ¬ (2 / 3 < (swappedLowerCode width body target : ℚ) /
          swappedUpperCode width target ∧
        (swappedLowerCode width body target : ℚ) /
          swappedUpperCode width target < 3 / 4) := by
  intro ratio
  let upper := upperWord width target
  let lower := lowerWord width body target
  have target_nonempty : target ≠ [] := by
    obtain ⟨front, letter, target_eq⟩ := target_block
    simp [target_eq]
  have upper_nonempty : upper ≠ [] := by
    obtain ⟨tail, upper_eq⟩ := upperWord_starts_false width target
    simp [upper, upper_eq]
  have lower_nonempty : lower ≠ [] := by
    obtain ⟨front, letter, target_eq⟩ := target_block
    subst target
    intro lower_nil
    have mapped_nil :
        List.map not (spell (nearyLower width body) (front ++ [.erase letter])) = [] := by
      simpa [lower, lowerWord] using lower_nil
    have spelling_nil : spell (nearyLower width body) (front ++ [.erase letter]) = [] := by
      exact List.map_eq_nil_iff.mp mapped_nil
    have last_nonempty := nearyLower_ne_nil width body (.erase letter)
    rw [spell_append] at spelling_nil
    exact last_nonempty (List.append_eq_nil_iff.mp spelling_nil).2
  have upper_cast :
      (swappedUpperCode width target : ℚ) = ternaryCode upper := by
    simp only [swappedUpperCode, upper, upperWord]
    norm_num
  have lower_cast :
      (swappedLowerCode width body target : ℚ) = ternaryCode lower := by
    simp only [swappedLowerCode, lower, lowerWord]
    norm_num
  have upper_code_pos_nat : 0 < ternaryCode upper :=
    lt_of_lt_of_le (pow_pos (by norm_num) (upper.length - 1))
      (ternaryCode_lower_bound upper upper_nonempty)
  have upper_code_pos : (0 : ℚ) < ternaryCode upper := by exact_mod_cast upper_code_pos_nat
  rw [upper_cast, lower_cast] at ratio
  have ratio_lower_rat :
      2 * (ternaryCode upper : ℚ) < 3 * ternaryCode lower := by
    have crossed := (lt_div_iff₀ upper_code_pos).mp ratio.1
    linarith
  have ratio_upper_rat :
      4 * (ternaryCode lower : ℚ) < 3 * ternaryCode upper := by
    have crossed := (div_lt_iff₀ upper_code_pos).mp ratio.2
    linarith
  have ratio_lower_nat :
      2 * ternaryCode upper < 3 * ternaryCode lower := by
    exact_mod_cast ratio_lower_rat
  have ratio_upper_nat :
      4 * ternaryCode lower < 3 * ternaryCode upper := by
    exact_mod_cast ratio_upper_rat
  rcases ratio_length_dichotomy upper_nonempty lower_nonempty ratio_lower_nat
      ratio_upper_nat with adjacent | equal
  · obtain ⟨front, letter, target_eq⟩ := target_block
    subst target
    have forbidden := adjacent_code_of_ends_erase (show 0 < width by omega)
      body_head front letter <| by
        simpa [upper, lower] using adjacent
    change
      2 * ternaryCode (upperWord width (front ++ [.erase letter])) <
        3 * ternaryCode (lowerWord width body (front ++ [.erase letter])) at ratio_lower_nat
    omega
  · have forbidden := equal_code_of_nonempty width_two body_head target_nonempty <| by
      simpa [upper, lower] using equal
    change
      4 * ternaryCode (lowerWord width body target) <
        3 * ternaryCode (upperWord width target) at ratio_upper_nat
    omega

/-- The literal `D_c²` transfer cannot reach any physical swapped role pole. -/
theorem doubleDeletion_avoids_role_pole
    {width : Nat} (width_large : 6 ≤ width) {body : List TagLetter}
    (body_head : body.head? = some .b) (first : List NearyTile)
    {target : List NearyTile} (target_block : IsRoleBlock target)
    (pole :
      (blockCoefficient width body target : ℚ) *
          nextY (blockCoefficient width body [.erase .c, .erase .c])
            (centeredCoupling width)
            (swappedLowerCode width body [.erase .c, .erase .c])
            (upperPower width first)
            (centeredCoefficient width * swappedUpperCode width first) +
        centeredCoupling width * swappedLowerCode width body target *
          nextX (3 ^ upperLength width [.erase .c, .erase .c])
            (centeredCoefficient width * swappedUpperCode width first) = 0) : False := by
  have target_nonempty : target ≠ [] := by
    obtain ⟨front, letter, target_eq⟩ := target_block
    simp [target_eq]
  have target_ratio :=
    doubleDeletion_pole_targetRatio width_large body first target_nonempty pole
  exact roleBlock_avoids_middle_ratio (show 2 ≤ width by omega) body_head
    target_block target_ratio

/-- Under the compiler envelope, no expected-shell first multi-transfer pole exists. -/
theorem firstMultiTransfer_pole_false
    {width firstDepth middleDepth targetDepth : Nat}
    (width_large : 6 ≤ width)
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
            (centeredCoefficient width * swappedUpperCode width first) = 0) : False := by
  have survivor := firstMultiTransfer_pole_forces_doubleDeletion
    (show 3 ≤ width by omega) body_long body_head first_block middle_shell target_shell
    first_nontrivial firstDepth_eq middleCoefficient_shell middleLower_unit
    targetCoefficient_shell targetLower_unit pole
  obtain ⟨middle_eq, _target_depth⟩ := survivor
  subst middle
  exact doubleDeletion_avoids_role_pole width_large body_head first target_shell.1 <| by
    simpa [upperPower] using pole

end MatrixMortality.SwappedSetterMultitransfer
