import MatrixMortality.SwappedSetterDoubleDeletion

/-!
# Physical arithmetic shells for the swapped setter

Every physical role block ends in an erasure. Its swapped lower code is therefore a `3`-adic
unit. A multi-role block has upper and lower codes congruent to eight modulo nine, giving its
centered coefficient exact depth one; a singleton erasure has exact depth `width`. These facts
remove the abstract shell hypotheses from the first multi-transfer extinction theorem.
-/

namespace MatrixMortality.SwappedSetterMultitransfer

open MatrixMortality.PadicValuation

private theorem swappedLowerCode_roleBlock_mod_three
    (width : Nat) (body : List TagLetter) {block : List NearyTile}
    (role_block : IsRoleBlock block) :
    swappedLowerCode width body block ≡ 2 [ZMOD 3] := by
  obtain ⟨front, letter, rfl⟩ := role_block
  have last : spell (nearyLower width body) [.erase letter] = [false] := by
    cases letter <;> rfl
  rw [swappedLowerCode, spell_append, last, List.map_append, ternaryCode_append]
  norm_num [Int.ModEq, ternaryDigit]

private theorem not_dvd_three_of_mod_two {value : ℤ}
    (value_mod : value ≡ 2 [ZMOD 3]) : ¬(3 : ℤ) ∣ value := by
  intro divides
  have value_zero : value ≡ 0 [ZMOD 3] := divides.modEq_zero_int
  have two_zero : (2 : ℤ) ≡ 0 [ZMOD 3] := value_mod.symm.trans value_zero
  norm_num [Int.ModEq] at two_zero

/-- A physical role block's swapped lower code is a `3`-adic unit. -/
theorem roleBlock_lower_isUnit
    (width : Nat) (body : List TagLetter) {block : List NearyTile}
    (role_block : IsRoleBlock block) :
    IsUnit 3 (swappedLowerCode width body block : ℚ) :=
  intCast_isUnit_of_not_dvd <|
    not_dvd_three_of_mod_two <|
      swappedLowerCode_roleBlock_mod_three width body role_block

private theorem swappedUpperWord_suffix_two
    {width : Nat} (width_two : 2 ≤ width) (block : List NearyTile) :
    ∃ front,
      (spell (nearyUpper width) block ++ nearyMarker width).map not =
        front ++ [true, true] := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le width_two
  refine ⟨(spell (nearyUpper (2 + offset)) block).map not ++
    false :: List.replicate offset true, ?_⟩
  simp [nearyMarker, List.map_append, List.replicate_add, List.append_assoc,
    add_comm]

private theorem swappedUpperCode_mod_nine
    {width : Nat} (width_two : 2 ≤ width) (block : List NearyTile) :
    swappedUpperCode width block ≡ 8 [ZMOD 9] := by
  obtain ⟨front, word_eq⟩ := swappedUpperWord_suffix_two width_two block
  rw [swappedUpperCode, word_eq, ternaryCode_append]
  norm_num [Int.ModEq, ternaryCode, ternaryDigit, Nat.ofDigits]

private theorem nearyLower_suffix_false
    (width : Nat) (body : List TagLetter) (tile : NearyTile) :
    ∃ front, nearyLower width body tile = front ++ [false] := by
  cases tile with
  | rule letter =>
      cases letter with
      | b => exact ⟨[true, true], rfl⟩
      | c => exact ⟨[true] ++ tagEncode width body ++ [true], by simp [nearyLower]⟩
  | erase letter => exact ⟨[], by cases letter <;> rfl⟩

private theorem swappedLowerWord_suffix_two
    (width : Nat) (body : List TagLetter) {block : List NearyTile}
    (role_block : IsRoleBlock block) (block_multi : 2 ≤ block.length) :
    ∃ front,
      (spell (nearyLower width body) block).map not = front ++ [true, true] := by
  obtain ⟨roles, finalLetter, rfl⟩ := role_block
  have roles_nonempty : roles ≠ [] := by
    intro roles_empty
    subst roles
    simp at block_multi
  let previous := roles.getLast roles_nonempty
  have roles_eq : roles.dropLast ++ [previous] = roles :=
    List.dropLast_append_getLast roles_nonempty
  obtain ⟨previousFront, previous_eq⟩ :=
    nearyLower_suffix_false width body previous
  refine ⟨(spell (nearyLower width body) roles.dropLast).map not ++
    previousFront.map not, ?_⟩
  conv_lhs => rw [← roles_eq]
  rw [List.append_assoc, spell_append, spell_append]
  rw [show spell (nearyLower width body) [previous] =
      nearyLower width body previous by simp [spell],
    show spell (nearyLower width body) [.erase finalLetter] =
      nearyLower width body (.erase finalLetter) by simp [spell]]
  rw [previous_eq]
  cases finalLetter <;> simp [nearyLower, List.map_append, List.append_assoc]

private theorem swappedLowerCode_multi_mod_nine
    (width : Nat) (body : List TagLetter) {block : List NearyTile}
    (role_block : IsRoleBlock block) (block_multi : 2 ≤ block.length) :
    swappedLowerCode width body block ≡ 8 [ZMOD 9] := by
  obtain ⟨front, word_eq⟩ :=
    swappedLowerWord_suffix_two width body role_block block_multi
  rw [swappedLowerCode, word_eq, ternaryCode_append]
  norm_num [Int.ModEq, ternaryCode, ternaryDigit, Nat.ofDigits]

private theorem widthScale_mod_nine {width : Nat} (width_two : 2 ≤ width) :
    widthScale width ≡ 0 [ZMOD 9] := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le width_two
  simpa [widthScale, pow_add, mul_comm] using
    (Int.ModEq.refl ((3 : ℤ) ^ offset)).mul
      (by norm_num : (9 : ℤ) ≡ 0 [ZMOD 9])

private theorem centeredCoefficient_mod_nine
    {width : Nat} (width_two : 2 ≤ width) :
    centeredCoefficient width ≡ 2 [ZMOD 9] := by
  simpa [centeredCoefficient] using
    (Int.ModEq.refl (2 : ℤ)).sub (widthScale_mod_nine width_two)

private theorem terminalDiscrepancy_mod_nine
    {width : Nat} (width_two : 2 ≤ width) :
    terminalDiscrepancy width ≡ 8 [ZMOD 9] := by
  have raw :=
    ((Int.ModEq.refl (5 : ℤ)).mul (widthScale_mod_nine width_two)).sub
      (Int.ModEq.refl (1 : ℤ))
  exact raw.trans (by norm_num)

private theorem blockCoefficient_multi_mod_nine
    {width : Nat} (width_two : 2 ≤ width) (body : List TagLetter)
    {block : List NearyTile} (role_block : IsRoleBlock block)
    (block_multi : 2 ≤ block.length) :
    blockCoefficient width body block ≡ 6 [ZMOD 9] := by
  have raw :=
    ((centeredCoefficient_mod_nine width_two).mul
      (swappedUpperCode_mod_nine width_two block)).sub
      ((terminalDiscrepancy_mod_nine width_two).mul
        (swappedLowerCode_multi_mod_nine width body role_block block_multi))
  simpa [blockCoefficient] using raw.trans
    (by norm_num : (2 * 8 - 8 * 8 : ℤ) ≡ 6 [ZMOD 9])

private theorem intCast_hasValue_one_of_mod_six {value : ℤ}
    (value_mod : value ≡ 6 [ZMOD 9]) :
    HasValue 3 (value : ℚ) 1 := by
  obtain ⟨quotient, quotient_eq⟩ := value_mod.dvd
  have value_eq : value = 3 * (2 - 3 * quotient) := by omega
  have unit_not_dvd : ¬(3 : ℤ) ∣ 2 - 3 * quotient := by
    intro divides
    obtain ⟨factor, factor_eq⟩ := divides
    omega
  rw [value_eq]
  push_cast
  simpa using mul_hasValue (primePower_hasValue (prime := 3) 1)
    (intCast_isUnit_of_not_dvd unit_not_dvd)

/-- A physical multi-role block's centered coefficient has exact `3`-adic depth one. -/
theorem roleBlock_multi_coefficient_hasValue
    {width : Nat} (width_two : 2 ≤ width) (body : List TagLetter)
    {block : List NearyTile} (role_block : IsRoleBlock block)
    (block_multi : 2 ≤ block.length) :
    HasValue 3 (blockCoefficient width body block : ℚ) 1 :=
  intCast_hasValue_one_of_mod_six <|
    blockCoefficient_multi_mod_nine width_two body role_block block_multi

private theorem terminalDiscrepancy_mod_three
    {width : Nat} (width_two : 2 ≤ width) :
    terminalDiscrepancy width ≡ 2 [ZMOD 3] := by
  have reduced := (terminalDiscrepancy_mod_nine width_two).of_dvd
    (by norm_num : (3 : ℤ) ∣ 9)
  exact reduced.trans (by norm_num)

private theorem singletonBCofactor_mod_three
    {width : Nat} (width_two : 2 ≤ width) :
    singletonBCofactor width ≡ 2 [ZMOD 3] := by
  have scale_mod := (widthScale_mod_nine width_two).of_dvd
    (by norm_num : (3 : ℤ) ∣ 9)
  have square_mod := scale_mod.mul scale_mod
  have raw :=
    (((Int.ModEq.refl (18 : ℤ)).mul square_mod).sub
      ((Int.ModEq.refl (40 : ℤ)).mul scale_mod)).add
        (Int.ModEq.refl (17 : ℤ))
  simpa [singletonBCofactor, pow_two] using raw.trans (by norm_num)

/-- Either physical singleton erasure's centered coefficient has exact depth `width`. -/
theorem singleton_coefficient_hasValue
    {width : Nat} (width_two : 2 ≤ width) (body : List TagLetter)
    (letter : TagLetter) :
    HasValue 3 (blockCoefficient width body [.erase letter] : ℚ) width := by
  have scale_value : HasValue 3 (widthScale width : ℚ) width := by
    simpa [widthScale] using primePower_hasValue (prime := 3) width
  cases letter with
  | b =>
      have cofactor_unit : IsUnit 3 (singletonBCofactor width : ℚ) :=
        intCast_isUnit_of_not_dvd <|
          not_dvd_three_of_mod_two <| singletonBCofactor_mod_three width_two
      rw [blockCoefficient_singleton]
      simpa [singletonCoefficient] using
        neg_hasValue (mul_hasValue scale_value cofactor_unit)
  | c =>
      have terminal_unit : IsUnit 3 (terminalDiscrepancy width : ℚ) :=
        intCast_isUnit_of_not_dvd <|
          not_dvd_three_of_mod_two <| terminalDiscrepancy_mod_three width_two
      rw [blockCoefficient_singleton]
      simpa [singletonCoefficient] using
        neg_hasValue (mul_hasValue scale_value terminal_unit)

/-- Every physical role block carries its expected pole shell, exact coefficient depth, and
lower-code unit. -/
theorem roleBlock_arithmeticShell
    {width : Nat} (width_two : 2 ≤ width) (body : List TagLetter)
    {block : List NearyTile} (role_block : IsRoleBlock block) :
    ∃ depth : Nat,
      HasPoleShell width block depth ∧
        HasValue 3 (blockCoefficient width body block : ℚ) depth ∧
        IsUnit 3 (swappedLowerCode width body block : ℚ) := by
  have block_nonempty : block ≠ [] := by
    obtain ⟨front, letter, block_eq⟩ := role_block
    simp [block_eq]
  have block_pos : 0 < block.length := List.length_pos_of_ne_nil block_nonempty
  by_cases singleton : block.length = 1
  · obtain ⟨front, letter, block_eq⟩ := role_block
    have front_nil : front = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa [block_eq] using singleton
    subst front
    simp only [List.nil_append] at block_eq
    subst block
    have singleton_role : IsRoleBlock [.erase letter] := ⟨[], letter, rfl⟩
    exact ⟨width, ⟨singleton_role, Or.inl ⟨by simp, rfl⟩⟩,
      singleton_coefficient_hasValue width_two body letter,
      roleBlock_lower_isUnit width body singleton_role⟩
  · have block_multi : 2 ≤ block.length := by omega
    exact ⟨1, ⟨role_block, Or.inr ⟨block_multi, rfl⟩⟩,
      roleBlock_multi_coefficient_hasValue width_two body role_block block_multi,
      roleBlock_lower_isUnit width body role_block⟩

private theorem block_length_le_upperLength (width : Nat) (block : List NearyTile) :
    block.length ≤ upperLength width block := by
  induction block with
  | nil => rfl
  | cons tile block induction =>
      have tile_length : 0 < (nearyUpper width tile).length :=
        List.length_pos_of_ne_nil (nearyUpper_ne_nil width tile)
      change (tile :: block).length ≤
        (nearyUpper width tile ++ spell (nearyUpper width) block).length
      change block.length ≤ (spell (nearyUpper width) block).length at induction
      simp only [List.length_cons, List.length_append]
      omega

/-- Any physical first block other than the literal distinguished transfer `D_c` has upper
length greater than one. -/
theorem roleBlock_one_lt_upperLength_of_ne_singleton_c
    {width : Nat} {block : List NearyTile}
    (role_block : IsRoleBlock block) (block_ne : block ≠ [.erase .c]) :
    1 < upperLength width block := by
  have block_nonempty : block ≠ [] := by
    obtain ⟨front, letter, block_eq⟩ := role_block
    simp [block_eq]
  by_cases singleton : block.length = 1
  · obtain ⟨front, letter, block_eq⟩ := role_block
    have front_nil : front = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa [block_eq] using singleton
    subst front
    simp only [List.nil_append] at block_eq
    subst block
    cases letter with
    | c => contradiction
    | b => simp [upperLength_singleton_erase_b]
  · have block_multi : 2 ≤ block.length := by
      have block_pos : 0 < block.length := List.length_pos_of_ne_nil block_nonempty
      omega
    exact lt_of_lt_of_le block_multi (block_length_le_upperLength width block)

/-- Physical role blocks supply every arithmetic shell needed by the first multi-transfer
extinction theorem. The only excluded first block is the distinguished singleton `D_c`. -/
theorem physicalFirstMultiTransfer_pole_false
    {width : Nat} (width_large : 6 ≤ width)
    {body : List TagLetter}
    (body_long : width - 1 ≤ body.length)
    (body_head : body.head? = some .b)
    {first middle target : List NearyTile}
    (first_block : IsRoleBlock first)
    (first_ne : first ≠ [.erase .c])
    (middle_block : IsRoleBlock middle)
    (target_block : IsRoleBlock target)
    (pole :
      (blockCoefficient width body target : ℚ) *
          nextY (blockCoefficient width body middle) (centeredCoupling width)
            (swappedLowerCode width body middle) ((3 : ℚ) ^ upperLength width first)
            (centeredCoefficient width * swappedUpperCode width first) +
        centeredCoupling width * swappedLowerCode width body target *
          nextX (3 ^ upperLength width middle)
            (centeredCoefficient width * swappedUpperCode width first) = 0) : False := by
  obtain ⟨middleDepth, middle_shell, middle_coefficient, middle_lower⟩ :=
    roleBlock_arithmeticShell (show 2 ≤ width by omega) body middle_block
  obtain ⟨targetDepth, target_shell, target_coefficient, target_lower⟩ :=
    roleBlock_arithmeticShell (show 2 ≤ width by omega) body target_block
  exact firstMultiTransfer_pole_false width_large body_long body_head first_block
    middle_shell target_shell
    (roleBlock_one_lt_upperLength_of_ne_singleton_c first_block first_ne)
    rfl middle_coefficient middle_lower target_coefficient target_lower pole

end MatrixMortality.SwappedSetterMultitransfer
