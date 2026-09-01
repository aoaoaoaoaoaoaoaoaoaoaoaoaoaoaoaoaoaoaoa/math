import MatrixMortality.DecimalSetterPositioned

/-!
# Decimal setter phase-toggle shells

Erasing every phase of a Neary role word preserves its upper spelling. Factoring at the
rightmost rule leaves an exact lower-code perturbation whose joint decimal shell depends only
on whether zero, one, or at least two roles precede that rule. The same trichotomy passes to the
distinguished raw residual through the unit factor `G(H−10μ)`. In particular, a leading
`R_c D_c⁺` block has the same prospective shell as its all-erasure companion and is impossible.
-/

namespace MatrixMortality.DecimalSetterPhase

open MatrixMortality.DecimalSetterArithmetic
open MatrixMortality.DecimalSetterAncestry
open MatrixMortality.DecimalSetterCarry
open MatrixMortality.DecimalSetterChamber
open MatrixMortality.DecimalSetterDepth
open MatrixMortality.PadicValuation

private instance factPrimeFive : Fact (Nat.Prime 5) :=
  ⟨by norm_num⟩

private theorem two_hasDecimalShell : HasDecimalShell (2 : ℚ) 1 0 := by
  refine ⟨?_, intCast_isUnit_of_not_dvd (by norm_num)⟩
  simpa using (primePower_hasValue (prime := 2) 1)

private theorem five_hasDecimalShell : HasDecimalShell (5 : ℚ) 0 1 := by
  refine ⟨intCast_isUnit_of_not_dvd (by norm_num), ?_⟩
  simpa using (primePower_hasValue (prime := 5) 1)

private theorem modEq_fiveHundredFifty_hasDecimalShell
    {value : ℤ} (value_mod : value ≡ 550 [ZMOD 1000]) :
    HasDecimalShell (value : ℚ) 1 2 := by
  rw [Int.modEq_iff_dvd] at value_mod
  obtain ⟨carry, carry_eq⟩ := value_mod
  have value_eq : value = 50 * (11 - 20 * carry) := by omega
  have unit_shell : HasDecimalShell ((11 - 20 * carry : ℤ) : ℚ) 0 0 := by
    refine ⟨intCast_isUnit_of_not_dvd ?_, intCast_isUnit_of_not_dvd ?_⟩
    · rintro ⟨quotient, quotient_eq⟩
      omega
    · rintro ⟨quotient, quotient_eq⟩
      omega
  have fifty_shell : HasDecimalShell (50 : ℚ) 1 2 := by
    convert ten_hasDecimalShell.mul five_hasDecimalShell using 1 <;> norm_num
  rw [value_eq, Int.cast_mul]
  simpa using fifty_shell.mul unit_shell

private theorem modEq_sevenHundredEighty_hasDecimalShell
    {value : ℤ} (value_mod : value ≡ 780 [ZMOD 1000]) :
    HasDecimalShell (value : ℚ) 2 1 := by
  rw [Int.modEq_iff_dvd] at value_mod
  obtain ⟨carry, carry_eq⟩ := value_mod
  have value_eq : value = 20 * (39 - 50 * carry) := by omega
  have unit_shell : HasDecimalShell ((39 - 50 * carry : ℤ) : ℚ) 0 0 := by
    refine ⟨intCast_isUnit_of_not_dvd ?_, intCast_isUnit_of_not_dvd ?_⟩
    · rintro ⟨quotient, quotient_eq⟩
      omega
    · rintro ⟨quotient, quotient_eq⟩
      omega
  have twenty_shell : HasDecimalShell (20 : ℚ) 2 1 := by
    convert two_hasDecimalShell.mul ten_hasDecimalShell using 1 <;> norm_num
  rw [value_eq, Int.cast_mul]
  simpa using twenty_shell.mul unit_shell

private theorem modEq_fourHundredEighty_hasValue_five
    {value : ℤ} (value_mod : value ≡ 480 [ZMOD 1000]) :
    HasValue 5 (value : ℚ) 1 := by
  rw [Int.modEq_iff_dvd] at value_mod
  obtain ⟨carry, carry_eq⟩ := value_mod
  have value_eq : value = 5 * (96 - 200 * carry) := by omega
  have unit_shell : HasValue 5 ((96 - 200 * carry : ℤ) : ℚ) 0 := by
    apply intCast_isUnit_of_not_dvd
    rintro ⟨quotient, quotient_eq⟩
    omega
  rw [value_eq, Int.cast_mul]
  simpa using mul_hasValue five_hasDecimalShell.2 unit_shell

private theorem count_b_replicate_c (width : Nat) :
    (List.replicate width TagLetter.c).count TagLetter.b = 0 := by
  induction width with
  | zero => rfl
  | succ width induction =>
      rw [List.replicate_succ]
      simpa using induction

/-- The calibrated decimal lift is a unit at both two and five. -/
theorem calibratedLift_decimalUnit
    {β : Nat} {G : ℤ} (β_positive : 1 ≤ β)
    (lift_eq : G = 502 * 10 ^ β - 7) :
    HasDecimalShell (G : ℚ) 0 0 := by
  have rho_mod : (10 : ℤ) ^ β ≡ 0 [ZMOD 10] := by
    rw [Int.modEq_zero_iff_dvd]
    simpa using pow_dvd_pow (10 : ℤ) β_positive
  have lift_mod : G ≡ 3 [ZMOD 10] := by
    calc
      G = 502 * 10 ^ β - 7 := lift_eq
      _ ≡ 502 * 0 - 7 [ZMOD 10] :=
        (Int.ModEq.refl 502).mul rho_mod |>.sub (Int.ModEq.refl 7)
      _ ≡ 3 [ZMOD 10] := by norm_num
  exact intCast_hasDecimalShell_of_mod_three lift_mod

/-- Subtracting the built-in decimal term from a lawful two-`c` raw head preserves decimal
unit depth. -/
theorem peeledDoubleCHead_sub_tenMarker_decimalUnit
    {β : Nat} (headTail : List TagLetter) (μ : ℤ) (β_positive : 1 ≤ β)
    (head_unit :
      HasDecimalShell (code (peeledHeadWord β (.c :: .c :: headTail)) : ℚ) 0 0) :
    HasDecimalShell
      (((code (peeledHeadWord β (.c :: .c :: headTail)) : ℤ) - 10 * μ : ℤ) : ℚ)
      0 0 := by
  obtain ⟨suffix, suffix_positive, _, head_eq, _⟩ :=
    peeledDoubleCHead_unit_shape headTail β_positive head_unit
  obtain ⟨suffixRest, suffix_eq⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : suffix ≠ 0)
  have word_eq :
      peeledHeadWord β (.c :: .c :: headTail) =
        (List.replicate (β + 2 - suffix) true ++
          List.replicate suffixRest false) ++ [false] := by
    rw [head_eq, suffix_eq, List.replicate_succ']
    simp only [List.append_assoc]
  have head_mod :
      (code (peeledHeadWord β (.c :: .c :: headTail)) : ℤ) ≡ 7 [ZMOD 10] := by
    rw [word_eq]
    exact code_append_false_mod_ten _
  have decimal_mod : (10 * μ : ℤ) ≡ 0 [ZMOD 10] := by
    rw [Int.modEq_zero_iff_dvd]
    exact dvd_mul_right 10 μ
  have difference_mod :
      (code (peeledHeadWord β (.c :: .c :: headTail)) : ℤ) - 10 * μ ≡
        7 [ZMOD 10] := by
    simpa using head_mod.sub decimal_mod
  exact intCast_hasDecimalShell_of_mod_seven difference_mod

/-- If a phase perturbation is deeper than a prospective equal shell at both primes, the
phase-erased companion inherits that equal shell. -/
theorem companion_hasDecimalShell_of_phaseToggle_deeper
    {left right : ℚ} {depth twoDepth fiveDepth : ℤ}
    (left_shell : HasDecimalShell left depth depth)
    (difference_shell : HasDecimalShell (left - right) twoDepth fiveDepth)
    (two_deeper : depth < twoDepth) (five_deeper : depth < fiveDepth) :
    HasDecimalShell right depth depth := by
  have opposite_shell :
      HasDecimalShell (-(left - right)) twoDepth fiveDepth :=
    ⟨neg_hasValue difference_shell.1, neg_hasValue difference_shell.2⟩
  rw [show right = -(left - right) + left by ring]
  exact
    ⟨add_hasValue_right opposite_shell.1 left_shell.1 two_deeper,
      add_hasValue_right opposite_shell.2 left_shell.2 five_deeper⟩

/-- If a phase perturbation is shallower than a prospective equal shell at both primes, the
phase-erased companion inherits the perturbation's unequal shell. -/
theorem companion_hasDecimalShell_of_phaseToggle_shallower
    {left right : ℚ} {depth twoDepth fiveDepth : ℤ}
    (left_shell : HasDecimalShell left depth depth)
    (difference_shell : HasDecimalShell (left - right) twoDepth fiveDepth)
    (two_shallower : twoDepth < depth) (five_shallower : fiveDepth < depth) :
    HasDecimalShell right twoDepth fiveDepth := by
  have opposite_shell :
      HasDecimalShell (-(left - right)) twoDepth fiveDepth :=
    ⟨neg_hasValue difference_shell.1, neg_hasValue difference_shell.2⟩
  rw [show right = -(left - right) + left by ring]
  exact
    ⟨add_hasValue_left opposite_shell.1 left_shell.1 two_shallower,
      add_hasValue_left opposite_shell.2 left_shell.2 five_shallower⟩

/-- Replace either phase of a Neary tile by its erasure phase. -/
def erasePhaseTile : NearyTile → NearyTile
  | .rule letter | .erase letter => .erase letter

@[simp] theorem erasePhaseTile_letter (tile : NearyTile) :
    (erasePhaseTile tile).letter = tile.letter := by
  cases tile <;> rfl

@[simp] theorem nearyUpper_erasePhaseTile (β : Nat) (tile : NearyTile) :
    nearyUpper β (erasePhaseTile tile) = nearyUpper β tile := by
  cases tile <;> rfl

/-- Erasing every phase preserves the complete Neary upper spelling. -/
theorem spell_erasePhase_upper (β : Nat) (roles : List NearyTile) :
    spell (nearyUpper β) (roles.map erasePhaseTile) =
      spell (nearyUpper β) roles := by
  induction roles with
  | nil => rfl
  | cons role roles induction =>
      change nearyUpper β (erasePhaseTile role) ++
          spell (nearyUpper β) (roles.map erasePhaseTile) =
        nearyUpper β role ++ spell (nearyUpper β) roles
      rw [nearyUpper_erasePhaseTile, induction]

@[simp] theorem nearyLower_erasePhaseTile
    (β : Nat) (body : List TagLetter) (tile : NearyTile) :
    nearyLower β body (erasePhaseTile tile) = [false] := by
  cases tile <;> rfl

@[simp] theorem spell_erasePhase_lower
    (β : Nat) (body : List TagLetter) (roles : List NearyTile) :
    spell (nearyLower β body) (roles.map erasePhaseTile) =
      List.replicate roles.length false := by
  induction roles with
  | nil => rfl
  | cons role roles induction =>
      cases role <;>
        change false :: spell (nearyLower β body) (roles.map erasePhaseTile) =
          List.replicate (roles.length + 1) false <;>
        rw [List.replicate_succ, induction]

@[simp] theorem spell_eraseTail_lower
    (β : Nat) (body tail : List TagLetter) :
    spell (nearyLower β body) (tail.map NearyTile.erase) =
      List.replicate tail.length false := by
  induction tail with
  | nil => rfl
  | cons letter tail induction =>
      change false :: spell (nearyLower β body) (tail.map NearyTile.erase) =
        false :: List.replicate tail.length false
      exact congrArg (false :: ·) induction

private theorem leading_tagEncode_eq_append_true (β : Nat) (body : List TagLetter) :
    ∃ stem, true :: tagEncode β body = stem ++ [true] := by
  induction body using List.reverseRecOn with
  | nil => exact ⟨[], rfl⟩
  | append_singleton body letter _ =>
      rw [tagEncode_append]
      cases letter
      · refine ⟨true :: tagEncode β body ++
          (true :: List.replicate β false), ?_⟩
        simp [tagCode]
      · refine ⟨true :: tagEncode β body, ?_⟩
        simp [tagCode]

private theorem ruleLower_eq_append_557
    (β : Nat) (body : List TagLetter) (letter : TagLetter) :
    ∃ stem, nearyLower β body (.rule letter) =
      stem ++ [true, true, false] := by
  cases letter with
  | b => exact ⟨[], rfl⟩
  | c =>
      obtain ⟨stem, stem_eq⟩ := leading_tagEncode_eq_append_true β body
      refine ⟨stem, ?_⟩
      simp [nearyLower, stem_eq, List.append_assoc]

private theorem code_ruleTerminated_mod_thousand
    (β : Nat) (body : List TagLetter) (front : List NearyTile) (letter : TagLetter) :
    (code
      (spell (nearyLower β body) front ++
        nearyLower β body (.rule letter)) : ℤ) ≡ 557 [ZMOD 1000] := by
  obtain ⟨stem, rule_eq⟩ := ruleLower_eq_append_557 β body letter
  rw [rule_eq, ← List.append_assoc, code_append]
  norm_num [code, digit, Nat.ofDigits]

private theorem code_replicateFalse_mod_thousand
    {width : Nat} (width_large : 3 ≤ width) :
    (code (List.replicate width false) : ℤ) ≡ 777 [ZMOD 1000] := by
  obtain ⟨stemWidth, width_eq⟩ := Nat.exists_eq_add_of_le width_large
  have width_eq' : width = stemWidth + 3 := by omega
  rw [width_eq', List.replicate_add, code_append]
  norm_num [code, digit, Nat.ofDigits, List.replicate]

private theorem intCode_append_sub_eq
    (left right suffix : List Bool) :
    (code (left ++ suffix) : ℤ) - code (right ++ suffix) =
      ((code left : ℤ) - code right) * 10 ^ suffix.length := by
  rw [code_append, code_append]
  push_cast
  ring

/-- Coefficient left after removing the common all-erasure suffix following the rightmost rule.
The comparison word erases every phase while retaining every tag letter. -/
def rightmostRuleLowerCoefficient
    (β : Nat) (body : List TagLetter) (front : List NearyTile)
    (letter : TagLetter) : ℤ :=
  code
      (spell (nearyLower β body) front ++
        nearyLower β body (.rule letter)) -
    code
      (spell (nearyLower β body) (front.map erasePhaseTile) ++ [false])

theorem rightmostRuleLowerCoefficient_mod_thousand_of_prefix_nil
    (β : Nat) (body : List TagLetter) (letter : TagLetter) :
    rightmostRuleLowerCoefficient β body [] letter ≡ 550 [ZMOD 1000] := by
  have rule_mod := code_ruleTerminated_mod_thousand β body [] letter
  simpa [rightmostRuleLowerCoefficient, spell, code, digit, Nat.ofDigits] using
    rule_mod.sub (Int.ModEq.refl 7)

theorem rightmostRuleLowerCoefficient_mod_thousand_of_prefix_one
    (β : Nat) (body : List TagLetter) (prefixTile : NearyTile)
    (letter : TagLetter) :
    rightmostRuleLowerCoefficient β body [prefixTile] letter ≡ 480 [ZMOD 1000] := by
  have rule_mod := code_ruleTerminated_mod_thousand β body [prefixTile] letter
  simpa [rightmostRuleLowerCoefficient, spell, code, digit, Nat.ofDigits] using
    rule_mod.sub (Int.ModEq.refl 77)

/-- With one preceding role, the unfactored rightmost-rule coefficient is divisible by eight. -/
theorem eight_dvd_rightmostRuleLowerCoefficient_of_prefix_one
    (β : Nat) (body : List TagLetter) (frontTile : NearyTile)
    (letter : TagLetter) :
    (8 : ℤ) ∣ rightmostRuleLowerCoefficient β body [frontTile] letter := by
  have coefficient_mod := rightmostRuleLowerCoefficient_mod_thousand_of_prefix_one
    β body frontTile letter
  rw [Int.modEq_iff_dvd] at coefficient_mod
  obtain ⟨carry, carry_eq⟩ := coefficient_mod
  refine ⟨60 - 125 * carry, ?_⟩
  omega

theorem rightmostRuleLowerCoefficient_mod_thousand_of_two_le_prefix
    (β : Nat) (body : List TagLetter) (front : List NearyTile) (letter : TagLetter)
    (front_large : 2 ≤ front.length) :
    rightmostRuleLowerCoefficient β body front letter ≡ 780 [ZMOD 1000] := by
  have rule_mod := code_ruleTerminated_mod_thousand β body front letter
  have erase_mod :
      (code
        (spell (nearyLower β body) (front.map erasePhaseTile) ++ [false]) : ℤ) ≡
          777 [ZMOD 1000] := by
    rw [spell_erasePhase_lower]
    have length_large : 3 ≤ front.length + 1 := by omega
    simpa [List.replicate_succ'] using
      code_replicateFalse_mod_thousand length_large
  dsimp only [rightmostRuleLowerCoefficient]
  exact rule_mod.sub erase_mod

theorem rightmostRuleLowerCode_sub_eq
    (β : Nat) (body : List TagLetter) (front : List NearyTile)
    (letter : TagLetter) (tail : List TagLetter) :
    (code
        (spell (nearyLower β body)
          (front ++ .rule letter :: tail.map NearyTile.erase)) : ℤ) -
      code
        (spell (nearyLower β body)
          (front.map erasePhaseTile ++
            .erase letter :: tail.map NearyTile.erase)) =
      rightmostRuleLowerCoefficient β body front letter * 10 ^ tail.length := by
  rw [spell_append, spell_append]
  rw [show spell (nearyLower β body) (.rule letter :: tail.map NearyTile.erase) =
      nearyLower β body (.rule letter) ++
        spell (nearyLower β body) (tail.map NearyTile.erase) by rfl]
  rw [show spell (nearyLower β body) (.erase letter :: tail.map NearyTile.erase) =
      [false] ++ spell (nearyLower β body) (tail.map NearyTile.erase) by rfl]
  rw [← List.append_assoc, ← List.append_assoc]
  rw [spell_eraseTail_lower]
  simpa only [rightmostRuleLowerCoefficient, List.length_replicate] using
    intCode_append_sub_eq
      (spell (nearyLower β body) front ++ nearyLower β body (.rule letter))
      (spell (nearyLower β body) (front.map erasePhaseTile) ++ [false])
      (List.replicate tail.length false)

/-- If the rightmost rule is the first tile, its lower-code perturbation has exact shell
`(|tail|+1,|tail|+2)`. -/
theorem rightmostRuleLowerCode_sub_hasDecimalShell_of_front_nil
    (β : Nat) (body : List TagLetter) (letter : TagLetter) (tail : List TagLetter) :
    HasDecimalShell
      (((code
          (spell (nearyLower β body)
            (.rule letter :: tail.map NearyTile.erase)) : ℤ) -
        code
          (spell (nearyLower β body)
            (.erase letter :: tail.map NearyTile.erase)) : ℤ) : ℚ)
      (tail.length + 1) (tail.length + 2) := by
  have coefficient_shell := modEq_fiveHundredFifty_hasDecimalShell
    (rightmostRuleLowerCoefficient_mod_thousand_of_prefix_nil β body letter)
  have scale_shell := ten_hasDecimalShell.pow tail.length
  have product_shell := coefficient_shell.mul scale_shell
  have difference_eq := rightmostRuleLowerCode_sub_eq β body [] letter tail
  rw [show ([] : List NearyTile) ++ .rule letter :: tail.map NearyTile.erase =
      .rule letter :: tail.map NearyTile.erase by rfl] at difference_eq
  rw [show List.map erasePhaseTile ([] : List NearyTile) ++
      .erase letter :: tail.map NearyTile.erase =
        .erase letter :: tail.map NearyTile.erase by rfl] at difference_eq
  rw [difference_eq]
  push_cast
  convert product_shell using 1
  · omega
  · omega

/-- If at least two tiles precede the rightmost rule, its lower-code perturbation has exact
shell `(|tail|+2,|tail|+1)`. -/
theorem rightmostRuleLowerCode_sub_hasDecimalShell_of_two_le_front
    (β : Nat) (body : List TagLetter) (front : List NearyTile)
    (letter : TagLetter) (tail : List TagLetter) (front_large : 2 ≤ front.length) :
    HasDecimalShell
      (((code
          (spell (nearyLower β body)
            (front ++ .rule letter :: tail.map NearyTile.erase)) : ℤ) -
        code
          (spell (nearyLower β body)
            (front.map erasePhaseTile ++
              .erase letter :: tail.map NearyTile.erase)) : ℤ) : ℚ)
      (tail.length + 2) (tail.length + 1) := by
  have coefficient_shell := modEq_sevenHundredEighty_hasDecimalShell
    (rightmostRuleLowerCoefficient_mod_thousand_of_two_le_prefix
      β body front letter front_large)
  have scale_shell := ten_hasDecimalShell.pow tail.length
  have product_shell := coefficient_shell.mul scale_shell
  rw [rightmostRuleLowerCode_sub_eq]
  push_cast
  convert product_shell using 1 <;> omega

/-- With exactly one preceding tile, the rightmost-rule perturbation has exact five-adic depth
`|tail|+1`; the two-adic depth is at least `|tail|+3`. -/
theorem rightmostRuleLowerCode_sub_hasValue_five_of_front_one
    (β : Nat) (body : List TagLetter) (frontTile : NearyTile)
    (letter : TagLetter) (tail : List TagLetter) :
    HasValue 5
      (((code
          (spell (nearyLower β body)
            (frontTile :: .rule letter :: tail.map NearyTile.erase)) : ℤ) -
        code
          (spell (nearyLower β body)
            (erasePhaseTile frontTile ::
              .erase letter :: tail.map NearyTile.erase)) : ℤ) : ℚ)
      (tail.length + 1) := by
  have coefficient_shell := modEq_fourHundredEighty_hasValue_five
    (rightmostRuleLowerCoefficient_mod_thousand_of_prefix_one
      β body frontTile letter)
  have scale_shell := (ten_hasDecimalShell.pow tail.length).2
  have product_shell := mul_hasValue coefficient_shell scale_shell
  have difference_eq := rightmostRuleLowerCode_sub_eq
    β body [frontTile] letter tail
  rw [show [frontTile] ++ .rule letter :: tail.map NearyTile.erase =
      frontTile :: .rule letter :: tail.map NearyTile.erase by rfl] at difference_eq
  rw [show List.map erasePhaseTile [frontTile] ++
      .erase letter :: tail.map NearyTile.erase =
        erasePhaseTile frontTile :: .erase letter :: tail.map NearyTile.erase by rfl]
    at difference_eq
  rw [difference_eq]
  push_cast
  convert product_shell using 1
  omega

/-- With exactly one preceding tile, the rightmost-rule lower perturbation is divisible by
`2^(|tail|+3)`. -/
theorem twoPower_dvd_rightmostRuleLowerCode_sub_of_front_one
    (β : Nat) (body : List TagLetter) (frontTile : NearyTile)
    (letter : TagLetter) (tail : List TagLetter) :
    (2 : ℤ) ^ (tail.length + 3) ∣
      (code
          (spell (nearyLower β body)
            (frontTile :: .rule letter :: tail.map NearyTile.erase)) : ℤ) -
        code
          (spell (nearyLower β body)
            (erasePhaseTile frontTile ::
              .erase letter :: tail.map NearyTile.erase)) := by
  obtain ⟨coefficient, coefficient_eq⟩ :=
    eight_dvd_rightmostRuleLowerCoefficient_of_prefix_one
      β body frontTile letter
  have difference_eq := rightmostRuleLowerCode_sub_eq
    β body [frontTile] letter tail
  rw [show [frontTile] ++ .rule letter :: tail.map NearyTile.erase =
      frontTile :: .rule letter :: tail.map NearyTile.erase by rfl] at difference_eq
  rw [show List.map erasePhaseTile [frontTile] ++
      .erase letter :: tail.map NearyTile.erase =
        erasePhaseTile frontTile :: .erase letter :: tail.map NearyTile.erase by rfl]
    at difference_eq
  rw [difference_eq, coefficient_eq]
  obtain ⟨tenQuotient, ten_eq⟩ : (2 : ℤ) ^ tail.length ∣ 10 ^ tail.length :=
    pow_dvd_pow_of_dvd (by norm_num : (2 : ℤ) ∣ 10) tail.length
  refine ⟨coefficient * tenQuotient, ?_⟩
  rw [pow_add, show (2 : ℤ) ^ 3 = 8 by norm_num, ten_eq]
  ring

/-- Changing only the lower code of a raw entry block changes its peeled residual by the
carrier-unit factor `G(H−10μ)`. -/
theorem peeledNumerator_sameUpper_sub
    (H μ E G P V₁ V₂ : ℤ) :
    peeledNumerator H 1 μ G (transferTrace E G P V₁) V₁ -
        peeledNumerator H 1 μ G (transferTrace E G P V₂) V₂ =
      G * (H - 10 * μ) * (V₁ - V₂) := by
  simp only [peeledNumerator, transferTrace]
  ring

/-- Decimal-unit calibration factors preserve the exact phase-toggle shell in the raw entry
residual. -/
theorem peeledNumerator_sameUpper_sub_hasDecimalShell
    {H μ E G P V₁ V₂ : ℤ} {twoDepth fiveDepth : ℤ}
    (lift_unit : HasDecimalShell (G : ℚ) 0 0)
    (head_gap_unit : HasDecimalShell ((H - 10 * μ : ℤ) : ℚ) 0 0)
    (lower_difference_shell :
      HasDecimalShell (((V₁ - V₂ : ℤ) : ℚ)) twoDepth fiveDepth) :
    HasDecimalShell
      ((peeledNumerator H 1 μ G (transferTrace E G P V₁) V₁ -
        peeledNumerator H 1 μ G (transferTrace E G P V₂) V₂ : ℤ) : ℚ)
      twoDepth fiveDepth := by
  rw [peeledNumerator_sameUpper_sub]
  push_cast
  simpa using (lift_unit.mul head_gap_unit).mul lower_difference_shell

/-- The exact five-adic phase-toggle depth likewise survives the calibrated raw residual. -/
theorem peeledNumerator_sameUpper_sub_hasValue_five
    {H μ E G P V₁ V₂ : ℤ} {fiveDepth : ℤ}
    (lift_unit : HasValue 5 (G : ℚ) 0)
    (head_gap_unit : HasValue 5 ((H - 10 * μ : ℤ) : ℚ) 0)
    (lower_difference_shell : HasValue 5 (((V₁ - V₂ : ℤ) : ℚ)) fiveDepth) :
    HasValue 5
      ((peeledNumerator H 1 μ G (transferTrace E G P V₁) V₁ -
        peeledNumerator H 1 μ G (transferTrace E G P V₂) V₂ : ℤ) : ℚ)
      fiveDepth := by
  rw [peeledNumerator_sameUpper_sub]
  push_cast
  simpa using mul_hasValue (mul_hasValue lift_unit head_gap_unit)
    lower_difference_shell

/-- A rule-`c` followed only by `D_c` erasures cannot be the first non-singleton block from the
distinguished decimal raw head. Its phase perturbation is deeper than the prospective pole, so
the forbidden all-erasure companion would have the same shell. -/
theorem leadingRuleC_rawHead_multi_shell_impossible
    {β tailWidth : Nat} (body headTail : List TagLetter) {μ E G : ℤ}
    (β_large : 2 ≤ β) (tail_nonempty : 1 ≤ tailWidth)
    (head_unit :
      HasDecimalShell (code (peeledHeadWord β (.c :: .c :: headTail)) : ℚ) 0 0)
    (mu_eq : 9 * μ = 52 * 10 ^ β - 7)
    (gap_eq : E = 18 * 10 ^ β - 63)
    (lift_eq : G = 502 * 10 ^ β - 7)
    (shell :
      HasDecimalShell
        (((code (peeledHeadWord β (.c :: .c :: headTail)) : ℤ) *
          (E * code (punctuatedUpper β (List.replicate (tailWidth + 1) .c)) +
            G * code
              (spell (nearyLower β body)
                (.rule .c :: List.replicate tailWidth (.erase .c)))) -
          10 * μ * G * code
            (spell (nearyLower β body)
              (.rule .c :: List.replicate tailWidth (.erase .c))) : ℤ) : ℚ)
        tailWidth tailWidth) :
    False := by
  let letters : List TagLetter := List.replicate (tailWidth + 1) .c
  let tail : List TagLetter := List.replicate tailWidth .c
  let H : ℤ := code (peeledHeadWord β (.c :: .c :: headTail))
  let P : ℤ := code (punctuatedUpper β letters)
  let VRule : ℤ := code
    (spell (nearyLower β body) (.rule .c :: tail.map NearyTile.erase))
  let VErase : ℤ := letterEraseLowerCode β body letters
  have rule_shell :
      HasDecimalShell
        ((peeledNumerator H 1 μ G (transferTrace E G P VRule) VRule : ℤ) : ℚ)
        tailWidth tailWidth := by
    simpa [H, P, VRule, letters, tail, peeledNumerator, transferTrace,
      List.map_replicate] using shell
  have lower_difference_shell :
      HasDecimalShell (((VRule - VErase : ℤ) : ℚ))
        (tailWidth + 1) (tailWidth + 2) := by
    have raw := rightmostRuleLowerCode_sub_hasDecimalShell_of_front_nil
      β body TagLetter.c tail
    simpa [VRule, VErase, letters, tail, letterEraseLowerCode, letterEraseBlock,
      List.map_replicate, List.replicate_succ] using raw
  have lift_unit := calibratedLift_decimalUnit (G := G) (by omega) lift_eq
  have head_gap_unit := peeledDoubleCHead_sub_tenMarker_decimalUnit
    headTail μ (by omega) head_unit
  have residual_difference_shell :
      HasDecimalShell
        ((peeledNumerator H 1 μ G (transferTrace E G P VRule) VRule -
          peeledNumerator H 1 μ G (transferTrace E G P VErase) VErase : ℤ) : ℚ)
        (tailWidth + 1) (tailWidth + 2) :=
    peeledNumerator_sameUpper_sub_hasDecimalShell
      lift_unit (by simpa only [H] using head_gap_unit) lower_difference_shell
  have erase_shell :
      HasDecimalShell
        ((peeledNumerator H 1 μ G (transferTrace E G P VErase) VErase : ℤ) : ℚ)
        tailWidth tailWidth := by
    have residual_difference_shell' :
        HasDecimalShell
          (((peeledNumerator H 1 μ G (transferTrace E G P VRule) VRule : ℤ) : ℚ) -
            ((peeledNumerator H 1 μ G (transferTrace E G P VErase) VErase : ℤ) : ℚ))
          (tailWidth + 1) (tailWidth + 2) := by
      simpa only [Int.cast_sub] using residual_difference_shell
    exact companion_hasDecimalShell_of_phaseToggle_deeper rule_shell residual_difference_shell'
      (by omega) (by omega)
  have multi_role : 2 ≤ letters.length := by
    simp only [letters, List.length_replicate]
    omega
  have depth_eq : (tagEncode β letters).length - 1 = tailWidth := by
    rw [tagEncode_length_eq_roleLength_add_markerCount]
    rw [show letters.length = tailWidth + 1 by simp [letters],
      show letters.count .b = 0 by exact count_b_replicate_c (tailWidth + 1)]
    omega
  apply letterErase_rawHead_multi_shell_impossible body headTail letters
    β_large multi_role head_unit mu_eq gap_eq lift_eq
  simpa [H, P, VErase, peeledNumerator, transferTrace, depth_eq] using erase_shell

end MatrixMortality.DecimalSetterPhase
