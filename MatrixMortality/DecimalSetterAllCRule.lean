import MatrixMortality.DecimalSetterPositionTwo

/-!
# Complete decimal all-c rule extinction

After the position-two cut, the exact rightmost-rule grammar retains two later all-`c`
frontiers: erasure-tail width `h` at a regular raw head of final-seven width `h`, and width
`2β-2` at the exceptional head.  On either frontier, scaling the all-erasure companion and the
phase perturbation exposes equal-depth normalized coefficients whose sum is nonzero modulo
five.  The resulting depth lies strictly below the physical target because at least two roles
precede the rule.
-/

namespace MatrixMortality.DecimalSetterAllCRule

open MatrixMortality.DecimalSetterArithmetic
open MatrixMortality.DecimalSetterAncestry
open MatrixMortality.DecimalSetterCarry
open MatrixMortality.DecimalSetterChamber
open MatrixMortality.DecimalSetterDepth
open MatrixMortality.DecimalSetterPhase
open MatrixMortality.DecimalSetterPositionTwo
open MatrixMortality.DecimalSetterRuleCoefficient
open MatrixMortality.DecimalSetterRuleResonance
open MatrixMortality.PadicValuation

private theorem twoPower_mul_not_five_dvd
    (depth : Nat) {coefficient : ℤ} (coefficient_unit : ¬(5 : ℤ) ∣ coefficient) :
    ¬(5 : ℤ) ∣ 2 ^ depth * coefficient := by
  intro product_dvd
  have coprime : IsCoprime (5 : ℤ) (2 ^ depth) :=
    (by norm_num : IsCoprime (5 : ℤ) 2).pow_right
  exact coefficient_unit (coprime.dvd_of_dvd_mul_left product_dvd)

/-- Neither exact later all-`c` frontier left by S56 can reach its physical pole shell. -/
theorem laterAllCRightmostRule_rawHead_shell_impossible
    {β suffix tailWidth : Nat} (body headTail : List TagLetter) (front : List NearyTile)
    {μ E G : ℤ}
    (β_large : 2 ≤ β)
    (front_large : 2 ≤ front.length)
    (front_all_c : front.map NearyTile.letter = List.replicate front.length .c)
    (suffix_positive : 1 ≤ suffix)
    (head_eq :
      9 * (code (peeledHeadWord β (.c :: .c :: headTail)) : ℤ) =
        5 * 10 ^ (β + 2) + 2 * 10 ^ suffix - 7)
    (frontier :
      (suffix + 2 ≤ β ∧ tailWidth = suffix) ∨
        (suffix = β - 1 ∧ tailWidth = 2 * β - 2))
    (mu_eq : 9 * μ = 52 * 10 ^ β - 7)
    (gap_eq : E = 18 * 10 ^ β - 63)
    (lift_eq : G = 502 * 10 ^ β - 7)
    (shell :
      HasDecimalShell
        (((code (peeledHeadWord β (.c :: .c :: headTail)) : ℤ) *
          (E * code (punctuatedUpper β
              (front.map NearyTile.letter ++
                .c :: List.replicate tailWidth .c)) +
            G * code
              (spell (nearyLower β body)
                (front ++ .rule .c :: List.replicate tailWidth (.erase .c)))) -
          10 * μ * G * code
            (spell (nearyLower β body)
              (front ++ .rule .c :: List.replicate tailWidth (.erase .c))) : ℤ) : ℚ)
        (front.length + tailWidth) (front.length + tailWidth)) :
    False := by
  let tail : List TagLetter := List.replicate tailWidth .c
  let n := front.length + tailWidth + 1
  let H : ℤ := code (peeledHeadWord β (.c :: .c :: headTail))
  let P : ℤ := code (punctuatedUpper β (List.replicate n .c))
  let VRule : ℤ := code
    (spell (nearyLower β body) (front ++ .rule .c :: tail.map NearyTile.erase))
  let VErase : ℤ := allEraseLowerCode β body n
  let RRule : ℤ := H * (E * P + G * VRule) - 10 * μ * G * VRule
  let RErase : ℤ := H * (E * P + G * VErase) - 10 * μ * G * VErase
  have letters_eq :
      front.map NearyTile.letter ++ .c :: List.replicate tailWidth .c =
        List.replicate n .c := by
    rw [front_all_c]
    dsimp only [n]
    rw [show front.length + tailWidth + 1 = front.length + (tailWidth + 1) by omega,
      List.replicate_add, List.replicate_succ]
  have tail_map : tail.map NearyTile.erase =
      List.replicate tailWidth (.erase .c) := by
    simp only [tail, List.map_replicate]
  have rule_value : HasValue 5 (RRule : ℚ) (front.length + tailWidth) := by
    simpa only [RRule, H, P, VRule, letters_eq, tail_map] using shell.2
  have companion_spell :
      spell (nearyLower β body)
          (front.map erasePhaseTile ++ .erase .c :: tail.map NearyTile.erase) =
        List.replicate n false := by
    have erased := spell_erasePhase_lower β body
      (front ++ .rule .c :: tail.map NearyTile.erase)
    simpa [n, tail, List.map_append, List.map_map, List.map_replicate,
      erasePhaseTile, Function.comp_def,
      Nat.add_assoc] using erased
  have companion_code :
      (code (spell (nearyLower β body)
        (front.map erasePhaseTile ++ .erase .c :: tail.map NearyTile.erase)) : ℤ) =
        VErase := by
    rw [companion_spell]
    simp only [VErase, allEraseLowerCode, spell_allEraseBlock]
  let K := rightmostRuleLowerCoefficient β body front .c
  have lower_difference : VRule - VErase = K * 10 ^ tail.length := by
    have raw := rightmostRuleLowerCode_sub_eq β body front .c tail
    rw [companion_code] at raw
    simpa only [VRule, K] using raw
  have phase_residual_difference :
      RRule - RErase = G * (H - 10 * μ) * (K * 10 ^ tail.length) := by
    dsimp only [RRule, RErase]
    linear_combination G * (H - 10 * μ) * lower_difference
  have coefficient_mod : K ≡ 780 [ZMOD 1000] :=
    rightmostRuleLowerCoefficient_mod_thousand_of_two_le_prefix
      β body front .c front_large
  have allC_upper_eq : 9 * P = 50 * 10 ^ β * 10 ^ n + 2 * 10 ^ β - 7 :=
    allC_punctuatedUpper_code_identity β n
  have lower_eq : 9 * VErase = 7 * 10 ^ n - 7 := by
    have identity := allEraseLowerCode_identity β body n
    linear_combination identity
  rcases frontier with ⟨suffix_below, tail_width⟩ |
      ⟨suffix_exceptional, tail_width⟩
  · have width_deep : suffix + 1 < n := by
      dsimp only [n]
      omega
    have base_lead :
        HasFiveLeadingResidue (81 * RErase) (suffix + 1) (2 ^ suffix) :=
      regularAllC_scaledEightyOne_lead suffix_below width_deep
        (by simpa only [H] using head_eq) mu_eq gap_eq lift_eq
        allC_upper_eq lower_eq rfl rfl
    have phase_lead :
        HasFiveLeadingResidue (81 * (RRule - RErase)) (suffix + 1) (2 ^ suffix) := by
      have raw := regularNonleadingPhase_scaledEightyOne_lead
        (by omega : 1 ≤ β) suffix_positive (by simpa only [H] using head_eq) lift_eq
        (Or.inr coefficient_mod) phase_residual_difference
      simpa only [tail, List.length_replicate, tail_width] using raw
    have collision_value := (base_lead.add phase_lead).hasValue (by
      rw [← mul_two]
      exact twoPower_mul_not_five_dvd suffix (by norm_num))
    have scaled_sum_eq :
        ((81 * RErase + 81 * (RRule - RErase) : ℤ) : ℚ) =
          ((81 * RRule : ℤ) : ℚ) := by
      push_cast
      ring
    rw [scaled_sum_eq] at collision_value
    have eightyOne_lead : HasFiveLeadingResidue 81 0 1 :=
      ⟨81, by norm_num, by norm_num⟩
    have scaled_rule_value :
        HasValue 5 (((81 * RRule : ℤ) : ℚ)) (front.length + tailWidth) := by
      have product_value := mul_hasValue (eightyOne_lead.hasValue (by norm_num)) rule_value
      simpa [Int.cast_mul] using product_value
    have depth_eq :
        ((suffix + 1 : Nat) : ℤ) = ((front.length + tailWidth : Nat) : ℤ) :=
      collision_value.2.symm.trans scaled_rule_value.2
    have depth_eq_nat : suffix + 1 = front.length + tailWidth := by
      exact_mod_cast depth_eq
    omega
  · rw [suffix_exceptional] at head_eq
    have frontier_width : 2 * β - 1 ≤ n := by
      dsimp only [n]
      omega
    obtain ⟨baseCoefficient, base_coefficient, base_lead_raw⟩ :=
      exceptionalAllC_scaled_lead β_large (by simpa only [H] using head_eq)
        mu_eq gap_eq lift_eq allC_upper_eq lower_eq rfl rfl
    have base_lead :
        HasFiveLeadingResidue (45 * RErase) (2 * β)
          (2 ^ (2 * β - 1) * baseCoefficient) := by
      simpa only [min_eq_right frontier_width,
        show 2 * β - 1 + 1 = 2 * β by omega] using base_lead_raw
    have phase_lead :
        HasFiveLeadingResidue (45 * (RRule - RErase)) (2 * β)
          (2 ^ (2 * β - 1) * 2) := by
      have raw := exceptionalNonleadingPhase_scaled_lead
        β_large (by simpa only [H] using head_eq) lift_eq (Or.inr coefficient_mod)
        phase_residual_difference
      simpa only [tail, List.length_replicate, tail_width,
        show 2 * β - 2 + 1 + 1 = 2 * β by omega,
        show 2 * β - 2 + 1 = 2 * β - 1 by omega,
        show 2 * β - 1 + 1 = 2 * β by omega] using raw
    have residue_unit :
        ¬(5 : ℤ) ∣ 2 ^ (2 * β - 1) * baseCoefficient + 2 ^ (2 * β - 1) * 2 := by
      rw [← mul_add]
      apply twoPower_mul_not_five_dvd
      rcases base_coefficient with base_two | base_four
      · rw [base_two]
        norm_num
      · rw [base_four]
        norm_num
    have collision_value := (base_lead.add phase_lead).hasValue residue_unit
    have scaled_sum_eq :
        ((45 * RErase + 45 * (RRule - RErase) : ℤ) : ℚ) =
          ((45 * RRule : ℤ) : ℚ) := by
      push_cast
      ring
    rw [scaled_sum_eq] at collision_value
    have fortyFive_lead : HasFiveLeadingResidue 45 1 4 :=
      ⟨9, by norm_num, by norm_num⟩
    have scaled_rule_value :
        HasValue 5 (((45 * RRule : ℤ) : ℚ))
          (((front.length + tailWidth + 1 : Nat) : ℤ)) := by
      have product_value := mul_hasValue (fortyFive_lead.hasValue (by norm_num)) rule_value
      simpa [Int.cast_mul, add_comm] using product_value
    have depth_eq :
        ((2 * β : Nat) : ℤ) = (((front.length + tailWidth + 1 : Nat) : ℤ)) :=
      collision_value.2.symm.trans scaled_rule_value.2
    have depth_eq_nat : 2 * β = front.length + tailWidth + 1 := by
      exact_mod_cast depth_eq
    omega

/-- Every all-`c` rightmost-rule block misses the physical multi-role pole shell from the
distinguished decimal-unit two-`c` raw head. -/
theorem allCRightmostRule_rawHead_shell_impossible
    {β tailWidth : Nat} (body headTail : List TagLetter) (front : List NearyTile)
    {μ E G : ℤ}
    (β_large : 2 ≤ β)
    (multi_role : 2 ≤ front.length + tailWidth + 1)
    (front_all_c : front.map NearyTile.letter = List.replicate front.length .c)
    (head_unit :
      HasDecimalShell (code (peeledHeadWord β (.c :: .c :: headTail)) : ℚ) 0 0)
    (mu_eq : 9 * μ = 52 * 10 ^ β - 7)
    (gap_eq : E = 18 * 10 ^ β - 63)
    (lift_eq : G = 502 * 10 ^ β - 7)
    (shell :
      HasDecimalShell
        (((code (peeledHeadWord β (.c :: .c :: headTail)) : ℤ) *
          (E * code (punctuatedUpper β
              (front.map NearyTile.letter ++
                .c :: List.replicate tailWidth .c)) +
            G * code
              (spell (nearyLower β body)
                (front ++ .rule .c :: List.replicate tailWidth (.erase .c)))) -
          10 * μ * G * code
            (spell (nearyLower β body)
              (front ++ .rule .c :: List.replicate tailWidth (.erase .c))) : ℤ) : ℚ)
        (front.length + tailWidth) (front.length + tailWidth)) :
    False := by
  obtain ⟨suffix, suffix_positive, suffix_le, head_shape, frontier⟩ :=
    allCRightmostRule_rawHead_forces_laterResonance body headTail front
      β_large multi_role front_all_c head_unit mu_eq gap_eq lift_eq shell
  have head_eq :
      9 * (code (peeledHeadWord β (.c :: .c :: headTail)) : ℤ) =
        5 * 10 ^ (β + 2) + 2 * 10 ^ suffix - 7 :=
    rawHeadShape_code_identity (by omega) head_shape
  have tail_positive : 1 ≤ tailWidth := by
    rcases frontier with regular | exceptional
    · omega
    · omega
  have front_large : 2 ≤ front.length := by
    rcases lt_trichotomy front.length 1 with front_nil | front_one | front_large
    · have front_eq : front = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst front
      exfalso
      apply leadingRuleC_rawHead_multi_shell_impossible body headTail
        β_large tail_positive head_unit mu_eq gap_eq lift_eq
      simpa [List.replicate_succ] using shell
    · rcases front with _ | ⟨frontTile, frontTail⟩
      · simp at front_one
      · have front_tail_nil : frontTail = [] := by
          apply List.eq_nil_of_length_eq_zero
          simp only [List.length_cons] at front_one
          omega
        subst frontTail
        have front_letter : frontTile.letter = .c := by
          have singleton_eq : [frontTile.letter] = [.c] := by
            simpa using front_all_c
          exact List.cons.inj singleton_eq |>.1
        exfalso
        exact positionTwoAllCRightmostRule_rawHead_shell_impossible
          (β := β) (tailWidth := tailWidth) body headTail frontTile
          β_large front_letter head_unit mu_eq gap_eq lift_eq (by simpa [add_comm] using shell)
    · exact front_large
  exact laterAllCRightmostRule_rawHead_shell_impossible body headTail front
    β_large front_large front_all_c suffix_positive head_eq frontier
    mu_eq gap_eq lift_eq shell

end MatrixMortality.DecimalSetterAllCRule
