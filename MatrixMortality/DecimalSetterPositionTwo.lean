import MatrixMortality.DecimalSetterRuleCoefficient

/-!
# Decimal setter position-two rule extinction

The last all-`c` branch left by the rightmost-rule position grammar has one role before the
rule.  Its phase perturbation has exact five-depth `n-1` but two-depth at least `n`, where `n`
is the block width.  Near either raw-head frontier, both the all-erasure companion and the
perturbation are divisible by `2^n`; beyond the frontier, the companion has strictly shallower
five-depth.  Either alternative contradicts the physical shell at depth `n-1`.
-/

namespace MatrixMortality.DecimalSetterPositionTwo

open MatrixMortality.DecimalSetterArithmetic
open MatrixMortality.DecimalSetterAncestry
open MatrixMortality.DecimalSetterCarry
open MatrixMortality.DecimalSetterChamber
open MatrixMortality.DecimalSetterDepth
open MatrixMortality.DecimalSetterPhase
open MatrixMortality.DecimalSetterRuleCoefficient
open MatrixMortality.DecimalSetterRuleResonance
open MatrixMortality.PadicValuation

private instance factPrimeTwo : Fact (Nat.Prime 2) :=
  ⟨by norm_num⟩

private theorem twoPower_dvd_tenPower {small large : Nat} (bound : small ≤ large) :
    (2 : ℤ) ^ small ∣ 10 ^ large :=
  (pow_dvd_pow (2 : ℤ) bound).trans
    (pow_dvd_pow_of_dvd (by norm_num : (2 : ℤ) ∣ 10) large)

private theorem nextTwoPower_not_dvd_int_of_hasValue
    {value : ℤ} {depth : Nat} (value_shell : HasValue 2 (value : ℚ) depth) :
    ¬(2 : ℤ) ^ (depth + 1) ∣ value := by
  intro divides
  have valuation_eq : padicValInt 2 value = depth := by
    have valuation_rat := value_shell.2
    rw [padicValRat.of_int] at valuation_rat
    exact_mod_cast valuation_rat
  have bound := (padicValInt_dvd_iff (depth + 1) value).mp divides
  have value_ne : value ≠ 0 := by exact_mod_cast value_shell.1
  have depth_bound := bound.resolve_left value_ne
  rw [valuation_eq] at depth_bound
  omega

/-- Up to the regular raw-head frontier, an all-`D_c` residual of width `n` is divisible by
`2^n`.  The frontier endpoint uses the additional factor of two in the raw-head coefficient. -/
theorem regularAllC_twoPower_dvd
    {β suffix n : Nat} {H μ E G P V T R : ℤ}
    (suffix_below : suffix + 2 ≤ β)
    (width_near : n ≤ suffix + 2)
    (head_eq : 9 * H = 5 * 10 ^ (β + 2) + 2 * 10 ^ suffix - 7)
    (mu_eq : 9 * μ = 52 * 10 ^ β - 7)
    (gap_eq : E = 18 * 10 ^ β - 63)
    (lift_eq : G = 502 * 10 ^ β - 7)
    (upper_eq : 9 * P = 50 * 10 ^ β * 10 ^ n + 2 * 10 ^ β - 7)
    (lower_eq : 9 * V = 7 * 10 ^ n - 7)
    (trace_eq : T = E * P + G * V)
    (residual_eq : R = H * T - 10 * μ * G * V) :
    (2 : ℤ) ^ n ∣ R := by
  obtain ⟨K, A, B, decomposition, _, K_even⟩ :=
    regularAllC_residualNormalForm suffix_below head_eq mu_eq gap_eq lift_eq
      upper_eq lower_eq trace_eq residual_eq
  have first_dvd : (2 : ℤ) ^ n ∣ 10 ^ (suffix + 1) * K := by
    rcases lt_or_eq_of_le width_near with width_shallow | width_boundary
    · exact dvd_mul_of_dvd_left (twoPower_dvd_tenPower (by omega)) K
    · subst n
      obtain ⟨KHalf, K_eq⟩ := K_even
      rw [K_eq, ← mul_assoc]
      have boundary_power : (2 : ℤ) ^ (suffix + 2) ∣ 10 ^ (suffix + 1) * 2 := by
        rw [show suffix + 2 = (suffix + 1) + 1 by omega, pow_add]
        exact mul_dvd_mul (twoPower_dvd_tenPower le_rfl) (dvd_refl 2)
      exact dvd_mul_of_dvd_left boundary_power KHalf
  have second_dvd : (2 : ℤ) ^ n ∣ 10 ^ n * A :=
    dvd_mul_of_dvd_left (twoPower_dvd_tenPower le_rfl) A
  have third_dvd : (2 : ℤ) ^ n ∣ 10 ^ β * B :=
    dvd_mul_of_dvd_left (twoPower_dvd_tenPower (by omega)) B
  have scaled_dvd : (2 : ℤ) ^ n ∣ 81 * R := by
    rw [decomposition]
    exact dvd_add (dvd_add first_dvd second_dvd) third_dvd
  exact ((by norm_num : IsCoprime (2 : ℤ) 81).pow_left).dvd_of_dvd_mul_left scaled_dvd

/-- Up to the exceptional raw-head frontier, an all-`D_c` residual of width `n` is divisible
by `2^n`. -/
theorem exceptionalAllC_twoPower_dvd
    {β n : Nat} {H μ E G P V T R : ℤ}
    (β_large : 2 ≤ β)
    (width_near : n ≤ 2 * β)
    (head_eq : 9 * H = 5 * 10 ^ (β + 2) + 2 * 10 ^ (β - 1) - 7)
    (mu_eq : 9 * μ = 52 * 10 ^ β - 7)
    (gap_eq : E = 18 * 10 ^ β - 63)
    (lift_eq : G = 502 * 10 ^ β - 7)
    (upper_eq : 9 * P = 50 * 10 ^ β * 10 ^ n + 2 * 10 ^ β - 7)
    (lower_eq : 9 * V = 7 * 10 ^ n - 7)
    (trace_eq : T = E * P + G * V)
    (residual_eq : R = H * T - 10 * μ * G * V) :
    (2 : ℤ) ^ n ∣ R := by
  obtain ⟨C, B, decomposition, _, _⟩ :=
    allCDeletion_firstRawHead_residueNormalForm β_large head_eq mu_eq gap_eq lift_eq
      upper_eq lower_eq trace_eq residual_eq
  have first_dvd : (2 : ℤ) ^ n ∣ 10 ^ n * (5 * C) :=
    dvd_mul_of_dvd_left (twoPower_dvd_tenPower le_rfl) (5 * C)
  have second_dvd : (2 : ℤ) ^ n ∣ 10 ^ (2 * β) * B :=
    dvd_mul_of_dvd_left (twoPower_dvd_tenPower width_near) B
  have scaled_dvd : (2 : ℤ) ^ n ∣ 45 * R := by
    rw [decomposition]
    exact dvd_add first_dvd second_dvd
  exact ((by norm_num : IsCoprime (2 : ℤ) 45).pow_left).dvd_of_dvd_mul_left scaled_dvd

/-- An all-`c` block whose rightmost rule is its second role cannot enter the expected pole
shell from the distinguished decimal raw head. -/
theorem positionTwoAllCRightmostRule_rawHead_shell_impossible
    {β tailWidth : Nat} (body headTail : List TagLetter) (frontTile : NearyTile)
    {μ E G : ℤ}
    (β_large : 2 ≤ β)
    (front_letter : frontTile.letter = .c)
    (head_unit :
      HasDecimalShell (code (peeledHeadWord β (.c :: .c :: headTail)) : ℚ) 0 0)
    (mu_eq : 9 * μ = 52 * 10 ^ β - 7)
    (gap_eq : E = 18 * 10 ^ β - 63)
    (lift_eq : G = 502 * 10 ^ β - 7)
    (shell :
      HasDecimalShell
        (((code (peeledHeadWord β (.c :: .c :: headTail)) : ℤ) *
          (E * code (punctuatedUpper β
              (frontTile.letter :: .c :: List.replicate tailWidth .c)) +
            G * code
              (spell (nearyLower β body)
                (frontTile :: .rule .c ::
                  List.replicate tailWidth (.erase .c)))) -
          10 * μ * G * code
            (spell (nearyLower β body)
              (frontTile :: .rule .c ::
                List.replicate tailWidth (.erase .c))) : ℤ) : ℚ)
        (tailWidth + 1) (tailWidth + 1)) :
    False := by
  let tail : List TagLetter := List.replicate tailWidth .c
  let n := tailWidth + 2
  let H : ℤ := code (peeledHeadWord β (.c :: .c :: headTail))
  let P : ℤ := code (punctuatedUpper β (List.replicate n .c))
  let VRule : ℤ := code
    (spell (nearyLower β body) (frontTile :: .rule .c :: tail.map NearyTile.erase))
  let VErase : ℤ := allEraseLowerCode β body n
  let RRule : ℤ := H * (E * P + G * VRule) - 10 * μ * G * VRule
  let RErase : ℤ := H * (E * P + G * VErase) - 10 * μ * G * VErase
  have letters_eq :
      frontTile.letter :: .c :: List.replicate tailWidth .c =
        List.replicate n .c := by
    rw [front_letter]
    simp only [n, List.replicate_succ]
  have rule_shell :
      HasDecimalShell (RRule : ℚ) (tailWidth + 1) (tailWidth + 1) := by
    have tail_map : tail.map NearyTile.erase =
        List.replicate tailWidth (.erase .c) := by
      simp only [tail, List.map_replicate]
    simpa only [RRule, H, P, VRule, letters_eq, tail_map] using shell
  have companion_spell :
      spell (nearyLower β body)
          (erasePhaseTile frontTile :: .erase .c :: tail.map NearyTile.erase) =
        List.replicate n false := by
    have erased := spell_erasePhase_lower β body
      (frontTile :: .rule .c :: tail.map NearyTile.erase)
    simpa [n, tail, erasePhaseTile] using erased
  have companion_code :
      (code (spell (nearyLower β body)
        (erasePhaseTile frontTile :: .erase .c :: tail.map NearyTile.erase)) : ℤ) =
        VErase := by
    rw [companion_spell]
    simp only [VErase, allEraseLowerCode, spell_allEraseBlock]
  have lower_five_value :
      HasValue 5 (((VRule - VErase : ℤ) : ℚ)) (tailWidth + 1) := by
    have raw := rightmostRuleLowerCode_sub_hasValue_five_of_front_one
      β body frontTile .c tail
    rw [companion_code] at raw
    simpa only [VRule, tail, List.length_replicate] using raw
  have lower_two_dvd : (2 : ℤ) ^ n ∣ VRule - VErase := by
    have raw := twoPower_dvd_rightmostRuleLowerCode_sub_of_front_one
      β body frontTile .c tail
    rw [companion_code] at raw
    have weakened : (2 : ℤ) ^ n ∣
        (code
            (spell (nearyLower β body)
              (frontTile :: .rule .c :: tail.map NearyTile.erase)) : ℤ) -
          VErase :=
      (pow_dvd_pow (2 : ℤ) (show n ≤ tail.length + 3 by simp [n, tail])).trans raw
    simpa only [VRule] using weakened
  have lift_unit := calibratedLift_decimalUnit (G := G) (by omega) lift_eq
  have head_gap_unit := peeledDoubleCHead_sub_tenMarker_decimalUnit
    headTail μ (by omega) head_unit
  have phase_value :
      HasValue 5 (((RRule - RErase : ℤ) : ℚ)) (tailWidth + 1) := by
    have raw := peeledNumerator_sameUpper_sub_hasValue_five
      (H := H) (μ := μ) (E := E) (G := G) (P := P)
      (V₁ := VRule) (V₂ := VErase)
      lift_unit.2 (by simpa only [H] using head_gap_unit.2) lower_five_value
    simpa [RRule, RErase, H, P, VRule, VErase, peeledNumerator, transferTrace] using raw
  have phase_two_dvd : (2 : ℤ) ^ n ∣ RRule - RErase := by
    have difference_eq := peeledNumerator_sameUpper_sub H μ E G P VRule VErase
    have residual_difference :
        RRule - RErase = G * (H - 10 * μ) * (VRule - VErase) := by
      simpa [RRule, RErase, peeledNumerator, transferTrace] using difference_eq
    rw [residual_difference]
    exact dvd_mul_of_dvd_right lower_two_dvd (G * (H - 10 * μ))
  have upper_eq : 9 * P = 50 * 10 ^ β * 10 ^ n + 2 * 10 ^ β - 7 :=
    allC_punctuatedUpper_code_identity β n
  have lower_eq : 9 * VErase = 7 * 10 ^ n - 7 := by
    have identity := allEraseLowerCode_identity β body n
    linear_combination identity
  obtain ⟨suffix, suffix_positive, suffix_le, _, head_eq⟩ :=
    peeledDoubleCHead_unit_shape headTail (by omega) head_unit
  rcases lt_or_eq_of_le suffix_le with suffix_regular | suffix_exceptional
  · have suffix_below : suffix + 2 ≤ β := by omega
    by_cases width_near : n ≤ suffix + 2
    · have erase_two_dvd : (2 : ℤ) ^ n ∣ RErase :=
        regularAllC_twoPower_dvd suffix_below width_near head_eq mu_eq gap_eq lift_eq
          upper_eq lower_eq rfl rfl
      have rule_two_dvd : (2 : ℤ) ^ n ∣ RRule := by
        have sum_dvd := dvd_add erase_two_dvd phase_two_dvd
        simpa only [show RErase + (RRule - RErase) = RRule by ring] using sum_dvd
      exact (nextTwoPower_not_dvd_int_of_hasValue rule_shell.1) (by
        simpa only [n] using rule_two_dvd)
    · have width_deep : suffix + 3 ≤ n := by omega
      have erase_value :
          HasValue 5 (RErase : ℚ) (((suffix + 1 : Nat) : ℤ)) := by
        have raw := allCDeletion_regularRawHead_hasValue_five suffix_positive suffix_below
          (show 1 ≤ n by dsimp only [n]; omega) head_eq mu_eq gap_eq lift_eq
          upper_eq lower_eq rfl rfl
        simpa only [min_eq_right (by omega : suffix + 1 ≤ n), RErase, H] using raw
      have depth_lt :
          ((suffix + 1 : Nat) : ℤ) < ((tailWidth + 1 : Nat) : ℤ) := by
        exact_mod_cast (show suffix + 1 < tailWidth + 1 by dsimp only [n] at width_deep; omega)
      have sum_value := add_hasValue_left erase_value phase_value depth_lt
      have sum_eq :
          (RErase : ℚ) + ((RRule - RErase : ℤ) : ℚ) = (RRule : ℚ) := by
        push_cast
        ring
      rw [sum_eq] at sum_value
      have depth_eq := sum_value.2.symm.trans rule_shell.2.2
      exact (by omega)
  · rw [suffix_exceptional] at head_eq
    by_cases width_near : n ≤ 2 * β
    · have erase_two_dvd : (2 : ℤ) ^ n ∣ RErase :=
        exceptionalAllC_twoPower_dvd β_large width_near head_eq mu_eq gap_eq lift_eq
          upper_eq lower_eq rfl rfl
      have rule_two_dvd : (2 : ℤ) ^ n ∣ RRule := by
        have sum_dvd := dvd_add erase_two_dvd phase_two_dvd
        simpa only [show RErase + (RRule - RErase) = RRule by ring] using sum_dvd
      exact (nextTwoPower_not_dvd_int_of_hasValue rule_shell.1) (by
        simpa only [n] using rule_two_dvd)
    · have width_deep : 2 * β < n := by omega
      have erase_value :
          HasValue 5 (RErase : ℚ) (((2 * β - 1 : Nat) : ℤ)) := by
        have raw := allCDeletion_exceptionalRawHead_hasValue_five β_large head_eq
          mu_eq gap_eq lift_eq upper_eq lower_eq rfl rfl
        simpa only [min_eq_right (by omega : 2 * β - 1 ≤ n), RErase, H] using raw
      have depth_lt :
          (((2 * β - 1 : Nat) : ℤ)) < ((tailWidth + 1 : Nat) : ℤ) := by
        exact_mod_cast (show 2 * β - 1 < tailWidth + 1 by dsimp only [n] at width_deep; omega)
      have sum_value := add_hasValue_left erase_value phase_value depth_lt
      have sum_eq :
          (RErase : ℚ) + ((RRule - RErase : ℤ) : ℚ) = (RRule : ℚ) := by
        push_cast
        ring
      rw [sum_eq] at sum_value
      have depth_eq := sum_value.2.symm.trans rule_shell.2.2
      exact (by omega)

/-- Removing the position-two alternative from the S56 all-`c` grammar leaves only the exact
regular or exceptional raw-head frontier resonance. -/
theorem allCRightmostRule_rawHead_forces_laterResonance
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
    ∃ suffix, 1 ≤ suffix ∧ suffix ≤ β - 1 ∧
      peeledHeadWord β (.c :: .c :: headTail) =
        List.replicate (β + 2 - suffix) true ++ List.replicate suffix false ∧
      ((suffix + 2 ≤ β ∧ tailWidth = suffix) ∨
        (suffix = β - 1 ∧ tailWidth = 2 * β - 2)) := by
  have boundary := allCRightmostRule_rawHead_forces_boundary body headTail front
    β_large multi_role front_all_c head_unit mu_eq gap_eq lift_eq shell
  rcases boundary with front_one | later_resonance
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
      exact False.elim
        (positionTwoAllCRightmostRule_rawHead_shell_impossible
          (β := β) (tailWidth := tailWidth) body headTail frontTile
          β_large front_letter head_unit mu_eq gap_eq lift_eq (by simpa [add_comm] using shell))
  · exact later_resonance

end MatrixMortality.DecimalSetterPositionTwo
