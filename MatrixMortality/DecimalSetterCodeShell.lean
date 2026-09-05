import MatrixMortality.DecimalSetterThreeBlockAllEraseCurrent

/-!
# A mixed-prime obstruction for decimal code differences

An unmatched digit contributes either a difference of two, or the end of one
code word. A nonempty decimal `5/7` code is never divisible by `125`. Removing
the shared suffix therefore gives `ν₅(P - V) ≤ ν₂(P - V) + 2` for any two code
words. This excludes the reversed shells of the exceptional all-erasure
three-block singleton branch.
-/

namespace MatrixMortality.DecimalSetterCarry

open MatrixMortality.PadicValuation
open MatrixMortality.DecimalSetterArithmetic

private theorem code_mod_five (word : List Bool) :
    code word % 5 = 0 ∨ code word % 5 = 2 := by
  induction word using List.reverseRecOn with
  | nil => simp
  | append_singleton head bit _ =>
      cases bit <;> simp [code_append, digit, Nat.add_mod, Nat.mul_mod]

private theorem code_mod_twentyFive (word : List Bool) :
    code word % 25 = 0 ∨ code word % 25 = 2 ∨
      code word % 25 = 5 ∨ code word % 25 = 7 := by
  induction word using List.reverseRecOn with
  | nil => simp
  | append_singleton head bit _ =>
      have residue := code_mod_five head
      cases bit <;> simp only [code_append, List.length_singleton, pow_one,
        code_singleton, digit_false, digit_true] <;> omega

private theorem code_not_dvd_oneTwentyFive {word : List Bool} (word_ne : word ≠ []) :
    ¬125 ∣ code word := by
  induction word using List.reverseRecOn with
  | nil => exact False.elim (word_ne rfl)
  | append_singleton head bit _ =>
      have residue := code_mod_twentyFive head
      rw [Nat.dvd_iff_mod_eq_zero, code_append]
      cases bit <;> simp only [List.length_singleton, pow_one,
        code_singleton, digit_false, digit_true] <;> omega

private theorem code_fiveDepth_le_two (word : List Bool) :
    padicValRat 5 (code word : ℚ) ≤ 2 := by
  by_cases word_nil : word = []
  · simp [word_nil]
  · have not_dvd := code_not_dvd_oneTwentyFive word_nil
    have bound : padicValNat 5 (code word) < 3 := by
      have no_power : ¬5 ^ 3 ∣ code word := by norm_num; exact not_dvd
      have divisibility := padicValNat_dvd_iff (p := 5) 3 (code word)
      omega
    rw [padicValRat.of_nat]
    omega

private theorem code_difference_depth_nonnegative (prime : Nat) (upper lower : List Bool) :
    0 ≤ padicValRat prime ((code upper : ℚ) - code lower) := by
  have cast : ((code upper : ℚ) - code lower) =
      (((code upper : ℤ) - code lower : ℤ) : ℚ) := by push_cast; rfl
  rw [cast, padicValRat.of_int]
  exact Int.natCast_nonneg _

/-- The five-adic depth of a decimal code difference exceeds its two-adic
depth by at most two. The zero difference also satisfies the inequality. -/
theorem code_difference_fiveDepth_le_twoDepth_add_two (upper lower : List Bool) :
    padicValRat 5 ((code upper : ℚ) - code lower) ≤
      padicValRat 2 ((code upper : ℚ) - code lower) + 2 := by
  induction upper using List.reverseRecOn generalizing lower with
  | nil =>
      have bound := code_fiveDepth_le_two lower
      have nonnegative := code_difference_depth_nonnegative 2 [] lower
      simp only [code_nil, Nat.cast_zero, zero_sub, padicValRat.neg] at nonnegative ⊢
      omega
  | append_singleton upper last_upper induction =>
      induction lower using List.reverseRecOn with
      | nil =>
          have bound := code_fiveDepth_le_two (upper ++ [last_upper])
          have nonnegative := code_difference_depth_nonnegative 2
            (upper ++ [last_upper]) []
          simp only [code_nil, Nat.cast_zero, sub_zero] at nonnegative ⊢
          omega
      | append_singleton lower last_lower _ =>
          by_cases same_digit : last_upper = last_lower
          · subst last_lower
            have difference :
                (code (upper ++ [last_upper]) : ℚ) - code (lower ++ [last_upper]) =
                  10 * ((code upper : ℚ) - code lower) := by
              simp only [code_append, List.length_singleton, pow_one,
                Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
              ring
            rw [difference]
            by_cases zero : (code upper : ℚ) - code lower = 0
            · simp [zero]
            · have previous := induction lower
              rw [padicValRat.mul (by norm_num : (10 : ℚ) ≠ 0) zero,
                padicValRat.mul (by norm_num : (10 : ℚ) ≠ 0) zero,
                ten_hasDecimalShell.1.2, ten_hasDecimalShell.2.2]
              omega
          · have integral_unit : ¬(5 : ℤ) ∣
                (code (upper ++ [last_upper]) : ℤ) - code (lower ++ [last_lower]) := by
              rw [Int.dvd_iff_emod_eq_zero]
              cases last_upper <;> cases last_lower <;>
                simp [code_append, digit] at same_digit ⊢ <;> omega
            have unit := intCast_isUnit_of_not_dvd integral_unit
            have five_zero : padicValRat 5
                ((code (upper ++ [last_upper]) : ℚ) - code (lower ++ [last_lower])) = 0 := by
              simpa using unit.2
            rw [five_zero]
            have nonnegative := code_difference_depth_nonnegative 2
              (upper ++ [last_upper]) (lower ++ [last_lower])
            omega

end MatrixMortality.DecimalSetterCarry

namespace MatrixMortality.DecimalSetterBridgeRay

open MatrixMortality.DecimalSetterAncestry
open MatrixMortality.DecimalSetterBridge
open MatrixMortality.DecimalSetterCarry

/-- The exceptional all-erasure current before `D_b` is impossible at every
intervening length, including the width-three exceptional coefficient. -/
theorem singletonPole_threeBlock_ruleCRoot_allEraseBlock_targetB_impossible
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter) (next : List NearyTile) :
    ¬HitsSquarePole β body [.erase .b]
      [allEraseBlock (β + 2), next, DecimalSetterMinimumBody.ruleCRoot] := by
  intro pole
  have bound := code_difference_fiveDepth_le_twoDepth_add_two
    (spell (nearyUpper β) next ++ nearyMarker β) (spell (nearyLower β body) next)
  change padicValRat 5 (upperBoundaryCode β next - lowerBoundaryCode β body next) ≤
    padicValRat 2 (upperBoundaryCode β next - lowerBoundaryCode β body next) + 2 at bound
  by_cases width_three : β = 3
  · subst β
    have shell :=
      singletonPole_threeBlock_ruleCRoot_allEraseBlock_targetB_beta_three_discrepancyShell
        body next pole
    rw [shell.1.2, shell.2.2] at bound
    omega
  · have shell := singletonPole_threeBlock_ruleCRoot_allEraseBlock_targetB_discrepancyShell
      (by omega) body next pole
    rw [shell.1.2, shell.2.2] at bound
    omega

end MatrixMortality.DecimalSetterBridgeRay
