import MatrixMortality.ReturnGuardDynamics

/-!
# Exact examples for the amalgamated valuation guard

The first pair is the concrete one-step mortal integer pair from the construction. The second
parameter set has a ready nonterminal fixed point, proving that the guard itself does not force
termination.
-/

namespace MatrixMortality.ReturnGuard.Examples

open MatrixMortality.PadicValuation
open scoped Matrix

noncomputable section

private theorem five_prime : Nat.Prime 5 := by norm_num

private instance : Fact (Nat.Prime 5) :=
  ⟨five_prime⟩

private theorem val5_int_unit (z : Int) (not_dvd : ¬(5 : Int) ∣ z) :
    padicValRat 5 (z : ℚ) = 0 := by
  rw [padicValRat.of_int]
  exact_mod_cast padicValInt.eq_zero_of_not_dvd not_dvd

private theorem val5_self : padicValRat 5 (5 : ℚ) = 1 :=
  padicValRat.self (p := 5) (by norm_num)

private theorem val5_square : padicValRat 5 ((5 : ℚ) ^ 2) = 2 :=
  primePower_valuation 2

private theorem val5_869_div_28 :
    padicValRat 5 (869 / 28 : ℚ) = 0 := by
  rw [padicValRat.div (by norm_num) (by norm_num)]
  change padicValRat 5 ((869 : Int) : ℚ) -
    padicValRat 5 ((28 : Int) : ℚ) = 0
  rw [val5_int_unit 869 (by norm_num), val5_int_unit 28 (by norm_num)]
  norm_num

private theorem val5_841_div_28 :
    padicValRat 5 (841 / 28 : ℚ) = 0 := by
  rw [padicValRat.div (by norm_num) (by norm_num)]
  change padicValRat 5 ((841 : Int) : ℚ) -
    padicValRat 5 ((28 : Int) : ℚ) = 0
  rw [val5_int_unit 841 (by norm_num), val5_int_unit 28 (by norm_num)]
  norm_num

private theorem val5_thirty : padicValRat 5 (30 : ℚ) = 1 := by
  rw [show (30 : ℚ) = 5 * 6 by norm_num,
    padicValRat.mul (by norm_num) (by norm_num), val5_self]
  change 1 + padicValRat 5 ((6 : Int) : ℚ) = 1
  rw [val5_int_unit 6 (by norm_num)]
  norm_num

private theorem val5_twenty_five : padicValRat 5 (25 : ℚ) = 2 := by
  rw [show (25 : ℚ) = (5 : ℚ) ^ 2 by norm_num, val5_square]

private theorem val5_five_div_six : padicValRat 5 (5 / 6 : ℚ) = 1 := by
  rw [padicValRat.div (by norm_num) (by norm_num), val5_self]
  change 1 - padicValRat 5 ((6 : Int) : ℚ) = 1
  rw [val5_int_unit 6 (by norm_num)]
  norm_num

private theorem val5_neg_twenty_five_div_six :
    padicValRat 5 (-(25 / 6) : ℚ) = 2 := by
  rw [padicValRat.neg, padicValRat.div (by norm_num) (by norm_num)]
  rw [show (25 : ℚ) = (5 : ℚ) ^ 2 by norm_num, val5_square]
  change 2 - padicValRat 5 ((6 : Int) : ℚ) = 2
  rw [val5_int_unit 6 (by norm_num)]
  norm_num

/-- Concrete ready parameter set whose sole first legal step reaches the terminal point. -/
def mortalParameters : Parameters where
  prime := 5
  prime_prime := five_prime
  depth := 2
  depth_two := by norm_num
  center := 869 / 28
  reset := 30
  center_unit := ⟨by norm_num, val5_869_div_28⟩
  center_sub_one_unit := ⟨by norm_num, by
    norm_num only [div_sub_one]
    exact val5_841_div_28⟩
  reset_positive := ⟨by norm_num, by rw [val5_thirty]; norm_num⟩

theorem mortal_reset_ready :
    Ready mortalParameters 1 30 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · exact val5_thirty
  · norm_num only [mortalParameters, Nat.cast_ofNat, pow_one]
    exact val5_twenty_five

theorem mortal_guarded_step :
    guardedStep mortalParameters 1 (some 30) = some 1 := by
  rw [guardedStep_some mortalParameters 1 30 (by norm_num [mortalParameters])]
  norm_num [mortalParameters, guardDefect, drift]

theorem mortal_reachable : GuardedReachable mortalParameters :=
  Relation.TransGen.single
    ⟨0, by simpa using mortal_reset_ready, by simpa using mortal_guarded_step⟩

theorem mortal_rational_pair :
    IsMortal
      (ReturnFamily.pairGenerator
        (ambient (5 : ℚ) 2)
        (cut (869 / 28) 30)) :=
  (physical_isMortal_iff_guardedReachable mortalParameters).mpr mortal_reachable

/-- Denominator-cleared ambient generator of the concrete mortal pair. -/
def integerAmbient : Square (Fin 3) ℤ :=
  !![5, 0, 0;
     0, 1, 0;
     0, 0, 25]

/-- Denominator-cleared rank-two cut of the concrete mortal pair. -/
def integerCut : Square (Fin 3) ℤ :=
  !![-28, 28, 0;
     -869, 869, -29;
     -841, 841, -29]

theorem integerAmbient_eq :
    integerAmbient.map ((↑) : ℤ → ℚ) =
      5 • ambient (5 : ℚ) 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [integerAmbient, ambient, Matrix.smul_apply,
      Matrix.diagonal_apply]
  all_goals split <;> simp_all [Fin.ext_iff]

theorem integerCut_eq :
    integerCut.map ((↑) : ℤ → ℚ) =
      28 • cut (869 / 28) 30 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [integerCut, cut, input, output, drift,
      Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Explicit denominator-cleared zero word `B² A B²`. -/
theorem integer_zero_word :
    integerCut ^ 2 * integerAmbient * integerCut ^ 2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [integerAmbient, integerCut, pow_two,
      Matrix.mul_apply, Fin.sum_univ_succ]

/-- Concrete ready parameter set with a legal nonterminal fixed point. -/
def fixedParameters : Parameters where
  prime := 5
  prime_prime := five_prime
  depth := 2
  depth_two := by norm_num
  center := 2
  reset := 5 / 6
  center_unit := ⟨by norm_num, val5_int_unit 2 (by norm_num)⟩
  center_sub_one_unit := ⟨by norm_num, by norm_num⟩
  reset_positive := ⟨by norm_num, by rw [val5_five_div_six]; norm_num⟩

theorem fixed_reset_ready :
    Ready fixedParameters 1 (5 / 6) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · exact val5_five_div_six
  · norm_num only [fixedParameters, Nat.cast_ofNat, pow_one]
    exact val5_neg_twenty_five_div_six

theorem fixed_guarded_step :
    guardedStep fixedParameters 1 (some (5 / 6)) = some (5 / 6) := by
  rw [guardedStep_some fixedParameters 1 (5 / 6)
    (by norm_num [fixedParameters])]
  norm_num [fixedParameters, guardDefect, drift]

end
end MatrixMortality.ReturnGuard.Examples
