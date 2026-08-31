import MatrixMortality.MixedPrimeDebt

/-!
# Mixed-prime debt collision boundary

Same-length debt bridges are globally rigid, while an exact cross-length collision realizes the
remaining carrier orientation.
-/

namespace MatrixMortality.MixedPrimeDebt

open PadicValuation
open PeriodicShell

private local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
private local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The opposite carrier orientation is also realized by an exact unequal-length debt
collision. Both endpoints remain five-adic units. -/
theorem negativeOrientation_crossLengthCollision :
    shellRun [1] (19 / 42) = 8 / 21 ∧
      shellRun [1, 2, 0] (19 / 42) = 8 / 21 ∧
      debtState (19 / 14) 1 = 19 / 42 ∧
      debtState (8 / 7) 1 = 8 / 21 ∧
      IsUnit 5 (19 / 42 : ℚ) ∧
      IsUnit 5 (8 / 21 : ℚ) ∧
      HasValue 3 (19 / 14 + 1) 1 ∧
      HasValue 3 (8 / 7 + 1) 1 := by
  constructor
  · rw [shellRun_singleton]
    norm_num [shellStep]
  constructor
  · rw [shellRun_cons, shellRun_cons, shellRun_singleton]
    norm_num [shellStep]
  constructor
  · norm_num [debtState]
  constructor
  · norm_num [debtState]
  constructor
  · exact div_hasValue
      (intCast_isUnit_of_not_dvd (prime := 5) (by norm_num : ¬(5 : ℤ) ∣ 19))
      (intCast_isUnit_of_not_dvd (prime := 5) (by norm_num : ¬(5 : ℤ) ∣ 42))
  constructor
  · exact div_hasValue
      (intCast_isUnit_of_not_dvd (prime := 5) (by norm_num : ¬(5 : ℤ) ∣ 8))
      (intCast_isUnit_of_not_dvd (prime := 5) (by norm_num : ¬(5 : ℤ) ∣ 21))
  constructor
  · convert primePower_mul_int_div_int_hasValue (prime := 3) 1
      (by norm_num : ¬(3 : ℤ) ∣ 11) (by norm_num : ¬(3 : ℤ) ∣ 14) using 1 <;>
      norm_num
  · convert primePower_mul_int_div_int_hasValue (prime := 3) 1
      (by norm_num : ¬(3 : ℤ) ∣ 5) (by norm_num : ¬(3 : ℤ) ∣ 7) using 1 <;>
      norm_num

/-- Within fixed debt endpoints and fixed length, a point collision is already a global affine
relation. Source-specific collisions can occur only across different lengths. -/
theorem debtSafe_sameLength_collision_global
    {left right : List ℕ} {startDepth endDepth : ℕ} {source : ℚ}
    (left_safe : DebtSafe startDepth left) (right_safe : DebtSafe startDepth right)
    (left_ends : debtRunDepth startDepth left = endDepth)
    (right_ends : debtRunDepth startDepth right = endDepth)
    (length_eq : left.length = right.length)
    (collision : shellRun left source = shellRun right source) :
    ∀ state, shellRun left state = shellRun right state := by
  have left_balance := debtRunDepth_eq_of_balance left startDepth endDepth
    left_safe left_ends
  have right_balance := debtRunDepth_eq_of_balance right startDepth endDepth
    right_safe right_ends
  have sum_eq : left.sum = right.sum := by omega
  have slope_eq : shellSlope left = shellSlope right :=
    shellSlope_eq_of_length_sum length_eq sum_eq
  intro state
  have left_displacement := shellRun_sub_shellRun left state source
  have right_displacement := shellRun_sub_shellRun right state source
  rw [slope_eq, collision] at left_displacement
  linarith

end MatrixMortality.MixedPrimeDebt
