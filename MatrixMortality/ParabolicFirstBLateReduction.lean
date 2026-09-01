import MatrixMortality.ParabolicFirstBLateCore

/-!
# Outer-root classification for later first-`b` cylinders

The common root window for positions three through eleven contains 44 integral `(k,x,y)`
points. They occupy ten compressed ranges and occur only at positions three through six.
-/

namespace MatrixMortality.ParabolicBlade

/-- The ten compressed ranges in the later-position outer-root window. -/
def FirstBLateRootCandidate (k x y : Nat) : Prop :=
  (k = 3 ∧ x = 209 ∧ y = 17) ∨
    (k = 3 ∧ x = 210 ∧ y = 21) ∨
    (k = 3 ∧ x = 211 ∧ y = 27) ∨
    (k = 3 ∧ x = 212 ∧ y = 38) ∨
    (k = 3 ∧ x = 213 ∧ 64 ≤ y ∧ y ≤ 66) ∨
    (k = 3 ∧ x = 214 ∧ 206 ≤ y ∧ y ≤ 236) ∨
    (k = 4 ∧ x = 213 ∧ y = 18) ∨
    (k = 4 ∧ x = 214 ∧ 43 ≤ y ∧ y ≤ 45) ∨
    (k = 5 ∧ x = 214 ∧ y = 13) ∨
    (k = 6 ∧ x = 213 ∧ y = 2)

private theorem firstBLateRootWindow_x_le
    (k x y : Nat) (three_le_k : 3 ≤ k) (k_le : k ≤ 11) (two_le_y : 2 ≤ y)
    (window : FirstBLateRootWindow k x y) :
    x ≤ 214 := by
  unfold FirstBLateRootWindow at window
  rcases window with ⟨lower, upper⟩
  clear lower
  by_contra x_not_bounded
  have x_large : 215 ≤ x := by omega
  have denominator_nonnegative :
      0 ≤ firstBLateRootUpperDenominator k y :=
    (firstBLate_upper_denominator_positive
      k y three_le_k k_le two_le_y).le
  have scaled := Int.mul_le_mul_of_nonneg_right
    (show (215 : ℤ) ≤ x by exact_mod_cast x_large) denominator_nonnegative
  interval_cases k <;>
    norm_num [firstBLateRootUpperNumerator, firstBLateRootUpperDenominator,
      firstBLatePrefixScale] at upper scaled <;>
    omega

private def firstBLateRootFloor (k : Nat) : Nat :=
  match k with
  | 3 => 174
  | 4 => 200
  | 5 => 210
  | 6 => 213
  | _ => 215

private theorem firstBLateRootWindow_x_ge
    (k x y : Nat) (three_le_k : 3 ≤ k) (k_le : k ≤ 11) (two_le_y : 2 ≤ y)
    (window : FirstBLateRootWindow k x y) :
    firstBLateRootFloor k ≤ x := by
  unfold FirstBLateRootWindow at window
  rcases window with ⟨lower, upper⟩
  clear upper
  by_contra x_not_bounded
  have floor_positive : 0 < firstBLateRootFloor k := by
    interval_cases k <;> norm_num [firstBLateRootFloor]
  have x_small : x ≤ firstBLateRootFloor k - 1 := by omega
  have denominator_nonnegative :
      0 ≤ firstBLateRootLowerDenominator k y :=
    (firstBLate_lower_denominator_positive
      k y three_le_k k_le two_le_y).le
  have scaled := Int.mul_le_mul_of_nonneg_right
    (show (x : ℤ) ≤ ((firstBLateRootFloor k - 1 : Nat) : ℤ) by
      exact_mod_cast x_small)
    denominator_nonnegative
  interval_cases k <;>
    norm_num [firstBLateRootLowerNumerator, firstBLateRootLowerDenominator,
      firstBLateRootFloor, firstBLatePrefixScale] at lower scaled <;>
    omega

set_option maxHeartbeats 4000000 in
/-- Exact classification of the integral later-position outer-root window. -/
theorem firstBLateRootWindow_candidates
    (k x y : Nat) (three_le_k : 3 ≤ k) (k_le : k ≤ 11)
    (two_le_y : 2 ≤ y) (y_upper : y ≤ 51767)
    (window : FirstBLateRootWindow k x y) :
    FirstBLateRootCandidate k x y := by
  have x_upper :=
    firstBLateRootWindow_x_le k x y three_le_k k_le two_le_y window
  have x_lower :=
    firstBLateRootWindow_x_ge k x y three_le_k k_le two_le_y window
  rcases window with ⟨lower, upper⟩
  unfold FirstBLateRootCandidate
  interval_cases k <;>
    norm_num [firstBLateRootFloor] at x_lower <;>
    interval_cases x <;>
    norm_num [firstBLateRootLowerNumerator, firstBLateRootLowerDenominator,
      firstBLateRootUpperNumerator, firstBLateRootUpperDenominator,
      firstBLatePrefixScale] at lower upper ⊢ <;>
    omega

/-- Every physical later-position zero with middle wait at least two belongs to the exact
44-point outer-root classification. -/
theorem firstBLateRootCandidate_of_core_zero
    (k : Nat) (tail : List TagLetter) (contains_b : .b ∈ tail)
    (x y z : Nat) (three_le_k : 3 ≤ k) (k_le : k ≤ 11) (two_le_y : 2 ≤ y)
    (core_zero :
      bZeroBDefectCOneCodeCore
        ((3 : ℚ) ^
          (tagEncode 3 (List.replicate k .c ++ .b :: tail)).length)
        (ternaryCode (tagEncode 3 (List.replicate k .c ++ .b :: tail))) x y z = 0) :
    FirstBLateRootCandidate k x y := by
  have window := firstBLateRootWindow_of_core_zero
    k tail contains_b x y z three_le_k k_le two_le_y core_zero
  have y_upper := bZeroBDefectCOne_y_le_of_first_b k tail x y z core_zero
  exact firstBLateRootWindow_candidates
    k x y three_le_k k_le two_le_y y_upper window

end MatrixMortality.ParabolicBlade
