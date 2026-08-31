import MatrixMortality.ParabolicWaitBounds

/-!
# Outer-wait reduction for the second-first-`b` cylinder

The normalized root enclosure for the body prefix `ccb` leaves exactly twelve compressed
integral `(x, y)` ranges.  This module checks that finite arithmetic reduction independently
of the subsequent tail-cylinder argument.
-/

namespace MatrixMortality.ParabolicBlade

private def firstBTwoRootLowerNumerator (y : Nat) : ℤ :=
  5541372938576372618 * y - 718629336347817375

private def firstBTwoRootLowerDenominator (y : Nat) : ℤ :=
  25950255067173888 * y + 30751845545334654

private def firstBTwoRootUpperNumerator (y : Nat) : ℤ :=
  112032354356496 * y - 14545738406053

private def firstBTwoRootUpperDenominator (y : Nat) : ℤ :=
  524493688320 * y + 618673335624

/-- Lower normalized root bound for the outer wait `x`, as a function of `y`. -/
def firstBTwoRootLower (y : Nat) : ℚ :=
  (5541372938576372618 * y - 718629336347817375) /
    (25950255067173888 * y + 30751845545334654)

/-- Upper normalized root bound for the outer wait `x`, as a function of `y`. -/
def firstBTwoRootUpper (y : Nat) : ℚ :=
  (112032354356496 * y - 14545738406053) /
    (524493688320 * y + 618673335624)

private theorem firstBTwoRootLower_integer_form (y : Nat) :
    firstBTwoRootLower y =
      firstBTwoRootLowerNumerator y / firstBTwoRootLowerDenominator y := by
  norm_num [firstBTwoRootLower, firstBTwoRootLowerNumerator,
    firstBTwoRootLowerDenominator]

private theorem firstBTwoRootUpper_integer_form (y : Nat) :
    firstBTwoRootUpper y =
      firstBTwoRootUpperNumerator y / firstBTwoRootUpperDenominator y := by
  norm_num [firstBTwoRootUpper, firstBTwoRootUpperNumerator,
    firstBTwoRootUpperDenominator]

/-- The normalized rational root window containing a possible integral outer wait. -/
def FirstBTwoRootWindow (x y : Nat) : Prop :=
  firstBTwoRootLower y ≤ x ∧ x ≤ firstBTwoRootUpper y

/-- The twelve compressed integral ranges contained in the normalized root window. -/
def FirstBTwoRootCandidate (x y : Nat) : Prop :=
  (x = 183 ∧ y = 8) ∨
    (x = 186 ∧ y = 9) ∨
    (x = 199 ∧ y = 18) ∨
    (x = 202 ∧ y = 23) ∨
    (x = 204 ∧ y = 28) ∨
    (x = 206 ∧ y = 36) ∨
    (x = 208 ∧ y = 49) ∨
    (x = 209 ∧ y = 60) ∨
    (x = 210 ∧ 77 ≤ y ∧ y ≤ 78) ∨
    (x = 211 ∧ 107 ≤ y ∧ y ≤ 109) ∨
    (x = 212 ∧ 174 ≤ y ∧ y ≤ 181) ∨
    (x = 213 ∧ 465 ≤ y ∧ y ≤ 520)

private theorem firstBTwoRootWindow_cross
    (x y : Nat) (window : FirstBTwoRootWindow x y) :
    firstBTwoRootLowerNumerator y ≤ (x : ℤ) * firstBTwoRootLowerDenominator y ∧
      (x : ℤ) * firstBTwoRootUpperDenominator y ≤ firstBTwoRootUpperNumerator y := by
  rcases window with ⟨lower, upper⟩
  rw [firstBTwoRootLower_integer_form] at lower
  rw [firstBTwoRootUpper_integer_form] at upper
  have lower_denominator_positive :
      (0 : ℚ) < firstBTwoRootLowerDenominator y := by
    unfold firstBTwoRootLowerDenominator
    positivity
  have upper_denominator_positive :
      (0 : ℚ) < firstBTwoRootUpperDenominator y := by
    unfold firstBTwoRootUpperDenominator
    positivity
  have lower_cross := (div_le_iff₀ lower_denominator_positive).mp lower
  have upper_cross := (le_div_iff₀ upper_denominator_positive).mp upper
  constructor
  · apply (Int.cast_le (R := ℚ)).mp
    simpa only [Int.cast_mul, Int.cast_natCast] using lower_cross
  · apply (Int.cast_le (R := ℚ)).mp
    simpa only [Int.cast_mul, Int.cast_natCast] using upper_cross

private theorem firstBTwoRootWindow_of_cross
    (x y : Nat)
    (lower :
      firstBTwoRootLowerNumerator y ≤ (x : ℤ) * firstBTwoRootLowerDenominator y)
    (upper :
      (x : ℤ) * firstBTwoRootUpperDenominator y ≤ firstBTwoRootUpperNumerator y) :
    FirstBTwoRootWindow x y := by
  have lower_denominator_positive :
      (0 : ℚ) < firstBTwoRootLowerDenominator y := by
    unfold firstBTwoRootLowerDenominator
    positivity
  have upper_denominator_positive :
      (0 : ℚ) < firstBTwoRootUpperDenominator y := by
    unfold firstBTwoRootUpperDenominator
    positivity
  constructor
  · rw [firstBTwoRootLower_integer_form]
    rw [div_le_iff₀ lower_denominator_positive]
    have lower_cast := (Int.cast_le (R := ℚ)).mpr lower
    simpa only [Int.cast_mul, Int.cast_natCast] using lower_cast
  · rw [firstBTwoRootUpper_integer_form]
    rw [le_div_iff₀ upper_denominator_positive]
    have upper_cast := (Int.cast_le (R := ℚ)).mpr upper
    simpa only [Int.cast_mul, Int.cast_natCast] using upper_cast

/-- At `y = 1`, the normalized root interval lies strictly between `85` and `86`. -/
theorem firstBTwoRoot_y_one_between :
    (85 : ℚ) < firstBTwoRootLower 1 ∧ firstBTwoRootUpper 1 < 86 := by
  constructor
  · norm_num [firstBTwoRootLower, firstBTwoRootLowerNumerator,
      firstBTwoRootLowerDenominator]
  · norm_num [firstBTwoRootUpper, firstBTwoRootUpperNumerator,
      firstBTwoRootUpperDenominator]

/-- No natural outer wait belongs to the normalized root window at `y = 1`. -/
theorem firstBTwoRootWindow_y_one_empty (x : Nat) :
    ¬FirstBTwoRootWindow x 1 := by
  intro window
  rcases window with ⟨lower, upper⟩
  rcases firstBTwoRoot_y_one_between with ⟨lower_strict, upper_strict⟩
  have x_gt : (85 : ℚ) < x := lt_of_lt_of_le lower_strict lower
  have x_lt : (x : ℚ) < 86 := lt_of_le_of_lt upper upper_strict
  have x_gt_nat : 85 < x := by exact_mod_cast x_gt
  have x_lt_nat : x < 86 := by exact_mod_cast x_lt
  omega

/-- The normalized root window with `y ≥ 2` lies in the finite coarse search box. -/
theorem firstBTwoRootWindow_coarse
    (x y : Nat) (wait_large : 2 ≤ y) (window : FirstBTwoRootWindow x y) :
    126 ≤ x ∧ x ≤ 213 ∧ y ≤ 520 := by
  rcases firstBTwoRootWindow_cross x y window with ⟨lower, upper⟩
  have x_lower : 126 ≤ x := by
    by_contra x_small
    have x_le : x ≤ 125 := by omega
    have scaled := Int.mul_le_mul_of_nonneg_right
      (show (x : ℤ) ≤ 125 by exact_mod_cast x_le)
      (show (0 : ℤ) ≤ firstBTwoRootLowerDenominator y by
        unfold firstBTwoRootLowerDenominator
        positivity)
    unfold firstBTwoRootLowerNumerator firstBTwoRootLowerDenominator at lower scaled
    omega
  have x_upper : x ≤ 213 := by
    by_contra x_large
    have x_ge : 214 ≤ x := by omega
    have scaled := Int.mul_le_mul_of_nonneg_right
      (show (214 : ℤ) ≤ x by exact_mod_cast x_ge)
      (show (0 : ℤ) ≤ firstBTwoRootUpperDenominator y by
        unfold firstBTwoRootUpperDenominator
        positivity)
    unfold firstBTwoRootUpperNumerator firstBTwoRootUpperDenominator at upper scaled
    omega
  have y_upper : y ≤ 520 := by
    have scaled := Int.mul_le_mul_of_nonneg_right
      (show (x : ℤ) ≤ 213 by exact_mod_cast x_upper)
      (show (0 : ℤ) ≤ firstBTwoRootLowerDenominator y by
        unfold firstBTwoRootLowerDenominator
        positivity)
    unfold firstBTwoRootLowerNumerator firstBTwoRootLowerDenominator at lower scaled
    omega
  exact ⟨x_lower, x_upper, y_upper⟩

/-- Every integral root window with `y ≥ 2` belongs to one of twelve compressed ranges. -/
theorem firstBTwoRootWindow_candidates
    (x y : Nat) (wait_large : 2 ≤ y) (window : FirstBTwoRootWindow x y) :
    FirstBTwoRootCandidate x y := by
  rcases firstBTwoRootWindow_coarse x y wait_large window with
    ⟨x_lower, x_upper, y_upper⟩
  rcases firstBTwoRootWindow_cross x y window with ⟨lower, upper⟩
  unfold FirstBTwoRootCandidate
  interval_cases x <;>
    norm_num [firstBTwoRootLowerNumerator, firstBTwoRootLowerDenominator,
      firstBTwoRootUpperNumerator, firstBTwoRootUpperDenominator] at lower upper ⊢ <;>
    omega

/-- Explicit normalized root bounds feed the twelve-range classifier directly. -/
theorem firstBTwoRootCandidate_of_bounds
    (x y : Nat) (wait_large : 2 ≤ y)
    (lower : firstBTwoRootLower y ≤ x) (upper : x ≤ firstBTwoRootUpper y) :
    FirstBTwoRootCandidate x y :=
  firstBTwoRootWindow_candidates x y wait_large ⟨lower, upper⟩

private theorem firstBTwoRootCandidate_cross
    (x y : Nat) (candidate : FirstBTwoRootCandidate x y) :
    firstBTwoRootLowerNumerator y ≤ (x : ℤ) * firstBTwoRootLowerDenominator y ∧
      (x : ℤ) * firstBTwoRootUpperDenominator y ≤ firstBTwoRootUpperNumerator y := by
  rcases candidate with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, y_lower, y_upper⟩ | ⟨rfl, y_lower, y_upper⟩ |
    ⟨rfl, y_lower, y_upper⟩ | ⟨rfl, y_lower, y_upper⟩
  · norm_num [firstBTwoRootLowerNumerator, firstBTwoRootLowerDenominator,
      firstBTwoRootUpperNumerator, firstBTwoRootUpperDenominator]
  · norm_num [firstBTwoRootLowerNumerator, firstBTwoRootLowerDenominator,
      firstBTwoRootUpperNumerator, firstBTwoRootUpperDenominator]
  · norm_num [firstBTwoRootLowerNumerator, firstBTwoRootLowerDenominator,
      firstBTwoRootUpperNumerator, firstBTwoRootUpperDenominator]
  · norm_num [firstBTwoRootLowerNumerator, firstBTwoRootLowerDenominator,
      firstBTwoRootUpperNumerator, firstBTwoRootUpperDenominator]
  · norm_num [firstBTwoRootLowerNumerator, firstBTwoRootLowerDenominator,
      firstBTwoRootUpperNumerator, firstBTwoRootUpperDenominator]
  · norm_num [firstBTwoRootLowerNumerator, firstBTwoRootLowerDenominator,
      firstBTwoRootUpperNumerator, firstBTwoRootUpperDenominator]
  · norm_num [firstBTwoRootLowerNumerator, firstBTwoRootLowerDenominator,
      firstBTwoRootUpperNumerator, firstBTwoRootUpperDenominator]
  · norm_num [firstBTwoRootLowerNumerator, firstBTwoRootLowerDenominator,
      firstBTwoRootUpperNumerator, firstBTwoRootUpperDenominator]
  · interval_cases y <;>
      norm_num [firstBTwoRootLowerNumerator, firstBTwoRootLowerDenominator,
        firstBTwoRootUpperNumerator, firstBTwoRootUpperDenominator]
  · interval_cases y <;>
      norm_num [firstBTwoRootLowerNumerator, firstBTwoRootLowerDenominator,
        firstBTwoRootUpperNumerator, firstBTwoRootUpperDenominator]
  · interval_cases y <;>
      norm_num [firstBTwoRootLowerNumerator, firstBTwoRootLowerDenominator,
        firstBTwoRootUpperNumerator, firstBTwoRootUpperDenominator]
  · interval_cases y <;>
      norm_num [firstBTwoRootLowerNumerator, firstBTwoRootLowerDenominator,
        firstBTwoRootUpperNumerator, firstBTwoRootUpperDenominator]

/-- Every one of the twelve compressed candidate ranges lies in the normalized root window. -/
theorem FirstBTwoRootCandidate.window
    {x y : Nat} (candidate : FirstBTwoRootCandidate x y) :
    FirstBTwoRootWindow x y := by
  rcases firstBTwoRootCandidate_cross x y candidate with ⟨lower, upper⟩
  exact firstBTwoRootWindow_of_cross x y lower upper

/-- For `y ≥ 2`, the normalized root window is exactly the twelve candidate ranges. -/
theorem firstBTwoRootWindow_iff_candidate (x y : Nat) (wait_large : 2 ≤ y) :
    FirstBTwoRootWindow x y ↔ FirstBTwoRootCandidate x y :=
  ⟨firstBTwoRootWindow_candidates x y wait_large, FirstBTwoRootCandidate.window⟩

end MatrixMortality.ParabolicBlade
