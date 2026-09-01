import MatrixMortality.ParabolicFirstBLateReduction
import MatrixMortality.ParabolicFirstBOneOuterSuffixCore

/-!
# Tail rectangles for later first-`b` cylinders

Removing the first body `b` leaves the same two normalized suffix coordinates at every
leading position. The position changes only the all-`c` scale coefficient.
-/

namespace MatrixMortality.ParabolicBlade

/-- Normalized all-`c` coordinate after a first `b` at position `k`. -/
def firstBLateTailA (k : Nat) (tail : List TagLetter) (y : Nat) : ℚ :=
  firstBLatePrefixScale k * (72 * y - 9) +
    (9 - 8 * y) / firstBTwoTailScale tail

/-- Lower all-`c` endpoint when the finite-scale correction is nonpositive. -/
def firstBLateTailALower (k j y : Nat) : ℚ :=
  firstBLatePrefixScale k * (72 * y - 9) + (9 - 8 * y) / 3 ^ (j + 5)

/-- Limiting all-`c` endpoint of a later-position tail rectangle. -/
def firstBLateTailABase (k y : Nat) : ℚ :=
  firstBLatePrefixScale k * (72 * y - 9)

/-- Upper all-`c` endpoint when the finite-scale correction is nonnegative. -/
def firstBLateTailAPositiveUpper (k j y : Nat) : ℚ :=
  firstBLatePrefixScale k * (72 * y - 9) + (9 - 8 * y) / 3 ^ (j + 5)

/-- A physical later-position zero satisfies the outer-root equation in the canonical tail
coordinates. -/
theorem firstBLateTail_outer_root_eq_of_core_zero
    (k : Nat) (tail : List TagLetter) (x y z : Nat)
    (core_zero :
      bZeroBDefectCOneCodeCore
        ((3 : ℚ) ^
          (tagEncode 3 (List.replicate k .c ++ .b :: tail)).length)
        (ternaryCode (tagEncode 3 (List.replicate k .c ++ .b :: tail))) x y z = 0) :
    parabolicOuterRootDenominator
      (firstBLateTailA k tail y) (firstBTwoTailD tail) z * x =
        parabolicOuterRootNumerator
          (firstBLateTailA k tail y) (firstBTwoTailD tail) y z := by
  have root_eq := firstBLate_normalized_root_eq_of_core_zero k tail x y z core_zero
  dsimp only at root_eq
  simpa [firstBLateTailA, firstBTwoTailD, firstBTwoTailScale,
    firstBTwoTailComplement] using root_eq

/-- A physical later-position zero satisfies the inner-root equation in the canonical tail
coordinates. -/
theorem firstBLateTail_inner_root_eq_of_core_zero
    (k : Nat) (tail : List TagLetter) (x y z : Nat)
    (core_zero :
      bZeroBDefectCOneCodeCore
        ((3 : ℚ) ^
          (tagEncode 3 (List.replicate k .c ++ .b :: tail)).length)
        (ternaryCode (tagEncode 3 (List.replicate k .c ++ .b :: tail))) x y z = 0) :
    firstBTwoTailZDenominator
      (firstBLateTailA k tail y) (firstBTwoTailD tail) x y * z =
        firstBTwoTailZNumerator
          (firstBLateTailA k tail y) (firstBTwoTailD tail) x y := by
  have root_eq := firstBLate_z_equation_of_core_zero k tail x y z core_zero
  dsimp only at root_eq
  simpa [firstBLateTailA, firstBTwoTailD, firstBTwoTailScale,
    firstBTwoTailComplement] using root_eq

/-- Exact tail rectangle for middle waits at least two. -/
theorem firstBLateTail_exact_rectangle
    (k j : Nat) (rest : List TagLetter) (y : Nat) (two_le_y : 2 ≤ y) :
    let tail := List.replicate j .c ++ .b :: rest
    FirstBTwoTailRectangle
      (firstBLateTailALower k j y) (firstBLateTailABase k y)
      (firstBTwoTailDLower j) (firstBTwoTailDUpper j)
      (firstBLateTailA k tail y) (firstBTwoTailD tail) := by
  let tail := List.replicate j .c ++ .b :: rest
  let T := firstBTwoTailScale tail
  let E := firstBTwoTailComplement tail
  have scale_positive : (0 : ℚ) < T := by
    dsimp [T, firstBTwoTailScale]
    positivity
  have threshold_positive : (0 : ℚ) < 3 ^ (j + 5) := by positivity
  have scale_lower : (3 : ℚ) ^ (j + 5) ≤ T := by
    dsimp only [T, tail]
    exact firstBTwoTail_scale_lower j rest
  have density := firstBTwoTail_density_bounds j rest
  dsimp only [tail, T, E] at density
  have correction_nonpositive : (9 : ℚ) - 8 * y ≤ 0 := by
    have y_lower : (2 : ℚ) ≤ y := by exact_mod_cast two_le_y
    linarith
  have correction_lower :
      ((9 : ℚ) - 8 * y) / 3 ^ (j + 5) ≤ (9 - 8 * y) / T := by
    rw [div_le_div_iff₀ threshold_positive scale_positive]
    nlinarith
  have correction_upper : (9 - 8 * (y : ℚ)) / T ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg correction_nonpositive scale_positive.le
  have density_lower : (13 : ℚ) / (81 * 3 ^ j) ≤ E / T := by
    have denominator_positive : (0 : ℚ) < 81 * 3 ^ j := by positivity
    rw [div_le_div_iff₀ denominator_positive scale_positive]
    nlinarith [density.1]
  have density_upper : E / T ≤ (39 : ℚ) / (242 * 3 ^ j) := by
    have denominator_positive : (0 : ℚ) < 242 * 3 ^ j := by positivity
    rw [div_le_div_iff₀ scale_positive denominator_positive]
    nlinarith [density.2]
  constructor
  · simpa [firstBLateTailALower, firstBLateTailA, tail, T] using
      add_le_add_left correction_lower
        ((firstBLatePrefixScale k : ℚ) * (72 * y - 9))
  · simpa [firstBLateTailABase, firstBLateTailA, tail, T] using
      add_le_add_left correction_upper
        ((firstBLatePrefixScale k : ℚ) * (72 * y - 9))
  · simpa [firstBTwoTailDLower, firstBTwoTailD, tail, T, E] using
      add_le_add_left density_lower 39
  · simpa [firstBTwoTailDUpper, firstBTwoTailD, tail, T, E] using
      add_le_add_left density_upper 39

/-- Uniform tail rectangle for all later first-`b` positions at least `threshold`. -/
theorem firstBLateTail_envelope_rectangle
    (k threshold j : Nat) (rest : List TagLetter) (y : Nat)
    (threshold_le_j : threshold ≤ j) (two_le_y : 2 ≤ y) :
    let tail := List.replicate j .c ++ .b :: rest
    FirstBTwoTailRectangle
      (firstBLateTailALower k threshold y) (firstBLateTailABase k y)
      39 (firstBTwoTailDUpper threshold)
      (firstBLateTailA k tail y) (firstBTwoTailD tail) := by
  let tail := List.replicate j .c ++ .b :: rest
  let T := firstBTwoTailScale tail
  let E := firstBTwoTailComplement tail
  have scale_positive : (0 : ℚ) < T := by
    dsimp [T, firstBTwoTailScale]
    positivity
  have threshold_power_order :
      (3 : Nat) ^ (threshold + 5) ≤ 3 ^ (j + 5) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have threshold_lower : (3 : ℚ) ^ (threshold + 5) ≤ T := by
    exact le_trans (by exact_mod_cast threshold_power_order)
      (firstBTwoTail_scale_lower j rest)
  have threshold_positive : (0 : ℚ) < 3 ^ (threshold + 5) := by positivity
  have density := firstBTwoTail_density_bounds j rest
  dsimp only [tail, T, E] at density
  have power_order : (3 : Nat) ^ threshold ≤ 3 ^ j :=
    Nat.pow_le_pow_right (by norm_num) threshold_le_j
  have density_at_threshold : (242 : ℚ) * 3 ^ threshold * E ≤ 39 * T := by
    have complement_nonnegative : (0 : ℚ) ≤ E := by
      dsimp [E, firstBTwoTailComplement]
      positivity
    have power_order_rat : (3 : ℚ) ^ threshold ≤ 3 ^ j := by
      exact_mod_cast power_order
    have scaled_power_order :
        (242 : ℚ) * 3 ^ threshold * E ≤ 242 * 3 ^ j * E := by
      have scaled := mul_le_mul_of_nonneg_left power_order_rat
        (by norm_num : (0 : ℚ) ≤ 242)
      exact mul_le_mul_of_nonneg_right scaled complement_nonnegative
    exact scaled_power_order.trans density.2
  have correction_nonpositive : (9 : ℚ) - 8 * y ≤ 0 := by
    have y_lower : (2 : ℚ) ≤ y := by exact_mod_cast two_le_y
    linarith
  have correction_lower :
      ((9 : ℚ) - 8 * y) / 3 ^ (threshold + 5) ≤ (9 - 8 * y) / T := by
    rw [div_le_div_iff₀ threshold_positive scale_positive]
    nlinarith
  have correction_upper : (9 - 8 * (y : ℚ)) / T ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg correction_nonpositive scale_positive.le
  have density_nonnegative : (0 : ℚ) ≤ E / T := by
    exact div_nonneg (by dsimp [E, firstBTwoTailComplement]; positivity)
      scale_positive.le
  have density_upper : E / T ≤ (39 : ℚ) / (242 * 3 ^ threshold) := by
    have denominator_positive : (0 : ℚ) < 242 * 3 ^ threshold := by positivity
    rw [div_le_div_iff₀ scale_positive denominator_positive]
    nlinarith
  constructor
  · simpa [firstBLateTailALower, firstBLateTailA, tail, T] using
      add_le_add_left correction_lower
        ((firstBLatePrefixScale k : ℚ) * (72 * y - 9))
  · simpa [firstBLateTailABase, firstBLateTailA, tail, T] using
      add_le_add_left correction_upper
        ((firstBLatePrefixScale k : ℚ) * (72 * y - 9))
  · simpa [firstBTwoTailD, tail, T, E] using add_le_add_left density_nonnegative 39
  · simpa [firstBTwoTailDUpper, firstBTwoTailD, tail, T, E] using
      add_le_add_left density_upper 39

/-- Exact tail rectangle when the finite-scale correction is nonnegative. -/
theorem firstBLateTail_positive_exact_rectangle
    (k j : Nat) (rest : List TagLetter) (y : Nat) (y_le_one : y ≤ 1) :
    let tail := List.replicate j .c ++ .b :: rest
    FirstBTwoTailRectangle
      (firstBLateTailABase k y) (firstBLateTailAPositiveUpper k j y)
      (firstBTwoTailDLower j) (firstBTwoTailDUpper j)
      (firstBLateTailA k tail y) (firstBTwoTailD tail) := by
  let tail := List.replicate j .c ++ .b :: rest
  let T := firstBTwoTailScale tail
  let E := firstBTwoTailComplement tail
  have scale_positive : (0 : ℚ) < T := by
    dsimp [T, firstBTwoTailScale]
    positivity
  have threshold_positive : (0 : ℚ) < 3 ^ (j + 5) := by positivity
  have scale_lower : (3 : ℚ) ^ (j + 5) ≤ T := by
    dsimp only [T, tail]
    exact firstBTwoTail_scale_lower j rest
  have density := firstBTwoTail_density_bounds j rest
  dsimp only [tail, T, E] at density
  have correction_nonnegative : (0 : ℚ) ≤ 9 - 8 * y := by
    have y_upper : (y : ℚ) ≤ 1 := by exact_mod_cast y_le_one
    linarith
  have correction_lower : (0 : ℚ) ≤ (9 - 8 * y) / T := by positivity
  have correction_upper :
      ((9 : ℚ) - 8 * y) / T ≤ (9 - 8 * y) / 3 ^ (j + 5) := by
    rw [div_le_div_iff₀ scale_positive threshold_positive]
    nlinarith
  have density_lower : (13 : ℚ) / (81 * 3 ^ j) ≤ E / T := by
    have denominator_positive : (0 : ℚ) < 81 * 3 ^ j := by positivity
    rw [div_le_div_iff₀ denominator_positive scale_positive]
    nlinarith [density.1]
  have density_upper : E / T ≤ (39 : ℚ) / (242 * 3 ^ j) := by
    have denominator_positive : (0 : ℚ) < 242 * 3 ^ j := by positivity
    rw [div_le_div_iff₀ scale_positive denominator_positive]
    nlinarith [density.2]
  constructor
  · simpa [firstBLateTailABase, firstBLateTailA, tail, T] using
      add_le_add_left correction_lower
        ((firstBLatePrefixScale k : ℚ) * (72 * y - 9))
  · simpa [firstBLateTailAPositiveUpper, firstBLateTailA, tail, T] using
      add_le_add_left correction_upper
        ((firstBLatePrefixScale k : ℚ) * (72 * y - 9))
  · simpa [firstBTwoTailDLower, firstBTwoTailD, tail, T, E] using
      add_le_add_left density_lower 39
  · simpa [firstBTwoTailDUpper, firstBTwoTailD, tail, T, E] using
      add_le_add_left density_upper 39

/-- Uniform nonnegative-correction rectangle beyond a tail-position threshold. -/
theorem firstBLateTail_positive_envelope_rectangle
    (k threshold j : Nat) (rest : List TagLetter) (y : Nat)
    (threshold_le_j : threshold ≤ j) (y_le_one : y ≤ 1) :
    let tail := List.replicate j .c ++ .b :: rest
    FirstBTwoTailRectangle
      (firstBLateTailABase k y) (firstBLateTailAPositiveUpper k threshold y)
      39 (firstBTwoTailDUpper threshold)
      (firstBLateTailA k tail y) (firstBTwoTailD tail) := by
  let tail := List.replicate j .c ++ .b :: rest
  let T := firstBTwoTailScale tail
  let E := firstBTwoTailComplement tail
  have scale_positive : (0 : ℚ) < T := by
    dsimp [T, firstBTwoTailScale]
    positivity
  have threshold_power_order :
      (3 : Nat) ^ (threshold + 5) ≤ 3 ^ (j + 5) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have threshold_lower : (3 : ℚ) ^ (threshold + 5) ≤ T :=
    le_trans (by exact_mod_cast threshold_power_order)
      (firstBTwoTail_scale_lower j rest)
  have threshold_positive : (0 : ℚ) < 3 ^ (threshold + 5) := by positivity
  have density := firstBTwoTail_density_bounds j rest
  dsimp only [tail, T, E] at density
  have power_order : (3 : Nat) ^ threshold ≤ 3 ^ j :=
    Nat.pow_le_pow_right (by norm_num) threshold_le_j
  have density_at_threshold : (242 : ℚ) * 3 ^ threshold * E ≤ 39 * T := by
    have complement_nonnegative : (0 : ℚ) ≤ E := by
      dsimp [E, firstBTwoTailComplement]
      positivity
    have power_order_rat : (3 : ℚ) ^ threshold ≤ 3 ^ j := by
      exact_mod_cast power_order
    have scaled_power_order :
        (242 : ℚ) * 3 ^ threshold * E ≤ 242 * 3 ^ j * E := by
      have scaled := mul_le_mul_of_nonneg_left power_order_rat
        (by norm_num : (0 : ℚ) ≤ 242)
      exact mul_le_mul_of_nonneg_right scaled complement_nonnegative
    exact scaled_power_order.trans density.2
  have correction_nonnegative : (0 : ℚ) ≤ 9 - 8 * y := by
    have y_upper : (y : ℚ) ≤ 1 := by exact_mod_cast y_le_one
    linarith
  have correction_lower : (0 : ℚ) ≤ (9 - 8 * y) / T := by positivity
  have correction_upper :
      ((9 : ℚ) - 8 * y) / T ≤ (9 - 8 * y) / 3 ^ (threshold + 5) := by
    rw [div_le_div_iff₀ scale_positive threshold_positive]
    nlinarith
  have density_nonnegative : (0 : ℚ) ≤ E / T := by
    exact div_nonneg (by dsimp [E, firstBTwoTailComplement]; positivity)
      scale_positive.le
  have density_upper : E / T ≤ (39 : ℚ) / (242 * 3 ^ threshold) := by
    have denominator_positive : (0 : ℚ) < 242 * 3 ^ threshold := by positivity
    rw [div_le_div_iff₀ scale_positive denominator_positive]
    nlinarith
  constructor
  · simpa [firstBLateTailABase, firstBLateTailA, tail, T] using
      add_le_add_left correction_lower
        ((firstBLatePrefixScale k : ℚ) * (72 * y - 9))
  · simpa [firstBLateTailAPositiveUpper, firstBLateTailA, tail, T] using
      add_le_add_left correction_upper
        ((firstBLatePrefixScale k : ℚ) * (72 * y - 9))
  · simpa [firstBTwoTailD, tail, T, E] using add_le_add_left density_nonnegative 39
  · simpa [firstBTwoTailDUpper, firstBTwoTailD, tail, T, E] using
      add_le_add_left density_upper 39

theorem firstBLateOuterDenominator_affine (s a d : ℚ) (z : Nat) :
    s * parabolicOuterRootDenominator a d z =
      (s * (119911680 * z + 11209824)) * a +
        (s * (631601581536 * z + 59048086536)) * d := by
  unfold parabolicOuterRootDenominator
  ring

theorem firstBLateOuterLower_affine
    (s a d : ℚ) (y z lower : Nat) :
    s * (parabolicOuterRootNumerator a d y z -
        lower * parabolicOuterRootDenominator a d z) =
      (s * ((25766986436 * z + 2408152393) -
        lower * (119911680 * z + 11209824))) * a +
      (s * (-((620717828832 * y + 422435605080) * z +
        58005064872 * y + 37838186340) -
        lower * (631601581536 * z + 59048086536))) * d := by
  unfold parabolicOuterRootNumerator parabolicOuterRootDenominator
  ring

theorem firstBLateOuterUpper_affine
    (s a d : ℚ) (y z upper : Nat) :
    s * (upper * parabolicOuterRootDenominator a d z -
        parabolicOuterRootNumerator a d y z) =
      (s * (upper * (119911680 * z + 11209824) -
        (25766986436 * z + 2408152393))) * a +
      (s * (upper * (631601581536 * z + 59048086536) +
        ((620717828832 * y + 422435605080) * z +
          58005064872 * y + 37838186340))) * d := by
  unfold parabolicOuterRootNumerator parabolicOuterRootDenominator
  ring

/-- Strict corner conditions trapping the outer-wait root in `(lower,upper)`. -/
def FirstBLateOuterOpenCorners
    (y lower upper z : Nat) (s a₀ a₁ d₀ d₁ : ℚ) : Prop :=
  0 < s * parabolicOuterRootDenominator a₀ d₀ z ∧
    0 < s * parabolicOuterRootDenominator a₀ d₁ z ∧
    0 < s * parabolicOuterRootDenominator a₁ d₀ z ∧
    0 < s * parabolicOuterRootDenominator a₁ d₁ z ∧
    0 < s * (parabolicOuterRootNumerator a₀ d₀ y z -
      lower * parabolicOuterRootDenominator a₀ d₀ z) ∧
    0 < s * (parabolicOuterRootNumerator a₀ d₁ y z -
      lower * parabolicOuterRootDenominator a₀ d₁ z) ∧
    0 < s * (parabolicOuterRootNumerator a₁ d₀ y z -
      lower * parabolicOuterRootDenominator a₁ d₀ z) ∧
    0 < s * (parabolicOuterRootNumerator a₁ d₁ y z -
      lower * parabolicOuterRootDenominator a₁ d₁ z) ∧
    0 < s * (upper * parabolicOuterRootDenominator a₀ d₀ z -
      parabolicOuterRootNumerator a₀ d₀ y z) ∧
    0 < s * (upper * parabolicOuterRootDenominator a₀ d₁ z -
      parabolicOuterRootNumerator a₀ d₁ y z) ∧
    0 < s * (upper * parabolicOuterRootDenominator a₁ d₀ z -
      parabolicOuterRootNumerator a₁ d₀ y z) ∧
    0 < s * (upper * parabolicOuterRootDenominator a₁ d₁ z -
      parabolicOuterRootNumerator a₁ d₁ y z)

/-- A normalized outer root lies in the open interval certified at all rectangle corners. -/
theorem firstBLateOuter_mem_open_interval
    (x y lower upper z : Nat) (s a₀ a₁ d₀ d₁ a d : ℚ)
    (rectangle : FirstBTwoTailRectangle a₀ a₁ d₀ d₁ a d)
    (corners : FirstBLateOuterOpenCorners y lower upper z s a₀ a₁ d₀ d₁)
    (root_eq : parabolicOuterRootDenominator a d z * x =
      parabolicOuterRootNumerator a d y z) :
    lower < x ∧ x < upper := by
  rcases corners with
    ⟨denominator₀₀, denominator₀₁, denominator₁₀, denominator₁₁,
      lower₀₀, lower₀₁, lower₁₀, lower₁₁,
      upper₀₀, upper₀₁, upper₁₀, upper₁₁⟩
  let A : ℚ := 119911680 * z + 11209824
  let B : ℚ := 631601581536 * z + 59048086536
  let C : ℚ := 25766986436 * z + 2408152393
  let E : ℚ := (620717828832 * y + 422435605080) * z +
    58005064872 * y + 37838186340
  have denominator_positive : 0 < s * parabolicOuterRootDenominator a d z := by
    have affine := firstBTwoTail_affine_rectangle_pos (s * A) (s * B) 0
      a₀ a₁ d₀ d₁ a d rectangle
    have result := affine
      (by rw [← firstBLateOuterDenominator_affine]; simpa using denominator₀₀)
      (by rw [← firstBLateOuterDenominator_affine]; simpa using denominator₀₁)
      (by rw [← firstBLateOuterDenominator_affine]; simpa using denominator₁₀)
      (by rw [← firstBLateOuterDenominator_affine]; simpa using denominator₁₁)
    rw [firstBLateOuterDenominator_affine]
    simpa only [A, B, add_zero] using result
  have lower_positive :
      0 < s * (parabolicOuterRootNumerator a d y z -
        lower * parabolicOuterRootDenominator a d z) := by
    have affine := firstBTwoTail_affine_rectangle_pos
      (s * (C - lower * A)) (s * (-E - lower * B)) 0
      a₀ a₁ d₀ d₁ a d rectangle
    have result := affine
      (by rw [← firstBLateOuterLower_affine]; simpa using lower₀₀)
      (by rw [← firstBLateOuterLower_affine]; simpa using lower₀₁)
      (by rw [← firstBLateOuterLower_affine]; simpa using lower₁₀)
      (by rw [← firstBLateOuterLower_affine]; simpa using lower₁₁)
    rw [firstBLateOuterLower_affine]
    simpa only [A, B, C, E, add_zero] using result
  have upper_positive :
      0 < s * (upper * parabolicOuterRootDenominator a d z -
        parabolicOuterRootNumerator a d y z) := by
    have affine := firstBTwoTail_affine_rectangle_pos
      (s * (upper * A - C)) (s * (upper * B + E)) 0
      a₀ a₁ d₀ d₁ a d rectangle
    have result := affine
      (by rw [← firstBLateOuterUpper_affine]; simpa using upper₀₀)
      (by rw [← firstBLateOuterUpper_affine]; simpa using upper₀₁)
      (by rw [← firstBLateOuterUpper_affine]; simpa using upper₁₀)
      (by rw [← firstBLateOuterUpper_affine]; simpa using upper₁₁)
    rw [firstBLateOuterUpper_affine]
    simpa only [A, B, C, E, add_zero] using result
  have scaled_root_eq :
      (s * parabolicOuterRootDenominator a d z) * x =
        s * parabolicOuterRootNumerator a d y z := by
    calc
      _ = s * (parabolicOuterRootDenominator a d z * x) := by ring
      _ = _ := by rw [root_eq]
  have lower_rat : (lower : ℚ) < x := by
    have scaled_lower :
        (s * parabolicOuterRootDenominator a d z) * lower <
          (s * parabolicOuterRootDenominator a d z) * x := by
      rw [scaled_root_eq]
      nlinarith
    exact lt_of_mul_lt_mul_left scaled_lower denominator_positive.le
  have upper_rat : (x : ℚ) < upper := by
    have scaled_upper :
        (s * parabolicOuterRootDenominator a d z) * x <
          (s * parabolicOuterRootDenominator a d z) * upper := by
      rw [scaled_root_eq]
      nlinarith
    exact lt_of_mul_lt_mul_left scaled_upper denominator_positive.le
  exact ⟨by exact_mod_cast lower_rat, by exact_mod_cast upper_rat⟩

end MatrixMortality.ParabolicBlade
