import MatrixMortality.ParabolicFirstBTwoReduction

/-!
# Tail certificate for the second-first-`b` cylinder

The second-first-`b` root envelope leaves seventy-seven integral outer-wait pairs.  This
module checks their tail-density rectangles and isolates the sole integral inner-wait
candidate, on the tail prefix `ccb`.
-/

namespace MatrixMortality.ParabolicBlade

/-- Encoded ternary scale of the tail following the prefix `ccb`. -/
def firstBTwoTailScale (tail : List TagLetter) : ℚ :=
  3 ^ (tagEncode 3 tail).length

/-- Complement coordinate of the tail following the prefix `ccb`. -/
def firstBTwoTailComplement (tail : List TagLetter) : ℚ :=
  tagComplementCode tail

/-- Normalized all-`c` factor on a second-first-`b` tail. -/
def firstBTwoTailA (tail : List TagLetter) (y : Nat) : ℚ :=
  2187 * (72 * y - 9) + (9 - 8 * y) / firstBTwoTailScale tail

/-- Normalized complement coordinate on a second-first-`b` tail. -/
def firstBTwoTailD (tail : List TagLetter) : ℚ :=
  39 + firstBTwoTailComplement tail / firstBTwoTailScale tail

/-- Denominator of the inner-wait root on the second-first-`b` tail rectangle. -/
def firstBTwoTailZDenominator (a d : ℚ) (x y : Nat) : ℚ :=
  a * (25766986436 - 119911680 * x) -
    d * (620717828832 * y + 631601581536 * x + 422435605080)

/-- Numerator of the inner-wait root on the second-first-`b` tail rectangle. -/
def firstBTwoTailZNumerator (a d : ℚ) (x y : Nat) : ℚ :=
  d * (58005064872 * y + 59048086536 * x + 37838186340) -
    a * (2408152393 - 11209824 * x)

/-- Lower endpoint of the normalized all-`c` coordinate on first-`b` tail cylinder `j`. -/
def firstBTwoTailALower (j : Nat) (y : Nat) : ℚ :=
  2187 * (72 * y - 9) + (9 - 8 * y) / 3 ^ (j + 5)

/-- Upper endpoint of the normalized all-`c` coordinate on every first-`b` tail cylinder. -/
def firstBTwoTailAUpper (y : Nat) : ℚ :=
  2187 * (72 * y - 9)

/-- Lower endpoint of the normalized complement coordinate on first-`b` tail cylinder `j`. -/
def firstBTwoTailDLower (j : Nat) : ℚ :=
  39 + 13 / (81 * 3 ^ j)

/-- Upper endpoint of the normalized complement coordinate on first-`b` tail cylinder `j`. -/
def firstBTwoTailDUpper (j : Nat) : ℚ :=
  39 + 39 / (242 * 3 ^ j)

/-- Membership of `(a,d)` in a closed affine rectangle. -/
structure FirstBTwoTailRectangle
    (a₀ a₁ d₀ d₁ a d : ℚ) : Prop where
  a_lower : a₀ ≤ a
  a_upper : a ≤ a₁
  d_lower : d₀ ≤ d
  d_upper : d ≤ d₁

theorem firstBTwoTail_first_b_decomposition
    (tail : List TagLetter) (contains_b : .b ∈ tail) :
    ∃ j rest, tail = List.replicate j .c ++ .b :: rest := by
  exact tagWord_first_b_decomposition tail contains_b

theorem firstBTwoTail_replicate_c_length (j : Nat) :
    (tagEncode 3 (List.replicate j .c)).length = j := by
  induction j with
  | zero => rfl
  | succ j induction =>
      rw [List.replicate_succ, tagEncode_cons, List.length_append]
      simp only [tagCode, List.length_singleton, induction]
      omega

theorem firstBTwoTail_scale_eq (j : Nat) (rest : List TagLetter) :
    firstBTwoTailScale (List.replicate j .c ++ .b :: rest) =
      3 ^ j * 243 * firstBTwoTailScale rest := by
  unfold firstBTwoTailScale
  rw [tagEncode_append, List.length_append, firstBTwoTail_replicate_c_length,
    tagEncode_cons, List.length_append]
  have b_length : (tagCode 3 .b).length = 5 := by decide
  rw [b_length, pow_add, pow_add]
  norm_num
  ring

theorem firstBTwoTail_scale_lower (j : Nat) (rest : List TagLetter) :
    (3 : ℚ) ^ (j + 5) ≤
      firstBTwoTailScale (List.replicate j .c ++ .b :: rest) := by
  rw [firstBTwoTail_scale_eq]
  have rest_scale_one : (1 : ℚ) ≤ firstBTwoTailScale rest := by
    have rest_scale_one_nat : 1 ≤ (3 : Nat) ^ (tagEncode 3 rest).length :=
      one_le_pow₀ (by norm_num)
    unfold firstBTwoTailScale
    exact_mod_cast rest_scale_one_nat
  have power_eq : (3 : ℚ) ^ (j + 5) = 3 ^ j * 243 := by
    rw [pow_add]
    norm_num
  rw [power_eq]
  nlinarith [show (0 : ℚ) < 3 ^ j by positivity]

theorem firstBTwoTail_density_bounds (j : Nat) (rest : List TagLetter) :
    let tail := List.replicate j .c ++ .b :: rest
    let T := firstBTwoTailScale tail
    let E := firstBTwoTailComplement tail
    13 * T ≤ 81 * 3 ^ j * E ∧ 242 * 3 ^ j * E ≤ 39 * T := by
  have density := tagComplementCode_first_b_density j rest
  dsimp only at density ⊢
  unfold firstBTwoTailScale firstBTwoTailComplement
  constructor
  · exact_mod_cast density.1
  · exact_mod_cast density.2.le

theorem firstBTwoTail_exact_rectangle
    (j : Nat) (rest : List TagLetter) (y : Nat) (two_le_y : 2 ≤ y) :
    let tail := List.replicate j .c ++ .b :: rest
    FirstBTwoTailRectangle
      (firstBTwoTailALower j y) (firstBTwoTailAUpper y)
      (firstBTwoTailDLower j) (firstBTwoTailDUpper j)
      (firstBTwoTailA tail y) (firstBTwoTailD tail) := by
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
  have correction_upper : (9 - 8 * (y : ℚ)) / T ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg correction_nonpositive scale_positive.le
  have density_lower : (13 : ℚ) / (81 * 3 ^ j) ≤ E / T := by
    have denominator_positive : (0 : ℚ) < 81 * 3 ^ j := by positivity
    rw [div_le_div_iff₀ denominator_positive scale_positive]
    nlinarith [density.1]
  have density_upper : E / T ≤ (39 : ℚ) / (242 * 3 ^ j) := by
    have denominator_positive : (0 : ℚ) < 242 * 3 ^ j := by positivity
    rw [div_le_div_iff₀ scale_positive denominator_positive]
    nlinarith [density.2]
  constructor
  · simpa [firstBTwoTailALower, firstBTwoTailA, tail, T] using
      add_le_add_left correction_lower (2187 * (72 * (y : ℚ) - 9))
  · simpa [firstBTwoTailAUpper, firstBTwoTailA, tail, T] using
      add_le_add_left correction_upper (2187 * (72 * (y : ℚ) - 9))
  · simpa [firstBTwoTailDLower, firstBTwoTailD, tail, T, E] using
      add_le_add_left density_lower 39
  · simpa [firstBTwoTailDUpper, firstBTwoTailD, tail, T, E] using
      add_le_add_left density_upper 39

theorem firstBTwoTail_envelope_rectangle
    (k j : Nat) (rest : List TagLetter) (y : Nat)
    (k_le_j : k ≤ j) (two_le_y : 2 ≤ y) :
    let tail := List.replicate j .c ++ .b :: rest
    FirstBTwoTailRectangle
      (firstBTwoTailALower k y) (firstBTwoTailAUpper y)
      39 (firstBTwoTailDUpper k)
      (firstBTwoTailA tail y) (firstBTwoTailD tail) := by
  let tail := List.replicate j .c ++ .b :: rest
  let T := firstBTwoTailScale tail
  let E := firstBTwoTailComplement tail
  have scale_positive : (0 : ℚ) < T := by
    dsimp [T, firstBTwoTailScale]
    positivity
  have threshold_power_order : (3 : Nat) ^ (k + 5) ≤ 3 ^ (j + 5) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have threshold_lower : (3 : ℚ) ^ (k + 5) ≤ T := by
    have body_scale_lower := firstBTwoTail_scale_lower j rest
    exact le_trans (by exact_mod_cast threshold_power_order) body_scale_lower
  have threshold_positive : (0 : ℚ) < 3 ^ (k + 5) := by positivity
  have density := firstBTwoTail_density_bounds j rest
  dsimp only [tail, T, E] at density
  have power_order : (3 : Nat) ^ k ≤ 3 ^ j :=
    Nat.pow_le_pow_right (by norm_num) k_le_j
  have density_at_k : (242 : ℚ) * 3 ^ k * E ≤ 39 * T := by
    have complement_nonnegative : (0 : ℚ) ≤ E := by
      dsimp [E, firstBTwoTailComplement]
      positivity
    have power_order_rat : (3 : ℚ) ^ k ≤ 3 ^ j := by
      exact_mod_cast power_order
    have scaled_power_order : (242 : ℚ) * 3 ^ k * E ≤ 242 * 3 ^ j * E := by
      have scaled := mul_le_mul_of_nonneg_left power_order_rat (by norm_num : (0 : ℚ) ≤ 242)
      exact mul_le_mul_of_nonneg_right scaled complement_nonnegative
    exact scaled_power_order.trans density.2
  have correction_nonpositive : (9 : ℚ) - 8 * y ≤ 0 := by
    have y_lower : (2 : ℚ) ≤ y := by exact_mod_cast two_le_y
    linarith
  have correction_lower :
      ((9 : ℚ) - 8 * y) / 3 ^ (k + 5) ≤ (9 - 8 * y) / T := by
    rw [div_le_div_iff₀ threshold_positive scale_positive]
    nlinarith
  have correction_upper : (9 - 8 * (y : ℚ)) / T ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg correction_nonpositive scale_positive.le
  have density_nonnegative : (0 : ℚ) ≤ E / T := by
    exact div_nonneg (by dsimp [E, firstBTwoTailComplement]; positivity) scale_positive.le
  have density_upper : E / T ≤ (39 : ℚ) / (242 * 3 ^ k) := by
    have denominator_positive : (0 : ℚ) < 242 * 3 ^ k := by positivity
    rw [div_le_div_iff₀ scale_positive denominator_positive]
    nlinarith
  constructor
  · simpa [firstBTwoTailALower, firstBTwoTailA, tail, T] using
      add_le_add_left correction_lower (2187 * (72 * (y : ℚ) - 9))
  · simpa [firstBTwoTailAUpper, firstBTwoTailA, tail, T] using
      add_le_add_left correction_upper (2187 * (72 * (y : ℚ) - 9))
  · simpa [firstBTwoTailD, tail, T, E] using add_le_add_left density_nonnegative 39
  · simpa [firstBTwoTailDUpper, firstBTwoTailD, tail, T, E] using
      add_le_add_left density_upper 39

theorem firstBTwoTail_affine_rectangle_pos
    (A B C a₀ a₁ d₀ d₁ a d : ℚ)
    (rectangle : FirstBTwoTailRectangle a₀ a₁ d₀ d₁ a d)
    (corner₀₀ : 0 < A * a₀ + B * d₀ + C)
    (corner₀₁ : 0 < A * a₀ + B * d₁ + C)
    (corner₁₀ : 0 < A * a₁ + B * d₀ + C)
    (corner₁₁ : 0 < A * a₁ + B * d₁ + C) :
    0 < A * a + B * d + C := by
  by_cases A_nonnegative : 0 ≤ A
  · have A_bound : A * a₀ ≤ A * a :=
      mul_le_mul_of_nonneg_left rectangle.a_lower A_nonnegative
    by_cases B_nonnegative : 0 ≤ B
    · have B_bound : B * d₀ ≤ B * d :=
        mul_le_mul_of_nonneg_left rectangle.d_lower B_nonnegative
      linarith
    · have B_bound : B * d₁ ≤ B * d :=
        mul_le_mul_of_nonpos_left rectangle.d_upper (le_of_not_ge B_nonnegative)
      linarith
  · have A_bound : A * a₁ ≤ A * a :=
      mul_le_mul_of_nonpos_left rectangle.a_upper (le_of_not_ge A_nonnegative)
    by_cases B_nonnegative : 0 ≤ B
    · have B_bound : B * d₀ ≤ B * d :=
        mul_le_mul_of_nonneg_left rectangle.d_lower B_nonnegative
      linarith
    · have B_bound : B * d₁ ≤ B * d :=
        mul_le_mul_of_nonpos_left rectangle.d_upper (le_of_not_ge B_nonnegative)
      linarith

theorem firstBTwoTailZDenominator_affine
    (s a d : ℚ) (x y : Nat) :
    s * firstBTwoTailZDenominator a d x y =
      (s * (25766986436 - 119911680 * x)) * a +
        (-s * (620717828832 * y + 631601581536 * x + 422435605080)) * d := by
  unfold firstBTwoTailZDenominator
  ring

theorem firstBTwoTailZLower_affine
    (s a d : ℚ) (x y lower : Nat) :
    s * (firstBTwoTailZNumerator a d x y -
        lower * firstBTwoTailZDenominator a d x y) =
      (s * (-(2408152393 - 11209824 * x) -
          lower * (25766986436 - 119911680 * x))) * a +
        (s * ((58005064872 * y + 59048086536 * x + 37838186340) +
          lower * (620717828832 * y + 631601581536 * x + 422435605080))) * d := by
  unfold firstBTwoTailZDenominator firstBTwoTailZNumerator
  ring

theorem firstBTwoTailZUpper_affine
    (s a d : ℚ) (x y upper : Nat) :
    s * (upper * firstBTwoTailZDenominator a d x y -
        firstBTwoTailZNumerator a d x y) =
      (s * (upper * (25766986436 - 119911680 * x) +
          (2408152393 - 11209824 * x))) * a +
        (s * (-upper *
            (620717828832 * y + 631601581536 * x + 422435605080) -
          (58005064872 * y + 59048086536 * x + 37838186340))) * d := by
  unfold firstBTwoTailZDenominator firstBTwoTailZNumerator
  ring

theorem firstBTwoTailZNegative_affine
    (s a d : ℚ) (x y : Nat) :
    -s * firstBTwoTailZNumerator a d x y =
      (s * (2408152393 - 11209824 * x)) * a +
        (-s * (58005064872 * y + 59048086536 * x + 37838186340)) * d := by
  unfold firstBTwoTailZNumerator
  ring

/-- Strict corner conditions trapping the inner-wait root in `(lower,upper)`. -/
def FirstBTwoTailOpenCorners
    (x y lower upper : Nat) (s a₀ a₁ d₀ d₁ : ℚ) : Prop :=
  0 < s * firstBTwoTailZDenominator a₀ d₀ x y ∧
    0 < s * firstBTwoTailZDenominator a₀ d₁ x y ∧
    0 < s * firstBTwoTailZDenominator a₁ d₀ x y ∧
    0 < s * firstBTwoTailZDenominator a₁ d₁ x y ∧
    0 < s * (firstBTwoTailZNumerator a₀ d₀ x y -
      lower * firstBTwoTailZDenominator a₀ d₀ x y) ∧
    0 < s * (firstBTwoTailZNumerator a₀ d₁ x y -
      lower * firstBTwoTailZDenominator a₀ d₁ x y) ∧
    0 < s * (firstBTwoTailZNumerator a₁ d₀ x y -
      lower * firstBTwoTailZDenominator a₁ d₀ x y) ∧
    0 < s * (firstBTwoTailZNumerator a₁ d₁ x y -
      lower * firstBTwoTailZDenominator a₁ d₁ x y) ∧
    0 < s * (upper * firstBTwoTailZDenominator a₀ d₀ x y -
      firstBTwoTailZNumerator a₀ d₀ x y) ∧
    0 < s * (upper * firstBTwoTailZDenominator a₀ d₁ x y -
      firstBTwoTailZNumerator a₀ d₁ x y) ∧
    0 < s * (upper * firstBTwoTailZDenominator a₁ d₀ x y -
      firstBTwoTailZNumerator a₁ d₀ x y) ∧
    0 < s * (upper * firstBTwoTailZDenominator a₁ d₁ x y -
      firstBTwoTailZNumerator a₁ d₁ x y)

/-- Strict corner conditions making the inner-wait numerator negative throughout a rectangle. -/
def FirstBTwoTailNegativeCorners
    (x y : Nat) (s a₀ a₁ d₀ d₁ : ℚ) : Prop :=
  0 < s * firstBTwoTailZDenominator a₀ d₀ x y ∧
    0 < s * firstBTwoTailZDenominator a₀ d₁ x y ∧
    0 < s * firstBTwoTailZDenominator a₁ d₀ x y ∧
    0 < s * firstBTwoTailZDenominator a₁ d₁ x y ∧
    s * firstBTwoTailZNumerator a₀ d₀ x y < 0 ∧
    s * firstBTwoTailZNumerator a₀ d₁ x y < 0 ∧
    s * firstBTwoTailZNumerator a₁ d₀ x y < 0 ∧
    s * firstBTwoTailZNumerator a₁ d₁ x y < 0

/-- Strict corner conditions placing the inner-wait root below `upper`. -/
def FirstBTwoTailUpperCorners
    (x y upper : Nat) (s a₀ a₁ d₀ d₁ : ℚ) : Prop :=
  0 < s * firstBTwoTailZDenominator a₀ d₀ x y ∧
    0 < s * firstBTwoTailZDenominator a₀ d₁ x y ∧
    0 < s * firstBTwoTailZDenominator a₁ d₀ x y ∧
    0 < s * firstBTwoTailZDenominator a₁ d₁ x y ∧
    0 < s * (upper * firstBTwoTailZDenominator a₀ d₀ x y -
      firstBTwoTailZNumerator a₀ d₀ x y) ∧
    0 < s * (upper * firstBTwoTailZDenominator a₀ d₁ x y -
      firstBTwoTailZNumerator a₀ d₁ x y) ∧
    0 < s * (upper * firstBTwoTailZDenominator a₁ d₀ x y -
      firstBTwoTailZNumerator a₁ d₀ x y) ∧
    0 < s * (upper * firstBTwoTailZDenominator a₁ d₁ x y -
      firstBTwoTailZNumerator a₁ d₁ x y)

/-- The upper half of the rectangle certificate bounds a natural inner-wait root. -/
theorem firstBTwoTailZ_lt_of_upper_corners
    (x y upper z : Nat) (s a₀ a₁ d₀ d₁ a d : ℚ)
    (rectangle : FirstBTwoTailRectangle a₀ a₁ d₀ d₁ a d)
    (corners : FirstBTwoTailUpperCorners x y upper s a₀ a₁ d₀ d₁)
    (root_eq : firstBTwoTailZDenominator a d x y * z =
      firstBTwoTailZNumerator a d x y) :
    z < upper := by
  rcases corners with
    ⟨denominator₀₀, denominator₀₁, denominator₁₀, denominator₁₁,
      upper₀₀, upper₀₁, upper₁₀, upper₁₁⟩
  let q₁ : ℚ := 25766986436 - 119911680 * x
  let j₁ : ℚ := 620717828832 * y + 631601581536 * x + 422435605080
  let q₀ : ℚ := 2408152393 - 11209824 * x
  let j₀ : ℚ := 58005064872 * y + 59048086536 * x + 37838186340
  have denominator_positive : 0 < s * firstBTwoTailZDenominator a d x y := by
    have affine := firstBTwoTail_affine_rectangle_pos (s * q₁) (-s * j₁) 0
      a₀ a₁ d₀ d₁ a d rectangle
    have result := affine
      (by simpa [q₁, j₁, firstBTwoTailZDenominator_affine] using denominator₀₀)
      (by simpa [q₁, j₁, firstBTwoTailZDenominator_affine] using denominator₀₁)
      (by simpa [q₁, j₁, firstBTwoTailZDenominator_affine] using denominator₁₀)
      (by simpa [q₁, j₁, firstBTwoTailZDenominator_affine] using denominator₁₁)
    simpa [q₁, j₁, firstBTwoTailZDenominator_affine] using result
  have upper_positive :
      0 < s * (upper * firstBTwoTailZDenominator a d x y -
        firstBTwoTailZNumerator a d x y) := by
    have affine := firstBTwoTail_affine_rectangle_pos
      (s * (upper * q₁ + q₀)) (s * (-upper * j₁ - j₀)) 0
      a₀ a₁ d₀ d₁ a d rectangle
    have result := affine
      (by simpa [q₀, q₁, j₀, j₁, firstBTwoTailZUpper_affine] using upper₀₀)
      (by simpa [q₀, q₁, j₀, j₁, firstBTwoTailZUpper_affine] using upper₀₁)
      (by simpa [q₀, q₁, j₀, j₁, firstBTwoTailZUpper_affine] using upper₁₀)
      (by simpa [q₀, q₁, j₀, j₁, firstBTwoTailZUpper_affine] using upper₁₁)
    simpa [q₀, q₁, j₀, j₁, firstBTwoTailZUpper_affine] using result
  have scaled_root_eq :
      (s * firstBTwoTailZDenominator a d x y) * z =
        s * firstBTwoTailZNumerator a d x y := by
    calc
      _ = s * (firstBTwoTailZDenominator a d x y * z) := by ring
      _ = _ := by rw [root_eq]
  have upper_rat : (z : ℚ) < upper := by
    have scaled_upper :
        (s * firstBTwoTailZDenominator a d x y) * z <
          (s * firstBTwoTailZDenominator a d x y) * upper := by
      rw [scaled_root_eq]
      nlinarith
    exact lt_of_mul_lt_mul_left scaled_upper denominator_positive.le
  exact_mod_cast upper_rat

theorem firstBTwoTailZ_mem_open_interval
    (x y lower upper z : Nat) (s a₀ a₁ d₀ d₁ a d : ℚ)
    (rectangle : FirstBTwoTailRectangle a₀ a₁ d₀ d₁ a d)
    (corners : FirstBTwoTailOpenCorners x y lower upper s a₀ a₁ d₀ d₁)
    (root_eq : firstBTwoTailZDenominator a d x y * z =
      firstBTwoTailZNumerator a d x y) :
    lower < z ∧ z < upper := by
  rcases corners with
    ⟨denominator₀₀, denominator₀₁, denominator₁₀, denominator₁₁,
      lower₀₀, lower₀₁, lower₁₀, lower₁₁,
      upper₀₀, upper₀₁, upper₁₀, upper₁₁⟩
  let q₁ : ℚ := 25766986436 - 119911680 * x
  let j₁ : ℚ := 620717828832 * y + 631601581536 * x + 422435605080
  let q₀ : ℚ := 2408152393 - 11209824 * x
  let j₀ : ℚ := 58005064872 * y + 59048086536 * x + 37838186340
  have denominator_positive : 0 < s * firstBTwoTailZDenominator a d x y := by
    have affine := firstBTwoTail_affine_rectangle_pos (s * q₁) (-s * j₁) 0
      a₀ a₁ d₀ d₁ a d rectangle
    have result := affine
      (by simpa [q₁, j₁, firstBTwoTailZDenominator_affine] using denominator₀₀)
      (by simpa [q₁, j₁, firstBTwoTailZDenominator_affine] using denominator₀₁)
      (by simpa [q₁, j₁, firstBTwoTailZDenominator_affine] using denominator₁₀)
      (by simpa [q₁, j₁, firstBTwoTailZDenominator_affine] using denominator₁₁)
    simpa [q₁, j₁, firstBTwoTailZDenominator_affine] using result
  have lower_positive :
      0 < s * (firstBTwoTailZNumerator a d x y -
        lower * firstBTwoTailZDenominator a d x y) := by
    have affine := firstBTwoTail_affine_rectangle_pos
      (s * (-q₀ - lower * q₁)) (s * (j₀ + lower * j₁)) 0
      a₀ a₁ d₀ d₁ a d rectangle
    have result := affine
      (by simpa [q₀, q₁, j₀, j₁, firstBTwoTailZLower_affine] using lower₀₀)
      (by simpa [q₀, q₁, j₀, j₁, firstBTwoTailZLower_affine] using lower₀₁)
      (by simpa [q₀, q₁, j₀, j₁, firstBTwoTailZLower_affine] using lower₁₀)
      (by simpa [q₀, q₁, j₀, j₁, firstBTwoTailZLower_affine] using lower₁₁)
    simpa [q₀, q₁, j₀, j₁, firstBTwoTailZLower_affine] using result
  have upper_positive :
      0 < s * (upper * firstBTwoTailZDenominator a d x y -
        firstBTwoTailZNumerator a d x y) := by
    have affine := firstBTwoTail_affine_rectangle_pos
      (s * (upper * q₁ + q₀)) (s * (-upper * j₁ - j₀)) 0
      a₀ a₁ d₀ d₁ a d rectangle
    have result := affine
      (by simpa [q₀, q₁, j₀, j₁, firstBTwoTailZUpper_affine] using upper₀₀)
      (by simpa [q₀, q₁, j₀, j₁, firstBTwoTailZUpper_affine] using upper₀₁)
      (by simpa [q₀, q₁, j₀, j₁, firstBTwoTailZUpper_affine] using upper₁₀)
      (by simpa [q₀, q₁, j₀, j₁, firstBTwoTailZUpper_affine] using upper₁₁)
    simpa [q₀, q₁, j₀, j₁, firstBTwoTailZUpper_affine] using result
  have scaled_root_eq :
      (s * firstBTwoTailZDenominator a d x y) * z =
        s * firstBTwoTailZNumerator a d x y := by
    calc
      _ = s * (firstBTwoTailZDenominator a d x y * z) := by ring
      _ = _ := by rw [root_eq]
  have lower_rat : (lower : ℚ) < z := by
    have scaled_lower :
        (s * firstBTwoTailZDenominator a d x y) * lower <
          (s * firstBTwoTailZDenominator a d x y) * z := by
      rw [scaled_root_eq]
      nlinarith
    exact lt_of_mul_lt_mul_left scaled_lower denominator_positive.le
  have upper_rat : (z : ℚ) < upper := by
    have scaled_upper :
        (s * firstBTwoTailZDenominator a d x y) * z <
          (s * firstBTwoTailZDenominator a d x y) * upper := by
      rw [scaled_root_eq]
      nlinarith
    exact lt_of_mul_lt_mul_left scaled_upper denominator_positive.le
  exact ⟨by exact_mod_cast lower_rat, by exact_mod_cast upper_rat⟩

theorem firstBTwoTailZ_no_nat_of_gap
    (x y gap z : Nat) (s a₀ a₁ d₀ d₁ a d : ℚ)
    (rectangle : FirstBTwoTailRectangle a₀ a₁ d₀ d₁ a d)
    (corners : FirstBTwoTailOpenCorners x y gap (gap + 1) s a₀ a₁ d₀ d₁)
    (root_eq : firstBTwoTailZDenominator a d x y * z =
      firstBTwoTailZNumerator a d x y) :
    False := by
  have interval := firstBTwoTailZ_mem_open_interval
    x y gap (gap + 1) z s a₀ a₁ d₀ d₁ a d rectangle corners root_eq
  omega

theorem firstBTwoTailZ_no_nat_of_negative
    (x y z : Nat) (s a₀ a₁ d₀ d₁ a d : ℚ)
    (rectangle : FirstBTwoTailRectangle a₀ a₁ d₀ d₁ a d)
    (corners : FirstBTwoTailNegativeCorners x y s a₀ a₁ d₀ d₁)
    (root_eq : firstBTwoTailZDenominator a d x y * z =
      firstBTwoTailZNumerator a d x y) :
    False := by
  rcases corners with
    ⟨denominator₀₀, denominator₀₁, denominator₁₀, denominator₁₁,
      negative₀₀, negative₀₁, negative₁₀, negative₁₁⟩
  let q₁ : ℚ := 25766986436 - 119911680 * x
  let j₁ : ℚ := 620717828832 * y + 631601581536 * x + 422435605080
  let q₀ : ℚ := 2408152393 - 11209824 * x
  let j₀ : ℚ := 58005064872 * y + 59048086536 * x + 37838186340
  have denominator_positive : 0 < s * firstBTwoTailZDenominator a d x y := by
    have affine := firstBTwoTail_affine_rectangle_pos (s * q₁) (-s * j₁) 0
      a₀ a₁ d₀ d₁ a d rectangle
    have result := affine
      (by simpa [q₁, j₁, firstBTwoTailZDenominator_affine] using denominator₀₀)
      (by simpa [q₁, j₁, firstBTwoTailZDenominator_affine] using denominator₀₁)
      (by simpa [q₁, j₁, firstBTwoTailZDenominator_affine] using denominator₁₀)
      (by simpa [q₁, j₁, firstBTwoTailZDenominator_affine] using denominator₁₁)
    simpa [q₁, j₁, firstBTwoTailZDenominator_affine] using result
  have numerator_negative : s * firstBTwoTailZNumerator a d x y < 0 := by
    have affine := firstBTwoTail_affine_rectangle_pos (s * q₀) (-s * j₀) 0
      a₀ a₁ d₀ d₁ a d rectangle
    have result := affine
      (by rw [← firstBTwoTailZNegative_affine]; nlinarith)
      (by rw [← firstBTwoTailZNegative_affine]; nlinarith)
      (by rw [← firstBTwoTailZNegative_affine]; nlinarith)
      (by rw [← firstBTwoTailZNegative_affine]; nlinarith)
    have negated : 0 < -s * firstBTwoTailZNumerator a d x y := by
      rw [firstBTwoTailZNegative_affine]
      simpa [q₀, j₀] using result
    nlinarith
  have scaled_root_eq :
      (s * firstBTwoTailZDenominator a d x y) * z =
        s * firstBTwoTailZNumerator a d x y := by
    calc
      _ = s * (firstBTwoTailZDenominator a d x y * z) := by ring
      _ = _ := by rw [root_eq]
  have z_nonnegative : (0 : ℚ) ≤ z := by positivity
  nlinarith


end MatrixMortality.ParabolicBlade
