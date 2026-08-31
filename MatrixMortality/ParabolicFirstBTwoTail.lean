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

private def firstBTwoTailALower (j : Nat) (y : Nat) : ℚ :=
  2187 * (72 * y - 9) + (9 - 8 * y) / 3 ^ (j + 5)

private def firstBTwoTailAUpper (y : Nat) : ℚ :=
  2187 * (72 * y - 9)

private def firstBTwoTailDLower (j : Nat) : ℚ :=
  39 + 13 / (81 * 3 ^ j)

private def firstBTwoTailDUpper (j : Nat) : ℚ :=
  39 + 39 / (242 * 3 ^ j)

private structure FirstBTwoTailRectangle
    (a₀ a₁ d₀ d₁ a d : ℚ) : Prop where
  a_lower : a₀ ≤ a
  a_upper : a ≤ a₁
  d_lower : d₀ ≤ d
  d_upper : d ≤ d₁

private theorem firstBTwoTail_first_b_decomposition
    (tail : List TagLetter) (contains_b : .b ∈ tail) :
    ∃ j rest, tail = List.replicate j .c ++ .b :: rest := by
  induction tail with
  | nil => simp at contains_b
  | cons first tail induction =>
      cases first with
      | b =>
          exact ⟨0, tail, by simp⟩
      | c =>
          have tail_contains_b : .b ∈ tail := by simpa using contains_b
          obtain ⟨j, rest, tail_eq⟩ := induction tail_contains_b
          refine ⟨j + 1, rest, ?_⟩
          rw [List.replicate_succ, List.cons_append, tail_eq]

private theorem firstBTwoTail_replicate_c_length (j : Nat) :
    (tagEncode 3 (List.replicate j .c)).length = j := by
  induction j with
  | zero => rfl
  | succ j induction =>
      rw [List.replicate_succ, tagEncode_cons, List.length_append]
      simp only [tagCode, List.length_singleton, induction]
      omega

private theorem firstBTwoTail_scale_eq (j : Nat) (rest : List TagLetter) :
    firstBTwoTailScale (List.replicate j .c ++ .b :: rest) =
      3 ^ j * 243 * firstBTwoTailScale rest := by
  unfold firstBTwoTailScale
  rw [tagEncode_append, List.length_append, firstBTwoTail_replicate_c_length,
    tagEncode_cons, List.length_append]
  have b_length : (tagCode 3 .b).length = 5 := by decide
  rw [b_length, pow_add, pow_add]
  norm_num
  ring

private theorem firstBTwoTail_scale_lower (j : Nat) (rest : List TagLetter) :
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

private theorem firstBTwoTail_density_bounds (j : Nat) (rest : List TagLetter) :
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

private theorem firstBTwoTail_exact_rectangle
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

private theorem firstBTwoTail_envelope_rectangle
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

private theorem firstBTwoTail_affine_rectangle_pos
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

private theorem firstBTwoTailZDenominator_affine
    (s a d : ℚ) (x y : Nat) :
    s * firstBTwoTailZDenominator a d x y =
      (s * (25766986436 - 119911680 * x)) * a +
        (-s * (620717828832 * y + 631601581536 * x + 422435605080)) * d := by
  unfold firstBTwoTailZDenominator
  ring

private theorem firstBTwoTailZLower_affine
    (s a d : ℚ) (x y lower : Nat) :
    s * (firstBTwoTailZNumerator a d x y -
        lower * firstBTwoTailZDenominator a d x y) =
      (s * (-(2408152393 - 11209824 * x) -
          lower * (25766986436 - 119911680 * x))) * a +
        (s * ((58005064872 * y + 59048086536 * x + 37838186340) +
          lower * (620717828832 * y + 631601581536 * x + 422435605080))) * d := by
  unfold firstBTwoTailZDenominator firstBTwoTailZNumerator
  ring

private theorem firstBTwoTailZUpper_affine
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

private theorem firstBTwoTailZNegative_affine
    (s a d : ℚ) (x y : Nat) :
    -s * firstBTwoTailZNumerator a d x y =
      (s * (2408152393 - 11209824 * x)) * a +
        (-s * (58005064872 * y + 59048086536 * x + 37838186340)) * d := by
  unfold firstBTwoTailZNumerator
  ring

private def FirstBTwoTailOpenCorners
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

private def FirstBTwoTailNegativeCorners
    (x y : Nat) (s a₀ a₁ d₀ d₁ : ℚ) : Prop :=
  0 < s * firstBTwoTailZDenominator a₀ d₀ x y ∧
    0 < s * firstBTwoTailZDenominator a₀ d₁ x y ∧
    0 < s * firstBTwoTailZDenominator a₁ d₀ x y ∧
    0 < s * firstBTwoTailZDenominator a₁ d₁ x y ∧
    s * firstBTwoTailZNumerator a₀ d₀ x y < 0 ∧
    s * firstBTwoTailZNumerator a₀ d₁ x y < 0 ∧
    s * firstBTwoTailZNumerator a₁ d₀ x y < 0 ∧
    s * firstBTwoTailZNumerator a₁ d₁ x y < 0

private theorem firstBTwoTailZ_mem_open_interval
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

private theorem firstBTwoTailZ_no_nat_of_gap
    (x y gap z : Nat) (s a₀ a₁ d₀ d₁ a d : ℚ)
    (rectangle : FirstBTwoTailRectangle a₀ a₁ d₀ d₁ a d)
    (corners : FirstBTwoTailOpenCorners x y gap (gap + 1) s a₀ a₁ d₀ d₁)
    (root_eq : firstBTwoTailZDenominator a d x y * z =
      firstBTwoTailZNumerator a d x y) :
    False := by
  have interval := firstBTwoTailZ_mem_open_interval
    x y gap (gap + 1) z s a₀ a₁ d₀ d₁ a d rectangle corners root_eq
  omega

private theorem firstBTwoTailZ_no_nat_of_negative
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

-- BEGIN GENERATED SECOND-FIRST-B TAIL CERTIFICATE

private theorem firstBTwoTail_root_183_8
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 8)
          (firstBTwoTailD tail) 183 8 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 8)
          (firstBTwoTailD tail) 183 8) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 8
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 183 8 * z =
    firstBTwoTailZNumerator a d 183 8 at root_eq
  have j_cases : j = 0 ∨ 1 ≤ j := by omega
  rcases j_cases with rfl | k_le_j
  · have rectangle := firstBTwoTail_exact_rectangle 0 rest 8 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 0 8) (firstBTwoTailAUpper 8)
      (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 183 8 0 1 1
        (firstBTwoTailALower 0 8) (firstBTwoTailAUpper 8) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 183 8 0 z 1
      (firstBTwoTailALower 0 8) (firstBTwoTailAUpper 8) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_envelope_rectangle 1 j rest 8 k_le_j (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 1 8) (firstBTwoTailAUpper 8)
      39 (firstBTwoTailDUpper 1) a d at rectangle
    have corners : FirstBTwoTailNegativeCorners 183 8 1
        (firstBTwoTailALower 1 8) (firstBTwoTailAUpper 8) 39 (firstBTwoTailDUpper 1) := by
      norm_num [FirstBTwoTailNegativeCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_negative 183 8 z 1
      (firstBTwoTailALower 1 8) (firstBTwoTailAUpper 8) 39 (firstBTwoTailDUpper 1) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_186_9
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 9)
          (firstBTwoTailD tail) 186 9 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 9)
          (firstBTwoTailD tail) 186 9) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 9
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 186 9 * z =
    firstBTwoTailZNumerator a d 186 9 at root_eq
  have j_cases : j = 0 ∨ 1 ≤ j := by omega
  rcases j_cases with rfl | k_le_j
  · have rectangle := firstBTwoTail_exact_rectangle 0 rest 9 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 0 9) (firstBTwoTailAUpper 9)
      (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 186 9 0 1 1
        (firstBTwoTailALower 0 9) (firstBTwoTailAUpper 9) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 186 9 0 z 1
      (firstBTwoTailALower 0 9) (firstBTwoTailAUpper 9) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_envelope_rectangle 1 j rest 9 k_le_j (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 1 9) (firstBTwoTailAUpper 9)
      39 (firstBTwoTailDUpper 1) a d at rectangle
    have corners : FirstBTwoTailNegativeCorners 186 9 1
        (firstBTwoTailALower 1 9) (firstBTwoTailAUpper 9) 39 (firstBTwoTailDUpper 1) := by
      norm_num [FirstBTwoTailNegativeCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_negative 186 9 z 1
      (firstBTwoTailALower 1 9) (firstBTwoTailAUpper 9) 39 (firstBTwoTailDUpper 1) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_199_18
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 18)
          (firstBTwoTailD tail) 199 18 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 18)
          (firstBTwoTailD tail) 199 18) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 18
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 199 18 * z =
    firstBTwoTailZNumerator a d 199 18 at root_eq
  have j_cases : j = 0 ∨ j = 1 ∨ 2 ≤ j := by omega
  rcases j_cases with rfl | rfl | k_le_j
  · have rectangle := firstBTwoTail_exact_rectangle 0 rest 18 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 0 18) (firstBTwoTailAUpper 18)
      (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d at rectangle
    have corners : FirstBTwoTailNegativeCorners 199 18 (-1)
        (firstBTwoTailALower 0 18) (firstBTwoTailAUpper 18) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) := by
      norm_num [FirstBTwoTailNegativeCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_negative 199 18 z (-1)
      (firstBTwoTailALower 0 18) (firstBTwoTailAUpper 18) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_exact_rectangle 1 rest 18 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 1 18) (firstBTwoTailAUpper 18)
      (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) a d at rectangle
    have corners : FirstBTwoTailNegativeCorners 199 18 (-1)
        (firstBTwoTailALower 1 18) (firstBTwoTailAUpper 18) (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) := by
      norm_num [FirstBTwoTailNegativeCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_negative 199 18 z (-1)
      (firstBTwoTailALower 1 18) (firstBTwoTailAUpper 18) (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_envelope_rectangle 2 j rest 18 k_le_j (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 2 18) (firstBTwoTailAUpper 18)
      39 (firstBTwoTailDUpper 2) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 199 18 0 1 1
        (firstBTwoTailALower 2 18) (firstBTwoTailAUpper 18) 39 (firstBTwoTailDUpper 2) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 199 18 0 z 1
      (firstBTwoTailALower 2 18) (firstBTwoTailAUpper 18) 39 (firstBTwoTailDUpper 2) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_202_23
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 23)
          (firstBTwoTailD tail) 202 23 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 23)
          (firstBTwoTailD tail) 202 23) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 23
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 202 23 * z =
    firstBTwoTailZNumerator a d 202 23 at root_eq
  have j_cases : j = 0 ∨ 1 ≤ j := by omega
  rcases j_cases with rfl | k_le_j
  · have rectangle := firstBTwoTail_exact_rectangle 0 rest 23 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 0 23) (firstBTwoTailAUpper 23)
      (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d at rectangle
    have corners : FirstBTwoTailNegativeCorners 202 23 (-1)
        (firstBTwoTailALower 0 23) (firstBTwoTailAUpper 23) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) := by
      norm_num [FirstBTwoTailNegativeCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_negative 202 23 z (-1)
      (firstBTwoTailALower 0 23) (firstBTwoTailAUpper 23) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_envelope_rectangle 1 j rest 23 k_le_j (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 1 23) (firstBTwoTailAUpper 23)
      39 (firstBTwoTailDUpper 1) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 202 23 0 1 1
        (firstBTwoTailALower 1 23) (firstBTwoTailAUpper 23) 39 (firstBTwoTailDUpper 1) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 202 23 0 z 1
      (firstBTwoTailALower 1 23) (firstBTwoTailAUpper 23) 39 (firstBTwoTailDUpper 1) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_204_28
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 28)
          (firstBTwoTailD tail) 204 28 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 28)
          (firstBTwoTailD tail) 204 28) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 28
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 204 28 * z =
    firstBTwoTailZNumerator a d 204 28 at root_eq
  have j_cases : j = 0 ∨ j = 1 ∨ 2 ≤ j := by omega
  rcases j_cases with rfl | rfl | k_le_j
  · have rectangle := firstBTwoTail_exact_rectangle 0 rest 28 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 0 28) (firstBTwoTailAUpper 28)
      (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d at rectangle
    have corners : FirstBTwoTailNegativeCorners 204 28 (-1)
        (firstBTwoTailALower 0 28) (firstBTwoTailAUpper 28) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) := by
      norm_num [FirstBTwoTailNegativeCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_negative 204 28 z (-1)
      (firstBTwoTailALower 0 28) (firstBTwoTailAUpper 28) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_exact_rectangle 1 rest 28 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 1 28) (firstBTwoTailAUpper 28)
      (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 204 28 3 4 1
        (firstBTwoTailALower 1 28) (firstBTwoTailAUpper 28) (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 204 28 3 z 1
      (firstBTwoTailALower 1 28) (firstBTwoTailAUpper 28) (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_envelope_rectangle 2 j rest 28 k_le_j (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 2 28) (firstBTwoTailAUpper 28)
      39 (firstBTwoTailDUpper 2) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 204 28 0 1 1
        (firstBTwoTailALower 2 28) (firstBTwoTailAUpper 28) 39 (firstBTwoTailDUpper 2) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 204 28 0 z 1
      (firstBTwoTailALower 2 28) (firstBTwoTailAUpper 28) 39 (firstBTwoTailDUpper 2) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_206_36
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 36)
          (firstBTwoTailD tail) 206 36 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 36)
          (firstBTwoTailD tail) 206 36) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 36
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 206 36 * z =
    firstBTwoTailZNumerator a d 206 36 at root_eq
  have j_cases : j = 0 ∨ 1 ≤ j := by omega
  rcases j_cases with rfl | k_le_j
  · have rectangle := firstBTwoTail_exact_rectangle 0 rest 36 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 0 36) (firstBTwoTailAUpper 36)
      (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 206 36 0 1 1
        (firstBTwoTailALower 0 36) (firstBTwoTailAUpper 36) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 206 36 0 z 1
      (firstBTwoTailALower 0 36) (firstBTwoTailAUpper 36) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_envelope_rectangle 1 j rest 36 k_le_j (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 1 36) (firstBTwoTailAUpper 36)
      39 (firstBTwoTailDUpper 1) a d at rectangle
    have corners : FirstBTwoTailNegativeCorners 206 36 1
        (firstBTwoTailALower 1 36) (firstBTwoTailAUpper 36) 39 (firstBTwoTailDUpper 1) := by
      norm_num [FirstBTwoTailNegativeCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_negative 206 36 z 1
      (firstBTwoTailALower 1 36) (firstBTwoTailAUpper 36) 39 (firstBTwoTailDUpper 1) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_208_49
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 49)
          (firstBTwoTailD tail) 208 49 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 49)
          (firstBTwoTailD tail) 208 49) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 49
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 208 49 * z =
    firstBTwoTailZNumerator a d 208 49 at root_eq
  have j_cases : j = 0 ∨ 1 ≤ j := by omega
  rcases j_cases with rfl | k_le_j
  · have rectangle := firstBTwoTail_exact_rectangle 0 rest 49 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 0 49) (firstBTwoTailAUpper 49)
      (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d at rectangle
    have corners : FirstBTwoTailNegativeCorners 208 49 (-1)
        (firstBTwoTailALower 0 49) (firstBTwoTailAUpper 49) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) := by
      norm_num [FirstBTwoTailNegativeCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_negative 208 49 z (-1)
      (firstBTwoTailALower 0 49) (firstBTwoTailAUpper 49) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_envelope_rectangle 1 j rest 49 k_le_j (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 1 49) (firstBTwoTailAUpper 49)
      39 (firstBTwoTailDUpper 1) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 208 49 0 1 1
        (firstBTwoTailALower 1 49) (firstBTwoTailAUpper 49) 39 (firstBTwoTailDUpper 1) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 208 49 0 z 1
      (firstBTwoTailALower 1 49) (firstBTwoTailAUpper 49) 39 (firstBTwoTailDUpper 1) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_209_60
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 60)
          (firstBTwoTailD tail) 209 60 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 60)
          (firstBTwoTailD tail) 209 60) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 60
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 209 60 * z =
    firstBTwoTailZNumerator a d 209 60 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 60 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 60) (firstBTwoTailAUpper 60)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 209 60 0 1 1
      (firstBTwoTailALower 0 60) (firstBTwoTailAUpper 60) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 209 60 0 z 1
    (firstBTwoTailALower 0 60) (firstBTwoTailAUpper 60) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_210_77
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 77)
          (firstBTwoTailD tail) 210 77 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 77)
          (firstBTwoTailD tail) 210 77) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 77
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 210 77 * z =
    firstBTwoTailZNumerator a d 210 77 at root_eq
  have j_cases : j = 0 ∨ 1 ≤ j := by omega
  rcases j_cases with rfl | k_le_j
  · have rectangle := firstBTwoTail_exact_rectangle 0 rest 77 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 0 77) (firstBTwoTailAUpper 77)
      (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 210 77 1 2 1
        (firstBTwoTailALower 0 77) (firstBTwoTailAUpper 77) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 210 77 1 z 1
      (firstBTwoTailALower 0 77) (firstBTwoTailAUpper 77) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_envelope_rectangle 1 j rest 77 k_le_j (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 1 77) (firstBTwoTailAUpper 77)
      39 (firstBTwoTailDUpper 1) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 210 77 0 1 1
        (firstBTwoTailALower 1 77) (firstBTwoTailAUpper 77) 39 (firstBTwoTailDUpper 1) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 210 77 0 z 1
      (firstBTwoTailALower 1 77) (firstBTwoTailAUpper 77) 39 (firstBTwoTailDUpper 1) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_210_78
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 78)
          (firstBTwoTailD tail) 210 78 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 78)
          (firstBTwoTailD tail) 210 78) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 78
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 210 78 * z =
    firstBTwoTailZNumerator a d 210 78 at root_eq
  have j_cases : j = 0 ∨ 1 ≤ j := by omega
  rcases j_cases with rfl | k_le_j
  · have rectangle := firstBTwoTail_exact_rectangle 0 rest 78 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 0 78) (firstBTwoTailAUpper 78)
      (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 210 78 0 1 1
        (firstBTwoTailALower 0 78) (firstBTwoTailAUpper 78) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 210 78 0 z 1
      (firstBTwoTailALower 0 78) (firstBTwoTailAUpper 78) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_envelope_rectangle 1 j rest 78 k_le_j (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 1 78) (firstBTwoTailAUpper 78)
      39 (firstBTwoTailDUpper 1) a d at rectangle
    have corners : FirstBTwoTailNegativeCorners 210 78 1
        (firstBTwoTailALower 1 78) (firstBTwoTailAUpper 78) 39 (firstBTwoTailDUpper 1) := by
      norm_num [FirstBTwoTailNegativeCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_negative 210 78 z 1
      (firstBTwoTailALower 1 78) (firstBTwoTailAUpper 78) 39 (firstBTwoTailDUpper 1) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_211_107
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 107)
          (firstBTwoTailD tail) 211 107 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 107)
          (firstBTwoTailD tail) 211 107) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 107
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 211 107 * z =
    firstBTwoTailZNumerator a d 211 107 at root_eq
  have j_cases : j = 0 ∨ 1 ≤ j := by omega
  rcases j_cases with rfl | k_le_j
  · have rectangle := firstBTwoTail_exact_rectangle 0 rest 107 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 0 107) (firstBTwoTailAUpper 107)
      (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d at rectangle
    have corners : FirstBTwoTailNegativeCorners 211 107 (-1)
        (firstBTwoTailALower 0 107) (firstBTwoTailAUpper 107) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) := by
      norm_num [FirstBTwoTailNegativeCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_negative 211 107 z (-1)
      (firstBTwoTailALower 0 107) (firstBTwoTailAUpper 107) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_envelope_rectangle 1 j rest 107 k_le_j (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 1 107) (firstBTwoTailAUpper 107)
      39 (firstBTwoTailDUpper 1) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 211 107 0 1 1
        (firstBTwoTailALower 1 107) (firstBTwoTailAUpper 107) 39 (firstBTwoTailDUpper 1) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 211 107 0 z 1
      (firstBTwoTailALower 1 107) (firstBTwoTailAUpper 107) 39 (firstBTwoTailDUpper 1) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_211_108
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 108)
          (firstBTwoTailD tail) 211 108 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 108)
          (firstBTwoTailD tail) 211 108) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 108
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 211 108 * z =
    firstBTwoTailZNumerator a d 211 108 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 108 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 108) (firstBTwoTailAUpper 108)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 211 108 0 1 1
      (firstBTwoTailALower 0 108) (firstBTwoTailAUpper 108) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 211 108 0 z 1
    (firstBTwoTailALower 0 108) (firstBTwoTailAUpper 108) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_211_109
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 109)
          (firstBTwoTailD tail) 211 109 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 109)
          (firstBTwoTailD tail) 211 109) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 109
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 211 109 * z =
    firstBTwoTailZNumerator a d 211 109 at root_eq
  have j_cases : j = 0 ∨ 1 ≤ j := by omega
  rcases j_cases with rfl | k_le_j
  · have rectangle := firstBTwoTail_exact_rectangle 0 rest 109 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 0 109) (firstBTwoTailAUpper 109)
      (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 211 109 0 1 1
        (firstBTwoTailALower 0 109) (firstBTwoTailAUpper 109) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 211 109 0 z 1
      (firstBTwoTailALower 0 109) (firstBTwoTailAUpper 109) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_envelope_rectangle 1 j rest 109 k_le_j (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 1 109) (firstBTwoTailAUpper 109)
      39 (firstBTwoTailDUpper 1) a d at rectangle
    have corners : FirstBTwoTailNegativeCorners 211 109 1
        (firstBTwoTailALower 1 109) (firstBTwoTailAUpper 109) 39 (firstBTwoTailDUpper 1) := by
      norm_num [FirstBTwoTailNegativeCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_negative 211 109 z 1
      (firstBTwoTailALower 1 109) (firstBTwoTailAUpper 109) 39 (firstBTwoTailDUpper 1) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_212_174
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 174)
          (firstBTwoTailD tail) 212 174 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 174)
          (firstBTwoTailD tail) 212 174) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 174
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 212 174 * z =
    firstBTwoTailZNumerator a d 212 174 at root_eq
  have j_cases : j = 0 ∨ j = 1 ∨ 2 ≤ j := by omega
  rcases j_cases with rfl | rfl | k_le_j
  · have rectangle := firstBTwoTail_exact_rectangle 0 rest 174 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 0 174) (firstBTwoTailAUpper 174)
      (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d at rectangle
    have corners : FirstBTwoTailNegativeCorners 212 174 (-1)
        (firstBTwoTailALower 0 174) (firstBTwoTailAUpper 174) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) := by
      norm_num [FirstBTwoTailNegativeCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_negative 212 174 z (-1)
      (firstBTwoTailALower 0 174) (firstBTwoTailAUpper 174) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_exact_rectangle 1 rest 174 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 1 174) (firstBTwoTailAUpper 174)
      (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 212 174 11 12 1
        (firstBTwoTailALower 1 174) (firstBTwoTailAUpper 174) (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 212 174 11 z 1
      (firstBTwoTailALower 1 174) (firstBTwoTailAUpper 174) (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_envelope_rectangle 2 j rest 174 k_le_j (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 2 174) (firstBTwoTailAUpper 174)
      39 (firstBTwoTailDUpper 2) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 212 174 1 2 1
        (firstBTwoTailALower 2 174) (firstBTwoTailAUpper 174) 39 (firstBTwoTailDUpper 2) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 212 174 1 z 1
      (firstBTwoTailALower 2 174) (firstBTwoTailAUpper 174) 39 (firstBTwoTailDUpper 2) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_212_175
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 175)
          (firstBTwoTailD tail) 212 175 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 175)
          (firstBTwoTailD tail) 212 175) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 175
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 212 175 * z =
    firstBTwoTailZNumerator a d 212 175 at root_eq
  have j_cases : j = 0 ∨ 1 ≤ j := by omega
  rcases j_cases with rfl | k_le_j
  · have rectangle := firstBTwoTail_exact_rectangle 0 rest 175 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 0 175) (firstBTwoTailAUpper 175)
      (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 212 175 3 4 1
        (firstBTwoTailALower 0 175) (firstBTwoTailAUpper 175) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 212 175 3 z 1
      (firstBTwoTailALower 0 175) (firstBTwoTailAUpper 175) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_envelope_rectangle 1 j rest 175 k_le_j (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 1 175) (firstBTwoTailAUpper 175)
      39 (firstBTwoTailDUpper 1) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 212 175 0 1 1
        (firstBTwoTailALower 1 175) (firstBTwoTailAUpper 175) 39 (firstBTwoTailDUpper 1) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 212 175 0 z 1
      (firstBTwoTailALower 1 175) (firstBTwoTailAUpper 175) 39 (firstBTwoTailDUpper 1) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_212_176
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 176)
          (firstBTwoTailD tail) 212 176 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 176)
          (firstBTwoTailD tail) 212 176) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 176
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 212 176 * z =
    firstBTwoTailZNumerator a d 212 176 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 176 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 176) (firstBTwoTailAUpper 176)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 212 176 0 1 1
      (firstBTwoTailALower 0 176) (firstBTwoTailAUpper 176) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 212 176 0 z 1
    (firstBTwoTailALower 0 176) (firstBTwoTailAUpper 176) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_212_177
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 177)
          (firstBTwoTailD tail) 212 177 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 177)
          (firstBTwoTailD tail) 212 177) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 177
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 212 177 * z =
    firstBTwoTailZNumerator a d 212 177 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 177 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 177) (firstBTwoTailAUpper 177)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 212 177 0 1 1
      (firstBTwoTailALower 0 177) (firstBTwoTailAUpper 177) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 212 177 0 z 1
    (firstBTwoTailALower 0 177) (firstBTwoTailAUpper 177) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_212_178
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 178)
          (firstBTwoTailD tail) 212 178 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 178)
          (firstBTwoTailD tail) 212 178) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 178
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 212 178 * z =
    firstBTwoTailZNumerator a d 212 178 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 178 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 178) (firstBTwoTailAUpper 178)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 212 178 0 1 1
      (firstBTwoTailALower 0 178) (firstBTwoTailAUpper 178) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 212 178 0 z 1
    (firstBTwoTailALower 0 178) (firstBTwoTailAUpper 178) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_212_179
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 179)
          (firstBTwoTailD tail) 212 179 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 179)
          (firstBTwoTailD tail) 212 179) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 179
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 212 179 * z =
    firstBTwoTailZNumerator a d 212 179 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 179 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 179) (firstBTwoTailAUpper 179)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 212 179 0 1 1
      (firstBTwoTailALower 0 179) (firstBTwoTailAUpper 179) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 212 179 0 z 1
    (firstBTwoTailALower 0 179) (firstBTwoTailAUpper 179) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_212_180
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 180)
          (firstBTwoTailD tail) 212 180 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 180)
          (firstBTwoTailD tail) 212 180) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 180
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 212 180 * z =
    firstBTwoTailZNumerator a d 212 180 at root_eq
  have j_cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ 4 ≤ j := by omega
  rcases j_cases with rfl | rfl | rfl | rfl | k_le_j
  · have rectangle := firstBTwoTail_exact_rectangle 0 rest 180 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 0 180) (firstBTwoTailAUpper 180)
      (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 212 180 0 1 1
        (firstBTwoTailALower 0 180) (firstBTwoTailAUpper 180) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 212 180 0 z 1
      (firstBTwoTailALower 0 180) (firstBTwoTailAUpper 180) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_exact_rectangle 1 rest 180 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 1 180) (firstBTwoTailAUpper 180)
      (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 212 180 0 1 1
        (firstBTwoTailALower 1 180) (firstBTwoTailAUpper 180) (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 212 180 0 z 1
      (firstBTwoTailALower 1 180) (firstBTwoTailAUpper 180) (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_exact_rectangle 2 rest 180 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 2 180) (firstBTwoTailAUpper 180)
      (firstBTwoTailDLower 2) (firstBTwoTailDUpper 2) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 212 180 0 1 1
        (firstBTwoTailALower 2 180) (firstBTwoTailAUpper 180) (firstBTwoTailDLower 2) (firstBTwoTailDUpper 2) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 212 180 0 z 1
      (firstBTwoTailALower 2 180) (firstBTwoTailAUpper 180) (firstBTwoTailDLower 2) (firstBTwoTailDUpper 2) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_exact_rectangle 3 rest 180 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 3 180) (firstBTwoTailAUpper 180)
      (firstBTwoTailDLower 3) (firstBTwoTailDUpper 3) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 212 180 0 1 1
        (firstBTwoTailALower 3 180) (firstBTwoTailAUpper 180) (firstBTwoTailDLower 3) (firstBTwoTailDUpper 3) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 212 180 0 z 1
      (firstBTwoTailALower 3 180) (firstBTwoTailAUpper 180) (firstBTwoTailDLower 3) (firstBTwoTailDUpper 3) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_envelope_rectangle 4 j rest 180 k_le_j (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 4 180) (firstBTwoTailAUpper 180)
      39 (firstBTwoTailDUpper 4) a d at rectangle
    have corners : FirstBTwoTailNegativeCorners 212 180 1
        (firstBTwoTailALower 4 180) (firstBTwoTailAUpper 180) 39 (firstBTwoTailDUpper 4) := by
      norm_num [FirstBTwoTailNegativeCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_negative 212 180 z 1
      (firstBTwoTailALower 4 180) (firstBTwoTailAUpper 180) 39 (firstBTwoTailDUpper 4) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_212_181
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 181)
          (firstBTwoTailD tail) 212 181 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 181)
          (firstBTwoTailD tail) 212 181) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 181
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 212 181 * z =
    firstBTwoTailZNumerator a d 212 181 at root_eq
  have j_cases : j = 0 ∨ 1 ≤ j := by omega
  rcases j_cases with rfl | k_le_j
  · have rectangle := firstBTwoTail_exact_rectangle 0 rest 181 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 0 181) (firstBTwoTailAUpper 181)
      (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 212 181 0 1 1
        (firstBTwoTailALower 0 181) (firstBTwoTailAUpper 181) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 212 181 0 z 1
      (firstBTwoTailALower 0 181) (firstBTwoTailAUpper 181) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_envelope_rectangle 1 j rest 181 k_le_j (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 1 181) (firstBTwoTailAUpper 181)
      39 (firstBTwoTailDUpper 1) a d at rectangle
    have corners : FirstBTwoTailNegativeCorners 212 181 1
        (firstBTwoTailALower 1 181) (firstBTwoTailAUpper 181) 39 (firstBTwoTailDUpper 1) := by
      norm_num [FirstBTwoTailNegativeCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_negative 212 181 z 1
      (firstBTwoTailALower 1 181) (firstBTwoTailAUpper 181) 39 (firstBTwoTailDUpper 1) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_465
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 465)
          (firstBTwoTailD tail) 213 465 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 465)
          (firstBTwoTailD tail) 213 465) :
    j = 2 ∧ z = 38 := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 465
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 465 * z =
    firstBTwoTailZNumerator a d 213 465 at root_eq
  have j_cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ 4 ≤ j := by omega
  rcases j_cases with rfl | rfl | rfl | rfl | k_le_j
  · have rectangle := firstBTwoTail_exact_rectangle 0 rest 465 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 0 465) (firstBTwoTailAUpper 465)
      (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d at rectangle
    have corners : FirstBTwoTailNegativeCorners 213 465 (-1)
        (firstBTwoTailALower 0 465) (firstBTwoTailAUpper 465) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) := by
      norm_num [FirstBTwoTailNegativeCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_negative 213 465 z (-1)
      (firstBTwoTailALower 0 465) (firstBTwoTailAUpper 465) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_exact_rectangle 1 rest 465 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 1 465) (firstBTwoTailAUpper 465)
      (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) a d at rectangle
    have corners : FirstBTwoTailNegativeCorners 213 465 (-1)
        (firstBTwoTailALower 1 465) (firstBTwoTailAUpper 465) (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) := by
      norm_num [FirstBTwoTailNegativeCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_negative 213 465 z (-1)
      (firstBTwoTailALower 1 465) (firstBTwoTailAUpper 465) (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_exact_rectangle 2 rest 465 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 2 465) (firstBTwoTailAUpper 465)
      (firstBTwoTailDLower 2) (firstBTwoTailDUpper 2) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 213 465 37 39 1
        (firstBTwoTailALower 2 465) (firstBTwoTailAUpper 465) (firstBTwoTailDLower 2) (firstBTwoTailDUpper 2) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    have interval := firstBTwoTailZ_mem_open_interval 213 465 37 39
      z 1 (firstBTwoTailALower 2 465) (firstBTwoTailAUpper 465) (firstBTwoTailDLower 2) (firstBTwoTailDUpper 2)
      a d rectangle corners root_eq
    exact ⟨rfl, by omega⟩
  · have rectangle := firstBTwoTail_exact_rectangle 3 rest 465 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 3 465) (firstBTwoTailAUpper 465)
      (firstBTwoTailDLower 3) (firstBTwoTailDUpper 3) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 213 465 7 8 1
        (firstBTwoTailALower 3 465) (firstBTwoTailAUpper 465) (firstBTwoTailDLower 3) (firstBTwoTailDUpper 3) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 213 465 7 z 1
      (firstBTwoTailALower 3 465) (firstBTwoTailAUpper 465) (firstBTwoTailDLower 3) (firstBTwoTailDUpper 3) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_envelope_rectangle 4 j rest 465 k_le_j (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 4 465) (firstBTwoTailAUpper 465)
      39 (firstBTwoTailDUpper 4) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 213 465 5 6 1
        (firstBTwoTailALower 4 465) (firstBTwoTailAUpper 465) 39 (firstBTwoTailDUpper 4) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 213 465 5 z 1
      (firstBTwoTailALower 4 465) (firstBTwoTailAUpper 465) 39 (firstBTwoTailDUpper 4) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_466
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 466)
          (firstBTwoTailD tail) 213 466 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 466)
          (firstBTwoTailD tail) 213 466) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 466
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 466 * z =
    firstBTwoTailZNumerator a d 213 466 at root_eq
  have j_cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ 3 ≤ j := by omega
  rcases j_cases with rfl | rfl | rfl | k_le_j
  · have rectangle := firstBTwoTail_exact_rectangle 0 rest 466 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 0 466) (firstBTwoTailAUpper 466)
      (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d at rectangle
    have corners : FirstBTwoTailNegativeCorners 213 466 (-1)
        (firstBTwoTailALower 0 466) (firstBTwoTailAUpper 466) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) := by
      norm_num [FirstBTwoTailNegativeCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_negative 213 466 z (-1)
      (firstBTwoTailALower 0 466) (firstBTwoTailAUpper 466) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_exact_rectangle 1 rest 466 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 1 466) (firstBTwoTailAUpper 466)
      (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) a d at rectangle
    have corners : FirstBTwoTailNegativeCorners 213 466 (-1)
        (firstBTwoTailALower 1 466) (firstBTwoTailAUpper 466) (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) := by
      norm_num [FirstBTwoTailNegativeCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_negative 213 466 z (-1)
      (firstBTwoTailALower 1 466) (firstBTwoTailAUpper 466) (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_exact_rectangle 2 rest 466 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 2 466) (firstBTwoTailAUpper 466)
      (firstBTwoTailDLower 2) (firstBTwoTailDUpper 2) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 213 466 3 4 1
        (firstBTwoTailALower 2 466) (firstBTwoTailAUpper 466) (firstBTwoTailDLower 2) (firstBTwoTailDUpper 2) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 213 466 3 z 1
      (firstBTwoTailALower 2 466) (firstBTwoTailAUpper 466) (firstBTwoTailDLower 2) (firstBTwoTailDUpper 2) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_envelope_rectangle 3 j rest 466 k_le_j (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 3 466) (firstBTwoTailAUpper 466)
      39 (firstBTwoTailDUpper 3) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 213 466 2 3 1
        (firstBTwoTailALower 3 466) (firstBTwoTailAUpper 466) 39 (firstBTwoTailDUpper 3) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 213 466 2 z 1
      (firstBTwoTailALower 3 466) (firstBTwoTailAUpper 466) 39 (firstBTwoTailDUpper 3) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_467
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 467)
          (firstBTwoTailD tail) 213 467 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 467)
          (firstBTwoTailD tail) 213 467) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 467
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 467 * z =
    firstBTwoTailZNumerator a d 213 467 at root_eq
  have j_cases : j = 0 ∨ j = 1 ∨ 2 ≤ j := by omega
  rcases j_cases with rfl | rfl | k_le_j
  · have rectangle := firstBTwoTail_exact_rectangle 0 rest 467 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 0 467) (firstBTwoTailAUpper 467)
      (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d at rectangle
    have corners : FirstBTwoTailNegativeCorners 213 467 (-1)
        (firstBTwoTailALower 0 467) (firstBTwoTailAUpper 467) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) := by
      norm_num [FirstBTwoTailNegativeCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_negative 213 467 z (-1)
      (firstBTwoTailALower 0 467) (firstBTwoTailAUpper 467) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_exact_rectangle 1 rest 467 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 1 467) (firstBTwoTailAUpper 467)
      (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 213 467 5 6 1
        (firstBTwoTailALower 1 467) (firstBTwoTailAUpper 467) (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 213 467 5 z 1
      (firstBTwoTailALower 1 467) (firstBTwoTailAUpper 467) (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_envelope_rectangle 2 j rest 467 k_le_j (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 2 467) (firstBTwoTailAUpper 467)
      39 (firstBTwoTailDUpper 2) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 213 467 1 2 1
        (firstBTwoTailALower 2 467) (firstBTwoTailAUpper 467) 39 (firstBTwoTailDUpper 2) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 213 467 1 z 1
      (firstBTwoTailALower 2 467) (firstBTwoTailAUpper 467) 39 (firstBTwoTailDUpper 2) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_468
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 468)
          (firstBTwoTailD tail) 213 468 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 468)
          (firstBTwoTailD tail) 213 468) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 468
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 468 * z =
    firstBTwoTailZNumerator a d 213 468 at root_eq
  have j_cases : j = 0 ∨ j = 1 ∨ 2 ≤ j := by omega
  rcases j_cases with rfl | rfl | k_le_j
  · have rectangle := firstBTwoTail_exact_rectangle 0 rest 468 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 0 468) (firstBTwoTailAUpper 468)
      (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d at rectangle
    have corners : FirstBTwoTailNegativeCorners 213 468 (-1)
        (firstBTwoTailALower 0 468) (firstBTwoTailAUpper 468) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) := by
      norm_num [FirstBTwoTailNegativeCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_negative 213 468 z (-1)
      (firstBTwoTailALower 0 468) (firstBTwoTailAUpper 468) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_exact_rectangle 1 rest 468 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 1 468) (firstBTwoTailAUpper 468)
      (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 213 468 2 3 1
        (firstBTwoTailALower 1 468) (firstBTwoTailAUpper 468) (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 213 468 2 z 1
      (firstBTwoTailALower 1 468) (firstBTwoTailAUpper 468) (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_envelope_rectangle 2 j rest 468 k_le_j (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 2 468) (firstBTwoTailAUpper 468)
      39 (firstBTwoTailDUpper 2) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 213 468 1 2 1
        (firstBTwoTailALower 2 468) (firstBTwoTailAUpper 468) 39 (firstBTwoTailDUpper 2) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 213 468 1 z 1
      (firstBTwoTailALower 2 468) (firstBTwoTailAUpper 468) 39 (firstBTwoTailDUpper 2) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_469
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 469)
          (firstBTwoTailD tail) 213 469 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 469)
          (firstBTwoTailD tail) 213 469) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 469
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 469 * z =
    firstBTwoTailZNumerator a d 213 469 at root_eq
  have j_cases : j = 0 ∨ j = 1 ∨ 2 ≤ j := by omega
  rcases j_cases with rfl | rfl | k_le_j
  · have rectangle := firstBTwoTail_exact_rectangle 0 rest 469 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 0 469) (firstBTwoTailAUpper 469)
      (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d at rectangle
    have corners : FirstBTwoTailNegativeCorners 213 469 (-1)
        (firstBTwoTailALower 0 469) (firstBTwoTailAUpper 469) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) := by
      norm_num [FirstBTwoTailNegativeCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_negative 213 469 z (-1)
      (firstBTwoTailALower 0 469) (firstBTwoTailAUpper 469) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_exact_rectangle 1 rest 469 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 1 469) (firstBTwoTailAUpper 469)
      (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 213 469 1 2 1
        (firstBTwoTailALower 1 469) (firstBTwoTailAUpper 469) (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 213 469 1 z 1
      (firstBTwoTailALower 1 469) (firstBTwoTailAUpper 469) (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_envelope_rectangle 2 j rest 469 k_le_j (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 2 469) (firstBTwoTailAUpper 469)
      39 (firstBTwoTailDUpper 2) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 213 469 0 1 1
        (firstBTwoTailALower 2 469) (firstBTwoTailAUpper 469) 39 (firstBTwoTailDUpper 2) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 213 469 0 z 1
      (firstBTwoTailALower 2 469) (firstBTwoTailAUpper 469) 39 (firstBTwoTailDUpper 2) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_470
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 470)
          (firstBTwoTailD tail) 213 470 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 470)
          (firstBTwoTailD tail) 213 470) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 470
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 470 * z =
    firstBTwoTailZNumerator a d 213 470 at root_eq
  have j_cases : j = 0 ∨ j = 1 ∨ 2 ≤ j := by omega
  rcases j_cases with rfl | rfl | k_le_j
  · have rectangle := firstBTwoTail_exact_rectangle 0 rest 470 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 0 470) (firstBTwoTailAUpper 470)
      (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d at rectangle
    have corners : FirstBTwoTailNegativeCorners 213 470 (-1)
        (firstBTwoTailALower 0 470) (firstBTwoTailAUpper 470) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) := by
      norm_num [FirstBTwoTailNegativeCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_negative 213 470 z (-1)
      (firstBTwoTailALower 0 470) (firstBTwoTailAUpper 470) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_exact_rectangle 1 rest 470 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 1 470) (firstBTwoTailAUpper 470)
      (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 213 470 1 2 1
        (firstBTwoTailALower 1 470) (firstBTwoTailAUpper 470) (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 213 470 1 z 1
      (firstBTwoTailALower 1 470) (firstBTwoTailAUpper 470) (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_envelope_rectangle 2 j rest 470 k_le_j (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 2 470) (firstBTwoTailAUpper 470)
      39 (firstBTwoTailDUpper 2) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 213 470 0 1 1
        (firstBTwoTailALower 2 470) (firstBTwoTailAUpper 470) 39 (firstBTwoTailDUpper 2) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 213 470 0 z 1
      (firstBTwoTailALower 2 470) (firstBTwoTailAUpper 470) 39 (firstBTwoTailDUpper 2) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_471
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 471)
          (firstBTwoTailD tail) 213 471 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 471)
          (firstBTwoTailD tail) 213 471) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 471
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 471 * z =
    firstBTwoTailZNumerator a d 213 471 at root_eq
  have j_cases : j = 0 ∨ 1 ≤ j := by omega
  rcases j_cases with rfl | k_le_j
  · have rectangle := firstBTwoTail_exact_rectangle 0 rest 471 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 0 471) (firstBTwoTailAUpper 471)
      (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 213 471 5 6 1
        (firstBTwoTailALower 0 471) (firstBTwoTailAUpper 471) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 213 471 5 z 1
      (firstBTwoTailALower 0 471) (firstBTwoTailAUpper 471) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_envelope_rectangle 1 j rest 471 k_le_j (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 1 471) (firstBTwoTailAUpper 471)
      39 (firstBTwoTailDUpper 1) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 213 471 0 1 1
        (firstBTwoTailALower 1 471) (firstBTwoTailAUpper 471) 39 (firstBTwoTailDUpper 1) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 213 471 0 z 1
      (firstBTwoTailALower 1 471) (firstBTwoTailAUpper 471) 39 (firstBTwoTailDUpper 1) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_472
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 472)
          (firstBTwoTailD tail) 213 472 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 472)
          (firstBTwoTailD tail) 213 472) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 472
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 472 * z =
    firstBTwoTailZNumerator a d 213 472 at root_eq
  have j_cases : j = 0 ∨ 1 ≤ j := by omega
  rcases j_cases with rfl | k_le_j
  · have rectangle := firstBTwoTail_exact_rectangle 0 rest 472 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 0 472) (firstBTwoTailAUpper 472)
      (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 213 472 2 3 1
        (firstBTwoTailALower 0 472) (firstBTwoTailAUpper 472) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 213 472 2 z 1
      (firstBTwoTailALower 0 472) (firstBTwoTailAUpper 472) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_envelope_rectangle 1 j rest 472 k_le_j (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 1 472) (firstBTwoTailAUpper 472)
      39 (firstBTwoTailDUpper 1) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 213 472 0 1 1
        (firstBTwoTailALower 1 472) (firstBTwoTailAUpper 472) 39 (firstBTwoTailDUpper 1) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 213 472 0 z 1
      (firstBTwoTailALower 1 472) (firstBTwoTailAUpper 472) 39 (firstBTwoTailDUpper 1) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_473
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 473)
          (firstBTwoTailD tail) 213 473 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 473)
          (firstBTwoTailD tail) 213 473) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 473
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 473 * z =
    firstBTwoTailZNumerator a d 213 473 at root_eq
  have j_cases : j = 0 ∨ 1 ≤ j := by omega
  rcases j_cases with rfl | k_le_j
  · have rectangle := firstBTwoTail_exact_rectangle 0 rest 473 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 0 473) (firstBTwoTailAUpper 473)
      (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 213 473 1 2 1
        (firstBTwoTailALower 0 473) (firstBTwoTailAUpper 473) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 213 473 1 z 1
      (firstBTwoTailALower 0 473) (firstBTwoTailAUpper 473) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_envelope_rectangle 1 j rest 473 k_le_j (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 1 473) (firstBTwoTailAUpper 473)
      39 (firstBTwoTailDUpper 1) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 213 473 0 1 1
        (firstBTwoTailALower 1 473) (firstBTwoTailAUpper 473) 39 (firstBTwoTailDUpper 1) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 213 473 0 z 1
      (firstBTwoTailALower 1 473) (firstBTwoTailAUpper 473) 39 (firstBTwoTailDUpper 1) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_474
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 474)
          (firstBTwoTailD tail) 213 474 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 474)
          (firstBTwoTailD tail) 213 474) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 474
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 474 * z =
    firstBTwoTailZNumerator a d 213 474 at root_eq
  have j_cases : j = 0 ∨ 1 ≤ j := by omega
  rcases j_cases with rfl | k_le_j
  · have rectangle := firstBTwoTail_exact_rectangle 0 rest 474 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 0 474) (firstBTwoTailAUpper 474)
      (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 213 474 1 2 1
        (firstBTwoTailALower 0 474) (firstBTwoTailAUpper 474) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 213 474 1 z 1
      (firstBTwoTailALower 0 474) (firstBTwoTailAUpper 474) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_envelope_rectangle 1 j rest 474 k_le_j (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 1 474) (firstBTwoTailAUpper 474)
      39 (firstBTwoTailDUpper 1) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 213 474 0 1 1
        (firstBTwoTailALower 1 474) (firstBTwoTailAUpper 474) 39 (firstBTwoTailDUpper 1) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 213 474 0 z 1
      (firstBTwoTailALower 1 474) (firstBTwoTailAUpper 474) 39 (firstBTwoTailDUpper 1) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_475
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 475)
          (firstBTwoTailD tail) 213 475 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 475)
          (firstBTwoTailD tail) 213 475) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 475
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 475 * z =
    firstBTwoTailZNumerator a d 213 475 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 475 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 475) (firstBTwoTailAUpper 475)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 475 0 1 1
      (firstBTwoTailALower 0 475) (firstBTwoTailAUpper 475) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 475 0 z 1
    (firstBTwoTailALower 0 475) (firstBTwoTailAUpper 475) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_476
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 476)
          (firstBTwoTailD tail) 213 476 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 476)
          (firstBTwoTailD tail) 213 476) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 476
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 476 * z =
    firstBTwoTailZNumerator a d 213 476 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 476 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 476) (firstBTwoTailAUpper 476)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 476 0 1 1
      (firstBTwoTailALower 0 476) (firstBTwoTailAUpper 476) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 476 0 z 1
    (firstBTwoTailALower 0 476) (firstBTwoTailAUpper 476) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_477
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 477)
          (firstBTwoTailD tail) 213 477 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 477)
          (firstBTwoTailD tail) 213 477) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 477
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 477 * z =
    firstBTwoTailZNumerator a d 213 477 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 477 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 477) (firstBTwoTailAUpper 477)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 477 0 1 1
      (firstBTwoTailALower 0 477) (firstBTwoTailAUpper 477) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 477 0 z 1
    (firstBTwoTailALower 0 477) (firstBTwoTailAUpper 477) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_478
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 478)
          (firstBTwoTailD tail) 213 478 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 478)
          (firstBTwoTailD tail) 213 478) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 478
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 478 * z =
    firstBTwoTailZNumerator a d 213 478 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 478 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 478) (firstBTwoTailAUpper 478)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 478 0 1 1
      (firstBTwoTailALower 0 478) (firstBTwoTailAUpper 478) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 478 0 z 1
    (firstBTwoTailALower 0 478) (firstBTwoTailAUpper 478) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_479
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 479)
          (firstBTwoTailD tail) 213 479 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 479)
          (firstBTwoTailD tail) 213 479) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 479
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 479 * z =
    firstBTwoTailZNumerator a d 213 479 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 479 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 479) (firstBTwoTailAUpper 479)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 479 0 1 1
      (firstBTwoTailALower 0 479) (firstBTwoTailAUpper 479) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 479 0 z 1
    (firstBTwoTailALower 0 479) (firstBTwoTailAUpper 479) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_480
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 480)
          (firstBTwoTailD tail) 213 480 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 480)
          (firstBTwoTailD tail) 213 480) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 480
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 480 * z =
    firstBTwoTailZNumerator a d 213 480 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 480 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 480) (firstBTwoTailAUpper 480)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 480 0 1 1
      (firstBTwoTailALower 0 480) (firstBTwoTailAUpper 480) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 480 0 z 1
    (firstBTwoTailALower 0 480) (firstBTwoTailAUpper 480) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_481
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 481)
          (firstBTwoTailD tail) 213 481 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 481)
          (firstBTwoTailD tail) 213 481) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 481
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 481 * z =
    firstBTwoTailZNumerator a d 213 481 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 481 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 481) (firstBTwoTailAUpper 481)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 481 0 1 1
      (firstBTwoTailALower 0 481) (firstBTwoTailAUpper 481) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 481 0 z 1
    (firstBTwoTailALower 0 481) (firstBTwoTailAUpper 481) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_482
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 482)
          (firstBTwoTailD tail) 213 482 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 482)
          (firstBTwoTailD tail) 213 482) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 482
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 482 * z =
    firstBTwoTailZNumerator a d 213 482 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 482 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 482) (firstBTwoTailAUpper 482)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 482 0 1 1
      (firstBTwoTailALower 0 482) (firstBTwoTailAUpper 482) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 482 0 z 1
    (firstBTwoTailALower 0 482) (firstBTwoTailAUpper 482) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_483
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 483)
          (firstBTwoTailD tail) 213 483 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 483)
          (firstBTwoTailD tail) 213 483) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 483
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 483 * z =
    firstBTwoTailZNumerator a d 213 483 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 483 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 483) (firstBTwoTailAUpper 483)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 483 0 1 1
      (firstBTwoTailALower 0 483) (firstBTwoTailAUpper 483) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 483 0 z 1
    (firstBTwoTailALower 0 483) (firstBTwoTailAUpper 483) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_484
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 484)
          (firstBTwoTailD tail) 213 484 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 484)
          (firstBTwoTailD tail) 213 484) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 484
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 484 * z =
    firstBTwoTailZNumerator a d 213 484 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 484 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 484) (firstBTwoTailAUpper 484)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 484 0 1 1
      (firstBTwoTailALower 0 484) (firstBTwoTailAUpper 484) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 484 0 z 1
    (firstBTwoTailALower 0 484) (firstBTwoTailAUpper 484) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_485
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 485)
          (firstBTwoTailD tail) 213 485 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 485)
          (firstBTwoTailD tail) 213 485) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 485
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 485 * z =
    firstBTwoTailZNumerator a d 213 485 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 485 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 485) (firstBTwoTailAUpper 485)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 485 0 1 1
      (firstBTwoTailALower 0 485) (firstBTwoTailAUpper 485) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 485 0 z 1
    (firstBTwoTailALower 0 485) (firstBTwoTailAUpper 485) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_486
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 486)
          (firstBTwoTailD tail) 213 486 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 486)
          (firstBTwoTailD tail) 213 486) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 486
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 486 * z =
    firstBTwoTailZNumerator a d 213 486 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 486 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 486) (firstBTwoTailAUpper 486)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 486 0 1 1
      (firstBTwoTailALower 0 486) (firstBTwoTailAUpper 486) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 486 0 z 1
    (firstBTwoTailALower 0 486) (firstBTwoTailAUpper 486) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_487
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 487)
          (firstBTwoTailD tail) 213 487 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 487)
          (firstBTwoTailD tail) 213 487) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 487
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 487 * z =
    firstBTwoTailZNumerator a d 213 487 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 487 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 487) (firstBTwoTailAUpper 487)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 487 0 1 1
      (firstBTwoTailALower 0 487) (firstBTwoTailAUpper 487) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 487 0 z 1
    (firstBTwoTailALower 0 487) (firstBTwoTailAUpper 487) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_488
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 488)
          (firstBTwoTailD tail) 213 488 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 488)
          (firstBTwoTailD tail) 213 488) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 488
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 488 * z =
    firstBTwoTailZNumerator a d 213 488 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 488 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 488) (firstBTwoTailAUpper 488)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 488 0 1 1
      (firstBTwoTailALower 0 488) (firstBTwoTailAUpper 488) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 488 0 z 1
    (firstBTwoTailALower 0 488) (firstBTwoTailAUpper 488) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_489
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 489)
          (firstBTwoTailD tail) 213 489 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 489)
          (firstBTwoTailD tail) 213 489) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 489
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 489 * z =
    firstBTwoTailZNumerator a d 213 489 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 489 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 489) (firstBTwoTailAUpper 489)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 489 0 1 1
      (firstBTwoTailALower 0 489) (firstBTwoTailAUpper 489) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 489 0 z 1
    (firstBTwoTailALower 0 489) (firstBTwoTailAUpper 489) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_490
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 490)
          (firstBTwoTailD tail) 213 490 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 490)
          (firstBTwoTailD tail) 213 490) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 490
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 490 * z =
    firstBTwoTailZNumerator a d 213 490 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 490 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 490) (firstBTwoTailAUpper 490)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 490 0 1 1
      (firstBTwoTailALower 0 490) (firstBTwoTailAUpper 490) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 490 0 z 1
    (firstBTwoTailALower 0 490) (firstBTwoTailAUpper 490) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_491
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 491)
          (firstBTwoTailD tail) 213 491 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 491)
          (firstBTwoTailD tail) 213 491) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 491
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 491 * z =
    firstBTwoTailZNumerator a d 213 491 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 491 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 491) (firstBTwoTailAUpper 491)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 491 0 1 1
      (firstBTwoTailALower 0 491) (firstBTwoTailAUpper 491) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 491 0 z 1
    (firstBTwoTailALower 0 491) (firstBTwoTailAUpper 491) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_492
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 492)
          (firstBTwoTailD tail) 213 492 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 492)
          (firstBTwoTailD tail) 213 492) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 492
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 492 * z =
    firstBTwoTailZNumerator a d 213 492 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 492 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 492) (firstBTwoTailAUpper 492)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 492 0 1 1
      (firstBTwoTailALower 0 492) (firstBTwoTailAUpper 492) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 492 0 z 1
    (firstBTwoTailALower 0 492) (firstBTwoTailAUpper 492) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_493
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 493)
          (firstBTwoTailD tail) 213 493 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 493)
          (firstBTwoTailD tail) 213 493) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 493
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 493 * z =
    firstBTwoTailZNumerator a d 213 493 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 493 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 493) (firstBTwoTailAUpper 493)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 493 0 1 1
      (firstBTwoTailALower 0 493) (firstBTwoTailAUpper 493) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 493 0 z 1
    (firstBTwoTailALower 0 493) (firstBTwoTailAUpper 493) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_494
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 494)
          (firstBTwoTailD tail) 213 494 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 494)
          (firstBTwoTailD tail) 213 494) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 494
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 494 * z =
    firstBTwoTailZNumerator a d 213 494 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 494 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 494) (firstBTwoTailAUpper 494)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 494 0 1 1
      (firstBTwoTailALower 0 494) (firstBTwoTailAUpper 494) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 494 0 z 1
    (firstBTwoTailALower 0 494) (firstBTwoTailAUpper 494) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_495
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 495)
          (firstBTwoTailD tail) 213 495 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 495)
          (firstBTwoTailD tail) 213 495) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 495
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 495 * z =
    firstBTwoTailZNumerator a d 213 495 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 495 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 495) (firstBTwoTailAUpper 495)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 495 0 1 1
      (firstBTwoTailALower 0 495) (firstBTwoTailAUpper 495) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 495 0 z 1
    (firstBTwoTailALower 0 495) (firstBTwoTailAUpper 495) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_496
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 496)
          (firstBTwoTailD tail) 213 496 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 496)
          (firstBTwoTailD tail) 213 496) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 496
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 496 * z =
    firstBTwoTailZNumerator a d 213 496 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 496 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 496) (firstBTwoTailAUpper 496)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 496 0 1 1
      (firstBTwoTailALower 0 496) (firstBTwoTailAUpper 496) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 496 0 z 1
    (firstBTwoTailALower 0 496) (firstBTwoTailAUpper 496) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_497
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 497)
          (firstBTwoTailD tail) 213 497 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 497)
          (firstBTwoTailD tail) 213 497) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 497
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 497 * z =
    firstBTwoTailZNumerator a d 213 497 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 497 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 497) (firstBTwoTailAUpper 497)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 497 0 1 1
      (firstBTwoTailALower 0 497) (firstBTwoTailAUpper 497) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 497 0 z 1
    (firstBTwoTailALower 0 497) (firstBTwoTailAUpper 497) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_498
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 498)
          (firstBTwoTailD tail) 213 498 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 498)
          (firstBTwoTailD tail) 213 498) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 498
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 498 * z =
    firstBTwoTailZNumerator a d 213 498 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 498 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 498) (firstBTwoTailAUpper 498)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 498 0 1 1
      (firstBTwoTailALower 0 498) (firstBTwoTailAUpper 498) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 498 0 z 1
    (firstBTwoTailALower 0 498) (firstBTwoTailAUpper 498) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_499
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 499)
          (firstBTwoTailD tail) 213 499 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 499)
          (firstBTwoTailD tail) 213 499) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 499
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 499 * z =
    firstBTwoTailZNumerator a d 213 499 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 499 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 499) (firstBTwoTailAUpper 499)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 499 0 1 1
      (firstBTwoTailALower 0 499) (firstBTwoTailAUpper 499) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 499 0 z 1
    (firstBTwoTailALower 0 499) (firstBTwoTailAUpper 499) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_500
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 500)
          (firstBTwoTailD tail) 213 500 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 500)
          (firstBTwoTailD tail) 213 500) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 500
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 500 * z =
    firstBTwoTailZNumerator a d 213 500 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 500 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 500) (firstBTwoTailAUpper 500)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 500 0 1 1
      (firstBTwoTailALower 0 500) (firstBTwoTailAUpper 500) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 500 0 z 1
    (firstBTwoTailALower 0 500) (firstBTwoTailAUpper 500) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_501
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 501)
          (firstBTwoTailD tail) 213 501 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 501)
          (firstBTwoTailD tail) 213 501) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 501
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 501 * z =
    firstBTwoTailZNumerator a d 213 501 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 501 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 501) (firstBTwoTailAUpper 501)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 501 0 1 1
      (firstBTwoTailALower 0 501) (firstBTwoTailAUpper 501) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 501 0 z 1
    (firstBTwoTailALower 0 501) (firstBTwoTailAUpper 501) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_502
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 502)
          (firstBTwoTailD tail) 213 502 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 502)
          (firstBTwoTailD tail) 213 502) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 502
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 502 * z =
    firstBTwoTailZNumerator a d 213 502 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 502 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 502) (firstBTwoTailAUpper 502)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 502 0 1 1
      (firstBTwoTailALower 0 502) (firstBTwoTailAUpper 502) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 502 0 z 1
    (firstBTwoTailALower 0 502) (firstBTwoTailAUpper 502) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_503
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 503)
          (firstBTwoTailD tail) 213 503 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 503)
          (firstBTwoTailD tail) 213 503) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 503
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 503 * z =
    firstBTwoTailZNumerator a d 213 503 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 503 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 503) (firstBTwoTailAUpper 503)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 503 0 1 1
      (firstBTwoTailALower 0 503) (firstBTwoTailAUpper 503) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 503 0 z 1
    (firstBTwoTailALower 0 503) (firstBTwoTailAUpper 503) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_504
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 504)
          (firstBTwoTailD tail) 213 504 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 504)
          (firstBTwoTailD tail) 213 504) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 504
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 504 * z =
    firstBTwoTailZNumerator a d 213 504 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 504 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 504) (firstBTwoTailAUpper 504)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 504 0 1 1
      (firstBTwoTailALower 0 504) (firstBTwoTailAUpper 504) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 504 0 z 1
    (firstBTwoTailALower 0 504) (firstBTwoTailAUpper 504) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_505
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 505)
          (firstBTwoTailD tail) 213 505 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 505)
          (firstBTwoTailD tail) 213 505) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 505
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 505 * z =
    firstBTwoTailZNumerator a d 213 505 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 505 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 505) (firstBTwoTailAUpper 505)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 505 0 1 1
      (firstBTwoTailALower 0 505) (firstBTwoTailAUpper 505) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 505 0 z 1
    (firstBTwoTailALower 0 505) (firstBTwoTailAUpper 505) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_506
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 506)
          (firstBTwoTailD tail) 213 506 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 506)
          (firstBTwoTailD tail) 213 506) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 506
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 506 * z =
    firstBTwoTailZNumerator a d 213 506 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 506 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 506) (firstBTwoTailAUpper 506)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 506 0 1 1
      (firstBTwoTailALower 0 506) (firstBTwoTailAUpper 506) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 506 0 z 1
    (firstBTwoTailALower 0 506) (firstBTwoTailAUpper 506) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_507
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 507)
          (firstBTwoTailD tail) 213 507 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 507)
          (firstBTwoTailD tail) 213 507) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 507
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 507 * z =
    firstBTwoTailZNumerator a d 213 507 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 507 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 507) (firstBTwoTailAUpper 507)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 507 0 1 1
      (firstBTwoTailALower 0 507) (firstBTwoTailAUpper 507) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 507 0 z 1
    (firstBTwoTailALower 0 507) (firstBTwoTailAUpper 507) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_508
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 508)
          (firstBTwoTailD tail) 213 508 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 508)
          (firstBTwoTailD tail) 213 508) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 508
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 508 * z =
    firstBTwoTailZNumerator a d 213 508 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 508 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 508) (firstBTwoTailAUpper 508)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 508 0 1 1
      (firstBTwoTailALower 0 508) (firstBTwoTailAUpper 508) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 508 0 z 1
    (firstBTwoTailALower 0 508) (firstBTwoTailAUpper 508) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_509
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 509)
          (firstBTwoTailD tail) 213 509 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 509)
          (firstBTwoTailD tail) 213 509) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 509
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 509 * z =
    firstBTwoTailZNumerator a d 213 509 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 509 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 509) (firstBTwoTailAUpper 509)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 509 0 1 1
      (firstBTwoTailALower 0 509) (firstBTwoTailAUpper 509) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 509 0 z 1
    (firstBTwoTailALower 0 509) (firstBTwoTailAUpper 509) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_510
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 510)
          (firstBTwoTailD tail) 213 510 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 510)
          (firstBTwoTailD tail) 213 510) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 510
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 510 * z =
    firstBTwoTailZNumerator a d 213 510 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 510 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 510) (firstBTwoTailAUpper 510)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 510 0 1 1
      (firstBTwoTailALower 0 510) (firstBTwoTailAUpper 510) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 510 0 z 1
    (firstBTwoTailALower 0 510) (firstBTwoTailAUpper 510) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_511
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 511)
          (firstBTwoTailD tail) 213 511 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 511)
          (firstBTwoTailD tail) 213 511) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 511
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 511 * z =
    firstBTwoTailZNumerator a d 213 511 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 511 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 511) (firstBTwoTailAUpper 511)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 511 0 1 1
      (firstBTwoTailALower 0 511) (firstBTwoTailAUpper 511) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 511 0 z 1
    (firstBTwoTailALower 0 511) (firstBTwoTailAUpper 511) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_512
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 512)
          (firstBTwoTailD tail) 213 512 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 512)
          (firstBTwoTailD tail) 213 512) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 512
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 512 * z =
    firstBTwoTailZNumerator a d 213 512 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 512 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 512) (firstBTwoTailAUpper 512)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 512 0 1 1
      (firstBTwoTailALower 0 512) (firstBTwoTailAUpper 512) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 512 0 z 1
    (firstBTwoTailALower 0 512) (firstBTwoTailAUpper 512) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_513
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 513)
          (firstBTwoTailD tail) 213 513 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 513)
          (firstBTwoTailD tail) 213 513) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 513
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 513 * z =
    firstBTwoTailZNumerator a d 213 513 at root_eq
  have k_le_j : 0 ≤ j := Nat.zero_le j
  have rectangle := firstBTwoTail_envelope_rectangle 0 j rest 513 k_le_j (by omega)
  change FirstBTwoTailRectangle
    (firstBTwoTailALower 0 513) (firstBTwoTailAUpper 513)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  have corners : FirstBTwoTailOpenCorners 213 513 0 1 1
      (firstBTwoTailALower 0 513) (firstBTwoTailAUpper 513) 39 (firstBTwoTailDUpper 0) := by
    norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
      firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator]
  exact (firstBTwoTailZ_no_nat_of_gap 213 513 0 z 1
    (firstBTwoTailALower 0 513) (firstBTwoTailAUpper 513) 39 (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_514
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 514)
          (firstBTwoTailD tail) 213 514 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 514)
          (firstBTwoTailD tail) 213 514) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 514
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 514 * z =
    firstBTwoTailZNumerator a d 213 514 at root_eq
  have j_cases : j = 0 ∨ j = 1 ∨ 2 ≤ j := by omega
  rcases j_cases with rfl | rfl | k_le_j
  · have rectangle := firstBTwoTail_exact_rectangle 0 rest 514 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 0 514) (firstBTwoTailAUpper 514)
      (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 213 514 0 1 1
        (firstBTwoTailALower 0 514) (firstBTwoTailAUpper 514) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 213 514 0 z 1
      (firstBTwoTailALower 0 514) (firstBTwoTailAUpper 514) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_exact_rectangle 1 rest 514 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 1 514) (firstBTwoTailAUpper 514)
      (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 213 514 0 1 1
        (firstBTwoTailALower 1 514) (firstBTwoTailAUpper 514) (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 213 514 0 z 1
      (firstBTwoTailALower 1 514) (firstBTwoTailAUpper 514) (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_envelope_rectangle 2 j rest 514 k_le_j (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 2 514) (firstBTwoTailAUpper 514)
      39 (firstBTwoTailDUpper 2) a d at rectangle
    have corners : FirstBTwoTailNegativeCorners 213 514 1
        (firstBTwoTailALower 2 514) (firstBTwoTailAUpper 514) 39 (firstBTwoTailDUpper 2) := by
      norm_num [FirstBTwoTailNegativeCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_negative 213 514 z 1
      (firstBTwoTailALower 2 514) (firstBTwoTailAUpper 514) 39 (firstBTwoTailDUpper 2) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_515
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 515)
          (firstBTwoTailD tail) 213 515 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 515)
          (firstBTwoTailD tail) 213 515) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 515
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 515 * z =
    firstBTwoTailZNumerator a d 213 515 at root_eq
  have j_cases : j = 0 ∨ j = 1 ∨ 2 ≤ j := by omega
  rcases j_cases with rfl | rfl | k_le_j
  · have rectangle := firstBTwoTail_exact_rectangle 0 rest 515 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 0 515) (firstBTwoTailAUpper 515)
      (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 213 515 0 1 1
        (firstBTwoTailALower 0 515) (firstBTwoTailAUpper 515) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 213 515 0 z 1
      (firstBTwoTailALower 0 515) (firstBTwoTailAUpper 515) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_exact_rectangle 1 rest 515 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 1 515) (firstBTwoTailAUpper 515)
      (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 213 515 0 1 1
        (firstBTwoTailALower 1 515) (firstBTwoTailAUpper 515) (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 213 515 0 z 1
      (firstBTwoTailALower 1 515) (firstBTwoTailAUpper 515) (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_envelope_rectangle 2 j rest 515 k_le_j (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 2 515) (firstBTwoTailAUpper 515)
      39 (firstBTwoTailDUpper 2) a d at rectangle
    have corners : FirstBTwoTailNegativeCorners 213 515 1
        (firstBTwoTailALower 2 515) (firstBTwoTailAUpper 515) 39 (firstBTwoTailDUpper 2) := by
      norm_num [FirstBTwoTailNegativeCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_negative 213 515 z 1
      (firstBTwoTailALower 2 515) (firstBTwoTailAUpper 515) 39 (firstBTwoTailDUpper 2) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_516
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 516)
          (firstBTwoTailD tail) 213 516 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 516)
          (firstBTwoTailD tail) 213 516) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 516
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 516 * z =
    firstBTwoTailZNumerator a d 213 516 at root_eq
  have j_cases : j = 0 ∨ 1 ≤ j := by omega
  rcases j_cases with rfl | k_le_j
  · have rectangle := firstBTwoTail_exact_rectangle 0 rest 516 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 0 516) (firstBTwoTailAUpper 516)
      (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 213 516 0 1 1
        (firstBTwoTailALower 0 516) (firstBTwoTailAUpper 516) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 213 516 0 z 1
      (firstBTwoTailALower 0 516) (firstBTwoTailAUpper 516) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_envelope_rectangle 1 j rest 516 k_le_j (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 1 516) (firstBTwoTailAUpper 516)
      39 (firstBTwoTailDUpper 1) a d at rectangle
    have corners : FirstBTwoTailNegativeCorners 213 516 1
        (firstBTwoTailALower 1 516) (firstBTwoTailAUpper 516) 39 (firstBTwoTailDUpper 1) := by
      norm_num [FirstBTwoTailNegativeCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_negative 213 516 z 1
      (firstBTwoTailALower 1 516) (firstBTwoTailAUpper 516) 39 (firstBTwoTailDUpper 1) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_517
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 517)
          (firstBTwoTailD tail) 213 517 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 517)
          (firstBTwoTailD tail) 213 517) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 517
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 517 * z =
    firstBTwoTailZNumerator a d 213 517 at root_eq
  have j_cases : j = 0 ∨ 1 ≤ j := by omega
  rcases j_cases with rfl | k_le_j
  · have rectangle := firstBTwoTail_exact_rectangle 0 rest 517 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 0 517) (firstBTwoTailAUpper 517)
      (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 213 517 0 1 1
        (firstBTwoTailALower 0 517) (firstBTwoTailAUpper 517) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 213 517 0 z 1
      (firstBTwoTailALower 0 517) (firstBTwoTailAUpper 517) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_envelope_rectangle 1 j rest 517 k_le_j (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 1 517) (firstBTwoTailAUpper 517)
      39 (firstBTwoTailDUpper 1) a d at rectangle
    have corners : FirstBTwoTailNegativeCorners 213 517 1
        (firstBTwoTailALower 1 517) (firstBTwoTailAUpper 517) 39 (firstBTwoTailDUpper 1) := by
      norm_num [FirstBTwoTailNegativeCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_negative 213 517 z 1
      (firstBTwoTailALower 1 517) (firstBTwoTailAUpper 517) 39 (firstBTwoTailDUpper 1) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_518
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 518)
          (firstBTwoTailD tail) 213 518 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 518)
          (firstBTwoTailD tail) 213 518) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 518
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 518 * z =
    firstBTwoTailZNumerator a d 213 518 at root_eq
  have j_cases : j = 0 ∨ 1 ≤ j := by omega
  rcases j_cases with rfl | k_le_j
  · have rectangle := firstBTwoTail_exact_rectangle 0 rest 518 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 0 518) (firstBTwoTailAUpper 518)
      (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 213 518 0 1 1
        (firstBTwoTailALower 0 518) (firstBTwoTailAUpper 518) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 213 518 0 z 1
      (firstBTwoTailALower 0 518) (firstBTwoTailAUpper 518) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_envelope_rectangle 1 j rest 518 k_le_j (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 1 518) (firstBTwoTailAUpper 518)
      39 (firstBTwoTailDUpper 1) a d at rectangle
    have corners : FirstBTwoTailNegativeCorners 213 518 1
        (firstBTwoTailALower 1 518) (firstBTwoTailAUpper 518) 39 (firstBTwoTailDUpper 1) := by
      norm_num [FirstBTwoTailNegativeCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_negative 213 518 z 1
      (firstBTwoTailALower 1 518) (firstBTwoTailAUpper 518) 39 (firstBTwoTailDUpper 1) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_519
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 519)
          (firstBTwoTailD tail) 213 519 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 519)
          (firstBTwoTailD tail) 213 519) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 519
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 519 * z =
    firstBTwoTailZNumerator a d 213 519 at root_eq
  have j_cases : j = 0 ∨ 1 ≤ j := by omega
  rcases j_cases with rfl | k_le_j
  · have rectangle := firstBTwoTail_exact_rectangle 0 rest 519 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 0 519) (firstBTwoTailAUpper 519)
      (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 213 519 0 1 1
        (firstBTwoTailALower 0 519) (firstBTwoTailAUpper 519) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 213 519 0 z 1
      (firstBTwoTailALower 0 519) (firstBTwoTailAUpper 519) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_envelope_rectangle 1 j rest 519 k_le_j (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 1 519) (firstBTwoTailAUpper 519)
      39 (firstBTwoTailDUpper 1) a d at rectangle
    have corners : FirstBTwoTailNegativeCorners 213 519 1
        (firstBTwoTailALower 1 519) (firstBTwoTailAUpper 519) 39 (firstBTwoTailDUpper 1) := by
      norm_num [FirstBTwoTailNegativeCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_negative 213 519 z 1
      (firstBTwoTailALower 1 519) (firstBTwoTailAUpper 519) 39 (firstBTwoTailDUpper 1) a d rectangle corners root_eq).elim

private theorem firstBTwoTail_root_213_520
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBTwoTailA tail 520)
          (firstBTwoTailD tail) 213 520 * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail 520)
          (firstBTwoTailD tail) 213 520) :
    False := by
  let tail := List.replicate j .c ++ .b :: rest
  let a := firstBTwoTailA tail 520
  let d := firstBTwoTailD tail
  change firstBTwoTailZDenominator a d 213 520 * z =
    firstBTwoTailZNumerator a d 213 520 at root_eq
  have j_cases : j = 0 ∨ 1 ≤ j := by omega
  rcases j_cases with rfl | k_le_j
  · have rectangle := firstBTwoTail_exact_rectangle 0 rest 520 (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 0 520) (firstBTwoTailAUpper 520)
      (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d at rectangle
    have corners : FirstBTwoTailOpenCorners 213 520 0 1 1
        (firstBTwoTailALower 0 520) (firstBTwoTailAUpper 520) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) := by
      norm_num [FirstBTwoTailOpenCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_gap 213 520 0 z 1
      (firstBTwoTailALower 0 520) (firstBTwoTailAUpper 520) (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d rectangle corners root_eq).elim
  · have rectangle := firstBTwoTail_envelope_rectangle 1 j rest 520 k_le_j (by omega)
    change FirstBTwoTailRectangle
      (firstBTwoTailALower 1 520) (firstBTwoTailAUpper 520)
      39 (firstBTwoTailDUpper 1) a d at rectangle
    have corners : FirstBTwoTailNegativeCorners 213 520 1
        (firstBTwoTailALower 1 520) (firstBTwoTailAUpper 520) 39 (firstBTwoTailDUpper 1) := by
      norm_num [FirstBTwoTailNegativeCorners, firstBTwoTailALower,
        firstBTwoTailAUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator]
    exact (firstBTwoTailZ_no_nat_of_negative 213 520 z 1
      (firstBTwoTailALower 1 520) (firstBTwoTailAUpper 520) 39 (firstBTwoTailDUpper 1) a d rectangle corners root_eq).elim

/-- A candidate tail root is the explicit `(213, 465, 38)` point on the `ccb` cylinder. -/
theorem firstBTwoTail_root_eq_exception
    (tail : List TagLetter) (contains_b : .b ∈ tail) (x y z : Nat)
    (candidate : FirstBTwoRootCandidate x y)
    (root_eq :
      firstBTwoTailZDenominator (firstBTwoTailA tail y) (firstBTwoTailD tail) x y * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail y) (firstBTwoTailD tail) x y) :
    x = 213 ∧ y = 465 ∧ z = 38 ∧ ∃ rest, tail = [.c, .c, .b] ++ rest := by
  obtain ⟨j, rest, tail_eq⟩ := firstBTwoTail_first_b_decomposition tail contains_b
  subst tail
  unfold FirstBTwoRootCandidate at candidate
  rcases candidate with c183 | c186 | c199 | c202 | c204 | c206 |
    c208 | c209 | c210 | c211 | c212 | c213
  · rcases c183 with ⟨rfl, rfl⟩
    exact (firstBTwoTail_root_183_8 j rest z root_eq).elim
  · rcases c186 with ⟨rfl, rfl⟩
    exact (firstBTwoTail_root_186_9 j rest z root_eq).elim
  · rcases c199 with ⟨rfl, rfl⟩
    exact (firstBTwoTail_root_199_18 j rest z root_eq).elim
  · rcases c202 with ⟨rfl, rfl⟩
    exact (firstBTwoTail_root_202_23 j rest z root_eq).elim
  · rcases c204 with ⟨rfl, rfl⟩
    exact (firstBTwoTail_root_204_28 j rest z root_eq).elim
  · rcases c206 with ⟨rfl, rfl⟩
    exact (firstBTwoTail_root_206_36 j rest z root_eq).elim
  · rcases c208 with ⟨rfl, rfl⟩
    exact (firstBTwoTail_root_208_49 j rest z root_eq).elim
  · rcases c209 with ⟨rfl, rfl⟩
    exact (firstBTwoTail_root_209_60 j rest z root_eq).elim
  · rcases c210 with ⟨rfl, lower, upper⟩
    interval_cases y
    · exact (firstBTwoTail_root_210_77 j rest z root_eq).elim
    · exact (firstBTwoTail_root_210_78 j rest z root_eq).elim
  · rcases c211 with ⟨rfl, lower, upper⟩
    interval_cases y
    · exact (firstBTwoTail_root_211_107 j rest z root_eq).elim
    · exact (firstBTwoTail_root_211_108 j rest z root_eq).elim
    · exact (firstBTwoTail_root_211_109 j rest z root_eq).elim
  · rcases c212 with ⟨rfl, lower, upper⟩
    interval_cases y
    · exact (firstBTwoTail_root_212_174 j rest z root_eq).elim
    · exact (firstBTwoTail_root_212_175 j rest z root_eq).elim
    · exact (firstBTwoTail_root_212_176 j rest z root_eq).elim
    · exact (firstBTwoTail_root_212_177 j rest z root_eq).elim
    · exact (firstBTwoTail_root_212_178 j rest z root_eq).elim
    · exact (firstBTwoTail_root_212_179 j rest z root_eq).elim
    · exact (firstBTwoTail_root_212_180 j rest z root_eq).elim
    · exact (firstBTwoTail_root_212_181 j rest z root_eq).elim
  · rcases c213 with ⟨rfl, lower, upper⟩
    interval_cases y
    · obtain ⟨j_eq, z_eq⟩ := firstBTwoTail_root_213_465 j rest z root_eq
      refine ⟨rfl, rfl, z_eq, rest, ?_⟩
      simp [j_eq]
    · exact (firstBTwoTail_root_213_466 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_467 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_468 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_469 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_470 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_471 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_472 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_473 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_474 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_475 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_476 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_477 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_478 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_479 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_480 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_481 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_482 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_483 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_484 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_485 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_486 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_487 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_488 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_489 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_490 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_491 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_492 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_493 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_494 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_495 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_496 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_497 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_498 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_499 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_500 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_501 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_502 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_503 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_504 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_505 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_506 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_507 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_508 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_509 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_510 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_511 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_512 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_513 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_514 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_515 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_516 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_517 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_518 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_519 j rest z root_eq).elim
    · exact (firstBTwoTail_root_213_520 j rest z root_eq).elim

-- END GENERATED SECOND-FIRST-B TAIL CERTIFICATE

end MatrixMortality.ParabolicBlade
