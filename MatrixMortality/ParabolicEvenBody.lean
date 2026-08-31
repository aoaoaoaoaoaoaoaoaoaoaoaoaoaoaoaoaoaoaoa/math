import MatrixMortality.ParabolicDefectCylinder

/-!
# Even-body arithmetic for the phase-zero right-c bridge

The residual `b | b | c` determinant admits an exact complement coordinate
`D = S - C - 1`.  This file uses that coordinate to eliminate the all-`b` body ray left by
the parity rectangle.
-/

namespace MatrixMortality.ParabolicBlade

private theorem tagEncode_b_run_length (k : Nat) :
    (tagEncode 3 (List.replicate k .b)).length = 5 * k := by
  induction k with
  | zero => simp
  | succ k induction =>
      rw [List.replicate_succ, tagEncode_cons]
      simp only [List.length_append, tagCode_b_length, induction]
      omega

private theorem tagEncode_b_run_code (k : Nat) :
    242 * ternaryCode (tagEncode 3 (List.replicate k .b)) =
      203 * (3 ^ (tagEncode 3 (List.replicate k .b)).length - 1) := by
  induction k with
  | zero => simp [ternaryCode]
  | succ k induction =>
      rw [List.replicate_succ, tagEncode_cons, ternaryCode_append]
      have prefix_code : ternaryCode (tagCode 3 .b) = 203 := by decide
      rw [tagEncode_b_run_length] at induction
      rw [prefix_code]
      simp only [List.length_append, tagCode_b_length, tagEncode_b_run_length]
      have power_positive : 1 ≤ 3 ^ (5 * k) := one_le_pow₀ (by norm_num)
      rw [show 3 + 2 + 5 * k = 5 + 5 * k by omega, pow_add]
      norm_num
      omega

/-- Positional value of the zero digits complementary to a native encoded tag word. -/
def tagComplementCode (body : List TagLetter) : Nat :=
  3 ^ (tagEncode 3 body).length - ternaryCode (tagEncode 3 body) - 1

theorem tagComplementCode_append_c (body : List TagLetter) :
    tagComplementCode (body ++ [.c]) = 3 * tagComplementCode body := by
  have code_lt := ternaryCode_lt_pow_length (tagEncode 3 body)
  simp only [tagComplementCode, tagEncode_append, tagEncode_cons, tagEncode_nil, tagCode,
    List.append_nil, ternaryCode_append, List.length_append,
    List.length_singleton, ternaryCode_singleton, ternaryDigit, pow_one]
  omega

theorem tagComplementCode_append_b (body : List TagLetter) :
    tagComplementCode (body ++ [.b]) = 243 * tagComplementCode body + 39 := by
  have code_lt := ternaryCode_lt_pow_length (tagEncode 3 body)
  have b_length : (tagEncode 3 [.b]).length = 5 := by decide
  have b_code : ternaryCode (tagEncode 3 [.b]) = 203 := by decide
  unfold tagComplementCode
  rw [tagEncode_append, ternaryCode_append, List.length_append, b_length, b_code, pow_add]
  norm_num only [Nat.reducePow]
  omega

theorem tagEncode_length_mod_four (body : List TagLetter) :
    (tagEncode 3 body).length % 4 = body.length % 4 := by
  induction body with
  | nil => rfl
  | cons head tail induction =>
      cases head <;> simp only [tagEncode_cons, tagCode, List.length_append,
        List.length_cons, List.length_nil, List.length_replicate] <;> omega

theorem tagComplementCode_mod_two (body : List TagLetter) :
    tagComplementCode body % 2 = body.count .b % 2 := by
  induction body using List.reverseRecOn with
  | nil => simp [tagComplementCode]
  | append_singleton body letter induction =>
      cases letter
      · have count_eq :
            (body ++ [TagLetter.b]).count TagLetter.b = body.count TagLetter.b + 1 := by simp
        rw [tagComplementCode_append_b, count_eq, Nat.add_mod, Nat.mul_mod, induction]
        norm_num
      · have count_eq :
            (body ++ [TagLetter.c]).count TagLetter.b = body.count TagLetter.b := by simp
        rw [tagComplementCode_append_c, count_eq, Nat.mul_mod, induction]
        norm_num

theorem tagComplementCode_global_bound (body : List TagLetter) :
    242 * tagComplementCode body ≤
      39 * (3 ^ (tagEncode 3 body).length - 1) := by
  induction body using List.reverseRecOn with
  | nil => simp [tagComplementCode]
  | append_singleton body letter induction =>
      cases letter
      · have scale_eq :
            3 ^ (tagEncode 3 (body ++ [.b])).length =
              243 * 3 ^ (tagEncode 3 body).length := by
          rw [tagEncode_append, List.length_append]
          have b_length : (tagEncode 3 [.b]).length = 5 := by decide
          rw [b_length, pow_add]
          norm_num
          ring
        rw [tagComplementCode_append_b, scale_eq]
        have scale_positive : 1 ≤ 3 ^ (tagEncode 3 body).length :=
          one_le_pow₀ (by norm_num)
        omega
      · have scale_eq :
            3 ^ (tagEncode 3 (body ++ [.c])).length =
              3 * 3 ^ (tagEncode 3 body).length := by
          rw [tagEncode_append, List.length_append]
          have c_length : (tagEncode 3 [.c]).length = 1 := by decide
          rw [c_length, pow_add]
          norm_num
          ring
        rw [tagComplementCode_append_c, scale_eq]
        have scale_positive : 1 ≤ 3 ^ (tagEncode 3 body).length :=
          one_le_pow₀ (by norm_num)
        omega

private theorem tagComplementCode_cast (body : List TagLetter) :
    (tagComplementCode body : ℤ) =
      (3 : ℤ) ^ (tagEncode 3 body).length -
        ternaryCode (tagEncode 3 body) - 1 := by
  have code_lt := ternaryCode_lt_pow_length (tagEncode 3 body)
  have code_le : ternaryCode (tagEncode 3 body) ≤
      3 ^ (tagEncode 3 body).length := code_lt.le
  have difference_positive :
      1 ≤ 3 ^ (tagEncode 3 body).length - ternaryCode (tagEncode 3 body) := by omega
  unfold tagComplementCode
  rw [Nat.cast_sub difference_positive, Nat.cast_sub code_le]
  push_cast
  rfl

/-- Positive complement polynomial produced by moving away from the all-`c` code ray. -/
def bZeroBDefectCOneComplementCore {R : Type*} [CommRing R] (x y z : R) : R :=
  631601581536 * x * z + 59048086536 * x +
    620717828832 * y * z + 58005064872 * y +
    422435605080 * z + 37838186340

/-- The `b | b | c` core is its all-`c` factorization plus the complement coordinate
`D = S - C - 1` times a coefficient-positive polynomial. -/
theorem bZeroBDefectCOneCodeCore_complement_factor {R : Type*} [CommRing R]
    (S C x y z : R) :
    bZeroBDefectCOneCodeCore S C x y z =
      (72 * S * y - 9 * S - 8 * y + 9) *
          (119911680 * x * z + 11209824 * x - 25766986436 * z - 2408152393) +
        (S - C - 1) * bZeroBDefectCOneComplementCore x y z := by
  unfold bZeroBDefectCOneCodeCore bZeroBDefectCOneComplementCore
  ring

private def bZeroBDefectCOneComplementOneQuotient (s d x y z : ℤ) : ℤ :=
  157900395384 * d * x * z + 14762021634 * d * x +
    155179457208 * d * y * z + 14501266218 * d * y +
    105608901270 * d * z + 9459546585 * d +
    8633640960 * s * x * y * z + 807107328 * s * x * y -
    1079205120 * s * x * z - 100888416 * s * x -
    1855223023392 * s * y * z - 173386972296 * s * y +
    231902877924 * s * z + 21673371537 * s +
    479646720 * x * y * z + 44839296 * x * y +
    78950197692 * x * z + 7381010817 * x -
    25478217140 * y * z - 2381976463 * y +
    52804450635 * z + 4729773292

/-- The first complement residue class makes the primitive core `8` modulo `16`. -/
theorem bZeroBDefectCOneCodeCore_complement_one_factor (s d x y z : ℤ) :
    bZeroBDefectCOneCodeCore (16 * s + 1) ((16 * s + 1) - (4 * d + 2) - 1)
        x y z =
      16 * bZeroBDefectCOneComplementOneQuotient s d x y z + 8 := by
  unfold bZeroBDefectCOneCodeCore bZeroBDefectCOneComplementOneQuotient
  ring

private def bZeroBDefectCOneComplementNineQuotient (s d x y z : ℤ) : ℤ :=
  157900395384 * d * x * z + 14762021634 * d * x +
    155179457208 * d * y * z + 14501266218 * d * y +
    105608901270 * d * z + 9459546585 * d +
    8633640960 * s * x * y * z + 807107328 * s * x * y -
    1079205120 * s * x * z - 100888416 * s * x -
    1855223023392 * s * y * z - 173386972296 * s * y +
    231902877924 * s * z + 21673371537 * s +
    4796467200 * x * y * z + 448392960 * x * y -
    539602560 * x * z - 50444208 * x -
    1030679457440 * y * z - 96326095720 * y +
    115951438962 * z + 10836685768

/-- The second complement residue class makes the primitive core `8` modulo `16`. -/
theorem bZeroBDefectCOneCodeCore_complement_nine_factor (s d x y z : ℤ) :
    bZeroBDefectCOneCodeCore (16 * s + 9) ((16 * s + 9) - 4 * d - 1)
        x y z =
      16 * bZeroBDefectCOneComplementNineQuotient s d x y z + 8 := by
  unfold bZeroBDefectCOneCodeCore bZeroBDefectCOneComplementNineQuotient
  ring

/-- Coefficient of `y*z` in the complement-coordinate core. -/
def bZeroBDefectCOneComplementYZ (S D x : ℤ) : ℤ :=
  32 * (19397432151 * D + 269801280 * S * x - 57975719481 * S -
    29977920 * x + 6441746609)

/-- Coefficient of `y` in the complement-coordinate core. -/
def bZeroBDefectCOneComplementY (S D x : ℤ) : ℤ :=
  8 * (7250633109 * D + 100888416 * S * x - 21673371537 * S -
    11209824 * x + 2408152393)

/-- Coefficient of `z` in the complement-coordinate core. -/
def bZeroBDefectCOneComplementZ (S D x : ℤ) : ℤ :=
  12 * (52633465128 * D * x + 35202967090 * D - 89933760 * S * x +
    19325239827 * S + 89933760 * x - 19325239827)

/-- Constant coefficient in the complement-coordinate core. -/
def bZeroBDefectCOneComplementConstant (S D x : ℤ) : ℤ :=
  3 * (19682695512 * D * x + 12612728780 * D - 33629472 * S * x +
    7224457179 * S + 33629472 * x - 7224457179)

theorem bZeroBDefectCOneCodeCore_complement_collect (S D x y z : ℤ) :
    bZeroBDefectCOneCodeCore S (S - 1 - D) x y z =
      bZeroBDefectCOneComplementYZ S D x * y * z +
        bZeroBDefectCOneComplementY S D x * y +
        bZeroBDefectCOneComplementZ S D x * z +
        bZeroBDefectCOneComplementConstant S D x := by
  unfold bZeroBDefectCOneCodeCore bZeroBDefectCOneComplementYZ
    bZeroBDefectCOneComplementY bZeroBDefectCOneComplementZ
    bZeroBDefectCOneComplementConstant
  ring

/-- The complement-coordinate SFFT discriminant splits into three explicit linear factors. -/
theorem bZeroBDefectCOneComplement_discriminant (S D x : ℤ) :
    bZeroBDefectCOneComplementY S D x * bZeroBDefectCOneComplementZ S D x -
        bZeroBDefectCOneComplementYZ S D x *
          bZeroBDefectCOneComplementConstant S D x =
      -306110016 * D * (48 * x - 3029) *
        (1096376045 * D + 2022264 * S * x - 3287358654 * S -
          224696 * x + 366706454) := by
  unfold bZeroBDefectCOneComplementYZ bZeroBDefectCOneComplementY
    bZeroBDefectCOneComplementZ bZeroBDefectCOneComplementConstant
  ring

/-- A zero complement core becomes a finite divisor equation between its two affine factors. -/
theorem bZeroBDefectCOneComplement_sfft (S D x y z : ℤ) :
    (bZeroBDefectCOneComplementYZ S D x * y +
        bZeroBDefectCOneComplementZ S D x) *
      (bZeroBDefectCOneComplementYZ S D x * z +
        bZeroBDefectCOneComplementY S D x) =
      bZeroBDefectCOneComplementYZ S D x *
          bZeroBDefectCOneCodeCore S (S - 1 - D) x y z -
        306110016 * D * (48 * x - 3029) *
          (1096376045 * D + 2022264 * S * x - 3287358654 * S -
            224696 * x + 366706454) := by
  rw [bZeroBDefectCOneCodeCore_complement_collect]
  linear_combination bZeroBDefectCOneComplement_discriminant S D x

/-- Wait factor inherited from the all-`c` ray. -/
def bZeroBDefectCOneWaitFactor {R : Type*} [CommRing R] (S y : R) : R :=
  72 * S * y - 9 * S - 8 * y + 9

/-- Affine `x` pencil inherited from the all-`c` ray. -/
def bZeroBDefectCOneRootPencil {R : Type*} [CommRing R] (x z : R) : R :=
  119911680 * x * z + 11209824 * x - 25766986436 * z - 2408152393

/-- Complement-coordinate decomposition into the all-`c` pencil and the positive correction. -/
theorem bZeroBDefectCOneCodeCore_thin_decomposition {R : Type*} [CommRing R]
    (S D x y z : R) :
    bZeroBDefectCOneCodeCore S (S - 1 - D) x y z =
      bZeroBDefectCOneWaitFactor S y * bZeroBDefectCOneRootPencil x z +
        D * bZeroBDefectCOneComplementCore x y z := by
  rw [bZeroBDefectCOneCodeCore_complement_factor]
  unfold bZeroBDefectCOneWaitFactor bZeroBDefectCOneRootPencil
  ring

private theorem affine_nat_ne_zero_of_negative_positive
    (a b : ℚ) (n x : Nat) (lower_negative : a * n + b < 0)
    (upper_positive : 0 < a * (n + 1) + b) : a * x + b ≠ 0 := by
  intro zero
  have slope_positive : 0 < a := by nlinarith
  have x_lower : (n : ℚ) < x := by nlinarith
  have x_upper : (x : ℚ) < n + 1 := by nlinarith
  have x_lower_nat : n < x := by exact_mod_cast x_lower
  have x_upper_nat : x < n + 1 := by exact_mod_cast x_upper
  omega

private theorem affine_nat_ne_zero_of_positive_negative
    (a b : ℚ) (n x : Nat) (lower_positive : 0 < a * n + b)
    (upper_negative : a * (n + 1) + b < 0) : a * x + b ≠ 0 := by
  intro zero
  have slope_negative : a < 0 := by nlinarith
  have x_lower : (n : ℚ) < x := by nlinarith
  have x_upper : (x : ℚ) < n + 1 := by nlinarith
  have x_lower_nat : n < x := by exact_mod_cast x_lower
  have x_upper_nat : x < n + 1 := by exact_mod_cast x_upper
  omega

/-- A sufficiently thin positive complement cannot close the `b | b | c` core. -/
theorem bZeroBDefectCOneCodeCore_ne_zero_of_thin_complement
    (S D : ℚ) (D_positive : 0 < D) (thin : 2160000 * D ≤ S - 1)
    (x y z : Nat) :
    bZeroBDefectCOneCodeCore S (S - 1 - D) x y z ≠ 0 := by
  let F : ℚ := bZeroBDefectCOneWaitFactor S y
  let slope : ℚ :=
    F * (119911680 * z + 11209824) +
      D * (631601581536 * z + 59048086536)
  let intercept : ℚ :=
    F * (-25766986436 * z - 2408152393) +
      D * (620717828832 * y * z + 58005064872 * y +
        422435605080 * z + 37838186340)
  have core_eq :
      bZeroBDefectCOneCodeCore S (S - 1 - D) x y z = slope * x + intercept := by
    rw [bZeroBDefectCOneCodeCore_thin_decomposition]
    unfold bZeroBDefectCOneRootPencil bZeroBDefectCOneComplementCore
    dsimp [F, slope, intercept]
    ring
  rw [core_eq]
  by_cases y_zero : y = 0
  · subst y
    have scale_greater_one : 1 < S := by nlinarith
    have F_eq : F = -9 * (S - 1) := by
      dsimp [F, bZeroBDefectCOneWaitFactor]
      ring
    have complement_small : 1080000 * D < S - 1 := by nlinarith
    have lower_positive : 0 < slope * 214 + intercept := by
      have delta_positive : (0 : ℚ) < 105886916 * z + 9250057 := by positivity
      have pencil_eq :
          bZeroBDefectCOneRootPencil (214 : ℚ) z =
            -(105886916 * z + 9250057) := by
        unfold bZeroBDefectCOneRootPencil
        ring
      have complement_positive :
          0 < bZeroBDefectCOneComplementCore (214 : ℚ) 0 z := by
        unfold bZeroBDefectCOneComplementCore
        positivity
      have endpoint_eq : slope * 214 + intercept =
          F * bZeroBDefectCOneRootPencil (214 : ℚ) z +
            D * bZeroBDefectCOneComplementCore (214 : ℚ) 0 z := by
        unfold bZeroBDefectCOneRootPencil bZeroBDefectCOneComplementCore
        dsimp [slope, intercept]
        ring
      rw [endpoint_eq, F_eq, pencil_eq]
      have first_positive :
          0 < (-9 * (S - 1)) * (-(105886916 * z + 9250057)) := by
        have left_negative : -9 * (S - 1) < 0 := by nlinarith
        have right_negative : (-(105886916 * (z : ℚ) + 9250057) : ℚ) < 0 := by
          nlinarith
        exact mul_pos_of_neg_of_neg left_negative right_negative
      have second_positive :
          0 < D * bZeroBDefectCOneComplementCore (214 : ℚ) 0 z :=
        mul_pos D_positive complement_positive
      nlinarith
    have upper_negative : slope * (214 + 1) + intercept < 0 := by
      have epsilon_positive : (0 : ℚ) < 14024764 * z + 1959767 := by positivity
      have pencil_eq :
          bZeroBDefectCOneRootPencil (215 : ℚ) z =
            14024764 * z + 1959767 := by
        unfold bZeroBDefectCOneRootPencil
        ring
      have complement_eq :
          bZeroBDefectCOneComplementCore (215 : ℚ) 0 z =
            136216775635320 * z + 12733176791580 := by
        unfold bZeroBDefectCOneComplementCore
        ring
      have complement_bound :
          bZeroBDefectCOneComplementCore (215 : ℚ) 0 z <
            9 * 1080000 * (14024764 * z + 1959767) := by
        rw [complement_eq]
        have difference_positive :
            (0 : ℚ) < 103930444680 * z + 6315758448420 := by positivity
        nlinarith
      have endpoint_eq : slope * (214 + 1) + intercept =
          F * bZeroBDefectCOneRootPencil (215 : ℚ) z +
            D * bZeroBDefectCOneComplementCore (215 : ℚ) 0 z := by
        norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
        unfold bZeroBDefectCOneRootPencil bZeroBDefectCOneComplementCore
        dsimp [slope, intercept]
        ring
      rw [endpoint_eq, F_eq, pencil_eq]
      have scaled_bound :
          D * bZeroBDefectCOneComplementCore (215 : ℚ) 0 z <
            9 * (S - 1) * (14024764 * z + 1959767) := by
        have scaled_complement_bound :=
          mul_lt_mul_of_pos_left complement_bound D_positive
        nlinarith [scaled_complement_bound, mul_pos D_positive epsilon_positive]
      nlinarith
    exact affine_nat_ne_zero_of_positive_negative slope intercept 214 x
      lower_positive upper_negative
  · have y_positive_nat : 1 ≤ y := Nat.one_le_iff_ne_zero.mpr y_zero
    have y_positive : (0 : ℚ) < y := by exact_mod_cast y_positive_nat
    have y_one : (1 : ℚ) ≤ y := by exact_mod_cast y_positive_nat
    have y_minus_nonnegative : (0 : ℚ) ≤ y - 1 := sub_nonneg.mpr y_one
    have scale_positive : 0 < S := by nlinarith
    have complement_small : 22000 * D < S := by nlinarith
    have F_lower : 63 * S * y < F := by
      dsimp [F, bZeroBDefectCOneWaitFactor]
      have scale_term_nonnegative : 0 ≤ 9 * S * (y - 1) := by positivity
      nlinarith
    have F_positive : 0 < F :=
      lt_of_le_of_lt (mul_nonneg (by positivity) y_positive.le) F_lower
    have lower_negative : slope * 214 + intercept < 0 := by
      let δ : ℚ := 105886916 * z + 9250057
      let J : ℚ := bZeroBDefectCOneComplementCore (214 : ℚ) y z
      let B : ℚ :=
        (620717828832 + 135585174053784) * z +
          (58005064872 + 12674128705044)
      have delta_positive : 0 < δ := by dsimp [δ]; positivity
      have J_positive : 0 < J := by
        dsimp [J]
        unfold bZeroBDefectCOneComplementCore
        positivity
      have J_eq : J =
          y * (620717828832 * z + 58005064872) +
            135585174053784 * z + 12674128705044 := by
        dsimp [J]
        unfold bZeroBDefectCOneComplementCore
        ring
      have J_le : J ≤ y * B := by
        rw [J_eq]
        dsimp [B]
        have base_nonnegative :
            0 ≤ ((y : ℚ) - 1) *
              (135585174053784 * z + 12674128705044) :=
          mul_nonneg y_minus_nonnegative (by positivity)
        nlinarith
      have B_bound : B < 63 * 22000 * δ := by
        dsimp [B, δ]
        have difference_positive :
            (0 : ℚ) < 10553373693384 * z + 88445232084 := by positivity
        nlinarith
      have DJ_lt : D * J < F * δ := by
        have J_bound : J < y * (63 * 22000 * δ) :=
          lt_of_le_of_lt J_le (mul_lt_mul_of_pos_left B_bound y_positive)
        have complement_product_bound := mul_lt_mul_of_pos_left J_bound D_positive
        have scale_product_bound : 63 * (22000 * D) * y * δ < 63 * S * y * δ := by
          nlinarith [mul_pos y_positive delta_positive]
        have wait_product_bound := mul_lt_mul_of_pos_right F_lower delta_positive
        nlinarith [complement_product_bound, scale_product_bound, wait_product_bound]
      have endpoint_eq : slope * 214 + intercept = -F * δ + D * J := by
        dsimp [δ, J]
        unfold bZeroBDefectCOneComplementCore
        dsimp [slope, intercept]
        ring
      rw [endpoint_eq]
      nlinarith
    have upper_positive : 0 < slope * (214 + 1) + intercept := by
      have pencil_positive :
          (0 : ℚ) < bZeroBDefectCOneRootPencil (215 : ℚ) z := by
        rw [show bZeroBDefectCOneRootPencil (215 : ℚ) z =
          14024764 * z + 1959767 by
            unfold bZeroBDefectCOneRootPencil
            ring]
        positivity
      have complement_positive :
          0 < bZeroBDefectCOneComplementCore (215 : ℚ) y z := by
        rw [show bZeroBDefectCOneComplementCore (215 : ℚ) y z =
          y * (620717828832 * z + 58005064872) +
            136216775635320 * z + 12733176791580 by
              unfold bZeroBDefectCOneComplementCore
              ring]
        positivity
      have endpoint_eq : slope * (214 + 1) + intercept =
          F * bZeroBDefectCOneRootPencil (215 : ℚ) z +
            D * bZeroBDefectCOneComplementCore (215 : ℚ) y z := by
        norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
        unfold bZeroBDefectCOneRootPencil bZeroBDefectCOneComplementCore
        dsimp [slope, intercept]
        ring
      rw [endpoint_eq]
      positivity
    exact affine_nat_ne_zero_of_negative_positive slope intercept 214 x
      lower_negative upper_positive

private theorem three_pow_mod_sixteen_of_mod_four_zero
    (n : Nat) (residue : n % 4 = 0) : 3 ^ n % 16 = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k := ⟨n / 4, by omega⟩
  rw [pow_mul]
  norm_num [Nat.pow_mod]

private theorem three_pow_mod_sixteen_of_mod_four_two
    (n : Nat) (residue : n % 4 = 2) : 3 ^ n % 16 = 9 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 2 := ⟨n / 4, by omega⟩
  rw [pow_add, pow_mul]
  norm_num only [Nat.reducePow]
  rw [Nat.mul_mod]
  rw [show 81 ^ k % 16 = 1 by norm_num [Nat.pow_mod]]

private theorem bZeroBDefectCOneCodeCore_ne_zero_of_complement_residue
    (body : List TagLetter) (x y z : Nat)
    (residue :
      (body.length % 4 = 0 ∧ tagComplementCode body % 4 = 2) ∨
        (body.length % 4 = 2 ∧ tagComplementCode body % 4 = 0)) :
    bZeroBDefectCOneCodeCore
        ((3 : ℤ) ^ (tagEncode 3 body).length)
        (ternaryCode (tagEncode 3 body)) x y z ≠ 0 := by
  let S : Nat := 3 ^ (tagEncode 3 body).length
  let C : Nat := ternaryCode (tagEncode 3 body)
  let D : Nat := tagComplementCode body
  have complement_eq : (D : ℤ) = (S : ℤ) - C - 1 := by
    dsimp [S, C, D]
    exact tagComplementCode_cast body
  change bZeroBDefectCOneCodeCore (S : ℤ) (C : ℤ) x y z ≠ 0
  rcases residue with ⟨length_zero, complement_two⟩ | ⟨length_two, complement_zero⟩
  · have encoded_length_zero : (tagEncode 3 body).length % 4 = 0 := by
      rw [tagEncode_length_mod_four]
      exact length_zero
    have scale_mod : S % 16 = 1 := by
      dsimp [S]
      exact three_pow_mod_sixteen_of_mod_four_zero _ encoded_length_zero
    obtain ⟨s, scale_eq⟩ : ∃ s, S = 16 * s + 1 := ⟨S / 16, by omega⟩
    obtain ⟨d, complement_form⟩ : ∃ d, D = 4 * d + 2 := ⟨D / 4, by omega⟩
    have scale_cast : (S : ℤ) = 16 * (s : ℤ) + 1 := by exact_mod_cast scale_eq
    have complement_cast : (D : ℤ) = 4 * (d : ℤ) + 2 := by
      exact_mod_cast complement_form
    have code_cast : (C : ℤ) =
        (16 * (s : ℤ) + 1) - (4 * (d : ℤ) + 2) - 1 := by
      nlinarith
    rw [scale_cast, code_cast, bZeroBDefectCOneCodeCore_complement_one_factor]
    omega
  · have encoded_length_two : (tagEncode 3 body).length % 4 = 2 := by
      rw [tagEncode_length_mod_four]
      exact length_two
    have scale_mod : S % 16 = 9 := by
      dsimp [S]
      exact three_pow_mod_sixteen_of_mod_four_two _ encoded_length_two
    obtain ⟨s, scale_eq⟩ : ∃ s, S = 16 * s + 9 := ⟨S / 16, by omega⟩
    obtain ⟨d, complement_form⟩ : ∃ d, D = 4 * d := ⟨D / 4, by omega⟩
    have scale_cast : (S : ℤ) = 16 * (s : ℤ) + 9 := by exact_mod_cast scale_eq
    have complement_cast : (D : ℤ) = 4 * (d : ℤ) := by
      exact_mod_cast complement_form
    have code_cast : (C : ℤ) =
        (16 * (s : ℤ) + 9) - 4 * (d : ℤ) - 1 := by
      nlinarith
    rw [scale_cast, code_cast, bZeroBDefectCOneCodeCore_complement_nine_factor]
    omega

private def bZeroBDefectCOneAllBLinearCore (S x y z : ℤ) : ℤ :=
  (S * (1044670556160 * x * y + 12185647020432 * x -
        212377988168208 * y + 36297742527864) +
      (-116074506240 * x * y - 12185647020432 * x +
        12838445207824 * y - 36297742527864)) * z +
    S * (97659986688 * x * y + 1139230189116 * x -
      19848724882812 * y + 3360322589607) +
    (-10851109632 * x * y - 1139230189116 * x +
      1199992751420 * y - 3360322589607)

private theorem bZeroBDefectCOneAllBLinearCore_eq
    (S C x y z : ℤ) (coordinates : 242 * (S - C - 1) = 39 * (S - 1)) :
    121 * bZeroBDefectCOneCodeCore S C x y z =
      bZeroBDefectCOneAllBLinearCore S x y z := by
  rw [bZeroBDefectCOneCodeCore_complement_factor]
  unfold bZeroBDefectCOneComplementCore bZeroBDefectCOneAllBLinearCore
  linear_combination coordinates *
    (315800790768 * x * z + 29524043268 * x + 310358914416 * y * z +
      29002532436 * y + 211217802540 * z + 18919093170)

private def allBZSlope (x y : ℤ) : ℤ :=
  1044670556160 * x * y + 12185647020432 * x -
    212377988168208 * y + 36297742527864

private def allBZIntercept (x y : ℤ) : ℤ :=
  -116074506240 * x * y - 12185647020432 * x +
    12838445207824 * y - 36297742527864

private def allBConstantSlope (x y : ℤ) : ℤ :=
  97659986688 * x * y + 1139230189116 * x -
    19848724882812 * y + 3360322589607

private def allBConstantIntercept (x y : ℤ) : ℤ :=
  -10851109632 * x * y - 1139230189116 * x +
    1199992751420 * y - 3360322589607

private theorem allBLinearCore_collect (S x y z : ℤ) :
    bZeroBDefectCOneAllBLinearCore S x y z =
      (S * allBZSlope x y + allBZIntercept x y) * z +
        S * allBConstantSlope x y + allBConstantIntercept x y := by
  rfl

private theorem allB_resultant_factor (x y : ℤ) :
    allBZSlope x y * allBConstantIntercept x y -
        allBZIntercept x y * allBConstantSlope x y =
      -1926044220672 * y * (48 * x - 3029) *
        (674088 * x - 4333144 * y - 1095244575) := by
  unfold allBZSlope allBZIntercept allBConstantSlope allBConstantIntercept
  ring

private theorem allBLinearCore_bounds
    (S x y z : ℤ) (scale_large : 59049 ≤ S)
    (x_nonnegative : 0 ≤ x) (y_nonnegative : 0 ≤ y) (z_nonnegative : 0 ≤ z)
    (core_zero : bZeroBDefectCOneAllBLinearCore S x y z = 0) :
    x ≤ 203 ∧ 1 ≤ y ∧ y < 10000 := by
  have scale_one_lt : 1 < S := by omega
  have y_positive : 1 ≤ y := by
    by_contra y_not_positive
    have y_zero : y = 0 := by omega
    subst y
    have core_eq :
        bZeroBDefectCOneAllBLinearCore S x 0 z =
          (S - 1) * ((12185647020432 * x + 36297742527864) * z +
            1139230189116 * x + 3360322589607) := by
      unfold bZeroBDefectCOneAllBLinearCore
      ring
    rw [core_eq] at core_zero
    have right_positive :
        0 < (12185647020432 * x + 36297742527864) * z +
          1139230189116 * x + 3360322589607 := by positivity
    have : 0 < (S - 1) *
        ((12185647020432 * x + 36297742527864) * z +
          1139230189116 * x + 3360322589607) := by positivity
    omega
  have x_small : x ≤ 203 := by
    by_contra x_not_small
    have x_large : 204 ≤ x := by omega
    let positivePart : ℤ :=
      (12185647020432 * x + 36297742527864) * z +
        1139230189116 * x + 3360322589607
    let zPenalty : ℤ :=
      116074506240 * x * (9 * S - 1) -
        (212377988168208 * S - 12838445207824)
    let constantPenalty : ℤ :=
      10851109632 * x * (9 * S - 1) -
        (19848724882812 * S - 1199992751420)
    have scale_factor_positive : 0 < 9 * S - 1 := by nlinarith
    have x_excess_nonnegative : 0 ≤ x - 204 := by omega
    have excess_scale_nonnegative : 0 ≤ (x - 204) * (9 * S - 1) :=
      mul_nonneg x_excess_nonnegative scale_factor_positive.le
    have positivePart_positive : 0 < positivePart := by
      dsimp [positivePart]
      positivity
    have zPenalty_positive : 0 < zPenalty := by
      dsimp [zPenalty]
      nlinarith
    have constantPenalty_positive : 0 < constantPenalty := by
      dsimp [constantPenalty]
      nlinarith
    have core_eq :
        bZeroBDefectCOneAllBLinearCore S x y z =
          (S - 1) * positivePart + y * (zPenalty * z + constantPenalty) := by
      unfold bZeroBDefectCOneAllBLinearCore
      dsimp [positivePart, zPenalty, constantPenalty]
      ring
    rw [core_eq] at core_zero
    have penalty_positive : 0 < zPenalty * z + constantPenalty := by positivity
    have : 0 < (S - 1) * positivePart + y * (zPenalty * z + constantPenalty) := by
      positivity
    omega
  let numerator : ℤ :=
    (S - 1) * ((12185647020432 * x + 36297742527864) * z +
      1139230189116 * x + 3360322589607)
  let denominator : ℤ :=
    (212377988168208 * S - 12838445207824 -
        x * 116074506240 * (9 * S - 1)) * z +
      19848724882812 * S - 1199992751420 -
        x * 10851109632 * (9 * S - 1)
  have x_defect_nonnegative : 0 ≤ 203 - x := by omega
  have denominator_eq : denominator =
      (309865267728 * S + 10724679558896) * z +
        23747585148 * S + 1002782503876 +
      (203 - x) * ((1044670556160 * S - 116074506240) * z +
        97659986688 * S - 10851109632) := by
    dsimp [denominator]
    ring
  have denominator_positive : 0 < denominator := by
    rw [denominator_eq]
    have defect_coefficient_nonnegative :
        0 ≤ (1044670556160 * S - 116074506240) * z +
          97659986688 * S - 10851109632 := by
      have z_slope_positive : 0 < 1044670556160 * S - 116074506240 := by nlinarith
      have z_term_nonnegative :
          0 ≤ (1044670556160 * S - 116074506240) * z :=
        mul_nonneg z_slope_positive.le z_nonnegative
      nlinarith
    positivity
  have core_eq :
      bZeroBDefectCOneAllBLinearCore S x y z = numerator - y * denominator := by
    unfold bZeroBDefectCOneAllBLinearCore
    dsimp [numerator, denominator]
    ring
  have numerator_eq : numerator = y * denominator := by
    rw [core_eq] at core_zero
    linarith
  have margin_eq : 10000 * denominator - numerator =
      (588668589604440 * S + 109756779676635560) * z +
        2851800499845 * S + 10262449089740155 +
      (203 - x) *
        ((10458891208620432 * S - 1172930709420432) * z +
          977739097069116 * S - 109650326509116) := by
    dsimp [numerator, denominator]
    ring
  have margin_positive : 0 < 10000 * denominator - numerator := by
    rw [margin_eq]
    have defect_margin_nonnegative :
        0 ≤ (10458891208620432 * S - 1172930709420432) * z +
          977739097069116 * S - 109650326509116 := by
      have z_slope_positive :
          0 < 10458891208620432 * S - 1172930709420432 := by nlinarith
      have z_term_nonnegative :
          0 ≤ (10458891208620432 * S - 1172930709420432) * z :=
        mul_nonneg z_slope_positive.le z_nonnegative
      nlinarith
    positivity
  have multiplied_lt : y * denominator < 10000 * denominator := by
    rw [← numerator_eq]
    linarith
  have y_small : y < 10000 :=
    lt_of_mul_lt_mul_right multiplied_lt denominator_positive.le
  exact ⟨x_small, y_positive, y_small⟩

private theorem allBZSlope_ne_zero (x y : ℤ) : allBZSlope x y ≠ 0 := by
  have slope_factor : allBZSlope x y = 72 *
      (2 * (7254656640 * x * y + 84622548753 * x -
        1474847140057 * y + 252067656443) + 1) := by
    unfold allBZSlope
    ring
  rw [slope_factor]
  exact mul_ne_zero (by norm_num) (by omega)

private theorem allBZIntercept_abs_lt
    (x y : ℤ) (x_nonnegative : 0 ≤ x) (x_small : x ≤ 203)
    (y_nonnegative : 0 ≤ y) (y_small : y < 10000) :
    |allBZIntercept x y| < 1000000000000000000 := by
  have y_le : y ≤ 10000 := by omega
  have xy_nonnegative : 0 ≤ x * y := mul_nonneg x_nonnegative y_nonnegative
  have xy_le : x * y ≤ 203 * 10000 := by
    have first : x * y ≤ 203 * y :=
      mul_le_mul_of_nonneg_right x_small y_nonnegative
    have second : 203 * y ≤ 203 * 10000 :=
      mul_le_mul_of_nonneg_left y_le (by norm_num)
    exact first.trans second
  apply abs_lt.mpr
  constructor <;>
    unfold allBZIntercept <;>
    nlinarith

private theorem allBResultant_abs_lt
    (x y : ℤ) (x_nonnegative : 0 ≤ x) (x_small : x ≤ 203)
    (y_positive : 1 ≤ y) (y_small : y < 10000) :
    |allBZSlope x y * allBConstantIntercept x y -
        allBZIntercept x y * allBConstantSlope x y| <
      10000000000000000000000000000000 := by
  have y_nonnegative : 0 ≤ y := y_positive.trans' (by norm_num)
  have y_le : y ≤ 10000 := by omega
  have x_factor_bound : |48 * x - 3029| ≤ 7000 := by
    apply abs_le.mpr
    constructor <;> nlinarith
  have final_factor_bound :
      |674088 * x - 4333144 * y - 1095244575| ≤ 50000000000 := by
    apply abs_le.mpr
    constructor <;> nlinarith
  rw [allB_resultant_factor, abs_mul, abs_mul, abs_mul]
  norm_num only [abs_neg]
  rw [abs_of_nonneg y_nonnegative]
  calc
    1926044220672 * y * |48 * x - 3029| *
          |674088 * x - 4333144 * y - 1095244575| ≤
        1926044220672 * 10000 * 7000 * 50000000000 := by gcongr
    _ < 10000000000000000000000000000000 := by norm_num

private theorem allBResultant_ne_zero
    (x y : ℤ) (y_positive : 1 ≤ y) :
    allBZSlope x y * allBConstantIntercept x y -
        allBZIntercept x y * allBConstantSlope x y ≠ 0 := by
  rw [allB_resultant_factor]
  apply mul_ne_zero
  · apply mul_ne_zero
    · apply mul_ne_zero (by norm_num)
      omega
    · have odd_factor : 48 * x - 3029 = 2 * (24 * x - 1515) + 1 := by ring
      rw [odd_factor]
      omega
  · have odd_factor :
        674088 * x - 4333144 * y - 1095244575 =
          2 * (337044 * x - 2166572 * y - 547622288) + 1 := by ring
    rw [odd_factor]
    omega

private theorem allBLinearCore_ne_zero_of_large_scale
    (S x y z : ℤ) (scale_large : 243 ^ 14 ≤ S)
    (x_nonnegative : 0 ≤ x) (y_nonnegative : 0 ≤ y) (z_nonnegative : 0 ≤ z) :
    bZeroBDefectCOneAllBLinearCore S x y z ≠ 0 := by
  intro core_zero
  have coarse_scale : 59049 ≤ S := by norm_num at scale_large ⊢; omega
  rcases allBLinearCore_bounds S x y z coarse_scale x_nonnegative y_nonnegative
      z_nonnegative core_zero with ⟨x_small, y_positive, y_small⟩
  let a := allBZSlope x y
  let b := allBZIntercept x y
  let c := allBConstantSlope x y
  let d := allBConstantIntercept x y
  let L := S * a + b
  let Δ := a * d - b * c
  have a_ne : a ≠ 0 := allBZSlope_ne_zero x y
  have b_bound : |b| < 1000000000000000000 :=
    allBZIntercept_abs_lt x y x_nonnegative x_small y_nonnegative y_small
  have delta_bound : |Δ| < 10000000000000000000000000000000 :=
    allBResultant_abs_lt x y x_nonnegative x_small y_positive y_small
  have delta_ne : Δ ≠ 0 := allBResultant_ne_zero x y y_positive
  have core_collected : L * z + S * c + d = 0 := by
    rw [allBLinearCore_collect] at core_zero
    exact core_zero
  let m := a * z + c
  have delta_eq : Δ = -L * m := by
    dsimp [Δ, L, m]
    linear_combination a * core_collected
  have m_ne : m ≠ 0 := by
    intro m_zero
    rw [m_zero, mul_zero] at delta_eq
    exact delta_ne delta_eq
  have scale_nonnegative : 0 ≤ S := by positivity
  have scale_dominates :
      10000000000000000000000000000000 + 1000000000000000000 < S := by
    norm_num at scale_large ⊢
    omega
  have L_abs_large : 10000000000000000000000000000000 < |L| := by
    rcases abs_lt.mp b_bound with ⟨b_lower, b_upper⟩
    by_cases a_positive : 0 < a
    · have a_one : 1 ≤ a := by omega
      have scale_growth : S ≤ S * a := by
        nlinarith [mul_nonneg scale_nonnegative (sub_nonneg.mpr a_one)]
      have L_positive : 0 < L := by dsimp [L]; nlinarith
      rw [abs_of_pos L_positive]
      dsimp [L]
      nlinarith
    · have a_negative : a ≤ -1 := by omega
      have scale_decay : S * a ≤ -S := by
        nlinarith [mul_nonneg scale_nonnegative (show 0 ≤ -a - 1 by omega)]
      have L_negative : L < 0 := by dsimp [L]; nlinarith
      rw [abs_of_neg L_negative]
      dsimp [L]
      nlinarith
  have m_abs_one : 1 ≤ |m| := by
    have : 0 < |m| := abs_pos.mpr m_ne
    omega
  have L_abs_nonnegative : 0 ≤ |L| := abs_nonneg L
  have product_dominates : |L| ≤ |L| * |m| := by
    nlinarith [mul_nonneg L_abs_nonnegative (sub_nonneg.mpr m_abs_one)]
  have delta_abs_eq : |Δ| = |L| * |m| := by
    rw [delta_eq, abs_mul, abs_neg]
  rw [delta_abs_eq] at delta_bound
  omega

private def allBResidueSixteenQuotient (s x y z : ℤ) : ℤ :=
  1044670556160 * s * x * y * z + 97659986688 * s * x * y +
    12185647020432 * s * x * z + 1139230189116 * s * x -
    212377988168208 * s * y * z - 19848724882812 * s * y +
    36297742527864 * s * z + 3360322589607 * s +
    580372531200 * x * y * z + 54255548160 * x * y +
    6092823510216 * x * z + 569615094558 * x -
    118660215519128 * y * z - 11089908199618 * y +
    18148871263932 * z + 1680161294803

private theorem allBLinearCore_residue_sixteen (s x y z : ℤ) :
    bZeroBDefectCOneAllBLinearCore (16 * s + 9) x y z =
      16 * allBResidueSixteenQuotient s x y z + 8 := by
  unfold bZeroBDefectCOneAllBLinearCore allBResidueSixteenQuotient
  ring

private def allBResidueThirtyTwoQuotient (s x y z : ℤ) : ℤ :=
  1044670556160 * s * x * y * z + 97659986688 * s * x * y +
    12185647020432 * s * x * z + 1139230189116 * s * x -
    212377988168208 * s * y * z - 19848724882812 * s * y +
    36297742527864 * s * z + 3360322589607 * s +
    551353904640 * x * y * z + 51542770752 * x * y +
    6092823510216 * x * z + 569615094558 * x -
    112424604801616 * y * z - 10507135320512 * y +
    18148871263932 * z + 1680161294803

private theorem allBLinearCore_residue_thirty_two (s x y z : ℤ) :
    bZeroBDefectCOneAllBLinearCore (32 * s + 17) x y z =
      32 * allBResidueThirtyTwoQuotient s x y z + 16 := by
  unfold bZeroBDefectCOneAllBLinearCore allBResidueThirtyTwoQuotient
  ring

private def allBResidueSixtyFourQuotient (s x y z : ℤ) : ℤ :=
  1044670556160 * s * x * y * z + 97659986688 * s * x * y +
    12185647020432 * s * x * z + 1139230189116 * s * x -
    212377988168208 * s * y * z - 19848724882812 * s * y +
    36297742527864 * s * z + 3360322589607 * s +
    536844591360 * x * y * z + 50186382048 * x * y +
    6092823510216 * x * z + 569615094558 * x -
    109306799442860 * y * z - 10215748880959 * y +
    18148871263932 * z + 1680161294803

private theorem allBLinearCore_residue_sixty_four (s x y z : ℤ) :
    bZeroBDefectCOneAllBLinearCore (64 * s + 33) x y z =
      64 * allBResidueSixtyFourQuotient s x y z + 32 := by
  unfold bZeroBDefectCOneAllBLinearCore allBResidueSixtyFourQuotient
  ring

private theorem allBLinearCore_ne_zero_of_small_even_run
    (n x y z : Nat) (n_positive : 0 < n) (n_even : n % 2 = 0) (n_small : n < 14) :
    bZeroBDefectCOneAllBLinearCore ((3 : ℤ) ^ (5 * n)) x y z ≠ 0 := by
  intro core_zero
  have cases : n = 2 ∨ n = 4 ∨ n = 6 ∨ n = 8 ∨ n = 10 ∨ n = 12 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show (3 : ℤ) ^ (5 * 2) = 16 * 3690 + 9 by norm_num,
      allBLinearCore_residue_sixteen] at core_zero
    omega
  · rw [show (3 : ℤ) ^ (5 * 4) = 32 * 108962012 + 17 by norm_num,
      allBLinearCore_residue_thirty_two] at core_zero
    omega
  · rw [show (3 : ℤ) ^ (5 * 6) = 16 * 12868195755915 + 9 by norm_num,
      allBLinearCore_residue_sixteen] at core_zero
    omega
  · rw [show (3 : ℤ) ^ (5 * 8) = 64 * 189963522797764512 + 33 by norm_num,
      allBLinearCore_residue_sixty_four] at core_zero
    omega
  · rw [show (3 : ℤ) ^ (5 * 10) = 16 * 44868624230740786798140 + 9 by norm_num,
      allBLinearCore_residue_sixteen] at core_zero
    omega
  · rw [show (3 : ℤ) ^ (5 * 12) = 32 * 1324723696100506359821701037 + 17 by norm_num,
      allBLinearCore_residue_thirty_two] at core_zero
    omega

private theorem b_run_complement_coordinates (n : Nat) :
    242 * (((3 : ℤ) ^ (tagEncode 3 (List.replicate n .b)).length) -
        ternaryCode (tagEncode 3 (List.replicate n .b)) - 1) =
      39 * (((3 : ℤ) ^ (tagEncode 3 (List.replicate n .b)).length) - 1) := by
  have code_eq := tagEncode_b_run_code n
  have power_positive : 1 ≤ 3 ^ (tagEncode 3 (List.replicate n .b)).length :=
    one_le_pow₀ (by norm_num)
  have cast_code_eq := congrArg (fun value : Nat ↦ (value : ℤ)) code_eq
  norm_num only [Nat.cast_mul] at cast_code_eq
  rw [Nat.cast_sub power_positive] at cast_code_eq
  push_cast at cast_code_eq
  nlinarith

private theorem bZeroBDefectCOneCodeCore_ne_zero_of_even_b_run
    (n x y z : Nat) (n_positive : 0 < n) (n_even : n % 2 = 0) :
    bZeroBDefectCOneCodeCore
        ((3 : ℤ) ^ (tagEncode 3 (List.replicate n .b)).length)
        (ternaryCode (tagEncode 3 (List.replicate n .b))) x y z ≠ 0 := by
  have length_eq := tagEncode_b_run_length n
  have coordinates := b_run_complement_coordinates n
  rw [length_eq] at coordinates ⊢
  have linear_ne :
      bZeroBDefectCOneAllBLinearCore ((3 : ℤ) ^ (5 * n)) x y z ≠ 0 := by
    by_cases n_small : n < 14
    · exact allBLinearCore_ne_zero_of_small_even_run n x y z n_positive n_even n_small
    · have exponent_le : 5 * 14 ≤ 5 * n := by omega
      have scale_large_nat : 3 ^ (5 * 14) ≤ 3 ^ (5 * n) :=
        Nat.pow_le_pow_right (by norm_num) exponent_le
      have scale_large : (243 : ℤ) ^ 14 ≤ (3 : ℤ) ^ (5 * n) := by
        exact_mod_cast scale_large_nat
      exact allBLinearCore_ne_zero_of_large_scale ((3 : ℤ) ^ (5 * n)) x y z
        scale_large (by positivity) (by positivity) (by positivity)
  intro core_zero
  have scaled_eq := bZeroBDefectCOneAllBLinearCore_eq
    ((3 : ℤ) ^ (5 * n)) (ternaryCode (tagEncode 3 (List.replicate n .b))) x y z
      coordinates
  rw [core_zero, mul_zero] at scaled_eq
  exact linear_ne scaled_eq.symm

private theorem bridge_bZero_bTwo_cOne_det_ne_zero_of_integer_core
    (body : List TagLetter) (x y z : Nat)
    (core_ne :
      bZeroBDefectCOneCodeCore
        ((3 : ℤ) ^ (tagEncode 3 body).length)
        (ternaryCode (tagEncode 3 body)) x y z ≠ 0) :
    (bridge 27
      (bAtom 27 (3 * z) * bAtom 27 (3 * x + 2) *
        cAtom 27 (nearySideLowerC 3 body)
          (nearySideLowerCScale 3 body) (3 * y + 1))).det ≠ 0 := by
  rw [bridge_bZero_bTwo_cOne_det]
  refine mul_ne_zero (by norm_num) ?_
  have power_cast :
      ((((3 : ℤ) ^ (tagEncode 3 body).length : ℤ) : ℚ)) =
        (3 : ℚ) ^ (tagEncode 3 body).length := by norm_num
  rw [← power_cast]
  intro core_zero
  have cast_integer_core :
      ((bZeroBDefectCOneCodeCore
        ((3 ^ (tagEncode 3 body).length : Nat) : ℤ)
        (ternaryCode (tagEncode 3 body)) x y z : ℤ) : ℚ) =
        bZeroBDefectCOneCodeCore
          ((3 ^ (tagEncode 3 body).length : Nat) : ℚ)
          (ternaryCode (tagEncode 3 body)) x y z := by
    norm_num [bZeroBDefectCOneCodeCore]
  have cast_zero :
      ((bZeroBDefectCOneCodeCore
        ((3 ^ (tagEncode 3 body).length : Nat) : ℤ)
        (ternaryCode (tagEncode 3 body)) x y z : ℤ) : ℚ) = 0 :=
    cast_integer_core.trans core_zero
  have integer_zero :
      bZeroBDefectCOneCodeCore
        ((3 ^ (tagEncode 3 body).length : Nat) : ℤ)
        (ternaryCode (tagEncode 3 body)) x y z = 0 := by
    exact_mod_cast cast_zero
  exact core_ne integer_zero

/-- No nonempty all-`b` body closes the shortest `0 | 2 | 1` bridge with letters
`b | b | c`, independently of all waits. -/
theorem bridge_bZero_bTwo_cOne_det_ne_zero_of_b_run
    (n : Nat) (n_positive : 0 < n) (x y z : Nat) :
    (bridge 27
      (bAtom 27 (3 * z) * bAtom 27 (3 * x + 2) *
        cAtom 27 (nearySideLowerC 3 (List.replicate n .b))
          (nearySideLowerCScale 3 (List.replicate n .b)) (3 * y + 1))).det ≠ 0 := by
  by_cases n_odd : n % 2 = 1
  · apply bridge_bZero_bTwo_cOne_det_ne_zero_of_odd_body
    simpa using n_odd
  · have n_even : n % 2 = 0 := by omega
    exact bridge_bZero_bTwo_cOne_det_ne_zero_of_integer_core
      (List.replicate n .b) x y z
        (bZeroBDefectCOneCodeCore_ne_zero_of_even_b_run
          n x y z n_positive n_even)

/-- One exact modulo-sixteen blade excludes every body whose length and complement code occupy
opposite even residue classes. -/
theorem bridge_bZero_bTwo_cOne_det_ne_zero_of_complement_residue
    (body : List TagLetter) (x y z : Nat)
    (residue :
      (body.length % 4 = 0 ∧ tagComplementCode body % 4 = 2) ∨
        (body.length % 4 = 2 ∧ tagComplementCode body % 4 = 0)) :
    (bridge 27
      (bAtom 27 (3 * z) * bAtom 27 (3 * x + 2) *
        cAtom 27 (nearySideLowerC 3 body)
          (nearySideLowerCScale 3 body) (3 * y + 1))).det ≠ 0 :=
  bridge_bZero_bTwo_cOne_det_ne_zero_of_integer_core body x y z
    (bZeroBDefectCOneCodeCore_ne_zero_of_complement_residue body x y z residue)

/-- A positive complement thinner than `1 / 2160000` of the code scale cannot close the
shortest `0 | 2 | 1` bridge with letters `b | b | c`. -/
theorem bridge_bZero_bTwo_cOne_det_ne_zero_of_thin_complement
    (body : List TagLetter)
    (complement_positive : 0 < tagComplementCode body)
    (thin : 2160000 * tagComplementCode body <
      3 ^ (tagEncode 3 body).length)
    (x y z : Nat) :
    (bridge 27
      (bAtom 27 (3 * z) * bAtom 27 (3 * x + 2) *
        cAtom 27 (nearySideLowerC 3 body)
          (nearySideLowerCScale 3 body) (3 * y + 1))).det ≠ 0 := by
  let S : Nat := 3 ^ (tagEncode 3 body).length
  let C : Nat := ternaryCode (tagEncode 3 body)
  let D : Nat := tagComplementCode body
  have thin_closed : 2160000 * D ≤ S - 1 := by
    dsimp [S, D]
    omega
  have complement_positive_rat : (0 : ℚ) < D := by
    exact_mod_cast complement_positive
  have scale_positive : 1 ≤ S := by
    dsimp [S]
    exact one_le_pow₀ (by norm_num)
  have thin_rat_aux : (2160000 : ℚ) * D ≤ ((S - 1 : Nat) : ℚ) := by
    exact_mod_cast thin_closed
  have scale_sub_cast : ((S - 1 : Nat) : ℚ) = (S : ℚ) - 1 := by
    rw [Nat.cast_sub scale_positive]
    norm_num
  have thin_rat : (2160000 : ℚ) * D ≤ S - 1 := by
    rw [← scale_sub_cast]
    exact thin_rat_aux
  have code_eq : (C : ℚ) = (S : ℚ) - 1 - D := by
    have complement_eq_int : (D : ℤ) = (S : ℤ) - C - 1 := by
      simpa [S, C, D] using tagComplementCode_cast body
    have complement_eq := congrArg (fun value : ℤ ↦ (value : ℚ)) complement_eq_int
    push_cast at complement_eq
    linarith
  have rational_core_ne :
      bZeroBDefectCOneCodeCore (S : ℚ) (C : ℚ) x y z ≠ 0 := by
    rw [code_eq]
    exact bZeroBDefectCOneCodeCore_ne_zero_of_thin_complement
      S D complement_positive_rat thin_rat x y z
  apply bridge_bZero_bTwo_cOne_det_ne_zero_of_integer_core body x y z
  intro integer_core_zero
  apply rational_core_ne
  have cast_integer_core :
      ((bZeroBDefectCOneCodeCore (S : ℤ) (C : ℤ) x y z : ℤ) : ℚ) =
        bZeroBDefectCOneCodeCore (S : ℚ) (C : ℚ) x y z := by
    norm_num [bZeroBDefectCOneCodeCore]
  rw [← cast_integer_core]
  exact_mod_cast integer_core_zero
end MatrixMortality.ParabolicBlade
