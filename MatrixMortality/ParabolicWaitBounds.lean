import MatrixMortality.ParabolicEvenBody

/-!
# Wait bounds for the phase-zero right-c bridge

The first-`b` complement cylinders bound the middle wait in every zero of the residual
`b | b | c` core.
-/

namespace MatrixMortality.ParabolicBlade

private theorem tagEncode_replicate_c_length (j : Nat) :
    (tagEncode 3 (List.replicate j .c)).length = j := by
  induction j with
  | zero => rfl
  | succ j induction =>
      rw [List.replicate_succ, tagEncode_cons, List.length_append]
      simp [tagCode, induction]
      omega

private theorem tagComplementCode_cast_rat (body : List TagLetter) :
    (tagComplementCode body : ℚ) =
      (3 : ℚ) ^ (tagEncode 3 body).length -
        ternaryCode (tagEncode 3 body) - 1 := by
  have code_lt := ternaryCode_lt_pow_length (tagEncode 3 body)
  have code_le : ternaryCode (tagEncode 3 body) ≤
      3 ^ (tagEncode 3 body).length := code_lt.le
  have difference_positive :
      1 ≤ 3 ^ (tagEncode 3 body).length - ternaryCode (tagEncode 3 body) := by
    omega
  unfold tagComplementCode
  rw [Nat.cast_sub difference_positive, Nat.cast_sub code_le]
  push_cast
  rfl

/-- The first-`b` cylinder retains the constant gap lost by its open density bound. -/
theorem tagComplementCode_first_b_sharp_upper (j : Nat) (tail : List TagLetter) :
    let body := List.replicate j .c ++ .b :: tail
    let S := 3 ^ (tagEncode 3 body).length
    let D := tagComplementCode body
    242 * 3 ^ j * D ≤ 39 * (S - 1) := by
  let R : Nat := 3 ^ (tagEncode 3 tail).length
  let E : Nat := tagComplementCode tail
  have scale_positive : 1 ≤ R := by
    dsimp [R]
    exact one_le_pow₀ (by norm_num)
  have complement_bound : 242 * E ≤ 39 * (R - 1) := by
    dsimp [R, E]
    exact tagComplementCode_global_bound tail
  have complement_eq :
      tagComplementCode (List.replicate j .c ++ .b :: tail) = 39 * R + E := by
    rw [tagComplementCode_replicate_c_append, tagComplementCode_cons_b]
  have encoded_length :
      (tagEncode 3 (List.replicate j .c ++ .b :: tail)).length =
        j + 5 + (tagEncode 3 tail).length := by
    rw [tagEncode_append, tagEncode_cons]
    simp [tagCode, tagEncode_replicate_c_length]
    omega
  have scale_eq :
      3 ^ (tagEncode 3 (List.replicate j .c ++ .b :: tail)).length =
        3 ^ j * 243 * R := by
    rw [encoded_length, pow_add, pow_add]
    norm_num only [Nat.reducePow]
    rfl
  have upper_base : 242 * (39 * R + E) ≤ 39 * (243 * R - 1) := by
    omega
  have upper_scaled := Nat.mul_le_mul_left (3 ^ j) upper_base
  have power_positive : 1 ≤ 3 ^ j := one_le_pow₀ (by norm_num)
  have scale_gap : 3 ^ j * (243 * R - 1) ≤ 3 ^ j * 243 * R - 1 := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    simpa only [mul_assoc] using
      Nat.sub_le_sub_left power_positive (3 ^ j * 243 * R)
  dsimp only
  rw [complement_eq, scale_eq]
  calc
    242 * 3 ^ j * (39 * R + E) = 3 ^ j * (242 * (39 * R + E)) := by ring
    _ ≤ 3 ^ j * (39 * (243 * R - 1)) := upper_scaled
    _ = 39 * (3 ^ j * (243 * R - 1)) := by ring
    _ ≤ 39 * (3 ^ j * 243 * R - 1) := Nat.mul_le_mul_left 39 scale_gap

private def bZeroBDefectCOneXSlope (S D y z : ℚ) : ℚ :=
  bZeroBDefectCOneWaitFactor S y * (119911680 * z + 11209824) +
    D * (631601581536 * z + 59048086536)

private def bZeroBDefectCOneYSlope (S D x z : ℚ) : ℚ :=
  (72 * S - 8) * bZeroBDefectCOneRootPencil x z +
    D * (620717828832 * z + 58005064872)

private theorem bZeroBDefectCOneCodeCore_sub_x
    (S D x₁ x₂ y z : ℚ) :
    bZeroBDefectCOneCodeCore S (S - 1 - D) x₂ y z -
        bZeroBDefectCOneCodeCore S (S - 1 - D) x₁ y z =
      bZeroBDefectCOneXSlope S D y z * (x₂ - x₁) := by
  rw [bZeroBDefectCOneCodeCore_thin_decomposition,
    bZeroBDefectCOneCodeCore_thin_decomposition]
  unfold bZeroBDefectCOneXSlope bZeroBDefectCOneRootPencil
    bZeroBDefectCOneComplementCore
  ring

private theorem bZeroBDefectCOneCodeCore_sub_y
    (S D x y₁ y₂ z : ℚ) :
    bZeroBDefectCOneCodeCore S (S - 1 - D) x y₂ z -
        bZeroBDefectCOneCodeCore S (S - 1 - D) x y₁ z =
      bZeroBDefectCOneYSlope S D x z * (y₂ - y₁) := by
  rw [bZeroBDefectCOneCodeCore_thin_decomposition,
    bZeroBDefectCOneCodeCore_thin_decomposition]
  unfold bZeroBDefectCOneYSlope bZeroBDefectCOneWaitFactor
    bZeroBDefectCOneComplementCore
  ring

private theorem bZeroBDefectCOneWaitFactor_pos
    (S y : ℚ) (scale_large : 1 < S) (wait_positive : 1 ≤ y) :
    0 < bZeroBDefectCOneWaitFactor S y := by
  have scale_gap : 0 < S - 1 := by linarith
  have wait_gap : 0 < 72 * y - 9 := by linarith
  have product_positive : 0 < (S - 1) * (72 * y - 9) :=
    mul_pos scale_gap wait_gap
  unfold bZeroBDefectCOneWaitFactor
  nlinarith

private theorem bZeroBDefectCOneXSlope_pos
    (S D y z : ℚ) (scale_large : 1 < S) (complement_positive : 0 < D)
    (wait_positive : 1 ≤ y) (z_nonnegative : 0 ≤ z) :
    0 < bZeroBDefectCOneXSlope S D y z := by
  have wait_factor_positive :=
    bZeroBDefectCOneWaitFactor_pos S y scale_large wait_positive
  unfold bZeroBDefectCOneXSlope
  positivity

private theorem bZeroBDefectCOne_y_lt_of_first_b_zero
    (S D : ℚ) (scale_large : 1 < S) (complement_positive : 0 < D)
    (density_lower : 13 * S ≤ 81 * D)
    (density_upper : 242 * D ≤ 39 * (S - 1))
    (x y z : Nat)
    (core_zero : bZeroBDefectCOneCodeCore S (S - 1 - D) x y z = 0) :
    y < 51768 := by
  by_contra wait_not_bounded
  have wait_large_nat : 51768 ≤ y := by omega
  have wait_positive : (1 : ℚ) ≤ y := by exact_mod_cast (show 1 ≤ y by omega)
  have z_nonnegative : (0 : ℚ) ≤ z := by positivity
  have scale_positive : (0 : ℚ) < S := by linarith
  have x_slope_positive :
      0 < bZeroBDefectCOneXSlope S D y z :=
    bZeroBDefectCOneXSlope_pos S D y z scale_large complement_positive
      wait_positive z_nonnegative
  have pencil_204_negative :
      bZeroBDefectCOneRootPencil (204 : ℚ) z < 0 := by
    rw [show bZeroBDefectCOneRootPencil (204 : ℚ) z =
      -(1305003716 * z + 121348297) by
        unfold bZeroBDefectCOneRootPencil
        ring]
    nlinarith
  have complement_204_zero_positive :
      0 < bZeroBDefectCOneComplementCore (204 : ℚ) 0 z := by
    unfold bZeroBDefectCOneComplementCore
    positivity
  have core_204_zero_positive :
      0 < bZeroBDefectCOneCodeCore S (S - 1 - D) 204 0 z := by
    rw [bZeroBDefectCOneCodeCore_thin_decomposition]
    have wait_zero : bZeroBDefectCOneWaitFactor S 0 = -9 * (S - 1) := by
      unfold bZeroBDefectCOneWaitFactor
      ring
    rw [wait_zero]
    have first_positive :
        0 < (-9 * (S - 1)) * bZeroBDefectCOneRootPencil (204 : ℚ) z :=
      mul_pos_of_neg_of_neg (by nlinarith) pencil_204_negative
    have second_positive :
        0 < D * bZeroBDefectCOneComplementCore (204 : ℚ) 0 z :=
      mul_pos complement_positive complement_204_zero_positive
    linarith
  let T : ℚ := 81 * D - 13 * S
  have T_nonnegative : 0 ≤ T := by
    dsimp [T]
    linarith
  have y_slope_204_identity :
      81 * bZeroBDefectCOneYSlope S D 204 z =
        S * (458550103104 * z + 46362575232) +
          T * (620717828832 * z + 58005064872) +
          (845642407968 * z + 78633696456) := by
    dsimp [T]
    unfold bZeroBDefectCOneYSlope bZeroBDefectCOneRootPencil
    ring
  have y_slope_204_positive :
      0 < bZeroBDefectCOneYSlope S D 204 z := by
    have scale_term_positive :
        0 < S * (458550103104 * z + 46362575232) := by positivity
    have complement_term_nonnegative :
        0 ≤ T * (620717828832 * z + 58005064872) := by positivity
    have residual_positive :
        0 < (845642407968 : ℚ) * z + 78633696456 := by positivity
    nlinarith [y_slope_204_identity]
  have core_204_positive :
      0 < bZeroBDefectCOneCodeCore S (S - 1 - D) 204 y z := by
    have y_difference := bZeroBDefectCOneCodeCore_sub_y S D 204 0 y z
    have wait_nonnegative : (0 : ℚ) ≤ y := by positivity
    nlinarith
  have x_lt_204 : x < 204 := by
    by_contra x_not_small
    have x_large_nat : 204 ≤ x := by omega
    have x_large : (204 : ℚ) ≤ x := by exact_mod_cast x_large_nat
    have x_difference := bZeroBDefectCOneCodeCore_sub_x S D 204 x y z
    nlinarith
  have x_le_203 : x ≤ 203 := by omega
  let U : ℚ := 39 * (S - 1) - 242 * D
  have U_nonnegative : 0 ≤ U := by
    dsimp [U]
    linarith
  have y_slope_203_identity :
      242 * bZeroBDefectCOneYSlope S D 203 z =
        -S * (619730535456 * z + 47495170296) -
          (21449359117792 * z + 2005565007752) -
          U * (620717828832 * z + 58005064872) := by
    dsimp [U]
    unfold bZeroBDefectCOneYSlope bZeroBDefectCOneRootPencil
    ring
  have y_slope_203_negative :
      bZeroBDefectCOneYSlope S D 203 z < 0 := by
    have scale_term_positive :
        0 < S * (619730535456 * z + 47495170296) := by positivity
    have residual_positive :
        0 < (21449359117792 : ℚ) * z + 2005565007752 := by positivity
    have complement_term_nonnegative :
        0 ≤ U * (620717828832 * z + 58005064872) := by positivity
    nlinarith [y_slope_203_identity]
  have core_203_endpoint_identity :
      242 * bZeroBDefectCOneCodeCore S (S - 1 - D) 203 51768 z =
        -S * (27062242184135088 * z + 1989481873923018) -
          (1115410390985207376 * z + 104293337423265846) -
          U * bZeroBDefectCOneComplementCore (203 : ℚ) (51768 : ℚ) z := by
    rw [bZeroBDefectCOneCodeCore_thin_decomposition]
    dsimp [U]
    unfold bZeroBDefectCOneWaitFactor bZeroBDefectCOneRootPencil
      bZeroBDefectCOneComplementCore
    ring
  have core_203_endpoint_negative :
      bZeroBDefectCOneCodeCore S (S - 1 - D) 203 51768 z < 0 := by
    have scale_term_positive :
        0 < S * (27062242184135088 * z + 1989481873923018) := by positivity
    have residual_positive :
        0 < (1115410390985207376 : ℚ) * z + 104293337423265846 := by positivity
    have complement_core_nonnegative :
        0 ≤ U * bZeroBDefectCOneComplementCore (203 : ℚ) 51768 z := by
      have core_positive :
          0 < bZeroBDefectCOneComplementCore (203 : ℚ) 51768 z := by
        unfold bZeroBDefectCOneComplementCore
        positivity
      positivity
    nlinarith [core_203_endpoint_identity]
  have core_203_negative :
      bZeroBDefectCOneCodeCore S (S - 1 - D) 203 y z < 0 := by
    have wait_large : (51768 : ℚ) ≤ y := by exact_mod_cast wait_large_nat
    have y_difference := bZeroBDefectCOneCodeCore_sub_y S D 203 51768 y z
    nlinarith
  have x_small : (x : ℚ) ≤ 203 := by exact_mod_cast x_le_203
  have x_difference := bZeroBDefectCOneCodeCore_sub_x S D x 203 y z
  nlinarith

private theorem bZeroBDefectCOne_no_zero_of_endpoint_negative
    (S D : ℚ) (x y z endpoint waitFloor : Nat)
    (core_zero : bZeroBDefectCOneCodeCore S (S - 1 - D) x y z = 0)
    (x_slope_positive : 0 < bZeroBDefectCOneXSlope S D y z)
    (x_bound : x ≤ endpoint) (wait_bound : waitFloor ≤ y)
    (y_slope_negative : bZeroBDefectCOneYSlope S D endpoint z < 0)
    (endpoint_negative :
      bZeroBDefectCOneCodeCore S (S - 1 - D) endpoint waitFloor z < 0) :
    False := by
  have wait_bound_rat : (waitFloor : ℚ) ≤ y := by exact_mod_cast wait_bound
  have endpoint_at_wait_negative :
      bZeroBDefectCOneCodeCore S (S - 1 - D) endpoint y z < 0 := by
    have y_difference :=
      bZeroBDefectCOneCodeCore_sub_y S D endpoint waitFloor y z
    nlinarith
  have x_bound_rat : (x : ℚ) ≤ endpoint := by exact_mod_cast x_bound
  have x_difference :=
    bZeroBDefectCOneCodeCore_sub_x S D x endpoint y z
  nlinarith

private theorem bZeroBDefectCOne_y_lt_of_first_b_one
    (S D : ℚ) (scale_large : 1 < S) (complement_positive : 0 < D)
    (density_lower : 13 * S ≤ 243 * D)
    (density_upper : 726 * D ≤ 39 * (S - 1))
    (x y z : Nat)
    (core_zero : bZeroBDefectCOneCodeCore S (S - 1 - D) x y z = 0) :
    y < 51768 := by
  by_contra wait_not_bounded
  have wait_large_nat : 51768 ≤ y := by omega
  have wait_positive : (1 : ℚ) ≤ y := by exact_mod_cast (show 1 ≤ y by omega)
  have z_nonnegative : (0 : ℚ) ≤ z := by positivity
  have scale_positive : (0 : ℚ) < S := by linarith
  have x_slope_positive :
      0 < bZeroBDefectCOneXSlope S D y z :=
    bZeroBDefectCOneXSlope_pos S D y z scale_large complement_positive
      wait_positive z_nonnegative
  have pencil_212_negative :
      bZeroBDefectCOneRootPencil (212 : ℚ) z < 0 := by
    rw [show bZeroBDefectCOneRootPencil (212 : ℚ) z =
      -(345710276 * z + 31669705) by
        unfold bZeroBDefectCOneRootPencil
        ring]
    nlinarith
  have complement_212_zero_positive :
      0 < bZeroBDefectCOneComplementCore (212 : ℚ) 0 z := by
    unfold bZeroBDefectCOneComplementCore
    positivity
  have core_212_zero_positive :
      0 < bZeroBDefectCOneCodeCore S (S - 1 - D) 212 0 z := by
    rw [bZeroBDefectCOneCodeCore_thin_decomposition]
    have wait_zero : bZeroBDefectCOneWaitFactor S 0 = -9 * (S - 1) := by
      unfold bZeroBDefectCOneWaitFactor
      ring
    rw [wait_zero]
    have first_positive :
        0 < (-9 * (S - 1)) * bZeroBDefectCOneRootPencil (212 : ℚ) z :=
      mul_pos_of_neg_of_neg (by nlinarith) pencil_212_negative
    have second_positive :
        0 < D * bZeroBDefectCOneComplementCore (212 : ℚ) 0 z :=
      mul_pos complement_positive complement_212_zero_positive
    linarith
  let T : ℚ := 243 * D - 13 * S
  have T_nonnegative : 0 ≤ T := by
    dsimp [T]
    linarith
  have y_slope_212_identity :
      243 * bZeroBDefectCOneYSlope S D 212 z =
        S * (2020784785920 * z + 199972684656) +
          T * (620717828832 * z + 58005064872) +
          (672060776544 * z + 61565906520) := by
    dsimp [T]
    unfold bZeroBDefectCOneYSlope bZeroBDefectCOneRootPencil
    ring
  have y_slope_212_positive :
      0 < bZeroBDefectCOneYSlope S D 212 z := by
    have scale_term_positive :
        0 < S * (2020784785920 * z + 199972684656) := by positivity
    have complement_term_nonnegative :
        0 ≤ T * (620717828832 * z + 58005064872) := by positivity
    have residual_positive :
        0 < (672060776544 : ℚ) * z + 61565906520 := by positivity
    nlinarith [y_slope_212_identity]
  have core_212_positive :
      0 < bZeroBDefectCOneCodeCore S (S - 1 - D) 212 y z := by
    have y_difference := bZeroBDefectCOneCodeCore_sub_y S D 212 0 y z
    have wait_nonnegative : (0 : ℚ) ≤ y := by positivity
    nlinarith
  have x_lt_212 : x < 212 := by
    by_contra x_not_small
    have x_large_nat : 212 ≤ x := by omega
    have x_large : (212 : ℚ) ≤ x := by exact_mod_cast x_large_nat
    have x_difference := bZeroBDefectCOneCodeCore_sub_x S D 212 x y z
    nlinarith
  have x_le_211 : x ≤ 211 := by omega
  let U : ℚ := 39 * (S - 1) - 726 * D
  have U_nonnegative : 0 ≤ U := by
    dsimp [U]
    linarith
  by_cases z_zero : z = 0
  · subst z
    have pencil_211_zero_negative :
        bZeroBDefectCOneRootPencil (211 : ℚ) 0 < 0 := by
      norm_num [bZeroBDefectCOneRootPencil]
    have complement_211_zero_positive :
        0 < bZeroBDefectCOneComplementCore (211 : ℚ) 0 0 := by
      norm_num [bZeroBDefectCOneComplementCore]
    have core_211_zero_positive :
        0 < bZeroBDefectCOneCodeCore S (S - 1 - D) 211 0 0 := by
      rw [bZeroBDefectCOneCodeCore_thin_decomposition]
      have wait_zero : bZeroBDefectCOneWaitFactor S 0 = -9 * (S - 1) := by
        unfold bZeroBDefectCOneWaitFactor
        ring
      rw [wait_zero]
      have first_positive :
          0 < (-9 * (S - 1)) * bZeroBDefectCOneRootPencil (211 : ℚ) 0 :=
        mul_pos_of_neg_of_neg (by nlinarith) pencil_211_zero_negative
      have second_positive :
          0 < D * bZeroBDefectCOneComplementCore (211 : ℚ) 0 0 :=
        mul_pos complement_positive complement_211_zero_positive
      linarith
    have y_slope_211_identity :
        243 * bZeroBDefectCOneYSlope S D 211 0 =
          S * 3845603952 + T * 58005064872 + 83357804376 := by
      dsimp [T]
      unfold bZeroBDefectCOneYSlope bZeroBDefectCOneRootPencil
      ring
    have y_slope_211_positive :
        0 < bZeroBDefectCOneYSlope S D 211 0 := by
      have scale_term_positive : 0 < S * 3845603952 := by positivity
      have complement_term_nonnegative : 0 ≤ T * 58005064872 := by positivity
      nlinarith [y_slope_211_identity]
    have core_211_positive :
        0 < bZeroBDefectCOneCodeCore S (S - 1 - D) 211 y 0 := by
      have y_difference := bZeroBDefectCOneCodeCore_sub_y S D 211 0 y 0
      have wait_nonnegative : (0 : ℚ) ≤ y := by positivity
      nlinarith
    have x_ne_211 : x ≠ 211 := by
      intro x_eq
      subst x
      norm_num at core_zero
      exact (ne_of_gt core_211_positive) core_zero
    have x_le_210 : x ≤ 210 := by omega
    have y_slope_210_identity :
        726 * bZeroBDefectCOneYSlope S D 210 0 =
          -S * 565161130008 - 1948046567784 - U * 58005064872 := by
      dsimp [U]
      unfold bZeroBDefectCOneYSlope bZeroBDefectCOneRootPencil
      ring
    have y_slope_210_negative :
        bZeroBDefectCOneYSlope S D 210 0 < 0 := by
      have scale_term_positive : 0 < S * 565161130008 := by positivity
      have complement_term_nonnegative : 0 ≤ U * 58005064872 := by positivity
      nlinarith [y_slope_210_identity]
    have core_210_endpoint_identity :
        726 * bZeroBDefectCOneCodeCore S (S - 1 - D) 210 51768 0 =
          -S * 28771828440424542 - 101331907658871714 -
            U * bZeroBDefectCOneComplementCore (210 : ℚ) 51768 0 := by
      rw [bZeroBDefectCOneCodeCore_thin_decomposition]
      dsimp [U]
      unfold bZeroBDefectCOneWaitFactor bZeroBDefectCOneRootPencil
        bZeroBDefectCOneComplementCore
      ring
    have core_210_endpoint_negative :
        bZeroBDefectCOneCodeCore S (S - 1 - D) 210 51768 0 < 0 := by
      have scale_term_positive : 0 < S * 28771828440424542 := by positivity
      have complement_term_nonnegative :
          0 ≤ U * bZeroBDefectCOneComplementCore (210 : ℚ) 51768 0 := by
        have core_positive :
            0 < bZeroBDefectCOneComplementCore (210 : ℚ) 51768 0 := by
          norm_num [bZeroBDefectCOneComplementCore]
        positivity
      nlinarith [core_210_endpoint_identity]
    exact bZeroBDefectCOne_no_zero_of_endpoint_negative S D x y 0 210 51768
      core_zero x_slope_positive x_le_210 wait_large_nat y_slope_210_negative
      core_210_endpoint_negative
  · have z_positive_nat : 1 ≤ z := by omega
    have z_positive : (1 : ℚ) ≤ z := by exact_mod_cast z_positive_nat
    have y_slope_211_identity :
        726 * bZeroBDefectCOneYSlope S D 211 z =
          S * (-130995559584 * z + 20798790120) -
            (21503663004000 * z + 2013153225576) -
            U * (620717828832 * z + 58005064872) := by
      dsimp [U]
      unfold bZeroBDefectCOneYSlope bZeroBDefectCOneRootPencil
      ring
    have y_slope_211_negative :
        bZeroBDefectCOneYSlope S D 211 z < 0 := by
      have scale_factor_negative :
          (-130995559584 : ℚ) * z + 20798790120 < 0 := by nlinarith
      have scale_term_negative :
          S * (-130995559584 * z + 20798790120) < 0 :=
        mul_neg_of_pos_of_neg scale_positive scale_factor_negative
      have residual_positive :
          0 < (21503663004000 : ℚ) * z + 2013153225576 := by positivity
      have complement_term_nonnegative :
          0 ≤ U * (620717828832 * z + 58005064872) := by positivity
      nlinarith [y_slope_211_identity]
    have core_211_endpoint_identity :
        726 * bZeroBDefectCOneCodeCore S (S - 1 - D) 211 51768 z =
          S * (-1564411351626144 * z + 1564374335146650) -
            (1118418593167990368 * z + 104704578749832858) -
            U * bZeroBDefectCOneComplementCore (211 : ℚ) 51768 z := by
      rw [bZeroBDefectCOneCodeCore_thin_decomposition]
      dsimp [U]
      unfold bZeroBDefectCOneWaitFactor bZeroBDefectCOneRootPencil
        bZeroBDefectCOneComplementCore
      ring
    have core_211_endpoint_negative :
        bZeroBDefectCOneCodeCore S (S - 1 - D) 211 51768 z < 0 := by
      have scale_factor_negative :
          (-1564411351626144 : ℚ) * z + 1564374335146650 < 0 := by nlinarith
      have scale_term_negative :
          S * (-1564411351626144 * z + 1564374335146650) < 0 :=
        mul_neg_of_pos_of_neg scale_positive scale_factor_negative
      have residual_positive :
          0 < (1118418593167990368 : ℚ) * z + 104704578749832858 := by positivity
      have complement_term_nonnegative :
          0 ≤ U * bZeroBDefectCOneComplementCore (211 : ℚ) 51768 z := by
        have core_positive :
            0 < bZeroBDefectCOneComplementCore (211 : ℚ) 51768 z := by
          unfold bZeroBDefectCOneComplementCore
          positivity
        positivity
      nlinarith [core_211_endpoint_identity]
    exact bZeroBDefectCOne_no_zero_of_endpoint_negative S D x y z 211 51768
      core_zero x_slope_positive x_le_211 wait_large_nat y_slope_211_negative
      core_211_endpoint_negative

private theorem bZeroBDefectCOne_y_lt_of_first_b_two
    (S D : ℚ) (scale_large : 1 < S) (complement_positive : 0 < D)
    (density_lower : 13 * S ≤ 729 * D)
    (density_upper : 2178 * D ≤ 39 * (S - 1))
    (x y z : Nat)
    (core_zero : bZeroBDefectCOneCodeCore S (S - 1 - D) x y z = 0) :
    y < 51768 := by
  by_contra wait_not_bounded
  have wait_large_nat : 51768 ≤ y := by omega
  have wait_positive : (1 : ℚ) ≤ y := by exact_mod_cast (show 1 ≤ y by omega)
  have z_nonnegative : (0 : ℚ) ≤ z := by positivity
  have scale_positive : (0 : ℚ) < S := by linarith
  have x_slope_positive :
      0 < bZeroBDefectCOneXSlope S D y z :=
    bZeroBDefectCOneXSlope_pos S D y z scale_large complement_positive
      wait_positive z_nonnegative
  have pencil_214_negative :
      bZeroBDefectCOneRootPencil (214 : ℚ) z < 0 := by
    rw [show bZeroBDefectCOneRootPencil (214 : ℚ) z =
      -(105886916 * z + 9250057) by
        unfold bZeroBDefectCOneRootPencil
        ring]
    nlinarith
  have complement_214_zero_positive :
      0 < bZeroBDefectCOneComplementCore (214 : ℚ) 0 z := by
    unfold bZeroBDefectCOneComplementCore
    positivity
  have core_214_zero_positive :
      0 < bZeroBDefectCOneCodeCore S (S - 1 - D) 214 0 z := by
    rw [bZeroBDefectCOneCodeCore_thin_decomposition]
    have wait_zero : bZeroBDefectCOneWaitFactor S 0 = -9 * (S - 1) := by
      unfold bZeroBDefectCOneWaitFactor
      ring
    rw [wait_zero]
    have first_positive :
        0 < (-9 * (S - 1)) * bZeroBDefectCOneRootPencil (214 : ℚ) z :=
      mul_pos_of_neg_of_neg (by nlinarith) pencil_214_negative
    have second_positive :
        0 < D * bZeroBDefectCOneComplementCore (214 : ℚ) 0 z :=
      mul_pos complement_positive complement_214_zero_positive
    linarith
  let T : ℚ := 729 * D - 13 * S
  have T_nonnegative : 0 ≤ T := by
    dsimp [T]
    linarith
  have y_slope_214_identity :
      729 * bZeroBDefectCOneYSlope S D 214 z =
        S * (2511539327808 * z + 268548851520) +
          T * (620717828832 * z + 58005064872) +
          (617532494112 * z + 53946332424) := by
    dsimp [T]
    unfold bZeroBDefectCOneYSlope bZeroBDefectCOneRootPencil
    ring
  have y_slope_214_positive :
      0 < bZeroBDefectCOneYSlope S D 214 z := by
    have scale_term_positive :
        0 < S * (2511539327808 * z + 268548851520) := by positivity
    have complement_term_nonnegative :
        0 ≤ T * (620717828832 * z + 58005064872) := by positivity
    have residual_positive :
        0 < (617532494112 : ℚ) * z + 53946332424 := by positivity
    nlinarith [y_slope_214_identity]
  have core_214_positive :
      0 < bZeroBDefectCOneCodeCore S (S - 1 - D) 214 y z := by
    have y_difference := bZeroBDefectCOneCodeCore_sub_y S D 214 0 y z
    have wait_nonnegative : (0 : ℚ) ≤ y := by positivity
    nlinarith
  have x_lt_214 : x < 214 := by
    by_contra x_not_small
    have x_large_nat : 214 ≤ x := by omega
    have x_large : (214 : ℚ) ≤ x := by exact_mod_cast x_large_nat
    have x_difference := bZeroBDefectCOneCodeCore_sub_x S D 214 x y z
    nlinarith
  have x_le_213 : x ≤ 213 := by omega
  let U : ℚ := 39 * (S - 1) - 2178 * D
  have U_nonnegative : 0 ≤ U := by
    dsimp [U]
    linarith
  have y_slope_213_identity :
      2178 * bZeroBDefectCOneYSlope S D 213 z =
        -S * (11200837305888 * z + 946239168888) -
          (20273680587744 * z + 1905704563464) -
          U * (620717828832 * z + 58005064872) := by
    dsimp [U]
    unfold bZeroBDefectCOneYSlope bZeroBDefectCOneRootPencil
    ring
  have y_slope_213_negative :
      bZeroBDefectCOneYSlope S D 213 z < 0 := by
    have scale_term_positive :
        0 < S * (11200837305888 * z + 946239168888) := by positivity
    have residual_positive :
        0 < (20273680587744 : ℚ) * z + 1905704563464 := by positivity
    have complement_term_nonnegative :
        0 ≤ U * (620717828832 * z + 58005064872) := by positivity
    nlinarith [y_slope_213_identity]
  have core_213_endpoint_identity :
      2178 * bZeroBDefectCOneCodeCore S (S - 1 - D) 213 51768 z =
        -S * (574577330220713520 * z + 48492520096284810) -
          (1054795512096827856 * z + 99146903040113526) -
          U * bZeroBDefectCOneComplementCore (213 : ℚ) 51768 z := by
    rw [bZeroBDefectCOneCodeCore_thin_decomposition]
    dsimp [U]
    unfold bZeroBDefectCOneWaitFactor bZeroBDefectCOneRootPencil
      bZeroBDefectCOneComplementCore
    ring
  have core_213_endpoint_negative :
      bZeroBDefectCOneCodeCore S (S - 1 - D) 213 51768 z < 0 := by
    have scale_term_positive :
        0 < S * (574577330220713520 * z + 48492520096284810) := by positivity
    have residual_positive :
        0 < (1054795512096827856 : ℚ) * z + 99146903040113526 := by positivity
    have complement_term_nonnegative :
        0 ≤ U * bZeroBDefectCOneComplementCore (213 : ℚ) 51768 z := by
      have core_positive :
          0 < bZeroBDefectCOneComplementCore (213 : ℚ) 51768 z := by
        unfold bZeroBDefectCOneComplementCore
        positivity
      positivity
    nlinarith [core_213_endpoint_identity]
  exact bZeroBDefectCOne_no_zero_of_endpoint_negative S D x y z 213 51768
    core_zero x_slope_positive x_le_213 wait_large_nat y_slope_213_negative
    core_213_endpoint_negative

private theorem bZeroBDefectCOne_y_lt_of_late_first_b
    (S D : ℚ) (scale_large : 1 < S) (complement_positive : 0 < D)
    (density_upper : 6534 * D ≤ 39 * (S - 1))
    (x y z : Nat)
    (core_zero : bZeroBDefectCOneCodeCore S (S - 1 - D) x y z = 0) :
    y < 51768 := by
  by_contra wait_not_bounded
  have wait_large_nat : 51768 ≤ y := by omega
  have wait_positive : (1 : ℚ) ≤ y := by exact_mod_cast (show 1 ≤ y by omega)
  have z_nonnegative : (0 : ℚ) ≤ z := by positivity
  have scale_positive : (0 : ℚ) < S := by linarith
  have wait_factor_positive :
      0 < bZeroBDefectCOneWaitFactor S y :=
    bZeroBDefectCOneWaitFactor_pos S y scale_large wait_positive
  have x_slope_positive :
      0 < bZeroBDefectCOneXSlope S D y z :=
    bZeroBDefectCOneXSlope_pos S D y z scale_large complement_positive
      wait_positive z_nonnegative
  have pencil_215_positive :
      0 < bZeroBDefectCOneRootPencil (215 : ℚ) z := by
    rw [show bZeroBDefectCOneRootPencil (215 : ℚ) z =
      14024764 * z + 1959767 by
        unfold bZeroBDefectCOneRootPencil
        ring]
    positivity
  have complement_215_positive :
      0 < bZeroBDefectCOneComplementCore (215 : ℚ) y z := by
    unfold bZeroBDefectCOneComplementCore
    positivity
  have core_215_positive :
      0 < bZeroBDefectCOneCodeCore S (S - 1 - D) 215 y z := by
    rw [bZeroBDefectCOneCodeCore_thin_decomposition]
    have first_positive :
        0 < bZeroBDefectCOneWaitFactor S y *
          bZeroBDefectCOneRootPencil (215 : ℚ) z :=
      mul_pos wait_factor_positive pencil_215_positive
    have second_positive :
        0 < D * bZeroBDefectCOneComplementCore (215 : ℚ) y z :=
      mul_pos complement_positive complement_215_positive
    linarith
  have x_lt_215 : x < 215 := by
    by_contra x_not_small
    have x_large_nat : 215 ≤ x := by omega
    have x_large : (215 : ℚ) ≤ x := by exact_mod_cast x_large_nat
    have x_difference := bZeroBDefectCOneCodeCore_sub_x S D 215 x y z
    nlinarith
  have x_le_214 : x ≤ 214 := by omega
  let U : ℚ := 39 * (S - 1) - 6534 * D
  have U_nonnegative : 0 ≤ U := by
    dsimp [U]
    linarith
  have y_slope_214_identity :
      6534 * bZeroBDefectCOneYSlope S D 214 z =
        -S * (25606292533920 * z + 2089473285528) -
          (18673074451296 * z + 1778678550504) -
          U * (620717828832 * z + 58005064872) := by
    dsimp [U]
    unfold bZeroBDefectCOneYSlope bZeroBDefectCOneRootPencil
    ring
  have y_slope_214_negative :
      bZeroBDefectCOneYSlope S D 214 z < 0 := by
    have scale_term_positive :
        0 < S * (25606292533920 * z + 2089473285528) := by positivity
    have residual_positive :
        0 < (18673074451296 : ℚ) * z + 1778678550504 := by positivity
    have complement_term_nonnegative :
        0 ≤ U * (620717828832 * z + 58005064872) := by positivity
    nlinarith [y_slope_214_identity]
  have core_214_endpoint_identity :
      6534 * bZeroBDefectCOneCodeCore S (S - 1 - D) 214 51768 z =
        -S * (1320292503321890688 * z + 107673018066864846) -
          (971961766768771200 * z + 92573466180839730) -
          U * bZeroBDefectCOneComplementCore (214 : ℚ) 51768 z := by
    rw [bZeroBDefectCOneCodeCore_thin_decomposition]
    dsimp [U]
    unfold bZeroBDefectCOneWaitFactor bZeroBDefectCOneRootPencil
      bZeroBDefectCOneComplementCore
    ring
  have core_214_endpoint_negative :
      bZeroBDefectCOneCodeCore S (S - 1 - D) 214 51768 z < 0 := by
    have scale_term_positive :
        0 < S * (1320292503321890688 * z + 107673018066864846) := by positivity
    have residual_positive :
        0 < (971961766768771200 : ℚ) * z + 92573466180839730 := by positivity
    have complement_term_nonnegative :
        0 ≤ U * bZeroBDefectCOneComplementCore (214 : ℚ) 51768 z := by
      have core_positive :
          0 < bZeroBDefectCOneComplementCore (214 : ℚ) 51768 z := by
        unfold bZeroBDefectCOneComplementCore
        positivity
      positivity
    nlinarith [core_214_endpoint_identity]
  exact bZeroBDefectCOne_no_zero_of_endpoint_negative S D x y z 214 51768
    core_zero x_slope_positive x_le_214 wait_large_nat y_slope_214_negative
    core_214_endpoint_negative

/-- A zero whose tag body has its first `b` after `j` leading `c` letters has middle wait at
most `51767`. -/
theorem bZeroBDefectCOne_y_lt_of_first_b
    (j : Nat) (tail : List TagLetter) (x y z : Nat)
    (core_zero :
      bZeroBDefectCOneCodeCore
        ((3 : ℚ) ^
          (tagEncode 3 (List.replicate j .c ++ .b :: tail)).length)
        (ternaryCode (tagEncode 3 (List.replicate j .c ++ .b :: tail))) x y z = 0) :
    y < 51768 := by
  let body := List.replicate j .c ++ .b :: tail
  let S : Nat := 3 ^ (tagEncode 3 body).length
  let D : Nat := tagComplementCode body
  have complement_positive_nat : 0 < D := by
    dsimp [D, body]
    apply tagComplementCode_pos_of_mem_b
    simp
  have sharp_upper_nat : 242 * 3 ^ j * D ≤ 39 * (S - 1) := by
    simpa only [body, S, D] using tagComplementCode_first_b_sharp_upper j tail
  have scale_large_nat : 1 < S := by
    have left_positive : 0 < 242 * 3 ^ j * D := by positivity
    have right_positive : 0 < 39 * (S - 1) :=
      lt_of_lt_of_le left_positive sharp_upper_nat
    omega
  have scale_large : (1 : ℚ) < S := by exact_mod_cast scale_large_nat
  have complement_positive : (0 : ℚ) < D := by exact_mod_cast complement_positive_nat
  have scale_sub_cast : ((S - 1 : Nat) : ℚ) = (S : ℚ) - 1 := by
    rw [Nat.cast_sub scale_large_nat.le]
    norm_num
  have code_eq :
      (ternaryCode (tagEncode 3 body) : ℚ) = (S : ℚ) - 1 - D := by
    have complement_eq :
        (D : ℚ) = (S : ℚ) - ternaryCode (tagEncode 3 body) - 1 := by
      simpa [D, S] using tagComplementCode_cast_rat body
    linarith
  have core_complement_zero :
      bZeroBDefectCOneCodeCore (S : ℚ) ((S : ℚ) - 1 - D) x y z = 0 := by
    rw [← code_eq]
    simpa [S, body] using core_zero
  have density := tagComplementCode_first_b_density j tail
  have density_lower_nat : 13 * S ≤ 81 * 3 ^ j * D := by
    simpa only [body, S, D] using density.1
  by_cases j_zero : j = 0
  · subst j
    have lower : (13 : ℚ) * S ≤ 81 * D := by
      norm_num at density_lower_nat
      exact_mod_cast density_lower_nat
    have upper : (242 : ℚ) * D ≤ 39 * ((S : ℚ) - 1) := by
      norm_num at sharp_upper_nat
      have cast_upper : (242 * D : ℕ) ≤ 39 * (S - 1) := sharp_upper_nat
      have cast_upper_rat : ((242 * D : Nat) : ℚ) ≤ (39 * (S - 1) : Nat) := by
        exact_mod_cast cast_upper
      norm_num only [Nat.cast_mul] at cast_upper_rat
      rw [scale_sub_cast] at cast_upper_rat
      exact cast_upper_rat
    exact bZeroBDefectCOne_y_lt_of_first_b_zero S D scale_large complement_positive
      lower upper x y z core_complement_zero
  · by_cases j_one : j = 1
    · subst j
      have lower : (13 : ℚ) * S ≤ 243 * D := by
        norm_num at density_lower_nat
        exact_mod_cast density_lower_nat
      have upper : (726 : ℚ) * D ≤ 39 * ((S : ℚ) - 1) := by
        norm_num at sharp_upper_nat
        have cast_upper : (726 * D : ℕ) ≤ 39 * (S - 1) := sharp_upper_nat
        have cast_upper_rat : ((726 * D : Nat) : ℚ) ≤ (39 * (S - 1) : Nat) := by
          exact_mod_cast cast_upper
        norm_num only [Nat.cast_mul] at cast_upper_rat
        rw [scale_sub_cast] at cast_upper_rat
        exact cast_upper_rat
      exact bZeroBDefectCOne_y_lt_of_first_b_one S D scale_large complement_positive
        lower upper x y z core_complement_zero
    · by_cases j_two : j = 2
      · subst j
        have lower : (13 : ℚ) * S ≤ 729 * D := by
          norm_num at density_lower_nat
          exact_mod_cast density_lower_nat
        have upper : (2178 : ℚ) * D ≤ 39 * ((S : ℚ) - 1) := by
          norm_num at sharp_upper_nat
          have cast_upper : (2178 * D : ℕ) ≤ 39 * (S - 1) := sharp_upper_nat
          have cast_upper_rat : ((2178 * D : Nat) : ℚ) ≤ (39 * (S - 1) : Nat) := by
            exact_mod_cast cast_upper
          norm_num only [Nat.cast_mul] at cast_upper_rat
          rw [scale_sub_cast] at cast_upper_rat
          exact cast_upper_rat
        exact bZeroBDefectCOne_y_lt_of_first_b_two S D scale_large complement_positive
          lower upper x y z core_complement_zero
      · have three_le : 3 ≤ j := by omega
        have power_lower : 27 ≤ 3 ^ j := by
          simpa only [Nat.reducePow] using
            Nat.pow_le_pow_right (n := 3) (by norm_num) three_le
        have scaled_power_lower : 242 * 27 * D ≤ 242 * 3 ^ j * D := by
          have multiplied := Nat.mul_le_mul_left (242 * D) power_lower
          simpa only [mul_assoc, mul_left_comm, mul_comm] using multiplied
        have late_upper_nat : 6534 * D ≤ 39 * (S - 1) := by
          calc
            6534 * D = 242 * 27 * D := by ring
            _ ≤ 242 * 3 ^ j * D := scaled_power_lower
            _ ≤ 39 * (S - 1) := sharp_upper_nat
        have upper : (6534 : ℚ) * D ≤ 39 * ((S : ℚ) - 1) := by
          have cast_upper_rat : ((6534 * D : Nat) : ℚ) ≤ (39 * (S - 1) : Nat) := by
            exact_mod_cast late_upper_nat
          norm_num only [Nat.cast_mul] at cast_upper_rat
          rw [scale_sub_cast] at cast_upper_rat
          exact cast_upper_rat
        exact bZeroBDefectCOne_y_lt_of_late_first_b S D scale_large
          complement_positive upper x y z core_complement_zero

/-- Equivalent closed form of `bZeroBDefectCOne_y_lt_of_first_b`. -/
theorem bZeroBDefectCOne_y_le_of_first_b
    (j : Nat) (tail : List TagLetter) (x y z : Nat)
    (core_zero :
      bZeroBDefectCOneCodeCore
        ((3 : ℚ) ^
          (tagEncode 3 (List.replicate j .c ++ .b :: tail)).length)
        (ternaryCode (tagEncode 3 (List.replicate j .c ++ .b :: tail))) x y z = 0) :
    y ≤ 51767 := by
  have wait_bound :=
    bZeroBDefectCOne_y_lt_of_first_b j tail x y z core_zero
  omega

end MatrixMortality.ParabolicBlade
