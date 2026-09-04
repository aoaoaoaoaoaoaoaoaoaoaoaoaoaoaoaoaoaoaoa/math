import MatrixMortality.ParabolicFirstBLateTailCore

/-!
# Boundary waits for later first-`b` cylinders

The middle-wait faces zero and one require the positive finite-scale rectangle, rather than
the nonpositive correction used by the main outer-root certificate.
-/

namespace MatrixMortality.ParabolicBlade

/-- Zero middle wait is strictly positive when the first body `b` occurs at position at
most four. -/
theorem bZeroBDefectCOneCodeCore_ne_zero_of_y_zero_first_b_at_most_four
    (k : Nat) (tail : List TagLetter) (x z : Nat) (k_le : k ≤ 4) :
    bZeroBDefectCOneCodeCore
      ((3 : ℚ) ^
        (tagEncode 3 (List.replicate k .c ++ .b :: tail)).length)
      (ternaryCode (tagEncode 3 (List.replicate k .c ++ .b :: tail))) x 0 z ≠ 0 := by
  let body := List.replicate k .c ++ .b :: tail
  let T : Nat := 3 ^ (tagEncode 3 tail).length
  let E : Nat := tagComplementCode tail
  let S : Nat := 3 ^ (tagEncode 3 body).length
  let C : Nat := ternaryCode (tagEncode 3 body)
  let D : Nat := tagComplementCode body
  have scale_eq : S = firstBLatePrefixScale k * T := by
    dsimp [S, T, body]
    exact firstBLate_scale k tail
  have complement_eq : D = 39 * T + E := by
    dsimp [D, T, E, body]
    exact firstBLate_complement k tail
  have code_lt : C < S := by
    dsimp [C, S, body]
    exact ternaryCode_lt_pow_length
      (tagEncode 3 (List.replicate k .c ++ .b :: tail))
  have complement_nat : D = S - C - 1 := rfl
  have coordinate_sum : C + D + 1 = S := by omega
  have code_eq : (C : ℚ) = (S : ℚ) - 1 - D := by
    have coordinate_sum_rat : (C : ℚ) + D + 1 = S := by
      exact_mod_cast coordinate_sum
    linarith
  have scale_large_nat : 1 < S := by
    rw [scale_eq]
    have prefix_power_one : 1 ≤ 3 ^ k := one_le_pow₀ (by norm_num)
    have tail_scale_one : 1 ≤ T := by
      dsimp [T]
      exact one_le_pow₀ (by norm_num)
    calc
      1 < 243 := by norm_num
      _ ≤ firstBLatePrefixScale k * T := by
        unfold firstBLatePrefixScale
        simpa only [mul_one] using
          Nat.mul_le_mul (Nat.mul_le_mul (le_refl 243) prefix_power_one) tail_scale_one
  have complement_positive_nat : 0 < D := by
    rw [complement_eq]
    have scale_positive : 1 ≤ T := by
      dsimp [T]
      exact one_le_pow₀ (by norm_num)
    omega
  have complement_large_nat : S - 1 ≤ 585 * D := by
    rw [scale_eq, complement_eq]
    have scale_positive : 1 ≤ T := by
      dsimp [T]
      exact one_le_pow₀ (by norm_num)
    interval_cases k <;> norm_num [firstBLatePrefixScale] <;> omega
  have scale_large : (1 : ℚ) < S := by exact_mod_cast scale_large_nat
  have complement_positive : (0 : ℚ) < D := by exact_mod_cast complement_positive_nat
  have complement_large_cast : ((S - 1 : Nat) : ℚ) ≤ 585 * D := by
    exact_mod_cast complement_large_nat
  have complement_large : (S : ℚ) - 1 ≤ 585 * D := by
    rw [Nat.cast_sub scale_large_nat.le] at complement_large_cast
    norm_num at complement_large_cast ⊢
    exact complement_large_cast
  intro core_zero
  have scale_cast :
      (S : ℚ) =
        (3 : ℚ) ^
          (tagEncode 3 (List.replicate k .c ++ .b :: tail)).length := by
    dsimp [S, body]
    norm_num
  rw [← scale_cast] at core_zero
  change bZeroBDefectCOneCodeCore (S : ℚ) (C : ℚ) x 0 z = 0 at core_zero
  rw [code_eq] at core_zero
  have core_positive := bZeroBDefectCOneCodeCore_pos_of_zero_wait_large_complement
    (S : ℚ) D scale_large complement_positive complement_large x z
  exact ne_of_gt core_positive core_zero

/-- Zero middle wait is strictly positive when the first body `b` follows three or four
leading `c` letters. -/
theorem bZeroBDefectCOneCodeCore_late_ne_zero_of_y_zero_small
    (k : Nat) (tail : List TagLetter) (x z : Nat)
    (_three_le_k : 3 ≤ k) (k_le : k ≤ 4) :
    bZeroBDefectCOneCodeCore
      ((3 : ℚ) ^
        (tagEncode 3 (List.replicate k .c ++ .b :: tail)).length)
      (ternaryCode (tagEncode 3 (List.replicate k .c ++ .b :: tail))) x 0 z ≠ 0 := by
  exact bZeroBDefectCOneCodeCore_ne_zero_of_y_zero_first_b_at_most_four
    k tail x z k_le

set_option maxHeartbeats 2000000 in
/-- At middle wait zero, only two integral outer-root chambers survive the global tail
rectangle. -/
theorem firstBLate_y_zero_outer_cases
    (k j : Nat) (rest : List TagLetter) (x z : Nat)
    (five_le_k : 5 ≤ k) (k_le : k ≤ 11)
    (root_eq : parabolicOuterRootDenominator
      (firstBLateTailA k (List.replicate j .c ++ .b :: rest) 0)
      (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) z * x =
        parabolicOuterRootNumerator
          (firstBLateTailA k (List.replicate j .c ++ .b :: rest) 0)
          (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) 0 z) :
    (k = 5 ∧ x = 351) ∨ (k = 8 ∧ x = 218) := by
  let a := firstBLateTailA k (List.replicate j .c ++ .b :: rest) 0
  let d := firstBTwoTailD (List.replicate j .c ++ .b :: rest)
  change parabolicOuterRootDenominator a d z * x =
    parabolicOuterRootNumerator a d 0 z at root_eq
  have rectangle := firstBLateTail_positive_envelope_rectangle
    k 0 j rest 0 (Nat.zero_le j) (by norm_num)
  dsimp only at rectangle
  change FirstBTwoTailRectangle
    (firstBLateTailABase k 0) (firstBLateTailAPositiveUpper k 0 0)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  interval_cases k
  · have interval := firstBLateOuter_mem_open_interval x 0 350 352 z (-1)
      (firstBLateTailABase 5 0) (firstBLateTailAPositiveUpper 5 0 0)
      39 (firstBTwoTailDUpper 0)
      a d rectangle
      (by
        norm_num [FirstBLateOuterOpenCorners, firstBLateTailABase,
        firstBLateTailAPositiveUpper, firstBTwoTailDUpper,
        parabolicOuterRootDenominator, parabolicOuterRootNumerator,
        firstBLatePrefixScale]
        (repeat' apply And.intro) <;>
          nlinarith [show (0 : ℚ) ≤ z by positivity]) root_eq
    left
    exact ⟨rfl, by omega⟩
  · have interval := firstBLateOuter_mem_open_interval x 0 246 247 z (-1)
      (firstBLateTailABase 6 0) (firstBLateTailAPositiveUpper 6 0 0)
      39 (firstBTwoTailDUpper 0)
      a d rectangle
      (by
        norm_num [FirstBLateOuterOpenCorners, firstBLateTailABase,
        firstBLateTailAPositiveUpper, firstBTwoTailDUpper,
        parabolicOuterRootDenominator, parabolicOuterRootNumerator,
        firstBLatePrefixScale]
        (repeat' apply And.intro) <;>
          nlinarith [show (0 : ℚ) ≤ z by positivity]) root_eq
    omega
  · have interval := firstBLateOuter_mem_open_interval x 0 224 225 z (-1)
      (firstBLateTailABase 7 0) (firstBLateTailAPositiveUpper 7 0 0)
      39 (firstBTwoTailDUpper 0)
      a d rectangle
      (by
        norm_num [FirstBLateOuterOpenCorners, firstBLateTailABase,
        firstBLateTailAPositiveUpper, firstBTwoTailDUpper,
        parabolicOuterRootDenominator, parabolicOuterRootNumerator,
        firstBLatePrefixScale]
        (repeat' apply And.intro) <;>
          nlinarith [show (0 : ℚ) ≤ z by positivity]) root_eq
    omega
  · have interval := firstBLateOuter_mem_open_interval x 0 217 219 z (-1)
      (firstBLateTailABase 8 0) (firstBLateTailAPositiveUpper 8 0 0)
      39 (firstBTwoTailDUpper 0)
      a d rectangle
      (by
        norm_num [FirstBLateOuterOpenCorners, firstBLateTailABase,
        firstBLateTailAPositiveUpper, firstBTwoTailDUpper,
        parabolicOuterRootDenominator, parabolicOuterRootNumerator,
        firstBLatePrefixScale]
        (repeat' apply And.intro) <;>
          nlinarith [show (0 : ℚ) ≤ z by positivity]) root_eq
    right
    exact ⟨rfl, by omega⟩
  · have interval := firstBLateOuter_mem_open_interval x 0 215 216 z (-1)
      (firstBLateTailABase 9 0) (firstBLateTailAPositiveUpper 9 0 0)
      39 (firstBTwoTailDUpper 0)
      a d rectangle
      (by
        norm_num [FirstBLateOuterOpenCorners, firstBLateTailABase,
        firstBLateTailAPositiveUpper, firstBTwoTailDUpper,
        parabolicOuterRootDenominator, parabolicOuterRootNumerator,
        firstBLatePrefixScale]
        (repeat' apply And.intro) <;>
          nlinarith [show (0 : ℚ) ≤ z by positivity]) root_eq
    omega
  · have interval := firstBLateOuter_mem_open_interval x 0 215 216 z (-1)
      (firstBLateTailABase 10 0) (firstBLateTailAPositiveUpper 10 0 0)
      39 (firstBTwoTailDUpper 0)
      a d rectangle
      (by
        norm_num [FirstBLateOuterOpenCorners, firstBLateTailABase,
        firstBLateTailAPositiveUpper, firstBTwoTailDUpper,
        parabolicOuterRootDenominator, parabolicOuterRootNumerator,
        firstBLatePrefixScale]
        (repeat' apply And.intro) <;>
          nlinarith [show (0 : ℚ) ≤ z by positivity]) root_eq
    omega
  · have interval := firstBLateOuter_mem_open_interval x 0 214 215 z (-1)
      (firstBLateTailABase 11 0) (firstBLateTailAPositiveUpper 11 0 0)
      39 (firstBTwoTailDUpper 0)
      a d rectangle
      (by
        norm_num [FirstBLateOuterOpenCorners, firstBLateTailABase,
        firstBLateTailAPositiveUpper, firstBTwoTailDUpper,
        parabolicOuterRootDenominator, parabolicOuterRootNumerator,
        firstBLatePrefixScale]
        (repeat' apply And.intro) <;>
          nlinarith [show (0 : ℚ) ≤ z by positivity]) root_eq
    omega

set_option maxHeartbeats 2000000 in
/-- At middle wait one, the sole integral outer-root chamber is `(k,x)=(4,184)`. -/
theorem firstBLate_y_one_outer_case
    (k j : Nat) (rest : List TagLetter) (x z : Nat)
    (three_le_k : 3 ≤ k) (k_le : k ≤ 11)
    (root_eq : parabolicOuterRootDenominator
      (firstBLateTailA k (List.replicate j .c ++ .b :: rest) 1)
      (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) z * x =
        parabolicOuterRootNumerator
          (firstBLateTailA k (List.replicate j .c ++ .b :: rest) 1)
          (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) 1 z) :
    k = 4 ∧ x = 184 := by
  let a := firstBLateTailA k (List.replicate j .c ++ .b :: rest) 1
  let d := firstBTwoTailD (List.replicate j .c ++ .b :: rest)
  change parabolicOuterRootDenominator a d z * x =
    parabolicOuterRootNumerator a d 1 z at root_eq
  have rectangle := firstBLateTail_positive_envelope_rectangle
    k 0 j rest 1 (Nat.zero_le j) (by norm_num)
  dsimp only at rectangle
  change FirstBTwoTailRectangle
    (firstBLateTailABase k 1) (firstBLateTailAPositiveUpper k 0 1)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  interval_cases k
  · have interval := firstBLateOuter_mem_open_interval x 1 142 143 z 1
      (firstBLateTailABase 3 1) (firstBLateTailAPositiveUpper 3 0 1)
      39 (firstBTwoTailDUpper 0)
      a d rectangle
      (by
        norm_num [FirstBLateOuterOpenCorners, firstBLateTailABase,
        firstBLateTailAPositiveUpper, firstBTwoTailDUpper,
        parabolicOuterRootDenominator, parabolicOuterRootNumerator,
        firstBLatePrefixScale]
        (repeat' apply And.intro) <;>
          nlinarith [show (0 : ℚ) ≤ z by positivity]) root_eq
    omega
  · have interval := firstBLateOuter_mem_open_interval x 1 183 185 z 1
      (firstBLateTailABase 4 1) (firstBLateTailAPositiveUpper 4 0 1)
      39 (firstBTwoTailDUpper 0)
      a d rectangle
      (by
        norm_num [FirstBLateOuterOpenCorners, firstBLateTailABase,
        firstBLateTailAPositiveUpper, firstBTwoTailDUpper,
        parabolicOuterRootDenominator, parabolicOuterRootNumerator,
        firstBLatePrefixScale]
        (repeat' apply And.intro) <;>
          nlinarith [show (0 : ℚ) ≤ z by positivity]) root_eq
    exact ⟨rfl, by omega⟩
  · have interval := firstBLateOuter_mem_open_interval x 1 203 204 z 1
      (firstBLateTailABase 5 1) (firstBLateTailAPositiveUpper 5 0 1)
      39 (firstBTwoTailDUpper 0)
      a d rectangle
      (by
        norm_num [FirstBLateOuterOpenCorners, firstBLateTailABase,
        firstBLateTailAPositiveUpper, firstBTwoTailDUpper,
        parabolicOuterRootDenominator, parabolicOuterRootNumerator,
        firstBLatePrefixScale]
        (repeat' apply And.intro) <;>
          nlinarith [show (0 : ℚ) ≤ z by positivity]) root_eq
    omega
  · have interval := firstBLateOuter_mem_open_interval x 1 210 211 z 1
      (firstBLateTailABase 6 1) (firstBLateTailAPositiveUpper 6 0 1)
      39 (firstBTwoTailDUpper 0)
      a d rectangle
      (by
        norm_num [FirstBLateOuterOpenCorners, firstBLateTailABase,
        firstBLateTailAPositiveUpper, firstBTwoTailDUpper,
        parabolicOuterRootDenominator, parabolicOuterRootNumerator,
        firstBLatePrefixScale]
        (repeat' apply And.intro) <;>
          nlinarith [show (0 : ℚ) ≤ z by positivity]) root_eq
    omega
  · have interval := firstBLateOuter_mem_open_interval x 1 213 214 z 1
      (firstBLateTailABase 7 1) (firstBLateTailAPositiveUpper 7 0 1)
      39 (firstBTwoTailDUpper 0)
      a d rectangle
      (by
        norm_num [FirstBLateOuterOpenCorners, firstBLateTailABase,
        firstBLateTailAPositiveUpper, firstBTwoTailDUpper,
        parabolicOuterRootDenominator, parabolicOuterRootNumerator,
        firstBLatePrefixScale]
        (repeat' apply And.intro) <;>
          nlinarith [show (0 : ℚ) ≤ z by positivity]) root_eq
    omega
  · have interval := firstBLateOuter_mem_open_interval x 1 214 215 z 1
      (firstBLateTailABase 8 1) (firstBLateTailAPositiveUpper 8 0 1)
      39 (firstBTwoTailDUpper 0)
      a d rectangle
      (by
        norm_num [FirstBLateOuterOpenCorners, firstBLateTailABase,
        firstBLateTailAPositiveUpper, firstBTwoTailDUpper,
        parabolicOuterRootDenominator, parabolicOuterRootNumerator,
        firstBLatePrefixScale]
        (repeat' apply And.intro) <;>
          nlinarith [show (0 : ℚ) ≤ z by positivity]) root_eq
    omega
  · have interval := firstBLateOuter_mem_open_interval x 1 214 215 z 1
      (firstBLateTailABase 9 1) (firstBLateTailAPositiveUpper 9 0 1)
      39 (firstBTwoTailDUpper 0)
      a d rectangle
      (by
        norm_num [FirstBLateOuterOpenCorners, firstBLateTailABase,
        firstBLateTailAPositiveUpper, firstBTwoTailDUpper,
        parabolicOuterRootDenominator, parabolicOuterRootNumerator,
        firstBLatePrefixScale]
        (repeat' apply And.intro) <;>
          nlinarith [show (0 : ℚ) ≤ z by positivity]) root_eq
    omega
  · have interval := firstBLateOuter_mem_open_interval x 1 214 215 z 1
      (firstBLateTailABase 10 1) (firstBLateTailAPositiveUpper 10 0 1)
      39 (firstBTwoTailDUpper 0)
      a d rectangle
      (by
        norm_num [FirstBLateOuterOpenCorners, firstBLateTailABase,
        firstBLateTailAPositiveUpper, firstBTwoTailDUpper,
        parabolicOuterRootDenominator, parabolicOuterRootNumerator,
        firstBLatePrefixScale]
        (repeat' apply And.intro) <;>
          nlinarith [show (0 : ℚ) ≤ z by positivity]) root_eq
    omega
  · have interval := firstBLateOuter_mem_open_interval x 1 214 215 z 1
      (firstBLateTailABase 11 1) (firstBLateTailAPositiveUpper 11 0 1)
      39 (firstBTwoTailDUpper 0)
      a d rectangle
      (by
        norm_num [FirstBLateOuterOpenCorners, firstBLateTailABase,
        firstBLateTailAPositiveUpper, firstBTwoTailDUpper,
        parabolicOuterRootDenominator, parabolicOuterRootNumerator,
        firstBLatePrefixScale]
        (repeat' apply And.intro) <;>
          nlinarith [show (0 : ℚ) ≤ z by positivity]) root_eq
    omega

set_option maxHeartbeats 2000000 in
/-- The middle-wait-zero survivor at first-`b` position eight has its inner root in
`(0,1)`. -/
theorem firstBLate_y_zero_k_eight_false
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq : firstBTwoTailZDenominator
      (firstBLateTailA 8 (List.replicate j .c ++ .b :: rest) 0)
      (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) 218 0 * z =
        firstBTwoTailZNumerator
          (firstBLateTailA 8 (List.replicate j .c ++ .b :: rest) 0)
          (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) 218 0) : False := by
  let a := firstBLateTailA 8 (List.replicate j .c ++ .b :: rest) 0
  let d := firstBTwoTailD (List.replicate j .c ++ .b :: rest)
  change firstBTwoTailZDenominator a d 218 0 * z =
    firstBTwoTailZNumerator a d 218 0 at root_eq
  have rectangle := firstBLateTail_positive_envelope_rectangle
    8 0 j rest 0 (Nat.zero_le j) (by norm_num)
  dsimp only at rectangle
  change FirstBTwoTailRectangle
    (firstBLateTailABase 8 0) (firstBLateTailAPositiveUpper 8 0 0)
    39 (firstBTwoTailDUpper 0) a d at rectangle
  exact firstBTwoTailZ_no_nat_of_gap 218 0 0 z (-1)
    (firstBLateTailABase 8 0) (firstBLateTailAPositiveUpper 8 0 0)
    39 (firstBTwoTailDUpper 0) a d rectangle
    (by norm_num [FirstBTwoTailOpenCorners, firstBLateTailABase,
      firstBLateTailAPositiveUpper, firstBTwoTailDUpper,
      firstBTwoTailZDenominator, firstBTwoTailZNumerator,
      firstBLatePrefixScale]) root_eq

set_option maxHeartbeats 2000000 in
/-- The middle-wait-zero survivor at first-`b` position five forces the next `b` to
position one and the inner wait to two. -/
theorem firstBLate_y_zero_k_five_tail_case
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq : firstBTwoTailZDenominator
      (firstBLateTailA 5 (List.replicate j .c ++ .b :: rest) 0)
      (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) 351 0 * z =
        firstBTwoTailZNumerator
          (firstBLateTailA 5 (List.replicate j .c ++ .b :: rest) 0)
          (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) 351 0) :
    j = 1 ∧ z = 2 := by
  let a := firstBLateTailA 5 (List.replicate j .c ++ .b :: rest) 0
  let d := firstBTwoTailD (List.replicate j .c ++ .b :: rest)
  change firstBTwoTailZDenominator a d 351 0 * z =
    firstBTwoTailZNumerator a d 351 0 at root_eq
  by_cases position_zero : j = 0
  · subst j
    have rectangle := firstBLateTail_positive_exact_rectangle 5 0 rest 0 (by norm_num)
    dsimp only at rectangle
    change FirstBTwoTailRectangle
      (firstBLateTailABase 5 0) (firstBLateTailAPositiveUpper 5 0 0)
      (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d at rectangle
    exact False.elim (firstBTwoTailZ_no_nat_of_negative 351 0 z (-1)
      (firstBLateTailABase 5 0) (firstBLateTailAPositiveUpper 5 0 0)
      (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d rectangle
      (by norm_num [FirstBTwoTailNegativeCorners, firstBLateTailABase,
        firstBLateTailAPositiveUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator,
        firstBLatePrefixScale]) root_eq)
  · by_cases position_one : j = 1
    · subst j
      have rectangle := firstBLateTail_positive_exact_rectangle 5 1 rest 0 (by norm_num)
      dsimp only at rectangle
      change FirstBTwoTailRectangle
        (firstBLateTailABase 5 0) (firstBLateTailAPositiveUpper 5 1 0)
        (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) a d at rectangle
      have interval := firstBTwoTailZ_mem_open_interval 351 0 1 3 z (-1)
        (firstBLateTailABase 5 0) (firstBLateTailAPositiveUpper 5 1 0)
        (firstBTwoTailDLower 1) (firstBTwoTailDUpper 1) a d rectangle
        (by norm_num [FirstBTwoTailOpenCorners, firstBLateTailABase,
          firstBLateTailAPositiveUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
          firstBTwoTailZDenominator, firstBTwoTailZNumerator,
          firstBLatePrefixScale]) root_eq
      exact ⟨rfl, by omega⟩
    · have position_large : 2 ≤ j := by omega
      have rectangle := firstBLateTail_positive_envelope_rectangle
        5 2 j rest 0 position_large (by norm_num)
      dsimp only at rectangle
      change FirstBTwoTailRectangle
        (firstBLateTailABase 5 0) (firstBLateTailAPositiveUpper 5 2 0)
        39 (firstBTwoTailDUpper 2) a d at rectangle
      exact False.elim (firstBTwoTailZ_no_nat_of_negative 351 0 z 1
        (firstBLateTailABase 5 0) (firstBLateTailAPositiveUpper 5 2 0)
        39 (firstBTwoTailDUpper 2) a d rectangle
        (by norm_num [FirstBTwoTailNegativeCorners, firstBLateTailABase,
          firstBLateTailAPositiveUpper, firstBTwoTailDUpper,
          firstBTwoTailZDenominator, firstBTwoTailZNumerator,
          firstBLatePrefixScale]) root_eq)

set_option maxHeartbeats 2000000 in
/-- The sole middle-wait-one outer chamber forces the next `b` to be immediate and the
inner wait to four. -/
theorem firstBLate_y_one_tail_case
    (j : Nat) (rest : List TagLetter) (z : Nat)
    (root_eq : firstBTwoTailZDenominator
      (firstBLateTailA 4 (List.replicate j .c ++ .b :: rest) 1)
      (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) 184 1 * z =
        firstBTwoTailZNumerator
          (firstBLateTailA 4 (List.replicate j .c ++ .b :: rest) 1)
          (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) 184 1) :
    j = 0 ∧ z = 4 := by
  let a := firstBLateTailA 4 (List.replicate j .c ++ .b :: rest) 1
  let d := firstBTwoTailD (List.replicate j .c ++ .b :: rest)
  change firstBTwoTailZDenominator a d 184 1 * z =
    firstBTwoTailZNumerator a d 184 1 at root_eq
  by_cases position_zero : j = 0
  · subst j
    have rectangle := firstBLateTail_positive_exact_rectangle 4 0 rest 1 (by norm_num)
    dsimp only at rectangle
    change FirstBTwoTailRectangle
      (firstBLateTailABase 4 1) (firstBLateTailAPositiveUpper 4 0 1)
      (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d at rectangle
    have interval := firstBTwoTailZ_mem_open_interval 184 1 3 5 z 1
      (firstBLateTailABase 4 1) (firstBLateTailAPositiveUpper 4 0 1)
      (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d rectangle
      (by norm_num [FirstBTwoTailOpenCorners, firstBLateTailABase,
        firstBLateTailAPositiveUpper, firstBTwoTailDLower, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator,
        firstBLatePrefixScale]) root_eq
    exact ⟨rfl, by omega⟩
  · have position_large : 1 ≤ j := by omega
    have rectangle := firstBLateTail_positive_envelope_rectangle
      4 1 j rest 1 position_large (by norm_num)
    dsimp only at rectangle
    change FirstBTwoTailRectangle
      (firstBLateTailABase 4 1) (firstBLateTailAPositiveUpper 4 1 1)
      39 (firstBTwoTailDUpper 1) a d at rectangle
    exact False.elim (firstBTwoTailZ_no_nat_of_negative 184 1 z 1
      (firstBLateTailABase 4 1) (firstBLateTailAPositiveUpper 4 1 1)
      39 (firstBTwoTailDUpper 1) a d rectangle
      (by norm_num [FirstBTwoTailNegativeCorners, firstBLateTailABase,
        firstBLateTailAPositiveUpper, firstBTwoTailDUpper,
        firstBTwoTailZDenominator, firstBTwoTailZNumerator,
        firstBLatePrefixScale]) root_eq)

private theorem cccccbcb_scale (rest : List TagLetter) :
    3 ^ (tagEncode 3 ([.c, .c, .c, .c, .c, .b, .c, .b] ++ rest)).length =
      43046721 * 3 ^ (tagEncode 3 rest).length := by
  rw [tagEncode_append, List.length_append, pow_add]
  norm_num [tagEncode, spell, tagCode]

private theorem cccccbcb_complement (rest : List TagLetter) :
    tagComplementCode ([.c, .c, .c, .c, .c, .b, .c, .b] ++ rest) =
      28470 * 3 ^ (tagEncode 3 rest).length + tagComplementCode rest := by
  rw [tagComplementCode_append]
  have stem_complement :
      tagComplementCode [.c, .c, .c, .c, .c, .b, .c, .b] = 28470 := by decide
  rw [stem_complement]

/-- The exceptional middle-wait-zero suffix cannot close the primitive core. -/
theorem bZeroBDefectCOneCodeCore_cccccbcb_ne_zero (rest : List TagLetter) :
    bZeroBDefectCOneCodeCore
      ((3 : ℚ) ^
        (tagEncode 3 ([.c, .c, .c, .c, .c, .b, .c, .b] ++ rest)).length)
      (ternaryCode
        (tagEncode 3 ([.c, .c, .c, .c, .c, .b, .c, .b] ++ rest)))
      351 0 2 ≠ 0 := by
  let R : Nat := 3 ^ (tagEncode 3 rest).length
  let G : Nat := tagComplementCode rest
  let body := [.c, .c, .c, .c, .c, .b, .c, .b] ++ rest
  let S : Nat := 3 ^ (tagEncode 3 body).length
  let C : Nat := ternaryCode (tagEncode 3 body)
  let D : Nat := tagComplementCode body
  have scale_positive : 1 ≤ R := by
    dsimp [R]
    exact one_le_pow₀ (by norm_num)
  have scale_eq : S = 43046721 * R := by
    dsimp [S, R, body]
    exact cccccbcb_scale rest
  have complement_eq : D = 28470 * R + G := by
    dsimp [D, R, G, body]
    exact cccccbcb_complement rest
  have code_lt : C < S := by
    dsimp [C, S, body]
    exact ternaryCode_lt_pow_length
      (tagEncode 3 ([.c, .c, .c, .c, .c, .b, .c, .b] ++ rest))
  have complement_nat : D = S - C - 1 := rfl
  have coordinate_sum : C + D + 1 = S := by omega
  have code_eq : (C : ℤ) = (S : ℤ) - 1 - D := by
    have coordinate_sum_int : (C : ℤ) + D + 1 = S := by
      exact_mod_cast coordinate_sum
    omega
  intro core_zero
  have power_cast :
      (S : ℚ) =
        (3 : ℚ) ^
          (tagEncode 3 ([.c, .c, .c, .c, .c, .b, .c, .b] ++ rest)).length := by
    dsimp [S, body]
    norm_num
  rw [← power_cast] at core_zero
  change bZeroBDefectCOneCodeCore (S : ℚ) (C : ℚ) 351 0 2 = 0 at core_zero
  have core_zero_int :
      bZeroBDefectCOneCodeCore (S : ℤ) (C : ℤ) 351 0 2 = 0 := by
    unfold bZeroBDefectCOneCodeCore at core_zero ⊢
    exact_mod_cast core_zero
  have balance :
      (464992898008908 : ℤ) * G =
        12659898783231 * R - 307534700871 := by
    rw [code_eq, bZeroBDefectCOneCodeCore_thin_decomposition] at core_zero_int
    unfold bZeroBDefectCOneWaitFactor bZeroBDefectCOneRootPencil
      bZeroBDefectCOneComplementCore at core_zero_int
    rw [scale_eq, complement_eq] at core_zero_int
    push_cast at core_zero_int
    norm_num at core_zero_int ⊢
    linear_combination core_zero_int
  have forced_lower : (39 : ℤ) * R < 2178 * G := by
    have R_positive : (0 : ℤ) < R := by exact_mod_cast scale_positive
    linarith [balance]
  have forced_upper : (243 : ℤ) * G < 13 * R := by
    have R_positive : (0 : ℤ) < R := by exact_mod_cast scale_positive
    linarith [balance]
  rcases tagComplementCode_first_b_position_gap 1 rest with high | low
  · have high_int : (13 : ℤ) * R ≤ 243 * G := by exact_mod_cast high
    linarith
  · have low_int : (2178 : ℤ) * G < 39 * R := by exact_mod_cast low
    linarith

private theorem ccccbb_scale (rest : List TagLetter) :
    3 ^ (tagEncode 3 ([.c, .c, .c, .c, .b, .b] ++ rest)).length =
      4782969 * 3 ^ (tagEncode 3 rest).length := by
  rw [tagEncode_append, List.length_append, pow_add]
  norm_num [tagEncode, spell, tagCode]

private theorem ccccbb_complement (rest : List TagLetter) :
    tagComplementCode ([.c, .c, .c, .c, .b, .b] ++ rest) =
      9516 * 3 ^ (tagEncode 3 rest).length + tagComplementCode rest := by
  rw [tagComplementCode_append]
  have stem_complement :
      tagComplementCode [.c, .c, .c, .c, .b, .b] = 9516 := by decide
  rw [stem_complement]

/-- The exceptional middle-wait-one suffix cannot close the primitive core. -/
theorem bZeroBDefectCOneCodeCore_ccccbb_ne_zero (rest : List TagLetter) :
    bZeroBDefectCOneCodeCore
      ((3 : ℚ) ^ (tagEncode 3 ([.c, .c, .c, .c, .b, .b] ++ rest)).length)
      (ternaryCode (tagEncode 3 ([.c, .c, .c, .c, .b, .b] ++ rest)))
      184 1 4 ≠ 0 := by
  let R : Nat := 3 ^ (tagEncode 3 rest).length
  let G : Nat := tagComplementCode rest
  let body := [.c, .c, .c, .c, .b, .b] ++ rest
  let S : Nat := 3 ^ (tagEncode 3 body).length
  let C : Nat := ternaryCode (tagEncode 3 body)
  let D : Nat := tagComplementCode body
  have scale_positive : 1 ≤ R := by
    dsimp [R]
    exact one_le_pow₀ (by norm_num)
  have scale_eq : S = 4782969 * R := by
    dsimp [S, R, body]
    exact ccccbb_scale rest
  have complement_eq : D = 9516 * R + G := by
    dsimp [D, R, G, body]
    exact ccccbb_complement rest
  have code_lt : C < S := by
    dsimp [C, S, body]
    exact ternaryCode_lt_pow_length
      (tagEncode 3 ([.c, .c, .c, .c, .b, .b] ++ rest))
  have complement_nat : D = S - C - 1 := rfl
  have coordinate_sum : C + D + 1 = S := by omega
  have code_eq : (C : ℤ) = (S : ℤ) - 1 - D := by
    have coordinate_sum_int : (C : ℤ) + D + 1 = S := by
      exact_mod_cast coordinate_sum
    omega
  intro core_zero
  have power_cast :
      (S : ℚ) =
        (3 : ℚ) ^ (tagEncode 3 ([.c, .c, .c, .c, .b, .b] ++ rest)).length := by
    dsimp [S, body]
    norm_num
  rw [← power_cast] at core_zero
  change bZeroBDefectCOneCodeCore (S : ℚ) (C : ℚ) 184 1 4 = 0 at core_zero
  have core_zero_int :
      bZeroBDefectCOneCodeCore (S : ℤ) (C : ℤ) 184 1 4 = 0 := by
    unfold bZeroBDefectCOneCodeCore at core_zero ⊢
    exact_mod_cast core_zero
  have balance :
      (479992068919980 : ℤ) * G =
        59718499097247 * R + 15158494041 := by
    rw [code_eq, bZeroBDefectCOneCodeCore_thin_decomposition] at core_zero_int
    unfold bZeroBDefectCOneWaitFactor bZeroBDefectCOneRootPencil
      bZeroBDefectCOneComplementCore at core_zero_int
    rw [scale_eq, complement_eq] at core_zero_int
    push_cast at core_zero_int
    norm_num at core_zero_int ⊢
    linear_combination core_zero_int
  have forced_lower : (39 : ℤ) * R < 726 * G := by
    have R_positive : (0 : ℤ) < R := by exact_mod_cast scale_positive
    linarith [balance]
  have forced_upper : (81 : ℤ) * G < 13 * R := by
    have R_positive : (0 : ℤ) < R := by exact_mod_cast scale_positive
    linarith [balance]
  rcases tagComplementCode_first_b_position_gap 0 rest with high | low
  · have high_int : (13 : ℤ) * R ≤ 81 * G := by exact_mod_cast high
    linarith
  · have low_int : (726 : ℤ) * G < 39 * R := by exact_mod_cast low
    linarith

end MatrixMortality.ParabolicBlade
