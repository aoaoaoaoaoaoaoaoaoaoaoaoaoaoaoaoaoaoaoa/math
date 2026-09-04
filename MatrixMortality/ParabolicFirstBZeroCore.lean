import MatrixMortality.ParabolicFirstBLateBoundary
import MatrixMortality.ParabolicFirstBOneOuterSuffixCore

/-!
# Leading first-`b` cylinder

A body beginning with `b` has prefix scale 243. Its positive middle-wait boundary is
empty below six, while every larger wait enters the common outer-root window. Removing
the next `b` produces the same parameter-free suffix grammar as the `cb` cylinder.
-/

namespace MatrixMortality.ParabolicBlade

/-- The zero-middle-wait face of the leading first-`b` cylinder is empty. -/
theorem bZeroBDefectCOneCodeCore_first_b_zero_ne_zero_of_y_zero
    (tail : List TagLetter) (x z : Nat) :
    bZeroBDefectCOneCodeCore
      ((3 : ℚ) ^ (tagEncode 3 (.b :: tail)).length)
      (ternaryCode (tagEncode 3 (.b :: tail))) x 0 z ≠ 0 := by
  simpa only [List.replicate_zero, List.nil_append] using
    bZeroBDefectCOneCodeCore_ne_zero_of_y_zero_first_b_at_most_four
      0 tail x z (by norm_num)

set_option maxHeartbeats 2000000 in
/-- Middle waits one through five admit no integral outer wait in the leading first-`b`
cylinder. -/
theorem firstBZero_outer_false_of_small_positive_y
    (j : Nat) (rest : List TagLetter) (x y z : Nat)
    (y_positive : 1 ≤ y) (y_small : y ≤ 5)
    (root_eq : parabolicOuterRootDenominator
      (firstBLateTailA 0 (List.replicate j .c ++ .b :: rest) y)
      (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) z * x =
        parabolicOuterRootNumerator
          (firstBLateTailA 0 (List.replicate j .c ++ .b :: rest) y)
          (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) y z) : False := by
  interval_cases y
  · let a := firstBLateTailA 0 (List.replicate j .c ++ .b :: rest) 1
    let d := firstBTwoTailD (List.replicate j .c ++ .b :: rest)
    change parabolicOuterRootDenominator a d z * x =
      parabolicOuterRootNumerator a d 1 z at root_eq
    have rectangle := firstBLateTail_positive_envelope_rectangle
      0 0 j rest 1 (Nat.zero_le j) (by norm_num)
    dsimp only at rectangle
    change FirstBTwoTailRectangle
      (firstBLateTailABase 0 1) (firstBLateTailAPositiveUpper 0 0 1)
      39 (firstBTwoTailDUpper 0) a d at rectangle
    have interval := firstBLateOuter_mem_open_interval x 1 13 14 z 1
      (firstBLateTailABase 0 1) (firstBLateTailAPositiveUpper 0 0 1)
      39 (firstBTwoTailDUpper 0) a d rectangle
      (by
        norm_num [FirstBLateOuterOpenCorners, firstBLateTailABase,
          firstBLateTailAPositiveUpper, firstBTwoTailDUpper,
          parabolicOuterRootDenominator, parabolicOuterRootNumerator,
          firstBLatePrefixScale]
        (repeat' apply And.intro) <;>
          nlinarith [show (0 : ℚ) ≤ z by positivity]) root_eq
    omega
  · let a := firstBLateTailA 0 (List.replicate j .c ++ .b :: rest) 2
    let d := firstBTwoTailD (List.replicate j .c ++ .b :: rest)
    change parabolicOuterRootDenominator a d z * x =
      parabolicOuterRootNumerator a d 2 z at root_eq
    have rectangle := firstBLateTail_envelope_rectangle
      0 0 j rest 2 (Nat.zero_le j) (by norm_num)
    dsimp only at rectangle
    change FirstBTwoTailRectangle
      (firstBLateTailALower 0 0 2) (firstBLateTailABase 0 2)
      39 (firstBTwoTailDUpper 0) a d at rectangle
    have interval := firstBLateOuter_mem_open_interval x 2 27 28 z 1
      (firstBLateTailALower 0 0 2) (firstBLateTailABase 0 2)
      39 (firstBTwoTailDUpper 0) a d rectangle
      (by
        norm_num [FirstBLateOuterOpenCorners, firstBLateTailALower,
          firstBLateTailABase, firstBTwoTailDUpper,
          parabolicOuterRootDenominator, parabolicOuterRootNumerator,
          firstBLatePrefixScale]
        (repeat' apply And.intro) <;>
          nlinarith [show (0 : ℚ) ≤ z by positivity]) root_eq
    omega
  · let a := firstBLateTailA 0 (List.replicate j .c ++ .b :: rest) 3
    let d := firstBTwoTailD (List.replicate j .c ++ .b :: rest)
    change parabolicOuterRootDenominator a d z * x =
      parabolicOuterRootNumerator a d 3 z at root_eq
    have rectangle := firstBLateTail_envelope_rectangle
      0 0 j rest 3 (Nat.zero_le j) (by norm_num)
    dsimp only at rectangle
    change FirstBTwoTailRectangle
      (firstBLateTailALower 0 0 3) (firstBLateTailABase 0 3)
      39 (firstBTwoTailDUpper 0) a d at rectangle
    have interval := firstBLateOuter_mem_open_interval x 3 39 40 z 1
      (firstBLateTailALower 0 0 3) (firstBLateTailABase 0 3)
      39 (firstBTwoTailDUpper 0) a d rectangle
      (by
        norm_num [FirstBLateOuterOpenCorners, firstBLateTailALower,
          firstBLateTailABase, firstBTwoTailDUpper,
          parabolicOuterRootDenominator, parabolicOuterRootNumerator,
          firstBLatePrefixScale]
        (repeat' apply And.intro) <;>
          nlinarith [show (0 : ℚ) ≤ z by positivity]) root_eq
    omega
  · let a := firstBLateTailA 0 (List.replicate j .c ++ .b :: rest) 4
    let d := firstBTwoTailD (List.replicate j .c ++ .b :: rest)
    change parabolicOuterRootDenominator a d z * x =
      parabolicOuterRootNumerator a d 4 z at root_eq
    have rectangle := firstBLateTail_envelope_rectangle
      0 0 j rest 4 (Nat.zero_le j) (by norm_num)
    dsimp only at rectangle
    change FirstBTwoTailRectangle
      (firstBLateTailALower 0 0 4) (firstBLateTailABase 0 4)
      39 (firstBTwoTailDUpper 0) a d at rectangle
    have interval := firstBLateOuter_mem_open_interval x 4 49 50 z 1
      (firstBLateTailALower 0 0 4) (firstBLateTailABase 0 4)
      39 (firstBTwoTailDUpper 0) a d rectangle
      (by
        norm_num [FirstBLateOuterOpenCorners, firstBLateTailALower,
          firstBLateTailABase, firstBTwoTailDUpper,
          parabolicOuterRootDenominator, parabolicOuterRootNumerator,
          firstBLatePrefixScale]
        (repeat' apply And.intro) <;>
          nlinarith [show (0 : ℚ) ≤ z by positivity]) root_eq
    omega
  · let a := firstBLateTailA 0 (List.replicate j .c ++ .b :: rest) 5
    let d := firstBTwoTailD (List.replicate j .c ++ .b :: rest)
    change parabolicOuterRootDenominator a d z * x =
      parabolicOuterRootNumerator a d 5 z at root_eq
    by_cases position_zero : j = 0
    · subst j
      have rectangle := firstBLateTail_exact_rectangle 0 0 rest 5 (by norm_num)
      dsimp only [List.replicate_zero, List.nil_append] at rectangle
      change FirstBTwoTailRectangle
        (firstBLateTailALower 0 0 5) (firstBLateTailABase 0 5)
        (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d at rectangle
      have interval := firstBLateOuter_mem_open_interval x 5 58 59 z 1
        (firstBLateTailALower 0 0 5) (firstBLateTailABase 0 5)
        (firstBTwoTailDLower 0) (firstBTwoTailDUpper 0) a d rectangle
        (by
          norm_num [FirstBLateOuterOpenCorners, firstBLateTailALower,
            firstBLateTailABase, firstBTwoTailDLower, firstBTwoTailDUpper,
            parabolicOuterRootDenominator, parabolicOuterRootNumerator,
            firstBLatePrefixScale]
          (repeat' apply And.intro) <;>
            nlinarith [show (0 : ℚ) ≤ z by positivity]) root_eq
      omega
    · have position_large : 1 ≤ j := by omega
      have rectangle := firstBLateTail_envelope_rectangle
        0 1 j rest 5 position_large (by norm_num)
      dsimp only at rectangle
      change FirstBTwoTailRectangle
        (firstBLateTailALower 0 1 5) (firstBLateTailABase 0 5)
        39 (firstBTwoTailDUpper 1) a d at rectangle
      have interval := firstBLateOuter_mem_open_interval x 5 59 60 z 1
        (firstBLateTailALower 0 1 5) (firstBLateTailABase 0 5)
        39 (firstBTwoTailDUpper 1) a d rectangle
        (by
          norm_num [FirstBLateOuterOpenCorners, firstBLateTailALower,
            firstBLateTailABase, firstBTwoTailDUpper,
            parabolicOuterRootDenominator, parabolicOuterRootNumerator,
            firstBLatePrefixScale]
          (repeat' apply And.intro) <;>
            nlinarith [show (0 : ℚ) ≤ z by positivity]) root_eq
      omega

/-- Scale coefficient in the normalized leading-`b` balance. -/
def firstBZeroScaleCoefficient (x y z : Nat) : ℤ :=
  243 * (72 * y - 9) * firstBOneOuterQ x z

/-- Exact suffix coefficient after `j` leading `c` letters and the second body `b`. -/
def firstBZeroSuffixH (j x y z : Nat) : ℤ :=
  243 * (3 : ℤ) ^ j *
      (firstBZeroScaleCoefficient x y z - 39 * firstBOneOuterJ x y z) -
    39 * firstBOneOuterJ x y z

/-- A physical leading-`b` zero satisfies its exact tail-complement balance. -/
theorem firstBZero_core_balance
    (tail : List TagLetter) (x y z : Nat)
    (core_zero :
      bZeroBDefectCOneCodeCore
        ((3 : ℚ) ^ (tagEncode 3 (.b :: tail)).length)
        (ternaryCode (tagEncode 3 (.b :: tail))) x y z = 0) :
    let T : Nat := 3 ^ (tagEncode 3 tail).length
    let E : Nat := tagComplementCode tail
    ((39 * T + E : Nat) : ℤ) * firstBOneOuterJ x y z =
      (T : ℤ) * firstBZeroScaleCoefficient x y z -
        firstBOneOuterCorrection x y z := by
  let body := .b :: tail
  let T : Nat := 3 ^ (tagEncode 3 tail).length
  let E : Nat := tagComplementCode tail
  let S : Nat := 3 ^ (tagEncode 3 body).length
  let C : Nat := ternaryCode (tagEncode 3 body)
  let D : Nat := tagComplementCode body
  have scale_eq : S = 243 * T := by
    dsimp [S, T, body]
    rw [List.length_append, pow_add]
    norm_num [tagCode]
  have complement_eq : D = 39 * T + E := by
    dsimp [D, T, E, body]
    rw [tagComplementCode_cons_b]
  have code_lt : C < S := by
    dsimp [C, S, body]
    exact ternaryCode_lt_pow_length (tagEncode 3 (.b :: tail))
  have complement_nat : D = S - C - 1 := rfl
  have coordinate_sum : C + D + 1 = S := by omega
  have code_eq_int : (C : ℤ) = 243 * T - 1 - (39 * T + E) := by
    have coordinate_sum_int : (C : ℤ) + D + 1 = S := by
      exact_mod_cast coordinate_sum
    have scale_eq_int : (S : ℤ) = 243 * T := by exact_mod_cast scale_eq
    have complement_eq_int : (D : ℤ) = 39 * T + E := by
      exact_mod_cast complement_eq
    omega
  have scale_cast :
      (S : ℚ) = (3 : ℚ) ^ (tagEncode 3 (.b :: tail)).length := by
    dsimp [S, body]
    norm_num
  rw [← scale_cast] at core_zero
  change bZeroBDefectCOneCodeCore (S : ℚ) (C : ℚ) x y z = 0 at core_zero
  have core_zero_int :
      bZeroBDefectCOneCodeCore (S : ℤ) (C : ℤ) x y z = 0 := by
    unfold bZeroBDefectCOneCodeCore at core_zero ⊢
    exact_mod_cast core_zero
  rw [scale_eq, code_eq_int] at core_zero_int
  change ((39 * T + E : Nat) : ℤ) * firstBOneOuterJ x y z =
    (T : ℤ) * firstBZeroScaleCoefficient x y z -
      firstBOneOuterCorrection x y z
  push_cast at core_zero_int ⊢
  unfold bZeroBDefectCOneCodeCore at core_zero_int
  unfold firstBOneOuterJ firstBZeroScaleCoefficient
    firstBOneOuterCorrection firstBOneOuterQ
  linear_combination core_zero_int

/-- Removing the tail's first `b` turns a physical leading-`b` zero into the uniform
suffix grammar. -/
theorem firstBZeroSuffixCore_of_core_zero
    (j : Nat) (tail rest : List TagLetter) (x y z : Nat)
    (first_b : tail = List.replicate j .c ++ .b :: rest)
    (core_zero :
      bZeroBDefectCOneCodeCore
        ((3 : ℚ) ^ (tagEncode 3 (.b :: tail)).length)
        (ternaryCode (tagEncode 3 (.b :: tail))) x y z = 0) :
    FirstBOneOuterSuffixCore rest (firstBZeroSuffixH j x y z)
      (firstBOneOuterJ x y z) (firstBOneOuterCorrection x y z) := by
  let R : Nat := 3 ^ (tagEncode 3 rest).length
  let G : Nat := tagComplementCode rest
  let T : Nat := 3 ^ (tagEncode 3 tail).length
  let E : Nat := tagComplementCode tail
  have scale_eq : T = 3 ^ j * 243 * R := by
    dsimp [T, R]
    rw [first_b, tagEncode_append, List.length_append,
      firstBTwoTail_replicate_c_length, tagEncode_cons, List.length_append,
      pow_add, pow_add]
    norm_num [tagCode]
    ring
  have complement_eq : E = 39 * R + G := by
    dsimp [E, R, G]
    rw [first_b, tagComplementCode_replicate_c_append, tagComplementCode_cons_b]
  have balance := firstBZero_core_balance tail x y z core_zero
  change ((39 * T + E : Nat) : ℤ) * firstBOneOuterJ x y z =
    (T : ℤ) * firstBZeroScaleCoefficient x y z -
      firstBOneOuterCorrection x y z at balance
  rw [scale_eq, complement_eq] at balance
  dsimp [R, G] at balance
  unfold FirstBOneOuterSuffixCore FirstBOneX211SuffixCore firstBZeroSuffixH
  linear_combination balance

end MatrixMortality.ParabolicBlade
