import MatrixMortality.ParabolicFirstBLateBoundary
import MatrixMortality.ParabolicFirstBLateCertificate

/-!
# Extinction of later first-`b` cylinders

The exact outer-root classifier, generated tail certificate, and two endpoint density gaps
compose here to eliminate first-`b` positions three through eleven.
-/

namespace MatrixMortality.ParabolicBlade

/-- The zero-middle-wait face of every later first-`b` cylinder is empty. -/
theorem bZeroBDefectCOneCodeCore_late_ne_zero_of_y_zero
    (k : Nat) (tail : List TagLetter) (contains_b : .b ∈ tail)
    (x z : Nat) (three_le_k : 3 ≤ k) (k_le : k ≤ 11) :
    bZeroBDefectCOneCodeCore
      ((3 : ℚ) ^
        (tagEncode 3 (List.replicate k .c ++ .b :: tail)).length)
      (ternaryCode (tagEncode 3 (List.replicate k .c ++ .b :: tail))) x 0 z ≠ 0 := by
  intro core_zero
  have outer_root_raw := firstBLateTail_outer_root_eq_of_core_zero
    k tail x 0 z core_zero
  have inner_root_raw := firstBLateTail_inner_root_eq_of_core_zero
    k tail x 0 z core_zero
  obtain ⟨j, rest, tail_eq⟩ := firstBTwoTail_first_b_decomposition tail contains_b
  have outer_root : parabolicOuterRootDenominator
      (firstBLateTailA k (List.replicate j .c ++ .b :: rest) 0)
      (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) z * x =
        parabolicOuterRootNumerator
          (firstBLateTailA k (List.replicate j .c ++ .b :: rest) 0)
          (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) 0 z := by
    simpa only [tail_eq, Nat.cast_zero] using outer_root_raw
  have inner_root : firstBTwoTailZDenominator
      (firstBLateTailA k (List.replicate j .c ++ .b :: rest) 0)
      (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) x 0 * z =
        firstBTwoTailZNumerator
          (firstBLateTailA k (List.replicate j .c ++ .b :: rest) 0)
          (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) x 0 := by
    simpa only [tail_eq] using inner_root_raw
  by_cases k_small : k ≤ 4
  · exact bZeroBDefectCOneCodeCore_late_ne_zero_of_y_zero_small
      k tail x z three_le_k k_small core_zero
  · have five_le_k : 5 ≤ k := by omega
    rcases firstBLate_y_zero_outer_cases
      k j rest x z five_le_k k_le outer_root with k_five | k_eight
    · rcases k_five with ⟨rfl, rfl⟩
      obtain ⟨rfl, rfl⟩ := firstBLate_y_zero_k_five_tail_case j rest z inner_root
      exact bZeroBDefectCOneCodeCore_cccccbcb_ne_zero rest (by
        simpa [tail_eq, List.replicate_succ] using core_zero)
    · rcases k_eight with ⟨rfl, rfl⟩
      exact firstBLate_y_zero_k_eight_false j rest z inner_root

/-- The one-middle-wait face of every later first-`b` cylinder is empty. -/
theorem bZeroBDefectCOneCodeCore_late_ne_zero_of_y_one
    (k : Nat) (tail : List TagLetter) (contains_b : .b ∈ tail)
    (x z : Nat) (three_le_k : 3 ≤ k) (k_le : k ≤ 11) :
    bZeroBDefectCOneCodeCore
      ((3 : ℚ) ^
        (tagEncode 3 (List.replicate k .c ++ .b :: tail)).length)
      (ternaryCode (tagEncode 3 (List.replicate k .c ++ .b :: tail))) x 1 z ≠ 0 := by
  intro core_zero
  have outer_root_raw := firstBLateTail_outer_root_eq_of_core_zero
    k tail x 1 z core_zero
  have inner_root_raw := firstBLateTail_inner_root_eq_of_core_zero
    k tail x 1 z core_zero
  obtain ⟨j, rest, tail_eq⟩ := firstBTwoTail_first_b_decomposition tail contains_b
  have outer_root : parabolicOuterRootDenominator
      (firstBLateTailA k (List.replicate j .c ++ .b :: rest) 1)
      (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) z * x =
        parabolicOuterRootNumerator
          (firstBLateTailA k (List.replicate j .c ++ .b :: rest) 1)
          (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) 1 z := by
    simpa only [tail_eq, Nat.cast_one] using outer_root_raw
  have inner_root : firstBTwoTailZDenominator
      (firstBLateTailA k (List.replicate j .c ++ .b :: rest) 1)
      (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) x 1 * z =
        firstBTwoTailZNumerator
          (firstBLateTailA k (List.replicate j .c ++ .b :: rest) 1)
          (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) x 1 := by
    simpa only [tail_eq] using inner_root_raw
  obtain ⟨rfl, rfl⟩ :=
    firstBLate_y_one_outer_case k j rest x z three_le_k k_le outer_root
  obtain ⟨rfl, rfl⟩ := firstBLate_y_one_tail_case j rest z inner_root
  exact bZeroBDefectCOneCodeCore_ccccbb_ne_zero rest (by
    simpa [tail_eq, List.replicate_succ] using core_zero)

/-- Every later first-`b` cylinder is empty when the middle wait is at least two. -/
theorem bZeroBDefectCOneCodeCore_late_ne_zero_of_two_le_y
    (k : Nat) (tail : List TagLetter) (contains_b : .b ∈ tail)
    (x y z : Nat) (three_le_k : 3 ≤ k) (k_le : k ≤ 11) (two_le_y : 2 ≤ y) :
    bZeroBDefectCOneCodeCore
      ((3 : ℚ) ^
        (tagEncode 3 (List.replicate k .c ++ .b :: tail)).length)
      (ternaryCode (tagEncode 3 (List.replicate k .c ++ .b :: tail))) x y z ≠ 0 := by
  intro core_zero
  have inner_root_raw := firstBLateTail_inner_root_eq_of_core_zero
    k tail x y z core_zero
  have candidate := firstBLateRootCandidate_of_core_zero
    k tail contains_b x y z three_le_k k_le two_le_y core_zero
  obtain ⟨j, rest, tail_eq⟩ := firstBTwoTail_first_b_decomposition tail contains_b
  have inner_root : firstBTwoTailZDenominator
      (firstBLateTailA k (List.replicate j .c ++ .b :: rest) y)
      (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) x y * z =
        firstBTwoTailZNumerator
          (firstBLateTailA k (List.replicate j .c ++ .b :: rest) y)
          (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) x y := by
    simpa only [tail_eq] using inner_root_raw
  exact firstBLateTail_false_of_candidate k j rest x y z candidate inner_root

/-- A physical phase-zero right-`c` core cannot vanish when its first body `b` follows three
through eleven leading `c` letters and its suffix contains another `b`. -/
theorem bZeroBDefectCOneCodeCore_late_ne_zero_of_mem_b
    (k : Nat) (tail : List TagLetter) (contains_b : .b ∈ tail)
    (x y z : Nat) (three_le_k : 3 ≤ k) (k_le : k ≤ 11) :
    bZeroBDefectCOneCodeCore
      ((3 : ℚ) ^
        (tagEncode 3 (List.replicate k .c ++ .b :: tail)).length)
      (ternaryCode (tagEncode 3 (List.replicate k .c ++ .b :: tail))) x y z ≠ 0 := by
  by_cases y_zero : y = 0
  · subst y
    exact bZeroBDefectCOneCodeCore_late_ne_zero_of_y_zero
      k tail contains_b x z three_le_k k_le
  by_cases y_one : y = 1
  · subst y
    exact bZeroBDefectCOneCodeCore_late_ne_zero_of_y_one
      k tail contains_b x z three_le_k k_le
  have two_le_y : 2 ≤ y := by omega
  exact bZeroBDefectCOneCodeCore_late_ne_zero_of_two_le_y
    k tail contains_b x y z three_le_k k_le two_le_y

/-- An even-`b` body whose first `b` is at a position from three through eleven cannot zero
the primitive phase-zero right-`c` core. -/
theorem bZeroBDefectCOneCodeCore_late_ne_zero_of_even_b_count
    (k : Nat) (tail : List TagLetter)
    (b_count_even :
      (List.replicate k TagLetter.c ++ .b :: tail).count TagLetter.b % 2 = 0)
    (x y z : Nat) (three_le_k : 3 ≤ k) (k_le : k ≤ 11) :
    bZeroBDefectCOneCodeCore
      ((3 : ℚ) ^
        (tagEncode 3 (List.replicate k .c ++ .b :: tail)).length)
      (ternaryCode (tagEncode 3 (List.replicate k .c ++ .b :: tail))) x y z ≠ 0 := by
  have contains_b : .b ∈ tail := by
    by_contra not_mem
    have tail_count_zero : tail.count .b = 0 := List.count_eq_zero.mpr not_mem
    simp [List.count_replicate, tail_count_zero] at b_count_even
  exact bZeroBDefectCOneCodeCore_late_ne_zero_of_mem_b
    k tail contains_b x y z three_le_k k_le

/-- No even-`b` body whose first `b` is at a position from three through eleven closes the
residual `b | b | c` bridge. -/
theorem bridge_bZero_bTwo_cOne_det_ne_zero_of_late_even_b_count
    (k : Nat) (tail : List TagLetter)
    (b_count_even :
      (List.replicate k TagLetter.c ++ .b :: tail).count TagLetter.b % 2 = 0)
    (x y z : Nat) (three_le_k : 3 ≤ k) (k_le : k ≤ 11) :
    (bridge 27
      (bAtom 27 (3 * z) * bAtom 27 (3 * x + 2) *
        cAtom 27 (nearySideLowerC 3 (List.replicate k .c ++ .b :: tail))
          (nearySideLowerCScale 3 (List.replicate k .c ++ .b :: tail))
          (3 * y + 1))).det ≠ 0 := by
  rw [bridge_bZero_bTwo_cOne_det]
  exact mul_ne_zero (by norm_num)
    (bZeroBDefectCOneCodeCore_late_ne_zero_of_even_b_count
      k tail b_count_even x y z three_le_k k_le)

end MatrixMortality.ParabolicBlade
