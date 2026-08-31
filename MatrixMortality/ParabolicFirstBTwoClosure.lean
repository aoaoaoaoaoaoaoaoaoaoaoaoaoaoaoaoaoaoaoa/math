import MatrixMortality.ParabolicFirstBTwo
import MatrixMortality.ParabolicFirstBTwoTail

/-!
# Extinction of the second-first-`b` cylinder

The analytic root enclosure, exact finite outer-wait classification, tail-density certificate,
and exceptional endpoint gap compose here.  A phase-zero right-`c` body beginning `ccb` cannot
close the residual `b | b | c` bridge when its remaining tail contains `b`.
-/

namespace MatrixMortality.ParabolicBlade

/-- A body beginning `ccb` whose remaining tail contains `b` cannot zero the primitive
phase-zero right-`c` core. -/
theorem bZeroBDefectCOneCodeCore_ccb_ne_zero_of_mem_b
    (tail : List TagLetter) (contains_b : .b ∈ tail) (x y z : Nat) :
    bZeroBDefectCOneCodeCore
      ((3 : ℚ) ^ (tagEncode 3 ([.c, .c, .b] ++ tail)).length)
      (ternaryCode (tagEncode 3 ([.c, .c, .b] ++ tail))) x y z ≠ 0 := by
  intro core_zero
  by_cases y_zero : y = 0
  · subst y
    exact bZeroBDefectCOneCodeCore_ccb_ne_zero_of_y_zero tail x z core_zero
  by_cases y_one : y = 1
  · subst y
    exact bZeroBDefectCOneCodeCore_ccb_ne_zero_of_y_one tail contains_b x z core_zero
  have two_le_y : 2 ≤ y := by omega
  have envelopes :=
    firstBTwo_root_between_envelopes_of_tail tail contains_b x y z two_le_y core_zero
  have lower : firstBTwoRootLower y ≤ (x : ℚ) := by
    simpa only [firstBTwoRootLower] using envelopes.1
  have upper : (x : ℚ) ≤ firstBTwoRootUpper y := by
    have strict_upper : (x : ℚ) < firstBTwoRootUpper y := by
      simpa only [firstBTwoRootUpper] using envelopes.2
    exact strict_upper.le
  have candidate : FirstBTwoRootCandidate x y :=
    firstBTwoRootCandidate_of_bounds x y two_le_y lower upper
  have raw_root_eq := firstBTwo_z_equation_of_tail_zero tail x y z core_zero
  dsimp only at raw_root_eq
  have tail_root_eq :
      firstBTwoTailZDenominator (firstBTwoTailA tail y) (firstBTwoTailD tail) x y * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail y) (firstBTwoTailD tail) x y := by
    simpa [firstBTwoTailZDenominator, firstBTwoTailZNumerator, firstBTwoTailA,
      firstBTwoTailD, firstBTwoTailScale, firstBTwoTailComplement] using raw_root_eq
  obtain ⟨x_eq, y_eq, z_eq, rest, tail_eq⟩ :=
    firstBTwoTail_root_eq_exception tail contains_b x y z candidate tail_root_eq
  subst x
  subst y
  subst z
  subst tail
  apply bZeroBDefectCOneCodeCore_ccbccb_ne_zero_rat rest
  push_cast at core_zero
  simpa only [List.cons_append, List.nil_append] using core_zero

/-- A body beginning `ccb` and containing an even number of `b` letters cannot zero the
primitive phase-zero right-`c` core. -/
theorem bZeroBDefectCOneCodeCore_ccb_ne_zero_of_even_b_count
    (tail : List TagLetter)
    (b_count_even :
      (([TagLetter.c, TagLetter.c, TagLetter.b] : List TagLetter) ++ tail).count
          TagLetter.b % 2 = 0)
    (x y z : Nat) :
    bZeroBDefectCOneCodeCore
      ((3 : ℚ) ^ (tagEncode 3 ([.c, .c, .b] ++ tail)).length)
      (ternaryCode (tagEncode 3 ([.c, .c, .b] ++ tail))) x y z ≠ 0 := by
  have contains_b : .b ∈ tail := by
    by_contra not_mem
    have tail_count_zero : tail.count .b = 0 := List.count_eq_zero.mpr not_mem
    simp [tail_count_zero] at b_count_even
  exact bZeroBDefectCOneCodeCore_ccb_ne_zero_of_mem_b tail contains_b x y z

/-- The second-first-`b` cylinder cannot close the residual `b | b | c` bridge when its
remaining tail contains `b`. -/
theorem bridge_bZero_bTwo_cOne_det_ne_zero_of_ccb_mem_b
    (tail : List TagLetter) (contains_b : .b ∈ tail) (x y z : Nat) :
    (bridge 27
      (bAtom 27 (3 * z) * bAtom 27 (3 * x + 2) *
        cAtom 27 (nearySideLowerC 3 ([.c, .c, .b] ++ tail))
          (nearySideLowerCScale 3 ([.c, .c, .b] ++ tail))
          (3 * y + 1))).det ≠ 0 := by
  rw [bridge_bZero_bTwo_cOne_det]
  exact mul_ne_zero (by norm_num)
    (bZeroBDefectCOneCodeCore_ccb_ne_zero_of_mem_b tail contains_b x y z)

/-- The second-first-`b` cylinder cannot close the residual `b | b | c` bridge inside the
even-`b` parity rectangle. -/
theorem bridge_bZero_bTwo_cOne_det_ne_zero_of_ccb_even_b_count
    (tail : List TagLetter)
    (b_count_even :
      (([TagLetter.c, TagLetter.c, TagLetter.b] : List TagLetter) ++ tail).count
          TagLetter.b % 2 = 0)
    (x y z : Nat) :
    (bridge 27
      (bAtom 27 (3 * z) * bAtom 27 (3 * x + 2) *
        cAtom 27 (nearySideLowerC 3 ([.c, .c, .b] ++ tail))
          (nearySideLowerCScale 3 ([.c, .c, .b] ++ tail))
          (3 * y + 1))).det ≠ 0 := by
  rw [bridge_bZero_bTwo_cOne_det]
  exact mul_ne_zero (by norm_num)
    (bZeroBDefectCOneCodeCore_ccb_ne_zero_of_even_b_count tail b_count_even x y z)

end MatrixMortality.ParabolicBlade
