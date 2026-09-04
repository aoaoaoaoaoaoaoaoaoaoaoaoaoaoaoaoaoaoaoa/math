import MatrixMortality.ParabolicFirstBOneInner
import MatrixMortality.ParabolicFirstBOneOuter
import MatrixMortality.ParabolicFirstBOneOuterSuffixCertificate

/-!
# Extinction of the complete first-`b`-after-one-`c` cylinder

The outer-wait cap, endpoint extinction, uniform lower-range classification, and exact suffix
certificate compose here. No physical `cb` body whose tail contains `b` zeros the primitive
phase-zero right-`c` core.
-/

namespace MatrixMortality.ParabolicBlade

/-- A physical body beginning `cb` whose remaining tail contains `b` cannot zero the primitive
phase-zero right-`c` core. -/
theorem bZeroBDefectCOneCodeCore_cb_ne_zero_of_mem_b
    (tail : List TagLetter) (contains_b : .b ∈ tail) (x y z : Nat) :
    bZeroBDefectCOneCodeCore
      ((3 : ℚ) ^ (tagEncode 3 ([.c, .b] ++ tail)).length)
      (ternaryCode (tagEncode 3 ([.c, .b] ++ tail))) x y z ≠ 0 := by
  intro core_zero
  have x_upper := bZeroBDefectCOne_x_le_211_of_first_b_one tail x y z core_zero
  by_cases x_endpoint : x = 211
  · subst x
    obtain ⟨j, rest, first_b⟩ := tagWord_first_b_decomposition tail contains_b
    obtain ⟨h, stem, last_b⟩ := tagWord_last_b_decomposition tail contains_b
    exact bZeroBDefectCOneCodeCore_x211_ne_zero
      j h tail stem rest y z first_b last_b core_zero
  · have x_lower_range : x ≤ 210 := by omega
    obtain ⟨j, rest, first_b, candidate⟩ :=
      firstBOneOuterCandidate_of_core_zero
        tail contains_b x y z x_lower_range core_zero
    have suffix_core :=
      firstBOneOuterSuffixCore_of_core_zero
        j tail rest x y z first_b core_zero
    unfold FirstBOneOuterCandidate at candidate
    rcases candidate with c206 | c207 | c210ray | c210802 | c210812
    · rcases c206 with ⟨rfl, rfl, rfl, z_lower, z_upper⟩
      exact firstBOneOuterSuffixCore_false_206_0_162
        rest z z_lower z_upper suffix_core
    · rcases c207 with ⟨rfl, rfl, rfl, rfl⟩
      exact firstBOneOuterSuffixCore_false_207_2_202
        rest 1 (by omega) (by omega) suffix_core
    · rcases c210ray with ⟨rfl, rfl, rfl, z_lower⟩
      exact firstBOneOuterSuffixCore_false_210_1_801
        rest z z_lower suffix_core
    · rcases c210802 with ⟨rfl, rfl, rfl, rfl⟩
      exact firstBOneOuterSuffixCore_false_210_1_802
        rest 4 (by omega) (by omega) suffix_core
    · rcases c210812 with ⟨rfl, rfl, rfl, rfl⟩
      exact firstBOneOuterSuffixCore_false_210_0_812
        rest 9 (by omega) (by omega) suffix_core

/-- An even-`b` body beginning `cb` cannot zero the primitive phase-zero right-`c` core. -/
theorem bZeroBDefectCOneCodeCore_cb_ne_zero_of_even_b_count
    (tail : List TagLetter)
    (b_count_even :
      (([TagLetter.c, TagLetter.b] : List TagLetter) ++ tail).count
          TagLetter.b % 2 = 0)
    (x y z : Nat) :
    bZeroBDefectCOneCodeCore
      ((3 : ℚ) ^ (tagEncode 3 ([.c, .b] ++ tail)).length)
      (ternaryCode (tagEncode 3 ([.c, .b] ++ tail))) x y z ≠ 0 := by
  have contains_b : .b ∈ tail := by
    by_contra not_mem
    have tail_count_zero : tail.count .b = 0 := List.count_eq_zero.mpr not_mem
    simp [tail_count_zero] at b_count_even
  exact bZeroBDefectCOneCodeCore_cb_ne_zero_of_mem_b tail contains_b x y z

/-- The complete first-`b`-after-one-`c` cylinder cannot close the residual `b | b | c`
bridge when the body has even `b` parity. -/
theorem bridge_bZero_bTwo_cOne_det_ne_zero_of_cb_even_b_count
    (tail : List TagLetter)
    (b_count_even :
      (([TagLetter.c, TagLetter.b] : List TagLetter) ++ tail).count
          TagLetter.b % 2 = 0)
    (x y z : Nat) :
    (bridge 27
      (bAtom 27 (3 * z) * bAtom 27 (3 * x + 2) *
        cAtom 27 (nearySideLowerC 3 ([.c, .b] ++ tail))
          (nearySideLowerCScale 3 ([.c, .b] ++ tail))
          (3 * y + 1))).det ≠ 0 := by
  rw [bridge_bZero_bTwo_cOne_det]
  exact mul_ne_zero (by norm_num)
    (bZeroBDefectCOneCodeCore_cb_ne_zero_of_even_b_count
      tail b_count_even x y z)

end MatrixMortality.ParabolicBlade
