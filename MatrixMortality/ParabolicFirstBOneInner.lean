import MatrixMortality.ParabolicFirstBOneInnerCertificate

/-!
# Large-inner extinction at outer wait 211

The exact suffix equation contracts every large-inner zero to four finite affine chambers.
The generated depth-three certificate eliminates those chambers. Together with the bounded
inner-wait theorem, this closes the physical `cb` body at outer wait 211.
-/

namespace MatrixMortality.ParabolicBlade

/-- No physical x=211 `cb` zero survives above the inner-wait threshold. -/
theorem bZeroBDefectCOneCodeCore_x211_ne_zero_of_large_inner
    (j : Nat) (tail rest : List TagLetter) (y z : Nat)
    (first_b : tail = List.replicate j .c ++ .b :: rest)
    (inner_large : 3 ^ 13 ≤ z) :
    bZeroBDefectCOneCodeCore
      ((3 : ℚ) ^ (tagEncode 3 ([.c, .b] ++ tail)).length)
      (ternaryCode (tagEncode 3 ([.c, .b] ++ tail))) 211 y z ≠ 0 := by
  intro core_zero
  have wait_positive := firstBOneX211_wait_two_le_of_core_zero tail y z core_zero
  have suffix_core :=
    firstBOneX211SuffixCore_of_core_zero j tail rest y z first_b core_zero
  have envelope :=
    firstBOneX211LargeInnerEnvelope_of_suffix_core
      j rest y z wait_positive suffix_core
  have core_zero_first_b :
      bZeroBDefectCOneCodeCore
        ((3 : ℚ) ^
          (tagEncode 3 (List.replicate 1 .c ++ .b :: tail)).length)
        (ternaryCode (tagEncode 3 (List.replicate 1 .c ++ .b :: tail)))
        211 y z = 0 := by
    simpa using core_zero
  have wait_upper :=
    bZeroBDefectCOne_y_le_of_first_b 1 tail 211 y z core_zero_first_b
  have candidate :=
    firstBOneX211LargeInnerCandidate_of_envelope
      j y z wait_upper inner_large envelope
  exact firstBOneX211SuffixCore_false_of_large_inner_candidate
    rest j y z inner_large candidate suffix_core

/-- The complete physical x=211 `cb` chamber is empty. -/
theorem bZeroBDefectCOneCodeCore_x211_ne_zero
    (j h : Nat) (tail stem rest : List TagLetter) (y z : Nat)
    (first_b : tail = List.replicate j .c ++ .b :: rest)
    (last_b : tail = stem ++ .b :: List.replicate h .c) :
    bZeroBDefectCOneCodeCore
      ((3 : ℚ) ^ (tagEncode 3 ([.c, .b] ++ tail)).length)
      (ternaryCode (tagEncode 3 ([.c, .b] ++ tail))) 211 y z ≠ 0 := by
  by_cases inner_bound : z < 3 ^ 13
  · exact bZeroBDefectCOneCodeCore_x211_ne_zero_of_inner_bound
      j h tail stem rest y z first_b last_b inner_bound
  · have inner_large : 3 ^ 13 ≤ z := by omega
    exact bZeroBDefectCOneCodeCore_x211_ne_zero_of_large_inner
      j tail rest y z first_b inner_large

/-- An even-`b` body beginning `cb` cannot zero the phase-zero right-`c` core at outer wait
211. -/
theorem bZeroBDefectCOneCodeCore_cb_x211_ne_zero_of_even_b_count
    (tail : List TagLetter)
    (b_count_even :
      (([TagLetter.c, TagLetter.b] : List TagLetter) ++ tail).count
          TagLetter.b % 2 = 0)
    (y z : Nat) :
    bZeroBDefectCOneCodeCore
      ((3 : ℚ) ^ (tagEncode 3 ([.c, .b] ++ tail)).length)
      (ternaryCode (tagEncode 3 ([.c, .b] ++ tail))) 211 y z ≠ 0 := by
  have contains_b : .b ∈ tail := by
    by_contra not_mem
    have tail_count_zero : tail.count .b = 0 := List.count_eq_zero.mpr not_mem
    simp [tail_count_zero] at b_count_even
  obtain ⟨j, rest, first_b⟩ := tagWord_first_b_decomposition tail contains_b
  obtain ⟨h, stem, last_b⟩ := tagWord_last_b_decomposition tail contains_b
  exact bZeroBDefectCOneCodeCore_x211_ne_zero
    j h tail stem rest y z first_b last_b

/-- The outer-wait-211 `cb` cylinder cannot close the residual `b | b | c` bridge when the
body has even `b` parity. -/
theorem bridge_bZero_bTwo_cOne_det_ne_zero_of_cb_x211_even_b_count
    (tail : List TagLetter)
    (b_count_even :
      (([TagLetter.c, TagLetter.b] : List TagLetter) ++ tail).count
          TagLetter.b % 2 = 0)
    (y z : Nat) :
    (bridge 27
      (bAtom 27 (3 * z) * bAtom 27 (3 * 211 + 2) *
        cAtom 27 (nearySideLowerC 3 ([.c, .b] ++ tail))
          (nearySideLowerCScale 3 ([.c, .b] ++ tail))
          (3 * y + 1))).det ≠ 0 := by
  rw [bridge_bZero_bTwo_cOne_det]
  exact mul_ne_zero (by norm_num)
    (bZeroBDefectCOneCodeCore_cb_x211_ne_zero_of_even_b_count
      tail b_count_even y z)

end MatrixMortality.ParabolicBlade
