import MatrixMortality.ParabolicFirstBOneOuterCertificate

/-!
# Uniform lower-range classification of the `cb` cylinder

The rational outer-root window reduces every physical zero with `x ≤ 210` to 113 exact
`(x,y)` pairs. First-`b` density rectangles then leave only five explicit suffix chambers.
-/

namespace MatrixMortality.ParabolicBlade

/-- Every physical `cb` zero below outer wait 211 lies in one of five exact tail chambers. -/
theorem firstBOneOuterCandidate_of_core_zero
    (tail : List TagLetter) (contains_b : .b ∈ tail) (x y z : Nat)
    (x_upper : x ≤ 210)
    (core_zero :
      bZeroBDefectCOneCodeCore
        ((3 : ℚ) ^ (tagEncode 3 ([.c, .b] ++ tail)).length)
        (ternaryCode (tagEncode 3 ([.c, .b] ++ tail))) x y z = 0) :
    ∃ j rest,
      tail = List.replicate j .c ++ .b :: rest ∧
        FirstBOneOuterCandidate x j y z := by
  obtain ⟨j, rest, first_b⟩ := tagWord_first_b_decomposition tail contains_b
  have root_candidate :=
    firstBOneOuterRootCandidate_of_core_zero
      tail contains_b x y z x_upper core_zero
  have raw_root_eq := firstBOneOuter_z_equation_of_core_zero tail x y z core_zero
  dsimp only at raw_root_eq
  have root_eq :
      let decomposed_tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBOneOuterA decomposed_tail y)
          (firstBOneOuterD decomposed_tail) x y * z =
        firstBTwoTailZNumerator (firstBOneOuterA decomposed_tail y)
          (firstBOneOuterD decomposed_tail) x y := by
    simpa only [first_b] using raw_root_eq
  exact ⟨j, rest, first_b,
    firstBOneOuterCandidate_of_root_candidate
      j rest x y z root_candidate root_eq⟩

end MatrixMortality.ParabolicBlade
