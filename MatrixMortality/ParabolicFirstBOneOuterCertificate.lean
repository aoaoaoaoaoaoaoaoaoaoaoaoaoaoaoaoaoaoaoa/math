import MatrixMortality.ParabolicFirstBOneOuterCertificate0
import MatrixMortality.ParabolicFirstBOneOuterCertificate1
import MatrixMortality.ParabolicFirstBOneOuterCertificate2
import MatrixMortality.ParabolicFirstBOneOuterCertificate3
import MatrixMortality.ParabolicFirstBOneOuterCertificate4

/-!
# Exact tail classification after the initial cb

This generated aggregate dispatches the 113 outer-root pairs to five exact certificate
shards.
-/

namespace MatrixMortality.ParabolicBlade

-- BEGIN GENERATED FIRST-B-ONE-OUTER TAIL CERTIFICATE

/-- The 113 outer-root pairs refine to exactly five integral tail chambers. -/
theorem firstBOneOuterCandidate_of_root_candidate
    (j : Nat) (rest : List TagLetter) (x y z : Nat)
    (candidate : FirstBOneOuterRootCandidate x y)
    (root_eq :
      let tail := List.replicate j .c ++ .b :: rest
      firstBTwoTailZDenominator (firstBOneOuterA tail y)
          (firstBOneOuterD tail) x y * z =
        firstBTwoTailZNumerator (firstBOneOuterA tail y)
          (firstBOneOuterD tail) x y) :
    FirstBOneOuterCandidate x j y z := by
  by_cases x_lower : x ≤ 206
  · exact firstBOneOuter_candidate_shard_0 j rest x y z candidate x_lower root_eq
  by_cases x_middle : x ≤ 209
  · have chamber_range : 207 ≤ x ∧ x ≤ 209 := by omega
    exact firstBOneOuter_candidate_shard_1 j rest x y z candidate chamber_range root_eq
  have x_eq : x = 210 := by
    unfold FirstBOneOuterRootCandidate at candidate
    omega
  by_cases y_lower : y ≤ 816
  · exact firstBOneOuter_candidate_shard_2 j rest x y z candidate ⟨x_eq, y_lower⟩ root_eq
  by_cases y_middle : y ≤ 837
  · have chamber_range : x = 210 ∧ 817 ≤ y ∧ y ≤ 837 := by omega
    exact firstBOneOuter_candidate_shard_3 j rest x y z candidate chamber_range root_eq
  have chamber_range : x = 210 ∧ 838 ≤ y := by omega
  exact firstBOneOuter_candidate_shard_4 j rest x y z candidate chamber_range root_eq

-- END GENERATED FIRST-B-ONE-OUTER TAIL CERTIFICATE

end MatrixMortality.ParabolicBlade
