import Frankl.CanonicalObjective
import Frankl.CenteredEndpoint
import Frankl.EndpointTrace

namespace Frankl

open Real Set

private theorem endpointConditionalMean_ge_core_of_large_a {a q : ℝ}
    (haLower : 13 / 40 ≤ a) (haUpper : a ≤ abundanceTarget) (hqLower : 0 ≤ q) :
    endpointCoreThreshold ≤ endpointConditionalMean a q := by
  have hdenominator : 0 < 1 + q - a - abundanceTarget := by
    nlinarith [abundanceTarget_lt_half]
  rw [endpointConditionalMean]
  apply (le_div_iff₀ hdenominator).2
  norm_num [endpointCoreThreshold, abundanceTarget] at haLower haUpper ⊢
  nlinarith

private theorem endpointConditionalMean_ge_core_of_large_q {a q : ℝ}
    (haLower : 1 / 4 ≤ a) (haUpper : a ≤ abundanceTarget)
    (hqLower : 31 / 100 ≤ q) :
    endpointCoreThreshold ≤ endpointConditionalMean a q := by
  have hdenominator : 0 < 1 + q - a - abundanceTarget := by
    nlinarith [abundanceTarget_lt_half]
  rw [endpointConditionalMean]
  apply (le_div_iff₀ hdenominator).2
  norm_num [endpointCoreThreshold, abundanceTarget] at haLower haUpper hqLower ⊢
  nlinarith

/-- Every canonical endpoint law allowed by half support has nonnegative certificate objective
at the abundance target. -/
theorem endpointCertificateObjective_nonneg {a q : ℝ}
    (haLower : 0 ≤ a) (haUpper : a ≤ abundanceTarget)
    (hqLower : 0 ≤ q) (hqUpper : q ≤ 1)
    (hqRange : q ≤ 1 / 2 ∨ q = 1) :
    0 ≤ endpointCertificateObjective a q := by
  rcases hqRange with hqHalf | rfl
  · by_cases haQuarter : a ≤ 1 / 4
    · exact endpointCertificateObjective_low_nonneg
        (by norm_num; exact haLower) haQuarter (by norm_num; exact hqLower) hqHalf
    · have haQuarterLower : 1 / 4 ≤ a := (not_le.1 haQuarter).le
      by_cases haResidual : a ≤ 13 / 40
      · by_cases hqResidual : q ≤ 31 / 100
        · exact endpointCertificateObjective_residual_nonneg
            haQuarterLower haResidual (by norm_num; exact hqLower) hqResidual
        · exact (endpointCertificateObjective_core_pos haQuarterLower haUpper hqLower
            hqHalf (endpointConditionalMean_ge_core_of_large_q haQuarterLower haUpper
              (not_le.1 hqResidual).le)).le
      · exact (endpointCertificateObjective_core_pos haQuarterLower haUpper hqLower
          hqHalf (endpointConditionalMean_ge_core_of_large_a
            (not_le.1 haResidual).le haUpper hqLower)).le
  · by_cases haCorner : a ≤ 1 / 1000
    · exact CertificateCorner.endpointCertificateObjective_one_corner
        haLower haCorner (by norm_num) (by norm_num)
    · exact endpointCertificateObjective_qOne_nonneg
        (not_le.1 haCorner).le haUpper (by norm_num) (by norm_num)

private theorem singleLowOrbitYuGap_nonneg :
    0 ≤ orbitYuGap (singleLowOrbitLaw abundanceTarget 0) := by
  have hgap : orbitYuGap (singleLowOrbitLaw abundanceTarget 0) =
      diagonalPairObjective 1 0 abundanceTarget abundanceTarget := by
    classical
    simp [orbitYuGap, orbitIndependentEntropy, orbitMarginalEntropy,
      orbitDependentEntropy, finiteJoinEntropy, finiteExpectation, orbitMarginalWeight,
      orbitMarginalPoint, singleLowOrbitLaw, diagonalPairObjective, Fintype.sum_prod_type,
      Fintype.sum_bool]
    ring_nf
  rw [hgap]
  exact diagonalPairObjective_point_nonneg

/-- Yu's strict affine entropy gap is nonnegative for every finite symmetric orbit law of
mean at most the abundance target. -/
theorem orbitYuGap_nonneg {index : Type*} [Fintype index]
    {left right : index → ℝ} {source : ℝ}
    (hleft : ∀ i, left i ∈ Icc (0 : ℝ) 1)
    (hright : ∀ i, right i ∈ Icc (0 : ℝ) 1)
    (law : FiniteOrbitLaw left right source)
    (hsourceTarget : source ≤ abundanceTarget) :
    0 ≤ orbitYuGap law := by
  apply orbitYuGap_nonneg_of_canonical_families hleft hright law hsourceTarget
      singleLowOrbitYuGap_nonneg
  · intro a b haTarget htargetB hab haLower hbUpper
    rw [orbitYuGap_twoLowDiagonal_eq_objective haTarget htargetB hab]
    exact diagonalPairObjective_nonneg
      (lowerOrbitWeight_nonneg htargetB hab)
      (upperOrbitWeight_nonneg haTarget hab)
      (orbitWeights_sum hab)
      ⟨haLower, haTarget.trans abundanceTarget_lt_half.le⟩
      ⟨by
        have htargetPositive : 0 < abundanceTarget := by norm_num [abundanceTarget]
        exact htargetPositive.le.trans htargetB, hbUpper⟩
      (orbitWeights_mean hab)
  · intro a q haTarget htargetEndpoint haEndpoint haLower hqLower hqUpper hqRange
    rw [← endpointCertificateObjective_eq_orbitYuGap
      haTarget htargetEndpoint haEndpoint hqLower hqUpper]
    exact endpointCertificateObjective_nonneg haLower haTarget hqLower hqUpper hqRange

end Frankl
