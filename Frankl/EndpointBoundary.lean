import Frankl.CanonicalObjective
import Frankl.SupportEndpoint
import Frankl.EndpointTrace

namespace Frankl

open Real Set

/-- Replacing a deterministic endpoint atom by the symmetric endpoint orbit at the low
diagonal preserves the marginal law and independent entropy, but can only lower Yu's
dependent entropy term. -/
theorem endpointCertificateObjective_diagonal_le_one {a : ℝ}
    (haLower : 0 ≤ a) (haUpper : a ≤ abundanceTarget) :
    endpointCertificateObjective a a ≤ endpointCertificateObjective a 1 := by
  let weight := (abundanceTarget - a) / (1 - a)
  have haOne : a < 1 :=
    haUpper.trans_lt (abundanceTarget_lt_half.trans (by norm_num))
  have hdenominator : 1 - a ≠ 0 := (sub_pos.2 haOne).ne'
  have hweight : 0 ≤ weight :=
    div_nonneg (sub_nonneg.2 haUpper) (sub_nonneg.2 haOne.le)
  have hweightOne : endpointCertificateWeight a 1 = weight := by
    dsimp only [endpointCertificateWeight, weight]
    rw [show 1 + 1 - 2 * a = 2 * (1 - a) by ring]
    field_simp [hdenominator]
    ring
  have hweightDiagonal : endpointCertificateWeight a a = 2 * weight := by
    dsimp only [endpointCertificateWeight, weight]
    rw [show 1 + a - 2 * a = 1 - a by ring]
    field_simp [hdenominator]
  have haHalf : a ≤ 1 / 2 := haUpper.trans abundanceTarget_lt_half.le
  have hdependent : 0 ≤ dependentCost a a := by
    rw [dependentCost_self_eq_cappedEntropy haHalf]
    exact binEntropy_nonneg
      (le_min (by nlinarith) (by norm_num))
      ((min_le_right (2 * a) (1 / 2)).trans (by norm_num))
  rw [← sub_nonneg]
  rw [show
      endpointCertificateObjective a 1 - endpointCertificateObjective a a =
        dependentShare * weight * dependentCost a a by
    simp only [endpointCertificateObjective, diagonalEndpointObjective, yuGap,
      hweightOne, hweightDiagonal, join_one_right, binEntropy_one]
    ring]
  exact mul_nonneg (mul_nonneg (by norm_num [dependentShare]) hweight) hdependent

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
      exact (endpointCertificateObjective_high_pos haQuarterLower haUpper hqLower hqHalf).le
  · have hdiagonal : 0 ≤ endpointCertificateObjective a a := by
      by_cases haQuarter : a ≤ 1 / 4
      · exact endpointCertificateObjective_low_nonneg
          (by norm_num; exact haLower) haQuarter (by norm_num; exact haLower)
          (haQuarter.trans (by norm_num))
      · have haQuarterLower : 1 / 4 ≤ a := (not_le.1 haQuarter).le
        exact (endpointCertificateObjective_high_pos haQuarterLower haUpper haLower
          (haUpper.trans abundanceTarget_lt_half.le)).le
    exact hdiagonal.trans (endpointCertificateObjective_diagonal_le_one haLower haUpper)

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
