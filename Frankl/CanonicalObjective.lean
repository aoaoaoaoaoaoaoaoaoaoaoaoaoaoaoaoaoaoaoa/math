import Frankl.OrbitClassification

namespace Frankl

open Real Set

/-- Yu's objective on two diagonal orbits with explicitly supplied masses. -/
noncomputable def diagonalPairObjective
    (lowerWeight upperWeight lowerMean upperMean : ℝ) : ℝ :=
  yuGap
    (lowerWeight ^ 2 * binEntropy (join lowerMean lowerMean)
      + 2 * lowerWeight * upperWeight * binEntropy (join lowerMean upperMean)
      + upperWeight ^ 2 * binEntropy (join upperMean upperMean))
    (lowerWeight * binEntropy lowerMean + upperWeight * binEntropy upperMean)
    (lowerWeight * dependentCost lowerMean lowerMean
      + upperWeight * dependentCost upperMean upperMean)

/-- Yu's objective on a diagonal orbit and an endpoint orbit `(q, 1)`. -/
noncomputable def diagonalEndpointObjective
    (lowerWeight upperWeight lowerMean q : ℝ) : ℝ :=
  yuGap
    (lowerWeight ^ 2 * binEntropy (join lowerMean lowerMean)
      + lowerWeight * upperWeight * binEntropy (join lowerMean q)
      + upperWeight ^ 2 / 4 * binEntropy (join q q))
    (lowerWeight * binEntropy lowerMean + upperWeight / 2 * binEntropy q)
    (lowerWeight * dependentCost lowerMean lowerMean)

/-- The mass of the endpoint orbit in the rational certificate coordinates. -/
noncomputable def endpointCertificateWeight (a q : ℝ) : ℝ :=
  2 * (abundanceTarget - a) / (1 + q - 2 * a)

/-- The bivariate diagonal–endpoint objective certified by interval arithmetic. -/
noncomputable def endpointCertificateObjective (a q : ℝ) : ℝ :=
  let upperWeight := endpointCertificateWeight a q
  diagonalEndpointObjective (1 - upperWeight) upperWeight a q

/-- Lower-weight certificate coordinates for two diagonal orbits. -/
noncomputable def lowerRegionLowerMean (upperWeight displacement : ℝ) : ℝ :=
  abundanceTarget
    - upperWeight * (displacement * (1 / 2 - abundanceTarget) / (1 - upperWeight))

/-- Upper mean in the lower-weight certificate coordinates. -/
noncomputable def lowerRegionUpperMean (displacement : ℝ) : ℝ :=
  abundanceTarget + displacement * (1 / 2 - abundanceTarget)

/-- The diagonal–diagonal objective on the region `upperWeight ≤ 2 * abundanceTarget`. -/
noncomputable def lowerRegionDiagonalObjective (upperWeight displacement : ℝ) : ℝ :=
  diagonalPairObjective (1 - upperWeight) upperWeight
    (lowerRegionLowerMean upperWeight displacement)
    (lowerRegionUpperMean displacement)

/-- Lower mean in the certificate coordinates `2 * abundanceTarget ≤ upperWeight`. -/
noncomputable def upperRegionLowerMean (displacement : ℝ) : ℝ :=
  abundanceTarget * (1 - displacement)

/-- Upper mean in the certificate coordinates `2 * abundanceTarget ≤ upperWeight`. -/
noncomputable def upperRegionUpperMean (upperWeight displacement : ℝ) : ℝ :=
  abundanceTarget
    + (1 - upperWeight) * (displacement * abundanceTarget / upperWeight)

/-- The diagonal–diagonal objective on the region `2 * abundanceTarget ≤ upperWeight`. -/
noncomputable def upperRegionDiagonalObjective (upperWeight displacement : ℝ) : ℝ :=
  diagonalPairObjective (1 - upperWeight) upperWeight
    (upperRegionLowerMean displacement)
    (upperRegionUpperMean upperWeight displacement)

theorem dependentCost_self_eq_cappedEntropy {p : ℝ} (hpHalf : p ≤ 1 / 2) :
    dependentCost p p = binEntropy (min (2 * p) (1 / 2)) := by
  rw [dependentCost, dependentParameter, max_self, max_eq_right hpHalf]
  congr 2
  ring_nf

theorem dependentCost_endpoint_eq_zero {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    dependentCost q 1 = 0 := by
  rw [dependentCost, dependentParameter, max_eq_right hq₁,
    max_eq_left (show (1 : ℝ) ≥ 1 / 2 by norm_num),
    min_eq_right (by linarith : (1 : ℝ) ≤ q + 1), binEntropy_one]

theorem orbitYuGap_twoLowDiagonal_eq_objective {a target b : ℝ}
    (haTarget : a ≤ target) (htargetB : target ≤ b) (hab : a < b) :
    orbitYuGap (twoLowOrbitLaw a 0 target b 0 haTarget htargetB hab) =
      diagonalPairObjective (lowerOrbitWeight a target b)
        (upperOrbitWeight a target b) a b := by
  classical
  simp [orbitYuGap, orbitIndependentEntropy, orbitMarginalEntropy,
    orbitDependentEntropy, finiteJoinEntropy, finiteExpectation, orbitMarginalWeight,
    orbitMarginalPoint, twoLowOrbitLaw, twoOrbitWeight, twoLowOrbitLeft,
    twoLowOrbitRight, diagonalPairObjective, Fintype.sum_prod_type, join_comm]
  ring_nf

theorem orbitYuGap_lowEndpointDiagonal_eq_objective {a target q : ℝ}
    (haTarget : a ≤ target) (htargetEndpoint : target ≤ endpointOrbitMean q)
    (haEndpoint : a < endpointOrbitMean q) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    orbitYuGap
        (lowEndpointOrbitLaw a 0 target q haTarget htargetEndpoint haEndpoint) =
      diagonalEndpointObjective (lowerOrbitWeight a target (endpointOrbitMean q))
        (upperOrbitWeight a target (endpointOrbitMean q)) a q := by
  classical
  have hendpoint := dependentCost_endpoint_eq_zero hq₀ hq₁
  simp [orbitYuGap, orbitIndependentEntropy, orbitMarginalEntropy,
    orbitDependentEntropy, finiteJoinEntropy, finiteExpectation, orbitMarginalWeight,
    orbitMarginalPoint, lowEndpointOrbitLaw, twoOrbitWeight, lowEndpointOrbitLeft,
    lowEndpointOrbitRight, diagonalEndpointObjective, Fintype.sum_prod_type, join_comm,
    hendpoint]
  ring_nf

theorem endpointCertificateWeight_eq_upperOrbitWeight {a q : ℝ}
    (haEndpoint : a < endpointOrbitMean q) :
    endpointCertificateWeight a q =
      upperOrbitWeight a abundanceTarget (endpointOrbitMean q) := by
  have hdenominator : 1 + q - 2 * a ≠ 0 := by
    dsimp [endpointOrbitMean] at haEndpoint
    linarith
  unfold endpointCertificateWeight upperOrbitWeight
  rw [show endpointOrbitMean q - a = (1 + q - 2 * a) / 2 by
    dsimp [endpointOrbitMean]
    ring]
  field_simp [hdenominator]

theorem endpointCertificateObjective_eq_orbitYuGap {a q : ℝ}
    (haTarget : a ≤ abundanceTarget)
    (htargetEndpoint : abundanceTarget ≤ endpointOrbitMean q)
    (haEndpoint : a < endpointOrbitMean q) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    endpointCertificateObjective a q =
      orbitYuGap
        (lowEndpointOrbitLaw a 0 abundanceTarget q haTarget htargetEndpoint haEndpoint) := by
  have hweight := endpointCertificateWeight_eq_upperOrbitWeight haEndpoint
  have hsum := orbitWeights_sum (a := a) (t := abundanceTarget)
    (b := endpointOrbitMean q) haEndpoint
  rw [orbitYuGap_lowEndpointDiagonal_eq_objective haTarget htargetEndpoint haEndpoint hq₀ hq₁]
  simp only [endpointCertificateObjective, hweight]
  congr 2
  linarith

end Frankl
