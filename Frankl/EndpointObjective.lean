import Frankl.DiagonalObjective

namespace Frankl

open Real Set

/-- Conditional low-mean threshold above which endpoint contraction is slack-feasible. -/
noncomputable def endpointCoreThreshold : ℝ := 13 / 50

/-- Mean of the two low coordinate values after conditioning an endpoint law away from its
deterministic coordinate. -/
noncomputable def endpointConditionalMean (a q : ℝ) : ℝ :=
  (a * (1 - 2 * abundanceTarget) + abundanceTarget * q) /
    (1 + q - a - abundanceTarget)

/-- Support-aware contraction coefficient for a conditioned endpoint law. -/
noncomputable def endpointSupportContractionCoefficient (support center : ℝ) : ℝ :=
  (1 - dependentShare) * targetComplement *
    (support / join support center + (1 - 4 * center / 3) / (1 - center))

/-- Saturated centered objective inherited from an endpoint law whose diagonal atom is at least
one quarter. -/
noncomputable def endpointSaturatedCenteredObjective (center : ℝ) : ℝ :=
  let lowMass := targetComplement / (1 - center)
  let leftWeight := (1 - 2 * abundanceTarget + center) / targetComplement
  (1 - dependentShare) * lowMass ^ 2 * binEntropy (join center center) +
    dependentShare * (lowMass * leftWeight * log 2) -
    (1 + entropySlack) * lowMass * binEntropy center

/-- The endpoint independent-loss coefficient fits inside the strict marginal slack throughout
the core low-mean interval. -/
theorem endpointCore_coefficient {center : ℝ}
    (hcenterLower : endpointCoreThreshold ≤ center)
    (hcenterUpper : center ≤ 1 / 2) :
    (1 - dependentShare) * ((1 - abundanceTarget) / (1 - center)) *
          ((1 - center) / (1 + center) + (1 - 4 * center / 3)) ≤
        1 + entropySlack := by
  have hcenterOne : center < 1 := hcenterUpper.trans_lt (by norm_num)
  have hleftPositive : 0 < 1 - center := sub_pos.2 hcenterOne
  have hrightPositive : 0 < 1 + center := by
    have hcenterPositive : 0 < center := by
      exact (show (0 : ℝ) < endpointCoreThreshold by
        norm_num [endpointCoreThreshold]).trans_le hcenterLower
    linarith
  rw [show
    (1 - dependentShare) * ((1 - abundanceTarget) / (1 - center)) *
          ((1 - center) / (1 + center) + (1 - 4 * center / 3)) =
        ((1 - dependentShare) * (1 - abundanceTarget) *
          ((1 - center) + (1 - 4 * center / 3) * (1 + center))) /
            ((1 - center) * (1 + center)) by
      field_simp [hleftPositive.ne', hrightPositive.ne']
      left
      ring]
  apply (div_le_iff₀ (mul_pos hleftPositive hrightPositive)).2
  norm_num [dependentShare, abundanceTarget, entropySlack, endpointCoreThreshold] at hcenterLower ⊢
  nlinarith

/-- A low endpoint law dominates the saturated objective at its conditional mean whenever
the support-aware independent entropy loss fits inside the marginal slack. -/
theorem diagonalEndpointObjective_saturated_center_le
    {lowMass leftWeight rightWeight lower center upper support : ℝ}
    (hlowMass : 0 ≤ lowMass)
    (hleftWeight : 0 ≤ leftWeight) (hrightWeight : 0 ≤ rightWeight)
    (hweight : leftWeight + rightWeight = 1)
    (hlower : lower ∈ Icc (1 / 4 : ℝ) support)
    (hcenter : center ∈ Icc (0 : ℝ) (1 / 2))
    (hupper : upper ∈ Icc (0 : ℝ) support)
    (hsupport₀ : 0 < support) (hsupportHalf : support ≤ 1 / 2)
    (hmean : leftWeight * lower + rightWeight * upper = center)
    (hcoefficient :
      (1 - dependentShare) * lowMass *
          (support * (1 - center) / join support center + (1 - 4 * center / 3)) ≤
        1 + entropySlack) :
    (1 - dependentShare) * lowMass ^ 2 * binEntropy (join center center) +
        dependentShare * (lowMass * leftWeight * log 2) -
        (1 + entropySlack) * lowMass * binEntropy center ≤
      diagonalEndpointObjective (lowMass * leftWeight) (2 * lowMass * rightWeight)
        lower upper := by
  let deficit := binarySpreadDeficit binEntropy leftWeight rightWeight lower upper
  let spreadIndependent :=
    leftWeight ^ 2 * binEntropy (join lower lower) +
      2 * leftWeight * rightWeight * binEntropy (join lower upper) +
      rightWeight ^ 2 * binEntropy (join upper upper)
  let spreadMarginal := leftWeight * binEntropy lower + rightWeight * binEntropy upper
  let centeredIndependent := binEntropy (join center center)
  have hdeficit : deficit = binEntropy center - spreadMarginal := by
    dsimp only [deficit, spreadMarginal, binarySpreadDeficit]
    rw [hmean]
  have hdeficitNonneg : 0 ≤ deficit :=
    binarySpreadDeficit_nonneg hleftWeight hrightWeight hweight
      ⟨hlower.1.trans' (by norm_num), hlower.2.trans hsupportHalf |>.trans (by norm_num)⟩
      ⟨hupper.1, hupper.2.trans hsupportHalf |>.trans (by norm_num)⟩
  have hindependent :
      centeredIndependent - spreadIndependent ≤
        (support * (1 - center) / join support center +
          (1 - 4 * center / 3)) * deficit := by
    simpa only [centeredIndependent, spreadIndependent, deficit] using
      diagonalIndependent_deficit_le_support hleftWeight hrightWeight hweight
        ⟨hlower.1.trans' (by norm_num), hlower.2⟩ hcenter hupper
        hsupport₀ hsupportHalf hmean
  have hindependentShare : 0 ≤ 1 - dependentShare := by
    norm_num [dependentShare]
  have hscale : 0 ≤ (1 - dependentShare) * lowMass ^ 2 :=
    mul_nonneg hindependentShare (sq_nonneg lowMass)
  have hindependentScaled := mul_le_mul_of_nonneg_left hindependent hscale
  have hmarginScale : 0 ≤ lowMass * deficit :=
    mul_nonneg hlowMass hdeficitNonneg
  have hcoefficientScaled :=
    mul_le_mul_of_nonneg_right hcoefficient hmarginScale
  have htotal :
      (1 - dependentShare) * lowMass ^ 2 *
          (centeredIndependent - spreadIndependent) ≤
        (1 + entropySlack) * lowMass * deficit := by
    calc
      (1 - dependentShare) * lowMass ^ 2 *
            (centeredIndependent - spreadIndependent) ≤
          (1 - dependentShare) * lowMass ^ 2 *
            ((support * (1 - center) / join support center +
              (1 - 4 * center / 3)) * deficit) :=
        hindependentScaled
      _ = ((1 - dependentShare) * lowMass *
            (support * (1 - center) / join support center +
              (1 - 4 * center / 3))) *
          (lowMass * deficit) := by ring
      _ ≤ (1 + entropySlack) * (lowMass * deficit) := hcoefficientScaled
      _ = (1 + entropySlack) * lowMass * deficit := by ring
  have hlowerDependent : dependentCost lower lower = log 2 := by
    rw [dependentCost_self_eq_cappedEntropy (hlower.2.trans hsupportHalf),
      min_eq_right (by norm_num at hlower ⊢; linarith)]
    simpa only [one_div] using binEntropy_two_inv
  have hspreadIndependentScale :
      (lowMass * leftWeight) ^ 2 * binEntropy (join lower lower) +
          lowMass * leftWeight * (2 * lowMass * rightWeight) *
            binEntropy (join lower upper) +
          (2 * lowMass * rightWeight) ^ 2 / 4 *
            binEntropy (join upper upper) =
        lowMass ^ 2 * spreadIndependent := by
    dsimp only [spreadIndependent]
    ring
  have hspreadMarginalScale :
      lowMass * leftWeight * binEntropy lower +
          2 * lowMass * rightWeight / 2 * binEntropy upper =
        lowMass * spreadMarginal := by
    dsimp only [spreadMarginal]
    ring
  have hspreadObjective :
      diagonalEndpointObjective (lowMass * leftWeight) (2 * lowMass * rightWeight)
          lower upper =
        (1 - dependentShare) * lowMass ^ 2 * spreadIndependent +
          dependentShare * (lowMass * leftWeight * log 2) -
          (1 + entropySlack) * lowMass * spreadMarginal := by
    unfold diagonalEndpointObjective yuGap
    rw [hlowerDependent]
    rw [hspreadIndependentScale, hspreadMarginalScale]
    ring
  rw [hspreadObjective]
  rw [hdeficit] at htotal
  dsimp only [centeredIndependent] at htotal
  linarith

/-- A low endpoint law contracts to its literal conditional-mean law once that mean reaches
the saturation threshold. -/
theorem diagonalEndpointObjective_center_le
    {lowMass leftWeight rightWeight lower center upper : ℝ}
    (hlowMass : 0 ≤ lowMass)
    (hleftWeight : 0 ≤ leftWeight) (hrightWeight : 0 ≤ rightWeight)
    (hweight : leftWeight + rightWeight = 1)
    (hlower : lower ∈ Icc (1 / 4 : ℝ) (1 / 2))
    (hcenter : center ∈ Icc (1 / 4 : ℝ) (1 / 2))
    (hupper : upper ∈ Icc (0 : ℝ) (1 / 2))
    (hmean : leftWeight * lower + rightWeight * upper = center)
    (hcoefficient :
      (1 - dependentShare) * lowMass *
          ((1 - center) / (1 + center) + (1 - 4 * center / 3)) ≤
        1 + entropySlack) :
    diagonalEndpointObjective (lowMass * leftWeight) (2 * lowMass * rightWeight)
        center center ≤
      diagonalEndpointObjective (lowMass * leftWeight) (2 * lowMass * rightWeight)
        lower upper := by
  have hratio :
      (1 / 2 : ℝ) * (1 - center) / join (1 / 2) center =
        (1 - center) / (1 + center) := by
    have hdenominator : 1 + center ≠ 0 := by linarith [hcenter.1]
    rw [show join (1 / 2 : ℝ) center = (1 + center) / 2 by
      simp only [join]
      ring]
    apply (div_eq_div_iff (by linarith [hcenter.1]) hdenominator).2
    ring
  have hsaturated := diagonalEndpointObjective_saturated_center_le hlowMass hleftWeight
    hrightWeight hweight hlower ⟨by linarith [hcenter.1], hcenter.2⟩ hupper
      (by norm_num) (by norm_num) hmean
    (by
      rw [hratio]
      exact hcoefficient)
  have hcenterDependent : dependentCost center center = log 2 := by
    rw [dependentCost_self_eq_cappedEntropy hcenter.2,
      min_eq_right (by norm_num at hcenter ⊢; linarith)]
    simpa only [one_div] using binEntropy_two_inv
  have hindependentScale :
      (lowMass * leftWeight) ^ 2 * binEntropy (join center center) +
          lowMass * leftWeight * (2 * lowMass * rightWeight) *
            binEntropy (join center center) +
          (2 * lowMass * rightWeight) ^ 2 / 4 * binEntropy (join center center) =
        lowMass ^ 2 * binEntropy (join center center) := by
    calc
      _ = lowMass ^ 2 * (leftWeight + rightWeight) ^ 2 *
          binEntropy (join center center) := by ring
      _ = lowMass ^ 2 * binEntropy (join center center) := by rw [hweight]; ring
  have hmarginalScale :
      lowMass * leftWeight * binEntropy center +
          2 * lowMass * rightWeight / 2 * binEntropy center =
        lowMass * binEntropy center := by
    calc
      _ = lowMass * (leftWeight + rightWeight) * binEntropy center := by ring
      _ = lowMass * binEntropy center := by rw [hweight]; ring
  rw [show diagonalEndpointObjective (lowMass * leftWeight) (2 * lowMass * rightWeight)
      center center =
      (1 - dependentShare) * lowMass ^ 2 * binEntropy (join center center) +
        dependentShare * (lowMass * leftWeight * log 2) -
        (1 + entropySlack) * lowMass * binEntropy center by
    unfold diagonalEndpointObjective yuGap
    rw [hcenterDependent, hindependentScale, hmarginalScale]
    ring]
  exact hsaturated

/-- Every high-diagonal endpoint law dominates its support-aware saturated centered
objective. -/
theorem endpointCertificateObjective_saturated_center_le {a q support : ℝ}
    (haLower : 1 / 4 ≤ a) (haUpper : a ≤ abundanceTarget)
    (hqLower : 0 ≤ q)
    (haSupport : a ≤ support) (hqSupport : q ≤ support)
    (hsupport₀ : 0 < support) (hsupportHalf : support ≤ 1 / 2)
    (hcoefficient :
      endpointSupportContractionCoefficient support (endpointConditionalMean a q) ≤
        1 + entropySlack) :
    endpointSaturatedCenteredObjective (endpointConditionalMean a q) ≤
      endpointCertificateObjective a q := by
  let center := endpointConditionalMean a q
  let lowMass := (1 - abundanceTarget) / (1 - center)
  let leftWeight := (1 - 2 * abundanceTarget + center) / (1 - abundanceTarget)
  let rightWeight := (abundanceTarget - center) / (1 - abundanceTarget)
  have htargetOne : abundanceTarget < 1 := abundanceTarget_lt_half.trans (by norm_num)
  have htargetComplement : 0 < 1 - abundanceTarget := sub_pos.2 htargetOne
  have hdenominator : 0 < 1 + q - a - abundanceTarget := by
    nlinarith [abundanceTarget_lt_half]
  have hendpointDenominator : 0 < 1 + q - 2 * a := by
    nlinarith [abundanceTarget_lt_half]
  have hcenterLower : 0 ≤ center := by
    dsimp only [center, endpointConditionalMean]
    apply div_nonneg
    · exact add_nonneg
        (mul_nonneg (by linarith) (by nlinarith [abundanceTarget_lt_half]))
        (mul_nonneg (by norm_num [abundanceTarget]) hqLower)
    · exact hdenominator.le
  have htargetMinusCenter :
      abundanceTarget - center =
        (1 - abundanceTarget) * (abundanceTarget - a) /
          (1 + q - a - abundanceTarget) := by
    dsimp only [center, endpointConditionalMean]
    field_simp [hdenominator.ne']
    ring
  have hcenterComplement :
      1 - center =
        (1 - abundanceTarget) * (1 + q - 2 * a) /
          (1 + q - a - abundanceTarget) := by
    dsimp only [center, endpointConditionalMean]
    field_simp [hdenominator.ne']
    ring
  have hcenterUpperTarget : center ≤ abundanceTarget := by
    rw [← sub_nonneg, htargetMinusCenter]
    exact div_nonneg
      (mul_nonneg htargetComplement.le (sub_nonneg.2 haUpper)) hdenominator.le
  have hcenterUpper : center ≤ 1 / 2 :=
    hcenterUpperTarget.trans abundanceTarget_lt_half.le
  have hcenterOne : center < 1 := hcenterUpper.trans_lt (by norm_num)
  have hcenterComplementPositive : 0 < 1 - center := sub_pos.2 hcenterOne
  have hsupportJoin : 0 < join support center :=
    join_pos_of_pos_left hsupport₀ hcenterLower (hcenterUpper.trans (by norm_num))
  have hlowMass : 0 ≤ lowMass := by
    dsimp only [lowMass]
    exact (div_pos htargetComplement hcenterComplementPositive).le
  have hleftWeight : 0 ≤ leftWeight := by
    dsimp only [leftWeight]
    apply div_nonneg
    · nlinarith [abundanceTarget_lt_half]
    · exact htargetComplement.le
  have hrightWeight : 0 ≤ rightWeight := by
    dsimp only [rightWeight]
    exact div_nonneg (sub_nonneg.2 hcenterUpperTarget) htargetComplement.le
  have hweight : leftWeight + rightWeight = 1 := by
    dsimp only [leftWeight, rightWeight]
    field_simp [htargetComplement.ne']
    ring
  have hmean : leftWeight * a + rightWeight * q = center := by
    dsimp only [leftWeight, rightWeight, center, endpointConditionalMean]
    field_simp [htargetComplement.ne', hdenominator.ne']
    ring
  have hgenericCoefficient :
      (1 - dependentShare) * lowMass *
          (support * (1 - center) / join support center +
            (1 - 4 * center / 3)) ≤
        1 + entropySlack := by
    have hequality :
        (1 - dependentShare) * lowMass *
            (support * (1 - center) / join support center +
              (1 - 4 * center / 3)) =
          endpointSupportContractionCoefficient support center := by
      dsimp only [lowMass, endpointSupportContractionCoefficient]
      dsimp only [targetComplement]
      field_simp [hcenterComplementPositive.ne', hsupportJoin.ne']
      ring
    rw [hequality]
    exact hcoefficient
  have hcontraction := diagonalEndpointObjective_saturated_center_le hlowMass hleftWeight
    hrightWeight hweight ⟨haLower, haSupport⟩ ⟨hcenterLower, hcenterUpper⟩
    ⟨hqLower, hqSupport⟩ hsupport₀ hsupportHalf hmean hgenericCoefficient
  have hcertificateWeight :
      endpointCertificateWeight a q =
        2 * (abundanceTarget - center) / (1 - center) := by
    rw [htargetMinusCenter, hcenterComplement]
    unfold endpointCertificateWeight
    field_simp [htargetComplement.ne', hdenominator.ne', hendpointDenominator.ne']
    ring
  have hleftScale :
      lowMass * leftWeight = 1 - endpointCertificateWeight a q := by
    rw [hcertificateWeight]
    dsimp only [lowMass, leftWeight]
    field_simp [htargetComplement.ne', hcenterComplementPositive.ne']
    ring
  have hrightScale :
      2 * lowMass * rightWeight = endpointCertificateWeight a q := by
    rw [hcertificateWeight]
    dsimp only [lowMass, rightWeight]
    field_simp [htargetComplement.ne', hcenterComplementPositive.ne']
    ring
  rw [hleftScale, hrightScale] at hcontraction
  simpa only [endpointSaturatedCenteredObjective, endpointCertificateObjective, center,
    lowMass, leftWeight, targetComplement, hleftScale] using hcontraction

/-- Every endpoint law in the high-conditional-mean core is bounded below by its centered
endpoint law. -/
theorem endpointCertificateObjective_core_center_le {a q : ℝ}
    (haLower : 1 / 4 ≤ a) (haUpper : a ≤ abundanceTarget)
    (hqLower : 0 ≤ q) (hqUpper : q ≤ 1 / 2)
    (hcenterLower : endpointCoreThreshold ≤ endpointConditionalMean a q) :
    endpointCertificateObjective (endpointConditionalMean a q) (endpointConditionalMean a q) ≤
      endpointCertificateObjective a q := by
  let center := endpointConditionalMean a q
  let lowMass := (1 - abundanceTarget) / (1 - center)
  let leftWeight := (1 - 2 * abundanceTarget + center) / (1 - abundanceTarget)
  let rightWeight := (abundanceTarget - center) / (1 - abundanceTarget)
  have htargetOne : abundanceTarget < 1 := abundanceTarget_lt_half.trans (by norm_num)
  have htargetComplement : 0 < 1 - abundanceTarget := sub_pos.2 htargetOne
  have hdenominator : 0 < 1 + q - a - abundanceTarget := by
    nlinarith [abundanceTarget_lt_half]
  have hendpointDenominator : 0 < 1 + q - 2 * a := by
    nlinarith [abundanceTarget_lt_half]
  have htargetMinusCenter :
      abundanceTarget - center =
        (1 - abundanceTarget) * (abundanceTarget - a) /
          (1 + q - a - abundanceTarget) := by
    dsimp only [center, endpointConditionalMean]
    field_simp [hdenominator.ne']
    ring
  have hcenterComplement :
      1 - center =
        (1 - abundanceTarget) * (1 + q - 2 * a) /
          (1 + q - a - abundanceTarget) := by
    dsimp only [center, endpointConditionalMean]
    field_simp [hdenominator.ne']
    ring
  have hcenterUpperTarget : center ≤ abundanceTarget := by
    rw [← sub_nonneg]
    rw [htargetMinusCenter]
    exact div_nonneg
      (mul_nonneg htargetComplement.le (sub_nonneg.2 haUpper)) hdenominator.le
  have hcenterUpper : center ≤ 1 / 2 :=
    hcenterUpperTarget.trans abundanceTarget_lt_half.le
  have hcenterQuarter : 1 / 4 ≤ center := by
    exact (show (1 / 4 : ℝ) ≤ endpointCoreThreshold by
      norm_num [endpointCoreThreshold]).trans hcenterLower
  have hcenterOne : center < 1 := hcenterUpper.trans_lt (by norm_num)
  have hcenterComplementPositive : 0 < 1 - center := sub_pos.2 hcenterOne
  have hlowMass : 0 ≤ lowMass := by
    dsimp only [lowMass]
    exact (div_pos htargetComplement hcenterComplementPositive).le
  have hleftWeight : 0 ≤ leftWeight := by
    dsimp only [leftWeight]
    apply div_nonneg
    · nlinarith [abundanceTarget_lt_half]
    · exact htargetComplement.le
  have hrightWeight : 0 ≤ rightWeight := by
    dsimp only [rightWeight]
    exact div_nonneg (sub_nonneg.2 hcenterUpperTarget) htargetComplement.le
  have hweight : leftWeight + rightWeight = 1 := by
    dsimp only [leftWeight, rightWeight]
    field_simp [htargetComplement.ne']
    ring
  have hmean : leftWeight * a + rightWeight * q = center := by
    dsimp only [leftWeight, rightWeight, center, endpointConditionalMean]
    field_simp [htargetComplement.ne', hdenominator.ne']
    ring
  have hcoefficient :
      (1 - dependentShare) * lowMass *
          ((1 - center) / (1 + center) + (1 - 4 * center / 3)) ≤
        1 + entropySlack := by
    simpa only [lowMass] using endpointCore_coefficient hcenterLower hcenterUpper
  have hcontraction := diagonalEndpointObjective_center_le hlowMass hleftWeight
    hrightWeight hweight ⟨haLower, haUpper.trans abundanceTarget_lt_half.le⟩
    ⟨hcenterQuarter, hcenterUpper⟩ ⟨hqLower, hqUpper⟩ hmean hcoefficient
  have hcertificateWeight :
      endpointCertificateWeight a q =
        2 * (abundanceTarget - center) / (1 - center) := by
    rw [htargetMinusCenter, hcenterComplement]
    unfold endpointCertificateWeight
    field_simp [htargetComplement.ne', hdenominator.ne', hendpointDenominator.ne']
    ring
  have hleftScale :
      lowMass * leftWeight = 1 - endpointCertificateWeight a q := by
    rw [hcertificateWeight]
    dsimp only [lowMass, leftWeight]
    field_simp [htargetComplement.ne', hcenterComplementPositive.ne']
    ring
  have hrightScale :
      2 * lowMass * rightWeight = endpointCertificateWeight a q := by
    rw [hcertificateWeight]
    dsimp only [lowMass, rightWeight]
    field_simp [htargetComplement.ne', hcenterComplementPositive.ne']
    ring
  have hcenterWeight :
      endpointCertificateWeight center center = endpointCertificateWeight a q := by
    rw [hcertificateWeight]
    unfold endpointCertificateWeight
    rw [show 1 + center - 2 * center = 1 - center by ring]
  rw [hleftScale, hrightScale] at hcontraction
  simpa only [endpointCertificateObjective, center, hcenterWeight] using hcontraction

end Frankl
