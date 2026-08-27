import Frankl.CenteredEndpoint

namespace Frankl

open Real Set

private theorem sub_two_divisions_mul_denominators
    {x c y z u v : ℝ} (hu : u ≠ 0) (hv : v ≠ 0) :
    (x - c * (y / u + z / v)) * (u * v) =
      x * u * v - c * (y * v + z * u) := by
  field_simp

private theorem endpointSupportContractionCoefficient_antitone_center
    {support lower upper : ℝ}
    (hsupport₀ : 0 < support) (hsupportHalf : support ≤ 1 / 2)
    (hlower₀ : 0 ≤ lower) (hlowerUpper : lower ≤ upper)
    (hupperHalf : upper ≤ 1 / 2) :
    endpointSupportContractionCoefficient support upper ≤
      endpointSupportContractionCoefficient support lower := by
  have hsupportOne : support ≤ 1 := hsupportHalf.trans (by norm_num)
  have hlowerHalf : lower ≤ 1 / 2 := hlowerUpper.trans hupperHalf
  have hlowerOne : lower ≤ 1 := hlowerHalf.trans (by norm_num)
  have hjoinLower : 0 < join support lower :=
    join_pos_of_pos_left hsupport₀ hlower₀ hlowerOne
  have hjoinOrder : join support lower ≤ join support upper := by
    simp only [join]
    nlinarith [mul_nonneg (sub_nonneg.2 hsupportOne)
      (sub_nonneg.2 hlowerUpper)]
  have hfirst : support / join support upper ≤ support / join support lower := by
    exact div_le_div_of_nonneg_left hsupport₀.le hjoinLower hjoinOrder
  have hlowerComplement : 0 < 1 - lower := sub_pos.2 (hlowerHalf.trans_lt (by norm_num))
  have hupperComplement : 0 < 1 - upper := sub_pos.2 (hupperHalf.trans_lt (by norm_num))
  have hsecond :
      (1 - 4 * upper / 3) / (1 - upper) ≤
        (1 - 4 * lower / 3) / (1 - lower) := by
    apply (div_le_div_iff₀ hupperComplement hlowerComplement).2
    nlinarith
  unfold endpointSupportContractionCoefficient
  exact mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond)
    (mul_nonneg (by norm_num [dependentShare]) targetComplement_pos.le)

private theorem endpointConditionalMean_zero_le {a q : ℝ}
    (ha₀ : 0 ≤ a) (haUpper : a ≤ abundanceTarget) (hq₀ : 0 ≤ q) :
    0 ≤ endpointConditionalMean a q := by
  have hdenominator : 0 < 1 + q - a - abundanceTarget := by
    nlinarith [abundanceTarget_lt_half]
  rw [endpointConditionalMean]
  exact div_nonneg
    (add_nonneg
      (mul_nonneg ha₀ (by nlinarith [abundanceTarget_lt_half]))
      (mul_nonneg (by norm_num [abundanceTarget]) hq₀))
    hdenominator.le

private theorem endpointConditionalMean_le_target {a q : ℝ}
    (haUpper : a ≤ abundanceTarget) (hq₀ : 0 ≤ q) :
    endpointConditionalMean a q ≤ abundanceTarget := by
  have hdenominator : 0 < 1 + q - a - abundanceTarget := by
    nlinarith [abundanceTarget_lt_half]
  rw [endpointConditionalMean]
  apply (div_le_iff₀ hdenominator).2
  nlinarith [mul_nonneg (sub_nonneg.2 haUpper)
    (sub_nonneg.2 abundanceTarget_lt_half.le)]

private theorem endpointConditionalMean_mono_q {a q : ℝ}
    (haUpper : a ≤ abundanceTarget) (hq₀ : 0 ≤ q) :
    endpointConditionalMean a 0 ≤ endpointConditionalMean a q := by
  have hzeroDenominator : 0 < 1 - a - abundanceTarget := by
    nlinarith [abundanceTarget_lt_half]
  have hqDenominator : 0 < 1 + q - a - abundanceTarget := by
    nlinarith [abundanceTarget_lt_half]
  rw [endpointConditionalMean, endpointConditionalMean]
  simp only [mul_zero, add_zero]
  apply (div_le_div_iff₀ hzeroDenominator hqDenominator).2
  have hproduct : 0 ≤ q * (abundanceTarget - a) * (1 - abundanceTarget) :=
    mul_nonneg (mul_nonneg hq₀ (sub_nonneg.2 haUpper))
      (sub_nonneg.2 (abundanceTarget_lt_half.le.trans (by norm_num)))
  nlinarith

private theorem endpointConditionalMean_mono_a {a q : ℝ}
    (haLower : 1 / 4 ≤ a) (haUpper : a ≤ abundanceTarget) (hq₀ : 0 ≤ q) :
    endpointConditionalMean (1 / 4) q ≤ endpointConditionalMean a q := by
  have hquarterDenominator : 0 < 1 + q - 1 / 4 - abundanceTarget := by
    nlinarith [abundanceTarget_lt_half]
  have haDenominator : 0 < 1 + q - a - abundanceTarget := by
    nlinarith [abundanceTarget_lt_half]
  rw [endpointConditionalMean, endpointConditionalMean]
  apply (div_le_div_iff₀ hquarterDenominator haDenominator).2
  have hproduct :
      0 ≤ (4 * a - 1) * (1 - abundanceTarget) *
        (q + 1 - 2 * abundanceTarget) := by
    exact mul_nonneg
      (mul_nonneg (by nlinarith) (sub_nonneg.2
        (abundanceTarget_lt_half.le.trans (by norm_num))))
      (by nlinarith [abundanceTarget_lt_half])
  nlinarith

private theorem endpointSupportContractionCoefficient_a_zero_le {a : ℝ}
    (haLower : 1 / 4 ≤ a) (haUpper : a ≤ abundanceTarget) :
    endpointSupportContractionCoefficient a (endpointConditionalMean a 0) ≤
      1 + entropySlack := by
  let center := endpointConditionalMean a 0
  have ha₀ : 0 < a := by linarith
  have hcenterUpper : center ≤ abundanceTarget := by
    exact endpointConditionalMean_le_target haUpper (by norm_num)
  have hcenterHalf : center ≤ 1 / 2 :=
    hcenterUpper.trans abundanceTarget_lt_half.le
  have hcenterComplement : 0 < 1 - center := by
    linarith [abundanceTarget_lt_half]
  have hrDenominator : 0 < 1 - a - abundanceTarget := by
    nlinarith [abundanceTarget_lt_half]
  have hbracket : 0 < 2 - 2 * a - 3 * abundanceTarget + 2 * a * abundanceTarget := by
    norm_num [abundanceTarget]
    nlinarith
  have hsecondDenominator :
      0 < 3 * (1 - abundanceTarget) * (1 - 2 * a) := by
    exact mul_pos (mul_pos (by norm_num)
      (sub_pos.2 (abundanceTarget_lt_half.trans (by norm_num)))) (by nlinarith)
  have hjoinFormula :
      join a center =
        a * (2 - 2 * a - 3 * abundanceTarget + 2 * a * abundanceTarget) /
          (1 - a - abundanceTarget) := by
    dsimp only [center, endpointConditionalMean]
    simp only [mul_zero, add_zero, join]
    field_simp [hrDenominator.ne']
    ring
  have hfirstRatio :
      a / join a center =
        (1 - a - abundanceTarget) /
          (2 - 2 * a - 3 * abundanceTarget + 2 * a * abundanceTarget) := by
    rw [hjoinFormula]
    field_simp [ha₀.ne', hrDenominator.ne', hbracket.ne']
  have hsecondRatio :
      (1 - 4 * center / 3) / (1 - center) =
        (3 * (1 - a - abundanceTarget) -
            4 * a * (1 - 2 * abundanceTarget)) /
          (3 * (1 - abundanceTarget) * (1 - 2 * a)) := by
    apply (div_eq_div_iff hcenterComplement.ne' hsecondDenominator.ne').2
    dsimp only [center, endpointConditionalMean]
    simp only [mul_zero, add_zero]
    field_simp [hrDenominator.ne']
    ring
  let certificateNumerator : ℝ :=
    (1 + entropySlack) *
        (2 - 2 * a - 3 * abundanceTarget + 2 * a * abundanceTarget) *
        (3 * (1 - abundanceTarget) * (1 - 2 * a)) -
      (1 - dependentShare) * targetComplement *
        ((1 - a - abundanceTarget) *
            (3 * (1 - abundanceTarget) * (1 - 2 * a)) +
          (3 * (1 - a - abundanceTarget) - 4 * a * (1 - 2 * abundanceTarget)) *
            (2 - 2 * a - 3 * abundanceTarget + 2 * a * abundanceTarget))
  have hcertificateNumerator : 0 ≤ certificateNumerator := by
    have hinterval : 0 ≤ (a - 1 / 4) * (abundanceTarget - a) :=
      mul_nonneg (sub_nonneg.2 haLower) (sub_nonneg.2 haUpper)
    dsimp only [certificateNumerator]
    norm_num [dependentShare, entropySlack, targetComplement, abundanceTarget]
      at hinterval haLower haUpper ⊢
    nlinarith
  rw [← sub_nonneg]
  rw [show
    (1 + entropySlack) -
          endpointSupportContractionCoefficient a (endpointConditionalMean a 0) =
        certificateNumerator /
          ((2 - 2 * a - 3 * abundanceTarget + 2 * a * abundanceTarget) *
            (3 * (1 - abundanceTarget) * (1 - 2 * a))) by
      change
        (1 + entropySlack) - endpointSupportContractionCoefficient a center = _
      apply (eq_div_iff (mul_ne_zero hbracket.ne' hsecondDenominator.ne')).2
      rw [endpointSupportContractionCoefficient, hfirstRatio, hsecondRatio]
      dsimp only [certificateNumerator]
      exact sub_two_divisions_mul_denominators hbracket.ne' hsecondDenominator.ne']
  exact div_nonneg hcertificateNumerator
    (mul_nonneg hbracket.le hsecondDenominator.le)

private theorem endpointSupportContractionCoefficient_quarter_q_le {q : ℝ}
    (hqLower : 1 / 4 ≤ q) (hqUpper : q ≤ 1 / 2) :
    endpointSupportContractionCoefficient q (endpointConditionalMean (1 / 4) q) ≤
      1 + entropySlack := by
  let center := endpointConditionalMean (1 / 4) q
  let denominator : ℝ := 1 + q - 1 / 4 - abundanceTarget
  let numerator : ℝ := (1 / 4) * (1 - 2 * abundanceTarget) + abundanceTarget * q
  let joinNumerator : ℝ := q * denominator + (1 - q) * numerator
  have hq₀ : 0 < q := by linarith
  have hdenominator : 0 < denominator := by
    dsimp only [denominator]
    nlinarith [abundanceTarget_lt_half]
  have hnumerator : 0 < numerator := by
    dsimp only [numerator]
    exact add_pos_of_pos_of_nonneg
      (mul_pos (by norm_num) (by nlinarith [abundanceTarget_lt_half]))
      (mul_nonneg (by nlinarith [abundanceTarget_gt_three_eighths]) hq₀.le)
  have hjoinNumerator : 0 < joinNumerator := by
    dsimp only [joinNumerator]
    exact add_pos_of_pos_of_nonneg (mul_pos hq₀ hdenominator)
      (mul_nonneg (by linarith) hnumerator.le)
  have hdenominatorDifference : 0 < denominator - numerator := by
    rw [show denominator - numerator =
        (1 - abundanceTarget) * (q + 1 / 2) by
      dsimp only [denominator, numerator]
      ring]
    exact mul_pos (by nlinarith [abundanceTarget_lt_half]) (by linarith)
  have hcenterFormula : center = numerator / denominator := by
    rfl
  have hjoinFormula :
      join q center = joinNumerator / denominator := by
    rw [hcenterFormula]
    simp only [join]
    field_simp [hdenominator.ne']
    dsimp only [joinNumerator]
    ring
  have hfirstRatio :
      q / join q center = q * denominator / joinNumerator := by
    rw [hjoinFormula]
    field_simp [hdenominator.ne', hjoinNumerator.ne']
  have hsecondRatio :
      (1 - 4 * center / 3) / (1 - center) =
        (3 * denominator - 4 * numerator) / (3 * (denominator - numerator)) := by
    rw [hcenterFormula]
    field_simp [hdenominator.ne', hdenominatorDifference.ne']
  have hcube : q ^ 3 ≤ (1 / 2 : ℝ) * q ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg q) (sub_nonneg.2 hqUpper)]
  have hsquare : q ^ 2 ≤ (1 / 2 : ℝ) * q := by
    nlinarith [mul_nonneg hq₀.le (sub_nonneg.2 hqUpper)]
  let certificateNumerator : ℝ :=
    (1 + entropySlack) * joinNumerator * (3 * (denominator - numerator)) -
      (1 - dependentShare) * targetComplement *
        (q * denominator * (3 * (denominator - numerator)) +
          (3 * denominator - 4 * numerator) * joinNumerator)
  have hcertificateNumerator : 0 ≤ certificateNumerator := by
    dsimp only [certificateNumerator, joinNumerator, numerator, denominator]
    norm_num [dependentShare, entropySlack, targetComplement, abundanceTarget]
      at hcube hsquare hqLower hqUpper ⊢
    nlinarith
  rw [← sub_nonneg]
  rw [show
    (1 + entropySlack) -
          endpointSupportContractionCoefficient q (endpointConditionalMean (1 / 4) q) =
        certificateNumerator /
          (joinNumerator * (3 * (denominator - numerator))) by
      change
        (1 + entropySlack) - endpointSupportContractionCoefficient q center = _
      rw [endpointSupportContractionCoefficient, hfirstRatio, hsecondRatio]
      dsimp only [certificateNumerator]
      field_simp [hjoinNumerator.ne', hdenominatorDifference.ne']]
  exact div_nonneg hcertificateNumerator
    (mul_nonneg hjoinNumerator.le (mul_nonneg (by norm_num) hdenominatorDifference.le))

/-- On the high-diagonal endpoint rectangle, the support-aware contraction coefficient fits
inside Yu's strict entropy slack. -/
theorem endpointSupportContractionCoefficient_high_le {a q : ℝ}
    (haLower : 1 / 4 ≤ a) (haUpper : a ≤ abundanceTarget)
    (hqLower : 0 ≤ q) (hqUpper : q ≤ 1 / 2) :
    endpointSupportContractionCoefficient (max a q) (endpointConditionalMean a q) ≤
      1 + entropySlack := by
  have hcenterUpper : endpointConditionalMean a q ≤ 1 / 2 :=
    (endpointConditionalMean_le_target haUpper hqLower).trans abundanceTarget_lt_half.le
  rcases le_total q a with hqa | haq
  · rw [max_eq_left hqa]
    have hcenterZero : 0 ≤ endpointConditionalMean a 0 :=
      endpointConditionalMean_zero_le (by linarith) haUpper (by norm_num)
    calc
      endpointSupportContractionCoefficient a (endpointConditionalMean a q) ≤
          endpointSupportContractionCoefficient a (endpointConditionalMean a 0) :=
        endpointSupportContractionCoefficient_antitone_center (by linarith)
          (haUpper.trans abundanceTarget_lt_half.le) hcenterZero
          (endpointConditionalMean_mono_q haUpper hqLower) hcenterUpper
      _ ≤ 1 + entropySlack :=
        endpointSupportContractionCoefficient_a_zero_le haLower haUpper
  · rw [max_eq_right haq]
    have hquarterTarget : (1 : ℝ) / 4 ≤ abundanceTarget := by
      linarith [abundanceTarget_gt_three_eighths]
    have hquarterCenterZero : 0 ≤ endpointConditionalMean (1 / 4) q :=
      endpointConditionalMean_zero_le (by norm_num) hquarterTarget hqLower
    calc
      endpointSupportContractionCoefficient q (endpointConditionalMean a q) ≤
          endpointSupportContractionCoefficient q (endpointConditionalMean (1 / 4) q) :=
        endpointSupportContractionCoefficient_antitone_center (by linarith)
          hqUpper hquarterCenterZero
          (endpointConditionalMean_mono_a haLower haUpper hqLower) hcenterUpper
      _ ≤ 1 + entropySlack :=
        endpointSupportContractionCoefficient_quarter_q_le (haLower.trans haq) hqUpper

private theorem centeredCurve_eq_scaled_endpointSaturatedCenteredObjective {center : ℝ}
    (hcenterUpper : center ≤ 1 / 2) :
    endpointCenteredCurve (1 - center) =
      (1 - center) ^ 2 * endpointSaturatedCenteredObjective center := by
  have hcomplement : 1 - center ≠ 0 := by linarith
  have hjoin : join center center = 1 - (1 - center) ^ 2 := by
    unfold join
    ring
  let lowMass := targetComplement / (1 - center)
  let leftWeight := (1 - 2 * abundanceTarget + center) / targetComplement
  have htargetComplement : targetComplement ≠ 0 := targetComplement_pos.ne'
  have hindependentScale : (1 - center) ^ 2 * lowMass ^ 2 = targetComplement ^ 2 := by
    dsimp only [lowMass]
    field_simp [hcomplement]
  have hdependentScale :
      (1 - center) ^ 2 * (lowMass * leftWeight) =
        2 * targetComplement * (1 - center) - (1 - center) ^ 2 := by
    dsimp only [lowMass, leftWeight]
    field_simp [hcomplement, htargetComplement]
    dsimp only [targetComplement]
    ring
  have hmarginalScale :
      (1 - center) ^ 2 * lowMass = targetComplement * (1 - center) := by
    dsimp only [lowMass]
    field_simp [hcomplement]
  rw [endpointCenteredCurve]
  calc
    (1 - dependentShare) * targetComplement ^ 2 * binEntropy ((1 - center) ^ 2) +
          dependentShare *
              (2 * targetComplement * (1 - center) - (1 - center) ^ 2) * log 2 -
        (1 + entropySlack) * targetComplement * (1 - center) *
          binEntropy (1 - center) =
      (1 - dependentShare) * ((1 - center) ^ 2 * lowMass ^ 2) *
            binEntropy ((1 - center) ^ 2) +
          dependentShare * ((1 - center) ^ 2 * (lowMass * leftWeight)) * log 2 -
        (1 + entropySlack) * ((1 - center) ^ 2 * lowMass) *
          binEntropy (1 - center) := by
      rw [hindependentScale, hdependentScale, hmarginalScale]
      ring
    _ = (1 - center) ^ 2 *
        ((1 - dependentShare) * lowMass ^ 2 * binEntropy (1 - (1 - center) ^ 2) +
          dependentShare * (lowMass * leftWeight * log 2) -
          (1 + entropySlack) * lowMass * binEntropy (1 - center)) := by
      rw [show binEntropy (1 - (1 - center) ^ 2) =
          binEntropy ((1 - center) ^ 2) by
        exact binEntropy_one_sub ((1 - center) ^ 2)]
      ring
    _ = (1 - center) ^ 2 * endpointSaturatedCenteredObjective center := by
      rw [endpointSaturatedCenteredObjective]
      rw [hjoin, binEntropy_one_sub center]

private theorem endpointConditionalMean_high_lower {a q : ℝ}
    (haLower : 1 / 4 ≤ a) (haUpper : a ≤ abundanceTarget) (hqLower : 0 ≤ q) :
    4 / 25 ≤ endpointConditionalMean a q := by
  have hquarterBase : (4 : ℝ) / 25 ≤ endpointConditionalMean (1 / 4) 0 := by
    norm_num [endpointConditionalMean, abundanceTarget]
  have hraiseA : endpointConditionalMean (1 / 4) 0 ≤ endpointConditionalMean a 0 :=
    endpointConditionalMean_mono_a haLower haUpper (by norm_num)
  exact hquarterBase.trans (hraiseA.trans
    (endpointConditionalMean_mono_q haUpper hqLower))

/-- The saturated centered objective is positive throughout the center range reached by the
high-diagonal endpoint rectangle. -/
theorem endpointSaturatedCenteredObjective_pos {center : ℝ}
    (hcenter : center ∈ Icc (4 / 25 : ℝ) abundanceTarget) :
    0 < endpointSaturatedCenteredObjective center := by
  have hcenterHalf : center ≤ 1 / 2 := hcenter.2.trans abundanceTarget_lt_half.le
  have hy : 1 - center ∈ Icc targetComplement (21 / 25) := by
    constructor
    · dsimp only [targetComplement]
      exact sub_le_sub_left hcenter.2 1
    · linarith [hcenter.1]
  have hcurve := endpointCenteredCurve_pos hy
  rw [centeredCurve_eq_scaled_endpointSaturatedCenteredObjective
    hcenterHalf] at hcurve
  exact pos_of_mul_pos_right hcurve (sq_nonneg (1 - center))

/-- Every endpoint law in the high-diagonal rectangle has positive certificate objective. -/
theorem endpointCertificateObjective_high_pos {a q : ℝ}
    (haLower : 1 / 4 ≤ a) (haUpper : a ≤ abundanceTarget)
    (hqLower : 0 ≤ q) (hqUpper : q ≤ 1 / 2) :
    0 < endpointCertificateObjective a q := by
  let support := max a q
  have haSupport : a ≤ support := le_max_left a q
  have hqSupport : q ≤ support := le_max_right a q
  have hsupport₀ : 0 < support :=
    (show (0 : ℝ) < 1 / 4 by norm_num).trans_le (haLower.trans haSupport)
  have hsupportHalf : support ≤ 1 / 2 :=
    max_le (haUpper.trans abundanceTarget_lt_half.le) hqUpper
  have hcoefficient :
      endpointSupportContractionCoefficient support (endpointConditionalMean a q) ≤
        1 + entropySlack := by
    simpa only [support] using
      endpointSupportContractionCoefficient_high_le haLower haUpper hqLower hqUpper
  have hcontraction := endpointCertificateObjective_saturated_center_le haLower haUpper
    hqLower haSupport hqSupport hsupport₀ hsupportHalf hcoefficient
  have hcenterLower := endpointConditionalMean_high_lower haLower haUpper hqLower
  have hcenterUpper := endpointConditionalMean_le_target haUpper hqLower
  exact (endpointSaturatedCenteredObjective_pos ⟨hcenterLower, hcenterUpper⟩).trans_le
    hcontraction

end Frankl
