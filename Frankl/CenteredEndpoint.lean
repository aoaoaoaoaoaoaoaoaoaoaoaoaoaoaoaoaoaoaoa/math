import Frankl.EndpointObjective

namespace Frankl

open Real Set

/-- The endpoint certificate restricted to equal low coordinates, rescaled by their common
complement. -/
noncomputable def endpointCenteredCurve (y : ℝ) : ℝ :=
  (1 - dependentShare) * targetComplement ^ 2 * binEntropy (y ^ 2)
    + dependentShare * (2 * targetComplement * y - y ^ 2) * log 2
    - (1 + entropySlack) * targetComplement * y * binEntropy y

private noncomputable def endpointCenteredCurveDeriv (y : ℝ) : ℝ :=
  (1 - dependentShare) * targetComplement ^ 2 *
      (2 * y * (log (1 - y ^ 2) - log (y ^ 2)))
    + dependentShare * (2 * targetComplement - 2 * y) * log 2
    - (1 + entropySlack) * targetComplement *
      (binEntropy y + y * (log (1 - y) - log y))

private noncomputable def endpointCenteredCurveDeriv2 (y : ℝ) : ℝ :=
  (1 - dependentShare) * targetComplement ^ 2 *
      (2 * (log (1 - y ^ 2) - 2 * log y) - 4 / (1 - y ^ 2))
    - 2 * dependentShare * log 2
    - (1 + entropySlack) * targetComplement *
      (2 * (log (1 - y) - log y) - 1 / (1 - y))

private noncomputable def endpointCenteredCurveDeriv3 (y : ℝ) : ℝ :=
  let a := (1 - dependentShare) * targetComplement ^ 2
  let s := (1 + entropySlack) * targetComplement
  (-(4 * a * y ^ 2 + 4 * a + s * y ^ 3 - 3 * s * y - 2 * s)) /
    (y * (y - 1) ^ 2 * (y + 1) ^ 2)

private noncomputable def endpointCenteredCurveThirdPolynomial (y : ℝ) : ℝ :=
  10000001 * y ^ 3 + 23855572 * y ^ 2 - 30000003 * y + 3855570

private theorem hasDerivAt_endpointCenteredCurve {y : ℝ} (hy₀ : 0 < y) (hy₁ : y < 1) :
    HasDerivAt endpointCenteredCurve (endpointCenteredCurveDeriv y) y := by
  have hySquare₀ : y ^ 2 ≠ 0 := pow_ne_zero 2 hy₀.ne'
  have hySquare₁ : y ^ 2 ≠ 1 := by
    have : y ^ 2 < 1 := by nlinarith [sq_nonneg (1 - y)]
    exact this.ne
  have hEntropySquare : HasDerivAt (fun z : ℝ ↦ binEntropy (z ^ 2))
      ((log (1 - y ^ 2) - log (y ^ 2)) * (2 * y)) y := by
    have hraw := (hasDerivAt_binEntropy hySquare₀ hySquare₁).comp
      (h := fun z : ℝ ↦ z ^ 2) y
      (hasDerivAt_pow 2 y)
    convert hraw using 1
    norm_num
  have hquadratic : HasDerivAt
      (fun z : ℝ ↦ 2 * targetComplement * z - z ^ 2)
      (2 * targetComplement - 2 * y) y := by
    convert ((hasDerivAt_id y).const_mul (2 * targetComplement)).sub
      ((hasDerivAt_id y).pow 2) using 1
    simp [id]
  have hweightedEntropy : HasDerivAt (fun z : ℝ ↦ z * binEntropy z)
      (binEntropy y + y * (log (1 - y) - log y)) y := by
    convert (hasDerivAt_id y).mul
      (hasDerivAt_binEntropy hy₀.ne' hy₁.ne) using 1
    all_goals simp [id]
  have hcombined :=
    ((hEntropySquare.const_mul ((1 - dependentShare) * targetComplement ^ 2)).add
      (hquadratic.const_mul (dependentShare * log 2))).sub
      (hweightedEntropy.const_mul ((1 + entropySlack) * targetComplement))
  convert hcombined using 1
  · funext z
    simp [endpointCenteredCurve, id]
    ring
  · simp [endpointCenteredCurveDeriv, id]
    ring

private theorem hasDerivAt_endpointCenteredCurveDeriv {y : ℝ} (hy₀ : 0 < y) (hy₁ : y < 1) :
    HasDerivAt endpointCenteredCurveDeriv (endpointCenteredCurveDeriv2 y) y := by
  have hySquare : HasDerivAt (fun z : ℝ ↦ z ^ 2) (2 * y) y := by
    convert (hasDerivAt_id y).mul (hasDerivAt_id y) using 1
    · funext z
      simp [pow_two]
    · simp [id]
      ring
  have hySquare₀ : y ^ 2 ≠ 0 := pow_ne_zero 2 hy₀.ne'
  have hySquare₁ : y ^ 2 ≠ 1 := by
    have : y ^ 2 < 1 := by nlinarith [sq_nonneg (1 - y)]
    exact this.ne
  have hSquareLog := hySquare.log hySquare₀
  have hSquareComplementLog := (hySquare.const_sub 1).log
    (sub_ne_zero.mpr hySquare₁.symm)
  have hLog : HasDerivAt (fun z : ℝ ↦ log z) (1 / y) y := by
    simpa only [id_eq] using (hasDerivAt_id y).log hy₀.ne'
  have hOneSub : HasDerivAt (fun z : ℝ ↦ 1 - z) (-1) y := by
    simpa only [id_eq] using (hasDerivAt_id y).const_sub 1
  have hComplementLog : HasDerivAt (fun z : ℝ ↦ log (1 - z))
      (-1 / (1 - y)) y := by
    exact hOneSub.log (sub_ne_zero.mpr hy₁.ne')
  have hEntropy := hasDerivAt_binEntropy hy₀.ne' hy₁.ne
  have hSquareLogDifference := hSquareComplementLog.sub hSquareLog
  have hLogDifference := hComplementLog.sub hLog
  have hfirst : HasDerivAt
      (fun z : ℝ ↦ 2 * z * (log (1 - z ^ 2) - log (z ^ 2)))
      (2 * (log (1 - y ^ 2) - log (y ^ 2)) +
        2 * y * (-(2 * y) / (1 - y ^ 2) - 2 * y / y ^ 2)) y := by
    convert ((hasDerivAt_id y).const_mul 2).mul hSquareLogDifference using 1
    all_goals simp [id]
  have hlast : HasDerivAt
      (fun z : ℝ ↦ binEntropy z + z * (log (1 - z) - log z))
      ((log (1 - y) - log y) +
        ((log (1 - y) - log y) + y * (-1 / (1 - y) - 1 / y))) y := by
    convert hEntropy.add ((hasDerivAt_id y).mul hLogDifference) using 1
    all_goals simp [id]
  have hlogSquare : log (y ^ 2) = 2 * log y := by
    rw [log_pow]
    norm_num
  have hfirstSimplified : HasDerivAt
      (fun z : ℝ ↦ 2 * z * (log (1 - z ^ 2) - log (z ^ 2)))
      (2 * (log (1 - y ^ 2) - 2 * log y) - 4 / (1 - y ^ 2)) y := by
    convert hfirst using 1
    rw [hlogSquare]
    field_simp [hy₀.ne', sub_ne_zero.mpr hySquare₁.symm]
    ring
  have hlastSimplified : HasDerivAt
      (fun z : ℝ ↦ binEntropy z + z * (log (1 - z) - log z))
      (2 * (log (1 - y) - log y) - 1 / (1 - y)) y := by
    convert hlast using 1
    field_simp [hy₀.ne', sub_ne_zero.mpr hy₁.ne']
    ring
  have hcombined :=
    ((hfirstSimplified.const_mul ((1 - dependentShare) * targetComplement ^ 2)).add
      (((hasDerivAt_const y (2 * targetComplement)).sub
        ((hasDerivAt_id y).const_mul 2)).const_mul (dependentShare * log 2))).sub
      (hlastSimplified.const_mul ((1 + entropySlack) * targetComplement))
  convert hcombined using 1
  · funext z
    simp [endpointCenteredCurveDeriv, id]
    ring
  · simp only [endpointCenteredCurveDeriv2]
    ring

private theorem hasDerivAt_endpointCenteredCurveDeriv2 {y : ℝ} (hy₀ : 0 < y) (hy₁ : y < 1) :
    HasDerivAt endpointCenteredCurveDeriv2 (endpointCenteredCurveDeriv3 y) y := by
  have hySquare : HasDerivAt (fun z : ℝ ↦ z ^ 2) (2 * y) y := by
    convert hasDerivAt_pow 2 y using 1
    norm_num
  have hySquare₁ : y ^ 2 ≠ 1 := by
    have : y ^ 2 < 1 := by nlinarith [sq_nonneg (1 - y)]
    exact this.ne
  have hComplementNe : 1 - y ≠ 0 := sub_ne_zero.mpr hy₁.ne'
  have hSquareComplementNe : 1 - y ^ 2 ≠ 0 := sub_ne_zero.mpr hySquare₁.symm
  have hSquareComplement : HasDerivAt (fun z : ℝ ↦ 1 - z ^ 2) (-(2 * y)) y := by
    exact hySquare.const_sub 1
  have hSquareComplementLog : HasDerivAt (fun z : ℝ ↦ log (1 - z ^ 2))
      (-(2 * y) / (1 - y ^ 2)) y :=
    hSquareComplement.log hSquareComplementNe
  have hSquareComplementInv : HasDerivAt (fun z : ℝ ↦ (1 - z ^ 2)⁻¹)
      (2 * y / (1 - y ^ 2) ^ 2) y := by
    convert hSquareComplement.inv hSquareComplementNe using 1
    all_goals ring
  have hLog : HasDerivAt (fun z : ℝ ↦ log z) (1 / y) y := by
    simpa only [id_eq] using (hasDerivAt_id y).log hy₀.ne'
  have hComplement : HasDerivAt (fun z : ℝ ↦ 1 - z) (-1) y := by
    simpa only [id_eq] using (hasDerivAt_id y).const_sub 1
  have hComplementLog : HasDerivAt (fun z : ℝ ↦ log (1 - z))
      (-1 / (1 - y)) y :=
    hComplement.log hComplementNe
  have hComplementInv : HasDerivAt (fun z : ℝ ↦ (1 - z)⁻¹)
      (1 / (1 - y) ^ 2) y := by
    convert hComplement.inv hComplementNe using 1
    all_goals ring
  have hfirstRaw :=
    ((hSquareComplementLog.sub (hLog.const_mul 2)).const_mul 2).sub
      (hSquareComplementInv.const_mul 4)
  have hfirst : HasDerivAt
      (fun z : ℝ ↦ 2 * (log (1 - z ^ 2) - 2 * log z) - 4 / (1 - z ^ 2))
      (-4 * (y ^ 2 + 1) / (y * (1 - y ^ 2) ^ 2)) y := by
    convert hfirstRaw using 1
    field_simp [hy₀.ne', hSquareComplementNe]
    ring
  have hsecondRaw :=
    ((hComplementLog.sub hLog).const_mul 2).sub hComplementInv
  have hsecond : HasDerivAt
      (fun z : ℝ ↦ 2 * (log (1 - z) - log z) - 1 / (1 - z))
      (-(2 - y) / (y * (1 - y) ^ 2)) y := by
    have hidentity : -(2 - y) / (y * (1 - y) ^ 2) =
        2 * (-1 / (1 - y) - 1 / y) - 1 / (1 - y) ^ 2 := by
      field_simp [hy₀.ne', hComplementNe]
      ring
    convert hsecondRaw using 1
    funext z
    simp only [one_div]
  have hcombined :=
    ((hfirst.const_mul ((1 - dependentShare) * targetComplement ^ 2)).add
      (hasDerivAt_const y (-2 * dependentShare * log 2))).sub
      (hsecond.const_mul ((1 + entropySlack) * targetComplement))
  convert hcombined using 1
  · funext z
    simp only [endpointCenteredCurveDeriv2]
    ring
  · simp only [endpointCenteredCurveDeriv3]
    have hyPlus : y + 1 ≠ 0 := by nlinarith
    have hyMinus : y - 1 ≠ 0 := by nlinarith
    rw [show y * (1 - y ^ 2) ^ 2 =
      y * (y - 1) ^ 2 * (y + 1) ^ 2 by ring]
    rw [show y * (1 - y) ^ 2 = y * (y - 1) ^ 2 by ring]
    field_simp [hy₀.ne', hyPlus, hyMinus]
    ring

private theorem endpointCenteredCurveThirdPolynomial_nonpos {y : ℝ}
    (hyLower : targetComplement ≤ y) (hyUpper : y ≤ 37 / 50) :
    endpointCenteredCurveThirdPolynomial y ≤ 0 := by
  let upper : ℝ := 37 / 50
  let quotient : ℝ :=
    10000001 * y ^ 2 + (10000001 * upper + 23855572) * y +
      (10000001 * upper ^ 2 + 23855572 * upper - 30000003)
  have hquotient : 0 ≤ quotient := by
    dsimp only [quotient, upper]
    norm_num [targetComplement, abundanceTarget] at hyLower
    nlinarith [sq_nonneg y]
  have hfactor :
      endpointCenteredCurveThirdPolynomial upper - endpointCenteredCurveThirdPolynomial y =
        (upper - y) * quotient := by
    dsimp only [endpointCenteredCurveThirdPolynomial, quotient]
    ring
  have hdiff :
      0 ≤ endpointCenteredCurveThirdPolynomial upper - endpointCenteredCurveThirdPolynomial y := by
    rw [hfactor]
    exact mul_nonneg (sub_nonneg.2 hyUpper) hquotient
  have hupper : endpointCenteredCurveThirdPolynomial upper < 0 := by
    norm_num [endpointCenteredCurveThirdPolynomial, upper]
  linarith

private theorem endpointCenteredCurveDeriv3_nonneg {y : ℝ}
    (hy : y ∈ Icc targetComplement (37 / 50)) : 0 ≤ endpointCenteredCurveDeriv3 y := by
  have hy₀ : 0 < y := targetComplement_pos.trans_le hy.1
  have hnumerator :
      4 * ((1 - dependentShare) * targetComplement ^ 2) * y ^ 2 +
          4 * ((1 - dependentShare) * targetComplement ^ 2) +
          ((1 + entropySlack) * targetComplement) * y ^ 3 -
          3 * ((1 + entropySlack) * targetComplement) * y -
          2 * ((1 + entropySlack) * targetComplement) ≤ 0 := by
    rw [show
      4 * ((1 - dependentShare) * targetComplement ^ 2) * y ^ 2 +
            4 * ((1 - dependentShare) * targetComplement ^ 2) +
            ((1 + entropySlack) * targetComplement) * y ^ 3 -
            3 * ((1 + entropySlack) * targetComplement) * y -
            2 * ((1 + entropySlack) * targetComplement) =
          (30901 / 500000000000 : ℝ) * endpointCenteredCurveThirdPolynomial y by
        norm_num [dependentShare, entropySlack, targetComplement, abundanceTarget,
          endpointCenteredCurveThirdPolynomial]
        ring]
    exact mul_nonpos_of_nonneg_of_nonpos (by norm_num)
      (endpointCenteredCurveThirdPolynomial_nonpos hy.1 hy.2)
  rw [endpointCenteredCurveDeriv3]
  exact div_nonneg (neg_nonneg.2 hnumerator)
    (mul_nonneg (mul_nonneg hy₀.le (sq_nonneg (y - 1))) (sq_nonneg (y + 1)))

private noncomputable def endpointCenteredTangent : ℝ := 1339 / 2000

private theorem endpointCenteredTangent_bounds :
    1 / 7000 < endpointCenteredCurve endpointCenteredTangent ∧
      |endpointCenteredCurveDeriv endpointCenteredTangent| < 1 / 10000 := by
  have hy := abs_log_sub_fastScaledLog_le (scale := 1) (x := endpointCenteredTangent)
    (by norm_num [endpointCenteredTangent])
    (by norm_num [endpointCenteredTangent, abs_of_nonneg])
  have hcomplement := abs_log_sub_fastScaledLog_le (scale := 2)
    (x := 1 - endpointCenteredTangent)
    (by norm_num [endpointCenteredTangent])
    (by norm_num [endpointCenteredTangent, abs_of_nonneg])
  have hsquare := abs_log_sub_fastScaledLog_le (scale := 1) (x := endpointCenteredTangent ^ 2)
    (by norm_num [endpointCenteredTangent])
    (by norm_num [endpointCenteredTangent, abs_of_nonneg, abs_of_nonpos])
  have hsquareComplement := abs_log_sub_fastScaledLog_le (scale := 1)
    (x := 1 - endpointCenteredTangent ^ 2)
    (by norm_num [endpointCenteredTangent])
    (by norm_num [endpointCenteredTangent, abs_of_nonneg, abs_of_nonpos])
  have htwo := abs_log_two_sub_center_le
  rw [abs_le] at hy hcomplement hsquare hsquareComplement htwo
  rw [show 1 - endpointCenteredTangent ^ 2 = (2207079 : ℝ) / 4000000 by
    norm_num [endpointCenteredTangent]] at hsquareComplement
  rw [show endpointCenteredTangent ^ 2 = (1792921 : ℝ) / 4000000 by
    norm_num [endpointCenteredTangent]]
    at hsquare
  norm_num [fastScaledLog, fastScaledLogError, atanhLogFour, atanhLogFourError,
    logTwoCenter, logTwoRadius, endpointCenteredTangent, abs_of_nonneg, abs_of_nonpos] at hy
  norm_num [fastScaledLog, fastScaledLogError, atanhLogFour, atanhLogFourError,
    logTwoCenter, logTwoRadius, endpointCenteredTangent, abs_of_nonneg, abs_of_nonpos]
    at hcomplement
  norm_num [fastScaledLog, fastScaledLogError, atanhLogFour, atanhLogFourError,
    logTwoCenter, logTwoRadius, abs_of_nonneg, abs_of_nonpos] at hsquare
  norm_num [fastScaledLog, fastScaledLogError, atanhLogFour, atanhLogFourError,
    logTwoCenter, logTwoRadius, abs_of_nonneg, abs_of_nonpos] at hsquareComplement
  norm_num [logTwoCenter, logTwoRadius] at htwo
  have hcurve : 1 / 7000 < endpointCenteredCurve endpointCenteredTangent := by
    rw [endpointCenteredCurve, binEntropy_eq_negMulLog_add_negMulLog_one_sub,
      binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    simp only [negMulLog]
    norm_num [dependentShare, entropySlack, targetComplement, abundanceTarget,
      endpointCenteredTangent]
    linarith
  have hderivLower : -(1 / 10000 : ℝ) < endpointCenteredCurveDeriv endpointCenteredTangent := by
    rw [endpointCenteredCurveDeriv, binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    simp only [negMulLog]
    norm_num [dependentShare, entropySlack, targetComplement, abundanceTarget,
      endpointCenteredTangent]
    linarith
  have hderivUpper : endpointCenteredCurveDeriv endpointCenteredTangent < 1 / 10000 := by
    rw [endpointCenteredCurveDeriv, binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    simp only [negMulLog]
    norm_num [dependentShare, entropySlack, targetComplement, abundanceTarget,
      endpointCenteredTangent]
    linarith
  exact ⟨hcurve, (abs_lt).2 ⟨hderivLower, hderivUpper⟩⟩

private theorem endpointCenteredCurveDeriv2_targetComplement_pos :
    0 < endpointCenteredCurveDeriv2 targetComplement := by
  have hy := abs_log_sub_fastScaledLog_le (scale := 1) (x := targetComplement)
    (by norm_num [targetComplement, abundanceTarget])
    (by norm_num [targetComplement, abundanceTarget, abs_of_nonneg])
  have ht := abs_log_sub_fastScaledLog_le (scale := 1) (x := abundanceTarget)
    (by norm_num [abundanceTarget])
    (by norm_num [abundanceTarget, abs_of_nonneg, abs_of_nonpos])
  have hsquare := abs_log_sub_fastScaledLog_le (scale := 1)
    (x := 1 - targetComplement ^ 2)
    (by norm_num [targetComplement, abundanceTarget])
    (by norm_num [targetComplement, abundanceTarget, abs_of_nonneg, abs_of_nonpos])
  have htwo := abs_log_two_sub_center_le
  rw [abs_le] at hy ht hsquare htwo
  norm_num [fastScaledLog, fastScaledLogError, atanhLogFour, atanhLogFourError,
    logTwoCenter, logTwoRadius, targetComplement, abundanceTarget, abs_of_nonneg,
    abs_of_nonpos] at hy ht hsquare htwo
  have htargetIdentity : 1 - targetComplement = abundanceTarget := by
    simp [targetComplement]
  rw [endpointCenteredCurveDeriv2, htargetIdentity]
  norm_num [dependentShare, entropySlack, targetComplement, abundanceTarget]
  linarith

private theorem endpointCenteredCurveDeriv2_monotoneOn :
    MonotoneOn endpointCenteredCurveDeriv2 (Icc targetComplement (37 / 50)) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := endpointCenteredCurveDeriv3)
    (convex_Icc targetComplement (37 / 50)) ?_ ?_ ?_
  · intro y hy
    have hy₀ : 0 < y := targetComplement_pos.trans_le hy.1
    have hy₁ : y < 1 := hy.2.trans_lt (by norm_num)
    exact (hasDerivAt_endpointCenteredCurveDeriv2 hy₀ hy₁).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Icc] at hy
    have hy₀ : 0 < y := targetComplement_pos.trans hy.1
    have hy₁ : y < 1 := hy.2.trans (by norm_num)
    exact (hasDerivAt_endpointCenteredCurveDeriv2 hy₀ hy₁).hasDerivWithinAt
  · intro y hy
    rw [interior_Icc] at hy
    exact endpointCenteredCurveDeriv3_nonneg ⟨hy.1.le, hy.2.le⟩

private theorem endpointCenteredCurveDeriv2_nonneg {y : ℝ}
    (hy : y ∈ Icc targetComplement (37 / 50)) : 0 ≤ endpointCenteredCurveDeriv2 y := by
  have hbase : targetComplement ∈ Icc targetComplement (37 / 50) := by
    constructor
    · rfl
    · norm_num [targetComplement, abundanceTarget]
  exact endpointCenteredCurveDeriv2_targetComplement_pos.le.trans
    (endpointCenteredCurveDeriv2_monotoneOn hbase hy hy.1)

private theorem endpointCenteredCurve_convexOn :
    ConvexOn ℝ (Icc targetComplement (37 / 50)) endpointCenteredCurve := by
  refine convexOn_of_hasDerivWithinAt2_nonneg
    (f' := endpointCenteredCurveDeriv) (f'' := endpointCenteredCurveDeriv2)
    (convex_Icc targetComplement (37 / 50)) ?_ ?_ ?_ ?_
  · intro y hy
    have hy₀ : 0 < y := targetComplement_pos.trans_le hy.1
    have hy₁ : y < 1 := hy.2.trans_lt (by norm_num)
    exact (hasDerivAt_endpointCenteredCurve hy₀ hy₁).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Icc] at hy
    exact (hasDerivAt_endpointCenteredCurve (targetComplement_pos.trans hy.1)
      (hy.2.trans (by norm_num))).hasDerivWithinAt
  · intro y hy
    rw [interior_Icc] at hy
    exact (hasDerivAt_endpointCenteredCurveDeriv (targetComplement_pos.trans hy.1)
      (hy.2.trans (by norm_num))).hasDerivWithinAt
  · intro y hy
    rw [interior_Icc] at hy
    exact endpointCenteredCurveDeriv2_nonneg ⟨hy.1.le, hy.2.le⟩

private theorem endpointCenteredCurve_tangent_lower {y : ℝ}
    (hy : y ∈ Icc targetComplement (37 / 50)) :
    endpointCenteredCurve endpointCenteredTangent +
        endpointCenteredCurveDeriv endpointCenteredTangent * (y - endpointCenteredTangent) ≤
      endpointCenteredCurve y := by
  have htangent : endpointCenteredTangent ∈ Icc targetComplement (37 / 50) := by
    norm_num [endpointCenteredTangent, targetComplement, abundanceTarget]
  have hderiv : HasDerivAt endpointCenteredCurve
      (endpointCenteredCurveDeriv endpointCenteredTangent) endpointCenteredTangent :=
    hasDerivAt_endpointCenteredCurve (by norm_num [endpointCenteredTangent])
      (by norm_num [endpointCenteredTangent])
  rcases lt_trichotomy y endpointCenteredTangent with hyTangent | rfl | hTangentY
  · have hslope := endpointCenteredCurve_convexOn.slope_le_of_hasDerivAt
      hy htangent hyTangent hderiv
    rw [slope_def_field] at hslope
    have hscaled := (div_le_iff₀ (sub_pos.2 hyTangent)).1 hslope
    linarith
  · simp
  · have hslope := endpointCenteredCurve_convexOn.le_slope_of_hasDerivAt
      htangent hy hTangentY hderiv
    rw [slope_def_field] at hslope
    have hscaled := (le_div_iff₀ (sub_pos.2 hTangentY)).1 hslope
    linarith

/-- The centered endpoint curve is strictly positive on the interval corresponding to the
contracted endpoint core. -/
theorem endpointCenteredCurve_pos {y : ℝ}
    (hy : y ∈ Icc targetComplement (37 / 50)) : 0 < endpointCenteredCurve y := by
  have hbounds := endpointCenteredTangent_bounds
  have hdelta : |y - endpointCenteredTangent| ≤ 1 := by
    rw [abs_le]
    constructor
    · have := hy.1
      norm_num [endpointCenteredTangent, targetComplement, abundanceTarget] at this ⊢
      linarith
    · have := hy.2
      norm_num [endpointCenteredTangent] at this ⊢
      linarith
  have hproduct :
      |endpointCenteredCurveDeriv endpointCenteredTangent * (y - endpointCenteredTangent)| <
        1 / 10000 := by
    rw [abs_mul]
    calc
      |endpointCenteredCurveDeriv endpointCenteredTangent| * |y - endpointCenteredTangent| ≤
          |endpointCenteredCurveDeriv endpointCenteredTangent| * 1 :=
        mul_le_mul_of_nonneg_left hdelta (abs_nonneg _)
      _ = |endpointCenteredCurveDeriv endpointCenteredTangent| := mul_one _
      _ < 1 / 10000 := hbounds.2
  have hproductLower := (abs_lt.1 hproduct).1
  have htangent := endpointCenteredCurve_tangent_lower hy
  norm_num at hbounds hproductLower ⊢
  linarith [hbounds.1]

private theorem curve_eq_scaled_endpointCertificateObjective {x : ℝ}
    (hxLower : 1 / 4 ≤ x) (hxUpper : x ≤ 1 / 2) :
    endpointCenteredCurve (1 - x) = (1 - x) ^ 2 * endpointCertificateObjective x x := by
  have hdenominator : 1 - x ≠ 0 := by linarith
  have hdependent : dependentCost x x = log 2 := by
    rw [dependentCost_self_eq_cappedEntropy hxUpper,
      min_eq_right (by linarith : (1 / 2 : ℝ) ≤ 2 * x)]
    simpa only [one_div] using binEntropy_two_inv
  let weight := endpointCertificateWeight x x
  have hweight : weight = 2 * (abundanceTarget - x) / (1 - x) := by
    dsimp only [weight, endpointCertificateWeight]
    rw [show 1 + x - 2 * x = 1 - x by ring]
  have hindependentScale :
      (1 - x) ^ 2 * ((1 - weight) ^ 2 + (1 - weight) * weight + weight ^ 2 / 4) =
        targetComplement ^ 2 := by
    rw [hweight]
    field_simp [hdenominator]
    dsimp only [targetComplement]
    ring
  have hdependentScale :
      (1 - x) ^ 2 * (1 - weight) =
        2 * targetComplement * (1 - x) - (1 - x) ^ 2 := by
    rw [hweight]
    field_simp [hdenominator]
    dsimp only [targetComplement]
    ring
  have hmarginalScale :
      (1 - x) ^ 2 * (1 - weight + weight / 2) = targetComplement * (1 - x) := by
    rw [hweight]
    field_simp [hdenominator]
    dsimp only [targetComplement]
    ring
  have hobjective : endpointCertificateObjective x x =
      (1 - dependentShare) *
          ((1 - weight) ^ 2 + (1 - weight) * weight + weight ^ 2 / 4) *
            binEntropy ((1 - x) ^ 2) +
        dependentShare * (1 - weight) * log 2 -
        (1 + entropySlack) * (1 - weight + weight / 2) * binEntropy (1 - x) := by
    dsimp only [endpointCertificateObjective, weight]
    unfold diagonalEndpointObjective yuGap
    rw [hdependent]
    rw [show join x x = 1 - (1 - x) ^ 2 by
      unfold join
      ring]
    rw [binEntropy_one_sub, ← binEntropy_one_sub x]
    ring
  rw [hobjective]
  unfold endpointCenteredCurve
  calc
    (1 - dependentShare) * targetComplement ^ 2 * binEntropy ((1 - x) ^ 2) +
          dependentShare *
              (2 * targetComplement * (1 - x) - (1 - x) ^ 2) * log 2 -
        (1 + entropySlack) * targetComplement * (1 - x) * binEntropy (1 - x) =
      (1 - dependentShare) *
            ((1 - x) ^ 2 *
              ((1 - weight) ^ 2 + (1 - weight) * weight + weight ^ 2 / 4)) *
              binEntropy ((1 - x) ^ 2) +
          dependentShare * ((1 - x) ^ 2 * (1 - weight)) * log 2 -
          (1 + entropySlack) *
            ((1 - x) ^ 2 * (1 - weight + weight / 2)) * binEntropy (1 - x) := by
        rw [hindependentScale, hdependentScale, hmarginalScale]
        ring
    _ = (1 - x) ^ 2 *
        ((1 - dependentShare) *
              ((1 - weight) ^ 2 + (1 - weight) * weight + weight ^ 2 / 4) *
                binEntropy ((1 - x) ^ 2) +
            dependentShare * (1 - weight) * log 2 -
            (1 + entropySlack) * (1 - weight + weight / 2) *
              binEntropy (1 - x)) := by ring

/-- The centered endpoint certificate is strictly positive throughout the contracted core. -/
theorem endpointCertificateObjective_center_pos {x : ℝ}
    (hx : x ∈ Icc endpointCoreThreshold abundanceTarget) :
    0 < endpointCertificateObjective x x := by
  have hxQuarter : 1 / 4 ≤ x := by
    exact (show (1 / 4 : ℝ) ≤ endpointCoreThreshold by
      norm_num [endpointCoreThreshold]).trans hx.1
  have hxHalf : x ≤ 1 / 2 := hx.2.trans abundanceTarget_lt_half.le
  have hy : 1 - x ∈ Icc targetComplement (37 / 50) := by
    constructor
    · dsimp only [targetComplement]
      linarith [hx.2]
    · have hxLower := hx.1
      norm_num [endpointCoreThreshold] at hxLower
      linarith
  have hcurve := endpointCenteredCurve_pos hy
  rw [curve_eq_scaled_endpointCertificateObjective hxQuarter hxHalf] at hcurve
  exact pos_of_mul_pos_right hcurve (sq_nonneg (1 - x))

/-- Every endpoint law in the contracted high-conditional-mean core has strictly positive
certificate objective. -/
theorem endpointCertificateObjective_core_pos {a q : ℝ}
    (haLower : 1 / 4 ≤ a) (haUpper : a ≤ abundanceTarget)
    (hqLower : 0 ≤ q) (hqUpper : q ≤ 1 / 2)
    (hcenterLower : endpointCoreThreshold ≤ endpointConditionalMean a q) :
    0 < endpointCertificateObjective a q := by
  have hdenominator : 0 < 1 + q - a - abundanceTarget := by
    nlinarith [abundanceTarget_lt_half]
  have htargetMinusCenter :
      abundanceTarget - endpointConditionalMean a q =
        (1 - abundanceTarget) * (abundanceTarget - a) /
          (1 + q - a - abundanceTarget) := by
    unfold endpointConditionalMean
    field_simp [hdenominator.ne']
    ring
  have hcenterUpper : endpointConditionalMean a q ≤ abundanceTarget := by
    rw [← sub_nonneg, htargetMinusCenter]
    exact div_nonneg
      (mul_nonneg (sub_nonneg.2 (abundanceTarget_lt_half.le.trans (by norm_num)))
        (sub_nonneg.2 haUpper))
      hdenominator.le
  have hcenterPositive := endpointCertificateObjective_center_pos
    ⟨hcenterLower, hcenterUpper⟩
  exact hcenterPositive.trans_le
    (endpointCertificateObjective_core_center_le haLower haUpper hqLower hqUpper hcenterLower)

end Frankl
