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
  4 * ((1 - dependentShare) * targetComplement ^ 2) * y ^ 2
    + 4 * ((1 - dependentShare) * targetComplement ^ 2)
    + ((1 + entropySlack) * targetComplement) * y ^ 3
    - 3 * ((1 + entropySlack) * targetComplement) * y
    - 2 * ((1 + entropySlack) * targetComplement)

private theorem hasDerivAt_endpointCenteredCurve {y : ℝ} (hy₀ : 0 < y) (hy₁ : y < 1) :
    HasDerivAt endpointCenteredCurve (endpointCenteredCurveDeriv y) y := by
  have hySquare₀ : y ^ 2 ≠ 0 := pow_ne_zero 2 hy₀.ne'
  have hySquare₁ : y ^ 2 ≠ 1 := by
    have : y ^ 2 < 1 := by nlinarith [sq_nonneg (1 - y)]
    exact this.ne
  have hEntropySquare : HasDerivAt (fun z : ℝ ↦ binEntropy (z ^ 2))
      ((log (1 - y ^ 2) - log (y ^ 2)) * (2 * y)) y := by
    have raw := (hasDerivAt_binEntropy hySquare₀ hySquare₁).comp
      (h := fun z : ℝ ↦ z ^ 2) y
      (hasDerivAt_pow 2 y)
    have derivative : HasDerivAt _
        ((log (1 - y ^ 2) - log (y ^ 2)) * (2 * y)) y :=
      raw.congr_deriv (by norm_num)
    apply derivative.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun _ ↦ rfl
  have hquadratic : HasDerivAt
      (fun z : ℝ ↦ 2 * targetComplement * z - z ^ 2)
      (2 * targetComplement - 2 * y) y := by
    have raw := ((hasDerivAt_id y).const_mul (2 * targetComplement)).sub
      ((hasDerivAt_id y).pow 2)
    have derivative : HasDerivAt _ (2 * targetComplement - 2 * y) y :=
      raw.congr_deriv (by
        simp only [id_eq]
        ring)
    apply derivative.congr_of_eventuallyEq
    filter_upwards with z
    rfl
  have hweightedEntropy : HasDerivAt (fun z : ℝ ↦ z * binEntropy z)
      (binEntropy y + y * (log (1 - y) - log y)) y := by
    have raw := (hasDerivAt_id y).mul
      (hasDerivAt_binEntropy hy₀.ne' hy₁.ne)
    have derivative : HasDerivAt _
        (binEntropy y + y * (log (1 - y) - log y)) y :=
      raw.congr_deriv (by
        simp only [id_eq]
        ring)
    apply derivative.congr_of_eventuallyEq
    filter_upwards with z
    rfl
  have hcombined :=
    ((hEntropySquare.const_mul ((1 - dependentShare) * targetComplement ^ 2)).add
      (hquadratic.const_mul (dependentShare * log 2))).sub
      (hweightedEntropy.const_mul ((1 + entropySlack) * targetComplement))
  have derivative : HasDerivAt _ (endpointCenteredCurveDeriv y) y :=
    hcombined.congr_deriv (by
      dsimp only [endpointCenteredCurveDeriv]
      ring)
  apply derivative.congr_of_eventuallyEq
  filter_upwards with z
  dsimp only [endpointCenteredCurve, Pi.add_apply, Pi.sub_apply]
  ring

private theorem hasDerivAt_endpointCenteredCurveDeriv {y : ℝ} (hy₀ : 0 < y) (hy₁ : y < 1) :
    HasDerivAt endpointCenteredCurveDeriv (endpointCenteredCurveDeriv2 y) y := by
  have hySquare : HasDerivAt (fun z : ℝ ↦ z ^ 2) (2 * y) y := by
    exact (hasDerivAt_pow 2 y).congr_deriv (by norm_num)
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
    have raw := ((hasDerivAt_id y).const_mul 2).mul hSquareLogDifference
    have derivative : HasDerivAt _
        (2 * (log (1 - y ^ 2) - log (y ^ 2)) +
          2 * y * (-(2 * y) / (1 - y ^ 2) - 2 * y / y ^ 2)) y :=
      raw.congr_deriv (by
        simp only [id_eq, Pi.sub_apply]
        ring)
    apply derivative.congr_of_eventuallyEq
    filter_upwards with z
    rfl
  have hlast : HasDerivAt
      (fun z : ℝ ↦ binEntropy z + z * (log (1 - z) - log z))
      ((log (1 - y) - log y) +
        ((log (1 - y) - log y) + y * (-1 / (1 - y) - 1 / y))) y := by
    have raw := hEntropy.add ((hasDerivAt_id y).mul hLogDifference)
    have derivative : HasDerivAt _
        ((log (1 - y) - log y) +
          ((log (1 - y) - log y) + y * (-1 / (1 - y) - 1 / y))) y :=
      raw.congr_deriv (by
        simp only [id_eq, Pi.sub_apply]
        ring)
    apply derivative.congr_of_eventuallyEq
    filter_upwards with z
    rfl
  have hlogSquare : log (y ^ 2) = 2 * log y := by
    rw [log_pow]
    norm_num
  have hfirstSimplified : HasDerivAt
      (fun z : ℝ ↦ 2 * z * (log (1 - z ^ 2) - log (z ^ 2)))
      (2 * (log (1 - y ^ 2) - 2 * log y) - 4 / (1 - y ^ 2)) y := by
    apply hfirst.congr_deriv
    rw [hlogSquare]
    field_simp [hy₀.ne', sub_ne_zero.mpr hySquare₁.symm]
    ring
  have hlastSimplified : HasDerivAt
      (fun z : ℝ ↦ binEntropy z + z * (log (1 - z) - log z))
      (2 * (log (1 - y) - log y) - 1 / (1 - y)) y := by
    apply hlast.congr_deriv
    field_simp [hy₀.ne', sub_ne_zero.mpr hy₁.ne']
    ring
  have hcombined :=
    ((hfirstSimplified.const_mul ((1 - dependentShare) * targetComplement ^ 2)).add
      (((hasDerivAt_const y (2 * targetComplement)).sub
        ((hasDerivAt_id y).const_mul 2)).const_mul (dependentShare * log 2))).sub
      (hlastSimplified.const_mul ((1 + entropySlack) * targetComplement))
  have derivative : HasDerivAt _ (endpointCenteredCurveDeriv2 y) y :=
    hcombined.congr_deriv (by
      dsimp only [endpointCenteredCurveDeriv2]
      ring)
  apply derivative.congr_of_eventuallyEq
  filter_upwards with z
  simp only [endpointCenteredCurveDeriv, Pi.add_apply, Pi.sub_apply, id_eq]
  ring

private theorem hasDerivAt_endpointCenteredCurveDeriv2 {y : ℝ} (hy₀ : 0 < y) (hy₁ : y < 1) :
    HasDerivAt endpointCenteredCurveDeriv2 (endpointCenteredCurveDeriv3 y) y := by
  have hySquare : HasDerivAt (fun z : ℝ ↦ z ^ 2) (2 * y) y := by
    exact (hasDerivAt_pow 2 y).congr_deriv (by norm_num)
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
    exact (hSquareComplement.inv hSquareComplementNe).congr_deriv (by ring)
  have hLog : HasDerivAt (fun z : ℝ ↦ log z) (1 / y) y := by
    simpa only [id_eq] using (hasDerivAt_id y).log hy₀.ne'
  have hComplement : HasDerivAt (fun z : ℝ ↦ 1 - z) (-1) y := by
    simpa only [id_eq] using (hasDerivAt_id y).const_sub 1
  have hComplementLog : HasDerivAt (fun z : ℝ ↦ log (1 - z))
      (-1 / (1 - y)) y :=
    hComplement.log hComplementNe
  have hComplementInv : HasDerivAt (fun z : ℝ ↦ (1 - z)⁻¹)
      (1 / (1 - y) ^ 2) y := by
    exact (hComplement.inv hComplementNe).congr_deriv (by ring)
  have hfirstRaw :=
    ((hSquareComplementLog.sub (hLog.const_mul 2)).const_mul 2).sub
      (hSquareComplementInv.const_mul 4)
  have hfirst : HasDerivAt
      (fun z : ℝ ↦ 2 * (log (1 - z ^ 2) - 2 * log z) - 4 / (1 - z ^ 2))
      (-4 * (y ^ 2 + 1) / (y * (1 - y ^ 2) ^ 2)) y := by
    have derivative : HasDerivAt _
        (-4 * (y ^ 2 + 1) / (y * (1 - y ^ 2) ^ 2)) y :=
      hfirstRaw.congr_deriv (by
        field_simp [hy₀.ne', hSquareComplementNe]
        ring)
    apply derivative.congr_of_eventuallyEq
    filter_upwards with z
    simp only [Pi.sub_apply, div_eq_mul_inv]
  have hsecondRaw :=
    ((hComplementLog.sub hLog).const_mul 2).sub hComplementInv
  have hsecond : HasDerivAt
      (fun z : ℝ ↦ 2 * (log (1 - z) - log z) - 1 / (1 - z))
      (-(2 - y) / (y * (1 - y) ^ 2)) y := by
    have hidentity : -(2 - y) / (y * (1 - y) ^ 2) =
        2 * (-1 / (1 - y) - 1 / y) - 1 / (1 - y) ^ 2 := by
      field_simp [hy₀.ne', hComplementNe]
      ring
    have derivative : HasDerivAt _ (-(2 - y) / (y * (1 - y) ^ 2)) y :=
      hsecondRaw.congr_deriv hidentity.symm
    apply derivative.congr_of_eventuallyEq
    filter_upwards with z
    simp only [Pi.sub_apply, div_eq_mul_inv, one_mul]
  have hcombined :=
    ((hfirst.const_mul ((1 - dependentShare) * targetComplement ^ 2)).add
      (hasDerivAt_const y (-2 * dependentShare * log 2))).sub
      (hsecond.const_mul ((1 + entropySlack) * targetComplement))
  have derivative : HasDerivAt _ (endpointCenteredCurveDeriv3 y) y :=
    hcombined.congr_deriv (by
      dsimp only [endpointCenteredCurveDeriv3]
      have hyPlus : y + 1 ≠ 0 := by nlinarith
      have hyMinus : y - 1 ≠ 0 := by nlinarith
      rw [show y * (1 - y ^ 2) ^ 2 =
        y * (y - 1) ^ 2 * (y + 1) ^ 2 by ring]
      rw [show y * (1 - y) ^ 2 = y * (y - 1) ^ 2 by ring]
      field_simp [hy₀.ne', hyPlus, hyMinus]
      ring)
  apply derivative.congr_of_eventuallyEq
  filter_upwards with z
  dsimp only [endpointCenteredCurveDeriv2, Pi.add_apply, Pi.sub_apply]
  ring

private theorem endpointCenteredCurveThirdPolynomial_monotoneOn :
    MonotoneOn endpointCenteredCurveThirdPolynomial
      (Icc targetComplement (21 / 25)) := by
  intro x hx y _ hxy
  have hs₀ : 0 ≤ targetComplement := targetComplement_pos.le
  have hx₀ : 0 ≤ x := hs₀.trans hx.1
  have hy₀ : 0 ≤ y := hx₀.trans hxy
  have hxsquare : targetComplement ^ 2 ≤ x ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hx.1) (add_nonneg hx₀ hs₀)]
  have hysquare : targetComplement ^ 2 ≤ y ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 (hx.1.trans hxy)) (add_nonneg hy₀ hs₀)]
  have hxyProduct : targetComplement ^ 2 ≤ x * y := by
    nlinarith [mul_nonneg (sub_nonneg.2 hx.1) hy₀,
      mul_nonneg hs₀ (sub_nonneg.2 (hx.1.trans hxy))]
  have haNonneg :
      0 ≤ 4 * ((1 - dependentShare) * targetComplement ^ 2) := by
    norm_num [dependentShare, targetComplement, abundanceTarget]
  have hsNonneg : 0 ≤ (1 + entropySlack) * targetComplement := by
    norm_num [entropySlack, targetComplement, abundanceTarget]
  have hbase :
      0 < (1 + entropySlack) * targetComplement * (3 * targetComplement ^ 2) +
        4 * ((1 - dependentShare) * targetComplement ^ 2) *
          (2 * targetComplement) -
        3 * ((1 + entropySlack) * targetComplement) := by
    norm_num [dependentShare, entropySlack, targetComplement, abundanceTarget]
  have hsquareSum :
      3 * targetComplement ^ 2 ≤ y ^ 2 + y * x + x ^ 2 := by
    nlinarith
  have hlinearSum : 2 * targetComplement ≤ y + x := by
    nlinarith [hx.1, hx.1.trans hxy]
  have hsquareScaled := mul_le_mul_of_nonneg_left hsquareSum hsNonneg
  have hlinearScaled := mul_le_mul_of_nonneg_left hlinearSum haNonneg
  have hquotient :
      0 ≤ (1 + entropySlack) * targetComplement * (y ^ 2 + y * x + x ^ 2) +
        4 * ((1 - dependentShare) * targetComplement ^ 2) * (y + x) -
        3 * ((1 + entropySlack) * targetComplement) := by
    nlinarith
  rw [← sub_nonneg]
  rw [show endpointCenteredCurveThirdPolynomial y -
        endpointCenteredCurveThirdPolynomial x =
      (y - x) *
        ((1 + entropySlack) * targetComplement * (y ^ 2 + y * x + x ^ 2) +
          4 * ((1 - dependentShare) * targetComplement ^ 2) * (y + x) -
          3 * ((1 + entropySlack) * targetComplement)) by
    dsimp only [endpointCenteredCurveThirdPolynomial]
    ring]
  exact mul_nonneg (sub_nonneg.2 hxy) hquotient

private theorem endpointCenteredCurveDeriv3_nonneg_of_polynomial_nonpos {y : ℝ}
    (hy₀ : 0 ≤ y) (hpolynomial : endpointCenteredCurveThirdPolynomial y ≤ 0) :
    0 ≤ endpointCenteredCurveDeriv3 y := by
  rw [endpointCenteredCurveDeriv3]
  exact div_nonneg (neg_nonneg.2 hpolynomial)
    (mul_nonneg (mul_nonneg hy₀ (sq_nonneg (y - 1))) (sq_nonneg (y + 1)))

private theorem endpointCenteredCurveDeriv3_nonpos_of_polynomial_nonneg {y : ℝ}
    (hy₀ : 0 ≤ y) (hpolynomial : 0 ≤ endpointCenteredCurveThirdPolynomial y) :
    endpointCenteredCurveDeriv3 y ≤ 0 := by
  rw [endpointCenteredCurveDeriv3]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hpolynomial)
    (mul_nonneg (mul_nonneg hy₀ (sq_nonneg (y - 1))) (sq_nonneg (y + 1)))

private noncomputable def endpointCenteredTangent : ℝ :=
  670545261496963 / 1000000000000000

private theorem endpointCenteredTangent_log_bounds :
    (-39966407444181545942 : ℝ) / 10 ^ 20 < log endpointCenteredTangent ∧
      log endpointCenteredTangent < (-39966407444181545941 : ℝ) / 10 ^ 20 := by
  have h := abs_log_sub_scaledLogSeries_le (terms := 72) (scale := 1)
    (x := endpointCenteredTangent)
    (by norm_num [endpointCenteredTangent])
    (by norm_num [endpointCenteredTangent, abs_of_nonneg])
  rw [abs_le] at h
  norm_num [scaledLogSeries, scaledLogSeriesError, logSeries, logSeriesError,
    Finset.sum_range_succ, endpointCenteredTangent, abs_of_nonneg, abs_of_nonpos] at h ⊢
  constructor <;> linarith

private theorem endpointCenteredTangent_complement_log_bounds :
    (-111031629865384492052 : ℝ) / 10 ^ 20 < log (1 - endpointCenteredTangent) ∧
      log (1 - endpointCenteredTangent) <
        (-111031629865384492051 : ℝ) / 10 ^ 20 := by
  have h := abs_log_sub_scaledLogSeries_le (terms := 72) (scale := 2)
    (x := 1 - endpointCenteredTangent)
    (by norm_num [endpointCenteredTangent])
    (by norm_num [endpointCenteredTangent, abs_of_nonneg])
  rw [abs_le] at h
  norm_num [scaledLogSeries, scaledLogSeriesError, logSeries, logSeriesError,
    Finset.sum_range_succ, endpointCenteredTangent, abs_of_nonneg, abs_of_nonpos] at h ⊢
  constructor <;> linarith

private theorem endpointCenteredTangent_square_log_bounds :
    (-79932814888363091883 : ℝ) / 10 ^ 20 < log (endpointCenteredTangent ^ 2) ∧
      log (endpointCenteredTangent ^ 2) <
        (-79932814888363091882 : ℝ) / 10 ^ 20 := by
  have h := abs_log_sub_scaledLogSeries_le (terms := 72) (scale := 1)
    (x := endpointCenteredTangent ^ 2)
    (by norm_num [endpointCenteredTangent])
    (by norm_num [endpointCenteredTangent, abs_of_nonneg, abs_of_nonpos])
  rw [abs_le] at h
  norm_num [scaledLogSeries, scaledLogSeriesError, logSeries, logSeriesError,
    Finset.sum_range_succ, endpointCenteredTangent, abs_of_nonneg, abs_of_nonpos] at h ⊢
  constructor <;> linarith

private theorem endpointCenteredTangent_squareComplement_log_bounds :
    (-59716622162557994496 : ℝ) / 10 ^ 20 <
        log (1 - endpointCenteredTangent ^ 2) ∧
      log (1 - endpointCenteredTangent ^ 2) <
        (-59716622162557994495 : ℝ) / 10 ^ 20 := by
  have h := abs_log_sub_scaledLogSeries_le (terms := 72) (scale := 1)
    (x := 1 - endpointCenteredTangent ^ 2)
    (by norm_num [endpointCenteredTangent])
    (by norm_num [endpointCenteredTangent, abs_of_nonneg, abs_of_nonpos])
  rw [abs_le] at h
  norm_num [scaledLogSeries, scaledLogSeriesError, logSeries, logSeriesError,
    Finset.sum_range_succ, endpointCenteredTangent, abs_of_nonneg, abs_of_nonpos] at h ⊢
  constructor <;> linarith

private theorem endpointCenteredTangent_logTwo_bounds :
    (69314718055994530941 : ℝ) / 10 ^ 20 < log 2 ∧
      log 2 < (69314718055994530942 : ℝ) / 10 ^ 20 := by
  have h := abs_log_sub_logSeries_le (terms := 72)
    (x := (1 : ℝ) / 2) (by norm_num [abs_of_nonneg])
  have hhalfLog : log ((1 : ℝ) / 2) = -log 2 := by
    rw [one_div, log_inv]
  rw [hhalfLog] at h
  rw [abs_le] at h
  norm_num [logSeries, logSeriesError, Finset.sum_range_succ, abs_of_nonneg,
    abs_of_nonpos] at h ⊢
  constructor <;> linarith

private theorem endpointCenteredTangent_bounds :
    1 / (25 * 10 ^ 16) < endpointCenteredCurve endpointCenteredTangent ∧
      0 < endpointCenteredCurveDeriv endpointCenteredTangent ∧
      endpointCenteredCurveDeriv endpointCenteredTangent <
        1 / (7 * 10 ^ 17) := by
  have hy := endpointCenteredTangent_log_bounds
  have hcomplement := endpointCenteredTangent_complement_log_bounds
  have hsquare := endpointCenteredTangent_square_log_bounds
  have hsquareComplement := endpointCenteredTangent_squareComplement_log_bounds
  have htwo := endpointCenteredTangent_logTwo_bounds
  rcases hy with ⟨hyLower, hyUpper⟩
  rcases hcomplement with ⟨hcomplementLower, hcomplementUpper⟩
  rcases hsquare with ⟨hsquareLower, hsquareUpper⟩
  rcases hsquareComplement with ⟨hsquareComplementLower, hsquareComplementUpper⟩
  rcases htwo with ⟨htwoLower, htwoUpper⟩
  norm_num [endpointCenteredTangent] at hyLower hyUpper
  norm_num [endpointCenteredTangent] at hcomplementLower hcomplementUpper
  norm_num [endpointCenteredTangent] at hsquareLower hsquareUpper
  norm_num [endpointCenteredTangent] at hsquareComplementLower hsquareComplementUpper
  norm_num at htwoLower htwoUpper
  have hcurve :
      1 / (25 * 10 ^ 16) < endpointCenteredCurve endpointCenteredTangent := by
    rw [endpointCenteredCurve, binEntropy_eq_negMulLog_add_negMulLog_one_sub,
      binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    simp only [negMulLog]
    norm_num [dependentShare, entropySlack, targetComplement, abundanceTarget,
      endpointCenteredTangent]
    linarith
  have hderivLower : 0 < endpointCenteredCurveDeriv endpointCenteredTangent := by
    rw [endpointCenteredCurveDeriv, binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    simp only [negMulLog]
    norm_num [dependentShare, entropySlack, targetComplement, abundanceTarget,
      endpointCenteredTangent]
    linarith
  have hderivUpper :
      endpointCenteredCurveDeriv endpointCenteredTangent <
        1 / (7 * 10 ^ 17) := by
    rw [endpointCenteredCurveDeriv, binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    simp only [negMulLog]
    norm_num [dependentShare, entropySlack, targetComplement, abundanceTarget,
      endpointCenteredTangent]
    linarith
  exact ⟨hcurve, hderivLower, hderivUpper⟩

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

private theorem endpointCenteredCurveDeriv2_twentyOneTwentyFive_pos :
    0 < endpointCenteredCurveDeriv2 (21 / 25) := by
  have hy := abs_log_sub_fastScaledLog_le (scale := 0) (x := (21 : ℝ) / 25)
    (by norm_num)
    (by norm_num [abs_of_nonneg, abs_of_nonpos])
  have hcomplement := abs_log_sub_fastScaledLog_le (scale := 3) (x := (4 : ℝ) / 25)
    (by norm_num)
    (by norm_num [abs_of_nonneg, abs_of_nonpos])
  have hsquareComplement := abs_log_sub_fastScaledLog_le (scale := 2)
    (x := (184 : ℝ) / 625)
    (by norm_num)
    (by norm_num [abs_of_nonneg, abs_of_nonpos])
  have htwo := abs_log_two_sub_center_le
  rw [abs_le] at hy hcomplement hsquareComplement htwo
  norm_num [fastScaledLog, fastScaledLogError, atanhLogFour, atanhLogFourError,
    logTwoCenter, logTwoRadius, abs_of_nonneg, abs_of_nonpos]
    at hy hcomplement hsquareComplement htwo
  rw [endpointCenteredCurveDeriv2]
  norm_num [dependentShare, entropySlack, targetComplement, abundanceTarget]
  linarith

private theorem endpointCenteredCurveDeriv2_nonneg {y : ℝ}
    (hy : y ∈ Icc targetComplement (21 / 25)) : 0 ≤ endpointCenteredCurveDeriv2 y := by
  by_cases hpolynomial : endpointCenteredCurveThirdPolynomial y ≤ 0
  · have hmonotone :
        MonotoneOn endpointCenteredCurveDeriv2 (Icc targetComplement y) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := endpointCenteredCurveDeriv3)
        (convex_Icc targetComplement y) ?_ ?_ ?_
      · intro z hz
        have hz₀ : 0 < z := targetComplement_pos.trans_le hz.1
        have hz₁ : z < 1 := (hz.2.trans hy.2).trans_lt (by norm_num)
        exact (hasDerivAt_endpointCenteredCurveDeriv2 hz₀ hz₁).continuousAt.continuousWithinAt
      · intro z hz
        rw [interior_Icc] at hz
        exact (hasDerivAt_endpointCenteredCurveDeriv2
          (targetComplement_pos.trans hz.1)
          ((hz.2.trans_le hy.2).trans (by norm_num))).hasDerivWithinAt
      · intro z hz
        rw [interior_Icc] at hz
        have hzDomain : z ∈ Icc targetComplement (21 / 25) :=
          ⟨hz.1.le, hz.2.le.trans hy.2⟩
        have hzPolynomial : endpointCenteredCurveThirdPolynomial z ≤
            endpointCenteredCurveThirdPolynomial y :=
          endpointCenteredCurveThirdPolynomial_monotoneOn hzDomain hy hz.2.le
        exact endpointCenteredCurveDeriv3_nonneg_of_polynomial_nonpos
          (targetComplement_pos.le.trans hz.1.le) (hzPolynomial.trans hpolynomial)
    have hleft : targetComplement ∈ Icc targetComplement y := ⟨le_rfl, hy.1⟩
    have hright : y ∈ Icc targetComplement y := ⟨hy.1, le_rfl⟩
    exact endpointCenteredCurveDeriv2_targetComplement_pos.le.trans
      (hmonotone hleft hright hy.1)
  · have hpolynomial₀ : 0 ≤ endpointCenteredCurveThirdPolynomial y :=
      (lt_of_not_ge hpolynomial).le
    have hantitone :
        AntitoneOn endpointCenteredCurveDeriv2 (Icc y (21 / 25)) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := endpointCenteredCurveDeriv3)
        (convex_Icc y (21 / 25)) ?_ ?_ ?_
      · intro z hz
        have hz₀ : 0 < z := targetComplement_pos.trans_le (hy.1.trans hz.1)
        have hz₁ : z < 1 := hz.2.trans_lt (by norm_num)
        exact (hasDerivAt_endpointCenteredCurveDeriv2 hz₀ hz₁).continuousAt.continuousWithinAt
      · intro z hz
        rw [interior_Icc] at hz
        exact (hasDerivAt_endpointCenteredCurveDeriv2
          (targetComplement_pos.trans (hy.1.trans_lt hz.1))
          (hz.2.trans (by norm_num))).hasDerivWithinAt
      · intro z hz
        rw [interior_Icc] at hz
        have hzDomain : z ∈ Icc targetComplement (21 / 25) :=
          ⟨hy.1.trans hz.1.le, hz.2.le⟩
        have hzPolynomial : endpointCenteredCurveThirdPolynomial y ≤
            endpointCenteredCurveThirdPolynomial z :=
          endpointCenteredCurveThirdPolynomial_monotoneOn hy hzDomain hz.1.le
        exact endpointCenteredCurveDeriv3_nonpos_of_polynomial_nonneg
          (targetComplement_pos.le.trans (hy.1.trans hz.1.le))
          (hpolynomial₀.trans hzPolynomial)
    have hleft : y ∈ Icc y (21 / 25) := ⟨le_rfl, hy.2⟩
    have hright : (21 / 25 : ℝ) ∈ Icc y (21 / 25) := ⟨hy.2, le_rfl⟩
    exact endpointCenteredCurveDeriv2_twentyOneTwentyFive_pos.le.trans
      (hantitone hleft hright hy.2)

private theorem endpointCenteredCurve_convexOn :
    ConvexOn ℝ (Icc targetComplement (21 / 25)) endpointCenteredCurve := by
  refine convexOn_of_hasDerivWithinAt2_nonneg
    (f' := endpointCenteredCurveDeriv) (f'' := endpointCenteredCurveDeriv2)
    (convex_Icc targetComplement (21 / 25)) ?_ ?_ ?_ ?_
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
    (hy : y ∈ Icc targetComplement (21 / 25)) :
    endpointCenteredCurve endpointCenteredTangent +
        endpointCenteredCurveDeriv endpointCenteredTangent * (y - endpointCenteredTangent) ≤
      endpointCenteredCurve y := by
  have htangent : endpointCenteredTangent ∈ Icc targetComplement (21 / 25) := by
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
    (hy : y ∈ Icc targetComplement (21 / 25)) : 0 < endpointCenteredCurve y := by
  have hbounds := endpointCenteredTangent_bounds
  have htangent := endpointCenteredCurve_tangent_lower hy
  rcases le_total y endpointCenteredTangent with _ | hTangentY
  · have hdelta : endpointCenteredTangent - y < 1 / 18 := by
      have hyLower := hy.1
      norm_num [endpointCenteredTangent, targetComplement, abundanceTarget] at hyLower ⊢
      linarith
    have hproductUpper :
        endpointCenteredCurveDeriv endpointCenteredTangent *
            (endpointCenteredTangent - y) < 1 / (126 * 10 ^ 17) := by
      calc
        endpointCenteredCurveDeriv endpointCenteredTangent *
              (endpointCenteredTangent - y) <
            endpointCenteredCurveDeriv endpointCenteredTangent * (1 / 18) :=
          mul_lt_mul_of_pos_left hdelta hbounds.2.1
        _ < (1 / (7 * 10 ^ 17)) * (1 / 18) :=
          mul_lt_mul_of_pos_right hbounds.2.2 (by norm_num)
        _ = 1 / (126 * 10 ^ 17) := by norm_num
    norm_num at hbounds hproductUpper ⊢
    linarith [hbounds.1]
  · have hproductNonneg :
        0 ≤ endpointCenteredCurveDeriv endpointCenteredTangent *
          (y - endpointCenteredTangent) :=
      mul_nonneg hbounds.2.1.le (sub_nonneg.2 hTangentY)
    have hcurvePos : 0 < endpointCenteredCurve endpointCenteredTangent :=
      (by norm_num : (0 : ℝ) < 1 / (25 * 10 ^ 16)).trans hbounds.1
    exact (add_pos_of_pos_of_nonneg hcurvePos hproductNonneg).trans_le htangent

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
  have hy : 1 - x ∈ Icc targetComplement (21 / 25) := by
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
