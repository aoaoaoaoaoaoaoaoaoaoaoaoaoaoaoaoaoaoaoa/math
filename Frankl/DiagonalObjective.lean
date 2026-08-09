import Frankl.CanonicalObjective
import Frankl.CertificateObjective

namespace Frankl

open Real Set

/-- Jensen deficit of a binary law with explicit masses. -/
noncomputable def binarySpreadDeficit (f : ℝ → ℝ)
    (lowerWeight upperWeight lower upper : ℝ) : ℝ :=
  f (lowerWeight * lower + upperWeight * upper) -
    (lowerWeight * f lower + upperWeight * f upper)

/-- A binary entropy spread has nonnegative Jensen deficit. -/
theorem binarySpreadDeficit_nonneg {lowerWeight upperWeight lower upper : ℝ}
    (hlowerWeight : 0 ≤ lowerWeight) (hupperWeight : 0 ≤ upperWeight)
    (hweight : lowerWeight + upperWeight = 1)
    (hlower : lower ∈ Icc (0 : ℝ) 1) (hupper : upper ∈ Icc (0 : ℝ) 1) :
    0 ≤ binarySpreadDeficit binEntropy lowerWeight upperWeight lower upper := by
  have hjensen := strictConcave_binEntropy.concaveOn.2 hlower hupper
    hlowerWeight hupperWeight hweight
  dsimp only [smul_eq_mul] at hjensen
  exact sub_nonneg.2 hjensen

/-- A pointwise join-curvature comparison controls every binary Jensen deficit. -/
theorem binarySpreadDeficit_joinEntropy_le {lowerWeight upperWeight lower upper q
    coefficient : ℝ}
    (hlowerWeight : 0 ≤ lowerWeight) (hupperWeight : 0 ≤ upperWeight)
    (hweight : lowerWeight + upperWeight = 1)
    (hlower : lower ∈ Icc (0 : ℝ) (1 / 2))
    (hupper : upper ∈ Icc (0 : ℝ) (1 / 2))
    (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    (hcoefficient : ∀ x ∈ Ioo (0 : ℝ) (1 / 2),
      x * (1 - q) / join x q ≤ coefficient) :
    binarySpreadDeficit (fun x ↦ binEntropy (join x q))
        lowerWeight upperWeight lower upper ≤
      coefficient * binarySpreadDeficit binEntropy
        lowerWeight upperWeight lower upper := by
  have hjensen := (joinEntropyDifference_concaveOn hq₀ hq₁ hcoefficient).2
    hlower hupper hlowerWeight hupperWeight hweight
  dsimp only [smul_eq_mul, joinEntropyDifference] at hjensen
  dsimp only [binarySpreadDeficit]
  linarith

/-- Sharp rational join-curvature coefficient for a low external parameter. -/
theorem binarySpreadDeficit_joinEntropy_le_ratio
    {lowerWeight upperWeight lower upper q : ℝ}
    (hlowerWeight : 0 ≤ lowerWeight) (hupperWeight : 0 ≤ upperWeight)
    (hweight : lowerWeight + upperWeight = 1)
    (hlower : lower ∈ Icc (0 : ℝ) (1 / 2))
    (hupper : upper ∈ Icc (0 : ℝ) (1 / 2))
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1 / 2) :
    binarySpreadDeficit (fun x ↦ binEntropy (join x q))
        lowerWeight upperWeight lower upper ≤
      (1 - q) / (1 + q) * binarySpreadDeficit binEntropy
        lowerWeight upperWeight lower upper := by
  apply binarySpreadDeficit_joinEntropy_le hlowerWeight hupperWeight hweight
    hlower hupper hq₀ (by linarith)
  intro x hx
  exact join_curvature_ratio_le hx.1 hx.2.le hq₀ hq₁

/-- Affine join-curvature coefficient for a low external parameter. -/
theorem binarySpreadDeficit_joinEntropy_le_affine
    {lowerWeight upperWeight lower upper q : ℝ}
    (hlowerWeight : 0 ≤ lowerWeight) (hupperWeight : 0 ≤ upperWeight)
    (hweight : lowerWeight + upperWeight = 1)
    (hlower : lower ∈ Icc (0 : ℝ) (1 / 2))
    (hupper : upper ∈ Icc (0 : ℝ) (1 / 2))
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1 / 2) :
    binarySpreadDeficit (fun x ↦ binEntropy (join x q))
        lowerWeight upperWeight lower upper ≤
      (1 - 4 * q / 3) * binarySpreadDeficit binEntropy
        lowerWeight upperWeight lower upper := by
  apply binarySpreadDeficit_joinEntropy_le hlowerWeight hupperWeight hweight
    hlower hupper hq₀ (by linarith)
  intro x hx
  exact join_curvature_ratio_le_affine hx.1 hx.2.le hq₀ hq₁

/-- Spreading a low diagonal law loses at most a fixed multiple of its marginal entropy. -/
theorem diagonalIndependent_deficit_le
    {lowerWeight upperWeight lower target upper : ℝ}
    (hlowerWeight : 0 ≤ lowerWeight) (hupperWeight : 0 ≤ upperWeight)
    (hweight : lowerWeight + upperWeight = 1)
    (hlower : lower ∈ Icc (0 : ℝ) (1 / 2))
    (htarget : target ∈ Icc (0 : ℝ) (1 / 2))
    (hupper : upper ∈ Icc (0 : ℝ) (1 / 2))
    (hmean : lowerWeight * lower + upperWeight * upper = target) :
    binEntropy (join target target) -
        (lowerWeight ^ 2 * binEntropy (join lower lower) +
          2 * lowerWeight * upperWeight * binEntropy (join lower upper) +
          upperWeight ^ 2 * binEntropy (join upper upper)) ≤
      ((1 - target) / (1 + target) + (1 - 4 * target / 3)) *
        binarySpreadDeficit binEntropy lowerWeight upperWeight lower upper := by
  let deficit := binarySpreadDeficit binEntropy lowerWeight upperWeight lower upper
  let middle := lowerWeight * binEntropy (join target lower) +
    upperWeight * binEntropy (join target upper)
  have hdeficit :
      deficit = binEntropy target -
        (lowerWeight * binEntropy lower + upperWeight * binEntropy upper) := by
    dsimp only [deficit, binarySpreadDeficit]
    rw [hmean]
  change binEntropy (join target target) -
      (lowerWeight ^ 2 * binEntropy (join lower lower) +
        2 * lowerWeight * upperWeight * binEntropy (join lower upper) +
        upperWeight ^ 2 * binEntropy (join upper upper)) ≤
    ((1 - target) / (1 + target) + (1 - 4 * target / 3)) * deficit
  have hcenterRaw := binarySpreadDeficit_joinEntropy_le_ratio
    hlowerWeight hupperWeight hweight hlower hupper htarget.1 htarget.2
  have hcenter :
      binEntropy (join target target) - middle ≤
        (1 - target) / (1 + target) * deficit := by
    dsimp only [binarySpreadDeficit] at hcenterRaw
    rw [hmean] at hcenterRaw
    rw [hdeficit]
    simpa only [middle, join_comm target lower,
      join_comm target upper] using hcenterRaw
  have hlowerRow := binarySpreadDeficit_joinEntropy_le_affine
    hlowerWeight hupperWeight hweight hlower hupper hlower.1 hlower.2
  have hupperRow := binarySpreadDeficit_joinEntropy_le_affine
    hlowerWeight hupperWeight hweight hlower hupper hupper.1 hupper.2
  have hlowerScaled := mul_le_mul_of_nonneg_left hlowerRow hlowerWeight
  have hupperScaled := mul_le_mul_of_nonneg_left hupperRow hupperWeight
  have hrows :
      middle -
          (lowerWeight ^ 2 * binEntropy (join lower lower) +
            2 * lowerWeight * upperWeight * binEntropy (join lower upper) +
            upperWeight ^ 2 * binEntropy (join upper upper)) ≤
        (1 - 4 * target / 3) * deficit := by
    have hsum := add_le_add hlowerScaled hupperScaled
    dsimp only [binarySpreadDeficit] at hsum
    rw [hmean] at hsum
    rw [← hdeficit] at hsum
    dsimp only [middle]
    rw [join_comm upper lower] at hsum
    calc
      lowerWeight * binEntropy (join target lower) +
            upperWeight * binEntropy (join target upper) -
          (lowerWeight ^ 2 * binEntropy (join lower lower) +
            2 * lowerWeight * upperWeight * binEntropy (join lower upper) +
            upperWeight ^ 2 * binEntropy (join upper upper)) =
        lowerWeight *
              (binEntropy (join target lower) -
              (lowerWeight * binEntropy (join lower lower) +
                upperWeight * binEntropy (join lower upper))) +
          upperWeight *
            (binEntropy (join target upper) -
              (lowerWeight * binEntropy (join lower upper) +
                upperWeight * binEntropy (join upper upper))) := by
          ring
      _ ≤ lowerWeight *
            ((1 - 4 * lower / 3) *
              deficit) +
          upperWeight *
            ((1 - 4 * upper / 3) * deficit) := hsum
      _ = (1 - 4 * target / 3) * deficit := by
          have hcoefficient :
              lowerWeight * (1 - 4 * lower / 3) +
                  upperWeight * (1 - 4 * upper / 3) =
                1 - 4 * target / 3 := by
            linear_combination hweight - 4 / 3 * hmean
          rw [← hcoefficient]
          ring
  calc
    binEntropy (join target target) -
          (lowerWeight ^ 2 * binEntropy (join lower lower) +
            2 * lowerWeight * upperWeight * binEntropy (join lower upper) +
            upperWeight ^ 2 * binEntropy (join upper upper)) =
        (binEntropy (join target target) - middle) +
          (middle -
            (lowerWeight ^ 2 * binEntropy (join lower lower) +
              2 * lowerWeight * upperWeight * binEntropy (join lower upper) +
              upperWeight ^ 2 * binEntropy (join upper upper))) := by ring
    _ ≤ (1 - target) / (1 + target) * deficit +
        (1 - 4 * target / 3) * deficit := add_le_add hcenter hrows
    _ = ((1 - target) / (1 + target) + (1 - 4 * target / 3)) * deficit := by ring

/-- The tangent to binary entropy at an interior probability supports its whole unit interval. -/
theorem binEntropy_le_tangent {target x : ℝ}
    (htarget₀ : 0 < target) (htarget₁ : target < 1)
    (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) :
    binEntropy x ≤ binEntropy target +
      (log (1 - target) - log target) * (x - target) := by
  have htarget : target ∈ Icc (0 : ℝ) 1 := ⟨htarget₀.le, htarget₁.le⟩
  have hx : x ∈ Icc (0 : ℝ) 1 := ⟨hx₀, hx₁⟩
  have hderiv := hasDerivAt_binEntropy htarget₀.ne' htarget₁.ne
  rcases lt_trichotomy x target with hxt | rfl | htx
  · have hslope := strictConcave_binEntropy.concaveOn.le_slope_of_hasDerivAt
      hx htarget hxt hderiv
    rw [slope_def_field] at hslope
    have hscaled := (le_div_iff₀ (sub_pos.2 hxt)).1 hslope
    linarith
  · simp
  · have hslope := strictConcave_binEntropy.concaveOn.slope_le_of_hasDerivAt
      htarget hx htx hderiv
    rw [slope_def_field] at hslope
    have hscaled := (div_le_iff₀ (sub_pos.2 htx)).1 hslope
    linarith

/-- Entropy gap between two independent copies and their capped diagonal coupling below `1 / 4`. -/
noncomputable def lowCappedEntropyGap (x : ℝ) : ℝ :=
  2 * binEntropy x - binEntropy (2 * x)

private noncomputable def lowCappedEntropyGapDeriv (x : ℝ) : ℝ :=
  2 * (log (1 - x) - log x) -
    2 * (log (1 - 2 * x) - log (2 * x))

private noncomputable def lowCappedEntropyGapDeriv2 (x : ℝ) : ℝ :=
  2 / ((1 - 2 * x) * (1 - x))

private theorem hasDerivAt_lowCappedEntropyGap {x : ℝ}
    (hx₀ : x ≠ 0) (hx₁ : x ≠ 1) (hdouble₀ : 2 * x ≠ 0) (hdouble₁ : 2 * x ≠ 1) :
    HasDerivAt lowCappedEntropyGap (lowCappedEntropyGapDeriv x) x := by
  have hscaled : HasDerivAt (fun y : ℝ ↦ 2 * y) 2 x := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul 2
  have hdouble := (hasDerivAt_binEntropy hdouble₀ hdouble₁).comp x hscaled
  convert ((hasDerivAt_binEntropy hx₀ hx₁).const_mul 2).sub hdouble using 1
  all_goals
    simp only [lowCappedEntropyGap, lowCappedEntropyGapDeriv]
    ring

private theorem lowCappedEntropyGapDeriv2_eq {x : ℝ}
    (hx₀ : x ≠ 0) (hx₁ : x ≠ 1) (hdouble₁ : 2 * x ≠ 1) :
    lowCappedEntropyGapDeriv2 x =
      2 * (-1 / (1 - x) - 1 / x) -
        2 * (-2 / (1 - 2 * x) - 2 / (2 * x)) := by
  have hcomplement : 1 - x ≠ 0 := sub_ne_zero.mpr hx₁.symm
  have hdoubleComplement : 1 - 2 * x ≠ 0 := sub_ne_zero.mpr hdouble₁.symm
  dsimp only [lowCappedEntropyGapDeriv2]
  field_simp [hx₀, hcomplement, hdoubleComplement]
  ring

private theorem hasDerivAt_lowCappedEntropyGapDeriv {x : ℝ}
    (hx₀ : x ≠ 0) (hx₁ : x ≠ 1) (hdouble₀ : 2 * x ≠ 0) (hdouble₁ : 2 * x ≠ 1) :
    HasDerivAt lowCappedEntropyGapDeriv (lowCappedEntropyGapDeriv2 x) x := by
  have hxlog : HasDerivAt (fun y : ℝ ↦ log y) x⁻¹ x := by
    simpa only [id_eq, one_div] using (hasDerivAt_id x).log hx₀
  have hxcomplog : HasDerivAt (fun y : ℝ ↦ log (1 - y)) (-1 / (1 - x)) x := by
    simpa only [id_eq] using
      ((hasDerivAt_id x).const_sub 1).log (sub_ne_zero.mpr hx₁.symm)
  have hscaled : HasDerivAt (fun y : ℝ ↦ 2 * y) 2 x := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul 2
  have hdoublelog : HasDerivAt (fun y : ℝ ↦ log (2 * y)) (2 / (2 * x)) x := by
    simpa only [one_div] using hscaled.log hdouble₀
  have hdoublecomplog : HasDerivAt (fun y : ℝ ↦ log (1 - 2 * y))
      (-2 / (1 - 2 * x)) x := by
    simpa only [one_div] using
      (hscaled.const_sub 1 |>.log (sub_ne_zero.mpr hdouble₁.symm))
  convert ((hxcomplog.sub hxlog).const_mul 2).sub
    ((hdoublecomplog.sub hdoublelog).const_mul 2) using 1
  simpa only [one_div] using lowCappedEntropyGapDeriv2_eq hx₀ hx₁ hdouble₁

/-- The low capped-entropy gap is convex up to the cap transition. -/
theorem lowCappedEntropyGap_convexOn :
    ConvexOn ℝ (Icc (0 : ℝ) (1 / 4)) lowCappedEntropyGap := by
  refine convexOn_of_hasDerivWithinAt2_nonneg
    (f' := lowCappedEntropyGapDeriv) (f'' := lowCappedEntropyGapDeriv2)
    (convex_Icc 0 (1 / 4)) ?_ ?_ ?_ ?_
  · exact (continuous_const.mul binEntropy_continuous |>.sub
      (binEntropy_continuous.comp (continuous_const.mul continuous_id))).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    apply HasDerivAt.hasDerivWithinAt
    apply hasDerivAt_lowCappedEntropyGap
    · exact hx.1.ne'
    · exact ne_of_lt (hx.2.trans (by norm_num))
    · exact mul_ne_zero (by norm_num) hx.1.ne'
    · exact ne_of_lt (by nlinarith [hx.2] : 2 * x < 1)
  · intro x hx
    rw [interior_Icc] at hx
    apply HasDerivAt.hasDerivWithinAt
    apply hasDerivAt_lowCappedEntropyGapDeriv
    · exact hx.1.ne'
    · exact ne_of_lt (hx.2.trans (by norm_num))
    · exact mul_ne_zero (by norm_num) hx.1.ne'
    · exact ne_of_lt (by nlinarith [hx.2] : 2 * x < 1)
  · intro x hx
    rw [interior_Icc] at hx
    exact div_nonneg (by norm_num)
      (mul_nonneg (by nlinarith [hx.2]) (by nlinarith [hx.2]))

/-- Entropy gap between two independent copies and their capped diagonal coupling. -/
noncomputable def cappedEntropyGap (x : ℝ) : ℝ :=
  2 * binEntropy x - binEntropy (min (2 * x) (1 / 2))

private noncomputable def targetCappedGapSupport (x : ℝ) : ℝ :=
  2 * binEntropy abundanceTarget - log 2 +
    2 * (log (1 - abundanceTarget) - log abundanceTarget) *
      (x - abundanceTarget)

private theorem targetCappedGapSupport_zero_nonneg :
    0 ≤ targetCappedGapSupport 0 := by
  have htarget₁ : abundanceTarget ≠ 1 := by norm_num [abundanceTarget]
  have hcomplement₀ : 1 - abundanceTarget ≠ 0 := sub_ne_zero.mpr htarget₁.symm
  have hproduct₀ : 0 ≤ 2 * (1 - abundanceTarget) ^ 2 := by positivity
  have hproduct₁ : 2 * (1 - abundanceTarget) ^ 2 ≤ 1 := by
    norm_num [abundanceTarget]
  have hlog := log_nonpos hproduct₀ hproduct₁
  have hlogExpand :
      log (2 * (1 - abundanceTarget) ^ 2) =
        log 2 + 2 * log (1 - abundanceTarget) := by
    rw [log_mul (by norm_num) (pow_ne_zero 2 hcomplement₀), log_pow]
    norm_num
  rw [hlogExpand] at hlog
  dsimp only [targetCappedGapSupport]
  rw [binEntropy, log_inv, log_inv]
  linarith

/-- At the candidate mean, the capped diagonal entropy gap lies below one affine support. -/
theorem cappedEntropyGap_le_targetSupport {x : ℝ}
    (hx₀ : 0 ≤ x) (hxHalf : x ≤ 1 / 2) :
    cappedEntropyGap x ≤ targetCappedGapSupport x := by
  have htarget₀ : 0 < abundanceTarget := by norm_num [abundanceTarget]
  have htarget₁ : abundanceTarget < 1 := by norm_num [abundanceTarget]
  by_cases hxQuarter : x ≤ 1 / 4
  · let leftWeight := 1 - 4 * x
    let rightWeight := 4 * x
    have hzeroMem : (0 : ℝ) ∈ Icc 0 (1 / 4) := by norm_num
    have hquarterMem : (1 / 4 : ℝ) ∈ Icc 0 (1 / 4) := by norm_num
    have hleftWeight : 0 ≤ leftWeight := by
      dsimp only [leftWeight]
      linarith
    have hrightWeight : 0 ≤ rightWeight := by
      dsimp only [rightWeight]
      linarith
    have hweightSum : leftWeight + rightWeight = 1 := by
      dsimp only [leftWeight, rightWeight]
      ring
    have hchord := lowCappedEntropyGap_convexOn.2 hzeroMem hquarterMem
      hleftWeight hrightWeight hweightSum
    dsimp only [smul_eq_mul] at hchord
    have hpoint : leftWeight * 0 + rightWeight * (1 / 4) = x := by
      dsimp only [leftWeight, rightWeight]
      ring
    rw [hpoint] at hchord
    have hzeroSupport :
        lowCappedEntropyGap 0 ≤ targetCappedGapSupport 0 := by
      simpa only [lowCappedEntropyGap, binEntropy_zero, mul_zero, sub_self] using
        targetCappedGapSupport_zero_nonneg
    have hquarterTangent := binEntropy_le_tangent htarget₀ htarget₁
      (show (0 : ℝ) ≤ 1 / 4 by norm_num) (show (1 / 4 : ℝ) ≤ 1 by norm_num)
    have hquarterSupport :
        lowCappedEntropyGap (1 / 4) ≤ targetCappedGapSupport (1 / 4) := by
      have hhalf : binEntropy (1 / 2) = log 2 := by
        convert binEntropy_two_inv using 1
        norm_num
      dsimp only [lowCappedEntropyGap, targetCappedGapSupport]
      rw [show 2 * (1 / 4 : ℝ) = 1 / 2 by norm_num, hhalf]
      linarith
    have hleftScaled := mul_le_mul_of_nonneg_left hzeroSupport hleftWeight
    have hrightScaled := mul_le_mul_of_nonneg_left hquarterSupport hrightWeight
    calc
      cappedEntropyGap x = lowCappedEntropyGap x := by
        rw [cappedEntropyGap, lowCappedEntropyGap,
          min_eq_left (show 2 * x ≤ 1 / 2 by linarith)]
      _ ≤ leftWeight * lowCappedEntropyGap 0 +
          rightWeight * lowCappedEntropyGap (1 / 4) := hchord
      _ ≤ leftWeight * targetCappedGapSupport 0 +
          rightWeight * targetCappedGapSupport (1 / 4) :=
        add_le_add hleftScaled hrightScaled
      _ = targetCappedGapSupport x := by
        dsimp only [leftWeight, rightWeight, targetCappedGapSupport]
        ring
  · have htangent := binEntropy_le_tangent htarget₀ htarget₁ hx₀ (by linarith)
    have hhalf : binEntropy (1 / 2) = log 2 := by
      convert binEntropy_two_inv using 1
      norm_num
    calc
      cappedEntropyGap x = 2 * binEntropy x - log 2 := by
        rw [cappedEntropyGap, min_eq_right (show (1 / 2 : ℝ) ≤ 2 * x by linarith)]
        rw [hhalf]
      _ ≤ targetCappedGapSupport x := by
        dsimp only [targetCappedGapSupport]
        linarith

/-- Spreading a target-mean diagonal law loses at most twice its marginal entropy deficit. -/
theorem diagonalDependent_deficit_le
    {lowerWeight upperWeight lower upper : ℝ}
    (hlowerWeight : 0 ≤ lowerWeight) (hupperWeight : 0 ≤ upperWeight)
    (hweight : lowerWeight + upperWeight = 1)
    (hlower : lower ∈ Icc (0 : ℝ) (1 / 2))
    (hupper : upper ∈ Icc (0 : ℝ) (1 / 2))
    (hmean : lowerWeight * lower + upperWeight * upper = abundanceTarget) :
    log 2 -
        (lowerWeight * binEntropy (min (2 * lower) (1 / 2)) +
          upperWeight * binEntropy (min (2 * upper) (1 / 2))) ≤
      2 * binarySpreadDeficit binEntropy
        lowerWeight upperWeight lower upper := by
  have hlowerSupport := cappedEntropyGap_le_targetSupport hlower.1 hlower.2
  have hupperSupport := cappedEntropyGap_le_targetSupport hupper.1 hupper.2
  have hlowerScaled := mul_le_mul_of_nonneg_left hlowerSupport hlowerWeight
  have hupperScaled := mul_le_mul_of_nonneg_left hupperSupport hupperWeight
  have hweighted := add_le_add hlowerScaled hupperScaled
  have hsupportAverage :
      lowerWeight * targetCappedGapSupport lower +
          upperWeight * targetCappedGapSupport upper =
        2 * binEntropy abundanceTarget - log 2 := by
    calc
      lowerWeight * targetCappedGapSupport lower +
          upperWeight * targetCappedGapSupport upper =
        (lowerWeight + upperWeight) *
            (2 * binEntropy abundanceTarget - log 2) +
          2 * (log (1 - abundanceTarget) - log abundanceTarget) *
            ((lowerWeight * lower + upperWeight * upper) -
              (lowerWeight + upperWeight) * abundanceTarget) := by
          dsimp only [targetCappedGapSupport]
          ring
      _ = 2 * binEntropy abundanceTarget - log 2 := by
        rw [hweight, hmean]
        ring
  rw [hsupportAverage] at hweighted
  dsimp only [cappedEntropyGap] at hweighted
  dsimp only [binarySpreadDeficit]
  rw [hmean]
  linarith

/-- The diagonal coupling at the candidate mean has maximal binary entropy. -/
theorem dependentCost_target_self_eq_log_two :
    dependentCost abundanceTarget abundanceTarget = log 2 := by
  rw [dependentCost_self_eq_cappedEntropy abundanceTarget_lt_half.le,
    min_eq_right (show (1 / 2 : ℝ) ≤ 2 * abundanceTarget by
      norm_num [abundanceTarget])]
  convert binEntropy_two_inv using 1
  norm_num

/-- Every target-mean binary diagonal law has objective at least that of the point mass. -/
theorem diagonalPairObjective_point_le
    {lowerWeight upperWeight lower upper : ℝ}
    (hlowerWeight : 0 ≤ lowerWeight) (hupperWeight : 0 ≤ upperWeight)
    (hweight : lowerWeight + upperWeight = 1)
    (hlower : lower ∈ Icc (0 : ℝ) (1 / 2))
    (hupper : upper ∈ Icc (0 : ℝ) (1 / 2))
    (hmean : lowerWeight * lower + upperWeight * upper = abundanceTarget) :
    diagonalPairObjective 1 0 abundanceTarget abundanceTarget ≤
      diagonalPairObjective lowerWeight upperWeight lower upper := by
  let deficit := binarySpreadDeficit binEntropy lowerWeight upperWeight lower upper
  let independent :=
    lowerWeight ^ 2 * binEntropy (join lower lower) +
      2 * lowerWeight * upperWeight * binEntropy (join lower upper) +
      upperWeight ^ 2 * binEntropy (join upper upper)
  let marginal := lowerWeight * binEntropy lower + upperWeight * binEntropy upper
  let dependent :=
    lowerWeight * binEntropy (min (2 * lower) (1 / 2)) +
      upperWeight * binEntropy (min (2 * upper) (1 / 2))
  let pointIndependent := binEntropy (join abundanceTarget abundanceTarget)
  have hdeficit : deficit = binEntropy abundanceTarget - marginal := by
    dsimp only [deficit, marginal, binarySpreadDeficit]
    rw [hmean]
  have hdeficitNonneg : 0 ≤ deficit :=
    binarySpreadDeficit_nonneg hlowerWeight hupperWeight hweight
      ⟨hlower.1, hlower.2.trans (by norm_num)⟩
      ⟨hupper.1, hupper.2.trans (by norm_num)⟩
  have hindependent :
      pointIndependent - independent ≤
        ((1 - abundanceTarget) / (1 + abundanceTarget) +
          (1 - 4 * abundanceTarget / 3)) * deficit := by
    simpa only [pointIndependent, independent, deficit] using
      diagonalIndependent_deficit_le hlowerWeight hupperWeight hweight hlower
        (show abundanceTarget ∈ Icc (0 : ℝ) (1 / 2) by
          exact ⟨abundanceTarget_gt_three_eighths.le.trans' (by norm_num),
            abundanceTarget_lt_half.le⟩)
        hupper hmean
  have hdependent :
      log 2 - dependent ≤ 2 * deficit := by
    simpa only [dependent, deficit] using
      diagonalDependent_deficit_le hlowerWeight hupperWeight hweight hlower hupper hmean
  have hindependentShare : 0 ≤ 1 - dependentShare := by
    norm_num [dependentShare]
  have hdependentShare : 0 ≤ dependentShare := by
    norm_num [dependentShare]
  have hindependentScaled :=
    mul_le_mul_of_nonneg_left hindependent hindependentShare
  have hdependentScaled :=
    mul_le_mul_of_nonneg_left hdependent hdependentShare
  have hcoefficient :
      (1 - dependentShare) *
            ((1 - abundanceTarget) / (1 + abundanceTarget) +
              (1 - 4 * abundanceTarget / 3)) +
          dependentShare * 2 ≤
        1 + entropySlack := by
    norm_num [dependentShare, entropySlack, abundanceTarget]
  have hcoefficientScaled :
      (1 - dependentShare) *
            (((1 - abundanceTarget) / (1 + abundanceTarget) +
              (1 - 4 * abundanceTarget / 3)) * deficit) +
          dependentShare * (2 * deficit) ≤
        (1 + entropySlack) * deficit := by
    calc
      (1 - dependentShare) *
            (((1 - abundanceTarget) / (1 + abundanceTarget) +
              (1 - 4 * abundanceTarget / 3)) * deficit) +
          dependentShare * (2 * deficit) =
        ((1 - dependentShare) *
              ((1 - abundanceTarget) / (1 + abundanceTarget) +
                (1 - 4 * abundanceTarget / 3)) +
            dependentShare * 2) * deficit := by ring
      _ ≤ (1 + entropySlack) * deficit :=
        mul_le_mul_of_nonneg_right hcoefficient hdeficitNonneg
  have htotal := (add_le_add hindependentScaled hdependentScaled).trans hcoefficientScaled
  have hpointObjective :
      diagonalPairObjective 1 0 abundanceTarget abundanceTarget =
        (1 - dependentShare) * pointIndependent + dependentShare * log 2 -
          (1 + entropySlack) * binEntropy abundanceTarget := by
    unfold diagonalPairObjective yuGap
    rw [dependentCost_target_self_eq_log_two]
    dsimp only [pointIndependent]
    ring
  have hobjective :
      diagonalPairObjective lowerWeight upperWeight lower upper =
        (1 - dependentShare) * independent + dependentShare * dependent -
          (1 + entropySlack) * marginal := by
    unfold diagonalPairObjective yuGap
    rw [dependentCost_self_eq_cappedEntropy hlower.2,
      dependentCost_self_eq_cappedEntropy hupper.2]
  rw [hpointObjective, hobjective]
  rw [hdeficit] at htotal
  linarith

private def diagonalPointRectangle : RatRectangle :=
  ⟨RatBall.point 0, RatBall.point 0⟩

private def diagonalPointDual : DualBall :=
  { value :=
      { center := (17879639045548115 : ℚ) / 18446744073709551616
        radius := (232381337554275 : ℚ) / 18446744073709551616 }
    gradient := some
      ({ center := 0
         radius := (149073401575459 : ℚ) / 4611686018427387904 },
       { center := 0, radius := 0 }) }

private theorem lowerRegionExpression_point_nonneg :
    0 ≤ CertificateObjective.lowerRegionExpression.eval 0 0 := by
  have hhorizontal : diagonalPointRectangle.horizontal.Contains (0 : ℝ) := by
    norm_num [diagonalPointRectangle, RatBall.point, RatBall.Contains]
  have hvertical : diagonalPointRectangle.vertical.Contains (0 : ℝ) := by
    norm_num [diagonalPointRectangle, RatBall.point, RatBall.Contains]
  have hdomain := CertificateObjective.lowerRegionExpression_domain
    (show (0 : ℝ) ≤ 0 by norm_num)
    (show (0 : ℝ) ≤ 2 * abundanceTarget by norm_num [abundanceTarget])
    (show (0 : ℝ) ≤ 0 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num)
  have hencloses := evaluateDual_encloses hhorizontal hvertical hdomain
    (show evaluateDual 12 64 64 diagonalPointRectangle
      CertificateObjective.lowerRegionExpression = some diagonalPointDual by rfl)
  have hbounds := RatBall.contains_iff_bounds.mp hencloses.1
  have hlower : (0 : ℝ) ≤ diagonalPointDual.value.lower := by
    norm_num [diagonalPointDual, RatBall.lower]
  exact hlower.trans hbounds.1

/-- The point-mass diagonal objective is strictly feasible at the candidate mean. -/
theorem diagonalPairObjective_point_nonneg :
    0 ≤ diagonalPairObjective 1 0 abundanceTarget abundanceTarget := by
  have hpoint := lowerRegionExpression_point_nonneg
  rw [CertificateObjective.lowerRegionExpression_eval
    (show lowerRegionLowerMean 0 0 ≤ (1 : ℝ) / 2 by
      norm_num [lowerRegionLowerMean, abundanceTarget])
    (show lowerRegionUpperMean 0 ≤ (1 : ℝ) / 2 by
      norm_num [lowerRegionUpperMean, abundanceTarget])] at hpoint
  simpa [lowerRegionDiagonalObjective, lowerRegionLowerMean,
    lowerRegionUpperMean] using hpoint

/-- Every target-mean binary diagonal law satisfies Yu's strict affine entropy inequality. -/
theorem diagonalPairObjective_nonneg
    {lowerWeight upperWeight lower upper : ℝ}
    (hlowerWeight : 0 ≤ lowerWeight) (hupperWeight : 0 ≤ upperWeight)
    (hweight : lowerWeight + upperWeight = 1)
    (hlower : lower ∈ Icc (0 : ℝ) (1 / 2))
    (hupper : upper ∈ Icc (0 : ℝ) (1 / 2))
    (hmean : lowerWeight * lower + upperWeight * upper = abundanceTarget) :
    0 ≤ diagonalPairObjective lowerWeight upperWeight lower upper :=
  diagonalPairObjective_point_nonneg.trans
    (diagonalPairObjective_point_le hlowerWeight hupperWeight hweight hlower hupper hmean)

/-- The lower certificate coordinates preserve the candidate mean exactly. -/
theorem lowerRegion_weighted_mean {upperWeight displacement : ℝ}
    (hweightUpper : upperWeight ≤ 2 * abundanceTarget) :
    (1 - upperWeight) * lowerRegionLowerMean upperWeight displacement +
        upperWeight * lowerRegionUpperMean displacement =
      abundanceTarget := by
  have hweightOne : upperWeight < 1 :=
    hweightUpper.trans_lt (by nlinarith [abundanceTarget_lt_half])
  let displacementBudget := displacement * (1 / 2 - abundanceTarget)
  have hcancel :
    (1 - upperWeight) * (displacementBudget / (1 - upperWeight)) =
        displacementBudget :=
    mul_div_cancel₀ displacementBudget (sub_ne_zero.mpr hweightOne.ne')
  change (1 - upperWeight) *
        (abundanceTarget - upperWeight * (displacementBudget / (1 - upperWeight))) +
      upperWeight * (abundanceTarget + displacementBudget) = abundanceTarget
  calc
    (1 - upperWeight) *
          (abundanceTarget - upperWeight * (displacementBudget / (1 - upperWeight))) +
        upperWeight * (abundanceTarget + displacementBudget) =
      abundanceTarget + upperWeight *
        (displacementBudget -
          (1 - upperWeight) * (displacementBudget / (1 - upperWeight))) := by ring
    _ = abundanceTarget := by rw [hcancel]; ring

/-- The upper certificate coordinates preserve the candidate mean exactly. -/
theorem upperRegion_weighted_mean {upperWeight displacement : ℝ}
    (hweightLower : 2 * abundanceTarget ≤ upperWeight) :
    (1 - upperWeight) * upperRegionLowerMean displacement +
        upperWeight * upperRegionUpperMean upperWeight displacement =
      abundanceTarget := by
  have hweightPositive : 0 < upperWeight :=
    (show 0 < 2 * abundanceTarget by norm_num [abundanceTarget]).trans_le hweightLower
  dsimp only [upperRegionLowerMean, upperRegionUpperMean]
  field_simp [hweightPositive.ne']
  ring

/-- Analytic discharge of the entire lower diagonal certificate rectangle. -/
theorem lowerRegionDiagonalObjective_nonneg {upperWeight displacement : ℝ}
    (hweightLower : 0 ≤ upperWeight)
    (hweightUpper : upperWeight ≤ 2 * abundanceTarget)
    (hdisplacementLower : 0 ≤ displacement) (hdisplacementUpper : displacement ≤ 1) :
    0 ≤ lowerRegionDiagonalObjective upperWeight displacement := by
  have hmeans := CertificateObjective.lowerRegion_means_mem hweightLower hweightUpper
    hdisplacementLower hdisplacementUpper
  rw [lowerRegionDiagonalObjective]
  apply diagonalPairObjective_nonneg
  · nlinarith [abundanceTarget_lt_half]
  · exact hweightLower
  · ring
  · exact hmeans.1
  · exact hmeans.2
  · exact lowerRegion_weighted_mean hweightUpper

/-- Analytic discharge of the entire upper diagonal certificate rectangle. -/
theorem upperRegionDiagonalObjective_nonneg {upperWeight displacement : ℝ}
    (hweightLower : 2 * abundanceTarget ≤ upperWeight)
    (hweightUpper : upperWeight ≤ 1)
    (hdisplacementLower : 0 ≤ displacement) (hdisplacementUpper : displacement ≤ 1) :
    0 ≤ upperRegionDiagonalObjective upperWeight displacement := by
  have hmeans := CertificateObjective.upperRegion_means_mem hweightLower hweightUpper
    hdisplacementLower hdisplacementUpper
  rw [upperRegionDiagonalObjective]
  apply diagonalPairObjective_nonneg
  · exact sub_nonneg.2 hweightUpper
  · exact (show (0 : ℝ) ≤ 2 * abundanceTarget by
      norm_num [abundanceTarget]).trans hweightLower
  · ring
  · exact hmeans.1
  · exact hmeans.2
  · exact upperRegion_weighted_mean hweightLower

end Frankl
