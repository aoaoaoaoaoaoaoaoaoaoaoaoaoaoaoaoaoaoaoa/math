import Frankl.TwoOrbit
import Mathlib.Data.Complex.ExponentialBounds

namespace Frankl

open Real Set

/-- Exact rational dependent-coupling share in the strict Yu gap. -/
abbrev dependentShareQ : ℚ := 356069804374481 / 10000000000000000

/-- Real-valued dependent-coupling share used by the analytic reduction. -/
noncomputable def dependentShare : ℝ := dependentShareQ

/-- Exact rational multiplicative slack in the marginal entropy term. -/
abbrev entropySlackQ : ℚ := 1 / 1000000000000000000

/-- Real-valued strict multiplicative slack used by the analytic reduction. -/
noncomputable def entropySlack : ℝ := entropySlackQ

/-- The linear marginal coefficient after normalizing the independent term of the strict Yu
gap. -/
noncomputable def marginalPenalty : ℝ := (1 + entropySlack) / (1 - dependentShare)

/-- The complement of the candidate abundance threshold. -/
noncomputable def targetComplement : ℝ := 1 - abundanceTarget

/-- The unique inflection point of the half-support scalar kernel. -/
noncomputable def halfSupportInflection : ℝ :=
  (2 * targetComplement - marginalPenalty) /
    (targetComplement * (2 - marginalPenalty))

theorem marginalPenalty_pos : 0 < marginalPenalty := by
  norm_num [marginalPenalty, entropySlack, dependentShare]

theorem marginalPenalty_lt_two : marginalPenalty < 2 := by
  norm_num [marginalPenalty, entropySlack, dependentShare]

theorem targetComplement_pos : 0 < targetComplement := by
  norm_num [targetComplement, abundanceTarget]

theorem targetComplement_lt_one : targetComplement < 1 := by
  norm_num [targetComplement, abundanceTarget]

theorem halfSupportInflection_pos : 0 < halfSupportInflection := by
  norm_num [halfSupportInflection, targetComplement, marginalPenalty, entropySlack,
    dependentShare, abundanceTarget]

theorem halfSupportInflection_lt_half : halfSupportInflection < (1 : ℝ) / 2 := by
  norm_num [halfSupportInflection, targetComplement, marginalPenalty, entropySlack,
    dependentShare, abundanceTarget]

/-- The scalar obstruction to replacing a point above one half by its mean-preserving endpoint
mixture. -/
noncomputable def halfSupportScalar (z : ℝ) : ℝ :=
  z * (4 * binEntropy (targetComplement / 2) - 2 * marginalPenalty * log 2)
    + marginalPenalty * binEntropy z
    - 2 * binEntropy (targetComplement * z)

private noncomputable def halfSupportScalarDeriv (z : ℝ) : ℝ :=
  4 * binEntropy (targetComplement / 2) - 2 * marginalPenalty * log 2
    + marginalPenalty * (log (1 - z) - log z)
    - 2 * targetComplement
      * (log (1 - targetComplement * z) - log (targetComplement * z))

private noncomputable def halfSupportScalarDeriv2 (z : ℝ) : ℝ :=
  marginalPenalty * (-1 / (1 - z) - 1 / z)
    - 2 * targetComplement ^ 2
      * (-1 / (1 - targetComplement * z) - 1 / (targetComplement * z))

private theorem hasDerivAt_halfSupportScalar {z : ℝ}
    (hz₀ : z ≠ 0) (hz₁ : z ≠ 1)
    (hrz₀ : targetComplement * z ≠ 0) (hrz₁ : targetComplement * z ≠ 1) :
    HasDerivAt halfSupportScalar (halfSupportScalarDeriv z) z := by
  have hlinear : HasDerivAt
      (fun x : ℝ ↦ x *
        (4 * binEntropy (targetComplement / 2) - 2 * marginalPenalty * log 2))
      (4 * binEntropy (targetComplement / 2) - 2 * marginalPenalty * log 2) z := by
    simpa only [id_eq, one_mul] using (hasDerivAt_id z).mul_const
      (4 * binEntropy (targetComplement / 2) - 2 * marginalPenalty * log 2)
  have hmarginal := (hasDerivAt_binEntropy hz₀ hz₁).const_mul marginalPenalty
  have hscaled : HasDerivAt (fun x : ℝ ↦ targetComplement * x) targetComplement z := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id z).const_mul targetComplement
  have hreplacement := (hasDerivAt_binEntropy hrz₀ hrz₁).comp z hscaled |>.const_mul 2
  convert (hlinear.add hmarginal).sub hreplacement using 1
  simp only [halfSupportScalar, halfSupportScalarDeriv]
  ring

private theorem hasDerivAt_halfSupportScalarDeriv {z : ℝ}
    (hz₀ : z ≠ 0) (hz₁ : z ≠ 1)
    (hrz₀ : targetComplement * z ≠ 0) (hrz₁ : targetComplement * z ≠ 1) :
    HasDerivAt halfSupportScalarDeriv (halfSupportScalarDeriv2 z) z := by
  have hzlog : HasDerivAt (fun x : ℝ ↦ log x) z⁻¹ z := by
    simpa only [id_eq, one_div] using (hasDerivAt_id z).log hz₀
  have hzcomplog : HasDerivAt (fun x : ℝ ↦ log (1 - x)) (-1 / (1 - z)) z := by
    simpa only [id_eq] using
      ((hasDerivAt_id z).const_sub 1).log (sub_ne_zero.mpr hz₁.symm)
  have hscaled : HasDerivAt (fun x : ℝ ↦ targetComplement * x) targetComplement z := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id z).const_mul targetComplement
  have hscaledlog : HasDerivAt (fun x : ℝ ↦ log (targetComplement * x))
      (targetComplement / (targetComplement * z)) z := by
    simpa only [one_div] using hscaled.log hrz₀
  have hscaledcomplog : HasDerivAt
      (fun x : ℝ ↦ log (1 - targetComplement * x))
      (-targetComplement / (1 - targetComplement * z)) z := by
    simpa only [one_div] using
      (hscaled.const_sub 1 |>.log (sub_ne_zero.mpr hrz₁.symm))
  convert ((hzcomplog.sub hzlog).const_mul marginalPenalty).sub
    ((hscaledcomplog.sub hscaledlog).const_mul (2 * targetComplement)) |>.const_add
      (4 * binEntropy (targetComplement / 2) - 2 * marginalPenalty * log 2) using 1
  · funext x
    simp only [halfSupportScalarDeriv]
    ring
  · simp only [halfSupportScalarDeriv2]
    ring

private theorem halfSupportScalarDeriv2_eq {z : ℝ}
    (hz₀ : z ≠ 0) (hz₁ : z ≠ 1)
    (hrz₁ : targetComplement * z ≠ 1) :
    halfSupportScalarDeriv2 z =
      (2 * targetComplement * (1 - z)
          - marginalPenalty * (1 - targetComplement * z)) /
        (z * (1 - z) * (1 - targetComplement * z)) := by
  have hr₀ : targetComplement ≠ 0 := targetComplement_pos.ne'
  have hrz₀ : targetComplement * z ≠ 0 := mul_ne_zero hr₀ hz₀
  dsimp [halfSupportScalarDeriv2]
  field_simp [hz₀, sub_ne_zero.mpr hz₁.symm, hr₀, hrz₀,
    sub_ne_zero.mpr hrz₁.symm]
  ring

private theorem halfSupportNumerator_eq (z : ℝ) :
    2 * targetComplement * (1 - z)
        - marginalPenalty * (1 - targetComplement * z) =
      targetComplement * (2 - marginalPenalty) * (halfSupportInflection - z) := by
  have hr₀ : targetComplement ≠ 0 := targetComplement_pos.ne'
  have hw₂ : 2 - marginalPenalty ≠ 0 := sub_ne_zero.mpr marginalPenalty_lt_two.ne'
  dsimp [halfSupportInflection]
  field_simp [hr₀, hw₂]
  ring

theorem halfSupportScalar_zero : halfSupportScalar 0 = 0 := by
  simp [halfSupportScalar]

theorem halfSupportScalar_half : halfSupportScalar (1 / 2) = 0 := by
  have hrhalf : targetComplement * (1 / 2 : ℝ) = targetComplement / 2 := by ring
  rw [halfSupportScalar, hrhalf]
  rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, binEntropy_two_inv]
  ring

private theorem log_one_add_target_le :
    log (1 + abundanceTarget) ≤ (41 : ℝ) / 125 := by
  let q : ℝ := 2541 / 2500
  have htargetPos : 0 < 1 + abundanceTarget := by
    norm_num [abundanceTarget]
  have hqPos : 0 < q := by norm_num [q]
  have hpower : 1 + abundanceTarget ≤ q ^ 20 := by
    norm_num [abundanceTarget, q]
  have hlogPower := log_le_log htargetPos hpower
  rw [log_pow] at hlogPower
  have hlogQ := log_le_sub_one_of_pos hqPos
  dsimp only [q] at hlogPower hlogQ
  norm_num at hlogPower hlogQ ⊢
  nlinarith

private theorem halfSupportScalarDeriv_half_pos :
    0 < halfSupportScalarDeriv (1 / 2) := by
  have htargetOne : 1 - targetComplement / 2 = (1 + abundanceTarget) / 2 := by
    dsimp [targetComplement]
    ring
  have htargetPos : 0 < 1 + abundanceTarget := by
    norm_num [abundanceTarget]
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  have hlogTarget :
      log ((1 + abundanceTarget) / 2) = log (1 + abundanceTarget) - log 2 := by
    rw [log_div htargetPos.ne' htwo]
  have hentropy :
      binEntropy (targetComplement / 2) =
        -(targetComplement / 2) * log (targetComplement / 2)
          - (1 - targetComplement / 2) * log (1 - targetComplement / 2) := by
    rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    simp only [negMulLog]
    ring
  have hidentity :
      halfSupportScalarDeriv (1 / 2) =
        -4 * log ((1 + abundanceTarget) / 2) - 2 * marginalPenalty * log 2 := by
    rw [halfSupportScalarDeriv, hentropy]
    rw [show 1 - (1 / 2 : ℝ) = 1 / 2 by norm_num]
    rw [show targetComplement * (1 / 2 : ℝ) = targetComplement / 2 by ring]
    rw [htargetOne]
    dsimp [targetComplement]
    ring
  have hlogTwoLower : (6931471803 : ℝ) / 10000000000 < log 2 := by
    rw [show (6931471803 : ℝ) / 10000000000 = 0.6931471803 by norm_num]
    exact log_two_gt_d9
  have hlogTargetUpper := log_one_add_target_le
  rw [hidentity, hlogTarget]
  norm_num [marginalPenalty, entropySlack, dependentShare]
  nlinarith

private theorem halfSupportScalar_continuous : Continuous halfSupportScalar := by
  unfold halfSupportScalar
  fun_prop

private theorem targetComplement_mul_mem {z : ℝ} (hz₀ : 0 < z) (hz₁ : z < 1) :
    0 < targetComplement * z ∧ targetComplement * z < 1 := by
  constructor
  · exact mul_pos targetComplement_pos hz₀
  · calc
      targetComplement * z < 1 * z := mul_lt_mul_of_pos_right targetComplement_lt_one hz₀
      _ = z := one_mul z
      _ < 1 := hz₁

private theorem halfSupportScalar_hasDerivAt {z : ℝ} (hz₀ : 0 < z) (hz₁ : z < 1) :
    HasDerivAt halfSupportScalar (halfSupportScalarDeriv z) z := by
  have hrz := targetComplement_mul_mem hz₀ hz₁
  exact hasDerivAt_halfSupportScalar hz₀.ne' hz₁.ne hrz.1.ne' hrz.2.ne

private theorem halfSupportScalarDeriv_hasDerivAt {z : ℝ} (hz₀ : 0 < z) (hz₁ : z < 1) :
    HasDerivAt halfSupportScalarDeriv (halfSupportScalarDeriv2 z) z := by
  have hrz := targetComplement_mul_mem hz₀ hz₁
  exact hasDerivAt_halfSupportScalarDeriv hz₀.ne' hz₁.ne hrz.1.ne' hrz.2.ne

private theorem halfSupportScalarDeriv2_nonneg {z : ℝ}
    (hz₀ : 0 < z) (hz₁ : z < 1) (hzInflection : z ≤ halfSupportInflection) :
    0 ≤ halfSupportScalarDeriv2 z := by
  have hrz := targetComplement_mul_mem hz₀ hz₁
  rw [halfSupportScalarDeriv2_eq hz₀.ne' hz₁.ne hrz.2.ne]
  rw [halfSupportNumerator_eq]
  exact div_nonneg
    (mul_nonneg
      (mul_nonneg targetComplement_pos.le (sub_nonneg.2 marginalPenalty_lt_two.le))
      (sub_nonneg.2 hzInflection))
    (mul_nonneg
      (mul_nonneg hz₀.le (sub_nonneg.2 hz₁.le)) (sub_nonneg.2 hrz.2.le))

private theorem halfSupportScalarDeriv2_nonpos {z : ℝ}
    (hz₀ : 0 < z) (hz₁ : z < 1) (hzInflection : halfSupportInflection ≤ z) :
    halfSupportScalarDeriv2 z ≤ 0 := by
  have hrz := targetComplement_mul_mem hz₀ hz₁
  rw [halfSupportScalarDeriv2_eq hz₀.ne' hz₁.ne hrz.2.ne]
  rw [halfSupportNumerator_eq]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg targetComplement_pos.le (sub_nonneg.2 marginalPenalty_lt_two.le))
      (sub_nonpos.2 hzInflection))
    (mul_nonneg
      (mul_nonneg hz₀.le (sub_nonneg.2 hz₁.le)) (sub_nonneg.2 hrz.2.le))

private theorem halfSupportScalar_convex_first :
    ConvexOn ℝ (Icc 0 halfSupportInflection) halfSupportScalar := by
  refine convexOn_of_hasDerivWithinAt2_nonneg
    (f' := halfSupportScalarDeriv) (f'' := halfSupportScalarDeriv2)
    (convex_Icc 0 halfSupportInflection)
    halfSupportScalar_continuous.continuousOn ?_ ?_ ?_
  · intro z hz
    rw [interior_Icc] at hz
    exact (halfSupportScalar_hasDerivAt hz.1
      (hz.2.trans halfSupportInflection_lt_half |>.trans (by norm_num))).hasDerivWithinAt
  · intro z hz
    rw [interior_Icc] at hz
    exact (halfSupportScalarDeriv_hasDerivAt hz.1
      (hz.2.trans halfSupportInflection_lt_half |>.trans (by norm_num))).hasDerivWithinAt
  · intro z hz
    rw [interior_Icc] at hz
    exact halfSupportScalarDeriv2_nonneg hz.1
      (hz.2.trans halfSupportInflection_lt_half |>.trans (by norm_num)) hz.2.le

private theorem halfSupportScalarDeriv_continuousOn_second :
    ContinuousOn halfSupportScalarDeriv (Icc halfSupportInflection (1 / 2)) := by
  intro z hz
  have hz₀ : 0 < z := halfSupportInflection_pos.trans_le hz.1
  have hz₁ : z < 1 := hz.2.trans_lt (by norm_num)
  have hrz := targetComplement_mul_mem hz₀ hz₁
  apply ContinuousAt.continuousWithinAt
  have hlogZ : ContinuousAt log z := continuousAt_log hz₀.ne'
  have hlogOneSub : ContinuousAt (fun x : ℝ ↦ log (1 - x)) z :=
    (continuousAt_const.sub continuousAt_id).log (sub_ne_zero.mpr hz₁.ne')
  have hscaled : ContinuousAt (fun x : ℝ ↦ targetComplement * x) z :=
    continuousAt_const.mul continuousAt_id
  have hlogScaled : ContinuousAt (fun x : ℝ ↦ log (targetComplement * x)) z :=
    hscaled.log hrz.1.ne'
  have hlogOneSubScaled :
      ContinuousAt (fun x : ℝ ↦ log (1 - targetComplement * x)) z :=
    (continuousAt_const.sub hscaled).log (sub_ne_zero.mpr hrz.2.ne')
  exact (continuousAt_const.add
    (continuousAt_const.mul (hlogOneSub.sub hlogZ))).sub
      (continuousAt_const.mul (hlogOneSubScaled.sub hlogScaled))

private theorem halfSupportScalarDeriv_antitone_second :
    AntitoneOn halfSupportScalarDeriv (Icc halfSupportInflection (1 / 2)) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := halfSupportScalarDeriv2)
    (convex_Icc halfSupportInflection (1 / 2))
    halfSupportScalarDeriv_continuousOn_second ?_ ?_
  · intro z hz
    rw [interior_Icc] at hz
    exact (halfSupportScalarDeriv_hasDerivAt
      (halfSupportInflection_pos.trans hz.1) (hz.2.trans (by norm_num))).hasDerivWithinAt
  · intro z hz
    rw [interior_Icc] at hz
    exact halfSupportScalarDeriv2_nonpos (halfSupportInflection_pos.trans hz.1)
      (hz.2.trans (by norm_num)) hz.1.le

private theorem halfSupportScalar_strictMono_second :
    StrictMonoOn halfSupportScalar (Icc halfSupportInflection (1 / 2)) := by
  have hanti := halfSupportScalarDeriv_antitone_second
  refine strictMonoOn_of_hasDerivWithinAt_pos (f' := halfSupportScalarDeriv)
    (convex_Icc halfSupportInflection (1 / 2))
    halfSupportScalar_continuous.continuousOn ?_ ?_
  · intro z hz
    rw [interior_Icc] at hz
    exact (halfSupportScalar_hasDerivAt (halfSupportInflection_pos.trans hz.1)
      (hz.2.trans (by norm_num))).hasDerivWithinAt
  · intro z hz
    rw [interior_Icc] at hz
    have hzMem : z ∈ Icc halfSupportInflection (1 / 2) := ⟨hz.1.le, hz.2.le⟩
    have hhalfMem : (1 / 2 : ℝ) ∈ Icc halfSupportInflection (1 / 2) :=
      ⟨halfSupportInflection_lt_half.le, le_rfl⟩
    exact halfSupportScalarDeriv_half_pos.trans_le (hanti hzMem hhalfMem hz.2.le)

private theorem halfSupportScalar_inflection_neg :
    halfSupportScalar halfSupportInflection < 0 := by
  have hstrict := halfSupportScalar_strictMono_second
  have hinflectionMem : halfSupportInflection ∈ Icc halfSupportInflection (1 / 2) :=
    ⟨le_rfl, halfSupportInflection_lt_half.le⟩
  have hhalfMem : (1 / 2 : ℝ) ∈ Icc halfSupportInflection (1 / 2) :=
    ⟨halfSupportInflection_lt_half.le, le_rfl⟩
  have hlt := hstrict hinflectionMem hhalfMem halfSupportInflection_lt_half
  rwa [halfSupportScalar_half] at hlt

/-- The finite half-support replacement kernel has strictly favorable scalar cost at every
nontrivial replacement point. -/
theorem halfSupportScalar_neg {z : ℝ} (hz₀ : 0 < z) (hzHalf : z < 1 / 2) :
    halfSupportScalar z < 0 := by
  by_cases hzInflection : halfSupportInflection ≤ z
  · have hstrict := halfSupportScalar_strictMono_second
    have hzMem : z ∈ Icc halfSupportInflection (1 / 2) := ⟨hzInflection, hzHalf.le⟩
    have hhalfMem : (1 / 2 : ℝ) ∈ Icc halfSupportInflection (1 / 2) :=
      ⟨halfSupportInflection_lt_half.le, le_rfl⟩
    have hlt := hstrict hzMem hhalfMem hzHalf
    rwa [halfSupportScalar_half] at hlt
  · have hzInflection' : z < halfSupportInflection := lt_of_not_ge hzInflection
    have hconvex := halfSupportScalar_convex_first
    have hzeroMem : (0 : ℝ) ∈ Icc 0 halfSupportInflection :=
      ⟨le_rfl, halfSupportInflection_pos.le⟩
    have hinflectionMem : halfSupportInflection ∈ Icc 0 halfSupportInflection :=
      ⟨halfSupportInflection_pos.le, le_rfl⟩
    have hleftWeight : 0 ≤ (halfSupportInflection - z) / halfSupportInflection :=
      div_nonneg (sub_nonneg.2 hzInflection'.le) halfSupportInflection_pos.le
    have hrightWeight : 0 ≤ z / halfSupportInflection :=
      div_nonneg hz₀.le halfSupportInflection_pos.le
    have hweightSum :
        (halfSupportInflection - z) / halfSupportInflection
            + z / halfSupportInflection = 1 := by
      field_simp [halfSupportInflection_pos.ne']
    have hchord := hconvex.2 hzeroMem hinflectionMem hleftWeight hrightWeight hweightSum
    dsimp only [smul_eq_mul] at hchord
    have hpoint :
        (halfSupportInflection - z) / halfSupportInflection * 0
            + z / halfSupportInflection * halfSupportInflection = z := by
      field_simp [halfSupportInflection_pos.ne']
    rw [hpoint, halfSupportScalar_zero] at hchord
    have hrightNeg :
        z / halfSupportInflection * halfSupportScalar halfSupportInflection < 0 :=
      mul_neg_of_pos_of_neg (div_pos hz₀ halfSupportInflection_pos)
        halfSupportScalar_inflection_neg
    linarith

/-- The independent-versus-marginal entropy gain generated by replacing a point of complement
mass `z`. -/
noncomputable def halfSupportGain (z x : ℝ) : ℝ :=
  2 * z * binEntropy ((1 - x) / 2) - binEntropy (z * (1 - x))

theorem halfSupportScalar_eq_gain (z : ℝ) :
    halfSupportScalar z =
      2 * halfSupportGain z abundanceTarget - marginalPenalty * halfSupportGain z 0 := by
  have hcomplement : 1 - abundanceTarget = targetComplement := by
    rfl
  have hhalf : binEntropy ((1 - (0 : ℝ)) / 2) = log 2 := by
    rw [show (1 - (0 : ℝ)) / 2 = 2⁻¹ by norm_num, binEntropy_two_inv]
  rw [halfSupportScalar, halfSupportGain, halfSupportGain, hcomplement, hhalf]
  ring_nf

/-- The scalar inequality needed by every nontrivial half-support replacement. -/
theorem twice_gain_target_lt_penalty_gain_zero {z : ℝ} (hz₀ : 0 < z) (hzHalf : z < 1 / 2) :
    2 * halfSupportGain z abundanceTarget < marginalPenalty * halfSupportGain z 0 := by
  have hnegative := halfSupportScalar_neg hz₀ hzHalf
  rw [halfSupportScalar_eq_gain] at hnegative
  linarith

private noncomputable def entropySlope (x : ℝ) : ℝ := log (1 - x) - log x

private noncomputable def entropyCurvature (x : ℝ) : ℝ := -1 / (1 - x) - 1 / x

private theorem hasDerivAt_entropySlope {x : ℝ} (hx₀ : x ≠ 0) (hx₁ : x ≠ 1) :
    HasDerivAt entropySlope (entropyCurvature x) x := by
  have hleft := ((hasDerivAt_id x).const_sub 1).log (sub_ne_zero.mpr hx₁.symm)
  have hright := (hasDerivAt_id x).log hx₀
  simpa only [entropySlope, entropyCurvature, id_eq] using hleft.sub hright

private noncomputable def halfSupportGainDeriv (z x : ℝ) : ℝ :=
  z * (entropySlope (z * (1 - x)) - entropySlope ((1 - x) / 2))

private noncomputable def halfSupportGainDeriv2 (z x : ℝ) : ℝ :=
  z * (-z * entropyCurvature (z * (1 - x))
    + (1 / 2) * entropyCurvature ((1 - x) / 2))

private theorem halfSupportArguments_mem {z x : ℝ}
    (hz₀ : 0 < z) (hzHalf : z ≤ 1 / 2) (hx₀ : 0 ≤ x) (hx₁ : x < 1) :
    0 < z * (1 - x) ∧ z * (1 - x) < 1 ∧
      0 < (1 - x) / 2 ∧ (1 - x) / 2 < 1 := by
  have honeSub : 0 < 1 - x := sub_pos.2 hx₁
  have hz₁ : z < 1 := hzHalf.trans_lt (by norm_num)
  constructor
  · exact mul_pos hz₀ honeSub
  constructor
  · calc
      z * (1 - x) ≤ z * 1 := mul_le_mul_of_nonneg_left (sub_le_self 1 hx₀) hz₀.le
      _ = z := mul_one z
      _ < 1 := hz₁
  constructor
  · positivity
  · linarith

private theorem hasDerivAt_halfSupportGain {z x : ℝ}
    (hz₀ : 0 < z) (hzHalf : z ≤ 1 / 2) (hx₀ : 0 ≤ x) (hx₁ : x < 1) :
    HasDerivAt (halfSupportGain z) (halfSupportGainDeriv z x) x := by
  have hargs := halfSupportArguments_mem hz₀ hzHalf hx₀ hx₁
  have hhalfArg : HasDerivAt (fun y : ℝ ↦ (1 - y) / 2) (-1 / 2) x := by
    exact ((hasDerivAt_id x).const_sub 1).div_const 2
  have hscaledArg : HasDerivAt (fun y : ℝ ↦ z * (1 - y)) (-z) x := by
    convert ((hasDerivAt_id x).const_sub 1).const_mul z using 1
    ring
  have hhalfEntropy := (hasDerivAt_binEntropy hargs.2.2.1.ne' hargs.2.2.2.ne).comp x hhalfArg
  have hscaledEntropy := (hasDerivAt_binEntropy hargs.1.ne' hargs.2.1.ne).comp x hscaledArg
  convert (hhalfEntropy.const_mul (2 * z)).sub hscaledEntropy using 1
  simp only [halfSupportGain, halfSupportGainDeriv, entropySlope]
  ring

private theorem hasDerivAt_halfSupportGainDeriv {z x : ℝ}
    (hz₀ : 0 < z) (hzHalf : z ≤ 1 / 2) (hx₀ : 0 ≤ x) (hx₁ : x < 1) :
    HasDerivAt (halfSupportGainDeriv z) (halfSupportGainDeriv2 z x) x := by
  have hargs := halfSupportArguments_mem hz₀ hzHalf hx₀ hx₁
  have hhalfArg : HasDerivAt (fun y : ℝ ↦ (1 - y) / 2) (-1 / 2) x := by
    exact ((hasDerivAt_id x).const_sub 1).div_const 2
  have hscaledArg : HasDerivAt (fun y : ℝ ↦ z * (1 - y)) (-z) x := by
    convert ((hasDerivAt_id x).const_sub 1).const_mul z using 1
    ring
  have hhalfSlope := (hasDerivAt_entropySlope hargs.2.2.1.ne' hargs.2.2.2.ne).comp x hhalfArg
  have hscaledSlope := (hasDerivAt_entropySlope hargs.1.ne' hargs.2.1.ne).comp x hscaledArg
  convert (hscaledSlope.sub hhalfSlope).const_mul z using 1
  simp only [halfSupportGainDeriv, halfSupportGainDeriv2, id_eq]
  ring

private theorem halfSupportGainDeriv_nonneg {z x : ℝ}
    (hz₀ : 0 < z) (hzHalf : z ≤ 1 / 2) (hx₀ : 0 ≤ x) (hx₁ : x < 1) :
    0 ≤ halfSupportGainDeriv z x := by
  have hargs := halfSupportArguments_mem hz₀ hzHalf hx₀ hx₁
  let scaled := z * (1 - x)
  let halved := (1 - x) / 2
  have hscaledHalved : scaled ≤ halved := by
    dsimp [scaled, halved]
    nlinarith [mul_nonneg (sub_nonneg.2 hzHalf) (sub_pos.2 hx₁).le]
  have hlogScaled := log_le_log hargs.1 hscaledHalved
  have hlogComplements := log_le_log (sub_pos.2 hargs.2.2.2)
    (show 1 - halved ≤ 1 - scaled by linarith)
  dsimp only [scaled, halved] at hlogScaled hlogComplements
  dsimp [halfSupportGainDeriv, entropySlope]
  exact mul_nonneg hz₀.le (by linarith)

private theorem halfSupportGainDeriv2_nonpos {z x : ℝ}
    (hz₀ : 0 < z) (hzHalf : z ≤ 1 / 2) (hx₀ : 0 ≤ x) (hx₁ : x < 1) :
    halfSupportGainDeriv2 z x ≤ 0 := by
  have hargs := halfSupportArguments_mem hz₀ hzHalf hx₀ hx₁
  have honeSub : 0 < 1 - x := sub_pos.2 hx₁
  have honeAdd : 0 < 1 + x := by linarith
  have honeScaled : 0 < 1 - z * (1 - x) := sub_pos.2 hargs.2.1
  have hscaledCurvature :
      -z * entropyCurvature (z * (1 - x)) =
        1 / ((1 - x) * (1 - z * (1 - x))) := by
    dsimp [entropyCurvature]
    field_simp [hargs.1.ne', honeSub.ne', honeScaled.ne']
    ring
  have hhalfCurvature :
      (1 / 2 : ℝ) * entropyCurvature ((1 - x) / 2) =
        -2 / ((1 - x) * (1 + x)) := by
    dsimp [entropyCurvature]
    rw [show 1 - (1 - x) / 2 = (1 + x) / 2 by ring]
    field_simp [honeSub.ne', honeAdd.ne']
    ring
  have hidentity :
      halfSupportGainDeriv2 z x =
        z / (1 - x)
          * (1 / (1 - z * (1 - x)) - 2 / (1 + x)) := by
    rw [halfSupportGainDeriv2, hscaledCurvature, hhalfCurvature]
    field_simp [honeSub.ne', honeAdd.ne', honeScaled.ne']
    ring
  rw [hidentity]
  have hbracket : 1 / (1 - z * (1 - x)) - 2 / (1 + x) ≤ 0 := by
    rw [sub_nonpos, div_le_div_iff honeScaled honeAdd]
    nlinarith [mul_nonneg (sub_nonneg.2 hzHalf) honeSub.le]
  exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg hz₀.le honeSub.le) hbracket

private theorem halfSupportGain_continuous (z : ℝ) : Continuous (halfSupportGain z) := by
  unfold halfSupportGain
  fun_prop

/-- The half-support gain is increasing on the unit interval. -/
theorem halfSupportGain_monotone {z : ℝ} (hz₀ : 0 < z) (hzHalf : z ≤ 1 / 2) :
    MonotoneOn (halfSupportGain z) (Icc 0 1) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := halfSupportGainDeriv z)
    (convex_Icc 0 1) (halfSupportGain_continuous z |>.continuousOn) ?_ ?_
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_halfSupportGain hz₀ hzHalf hx.1.le hx.2).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact halfSupportGainDeriv_nonneg hz₀ hzHalf hx.1.le hx.2

/-- The half-support gain is concave on the unit interval. -/
theorem halfSupportGain_concave {z : ℝ} (hz₀ : 0 < z) (hzHalf : z ≤ 1 / 2) :
    ConcaveOn ℝ (Icc 0 1) (halfSupportGain z) := by
  refine concaveOn_of_hasDerivWithinAt2_nonpos
    (f' := halfSupportGainDeriv z) (f'' := halfSupportGainDeriv2 z)
    (convex_Icc 0 1) (halfSupportGain_continuous z |>.continuousOn) ?_ ?_ ?_
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_halfSupportGain hz₀ hzHalf hx.1.le hx.2).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_halfSupportGainDeriv hz₀ hzHalf hx.1.le hx.2).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact halfSupportGainDeriv2_nonpos hz₀ hzHalf hx.1.le hx.2

/-- The Bernoulli entropy graph lies above the chord joining zero to its maximum. -/
theorem two_mul_log_two_le_binEntropy {z : ℝ} (hz₀ : 0 ≤ z) (hzHalf : z ≤ 1 / 2) :
    2 * z * log 2 ≤ binEntropy z := by
  have hzero : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have hhalf : (1 / 2 : ℝ) ∈ Icc 0 1 := by norm_num
  have hleftWeight : 0 ≤ 1 - 2 * z := by linarith
  have hrightWeight : 0 ≤ 2 * z := by positivity
  have hweightSum : (1 - 2 * z) + 2 * z = 1 := by ring
  have hchord := strictConcave_binEntropy.concaveOn.2 hzero hhalf
    hleftWeight hrightWeight hweightSum
  dsimp only [smul_eq_mul] at hchord
  have hpoint : (1 - 2 * z) * 0 + 2 * z * (1 / 2 : ℝ) = z := by ring
  rw [hpoint, binEntropy_zero] at hchord
  rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, binEntropy_two_inv] at hchord
  linarith

/-- The Bernoulli parameter selected by Yu's dependent-union entropy term. -/
noncomputable def dependentParameter (p q : ℝ) : ℝ :=
  min (p + q) (max (max p q) (1 / 2))

/-- Yu's dependent-union entropy cost. -/
noncomputable def dependentCost (p q : ℝ) : ℝ := binEntropy (dependentParameter p q)

private theorem dependentCost_one_left {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    dependentCost 1 r = 0 := by
  rw [dependentCost, dependentParameter, max_eq_left hr₁,
    max_eq_left (show (1 / 2 : ℝ) ≤ 1 by norm_num), min_eq_right (by linarith),
    binEntropy_one]

/-- Replacing `1-z > 1/2` by mass `2z` at `1/2` and the remaining mass at `1` cannot increase
the dependent-union entropy cost, pointwise in the other coordinate. -/
theorem halfSupportDependentCost_le {z r : ℝ}
    (hz₀ : 0 ≤ z) (hzHalf : z ≤ 1 / 2) (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    2 * z * dependentCost (1 / 2) r
        + (1 - 2 * z) * dependentCost 1 r ≤ dependentCost (1 - z) r := by
  rw [dependentCost_one_left hr₀ hr₁]
  simp only [mul_zero, add_zero]
  have hyHalf : 1 / 2 ≤ 1 - z := by linarith
  by_cases hrHalf : r ≤ 1 / 2
  · have hhalfParameter : dependentParameter (1 / 2) r = 1 / 2 := by
      rw [dependentParameter, max_eq_left hrHalf, max_self]
      exact min_eq_right (by linarith)
    have hyParameter : dependentParameter (1 - z) r = 1 - z := by
      rw [dependentParameter, max_eq_left (hrHalf.trans hyHalf), max_eq_left hyHalf]
      exact min_eq_right (by linarith)
    rw [dependentCost, dependentCost, hhalfParameter, hyParameter, binEntropy_one_sub]
    rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, binEntropy_two_inv]
    exact two_mul_log_two_le_binEntropy hz₀ hzHalf
  · have hrHalf' : 1 / 2 < r := lt_of_not_ge hrHalf
    have hhalfParameter : dependentParameter (1 / 2) r = r := by
      rw [dependentParameter, max_eq_right hrHalf'.le, max_eq_left hrHalf'.le]
      exact min_eq_right (by linarith)
    by_cases hry : r ≤ 1 - z
    · have hyParameter : dependentParameter (1 - z) r = 1 - z := by
        rw [dependentParameter, max_eq_left hry, max_eq_left hyHalf]
        exact min_eq_right (by linarith)
      rw [dependentCost, dependentCost, hhalfParameter, hyParameter, binEntropy_one_sub]
      calc
        2 * z * binEntropy r ≤ 2 * z * log 2 :=
          mul_le_mul_of_nonneg_left binEntropy_le_log_two (by positivity)
        _ ≤ binEntropy z := two_mul_log_two_le_binEntropy hz₀ hzHalf
    · have hry' : 1 - z < r := lt_of_not_ge hry
      have hyParameter : dependentParameter (1 - z) r = r := by
        rw [dependentParameter, max_eq_right hry'.le, max_eq_left hrHalf'.le]
        exact min_eq_right (by linarith)
      rw [dependentCost, dependentCost, hhalfParameter, hyParameter]
      have hentropy : 0 ≤ binEntropy r := binEntropy_nonneg hr₀ hr₁
      nlinarith

end Frankl
