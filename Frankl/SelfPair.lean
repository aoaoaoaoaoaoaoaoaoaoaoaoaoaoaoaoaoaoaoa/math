import Frankl.OrbitContraction

namespace Frankl

open Real Set

private noncomputable def entropyDerivative (x : ℝ) : ℝ :=
  log (1 - x) - log x

private noncomputable def entropyDerivative2 (x : ℝ) : ℝ :=
  -1 / (1 - x) - 1 / x

private noncomputable def entropyDerivative3 (x : ℝ) : ℝ :=
  1 / x ^ 2 - 1 / (1 - x) ^ 2

private theorem hasDerivAt_entropyDerivative {x : ℝ} (hx₀ : x ≠ 0) (hx₁ : x ≠ 1) :
    HasDerivAt entropyDerivative (entropyDerivative2 x) x := by
  have hleft := ((hasDerivAt_id x).const_sub 1).log (sub_ne_zero.mpr hx₁.symm)
  have hright := (hasDerivAt_id x).log hx₀
  unfold entropyDerivative entropyDerivative2
  apply HasDerivAt.sub
  · exact hleft
  · exact hright

private theorem hasDerivAt_entropyDerivative2 {x : ℝ} (hx₀ : x ≠ 0) (hx₁ : x ≠ 1) :
    HasDerivAt entropyDerivative2 (entropyDerivative3 x) x := by
  have hleft := (((hasDerivAt_id x).const_sub 1).inv (sub_ne_zero.mpr hx₁.symm)).neg
  have hright := (hasDerivAt_id x).inv hx₀
  refine ((hleft.sub hright).congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp only [entropyDerivative3, id_eq, one_div]
    field_simp [hx₀, sub_ne_zero.mpr hx₁.symm]
    ring
  · exact Filter.Eventually.of_forall fun _ ↦ by
      simp only [entropyDerivative2, Pi.inv_apply, Pi.neg_apply, Pi.sub_apply, id_eq,
        div_eq_mul_inv]
      ring

/-- The continuous extension of `x h'(x²) - h'(x)` to `x=1`. -/
noncomputable def curvatureR (x : ℝ) : ℝ :=
  negMulLog (1 - x) + x * log (1 + x) + (1 - 2 * x) * log x

private noncomputable def curvatureRDeriv (x : ℝ) : ℝ :=
  log (1 - x) + 1 + log (1 + x) + x / (1 + x)
    - 2 * log x + (1 - 2 * x) / x

private noncomputable def curvatureRDeriv2 (x : ℝ) : ℝ :=
  -1 / (1 - x) + 1 / (1 + x) + 1 / (1 + x) ^ 2 - 2 / x - 1 / x ^ 2

private theorem hasDerivAt_curvatureR {x : ℝ} (hx₀ : x ≠ 0) (hx₁ : x ≠ 1)
    (hxneg₁ : x ≠ -1) : HasDerivAt curvatureR (curvatureRDeriv x) x := by
  have honeSub := (hasDerivAt_negMulLog (sub_ne_zero.mpr hx₁.symm)).comp x
    ((hasDerivAt_id x).const_sub 1)
  have honeAddNe : 1 + x ≠ 0 := by
    intro h
    apply hxneg₁
    linarith
  have honeAddLog := ((hasDerivAt_id x).const_add 1).log honeAddNe
  have hmiddle := (hasDerivAt_id x).mul honeAddLog
  have hcoefficient := (hasDerivAt_id x).const_mul 2 |>.const_sub 1
  have hlast := hcoefficient.mul ((hasDerivAt_id x).log hx₀)
  refine (((honeSub.add hmiddle).add hlast).congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp only [curvatureRDeriv, id_eq]
    ring
  · exact Filter.Eventually.of_forall fun _ ↦ by
      simp only [curvatureR, Function.comp_apply, Pi.add_apply, Pi.mul_apply, id_eq]

private theorem hasDerivAt_curvatureRDeriv {x : ℝ} (hx₀ : x ≠ 0) (hx₁ : x ≠ 1)
    (hxneg₁ : x ≠ -1) : HasDerivAt curvatureRDeriv (curvatureRDeriv2 x) x := by
  have honeSubLog := ((hasDerivAt_id x).const_sub 1).log (sub_ne_zero.mpr hx₁.symm)
  have honeAdd := (hasDerivAt_id x).const_add 1
  have honeAddNe : 1 + x ≠ 0 := by
    intro h
    apply hxneg₁
    linarith
  have honeAddLog := honeAdd.log honeAddNe
  have hfraction := (hasDerivAt_id x).div honeAdd honeAddNe
  have hlog := ((hasDerivAt_id x).log hx₀).const_mul 2
  have hcoefficient := (hasDerivAt_id x).const_mul 2 |>.const_sub 1
  have hlast := hcoefficient.div (hasDerivAt_id x) hx₀
  refine
    (((((honeSubLog.const_add 1).add honeAddLog).add hfraction).sub hlog |>.add hlast).congr_deriv
      ?_).congr_of_eventuallyEq ?_
  · simp only [curvatureRDeriv2, id_eq]
    field_simp [hx₀, sub_ne_zero.mpr hx₁.symm, honeAddNe]
    ring
  · exact Filter.Eventually.of_forall fun _ ↦ by
      simp only [curvatureRDeriv, Pi.add_apply, Pi.sub_apply, Pi.div_apply, id_eq]
      ring

private theorem curvatureRDeriv2_eq {x : ℝ} (hx₀ : x ≠ 0) (hx₁ : x ≠ 1)
    (hxneg₁ : x ≠ -1) :
    curvatureRDeriv2 x = (3 * x + 1) / (x ^ 2 * (x - 1) * (x + 1) ^ 2) := by
  have honeAddNe : x + 1 ≠ 0 := by
    intro h
    apply hxneg₁
    linarith
  have hdenominator : x ^ 2 * (x - 1) * (x + 1) ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hx₀) (sub_ne_zero.mpr hx₁))
      (pow_ne_zero 2 honeAddNe)
  have honeAddNe' : 1 + x ≠ 0 := by simpa [add_comm] using honeAddNe
  have honeSubNe : 1 - x ≠ 0 := sub_ne_zero.mpr hx₁.symm
  have h₁ : (-1 / (1 - x)) * (x ^ 2 * (x - 1) * (x + 1) ^ 2) =
      x ^ 2 * (x + 1) ^ 2 := by
    field_simp [honeSubNe]
    ring
  have h₂ : (1 / (1 + x)) * (x ^ 2 * (x - 1) * (x + 1) ^ 2) =
      x ^ 2 * (x - 1) * (x + 1) := by
    field_simp [honeAddNe']
    ring
  have h₃ : (1 / (1 + x) ^ 2) * (x ^ 2 * (x - 1) * (x + 1) ^ 2) =
      x ^ 2 * (x - 1) := by
    field_simp [honeAddNe']
    ring
  have h₄ : (-2 / x) * (x ^ 2 * (x - 1) * (x + 1) ^ 2) =
      -2 * x * (x - 1) * (x + 1) ^ 2 := by
    field_simp [hx₀]
  have h₅ : (-1 / x ^ 2) * (x ^ 2 * (x - 1) * (x + 1) ^ 2) =
      -(x - 1) * (x + 1) ^ 2 := by
    field_simp [hx₀]
  simp only [curvatureRDeriv2]
  apply (eq_div_iff hdenominator).2
  calc
    (-1 / (1 - x) + 1 / (1 + x) + 1 / (1 + x) ^ 2 - 2 / x - 1 / x ^ 2) *
        (x ^ 2 * (x - 1) * (x + 1) ^ 2) =
      (-1 / (1 - x)) * (x ^ 2 * (x - 1) * (x + 1) ^ 2)
        + (1 / (1 + x)) * (x ^ 2 * (x - 1) * (x + 1) ^ 2)
        + (1 / (1 + x) ^ 2) * (x ^ 2 * (x - 1) * (x + 1) ^ 2)
        + (-2 / x) * (x ^ 2 * (x - 1) * (x + 1) ^ 2)
        + (-1 / x ^ 2) * (x ^ 2 * (x - 1) * (x + 1) ^ 2) := by ring
    _ = x ^ 2 * (x + 1) ^ 2 + x ^ 2 * (x - 1) * (x + 1)
        + x ^ 2 * (x - 1) - 2 * x * (x - 1) * (x + 1) ^ 2
        - (x - 1) * (x + 1) ^ 2 := by
          rw [h₁, h₂, h₃, h₄, h₅]
          ring
    _ = 3 * x + 1 := by ring

/-- The kernel controlling the low-orbit self-pair deficit. -/
noncomputable def curvatureKernel (x y : ℝ) : ℝ :=
  curvatureR x - curvatureR y - (x - y) * entropyDerivative (x * y)

private noncomputable def curvatureKernelDeriv (x y : ℝ) : ℝ :=
  curvatureRDeriv x - entropyDerivative (x * y)
    - (x - y) * y * entropyDerivative2 (x * y)

private noncomputable def curvatureKernelDeriv2 (x y : ℝ) : ℝ :=
  curvatureRDeriv2 x - 2 * y * entropyDerivative2 (x * y)
    - (x - y) * y ^ 2 * entropyDerivative3 (x * y)

private theorem hasDerivAt_curvatureKernel {x y : ℝ}
    (hx₀ : x ≠ 0) (hx₁ : x ≠ 1) (hxneg₁ : x ≠ -1)
    (hxy₀ : x * y ≠ 0) (hxy₁ : x * y ≠ 1) :
    HasDerivAt (fun z ↦ curvatureKernel z y) (curvatureKernelDeriv x y) x := by
  have hr := hasDerivAt_curvatureR hx₀ hx₁ hxneg₁
  have hxy := (hasDerivAt_id x).mul_const y
  have he := (hasDerivAt_entropyDerivative hxy₀ hxy₁).comp x hxy
  have hcoefficient := (hasDerivAt_id x).sub_const y
  refine
    (((hr.sub_const (curvatureR y)).sub (hcoefficient.mul he)).congr_deriv
      ?_).congr_of_eventuallyEq ?_
  · simp only [curvatureKernelDeriv, id_eq, Function.comp_apply]
    ring
  · exact Filter.Eventually.of_forall fun _ ↦ by
      simp only [curvatureKernel, Function.comp_apply, Pi.sub_apply, Pi.mul_apply, id_eq]

private theorem hasDerivAt_curvatureKernelDeriv {x y : ℝ}
    (hx₀ : x ≠ 0) (hx₁ : x ≠ 1) (hxneg₁ : x ≠ -1)
    (hxy₀ : x * y ≠ 0) (hxy₁ : x * y ≠ 1) :
    HasDerivAt (fun z ↦ curvatureKernelDeriv z y) (curvatureKernelDeriv2 x y) x := by
  have hr := hasDerivAt_curvatureRDeriv hx₀ hx₁ hxneg₁
  have hxy := (hasDerivAt_id x).mul_const y
  have he1 := (hasDerivAt_entropyDerivative hxy₀ hxy₁).comp x hxy
  have he2 := (hasDerivAt_entropyDerivative2 hxy₀ hxy₁).comp x hxy
  have hcoefficient := ((hasDerivAt_id x).sub_const y).mul_const y
  refine (((hr.sub he1).sub (hcoefficient.mul he2)).congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp only [curvatureKernelDeriv2, id_eq, Function.comp_apply]
    ring
  · exact Filter.Eventually.of_forall fun _ ↦ by
      simp only [curvatureKernelDeriv, Function.comp_apply, Pi.sub_apply, Pi.mul_apply, id_eq]

private theorem curvatureKernelDeriv2_eq {x y : ℝ}
    (hx₀ : x ≠ 0) (hx₁ : x ≠ 1) (hxneg₁ : x ≠ -1)
    (hxy₀ : x * y ≠ 0) (hxy₁ : x * y ≠ 1) :
    curvatureKernelDeriv2 x y = curvaturePolynomial x y /
      (x ^ 2 * (1 - x) * (x + 1) ^ 2 * (1 - x * y) ^ 2) := by
  simp only [curvatureKernelDeriv2]
  have honeAddNe : 1 + x ≠ 0 := by
    intro h
    apply hxneg₁
    linarith
  have hdenominator :
      x ^ 2 * (1 - x) * (x + 1) ^ 2 * (1 - x * y) ^ 2 ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact mul_ne_zero (pow_ne_zero 2 hx₀) (sub_ne_zero.mpr hx₁.symm)
      · exact pow_ne_zero 2 (by simpa [add_comm] using honeAddNe)
    · exact pow_ne_zero 2 (sub_ne_zero.mpr hxy₁.symm)
  rw [eq_div_iff hdenominator]
  rw [curvatureRDeriv2_eq hx₀ hx₁ hxneg₁]
  simp only [entropyDerivative2, entropyDerivative3]
  have hy₀ : y ≠ 0 := by
    intro hy
    apply hxy₀
    simp [hy]
  have hRdenominator : x ^ 2 * (x - 1) * (x + 1) ^ 2 ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hx₀) (sub_ne_zero.mpr hx₁))
      (pow_ne_zero 2 (by simpa [add_comm] using honeAddNe))
  have honeAddExpanded : 1 + x * 2 + x ^ 2 ≠ 0 := by
    rw [show 1 + x * 2 + x ^ 2 = (1 + x) ^ 2 by ring]
    exact pow_ne_zero 2 honeAddNe
  field_simp [hx₀, hy₀, sub_ne_zero.mpr hx₁.symm, honeAddNe, hxy₀,
    sub_ne_zero.mpr hxy₁.symm, hRdenominator, honeAddExpanded]
  simp only [curvaturePolynomial]
  have honeAddSq : (x + 1) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (by simpa [add_comm] using honeAddNe)
  have hcancel : (x + 1) ^ 2 *
      (((3 * x + 1) * (1 - x * y)) / (x + 1) ^ 2) =
      (3 * x + 1) * (1 - x * y) :=
    mul_div_cancel₀ _ honeAddSq
  linear_combination ((1 - x * y) * (1 - x)) * hcancel

private theorem curvatureKernel_continuousOn {y : ℝ} (hy₀ : 0 < y) (hy₁ : y < 1) :
    ContinuousOn (fun x ↦ curvatureKernel x y) (Icc y 1) := by
  intro x hx
  have hx_pos : 0 < x := hy₀.trans_le hx.1
  have hx₀ : x ≠ 0 := hx_pos.ne'
  have honeAdd : 1 + x ≠ 0 := by linarith
  have hxy_pos : 0 < x * y := mul_pos (lt_of_lt_of_le hy₀ hx.1) hy₀
  have hxy_lt : x * y < 1 := by
    calc
      x * y ≤ 1 * y := mul_le_mul_of_nonneg_right hx.2 hy₀.le
      _ = y := one_mul y
      _ < 1 := hy₁
  have hconstOne : ContinuousAt (fun _ : ℝ ↦ (1 : ℝ)) x := continuousAt_const
  have hneg : ContinuousAt (fun z : ℝ ↦ negMulLog (1 - z)) x := by
    refine (continuous_negMulLog.continuousAt.comp
      (hconstOne.sub continuousAt_id)).congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun _ ↦ by
      simp only [Function.comp_apply, Pi.sub_apply, id_eq]
  have hlogOneAdd : ContinuousAt (fun z : ℝ ↦ log (1 + z)) x := by
    refine ((continuousAt_log honeAdd).comp
      (hconstOne.add continuousAt_id)).congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun _ ↦ by
      simp only [Function.comp_apply]
  have hlogX : ContinuousAt log x := continuousAt_log hx₀
  have hR : ContinuousAt curvatureR x := by
    exact (hneg.add (continuousAt_id.mul hlogOneAdd)).add
      ((continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).mul hlogX)
  have hproduct : ContinuousAt (fun z : ℝ ↦ z * y) x :=
    continuousAt_id.mul continuousAt_const
  have honeSubProduct : ContinuousAt (fun z : ℝ ↦ 1 - z * y) x :=
    continuousAt_const.sub hproduct
  have hlogOneSubProduct : ContinuousAt (fun z : ℝ ↦ log (1 - z * y)) x :=
    honeSubProduct.log (sub_pos.2 hxy_lt).ne'
  have hlogProduct : ContinuousAt (fun z : ℝ ↦ log (z * y)) x :=
    hproduct.log hxy_pos.ne'
  apply ContinuousAt.continuousWithinAt
  exact (hR.sub continuousAt_const).sub
    ((continuousAt_id.sub continuousAt_const).mul (hlogOneSubProduct.sub hlogProduct))

/-- The entropy curvature kernel is nonnegative on `1/2 ≤ y ≤ x ≤ 1`. -/
theorem curvatureKernel_nonneg {x y : ℝ} (hy : 1 / 2 ≤ y) (hyx : y ≤ x)
    (hx : x ≤ 1) : 0 ≤ curvatureKernel x y := by
  by_cases hy₁ : y = 1
  · subst y
    have hx₁ : x = 1 := by linarith
    subst x
    simp [curvatureKernel]
  have hy₀ : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have hy_lt : y < 1 := lt_of_le_of_ne (hyx.trans hx) hy₁
  have hconcave : ConcaveOn ℝ (Icc y 1) (fun z ↦ curvatureKernel z y) := by
    refine concaveOn_of_hasDerivWithinAt2_nonpos (f' := fun z ↦ curvatureKernelDeriv z y)
      (f'' := fun z ↦ curvatureKernelDeriv2 z y) (convex_Icc y 1)
      (curvatureKernel_continuousOn hy₀ hy_lt) ?_ ?_ ?_
    · intro z hz
      rw [interior_Icc] at hz
      have hz_pos : 0 < z := hy₀.trans hz.1
      have hz₀ : z ≠ 0 := hz_pos.ne'
      have hz₁ : z ≠ 1 := ne_of_lt hz.2
      have hzneg₁ : z ≠ -1 := by nlinarith
      have hzy₀ : z * y ≠ 0 := mul_ne_zero hz₀ hy₀.ne'
      have hzy₁ : z * y ≠ 1 := by
        apply ne_of_lt
        calc
          z * y < 1 * y := mul_lt_mul_of_pos_right hz.2 hy₀
          _ = y := one_mul y
          _ < 1 := hy_lt
      exact (hasDerivAt_curvatureKernel hz₀ hz₁ hzneg₁ hzy₀ hzy₁).hasDerivWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      have hz_pos : 0 < z := hy₀.trans hz.1
      have hz₀ : z ≠ 0 := hz_pos.ne'
      have hz₁ : z ≠ 1 := ne_of_lt hz.2
      have hzneg₁ : z ≠ -1 := by nlinarith
      have hzy₀ : z * y ≠ 0 := mul_ne_zero hz₀ hy₀.ne'
      have hzy₁ : z * y ≠ 1 := by
        apply ne_of_lt
        calc
          z * y < 1 * y := mul_lt_mul_of_pos_right hz.2 hy₀
          _ = y := one_mul y
          _ < 1 := hy_lt
      exact (hasDerivAt_curvatureKernelDeriv hz₀ hz₁ hzneg₁ hzy₀ hzy₁).hasDerivWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      have hz_pos : 0 < z := hy₀.trans hz.1
      have hz₀ : z ≠ 0 := hz_pos.ne'
      have hz₁ : z ≠ 1 := ne_of_lt hz.2
      have hzneg₁ : z ≠ -1 := by nlinarith
      have hzy₀ : z * y ≠ 0 := mul_ne_zero hz₀ hy₀.ne'
      have hzy₁ : z * y ≠ 1 := by
        apply ne_of_lt
        calc
          z * y < 1 * y := mul_lt_mul_of_pos_right hz.2 hy₀
          _ = y := one_mul y
          _ < 1 := hy_lt
      change curvatureKernelDeriv2 z y ≤ 0
      rw [curvatureKernelDeriv2_eq hz₀ hz₁ hzneg₁ hzy₀ hzy₁]
      exact div_nonpos_of_nonpos_of_nonneg
        (curvaturePolynomial_nonpos hy hz.1.le hz.2.le)
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (sq_nonneg z) (sub_nonneg.2 hz.2.le)) (sq_nonneg (z + 1)))
          (sq_nonneg (1 - z * y)))
  have hleft : curvatureKernel y y = 0 := by simp [curvatureKernel]
  have hright : 0 ≤ curvatureKernel 1 y := by
    have hy_ne : y ≠ 0 := hy₀.ne'
    have honeAdd : 1 + y ≠ 0 := by linarith
    have hquotient : 1 + 1 / y = (1 + y) / y := by
      field_simp [hy_ne]
      ring
    have hlogquotient : log (1 + 1 / y) = log (1 + y) - log y := by
      rw [hquotient, log_div honeAdd hy_ne]
    have haverage : y * (1 + 1 / y) + (1 - y) * 1 = 2 := by
      field_simp [hy_ne]
      ring
    have hjensen := strictConcaveOn_log_Ioi.concaveOn.2
      (show 1 + 1 / y ∈ Ioi (0 : ℝ) by
        rw [hquotient]
        exact div_pos (by linarith) hy₀)
      (show (1 : ℝ) ∈ Ioi (0 : ℝ) by norm_num)
      hy₀.le (sub_nonneg.2 hy_lt.le) (show y + (1 - y) = 1 by ring)
    dsimp only [smul_eq_mul] at hjensen
    rw [haverage] at hjensen
    simp only [log_one, mul_zero, add_zero] at hjensen
    have hidentity : curvatureKernel 1 y = log 2 - y * log (1 + 1 / y) := by
      simp only [curvatureKernel, curvatureR, entropyDerivative, negMulLog, log_one,
        mul_zero, one_mul, sub_self, neg_zero, zero_mul, zero_add]
      rw [hlogquotient]
      ring_nf
    rw [hidentity]
    linarith
  have hdenominator : 0 < 1 - y := sub_pos.2 hy_lt
  have hchord := hconcave.2 (show y ∈ Icc y 1 by exact ⟨le_rfl, hy_lt.le⟩)
    (show (1 : ℝ) ∈ Icc y 1 by exact ⟨hy_lt.le, le_rfl⟩)
    (div_nonneg (sub_nonneg.2 hx) hdenominator.le)
    (div_nonneg (sub_nonneg.2 hyx) hdenominator.le)
    (show (1 - x) / (1 - y) + (x - y) / (1 - y) = 1 by
      field_simp [hdenominator.ne']
      ring)
  dsimp only [smul_eq_mul] at hchord
  rw [hleft] at hchord
  have hpoint :
      (1 - x) / (1 - y) * y + (x - y) / (1 - y) * (1 : ℝ) = x := by
    calc
      (1 - x) / (1 - y) * y + (x - y) / (1 - y) * (1 : ℝ) =
          ((1 - x) * y) / (1 - y) + ((x - y) * 1) / (1 - y) := by
            rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
      _ = ((1 - x) * y + (x - y) * 1) / (1 - y) := (add_div _ _ _).symm
      _ = x := (div_eq_iff hdenominator.ne').2 (by ring)
  rw [hpoint] at hchord
  have hweight : 0 ≤ (x - y) / (1 - y) :=
    div_nonneg (sub_nonneg.2 hyx) hdenominator.le
  have hcombination : 0 ≤
      (1 - x) / (1 - y) * 0 + (x - y) / (1 - y) * curvatureKernel 1 y := by
    exact add_nonneg (mul_nonneg (div_nonneg (sub_nonneg.2 hx) hdenominator.le) le_rfl)
      (mul_nonneg hweight hright)
  exact hcombination.trans hchord

private theorem curvatureR_eq {u : ℝ} (hu₀ : 0 < u) (hu₁ : u < 1) :
    curvatureR u = u * entropyDerivative (u ^ 2) - entropyDerivative u := by
  have honeSub : 1 - u ≠ 0 := (sub_pos.2 hu₁).ne'
  have honeAdd : 1 + u ≠ 0 := by linarith
  have hfactor : 1 - u ^ 2 = (1 - u) * (1 + u) := by ring
  simp only [curvatureR, entropyDerivative, negMulLog]
  rw [hfactor, log_mul honeSub honeAdd, log_pow]
  ring

/-- The join-entropy advantage of a symmetric low orbit, in complement coordinates. -/
noncomputable def selfPairAdvantage (a d : ℝ) : ℝ :=
  let x := 1 - a + d
  let y := 1 - a - d
  (binEntropy (x ^ 2) + 2 * binEntropy (x * y) + binEntropy (y ^ 2)) / 4
    - (binEntropy x + binEntropy y) / 2

private theorem hasDerivAt_selfPairAdvantage {a s : ℝ}
    (hlower₀ : 0 < a - s) (hlower₁ : a - s < 1)
    (hupper₀ : 0 < a + s) (hupper₁ : a + s < 1) :
    HasDerivAt (selfPairAdvantage a) (curvatureKernel (1 - a + s) (1 - a - s) / 2) s := by
  let x := 1 - a + s
  let y := 1 - a - s
  have hx₀ : 0 < x := by dsimp [x]; linarith
  have hx₁ : x < 1 := by dsimp [x]; linarith
  have hy₀ : 0 < y := by dsimp [y]; linarith
  have hy₁ : y < 1 := by dsimp [y]; linarith
  have hxy₀ : 0 < x * y := mul_pos hx₀ hy₀
  have hxy₁ : x * y < 1 := (mul_lt_mul_of_pos_right hx₁ hy₀).trans (by simpa using hy₁)
  have hxx₀ : 0 < x ^ 2 := sq_pos_of_pos hx₀
  have hxx₁ : x ^ 2 < 1 := by nlinarith [mul_pos hx₀ (sub_pos.2 hx₁)]
  have hyy₀ : 0 < y ^ 2 := sq_pos_of_pos hy₀
  have hyy₁ : y ^ 2 < 1 := by nlinarith [mul_pos hy₀ (sub_pos.2 hy₁)]
  have hx : HasDerivAt (fun z : ℝ ↦ 1 - a + z) 1 s := by
    simpa only [id_eq] using (hasDerivAt_id s).const_add (1 - a)
  have hy : HasDerivAt (fun z : ℝ ↦ 1 - a - z) (-1) s := by
    simpa only [id_eq] using (hasDerivAt_id s).const_sub (1 - a)
  have hxx := hx.pow 2
  have hxy := hx.mul hy
  have hyy := hy.pow 2
  have hEntropyX := (hasDerivAt_binEntropy hxx₀.ne' hxx₁.ne).comp s hxx
  have hEntropyXY := (hasDerivAt_binEntropy hxy₀.ne' hxy₁.ne).comp s hxy
  have hEntropyY := (hasDerivAt_binEntropy hyy₀.ne' hyy₁.ne).comp s hyy
  have hMarginalX := (hasDerivAt_binEntropy hx₀.ne' hx₁.ne).comp s hx
  have hMarginalY := (hasDerivAt_binEntropy hy₀.ne' hy₁.ne).comp s hy
  have hindependent := ((hEntropyX.add (hEntropyXY.const_mul 2)).add hEntropyY).div_const 4
  have hmarginal := (hMarginalX.add hMarginalY).div_const 2
  apply (hindependent.sub hmarginal).congr_deriv
  simp only [curvatureKernel, x, y]
  rw [curvatureR_eq hx₀ hx₁, curvatureR_eq hy₀ hy₁]
  simp only [entropyDerivative]
  ring

private theorem selfPairAdvantage_mono {a d : ℝ}
    (hlower : 0 ≤ a - d) (hupper : a + d ≤ 1 / 2) (hd : 0 ≤ d) :
    selfPairAdvantage a 0 ≤ selfPairAdvantage a d := by
  have hcontinuous : ContinuousOn (selfPairAdvantage a) (Icc 0 d) := by
    apply Continuous.continuousOn
    unfold selfPairAdvantage
    fun_prop
  have hmonotone : MonotoneOn (selfPairAdvantage a) (Icc 0 d) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg
      (f' := fun s ↦ curvatureKernel (1 - a + s) (1 - a - s) / 2)
      (convex_Icc 0 d) hcontinuous ?_ ?_
    · intro s hs
      rw [interior_Icc] at hs
      change 0 < s ∧ s < d at hs
      have hlow : 0 < a - s := by linarith
      have hlow₁ : a - s < 1 := by linarith
      have hupp₀ : 0 < a + s := by linarith
      have hupp : a + s < 1 := by linarith
      exact (hasDerivAt_selfPairAdvantage hlow hlow₁ hupp₀ hupp).hasDerivWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      change 0 < s ∧ s < d at hs
      have hy : 1 / 2 ≤ 1 - a - s := by linarith
      have hyx : 1 - a - s ≤ 1 - a + s := by linarith
      have hx : 1 - a + s ≤ 1 := by linarith
      exact div_nonneg (curvatureKernel_nonneg hy hyx hx) (by norm_num)
  exact hmonotone (by exact ⟨le_rfl, hd⟩) (by exact ⟨hd, le_rfl⟩) hd

/-- The entropy loss when both copies of a symmetric low orbit are contracted to its mean. -/
noncomputable def selfPairDeficit (a d : ℝ) : ℝ :=
  binEntropy (join a a) -
    (binEntropy (join (a - d) (a - d))
      + 2 * binEntropy (join (a - d) (a + d))
      + binEntropy (join (a + d) (a + d))) / 4

/-- Contracting both copies of a low orbit costs at most its marginal entropy deficit. -/
theorem selfPairDeficit_le_orbitDeficit {a d : ℝ}
    (hlower : 0 ≤ a - d) (hupper : a + d ≤ 1 / 2) (hd : 0 ≤ d) :
    selfPairDeficit a d ≤ orbitDeficit binEntropy a d := by
  have hmono := selfPairAdvantage_mono hlower hupper hd
  have hzero : selfPairAdvantage a 0 = binEntropy (join a a) - binEntropy a := by
    unfold selfPairAdvantage
    simp only [add_zero, sub_zero]
    have hself : binEntropy ((1 - a) ^ 2) = binEntropy (join a a) := by
      rw [← binEntropy_one_sub]
      congr 1
      simp only [join]
      ring
    rw [hself, binEntropy_one_sub]
    have hproduct : binEntropy ((1 - a) * (1 - a)) = binEntropy (join a a) := by
      rw [← pow_two, hself]
    rw [hproduct]
    ring
  have hwide : binEntropy ((1 - a + d) ^ 2) =
      binEntropy (join (a - d) (a - d)) := by
    rw [← binEntropy_one_sub]
    congr 1
    simp only [join]
    ring
  have hcross : binEntropy ((1 - a + d) * (1 - a - d)) =
      binEntropy (join (a - d) (a + d)) := by
    rw [← binEntropy_one_sub]
    congr 1
    simp only [join]
    ring
  have hnarrow : binEntropy ((1 - a - d) ^ 2) =
      binEntropy (join (a + d) (a + d)) := by
    rw [← binEntropy_one_sub]
    congr 1
    simp only [join]
    ring
  have hmarginalWide : binEntropy (1 - a + d) = binEntropy (a - d) := by
    rw [show 1 - a + d = 1 - (a - d) by ring, binEntropy_one_sub]
  have hmarginalNarrow : binEntropy (1 - a - d) = binEntropy (a + d) := by
    rw [show 1 - a - d = 1 - (a + d) by ring, binEntropy_one_sub]
  rw [hzero] at hmono
  dsimp [selfPairAdvantage] at hmono
  rw [hwide, hcross, hnarrow, hmarginalWide, hmarginalNarrow] at hmono
  dsimp [selfPairDeficit, orbitDeficit]
  linarith

/-- The mean-sensitive self-pair estimate obtained by contracting the two copies in sequence. -/
theorem selfPairDeficit_le_affine {a d : ℝ}
    (hlower : 0 ≤ a - d) (hupper : a + d ≤ 1 / 2) (hd : 0 ≤ d) :
    selfPairDeficit a d ≤
      2 * (1 - 4 * a / 3) * orbitDeficit binEntropy a d := by
  have ha₀ : 0 ≤ a := by linarith
  have ha₁ : a ≤ 1 / 2 := by linarith
  have hcenter := orbitDeficit_joinEntropy_le_affine
    (a := a) (d := d) (q := a) hlower hupper hd ha₀ ha₁
  have hlowerPair := orbitDeficit_joinEntropy_le_affine
    (a := a) (d := d) (q := a - d) hlower hupper hd hlower (by linarith)
  have hupperPair := orbitDeficit_joinEntropy_le_affine
    (a := a) (d := d) (q := a + d) hlower hupper hd (by linarith) hupper
  have hdecomposition :
      selfPairDeficit a d =
        orbitDeficit (fun x ↦ binEntropy (join x a)) a d
          + (orbitDeficit (fun x ↦ binEntropy (join x (a - d))) a d
              + orbitDeficit (fun x ↦ binEntropy (join x (a + d))) a d) / 2 := by
    dsimp [selfPairDeficit, orbitDeficit]
    rw [join_comm (a - d) a, join_comm (a + d) a, join_comm (a + d) (a - d)]
    ring
  rw [hdecomposition]
  linarith

end Frankl
