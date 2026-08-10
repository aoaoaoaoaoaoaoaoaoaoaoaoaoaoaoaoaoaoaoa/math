import Frankl.CertificateExpr

namespace Frankl

open Filter Real Set

/-- Executable rounded evaluation of an entropy expression and its two coordinate derivatives. -/
def evaluateDual (terms fuel bits : ℕ) (rectangle : RatRectangle) :
    EntropyExpr → Option DualBall
  | .constant value => some (DualBall.constant value)
  | .horizontal => some (DualBall.horizontal rectangle)
  | .vertical => some (DualBall.vertical rectangle)
  | .add left right => do
      let leftDual ← evaluateDual terms fuel bits rectangle left
      let rightDual ← evaluateDual terms fuel bits rectangle right
      some (DualBall.add bits leftDual rightDual)
  | .neg body => do
      let bodyDual ← evaluateDual terms fuel bits rectangle body
      some bodyDual.neg
  | .mul left right => do
      let leftDual ← evaluateDual terms fuel bits rectangle left
      let rightDual ← evaluateDual terms fuel bits rectangle right
      some (DualBall.mul bits leftDual rightDual)
  | .inv body => do
      let bodyDual ← evaluateDual terms fuel bits rectangle body
      bodyDual.inv? bits
  | .entropy body => do
      let bodyDual ← evaluateDual terms fuel bits rectangle body
      bodyDual.entropy? terms fuel bits
  | .cappedEntropy body => do
      let bodyDual ← evaluateDual terms fuel bits rectangle body
      bodyDual.cappedEntropy? terms fuel bits
  | .selfUnion body => do
      let bodyDual ← evaluateDual terms fuel bits rectangle body
      some (bodyDual.selfUnion bits)

/-- Executable smoothness gate for a first-order certificate leaf. -/
def certifySmooth (terms fuel bits : ℕ) (rectangle : RatRectangle) :
    EntropyExpr → Option Unit
  | .constant _ | .horizontal | .vertical => some ()
  | .add left right | .mul left right => do
      let _ ← certifySmooth terms fuel bits rectangle left
      certifySmooth terms fuel bits rectangle right
  | .neg body | .inv body => certifySmooth terms fuel bits rectangle body
  | .entropy body => do
      let _ ← certifySmooth terms fuel bits rectangle body
      let bodyDual ← evaluateDual terms fuel bits rectangle body
      if 0 < bodyDual.value.lower ∧ bodyDual.value.upper < 1 then some () else none
  | .cappedEntropy body => do
      let _ ← certifySmooth terms fuel bits rectangle body
      let bodyDual ← evaluateDual terms fuel bits rectangle body
      if 0 < bodyDual.value.lower then some () else none
  | .selfUnion body => certifySmooth terms fuel bits rectangle body

/-- Soundness of the executable dual evaluator at every point in its rectangle. -/
theorem evaluateDual_encloses {terms fuel bits : ℕ} {rectangle : RatRectangle}
    {expression : EntropyExpr} {dual : DualBall} {x y : ℝ}
    (hx : rectangle.horizontal.Contains x) (hy : rectangle.vertical.Contains y)
    (hdomain : expression.DomainAt x y)
    (hdual : evaluateDual terms fuel bits rectangle expression = some dual) :
    dual.Encloses (expression.eval x y)
      (expression.slope .horizontal x y) (expression.slope .vertical x y) := by
  induction expression generalizing dual with
  | constant value =>
    simp only [evaluateDual, Option.some.injEq] at hdual
    subst dual
    simpa [EntropyExpr.eval, EntropyExpr.slope] using DualBall.constant_encloses value
  | horizontal =>
    simp only [evaluateDual, Option.some.injEq] at hdual
    subst dual
    simpa [EntropyExpr.eval, EntropyExpr.slope] using DualBall.horizontal_encloses hx
  | vertical =>
    simp only [evaluateDual, Option.some.injEq] at hdual
    subst dual
    simpa [EntropyExpr.eval, EntropyExpr.slope] using DualBall.vertical_encloses hy
  | add left right hleft hright =>
    rcases hdomain with ⟨hleftDomain, hrightDomain⟩
    cases hleftDual : evaluateDual terms fuel bits rectangle left with
    | none => simp [evaluateDual, hleftDual] at hdual
    | some leftDual =>
      cases hrightDual : evaluateDual terms fuel bits rectangle right with
      | none => simp [evaluateDual, hleftDual, hrightDual] at hdual
      | some rightDual =>
        simp [evaluateDual, hleftDual, hrightDual] at hdual
        subst dual
        have hleftEncloses := hleft hleftDomain hleftDual
        have hrightEncloses := hright hrightDomain hrightDual
        simpa [EntropyExpr.eval, EntropyExpr.slope] using
          DualBall.add_encloses (bits := bits) hleftEncloses hrightEncloses
  | neg body hbody =>
    cases hbodyDual : evaluateDual terms fuel bits rectangle body with
    | none => simp [evaluateDual, hbodyDual] at hdual
    | some bodyDual =>
      simp [evaluateDual, hbodyDual] at hdual
      subst dual
      have hbodyEncloses := hbody hdomain hbodyDual
      simpa [EntropyExpr.eval, EntropyExpr.slope] using
        DualBall.neg_encloses hbodyEncloses
  | mul left right hleft hright =>
    rcases hdomain with ⟨hleftDomain, hrightDomain⟩
    cases hleftDual : evaluateDual terms fuel bits rectangle left with
    | none => simp [evaluateDual, hleftDual] at hdual
    | some leftDual =>
      cases hrightDual : evaluateDual terms fuel bits rectangle right with
      | none => simp [evaluateDual, hleftDual, hrightDual] at hdual
      | some rightDual =>
        simp [evaluateDual, hleftDual, hrightDual] at hdual
        subst dual
        have hleftEncloses := hleft hleftDomain hleftDual
        have hrightEncloses := hright hrightDomain hrightDual
        simpa [EntropyExpr.eval, EntropyExpr.slope] using
          DualBall.mul_encloses (bits := bits) hleftEncloses hrightEncloses
  | inv body hbody =>
    rcases hdomain with ⟨hbodyDomain, _hpositive⟩
    cases hbodyDual : evaluateDual terms fuel bits rectangle body with
    | none => simp [evaluateDual, hbodyDual] at hdual
    | some bodyDual =>
      simp [evaluateDual, hbodyDual] at hdual
      have hbodyEncloses := hbody hbodyDomain hbodyDual
      have hinverse := DualBall.inv_encloses hbodyEncloses hdual
      simpa [EntropyExpr.eval, EntropyExpr.slope] using hinverse
  | entropy body hbody =>
    rcases hdomain with ⟨hbodyDomain, hvalue⟩
    cases hbodyDual : evaluateDual terms fuel bits rectangle body with
    | none => simp [evaluateDual, hbodyDual] at hdual
    | some bodyDual =>
      simp [evaluateDual, hbodyDual] at hdual
      have hbodyEncloses := hbody hbodyDomain hbodyDual
      have hentropy := DualBall.entropy_encloses hbodyEncloses hvalue hdual
      simpa [EntropyExpr.eval, EntropyExpr.slope] using hentropy
  | cappedEntropy body hbody =>
    rcases hdomain with ⟨hbodyDomain, hvalue⟩
    cases hbodyDual : evaluateDual terms fuel bits rectangle body with
    | none => simp [evaluateDual, hbodyDual] at hdual
    | some bodyDual =>
      simp [evaluateDual, hbodyDual] at hdual
      have hbodyEncloses := hbody hbodyDomain hbodyDual
      have hcapped := DualBall.cappedEntropy_encloses hbodyEncloses hvalue hdual
      simpa [EntropyExpr.eval, EntropyExpr.slope] using hcapped
  | selfUnion body hbody =>
    rcases hdomain with ⟨hbodyDomain, hvalue⟩
    cases hbodyDual : evaluateDual terms fuel bits rectangle body with
    | none => simp [evaluateDual, hbodyDual] at hdual
    | some bodyDual =>
      simp [evaluateDual, hbodyDual] at hdual
      subst dual
      have hbodyEncloses := hbody hbodyDomain hbodyDual
      simpa [EntropyExpr.eval, EntropyExpr.slope] using
        DualBall.selfUnion_encloses hbodyEncloses hvalue

/-- The executable smoothness gate proves the analytic smoothness predicate throughout its
rectangle. -/
theorem certifySmooth_sound {terms fuel bits : ℕ} {rectangle : RatRectangle}
    {expression : EntropyExpr} {x y : ℝ}
    (hx : rectangle.horizontal.Contains x) (hy : rectangle.vertical.Contains y)
    (hdomain : expression.DomainAt x y)
    (hsmooth : certifySmooth terms fuel bits rectangle expression = some ()) :
    expression.SmoothAt x y := by
  induction expression with
  | constant value => trivial
  | horizontal => trivial
  | vertical => trivial
  | add left right hleft hright =>
    rcases hdomain with ⟨hleftDomain, hrightDomain⟩
    unfold certifySmooth at hsmooth
    cases hleftResult : certifySmooth terms fuel bits rectangle left with
    | none => simp [hleftResult] at hsmooth
    | some _witness =>
      cases _witness
      simp [hleftResult] at hsmooth
      exact ⟨hleft hleftDomain hleftResult, hright hrightDomain hsmooth⟩
  | neg body hbody =>
    exact hbody hdomain hsmooth
  | mul left right hleft hright =>
    rcases hdomain with ⟨hleftDomain, hrightDomain⟩
    unfold certifySmooth at hsmooth
    cases hleftResult : certifySmooth terms fuel bits rectangle left with
    | none => simp [hleftResult] at hsmooth
    | some _witness =>
      cases _witness
      simp [hleftResult] at hsmooth
      exact ⟨hleft hleftDomain hleftResult, hright hrightDomain hsmooth⟩
  | inv body hbody =>
    exact hbody hdomain.1 hsmooth
  | entropy body hbody =>
    rcases hdomain with ⟨hbodyDomain, _hvalue⟩
    unfold certifySmooth at hsmooth
    cases hbodySmooth : certifySmooth terms fuel bits rectangle body with
    | none => simp [hbodySmooth] at hsmooth
    | some _witness =>
      cases _witness
      cases hbodyDual : evaluateDual terms fuel bits rectangle body with
      | none => simp [hbodySmooth, hbodyDual] at hsmooth
      | some bodyDual =>
        simp [hbodySmooth, hbodyDual] at hsmooth
        have hencloses := evaluateDual_encloses hx hy hbodyDomain hbodyDual
        have hbounds := RatBall.contains_iff_bounds.mp hencloses.1
        have hlowerReal : (0 : ℝ) < bodyDual.value.lower := by
          exact_mod_cast hsmooth.1
        have hupperReal : (bodyDual.value.upper : ℝ) < 1 := by
          exact_mod_cast hsmooth.2
        exact ⟨hbody hbodyDomain hbodySmooth,
          ne_of_gt (hlowerReal.trans_le hbounds.1),
          ne_of_lt (hbounds.2.trans_lt hupperReal)⟩
  | cappedEntropy body hbody =>
    rcases hdomain with ⟨hbodyDomain, _hvalue⟩
    unfold certifySmooth at hsmooth
    cases hbodySmooth : certifySmooth terms fuel bits rectangle body with
    | none => simp [hbodySmooth] at hsmooth
    | some _witness =>
      cases _witness
      cases hbodyDual : evaluateDual terms fuel bits rectangle body with
      | none => simp [hbodySmooth, hbodyDual] at hsmooth
      | some bodyDual =>
        simp [hbodySmooth, hbodyDual] at hsmooth
        have hencloses := evaluateDual_encloses hx hy hbodyDomain hbodyDual
        have hbounds := RatBall.contains_iff_bounds.mp hencloses.1
        have hlowerReal : (0 : ℝ) < bodyDual.value.lower := by
          exact_mod_cast hsmooth
        exact ⟨hbody hbodyDomain hbodySmooth,
          ne_of_gt (hlowerReal.trans_le hbounds.1)⟩
  | selfUnion body hbody =>
    exact hbody hdomain.1 hsmooth

/-- First-order mean-value lower bound on a rectangle. -/
theorem eval_ge_center_sub_gradient_error {terms fuel bits : ℕ}
    {rectangle : RatRectangle} {expression : EntropyExpr}
    {dual centerDual : DualBall} {gradient : RatBall × RatBall} {x y : ℝ}
    (hhorizontalRadius : 0 ≤ rectangle.horizontal.radius)
    (hverticalRadius : 0 ≤ rectangle.vertical.radius)
    (hx : rectangle.horizontal.Contains x) (hy : rectangle.vertical.Contains y)
    (hdomain : ∀ u v, rectangle.horizontal.Contains u → rectangle.vertical.Contains v →
      expression.DomainAt u v)
    (hsmooth : certifySmooth terms fuel bits rectangle expression = some ())
    (hdual : evaluateDual terms fuel bits rectangle expression = some dual)
    (hgradient : dual.gradient = some gradient)
    (hcenterDual : evaluateDual terms fuel bits rectangle.center expression = some centerDual) :
    (centerDual.value.lower : ℝ)
        - (gradient.1.absUpper : ℝ) * rectangle.horizontal.radius
        - (gradient.2.absUpper : ℝ) * rectangle.vertical.radius ≤
      expression.eval x y := by
  have hcenterHorizontal : rectangle.horizontal.Contains rectangle.horizontal.center := by
    simp only [RatBall.Contains]
    simpa using hhorizontalRadius
  have hcenterVertical : rectangle.vertical.Contains rectangle.vertical.center := by
    simp only [RatBall.Contains]
    simpa using hverticalRadius
  have hcenterDomain := hdomain rectangle.horizontal.center rectangle.vertical.center
    hcenterHorizontal hcenterVertical
  have hcenterPointHorizontal : rectangle.center.horizontal.Contains
      (rectangle.horizontal.center : ℝ) := by
    simpa [RatRectangle.center] using RatBall.point_contains rectangle.horizontal.center
  have hcenterPointVertical : rectangle.center.vertical.Contains
      (rectangle.vertical.center : ℝ) := by
    simpa [RatRectangle.center] using RatBall.point_contains rectangle.vertical.center
  have hcenterEncloses := evaluateDual_encloses hcenterPointHorizontal hcenterPointVertical
    hcenterDomain hcenterDual
  have hcenterLower := (RatBall.contains_iff_bounds.mp hcenterEncloses.1).1
  have hhorizontalSet : x ∈ Icc (rectangle.horizontal.lower : ℝ)
      rectangle.horizontal.upper := RatBall.contains_iff_bounds.mp hx
  have hcenterHorizontalSet : (rectangle.horizontal.center : ℝ) ∈
      Icc (rectangle.horizontal.lower : ℝ) rectangle.horizontal.upper :=
    RatBall.contains_iff_bounds.mp hcenterHorizontal
  have hverticalSet : y ∈ Icc (rectangle.vertical.lower : ℝ)
      rectangle.vertical.upper := RatBall.contains_iff_bounds.mp hy
  have hcenterVerticalSet : (rectangle.vertical.center : ℝ) ∈
      Icc (rectangle.vertical.lower : ℝ) rectangle.vertical.upper :=
    RatBall.contains_iff_bounds.mp hcenterVertical
  have hhorizontalDifference :
      |expression.eval x y - expression.eval rectangle.horizontal.center y| ≤
        (gradient.1.absUpper : ℝ) * |x - rectangle.horizontal.center| := by
    have hdifferentiable : ∀ u ∈ Icc (rectangle.horizontal.lower : ℝ)
        rectangle.horizontal.upper,
        DifferentiableAt ℝ (fun z => expression.eval z y) u := by
      intro u hu
      have huBall : rectangle.horizontal.Contains u :=
        RatBall.contains_iff_bounds.mpr hu
      have huDomain := hdomain u y huBall hy
      have huSmooth := certifySmooth_sound huBall hy huDomain hsmooth
      have hderiv := EntropyExpr.hasDerivAt_along
        (coordinate := EntropyExpr.Coordinate.horizontal)
        huDomain huSmooth
      simpa only [EntropyExpr.along, EntropyExpr.lineBase] using hderiv.differentiableAt
    have hbound : ∀ u ∈ Icc (rectangle.horizontal.lower : ℝ)
        rectangle.horizontal.upper,
        ‖deriv (fun z => expression.eval z y) u‖ ≤ (gradient.1.absUpper : ℝ) := by
      intro u hu
      have huBall : rectangle.horizontal.Contains u :=
        RatBall.contains_iff_bounds.mpr hu
      have huDomain := hdomain u y huBall hy
      have huSmooth := certifySmooth_sound huBall hy huDomain hsmooth
      have hderiv := EntropyExpr.hasDerivAt_along
        (coordinate := EntropyExpr.Coordinate.horizontal)
        huDomain huSmooth
      have hslope : deriv (fun z => expression.eval z y) u =
          expression.slope .horizontal u y := by
        simpa only [EntropyExpr.along, EntropyExpr.lineBase] using hderiv.deriv
      have hencloses := evaluateDual_encloses huBall hy huDomain hdual
      have hgradientContains := (hencloses.2 gradient hgradient).1
      rw [hslope, Real.norm_eq_abs]
      exact RatBall.abs_le_absUpper hgradientContains
    have hmean := (convex_Icc (rectangle.horizontal.lower : ℝ)
      rectangle.horizontal.upper).norm_image_sub_le_of_norm_deriv_le
        hdifferentiable hbound hcenterHorizontalSet hhorizontalSet
    simpa only [Real.norm_eq_abs] using hmean
  have hverticalDifference :
      |expression.eval rectangle.horizontal.center y -
          expression.eval rectangle.horizontal.center rectangle.vertical.center| ≤
        (gradient.2.absUpper : ℝ) * |y - rectangle.vertical.center| := by
    have hdifferentiable : ∀ v ∈ Icc (rectangle.vertical.lower : ℝ)
        rectangle.vertical.upper,
        DifferentiableAt ℝ (fun z => expression.eval rectangle.horizontal.center z) v := by
      intro v hv
      have hvBall : rectangle.vertical.Contains v := RatBall.contains_iff_bounds.mpr hv
      have hvDomain := hdomain rectangle.horizontal.center v hcenterHorizontal hvBall
      have hvSmooth := certifySmooth_sound hcenterHorizontal hvBall hvDomain hsmooth
      have hderiv := EntropyExpr.hasDerivAt_along
        (coordinate := EntropyExpr.Coordinate.vertical)
        hvDomain hvSmooth
      simpa only [EntropyExpr.along, EntropyExpr.lineBase] using hderiv.differentiableAt
    have hbound : ∀ v ∈ Icc (rectangle.vertical.lower : ℝ)
        rectangle.vertical.upper,
        ‖deriv (fun z => expression.eval rectangle.horizontal.center z) v‖ ≤
          (gradient.2.absUpper : ℝ) := by
      intro v hv
      have hvBall : rectangle.vertical.Contains v := RatBall.contains_iff_bounds.mpr hv
      have hvDomain := hdomain rectangle.horizontal.center v hcenterHorizontal hvBall
      have hvSmooth := certifySmooth_sound hcenterHorizontal hvBall hvDomain hsmooth
      have hderiv := EntropyExpr.hasDerivAt_along
        (coordinate := EntropyExpr.Coordinate.vertical)
        hvDomain hvSmooth
      have hslope : deriv (fun z => expression.eval rectangle.horizontal.center z) v =
          expression.slope .vertical rectangle.horizontal.center v := by
        simpa only [EntropyExpr.along, EntropyExpr.lineBase] using hderiv.deriv
      have hencloses := evaluateDual_encloses hcenterHorizontal hvBall hvDomain hdual
      have hgradientContains := (hencloses.2 gradient hgradient).2
      rw [hslope, Real.norm_eq_abs]
      exact RatBall.abs_le_absUpper hgradientContains
    have hmean := (convex_Icc (rectangle.vertical.lower : ℝ)
      rectangle.vertical.upper).norm_image_sub_le_of_norm_deriv_le
        hdifferentiable hbound hcenterVerticalSet hverticalSet
    simpa only [Real.norm_eq_abs] using hmean
  have hhorizontalDistance : |x - (rectangle.horizontal.center : ℝ)| ≤
      rectangle.horizontal.radius := by
    simpa only [RatBall.Contains] using hx
  have hverticalDistance : |y - (rectangle.vertical.center : ℝ)| ≤
      rectangle.vertical.radius := by
    simpa only [RatBall.Contains] using hy
  have hhorizontalAbsUpper : (0 : ℝ) ≤ gradient.1.absUpper := by
    have hnonnegative : (0 : ℚ) ≤ gradient.1.absUpper :=
      (abs_nonneg gradient.1.lower).trans (le_max_left _ _)
    exact_mod_cast hnonnegative
  have hverticalAbsUpper : (0 : ℝ) ≤ gradient.2.absUpper := by
    have hnonnegative : (0 : ℚ) ≤ gradient.2.absUpper :=
      (abs_nonneg gradient.2.lower).trans (le_max_left _ _)
    exact_mod_cast hnonnegative
  have hhorizontalError := hhorizontalDifference.trans
    (mul_le_mul_of_nonneg_left hhorizontalDistance hhorizontalAbsUpper)
  have hverticalError := hverticalDifference.trans
    (mul_le_mul_of_nonneg_left hverticalDistance hverticalAbsUpper)
  have hhorizontalLower := neg_le_of_abs_le hhorizontalError
  have hverticalLower := neg_le_of_abs_le hverticalError
  linarith

end Frankl
