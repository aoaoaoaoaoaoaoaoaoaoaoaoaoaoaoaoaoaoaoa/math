import Frankl.CertificateAdaptive
import Frankl.CertificateCorners

namespace Frankl

open Real Set

/-- A successful reflected subdivision proves the endpoint objective throughout its rectangle. -/
theorem endpointCertificateObjective_nonneg_of_subdivision
    {rectangle : RatRectangle} {tree : Subdivision} {a q : ℝ}
    (hhorizontalRadius : 0 ≤ rectangle.horizontal.radius)
    (hverticalRadius : 0 ≤ rectangle.vertical.radius)
    (hhorizontalLower : 0 ≤ rectangle.horizontal.lower)
    (hhorizontalUpper : rectangle.horizontal.upper ≤ abundanceTarget)
    (hverticalLower : 0 ≤ rectangle.vertical.lower)
    (hverticalUpper : rectangle.vertical.upper ≤ 1)
    (ha : rectangle.horizontal.Contains a) (hq : rectangle.vertical.Contains q)
    (hcertified : certifySubdivision 12 64 32 rectangle
      CertificateObjective.endpointExpression tree = some ()) :
    0 ≤ endpointCertificateObjective a q := by
  have hdomain : ∀ u v, rectangle.horizontal.Contains u →
      rectangle.vertical.Contains v →
      CertificateObjective.endpointExpression.DomainAt u v := by
    intro u v hu hv
    have huBounds := RatBall.contains_iff_bounds.mp hu
    have hvBounds := RatBall.contains_iff_bounds.mp hv
    have huLower : (0 : ℝ) ≤ u := by
      have hlower : (0 : ℝ) ≤ rectangle.horizontal.lower := by
        exact_mod_cast hhorizontalLower
      exact hlower.trans huBounds.1
    have huUpper : u ≤ abundanceTarget := by
      have hupper : (rectangle.horizontal.upper : ℝ) ≤ abundanceTarget := by
        exact_mod_cast hhorizontalUpper
      exact huBounds.2.trans hupper
    have hvLower : (0 : ℝ) ≤ v := by
      have hlower : (0 : ℝ) ≤ rectangle.vertical.lower := by
        exact_mod_cast hverticalLower
      exact hlower.trans hvBounds.1
    have hvUpper : v ≤ 1 := by
      have hupper : (rectangle.vertical.upper : ℝ) ≤ 1 := by
        exact_mod_cast hverticalUpper
      exact hvBounds.2.trans hupper
    exact CertificateObjective.endpointExpression_domain huLower huUpper hvLower hvUpper
  have hnonneg := certifySubdivision_sound hhorizontalRadius hverticalRadius ha hq hdomain
    (fun u v hu₀ huCorner hv₀ hvCorner =>
      CertificateCorner.endpointExpression_zero_corner hu₀ huCorner hv₀ hvCorner)
    (fun u v hu₀ huCorner hvCorner hv₁ =>
      CertificateCorner.endpointExpression_one_corner hu₀ huCorner hvCorner hv₁)
    hcertified
  have haBounds := RatBall.contains_iff_bounds.mp ha
  have haUpper : a ≤ abundanceTarget := by
    have hupper : (rectangle.horizontal.upper : ℝ) ≤ abundanceTarget := by
      exact_mod_cast hhorizontalUpper
    exact haBounds.2.trans hupper
  rw [CertificateObjective.endpointExpression_eval
    (haUpper.trans abundanceTarget_lt_half.le)] at hnonneg
  exact hnonneg

end Frankl
