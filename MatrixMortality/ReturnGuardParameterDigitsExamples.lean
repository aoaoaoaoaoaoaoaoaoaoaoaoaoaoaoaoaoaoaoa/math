import MatrixMortality.ReturnGuardParameterDigits

/-!
# Weighted parameter-digit certificates

One exact guard stage displays the complete scale cancellation.  At base three, depth two,
wait one, drift one, unit tail one, and reset gradient `(0,1)`, the raw scale changes from
`1` to `-2/9`.  The normalized jets are `(1,1)` and `(-7/2,-97/2)`, while the transverse
defect is `10`.  The weighted Cramer digit for values `(2,3)` and old target `1` is exactly
`(-7/9,-1)`.

The final theorem checks the denominator-digit model on `-1/2`: every ternary digit is one,
the familiar identity `-1/2 = 1+3+3²+⋯` in `ℚ₃`.
-/

namespace MatrixMortality.ReturnGuard.Examples

open MatrixMortality.RationalPadicDigits

/-- Reset gradient used by the weighted Cramer certificate. -/
def weightedDigitGradient : Fin 2 → ℚ :=
  ![0, 1]

/-- Initial normalized jet of the certificate. -/
theorem weightedDigit_oldJet :
    renormalizedParameterGradient 1 weightedDigitGradient = ![1, 1] := by
  norm_num [renormalizedParameterGradient, parameterGradientMass,
    weightedDigitGradient]

/-- The certificate's singular scale ratio is `-2/9`. -/
theorem weightedDigit_scale :
    sensitivityScaleStep 3 2 1 1 1 1 = -(2 / 9 : ℚ) := by
  norm_num [sensitivityScaleStep, sensitivityMultiplier]

/-- Normalized successor jet of the certificate. -/
theorem weightedDigit_newJet :
    renormalizedParameterGradient
        (sensitivityScaleStep 3 2 1 1 1 1)
        (parameterGradientStep 3 2 1 1 1 weightedDigitGradient) =
      ![-7 / 2, -97 / 2] := by
  norm_num [renormalizedParameterGradient, parameterGradientMass,
    sensitivityScaleStep, sensitivityMultiplier, parameterGradientStep,
    legalPayload, weightedDigitGradient]

/-- The certificate's renormalized transverse defect is ten. -/
theorem weightedDigit_defect :
    renormalizedTransverseDefect
        (legalPayload 3 2 1 1) 1 weightedDigitGradient = 10 := by
  norm_num [renormalizedTransverseDefect, legalPayload,
    parameterGradientMass, weightedDigitGradient]

/-- Exact nonintegral weighted escape digit after the raw sensitivity scale cancels. -/
theorem weightedDigit_value :
    weightedPlaneSolveDigit (2 : ℚ) ![1, 1] 3 ![-7 / 2, -97 / 2]
        1 (-(2 / 9 : ℚ)) 10 =
      (![-7 / 9, -1] : Fin 2 → ℚ) := by
  norm_num [weightedPlaneSolveDigit, weightedCenterNumerator,
    weightedResetNumerator]

/-- The ternary denominator-digit stream of `-1/2` is the constant stream one. -/
theorem minusHalf_ternaryDigit (index : Nat) :
    denominatorDigit 3 2 (by norm_num) (1 : ZMod 2) index = 1 := by
  let coprime : Nat.Coprime 3 2 := by norm_num
  have remainder (n : Nat) :
      inverseRemainder 3 2 coprime (1 : ZMod 2) n = 1 := by
    have unit_eq : ZMod.unitOfCoprime 3 coprime = (1 : (ZMod 2)ˣ) := by
      apply Units.ext
      change (3 : ZMod 2) = 1
      exact (ZMod.natCast_eq_natCast_iff' 3 1 2).mpr (by norm_num)
    simp [inverseRemainder, unit_eq]
  simpa only [denominatorDigit, remainder] using
    (show (((3 : Int) * 1 - 1) / 2) = 1 by norm_num)

end MatrixMortality.ReturnGuard.Examples
