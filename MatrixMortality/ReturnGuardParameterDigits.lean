import MatrixMortality.RationalPadicDigits
import MatrixMortality.ReturnGuardParameterJet

/-!
# Weighted parameter digits

The center/reset escape digit is obtained by Cramer's rule from two successive parameter
gradients.  In raw coordinates its denominator is their exterior product, whose scale grows
singularly.  The integrating-factor chart removes that spurious growth exactly.

Write a gradient as

```text
g = q · (j₀-j₁,j₁)
```

in mass/reset jet coordinates.  For a second gradient with scale `q'`, put

```text
λ = q'/q,
κ = q' · (j ∧ j').
```

Then the raw Cramer digit depends only on `(j,j',λ,κ)`: the incoming scale `q` cancels.
For a legal guard step, `λ=-C` and `κ` is precisely the renormalized transverse defect from
`ReturnGuardParameterJet`.

This identifies the actual arithmetic denominator of parameter lifting.  It is not the
exploding sensitivity scale; it is the single transverse coordinate `κ`.
-/

namespace MatrixMortality.ReturnGuard

open MatrixMortality.PadicValuation
open scoped Matrix

noncomputable section

/-- Recover a center/reset gradient from its integrating factor and mass/reset jet. -/
def parameterGradientOfJet
    {K : Type*} [Ring K] (scale : K) (jet : Fin 2 → K) : Fin 2 → K :=
  ![scale * (jet 0 - jet 1), scale * jet 1]

/-- Numerator of the center coordinate of the weighted Cramer digit. -/
def weightedCenterNumerator
    {K : Type*} [Ring K]
    (oldValue : K) (oldJet : Fin 2 → K)
    (newValue : K) (newJet : Fin 2 → K)
    (oldTarget scaleRatio : K) : K :=
  (oldTarget - oldValue) * scaleRatio * newJet 1 +
    oldJet 1 * newValue

/-- Numerator of the reset coordinate of the weighted Cramer digit. -/
def weightedResetNumerator
    {K : Type*} [Ring K]
    (oldValue : K) (oldJet : Fin 2 → K)
    (newValue : K) (newJet : Fin 2 → K)
    (oldTarget scaleRatio : K) : K :=
  -(oldJet 0 - oldJet 1) * newValue -
    (oldTarget - oldValue) * scaleRatio * (newJet 0 - newJet 1)

/-- Cramer's rule after removal of the incoming sensitivity scale. -/
def weightedPlaneSolveDigit
    {K : Type*} [Field K]
    (oldValue : K) (oldJet : Fin 2 → K)
    (newValue : K) (newJet : Fin 2 → K)
    (oldTarget scaleRatio transverseDefect : K) : Fin 2 → K :=
  ![
    weightedCenterNumerator oldValue oldJet newValue newJet
        oldTarget scaleRatio /
      transverseDefect,
    weightedResetNumerator oldValue oldJet newValue newJet
        oldTarget scaleRatio /
      transverseDefect
  ]

/-- Weighted Cramer digit attached to one legal guard-sensitivity step. -/
def weightedParameterStepDigit
    (prime depth wait : Nat) (driftValue tail : ℚ)
    (oldValue newValue oldTarget scale : ℚ)
    (gradient : Fin 2 → ℚ) : Fin 2 → ℚ :=
  weightedPlaneSolveDigit oldValue
    (renormalizedParameterGradient scale gradient)
    newValue
    (renormalizedParameterGradient
      (sensitivityScaleStep prime depth wait driftValue tail scale)
      (parameterGradientStep prime depth wait driftValue tail gradient))
    oldTarget
    (-sensitivityMultiplier prime depth wait driftValue tail)
    (renormalizedTransverseDefect
      (legalPayload prime depth wait tail) scale gradient)

/-- The mass/reset chart is an orientation-preserving change of basis; scales factor from its
exterior product. -/
theorem planeCross_parameterGradientOfJet
    {K : Type*} [CommRing K]
    (oldScale newScale : K) (oldJet newJet : Fin 2 → K) :
    planeCross
        (parameterGradientOfJet oldScale oldJet)
        (parameterGradientOfJet newScale newJet) =
      oldScale * newScale * planeCross oldJet newJet := by
  simp [planeCross, parameterGradientOfJet]
  ring

/-- A nonzero integrating factor reconstructs the original parameter gradient from its
renormalized jet. -/
theorem parameterGradientOfJet_renormalized
    (scale : ℚ) (gradient : Fin 2 → ℚ) (scale_ne : scale ≠ 0) :
    parameterGradientOfJet scale
        (renormalizedParameterGradient scale gradient) =
      gradient := by
  ext i
  fin_cases i <;>
    simp [parameterGradientOfJet, renormalizedParameterGradient,
      parameterGradientMass]
  all_goals field_simp [scale_ne]

/-- General scale-cancellation theorem for the two-plane Cramer solver. -/
theorem planeSolveDigit_parameterGradientOfJet
    {K : Type*} [Field K]
    (oldValue : K) (oldJet : Fin 2 → K)
    (newValue : K) (newJet : Fin 2 → K)
    (oldTarget oldScale newScale : K)
    (oldScale_ne : oldScale ≠ 0)
    (newScale_ne : newScale ≠ 0)
    (jetCross_ne : planeCross oldJet newJet ≠ 0) :
    planeSolveDigit oldValue
        (parameterGradientOfJet oldScale oldJet)
        newValue
        (parameterGradientOfJet newScale newJet)
        oldTarget =
      weightedPlaneSolveDigit oldValue oldJet newValue newJet oldTarget
        (newScale / oldScale)
        (newScale * planeCross oldJet newJet) := by
  unfold planeSolveDigit weightedPlaneSolveDigit
  rw [planeCross_parameterGradientOfJet]
  ext i
  fin_cases i <;>
    simp [weightedCenterNumerator, weightedResetNumerator,
      parameterGradientOfJet]
  all_goals field_simp [oldScale_ne, newScale_ne, jetCross_ne]
  all_goals ring

/-- The guard-specific Cramer digit has scale ratio `-C` and denominator equal to the
renormalized transverse defect. -/
theorem planeSolveDigit_parameterGradientStep
    (prime depth wait : Nat) (driftValue tail scale : ℚ)
    (oldValue newValue oldTarget : ℚ)
    (gradient : Fin 2 → ℚ)
    (scale_ne : scale ≠ 0)
    (multiplier_ne :
      sensitivityMultiplier prime depth wait driftValue tail ≠ 0)
    (defect_ne :
      renormalizedTransverseDefect
          (legalPayload prime depth wait tail) scale gradient ≠
        0) :
    planeSolveDigit oldValue gradient newValue
        (parameterGradientStep prime depth wait driftValue tail gradient)
        oldTarget =
      weightedParameterStepDigit prime depth wait driftValue tail
        oldValue newValue oldTarget scale gradient := by
  have nextScale_ne :
      sensitivityScaleStep prime depth wait driftValue tail scale ≠ 0 :=
    sensitivityScaleStep_ne_zero prime depth wait driftValue tail scale
      multiplier_ne scale_ne
  have oldReconstruction :=
    parameterGradientOfJet_renormalized scale gradient scale_ne
  have newReconstruction :=
    parameterGradientOfJet_renormalized
      (sensitivityScaleStep prime depth wait driftValue tail scale)
      (parameterGradientStep prime depth wait driftValue tail gradient)
      nextScale_ne
  have transverse :
      planeCross gradient
          (parameterGradientStep prime depth wait driftValue tail gradient) ≠
        0 := by
    intro cross_zero
    apply defect_ne
    rw [renormalizedTransverseDefect_eq_planeCross_step, cross_zero]
    simp
  have jetCross_ne :
      planeCross
          (renormalizedParameterGradient scale gradient)
          (renormalizedParameterGradient
            (sensitivityScaleStep prime depth wait driftValue tail scale)
            (parameterGradientStep prime depth wait driftValue tail gradient)) ≠
        0 := by
    intro jetCross_zero
    apply transverse
    calc
      planeCross gradient
          (parameterGradientStep prime depth wait driftValue tail gradient) =
          planeCross
            (parameterGradientOfJet scale
              (renormalizedParameterGradient scale gradient))
            (parameterGradientOfJet
              (sensitivityScaleStep prime depth wait driftValue tail scale)
              (renormalizedParameterGradient
                (sensitivityScaleStep prime depth wait driftValue tail scale)
                (parameterGradientStep prime depth wait driftValue tail
                  gradient))) := by
            rw [oldReconstruction, newReconstruction]
      _ =
          scale *
              sensitivityScaleStep prime depth wait driftValue tail scale *
            planeCross
              (renormalizedParameterGradient scale gradient)
              (renormalizedParameterGradient
                (sensitivityScaleStep prime depth wait driftValue tail scale)
                (parameterGradientStep prime depth wait driftValue tail
                  gradient)) := by
            rw [planeCross_parameterGradientOfJet]
      _ = 0 := by rw [jetCross_zero, mul_zero]
  have core :=
    planeSolveDigit_parameterGradientOfJet
      oldValue
      (renormalizedParameterGradient scale gradient)
      newValue
      (renormalizedParameterGradient
        (sensitivityScaleStep prime depth wait driftValue tail scale)
        (parameterGradientStep prime depth wait driftValue tail gradient))
      oldTarget scale
      (sensitivityScaleStep prime depth wait driftValue tail scale)
      scale_ne nextScale_ne jetCross_ne
  rw [oldReconstruction, newReconstruction] at core
  have ratio_eq :
      sensitivityScaleStep prime depth wait driftValue tail scale / scale =
        -sensitivityMultiplier prime depth wait driftValue tail := by
    simp only [sensitivityScaleStep]
    field_simp [scale_ne]
  have defect_eq :
      sensitivityScaleStep prime depth wait driftValue tail scale *
          planeCross
            (renormalizedParameterGradient scale gradient)
            (renormalizedParameterGradient
              (sensitivityScaleStep prime depth wait driftValue tail scale)
              (parameterGradientStep prime depth wait driftValue tail gradient)) =
        renormalizedTransverseDefect
          (legalPayload prime depth wait tail) scale gradient := by
    calc
      _ =
          (scale *
              sensitivityScaleStep prime depth wait driftValue tail scale *
            planeCross
              (renormalizedParameterGradient scale gradient)
              (renormalizedParameterGradient
                (sensitivityScaleStep prime depth wait driftValue tail scale)
                (parameterGradientStep prime depth wait driftValue tail
                  gradient))) /
            scale := by field_simp [scale_ne]
                        ring
      _ =
          planeCross
              (parameterGradientOfJet scale
                (renormalizedParameterGradient scale gradient))
              (parameterGradientOfJet
                (sensitivityScaleStep prime depth wait driftValue tail scale)
                (renormalizedParameterGradient
                  (sensitivityScaleStep prime depth wait driftValue tail scale)
                  (parameterGradientStep prime depth wait driftValue tail
                    gradient))) /
            scale := by rw [planeCross_parameterGradientOfJet]
      _ =
          planeCross gradient
              (parameterGradientStep prime depth wait driftValue tail gradient) /
            scale := by rw [oldReconstruction, newReconstruction]
      _ =
          renormalizedTransverseDefect
            (legalPayload prime depth wait tail) scale gradient := by
          rw [← renormalizedTransverseDefect_eq_planeCross_step]
  simpa only [weightedParameterStepDigit, ratio_eq, defect_eq] using core

/-- Exact p-adic weight of the center refinement digit. -/
theorem weightedPlaneSolveDigit_zero_hasValue
    {prime : Nat} [Fact prime.Prime]
    {oldValue newValue oldTarget scaleRatio transverseDefect : ℚ}
    {oldJet newJet : Fin 2 → ℚ}
    {numeratorValue defectValue : ℤ}
    (numerator_value :
      HasValue prime
        (weightedCenterNumerator oldValue oldJet newValue newJet
          oldTarget scaleRatio)
        numeratorValue)
    (defect_value :
      HasValue prime transverseDefect defectValue) :
    HasValue prime
      (weightedPlaneSolveDigit oldValue oldJet newValue newJet
        oldTarget scaleRatio transverseDefect 0)
      (numeratorValue - defectValue) := by
  simpa [weightedPlaneSolveDigit] using
    div_hasValue numerator_value defect_value

/-- Exact p-adic weight of the reset refinement digit. -/
theorem weightedPlaneSolveDigit_one_hasValue
    {prime : Nat} [Fact prime.Prime]
    {oldValue newValue oldTarget scaleRatio transverseDefect : ℚ}
    {oldJet newJet : Fin 2 → ℚ}
    {numeratorValue defectValue : ℤ}
    (numerator_value :
      HasValue prime
        (weightedResetNumerator oldValue oldJet newValue newJet
          oldTarget scaleRatio)
        numeratorValue)
    (defect_value :
      HasValue prime transverseDefect defectValue) :
    HasValue prime
      (weightedPlaneSolveDigit oldValue oldJet newValue newJet
        oldTarget scaleRatio transverseDefect 1)
      (numeratorValue - defectValue) := by
  simpa [weightedPlaneSolveDigit] using
    div_hasValue numerator_value defect_value

/-- Arbitrary transverse depth becomes an equally deep denominator in the weighted center
digit.  Renormalization cancels the raw sensitivity scale but cannot bound the arithmetic
precision required by Cramer's rule. -/
theorem prescribedTransverseDepth_weightedCenterDigit
    {prime : Nat} [Fact prime.Prime]
    (depth wait transverseDepth : Nat) (wait_positive : 0 < wait) :
    weightedParameterStepDigit prime depth wait 1
        (prescribedTransverseDepthTail prime depth wait transverseDepth)
        0 1 0 1 resetParameterGradient 0 =
      1 / (prime : ℚ) ^ transverseDepth := by
  simp only [weightedParameterStepDigit, weightedPlaneSolveDigit,
    weightedCenterNumerator, renormalizedParameterGradient,
    resetParameterGradient, parameterGradientMass,
    renormalizedTransverseDefect, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, zero_add, zero_div, sub_self,
    zero_mul, one_mul, one_div]
  rw [legalPayload_prescribedTransverseDepthTail
    depth wait transverseDepth wait_positive]
  ring

/-- Exact valuation of the unbounded weighted center denominator. -/
theorem prescribedTransverseDepth_weightedCenterDigit_hasValue
    {prime : Nat} [Fact prime.Prime]
    (depth wait transverseDepth : Nat) (wait_positive : 0 < wait) :
    HasValue prime
      (weightedParameterStepDigit prime depth wait 1
        (prescribedTransverseDepthTail prime depth wait transverseDepth)
        0 1 0 1 resetParameterGradient 0)
      (-(transverseDepth : ℤ)) := by
  rw [prescribedTransverseDepth_weightedCenterDigit
    depth wait transverseDepth wait_positive]
  have one_unit : IsUnit prime (1 : ℚ) :=
    ⟨one_ne_zero, padicValRat.one⟩
  convert div_hasValue one_unit
    (primePower_hasValue (prime := prime) transverseDepth) using 1
  omega

/-- One refinement step in a moving parameter basis. -/
def parameterRefinement
    {K : Type*} [CommRing K]
    (origin : Fin 2 → K) (basis : Matrix (Fin 2) (Fin 2) K)
    (digit : Fin 2 → K) : Fin 2 → K :=
  origin + basis *ᵥ digit

/-- Exact tail transport for a moving parameter basis.

The ordinary fixed-base digit recurrence is the special case in which `transport` is a fixed
scalar matrix.  For guard lifting, the basis is built from the changing normalized jets, so
the tail is conjugated by a nonconstant matrix cocycle.  Periodicity of ordinary rational
digits therefore constrains the weighted Cramer stream only after this transport cocycle is
controlled. -/
theorem parameterRefinement_movingBasis
    {K : Type*} [CommRing K]
    (origin : Fin 2 → K)
    (basis transport : Matrix (Fin 2) (Fin 2) K)
    (digit nextTail : Fin 2 → K) :
    parameterRefinement origin basis
        (digit + transport *ᵥ nextTail) =
      parameterRefinement origin basis digit +
        (basis * transport) *ᵥ nextTail := by
  simp [parameterRefinement, Matrix.mulVec_add, Matrix.mulVec_mulVec]
  abel

end
end MatrixMortality.ReturnGuard
