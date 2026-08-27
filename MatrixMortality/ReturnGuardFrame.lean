import MatrixMortality.ReturnGuardGauss
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Evaluation frames of the guard parameter jet

The normalized center/reset gradient is best read as an evaluation frame, not as a second
dynamical system.  Its consecutive transition is an explicit change of basis, hence a
coboundary.  The transverse scalar is only the determinant needed to recover fixed parameter
coordinates from two evaluation values.

This file retains the exact algebraic core of the former moving-Cramer branch without carrying
its generic digit automaton.
-/

namespace MatrixMortality.ReturnGuard

open MatrixMortality.PadicValuation
open scoped Matrix

noncomputable section

/-- One additive step of the scale-free mass/reset jet. -/
def evaluationJetStep
    (nextScale payload : ℚ) (jet : Fin 2 → ℚ) : Fin 2 → ℚ :=
  jet + ![1 / nextScale, payload / nextScale]

/-- Evaluation frame with columns `jet` and `(1,payload)`. -/
def evaluationFrame
    (jet : Fin 2 → ℚ) (payload : ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![jet 0, 1;
     jet 1, payload]

/-- Determinant of the evaluation frame. -/
def frameDefect (jet : Fin 2 → ℚ) (payload : ℚ) : ℚ :=
  payload * jet 0 - jet 1

/-- Exact frame transition between two consecutive payloads. -/
def evaluationFrameTransition
    (nextScale currentPayload nextPayload : ℚ)
    (jet : Fin 2 → ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  let quotient := (nextPayload - currentPayload) / frameDefect jet currentPayload
  !![1, -quotient;
     1 / nextScale, 1 + quotient * jet 0]

/-- The frame determinant is exactly the transverse defect. -/
theorem evaluationFrame_det
    (jet : Fin 2 → ℚ) (payload : ℚ) :
    (evaluationFrame jet payload).det = frameDefect jet payload := by
  rw [Matrix.det_fin_two]
  simp [evaluationFrame, frameDefect]
  ring

/-- The defect after a jet step changes only through the payload displacement. -/
theorem frameDefect_step
    (nextScale currentPayload nextPayload : ℚ)
    (jet : Fin 2 → ℚ) (nextScale_ne : nextScale ≠ 0) :
    frameDefect (evaluationJetStep nextScale currentPayload jet) nextPayload =
      frameDefect jet currentPayload +
        (nextPayload - currentPayload) *
          evaluationJetStep nextScale currentPayload jet 0 := by
  simp [frameDefect, evaluationJetStep]
  field_simp [nextScale_ne]
  ring

/-- Consecutive evaluation frames differ by the displayed explicit basis change. -/
theorem evaluationFrame_mul_transition
    (nextScale currentPayload nextPayload : ℚ)
    (jet : Fin 2 → ℚ)
    (nextScale_ne : nextScale ≠ 0)
    (defect_ne : frameDefect jet currentPayload ≠ 0) :
    evaluationFrame jet currentPayload *
        evaluationFrameTransition nextScale currentPayload nextPayload jet =
      evaluationFrame
        (evaluationJetStep nextScale currentPayload jet) nextPayload := by
  have raw_defect_ne :
      currentPayload * jet 0 - jet 1 ≠ 0 := by
    simpa [frameDefect] using defect_ne
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [evaluationFrame, evaluationFrameTransition, evaluationJetStep,
      frameDefect, Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals field_simp [nextScale_ne, raw_defect_ne]
  all_goals ring

/-- The consecutive frame transition is literally `F⁻¹F'`; its matrix cocycle is pure gauge. -/
theorem evaluationFrameTransition_eq_coboundary
    (nextScale currentPayload nextPayload : ℚ)
    (jet : Fin 2 → ℚ)
    (nextScale_ne : nextScale ≠ 0)
    (defect_ne : frameDefect jet currentPayload ≠ 0) :
    evaluationFrameTransition nextScale currentPayload nextPayload jet =
      (evaluationFrame jet currentPayload)⁻¹ *
        evaluationFrame
          (evaluationJetStep nextScale currentPayload jet) nextPayload := by
  symm
  rw [← evaluationFrame_mul_transition
    nextScale currentPayload nextPayload jet nextScale_ne defect_ne]
  apply Matrix.nonsing_inv_mul_cancel_left
  rw [evaluationFrame_det]
  exact isUnit_iff_ne_zero.mpr defect_ne

/-- Determinants telescope by the exact ratio of consecutive transverse defects. -/
theorem evaluationFrameTransition_det
    (nextScale currentPayload nextPayload : ℚ)
    (jet : Fin 2 → ℚ)
    (nextScale_ne : nextScale ≠ 0)
    (defect_ne : frameDefect jet currentPayload ≠ 0) :
    (evaluationFrameTransition
        nextScale currentPayload nextPayload jet).det =
      frameDefect
          (evaluationJetStep nextScale currentPayload jet) nextPayload /
        frameDefect jet currentPayload := by
  have frame_product :=
    congrArg Matrix.det
      (evaluationFrame_mul_transition
        nextScale currentPayload nextPayload jet nextScale_ne defect_ne)
  rw [Matrix.det_mul, evaluationFrame_det, evaluationFrame_det] at frame_product
  apply (eq_div_iff defect_ne).2
  simpa [mul_comm] using frame_product

/-- Center/reset parameter displacement written in mass/reset coordinates. -/
def massResetDisplacement (displacement : Fin 2 → ℚ) : Fin 2 → ℚ :=
  ![displacement 0, displacement 1 - displacement 0]

/-- Recovering fixed parameter coordinates is the only place the frame determinant enters. -/
theorem evaluationFrame_transpose_mulVec_massReset
    (jet : Fin 2 → ℚ) (payload : ℚ) (displacement : Fin 2 → ℚ) :
    (evaluationFrame jet payload)ᵀ *ᵥ massResetDisplacement displacement =
      ![
        (jet 0 - jet 1) * displacement 0 + jet 1 * displacement 1,
        (1 - payload) * displacement 0 + payload * displacement 1
      ] := by
  ext i
  fin_cases i
  all_goals
    simp [evaluationFrame, massResetDisplacement, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]
  all_goals ring

/-- Projective shadow carried by a nonvertical evaluation jet. -/
def shadowPayload (jet : Fin 2 → ℚ) : ℚ :=
  jet 1 / jet 0

/-- The frame defect is the state/shadow separation, scaled by the jet mass. -/
theorem frameDefect_eq_mass_mul_shadowGap
    (jet : Fin 2 → ℚ) (payload : ℚ) (mass_ne : jet 0 ≠ 0) :
    frameDefect jet payload =
      jet 0 * (payload - shadowPayload jet) := by
  simp [frameDefect, shadowPayload]
  field_simp [mass_ne]

/-- Jet evaluation at the fixed center/drift anchor. -/
def anchoredJet (anchor : ℚ) (jet : Fin 2 → ℚ) : ℚ :=
  jet 1 + anchor * jet 0

/-- The anchor increment is the anchored payload divided by the next integrating factor. -/
theorem anchoredJet_step
    (nextScale payload anchor : ℚ) (jet : Fin 2 → ℚ)
    (nextScale_ne : nextScale ≠ 0) :
    anchoredJet anchor (evaluationJetStep nextScale payload jet) =
      anchoredJet anchor jet + (payload + anchor) / nextScale := by
  simp [anchoredJet, evaluationJetStep]
  field_simp [nextScale_ne]
  ring

/-- Any anchored increment deeper than the reset shell preserves the anchored depth exactly. -/
theorem anchoredJet_step_hasValue
    {prime : Nat} [Fact prime.Prime]
    {nextScale payload anchor : ℚ} {jet : Fin 2 → ℚ}
    {anchorDepth payloadDepth scaleDepth : ℤ}
    (anchor_value : HasValue prime (anchoredJet anchor jet) anchorDepth)
    (payload_value : HasValue prime (payload + anchor) payloadDepth)
    (scale_value : HasValue prime nextScale scaleDepth)
    (deeper : anchorDepth < payloadDepth - scaleDepth) :
    HasValue prime
      (anchoredJet anchor (evaluationJetStep nextScale payload jet))
      anchorDepth := by
  rw [anchoredJet_step nextScale payload anchor jet scale_value.1]
  exact add_hasValue_left anchor_value
    (div_hasValue payload_value scale_value) deeper

/-- The transverse defect compares the actual payload with the anchored shadow evaluation. -/
theorem frameDefect_eq_anchoredSeparation
    (jet : Fin 2 → ℚ) (payload anchor : ℚ) :
    frameDefect jet payload =
      jet 0 * (payload + anchor) - anchoredJet anchor jet := by
  simp [frameDefect, anchoredJet]
  ring

/-- Below the anchor shell, the actual payload depth is the exact transverse depth. -/
theorem frameDefect_hasValue_of_state_lt_anchor
    {prime : Nat} [Fact prime.Prime]
    {jet : Fin 2 → ℚ} {payload anchor : ℚ} {stateDepth anchorDepth : ℤ}
    (mass_unit : IsUnit prime (jet 0))
    (state_value : HasValue prime (payload + anchor) stateDepth)
    (anchor_value : HasValue prime (anchoredJet anchor jet) anchorDepth)
    (state_lt : stateDepth < anchorDepth) :
    HasValue prime (frameDefect jet payload) stateDepth := by
  rw [frameDefect_eq_anchoredSeparation jet payload anchor]
  have result :=
    add_hasValue_left
      (mul_hasValue mass_unit state_value)
      (neg_hasValue anchor_value) (by simpa using state_lt)
  simpa only [sub_eq_add_neg, zero_add] using result

/-- Above the anchor shell, the fixed anchor depth is the exact transverse depth. -/
theorem frameDefect_hasValue_of_anchor_lt_state
    {prime : Nat} [Fact prime.Prime]
    {jet : Fin 2 → ℚ} {payload anchor : ℚ} {stateDepth anchorDepth : ℤ}
    (mass_unit : IsUnit prime (jet 0))
    (state_value : HasValue prime (payload + anchor) stateDepth)
    (anchor_value : HasValue prime (anchoredJet anchor jet) anchorDepth)
    (anchor_lt : anchorDepth < stateDepth) :
    HasValue prime (frameDefect jet payload) anchorDepth := by
  rw [frameDefect_eq_anchoredSeparation jet payload anchor]
  have result :=
    add_hasValue_right
      (mul_hasValue mass_unit state_value)
      (neg_hasValue anchor_value) (by simpa using anchor_lt)
  simpa only [sub_eq_add_neg, zero_add] using result

/-- Any transverse depth strictly beyond the anchor shell forces an exact return to that
shell. This is the reset-shell localization of the former Cramer denominator. -/
theorem deep_frameDefect_forces_stateDepth_eq_anchorDepth
    {prime : Nat} [Fact prime.Prime]
    {jet : Fin 2 → ℚ} {payload anchor : ℚ}
    {stateDepth anchorDepth defectDepth : ℤ}
    (mass_unit : IsUnit prime (jet 0))
    (state_value : HasValue prime (payload + anchor) stateDepth)
    (anchor_value : HasValue prime (anchoredJet anchor jet) anchorDepth)
    (defect_value : HasValue prime (frameDefect jet payload) defectDepth)
    (anchor_lt_defect : anchorDepth < defectDepth) :
    stateDepth = anchorDepth := by
  rcases lt_trichotomy stateDepth anchorDepth with
    state_lt | equal | anchor_lt
  · have shallow :=
      frameDefect_hasValue_of_state_lt_anchor
        mass_unit state_value anchor_value state_lt
    have depths_equal : stateDepth = defectDepth := by
      rw [← shallow.2, defect_value.2]
    omega
  · exact equal
  · have shallow :=
      frameDefect_hasValue_of_anchor_lt_state
        mass_unit state_value anchor_value anchor_lt
    have depths_equal : anchorDepth = defectDepth := by
      rw [← shallow.2, defect_value.2]
    omega

/-- A unit terminal payload is always transverse to a positive-depth reset anchor. -/
theorem terminal_frameDefect_isUnit
    {prime : Nat} [Fact prime.Prime]
    {jet : Fin 2 → ℚ} {payload anchor : ℚ} {anchorDepth : ℤ}
    (mass_unit : IsUnit prime (jet 0))
    (terminal_unit : IsUnit prime (payload + anchor))
    (anchor_value : HasValue prime (anchoredJet anchor jet) anchorDepth)
    (anchor_positive : 0 < anchorDepth) :
    IsUnit prime (frameDefect jet payload) :=
  frameDefect_hasValue_of_state_lt_anchor
    mass_unit terminal_unit anchor_value anchor_positive

end
end MatrixMortality.ReturnGuard
