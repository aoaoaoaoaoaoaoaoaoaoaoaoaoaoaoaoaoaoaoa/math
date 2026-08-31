import MatrixMortality.ReturnSquareComposite

/-!
# Fraction pullbacks for ReturnSquare

This file turns the full rational fraction `d=A/B` in composite-base ReturnSquare into an exact
two-coordinate pullback recurrence.  It is a projective return interface, not a reduction from
`M₃(2)` to three-generator `M₂(3)`: the pullback alphabet still contains every geometric scale
`qⁿ`.
-/

namespace MatrixMortality.ReturnSquare

open scoped Matrix
open PadicValuation

private theorem add_hasValue_min_of_ne
    {prime : Nat} [Fact prime.Prime]
    {left right : ℚ} {leftValue rightValue : ℤ}
    (left_shell : HasValue prime left leftValue)
    (right_shell : HasValue prime right rightValue)
    (value_ne : leftValue ≠ rightValue) :
    HasValue prime (left + right) (min leftValue rightValue) := by
  rcases lt_or_gt_of_ne value_ne with left_lt | right_lt
  · simpa [min_eq_left left_lt.le] using
      add_hasValue_left left_shell right_shell left_lt
  · simpa [min_eq_right right_lt.le] using
      add_hasValue_right left_shell right_shell right_lt

/-- A denominator-cleared return at parameter `c=-A/B`. -/
def fractionIntegralTransfer {R : Type*} [CommRing R] (A B t : R) :
    Square (Fin 2) R :=
  !![(B - A) * t ^ 2 - B, B * t;
     -A, B * t]

/-- The homogeneous dual pullback on a row encoded as `(R,-BS)`. -/
def fractionPullback {R : Type*} [CommRing R] (A B t : R) :
    Square (Fin 2) R :=
  !![(B - A) * t ^ 2 - B, A * B;
     -t, B * t]

/-- Diagonal gauge sending a pullback column `(R,S)` to the physical row `(R,-BS)`. -/
def fractionGauge {R : Type*} [CommRing R] (B : R) : Square (Fin 2) R :=
  !![1, 0;
     0, -B]

/-- Clearing the fraction denominator multiplies the rational return by `B`. -/
theorem fractionIntegralTransfer_eq_smul (A B t : ℚ) (B_ne : B ≠ 0) :
    fractionIntegralTransfer A B t = B • transfer (-(A / B)) t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fractionIntegralTransfer, transfer, Matrix.smul_apply]
  all_goals field_simp
  all_goals ring

/-- One dual step is the transpose of the denominator-cleared return in the fixed gauge. -/
theorem fractionIntegralTransfer_transpose_mul_gauge
    {R : Type*} [CommRing R] (A B t : R) :
    (fractionIntegralTransfer A B t)ᵀ * fractionGauge B =
      fractionGauge B * fractionPullback A B t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fractionIntegralTransfer, fractionGauge, fractionPullback,
      Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals ring

/-- Dualization reverses a complete return word. -/
theorem fractionIntegralWord_transpose_mul_gauge
    {R : Type*} [CommRing R] (A B : R) (scales : List R) :
    (wordProduct (fractionIntegralTransfer A B) scales)ᵀ * fractionGauge B =
      fractionGauge B * wordProduct (fractionPullback A B) scales.reverse := by
  induction scales with
  | nil => simp
  | cons head tail induction =>
      rw [wordProduct_cons, Matrix.transpose_mul, Matrix.mul_assoc,
        fractionIntegralTransfer_transpose_mul_gauge,
        ← Matrix.mul_assoc, induction, Matrix.mul_assoc]
      simp [wordProduct_append]

/-- The pullback is invertible at every nondegenerate positive return. -/
theorem fractionPullback_det {R : Type*} [CommRing R] (A B t : R) :
    (fractionPullback A B t).det = B * (B - A) * t * (t ^ 2 - 1) := by
  rw [Matrix.det_fin_two]
  simp [fractionPullback]
  ring

/-- The first dual pullback normalizes to the fraction numerator times the selected scale. -/
theorem fractionPullback_mulVec_reset {R : Type*} [CommRing R] (A B t : R) :
    fractionPullback A B t *ᵥ ![A, 1] =
      ((B - A) * t) • ![A * t, 1] := by
  ext i
  fin_cases i <;>
    simp [fractionPullback, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring

/-- Homogeneous predecessor of the terminal line `(B,1)` under one pullback. -/
def fractionTerminalPredecessorVector {R : Type*} [CommRing R] (A B t : R) :
    Fin 2 → R :=
  ![B * (B * t - A), B * t + (B - A) * t ^ 2 - B]

/-- The displayed predecessor reaches the terminal line exactly. -/
theorem fractionPullback_mulVec_terminalPredecessor
    {R : Type*} [CommRing R] (A B t : R) :
    fractionPullback A B t *ᵥ fractionTerminalPredecessorVector A B t =
      (B * t * (B - A) * (t ^ 2 - 1)) • ![B, 1] := by
  ext i
  fin_cases i <;>
    simp [fractionPullback, fractionTerminalPredecessorVector,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring

/-- Cross-multiplied classification of every affine predecessor of the terminal line. -/
theorem fractionPullback_terminal_incidence_iff
    {R : Type*} [CommRing R] (A B t r : R) :
    (fractionPullback A B t *ᵥ ![r, 1]) 0 =
        B * (fractionPullback A B t *ᵥ ![r, 1]) 1 ↔
      (B * t + (B - A) * t ^ 2 - B) * r = B * (B * t - A) := by
  simp [fractionPullback, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  constructor <;> intro equality
  · linear_combination equality
  · linear_combination equality

/-- Affine terminal predecessor when its homogeneous denominator survives. -/
def fractionTerminalPredecessor (A B t : ℚ) : ℚ :=
  B * (B * t - A) / (B * t + (B - A) * t ^ 2 - B)

/-- The terminal predecessor is unique whenever its displayed denominator is nonzero. -/
theorem fractionPullback_terminal_incidence_iff_eq_predecessor
    (A B t r : ℚ)
    (denominator_ne : B * t + (B - A) * t ^ 2 - B ≠ 0) :
    (fractionPullback A B t *ᵥ ![r, 1]) 0 =
        B * (fractionPullback A B t *ᵥ ![r, 1]) 1 ↔
      r = fractionTerminalPredecessor A B t := by
  rw [fractionPullback_terminal_incidence_iff]
  constructor
  · intro cross
    rw [fractionTerminalPredecessor]
    apply (eq_div_iff denominator_ne).2
    simpa [mul_comm] using cross
  · intro predecessor
    rw [fractionTerminalPredecessor] at predecessor
    have cross := (eq_div_iff denominator_ne).1 predecessor
    simpa [mul_comm] using cross

/-- Homogeneous predecessor of an arbitrary target ray `(s,1)`. -/
def fractionPredecessorVector {R : Type*} [CommRing R] (A B t s : R) :
    Fin 2 → R :=
  ![B * (s * t - A), s * t + (B - A) * t ^ 2 - B]

/-- The arbitrary predecessor vector realizes its target ray exactly. -/
theorem fractionPullback_mulVec_predecessor
    {R : Type*} [CommRing R] (A B t s : R) :
    fractionPullback A B t *ᵥ fractionPredecessorVector A B t s =
      (B * (B - A) * t * (t ^ 2 - 1)) • ![s, 1] := by
  ext i
  fin_cases i <;>
    simp [fractionPullback, fractionPredecessorVector,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring

/-- Affine inverse branch for an arbitrary target coordinate. -/
def fractionPredecessor (A B t s : ℚ) : ℚ :=
  B * (s * t - A) / (s * t + (B - A) * t ^ 2 - B)

/-- Cross-multiplied classification of every predecessor of `(s,1)`. -/
theorem fractionPullback_incidence_iff
    {R : Type*} [CommRing R] (A B t s r : R) :
    (fractionPullback A B t *ᵥ ![r, 1]) 0 =
        s * (fractionPullback A B t *ᵥ ![r, 1]) 1 ↔
      (s * t + (B - A) * t ^ 2 - B) * r = B * (s * t - A) := by
  simp [fractionPullback, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  constructor <;> intro equality
  · linear_combination equality
  · linear_combination equality

/-- The arbitrary affine inverse branch is unique off its displayed pole. -/
theorem fractionPullback_incidence_iff_eq_predecessor
    (A B t s r : ℚ)
    (denominator_ne : s * t + (B - A) * t ^ 2 - B ≠ 0) :
    (fractionPullback A B t *ᵥ ![r, 1]) 0 =
        s * (fractionPullback A B t *ᵥ ![r, 1]) 1 ↔
      r = fractionPredecessor A B t s := by
  rw [fractionPullback_incidence_iff]
  constructor
  · intro cross
    rw [fractionPredecessor]
    apply (eq_div_iff denominator_ne).2
    simpa [mul_comm] using cross
  · intro predecessor
    rw [fractionPredecessor] at predecessor
    have cross := (eq_div_iff denominator_ne).1 predecessor
    simpa [mul_comm] using cross

/-- A target deeper than the inverse scale (`vₚ(s)+vₚ(t)<0`) pulls back to the complete
denominator depth. -/
theorem fractionPredecessor_hasValue_of_target_below
    {prime : Nat} [Fact prime.Prime]
    (A B t s : ℚ) (BValue tValue targetValue : ℤ)
    (A_unit : IsUnit prime A)
    (B_shell : HasValue prime B BValue) (B_positive : 0 < BValue)
    (t_shell : HasValue prime t tValue) (t_positive : 0 < tValue)
    (target_shell : HasValue prime s targetValue)
    (target_below : targetValue + tValue < 0) :
    HasValue prime (fractionPredecessor A B t s) BValue := by
  have B_positive_shell : IsPositive prime B :=
    ⟨B_shell.1, B_shell.2.symm ▸ B_positive⟩
  have t_positive_shell : IsPositive prime t :=
    ⟨t_shell.1, t_shell.2.symm ▸ t_positive⟩
  have A_neg_unit : IsUnit prime (-A) := neg_hasValue A_unit
  have B_sub_A_unit : IsUnit prime (B - A) := by
    have A_sub_B_unit := unit_sub_positive A_unit B_positive_shell
    rw [show B - A = -(A - B) by ring]
    exact neg_hasValue A_sub_B_unit
  have target_scale_shell :
      HasValue prime (s * t) (targetValue + tValue) :=
    mul_hasValue target_shell t_shell
  have target_sub_A_shell :
      HasValue prime (s * t - A) (targetValue + tValue) := by
    simpa [sub_eq_add_neg] using
      add_hasValue_left target_scale_shell A_neg_unit target_below
  have numerator_shell :
      HasValue prime (B * (s * t - A))
        (BValue + (targetValue + tValue)) :=
    mul_hasValue B_shell target_sub_A_shell
  have t_sq_shell : HasValue prime (t ^ 2) (2 * tValue) := by
    have square := mul_hasValue t_shell t_shell
    simpa [pow_two, two_mul] using square
  have square_term_shell :
      HasValue prime ((B - A) * t ^ 2) (2 * tValue) := by
    simpa using mul_hasValue B_sub_A_unit t_sq_shell
  have first_sum_shell :
      HasValue prime (s * t + (B - A) * t ^ 2)
        (targetValue + tValue) :=
    add_hasValue_left target_scale_shell square_term_shell (by omega)
  have denominator_shell :
      HasValue prime (s * t + (B - A) * t ^ 2 - B)
        (targetValue + tValue) := by
    simpa [sub_eq_add_neg] using
      add_hasValue_left first_sum_shell (neg_hasValue B_shell) (by omega)
  have quotient := div_hasValue numerator_shell denominator_shell
  simpa [fractionPredecessor] using quotient

/-- Above the inverse scale, and away from the three pairwise valuation ties in the denominator,
the inverse branch follows one exact tropical minimum. -/
theorem fractionPredecessor_hasValue_of_target_above
    {prime : Nat} [Fact prime.Prime]
    (A B t s : ℚ) (BValue tValue targetValue : ℤ)
    (A_unit : IsUnit prime A)
    (B_shell : HasValue prime B BValue) (B_positive : 0 < BValue)
    (t_shell : HasValue prime t tValue) (t_positive : 0 < tValue)
    (target_shell : HasValue prime s targetValue)
    (target_above : 0 < targetValue + tValue)
    (target_scale_ne_square : targetValue + tValue ≠ 2 * tValue)
    (target_scale_ne_denominator : targetValue + tValue ≠ BValue)
    (square_ne_denominator : 2 * tValue ≠ BValue) :
    HasValue prime (fractionPredecessor A B t s)
      (BValue - min (min (targetValue + tValue) (2 * tValue)) BValue) := by
  have B_positive_shell : IsPositive prime B :=
    ⟨B_shell.1, B_shell.2.symm ▸ B_positive⟩
  have t_positive_shell : IsPositive prime t :=
    ⟨t_shell.1, t_shell.2.symm ▸ t_positive⟩
  have target_scale_shell :
      HasValue prime (s * t) (targetValue + tValue) :=
    mul_hasValue target_shell t_shell
  have target_scale_positive : IsPositive prime (s * t) :=
    ⟨target_scale_shell.1, target_scale_shell.2.symm ▸ target_above⟩
  have A_sub_target_scale_unit : IsUnit prime (A - s * t) :=
    unit_sub_positive A_unit target_scale_positive
  have target_scale_sub_A_unit : IsUnit prime (s * t - A) := by
    rw [show s * t - A = -(A - s * t) by ring]
    exact neg_hasValue A_sub_target_scale_unit
  have numerator_shell :
      HasValue prime (B * (s * t - A)) BValue := by
    simpa using mul_hasValue B_shell target_scale_sub_A_unit
  have A_sub_B_unit : IsUnit prime (A - B) :=
    unit_sub_positive A_unit B_positive_shell
  have B_sub_A_unit : IsUnit prime (B - A) := by
    rw [show B - A = -(A - B) by ring]
    exact neg_hasValue A_sub_B_unit
  have t_sq_shell : HasValue prime (t ^ 2) (2 * tValue) := by
    have square := mul_hasValue t_shell t_shell
    simpa [pow_two, two_mul] using square
  have square_term_shell :
      HasValue prime ((B - A) * t ^ 2) (2 * tValue) := by
    simpa using mul_hasValue B_sub_A_unit t_sq_shell
  have first_sum_shell :
      HasValue prime (s * t + (B - A) * t ^ 2)
        (min (targetValue + tValue) (2 * tValue)) :=
    add_hasValue_min_of_ne target_scale_shell square_term_shell
      target_scale_ne_square
  have first_min_ne_denominator :
      min (targetValue + tValue) (2 * tValue) ≠ BValue := by
    intro equality
    rcases min_choice (targetValue + tValue) (2 * tValue) with minimum | minimum
    · exact target_scale_ne_denominator (minimum ▸ equality)
    · exact square_ne_denominator (minimum ▸ equality)
  have denominator_shell :
      HasValue prime (s * t + (B - A) * t ^ 2 - B)
        (min (min (targetValue + tValue) (2 * tValue)) BValue) := by
    simpa [sub_eq_add_neg] using
      add_hasValue_min_of_ne first_sum_shell (neg_hasValue B_shell)
        first_min_ne_denominator
  exact div_hasValue numerator_shell denominator_shell

/-! ## Exact residue laws on the four valuation walls -/

/-- At the numerator wall `vₚ(st)=0`, the denominator stays a unit.  Every common factor in
the predecessor therefore comes exactly from the visible difference `st-A`. -/
theorem fractionPredecessor_hasValue_of_numerator_wall
    {prime : Nat} [Fact prime.Prime]
    (A B t s : ℚ) (BValue tValue residueValue : ℤ)
    (A_unit : IsUnit prime A)
    (B_shell : HasValue prime B BValue) (B_positive : 0 < BValue)
    (t_shell : HasValue prime t tValue) (t_positive : 0 < tValue)
    (target_scale_unit : IsUnit prime (s * t))
    (residue_shell : HasValue prime (s * t - A) residueValue) :
    HasValue prime (fractionPredecessor A B t s) (BValue + residueValue) := by
  have B_positive_shell : IsPositive prime B :=
    ⟨B_shell.1, B_shell.2.symm ▸ B_positive⟩
  have A_sub_B_unit : IsUnit prime (A - B) :=
    unit_sub_positive A_unit B_positive_shell
  have B_sub_A_unit : IsUnit prime (B - A) := by
    rw [show B - A = -(A - B) by ring]
    exact neg_hasValue A_sub_B_unit
  have t_sq_shell : HasValue prime (t ^ 2) (2 * tValue) := by
    have square := mul_hasValue t_shell t_shell
    simpa [pow_two, two_mul] using square
  have square_term_shell :
      HasValue prime ((B - A) * t ^ 2) (2 * tValue) := by
    simpa using mul_hasValue B_sub_A_unit t_sq_shell
  have square_term_positive : IsPositive prime ((B - A) * t ^ 2) :=
    ⟨square_term_shell.1, square_term_shell.2.symm ▸ (by omega)⟩
  have first_sum_unit : IsUnit prime (s * t + (B - A) * t ^ 2) :=
    unit_add_positive target_scale_unit square_term_positive
  have denominator_unit :
      IsUnit prime (s * t + (B - A) * t ^ 2 - B) := by
    simpa [sub_eq_add_neg] using
      unit_add_positive first_sum_unit
        ⟨(neg_hasValue B_shell).1, (neg_hasValue B_shell).2.symm ▸ B_positive⟩
  have numerator_shell :
      HasValue prime (B * (s * t - A)) (BValue + residueValue) :=
    mul_hasValue B_shell residue_shell
  simpa [fractionPredecessor] using
    div_hasValue numerator_shell denominator_unit

/-- The center of the numerator wall is exact: `st=A` pulls back to zero.  Conversely, zero
cannot arise elsewhere on this wall because both the cleared denominator and `B` survive. -/
theorem fractionPredecessor_eq_zero_iff_of_numerator_wall
    {prime : Nat} [Fact prime.Prime]
    (A B t s : ℚ) (BValue tValue : ℤ)
    (A_unit : IsUnit prime A)
    (B_shell : HasValue prime B BValue) (B_positive : 0 < BValue)
    (t_shell : HasValue prime t tValue) (t_positive : 0 < tValue)
    (target_scale_unit : IsUnit prime (s * t)) :
    fractionPredecessor A B t s = 0 ↔ s * t = A := by
  have B_positive_shell : IsPositive prime B :=
    ⟨B_shell.1, B_shell.2.symm ▸ B_positive⟩
  have A_sub_B_unit : IsUnit prime (A - B) :=
    unit_sub_positive A_unit B_positive_shell
  have B_sub_A_unit : IsUnit prime (B - A) := by
    rw [show B - A = -(A - B) by ring]
    exact neg_hasValue A_sub_B_unit
  have t_sq_shell : HasValue prime (t ^ 2) (2 * tValue) := by
    have square := mul_hasValue t_shell t_shell
    simpa [pow_two, two_mul] using square
  have square_term_shell :
      HasValue prime ((B - A) * t ^ 2) (2 * tValue) := by
    simpa using mul_hasValue B_sub_A_unit t_sq_shell
  have square_term_positive : IsPositive prime ((B - A) * t ^ 2) :=
    ⟨square_term_shell.1, square_term_shell.2.symm ▸ (by omega)⟩
  have first_sum_unit : IsUnit prime (s * t + (B - A) * t ^ 2) :=
    unit_add_positive target_scale_unit square_term_positive
  have denominator_unit :
      IsUnit prime (s * t + (B - A) * t ^ 2 - B) := by
    simpa [sub_eq_add_neg] using
      unit_add_positive first_sum_unit
        ⟨(neg_hasValue B_shell).1, (neg_hasValue B_shell).2.symm ▸ B_positive⟩
  rw [fractionPredecessor]
  constructor
  · intro quotient_zero
    have numerator_or_denominator := div_eq_zero_iff.mp quotient_zero
    have numerator_zero :=
      numerator_or_denominator.resolve_right denominator_unit.1
    exact sub_eq_zero.mp
      ((mul_eq_zero.mp numerator_zero).resolve_left B_shell.1)
  · intro target_eq
    rw [target_eq, sub_self, mul_zero, zero_div]

/-- Residue remaining after the common `B` factor is removed on `s=tu`. -/
def fractionEqualScaleResidue (A B t u : ℚ) : ℚ :=
  t ^ 2 * (u + B - A) / B - 1

/-- Exact normalized inverse law on the equal-scale wall. -/
theorem fractionPredecessor_eq_equalScale_normalForm
    (A B t u : ℚ) (B_ne : B ≠ 0) :
    fractionPredecessor A B t (t * u) =
      (t ^ 2 * u - A) / fractionEqualScaleResidue A B t u := by
  rw [fractionPredecessor, fractionEqualScaleResidue]
  field_simp
  ring

/-- Once the common `B` factor is removed, the complete equal-scale-wall cancellation is the
valuation of `fractionEqualScaleResidue`; no hidden primitive reduction remains. -/
theorem fractionPredecessor_hasValue_of_equalScale_residue
    {prime : Nat} [Fact prime.Prime]
    (A B t u : ℚ) (tValue residueValue : ℤ)
    (A_unit : IsUnit prime A) (B_ne : B ≠ 0)
    (t_shell : HasValue prime t tValue) (t_positive : 0 < tValue)
    (u_unit : IsUnit prime u)
    (residue_shell :
      HasValue prime (fractionEqualScaleResidue A B t u) residueValue) :
    HasValue prime (fractionPredecessor A B t (t * u)) (-residueValue) := by
  have t_sq_shell : HasValue prime (t ^ 2) (2 * tValue) := by
    have square := mul_hasValue t_shell t_shell
    simpa [pow_two, two_mul] using square
  have t_sq_u_shell : HasValue prime (t ^ 2 * u) (2 * tValue) := by
    simpa using mul_hasValue t_sq_shell u_unit
  have t_sq_u_positive : IsPositive prime (t ^ 2 * u) :=
    ⟨t_sq_u_shell.1, t_sq_u_shell.2.symm ▸ (by omega)⟩
  have numerator_unit : IsUnit prime (t ^ 2 * u - A) := by
    have A_sub_target_unit := unit_sub_positive A_unit t_sq_u_positive
    rw [show t ^ 2 * u - A = -(A - t ^ 2 * u) by ring]
    exact neg_hasValue A_sub_target_unit
  rw [fractionPredecessor_eq_equalScale_normalForm A B t u B_ne]
  simpa using div_hasValue numerator_unit residue_shell

/-- On `vₚ(s)=vₚ(t)`, writing `s=tu` exposes the sole first residue
`u+B-A`. -/
theorem fractionPredecessor_hasValue_of_equal_scale_wall
    {prime : Nat} [Fact prime.Prime]
    (A B t u : ℚ) (BValue tValue residueValue : ℤ)
    (A_unit : IsUnit prime A)
    (B_shell : HasValue prime B BValue) (B_positive : 0 < BValue)
    (t_shell : HasValue prime t tValue) (t_positive : 0 < tValue)
    (u_unit : IsUnit prime u)
    (residue_shell : HasValue prime (u + B - A) residueValue)
    (secondary_ne : 2 * tValue + residueValue ≠ BValue) :
    HasValue prime (fractionPredecessor A B t (t * u))
      (BValue - min (2 * tValue + residueValue) BValue) := by
  have B_positive_shell : IsPositive prime B :=
    ⟨B_shell.1, B_shell.2.symm ▸ B_positive⟩
  have t_sq_shell : HasValue prime (t ^ 2) (2 * tValue) := by
    have square := mul_hasValue t_shell t_shell
    simpa [pow_two, two_mul] using square
  have t_sq_u_shell : HasValue prime (t ^ 2 * u) (2 * tValue) := by
    simpa using mul_hasValue t_sq_shell u_unit
  have t_sq_u_positive : IsPositive prime (t ^ 2 * u) :=
    ⟨t_sq_u_shell.1, t_sq_u_shell.2.symm ▸ (by omega)⟩
  have target_sub_A_unit : IsUnit prime ((t * u) * t - A) := by
    have A_sub_target_unit := unit_sub_positive A_unit t_sq_u_positive
    rw [show (t * u) * t - A = -(A - t ^ 2 * u) by ring]
    exact neg_hasValue A_sub_target_unit
  have numerator_shell :
      HasValue prime (B * ((t * u) * t - A)) BValue := by
    simpa using mul_hasValue B_shell target_sub_A_unit
  have residue_term_shell :
      HasValue prime (t ^ 2 * (u + B - A))
        (2 * tValue + residueValue) :=
    mul_hasValue t_sq_shell residue_shell
  have denominator_shell :
      HasValue prime (t ^ 2 * (u + B - A) - B)
        (min (2 * tValue + residueValue) BValue) := by
    simpa [sub_eq_add_neg] using
      add_hasValue_min_of_ne residue_term_shell (neg_hasValue B_shell) secondary_ne
  have denominator_eq :
      (t * u) * t + (B - A) * t ^ 2 - B =
        t ^ 2 * (u + B - A) - B := by
    ring
  rw [fractionPredecessor, denominator_eq]
  exact div_hasValue numerator_shell denominator_shell

/-- The zero residue on the equal-scale wall collapses to a unit affine expression rather than
creating an extra denominator shell. -/
theorem fractionPredecessor_equal_scale_eq_of_residue_zero
    (A B t u : ℚ) (B_ne : B ≠ 0) (residue_zero : u + B - A = 0) :
    fractionPredecessor A B t (t * u) = A - t ^ 2 * u := by
  rw [fractionPredecessor]
  have denominator_eq :
      (t * u) * t + (B - A) * t ^ 2 - B = -B := by
    linear_combination t ^ 2 * residue_zero
  rw [denominator_eq]
  field_simp
  ring

/-- The zero first residue on the equal-scale wall always drains to the unit shell. -/
theorem fractionPredecessor_isUnit_of_equalScale_residue_zero
    {prime : Nat} [Fact prime.Prime]
    (A B t u : ℚ) (tValue : ℤ)
    (A_unit : IsUnit prime A) (B_ne : B ≠ 0)
    (t_shell : HasValue prime t tValue) (t_positive : 0 < tValue)
    (u_unit : IsUnit prime u) (residue_zero : u + B - A = 0) :
    IsUnit prime (fractionPredecessor A B t (t * u)) := by
  have t_sq_shell : HasValue prime (t ^ 2) (2 * tValue) := by
    have square := mul_hasValue t_shell t_shell
    simpa [pow_two, two_mul] using square
  have t_sq_u_shell : HasValue prime (t ^ 2 * u) (2 * tValue) := by
    simpa using mul_hasValue t_sq_shell u_unit
  have t_sq_u_positive : IsPositive prime (t ^ 2 * u) :=
    ⟨t_sq_u_shell.1, t_sq_u_shell.2.symm ▸ (by omega)⟩
  rw [fractionPredecessor_equal_scale_eq_of_residue_zero
    A B t u B_ne residue_zero]
  exact unit_sub_positive A_unit t_sq_u_positive

/-- Residue remaining after the common `B` factor is removed on `st=Bu`. -/
def fractionDenominatorScaleResidue (A B t u : ℚ) : ℚ :=
  u - 1 + (B - A) * t ^ 2 / B

/-- Exact normalized inverse law on the target-scale-versus-denominator wall. -/
theorem fractionPredecessor_eq_denominatorScale_normalForm
    (A B t s u : ℚ) (B_ne : B ≠ 0) (target_scale_eq : s * t = B * u) :
    fractionPredecessor A B t s =
      (B * u - A) / fractionDenominatorScaleResidue A B t u := by
  rw [fractionPredecessor, fractionDenominatorScaleResidue, target_scale_eq]
  field_simp
  ring

/-- Once the common `B` factor is removed, the complete denominator-scale-wall cancellation is
the valuation of `fractionDenominatorScaleResidue`. -/
theorem fractionPredecessor_hasValue_of_denominatorScale_residue
    {prime : Nat} [Fact prime.Prime]
    (A B t s u : ℚ) (BValue residueValue : ℤ)
    (A_unit : IsUnit prime A)
    (B_shell : HasValue prime B BValue) (B_positive : 0 < BValue)
    (u_unit : IsUnit prime u) (target_scale_eq : s * t = B * u)
    (residue_shell :
      HasValue prime (fractionDenominatorScaleResidue A B t u) residueValue) :
    HasValue prime (fractionPredecessor A B t s) (-residueValue) := by
  have B_u_shell : HasValue prime (B * u) BValue := by
    simpa using mul_hasValue B_shell u_unit
  have B_u_positive : IsPositive prime (B * u) :=
    ⟨B_u_shell.1, B_u_shell.2.symm ▸ B_positive⟩
  have numerator_unit : IsUnit prime (B * u - A) := by
    have A_sub_target_unit := unit_sub_positive A_unit B_u_positive
    rw [show B * u - A = -(A - B * u) by ring]
    exact neg_hasValue A_sub_target_unit
  rw [fractionPredecessor_eq_denominatorScale_normalForm
    A B t s u B_shell.1 target_scale_eq]
  simpa using div_hasValue numerator_unit residue_shell

/-- On `vₚ(st)=vₚ(B)`, writing `st=Bu` exposes the sole first residue `u-1`. -/
theorem fractionPredecessor_hasValue_of_denominator_scale_wall
    {prime : Nat} [Fact prime.Prime]
    (A B t s u : ℚ) (BValue tValue residueValue : ℤ)
    (A_unit : IsUnit prime A)
    (B_shell : HasValue prime B BValue) (B_positive : 0 < BValue)
    (t_shell : HasValue prime t tValue)
    (u_unit : IsUnit prime u) (target_scale_eq : s * t = B * u)
    (residue_shell : HasValue prime (u - 1) residueValue)
    (secondary_ne : BValue + residueValue ≠ 2 * tValue) :
    HasValue prime (fractionPredecessor A B t s)
      (BValue - min (BValue + residueValue) (2 * tValue)) := by
  have B_positive_shell : IsPositive prime B :=
    ⟨B_shell.1, B_shell.2.symm ▸ B_positive⟩
  have B_sub_A_unit : IsUnit prime (B - A) := by
    have A_sub_B_unit := unit_sub_positive A_unit B_positive_shell
    rw [show B - A = -(A - B) by ring]
    exact neg_hasValue A_sub_B_unit
  have B_u_shell : HasValue prime (B * u) BValue := by
    simpa using mul_hasValue B_shell u_unit
  have B_u_positive : IsPositive prime (B * u) :=
    ⟨B_u_shell.1, B_u_shell.2.symm ▸ B_positive⟩
  have target_sub_A_unit : IsUnit prime (s * t - A) := by
    have A_sub_target_unit := unit_sub_positive A_unit B_u_positive
    rw [target_scale_eq, show B * u - A = -(A - B * u) by ring]
    exact neg_hasValue A_sub_target_unit
  have numerator_shell :
      HasValue prime (B * (s * t - A)) BValue := by
    simpa using mul_hasValue B_shell target_sub_A_unit
  have B_residue_shell :
      HasValue prime (B * (u - 1)) (BValue + residueValue) :=
    mul_hasValue B_shell residue_shell
  have t_sq_shell : HasValue prime (t ^ 2) (2 * tValue) := by
    have square := mul_hasValue t_shell t_shell
    simpa [pow_two, two_mul] using square
  have square_term_shell :
      HasValue prime ((B - A) * t ^ 2) (2 * tValue) := by
    simpa using mul_hasValue B_sub_A_unit t_sq_shell
  have denominator_shell :
      HasValue prime (B * (u - 1) + (B - A) * t ^ 2)
        (min (BValue + residueValue) (2 * tValue)) :=
    add_hasValue_min_of_ne B_residue_shell square_term_shell secondary_ne
  have denominator_eq :
      s * t + (B - A) * t ^ 2 - B =
        B * (u - 1) + (B - A) * t ^ 2 := by
    rw [target_scale_eq]
    ring
  rw [fractionPredecessor, denominator_eq]
  exact div_hasValue numerator_shell denominator_shell

/-- The exact center `st=B` of the denominator-scale wall is the monomial shift `B/t²`; it
does not depend on the numerator `A`. -/
theorem fractionPredecessor_eq_of_target_scale_eq_denominator
    (A B t s : ℚ) (B_sub_A_ne : B - A ≠ 0) (t_ne : t ≠ 0)
    (target_scale_eq : s * t = B) :
    fractionPredecessor A B t s = B / t ^ 2 := by
  rw [fractionPredecessor, target_scale_eq]
  field_simp
  ring

/-- Unit residue left after dividing the critical square-versus-denominator tie by `B`. -/
def fractionCriticalResidue (A B t : ℚ) : ℚ :=
  (B - A) * t ^ 2 / B - 1

/-- The critical residue exactly carries the common denominator factor. -/
theorem fractionCriticalResidue_spec
    (A B t : ℚ) (B_ne : B ≠ 0) :
    B * fractionCriticalResidue A B t = (B - A) * t ^ 2 - B := by
  rw [fractionCriticalResidue]
  field_simp

/-- Exact normalized inverse law at the square-versus-denominator wall.  After the common `B`
is removed, all remaining cancellation is the displayed sum of two normalized residues. -/
theorem fractionPredecessor_eq_critical_normalForm
    (A B t s : ℚ) (B_ne : B ≠ 0) :
    fractionPredecessor A B t s =
      (s * t - A) / (s * t / B + fractionCriticalResidue A B t) := by
  rw [fractionPredecessor, fractionCriticalResidue]
  field_simp
  ring

/-- At `vₚ(B)=2vₚ(t)`, every nonzero critical residue has nonnegative valuation. -/
theorem fractionCriticalResidue_valuation_nonnegative
    {prime : Nat} [Fact prime.Prime]
    (A B t : ℚ) (BValue tValue : ℤ)
    (A_unit : IsUnit prime A)
    (B_shell : HasValue prime B BValue) (B_positive : 0 < BValue)
    (t_shell : HasValue prime t tValue)
    (critical : BValue = 2 * tValue)
    (residue_ne : fractionCriticalResidue A B t ≠ 0) :
    0 ≤ padicValRat prime (fractionCriticalResidue A B t) := by
  have B_positive_shell : IsPositive prime B :=
    ⟨B_shell.1, B_shell.2.symm ▸ B_positive⟩
  have B_sub_A_unit : IsUnit prime (B - A) := by
    have A_sub_B_unit := unit_sub_positive A_unit B_positive_shell
    rw [show B - A = -(A - B) by ring]
    exact neg_hasValue A_sub_B_unit
  have t_sq_shell : HasValue prime (t ^ 2) (2 * tValue) := by
    have square := mul_hasValue t_shell t_shell
    simpa [pow_two, two_mul] using square
  have quotient_unit : IsUnit prime ((B - A) * t ^ 2 / B) := by
    have numerator_shell := mul_hasValue B_sub_A_unit t_sq_shell
    have quotient_shell := div_hasValue numerator_shell B_shell
    simpa [critical] using quotient_shell
  have residue_bound := min_le_sub (prime := prime) residue_ne
  simpa [fractionCriticalResidue, quotient_unit.2, padicValRat.one] using residue_bound

/-- The exact critical-wall transition.  If `y=vₚ(st)>0` and `κ` is the valuation of the
critical residue, the only secondary wall is `y-a=κ`; away from it the predecessor has value
`-min(y-a,κ)`. -/
theorem fractionPredecessor_hasValue_of_critical_scale_wall
    {prime : Nat} [Fact prime.Prime]
    (A B t s : ℚ) (BValue tValue targetScaleValue residueValue : ℤ)
    (A_unit : IsUnit prime A)
    (B_shell : HasValue prime B BValue) (B_positive : 0 < BValue)
    (t_shell : HasValue prime t tValue)
    (critical : BValue = 2 * tValue)
    (target_scale_shell : HasValue prime (s * t) targetScaleValue)
    (target_scale_positive : 0 < targetScaleValue)
    (residue_shell :
      HasValue prime (fractionCriticalResidue A B t) residueValue)
    (secondary_ne : targetScaleValue - BValue ≠ residueValue) :
    0 ≤ residueValue ∧
      HasValue prime (fractionPredecessor A B t s)
        (-min (targetScaleValue - BValue) residueValue) := by
  have residue_nonnegative : 0 ≤ residueValue := by
    rw [← residue_shell.2]
    exact fractionCriticalResidue_valuation_nonnegative
      A B t BValue tValue A_unit B_shell B_positive t_shell critical residue_shell.1
  have target_scale_positive_shell : IsPositive prime (s * t) :=
    ⟨target_scale_shell.1, target_scale_shell.2.symm ▸ target_scale_positive⟩
  have A_sub_target_scale_unit : IsUnit prime (A - s * t) :=
    unit_sub_positive A_unit target_scale_positive_shell
  have numerator_unit : IsUnit prime (s * t - A) := by
    rw [show s * t - A = -(A - s * t) by ring]
    exact neg_hasValue A_sub_target_scale_unit
  have normalized_target_shell :
      HasValue prime (s * t / B) (targetScaleValue - BValue) :=
    div_hasValue target_scale_shell B_shell
  have normalized_denominator_shell :
      HasValue prime (s * t / B + fractionCriticalResidue A B t)
        (min (targetScaleValue - BValue) residueValue) :=
    add_hasValue_min_of_ne normalized_target_shell residue_shell secondary_ne
  refine ⟨residue_nonnegative, ?_⟩
  rw [fractionPredecessor_eq_critical_normalForm A B t s B_shell.1]
  simpa using div_hasValue numerator_unit normalized_denominator_shell

/-- The numerator and critical walls are not global obstructions once common geometric powers
are discarded. This nonresonant word uses only even scales; its exact inverse orbit crosses both
walls at the denominator prime two. -/
theorem evenScales_threeFourths_wall_fracture :
    List.Forall (fun scale : ℤ => 2 ∣ scale) [44, 2, 6, 10, 6] ∧
      (wordProduct (normalizedTransfer (3 / 4 : ℚ)) [44, 2, 6, 10, 6]) 0 0 = 0 ∧
      (∀ scale ∈ ([44, 2, 6, 10, 6] : List ℚ), (3 / 4 : ℚ) ≠ scale⁻¹) ∧
      fractionPredecessor 3 4 6 4 = 3 / 2 ∧
      fractionPredecessor 3 4 10 (3 / 2) = 16 / 37 ∧
      fractionPredecessor 3 4 6 (16 / 37) = -3 / 64 ∧
      fractionPredecessor 3 4 2 (-3 / 64) = 132 := by
  norm_num [List.forall_cons, wordProduct, normalizedTransfer_eq,
    Matrix.mul_apply, Fin.sum_univ_succ, fractionPredecessor]

/-- Exact two-adic shells certifying the critical and numerator-wall crossings in
`evenScales_threeFourths_wall_fracture`. -/
theorem evenScales_threeFourths_wall_values :
    HasValue 2 (4 : ℚ) 2 ∧
      HasValue 2 (6 : ℚ) 1 ∧
      HasValue 2 (3 / 2 : ℚ) (-1) ∧
      HasValue 2 (10 : ℚ) 1 := by
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  have two_shell : HasValue 2 (2 : ℚ) 1 := by
    simpa using (primePower_hasValue (prime := 2) 1)
  have three_unit : IsUnit 2 (3 : ℚ) :=
    intCast_isUnit_of_not_dvd (by norm_num)
  have five_unit : IsUnit 2 (5 : ℚ) :=
    intCast_isUnit_of_not_dvd (by norm_num)
  have four_shell : HasValue 2 (4 : ℚ) 2 := by
    convert (primePower_hasValue (prime := 2) 2) using 1 <;> norm_num
  have six_shell : HasValue 2 (6 : ℚ) 1 := by
    convert mul_hasValue two_shell three_unit using 1 <;> norm_num
  have three_halves_shell : HasValue 2 (3 / 2 : ℚ) (-1) := by
    simpa using div_hasValue three_unit two_shell
  have ten_shell : HasValue 2 (10 : ℚ) 1 := by
    convert mul_hasValue two_shell five_unit using 1 <;> norm_num
  exact ⟨four_shell, six_shell, three_halves_shell, ten_shell⟩

/-- Away from `vₚ(B)=2vₚ(t)`, a denominator prime gives the terminal predecessor the exact
clipped valuation `vₚ(B)-min(2vₚ(t),vₚ(B))`.  The numerator is allowed to contain every other
base prime; only its required p-adic unit hypothesis is used. -/
theorem fractionTerminalPredecessor_hasValue
    {prime : Nat} [Fact prime.Prime]
    (A B t : ℚ) (BValue tValue : ℤ)
    (A_unit : IsUnit prime A)
    (B_shell : HasValue prime B BValue) (B_positive : 0 < BValue)
    (t_shell : HasValue prime t tValue) (t_positive : 0 < tValue)
    (not_critical : BValue ≠ 2 * tValue) :
    HasValue prime (fractionTerminalPredecessor A B t)
      (BValue - min (2 * tValue) BValue) := by
  have B_positive_shell : IsPositive prime B :=
    ⟨B_shell.1, B_shell.2.symm ▸ B_positive⟩
  have t_positive_shell : IsPositive prime t :=
    ⟨t_shell.1, t_shell.2.symm ▸ t_positive⟩
  have A_sub_B_unit : IsUnit prime (A - B) :=
    unit_sub_positive A_unit B_positive_shell
  have B_sub_A_unit : IsUnit prime (B - A) := by
    rw [show B - A = -(A - B) by ring]
    exact neg_hasValue A_sub_B_unit
  have t_sub_one_unit : IsUnit prime (t - 1) :=
    positive_sub_one t_positive_shell
  have Bt_shell : HasValue prime (B * t) (BValue + tValue) :=
    mul_hasValue B_shell t_shell
  have Bt_positive : IsPositive prime (B * t) :=
    ⟨Bt_shell.1, Bt_shell.2.symm ▸ add_pos B_positive t_positive⟩
  have A_sub_Bt_unit : IsUnit prime (A - B * t) :=
    unit_sub_positive A_unit Bt_positive
  have Bt_sub_A_unit : IsUnit prime (B * t - A) := by
    rw [show B * t - A = -(A - B * t) by ring]
    exact neg_hasValue A_sub_Bt_unit
  have numerator_shell :
      HasValue prime (B * (B * t - A)) BValue := by
    simpa using mul_hasValue B_shell Bt_sub_A_unit
  have t_sq_shell : HasValue prime (t ^ 2) (2 * tValue) := by
    have square := mul_hasValue t_shell t_shell
    simpa [pow_two, two_mul] using square
  have square_term_shell :
      HasValue prime ((B - A) * t ^ 2) (2 * tValue) := by
    simpa using mul_hasValue B_sub_A_unit t_sq_shell
  have linear_term_shell :
      HasValue prime (B * (t - 1)) BValue := by
    simpa using mul_hasValue B_shell t_sub_one_unit
  have denominator_eq :
      B * t + (B - A) * t ^ 2 - B =
        (B - A) * t ^ 2 + B * (t - 1) := by
    ring
  have denominator_shell :
      HasValue prime (B * t + (B - A) * t ^ 2 - B)
        (min (2 * tValue) BValue) := by
    rw [denominator_eq]
    rcases lt_or_gt_of_ne not_critical with B_lt | square_lt
    · simpa [min_eq_right B_lt.le] using
        add_hasValue_right square_term_shell linear_term_shell B_lt
    · simpa [min_eq_left square_lt.le] using
        add_hasValue_left square_term_shell linear_term_shell square_lt
  exact div_hasValue numerator_shell denominator_shell

/-- On the critical equality `vₚ(B)=2vₚ(t)`, the affine predecessor cannot retain positive
denominator depth. Its exact nonpositive value is residue-sensitive. -/
theorem fractionTerminalPredecessor_valuation_nonpositive_of_critical
    {prime : Nat} [Fact prime.Prime]
    (A B t : ℚ) (BValue tValue : ℤ)
    (A_unit : IsUnit prime A)
    (B_shell : HasValue prime B BValue) (B_positive : 0 < BValue)
    (t_shell : HasValue prime t tValue) (t_positive : 0 < tValue)
    (critical : BValue = 2 * tValue)
    (denominator_ne : B * t + (B - A) * t ^ 2 - B ≠ 0) :
    padicValRat prime (fractionTerminalPredecessor A B t) ≤ 0 := by
  have B_positive_shell : IsPositive prime B :=
    ⟨B_shell.1, B_shell.2.symm ▸ B_positive⟩
  have t_positive_shell : IsPositive prime t :=
    ⟨t_shell.1, t_shell.2.symm ▸ t_positive⟩
  have A_sub_B_unit : IsUnit prime (A - B) :=
    unit_sub_positive A_unit B_positive_shell
  have B_sub_A_unit : IsUnit prime (B - A) := by
    rw [show B - A = -(A - B) by ring]
    exact neg_hasValue A_sub_B_unit
  have t_sub_one_unit : IsUnit prime (t - 1) :=
    positive_sub_one t_positive_shell
  have Bt_shell : HasValue prime (B * t) (BValue + tValue) :=
    mul_hasValue B_shell t_shell
  have Bt_positive : IsPositive prime (B * t) :=
    ⟨Bt_shell.1, Bt_shell.2.symm ▸ add_pos B_positive t_positive⟩
  have A_sub_Bt_unit : IsUnit prime (A - B * t) :=
    unit_sub_positive A_unit Bt_positive
  have Bt_sub_A_unit : IsUnit prime (B * t - A) := by
    rw [show B * t - A = -(A - B * t) by ring]
    exact neg_hasValue A_sub_Bt_unit
  have numerator_shell :
      HasValue prime (B * (B * t - A)) BValue := by
    simpa using mul_hasValue B_shell Bt_sub_A_unit
  have t_sq_shell : HasValue prime (t ^ 2) (2 * tValue) := by
    have square := mul_hasValue t_shell t_shell
    simpa [pow_two, two_mul] using square
  have square_term_shell :
      HasValue prime ((B - A) * t ^ 2) BValue := by
    have shell := mul_hasValue B_sub_A_unit t_sq_shell
    simpa [critical] using shell
  have linear_term_shell :
      HasValue prime (B * (t - 1)) BValue := by
    simpa using mul_hasValue B_shell t_sub_one_unit
  have denominator_eq :
      B * t + (B - A) * t ^ 2 - B =
        (B - A) * t ^ 2 + B * (t - 1) := by
    ring
  have denominator_bound :
      BValue ≤ padicValRat prime (B * t + (B - A) * t ^ 2 - B) := by
    rw [denominator_eq]
    have bound := padicValRat.min_le_padicValRat_add
      (p := prime) (denominator_eq ▸ denominator_ne)
    simpa [square_term_shell.2, linear_term_shell.2] using bound
  rw [fractionTerminalPredecessor,
    padicValRat.div numerator_shell.1 denominator_ne, numerator_shell.2]
  omega

/-- Below the critical denominator depth, the unique terminal predecessor is a p-adic unit. -/
theorem fractionTerminalPredecessor_isUnit_of_lt
    {prime : Nat} [Fact prime.Prime]
    (A B t : ℚ) (BValue tValue : ℤ)
    (A_unit : IsUnit prime A)
    (B_shell : HasValue prime B BValue) (B_positive : 0 < BValue)
    (t_shell : HasValue prime t tValue) (t_positive : 0 < tValue)
    (below_critical : BValue < 2 * tValue) :
    IsUnit prime (fractionTerminalPredecessor A B t) := by
  have shell := fractionTerminalPredecessor_hasValue
    A B t BValue tValue A_unit B_shell B_positive t_shell t_positive
      (ne_of_lt below_critical)
  simpa [min_eq_right below_critical.le] using shell

/-- Above the critical denominator depth, one inverse terminal step subtracts exactly twice the
selected scale depth. -/
theorem fractionTerminalPredecessor_hasValue_of_gt
    {prime : Nat} [Fact prime.Prime]
    (A B t : ℚ) (BValue tValue : ℤ)
    (A_unit : IsUnit prime A)
    (B_shell : HasValue prime B BValue) (B_positive : 0 < BValue)
    (t_shell : HasValue prime t tValue) (t_positive : 0 < tValue)
    (above_critical : 2 * tValue < BValue) :
    HasValue prime (fractionTerminalPredecessor A B t)
      (BValue - 2 * tValue) := by
  have shell := fractionTerminalPredecessor_hasValue
    A B t BValue tValue A_unit B_shell B_positive t_shell t_positive
      (ne_of_gt above_critical)
  simpa [min_eq_left above_critical.le] using shell

/-- Common geometric scales make the clipped shell word-visible: the selected depth is exactly
`(wait+1)vₚ(q)`. -/
theorem fractionTerminalPredecessor_geometric_hasValue
    {prime : Nat} [Fact prime.Prime]
    (q A B : ℚ) (qValue BValue : ℤ) (wait : Nat)
    (A_unit : IsUnit prime A)
    (q_shell : HasValue prime q qValue) (q_positive : 0 < qValue)
    (B_shell : HasValue prime B BValue) (B_positive : 0 < BValue)
    (not_critical : BValue ≠ 2 * ((wait + 1) * qValue)) :
    HasValue prime
      (fractionTerminalPredecessor A B (q ^ (wait + 1)))
      (BValue - min (2 * ((wait + 1) * qValue)) BValue) := by
  have scale_shell :
      HasValue prime (q ^ (wait + 1)) ((wait + 1) * qValue) := by
    refine ⟨pow_ne_zero (wait + 1) q_shell.1, ?_⟩
    rw [padicValRat.pow, q_shell.2]
    norm_num
  have scale_positive : 0 < (wait + 1 : ℤ) * qValue := by
    exact mul_pos (by exact_mod_cast Nat.succ_pos wait) q_positive
  exact fractionTerminalPredecessor_hasValue
    A B (q ^ (wait + 1)) BValue ((wait + 1) * qValue)
      A_unit B_shell B_positive scale_shell scale_positive not_critical

/-- Pulling the physical terminal row through one cleared return selects `At`. -/
theorem fractionTerminal_vecMul_integralTransfer
    {R : Type*} [CommRing R] (A B t : R) :
    Matrix.vecMul ![A, -B] (fractionIntegralTransfer A B t) =
      ((B - A) * t) • ![A * t, -B] := by
  ext j
  fin_cases j <;>
    simp [fractionIntegralTransfer, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ]
  all_goals ring

/-- A rational ReturnSquare bridge vanishes exactly when the reversed homogeneous pullback
orbit meets `R=BS`.  No primitive normalization or affine-chart division is hidden. -/
theorem bridgeScalar_fraction_zero_iff
    (A B : ℚ) (B_ne : B ≠ 0) (scales : List ℚ) :
    bridgeScalar ![1, 1] ![-(A / B), 1]
        (wordProduct (fun t => transfer (-(A / B)) t) scales) = 0 ↔
      let state :=
        wordProduct (fractionPullback A B) scales.reverse *ᵥ ![A, 1]
      state 0 = B * state 1 := by
  let rationalTransfer : ℚ → Square (Fin 2) ℚ :=
    fun t => transfer (-(A / B)) t
  have integral_eq :
      wordProduct (fractionIntegralTransfer A B) scales =
        B ^ scales.length • wordProduct rationalTransfer scales := by
    have scaled := wordProduct_smulMatrix
      (fun _ : ℚ => B) rationalTransfer scales
    have family_eq :
        (fun t => B • rationalTransfer t) = fractionIntegralTransfer A B := by
      funext t
      exact (fractionIntegralTransfer_eq_smul A B t B_ne).symm
    rw [family_eq] at scaled
    simpa using scaled
  let state :=
    wordProduct (fractionPullback A B) scales.reverse *ᵥ ![A, 1]
  have gauge_reset : fractionGauge B *ᵥ ![A, 1] = ![A, -B] := by
    ext i
    fin_cases i <;>
      simp [fractionGauge, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have transposed_state :
      (wordProduct (fractionIntegralTransfer A B) scales)ᵀ *ᵥ ![A, -B] =
        fractionGauge B *ᵥ state := by
    rw [← gauge_reset, Matrix.mulVec_mulVec,
      fractionIntegralWord_transpose_mul_gauge, ← Matrix.mulVec_mulVec]
  have scaled_bridge :
      bridgeScalar ![1, 1] ![A, -B]
          (wordProduct (fractionIntegralTransfer A B) scales) =
        -(B ^ (scales.length + 1)) *
          bridgeScalar ![1, 1] ![-(A / B), 1]
            (wordProduct rationalTransfer scales) := by
    rw [integral_eq]
    simp [bridgeScalar, rationalTransfer, Matrix.smul_mulVec,
      dotProduct, Fin.sum_univ_succ]
    field_simp
    ring
  have dual_bridge :
      bridgeScalar ![1, 1] ![A, -B]
          (wordProduct (fractionIntegralTransfer A B) scales) =
        state 0 - B * state 1 := by
    rw [bridgeScalar, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, transposed_state]
    simp [state, fractionGauge, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
    ring
  change bridgeScalar ![1, 1] ![-(A / B), 1]
      (wordProduct rationalTransfer scales) = 0 ↔
        state 0 = B * state 1
  constructor
  · intro bridge_zero
    apply sub_eq_zero.mp
    rw [← dual_bridge, scaled_bridge, bridge_zero, mul_zero]
  · intro incidence
    have dual_zero :
        bridgeScalar ![1, 1] ![A, -B]
            (wordProduct (fractionIntegralTransfer A B) scales) = 0 := by
      rw [dual_bridge, sub_eq_zero.mpr incidence]
    rw [scaled_bridge] at dual_zero
    exact (mul_eq_zero.mp dual_zero).resolve_left
      (neg_ne_zero.mpr (pow_ne_zero (scales.length + 1) B_ne))

/-- Reversed dual state for the actual one-base ReturnSquare wait alphabet. -/
def fractionWaitState (q A B : ℚ) (waits : List Nat) : Fin 2 → ℚ :=
  wordProduct
      (fun wait => fractionPullback A B (q ^ (wait + 1))) waits.reverse *ᵥ
    ![A, 1]

/-- The geometric ReturnSquare bridge at `d=A/B` is exactly one target-line incidence in the
reversed two-coordinate pullback orbit. -/
theorem positiveBridge_fraction_zero_iff
    (q A B : ℚ) (B_ne : B ≠ 0) (waits : List Nat) :
    positiveBridge q (-(A / B)) waits = 0 ↔
      fractionWaitState q A B waits 0 = B * fractionWaitState q A B waits 1 := by
  let scale : Nat → ℚ := fun wait => q ^ (wait + 1)
  have transfer_word :
      wordProduct (fun t => transfer (-(A / B)) t) (waits.map scale) =
        wordProduct (positiveTransfer q (-(A / B))) waits := by
    rw [← wordProduct_comp]
    rfl
  have pullback_word :
      wordProduct (fractionPullback A B) (waits.map scale).reverse =
        wordProduct
          (fun wait => fractionPullback A B (scale wait)) waits.reverse := by
    rw [← List.map_reverse, ← wordProduct_comp]
    rfl
  simpa only [positiveBridge, fractionWaitState, scale, transfer_word,
    pullback_word] using
    bridgeScalar_fraction_zero_iff A B B_ne (waits.map scale)

end MatrixMortality.ReturnSquare
