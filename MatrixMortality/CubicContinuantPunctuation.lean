import MatrixMortality.CubicReturnNonPure
import MatrixMortality.TerminalTile

/-!
# Sole-singular punctuation in the fixed cubic continuant family

An integral determinant coefficient follows a positive recurrence, so wait zero is the unique
singular return. Relabelling positive waits then reduces every arbitrary mortality witness to
one scalar bridge between two copies of that rank-one separator.
-/

namespace MatrixMortality.CubicReturn.NonPure

/-- Integral coefficient left after removing the constant factor from a false-wait determinant. -/
def falseWaitDeterminantCoefficient (state : CubicDefectState) : ℤ :=
  3 * state.first ^ 2 - 2 * state.first * state.third - state.second ^ 2 -
    3 * state.second * state.third

/-- Advancing three recurrence steps adds the current and once-advanced determinant coefficients. -/
theorem falseWaitDeterminantCoefficient_next_three (state : CubicDefectState) :
    falseWaitDeterminantCoefficient state.next.next.next =
      falseWaitDeterminantCoefficient state.next +
        falseWaitDeterminantCoefficient state := by
  simp [falseWaitDeterminantCoefficient, CubicDefectState.next]
  ring

/-- Determinant coefficients along the cubic state orbit satisfy a positive lagged recurrence. -/
theorem falseWaitDeterminantCoefficient_state_recurrence (wait : ℕ) :
    falseWaitDeterminantCoefficient (cubicDefectState (wait + 3)) =
      falseWaitDeterminantCoefficient (cubicDefectState (wait + 1)) +
        falseWaitDeterminantCoefficient (cubicDefectState wait) := by
  simpa [cubicDefectState, CubicDefectState.next] using
    falseWaitDeterminantCoefficient_next_three (cubicDefectState wait)

/-- Every strictly positive wait has a strictly positive integral determinant coefficient. -/
theorem falseWaitDeterminantCoefficient_state_positive {wait : ℕ}
    (positive : 0 < wait) :
    0 < falseWaitDeterminantCoefficient (cubicDefectState wait) := by
  induction wait using Nat.strong_induction_on with
  | h wait induction =>
      rcases wait with _ | _ | _ | wait
      · omega
      · norm_num [falseWaitDeterminantCoefficient, cubicDefectState,
          CubicDefectState.next]
      · norm_num [falseWaitDeterminantCoefficient, cubicDefectState,
          CubicDefectState.next]
      · rw [show wait + 3 = wait + 3 by rfl,
          falseWaitDeterminantCoefficient_state_recurrence]
        by_cases wait_zero : wait = 0
        · subst wait
          norm_num [falseWaitDeterminantCoefficient, cubicDefectState,
            CubicDefectState.next]
        · have current :
              0 < falseWaitDeterminantCoefficient (cubicDefectState wait) :=
            induction wait (by omega) (by omega)
          have next :
              0 < falseWaitDeterminantCoefficient (cubicDefectState (wait + 1)) :=
            induction (wait + 1) (by omega) (by omega)
          omega

/-- Every strictly positive false-wait return has nonzero determinant. -/
theorem falseWaitReturn_positive_det_ne_zero {wait : ℕ} (positive : 0 < wait) :
    (falseWaitReturn wait).det ≠ 0 := by
  have coefficient_positive :=
    falseWaitDeterminantCoefficient_state_positive positive
  rw [falseWaitReturn_det]
  have coefficient_ne_zero :
      (falseWaitDeterminantCoefficient (cubicDefectState wait) : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt coefficient_positive)
  simpa [falseWaitDeterminantCoefficient] using
    mul_ne_zero (by norm_num : (720 : ℚ) ≠ 0) coefficient_ne_zero

/-- Every strictly positive false-wait return is a unit. -/
theorem falseWaitReturn_positive_isUnit {wait : ℕ} (positive : 0 < wait) :
    IsUnit (falseWaitReturn wait) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_iff_ne_zero.mpr (falseWaitReturn_positive_det_ne_zero positive)

/-- Wait zero is the unique nonunit in the complete false-wait return family. -/
theorem falseWaitReturn_isUnit_iff_positive (wait : ℕ) :
    IsUnit (falseWaitReturn wait) ↔ 0 < wait := by
  constructor
  · intro unit
    cases wait with
    | zero =>
        rw [Matrix.isUnit_iff_isUnit_det] at unit
        norm_num [falseWaitReturn_eq_state, falseWaitReturnOfState, cubicDefectState,
          CubicDefectState.next, Matrix.det_fin_two] at unit
    | succ wait => omega
  · exact falseWaitReturn_positive_isUnit

/-- Column of the rank-one wait-zero separator. -/
def falseWaitSeparatorColumn : Fin 2 → ℚ := ![-79, -90]

/-- Row of the rank-one wait-zero separator. -/
def falseWaitSeparatorRow : Fin 2 → ℚ := ![0, 1]

/-- Positive waits relabelled by subtraction of one. -/
def positiveFalseWaitReturn (wait : ℕ) : Square (Fin 2) ℚ :=
  falseWaitReturn (wait + 1)

/-- Every relabelled positive return is a unit. -/
theorem positiveFalseWaitReturn_isUnit (wait : ℕ) :
    IsUnit (positiveFalseWaitReturn wait) :=
  falseWaitReturn_positive_isUnit (by omega)

/-- Every word containing only positive waits is a unit. -/
theorem positiveFalseWaitReturn_wordProduct_isUnit (waits : List ℕ) :
    IsUnit (wordProduct positiveFalseWaitReturn waits) := by
  induction waits with
  | nil => exact isUnit_one
  | cons wait waits induction =>
      rw [wordProduct_cons]
      exact (positiveFalseWaitReturn_isUnit wait).mul induction

/-- Any raw word whose waits are all positive has an invertible product. -/
theorem falseWaitReturn_wordProduct_isUnit_of_positive (waits : List ℕ)
    (positive : ∀ wait ∈ waits, 0 < wait) :
    IsUnit (wordProduct falseWaitReturn waits) := by
  induction waits with
  | nil => exact isUnit_one
  | cons wait waits induction =>
      have head_positive := positive wait (by simp)
      have tail_positive : ∀ tail ∈ waits, 0 < tail := by
        intro tail membership
        exact positive tail (by simp [membership])
      rw [wordProduct_cons]
      exact (falseWaitReturn_positive_isUnit head_positive).mul (induction tail_positive)

/-- Scalar incidence of one word of positive waits between two wait-zero separators. -/
def falseWaitPositiveBridge (waits : List ℕ) : ℚ :=
  bridgeScalar falseWaitSeparatorColumn falseWaitSeparatorRow
    (wordProduct positiveFalseWaitReturn waits)

/-- Wait zero is exactly the outer product of its separator column and row. -/
theorem falseWaitReturn_zero_eq_outer :
    falseWaitReturn 0 =
      Matrix.vecMulVec falseWaitSeparatorColumn falseWaitSeparatorRow := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [falseWaitReturn_eq_state, falseWaitReturnOfState, cubicDefectState,
      falseWaitSeparatorColumn, falseWaitSeparatorRow, Matrix.vecMulVec_apply]

/-- Separating wait zero from positive waits is only a relabelling of the return family. -/
theorem separatedPositiveFalseWaitReturn_comp_natEquivOption :
    separatedGenerator (falseWaitReturn 0) positiveFalseWaitReturn ∘ natEquivOption =
      falseWaitReturn := by
  funext wait
  cases wait with
  | zero => simp [separatedGenerator]
  | succ wait => simp [separatedGenerator, positiveFalseWaitReturn]

/-- Mortality of the complete false-wait family is exactly one zero scalar bridge over positive
waits. -/
theorem falseWaitReturn_isMortal_iff_positiveBridge :
    IsMortal falseWaitReturn ↔
      ∃ waits, falseWaitPositiveBridge waits = 0 := by
  rw [← separatedPositiveFalseWaitReturn_comp_natEquivOption,
    isMortal_comp_equiv, falseWaitReturn_zero_eq_outer]
  simpa [falseWaitPositiveBridge] using
    mortal_adjoin_outer_iff positiveFalseWaitReturn
      falseWaitSeparatorColumn falseWaitSeparatorRow

/-- A second explicit seven-positive-wait bridge between the singular returns vanishes. -/
theorem falseWait_second_positive_bridge_zero :
    falseWaitReturn 0 *
        wordProduct falseWaitReturn [13, 15, 29, 11, 13, 7, 8] *
      falseWaitReturn 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [wordProduct_cons, wordProduct_nil, falseWaitReturn_eq_state,
      falseWaitReturnOfState, cubicDefectState, CubicDefectState.next,
      Matrix.mul_apply, Fin.sum_univ_succ]

end MatrixMortality.CubicReturn.NonPure
