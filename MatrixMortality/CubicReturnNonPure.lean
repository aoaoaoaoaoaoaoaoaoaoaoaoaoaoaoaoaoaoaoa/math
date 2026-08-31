import MatrixMortality.CubicReturn

/-!
# Non-pure cubic endpoint witnesses

One irreducible non-pure cubic return family aligns the actual singular image and kernel through
a selected unit return. A second family keeps every word over two selected waits away from the
kernel, while seven strictly unselected positive waits reach it exactly. This isolates the
arbitrary-wait converse as the remaining cubic obstruction.
-/

namespace MatrixMortality.CubicReturn.NonPure

open scoped Matrix

/-- Companion ambient matrix for `X³+X²−1`; it is invertible and not pure cubic. -/
def ambient : Square (Fin 3) ℚ :=
  !![-1, 1, 0;
     0, 0, 1;
     1, 0, 0]

/-- Common rank-two input interface for the two non-pure witnesses. -/
def input : Matrix (Fin 3) (Fin 2) ℚ :=
  !![0, -2;
     3, 0;
     0, 3]

/-- Output twist whose selected wait one joins the actual singular endpoints. -/
def terminalOutput : Matrix (Fin 2) (Fin 3) ℚ :=
  !![-258, 0, -235;
     -54, 0, -117]

/-- Output twist whose selected waits avoid the kernel but whose unselected waits do not. -/
def falseWaitOutput : Matrix (Fin 2) (Fin 3) ℚ :=
  !![8, 0, -21;
     0, 0, -30]

/-- Explicit left inverse of the common input interface. -/
def inputLeftInverse : Matrix (Fin 2) (Fin 3) ℚ :=
  !![0, 1 / 3, 0;
     -1 / 2, 0, 0]

/-- Explicit right inverse of the terminal-aligned output. -/
def terminalOutputRightInverse : Matrix (Fin 3) (Fin 2) ℚ :=
  !![-117 / 17496, 235 / 17496;
     0, 0;
     54 / 17496, -258 / 17496]

/-- Explicit right inverse of the false-wait output. -/
def falseWaitOutputRightInverse : Matrix (Fin 3) (Fin 2) ℚ :=
  !![1 / 8, -7 / 80;
     0, 0;
     0, -1 / 30]

/-- Return family for the endpoint-aligned twist. -/
def terminalReturn (wait : Nat) : Square (Fin 2) ℚ :=
  ReturnFamily.returnMatrix ambient input terminalOutput wait

/-- Return family exposing the false-wait obstruction. -/
def falseWaitReturn (wait : Nat) : Square (Fin 2) ℚ :=
  ReturnFamily.returnMatrix ambient input falseWaitOutput wait

/-- Three consecutive values of the scalar defect in the normalized return recurrence. -/
structure CubicDefectState where
  first : ℤ
  second : ℤ
  third : ℤ

/-- Shift one scalar-defect window through `u_(n+3)=u_n-u_(n+2)`. -/
def CubicDefectState.next (state : CubicDefectState) : CubicDefectState :=
  ⟨state.second, state.third, state.first - state.third⟩

/-- Integral scalar-defect windows for the non-pure cubic return family. -/
def cubicDefectState : Nat → CubicDefectState
  | 0 => ⟨0, 0, 1⟩
  | wait + 1 => (cubicDefectState wait).next

/-- Lower-left defect of the normalized non-pure cubic return. -/
def cubicDefect (wait : Nat) : ℤ :=
  (cubicDefectState wait).first

/-- Cubic norm preserved by the scalar-defect recurrence. -/
def cubicDefectNorm (state : CubicDefectState) : ℤ :=
  state.first ^ 3 - state.first ^ 2 * state.third -
      state.first * state.second ^ 2 -
    3 * state.first * state.second * state.third + state.second ^ 3 +
      state.second ^ 2 * state.third +
    2 * state.second * state.third ^ 2 + state.third ^ 3

/-- Rational lower-left defect extracted directly from the physical false-wait family. -/
def falseWaitDefect (wait : Nat) : ℚ :=
  -(falseWaitReturn wait 1 0) / 90

/-- The ambient companion obeys its non-pure cubic polynomial. -/
theorem ambient_recurrence : ambient ^ 3 + ambient ^ 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ambient, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_succ, pow_succ]

/-- The non-pure ambient has determinant one. -/
theorem ambient_det : ambient.det = 1 := by
  norm_num [ambient, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail]

/-- The non-pure ambient is invertible. -/
theorem ambient_isUnit : IsUnit ambient := by
  rw [Matrix.isUnit_iff_isUnit_det, ambient_det]
  exact isUnit_one

/-- No scalar turns the third ambient power into the identity. -/
theorem ambient_not_pureCubic (scalar : ℚ) :
    ambient ^ 3 ≠ scalar • 1 := by
  intro pure
  have offDiagonal := congrFun (congrFun pure 0) 1
  norm_num [ambient, Matrix.mul_apply, Matrix.one_apply, Matrix.smul_apply,
    Fin.sum_univ_succ, pow_succ] at offDiagonal

/-- The displayed matrix is a left inverse of the common input. -/
theorem inputLeftInverse_mul_input : inputLeftInverse * input = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [inputLeftInverse, input, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_succ]

/-- The endpoint-aligned output has the displayed right inverse. -/
theorem terminalOutput_mul_rightInverse :
    terminalOutput * terminalOutputRightInverse = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [terminalOutput, terminalOutputRightInverse, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_succ]

/-- The false-wait output has the displayed right inverse. -/
theorem falseWaitOutput_mul_rightInverse :
    falseWaitOutput * falseWaitOutputRightInverse = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [falseWaitOutput, falseWaitOutputRightInverse, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_succ]

private theorem cut_rank_of_rightInverse
    (output : Matrix (Fin 2) (Fin 3) ℚ)
    (rightInverse : Matrix (Fin 3) (Fin 2) ℚ)
    (right_inverse : output * rightInverse = 1) :
    (input * output).rank = 2 := by
  have output_rank : output.rank = 2 := by
    apply le_antisymm
    · exact Matrix.rank_le_height output
    · have rank_bound := Matrix.rank_mul_le_left output rightInverse
      rw [right_inverse, Matrix.rank_one] at rank_bound
      norm_num at rank_bound ⊢
      exact rank_bound
  apply le_antisymm
  · exact (Matrix.rank_mul_le_left input output).trans (Matrix.rank_le_width input)
  · have output_factor : output = inputLeftInverse * (input * output) := by
      calc
        output = (1 : Square (Fin 2) ℚ) * output := by simp
        _ = (inputLeftInverse * input) * output := by rw [inputLeftInverse_mul_input]
        _ = inputLeftInverse * (input * output) := by rw [Matrix.mul_assoc]
    have lower : output.rank ≤ (input * output).rank := by
      calc
        output.rank = (inputLeftInverse * (input * output)).rank :=
          congrArg Matrix.rank output_factor
        _ ≤ (input * output).rank :=
          Matrix.rank_mul_le_right inputLeftInverse (input * output)
    rwa [output_rank] at lower

/-- The terminal-aligned physical cut has rank exactly two. -/
theorem terminalCut_rank : (input * terminalOutput).rank = 2 :=
  cut_rank_of_rightInverse terminalOutput terminalOutputRightInverse
    terminalOutput_mul_rightInverse

/-- The false-wait physical cut has rank exactly two. -/
theorem falseWaitCut_rank : (input * falseWaitOutput).rank = 2 :=
  cut_rank_of_rightInverse falseWaitOutput falseWaitOutputRightInverse
    falseWaitOutput_mul_rightInverse

/-- Every ambient power inherits the same order-three non-pure recurrence. -/
theorem ambient_pow_recurrence (wait : Nat) :
    ambient ^ (wait + 3) = ambient ^ wait - ambient ^ (wait + 2) := by
  have cubic : ambient ^ 3 = 1 - ambient ^ 2 :=
    eq_sub_of_add_eq ambient_recurrence
  calc
    ambient ^ (wait + 3) = ambient ^ wait * ambient ^ 3 := by rw [pow_add]
    _ = ambient ^ wait * (1 - ambient ^ 2) := by rw [cubic]
    _ = ambient ^ wait - ambient ^ (wait + 2) := by
      rw [Matrix.mul_sub, Matrix.mul_one, pow_add]

/-- Every return family over this ambient obeys `M_(n+3)=M_n−M_(n+2)`. -/
theorem return_recurrence
    (output : Matrix (Fin 2) (Fin 3) ℚ) (wait : Nat) :
    ReturnFamily.returnMatrix ambient input output (wait + 3) =
      ReturnFamily.returnMatrix ambient input output wait -
        ReturnFamily.returnMatrix ambient input output (wait + 2) := by
  simp only [ReturnFamily.returnMatrix]
  rw [ambient_pow_recurrence, Matrix.mul_sub, Matrix.sub_mul]

@[simp]
theorem cubicDefectState_succ (wait : Nat) :
    cubicDefectState (wait + 1) = (cubicDefectState wait).next := rfl

theorem cubicDefect_recurrence (wait : Nat) :
    cubicDefect (wait + 3) = cubicDefect wait - cubicDefect (wait + 2) := by
  simp [cubicDefect, cubicDefectState, CubicDefectState.next]

/-- The recurrence shift preserves one discriminant-`-23` cubic norm. -/
theorem cubicDefectNorm_next (state : CubicDefectState) :
    cubicDefectNorm state.next = cubicDefectNorm state := by
  simp [cubicDefectNorm, CubicDefectState.next]
  ring

/-- Every consecutive scalar-defect window has cubic norm one. -/
theorem cubicDefectNorm_state (wait : Nat) :
    cubicDefectNorm (cubicDefectState wait) = 1 := by
  induction wait with
  | zero => norm_num [cubicDefectNorm, cubicDefectState]
  | succ wait induction =>
      rw [cubicDefectState_succ, cubicDefectNorm_next, induction]

/-- The first physical false-wait defect is the integral recurrence above. -/
theorem falseWaitDefect_state (wait : Nat) :
    falseWaitDefect wait = (cubicDefectState wait).first ∧
      falseWaitDefect (wait + 1) = (cubicDefectState wait).second ∧
      falseWaitDefect (wait + 2) = (cubicDefectState wait).third := by
  induction wait with
  | zero =>
      norm_num [falseWaitDefect, falseWaitReturn, ReturnFamily.returnMatrix,
        ambient, input, falseWaitOutput, cubicDefectState, Matrix.mul_apply,
        Fin.sum_univ_succ, pow_succ]
  | succ wait induction =>
      rcases induction with ⟨first, second, third⟩
      refine ⟨?_, ?_, ?_⟩
      · simpa [cubicDefectState, CubicDefectState.next] using second
      · simpa [cubicDefectState, CubicDefectState.next, Nat.add_assoc] using third
      · have recurrence := congrFun (congrFun (return_recurrence falseWaitOutput wait) 1) 0
        change
          falseWaitReturn (wait + 3) 1 0 =
            falseWaitReturn wait 1 0 - falseWaitReturn (wait + 2) 1 0
          at recurrence
        have defectRecurrence :
            falseWaitDefect (wait + 3) =
              falseWaitDefect wait - falseWaitDefect (wait + 2) := by
          rw [falseWaitDefect, falseWaitDefect, falseWaitDefect, recurrence]
          ring
        rw [show wait + 1 + 2 = wait + 3 by omega, defectRecurrence, first, third]
        simp [cubicDefectState, CubicDefectState.next]

theorem falseWaitDefect_eq_cubicDefect (wait : Nat) :
    falseWaitDefect wait = cubicDefect wait := by
  simpa [cubicDefect] using (falseWaitDefect_state wait).1

/-- The physical lower-left entry is exactly the integral cubic defect. -/
theorem falseWaitReturn_lowerLeft (wait : Nat) :
    falseWaitReturn wait 1 0 = -90 * cubicDefect wait := by
  have defect := falseWaitDefect_eq_cubicDefect wait
  rw [falseWaitDefect] at defect
  linarith

/-- A triangular return index yields an integral point on the exceptional discriminant-`-23`
Thue curve `x³-xy²+y³=1`. -/
theorem cubicDefect_zero_forces_exceptionalThue
    {wait : Nat} (defect_zero : cubicDefect wait = 0) :
    let x := cubicDefect (wait + 1)
    let y := cubicDefect (wait + 1) + cubicDefect (wait + 2)
    x ^ 3 - x * y ^ 2 + y ^ 3 = 1 := by
  let state := cubicDefectState wait
  have norm := cubicDefectNorm_state wait
  have first_zero : state.first = 0 := by
    simpa [state, cubicDefect] using defect_zero
  have second_eq : cubicDefect (wait + 1) = state.second := by
    simp [cubicDefect, state, cubicDefectState, CubicDefectState.next]
  have third_eq : cubicDefect (wait + 2) = state.third := by
    simp [cubicDefect, state, cubicDefectState, CubicDefectState.next]
  dsimp
  rw [second_eq, third_eq]
  rw [cubicDefectNorm, first_zero] at norm
  norm_num at norm
  linear_combination norm

/-- The four observed triangular indices on the normalized recurrence. -/
theorem cubicDefect_known_zeros :
    cubicDefect 0 = 0 ∧ cubicDefect 1 = 0 ∧
      cubicDefect 5 = 0 ∧ cubicDefect 14 = 0 := by
  norm_num [cubicDefect, cubicDefectState, CubicDefectState.next]

/-- The endpoint-aligned twist has the displayed singular and selected returns. -/
theorem terminal_returns :
    terminalReturn 0 = !![0, -189; 0, -243] ∧
    terminalReturn 1 = !![-774, -46; -162, 126] ∧
    terminalReturn 5 = !![774, -143; 162, -369] := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [terminalReturn, ReturnFamily.returnMatrix, ambient, input,
        terminalOutput, Matrix.mul_apply, Fin.sum_univ_succ]
  constructor <;>
    ext i j <;>
    fin_cases i <;> fin_cases j <;>
      norm_num [terminalReturn, ReturnFamily.returnMatrix, ambient, input,
        terminalOutput, Matrix.mul_apply, Fin.sum_univ_succ, pow_succ]

/-- The actual singular image reaches the actual kernel through selected wait one. -/
theorem terminal_zero :
    terminalReturn 0 * terminalReturn 1 * terminalReturn 0 = 0 := by
  rw [terminal_returns.1, terminal_returns.2.1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

private theorem falseWaitReturn_zero :
    falseWaitReturn 0 = !![0, -79; 0, -90] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [falseWaitReturn, ReturnFamily.returnMatrix, ambient, input,
      falseWaitOutput, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem falseWaitReturn_one :
    falseWaitReturn 1 = !![24, 58; 0, 60] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [falseWaitReturn, ReturnFamily.returnMatrix, ambient, input,
      falseWaitOutput, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem falseWaitReturn_five :
    falseWaitReturn 5 = !![-24, -137; 0, -150] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [falseWaitReturn, ReturnFamily.returnMatrix, ambient, input,
      falseWaitOutput, Matrix.mul_apply, Fin.sum_univ_succ, pow_succ]

private theorem falseWaitReturn_eight :
    falseWaitReturn 8 = !![150, -148; 180, -120] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [falseWaitReturn, ReturnFamily.returnMatrix, ambient, input,
      falseWaitOutput, Matrix.mul_apply, Fin.sum_univ_succ, pow_succ]

private theorem falseWaitReturn_twelve :
    falseWaitReturn 12 = !![-324, 159; -360, 90] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [falseWaitReturn, ReturnFamily.returnMatrix, ambient, input,
      falseWaitOutput, Matrix.mul_apply, Fin.sum_univ_succ, pow_succ]

private theorem falseWaitReturn_fifteen :
    falseWaitReturn 15 = !![-420, -310; -360, -420] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [falseWaitReturn, ReturnFamily.returnMatrix, ambient, input,
      falseWaitOutput, Matrix.mul_apply, Fin.sum_univ_succ, pow_succ]

/-- Seven strictly unselected positive waits carrying the singular image to the kernel. -/
def falseWaitWord : List Nat := [12, 12, 8, 12, 12, 15, 8]

/-- Every letter of the false-wait word is positive and outside the selected alphabet `{1,5}`. -/
theorem falseWaitWord_strictly_unselected :
    ∀ wait ∈ falseWaitWord, 0 < wait ∧ wait ≠ 1 ∧ wait ≠ 5 := by
  simp [falseWaitWord]

/-- The strictly unselected word creates an exact zero between the singular returns. -/
theorem falseWait_zero :
    falseWaitReturn 0 *
      wordProduct falseWaitReturn falseWaitWord *
      falseWaitReturn 0 = 0 := by
  simp only [falseWaitWord, wordProduct_cons, wordProduct_nil, Matrix.mul_one]
  rw [falseWaitReturn_zero, falseWaitReturn_eight, falseWaitReturn_twelve,
    falseWaitReturn_fifteen]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

/-- No word over selected waits one and five sends the actual singular image `[79:90]` to the
actual singular kernel `[1:0]`. -/
theorem selected_lower_ne_zero (word : List Bool) :
    (wordProduct (fun selected => if selected then falseWaitReturn 5 else falseWaitReturn 1)
      word *ᵥ ![(79 : ℚ), 90]) 1 ≠ 0 := by
  induction word with
  | nil => norm_num [wordProduct]
  | cons selected word induction =>
      rw [wordProduct_cons, ← Matrix.mulVec_mulVec]
      let tail :=
        wordProduct
          (fun selected => if selected then falseWaitReturn 5 else falseWaitReturn 1)
          word *ᵥ ![(79 : ℚ), 90]
      have action :
          ((if selected then falseWaitReturn 5 else falseWaitReturn 1) *ᵥ tail) 1 =
            (if selected then (-150 : ℚ) else 60) * tail 1 := by
        cases selected
        · rw [falseWaitReturn_one]
          simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
        · rw [falseWaitReturn_five]
          simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      rw [action]
      exact mul_ne_zero (by cases selected <;> norm_num) induction

end MatrixMortality.CubicReturn.NonPure
