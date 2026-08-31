import MatrixMortality.CubicReturn

/-!
# Non-pure cubic endpoint witnesses

One irreducible non-pure cubic return family aligns the actual singular image and kernel through
a selected unit return. A second family keeps every word over two selected waits away from the
kernel, while seven strictly unselected positive waits reach it exactly. Its complete return is
one linear projection of an integral cubic-recurrence state. Two nontriangular ternary words
already cancel to upper-triangular macro returns. A four-ray cycle pumps concatenation-prime
upper-triangular words beyond every length bound, isolating the global continuant language as the
remaining cubic obstruction.
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
  /-- Scalar defect at the first index of the recurrence window. -/
  first : ℤ
  /-- Scalar defect at the second index of the recurrence window. -/
  second : ℤ
  /-- Scalar defect at the third index of the recurrence window. -/
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

/-- The complete false-wait return reconstructed from one integral defect window. -/
def falseWaitReturnOfState (state : CubicDefectState) : Square (Fin 2) ℚ :=
  !![(-63 : ℚ) * state.first + 24 * state.second,
      24 * state.first - 21 * state.second - 79 * state.third;
    (-90 : ℚ) * state.first, -30 * state.second - 90 * state.third]

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

private theorem falseWaitReturnOfState_recurrence (state : CubicDefectState) :
    falseWaitReturnOfState state - falseWaitReturnOfState state.next.next =
      falseWaitReturnOfState state.next.next.next := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [falseWaitReturnOfState, CubicDefectState.next] <;> ring

private theorem falseWaitReturn_window (wait : Nat) :
    falseWaitReturn wait = falseWaitReturnOfState (cubicDefectState wait) ∧
      falseWaitReturn (wait + 1) =
        falseWaitReturnOfState (cubicDefectState wait).next ∧
      falseWaitReturn (wait + 2) =
        falseWaitReturnOfState (cubicDefectState wait).next.next := by
  induction wait with
  | zero =>
      constructor
      · ext i j
        fin_cases i <;> fin_cases j <;>
          norm_num [falseWaitReturn, ReturnFamily.returnMatrix, ambient, input,
            falseWaitOutput, falseWaitReturnOfState, cubicDefectState,
            CubicDefectState.next, Matrix.mul_apply, Fin.sum_univ_succ]
      constructor <;>
        ext i j <;>
        fin_cases i <;> fin_cases j <;>
          norm_num [falseWaitReturn, ReturnFamily.returnMatrix, ambient, input,
            falseWaitOutput, falseWaitReturnOfState, cubicDefectState,
            CubicDefectState.next, Matrix.mul_apply, Fin.sum_univ_succ, pow_succ]
  | succ wait induction =>
      rcases induction with ⟨first, second, third⟩
      rw [cubicDefectState_succ]
      refine ⟨second, third, ?_⟩
      rw [show wait + 1 + 2 = wait + 3 by omega]
      change
        ReturnFamily.returnMatrix ambient input falseWaitOutput (wait + 3) =
          falseWaitReturnOfState (cubicDefectState wait).next.next.next
      rw [return_recurrence falseWaitOutput wait]
      change
        falseWaitReturn wait - falseWaitReturn (wait + 2) =
          falseWaitReturnOfState (cubicDefectState wait).next.next.next
      rw [first, third, falseWaitReturnOfState_recurrence]

/-- Every entry of the physical false-wait return is controlled by the same integral defect
window. -/
theorem falseWaitReturn_eq_state (wait : Nat) :
    falseWaitReturn wait = falseWaitReturnOfState (cubicDefectState wait) :=
  (falseWaitReturn_window wait).1

/-- The determinant is the quadratic companion of the cubic defect state. -/
theorem falseWaitReturn_det (wait : Nat) :
    let state := cubicDefectState wait
    (falseWaitReturn wait).det =
      720 * (3 * (state.first : ℚ) ^ 2 -
        2 * state.first * state.third - state.second ^ 2 -
        3 * state.second * state.third) := by
  dsimp
  rw [falseWaitReturn_eq_state, Matrix.det_fin_two]
  simp [falseWaitReturnOfState]
  ring

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

/-- Three individually nontriangular returns can cancel their lower-left defects exactly. -/
theorem nontriangular_triple_fifteen_eight_twentySix :
    falseWaitReturn 15 1 0 ≠ 0 ∧ falseWaitReturn 8 1 0 ≠ 0 ∧
      falseWaitReturn 26 1 0 ≠ 0 ∧
      (falseWaitReturn 15 * falseWaitReturn 8) 1 0 ≠ 0 ∧
      (falseWaitReturn 8 * falseWaitReturn 26) 1 0 ≠ 0 ∧
      falseWaitReturn 15 * falseWaitReturn 8 * falseWaitReturn 26 =
        !![9331200, 71139600; 0, 85665600] := by
  norm_num [falseWaitReturn_eq_state, falseWaitReturnOfState, cubicDefectState,
    CubicDefectState.next, Matrix.mul_apply, Fin.sum_univ_succ]

/-- A second three-letter cancellation uses a different outer defect and recurrence index. -/
theorem nontriangular_triple_twelve_eight_thirtyThree :
    falseWaitReturn 12 1 0 ≠ 0 ∧ falseWaitReturn 8 1 0 ≠ 0 ∧
      falseWaitReturn 33 1 0 ≠ 0 ∧
      (falseWaitReturn 12 * falseWaitReturn 8) 1 0 ≠ 0 ∧
      (falseWaitReturn 8 * falseWaitReturn 33) 1 0 ≠ 0 ∧
      falseWaitReturn 12 * falseWaitReturn 8 * falseWaitReturn 33 =
        !![-32348160, -70752420; 0, -76663800] := by
  norm_num [falseWaitReturn_eq_state, falseWaitReturnOfState, cubicDefectState,
    CubicDefectState.next, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Terminal upper-flag ray for the pumped continuant family. -/
def continuantTerminalRay : Fin 2 → ℚ := ![1, 0]

/-- First finite ray of the internal continuant cycle. -/
def continuantRayZero : Fin 2 → ℚ := ![31, -30]

/-- Second finite ray of the internal continuant cycle. -/
def continuantRayOne : Fin 2 → ℚ := ![-31, 12]

/-- Third finite ray of the internal continuant cycle. -/
def continuantRayTwo : Fin 2 → ℚ := ![-29, -30]

/-- Fourth finite ray of the internal continuant cycle. -/
def continuantRayThree : Fin 2 → ℚ := ![1, -18]

/-- Four waits traversing the finite projective continuant cycle. -/
def continuantCycleWord : List Nat := [7, 8, 21, 15]

/-- Repeated internal cycles followed by the three-wait entry path. -/
def continuantTail : Nat → List Nat
  | 0 => [7, 8, 2]
  | cycles + 1 => continuantCycleWord ++ continuantTail cycles

/-- The two-wait exit, an arbitrary number of internal cycles, and the entry path. -/
def continuantPumpWord (cycles : Nat) : List Nat :=
  [19, 15] ++ continuantTail cycles

/-- Exact entry, cycle, and exit actions for the four finite continuant rays. -/
theorem continuant_ray_steps :
    falseWaitReturn 2 *ᵥ continuantTerminalRay = 3 • continuantRayTwo ∧
      falseWaitReturn 8 *ᵥ continuantRayTwo = 90 • continuantRayThree ∧
      falseWaitReturn 7 *ᵥ continuantRayThree = -12 • continuantRayZero ∧
      falseWaitReturn 15 *ᵥ continuantRayZero = 120 • continuantRayOne ∧
      falseWaitReturn 21 *ᵥ continuantRayOne = 1458 • continuantRayTwo ∧
      falseWaitReturn 19 *ᵥ continuantRayOne = -6648 • continuantTerminalRay := by
  have stepTwo : falseWaitReturn 2 *ᵥ continuantTerminalRay = 3 • continuantRayTwo := by
    ext i
    fin_cases i <;>
      norm_num [falseWaitReturn_eq_state, falseWaitReturnOfState, cubicDefectState,
        CubicDefectState.next, continuantTerminalRay, continuantRayTwo, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ]
  have stepEight : falseWaitReturn 8 *ᵥ continuantRayTwo = 90 • continuantRayThree := by
    ext i
    fin_cases i <;>
      norm_num [falseWaitReturn_eq_state, falseWaitReturnOfState, cubicDefectState,
        CubicDefectState.next, continuantRayTwo, continuantRayThree, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ]
  have stepSeven : falseWaitReturn 7 *ᵥ continuantRayThree = -12 • continuantRayZero := by
    ext i
    fin_cases i <;>
      norm_num [falseWaitReturn_eq_state, falseWaitReturnOfState, cubicDefectState,
        CubicDefectState.next, continuantRayZero, continuantRayThree, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ]
  have stepFifteen : falseWaitReturn 15 *ᵥ continuantRayZero = 120 • continuantRayOne := by
    ext i
    fin_cases i <;>
      norm_num [falseWaitReturn_eq_state, falseWaitReturnOfState, cubicDefectState,
        CubicDefectState.next, continuantRayZero, continuantRayOne, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ]
  have stepTwentyOne : falseWaitReturn 21 *ᵥ continuantRayOne = 1458 • continuantRayTwo := by
    ext i
    fin_cases i <;>
      norm_num [falseWaitReturn_eq_state, falseWaitReturnOfState, cubicDefectState,
        CubicDefectState.next, continuantRayOne, continuantRayTwo, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ]
  have stepNineteen :
      falseWaitReturn 19 *ᵥ continuantRayOne = -6648 • continuantTerminalRay := by
    ext i
    fin_cases i <;>
      norm_num [falseWaitReturn_eq_state, falseWaitReturnOfState, cubicDefectState,
        CubicDefectState.next, continuantTerminalRay, continuantRayOne, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ]
  exact ⟨stepTwo, stepEight, stepSeven, stepFifteen, stepTwentyOne, stepNineteen⟩

/-- One cycle fixes its entry ray projectively with the displayed nonzero multiplier. -/
theorem continuantCycleWord_mulVec :
    wordProduct falseWaitReturn continuantCycleWord *ᵥ continuantRayZero =
      -188956800 • continuantRayZero := by
  ext i
  fin_cases i <;>
    norm_num [continuantCycleWord, wordProduct_cons, wordProduct_nil,
      falseWaitReturn_eq_state, falseWaitReturnOfState, cubicDefectState,
      CubicDefectState.next, continuantRayZero, Matrix.mul_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]

/-- Every pumped tail enters the same finite ray. -/
theorem continuantTail_mulVec (cycles : Nat) :
    wordProduct falseWaitReturn (continuantTail cycles) *ᵥ continuantTerminalRay =
      ((-188956800 : ℚ) ^ cycles * -3240) • continuantRayZero := by
  induction cycles with
  | zero =>
      ext i
      fin_cases i <;>
        norm_num [continuantTail, wordProduct_cons, wordProduct_nil,
          falseWaitReturn_eq_state, falseWaitReturnOfState, cubicDefectState,
          CubicDefectState.next, continuantTerminalRay, continuantRayZero,
          Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  | succ cycles induction =>
      rw [continuantTail, wordProduct_append, ← Matrix.mulVec_mulVec, induction,
        Matrix.mulVec_smul, continuantCycleWord_mulVec]
      ext i
      fin_cases i <;> simp [continuantRayZero, pow_succ] <;> ring

private theorem terminalRay_mulVec_one (matrix : Square (Fin 2) ℚ) :
    (matrix *ᵥ continuantTerminalRay) 1 = matrix 1 0 := by
  simp [Matrix.mulVec, dotProduct, continuantTerminalRay, Fin.sum_univ_succ]

/-- The three suffixes introduced by one more cycle land on the other three finite rays. -/
theorem continuantTail_prefix_actions (cycles : Nat) :
    wordProduct falseWaitReturn (15 :: continuantTail cycles) *ᵥ continuantTerminalRay =
        (((-188956800 : ℚ) ^ cycles * -3240) * 120) • continuantRayOne ∧
      wordProduct falseWaitReturn (21 :: 15 :: continuantTail cycles) *ᵥ
          continuantTerminalRay =
        (((-188956800 : ℚ) ^ cycles * -3240) * 120 * 1458) • continuantRayTwo ∧
      wordProduct falseWaitReturn (8 :: 21 :: 15 :: continuantTail cycles) *ᵥ
          continuantTerminalRay =
        (((-188956800 : ℚ) ^ cycles * -3240) * 120 * 1458 * 90) •
          continuantRayThree := by
  rcases continuant_ray_steps with ⟨_, stepEight, _, stepFifteen, stepTwentyOne, _⟩
  have tail := continuantTail_mulVec cycles
  have fifteen :
      wordProduct falseWaitReturn (15 :: continuantTail cycles) *ᵥ continuantTerminalRay =
        (((-188956800 : ℚ) ^ cycles * -3240) * 120) • continuantRayOne := by
    simp only [wordProduct_cons, ← Matrix.mulVec_mulVec]
    rw [tail]
    simp only [Matrix.mulVec_smul]
    rw [stepFifteen]
    ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have twentyOne :
      wordProduct falseWaitReturn (21 :: 15 :: continuantTail cycles) *ᵥ
          continuantTerminalRay =
        (((-188956800 : ℚ) ^ cycles * -3240) * 120 * 1458) • continuantRayTwo := by
    simp only [wordProduct_cons, ← Matrix.mulVec_mulVec]
    rw [tail]
    simp only [Matrix.mulVec_smul]
    rw [stepFifteen]
    simp only [Matrix.mulVec_smul]
    rw [stepTwentyOne]
    ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have eight :
      wordProduct falseWaitReturn (8 :: 21 :: 15 :: continuantTail cycles) *ᵥ
          continuantTerminalRay =
        (((-188956800 : ℚ) ^ cycles * -3240) * 120 * 1458 * 90) •
          continuantRayThree := by
    simp only [wordProduct_cons, ← Matrix.mulVec_mulVec]
    rw [tail]
    simp only [Matrix.mulVec_smul]
    rw [stepFifteen]
    simp only [Matrix.mulVec_smul]
    rw [stepTwentyOne]
    simp only [Matrix.mulVec_smul]
    rw [stepEight]
    ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  exact ⟨fifteen, twentyOne, eight⟩

private theorem lowerLeft_ne_zero_of_terminal_action
    {word : List Nat} {scalar : ℚ} {ray : Fin 2 → ℚ}
    (action : wordProduct falseWaitReturn word *ᵥ continuantTerminalRay = scalar • ray)
    (scalar_ne_zero : scalar ≠ 0) (ray_lower_ne_zero : ray 1 ≠ 0) :
    (wordProduct falseWaitReturn word) 1 0 ≠ 0 := by
  intro lowerLeft
  have lower := congrFun action 1
  rw [terminalRay_mulVec_one, lowerLeft] at lower
  simp only [Pi.smul_apply, smul_eq_mul] at lower
  exact (mul_ne_zero scalar_ne_zero ray_lower_ne_zero) lower.symm

private theorem continuantTail_weight_ne_zero (cycles : Nat) :
    ((-188956800 : ℚ) ^ cycles * -3240) ≠ 0 := by
  exact mul_ne_zero (pow_ne_zero cycles (by norm_num)) (by norm_num)

/-- Every nonempty suffix of a pumped tail remains on a finite ray, hence is nontriangular. -/
theorem continuantTail_nonemptySuffix_lowerLeft (cycles : Nat) {suffix : List Nat}
    (membership : suffix ∈ (continuantTail cycles).tails)
    (nonempty : suffix ≠ []) :
    (wordProduct falseWaitReturn suffix) 1 0 ≠ 0 := by
  induction cycles with
  | zero =>
      simp [continuantTail] at membership
      rcases membership with rfl | rfl | rfl | rfl
      · norm_num [wordProduct_cons, wordProduct_nil, falseWaitReturn_eq_state,
          falseWaitReturnOfState, cubicDefectState, CubicDefectState.next,
          Matrix.mul_apply, Fin.sum_univ_succ]
      · norm_num [wordProduct_cons, wordProduct_nil, falseWaitReturn_eq_state,
          falseWaitReturnOfState, cubicDefectState, CubicDefectState.next,
          Matrix.mul_apply, Fin.sum_univ_succ]
      · norm_num [wordProduct_cons, wordProduct_nil, falseWaitReturn_eq_state,
          falseWaitReturnOfState, cubicDefectState, CubicDefectState.next,
          Matrix.mul_apply, Fin.sum_univ_succ]
      · exact (nonempty rfl).elim
  | succ cycles induction =>
      simp [continuantTail, continuantCycleWord] at membership
      rcases membership with rfl | rfl | rfl | rfl | membership
      · apply lowerLeft_ne_zero_of_terminal_action
          (action := by
            simpa [continuantTail, continuantCycleWord] using
              continuantTail_mulVec (cycles + 1))
          (continuantTail_weight_ne_zero (cycles + 1))
        norm_num [continuantRayZero]
      · apply lowerLeft_ne_zero_of_terminal_action (continuantTail_prefix_actions cycles).2.2
          (mul_ne_zero
            (mul_ne_zero
              (mul_ne_zero (continuantTail_weight_ne_zero cycles) (by norm_num))
              (by norm_num))
            (by norm_num))
        norm_num [continuantRayThree]
      · apply lowerLeft_ne_zero_of_terminal_action (continuantTail_prefix_actions cycles).2.1
          (mul_ne_zero
            (mul_ne_zero (continuantTail_weight_ne_zero cycles) (by norm_num))
            (by norm_num))
        norm_num [continuantRayTwo]
      · apply lowerLeft_ne_zero_of_terminal_action (continuantTail_prefix_actions cycles).1
          (mul_ne_zero (continuantTail_weight_ne_zero cycles) (by norm_num))
        norm_num [continuantRayOne]
      · exact induction ((List.mem_tails suffix (continuantTail cycles)).2 membership)

/-- The pumped words are upper triangular for every cycle count. -/
theorem continuantPumpWord_lowerLeft (cycles : Nat) :
    (wordProduct falseWaitReturn (continuantPumpWord cycles)) 1 0 = 0 := by
  rcases continuant_ray_steps with ⟨_, _, _, stepFifteen, _, stepNineteen⟩
  have tail := continuantTail_mulVec cycles
  have action :
      wordProduct falseWaitReturn (continuantPumpWord cycles) *ᵥ continuantTerminalRay =
        (((-188956800 : ℚ) ^ cycles * -3240) * 120 * -6648) •
          continuantTerminalRay := by
    simp only [continuantPumpWord, wordProduct_append, wordProduct_cons, wordProduct_nil,
      Matrix.mul_one, ← Matrix.mulVec_mulVec]
    rw [tail]
    calc
      falseWaitReturn 19 *ᵥ
            (falseWaitReturn 15 *ᵥ
              (((-188956800 : ℚ) ^ cycles * -3240) • continuantRayZero)) =
          ((-188956800 : ℚ) ^ cycles * -3240) •
            (falseWaitReturn 19 *ᵥ (falseWaitReturn 15 *ᵥ continuantRayZero)) := by
        simp only [Matrix.mulVec_smul]
      _ = ((-188956800 : ℚ) ^ cycles * -3240) •
            (falseWaitReturn 19 *ᵥ (120 • continuantRayOne)) := by
        rw [stepFifteen]
      _ = (((-188956800 : ℚ) ^ cycles * -3240) * 120) •
            (falseWaitReturn 19 *ᵥ continuantRayOne) := by
        rw [Matrix.mulVec_smul]
        ext i
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      _ = (((-188956800 : ℚ) ^ cycles * -3240) * 120) •
            (-6648 • continuantTerminalRay) := by
        rw [stepNineteen]
      _ = (((-188956800 : ℚ) ^ cycles * -3240) * 120 * -6648) •
            continuantTerminalRay := by
        ext i
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
  have lower := congrFun action 1
  simpa [Matrix.mulVec, dotProduct, continuantTerminalRay, Fin.sum_univ_succ] using lower

/-- Pumped macro lengths are the unbounded progression `5+4k`. -/
theorem continuantPumpWord_length (cycles : Nat) :
    (continuantPumpWord cycles).length = 4 * cycles + 5 := by
  induction cycles with
  | zero => simp [continuantPumpWord, continuantTail]
  | succ cycles induction =>
      simp [continuantPumpWord, continuantTail, continuantCycleWord] at induction ⊢
      omega

/-- Every nonempty proper suffix of a pumped word is nontriangular. -/
theorem continuantPumpWord_properSuffix_lowerLeft (cycles : Nat) {suffix : List Nat}
    (membership : suffix ∈ (continuantPumpWord cycles).tails)
    (proper : suffix ≠ continuantPumpWord cycles)
    (nonempty : suffix ≠ []) :
    (wordProduct falseWaitReturn suffix) 1 0 ≠ 0 := by
  simp [continuantPumpWord] at membership
  rcases membership with rfl | rfl | membership
  · exact (proper rfl).elim
  · apply lowerLeft_ne_zero_of_terminal_action (continuantTail_prefix_actions cycles).1
      (mul_ne_zero (continuantTail_weight_ne_zero cycles) (by norm_num))
    norm_num [continuantRayOne]
  · exact continuantTail_nonemptySuffix_lowerLeft cycles
      ((List.mem_tails suffix (continuantTail cycles)).2 membership) nonempty

/-- No nontrivial split of a pumped word has two upper-triangular factors. -/
theorem continuantPumpWord_concat_prime (cycles : Nat) :
    (wordProduct falseWaitReturn (continuantPumpWord cycles)) 1 0 = 0 ∧
      ∀ left right : List Nat,
        continuantPumpWord cycles = left ++ right → left ≠ [] → right ≠ [] →
          ¬ ((wordProduct falseWaitReturn left) 1 0 = 0 ∧
            (wordProduct falseWaitReturn right) 1 0 = 0) := by
  refine ⟨continuantPumpWord_lowerLeft cycles, ?_⟩
  intro left right split left_nonempty right_nonempty triangular
  have membership : right ∈ (continuantPumpWord cycles).tails :=
    (List.mem_tails right (continuantPumpWord cycles)).2 ⟨left, split.symm⟩
  have proper : right ≠ continuantPumpWord cycles := by
    intro right_eq
    have lengths := congrArg List.length split
    rw [right_eq, List.length_append] at lengths
    have left_length := List.length_pos_of_ne_nil left_nonempty
    omega
  exact continuantPumpWord_properSuffix_lowerLeft cycles membership proper right_nonempty
    triangular.2

/-- Concatenation-prime upper-triangular words occur beyond every length bound. -/
theorem continuantPumpWord_unbounded_concat_prime (bound : Nat) :
    ∃ cycles,
      bound < (continuantPumpWord cycles).length ∧
        (wordProduct falseWaitReturn (continuantPumpWord cycles)) 1 0 = 0 ∧
        ∀ left right : List Nat,
          continuantPumpWord cycles = left ++ right → left ≠ [] → right ≠ [] →
            ¬ ((wordProduct falseWaitReturn left) 1 0 = 0 ∧
              (wordProduct falseWaitReturn right) 1 0 = 0) := by
  refine ⟨bound, ?_, continuantPumpWord_concat_prime bound⟩
  rw [continuantPumpWord_length]
  omega

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
