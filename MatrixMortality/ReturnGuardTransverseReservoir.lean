import Mathlib.Tactic.NormNum.IsCoprime
import MatrixMortality.ReturnGuardExamples

/-!
# A transverse reservoir invisible to the reset orbit

The checked period-three guard returns projectively to reset while its endpoint macro has a
second rational eigenline. The eigenvalue on that transverse line acquires one factor of
thirteen per period; the eigenvalue visible on the reset line remains coprime to thirteen.
Thus no path-independent potential of the projective endpoints can charge every reverse
cyclotomic packet.
-/

namespace MatrixMortality.ReturnGuard.Examples

open scoped Matrix

noncomputable section

/-- The period-three endpoint cycle has forward contents `-160, -1204, -80`; their exact
complements in `DL(3^a - 1)` are `-13244, -7040, -344344`. -/
theorem cycle_endpointReductions :
    PrimitiveEndpointReduction 3 2 (-953) 473 2240 1
        (-2720, 1) (-7924, 5) (-160) ∧
      PrimitiveEndpointReduction 3 2 (-953) 473 2240 2
        (-7924, 5) (-80, 1) (-1204) ∧
      PrimitiveEndpointReduction 3 2 (-953) 473 2240 3
        (-80, 1) (-2720, 1) (-80) ∧
      (-160 : ℤ) * (-13244) = 473 * 2240 * (3 ^ 1 - 1) ∧
      (-1204 : ℤ) * (-7040) = 473 * 2240 * (3 ^ 2 - 1) ∧
      (-80 : ℤ) * (-344344) = 473 * 2240 * (3 ^ 3 - 1) ∧
      (3 : ℤ) ^ 12 * (-160) * (-1204) * (-80) = -8190143539200 ∧
      (-1 : ℤ) ^ 3 * (-13244) * (-7040) * (-344344) = 32105863229440 := by
  constructor
  · refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    constructor <;> norm_num
  constructor
  · refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    constructor <;> norm_num
  constructor
  · refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    constructor <;> norm_num
  all_goals norm_num

private theorem cycle_schedule_follows :
    FollowsResidualSchedule cycleParameters [1, 2, 3] 1 := by
  have branch_zero : ResidualBranch cycleParameters 1 1 := by
    rw [residualBranch_iff_ready]
    simpa [cycle_residual_states.1] using cycle_state_zero_ready
  have branch_one : ResidualBranch cycleParameters 2 (5 / 17) := by
    rw [residualBranch_iff_ready, cycle_residual_states.2.1]
    exact cycle_state_one_ready
  have branch_two : ResidualBranch cycleParameters 3 (43 / 283) := by
    rw [residualBranch_iff_ready, cycle_residual_states.2.2]
    exact cycle_state_two_ready
  have step_zero : residualStep cycleParameters 1 1 = 5 / 17 := by
    norm_num [residualStep, prefixDecode, centerTransform, cycleParameters, drift]
  have step_one : residualStep cycleParameters 2 (5 / 17) = 43 / 283 := by
    norm_num [residualStep, prefixDecode, centerTransform, cycleParameters, drift]
  simp only [followsResidualSchedule_cons, followsResidualSchedule_nil]
  rw [step_zero, step_one]
  exact ⟨branch_zero, branch_one, branch_two, trivial⟩

private theorem cycle_schedule_returns :
    residualRun cycleParameters [1, 2, 3] 1 = 1 := by
  norm_num [residualRun, residualStep, prefixDecode, centerTransform,
    cycleParameters, drift]

private theorem cycle_macro_eigenlines :
    endpointProduct (3 : ℤ) 2 (-953) 473 2240 [1, 2, 3] *ᵥ
        pairVector (-2720, 1) =
      (-8190143539200 : ℤ) • pairVector (-2720, 1) ∧
    endpointProduct (3 : ℤ) 2 (-953) 473 2240 [1, 2, 3] *ᵥ
        pairVector (193981136, 5587) =
      (32105863229440 : ℤ) • pairVector (193981136, 5587) := by
  constructor <;>
    ext i <;>
    fin_cases i <;>
    norm_num [endpointProduct, endpointTransfer, pairVector, Matrix.mul_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, smul_eq_mul]

private theorem cycle_repeat_follows_and_returns (periods : Nat) :
    FollowsResidualSchedule cycleParameters
        (repeatSchedule [1, 2, 3] periods) 1 ∧
      residualRun cycleParameters (repeatSchedule [1, 2, 3] periods) 1 = 1 := by
  induction periods with
  | zero => simp
  | succ periods induction =>
      rw [repeatSchedule_succ, followsResidualSchedule_append,
        residualRun_append, induction.2]
      exact ⟨⟨induction.1, cycle_schedule_follows⟩, cycle_schedule_returns⟩

private theorem cycle_repeat_eigenline
    (vector : Fin 2 → ℤ) (eigenvalue : ℤ)
    (eigenline :
      endpointProduct (3 : ℤ) 2 (-953) 473 2240 [1, 2, 3] *ᵥ vector =
        eigenvalue • vector)
    (periods : Nat) :
    endpointProduct (3 : ℤ) 2 (-953) 473 2240
          (repeatSchedule [1, 2, 3] periods) *ᵥ vector =
      eigenvalue ^ periods • vector := by
  induction periods with
  | zero => simp
  | succ periods induction =>
      rw [repeatSchedule_succ, endpointProduct_append,
        ← Matrix.mulVec_mulVec, induction, Matrix.mulVec_smul,
        eigenline, smul_smul, pow_succ]

/-- Repeating the lawful period-three word fixes the rational reset orbit while accumulating
an arbitrary power of thirteen in a transverse eigenvalue invisible to that orbit. -/
theorem cycle_transverseReservoir (periods : Nat) :
    FollowsResidualSchedule cycleParameters
        (repeatSchedule [1, 2, 3] periods) 1 ∧
      residualRun cycleParameters (repeatSchedule [1, 2, 3] periods) 1 = 1 ∧
      endpointProduct (3 : ℤ) 2 (-953) 473 2240
            (repeatSchedule [1, 2, 3] periods) *ᵥ pairVector (-2720, 1) =
        (-8190143539200 : ℤ) ^ periods • pairVector (-2720, 1) ∧
      endpointProduct (3 : ℤ) 2 (-953) 473 2240
            (repeatSchedule [1, 2, 3] periods) *ᵥ pairVector (193981136, 5587) =
        (32105863229440 : ℤ) ^ periods • pairVector (193981136, 5587) ∧
      (32105863229440 : ℤ) ^ periods =
        (13 : ℤ) ^ periods * (2469681786880 : ℤ) ^ periods ∧
      IsCoprime ((13 : ℤ) ^ periods) ((2469681786880 : ℤ) ^ periods) ∧
      IsCoprime ((13 : ℤ) ^ periods) ((-8190143539200 : ℤ) ^ periods) := by
  obtain ⟨follows, returns⟩ := cycle_repeat_follows_and_returns periods
  refine ⟨follows, returns,
    cycle_repeat_eigenline (pairVector (-2720, 1)) (-8190143539200)
      cycle_macro_eigenlines.1 periods,
    cycle_repeat_eigenline (pairVector (193981136, 5587)) 32105863229440
      cycle_macro_eigenlines.2 periods, ?_, ?_, ?_⟩
  · rw [show (32105863229440 : ℤ) = 13 * 2469681786880 by norm_num,
      mul_pow]
  · exact (show IsCoprime (13 : ℤ) (2469681786880 : ℤ) by norm_num).pow
  · exact (show IsCoprime (13 : ℤ) (-8190143539200 : ℤ) by norm_num).pow

end

end MatrixMortality.ReturnGuard.Examples
