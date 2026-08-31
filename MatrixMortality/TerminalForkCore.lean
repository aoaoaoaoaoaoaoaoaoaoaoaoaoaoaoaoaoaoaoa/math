import MatrixMortality.TransverseSeparatedForkNoGo

/-!
# Every exact `bcbc` recognizer contains a proper binary fork core

The complete `bcbc` terminal fork imposes a representation-independent constraint. For any
three-state same-zero recognizer, the orbit of the toggled boundary column under the flat and
nested null-block products spans a nonzero proper common invariant subspace. Its dimension is
therefore one or two. Generic irreducible fork actions are impossible; an invertible escape must
carry its unbounded fork dynamics in a one- or two-state core and use the remaining coordinate
only outside that terminal orbit.
-/

namespace MatrixMortality
namespace TerminalForkCore

open scoped Matrix
open BranchingHistory BranchingRecognizer TransverseInfiniteAtlas
open TransverseSeparatedForkNoGo

/-- Select the matrix product of one flat or nested null fork block. -/
def forkTransition (generators : PairedControl → ControlMatrix) (bit : Bool) : ControlMatrix :=
  if bit then wordProduct generators nestedForkControl
  else wordProduct generators flatForkControl

/-- The toggled boundary column after an arbitrary word of null fork blocks. -/
def forkState (generators : PairedControl → ControlMatrix) (column : State)
    (bits : List Bool) : State :=
  wordProduct (forkTransition generators) bits *ᵥ (generators .toggle *ᵥ column)

/-- Linear span of the complete binary null-fork orbit. -/
def carrier (generators : PairedControl → ControlMatrix) (column : State) :
    Submodule ℚ State :=
  Submodule.span ℚ (Set.range (forkState generators column))

/-- Row transported through the fixed terminal prefix. -/
def boundaryRow (generators : PairedControl → ControlMatrix) (row : State) : State :=
  row ᵥ* wordProduct generators terminalPrefixControl

theorem wordProduct_historyControl_bcbcFork
    (generators : PairedControl → ControlMatrix) (bits : List Bool) :
    wordProduct generators (historyControl (bcbcFork bits)) =
      wordProduct (forkTransition generators) bits := by
  induction bits with
  | nil => simp [bcbcFork, historyControl, wordProduct]
  | cons bit bits induction =>
      rw [bcbcFork, historyControl_append, wordProduct_append, induction]
      cases bit <;>
        simp [forkTransition, forkBlock, flatForkControl, nestedForkControl,
          wordProduct]

theorem wordProduct_terminalForkControl
    (generators : PairedControl → ControlMatrix) (bits : List Bool) :
    wordProduct generators (terminalForkControl bits) =
      wordProduct generators terminalPrefixControl *
        wordProduct (forkTransition generators) bits * generators .toggle := by
  rw [terminalForkControl_eq, wordProduct_append, wordProduct_append,
    wordProduct_historyControl_bcbcFork]
  simp [wordProduct]

theorem terminalForkCoefficient_eq
    (generators : PairedControl → ControlMatrix) (row column : State) (bits : List Bool) :
    linearCoefficient generators row column (terminalForkControl bits) =
      boundaryRow generators row ⬝ᵥ forkState generators column bits := by
  rw [linearCoefficient, wordProduct_terminalForkControl]
  simp only [boundaryRow, forkState, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- The flat or nested fork transition preserves the binary orbit span. -/
theorem forkTransition_mulVec_mem_carrier
    (generators : PairedControl → ControlMatrix) (column : State) (bit : Bool)
    {state : State} (state_mem : state ∈ carrier generators column) :
    forkTransition generators bit *ᵥ state ∈ carrier generators column := by
  refine Submodule.span_induction
    (p := fun candidate : State => fun _ ↦
      forkTransition generators bit *ᵥ candidate ∈ carrier generators column)
    (s := Set.range (forkState generators column)) ?_ ?_ ?_ ?_
    (by simpa only [carrier] using state_mem)
  · rintro _ ⟨bits, rfl⟩
    apply Submodule.subset_span
    refine ⟨bit :: bits, ?_⟩
    simp [forkState, wordProduct_cons, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  · simp
  · intro left right _ _ left_mem right_mem
    rw [Matrix.mulVec_add]
    exact Submodule.add_mem _ left_mem right_mem
  · intro scalar candidate _ candidate_mem
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ scalar candidate_mem

/-- The toggled boundary column belongs to the fork carrier. -/
theorem toggledColumn_mem_carrier
    (generators : PairedControl → ControlMatrix) (column : State) :
    generators .toggle *ᵥ column ∈ carrier generators column := by
  apply Submodule.subset_span
  refine ⟨[], ?_⟩
  simp [forkState, wordProduct]

/-- The one-letter toggle is not a paired zero for the fixed `bcbc` source. -/
theorem toggle_paired_ne_zero :
    pairedCoefficient ℚ 3 bcbcBody [.toggle] ≠ 0 := by
  rw [pairedCoefficient_eq_sideCoefficient]
  intro source_zero
  have terminal_match :=
    (sideCoefficient_eq_zero_iff_terminal_match_rat 3 bcbcBody _).mp source_zero
  have not_terminal :
      spell (nearyUpper 3) (decodePairedWord [.toggle]) ++ nearyMarker 3 ≠
        spell (nearyLower 3 bcbcBody) (decodePairedWord [.toggle]) := by
    decide
  exact not_terminal terminal_match

/-- Same-zero recognition forces the toggled boundary column to be nonzero. -/
theorem toggledColumn_ne_zero_of_sameZero
    (generators : PairedControl → ControlMatrix) (row column : State)
    (sameZero : ∀ word,
      linearCoefficient generators row column word = 0 ↔
        pairedCoefficient ℚ 3 bcbcBody word = 0) :
    generators .toggle *ᵥ column ≠ 0 := by
  intro toggled_zero
  have target_zero : linearCoefficient generators row column [.toggle] = 0 := by
    simp [linearCoefficient, wordProduct, toggled_zero]
  exact toggle_paired_ne_zero ((sameZero [.toggle]).mp target_zero)

/-- Same-zero recognition forces the transported prefix row to be nonzero. -/
theorem boundaryRow_ne_zero_of_sameZero
    (generators : PairedControl → ControlMatrix) (row column : State)
    (sameZero : ∀ word,
      linearCoefficient generators row column word = 0 ↔
        pairedCoefficient ℚ 3 bcbcBody word = 0) :
    boundaryRow generators row ≠ 0 := by
  intro boundary_zero
  have target_zero :
      linearCoefficient generators row column terminalPrefixControl = 0 := by
    rw [linearCoefficient, Matrix.dotProduct_mulVec]
    change boundaryRow generators row ⬝ᵥ column = 0
    rw [boundary_zero]
    simp
  exact terminalPrefixControl_paired_ne_zero
    ((sameZero terminalPrefixControl).mp target_zero)

/-- Every vector in the fork carrier is annihilated by the transported terminal-prefix row. -/
theorem boundaryRow_dot_eq_zero_of_mem
    (generators : PairedControl → ControlMatrix) (row column : State)
    (sameZero : ∀ word,
      linearCoefficient generators row column word = 0 ↔
        pairedCoefficient ℚ 3 bcbcBody word = 0)
    {state : State} (state_mem : state ∈ carrier generators column) :
    boundaryRow generators row ⬝ᵥ state = 0 := by
  induction state_mem using Submodule.span_induction with
  | mem state state_generator =>
      rcases state_generator with ⟨bits, rfl⟩
      rw [← terminalForkCoefficient_eq]
      exact (sameZero (terminalForkControl bits)).mpr
        (terminalForkControl_paired_zero bits)
  | zero => simp
  | add left right _ _ left_zero right_zero =>
      rw [dotProduct_add, left_zero, right_zero, add_zero]
  | smul scalar state _ state_zero =>
      rw [dotProduct_smul, state_zero, smul_zero]

/-- Same-zero recognition makes the fork carrier nontrivial. -/
theorem carrier_ne_bot_of_sameZero
    (generators : PairedControl → ControlMatrix) (row column : State)
    (sameZero : ∀ word,
      linearCoefficient generators row column word = 0 ↔
        pairedCoefficient ℚ 3 bcbcBody word = 0) :
    carrier generators column ≠ ⊥ := by
  intro carrier_bot
  have toggled_mem := toggledColumn_mem_carrier generators column
  rw [carrier_bot] at toggled_mem
  exact toggledColumn_ne_zero_of_sameZero generators row column sameZero
    (by simpa using toggled_mem)

/-- Same-zero recognition makes the fork carrier proper. -/
theorem carrier_ne_top_of_sameZero
    (generators : PairedControl → ControlMatrix) (row column : State)
    (sameZero : ∀ word,
      linearCoefficient generators row column word = 0 ↔
        pairedCoefficient ℚ 3 bcbcBody word = 0) :
    carrier generators column ≠ ⊤ := by
  intro carrier_top
  have all_zero : ∀ state : State, boundaryRow generators row ⬝ᵥ state = 0 := by
    intro state
    apply boundaryRow_dot_eq_zero_of_mem generators row column sameZero
    rw [carrier_top]
    exact Submodule.mem_top
  have boundary_zero : boundaryRow generators row = 0 := by
    funext coordinate
    have coordinate_zero := all_zero (Pi.single coordinate 1)
    rw [dotProduct, Fintype.sum_eq_single coordinate] at coordinate_zero
    · simpa using coordinate_zero
    · intro other other_ne
      simp [Pi.single, other_ne]
  exact boundaryRow_ne_zero_of_sameZero generators row column sameZero boundary_zero

/-- Every exact three-state `bcbc` recognizer has a one- or two-dimensional binary fork core. -/
theorem carrier_finrank_one_or_two_of_sameZero
    (generators : PairedControl → ControlMatrix) (row column : State)
    (sameZero : ∀ word,
      linearCoefficient generators row column word = 0 ↔
        pairedCoefficient ℚ 3 bcbcBody word = 0) :
    Module.finrank ℚ (carrier generators column) = 1 ∨
      Module.finrank ℚ (carrier generators column) = 2 := by
  have carrier_ne_bot := carrier_ne_bot_of_sameZero generators row column sameZero
  have carrier_ne_top := carrier_ne_top_of_sameZero generators row column sameZero
  have positive_rank : 1 ≤ Module.finrank ℚ (carrier generators column) :=
    Submodule.one_le_finrank_iff.mpr carrier_ne_bot
  have rank_lt_three : Module.finrank ℚ (carrier generators column) < 3 := by
    have rank_lt := Submodule.finrank_lt carrier_ne_top
    simpa using rank_lt
  omega

end TerminalForkCore
end MatrixMortality
