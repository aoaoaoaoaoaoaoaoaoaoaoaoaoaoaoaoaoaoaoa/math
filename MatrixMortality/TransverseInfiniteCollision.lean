import MatrixMortality.BranchingHistory
import MatrixMortality.TransverseInfiniteAtlas

/-!
# Letter-blind collision in the infinite transverse carrier

The explicit nonprojective carrier generator uses the same rank-two matrix for both data
controls. The `bcbc` terminal prefix and its certified nonterminal near-fork have the same toggle
positions, so this generator gives them identical products. No choice of terminal row and column
can turn the literal infinite-carrier family into a same-zero recognizer for `bcbc`.
-/

namespace MatrixMortality
namespace TransverseInfiniteCollision

open TransverseInfiniteAtlas

/-- The `bcbc` terminal control and nonterminal near-fork collide under every letter-blind
infinite-carrier generator. -/
theorem bcbcTerminal_wordProduct_eq_nearFork (source : ℚ) :
    wordProduct (generator source) BranchingHistory.bcbcTerminalControl =
      wordProduct (generator source) BranchingHistory.bcbcNearForkControl := by
  simp [BranchingHistory.bcbcTerminalControl, BranchingHistory.bcbcNearForkControl,
    wordProduct, generator, TransverseLineAtlas.generator]

/-- No row and column recover the `bcbc` paired zero language from the literal nonprojective
infinite-carrier generator. -/
theorem no_letterBlind_bcbc_sameZero (source : ℚ)
    (row column : TransverseInfiniteAtlas.State) :
    ¬ RepresentsZeroSet (pairedCoefficient ℚ 3 BranchingHistory.bcbcBody)
      (generator source) row column := by
  intro sameZero
  have terminalZero :
      linearCoefficient (generator source) row column BranchingHistory.bcbcTerminalControl = 0 :=
    (sameZero BranchingHistory.bcbcTerminalControl).mpr
      BranchingHistory.bcbc_terminal_nearFork.1
  have nearForkZero :
      linearCoefficient (generator source) row column BranchingHistory.bcbcNearForkControl = 0 := by
    rw [linearCoefficient, ← bcbcTerminal_wordProduct_eq_nearFork]
    simpa only [linearCoefficient] using terminalZero
  have nearForkSourceZero :
      pairedCoefficient ℚ 3 BranchingHistory.bcbcBody BranchingHistory.bcbcNearForkControl = 0 :=
    (sameZero BranchingHistory.bcbcNearForkControl).mp nearForkZero
  exact BranchingHistory.bcbc_terminal_nearFork.2 nearForkSourceZero

end TransverseInfiniteCollision
end MatrixMortality
