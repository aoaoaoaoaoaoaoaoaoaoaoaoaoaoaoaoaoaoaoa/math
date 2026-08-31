import MatrixMortality.ChangedSeparatorZeroMomentRow0
import MatrixMortality.ChangedSeparatorZeroMomentRow1
import MatrixMortality.ChangedSeparatorZeroMomentRow2
import MatrixMortality.ChangedSeparatorZeroMomentRow3

/-!
# Rank-nine zero-moment certificate

The four independently elaborated row certificates assemble the exact zeroth return moment.
-/

namespace MatrixMortality

open scoped Matrix

namespace ChangedSeparatorRealization

/-- The exact chain chart realizes the phase toggle at return time zero. -/
theorem chain_zero_moment (ρ V K : ℚ) (regular : RegularChart ρ V K) :
    chainOutput ρ V K * chainInput ρ V K = pairedToggleMatrix ℚ := by
  rw [pairedToggleMatrix_eq_explicit]
  apply Matrix.ext
  intro i j
  fin_cases i
  · exact congrFun (chain_zero_moment_row_zero ρ V K regular) j
  · exact congrFun (chain_zero_moment_row_one ρ V K regular) j
  · exact congrFun (chain_zero_moment_row_two ρ V K regular) j
  · exact congrFun (chain_zero_moment_row_three ρ V K regular) j

/-- Every positive-width encoded body containing `b` realizes the phase toggle at time zero. -/
theorem zero_moment (β : Nat) (β_pos : 0 < β) (body : List TagLetter)
    (b_mem : .b ∈ body) :
    output β body * input β body = pairedToggleMatrix ℚ := by
  exact chain_zero_moment
    (widthScale β) (ChangedSeparatorTail.lowerCCode β body)
    (ChangedSeparatorTail.lowerCScale β body) (regularChart β β_pos body b_mem)

end ChangedSeparatorRealization

end MatrixMortality
