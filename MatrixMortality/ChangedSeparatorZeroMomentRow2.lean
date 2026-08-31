import MatrixMortality.ChangedSeparatorZeroMomentEntry20
import MatrixMortality.ChangedSeparatorZeroMomentEntry21
import MatrixMortality.ChangedSeparatorZeroMomentEntry22
import MatrixMortality.ChangedSeparatorZeroMomentEntry23

/-!
# Rank-nine zero-moment certificate, row two

The four independently elaborated entry certificates assemble this row.
-/

namespace MatrixMortality

open scoped Matrix

namespace ChangedSeparatorRealization

/-- Row two of the chart's zeroth moment is the phase-toggle row. -/
theorem chain_zero_moment_row_two (ρ V K : ℚ) (regular : RegularChart ρ V K) :
    (chainOutput ρ V K * chainInput ρ V K) 2 = ![0, 0, 1, 0] := by
  funext j
  fin_cases j
  · simpa using chain_zero_moment_entry_two_zero ρ V K regular
  · simpa using chain_zero_moment_entry_two_one ρ V K regular
  · simpa using chain_zero_moment_entry_two_two ρ V K regular
  · simpa using chain_zero_moment_entry_two_three ρ V K regular

end ChangedSeparatorRealization

end MatrixMortality

