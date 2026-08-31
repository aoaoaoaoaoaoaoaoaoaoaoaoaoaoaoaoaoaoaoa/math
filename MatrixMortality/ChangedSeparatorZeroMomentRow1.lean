import MatrixMortality.ChangedSeparatorZeroMomentEntry10
import MatrixMortality.ChangedSeparatorZeroMomentEntry11
import MatrixMortality.ChangedSeparatorZeroMomentEntry12
import MatrixMortality.ChangedSeparatorZeroMomentEntry13

/-!
# Rank-nine zero-moment certificate, row one

The four independently elaborated entry certificates assemble this row.
-/

namespace MatrixMortality

open scoped Matrix

namespace ChangedSeparatorRealization

/-- Row one of the chart's zeroth moment is the phase-toggle row. -/
theorem chain_zero_moment_row_one (ρ V K : ℚ) (regular : RegularChart ρ V K) :
    (chainOutput ρ V K * chainInput ρ V K) 1 = ![0, 0, 0, 1] := by
  funext j
  fin_cases j
  · simpa using chain_zero_moment_entry_one_zero ρ V K regular
  · simpa using chain_zero_moment_entry_one_one ρ V K regular
  · simpa using chain_zero_moment_entry_one_two ρ V K regular
  · simpa using chain_zero_moment_entry_one_three ρ V K regular

end ChangedSeparatorRealization

end MatrixMortality

