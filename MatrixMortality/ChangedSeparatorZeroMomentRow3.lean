import MatrixMortality.ChangedSeparatorZeroMomentEntry30
import MatrixMortality.ChangedSeparatorZeroMomentEntry31
import MatrixMortality.ChangedSeparatorZeroMomentEntry32
import MatrixMortality.ChangedSeparatorZeroMomentEntry33

/-!
# Rank-nine zero-moment certificate, row three

The four independently elaborated entry certificates assemble this row.
-/

namespace MatrixMortality

open scoped Matrix

namespace ChangedSeparatorRealization

/-- Row three of the chart's zeroth moment is the phase-toggle row. -/
theorem chain_zero_moment_row_three (ρ V K : ℚ) (regular : RegularChart ρ V K) :
    (chainOutput ρ V K * chainInput ρ V K) 3 = ![0, 1, 0, 0] := by
  funext j
  fin_cases j
  · simpa using chain_zero_moment_entry_three_zero ρ V K regular
  · simpa using chain_zero_moment_entry_three_one ρ V K regular
  · simpa using chain_zero_moment_entry_three_two ρ V K regular
  · simpa using chain_zero_moment_entry_three_three ρ V K regular

end ChangedSeparatorRealization

end MatrixMortality

