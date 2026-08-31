import MatrixMortality.ChangedSeparatorRealization

/-!
# Rank-nine zero-moment certificate, entry 30

This module isolates one exact symbolic entry so Lake can elaborate the certificate independently.
-/

namespace MatrixMortality

open scoped Matrix

namespace ChangedSeparatorRealization

/- Exact normalization of the generated chart, with no heuristic proof search. -/
set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in
/-- Entry (3, 0) of the chain chart's zeroth moment. -/
theorem chain_zero_moment_entry_three_zero (ρ V K : ℚ)
    (regular : RegularChart ρ V K) :
    (chainOutput ρ V K * chainInput ρ V K) 3 0 = 0 := by
  have negTailGap_ne_zero := regular.negTailGap_ne_zero
  have negChartGap_ne_zero := regular.negChartGap_ne_zero
  have factoredGap_ne_zero := regular.factoredGap_ne_zero
  simp only [chainOutput, chainInput, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.of_apply]
  simp only [RegularChart.negTailGap_eq, RegularChart.negChartGap_eq,
    RegularChart.mixedDenominator_eq, RegularChart.widthTailDenominator_eq]
  simp
  rw [RegularChart.subNegTailGap_cube_eq]
  field_simp [regular.lowerScale_ne_zero, regular.widthFactor_ne_zero,
    regular.tailGap_ne_zero]
  ring

end ChangedSeparatorRealization

end MatrixMortality
