import MatrixMortality.ChangedSeparatorRealization

/-!
# Rank-nine zero-moment certificate, entry 32

This module isolates one exact symbolic entry so Lake can elaborate the certificate independently.
-/

namespace MatrixMortality

open scoped Matrix

namespace ChangedSeparatorRealization

/- Exact normalization of the generated chart, with no heuristic proof search. -/
set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in
/-- Entry (3, 2) of the chain chart's zeroth moment. -/
theorem chain_zero_moment_entry_three_two (ρ V K : ℚ)
    (regular : RegularChart ρ V K) :
    (chainOutput ρ V K * chainInput ρ V K) 3 2 = 0 := by
  have negTailGap_ne_zero := regular.negTailGap_ne_zero
  have negChartGap_ne_zero := regular.negChartGap_ne_zero
  have factoredGap_ne_zero := regular.factoredGap_ne_zero
  simp only [chainOutput, chainInput, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.of_apply]
  simp only [RegularChart.negTailGap_eq, RegularChart.negChartGap_eq,
    RegularChart.mixedDenominator_eq, RegularChart.widthTailDenominator_eq]
  simp
  simp only [RegularChart.subNegTailGap_eq]
  field_simp [regular.width_ne_zero, regular.lowerScale_ne_zero,
    regular.widthFactor_ne_zero, regular.tailGap_ne_zero,
    regular.sumGap_ne_zero, regular.chartGap_ne_zero,
    negTailGap_ne_zero, negChartGap_ne_zero, factoredGap_ne_zero]
  ring

end ChangedSeparatorRealization

end MatrixMortality
