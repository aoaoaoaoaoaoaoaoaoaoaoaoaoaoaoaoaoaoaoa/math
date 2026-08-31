import MatrixMortality.ChangedSeparatorRealization

/-!
# Rank-nine zero-moment certificate, row zero

This file isolates one row of the exact symbolic product so Lake can elaborate the four
independent normalization certificates in parallel.
-/

namespace MatrixMortality

open scoped Matrix

namespace ChangedSeparatorRealization

/- Exact normalization of the generated chart, with no heuristic proof search. -/
set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in
/-- Row zero of the chart's zeroth moment is the phase-toggle row. -/
theorem chain_zero_moment_row_zero (ρ V K : ℚ) (regular : RegularChart ρ V K) :
    (chainOutput ρ V K * chainInput ρ V K) 0 = ![1, 0, 0, 0] := by
  have negTailGap_ne_zero := regular.negTailGap_ne_zero
  have negChartGap_ne_zero := regular.negChartGap_ne_zero
  have factoredGap_ne_zero := regular.factoredGap_ne_zero
  funext j
  fin_cases j <;>
    simp only [chainOutput, chainInput, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue,
      Matrix.cons_val_zero', Matrix.cons_val_succ', zero_mul, mul_zero, mul_one,
      add_zero, zero_add, Finset.sum_of_isEmpty] <;>
    simp only [RegularChart.negTailGap_eq, RegularChart.mixedDenominator_eq] <;>
    field_simp [regular.width_ne_zero, regular.lowerScale_ne_zero,
      regular.widthFactor_ne_zero, regular.tailGap_ne_zero,
      regular.sumGap_ne_zero, regular.chartGap_ne_zero,
      negTailGap_ne_zero, negChartGap_ne_zero, factoredGap_ne_zero] <;>
    ring

end ChangedSeparatorRealization

end MatrixMortality
