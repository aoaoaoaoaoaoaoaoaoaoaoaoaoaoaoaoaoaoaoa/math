import MatrixMortality.ChangedSeparatorRealization

/-!
# Rank-nine first-moment certificate

The four row certificates identify the first return moment with the paired `b` data role.
-/

namespace MatrixMortality

open scoped Matrix

namespace ChangedSeparatorRealization

/- Exact normalization of the generated 9-by-9 identity, with no heuristic proof search. -/
set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in
private theorem chain_moment_one_row_zero (ρ V K : ℚ)
    (regular : RegularChart ρ V K) :
    (chainOutput ρ V K * chainTransition ρ V K * chainInput ρ V K) 0 =
      chainDataB ρ 0 := by
  have negTailGap_ne_zero := regular.negTailGap_ne_zero
  have negChartGap_ne_zero := regular.negChartGap_ne_zero
  have factoredGap_ne_zero := regular.factoredGap_ne_zero
  funext j
  fin_cases j <;>
    simp only [chainOutput, chainTransition, chainTailEigenvalue,
      chainDenominator, chainInput, chainDataB, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.of_apply] <;>
    simp only [RegularChart.negTailGap_eq, RegularChart.negChartGap_eq,
      RegularChart.mixedDenominator_eq,
      RegularChart.widthTailDenominator_eq] <;>
    simp <;>
    simp only [RegularChart.subNegTailGap_eq] <;>
    field_simp [regular.width_ne_zero, regular.lowerScale_ne_zero,
      regular.denominator_ne_zero, regular.widthFactor_ne_zero,
      regular.tailGap_ne_zero, regular.sumGap_ne_zero,
      regular.chartGap_ne_zero, negTailGap_ne_zero,
      negChartGap_ne_zero, factoredGap_ne_zero] <;>
    ring

/- Exact normalization of the generated 9-by-9 identity, with no heuristic proof search. -/
set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in
private theorem chain_moment_one_row_one (ρ V K : ℚ)
    (regular : RegularChart ρ V K) :
    (chainOutput ρ V K * chainTransition ρ V K * chainInput ρ V K) 1 =
      chainDataB ρ 1 := by
  have negTailGap_ne_zero := regular.negTailGap_ne_zero
  have negChartGap_ne_zero := regular.negChartGap_ne_zero
  have factoredGap_ne_zero := regular.factoredGap_ne_zero
  funext j
  fin_cases j <;>
    simp only [chainOutput, chainTransition, chainTailEigenvalue,
      chainDenominator, chainInput, chainDataB, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.of_apply] <;>
    simp only [RegularChart.negTailGap_eq, RegularChart.negChartGap_eq,
      RegularChart.mixedDenominator_eq,
      RegularChart.widthTailDenominator_eq] <;>
    simp

/- Exact normalization of the generated 9-by-9 identity, with no heuristic proof search. -/
set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in
private theorem chain_moment_one_row_two (ρ V K : ℚ)
    (regular : RegularChart ρ V K) :
    (chainOutput ρ V K * chainTransition ρ V K * chainInput ρ V K) 2 =
      chainDataB ρ 2 := by
  have negTailGap_ne_zero := regular.negTailGap_ne_zero
  have negChartGap_ne_zero := regular.negChartGap_ne_zero
  have factoredGap_ne_zero := regular.factoredGap_ne_zero
  have reversedWidthFactor_ne_zero : -1 + ρ * 3 ≠ 0 := by
    rw [show -1 + ρ * 3 = 3 * ρ - 1 by ring]
    exact regular.widthFactor_ne_zero
  have widthFactorSquare_ne_zero : 1 - ρ * 6 + ρ ^ 2 * 9 ≠ 0 := by
    rw [show 1 - ρ * 6 + ρ ^ 2 * 9 = (3 * ρ - 1) ^ 2 by ring]
    exact pow_ne_zero 2 regular.widthFactor_ne_zero
  funext j
  fin_cases j <;>
    simp only [chainOutput, chainTransition, chainTailEigenvalue,
      chainDenominator, chainInput, chainDataB, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.of_apply] <;>
    simp only [RegularChart.negTailGap_eq, RegularChart.negChartGap_eq,
      RegularChart.mixedDenominator_eq,
      RegularChart.widthTailDenominator_eq] <;>
    simp <;>
    simp only [RegularChart.subNegTailGap_eq] <;>
    field_simp [regular.width_ne_zero, regular.lowerScale_ne_zero,
      regular.denominator_ne_zero, regular.widthFactor_ne_zero,
      regular.tailGap_ne_zero, regular.sumGap_ne_zero,
      regular.chartGap_ne_zero, negTailGap_ne_zero,
      negChartGap_ne_zero, factoredGap_ne_zero,
      reversedWidthFactor_ne_zero, widthFactorSquare_ne_zero] <;>
    ring_nf <;>
    field_simp [reversedWidthFactor_ne_zero,
      widthFactorSquare_ne_zero] <;>
    ring

/- Exact normalization of the generated 9-by-9 identity, with no heuristic proof search. -/
set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in
private theorem chain_moment_one_row_three (ρ V K : ℚ)
    (regular : RegularChart ρ V K) :
    (chainOutput ρ V K * chainTransition ρ V K * chainInput ρ V K) 3 =
      chainDataB ρ 3 := by
  have negTailGap_ne_zero := regular.negTailGap_ne_zero
  have negChartGap_ne_zero := regular.negChartGap_ne_zero
  have factoredGap_ne_zero := regular.factoredGap_ne_zero
  funext j
  fin_cases j <;>
    simp only [chainOutput, chainTransition, chainTailEigenvalue,
      chainDenominator, chainInput, chainDataB, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.of_apply] <;>
    simp only [RegularChart.negTailGap_eq, RegularChart.negChartGap_eq,
      RegularChart.mixedDenominator_eq,
      RegularChart.widthTailDenominator_eq] <;>
    simp <;>
    simp only [RegularChart.subNegTailGap_eq] <;>
    field_simp [regular.width_ne_zero, regular.lowerScale_ne_zero,
      regular.denominator_ne_zero, regular.widthFactor_ne_zero,
      regular.tailGap_ne_zero, regular.sumGap_ne_zero,
      regular.chartGap_ne_zero, negTailGap_ne_zero,
      negChartGap_ne_zero, factoredGap_ne_zero] <;>
    ring

/-- The exact chain chart realizes the paired `b` data role at return time one. -/
theorem chain_moment_one (ρ V K : ℚ) (regular : RegularChart ρ V K) :
    chainOutput ρ V K * chainTransition ρ V K * chainInput ρ V K =
      chainDataB ρ := by
  apply Matrix.ext
  intro i j
  fin_cases i
  · exact congrFun (chain_moment_one_row_zero ρ V K regular) j
  · exact congrFun (chain_moment_one_row_one ρ V K regular) j
  · exact congrFun (chain_moment_one_row_two ρ V K regular) j
  · exact congrFun (chain_moment_one_row_three ρ V K regular) j

/-- The chart's closed `b` role is the paired Neary generator. -/
theorem chainDataB_eq_pairedDataMatrix (β : Nat) (body : List TagLetter) :
    chainDataB (widthScale β) = pairedDataMatrix ℚ β body .b := by
  have upper_b :
      (ternaryCode (nearyUpper β (.rule .b)) : ℚ) =
        (15 * (3 : ℚ) ^ β + 1) / 2 := by
    simpa [nearyUpper, nearySideUpperB] using nearySideUpperB_eq β
  have upper_b_scale :
      ((3 : ℚ) ^ (nearyUpper β (.rule .b)).length) = 9 * (3 : ℚ) ^ β := by
    simpa [nearyUpper, nearySideUpperBScale] using nearySideUpperBScale_eq β
  have lower_b_scale :
      ((3 : ℚ) ^ (nearyLower β body (.rule .b)).length) = 27 := by
    norm_num [nearyLower]
  have erase_scale :
      ((3 : ℚ) ^ (nearyLower β body (.erase .b)).length) = 3 := by
    norm_num [nearyLower]
  rw [pairedDataMatrix_eq_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chainDataB, widthScale, upper_b, upper_b_scale, lower_b_scale,
      erase_scale]

/-- Every positive-width encoded body containing `b` realizes its `b` role at time one. -/
theorem moment_one (β : Nat) (β_pos : 0 < β) (body : List TagLetter)
    (b_mem : .b ∈ body) :
    output β body * transition β body * input β body =
      pairedDataMatrix ℚ β body .b := by
  calc
    output β body * transition β body * input β body =
        chainDataB (widthScale β) := by
      simpa [output, transition, input] using
        chain_moment_one (widthScale β) (ChangedSeparatorTail.lowerCCode β body)
          (ChangedSeparatorTail.lowerCScale β body) (regularChart β β_pos body b_mem)
    _ = pairedDataMatrix ℚ β body .b := chainDataB_eq_pairedDataMatrix β body

end ChangedSeparatorRealization

end MatrixMortality
