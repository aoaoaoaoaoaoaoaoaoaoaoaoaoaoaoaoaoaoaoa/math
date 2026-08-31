import MatrixMortality.ChangedSeparatorTransitionPowers

/-!
# Rank-nine second-moment certificate

The four row certificates identify the second return moment with the paired `c` data role.
-/

namespace MatrixMortality

open scoped Matrix

namespace ChangedSeparatorRealization

private theorem normalizedWidthFactor_ne_zero {ρ V K : ℚ}
    (regular : RegularChart ρ V K) : -1 + ρ * 3 ≠ 0 := by
  rw [show -1 + ρ * 3 = 3 * ρ - 1 by ring]
  exact regular.widthFactor_ne_zero

private theorem normalizedWidthFactorSquare_ne_zero {ρ V K : ℚ}
    (regular : RegularChart ρ V K) : 1 - ρ * 6 + ρ ^ 2 * 9 ≠ 0 := by
  rw [show 1 - ρ * 6 + ρ ^ 2 * 9 = (3 * ρ - 1) ^ 2 by ring]
  exact pow_ne_zero 2 regular.widthFactor_ne_zero

private theorem normalizedTailGap_ne_zero {ρ V K : ℚ}
    (regular : RegularChart ρ V K) : -1 - V * 2 + K ≠ 0 := by
  rw [show -1 - V * 2 + K = K - 2 * V - 1 by ring]
  exact regular.tailGap_ne_zero

/- Exact normalization of the generated 9-by-9 identity, with no heuristic proof search. -/
set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in
private theorem chain_moment_two_row_zero (ρ V K : ℚ)
    (regular : RegularChart ρ V K) :
    (chainOutput ρ V K * chainTransitionSquare ρ V K * chainInput ρ V K) 0 =
      chainDataC V K 0 := by
  have negTailGap_ne_zero := regular.negTailGap_ne_zero
  have negChartGap_ne_zero := regular.negChartGap_ne_zero
  have factoredGap_ne_zero := regular.factoredGap_ne_zero
  funext j
  fin_cases j <;>
    simp only [chainOutput, chainTransitionSquare, chainTailEigenvalue,
      chainInput, chainDataC, Matrix.mul_apply,
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
    simp only [chainDenominator] <;>
    ring_nf
  field_simp [normalizedWidthFactor_ne_zero regular,
    normalizedWidthFactorSquare_ne_zero regular,
    normalizedTailGap_ne_zero regular]
  ring

/- Exact normalization of the generated 9-by-9 identity, with no heuristic proof search. -/
set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in
private theorem chain_moment_two_row_one (ρ V K : ℚ)
    (regular : RegularChart ρ V K) :
    (chainOutput ρ V K * chainTransitionSquare ρ V K * chainInput ρ V K) 1 =
      chainDataC V K 1 := by
  have negTailGap_ne_zero := regular.negTailGap_ne_zero
  have negChartGap_ne_zero := regular.negChartGap_ne_zero
  have factoredGap_ne_zero := regular.factoredGap_ne_zero
  funext j
  fin_cases j <;>
    simp only [chainOutput, chainTransitionSquare, chainTailEigenvalue,
      chainInput, chainDataC, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.of_apply] <;>
    simp only [RegularChart.negTailGap_eq, RegularChart.negChartGap_eq,
      RegularChart.mixedDenominator_eq,
      RegularChart.widthTailDenominator_eq] <;>
    simp

/- Exact normalization of the generated 9-by-9 identity, with no heuristic proof search. -/
set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in
private theorem chain_moment_two_row_two (ρ V K : ℚ)
    (regular : RegularChart ρ V K) :
    (chainOutput ρ V K * chainTransitionSquare ρ V K * chainInput ρ V K) 2 =
      chainDataC V K 2 := by
  have negTailGap_ne_zero := regular.negTailGap_ne_zero
  have negChartGap_ne_zero := regular.negChartGap_ne_zero
  have factoredGap_ne_zero := regular.factoredGap_ne_zero
  funext j
  fin_cases j <;>
    simp only [chainOutput, chainTransitionSquare, chainTailEigenvalue,
      chainInput, chainDataC, Matrix.mul_apply,
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
    simp only [chainDenominator] <;>
    ring_nf
  field_simp [normalizedWidthFactor_ne_zero regular,
    normalizedWidthFactorSquare_ne_zero regular,
    normalizedTailGap_ne_zero regular]
  ring

/- Exact normalization of the generated 9-by-9 identity, with no heuristic proof search. -/
set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in
private theorem chain_moment_two_row_three (ρ V K : ℚ)
    (regular : RegularChart ρ V K) :
    (chainOutput ρ V K * chainTransitionSquare ρ V K * chainInput ρ V K) 3 =
      chainDataC V K 3 := by
  have negTailGap_ne_zero := regular.negTailGap_ne_zero
  have negChartGap_ne_zero := regular.negChartGap_ne_zero
  have factoredGap_ne_zero := regular.factoredGap_ne_zero
  funext j
  fin_cases j <;>
    simp only [chainOutput, chainTransitionSquare, chainTailEigenvalue,
      chainInput, chainDataC, Matrix.mul_apply,
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
    simp only [chainDenominator] <;>
    ring_nf

/-- The exact chain chart realizes the paired `c` data role at return time two. -/
theorem chain_moment_two (ρ V K : ℚ) (regular : RegularChart ρ V K) :
    chainOutput ρ V K * chainTransitionSquare ρ V K * chainInput ρ V K =
      chainDataC V K := by
  apply Matrix.ext
  intro i j
  fin_cases i
  · exact congrFun (chain_moment_two_row_zero ρ V K regular) j
  · exact congrFun (chain_moment_two_row_one ρ V K regular) j
  · exact congrFun (chain_moment_two_row_two ρ V K regular) j
  · exact congrFun (chain_moment_two_row_three ρ V K regular) j

/-- The chart's closed `c` role is the paired Neary generator. -/
theorem chainDataC_eq_pairedDataMatrix (β : Nat) (body : List TagLetter) :
    chainDataC (ChangedSeparatorTail.lowerCCode β body)
        (ChangedSeparatorTail.lowerCScale β body) =
      pairedDataMatrix ℚ β body .c := by
  rw [pairedDataMatrix_eq_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chainDataC, ChangedSeparatorTail.lowerCCode,
      ChangedSeparatorTail.lowerCScale, nearySideLowerC,
      nearySideLowerCScale, nearyUpper, nearyLower, tagCode, ternaryDigit]

/-- Every positive-width encoded body containing `b` realizes its `c` role at time two. -/
theorem moment_two (β : Nat) (β_pos : 0 < β) (body : List TagLetter)
    (b_mem : .b ∈ body) :
    output β body * transition β body ^ 2 * input β body =
      pairedDataMatrix ℚ β body .c := by
  calc
    output β body * transition β body ^ 2 * input β body =
        chainDataC (ChangedSeparatorTail.lowerCCode β body)
          (ChangedSeparatorTail.lowerCScale β body) := by
      simpa [output, transition, input, chainTransition_pow_two] using
        chain_moment_two (widthScale β) (ChangedSeparatorTail.lowerCCode β body)
          (ChangedSeparatorTail.lowerCScale β body) (regularChart β β_pos body b_mem)
    _ = pairedDataMatrix ℚ β body .c := chainDataC_eq_pairedDataMatrix β body

end ChangedSeparatorRealization

end MatrixMortality
