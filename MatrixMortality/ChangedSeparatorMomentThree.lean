import MatrixMortality.ChangedSeparatorTransitionPowers

/-!
# Rank-nine third-moment certificate

The four row certificates identify the third return moment with the changed rank-one separator.
-/

namespace MatrixMortality

open scoped Matrix

namespace ChangedSeparatorRealization

private theorem normalizedWidthFactor_ne_zero {ρ V K : ℚ}
    (regular : RegularChart ρ V K) : -1 + ρ * 3 ≠ 0 := by
  rw [show -1 + ρ * 3 = 3 * ρ - 1 by ring]
  exact regular.widthFactor_ne_zero

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in
private theorem chain_moment_three_row_zero (ρ V K : ℚ)
    (regular : RegularChart ρ V K) :
    (chainOutput ρ V K * chainTransitionCube ρ V K * chainInput ρ V K) 0 =
      chainTailSeparator ρ V K 0 := by
  have negTailGap_ne_zero := regular.negTailGap_ne_zero
  have negChartGap_ne_zero := regular.negChartGap_ne_zero
  have factoredGap_ne_zero := regular.factoredGap_ne_zero
  funext j
  fin_cases j <;>
    simp only [chainOutput, chainTransitionCube, chainTailEigenvalue,
      chainInput, chainTailSeparator, chainTailColumn, chainTailRow,
      Matrix.vecMulVec, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.of_apply] <;>
    simp only [RegularChart.negTailGap_eq, RegularChart.negChartGap_eq,
      RegularChart.mixedDenominator_eq,
      RegularChart.widthTailDenominator_eq] <;>
    simp <;>
    field_simp [regular.width_ne_zero, regular.lowerScale_ne_zero,
      regular.denominator_ne_zero, regular.widthFactor_ne_zero,
      regular.tailGap_ne_zero, regular.sumGap_ne_zero,
      regular.chartGap_ne_zero, negTailGap_ne_zero,
      negChartGap_ne_zero, factoredGap_ne_zero] <;>
    simp only [chainDenominator] <;>
    ring_nf <;>
    (field_simp [normalizedWidthFactor_ne_zero regular]; ring)

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in
private theorem chain_moment_three_row_one (ρ V K : ℚ)
    (_regular : RegularChart ρ V K) :
    (chainOutput ρ V K * chainTransitionCube ρ V K * chainInput ρ V K) 1 =
      chainTailSeparator ρ V K 1 := by
  funext j
  fin_cases j <;>
    simp [chainOutput, chainTransitionCube, chainInput,
      chainTailSeparator, chainTailColumn, Matrix.vecMulVec,
      Matrix.mul_apply, Fin.sum_univ_succ]

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in
private theorem chain_moment_three_row_two (ρ V K : ℚ)
    (regular : RegularChart ρ V K) :
    (chainOutput ρ V K * chainTransitionCube ρ V K * chainInput ρ V K) 2 =
      chainTailSeparator ρ V K 2 := by
  have negTailGap_ne_zero := regular.negTailGap_ne_zero
  have negChartGap_ne_zero := regular.negChartGap_ne_zero
  have factoredGap_ne_zero := regular.factoredGap_ne_zero
  funext j
  fin_cases j <;>
    simp only [chainOutput, chainTransitionCube, chainTailEigenvalue,
      chainInput, chainTailSeparator, chainTailColumn, chainTailRow,
      Matrix.vecMulVec, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.of_apply] <;>
    simp only [RegularChart.negTailGap_eq, RegularChart.negChartGap_eq,
      RegularChart.mixedDenominator_eq,
      RegularChart.widthTailDenominator_eq] <;>
    simp <;>
    field_simp [regular.width_ne_zero, regular.lowerScale_ne_zero,
      regular.denominator_ne_zero, regular.widthFactor_ne_zero,
      regular.tailGap_ne_zero, regular.sumGap_ne_zero,
      regular.chartGap_ne_zero, negTailGap_ne_zero,
      negChartGap_ne_zero, factoredGap_ne_zero] <;>
    simp only [chainDenominator] <;>
    ring_nf

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in
private theorem chain_moment_three_row_three (ρ V K : ℚ)
    (regular : RegularChart ρ V K) :
    (chainOutput ρ V K * chainTransitionCube ρ V K * chainInput ρ V K) 3 =
      chainTailSeparator ρ V K 3 := by
  have negTailGap_ne_zero := regular.negTailGap_ne_zero
  have negChartGap_ne_zero := regular.negChartGap_ne_zero
  have factoredGap_ne_zero := regular.factoredGap_ne_zero
  funext j
  fin_cases j <;>
    simp only [chainOutput, chainTransitionCube, chainTailEigenvalue,
      chainInput, chainTailSeparator, chainTailColumn, chainTailRow,
      Matrix.vecMulVec, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.of_apply] <;>
    simp only [RegularChart.negTailGap_eq, RegularChart.negChartGap_eq,
      RegularChart.mixedDenominator_eq,
      RegularChart.widthTailDenominator_eq] <;>
    simp <;>
    field_simp [regular.width_ne_zero, regular.lowerScale_ne_zero,
      regular.denominator_ne_zero, regular.widthFactor_ne_zero,
      regular.tailGap_ne_zero, regular.sumGap_ne_zero,
      regular.chartGap_ne_zero, negTailGap_ne_zero,
      negChartGap_ne_zero, factoredGap_ne_zero] <;>
    simp only [chainDenominator] <;>
    ring_nf

/-- The exact chain chart reaches its changed rank-one separator at time three. -/
theorem chain_moment_three (ρ V K : ℚ) (regular : RegularChart ρ V K) :
    chainOutput ρ V K * chainTransitionCube ρ V K * chainInput ρ V K =
      chainTailSeparator ρ V K := by
  apply Matrix.ext
  intro i j
  fin_cases i
  · exact congrFun (chain_moment_three_row_zero ρ V K regular) j
  · exact congrFun (chain_moment_three_row_one ρ V K regular) j
  · exact congrFun (chain_moment_three_row_two ρ V K regular) j
  · exact congrFun (chain_moment_three_row_three ρ V K regular) j

/-- Changed rank-one separator specialized to one encoded Neary instance. -/
def separator (β : Nat) (body : List TagLetter) : Square (Fin 4) ℚ :=
  chainTailSeparator (widthScale β) (ChangedSeparatorTail.lowerCCode β body)
    (ChangedSeparatorTail.lowerCScale β body)

/-- Every positive-width encoded body containing `b` reaches its separator at time three. -/
theorem moment_three (β : Nat) (β_pos : 0 < β) (body : List TagLetter)
    (b_mem : .b ∈ body) :
    output β body * transition β body ^ 3 * input β body = separator β body := by
  simpa [output, transition, input, separator, chainTransition_pow_three] using
    chain_moment_three (widthScale β) (ChangedSeparatorTail.lowerCCode β body)
      (ChangedSeparatorTail.lowerCScale β body) (regularChart β β_pos body b_mem)

end ChangedSeparatorRealization

end MatrixMortality
