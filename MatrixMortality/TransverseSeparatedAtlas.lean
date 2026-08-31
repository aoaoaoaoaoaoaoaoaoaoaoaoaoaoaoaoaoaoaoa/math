import MatrixMortality.TransverseInfiniteCollision

/-!
# A distinct-data escape from the letter-blind carrier collision

Left-multiplying the second rank-two data map by one fixed invertible matrix separates the `bcbc`
terminal prefix from its near-fork at every rational source. The first data map, nonprojective
toggle, infinite carrier orbit, and source-universal delayed terminal section remain unchanged.
This supplies a candidate mechanism beyond the letter-blind obstruction, not a complete same-zero
recognizer.
-/

namespace MatrixMortality
namespace TransverseSeparatedAtlas

open scoped Matrix

open TransverseInfiniteAtlas

/-- Invertible left multiplier distinguishing the second data control. -/
def separator : ControlMatrix :=
  !![2, -1, -1;
     0, 0, 1;
     2, 1, -1]

theorem separator_det : separator.det = -4 := by
  norm_num [separator, Matrix.det_fin_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]

theorem separator_isUnit : IsUnit separator := by
  rw [Matrix.isUnit_iff_isUnit_det, separator_det]
  norm_num

/-- Distinct source-dependent data controls, with the original map retained at letter `b`. -/
def separatedData (source : ℚ) : TagLetter → ControlMatrix
  | .b => data source
  | .c => separator * data source

/-- Both separated data controls have rank exactly two. -/
theorem separatedData_rank_eq_two (source : ℚ) (letter : TagLetter) :
    (separatedData source letter).rank = 2 := by
  cases letter with
  | b => exact data_rank_eq_two source
  | c =>
      rw [separatedData,
        Matrix.rank_mul_eq_right_of_det_ne_zero separator (data source)]
      · exact data_rank_eq_two source
      · rw [separator_det]
        norm_num

/-- The two data maps are distinct at every source. -/
theorem separatedData_ne (source : ℚ) :
    separatedData source .b ≠ separatedData source .c := by
  intro dataEqual
  have entryEqual := congrArg (fun matrix : ControlMatrix => matrix 1 0) dataEqual
  norm_num [separatedData, separator, data, dataInput, dataProjection, Matrix.mul_apply,
    Fin.sum_univ_succ] at entryEqual

/-- Three-control candidate retaining the original diagonal toggle. -/
def generator (source : ℚ) : PairedControl → ControlMatrix :=
  TransverseLineAtlas.generator (separatedData source) toggle

/-- The literal `tⁿb` carrier prefixes still produce the original carrier matrices. -/
theorem wordProduct_carrierWord (source : ℚ) (power : Nat) :
    wordProduct (generator source) (carrierWord power) = carrierMatrix source power := by
  simp [wordProduct, generator, carrierWord, TransverseLineAtlas.generator, separatedData,
    carrierMatrix, List.map_replicate, List.prod_replicate]

/-- The source-universal coefficient section remains exact on every retained carrier prefix. -/
theorem linearCoefficient_carrierWord
    (source : ℚ) (coefficients : State) (power : Nat) :
    linearCoefficient (generator source) (coefficientSectionRow source coefficients)
        (coefficientSectionColumn source) (carrierWord power) =
      exponentialScalar (coefficients 0) (coefficients 1) (coefficients 2) power := by
  rw [linearCoefficient, wordProduct_carrierWord]
  simpa only [terminalValue] using coefficientSection_terminalValue source coefficients power

/-- Every source-indexed delayed singleton remains exact on the retained carrier prefixes. -/
theorem sourceFamily_delayed_carrierWord_zero_iff
    {Source : Type*} (sourceParameter : Source → ℚ) (targetDepth : Source → Nat)
    (source : Source) (power : Nat) :
    linearCoefficient (generator (sourceParameter source))
          (coefficientSectionRow (sourceParameter source)
            ![(2 : ℚ) ^ targetDepth source, 1, 0])
          (coefficientSectionColumn (sourceParameter source)) (carrierWord power) = 0 ↔
      power = targetDepth source := by
  rw [linearCoefficient_carrierWord]
  simpa using exponentialScalar_binary_singleton (targetDepth source) power

/-- Exact separating entry between the `bcbc` terminal prefix and its near-fork. -/
theorem bcbc_product_difference_entry (source : ℚ) :
    wordProduct (generator source) BranchingHistory.bcbcTerminalControl 1 0 -
        wordProduct (generator source) BranchingHistory.bcbcNearForkControl 1 0 =
      6 * (2 * source ^ 2 - 5 * source + 4) := by
  simp [BranchingHistory.bcbcTerminalControl, BranchingHistory.bcbcNearForkControl,
    wordProduct, generator, TransverseLineAtlas.generator, separatedData, separator, toggle,
    data, dataInput, dataProjection, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

theorem separation_polynomial_pos (source : ℚ) :
    0 < 2 * source ^ 2 - 5 * source + 4 := by
  nlinarith [sq_nonneg (4 * source - 5)]

/-- The distinct-data candidate separates the exact letter-blind collision at every source. -/
theorem bcbcTerminal_wordProduct_ne_nearFork (source : ℚ) :
    wordProduct (generator source) BranchingHistory.bcbcTerminalControl ≠
      wordProduct (generator source) BranchingHistory.bcbcNearForkControl := by
  intro productsEqual
  have entryEqual := congrArg (fun matrix : ControlMatrix => matrix 1 0) productsEqual
  have differenceZero :
      wordProduct (generator source) BranchingHistory.bcbcTerminalControl 1 0 -
          wordProduct (generator source) BranchingHistory.bcbcNearForkControl 1 0 = 0 :=
    sub_eq_zero.mpr entryEqual
  have differencePos :
      0 < wordProduct (generator source) BranchingHistory.bcbcTerminalControl 1 0 -
          wordProduct (generator source) BranchingHistory.bcbcNearForkControl 1 0 := by
    rw [bcbc_product_difference_entry]
    exact mul_pos (by norm_num) (separation_polynomial_pos source)
  linarith

end TransverseSeparatedAtlas
end MatrixMortality
