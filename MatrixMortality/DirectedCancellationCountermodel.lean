import MatrixMortality.DirectedCancellation
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# A positive rank-two directed-cancellation countermodel
-/

namespace MatrixMortality

namespace DirectedCancellationCountermodel

open scoped Matrix

/-- Three-state rational carrier matrices. -/
abbrev Carrier := Matrix (Fin 3) (Fin 3) ℚ

/-- Positive rank-two push generator. -/
def push : Carrier :=
  !![1, 1, 1;
     1, 2, 3;
     2, 3, 4]

/-- Positive rank-two pop generator. -/
def pop : Carrier :=
  !![1, 2, 1;
     2, 1, 2;
     3, 3, 3]

private def carrierEmbed : Matrix (Fin 3) (Fin 2) ℚ :=
  !![1, 0;
     0, 1;
     1, 1]

private def pushCore : Matrix (Fin 2) (Fin 3) ℚ :=
  !![1, 1, 1;
     1, 2, 3]

private def popCore : Matrix (Fin 2) (Fin 3) ℚ :=
  !![1, 2, 1;
     2, 1, 2]

private def carrierRetract : Matrix (Fin 2) (Fin 3) ℚ :=
  !![1, 0, 0;
     0, 1, 0]

private def pushCoreSection : Matrix (Fin 3) (Fin 2) ℚ :=
  !![2, -1;
     -1, 1;
     0, 0]

private def popCoreSection : Matrix (Fin 3) (Fin 2) ℚ :=
  !![-1 / 3, 2 / 3;
     2 / 3, -1 / 3;
     0, 0]

private theorem push_eq_factor : push = carrierEmbed * pushCore := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [push, carrierEmbed, pushCore, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem pop_eq_factor : pop = carrierEmbed * popCore := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pop, carrierEmbed, popCore, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem carrierRetract_mul_embed : carrierRetract * carrierEmbed = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [carrierRetract, carrierEmbed, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_succ]

private theorem pushCore_mul_section : pushCore * pushCoreSection = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pushCore, pushCoreSection, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_succ]

private theorem popCore_mul_section : popCore * popCoreSection = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [popCore, popCoreSection, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_succ]

private theorem factor_rank_eq_two
    (matrix : Carrier) (core : Matrix (Fin 2) (Fin 3) ℚ)
    (matrix_eq : matrix = carrierEmbed * core)
    (rightInverse : Matrix (Fin 3) (Fin 2) ℚ)
    (core_rightInverse : core * rightInverse = 1) :
    matrix.rank = 2 := by
  have core_rank : core.rank = 2 := by
    apply le_antisymm
    · exact Matrix.rank_le_height core
    · have rank_bound := Matrix.rank_mul_le_left core rightInverse
      rw [core_rightInverse, Matrix.rank_one] at rank_bound
      norm_num at rank_bound ⊢
      exact rank_bound
  apply le_antisymm
  · rw [matrix_eq]
    exact (Matrix.rank_mul_le_left carrierEmbed core).trans (Matrix.rank_le_width carrierEmbed)
  · have core_factor : core = carrierRetract * matrix := by
      calc
        core = (1 : Matrix (Fin 2) (Fin 2) ℚ) * core := by simp
        _ = (carrierRetract * carrierEmbed) * core := by rw [carrierRetract_mul_embed]
        _ = carrierRetract * (carrierEmbed * core) := by rw [Matrix.mul_assoc]
        _ = carrierRetract * matrix := by rw [← matrix_eq]
    have lower : core.rank ≤ matrix.rank := by
      calc
        core.rank = (carrierRetract * matrix).rank := congrArg Matrix.rank core_factor
        _ ≤ matrix.rank := Matrix.rank_mul_le_right carrierRetract matrix
    rwa [core_rank] at lower

theorem push_rank : push.rank = 2 :=
  factor_rank_eq_two push pushCore push_eq_factor pushCoreSection pushCore_mul_section

theorem pop_rank : pop.rank = 2 :=
  factor_rank_eq_two pop popCore pop_eq_factor popCoreSection popCore_mul_section

theorem push_entry_pos (i j : Fin 3) : 0 < push i j := by
  fin_cases i <;> fin_cases j <;> norm_num [push]

theorem pop_entry_pos (i j : Fin 3) : 0 < pop i j := by
  fin_cases i <;> fin_cases j <;> norm_num [pop]

/-- Encoded height-one Dyck block `x x̄`. -/
def unitBlock : Carrier := push * pop

/-- Encoded height-two Dyck block `x² x̄²`. -/
def doubleBlock : Carrier := push ^ 2 * pop ^ 2

/-- Distinguished scalar coefficient used to order the published code matrices. -/
def score (matrix : Carrier) : ℚ := matrix 0 0

/-- Matrix code for `d`. -/
def codeD : Carrier := 1
/-- Matrix code for `a`. -/
def codeA : Carrier := unitBlock ^ 2 * doubleBlock
/-- Matrix code for `â`. -/
def codeAHat : Carrier := doubleBlock ^ 3
/-- Matrix code for `b`. -/
def codeB : Carrier := unitBlock ^ 2 * doubleBlock ^ 2
/-- Matrix code for `b̂`. -/
def codeBHat : Carrier := doubleBlock ^ 4
/-- Matrix code for `c`. -/
def codeC : Carrier := unitBlock ^ 5
/-- Matrix code for `č`. -/
def codeCCheck : Carrier := doubleBlock ^ 2 * unitBlock ^ 3
/-- Matrix code for `ĉ`. -/
def codeCHat : Carrier := doubleBlock ^ 4 * unitBlock

theorem unitBlock_entry_gt_one (i j : Fin 3) :
    (1 : Carrier) i j < unitBlock i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [unitBlock, push, pop, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_succ]

/-- In every nonnegative context with a positive distinguished boundary path, retaining one
`push * pop` redex strictly increases the distinguished coefficient. -/
theorem context_deletion_score_strict (before after : Carrier)
    (before_nonnegative : ∀ i j, 0 ≤ before i j)
    (after_nonnegative : ∀ i j, 0 ≤ after i j)
    (before_boundary_pos : 0 < before 0 0)
    (after_boundary_pos : 0 < after 0 0) :
    score (before * push * pop * after) > score (before * after) := by
  have h00 : 0 < before 0 0 * after 0 0 :=
    mul_pos before_boundary_pos after_boundary_pos
  have h01 : 0 ≤ before 0 0 * after 1 0 :=
    mul_nonneg (before_nonnegative 0 0) (after_nonnegative 1 0)
  have h02 : 0 ≤ before 0 0 * after 2 0 :=
    mul_nonneg (before_nonnegative 0 0) (after_nonnegative 2 0)
  have h10 : 0 ≤ before 0 1 * after 0 0 :=
    mul_nonneg (before_nonnegative 0 1) (after_nonnegative 0 0)
  have h11 : 0 ≤ before 0 1 * after 1 0 :=
    mul_nonneg (before_nonnegative 0 1) (after_nonnegative 1 0)
  have h12 : 0 ≤ before 0 1 * after 2 0 :=
    mul_nonneg (before_nonnegative 0 1) (after_nonnegative 2 0)
  have h20 : 0 ≤ before 0 2 * after 0 0 :=
    mul_nonneg (before_nonnegative 0 2) (after_nonnegative 0 0)
  have h21 : 0 ≤ before 0 2 * after 1 0 :=
    mul_nonneg (before_nonnegative 0 2) (after_nonnegative 1 0)
  have h22 : 0 ≤ before 0 2 * after 2 0 :=
    mul_nonneg (before_nonnegative 0 2) (after_nonnegative 2 0)
  norm_num [score, push, pop, Matrix.mul_apply, Fin.sum_univ_succ]
  nlinarith

theorem blocks_do_not_commute : unitBlock * doubleBlock ≠ doubleBlock * unitBlock := by
  intro commute
  have entry := congrFun (congrFun commute 0) 1
  norm_num [unitBlock, doubleBlock, push, pop, Matrix.mul_apply,
    Fin.sum_univ_succ, pow_succ] at entry

theorem code_scores :
    score codeD = 1 ∧
    score codeA = 372552 ∧
    score codeAHat = 592736996 ∧
    score codeB = 590460360 ∧
    score codeBHat = 939434284388 ∧
    score codeC = 14571576 ∧
    score codeCCheck = 23179095612 ∧
    score codeCHat = 37693915494876 := by
  norm_num [score, codeD, codeA, codeAHat, codeB, codeBHat, codeC, codeCCheck,
    codeCHat, unitBlock, doubleBlock, push, pop, Matrix.mul_apply,
    Matrix.one_apply, Fin.sum_univ_succ, pow_succ]

theorem code_scores_strict_on_covers :
    score codeBHat < score codeCHat ∧
    score codeCCheck < score codeCHat ∧
    score codeAHat < score codeBHat ∧
    score codeB < score codeBHat ∧
    score codeC < score codeCCheck ∧
    score codeA < score codeAHat ∧
    score codeA < score codeB ∧
    score codeD < score codeC ∧
    score codeD < score codeA := by
  rcases code_scores with ⟨d, a, ahat, b, bhat, c, ccheck, chat⟩
  rw [d, a, ahat, b, bhat, c, ccheck, chat]
  norm_num

end DirectedCancellationCountermodel

end MatrixMortality
