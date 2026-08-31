import MatrixMortality.ChangedSeparatorRealization

/-!
# Rank-nine transition powers

The nilpotent chains vanish after their declared lengths; only the geometric tail survives the
third power.
-/

namespace MatrixMortality

open scoped Matrix

namespace ChangedSeparatorRealization

/-- Closed square of the `3+3+2+1` transition. -/
def chainTransitionSquare (ρ V K : ℚ) : Square (Fin 9) ℚ :=
  let s := chainTailEigenvalue ρ V K
  !![0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, s ^ 2]

/-- Closed cube of the `3+3+2+1` transition. -/
def chainTransitionCube (ρ V K : ℚ) : Square (Fin 9) ℚ :=
  let s := chainTailEigenvalue ρ V K
  !![0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, s ^ 3]

/-- The displayed square is the exact second power of the chain transition. -/
theorem chainTransition_pow_two (ρ V K : ℚ) :
    chainTransition ρ V K ^ 2 = chainTransitionSquare ρ V K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, chainTransition, chainTransitionSquare,
      Matrix.mul_apply, Fin.sum_univ_succ]

/-- The displayed cube is the exact third power of the chain transition. -/
theorem chainTransition_pow_three (ρ V K : ℚ) :
    chainTransition ρ V K ^ 3 = chainTransitionCube ρ V K := by
  rw [show (3 : Nat) = 2 + 1 by norm_num, pow_succ,
    chainTransition_pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chainTransition, chainTransitionSquare, chainTransitionCube,
      Matrix.mul_apply, Fin.sum_univ_succ]
  ring

end ChangedSeparatorRealization

end MatrixMortality
