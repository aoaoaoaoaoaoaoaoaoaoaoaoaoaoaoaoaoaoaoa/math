import MatrixMortality.ChangedSeparatorMomentThree

/-!
# Rank-nine geometric tail moments

After the third return, only the geometric tail line survives. Every later return is therefore
the same changed separator multiplied by the corresponding power of its nonzero eigenvalue.
-/

namespace MatrixMortality

open scoped Matrix

namespace ChangedSeparatorRealization

/-- The transition scales its surviving cube on the right by the tail eigenvalue. -/
theorem chainTransitionCube_mul_chainTransition (ρ V K : ℚ) :
    chainTransitionCube ρ V K * chainTransition ρ V K =
      chainTailEigenvalue ρ V K • chainTransitionCube ρ V K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chainTransitionCube, chainTransition, chainTailEigenvalue,
      Matrix.mul_apply, Fin.sum_univ_succ]
  ring

/-- Every further transition step scales the surviving cube geometrically. -/
theorem chainTransitionCube_mul_pow (ρ V K : ℚ) (n : Nat) :
    chainTransitionCube ρ V K * chainTransition ρ V K ^ n =
      chainTailEigenvalue ρ V K ^ n • chainTransitionCube ρ V K := by
  induction n with
  | zero => simp
  | succ n induction =>
      rw [pow_succ, ← Matrix.mul_assoc, induction, Matrix.smul_mul,
        chainTransitionCube_mul_chainTransition, smul_smul, ← pow_succ]

/-- The complete power sequence is geometric from time three onward. -/
theorem chainTransition_pow_add_three (ρ V K : ℚ) (n : Nat) :
    chainTransition ρ V K ^ (n + 3) =
      chainTailEigenvalue ρ V K ^ n • chainTransitionCube ρ V K := by
  rw [Nat.add_comm n 3, pow_add, chainTransition_pow_three,
    chainTransitionCube_mul_pow]

/-- Every generic return from time three onward is a scaled changed separator. -/
theorem chain_moment_add_three (ρ V K : ℚ) (regular : RegularChart ρ V K)
    (n : Nat) :
    chainOutput ρ V K * chainTransition ρ V K ^ (n + 3) * chainInput ρ V K =
      chainTailEigenvalue ρ V K ^ n • chainTailSeparator ρ V K := by
  rw [chainTransition_pow_add_three, Matrix.mul_smul, Matrix.smul_mul,
    chain_moment_three ρ V K regular]

/-- Every specialized return from time three onward is a nonzero separator scaling. -/
theorem moment_add_three (β : Nat) (β_pos : 0 < β) (body : List TagLetter)
    (b_mem : .b ∈ body) (n : Nat) :
    output β body * transition β body ^ (n + 3) * input β body =
      tailEigenvalue β body ^ n • separator β body := by
  simpa [output, transition, input, tailEigenvalue, separator] using
    chain_moment_add_three (widthScale β) (ChangedSeparatorTail.lowerCCode β body)
      (ChangedSeparatorTail.lowerCScale β body) (regularChart β β_pos body b_mem) n

end ChangedSeparatorRealization

end MatrixMortality
