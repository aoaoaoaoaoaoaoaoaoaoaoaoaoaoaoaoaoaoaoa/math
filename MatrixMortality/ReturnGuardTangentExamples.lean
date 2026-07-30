import MatrixMortality.ReturnGuardExamples
import MatrixMortality.ReturnGuardTangent

/-!
# Tangent-cocycle examples

The checked rational period-three guard also closes projectively after cancellation blow-up.
This is a canonical-reset orbit, not an arbitrary tangent input.  Consequently no scalar height
which strictly descends on every tangent step can decide the guard before fixed parameter-prime
cancellation has been separated.
-/

namespace MatrixMortality.ReturnGuard.Examples

open scoped Matrix

noncomputable section

/-- Tangent coordinates after the wait-one leg of the rational three-cycle. -/
def cycleTangentZero : Fin 2 → ℤ :=
  cancellationTangent (3 ^ (2 * 1) : ℤ) 5 17

/-- Tangent coordinates after the wait-two leg of the rational three-cycle. -/
def cycleTangentOne : Fin 2 → ℤ :=
  cancellationTangent (3 ^ (2 * 2) : ℤ) 43 283

/-- Tangent coordinates after the wait-three leg of the rational three-cycle. -/
def cycleTangentTwo : Fin 2 → ℤ :=
  cancellationTangent (3 ^ (2 * 3) : ℤ) 1 1

theorem cycleTangentZero_eq :
    cycleTangentZero = ![17, 28] := by
  norm_num [cycleTangentZero, cancellationTangent]

theorem cycleTangentOne_eq :
    cycleTangentOne = ![283, 3200] := by
  norm_num [cycleTangentOne, cancellationTangent]

theorem cycleTangentTwo_eq :
    cycleTangentTwo = ![1, 728] := by
  norm_num [cycleTangentTwo, cancellationTangent]

/-- The first tangent leg removes the primitive-reduction scalar `−28`, in addition to the
preceding depth power `9`. -/
theorem cycle_tangent_step_zero :
    tangentTransfer (-953 : ℤ) 473 2240 9 9 *ᵥ cycleTangentZero =
      (-252 : ℤ) • cycleTangentOne := by
  ext i
  fin_cases i <;>
    norm_num [cycleTangentZero, cycleTangentOne, cancellationTangent,
      tangentTransfer, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ]

/-- The second tangent leg removes `81 · (−3440)`. -/
theorem cycle_tangent_step_one :
    tangentTransfer (-953 : ℤ) 473 2240 81 27 *ᵥ cycleTangentOne =
      (-278640 : ℤ) • cycleTangentTwo := by
  ext i
  fin_cases i <;>
    norm_num [cycleTangentOne, cycleTangentTwo, cancellationTangent,
      tangentTransfer, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ]

/-- The third tangent leg removes `729 · (−160)` and closes the projective tangent cycle. -/
theorem cycle_tangent_step_two :
    tangentTransfer (-953 : ℤ) 473 2240 729 3 *ᵥ cycleTangentTwo =
      (-116640 : ℤ) • cycleTangentZero := by
  ext i
  fin_cases i <;>
    norm_num [cycleTangentTwo, cycleTangentZero, cancellationTangent,
      tangentTransfer, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ]

/-- All three tangent normalization scalars are nonzero, so the displayed identities form a
genuine projective three-cycle rather than an annihilating orbit. -/
theorem cycle_tangent_scalars_nonzero :
    (-252 : ℤ) ≠ 0 ∧ (-278640 : ℤ) ≠ 0 ∧ (-116640 : ℤ) ≠ 0 := by
  norm_num

end
end MatrixMortality.ReturnGuard.Examples
