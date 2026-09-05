import MatrixMortality.SingularReturnFamily

/-!
# Two length-three chains with a static state and an eigenline

The eight coordinates have sizes `2+2+2+1+1`. The first six form two length-three shift chains;
the seventh vanishes at the first step, and the last scales by `eigenvalue`. The factors expose
the three exceptional return moments without a basis-selection algorithm.
-/

namespace MatrixMortality.ThreeStepRealization

open scoped Matrix

/-- Two nilpotent length-three chains, one zero block, and one scalar block. -/
def transition {R : Type*} [Zero R] [One R] (eigenvalue : R) : Square (Fin 8) R :=
  !![0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, eigenvalue]

/-- The input feeds each nilpotent depth and the two one-dimensional states. -/
def input {R κ : Type*} (Q₀ Q₁ Q₂ : Matrix (Fin 2) κ R)
    (staticRow tailRow : κ → R) : Matrix (Fin 8) κ R :=
  Matrix.of ![Q₂ 0, Q₂ 1, Q₁ 0, Q₁ 1, Q₀ 0, Q₀ 1, staticRow, tailRow]

/-- The output reads each depth, the static state, and the surviving eigenline. -/
def output {R κ : Type*} (L₀ L₁ L₂ : Matrix κ (Fin 2) R)
    (staticColumn tailColumn : κ → R) : Matrix κ (Fin 8) R :=
  Matrix.of fun row => ![L₀ row 0, L₀ row 1, L₁ row 0, L₁ row 1,
    L₂ row 0, L₂ row 1, staticColumn row, tailColumn row]

section Moments

variable {R κ : Type*} [CommSemiring R]
  (eigenvalue : R) (L₀ L₁ L₂ : Matrix κ (Fin 2) R)
  (Q₀ Q₁ Q₂ : Matrix (Fin 2) κ R)
  (staticColumn tailColumn staticRow tailRow : κ → R)

/-- The zeroth return contains all three transient factors and both outer products. -/
theorem moment_zero :
    output L₀ L₁ L₂ staticColumn tailColumn * input Q₀ Q₁ Q₂ staticRow tailRow =
      L₀ * Q₂ + L₁ * Q₁ + L₂ * Q₀ + Matrix.vecMulVec staticColumn staticRow +
        Matrix.vecMulVec tailColumn tailRow := by
  ext row column
  simp [output, input, Matrix.mul_apply, Matrix.add_apply, Matrix.vecMulVec,
    Fin.sum_univ_succ]
  ring

/-- One transition removes the first depth and the static state. -/
theorem moment_one :
    output L₀ L₁ L₂ staticColumn tailColumn * transition eigenvalue *
        input Q₀ Q₁ Q₂ staticRow tailRow =
      L₁ * Q₂ + L₂ * Q₁ + eigenvalue • Matrix.vecMulVec tailColumn tailRow := by
  ext row column
  simp [output, input, transition, Matrix.mul_apply, Matrix.add_apply, Matrix.vecMulVec,
    Fin.sum_univ_succ, smul_eq_mul]
  ring

/-- Two transitions leave only the final nilpotent pairing and the eigenline. -/
theorem moment_two :
    output L₀ L₁ L₂ staticColumn tailColumn * transition eigenvalue ^ 2 *
        input Q₀ Q₁ Q₂ staticRow tailRow =
      L₂ * Q₂ + eigenvalue ^ 2 • Matrix.vecMulVec tailColumn tailRow := by
  ext row column
  simp [pow_succ, output, input, transition, Matrix.mul_apply, Matrix.add_apply,
    Matrix.vecMulVec, Fin.sum_univ_succ, smul_eq_mul]
  ring

/-- The third power has only its final diagonal entry. -/
theorem transition_cube :
    transition eigenvalue ^ 3 = Matrix.diagonal ![0, 0, 0, 0, 0, 0, 0, eigenvalue ^ 3] := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [pow_succ, transition, Matrix.mul_apply, Matrix.diagonal, Fin.sum_univ_succ]

/-- At time three, both nilpotent chains and the static state have vanished. -/
theorem moment_three :
    output L₀ L₁ L₂ staticColumn tailColumn * transition eigenvalue ^ 3 *
        input Q₀ Q₁ Q₂ staticRow tailRow =
      eigenvalue ^ 3 • Matrix.vecMulVec tailColumn tailRow := by
  rw [transition_cube]
  ext row column
  simp [output, input, Matrix.mul_apply, Matrix.diagonal, Matrix.vecMulVec,
    Fin.sum_univ_succ, smul_eq_mul]
  ring

/-- After the transient, multiplication by the transition is scalar multiplication. -/
theorem transition_pow_four :
    transition eigenvalue ^ 4 = eigenvalue • transition eigenvalue ^ 3 := by
  rw [show 4 = 3 + 1 from rfl, pow_succ, transition_cube]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [transition, Matrix.mul_apply, Matrix.diagonal, smul_eq_mul,
      mul_comm]

/-- Every power after time three is a nonnegative power of the same scalar times the cube. -/
theorem transition_pow_add_three (n : Nat) :
    transition eigenvalue ^ (n + 3) = eigenvalue ^ n • transition eigenvalue ^ 3 := by
  induction n with
  | zero => simp
  | succ n induction =>
      calc
        transition eigenvalue ^ (n + 1 + 3) =
            transition eigenvalue ^ (n + 3) * transition eigenvalue := by
          rw [show n + 1 + 3 = (n + 3) + 1 by omega, pow_succ]
        _ = (eigenvalue ^ n • transition eigenvalue ^ 3) * transition eigenvalue := by
          rw [induction]
        _ = eigenvalue ^ n • transition eigenvalue ^ 4 := by
          rw [Matrix.smul_mul, ← pow_succ]
        _ = eigenvalue ^ (n + 1) • transition eigenvalue ^ 3 := by
          rw [transition_pow_four, smul_smul, pow_succ eigenvalue n]

/-- The complete return tail, not merely finitely many checked moments. -/
theorem moment_add_three (n : Nat) :
    output L₀ L₁ L₂ staticColumn tailColumn * transition eigenvalue ^ (n + 3) *
        input Q₀ Q₁ Q₂ staticRow tailRow =
      eigenvalue ^ (n + 3) • Matrix.vecMulVec tailColumn tailRow := by
  rw [transition_pow_add_three, Matrix.mul_smul, Matrix.smul_mul, moment_three,
    smul_smul, pow_add]

/-- The last coordinate records the scalar power even before the transient vanishes. -/
theorem transition_pow_last (n : Nat) :
    (transition eigenvalue ^ n) 7 7 = eigenvalue ^ n := by
  have last_column (index : Fin 8) :
      transition eigenvalue index 7 = if index = 7 then eigenvalue else 0 := by
    fin_cases index <;> simp [transition]
  induction n with
  | zero => simp
  | succ n induction =>
      rw [pow_succ, Matrix.mul_apply]
      simp [last_column, induction, pow_succ]

end Moments

/-- A nonzero eigenline excludes every pure-transition zero word. -/
theorem transition_pow_ne_zero {R : Type*} [CommSemiring R] [Nontrivial R]
    [NoZeroDivisors R] (eigenvalue : R) (eigenvalue_ne_zero : eigenvalue ≠ 0) (n : Nat) :
    transition eigenvalue ^ n ≠ 0 := by
  intro zero
  have last_zero := congrArg (fun matrix : Square (Fin 8) R => matrix 7 7) zero
  have scalar_zero : eigenvalue ^ n = 0 := by
    simpa [transition_pow_last] using last_zero
  exact pow_ne_zero n eigenvalue_ne_zero scalar_zero

/-- The eight-state realization has no unaccounted exterior transition words. -/
theorem physical_mortality_iff {R κ : Type*} [CommSemiring R] [Nontrivial R]
    [NoZeroDivisors R] [Fintype κ] [DecidableEq κ]
    (eigenvalue : R) (eigenvalue_ne_zero : eigenvalue ≠ 0)
    (reader : Matrix κ (Fin 8) R) (writer : Matrix (Fin 8) κ R) :
    IsMortal (ReturnFamily.pairGenerator (transition eigenvalue) (writer * reader)) ↔
      IsMortal (ReturnFamily.returnMatrix (transition eigenvalue) writer reader) :=
  ReturnFamily.pairGenerator_isMortal_iff_returnFamily (transition eigenvalue) writer reader
    (transition_pow_ne_zero eigenvalue eigenvalue_ne_zero)

end MatrixMortality.ThreeStepRealization
