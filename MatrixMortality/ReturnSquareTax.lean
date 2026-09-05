import Mathlib.LinearAlgebra.Matrix.SchurComplement
import MatrixMortality.ReturnSquare

/-!
# Exact state taxes around ReturnSquare

This file owns exact lower bounds for literal arithmetic operations proposed as replacements for
ReturnSquare's one-way squaring rail.
-/

namespace MatrixMortality

open scoped Matrix

namespace ReturnSquareTax

/-- Reversible projective operation exchanging `t` and `κt²`. -/
def stackTransfer {R : Type*} [CommRing R] (κ t : R) : Square (Fin 2) R :=
  !![1 - κ * t, -t;
     -κ, κ * t - 1]

/-- Constant coefficient of `stackTransfer κ t`. -/
def stackConstant {R : Type*} [CommRing R] (κ : R) : Square (Fin 2) R :=
  !![1, 0;
     -κ, -1]

/-- Linear coefficient of `stackTransfer κ t`. -/
def stackLinear {R : Type*} [CommRing R] (κ : R) : Square (Fin 2) R :=
  !![-κ, -1;
     0, κ]

/-- Time-major conversion between a two-time block index and a direct sum of two interfaces. -/
def timeBlockEquiv : Fin 2 × Fin 2 ≃ Fin 2 ⊕ Fin 2 where
  toFun pair := if pair.1 = 0 then Sum.inl pair.2 else Sum.inr pair.2
  invFun
    | Sum.inl state => (0, state)
    | Sum.inr state => (1, state)
  left_inv pair := by
    rcases pair with ⟨time, state⟩
    fin_cases time <;> rfl
  right_inv index := by
    rcases index with state | state <;> rfl

/-- Two-time block Hankel section of the reversible stack operation. -/
def stackHankel {R : Type*} [CommRing R] (q κ : R) :
    Square (Fin 2 ⊕ Fin 2) R :=
  Matrix.fromBlocks
    (stackTransfer κ 1) (stackTransfer κ q)
    (stackTransfer κ q) (stackTransfer κ (q ^ 2))

/-- Block Vandermonde factor for the two spectral modes `1,t`. -/
def stackVandermonde {R : Type*} [CommRing R] (q : R) :
    Square (Fin 2 ⊕ Fin 2) R :=
  Matrix.fromBlocks 1 1 1 (q • (1 : Square (Fin 2) R))

/-- Block diagonal matrix of the two coefficient matrices. -/
def stackCoefficientBlock {R : Type*} [CommRing R] (κ : R) :
    Square (Fin 2 ⊕ Fin 2) R :=
  Matrix.fromBlocks (stackConstant κ) 0 0 (stackLinear κ)

/-- The reversible stack operation has exactly the two advertised spectral coefficients. -/
theorem stackTransfer_eq {R : Type*} [CommRing R] (κ t : R) :
    stackTransfer κ t = stackConstant κ + t • stackLinear κ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stackTransfer, stackConstant, stackLinear]
  all_goals ring

/-- Exact block-Hankel factorization through the two coefficient matrices. -/
theorem stackHankel_factor {R : Type*} [CommRing R] (q κ : R) :
    stackHankel q κ =
      stackVandermonde q * stackCoefficientBlock κ * stackVandermonde q := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [stackHankel, stackVandermonde, stackCoefficientBlock,
      Matrix.fromBlocks_multiply, stackTransfer_eq]
  all_goals ring

/-- Constant coefficient is nonsingular with determinant `-1`. -/
theorem stackConstant_det {R : Type*} [CommRing R] (κ : R) :
    (stackConstant κ).det = -1 := by
  rw [Matrix.det_fin_two]
  simp [stackConstant]

/-- Linear coefficient is nonsingular whenever `κ` is, with determinant `-κ²`. -/
theorem stackLinear_det {R : Type*} [CommRing R] (κ : R) :
    (stackLinear κ).det = -(κ ^ 2) := by
  rw [Matrix.det_fin_two]
  simp [stackLinear]
  ring

/-- Determinant of the two-time block Vandermonde factor. -/
theorem stackVandermonde_det {R : Type*} [CommRing R] (q : R) :
    (stackVandermonde q).det = (q - 1) ^ 2 := by
  rw [stackVandermonde, Matrix.det_fromBlocks_one₁₁, Matrix.det_fin_two]
  simp
  ring

/-- Determinant of the block-diagonal coefficient factor. -/
theorem stackCoefficientBlock_det {R : Type*} [CommRing R] (κ : R) :
    (stackCoefficientBlock κ).det = κ ^ 2 := by
  rw [stackCoefficientBlock, Matrix.det_fromBlocks_zero₂₁,
    stackConstant_det, stackLinear_det]
  ring

/-- The reversible stack operation's two-time block Hankel determinant. -/
theorem stackHankel_det {R : Type*} [CommRing R] (q κ : R) :
    (stackHankel q κ).det = κ ^ 2 * (q - 1) ^ 4 := by
  rw [stackHankel_factor, Matrix.det_mul, Matrix.det_mul,
    stackVandermonde_det, stackCoefficientBlock_det]
  ring

/-- The abstract two-time return Hankel section is the displayed block matrix. -/
theorem finiteReturnHankel_reindex {R : Type*} [CommRing R] (q κ : R) :
    Matrix.reindex timeBlockEquiv timeBlockEquiv
        (ReturnFamily.finiteReturnHankel
          (fun n => stackTransfer κ (q ^ n))
          (fun time : Fin 2 => time.val) (fun time : Fin 2 => time.val)) =
      stackHankel q κ := by
  ext left right
  rcases left with left | left <;> rcases right with right | right <;>
    fin_cases left <;> fin_cases right <;>
      simp [Matrix.reindex_apply, Matrix.submatrix, timeBlockEquiv,
        ReturnFamily.finiteReturnHankel, stackHankel]

/-- Determinant of the abstract two-time return Hankel section. -/
theorem finiteReturnHankel_det {R : Type*} [CommRing R] (q κ : R) :
    (ReturnFamily.finiteReturnHankel
      (fun n => stackTransfer κ (q ^ n))
      (fun time : Fin 2 => time.val) (fun time : Fin 2 => time.val)).det =
        κ ^ 2 * (q - 1) ^ 4 := by
  rw [← stackHankel_det q κ, ← finiteReturnHankel_reindex]
  exact (Matrix.det_reindex_self timeBlockEquiv _).symm

/-- Literal reversible push/pop requires at least four ambient states in every exact return
realization. -/
theorem reversibleStack_card_lower_bound
    {K State : Type*} [Field K]
    [Fintype State] [DecidableEq State]
    (q κ : K) (ambient : Square State K)
    (input : Matrix State (Fin 2) K) (output : Matrix (Fin 2) State K)
    (exact :
      ∀ n, ReturnFamily.returnMatrix ambient input output n = stackTransfer κ (q ^ n))
    (q_ne_one : q ≠ 1) (κ_ne_zero : κ ≠ 0) :
    4 ≤ Fintype.card State := by
  have series_eq :
      ReturnFamily.returnMatrix ambient input output =
        fun n => stackTransfer κ (q ^ n) := by
    funext n
    exact exact n
  have det_ne :
      (ReturnFamily.finiteReturnHankel
        (ReturnFamily.returnMatrix ambient input output)
        (fun time : Fin 2 => time.val) (fun time : Fin 2 => time.val)).det ≠ 0 := by
    rw [series_eq, finiteReturnHankel_det]
    exact mul_ne_zero (pow_ne_zero 2 κ_ne_zero) (pow_ne_zero 4 (sub_ne_zero.mpr q_ne_one))
  simpa using
    ReturnFamily.returnHankel_card_le ambient input output
      (fun time : Fin 2 => time.val) (fun time : Fin 2 => time.val) det_ne

end ReturnSquareTax

end MatrixMortality
