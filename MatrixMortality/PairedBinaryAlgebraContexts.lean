import MatrixMortality.PairedBinaryAlgebra

/-!
# Closed paired-binary context matrices

Short physical contexts around the canonical separator realize the explicit sparse reachable
and observable matrices used by the full-algebra certificate.
-/

namespace MatrixMortality

open scoped Matrix

theorem pairedBinaryAlgebraReachable_eq_closed (β : Nat) (body : List TagLetter) :
    pairedBinaryAlgebraReachable β body =
      pairedBinaryAlgebraReachableClosed β body := by
  rw [pairedBinaryAlgebraReachable, pairedBinaryAlgebraGenerator_eq_closed_fun,
    pairedBinaryAlgebraColumn_eq_closed]
  ext row column
  fin_cases column <;>
    simp [contextColumns, pairedBinaryAlgebraLeftWords, Matrix.vecHead, Matrix.vecTail]
  · fin_cases row <;>
      simp [pairedBinaryAlgebraReachableClosed, pairedBinaryAlgebraColumnClosed,
        Matrix.vecHead, Matrix.vecTail]
  · rw [pairedBinaryAlgebraGeneratorClosed_false_mulVec]
    fin_cases row <;>
      simp [pairedBinaryAlgebraReachableClosed, pairedBinaryAlgebraColumnClosed,
        Matrix.vecHead, Matrix.vecTail]
  · rw [pairedBinaryAlgebraGeneratorClosed_true_mulVec]
    fin_cases row <;>
      simp [pairedBinaryAlgebraReachableClosed, pairedBinaryAlgebraColumnClosed,
        Matrix.vecHead, Matrix.vecTail]
  · rw [← Matrix.mulVec_mulVec]
    rw [pairedBinaryAlgebraGeneratorClosed_false_mulVec]
    rw [pairedBinaryAlgebraGeneratorClosed_false_mulVec]
    fin_cases row <;>
      simp [pairedBinaryAlgebraReachableClosed, pairedBinaryAlgebraColumnClosed,
        Matrix.vecHead, Matrix.vecTail] <;>
      ring
  · rw [← Matrix.mulVec_mulVec]
    rw [pairedBinaryAlgebraGeneratorClosed_false_mulVec]
    rw [pairedBinaryAlgebraGeneratorClosed_true_mulVec]
    fin_cases row <;>
      simp [pairedBinaryAlgebraReachableClosed, pairedBinaryAlgebraColumnClosed,
        Matrix.vecHead, Matrix.vecTail] <;>
      ring
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [pairedBinaryAlgebraGeneratorClosed_false_mulVec]
    rw [pairedBinaryAlgebraGeneratorClosed_false_mulVec]
    rw [pairedBinaryAlgebraGeneratorClosed_false_mulVec]
    fin_cases row <;>
      simp [pairedBinaryAlgebraReachableClosed, pairedBinaryAlgebraColumnClosed,
        Matrix.vecHead, Matrix.vecTail] <;>
      ring

theorem pairedBinaryAlgebraObservable_eq_closed (β : Nat) (body : List TagLetter) :
    pairedBinaryAlgebraObservable β body =
      pairedBinaryAlgebraObservableClosed β body := by
  rw [pairedBinaryAlgebraObservable, pairedBinaryAlgebraGenerator_eq_closed_fun,
    pairedBinaryAlgebraRow_eq]
  ext row column
  fin_cases row <;>
    simp [contextRows, pairedBinaryAlgebraRightWords, Matrix.vecHead, Matrix.vecTail]
  · fin_cases column <;>
      simp [pairedBinaryAlgebraObservableClosed, Matrix.vecHead, Matrix.vecTail]
  · rw [pairedBinaryAlgebraGeneratorClosed_vecMul_false]
    fin_cases column <;>
      simp [pairedBinaryAlgebraObservableClosed, Matrix.vecHead, Matrix.vecTail]
  · rw [pairedBinaryAlgebraGeneratorClosed_vecMul_true]
    fin_cases column <;>
      simp [pairedBinaryAlgebraObservableClosed, Matrix.vecHead, Matrix.vecTail]
  · rw [← Matrix.vecMul_vecMul]
    rw [pairedBinaryAlgebraGeneratorClosed_vecMul_false]
    rw [pairedBinaryAlgebraGeneratorClosed_vecMul_false]
    fin_cases column <;>
      simp [pairedBinaryAlgebraObservableClosed, Matrix.vecHead, Matrix.vecTail]
  · rw [← Matrix.vecMul_vecMul]
    rw [pairedBinaryAlgebraGeneratorClosed_vecMul_false]
    rw [pairedBinaryAlgebraGeneratorClosed_vecMul_true]
    fin_cases column <;>
      simp [pairedBinaryAlgebraObservableClosed, Matrix.vecHead, Matrix.vecTail]
  · rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul]
    rw [pairedBinaryAlgebraGeneratorClosed_vecMul_false]
    rw [pairedBinaryAlgebraGeneratorClosed_vecMul_false]
    rw [pairedBinaryAlgebraGeneratorClosed_vecMul_false]
    fin_cases column <;>
      simp [pairedBinaryAlgebraObservableClosed, Matrix.vecHead, Matrix.vecTail] <;>
      ring

end MatrixMortality
