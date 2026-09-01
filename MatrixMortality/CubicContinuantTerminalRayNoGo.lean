import MatrixMortality.CubicContinuantFreeSourceStabilizer
import MatrixMortality.CubicContinuantMacroNormalForm
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# A 17-adic obstruction to transported transverse readers

This file defines the exact segmented terminal grammar currently available to the cubic
continuant construction: positive physical radix writers and readers, interleaved with arbitrary
nonnegative count vectors of the four terminal translation blocks.  Every such terminal product
has diagonal ratio a power of `4/25`.  The fixed ray connector contributes the uncancellable
factor `9/340`, of 17-adic valuation `-1`; both desired inverse transverse pump ratios have
valuation zero.  Thus this entire grammar cannot realize either inverse pump letter.
-/

namespace MatrixMortality.CubicReturn.NonPure

open scoped Matrix

local instance terminalRayPrime17 : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- One segment in the currently available terminal grammar. -/
inductive ContinuantTerminalRayMacro
  /-- A positive physical radix writer or reader. -/
  | radix (operation : ContinuantRadixMacro)
  /-- Any nonnegative count vector of the four positive terminal translations. -/
  | translation (counts : ContinuantTerminalTranslationCounts)

/-- Normalized terminal matrix of one grammar segment. -/
def continuantTerminalRayMacroMatrix :
    ContinuantTerminalRayMacro → Square (Fin 2) ℚ
  | .radix operation => continuantRadixMacroMatrix operation
  | .translation counts =>
      continuantDefectTranslation (continuantTerminalTranslationShift counts)

/-- Positive physical spelling of one terminal grammar segment. -/
def continuantTerminalRayMacroWord : ContinuantTerminalRayMacro → List Nat
  | .radix operation => continuantRadixMacroWord operation
  | .translation counts => continuantTerminalTranslationWord counts

/-- Flatten a segmented terminal program into its positive physical wait word. -/
def continuantTerminalRayEncoding
    (program : List ContinuantTerminalRayMacro) : List Nat :=
  program.flatMap continuantTerminalRayMacroWord

/-- Signed radix height of one terminal segment; translations have height zero. -/
def continuantTerminalRayMacroHeight : ContinuantTerminalRayMacro → ℤ
  | .radix operation => continuantRadixMacroHeight operation
  | .translation _ => 0

/-- Total signed radix height of a segmented terminal program. -/
def continuantTerminalRayHeight
    (program : List ContinuantTerminalRayMacro) : ℤ :=
  (program.map continuantTerminalRayMacroHeight).sum

/-- Every terminal grammar segment has its displayed normalized physical realization. -/
theorem continuantTerminalRayMacroWord_projectivelyRealizes
    (segment : ContinuantTerminalRayMacro) :
    continuantProjectivelyRealizes (continuantTerminalRayMacroWord segment)
      (continuantTerminalRayMacroMatrix segment) := by
  cases segment with
  | radix operation =>
      exact continuantRadixMacroWord_projectivelyRealizes operation
  | translation counts =>
      exact continuantTerminalTranslationWord_projectivelyRealizes counts

/-- Every terminal grammar program physically realizes its normalized segmented product. -/
theorem continuantTerminalRayEncoding_projectivelyRealizes
    (program : List ContinuantTerminalRayMacro) :
    continuantProjectivelyRealizes (continuantTerminalRayEncoding program)
      (wordProduct continuantTerminalRayMacroMatrix program) := by
  induction program with
  | nil =>
      refine ⟨1, one_ne_zero, ?_⟩
      simp [continuantTerminalRayEncoding]
  | cons segment program induction =>
      rw [continuantTerminalRayEncoding, List.flatMap_cons]
      exact continuantProjectivelyRealizes_append
        (continuantTerminalRayMacroWord_projectivelyRealizes segment) induction

/-- Every physical wait in the segmented terminal grammar is strictly positive. -/
theorem continuantTerminalRayEncoding_positive
    (program : List ContinuantTerminalRayMacro) :
    ∀ wait ∈ continuantTerminalRayEncoding program, 0 < wait := by
  intro wait membership
  obtain ⟨segment, _, wait_mem⟩ := List.mem_flatMap.mp membership
  cases segment with
  | radix operation =>
      exact continuantRadixMacroEncoding_positive [operation] wait (by
        simpa [continuantRadixMacroEncoding,
          continuantTerminalRayMacroWord] using wait_mem)
  | translation counts =>
      exact continuantTerminalTranslationWord_positive counts wait wait_mem

private theorem terminalRayRatio_ne_zero : (4 / 25 : ℚ) ≠ 0 := by norm_num

private theorem continuantTerminalRayMacro_entries
    (segment : ContinuantTerminalRayMacro) :
    continuantTerminalRayMacroMatrix segment 0 0 =
        (4 / 25 : ℚ) ^ continuantTerminalRayMacroHeight segment ∧
      continuantTerminalRayMacroMatrix segment 1 0 = 0 ∧
      continuantTerminalRayMacroMatrix segment 1 1 = 1 := by
  cases segment with
  | radix operation =>
      cases operation with
      | writer bit =>
          norm_num [continuantTerminalRayMacroMatrix,
            continuantTerminalRayMacroHeight, continuantRadixMacroMatrix,
            continuantRadixMacroHeight, continuantRadixMacroRatio]
      | reader bit =>
          norm_num [continuantTerminalRayMacroMatrix,
            continuantTerminalRayMacroHeight, continuantRadixMacroMatrix,
            continuantRadixMacroHeight, continuantRadixMacroRatio]
  | translation counts =>
      norm_num [continuantTerminalRayMacroMatrix,
        continuantTerminalRayMacroHeight, continuantDefectTranslation]

/-- Exact diagonal normal form of every segmented terminal product. -/
theorem continuantTerminalRayProduct_entries
    (program : List ContinuantTerminalRayMacro) :
    (wordProduct continuantTerminalRayMacroMatrix program) 0 0 =
        (4 / 25 : ℚ) ^ continuantTerminalRayHeight program ∧
      (wordProduct continuantTerminalRayMacroMatrix program) 1 0 = 0 ∧
      (wordProduct continuantTerminalRayMacroMatrix program) 1 1 = 1 := by
  induction program with
  | nil =>
      norm_num [continuantTerminalRayHeight, Matrix.one_apply]
  | cons segment program induction =>
      rcases continuantTerminalRayMacro_entries segment with
        ⟨head_upper, head_lower, head_diagonal⟩
      rcases induction with ⟨tail_upper, tail_lower, tail_diagonal⟩
      constructor
      · rw [wordProduct_cons, Matrix.mul_apply]
        simp [Fin.sum_univ_succ, head_upper, tail_upper, tail_lower,
          continuantTerminalRayHeight, List.map_cons, List.sum_cons,
          zpow_add₀ terminalRayRatio_ne_zero]
      constructor
      · rw [wordProduct_cons, Matrix.mul_apply]
        simp [Fin.sum_univ_succ, head_lower, tail_lower]
      · rw [wordProduct_cons, Matrix.mul_apply]
        simp [Fin.sum_univ_succ, head_lower, head_diagonal, tail_diagonal]

private theorem terminalRayVal17_unit
    (value : ℕ) (not_dvd : ¬17 ∣ value) :
    padicValRat 17 (value : ℚ) = 0 := by
  rw [padicValRat.of_nat]
  exact_mod_cast padicValNat.eq_zero_of_not_dvd not_dvd

private theorem terminalRayBase_val17 :
    padicValRat 17 (4 / 25 : ℚ) = 0 := by
  have numerator : padicValRat 17 (4 : ℚ) = 0 := by
    simpa using terminalRayVal17_unit 4 (by norm_num)
  have denominator : padicValRat 17 (25 : ℚ) = 0 := by
    simpa using terminalRayVal17_unit 25 (by norm_num)
  rw [padicValRat.div (by norm_num) (by norm_num), numerator, denominator]
  norm_num

private theorem terminalRayBase_zpow_val17 (height : ℤ) :
    padicValRat 17 ((4 / 25 : ℚ) ^ height) = 0 := by
  cases height with
  | ofNat exponent =>
      change padicValRat 17 ((4 / 25 : ℚ) ^ exponent) = 0
      rw [padicValRat.pow, terminalRayBase_val17]
      norm_num
  | negSucc exponent =>
      rw [zpow_negSucc, padicValRat.inv, padicValRat.pow,
        terminalRayBase_val17]
      norm_num

private theorem terminalRayConnector_val17 :
    padicValRat 17 (9 / 340 : ℚ) = -1 := by
  have numerator : padicValRat 17 (9 : ℚ) = 0 := by
    simpa using terminalRayVal17_unit 9 (by norm_num)
  have factor : padicValRat 17 (17 : ℚ) = 1 :=
    padicValRat.self (p := 17) (by norm_num)
  have cofactor : padicValRat 17 (20 : ℚ) = 0 := by
    simpa using terminalRayVal17_unit 20 (by norm_num)
  have denominator : padicValRat 17 (340 : ℚ) = 1 := by
    rw [show (340 : ℚ) = 17 * 20 by norm_num,
      padicValRat.mul (by norm_num) (by norm_num), factor, cofactor]
    norm_num
  rw [padicValRat.div (by norm_num) (by norm_num), numerator, denominator]
  norm_num

/-- The transported transverse ratio of every current terminal program has 17-adic valuation
exactly `-1`. -/
theorem continuantTerminalRayTransportRatio_val17
    (program : List ContinuantTerminalRayMacro) :
    padicValRat 17
        (falseWaitFirstHitRayTransportNormalized
          ((wordProduct continuantTerminalRayMacroMatrix program) 0 0)
          ((wordProduct continuantTerminalRayMacroMatrix program) 0 1)
          ((wordProduct continuantTerminalRayMacroMatrix program) 1 1) 1 1) = -1 := by
  rcases continuantTerminalRayProduct_entries program with
    ⟨upper, _, lower⟩
  have upper_ne : (4 / 25 : ℚ) ^ continuantTerminalRayHeight program ≠ 0 :=
    zpow_ne_zero _ terminalRayRatio_ne_zero
  rw [falseWaitFirstHitRayTransportNormalized, upper, lower]
  change padicValRat 17
    ((9 / 340 : ℚ) * (1 / (4 / 25 : ℚ) ^ continuantTerminalRayHeight program)) = -1
  rw [
    padicValRat.mul (by norm_num) (div_ne_zero (by norm_num) upper_ne),
    terminalRayConnector_val17,
    padicValRat.div (by norm_num) upper_ne, padicValRat.one,
    terminalRayBase_zpow_val17]
  norm_num

private theorem terminalRayInverseFalse_val17 :
    padicValRat 17 (625 : ℚ) = 0 := by
  simpa using terminalRayVal17_unit 625 (by norm_num)

private theorem terminalRayInverseTrue_val17 :
    padicValRat 17 (336000 / 197 : ℚ) = 0 := by
  have numerator : padicValRat 17 (336000 : ℚ) = 0 := by
    simpa using terminalRayVal17_unit 336000 (by norm_num)
  have denominator : padicValRat 17 (197 : ℚ) = 0 := by
    simpa using terminalRayVal17_unit 197 (by norm_num)
  rw [padicValRat.div (by norm_num) (by norm_num), numerator, denominator]
  norm_num

/-- No positive segmented terminal program transports to the inverse false pump ratio. -/
theorem continuantTerminalRayTransportRatio_ne_inverseFalse
    (program : List ContinuantTerminalRayMacro) :
    falseWaitFirstHitRayTransportNormalized
        ((wordProduct continuantTerminalRayMacroMatrix program) 0 0)
        ((wordProduct continuantTerminalRayMacroMatrix program) 0 1)
        ((wordProduct continuantTerminalRayMacroMatrix program) 1 1) 1 1 ≠ 625 := by
  intro ratio_eq
  have valuation_eq := congrArg (padicValRat 17) ratio_eq
  rw [continuantTerminalRayTransportRatio_val17,
    terminalRayInverseFalse_val17] at valuation_eq
  omega

/-- No positive segmented terminal program transports to the inverse true pump ratio. -/
theorem continuantTerminalRayTransportRatio_ne_inverseTrue
    (program : List ContinuantTerminalRayMacro) :
    falseWaitFirstHitRayTransportNormalized
        ((wordProduct continuantTerminalRayMacroMatrix program) 0 0)
        ((wordProduct continuantTerminalRayMacroMatrix program) 0 1)
        ((wordProduct continuantTerminalRayMacroMatrix program) 1 1) 1 1 ≠
      336000 / 197 := by
  intro ratio_eq
  have valuation_eq := congrArg (padicValRat 17) ratio_eq
  rw [continuantTerminalRayTransportRatio_val17,
    terminalRayInverseTrue_val17] at valuation_eq
  omega

/-- No transported current-terminal program is a projective left inverse of either transverse
pump letter. -/
theorem continuantTerminalRayTransport_mul_pump_not_projectiveIdentity
    (program : List ContinuantTerminalRayMacro) (bit : Bool) (scale : ℚ) :
    falseWaitFirstHitRayTransportNormalized
          ((wordProduct continuantTerminalRayMacroMatrix program) 0 0)
          ((wordProduct continuantTerminalRayMacroMatrix program) 0 1)
          ((wordProduct continuantTerminalRayMacroMatrix program) 1 1) *
        falseWaitFirstHitBinaryNormalizedLoop bit ≠
      scale • (1 : Square (Fin 2) ℚ) := by
  intro projective_identity
  have upper := congrFun (congrFun projective_identity 0) 0
  have lower := congrFun (congrFun projective_identity 1) 1
  have scale_eq : scale = 1 := by
    simpa [falseWaitFirstHitRayTransportNormalized,
      falseWaitFirstHitBinaryNormalizedLoop, Matrix.mul_apply,
      Matrix.one_apply, Matrix.smul_apply, Fin.sum_univ_succ] using upper.symm
  cases bit
  · have inverse_ratio :
        falseWaitFirstHitRayTransportNormalized
            ((wordProduct continuantTerminalRayMacroMatrix program) 0 0)
            ((wordProduct continuantTerminalRayMacroMatrix program) 0 1)
            ((wordProduct continuantTerminalRayMacroMatrix program) 1 1) 1 1 =
          625 := by
      rw [scale_eq] at lower
      norm_num [falseWaitFirstHitRayTransportNormalized,
        falseWaitFirstHitBinaryNormalizedLoop,
        falseWaitFirstHitBinaryRatio, Matrix.mul_apply,
        Matrix.one_apply, Matrix.smul_apply, Fin.sum_univ_succ] at lower ⊢
      linarith
    exact continuantTerminalRayTransportRatio_ne_inverseFalse program inverse_ratio
  · have inverse_ratio :
        falseWaitFirstHitRayTransportNormalized
            ((wordProduct continuantTerminalRayMacroMatrix program) 0 0)
            ((wordProduct continuantTerminalRayMacroMatrix program) 0 1)
            ((wordProduct continuantTerminalRayMacroMatrix program) 1 1) 1 1 =
          336000 / 197 := by
      rw [scale_eq] at lower
      norm_num [falseWaitFirstHitRayTransportNormalized,
        falseWaitFirstHitBinaryNormalizedLoop,
        falseWaitFirstHitBinaryRatio, Matrix.mul_apply,
        Matrix.one_apply, Matrix.smul_apply, Fin.sum_univ_succ] at lower ⊢
      linarith
    exact continuantTerminalRayTransportRatio_ne_inverseTrue program inverse_ratio

end MatrixMortality.CubicReturn.NonPure
