import MatrixMortality.CubicContinuantSingletonSelector
import MatrixMortality.CubicContinuantMismatchClock

/-!
# Positive terminal-translation lattice in the fixed cubic continuant

The four positive terminal translation blocks generate an explicit additive monoid of rational
shifts. This module packages arbitrary nonnegative count vectors once, including their exact
projective realization, positivity, and physical length.
-/

namespace MatrixMortality.CubicReturn.NonPure

open scoped Matrix

/-- Multiplicities of the four available positive physical terminal-translation blocks. -/
structure ContinuantTerminalTranslationCounts where
  /-- Copies of the false-bit positive translation. -/
  positiveFalse : Nat
  /-- Copies of the false-bit negative translation. -/
  negativeFalse : Nat
  /-- Copies of the true-bit positive translation. -/
  positiveTrue : Nat
  /-- Copies of the true-bit negative translation. -/
  negativeTrue : Nat
  deriving DecidableEq

/-- Positive physical word associated with one terminal-translation count vector. -/
def continuantTerminalTranslationWord
    (counts : ContinuantTerminalTranslationCounts) : List Nat :=
  continuantRepeatWord (continuantReaderPositiveWord false) counts.positiveFalse ++
    (continuantRepeatWord (continuantReaderNegativeWord false) counts.negativeFalse ++
      (continuantRepeatWord (continuantReaderPositiveWord true) counts.positiveTrue ++
        continuantRepeatWord (continuantReaderNegativeWord true) counts.negativeTrue))

/-- Exact rational shift associated with one terminal-translation count vector. -/
def continuantTerminalTranslationShift
    (counts : ContinuantTerminalTranslationCounts) : ℚ :=
  counts.positiveFalse * (2839 / 108) +
    counts.negativeFalse * (-189665 / 144) +
      counts.positiveTrue * (31457 / 6480) +
        counts.negativeTrue * (-266051 / 303750)

/-- Powers of one normalized upper translation add their shifts. -/
theorem continuantDefectTranslation_pow (shift : ℚ) (repetitions : Nat) :
    continuantDefectTranslation shift ^ repetitions =
      continuantDefectTranslation (repetitions * shift) := by
  induction repetitions with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [continuantDefectTranslation, Matrix.one_apply]
  | succ repetitions induction =>
      rw [pow_succ', induction]
      ext i j
      fin_cases i
      · fin_cases j
        · simp [continuantDefectTranslation, Matrix.mul_apply,
            Fin.sum_univ_succ]
        · simp [continuantDefectTranslation, Matrix.mul_apply,
            Fin.sum_univ_succ]
          ring
      · fin_cases j <;>
          simp [continuantDefectTranslation, Matrix.mul_apply,
            Fin.sum_univ_succ]

/-- Every nonnegative count vector realizes its exact summed terminal translation. -/
theorem continuantTerminalTranslationWord_projectivelyRealizes
    (counts : ContinuantTerminalTranslationCounts) :
    continuantProjectivelyRealizes (continuantTerminalTranslationWord counts)
      (continuantDefectTranslation (continuantTerminalTranslationShift counts)) := by
  have positiveFalse :
      continuantProjectivelyRealizes (continuantReaderPositiveWord false)
        (continuantDefectTranslation (2839 / 108)) := by
    simpa [continuantReaderPositive, continuantDefectTranslation] using
      continuantReaderPositiveWord_projectivelyRealizes false
  have negativeFalse :
      continuantProjectivelyRealizes (continuantReaderNegativeWord false)
        (continuantDefectTranslation (-189665 / 144)) := by
    simpa [continuantReaderNegative, continuantDefectTranslation] using
      continuantReaderNegativeWord_projectivelyRealizes false
  have positiveTrue :
      continuantProjectivelyRealizes (continuantReaderPositiveWord true)
        (continuantDefectTranslation (31457 / 6480)) := by
    simpa [continuantReaderPositive, continuantDefectTranslation] using
      continuantReaderPositiveWord_projectivelyRealizes true
  have negativeTrue :
      continuantProjectivelyRealizes (continuantReaderNegativeWord true)
        (continuantDefectTranslation (-266051 / 303750)) := by
    simpa [continuantReaderNegative, continuantDefectTranslation] using
      continuantReaderNegativeWord_projectivelyRealizes true
  have first := continuantProjectivelyRealizes_repeat
    positiveFalse counts.positiveFalse
  have second := continuantProjectivelyRealizes_repeat
    negativeFalse counts.negativeFalse
  have third := continuantProjectivelyRealizes_repeat
    positiveTrue counts.positiveTrue
  have fourth := continuantProjectivelyRealizes_repeat
    negativeTrue counts.negativeTrue
  have combined := continuantProjectivelyRealizes_append first
    (continuantProjectivelyRealizes_append second
      (continuantProjectivelyRealizes_append third fourth))
  have normalized :
      continuantDefectTranslation (2839 / 108) ^ counts.positiveFalse *
          (continuantDefectTranslation (-189665 / 144) ^ counts.negativeFalse *
            (continuantDefectTranslation (31457 / 6480) ^ counts.positiveTrue *
              continuantDefectTranslation (-266051 / 303750) ^ counts.negativeTrue)) =
        continuantDefectTranslation (continuantTerminalTranslationShift counts) := by
    rw [continuantDefectTranslation_pow, continuantDefectTranslation_pow,
      continuantDefectTranslation_pow, continuantDefectTranslation_pow]
    ext i j
    fin_cases i
    · fin_cases j
      · simp [continuantTerminalTranslationShift, continuantDefectTranslation,
          Matrix.mul_apply, Fin.sum_univ_succ]
      · simp [continuantTerminalTranslationShift, continuantDefectTranslation,
          Matrix.mul_apply, Fin.sum_univ_succ]
        ring
    · fin_cases j <;>
        simp [continuantTerminalTranslationShift, continuantDefectTranslation,
          Matrix.mul_apply, Fin.sum_univ_succ]
  rw [normalized] at combined
  simpa only [continuantTerminalTranslationWord] using combined

/-- Every wait in a terminal-translation count-vector word is strictly positive. -/
theorem continuantTerminalTranslationWord_positive
    (counts : ContinuantTerminalTranslationCounts) :
    ∀ wait ∈ continuantTerminalTranslationWord counts, 0 < wait := by
  have positiveFalse :
      ∀ wait ∈ continuantReaderPositiveWord false, 0 < wait := by
    simp [continuantReaderPositiveWord]
  have negativeFalse :
      ∀ wait ∈ continuantReaderNegativeWord false, 0 < wait := by
    simp [continuantReaderNegativeWord]
  have positiveTrue :
      ∀ wait ∈ continuantReaderPositiveWord true, 0 < wait := by
    simp [continuantReaderPositiveWord]
  have negativeTrue :
      ∀ wait ∈ continuantReaderNegativeWord true, 0 < wait := by
    simp [continuantReaderNegativeWord]
  intro wait membership
  simp only [continuantTerminalTranslationWord, List.mem_append] at membership
  rcases membership with first | rest
  · exact continuantRepeatWord_positive
      positiveFalse counts.positiveFalse wait first
  rcases rest with second | rest
  · exact continuantRepeatWord_positive
      negativeFalse counts.negativeFalse wait second
  rcases rest with third | fourth
  · exact continuantRepeatWord_positive positiveTrue counts.positiveTrue wait third
  · exact continuantRepeatWord_positive negativeTrue counts.negativeTrue wait fourth

/-- Exact physical length of a terminal-translation count-vector word. -/
theorem continuantTerminalTranslationWord_length
    (counts : ContinuantTerminalTranslationCounts) :
    (continuantTerminalTranslationWord counts).length =
      30 * counts.positiveFalse + 34 * counts.negativeFalse +
        23 * counts.positiveTrue + 37 * counts.negativeTrue := by
  simp [continuantTerminalTranslationWord, List.length_append,
    continuantRepeatWord_length, continuantReaderPositiveWord,
    continuantReaderNegativeWord]
  omega

end MatrixMortality.CubicReturn.NonPure
