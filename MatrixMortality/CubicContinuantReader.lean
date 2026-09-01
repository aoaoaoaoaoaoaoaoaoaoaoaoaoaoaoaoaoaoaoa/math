import MatrixMortality.CubicContinuantRadix

/-!
# Positive readers for the cubic continuant radix stack

The terminal loop semigroup of the false-wait cubic family contains affine translations of
both signs. Combining two such translations with a loop of reciprocal diagonal ratio produces
a positive projective inverse for each radix letter from `CubicContinuantRadix`.

Correctly guessed letters therefore pop exactly. A pair of opposite wrong guesses also cancels,
so these readers alone are not a sound stack compiler; a separate mismatch trap remains
necessary.
-/

namespace MatrixMortality.CubicReturn.NonPure

open scoped Matrix

/-- Repeat a physical return word without expanding its fixed block in the source. -/
def continuantRepeatWord (word : List Nat) : Nat → List Nat
  | 0 => []
  | repetitions + 1 => word ++ continuantRepeatWord word repetitions

/-- Reciprocal-ratio loop used by the reader for each radix digit. -/
def continuantReaderExpansionWord : Bool → List Nat
  | false =>
      [8, 3, 15, 15, 15, 8, 5, 15, 8, 1, 15, 8, 2, 1, 15, 8, 11, 11,
        12, 12, 15, 8, 5, 15, 2, 1, 15, 8, 4, 8, 12, 12, 15, 8, 8]
  | true =>
      [8, 1, 15, 8, 1, 8, 15, 21, 15, 7, 8, 15, 15, 1, 15, 2, 8, 2, 1,
        15, 8, 7, 8, 12, 12, 8, 1, 15, 8, 7, 1, 8, 2]

/-- Positive-translation loop used to correct the reciprocal-ratio loop. -/
def continuantReaderPositiveWord : Bool → List Nat
  | false =>
      [4, 5, 15, 8, 15, 21, 15, 12, 15, 8, 2, 1, 15, 8, 2, 15, 8, 12,
        2, 1, 15, 8, 11, 11, 12, 12, 15, 8, 5, 15]
  | true =>
      [12, 12, 8, 1, 15, 8, 7, 1, 8, 2, 15, 8, 7, 15, 15, 8, 7, 1, 8,
        1, 15, 8, 4]

/-- Negative-translation loop used to correct the reciprocal-ratio loop. -/
def continuantReaderNegativeWord : Bool → List Nat
  | false =>
      [15, 8, 5, 15, 4, 8, 12, 12, 15, 8, 5, 15, 8, 3, 15, 15, 15, 8,
        5, 15, 3, 15, 8, 1, 15, 8, 8, 8, 15, 8, 1, 15, 8, 8]
  | true =>
      [7, 8, 1, 15, 12, 12, 15, 8, 1, 15, 8, 8, 8, 3, 15, 15, 15, 8, 5,
        15, 14, 15, 7, 8, 2, 15, 8, 1, 15, 8, 7, 1, 14, 15, 3, 15, 15]

/-- Number of positive translations in each reader. -/
def continuantReaderPositiveCount : Bool → Nat
  | false => 39
  | true => 1

/-- Number of negative translations in each reader. -/
def continuantReaderNegativeCount : Bool → Nat
  | false => 26
  | true => 30

/-- Physical positive-wait word realizing the projective inverse of one radix letter. -/
def continuantRadixReaderWord (bit : Bool) : List Nat :=
  continuantRepeatWord (continuantReaderNegativeWord bit)
      (continuantReaderNegativeCount bit) ++
    (continuantRepeatWord (continuantReaderPositiveWord bit)
        (continuantReaderPositiveCount bit) ++
      continuantReaderExpansionWord bit)

/-- Normalized reciprocal-ratio loop for each reader. -/
def continuantReaderExpansion (bit : Bool) : Square (Fin 2) ℚ :=
  match bit with
  | false => !![25 / 4, 199285 / 6; 0, 1]
  | true => !![25 / 4, 9159 / 500; 0, 1]

/-- Normalized positive translation for each reader. -/
def continuantReaderPositive (bit : Bool) : Square (Fin 2) ℚ :=
  match bit with
  | false => !![1, 2839 / 108; 0, 1]
  | true => !![1, 31457 / 6480; 0, 1]

/-- Normalized negative translation for each reader. -/
def continuantReaderNegative (bit : Bool) : Square (Fin 2) ℚ :=
  match bit with
  | false => !![1, -189665 / 144; 0, 1]
  | true => !![1, -266051 / 303750; 0, 1]

/-- Exact normalized inverse of one cubic-continuant radix generator. -/
def continuantRadixReader (bit : Bool) : Square (Fin 2) ℚ :=
  !![25 / 4, -(continuantRadixDigit bit : ℚ) / 48; 0, 1]

private def ContinuantProjectivelyRealizes
    (word : List Nat) (matrix : Square (Fin 2) ℚ) : Prop :=
  ∃ scale : ℚ, scale ≠ 0 ∧
    wordProduct falseWaitReturn word = scale • matrix

private theorem continuantProjectivelyRealizes_append
    {leftWord rightWord : List Nat} {leftMatrix rightMatrix : Square (Fin 2) ℚ}
    (left : ContinuantProjectivelyRealizes leftWord leftMatrix)
    (right : ContinuantProjectivelyRealizes rightWord rightMatrix) :
    ContinuantProjectivelyRealizes (leftWord ++ rightWord) (leftMatrix * rightMatrix) := by
  rcases left with ⟨leftScale, leftScale_ne, leftProduct⟩
  rcases right with ⟨rightScale, rightScale_ne, rightProduct⟩
  refine ⟨leftScale * rightScale, mul_ne_zero leftScale_ne rightScale_ne, ?_⟩
  rw [wordProduct_append, leftProduct, rightProduct, Matrix.smul_mul, Matrix.mul_smul]
  simp only [smul_smul]

private theorem continuantProjectivelyRealizes_repeat
    {word : List Nat} {matrix : Square (Fin 2) ℚ}
    (realizes : ContinuantProjectivelyRealizes word matrix) (repetitions : Nat) :
    ContinuantProjectivelyRealizes (continuantRepeatWord word repetitions)
      (matrix ^ repetitions) := by
  induction repetitions with
  | zero =>
      refine ⟨1, one_ne_zero, ?_⟩
      simp [continuantRepeatWord]
  | succ repetitions induction =>
      simpa [continuantRepeatWord, pow_succ'] using
        continuantProjectivelyRealizes_append realizes induction

private theorem continuantReaderExpansionWord_realizes (bit : Bool) :
    ContinuantProjectivelyRealizes (continuantReaderExpansionWord bit)
      (continuantReaderExpansion bit) := by
  cases bit
  · refine ⟨350478128260971999568608408075016857496996911513600000000000000000000000,
      by norm_num, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [continuantReaderExpansionWord, continuantReaderExpansion,
        wordProduct_cons, wordProduct_nil, falseWaitReturn_eq_state,
        falseWaitReturnOfState, cubicDefectState, CubicDefectState.next,
        Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_succ]
  · refine ⟨1032944675098650160827021538682631469192445952000000000000000000000,
      by norm_num, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [continuantReaderExpansionWord, continuantReaderExpansion,
        wordProduct_cons, wordProduct_nil, falseWaitReturn_eq_state,
        falseWaitReturnOfState, cubicDefectState, CubicDefectState.next,
        Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_succ]

private theorem continuantReaderPositiveWord_realizes (bit : Bool) :
    ContinuantProjectivelyRealizes (continuantReaderPositiveWord bit)
      (continuantReaderPositive bit) := by
  cases bit
  · refine ⟨-880308120189957480269339373741663194185728000000000000000000000,
      by norm_num, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [continuantReaderPositiveWord, continuantReaderPositive,
        wordProduct_cons, wordProduct_nil, falseWaitReturn_eq_state,
        falseWaitReturnOfState, cubicDefectState, CubicDefectState.next,
        Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_succ]
  · refine ⟨-6356741801736389314381527121920000000000000000, by norm_num, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [continuantReaderPositiveWord, continuantReaderPositive,
        wordProduct_cons, wordProduct_nil, falseWaitReturn_eq_state,
        falseWaitReturnOfState, cubicDefectState, CubicDefectState.next,
        Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_succ]

private theorem continuantReaderNegativeWord_realizes (bit : Bool) :
    ContinuantProjectivelyRealizes (continuantReaderNegativeWord bit)
      (continuantReaderNegative bit) := by
  cases bit
  · refine ⟨23241255189719628618607984620359208056830033920000000000000000000000000,
      by norm_num, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [continuantReaderNegativeWord, continuantReaderNegative,
        wordProduct_cons, wordProduct_nil, falseWaitReturn_eq_state,
        falseWaitReturnOfState, cubicDefectState, CubicDefectState.next,
        Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_succ]
  · refine ⟨-68273511245320381030022815620767209587743907643392000000000000000000000000000,
      by norm_num, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [continuantReaderNegativeWord, continuantReaderNegative,
        wordProduct_cons, wordProduct_nil, falseWaitReturn_eq_state,
        falseWaitReturnOfState, cubicDefectState, CubicDefectState.next,
        Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_succ]

private theorem upperTranslation_pow (shift : ℚ) (repetitions : Nat) :
    (!![1, shift; 0, 1] : Square (Fin 2) ℚ) ^ repetitions =
      !![1, repetitions * shift; 0, 1] := by
  induction repetitions with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.one_apply]
  | succ repetitions induction =>
      rw [pow_succ', induction]
      ext i j
      fin_cases i
      · fin_cases j
        · simp [Matrix.mul_apply, Fin.sum_univ_succ]
        · simp [Matrix.mul_apply, Fin.sum_univ_succ]
          ring
      · fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

private theorem continuantReader_factorization (bit : Bool) :
    continuantReaderNegative bit ^ continuantReaderNegativeCount bit *
        (continuantReaderPositive bit ^ continuantReaderPositiveCount bit *
          continuantReaderExpansion bit) =
      continuantRadixReader bit := by
  cases bit
  · rw [show continuantReaderNegative false = !![1, -189665 / 144; 0, 1] by rfl,
      show continuantReaderPositive false = !![1, 2839 / 108; 0, 1] by rfl,
      upperTranslation_pow, upperTranslation_pow]
    ext i j
    fin_cases i <;> fin_cases j <;>
    norm_num [continuantReaderNegative, continuantReaderPositive,
      continuantReaderExpansion, continuantReaderNegativeCount,
      continuantReaderPositiveCount, continuantRadixReader, continuantRadixDigit,
      Matrix.mul_apply, Fin.sum_univ_succ]
  · rw [show continuantReaderNegative true = !![1, -266051 / 303750; 0, 1] by rfl,
      show continuantReaderPositive true = !![1, 31457 / 6480; 0, 1] by rfl,
      upperTranslation_pow, upperTranslation_pow]
    ext i j
    fin_cases i <;> fin_cases j <;>
    norm_num [continuantReaderNegative, continuantReaderPositive,
      continuantReaderExpansion, continuantReaderNegativeCount,
      continuantReaderPositiveCount, continuantRadixReader, continuantRadixDigit,
      Matrix.mul_apply, Fin.sum_univ_succ]

private theorem continuantRadixReaderWord_realizes (bit : Bool) :
    ContinuantProjectivelyRealizes (continuantRadixReaderWord bit)
      (continuantRadixReader bit) := by
  have negative := continuantProjectivelyRealizes_repeat
    (continuantReaderNegativeWord_realizes bit) (continuantReaderNegativeCount bit)
  have positive := continuantProjectivelyRealizes_repeat
    (continuantReaderPositiveWord_realizes bit) (continuantReaderPositiveCount bit)
  have expansion := continuantReaderExpansionWord_realizes bit
  have combined := continuantProjectivelyRealizes_append negative
    (continuantProjectivelyRealizes_append positive expansion)
  rw [continuantReader_factorization bit] at combined
  simpa only [continuantRadixReaderWord] using combined

private theorem continuantRepeatWord_positive {word : List Nat}
    (positive : ∀ wait ∈ word, 0 < wait) (repetitions : Nat) :
    ∀ wait ∈ continuantRepeatWord word repetitions, 0 < wait := by
  induction repetitions with
  | zero => simp [continuantRepeatWord]
  | succ repetitions induction =>
      intro wait membership
      rw [continuantRepeatWord, List.mem_append] at membership
      exact membership.elim (positive wait) (induction wait)

/-- Every physical letter in a reader is a strictly positive wait. -/
theorem continuantRadixReaderWord_positive (bit : Bool) :
    ∀ wait ∈ continuantRadixReaderWord bit, 0 < wait := by
  have expansion : ∀ wait ∈ continuantReaderExpansionWord bit, 0 < wait := by
    cases bit <;> simp [continuantReaderExpansionWord]
  have positive : ∀ wait ∈ continuantReaderPositiveWord bit, 0 < wait := by
    cases bit <;> simp [continuantReaderPositiveWord]
  have negative : ∀ wait ∈ continuantReaderNegativeWord bit, 0 < wait := by
    cases bit <;> simp [continuantReaderNegativeWord]
  intro wait membership
  rw [continuantRadixReaderWord, List.mem_append] at membership
  rcases membership with negative_mem | positive_or_expansion
  · exact continuantRepeatWord_positive negative _ wait negative_mem
  · rw [List.mem_append] at positive_or_expansion
    exact positive_or_expansion.elim
      (continuantRepeatWord_positive positive _ wait)
      (expansion wait)

/-- Each normalized reader is the exact projective inverse of its radix letter. -/
theorem continuantRadixReader_mul_generator (bit : Bool) :
    continuantRadixReader bit * continuantRadixGenerator bit =
      (25 : ℚ) • (1 : Square (Fin 2) ℚ) := by
  cases bit <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [continuantRadixReader, continuantRadixGenerator, continuantRadixDigit,
      Matrix.mul_apply, Matrix.one_apply, Matrix.smul_apply, Fin.sum_univ_succ]

/-- A reader followed by its physical radix letter is a nonzero scalar identity. -/
theorem continuantRadixReaderWord_push_pop (bit : Bool) :
    ∃ scale : ℚ, scale ≠ 0 ∧
      wordProduct falseWaitReturn
          (continuantRadixReaderWord bit ++ continuantRadixWord bit) =
        scale • (1 : Square (Fin 2) ℚ) := by
  have reader := continuantRadixReaderWord_realizes bit
  have writer :
      ContinuantProjectivelyRealizes (continuantRadixWord bit)
        (continuantRadixGenerator bit) := by
    refine ⟨continuantRadixScale bit, ?_, continuantRadixWord_product bit⟩
    cases bit <;> norm_num [continuantRadixScale]
  rcases continuantProjectivelyRealizes_append reader writer with
    ⟨scale, scale_ne, product⟩
  refine ⟨scale * 25, mul_ne_zero scale_ne (by norm_num), ?_⟩
  rw [product, continuantRadixReader_mul_generator]
  simp only [smul_smul]

/-- A correctly guessed reader deletes the head radix letter and preserves every suffix up to
one nonzero scalar. -/
theorem continuantRadixReaderWord_pop_suffix (bit : Bool) (suffix : List Nat) :
    ∃ scale : ℚ, scale ≠ 0 ∧
      wordProduct falseWaitReturn
          ((continuantRadixReaderWord bit ++ continuantRadixWord bit) ++ suffix) =
        scale • wordProduct falseWaitReturn suffix := by
  rcases continuantRadixReaderWord_push_pop bit with ⟨scale, scale_ne, pop⟩
  refine ⟨scale, scale_ne, ?_⟩
  rw [wordProduct_append, pop, Matrix.smul_mul]
  simp

/-- A correctly guessed reader pops the head of every physical radix encoding. -/
theorem continuantRadixReaderWord_pop_encoding (bit : Bool) (bits : List Bool) :
    ∃ scale : ℚ, scale ≠ 0 ∧
      wordProduct falseWaitReturn
          (continuantRadixReaderWord bit ++ continuantRadixEncoding (bit :: bits)) =
        scale • wordProduct falseWaitReturn (continuantRadixEncoding bits) := by
  simpa [continuantRadixEncoding, List.append_assoc] using
    continuantRadixReaderWord_pop_suffix bit (continuantRadixEncoding bits)

/-- A wrong reader leaves one of two opposite nonzero parabolic defects. -/
theorem continuantRadixReader_mismatch :
    continuantRadixReader false * continuantRadixGenerator true =
        (25 : ℚ) • (!![1, -125 / 48; 0, 1] : Square (Fin 2) ℚ) ∧
      continuantRadixReader true * continuantRadixGenerator false =
        (25 : ℚ) • (!![1, 125 / 48; 0, 1] : Square (Fin 2) ℚ) := by
  constructor <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [continuantRadixReader, continuantRadixGenerator, continuantRadixDigit,
      Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_succ]

/-- The two opposite mismatch defects cancel. Thus the positive readers require an independent
local mismatch trap before they can serve as a sound stack compiler. -/
theorem continuantRadixReader_two_mismatches :
    (continuantRadixReader false * continuantRadixGenerator true) *
        (continuantRadixReader true * continuantRadixGenerator false) =
      (625 : ℚ) • (1 : Square (Fin 2) ℚ) := by
  rw [continuantRadixReader_mismatch.1, continuantRadixReader_mismatch.2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Matrix.one_apply, Matrix.smul_apply,
      Fin.sum_univ_succ]

/-- The physical positive-wait spelling of two opposite mismatches is already projectively the
identity, so terminal equality cannot distinguish it from two correct pops. -/
theorem continuantRadixReaderWord_two_mismatches :
    ∃ scale : ℚ, scale ≠ 0 ∧
      wordProduct falseWaitReturn
          (continuantRadixReaderWord false ++
            (continuantRadixWord true ++
              (continuantRadixReaderWord true ++ continuantRadixWord false))) =
        scale • (1 : Square (Fin 2) ℚ) := by
  have readerFalse := continuantRadixReaderWord_realizes false
  have readerTrue := continuantRadixReaderWord_realizes true
  have writerFalse :
      ContinuantProjectivelyRealizes (continuantRadixWord false)
        (continuantRadixGenerator false) := by
    refine ⟨continuantRadixScale false, by norm_num [continuantRadixScale],
      continuantRadixWord_product false⟩
  have writerTrue :
      ContinuantProjectivelyRealizes (continuantRadixWord true)
        (continuantRadixGenerator true) := by
    refine ⟨continuantRadixScale true, by norm_num [continuantRadixScale],
      continuantRadixWord_product true⟩
  have combined := continuantProjectivelyRealizes_append readerFalse
    (continuantProjectivelyRealizes_append writerTrue
      (continuantProjectivelyRealizes_append readerTrue writerFalse))
  rcases combined with ⟨scale, scale_ne, product⟩
  refine ⟨scale * 625, mul_ne_zero scale_ne (by norm_num), ?_⟩
  rw [product]
  have normalized := continuantRadixReader_two_mismatches
  rw [← Matrix.mul_assoc, normalized]
  simp [smul_smul]

end MatrixMortality.CubicReturn.NonPure
