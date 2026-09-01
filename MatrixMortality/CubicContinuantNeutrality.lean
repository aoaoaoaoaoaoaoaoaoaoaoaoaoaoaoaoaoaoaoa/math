import MatrixMortality.CubicContinuantReader

/-!
# Projective-neutral insertion in the cubic continuant reader

Every correct reader-writer block is a nonzero scalar identity. It is therefore invisible to
zero testing in every homogeneous matrix context, so the fixed two-dimensional representation
cannot enforce the presence, count, or boundary of such blocks.
-/

namespace MatrixMortality.CubicReturn.NonPure

/-- Physical spelling of one cubic radix read followed by one writer. -/
def continuantReadWriteWord (guess written : Bool) : List Nat :=
  continuantRadixReaderWord guess ++ continuantRadixWord written

/-- Physical spelling of one correct cubic radix read followed by its matching writer. -/
def continuantCorrectReadWriteWord (bit : Bool) : List Nat :=
  continuantReadWriteWord bit bit

/-- Inserting or deleting any correct reader-writer block preserves mortality in every physical
left and right context. -/
theorem continuantCorrectReadWrite_insertion_zero_iff
    (bit : Bool) (left right : List Nat) :
    wordProduct falseWaitReturn
        (left ++ continuantCorrectReadWriteWord bit ++ right) = 0 ↔
      wordProduct falseWaitReturn (left ++ right) = 0 := by
  rcases continuantRadixReaderWord_push_pop bit with
    ⟨scale, scale_ne, neutral_product⟩
  exact wordProduct_zero_iff_projectiveIdentity_insertion falseWaitReturn
    left (continuantCorrectReadWriteWord bit) right scale scale_ne neutral_product

/-- A positive physical radix-carry word with four negative errors below one clock and twenty-five
positive errors above it. -/
def continuantCarryNeutralWord : List Nat :=
  continuantRepeatWord (continuantReadWriteWord false true) 4 ++
    (continuantRadixWord true ++
      (continuantRepeatWord (continuantReadWriteWord true false) 25 ++
        continuantRadixReaderWord true))

private theorem continuantWriter_projectivelyRealizes (bit : Bool) :
    continuantProjectivelyRealizes (continuantRadixWord bit)
      (continuantRadixGenerator bit) := by
  refine ⟨continuantRadixScale bit, ?_, continuantRadixWord_product bit⟩
  cases bit <;> norm_num [continuantRadixScale]

/-- Every physical read-write block realizes its normalized reader-writer product. -/
theorem continuantReadWriteWord_projectivelyRealizes (guess written : Bool) :
    continuantProjectivelyRealizes (continuantReadWriteWord guess written)
      (continuantRadixReader guess * continuantRadixGenerator written) := by
  exact continuantProjectivelyRealizes_append
    (continuantRadixReaderWord_projectivelyRealizes guess)
    (continuantWriter_projectivelyRealizes written)

/-- Four negative mismatches, one true clock, twenty-five positive mismatches, and one cleanup
reader form an exact scalar identity after normalization. -/
theorem continuantCarry_normalized_identity :
    (continuantRadixReader false * continuantRadixGenerator true) ^ 4 *
        (continuantRadixGenerator true *
          ((continuantRadixReader true * continuantRadixGenerator false) ^ 25 *
            continuantRadixReader true)) =
      (25 ^ 30 : ℚ) • (1 : Square (Fin 2) ℚ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [continuantRadixReader, continuantRadixGenerator,
      continuantRadixDigit, Matrix.mul_apply, Matrix.one_apply,
      Matrix.smul_apply, Fin.sum_univ_succ, pow_succ]

/-- The complete positive physical carry word is a nonzero projective identity. -/
theorem continuantCarryNeutralWord_projectiveIdentity :
    ∃ scale : ℚ, scale ≠ 0 ∧
      wordProduct falseWaitReturn continuantCarryNeutralWord =
        scale • (1 : Square (Fin 2) ℚ) := by
  have negativeMismatch := continuantProjectivelyRealizes_repeat
    (continuantReadWriteWord_projectivelyRealizes false true) 4
  have positiveMismatch := continuantProjectivelyRealizes_repeat
    (continuantReadWriteWord_projectivelyRealizes true false) 25
  have writer := continuantWriter_projectivelyRealizes true
  have reader := continuantRadixReaderWord_projectivelyRealizes true
  have combined := continuantProjectivelyRealizes_append negativeMismatch
    (continuantProjectivelyRealizes_append writer
      (continuantProjectivelyRealizes_append positiveMismatch reader))
  rcases combined with ⟨scale, scale_ne, product⟩
  refine ⟨scale * 25 ^ 30, mul_ne_zero scale_ne (by norm_num), ?_⟩
  rw [continuantCarryNeutralWord, product, continuantCarry_normalized_identity]
  simp only [smul_smul]

private theorem continuantNeutralRadixWord_positive (bit : Bool) :
    ∀ wait ∈ continuantRadixWord bit, 0 < wait := by
  cases bit <;> simp [continuantRadixWord]

private theorem continuantReadWriteWord_positive (guess written : Bool) :
    ∀ wait ∈ continuantReadWriteWord guess written, 0 < wait := by
  intro wait membership
  rw [continuantReadWriteWord, List.mem_append] at membership
  exact membership.elim
    (continuantRadixReaderWord_positive guess wait)
    (continuantNeutralRadixWord_positive written wait)

/-- Every wait in the physical radix-carry identity is strictly positive. -/
theorem continuantCarryNeutralWord_positive :
    ∀ wait ∈ continuantCarryNeutralWord, 0 < wait := by
  intro wait membership
  simp only [continuantCarryNeutralWord, List.mem_append] at membership
  rcases membership with negativeMismatch | writerOrRest
  · exact continuantRepeatWord_positive
      (continuantReadWriteWord_positive false true) 4 wait negativeMismatch
  rcases writerOrRest with writer | negativeOrReader
  · exact continuantNeutralRadixWord_positive true wait writer
  rcases negativeOrReader with positiveMismatch | reader
  · exact continuantRepeatWord_positive
      (continuantReadWriteWord_positive true false) 25 wait positiveMismatch
  · exact continuantRadixReaderWord_positive true wait reader

private theorem continuantNeutralRepeatWord_length (word : List Nat) (repetitions : Nat) :
    (continuantRepeatWord word repetitions).length = repetitions * word.length := by
  induction repetitions with
  | zero => simp [continuantRepeatWord]
  | succ repetitions induction =>
      rw [continuantRepeatWord, List.length_append, induction]
      simp [Nat.succ_mul, Nat.add_comm]

private theorem continuantNeutralRadixReaderWord_length :
    (continuantRadixReaderWord false).length = 2089 ∧
      (continuantRadixReaderWord true).length = 1166 := by
  constructor <;>
    simp [continuantRadixReaderWord, continuantNeutralRepeatWord_length,
      continuantReaderNegativeCount, continuantReaderPositiveCount,
      continuantReaderNegativeWord, continuantReaderPositiveWord,
      continuantReaderExpansionWord]

private theorem continuantNeutralRadixWord_length :
    (continuantRadixWord false).length = 1 ∧
      (continuantRadixWord true).length = 9 := by
  simp [continuantRadixWord]

/-- The optimized positive physical radix-carry identity has length `38,742`. -/
theorem continuantCarryNeutralWord_length :
    continuantCarryNeutralWord.length = 38742 := by
  simp [continuantCarryNeutralWord, continuantReadWriteWord,
    continuantNeutralRepeatWord_length, continuantNeutralRadixReaderWord_length,
    continuantNeutralRadixWord_length]

/-- Inserting or deleting the positive physical radix-carry word preserves mortality in every
physical context. -/
theorem continuantCarryNeutralWord_insertion_zero_iff (left right : List Nat) :
    wordProduct falseWaitReturn (left ++ continuantCarryNeutralWord ++ right) = 0 ↔
      wordProduct falseWaitReturn (left ++ right) = 0 := by
  rcases continuantCarryNeutralWord_projectiveIdentity with
    ⟨scale, scale_ne, neutral_product⟩
  exact wordProduct_zero_iff_projectiveIdentity_insertion falseWaitReturn
    left continuantCarryNeutralWord right scale scale_ne neutral_product

end MatrixMortality.CubicReturn.NonPure
