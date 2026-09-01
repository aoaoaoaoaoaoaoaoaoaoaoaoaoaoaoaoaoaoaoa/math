import MatrixMortality.CubicContinuantSelectedComparator

/-!
# A non-scalar positive source stabilizer in the fixed cubic continuant

The original separator source has a short affine stabilizer once the radix writer is composed
with the available positive terminal translations. Appending its positive physical spelling to
the selected `00` source preserves the observed source ray without preserving the projective
matrix product. Scalar-identity stutters therefore do not exhaust the source fibre.
-/

namespace MatrixMortality.CubicReturn.NonPure

open scoped Matrix

/-- Positive translation word whose exact normalized shift is `-11/10`. -/
def falseWaitSourceStabilizerTranslationWord : List Nat :=
  continuantRepeatWord (continuantReaderPositiveWord false) 25 ++
    (continuantRepeatWord (continuantReaderNegativeWord false) 5 ++
      continuantRepeatWord (continuantReaderPositiveWord true) 1221)

/-- Positive physical spelling of the separator-source affine stabilizer. -/
def falseWaitSourceStabilizerWord : List Nat :=
  continuantRadixWord false ++ falseWaitSourceStabilizerTranslationWord

/-- Exact lower-right-one affine stabilizer of the original separator source. -/
def falseWaitSourceStabilizer : Square (Fin 2) ℚ :=
  !![4 / 25, 553 / 750; 0, 1]

/-- The selected `00` physical source word. -/
def falseWaitSelectedSourceWord : List Nat :=
  falseWaitFirstHitBinaryEncoding falseWaitFirstHitSingletonTarget

/-- A nontrivial source-stabilizer insertion after the selected `00` word. -/
def falseWaitSelectedSourceStabilizerCollisionWord : List Nat :=
  falseWaitSelectedSourceWord ++ falseWaitSourceStabilizerWord

private theorem falseWaitSourceTranslation_pow (shift : ℚ) (repetitions : Nat) :
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

/-- The three positive terminal-translation runs realize the exact total shift `-11/10`. -/
theorem falseWaitSourceStabilizerTranslationWord_projectivelyRealizes :
    continuantProjectivelyRealizes falseWaitSourceStabilizerTranslationWord
      (continuantDefectTranslation (-11 / 10)) := by
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
  have first := continuantProjectivelyRealizes_repeat positiveFalse 25
  have second := continuantProjectivelyRealizes_repeat negativeFalse 5
  have third := continuantProjectivelyRealizes_repeat positiveTrue 1221
  have combined := continuantProjectivelyRealizes_append first
    (continuantProjectivelyRealizes_append second third)
  have normalized :
      continuantDefectTranslation (2839 / 108) ^ 25 *
          (continuantDefectTranslation (-189665 / 144) ^ 5 *
            continuantDefectTranslation (31457 / 6480) ^ 1221) =
        continuantDefectTranslation (-11 / 10) := by
    rw [falseWaitSourceTranslation_pow, falseWaitSourceTranslation_pow,
      falseWaitSourceTranslation_pow]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [continuantDefectTranslation, Matrix.mul_apply,
        Fin.sum_univ_succ]
  rw [normalized] at combined
  simpa only [falseWaitSourceStabilizerTranslationWord] using combined

private theorem falseWaitSourceStabilizerWriter_projectivelyRealizes :
    continuantProjectivelyRealizes (continuantRadixWord false)
      (!![4 / 25, 137 / 150; 0, 1] : Square (Fin 2) ℚ) := by
  refine ⟨-150, by norm_num, ?_⟩
  rw [continuantRadixWord_product]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [continuantRadixScale, continuantRadixGenerator,
      continuantRadixDigit, Matrix.smul_apply]

/-- The complete positive word realizes the displayed non-scalar source stabilizer. -/
theorem falseWaitSourceStabilizerWord_projectivelyRealizes :
    continuantProjectivelyRealizes falseWaitSourceStabilizerWord
      falseWaitSourceStabilizer := by
  have combined := continuantProjectivelyRealizes_append
    falseWaitSourceStabilizerWriter_projectivelyRealizes
    falseWaitSourceStabilizerTranslationWord_projectivelyRealizes
  have normalized :
      (!![4 / 25, 137 / 150; 0, 1] : Square (Fin 2) ℚ) *
          continuantDefectTranslation (-11 / 10) =
        falseWaitSourceStabilizer := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [falseWaitSourceStabilizer, continuantDefectTranslation,
        Matrix.mul_apply, Fin.sum_univ_succ]
  rw [normalized] at combined
  simpa only [falseWaitSourceStabilizerWord] using combined

/-- The affine matrix fixes the original physical separator source exactly. -/
theorem falseWaitSourceStabilizer_source :
    falseWaitSourceStabilizer *ᵥ falseWaitSeparatorColumn =
      falseWaitSeparatorColumn := by
  ext coordinate
  fin_cases coordinate <;>
    norm_num [falseWaitSourceStabilizer, falseWaitSeparatorColumn,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The source stabilizer is not a projective identity. -/
theorem falseWaitSourceStabilizer_not_projectiveIdentity (scale : ℚ) :
    falseWaitSourceStabilizer ≠ scale • (1 : Square (Fin 2) ℚ) := by
  intro identity
  have upperLeft := congrFun (congrFun identity 0) 0
  have lowerRight := congrFun (congrFun identity 1) 1
  norm_num [falseWaitSourceStabilizer, Matrix.smul_apply,
    Matrix.one_apply] at upperLeft lowerRight
  linarith

/-- Every wait in the source-stabilizer spelling is strictly positive. -/
theorem falseWaitSourceStabilizerWord_positive :
    ∀ wait ∈ falseWaitSourceStabilizerWord, 0 < wait := by
  have writer : ∀ wait ∈ continuantRadixWord false, 0 < wait := by
    intro wait membership
    exact continuantRadixEncoding_positive [false] wait (by
      simpa [continuantRadixEncoding] using membership)
  have positiveFalse :
      ∀ wait ∈ continuantReaderPositiveWord false, 0 < wait := by
    simp [continuantReaderPositiveWord]
  have negativeFalse :
      ∀ wait ∈ continuantReaderNegativeWord false, 0 < wait := by
    simp [continuantReaderNegativeWord]
  have positiveTrue :
      ∀ wait ∈ continuantReaderPositiveWord true, 0 < wait := by
    simp [continuantReaderPositiveWord]
  intro wait membership
  rw [falseWaitSourceStabilizerWord, List.mem_append] at membership
  rcases membership with writer_mem | translation_mem
  · exact writer wait writer_mem
  · simp only [falseWaitSourceStabilizerTranslationWord,
      List.mem_append] at translation_mem
    rcases translation_mem with positive_false_mem | rest_mem
    · exact continuantRepeatWord_positive positiveFalse 25 wait positive_false_mem
    · rcases rest_mem with negative_false_mem | positive_true_mem
      · exact continuantRepeatWord_positive negativeFalse 5 wait negative_false_mem
      · exact continuantRepeatWord_positive positiveTrue 1221 wait positive_true_mem

/-- The source-stabilizer spelling has exact physical length `29,004`. -/
theorem falseWaitSourceStabilizerWord_length :
    falseWaitSourceStabilizerWord.length = 29004 := by
  norm_num [falseWaitSourceStabilizerWord,
    falseWaitSourceStabilizerTranslationWord, List.length_append,
    continuantRepeatWord_length, continuantRadixWord,
    continuantReaderPositiveWord, continuantReaderNegativeWord]

/-- The extended selected source word has exact physical length `29,012`. -/
theorem falseWaitSelectedSourceStabilizerCollisionWord_length :
    falseWaitSelectedSourceStabilizerCollisionWord.length = 29012 := by
  rw [falseWaitSelectedSourceStabilizerCollisionWord, List.length_append,
    falseWaitSourceStabilizerWord_length]
  norm_num [falseWaitSelectedSourceWord, falseWaitFirstHitSingletonTarget,
    falseWaitFirstHitBinaryEncoding, falseWaitFirstHitBinaryLoop]

/-- Every wait in the extended selected source word is strictly positive. -/
theorem falseWaitSelectedSourceStabilizerCollisionWord_positive :
    ∀ wait ∈ falseWaitSelectedSourceStabilizerCollisionWord, 0 < wait := by
  intro wait membership
  rw [falseWaitSelectedSourceStabilizerCollisionWord,
    List.mem_append] at membership
  exact membership.elim
    (falseWaitFirstHitBinaryEncoding_positive
      falseWaitFirstHitSingletonTarget wait)
    (falseWaitSourceStabilizerWord_positive wait)

/-- Appending the non-scalar stabilizer preserves the selected source ray by one nonzero
physical scale. -/
theorem falseWaitSelectedSourceStabilizerCollisionWord_source :
    ∃ scale : ℚ, scale ≠ 0 ∧
      wordProduct falseWaitReturn falseWaitSelectedSourceStabilizerCollisionWord *ᵥ
          falseWaitSeparatorColumn =
        scale •
          (wordProduct falseWaitReturn falseWaitSelectedSourceWord *ᵥ
            falseWaitSeparatorColumn) := by
  rcases falseWaitSourceStabilizerWord_projectivelyRealizes with
    ⟨scale, scale_ne, stabilizerProduct⟩
  refine ⟨scale, scale_ne, ?_⟩
  rw [falseWaitSelectedSourceStabilizerCollisionWord, wordProduct_append,
    ← Matrix.mulVec_mulVec, stabilizerProduct, Matrix.smul_mulVec,
    falseWaitSourceStabilizer_source, Matrix.mulVec_smul]

private theorem falseWaitPositiveWord_product_isUnit
    (word : List Nat) (positive : ∀ wait ∈ word, 0 < wait) :
    IsUnit (wordProduct falseWaitReturn word) := by
  induction word with
  | nil => exact isUnit_one
  | cons wait word induction =>
      rw [wordProduct_cons]
      exact ((falseWaitReturn_isUnit_iff_positive wait).2
        (positive wait (by simp))).mul
        (induction (by
          intro tail tail_mem
          exact positive tail (by simp [tail_mem])))

/-- The collision word and the selected source word are not projectively equal as matrices,
despite inducing the same source ray. -/
theorem falseWaitSelectedSourceStabilizerCollisionWord_not_projectivelyEqual
    (scale : ℚ) :
    wordProduct falseWaitReturn falseWaitSelectedSourceStabilizerCollisionWord ≠
      scale • wordProduct falseWaitReturn falseWaitSelectedSourceWord := by
  intro projective_eq
  rcases falseWaitSourceStabilizerWord_projectivelyRealizes with
    ⟨stabilizerScale, stabilizerScale_ne, stabilizerProduct⟩
  have sourceUnit :
      IsUnit (wordProduct falseWaitReturn falseWaitSelectedSourceWord) := by
    exact falseWaitPositiveWord_product_isUnit falseWaitSelectedSourceWord
      (by
        intro wait membership
        exact falseWaitFirstHitBinaryEncoding_positive
          falseWaitFirstHitSingletonTarget wait membership)
  have contextual_eq :
      wordProduct falseWaitReturn falseWaitSelectedSourceWord *
          (stabilizerScale • falseWaitSourceStabilizer) =
        wordProduct falseWaitReturn falseWaitSelectedSourceWord *
          (scale • (1 : Square (Fin 2) ℚ)) := by
    calc
      wordProduct falseWaitReturn falseWaitSelectedSourceWord *
            (stabilizerScale • falseWaitSourceStabilizer) =
          wordProduct falseWaitReturn falseWaitSelectedSourceStabilizerCollisionWord := by
            rw [falseWaitSelectedSourceStabilizerCollisionWord,
              wordProduct_append, stabilizerProduct]
      _ = scale • wordProduct falseWaitReturn falseWaitSelectedSourceWord :=
        projective_eq
      _ = wordProduct falseWaitReturn falseWaitSelectedSourceWord *
          (scale • (1 : Square (Fin 2) ℚ)) := by
            rw [Matrix.mul_smul, Matrix.mul_one]
  have stabilizer_identity :
      stabilizerScale • falseWaitSourceStabilizer =
        scale • (1 : Square (Fin 2) ℚ) :=
    sourceUnit.mul_left_cancel contextual_eq
  have upperLeft := congrFun (congrFun stabilizer_identity 0) 0
  have lowerRight := congrFun (congrFun stabilizer_identity 1) 1
  norm_num [falseWaitSourceStabilizer, Matrix.smul_apply,
    Matrix.one_apply] at upperLeft lowerRight
  have stabilizerScale_zero : stabilizerScale = 0 := by linarith
  exact stabilizerScale_ne stabilizerScale_zero

end MatrixMortality.CubicReturn.NonPure
