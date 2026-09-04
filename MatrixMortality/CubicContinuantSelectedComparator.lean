import MatrixMortality.CubicContinuantMismatchClock
import MatrixMortality.CubicContinuantNeutrality
import MatrixMortality.CubicContinuantSingletonSelector

/-!
# Selected comparison and projective-neutral fracture

The balanced mismatch clock can be inserted into the positive singleton selector. Its residual
translation moves the selected row by a nonzero multiple of the signed mismatch defect, so the
physical incidence vanishes exactly when every guessed bit matches. This local composition does
not enforce its own block syntax: the two opposite unclocked mismatches form a nonzero scalar
identity and can be inserted into the selected zero word without changing mortality.
-/

namespace MatrixMortality.CubicReturn.NonPure

open scoped Matrix

/-- Signed mismatch defect carried by one balanced comparison schedule. -/
def falseWaitFirstHitSelectedComparatorDefect
    (checks : List (Bool × Bool)) : ℚ :=
  continuantMismatchDefect (checks.map continuantReadError)

/-- Repeated selector translation followed by the balanced mismatch checker. -/
def falseWaitFirstHitSelectedComparatorMiddle
    (checks : List (Bool × Bool)) : List Nat :=
  falseWaitFirstHitSingletonMiddle ++ continuantBalancedReadWord checks

/-- Complete positive row word for a selected mismatch comparison. -/
def falseWaitFirstHitSelectedComparatorWord
    (checks : List (Bool × Bool)) : List Nat :=
  falseWaitFirstHitSingletonPrefix ++
    falseWaitFirstHitRayTransportWord
      (falseWaitFirstHitSelectedComparatorMiddle checks)

/-- Exact terminal translation accumulated before common-ray transport. -/
def falseWaitFirstHitSelectedComparatorTranslation
    (checks : List (Bool × Bool)) : Square (Fin 2) ℚ :=
  continuantDefectTranslation
    (-762919 / 2 + 125 / 48 * falseWaitFirstHitSelectedComparatorDefect checks)

/-- Common-ray loop obtained by transporting the selected mismatch translation. -/
def falseWaitFirstHitSelectedComparatorLoop
    (checks : List (Bool × Bool)) : Square (Fin 2) ℚ :=
  !![1,
      -85828079 / 1020 +
        625 / 1088 * falseWaitFirstHitSelectedComparatorDefect checks;
     0, 9 / 340]

/-- Common-ray row after the selected mismatch loop acts on the fixed prefix row. -/
def falseWaitFirstHitSelectedComparatorRow
    (checks : List (Bool × Bool)) : Fin 2 → ℚ :=
  ![1,
    falseWaitFirstHitBinarySourceCoordinate falseWaitFirstHitSingletonTarget +
      625 / 1088 * falseWaitFirstHitSelectedComparatorDefect checks]

/-- The physical middle word realizes its exact mismatch-dependent terminal translation. -/
theorem falseWaitFirstHitSelectedComparatorMiddle_projectivelyRealizes
    (checks : List (Bool × Bool)) :
    continuantProjectivelyRealizes
      (falseWaitFirstHitSelectedComparatorMiddle checks)
      (falseWaitFirstHitSelectedComparatorTranslation checks) := by
  have selector := falseWaitFirstHitSingletonMiddle_projectivelyRealizes
  have checker := continuantBalancedReadWord_projectivelyRealizes checks
  have combined := continuantProjectivelyRealizes_append selector checker
  have combined' :
      continuantProjectivelyRealizes
        (falseWaitFirstHitSingletonMiddle ++ continuantBalancedReadWord checks)
        (falseWaitFirstHitSingletonTranslation *
          continuantDefectTranslation
            ((125 / 48) * falseWaitFirstHitSelectedComparatorDefect checks)) := by
    simpa only [falseWaitFirstHitSelectedComparatorDefect] using combined
  have translation :
      falseWaitFirstHitSingletonTranslation *
          continuantDefectTranslation
            ((125 / 48) * falseWaitFirstHitSelectedComparatorDefect checks) =
        falseWaitFirstHitSelectedComparatorTranslation checks := by
    ext i j
    fin_cases i
    · fin_cases j
      · simp [falseWaitFirstHitSingletonTranslation,
          falseWaitFirstHitSelectedComparatorTranslation,
          continuantDefectTranslation, Matrix.mul_apply,
          Fin.sum_univ_succ]
      · simp [falseWaitFirstHitSingletonTranslation,
          falseWaitFirstHitSelectedComparatorTranslation,
          continuantDefectTranslation, Matrix.mul_apply,
          Fin.sum_univ_succ]
        ring
    · fin_cases j <;>
        simp [falseWaitFirstHitSingletonTranslation,
          falseWaitFirstHitSelectedComparatorTranslation,
          continuantDefectTranslation, Matrix.mul_apply,
          Fin.sum_univ_succ]
  rw [translation] at combined'
  simpa only [falseWaitFirstHitSelectedComparatorMiddle] using combined'

/-- The transported comparison realizes its exact mismatch-dependent common-ray loop. -/
theorem falseWaitFirstHitSelectedComparatorConnector_chart
    (checks : List (Bool × Bool)) :
    ∃ scale : ℚ, scale ≠ 0 ∧
      falseWaitFirstHitBinaryBasisInverse *
            wordProduct falseWaitReturn
              (falseWaitFirstHitRayTransportWord
                (falseWaitFirstHitSelectedComparatorMiddle checks)) *
        falseWaitFirstHitBinaryBasis =
          scale • falseWaitFirstHitSelectedComparatorLoop checks := by
  have transported :=
    falseWaitFirstHitRayTransport_projectivelyRealizes (by norm_num : (1 : ℚ) ≠ 0)
      (falseWaitFirstHitSelectedComparatorMiddle_projectivelyRealizes checks)
  have normalized :
      falseWaitFirstHitRayTransportNormalized 1
          (-762919 / 2 +
            125 / 48 * falseWaitFirstHitSelectedComparatorDefect checks) 1 =
        falseWaitFirstHitSelectedComparatorLoop checks := by
    ext i j
    fin_cases i
    · fin_cases j
      · simp [falseWaitFirstHitRayTransportNormalized,
          falseWaitFirstHitSelectedComparatorLoop]
      · simp [falseWaitFirstHitRayTransportNormalized,
          falseWaitFirstHitSelectedComparatorLoop]
        ring
    · fin_cases j <;>
        simp [falseWaitFirstHitRayTransportNormalized,
          falseWaitFirstHitSelectedComparatorLoop]
  rw [normalized] at transported
  simpa [falseWaitFirstHitSelectedComparatorTranslation,
    continuantDefectTranslation] using transported

/-- The fixed prefix converts the transported mismatch into the displayed selected row. -/
theorem falseWaitFirstHitSelectedComparatorLoop_row
    (checks : List (Bool × Bool)) :
    ![1, 937 / 3321] ᵥ* falseWaitFirstHitSelectedComparatorLoop checks =
      falseWaitFirstHitSelectedComparatorRow checks := by
  unfold falseWaitFirstHitSelectedComparatorRow
  rw [falseWaitFirstHitSingletonTarget_coordinate]
  ext coordinate
  fin_cases coordinate
  · simp [falseWaitFirstHitSelectedComparatorLoop, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ]
  · simp [falseWaitFirstHitSelectedComparatorLoop, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ]
    ring

/-- The complete positive comparator word has the mismatch-dependent selected row as its
nonzero projective chart. -/
theorem falseWaitFirstHitSelectedComparatorWord_row
    (checks : List (Bool × Bool)) :
    ∃ scale : ℚ, scale ≠ 0 ∧
      (falseWaitSeparatorRow ᵥ*
            wordProduct falseWaitReturn
              (falseWaitFirstHitSelectedComparatorWord checks)) ᵥ*
          falseWaitFirstHitBinaryBasis =
        scale • falseWaitFirstHitSelectedComparatorRow checks := by
  rcases falseWaitFirstHitSelectedComparatorConnector_chart checks with
    ⟨connectorScale, connectorScale_ne, connectorChart⟩
  refine ⟨(-2905210800 : ℚ) * connectorScale,
    mul_ne_zero (by norm_num) connectorScale_ne, ?_⟩
  rw [falseWaitFirstHitSelectedComparatorWord, wordProduct_append,
    falseWaitFirstHitChart_conjugatedRow,
    falseWaitFirstHitSingletonPrefix_row, connectorChart,
    falseWaitFirstHitChart_vecMul_smul,
    falseWaitFirstHitSelectedComparatorLoop_row]

/-- Every wait in the selected mismatch comparator is strictly positive. -/
theorem falseWaitFirstHitSelectedComparatorWord_positive
    (checks : List (Bool × Bool)) :
    ∀ wait ∈ falseWaitFirstHitSelectedComparatorWord checks, 0 < wait := by
  have middle :
      ∀ wait ∈ falseWaitFirstHitSelectedComparatorMiddle checks, 0 < wait := by
    intro wait membership
    rw [falseWaitFirstHitSelectedComparatorMiddle, List.mem_append] at membership
    exact membership.elim
      (falseWaitFirstHitSingletonMiddle_positive wait)
      (continuantBalancedReadWord_positive checks wait)
  intro wait membership
  rw [falseWaitFirstHitSelectedComparatorWord, List.mem_append] at membership
  rcases membership with prefix_mem | connector_mem
  · simp only [falseWaitFirstHitSingletonPrefix, List.mem_cons,
      List.not_mem_nil, or_false] at prefix_mem
    omega
  · exact falseWaitFirstHitRayTransportWord_positive middle wait connector_mem

/-- The normalized selected row annihilates the fixed target source exactly when every checked
bit matches. -/
theorem falseWaitFirstHitSelectedComparatorRow_zero_iff
    (checks : List (Bool × Bool)) :
    falseWaitFirstHitSelectedComparatorRow checks ⬝ᵥ
          (wordProduct falseWaitFirstHitBinaryNormalizedLoop
              falseWaitFirstHitSingletonTarget *ᵥ
            falseWaitFirstHitBinarySourceChartVector) = 0 ↔
      ∀ check ∈ checks, check.1 = check.2 := by
  let source :=
    wordProduct falseWaitFirstHitBinaryNormalizedLoop
        falseWaitFirstHitSingletonTarget *ᵥ
      falseWaitFirstHitBinarySourceChartVector
  have source_lower :
      source 1 =
        -123 *
          (falseWaitFirstHitSingletonTarget.map
            falseWaitFirstHitBinaryRatio).prod := by
    dsimp [source]
    rw [falseWaitFirstHitBinaryNormalizedLoop_source]
    rfl
  have source_lower_ne : source 1 ≠ 0 := by
    rw [source_lower]
    exact mul_ne_zero (by norm_num)
      (falseWaitFirstHitBinaryRatioProduct_ne_zero
        falseWaitFirstHitSingletonTarget)
  have base_zero :
      ![1,
          falseWaitFirstHitBinarySourceCoordinate
            falseWaitFirstHitSingletonTarget] ⬝ᵥ source = 0 := by
    exact (falseWaitFirstHitBinarySourceRow_zero_iff
      falseWaitFirstHitSingletonTarget falseWaitFirstHitSingletonTarget).2 rfl
  have incidence :
      falseWaitFirstHitSelectedComparatorRow checks ⬝ᵥ source =
        (625 / 1088 * falseWaitFirstHitSelectedComparatorDefect checks) *
          source 1 := by
    change
      ![1,
          falseWaitFirstHitBinarySourceCoordinate
              falseWaitFirstHitSingletonTarget +
            625 / 1088 * falseWaitFirstHitSelectedComparatorDefect checks] ⬝ᵥ source =
        (625 / 1088 * falseWaitFirstHitSelectedComparatorDefect checks) *
          source 1
    simp [dotProduct, Fin.sum_univ_succ] at base_zero ⊢
    linarith
  change falseWaitFirstHitSelectedComparatorRow checks ⬝ᵥ source = 0 ↔ _
  rw [incidence, mul_eq_zero, or_iff_left source_lower_ne,
    mul_eq_zero, or_iff_right (by norm_num : (625 / 1088 : ℚ) ≠ 0)]
  exact continuantReadDefect_eq_zero_iff checks

/-- Physical selected-comparator incidence is a nonzero scale times its normalized incidence. -/
theorem falseWaitFirstHitSelectedComparatorWord_incidence
    (checks : List (Bool × Bool)) :
    ∃ scale : ℚ, scale ≠ 0 ∧
      falseWaitSeparatorRow ⬝ᵥ
          (wordProduct falseWaitReturn
            (falseWaitFirstHitSelectedComparatorWord checks ++
              falseWaitFirstHitBinaryEncoding falseWaitFirstHitSingletonTarget) *ᵥ
            falseWaitSeparatorColumn) =
        scale *
          (falseWaitFirstHitSelectedComparatorRow checks ⬝ᵥ
            (wordProduct falseWaitFirstHitBinaryNormalizedLoop
                falseWaitFirstHitSingletonTarget *ᵥ
              falseWaitFirstHitBinarySourceChartVector)) := by
  rcases falseWaitFirstHitSelectedComparatorWord_row checks with
    ⟨rowScale, rowScale_ne, rowChart⟩
  exact falseWaitFirstHitChartRow_incidence
    (falseWaitFirstHitSelectedComparatorWord checks)
    (falseWaitFirstHitSelectedComparatorRow checks)
    rowScale rowScale_ne rowChart falseWaitFirstHitSingletonTarget

/-- The physical selected incidence vanishes exactly when every guessed bit matches. -/
theorem falseWaitFirstHitSelectedComparatorWord_zero_iff
    (checks : List (Bool × Bool)) :
    falseWaitSeparatorRow ⬝ᵥ
          (wordProduct falseWaitReturn
            (falseWaitFirstHitSelectedComparatorWord checks ++
              falseWaitFirstHitBinaryEncoding falseWaitFirstHitSingletonTarget) *ᵥ
            falseWaitSeparatorColumn) = 0 ↔
      ∀ check ∈ checks, check.1 = check.2 := by
  rcases falseWaitFirstHitSelectedComparatorWord_incidence checks with
    ⟨scale, scale_ne, incidence⟩
  rw [incidence, mul_eq_zero, or_iff_right scale_ne]
  exact falseWaitFirstHitSelectedComparatorRow_zero_iff checks

/-- Physical word consisting of two opposite, unclocked wrong reads. -/
def falseWaitFirstHitNeutralMismatchWord : List Nat :=
  continuantReadWriteWord false true ++ continuantReadWriteWord true false

/-- The two opposite wrong reads form a nonzero scalar identity. -/
theorem falseWaitFirstHitNeutralMismatchWord_projectiveIdentity :
    ∃ scale : ℚ, scale ≠ 0 ∧
      wordProduct falseWaitReturn falseWaitFirstHitNeutralMismatchWord =
        scale • (1 : Square (Fin 2) ℚ) := by
  simpa [falseWaitFirstHitNeutralMismatchWord, continuantReadWriteWord,
    List.append_assoc] using continuantRadixReaderWord_two_mismatches

/-- Both wrong-read blocks use only strictly positive physical waits. -/
theorem falseWaitFirstHitNeutralMismatchWord_positive :
    ∀ wait ∈ falseWaitFirstHitNeutralMismatchWord, 0 < wait := by
  intro wait membership
  simp only [falseWaitFirstHitNeutralMismatchWord, continuantReadWriteWord,
    List.mem_append] at membership
  rcases membership with falseBlock | trueBlock
  · rcases falseBlock with readerFalse | writerTrue
    · exact continuantRadixReaderWord_positive false wait readerFalse
    · exact continuantRadixEncoding_positive [true] wait (by
        simpa [continuantRadixEncoding] using writerTrue)
  · rcases trueBlock with readerTrue | writerFalse
    · exact continuantRadixReaderWord_positive true wait readerTrue
    · exact continuantRadixEncoding_positive [false] wait (by
        simpa [continuantRadixEncoding] using writerFalse)

/-- The unclocked opposite-mismatch identity has physical length `3265`. -/
theorem falseWaitFirstHitNeutralMismatchWord_length :
    falseWaitFirstHitNeutralMismatchWord.length = 3265 := by
  simp only [falseWaitFirstHitNeutralMismatchWord, continuantReadWriteWord,
    List.length_append]
  norm_num [continuantRadixReaderWord, continuantRepeatWord_length,
    continuantReaderNegativeCount, continuantReaderPositiveCount,
    continuantReaderNegativeWord, continuantReaderPositiveWord,
    continuantReaderExpansionWord, continuantRadixWord]

/-- Singularly punctuated designated singleton zero word. -/
def falseWaitFirstHitSingletonZeroWord : List Nat :=
  [0] ++
    (falseWaitFirstHitSingletonWord ++
      (falseWaitFirstHitBinaryEncoding falseWaitFirstHitSingletonTarget ++ [0]))

/-- Malformed singleton zero word containing two wrong reads with both clocks omitted. -/
def falseWaitFirstHitSingletonNeutralFractureWord : List Nat :=
  [0] ++
    (falseWaitFirstHitSingletonWord ++
      (falseWaitFirstHitNeutralMismatchWord ++
        (falseWaitFirstHitBinaryEncoding falseWaitFirstHitSingletonTarget ++ [0])))

private theorem falseWaitSeparator_sandwich (middle : List Nat) :
    falseWaitReturn 0 * wordProduct falseWaitReturn middle * falseWaitReturn 0 =
      (falseWaitSeparatorRow ⬝ᵥ
          (wordProduct falseWaitReturn middle *ᵥ falseWaitSeparatorColumn)) •
        falseWaitReturn 0 := by
  rw [falseWaitReturn_zero_eq_outer, outer_mul, outer_mul_outer,
    ← Matrix.dotProduct_mulVec]

/-- The singularly punctuated designated singleton word is a physical zero. -/
theorem falseWaitFirstHitSingletonZeroWord_zero :
    wordProduct falseWaitReturn falseWaitFirstHitSingletonZeroWord = 0 := by
  have incidence :=
    (falseWaitFirstHitSingletonWord_zero_iff falseWaitFirstHitSingletonTarget).2 rfl
  rw [falseWaitFirstHitSingletonZeroWord, wordProduct_append,
    wordProduct_append, wordProduct_append]
  simp only [wordProduct_cons, wordProduct_nil, Matrix.mul_one]
  calc
    falseWaitReturn 0 *
          (wordProduct falseWaitReturn falseWaitFirstHitSingletonWord *
            (wordProduct falseWaitReturn
                (falseWaitFirstHitBinaryEncoding falseWaitFirstHitSingletonTarget) *
              falseWaitReturn 0)) =
        falseWaitReturn 0 *
            wordProduct falseWaitReturn
              (falseWaitFirstHitSingletonWord ++
                falseWaitFirstHitBinaryEncoding falseWaitFirstHitSingletonTarget) *
          falseWaitReturn 0 := by
            rw [wordProduct_append]
            simp only [Matrix.mul_assoc]
    _ = (falseWaitSeparatorRow ⬝ᵥ
          (wordProduct falseWaitReturn
              (falseWaitFirstHitSingletonWord ++
                falseWaitFirstHitBinaryEncoding falseWaitFirstHitSingletonTarget) *ᵥ
            falseWaitSeparatorColumn)) • falseWaitReturn 0 :=
        falseWaitSeparator_sandwich _
    _ = 0 := by rw [incidence, zero_smul]

/-- The shorter opposite-mismatch identity already supplies a malformed physical zero through
the singleton selector. -/
theorem falseWaitFirstHitSingletonNeutralFractureWord_zero :
    wordProduct falseWaitReturn falseWaitFirstHitSingletonNeutralFractureWord = 0 := by
  rcases falseWaitFirstHitNeutralMismatchWord_projectiveIdentity with
    ⟨scale, scale_ne, neutralProduct⟩
  have inserted :=
    (wordProduct_zero_iff_projectiveIdentity_insertion falseWaitReturn
      ([0] ++ falseWaitFirstHitSingletonWord)
      falseWaitFirstHitNeutralMismatchWord
      (falseWaitFirstHitBinaryEncoding falseWaitFirstHitSingletonTarget ++ [0])
      scale scale_ne neutralProduct).2
  have base :
      wordProduct falseWaitReturn
        (([0] ++ falseWaitFirstHitSingletonWord) ++
          (falseWaitFirstHitBinaryEncoding falseWaitFirstHitSingletonTarget ++ [0])) = 0 := by
    simpa [falseWaitFirstHitSingletonZeroWord, List.append_assoc] using
      falseWaitFirstHitSingletonZeroWord_zero
  simpa [falseWaitFirstHitSingletonNeutralFractureWord,
    List.append_assoc] using inserted base

/-- The malformed opposite-mismatch zero word is not the designated singleton spelling. -/
theorem falseWaitFirstHitSingletonNeutralFractureWord_ne :
    falseWaitFirstHitSingletonNeutralFractureWord ≠
      falseWaitFirstHitSingletonZeroWord := by
  intro words_eq
  have lengths_eq := congrArg List.length words_eq
  simp only [falseWaitFirstHitSingletonNeutralFractureWord,
    falseWaitFirstHitSingletonZeroWord, List.length_append,
    falseWaitFirstHitNeutralMismatchWord_length] at lengths_eq
  omega

end MatrixMortality.CubicReturn.NonPure
