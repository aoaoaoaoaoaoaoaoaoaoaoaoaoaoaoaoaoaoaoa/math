import MatrixMortality.CubicFalsePumpInverseConnector

/-!
# A finite positive inverse of the true transverse pump

An interleaved terminal program realizes the sole large affine correction required by a
new pair of bridge words.  Three copies of the positive false-pump inverse and a fixed
parabolic tuner then turn that connector into the exact inverse of the true transverse
pump.  The final bridge itself reaches the accepting ray, so this algebraic inverse is not
on its own a first-hit-safe reader.
-/

namespace MatrixMortality.CubicReturn.NonPure

open scoped Matrix

/-- Translation inserted before the seven false radix readers. -/
def falseWaitTruePumpInverseShallowCounts :
    ContinuantTerminalTranslationCounts where
  positiveFalse := 114
  negativeFalse := 7
  positiveTrue := 1840
  negativeTrue := 1250

/-- Translation inserted after the seven false radix readers. -/
def falseWaitTruePumpInverseDeepCounts :
    ContinuantTerminalTranslationCounts where
  positiveFalse := 779
  negativeFalse := 23
  positiveTrue := 2415
  negativeTrue := 136

/-- Seven false radix readers, with translations at depths zero and seven. -/
def falseWaitTruePumpInverseTerminalWord : List Nat :=
  continuantTerminalTranslationWord falseWaitTruePumpInverseShallowCounts ++
    (continuantRepeatWord (continuantRadixReaderWord false) 7 ++
      continuantTerminalTranslationWord falseWaitTruePumpInverseDeepCounts)

/-- Exact upper-triangular matrix realized by the interleaved terminal program. -/
def falseWaitTruePumpInverseTerminal : Square (Fin 2) ℚ :=
  !![(25 / 4) ^ 7, 65450709305237 / 98304; 0, 1]

/-- Positive bridge from the terminal chart to the common binary-pump ray. -/
def falseWaitTruePumpInverseHead : List Nat :=
  [8, 3, 1, 12, 15, 8, 38, 6]

/-- Positive bridge from the common binary-pump ray back to the terminal chart. -/
def falseWaitTruePumpInverseTail : List Nat :=
  [1, 4, 15, 8, 12, 12, 15, 8, 12]

/-- Primitive matrix of the left bridge. -/
def falseWaitTruePumpInverseHeadMatrix : Square (Fin 2) ℚ :=
  !![9456, -52543; 7092, 37374]

/-- Primitive matrix of the right bridge. -/
def falseWaitTruePumpInverseTailMatrix : Square (Fin 2) ℚ :=
  !![507, -1508; 150, -200]

/-- The bridge and interleaved terminal program in physical coordinates. -/
def falseWaitTruePumpInverseConnectorWord : List Nat :=
  falseWaitTruePumpInverseHead ++
    (falseWaitTruePumpInverseTerminalWord ++ falseWaitTruePumpInverseTail)

/-- Normalized chart of the bridge and interleaved terminal program. -/
def falseWaitTruePumpInverseConnector : Square (Fin 2) ℚ :=
  !![1, 125367503779 / 3462890625; 0, 2688 / 384765625]

/-- A positive parabolic tuner in the common-ray chart. -/
def falseWaitTruePumpInverseTunerWord : List Nat :=
  [1, 15, 8, 8, 2, 1, 15, 8, 5, 4]

/-- Normalized chart of the tuner. -/
def falseWaitTruePumpInverseTuner : Square (Fin 2) ℚ :=
  continuantDefectTranslation (-241 / 18)

/-- The complete physical true-pump inverse. -/
def falseWaitTruePumpInverseWord : List Nat :=
  continuantRepeatWord falseWaitFalsePumpInverseWord 3 ++
    (continuantRepeatWord falseWaitTruePumpInverseTunerWord 187 ++
      falseWaitTruePumpInverseConnectorWord)

/-- Exact normalized inverse of the true transverse pump. -/
def falseWaitTruePumpInverseLoop : Square (Fin 2) ℚ :=
  !![1, -857689 / 1773; 0, 336000 / 197]

theorem falseWaitTruePumpInverseShallowShift :
    continuantTerminalTranslationShift falseWaitTruePumpInverseShallowCounts =
      6276283 / 3888 := by
  norm_num [continuantTerminalTranslationShift,
    falseWaitTruePumpInverseShallowCounts]

theorem falseWaitTruePumpInverseDeepShift :
    continuantTerminalTranslationShift falseWaitTruePumpInverseDeepCounts =
      271601657 / 151875 := by
  norm_num [continuantTerminalTranslationShift,
    falseWaitTruePumpInverseDeepCounts]

/-- The literal interleaving realizes the required terminal matrix. -/
theorem falseWaitTruePumpInverseTerminalWord_projectivelyRealizes :
    continuantProjectivelyRealizes falseWaitTruePumpInverseTerminalWord
      falseWaitTruePumpInverseTerminal := by
  have reader := continuantRadixReaderWord_projectivelyRealizes false
  have readers := continuantProjectivelyRealizes_repeat reader 7
  have shallow := continuantTerminalTranslationWord_projectivelyRealizes
    falseWaitTruePumpInverseShallowCounts
  have deep := continuantTerminalTranslationWord_projectivelyRealizes
    falseWaitTruePumpInverseDeepCounts
  rw [falseWaitTruePumpInverseShallowShift] at shallow
  rw [falseWaitTruePumpInverseDeepShift] at deep
  have combined := continuantProjectivelyRealizes_append shallow
    (continuantProjectivelyRealizes_append readers deep)
  have normalized :
      continuantDefectTranslation (6276283 / 3888) *
            (continuantRadixReader false ^ 7 *
              continuantDefectTranslation (271601657 / 151875)) =
        falseWaitTruePumpInverseTerminal := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [continuantRadixReader, continuantRadixDigit,
        continuantDefectTranslation, falseWaitTruePumpInverseTerminal,
        Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ, pow_succ]
  rw [normalized] at combined
  simpa only [falseWaitTruePumpInverseTerminalWord] using combined

theorem falseWaitTruePumpInverseHead_projectivelyRealizes :
    continuantProjectivelyRealizes falseWaitTruePumpInverseHead
      falseWaitTruePumpInverseHeadMatrix := by
  refine ⟨9029615616000, by norm_num, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [falseWaitTruePumpInverseHead,
      falseWaitTruePumpInverseHeadMatrix, wordProduct_cons, wordProduct_nil,
      falseWaitReturn_eq_state, falseWaitReturnOfState, cubicDefectState,
      CubicDefectState.next, Matrix.mul_apply, Matrix.smul_apply,
      Fin.sum_univ_succ]

theorem falseWaitTruePumpInverseTail_projectivelyRealizes :
    continuantProjectivelyRealizes falseWaitTruePumpInverseTail
      falseWaitTruePumpInverseTailMatrix := by
  refine ⟨16978902220800000, by norm_num, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [falseWaitTruePumpInverseTail,
      falseWaitTruePumpInverseTailMatrix, wordProduct_cons, wordProduct_nil,
      falseWaitReturn_eq_state, falseWaitReturnOfState, cubicDefectState,
      CubicDefectState.next, Matrix.mul_apply, Matrix.smul_apply,
      Fin.sum_univ_succ]

/-- Exact connector calculation in the common-ray chart. -/
theorem falseWaitTruePumpInverseConnector_normalized :
    falseWaitFirstHitBinaryBasisInverse *
            falseWaitTruePumpInverseHeadMatrix *
          falseWaitTruePumpInverseTerminal *
        falseWaitTruePumpInverseTailMatrix *
      falseWaitFirstHitBinaryBasis =
        (-140679931640625 / 64 : ℚ) • falseWaitTruePumpInverseConnector := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [falseWaitFirstHitBinaryBasisInverse,
      falseWaitFirstHitBinaryBasis, falseWaitTruePumpInverseHeadMatrix,
      falseWaitTruePumpInverseTailMatrix, falseWaitTruePumpInverseTerminal,
      falseWaitTruePumpInverseConnector, Matrix.mul_apply, Matrix.smul_apply,
      Fin.sum_univ_succ]

/-- The physical connector realizes its normalized chart with a nonzero scale. -/
theorem falseWaitTruePumpInverseConnectorWord_chart :
    ∃ scale : ℚ, scale ≠ 0 ∧
      falseWaitFirstHitBinaryBasisInverse *
            wordProduct falseWaitReturn falseWaitTruePumpInverseConnectorWord *
        falseWaitFirstHitBinaryBasis =
          scale • falseWaitTruePumpInverseConnector := by
  have combined := continuantProjectivelyRealizes_append
    falseWaitTruePumpInverseHead_projectivelyRealizes
    (continuantProjectivelyRealizes_append
      falseWaitTruePumpInverseTerminalWord_projectivelyRealizes
      falseWaitTruePumpInverseTail_projectivelyRealizes)
  rcases combined with ⟨physicalScale, physicalScale_ne, product⟩
  refine ⟨physicalScale * (-140679931640625 / 64),
    mul_ne_zero physicalScale_ne (by norm_num), ?_⟩
  rw [falseWaitTruePumpInverseConnectorWord, product]
  calc
    _ = physicalScale •
        (falseWaitFirstHitBinaryBasisInverse *
              (falseWaitTruePumpInverseHeadMatrix *
                (falseWaitTruePumpInverseTerminal *
                  falseWaitTruePumpInverseTailMatrix)) *
            falseWaitFirstHitBinaryBasis) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul]
    _ = physicalScale •
        (falseWaitFirstHitBinaryBasisInverse *
              falseWaitTruePumpInverseHeadMatrix *
            falseWaitTruePumpInverseTerminal *
          falseWaitTruePumpInverseTailMatrix *
        falseWaitFirstHitBinaryBasis) := by
          simp only [Matrix.mul_assoc]
    _ = physicalScale •
        ((-140679931640625 / 64 : ℚ) •
          falseWaitTruePumpInverseConnector) := by
          rw [falseWaitTruePumpInverseConnector_normalized]
    _ = (physicalScale * (-140679931640625 / 64)) •
        falseWaitTruePumpInverseConnector := by
          rw [smul_smul]

/-- The tuner is exactly the displayed parabolic translation in the common-ray chart. -/
theorem falseWaitTruePumpInverseTunerWord_chart :
    falseWaitFirstHitBinaryBasisInverse *
          wordProduct falseWaitReturn falseWaitTruePumpInverseTunerWord *
      falseWaitFirstHitBinaryBasis =
        (12538266255360000000 : ℚ) • falseWaitTruePumpInverseTuner := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [falseWaitTruePumpInverseTunerWord,
      falseWaitTruePumpInverseTuner, continuantDefectTranslation,
      falseWaitFirstHitBinaryBasisInverse, falseWaitFirstHitBinaryBasis,
      wordProduct_cons, wordProduct_nil, falseWaitReturn_eq_state,
      falseWaitReturnOfState, cubicDefectState, CubicDefectState.next,
      Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_succ]

private theorem falseWaitPumpChart_mul
    (left right : Square (Fin 2) ℚ) :
    falseWaitFirstHitBinaryBasisInverse * (left * right) *
        falseWaitFirstHitBinaryBasis =
      (falseWaitFirstHitBinaryBasisInverse * left *
          falseWaitFirstHitBinaryBasis) *
        (falseWaitFirstHitBinaryBasisInverse * right *
          falseWaitFirstHitBinaryBasis) := by
  symm
  calc
    _ = falseWaitFirstHitBinaryBasisInverse *
          (left *
            ((falseWaitFirstHitBinaryBasis * falseWaitFirstHitBinaryBasisInverse) *
              right)) *
        falseWaitFirstHitBinaryBasis := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [falseWaitFirstHitBinaryBasis_inverse_right]
      simp

private theorem falseWaitPumpChart_append
    {leftWord rightWord : List Nat} {left right : Square (Fin 2) ℚ}
    {leftScale rightScale : ℚ}
    (leftChart :
      falseWaitFirstHitBinaryBasisInverse *
            wordProduct falseWaitReturn leftWord *
        falseWaitFirstHitBinaryBasis = leftScale • left)
    (rightChart :
      falseWaitFirstHitBinaryBasisInverse *
            wordProduct falseWaitReturn rightWord *
        falseWaitFirstHitBinaryBasis = rightScale • right) :
    falseWaitFirstHitBinaryBasisInverse *
          wordProduct falseWaitReturn (leftWord ++ rightWord) *
      falseWaitFirstHitBinaryBasis =
        (leftScale * rightScale) • (left * right) := by
  rw [wordProduct_append, falseWaitPumpChart_mul]
  calc
    _ = (leftScale • left) * (rightScale • right) := by
      rw [leftChart, rightChart]
    _ = (leftScale * rightScale) • (left * right) := by
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      congr 1
      ring

private theorem falseWaitPumpChart_repeat
    {word : List Nat} {matrix : Square (Fin 2) ℚ} {scale : ℚ}
    (chart :
      falseWaitFirstHitBinaryBasisInverse *
            wordProduct falseWaitReturn word *
        falseWaitFirstHitBinaryBasis = scale • matrix)
    (repetitions : Nat) :
    falseWaitFirstHitBinaryBasisInverse *
          wordProduct falseWaitReturn (continuantRepeatWord word repetitions) *
      falseWaitFirstHitBinaryBasis =
        scale ^ repetitions • matrix ^ repetitions := by
  induction repetitions with
  | zero =>
      simp [continuantRepeatWord, falseWaitFirstHitBinaryBasis_inverse_left]
  | succ repetitions induction =>
      rw [continuantRepeatWord]
      have appended := falseWaitPumpChart_append chart induction
      simpa [pow_succ'] using appended

/-- The three false inverses, 187 tuners, and connector multiply to the exact true inverse. -/
theorem falseWaitTruePumpInverseNormalized_product :
    falseWaitFalsePumpInverseLoop ^ 3 *
          (falseWaitTruePumpInverseTuner ^ 187 *
            falseWaitTruePumpInverseConnector) =
      falseWaitTruePumpInverseLoop := by
  rw [show falseWaitTruePumpInverseTuner =
    continuantDefectTranslation (-241 / 18) by rfl,
    continuantDefectTranslation_pow]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [falseWaitFalsePumpInverseLoop,
      falseWaitTruePumpInverseTuner, continuantDefectTranslation,
      falseWaitTruePumpInverseConnector, falseWaitTruePumpInverseLoop,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ, pow_succ]

/-- The complete positive physical word realizes the exact true-pump inverse up to nonzero
scale. -/
theorem falseWaitTruePumpInverseWord_chart :
    ∃ scale : ℚ, scale ≠ 0 ∧
      falseWaitFirstHitBinaryBasisInverse *
            wordProduct falseWaitReturn falseWaitTruePumpInverseWord *
        falseWaitFirstHitBinaryBasis =
          scale • falseWaitTruePumpInverseLoop := by
  rcases falseWaitFalsePumpInverseWord_chart with
    ⟨inverseScale, inverseScale_ne, inverseChart⟩
  have inverseRepeat := falseWaitPumpChart_repeat inverseChart 3
  have tunerRepeat := falseWaitPumpChart_repeat
    falseWaitTruePumpInverseTunerWord_chart 187
  rcases falseWaitTruePumpInverseConnectorWord_chart with
    ⟨connectorScale, connectorScale_ne, connectorChart⟩
  have tunerConnector := falseWaitPumpChart_append tunerRepeat connectorChart
  have total := falseWaitPumpChart_append inverseRepeat tunerConnector
  refine ⟨inverseScale ^ 3 *
      (12538266255360000000 ^ 187 * connectorScale),
    mul_ne_zero (pow_ne_zero _ inverseScale_ne)
      (mul_ne_zero (pow_ne_zero _ (by norm_num)) connectorScale_ne), ?_⟩
  rw [falseWaitTruePumpInverseWord, total,
    falseWaitTruePumpInverseNormalized_product]

/-- The displayed normalized loop cancels the true pump on both sides. -/
theorem falseWaitTruePumpInverseLoop_isInverse :
    falseWaitTruePumpInverseLoop *
          falseWaitFirstHitBinaryNormalizedLoop true = 1 ∧
      falseWaitFirstHitBinaryNormalizedLoop true *
          falseWaitTruePumpInverseLoop = 1 := by
  constructor <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [falseWaitTruePumpInverseLoop,
        falseWaitFirstHitBinaryNormalizedLoop, falseWaitFirstHitBinaryDigit,
        falseWaitFirstHitBinaryRatio, Matrix.mul_apply, Matrix.one_apply,
        Fin.sum_univ_succ]

private theorem falseWaitPumpChart_projectiveIdentity_physical
    {word : List Nat} {scale : ℚ} (scale_ne : scale ≠ 0)
    (chart :
      falseWaitFirstHitBinaryBasisInverse *
            wordProduct falseWaitReturn word *
        falseWaitFirstHitBinaryBasis =
          scale • (1 : Square (Fin 2) ℚ)) :
    ∃ physicalScale : ℚ, physicalScale ≠ 0 ∧
      wordProduct falseWaitReturn word =
        physicalScale • (1 : Square (Fin 2) ℚ) := by
  refine ⟨scale, scale_ne, ?_⟩
  calc
    _ = falseWaitFirstHitBinaryBasis *
          (falseWaitFirstHitBinaryBasisInverse *
              wordProduct falseWaitReturn word *
            falseWaitFirstHitBinaryBasis) *
        falseWaitFirstHitBinaryBasisInverse := by
      symm
      calc
        _ = (falseWaitFirstHitBinaryBasis * falseWaitFirstHitBinaryBasisInverse) *
              wordProduct falseWaitReturn word *
            (falseWaitFirstHitBinaryBasis *
              falseWaitFirstHitBinaryBasisInverse) := by
          simp only [Matrix.mul_assoc]
        _ = _ := by
          rw [falseWaitFirstHitBinaryBasis_inverse_right]
          simp
    _ = falseWaitFirstHitBinaryBasis *
          (scale • (1 : Square (Fin 2) ℚ)) *
        falseWaitFirstHitBinaryBasisInverse := by
      rw [chart]
    _ = scale • (1 : Square (Fin 2) ℚ) := by
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      rw [falseWaitFirstHitBinaryBasis_inverse_right]

/-- The positive true inverse followed by the physical true pump is projectively identity. -/
theorem falseWaitTruePumpInverseWord_push_pop :
    ∃ scale : ℚ, scale ≠ 0 ∧
      wordProduct falseWaitReturn
          (falseWaitTruePumpInverseWord ++ falseWaitFirstHitBinaryLoop true) =
        scale • (1 : Square (Fin 2) ℚ) := by
  rcases falseWaitTruePumpInverseWord_chart with
    ⟨inverseScale, inverseScale_ne, inverseChart⟩
  have combined := falseWaitPumpChart_append inverseChart
    (falseWaitFirstHitBinaryLoop_chart true)
  rw [falseWaitTruePumpInverseLoop_isInverse.1] at combined
  exact falseWaitPumpChart_projectiveIdentity_physical
    (mul_ne_zero inverseScale_ne (falseWaitFirstHitBinaryScale_ne_zero true)) combined

/-- A successful physical true pop preserves every subsequent context up to nonzero scale. -/
theorem falseWaitTruePumpInverseWord_pop_suffix (suffix : List Nat) :
    ∃ scale : ℚ, scale ≠ 0 ∧
      wordProduct falseWaitReturn
          ((falseWaitTruePumpInverseWord ++ falseWaitFirstHitBinaryLoop true) ++ suffix) =
        scale • wordProduct falseWaitReturn suffix := by
  rcases falseWaitTruePumpInverseWord_push_pop with ⟨scale, scale_ne, pop⟩
  refine ⟨scale, scale_ne, ?_⟩
  rw [wordProduct_append, pop, Matrix.smul_mul]
  simp

/-- Every wait in the terminal program is positive. -/
theorem falseWaitTruePumpInverseTerminalWord_positive :
    ∀ wait ∈ falseWaitTruePumpInverseTerminalWord, 0 < wait := by
  intro wait membership
  simp only [falseWaitTruePumpInverseTerminalWord, List.mem_append] at membership
  rcases membership with shallow | readers_or_deep
  · exact continuantTerminalTranslationWord_positive
      falseWaitTruePumpInverseShallowCounts wait shallow
  rcases readers_or_deep with readers | deep
  · exact continuantRepeatWord_positive
      (continuantRadixReaderWord_positive false) 7 wait readers
  · exact continuantTerminalTranslationWord_positive
      falseWaitTruePumpInverseDeepCounts wait deep

private theorem falseWaitTruePumpInverseTunerWord_positive :
    ∀ wait ∈ falseWaitTruePumpInverseTunerWord, 0 < wait := by
  intro wait membership
  simp [falseWaitTruePumpInverseTunerWord] at membership
  omega

/-- Every wait in the complete true-pump inverse is positive. -/
theorem falseWaitTruePumpInverseWord_positive :
    ∀ wait ∈ falseWaitTruePumpInverseWord, 0 < wait := by
  intro wait membership
  simp only [falseWaitTruePumpInverseWord, List.mem_append] at membership
  rcases membership with inverse | rest
  · exact continuantRepeatWord_positive falseWaitFalsePumpInverseWord_positive
      3 wait inverse
  rcases rest with tuner | connector
  · exact continuantRepeatWord_positive falseWaitTruePumpInverseTunerWord_positive
      187 wait tuner
  simp only [falseWaitTruePumpInverseConnectorWord, List.mem_append] at connector
  rcases connector with head | rest
  · simp [falseWaitTruePumpInverseHead] at head
    omega
  rcases rest with terminal | tail
  · exact falseWaitTruePumpInverseTerminalWord_positive wait terminal
  · simp [falseWaitTruePumpInverseTail] at tail
    omega

private theorem falseWaitRadixReaderFalse_length :
    (continuantRadixReaderWord false).length = 2089 := by
  simp [continuantRadixReaderWord, continuantRepeatWord_length,
    continuantReaderNegativeCount, continuantReaderPositiveCount,
    continuantReaderNegativeWord, continuantReaderPositiveWord,
    continuantReaderExpansionWord]

/-- Exact physical length of the interleaved terminal program. -/
theorem falseWaitTruePumpInverseTerminalWord_length :
    falseWaitTruePumpInverseTerminalWord.length = 191580 := by
  rw [falseWaitTruePumpInverseTerminalWord, List.length_append,
    List.length_append, continuantRepeatWord_length,
    continuantTerminalTranslationWord_length,
    continuantTerminalTranslationWord_length,
    falseWaitRadixReaderFalse_length]
  norm_num [falseWaitTruePumpInverseShallowCounts,
    falseWaitTruePumpInverseDeepCounts]

/-- Exact physical length of the complete true-pump inverse. -/
theorem falseWaitTruePumpInverseWord_length :
    falseWaitTruePumpInverseWord.length = 306510 := by
  rw [falseWaitTruePumpInverseWord, List.length_append, List.length_append,
    continuantRepeatWord_length, continuantRepeatWord_length,
    falseWaitFalsePumpInverseWord_length,
    falseWaitTruePumpInverseConnectorWord, List.length_append,
    List.length_append, falseWaitTruePumpInverseTerminalWord_length]
  norm_num [falseWaitTruePumpInverseTunerWord,
    falseWaitTruePumpInverseHead, falseWaitTruePumpInverseTail]

/-- The final bridge sends the common pump ray to the accepting ray. -/
theorem falseWaitTruePumpInverseTail_accepting :
    wordProduct falseWaitReturn falseWaitTruePumpInverseTail *ᵥ ![4, 3] =
      (-42379339943116800000 : ℚ) • ![1, 0] := by
  ext i
  fin_cases i <;>
    norm_num [falseWaitTruePumpInverseTail, wordProduct_cons, wordProduct_nil,
      falseWaitReturn_eq_state, falseWaitReturnOfState, cubicDefectState,
      CubicDefectState.next, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

/-- Dropping the first wait from the final bridge still reaches the accepting ray. -/
theorem falseWaitTruePumpInverseTail_tail_accepting :
    wordProduct falseWaitReturn falseWaitTruePumpInverseTail.tail *ᵥ ![4, 3] =
      (-1765805830963200000 : ℚ) • ![1, 0] := by
  ext i
  fin_cases i <;>
    norm_num [falseWaitTruePumpInverseTail, wordProduct_cons, wordProduct_nil,
      falseWaitReturn_eq_state, falseWaitReturnOfState, cubicDefectState,
      CubicDefectState.next, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

/-- An accepting tail makes every nonempty left extension fail the suffix-safety predicate. -/
theorem falseWaitNoAcceptingSuffixFrom_append_of_tail_accepting
    (initial tail : List Nat) (ray : Fin 2 → ℚ)
    (tail_accepting :
      falseWaitSeparatorRow ⬝ᵥ
        (wordProduct falseWaitReturn tail *ᵥ ray) = 0) :
    ¬ falseWaitNoAcceptingSuffixFrom (initial ++ tail) ray := by
  intro safe
  have tail_mem : tail ∈ (initial ++ tail).tails :=
    (List.mem_tails tail (initial ++ tail)).2 ⟨initial, rfl⟩
  exact (safe tail tail_mem) tail_accepting

/-- Every terminal-to-common-ray connector whose right bridge lands on the accepting terminal
ray is excluded from a first-hit reader, independently of its head and terminal program. -/
theorem falseWaitTerminalConnector_not_noAcceptingSuffix
    (head program tail : List Nat) (ray : Fin 2 → ℚ) (scale : ℚ)
    (tail_ray :
      wordProduct falseWaitReturn tail *ᵥ ray = scale • ![1, 0]) :
    ¬ falseWaitNoAcceptingSuffixFrom (head ++ program ++ tail) ray := by
  have tail_accepting :
      falseWaitSeparatorRow ⬝ᵥ
        (wordProduct falseWaitReturn tail *ᵥ ray) = 0 := by
    rw [tail_ray, dotProduct_smul]
    simp [falseWaitSeparatorRow, dotProduct]
  simpa [List.append_assoc] using
    falseWaitNoAcceptingSuffixFrom_append_of_tail_accepting
      (head ++ program) tail ray tail_accepting

/-- Consequently the algebraic inverse is not a first-hit-safe reader from the common ray:
its final bridge is already an accepting proper suffix. -/
theorem falseWaitTruePumpInverseWord_not_noAcceptingSuffix :
    ¬ falseWaitNoAcceptingSuffixFrom falseWaitTruePumpInverseWord ![4, 3] := by
  simpa [falseWaitTruePumpInverseWord, falseWaitTruePumpInverseConnectorWord,
    List.append_assoc] using
    falseWaitTerminalConnector_not_noAcceptingSuffix
      (continuantRepeatWord falseWaitFalsePumpInverseWord 3 ++
        (continuantRepeatWord falseWaitTruePumpInverseTunerWord 187 ++
          falseWaitTruePumpInverseHead))
      falseWaitTruePumpInverseTerminalWord falseWaitTruePumpInverseTail ![4, 3]
      (-42379339943116800000) falseWaitTruePumpInverseTail_accepting

end MatrixMortality.CubicReturn.NonPure
