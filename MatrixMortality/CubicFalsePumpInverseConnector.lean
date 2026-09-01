import MatrixMortality.CubicContinuantTranslationLattice
import MatrixMortality.CubicContinuantTransversePump

/-!
# A positive inverse of the false transverse pump

Two positive bridge words transport one terminal translation to the common-ray chart.  The
result is the exact inverse of the false transverse pump.  The terminal translation has an
explicit nonnegative count certificate.  The right bridge reaches the accepting ray only at
its full length; as a suffix of the transported loop, that endpoint remains an obstruction to
a first-hit compiler.
-/

namespace MatrixMortality.CubicReturn.NonPure

open scoped Matrix

/-- Positive bridge from the terminal ray to the common binary-pump ray. -/
def falseWaitFalsePumpInverseHead : List Nat :=
  [8, 8, 15, 21, 1, 1, 8, 4]

/-- Positive bridge from the common binary-pump ray back to the terminal ray. -/
def falseWaitFalsePumpInverseTail : List Nat :=
  [12, 12, 15, 8, 1, 8, 1, 15, 8, 2]

/-- Nonnegative terminal-translation counts producing the required affine correction. -/
def falseWaitFalsePumpInverseTranslationCounts :
    ContinuantTerminalTranslationCounts where
  positiveFalse := 859
  negativeFalse := 19
  positiveTrue := 489
  negativeTrue := 0

/-- Full positive physical spelling of the false-pump inverse. -/
def falseWaitFalsePumpInverseWord : List Nat :=
  falseWaitFalsePumpInverseHead ++
    (continuantTerminalTranslationWord
      falseWaitFalsePumpInverseTranslationCounts ++ falseWaitFalsePumpInverseTail)

/-- Exact normalized inverse of the false transverse pump. -/
def falseWaitFalsePumpInverseLoop : Square (Fin 2) ℚ :=
  !![1, -1712 / 9; 0, 625]

/-- Primitive physical matrix of the left bridge. -/
def falseWaitFalsePumpInverseHeadMatrix : Square (Fin 2) ℚ :=
  !![432, 26863; 324, 24366]

/-- Primitive physical matrix of the right bridge. -/
def falseWaitFalsePumpInverseTailMatrix : Square (Fin 2) ℚ :=
  !![87, -146; 1080, -1440]

/-- The count certificate gives the affine shift needed by the inverse chart. -/
theorem falseWaitFalsePumpInverseTranslationShift :
    continuantTerminalTranslationShift falseWaitFalsePumpInverseTranslationCounts =
      -76507 / 1080 := by
  norm_num [continuantTerminalTranslationShift,
    falseWaitFalsePumpInverseTranslationCounts]

/-- Exact projective realization of the left bridge. -/
theorem falseWaitFalsePumpInverseHead_projectivelyRealizes :
    continuantProjectivelyRealizes falseWaitFalsePumpInverseHead
      falseWaitFalsePumpInverseHeadMatrix := by
  refine ⟨7739670528000, by norm_num, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [falseWaitFalsePumpInverseHead,
      falseWaitFalsePumpInverseHeadMatrix, wordProduct_cons, wordProduct_nil,
      falseWaitReturn_eq_state, falseWaitReturnOfState, cubicDefectState,
      CubicDefectState.next, Matrix.mul_apply, Matrix.smul_apply,
      Fin.sum_univ_succ]

/-- Exact projective realization of the right bridge. -/
theorem falseWaitFalsePumpInverseTail_projectivelyRealizes :
    continuantProjectivelyRealizes falseWaitFalsePumpInverseTail
      falseWaitFalsePumpInverseTailMatrix := by
  refine ⟨-543324871065600000, by norm_num, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [falseWaitFalsePumpInverseTail,
      falseWaitFalsePumpInverseTailMatrix, wordProduct_cons, wordProduct_nil,
      falseWaitReturn_eq_state, falseWaitReturnOfState, cubicDefectState,
      CubicDefectState.next, Matrix.mul_apply, Matrix.smul_apply,
      Fin.sum_univ_succ]

/-- The two bridge matrices transport the certified terminal shift to the inverse pump chart. -/
theorem falseWaitFalsePumpInverseConnector_chart :
    falseWaitFirstHitBinaryBasisInverse *
          falseWaitFalsePumpInverseHeadMatrix *
        continuantDefectTranslation (-76507 / 1080) *
          falseWaitFalsePumpInverseTailMatrix *
      falseWaitFirstHitBinaryBasis =
        (-9720 : ℚ) • falseWaitFalsePumpInverseLoop := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [falseWaitFirstHitBinaryBasisInverse,
      falseWaitFirstHitBinaryBasis, falseWaitFalsePumpInverseHeadMatrix,
      falseWaitFalsePumpInverseTailMatrix, continuantDefectTranslation,
      falseWaitFalsePumpInverseLoop, Matrix.mul_apply, Matrix.smul_apply,
      Fin.sum_univ_succ]

/-- The full positive word realizes the inverse common-ray chart up to nonzero scale. -/
theorem falseWaitFalsePumpInverseWord_chart :
    ∃ scale : ℚ, scale ≠ 0 ∧
      falseWaitFirstHitBinaryBasisInverse *
            wordProduct falseWaitReturn falseWaitFalsePumpInverseWord *
        falseWaitFirstHitBinaryBasis =
          scale • falseWaitFalsePumpInverseLoop := by
  have terminal := continuantTerminalTranslationWord_projectivelyRealizes
    falseWaitFalsePumpInverseTranslationCounts
  rw [falseWaitFalsePumpInverseTranslationShift] at terminal
  have combined := continuantProjectivelyRealizes_append
    falseWaitFalsePumpInverseHead_projectivelyRealizes
    (continuantProjectivelyRealizes_append terminal
      falseWaitFalsePumpInverseTail_projectivelyRealizes)
  rcases combined with ⟨physicalScale, physicalScale_ne, product⟩
  refine ⟨physicalScale * (-9720),
    mul_ne_zero physicalScale_ne (by norm_num), ?_⟩
  rw [falseWaitFalsePumpInverseWord, product]
  calc
    _ = physicalScale •
        (falseWaitFirstHitBinaryBasisInverse *
              (falseWaitFalsePumpInverseHeadMatrix *
                (continuantDefectTranslation (-76507 / 1080) *
                  falseWaitFalsePumpInverseTailMatrix)) *
            falseWaitFirstHitBinaryBasis) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul]
    _ = physicalScale •
        (falseWaitFirstHitBinaryBasisInverse *
              falseWaitFalsePumpInverseHeadMatrix *
            continuantDefectTranslation (-76507 / 1080) *
              falseWaitFalsePumpInverseTailMatrix *
          falseWaitFirstHitBinaryBasis) := by
          simp only [Matrix.mul_assoc]
    _ = physicalScale • ((-9720 : ℚ) • falseWaitFalsePumpInverseLoop) := by
          rw [falseWaitFalsePumpInverseConnector_chart]
    _ = (physicalScale * (-9720)) • falseWaitFalsePumpInverseLoop := by
          rw [smul_smul]

/-- Every wait in the inverse spelling is strictly positive. -/
theorem falseWaitFalsePumpInverseWord_positive :
    ∀ wait ∈ falseWaitFalsePumpInverseWord, 0 < wait := by
  intro wait membership
  simp only [falseWaitFalsePumpInverseWord, List.mem_append] at membership
  rcases membership with head_mem | terminal_or_tail
  · simp [falseWaitFalsePumpInverseHead] at head_mem
    omega
  rcases terminal_or_tail with terminal_mem | tail_mem
  · exact continuantTerminalTranslationWord_positive
      falseWaitFalsePumpInverseTranslationCounts wait terminal_mem
  · simp [falseWaitFalsePumpInverseTail] at tail_mem
    omega

/-- Exact physical length of the inverse spelling. -/
theorem falseWaitFalsePumpInverseWord_length :
    falseWaitFalsePumpInverseWord.length = 37681 := by
  rw [falseWaitFalsePumpInverseWord, List.length_append, List.length_append,
    continuantTerminalTranslationWord_length]
  norm_num [falseWaitFalsePumpInverseHead, falseWaitFalsePumpInverseTail,
    falseWaitFalsePumpInverseTranslationCounts]

/-- The displayed inverse cancels the false pump on both sides. -/
theorem falseWaitFalsePumpInverseLoop_isInverse :
    falseWaitFalsePumpInverseLoop *
          falseWaitFirstHitBinaryNormalizedLoop false = 1 ∧
      falseWaitFirstHitBinaryNormalizedLoop false *
          falseWaitFalsePumpInverseLoop = 1 := by
  constructor <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [falseWaitFalsePumpInverseLoop,
        falseWaitFirstHitBinaryNormalizedLoop, falseWaitFirstHitBinaryDigit,
        falseWaitFirstHitBinaryRatio, Matrix.mul_apply, Matrix.one_apply,
        Fin.sum_univ_succ]

/-- Multiplying the physical inverse chart by the false pump is projectively scalar identity. -/
theorem falseWaitFalsePumpInverseWord_mul_falsePump_chart :
    ∃ scale : ℚ, scale ≠ 0 ∧
      (falseWaitFirstHitBinaryBasisInverse *
            wordProduct falseWaitReturn falseWaitFalsePumpInverseWord *
          falseWaitFirstHitBinaryBasis) *
          falseWaitFirstHitBinaryNormalizedLoop false =
        scale • (1 : Square (Fin 2) ℚ) := by
  rcases falseWaitFalsePumpInverseWord_chart with ⟨scale, scale_ne, chart⟩
  refine ⟨scale, scale_ne, ?_⟩
  rw [chart, Matrix.smul_mul, falseWaitFalsePumpInverseLoop_isInverse.1]

private theorem falseWaitFirstHitBinaryBasis_reconstruct
    (matrix : Square (Fin 2) ℚ) :
    falseWaitFirstHitBinaryBasis *
          (falseWaitFirstHitBinaryBasisInverse * matrix *
            falseWaitFirstHitBinaryBasis) *
        falseWaitFirstHitBinaryBasisInverse =
      matrix := by
  calc
    _ = (falseWaitFirstHitBinaryBasis * falseWaitFirstHitBinaryBasisInverse) *
          matrix *
        (falseWaitFirstHitBinaryBasis * falseWaitFirstHitBinaryBasisInverse) := by
      simp only [Matrix.mul_assoc]
    _ = matrix := by
      rw [falseWaitFirstHitBinaryBasis_inverse_right]
      simp

private theorem falseWaitFirstHitBinaryBasis_conjugate_mul
    (left right : Square (Fin 2) ℚ) :
    (falseWaitFirstHitBinaryBasis * left * falseWaitFirstHitBinaryBasisInverse) *
        (falseWaitFirstHitBinaryBasis * right * falseWaitFirstHitBinaryBasisInverse) =
      falseWaitFirstHitBinaryBasis * (left * right) *
        falseWaitFirstHitBinaryBasisInverse := by
  calc
    _ = falseWaitFirstHitBinaryBasis *
          (left *
            ((falseWaitFirstHitBinaryBasisInverse * falseWaitFirstHitBinaryBasis) *
              right)) *
        falseWaitFirstHitBinaryBasisInverse := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [falseWaitFirstHitBinaryBasis_inverse_left]
      simp

/-- The positive inverse word followed by the physical false pump is projectively identity. -/
theorem falseWaitFalsePumpInverseWord_push_pop :
    ∃ scale : ℚ, scale ≠ 0 ∧
      wordProduct falseWaitReturn
          (falseWaitFalsePumpInverseWord ++ falseWaitFirstHitBinaryLoop false) =
        scale • (1 : Square (Fin 2) ℚ) := by
  rcases falseWaitFalsePumpInverseWord_chart with
    ⟨inverseScale, inverseScale_ne, inverseChart⟩
  have pumpChart := falseWaitFirstHitBinaryLoop_chart false
  have inversePhysical :
      wordProduct falseWaitReturn falseWaitFalsePumpInverseWord =
        inverseScale •
          (falseWaitFirstHitBinaryBasis * falseWaitFalsePumpInverseLoop *
            falseWaitFirstHitBinaryBasisInverse) := by
    calc
      _ = falseWaitFirstHitBinaryBasis *
            (falseWaitFirstHitBinaryBasisInverse *
                wordProduct falseWaitReturn falseWaitFalsePumpInverseWord *
              falseWaitFirstHitBinaryBasis) *
          falseWaitFirstHitBinaryBasisInverse :=
        (falseWaitFirstHitBinaryBasis_reconstruct _).symm
      _ = falseWaitFirstHitBinaryBasis *
            (inverseScale • falseWaitFalsePumpInverseLoop) *
          falseWaitFirstHitBinaryBasisInverse := by
        rw [inverseChart]
      _ = inverseScale •
          (falseWaitFirstHitBinaryBasis * falseWaitFalsePumpInverseLoop *
            falseWaitFirstHitBinaryBasisInverse) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul]
  have pumpPhysical :
      wordProduct falseWaitReturn (falseWaitFirstHitBinaryLoop false) =
        falseWaitFirstHitBinaryScale false •
          (falseWaitFirstHitBinaryBasis *
              falseWaitFirstHitBinaryNormalizedLoop false *
            falseWaitFirstHitBinaryBasisInverse) := by
    calc
      _ = falseWaitFirstHitBinaryBasis *
            (falseWaitFirstHitBinaryBasisInverse *
                wordProduct falseWaitReturn (falseWaitFirstHitBinaryLoop false) *
              falseWaitFirstHitBinaryBasis) *
          falseWaitFirstHitBinaryBasisInverse :=
        (falseWaitFirstHitBinaryBasis_reconstruct _).symm
      _ = falseWaitFirstHitBinaryBasis *
            (falseWaitFirstHitBinaryScale false •
              falseWaitFirstHitBinaryNormalizedLoop false) *
          falseWaitFirstHitBinaryBasisInverse := by
        rw [pumpChart]
      _ = falseWaitFirstHitBinaryScale false •
          (falseWaitFirstHitBinaryBasis *
              falseWaitFirstHitBinaryNormalizedLoop false *
            falseWaitFirstHitBinaryBasisInverse) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul]
  have conjugated_cancel :
      (falseWaitFirstHitBinaryBasis * falseWaitFalsePumpInverseLoop *
          falseWaitFirstHitBinaryBasisInverse) *
          (falseWaitFirstHitBinaryBasis *
            falseWaitFirstHitBinaryNormalizedLoop false *
              falseWaitFirstHitBinaryBasisInverse) =
        1 := by
    calc
      _ = falseWaitFirstHitBinaryBasis *
            (falseWaitFalsePumpInverseLoop *
              falseWaitFirstHitBinaryNormalizedLoop false) *
          falseWaitFirstHitBinaryBasisInverse :=
        falseWaitFirstHitBinaryBasis_conjugate_mul _ _
      _ = falseWaitFirstHitBinaryBasis * 1 *
          falseWaitFirstHitBinaryBasisInverse := by
        rw [falseWaitFalsePumpInverseLoop_isInverse.1]
      _ = 1 := by
        rw [Matrix.mul_one, falseWaitFirstHitBinaryBasis_inverse_right]
  refine ⟨inverseScale * falseWaitFirstHitBinaryScale false,
    mul_ne_zero inverseScale_ne (falseWaitFirstHitBinaryScale_ne_zero false), ?_⟩
  rw [wordProduct_append, inversePhysical, pumpPhysical]
  calc
    _ = (inverseScale * falseWaitFirstHitBinaryScale false) •
        ((falseWaitFirstHitBinaryBasis * falseWaitFalsePumpInverseLoop *
            falseWaitFirstHitBinaryBasisInverse) *
          (falseWaitFirstHitBinaryBasis *
            falseWaitFirstHitBinaryNormalizedLoop false *
              falseWaitFirstHitBinaryBasisInverse)) := by
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      congr 1
      ring
    _ = (inverseScale * falseWaitFirstHitBinaryScale false) •
        (1 : Square (Fin 2) ℚ) := by
      rw [conjugated_cancel]

/-- A successful physical false pop preserves every subsequent context up to nonzero scale. -/
theorem falseWaitFalsePumpInverseWord_pop_suffix (suffix : List Nat) :
    ∃ scale : ℚ, scale ≠ 0 ∧
      wordProduct falseWaitReturn
          ((falseWaitFalsePumpInverseWord ++ falseWaitFirstHitBinaryLoop false) ++ suffix) =
        scale • wordProduct falseWaitReturn suffix := by
  rcases falseWaitFalsePumpInverseWord_push_pop with ⟨scale, scale_ne, pop⟩
  refine ⟨scale, scale_ne, ?_⟩
  rw [wordProduct_append, pop, Matrix.smul_mul]
  simp

/-- No proper suffix inside the right bridge reaches the accepting ray. -/
theorem falseWaitFalsePumpInverseTail_properSuffixes_nonaccepting :
    falseWaitNoAcceptingSuffixFrom falseWaitFalsePumpInverseTail.tail ![4, 3] := by
  intro suffix membership
  simp only [falseWaitFalsePumpInverseTail, List.tail_cons, List.tails,
    List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [falseWaitSeparatorRow, wordProduct_cons, wordProduct_nil,
      falseWaitReturn_eq_state, falseWaitReturnOfState, cubicDefectState,
      CubicDefectState.next, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

/-- The complete right bridge reaches the accepting ray with its exact scale. -/
theorem falseWaitFalsePumpInverseTail_accepting :
    wordProduct falseWaitReturn falseWaitFalsePumpInverseTail *ᵥ ![4, 3] =
      (48899238395904000000 : ℚ) • ![1, 0] := by
  ext coordinate
  fin_cases coordinate <;>
    norm_num [falseWaitFalsePumpInverseTail, wordProduct_cons, wordProduct_nil,
      falseWaitReturn_eq_state, falseWaitReturnOfState, cubicDefectState,
      CubicDefectState.next, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

end MatrixMortality.CubicReturn.NonPure
