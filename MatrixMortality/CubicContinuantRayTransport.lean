import MatrixMortality.CubicContinuantReader
import MatrixMortality.CubicContinuantSourceDecoder

/-!
# Common-ray transport for cubic continuant loops

A fixed positive connector transports every upper-triangular terminal loop into the common-ray
chart of the free binary pump. Applied to two previously certified translation loops, it gives
opposite-signed affine digits with one common contraction ratio. The same connector also yields
a short expanding stabilizer, but three of its proper suffixes already reach the accepting ray.
-/

namespace MatrixMortality.CubicReturn.NonPure

open scoped Matrix

/-- Fixed left connector from the terminal triangular chart to the binary-pump common ray. -/
def falseWaitFirstHitRayTransportHead : List Nat := [1, 15, 8]

/-- Fixed right connector from the terminal triangular chart to the binary-pump common ray. -/
def falseWaitFirstHitRayTransportTail : List Nat := [13]

/-- Transport an arbitrary terminal word into a common-ray loop. -/
def falseWaitFirstHitRayTransportWord (middle : List Nat) : List Nat :=
  falseWaitFirstHitRayTransportHead ++ middle ++ falseWaitFirstHitRayTransportTail

/-- Normalized common-ray chart obtained from a terminal upper-triangular matrix. -/
def falseWaitFirstHitRayTransportNormalized
    (upperLeft upperRight lowerRight : ℚ) : Square (Fin 2) ℚ :=
  !![1,
      199 / 408 + 15 / 68 * (upperRight / upperLeft) -
        63 / 340 * (lowerRight / upperLeft);
     0, 9 / 340 * (lowerRight / upperLeft)]

/-- Exact connector action before projective normalization. -/
theorem falseWaitFirstHitRayTransport_raw
    (upperLeft upperRight lowerRight : ℚ) :
    falseWaitFirstHitBinaryBasisInverse *
          wordProduct falseWaitReturn falseWaitFirstHitRayTransportHead *
        !![upperLeft, upperRight; 0, lowerRight] *
          wordProduct falseWaitReturn falseWaitFirstHitRayTransportTail *
      falseWaitFirstHitBinaryBasis =
        !![1057536000 * upperLeft,
            515808000 * upperLeft + 233280000 * upperRight -
              195955200 * lowerRight;
           0, 27993600 * lowerRight] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [falseWaitFirstHitBinaryBasisInverse, falseWaitFirstHitBinaryBasis,
      falseWaitFirstHitRayTransportHead, falseWaitFirstHitRayTransportTail,
      wordProduct_cons, wordProduct_nil, falseWaitReturn_eq_state,
      falseWaitReturnOfState, cubicDefectState, CubicDefectState.next,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

/-- When the leading entry is nonzero, the connector has the displayed normalized affine
chart. -/
theorem falseWaitFirstHitRayTransport_normalized
    {upperLeft upperRight lowerRight : ℚ} (upperLeft_ne : upperLeft ≠ 0) :
    falseWaitFirstHitBinaryBasisInverse *
          wordProduct falseWaitReturn falseWaitFirstHitRayTransportHead *
        !![upperLeft, upperRight; 0, lowerRight] *
          wordProduct falseWaitReturn falseWaitFirstHitRayTransportTail *
      falseWaitFirstHitBinaryBasis =
        (1057536000 * upperLeft) •
          falseWaitFirstHitRayTransportNormalized upperLeft upperRight lowerRight := by
  rw [falseWaitFirstHitRayTransport_raw]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [falseWaitFirstHitRayTransportNormalized, Matrix.smul_apply] <;>
    field_simp [upperLeft_ne] <;>
    ring

/-- The connector transports every physical realization of a nonsingular upper-triangular
terminal loop into its normalized common-ray chart. -/
theorem falseWaitFirstHitRayTransport_projectivelyRealizes
    {middle : List Nat} {upperLeft upperRight lowerRight : ℚ}
    (upperLeft_ne : upperLeft ≠ 0)
    (realizes : continuantProjectivelyRealizes middle
      !![upperLeft, upperRight; 0, lowerRight]) :
    ∃ scale : ℚ, scale ≠ 0 ∧
      falseWaitFirstHitBinaryBasisInverse *
            wordProduct falseWaitReturn
              (falseWaitFirstHitRayTransportWord middle) *
        falseWaitFirstHitBinaryBasis =
          scale •
            falseWaitFirstHitRayTransportNormalized
              upperLeft upperRight lowerRight := by
  rcases realizes with ⟨middleScale, middleScale_ne, middleProduct⟩
  refine ⟨middleScale * (1057536000 * upperLeft),
    mul_ne_zero middleScale_ne (mul_ne_zero (by norm_num) upperLeft_ne), ?_⟩
  rw [falseWaitFirstHitRayTransportWord, wordProduct_append,
    wordProduct_append, middleProduct]
  calc
    _ =
        middleScale •
          (falseWaitFirstHitBinaryBasisInverse *
                wordProduct falseWaitReturn falseWaitFirstHitRayTransportHead *
              !![upperLeft, upperRight; 0, lowerRight] *
                wordProduct falseWaitReturn falseWaitFirstHitRayTransportTail *
            falseWaitFirstHitBinaryBasis) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = middleScale •
          ((1057536000 * upperLeft) •
            falseWaitFirstHitRayTransportNormalized
              upperLeft upperRight lowerRight) := by
          rw [falseWaitFirstHitRayTransport_normalized upperLeft_ne]
    _ = (middleScale * (1057536000 * upperLeft)) •
          falseWaitFirstHitRayTransportNormalized
            upperLeft upperRight lowerRight := by
          rw [smul_smul]

/-- Strict positivity of a terminal word survives the fixed transport connector. -/
theorem falseWaitFirstHitRayTransportWord_positive
    {middle : List Nat} (middle_positive : ∀ wait ∈ middle, 0 < wait) :
    ∀ wait ∈ falseWaitFirstHitRayTransportWord middle, 0 < wait := by
  intro wait membership
  simp only [falseWaitFirstHitRayTransportWord, List.mem_append] at membership
  rcases membership with head_or_middle | tail_mem
  · rcases head_or_middle with head_mem | middle_mem
    · simp only [falseWaitFirstHitRayTransportHead, List.mem_cons,
        List.not_mem_nil, or_false] at head_mem
      omega
    · exact middle_positive wait middle_mem
  · simp only [falseWaitFirstHitRayTransportTail, List.mem_singleton] at tail_mem
    rw [tail_mem]
    norm_num

/-- Positive physical word whose normalized common-ray digit is negative. -/
def falseWaitFirstHitNegativeDigitWord : List Nat :=
  falseWaitFirstHitRayTransportWord (continuantReaderNegativeWord false)

/-- Positive physical word whose normalized common-ray digit is positive. -/
def falseWaitFirstHitPositiveDigitWord : List Nat :=
  falseWaitFirstHitRayTransportWord (continuantReaderPositiveWord false)

/-- Negative common-ray digit obtained from the negative terminal translation. -/
def falseWaitFirstHitNegativeDigitLoop : Square (Fin 2) ℚ :=
  !![1, -4736689 / 16320; 0, 9 / 340]

/-- Positive common-ray digit obtained from the positive terminal translation. -/
def falseWaitFirstHitPositiveDigitLoop : Square (Fin 2) ℚ :=
  !![1, 74677 / 12240; 0, 9 / 340]

/-- The negative-digit physical word realizes its displayed common-ray loop. -/
theorem falseWaitFirstHitNegativeDigitWord_chart :
    ∃ scale : ℚ, scale ≠ 0 ∧
      falseWaitFirstHitBinaryBasisInverse *
            wordProduct falseWaitReturn falseWaitFirstHitNegativeDigitWord *
        falseWaitFirstHitBinaryBasis =
          scale • falseWaitFirstHitNegativeDigitLoop := by
  have transported :=
    falseWaitFirstHitRayTransport_projectivelyRealizes (by norm_num : (1 : ℚ) ≠ 0)
      (continuantReaderNegativeWord_projectivelyRealizes false)
  have normalized :
      falseWaitFirstHitRayTransportNormalized 1 (-189665 / 144) 1 =
        falseWaitFirstHitNegativeDigitLoop := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [falseWaitFirstHitRayTransportNormalized,
        falseWaitFirstHitNegativeDigitLoop]
  rw [normalized] at transported
  simpa [falseWaitFirstHitNegativeDigitWord, continuantReaderNegative] using transported

/-- The positive-digit physical word realizes its displayed common-ray loop. -/
theorem falseWaitFirstHitPositiveDigitWord_chart :
    ∃ scale : ℚ, scale ≠ 0 ∧
      falseWaitFirstHitBinaryBasisInverse *
            wordProduct falseWaitReturn falseWaitFirstHitPositiveDigitWord *
        falseWaitFirstHitBinaryBasis =
          scale • falseWaitFirstHitPositiveDigitLoop := by
  have transported :=
    falseWaitFirstHitRayTransport_projectivelyRealizes (by norm_num : (1 : ℚ) ≠ 0)
      (continuantReaderPositiveWord_projectivelyRealizes false)
  have normalized :
      falseWaitFirstHitRayTransportNormalized 1 (2839 / 108) 1 =
        falseWaitFirstHitPositiveDigitLoop := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [falseWaitFirstHitRayTransportNormalized,
        falseWaitFirstHitPositiveDigitLoop]
  rw [normalized] at transported
  simpa [falseWaitFirstHitPositiveDigitWord, continuantReaderPositive] using transported

/-- Both transported digit spellings use only strictly positive waits. -/
theorem falseWaitFirstHitSignedDigitWords_positive :
    (∀ wait ∈ falseWaitFirstHitNegativeDigitWord, 0 < wait) ∧
      ∀ wait ∈ falseWaitFirstHitPositiveDigitWord, 0 < wait := by
  constructor
  · apply falseWaitFirstHitRayTransportWord_positive
    simp [continuantReaderNegativeWord]
  · apply falseWaitFirstHitRayTransportWord_positive
    simp [continuantReaderPositiveWord]

/-- The two transported digits have the same positive contraction ratio and opposite signs. -/
theorem falseWaitFirstHitSignedDigits_equalRatio :
    falseWaitFirstHitNegativeDigitLoop 1 1 =
        falseWaitFirstHitPositiveDigitLoop 1 1 ∧
      0 < falseWaitFirstHitNegativeDigitLoop 1 1 ∧
      falseWaitFirstHitNegativeDigitLoop 1 1 < 1 ∧
      falseWaitFirstHitNegativeDigitLoop 0 1 < 0 ∧
      0 < falseWaitFirstHitPositiveDigitLoop 0 1 := by
  norm_num [falseWaitFirstHitNegativeDigitLoop,
    falseWaitFirstHitPositiveDigitLoop]

/-- Short common-ray loop obtained by transporting two wait-five returns. -/
def falseWaitFirstHitExpandingLoopWord : List Nat :=
  falseWaitFirstHitRayTransportWord [5, 5]

/-- Normalized affine chart of the short expanding common-ray loop. -/
def falseWaitFirstHitExpandingLoop : Square (Fin 2) ℚ :=
  !![1, 15529 / 6528; 0, 1125 / 1088]

/-- The short physical loop has the displayed expanding common-ray chart. -/
theorem falseWaitFirstHitExpandingLoop_chart :
    falseWaitFirstHitBinaryBasisInverse *
          wordProduct falseWaitReturn falseWaitFirstHitExpandingLoopWord *
      falseWaitFirstHitBinaryBasis =
        (609140736000 : ℚ) • falseWaitFirstHitExpandingLoop := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [falseWaitFirstHitBinaryBasisInverse, falseWaitFirstHitBinaryBasis,
      falseWaitFirstHitExpandingLoopWord, falseWaitFirstHitRayTransportWord,
      falseWaitFirstHitRayTransportHead, falseWaitFirstHitRayTransportTail,
      falseWaitFirstHitExpandingLoop, wordProduct_cons, wordProduct_nil,
      falseWaitReturn_eq_state, falseWaitReturnOfState, cubicDefectState,
      CubicDefectState.next, Matrix.mul_apply, Matrix.smul_apply,
      Fin.sum_univ_succ]

/-- The transverse multiplier of the short loop is genuinely expanding. -/
theorem falseWaitFirstHitExpandingLoop_ratio_gt_one :
    1 < falseWaitFirstHitExpandingLoop 1 1 := by
  norm_num [falseWaitFirstHitExpandingLoop]

/-- The short expanding word stabilizes the pump ray with its exact physical eigenvalue. -/
theorem falseWaitFirstHitExpandingLoop_ray :
    wordProduct falseWaitReturn falseWaitFirstHitExpandingLoopWord *ᵥ ![4, 3] =
      (609140736000 : ℚ) • ![4, 3] := by
  ext coordinate
  fin_cases coordinate <;>
    norm_num [falseWaitFirstHitExpandingLoopWord,
      falseWaitFirstHitRayTransportWord, falseWaitFirstHitRayTransportHead,
      falseWaitFirstHitRayTransportTail, wordProduct_cons, wordProduct_nil,
      falseWaitReturn_eq_state, falseWaitReturnOfState, cubicDefectState,
      CubicDefectState.next, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Every nonempty suffix inside the final wait-five run already reaches the accepting physical
ray, so the expanding loop cannot replace the safe contractions in a first-hit bridge. -/
theorem falseWaitFirstHitExpandingLoop_unsafeSuffixes :
    wordProduct falseWaitReturn [13] *ᵥ ![4, 3] =
        (-408 : ℚ) • ![1, 0] ∧
      wordProduct falseWaitReturn [5, 13] *ᵥ ![4, 3] =
        (9792 : ℚ) • ![1, 0] ∧
      wordProduct falseWaitReturn [5, 5, 13] *ᵥ ![4, 3] =
        (-235008 : ℚ) • ![1, 0] := by
  constructor
  · ext coordinate
    fin_cases coordinate <;>
      norm_num [wordProduct_cons, wordProduct_nil, falseWaitReturn_eq_state,
        falseWaitReturnOfState, cubicDefectState, CubicDefectState.next,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  constructor <;>
    ext coordinate <;>
    fin_cases coordinate <;>
      norm_num [wordProduct_cons, wordProduct_nil, falseWaitReturn_eq_state,
        falseWaitReturnOfState, cubicDefectState, CubicDefectState.next,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The three pole-hitting suffixes are all annihilated by the physical separator row. -/
theorem falseWaitFirstHitExpandingLoop_unsafeSuffixes_accepting :
    falseWaitSeparatorRow ⬝ᵥ
          (wordProduct falseWaitReturn [13] *ᵥ ![4, 3]) = 0 ∧
      falseWaitSeparatorRow ⬝ᵥ
          (wordProduct falseWaitReturn [5, 13] *ᵥ ![4, 3]) = 0 ∧
      falseWaitSeparatorRow ⬝ᵥ
          (wordProduct falseWaitReturn [5, 5, 13] *ᵥ ![4, 3]) = 0 := by
  rw [falseWaitFirstHitExpandingLoop_unsafeSuffixes.1,
    falseWaitFirstHitExpandingLoop_unsafeSuffixes.2.1,
    falseWaitFirstHitExpandingLoop_unsafeSuffixes.2.2]
  norm_num [falseWaitSeparatorRow, dotProduct]

end MatrixMortality.CubicReturn.NonPure
