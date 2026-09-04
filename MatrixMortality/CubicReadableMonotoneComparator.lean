import MatrixMortality.CubicContinuantReadableSourceSelector
import MatrixMortality.CubicContinuantNeutrality

/-!
# A monotone comparator inside the readable cubic source selector

Each corrected reader-writer block is projectively the identity when its bits agree and the
same positive unit translation when they differ.  Appending these blocks to the height-five
selector middle therefore moves the selected row in only one direction.
-/

namespace MatrixMortality.CubicReturn.NonPure

open scoped Matrix

/-- Positive terminal spelling of the correction `173 / 48`. -/
def falseWaitMonotonePositiveCorrectionCounts :
    ContinuantTerminalTranslationCounts :=
  ⟨391, 9, 596, 1500⟩

/-- Positive terminal spelling of the correction `-77 / 48`. -/
def falseWaitMonotoneNegativeCorrectionCounts :
    ContinuantTerminalTranslationCounts :=
  ⟨606, 12, 177, 1125⟩

/-- Correction attached to one reader-writer block. -/
def falseWaitMonotoneCorrectionCounts
    (check : Bool × Bool) : ContinuantTerminalTranslationCounts :=
  match check with
  | (false, true) => falseWaitMonotonePositiveCorrectionCounts
  | (true, false) => falseWaitMonotoneNegativeCorrectionCounts
  | _ => ⟨0, 0, 0, 0⟩

/-- One corrected physical reader-writer comparison. -/
def falseWaitMonotoneCheckWord (check : Bool × Bool) : List Nat :=
  continuantReadWriteWord check.1 check.2 ++
    continuantTerminalTranslationWord
      (falseWaitMonotoneCorrectionCounts check)

/-- A positive comparison schedule whose normalized translation counts mismatches. -/
def falseWaitMonotoneComparatorWord
    (checks : List (Bool × Bool)) : List Nat :=
  checks.flatMap falseWaitMonotoneCheckWord

/-- Number of mismatching reader-writer pairs. -/
def falseWaitMonotoneMismatchCount : List (Bool × Bool) → Nat
  | [] => 0
  | check :: checks =>
      (if check.1 = check.2 then 0 else 1) +
        falseWaitMonotoneMismatchCount checks

/-- Height-five selector middle followed by the monotone comparison schedule. -/
def falseWaitReadableMonotoneMiddleWord
    (checks : List (Bool × Bool)) : List Nat :=
  falseWaitReadableSelectorMiddleWord ++
    falseWaitMonotoneComparatorWord checks

/-- Complete row word for the readable selector and monotone comparison schedule. -/
def falseWaitOneProbeMonotoneSelectorWord
    (checks : List (Bool × Bool)) : List Nat :=
  (falseWaitFirstHitSingletonPrefix ++ falseWaitReadableSelectorPreWord) ++
    falseWaitFirstHitRayTransportWord
      (falseWaitReadableMonotoneMiddleWord checks)

/-- Full readable-memory gate with a fixed `00` marker before its payload. -/
def falseWaitReadableMonotoneGateWord
    (checks : List (Bool × Bool)) (payload : List Bool) : List Nat :=
  falseWaitOneProbeMonotoneSelectorWord checks ++
    (falseWaitReadableSelectorCancellationWord ++
      falseWaitReadableSourceMemoryWord
        (falseWaitFirstHitSingletonTarget ++ payload))

/-- Normalized terminal matrix of the height-five middle and monotone comparison schedule. -/
def falseWaitReadableMonotoneMiddle
    (checks : List (Bool × Bool)) : Square (Fin 2) ℚ :=
  !![1024,
      -38166180409 / 90 +
        1024 * falseWaitMonotoneMismatchCount checks;
     0, 9765625]

/-- Common-ray chart of the height-five middle and monotone comparison schedule. -/
def falseWaitReadableMonotoneLoop
    (checks : List (Bool × Bool)) : Square (Fin 2) ℚ :=
  falseWaitFirstHitRayTransportNormalized 1024
    (-38166180409 / 90 +
      1024 * falseWaitMonotoneMismatchCount checks)
    9765625

/-- Exact selected row, shifted monotonically by the mismatch count. -/
def falseWaitReadableMonotoneRow
    (checks : List (Bool × Bool)) : Fin 2 → ℚ :=
  ![1,
    -4133081074213 / 44425216 +
      15 / 68 * falseWaitMonotoneMismatchCount checks]

/-- The positive correction count vectors have their claimed shifts. -/
theorem falseWaitMonotoneCorrection_shifts :
    continuantTerminalTranslationShift
        falseWaitMonotonePositiveCorrectionCounts = 173 / 48 ∧
      continuantTerminalTranslationShift
        falseWaitMonotoneNegativeCorrectionCounts = -77 / 48 := by
  constructor <;>
    norm_num [falseWaitMonotonePositiveCorrectionCounts,
      falseWaitMonotoneNegativeCorrectionCounts,
      continuantTerminalTranslationShift]

private theorem continuantProjectivelyRealizes_of_scaled
    {word : List Nat} {matrix : Square (Fin 2) ℚ} {scale : ℚ}
    (scale_ne : scale ≠ 0)
    (realizes : continuantProjectivelyRealizes word (scale • matrix)) :
    continuantProjectivelyRealizes word matrix := by
  rcases realizes with ⟨physicalScale, physicalScale_ne, product⟩
  refine ⟨physicalScale * scale, mul_ne_zero physicalScale_ne scale_ne, ?_⟩
  rw [product, smul_smul]

/-- One corrected check is projectively the identity on a match and translation by one on a
mismatch. -/
theorem falseWaitMonotoneCheckWord_projectivelyRealizes
    (check : Bool × Bool) :
    continuantProjectivelyRealizes (falseWaitMonotoneCheckWord check)
      (continuantDefectTranslation
        (if check.1 = check.2 then 0 else 1)) := by
  rcases check with ⟨guess, actual⟩
  cases guess
  · cases actual
    · have combined := continuantProjectivelyRealizes_append
        (continuantReadWriteWord_projectivelyRealizes false false)
        (continuantTerminalTranslationWord_projectivelyRealizes
          (falseWaitMonotoneCorrectionCounts (false, false)))
      have normalized :
          (continuantRadixReader false * continuantRadixGenerator false) *
              continuantDefectTranslation
                (continuantTerminalTranslationShift
                  (falseWaitMonotoneCorrectionCounts (false, false))) =
            (25 : ℚ) • continuantDefectTranslation 0 := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          norm_num [falseWaitMonotoneCorrectionCounts,
            continuantTerminalTranslationShift, continuantRadixReader,
            continuantRadixGenerator, continuantRadixDigit,
            continuantDefectTranslation, Matrix.mul_apply, Matrix.smul_apply,
            Fin.sum_univ_succ]
      rw [normalized] at combined
      apply continuantProjectivelyRealizes_of_scaled (by norm_num : (25 : ℚ) ≠ 0)
      simpa [falseWaitMonotoneCheckWord,
        falseWaitMonotoneCorrectionCounts] using combined
    · have combined := continuantProjectivelyRealizes_append
        (continuantReadWriteWord_projectivelyRealizes false true)
        (continuantTerminalTranslationWord_projectivelyRealizes
          falseWaitMonotonePositiveCorrectionCounts)
      rw [falseWaitMonotoneCorrection_shifts.1] at combined
      have normalized :
          (continuantRadixReader false * continuantRadixGenerator true) *
              continuantDefectTranslation (173 / 48) =
            (25 : ℚ) • continuantDefectTranslation 1 := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          norm_num [continuantRadixReader, continuantRadixGenerator,
            continuantRadixDigit, continuantDefectTranslation,
            Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_succ]
      rw [normalized] at combined
      apply continuantProjectivelyRealizes_of_scaled (by norm_num : (25 : ℚ) ≠ 0)
      simpa [falseWaitMonotoneCheckWord,
        falseWaitMonotoneCorrectionCounts] using combined
  · cases actual
    · have combined := continuantProjectivelyRealizes_append
        (continuantReadWriteWord_projectivelyRealizes true false)
        (continuantTerminalTranslationWord_projectivelyRealizes
          falseWaitMonotoneNegativeCorrectionCounts)
      rw [falseWaitMonotoneCorrection_shifts.2] at combined
      have normalized :
          (continuantRadixReader true * continuantRadixGenerator false) *
              continuantDefectTranslation (-77 / 48) =
            (25 : ℚ) • continuantDefectTranslation 1 := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          norm_num [continuantRadixReader, continuantRadixGenerator,
            continuantRadixDigit, continuantDefectTranslation,
            Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_succ]
      rw [normalized] at combined
      apply continuantProjectivelyRealizes_of_scaled (by norm_num : (25 : ℚ) ≠ 0)
      simpa [falseWaitMonotoneCheckWord,
        falseWaitMonotoneCorrectionCounts] using combined
    · have combined := continuantProjectivelyRealizes_append
        (continuantReadWriteWord_projectivelyRealizes true true)
        (continuantTerminalTranslationWord_projectivelyRealizes
          (falseWaitMonotoneCorrectionCounts (true, true)))
      have normalized :
          (continuantRadixReader true * continuantRadixGenerator true) *
              continuantDefectTranslation
                (continuantTerminalTranslationShift
                  (falseWaitMonotoneCorrectionCounts (true, true))) =
            (25 : ℚ) • continuantDefectTranslation 0 := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          norm_num [falseWaitMonotoneCorrectionCounts,
            continuantTerminalTranslationShift, continuantRadixReader,
            continuantRadixGenerator, continuantRadixDigit,
            continuantDefectTranslation, Matrix.mul_apply, Matrix.smul_apply,
            Fin.sum_univ_succ]
      rw [normalized] at combined
      apply continuantProjectivelyRealizes_of_scaled (by norm_num : (25 : ℚ) ≠ 0)
      simpa [falseWaitMonotoneCheckWord,
        falseWaitMonotoneCorrectionCounts] using combined

private theorem continuantDefectTranslation_add (left right : ℚ) :
    continuantDefectTranslation left * continuantDefectTranslation right =
      continuantDefectTranslation (left + right) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [continuantDefectTranslation, Matrix.mul_apply,
      Fin.sum_univ_succ, add_comm]

/-- The complete corrected schedule realizes translation by its mismatch count. -/
theorem falseWaitMonotoneComparatorWord_projectivelyRealizes
    (checks : List (Bool × Bool)) :
    continuantProjectivelyRealizes (falseWaitMonotoneComparatorWord checks)
      (continuantDefectTranslation (falseWaitMonotoneMismatchCount checks)) := by
  induction checks with
  | nil =>
      refine ⟨1, one_ne_zero, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [falseWaitMonotoneComparatorWord,
          falseWaitMonotoneMismatchCount, continuantDefectTranslation,
          Matrix.one_apply]
  | cons check checks induction =>
      have combined := continuantProjectivelyRealizes_append
        (falseWaitMonotoneCheckWord_projectivelyRealizes check) induction
      rw [continuantDefectTranslation_add] at combined
      simpa [falseWaitMonotoneComparatorWord,
        falseWaitMonotoneMismatchCount] using combined

/-- The mismatch count vanishes exactly when every guessed bit equals its writer. -/
theorem falseWaitMonotoneMismatchCount_eq_zero_iff
    (checks : List (Bool × Bool)) :
    falseWaitMonotoneMismatchCount checks = 0 ↔
      ∀ check ∈ checks, check.1 = check.2 := by
  induction checks with
  | nil => simp [falseWaitMonotoneMismatchCount]
  | cons check checks induction =>
      rcases check with ⟨guess, actual⟩
      cases guess <;> cases actual <;>
        simp [falseWaitMonotoneMismatchCount, induction]

/-- The height-five selector middle followed by the corrected schedule has its displayed
terminal matrix. -/
theorem falseWaitReadableMonotoneMiddleWord_projectivelyRealizes
    (checks : List (Bool × Bool)) :
    continuantProjectivelyRealizes
      (falseWaitReadableMonotoneMiddleWord checks)
      (falseWaitReadableMonotoneMiddle checks) := by
  have combined := continuantProjectivelyRealizes_append
    falseWaitReadableSelectorMiddleWord_projectivelyRealizes
    (falseWaitMonotoneComparatorWord_projectivelyRealizes checks)
  have normalized :
      falseWaitReadableSelectorMiddle *
          continuantDefectTranslation (falseWaitMonotoneMismatchCount checks) =
        falseWaitReadableMonotoneMiddle checks := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [falseWaitReadableSelectorMiddle,
          falseWaitReadableMonotoneMiddle, continuantDefectTranslation,
          Matrix.mul_apply, Fin.sum_univ_succ] <;>
        ring)
  rw [normalized] at combined
  simpa only [falseWaitReadableMonotoneMiddleWord] using combined

/-- Ray transport exposes the monotone schedule in the displayed common-ray chart. -/
theorem falseWaitReadableMonotoneConnector_chart
    (checks : List (Bool × Bool)) :
    ∃ scale : ℚ, scale ≠ 0 ∧
      falseWaitFirstHitBinaryBasisInverse *
            wordProduct falseWaitReturn
              (falseWaitFirstHitRayTransportWord
                (falseWaitReadableMonotoneMiddleWord checks)) *
        falseWaitFirstHitBinaryBasis =
          scale • falseWaitReadableMonotoneLoop checks := by
  have transported := falseWaitFirstHitRayTransport_projectivelyRealizes
    (by norm_num : (1024 : ℚ) ≠ 0)
    (falseWaitReadableMonotoneMiddleWord_projectivelyRealizes checks)
  simpa [falseWaitReadableMonotoneMiddle,
    falseWaitReadableMonotoneLoop] using transported

/-- The fixed prefix turns the transported mismatch count into a positive row shift. -/
theorem falseWaitReadableSelectorPrefixRow_mul_monotoneLoop
    (checks : List (Bool × Bool)) :
    falseWaitReadableSelectorPrefixRow ᵥ* falseWaitReadableMonotoneLoop checks =
      falseWaitReadableMonotoneRow checks := by
  ext coordinate
  fin_cases coordinate <;>
    (simp [falseWaitReadableSelectorPrefixRow,
        falseWaitReadableMonotoneLoop, falseWaitReadableMonotoneRow,
        falseWaitFirstHitRayTransportNormalized, Matrix.vecMul,
        dotProduct, Fin.sum_univ_succ] <;>
      ring)

/-- The complete monotone selector has its displayed nonzero chart row. -/
theorem falseWaitOneProbeMonotoneSelectorWord_row
    (checks : List (Bool × Bool)) :
    ∃ scale : ℚ, scale ≠ 0 ∧
      (falseWaitSeparatorRow ᵥ*
            wordProduct falseWaitReturn
              (falseWaitOneProbeMonotoneSelectorWord checks)) ᵥ*
          falseWaitFirstHitBinaryBasis =
        scale • falseWaitReadableMonotoneRow checks := by
  rcases falseWaitReadableSelectorPrefix_row with
    ⟨prefixScale, prefixScale_ne, prefixRow⟩
  rcases falseWaitReadableMonotoneConnector_chart checks with
    ⟨connectorScale, connectorScale_ne, connectorChart⟩
  refine ⟨prefixScale * connectorScale,
    mul_ne_zero prefixScale_ne connectorScale_ne, ?_⟩
  rw [falseWaitOneProbeMonotoneSelectorWord, wordProduct_append,
    falseWaitFirstHitChart_conjugatedRow, prefixRow, connectorChart,
    falseWaitFirstHitChart_vecMul_smul,
    falseWaitReadableSelectorPrefixRow_mul_monotoneLoop]

private theorem falseWaitFirstHitBinaryAffineCode_append
    (left right : List Bool) :
    falseWaitFirstHitBinaryAffineCode (left ++ right) =
      falseWaitFirstHitBinaryAffineCode left +
        (left.map falseWaitFirstHitBinaryRatio).prod *
          falseWaitFirstHitBinaryAffineCode right := by
  induction left with
  | nil => simp [falseWaitFirstHitBinaryAffineCode]
  | cons bit bits induction =>
      simp only [List.cons_append, falseWaitFirstHitBinaryAffineCode,
        List.map_cons, List.prod_cons, induction]
      ring

/-- Exact one-wait coordinate of the empty payload. -/
theorem falseWaitOneProbeCoordinate_nil :
    falseWaitOneProbeCoordinate [] = falseWaitOneProbeOffset := by
  norm_num [falseWaitOneProbeCoordinate,
    falseWaitFirstHitBinaryAffineCode]

/-- Exact one-wait coordinate selected by the `00` marker. -/
theorem falseWaitOneProbeCoordinate_singletonTarget :
    falseWaitOneProbeCoordinate falseWaitFirstHitSingletonTarget =
      4133081074213 / 44425216 := by
  norm_num [falseWaitFirstHitSingletonTarget, falseWaitOneProbeCoordinate,
    falseWaitOneProbeOffset, falseWaitFirstHitBinaryAffineCode,
    falseWaitFirstHitBinaryDigit, falseWaitFirstHitBinaryRatio]

/-- Prefixing the `00` marker magnifies the payload's displacement from the probe offset by
`625²`. -/
theorem falseWaitOneProbeCoordinate_singletonTarget_append
    (payload : List Bool) :
    falseWaitOneProbeCoordinate
        (falseWaitFirstHitSingletonTarget ++ payload) =
      falseWaitOneProbeCoordinate falseWaitFirstHitSingletonTarget +
        390625 *
          (falseWaitOneProbeCoordinate payload - falseWaitOneProbeOffset) := by
  have ratio_ne := falseWaitFirstHitBinaryRatioProduct_ne_zero payload
  rw [falseWaitOneProbeCoordinate, falseWaitOneProbeCoordinate,
    falseWaitOneProbeCoordinate, List.reverse_append,
    falseWaitFirstHitBinaryAffineCode_append]
  simp only [falseWaitFirstHitSingletonTarget, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.map_append, List.prod_append,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    falseWaitFirstHitBinaryRatio]
  rw [List.map_reverse, List.prod_reverse]
  norm_num [falseWaitFirstHitBinaryAffineCode,
    falseWaitFirstHitBinaryDigit, falseWaitOneProbeOffset]
  field_simp [ratio_ne]
  ring

/-- The marker-prefixed coordinate moves strictly above its marker value exactly when the
payload is nonempty. -/
theorem falseWaitOneProbeCoordinate_singletonTarget_append_pos
    {payload : List Bool} (payload_ne : payload ≠ []) :
    falseWaitOneProbeCoordinate falseWaitFirstHitSingletonTarget <
      falseWaitOneProbeCoordinate
        (falseWaitFirstHitSingletonTarget ++ payload) := by
  rw [falseWaitOneProbeCoordinate_singletonTarget_append]
  have payload_positive := falseWaitOneProbeCoordinate_pos payload_ne
  have offset_negative : falseWaitOneProbeOffset < 0 := by
    norm_num [falseWaitOneProbeOffset]
  linarith

/-- The marker-prefixed coordinate gap is nonnegative and vanishes only on the empty payload. -/
theorem falseWaitOneProbeCoordinate_singletonTarget_append_gap
    (payload : List Bool) :
    0 ≤
        falseWaitOneProbeCoordinate
            (falseWaitFirstHitSingletonTarget ++ payload) -
          falseWaitOneProbeCoordinate falseWaitFirstHitSingletonTarget ∧
      (falseWaitOneProbeCoordinate
            (falseWaitFirstHitSingletonTarget ++ payload) -
          falseWaitOneProbeCoordinate falseWaitFirstHitSingletonTarget = 0 ↔
        payload = []) := by
  by_cases payload_empty : payload = []
  · subst payload
    simp
  · have strict :=
      falseWaitOneProbeCoordinate_singletonTarget_append_pos payload_empty
    constructor
    · linarith
    · constructor
      · intro gap_zero
        linarith
      · exact fun payload_nil => (payload_empty payload_nil).elim

/-- Exact normalized incidence: the payload coordinate gap and mismatch count enter with the
same sign. -/
theorem falseWaitReadableMonotoneRow_incidence
    (checks : List (Bool × Bool)) (bits : List Bool) :
    falseWaitReadableMonotoneRow checks ⬝ᵥ
          (wordProduct falseWaitFirstHitBinaryNormalizedLoop bits *ᵥ
            falseWaitOneProbeChartVector) =
      ((falseWaitOneProbeCoordinate bits -
          falseWaitOneProbeCoordinate falseWaitFirstHitSingletonTarget) +
        15 / 68 * falseWaitMonotoneMismatchCount checks) *
        (bits.map falseWaitFirstHitBinaryRatio).prod := by
  have ratio_ne := falseWaitFirstHitBinaryRatioProduct_ne_zero bits
  rw [falseWaitOneProbeNormalizedLoop_source]
  simp [falseWaitReadableMonotoneRow, dotProduct,
    Fin.sum_univ_succ]
  rw [falseWaitOneProbeCoordinate,
    falseWaitOneProbeCoordinate_singletonTarget]
  field_simp [ratio_ne]
  ring

/-- The normalized marker incidence vanishes exactly for an empty payload and a completely
matching comparison schedule. -/
theorem falseWaitReadableMonotoneRow_marker_zero_iff
    (checks : List (Bool × Bool)) (payload : List Bool) :
    falseWaitReadableMonotoneRow checks ⬝ᵥ
          (wordProduct falseWaitFirstHitBinaryNormalizedLoop
              (falseWaitFirstHitSingletonTarget ++ payload) *ᵥ
            falseWaitOneProbeChartVector) = 0 ↔
      payload = [] ∧ ∀ check ∈ checks, check.1 = check.2 := by
  rw [falseWaitReadableMonotoneRow_incidence]
  have ratio_ne := falseWaitFirstHitBinaryRatioProduct_ne_zero
    (falseWaitFirstHitSingletonTarget ++ payload)
  rw [mul_eq_zero, or_iff_left ratio_ne]
  let gap :=
    falseWaitOneProbeCoordinate
        (falseWaitFirstHitSingletonTarget ++ payload) -
      falseWaitOneProbeCoordinate falseWaitFirstHitSingletonTarget
  let mismatch : ℚ := falseWaitMonotoneMismatchCount checks
  have gap_facts := falseWaitOneProbeCoordinate_singletonTarget_append_gap payload
  have gap_nonnegative : 0 ≤ gap := by
    simpa only [gap] using gap_facts.1
  have gap_zero_iff : gap = 0 ↔ payload = [] := by
    simpa only [gap] using gap_facts.2
  have mismatch_nonnegative : 0 ≤ mismatch := by
    dsimp [mismatch]
    positivity
  change gap + 15 / 68 * mismatch = 0 ↔ _
  constructor
  · intro sum_zero
    have gap_zero : gap = 0 := by nlinarith
    have mismatch_zero : mismatch = 0 := by nlinarith
    have mismatch_count_zero : falseWaitMonotoneMismatchCount checks = 0 := by
      dsimp [mismatch] at mismatch_zero
      exact_mod_cast mismatch_zero
    exact ⟨gap_zero_iff.mp gap_zero,
      (falseWaitMonotoneMismatchCount_eq_zero_iff checks).mp mismatch_count_zero⟩
  · rintro ⟨payload_empty, matching⟩
    have gap_zero := gap_zero_iff.mpr payload_empty
    have mismatch_count_zero :=
      (falseWaitMonotoneMismatchCount_eq_zero_iff checks).mpr matching
    have mismatch_zero : mismatch = 0 := by
      dsimp [mismatch]
      exact_mod_cast mismatch_count_zero
    rw [gap_zero, mismatch_zero]
    norm_num

/-- Physical monotone-selector incidence is a nonzero scale times the normalized one-wait
incidence. -/
theorem falseWaitOneProbeMonotoneSelectorWord_incidence
    (checks : List (Bool × Bool)) (bits : List Bool) :
    ∃ scale : ℚ, scale ≠ 0 ∧
      falseWaitSeparatorRow ⬝ᵥ
          (wordProduct falseWaitReturn
            (falseWaitOneProbeMonotoneSelectorWord checks ++
              falseWaitOneProbeWord bits) *ᵥ
            falseWaitSeparatorColumn) =
        scale *
          (falseWaitReadableMonotoneRow checks ⬝ᵥ
            (wordProduct falseWaitFirstHitBinaryNormalizedLoop bits *ᵥ
              falseWaitOneProbeChartVector)) := by
  rcases falseWaitOneProbeMonotoneSelectorWord_row checks with
    ⟨rowScale, rowScale_ne, rowChart⟩
  let sourceScale : ℚ :=
    30220007956807680000 *
      (bits.map falseWaitFirstHitBinaryScale).prod
  have sourceScale_ne : sourceScale ≠ 0 :=
    mul_ne_zero (by norm_num)
      (falseWaitFirstHitBinaryEncoding_scale_ne_zero bits)
  refine ⟨rowScale * sourceScale,
    mul_ne_zero rowScale_ne sourceScale_ne, ?_⟩
  let physicalRow :=
    falseWaitSeparatorRow ᵥ*
      wordProduct falseWaitReturn
        (falseWaitOneProbeMonotoneSelectorWord checks)
  let physicalSource :=
    wordProduct falseWaitReturn (falseWaitOneProbeWord bits) *ᵥ
      falseWaitSeparatorColumn
  have pairing :=
    falseWaitFirstHitBinaryBasis_pairing physicalRow physicalSource
  have sourceChart := falseWaitOneProbeWord_source_chart bits
  calc
    falseWaitSeparatorRow ⬝ᵥ
          (wordProduct falseWaitReturn
            (falseWaitOneProbeMonotoneSelectorWord checks ++
              falseWaitOneProbeWord bits) *ᵥ
            falseWaitSeparatorColumn) =
        physicalRow ⬝ᵥ physicalSource := by
          simp only [physicalRow, physicalSource, wordProduct_append,
            Matrix.vecMul_vecMul, Matrix.dotProduct_mulVec]
    _ = (physicalRow ᵥ* falseWaitFirstHitBinaryBasis) ⬝ᵥ
          (falseWaitFirstHitBinaryBasisInverse *ᵥ physicalSource) :=
        pairing.symm
    _ = (rowScale • falseWaitReadableMonotoneRow checks) ⬝ᵥ
          (sourceScale •
            (wordProduct falseWaitFirstHitBinaryNormalizedLoop bits *ᵥ
              falseWaitOneProbeChartVector)) := by
        rw [show physicalRow ᵥ* falseWaitFirstHitBinaryBasis =
            rowScale • falseWaitReadableMonotoneRow checks by
              simpa only [physicalRow] using rowChart,
          show falseWaitFirstHitBinaryBasisInverse *ᵥ physicalSource =
            sourceScale •
              (wordProduct falseWaitFirstHitBinaryNormalizedLoop bits *ᵥ
                falseWaitOneProbeChartVector) by
              simpa only [physicalSource, sourceScale] using sourceChart]
    _ = (rowScale * sourceScale) *
          (falseWaitReadableMonotoneRow checks ⬝ᵥ
            (wordProduct falseWaitFirstHitBinaryNormalizedLoop bits *ᵥ
              falseWaitOneProbeChartVector)) := by
        rw [dotProduct_smul, smul_dotProduct]
        ring

/-- The physical one-wait monotone selector accepts exactly the empty marker payload and a
matching comparison schedule. -/
theorem falseWaitOneProbeMonotoneSelectorWord_marker_zero_iff
    (checks : List (Bool × Bool)) (payload : List Bool) :
    falseWaitSeparatorRow ⬝ᵥ
          (wordProduct falseWaitReturn
            (falseWaitOneProbeMonotoneSelectorWord checks ++
              falseWaitOneProbeWord
                (falseWaitFirstHitSingletonTarget ++ payload)) *ᵥ
            falseWaitSeparatorColumn) = 0 ↔
      payload = [] ∧ ∀ check ∈ checks, check.1 = check.2 := by
  rcases falseWaitOneProbeMonotoneSelectorWord_incidence checks
      (falseWaitFirstHitSingletonTarget ++ payload) with
    ⟨scale, scale_ne, incidence⟩
  rw [incidence, mul_eq_zero, or_iff_right scale_ne]
  exact falseWaitReadableMonotoneRow_marker_zero_iff checks payload

/-- The complete physical readable-memory gate accepts exactly the empty marker payload and a
matching comparison schedule. -/
theorem falseWaitReadableMonotoneGateWord_zero_iff
    (checks : List (Bool × Bool)) (payload : List Bool) :
    falseWaitSeparatorRow ⬝ᵥ
          (wordProduct falseWaitReturn
            (falseWaitReadableMonotoneGateWord checks payload) *ᵥ
            falseWaitSeparatorColumn) = 0 ↔
      payload = [] ∧ ∀ check ∈ checks, check.1 = check.2 := by
  rcases falseWaitReadableSelectorCancellationWord_mul_return with
    ⟨scale, scale_ne, cancellation⟩
  have word_eq :
      falseWaitReadableMonotoneGateWord checks payload =
        falseWaitOneProbeMonotoneSelectorWord checks ++
          ((falseWaitReadableSelectorCancellationWord ++
              falseWaitFreeSourceReturnWord) ++
            falseWaitOneProbeWord
              (falseWaitFirstHitSingletonTarget ++ payload)) := by
    simp [falseWaitReadableMonotoneGateWord,
      falseWaitReadableSourceMemoryWord, List.append_assoc]
  have product_eq :
      wordProduct falseWaitReturn
          (falseWaitReadableMonotoneGateWord checks payload) =
        scale • wordProduct falseWaitReturn
          (falseWaitOneProbeMonotoneSelectorWord checks ++
            falseWaitOneProbeWord
              (falseWaitFirstHitSingletonTarget ++ payload)) := by
    rw [word_eq, wordProduct_append, wordProduct_append,
      cancellation, Matrix.smul_mul, Matrix.mul_smul]
    rw [wordProduct_append, Matrix.one_mul]
  rw [product_eq, Matrix.smul_mulVec, dotProduct_smul]
  change scale *
      (falseWaitSeparatorRow ⬝ᵥ
        (wordProduct falseWaitReturn
          (falseWaitOneProbeMonotoneSelectorWord checks ++
            falseWaitOneProbeWord
              (falseWaitFirstHitSingletonTarget ++ payload)) *ᵥ
          falseWaitSeparatorColumn)) = 0 ↔ _
  rw [mul_eq_zero, or_iff_right scale_ne,
    falseWaitOneProbeMonotoneSelectorWord_marker_zero_iff]

/-- Every wait in one corrected check is strictly positive. -/
theorem falseWaitMonotoneCheckWord_positive (check : Bool × Bool) :
    ∀ wait ∈ falseWaitMonotoneCheckWord check, 0 < wait := by
  intro wait membership
  rw [falseWaitMonotoneCheckWord, List.mem_append] at membership
  rcases membership with readWrite | correction
  · rw [continuantReadWriteWord, List.mem_append] at readWrite
    rcases readWrite with reader | writer
    · exact continuantRadixReaderWord_positive check.1 wait reader
    · exact continuantRadixEncoding_positive [check.2] wait (by
        simpa [continuantRadixEncoding] using writer)
  · exact continuantTerminalTranslationWord_positive
      (falseWaitMonotoneCorrectionCounts check) wait correction

/-- Every wait in the complete monotone comparison schedule is strictly positive. -/
theorem falseWaitMonotoneComparatorWord_positive
    (checks : List (Bool × Bool)) :
    ∀ wait ∈ falseWaitMonotoneComparatorWord checks, 0 < wait := by
  intro wait membership
  obtain ⟨check, _, check_mem⟩ := List.mem_flatMap.mp membership
  exact falseWaitMonotoneCheckWord_positive check wait check_mem

/-- Every wait in the height-five selector middle and monotone comparison schedule is strictly
positive. -/
theorem falseWaitReadableMonotoneMiddleWord_positive
    (checks : List (Bool × Bool)) :
    ∀ wait ∈ falseWaitReadableMonotoneMiddleWord checks, 0 < wait := by
  intro wait membership
  rw [falseWaitReadableMonotoneMiddleWord, List.mem_append] at membership
  exact membership.elim
    (falseWaitReadableSelectorMiddleWord_positive wait)
    (falseWaitMonotoneComparatorWord_positive checks wait)

/-- Every wait in the complete monotone selector is strictly positive. -/
theorem falseWaitOneProbeMonotoneSelectorWord_positive
    (checks : List (Bool × Bool)) :
    ∀ wait ∈ falseWaitOneProbeMonotoneSelectorWord checks, 0 < wait := by
  have pre := continuantTerminalTranslationWord_positive
    falseWaitReadableSelectorPreCounts
  have connector := falseWaitFirstHitRayTransportWord_positive
    (falseWaitReadableMonotoneMiddleWord_positive checks)
  intro wait membership
  rw [falseWaitOneProbeMonotoneSelectorWord, List.mem_append] at membership
  rcases membership with prefixMembership | transported
  · rw [List.mem_append] at prefixMembership
    rcases prefixMembership with short | translated
    · simp [falseWaitFirstHitSingletonPrefix] at short
      omega
    · exact pre wait translated
  · exact connector wait transported

/-- Every wait in the complete readable monotone gate is strictly positive. -/
theorem falseWaitReadableMonotoneGateWord_positive
    (checks : List (Bool × Bool)) (payload : List Bool) :
    ∀ wait ∈ falseWaitReadableMonotoneGateWord checks payload, 0 < wait := by
  intro wait membership
  rw [falseWaitReadableMonotoneGateWord, List.mem_append] at membership
  rcases membership with selector | remainder
  · exact falseWaitOneProbeMonotoneSelectorWord_positive checks wait selector
  · rw [List.mem_append] at remainder
    exact remainder.elim
      (continuantTerminalTranslationWord_positive
        falseWaitReadableSelectorCancellationCounts wait)
      (falseWaitReadableSourceMemoryWord_positive
        (falseWaitFirstHitSingletonTarget ++ payload) wait)

/-- Exact physical length of one corrected check. -/
def falseWaitMonotoneCheckCost : Bool × Bool → Nat
  | (false, false) => 2090
  | (false, true) => 83342
  | (true, false) => 65451
  | (true, true) => 1175

private theorem falseWaitMonotoneCorrectionWord_length
    (check : Bool × Bool) :
    (continuantTerminalTranslationWord
      (falseWaitMonotoneCorrectionCounts check)).length =
      match check with
      | (false, false) => 0
      | (false, true) => 81244
      | (true, false) => 64284
      | (true, true) => 0 := by
  rw [continuantTerminalTranslationWord_length]
  rcases check with ⟨guess, actual⟩
  cases guess <;> cases actual <;>
    norm_num [falseWaitMonotoneCorrectionCounts,
      falseWaitMonotonePositiveCorrectionCounts,
      falseWaitMonotoneNegativeCorrectionCounts]

private theorem continuantRadixReaderWord_length_monotone (bit : Bool) :
    (continuantRadixReaderWord bit).length = if bit then 1166 else 2089 := by
  cases bit <;>
    simp only [continuantRadixReaderWord, List.length_append,
      continuantRepeatWord_length] <;>
    norm_num [continuantReaderNegativeCount, continuantReaderPositiveCount,
      continuantReaderNegativeWord, continuantReaderPositiveWord,
      continuantReaderExpansionWord]

private theorem continuantRadixWord_length_monotone (bit : Bool) :
    (continuantRadixWord bit).length = if bit then 9 else 1 := by
  cases bit <;> norm_num [continuantRadixWord]

/-- Each corrected check has its exact compressed physical cost. -/
theorem falseWaitMonotoneCheckWord_length (check : Bool × Bool) :
    (falseWaitMonotoneCheckWord check).length =
      falseWaitMonotoneCheckCost check := by
  rw [falseWaitMonotoneCheckWord, continuantReadWriteWord,
    List.length_append, List.length_append,
    continuantRadixReaderWord_length_monotone,
    continuantRadixWord_length_monotone,
    falseWaitMonotoneCorrectionWord_length]
  rcases check with ⟨guess, actual⟩
  cases guess <;> cases actual <;>
    norm_num [falseWaitMonotoneCheckCost]

/-- The comparison schedule length is the sum of its four exact per-check costs. -/
theorem falseWaitMonotoneComparatorWord_length
    (checks : List (Bool × Bool)) :
    (falseWaitMonotoneComparatorWord checks).length =
      (checks.map falseWaitMonotoneCheckCost).sum := by
  simp [falseWaitMonotoneComparatorWord,
    falseWaitMonotoneCheckWord_length]

/-- Appending the monotone comparison schedule adds exactly its per-check cost sum to the base
selector. -/
theorem falseWaitOneProbeMonotoneSelectorWord_length
    (checks : List (Bool × Bool)) :
    (falseWaitOneProbeMonotoneSelectorWord checks).length =
      falseWaitOneProbeSelectorWord.length +
        (checks.map falseWaitMonotoneCheckCost).sum := by
  have comparison_length := falseWaitMonotoneComparatorWord_length checks
  simp only [falseWaitOneProbeMonotoneSelectorWord,
    falseWaitReadableMonotoneMiddleWord,
    falseWaitOneProbeSelectorWord, falseWaitFirstHitRayTransportWord,
    List.length_append] at comparison_length ⊢
  omega

/-- Exact full-gate length relative to the base selector, including the `00` marker. -/
theorem falseWaitReadableMonotoneGateWord_length
    (checks : List (Bool × Bool)) (payload : List Bool) :
    (falseWaitReadableMonotoneGateWord checks payload).length =
      falseWaitOneProbeSelectorWord.length +
        (checks.map falseWaitMonotoneCheckCost).sum +
          161121 + 4 * payload.length := by
  rw [falseWaitReadableMonotoneGateWord, List.length_append,
    List.length_append, falseWaitOneProbeMonotoneSelectorWord_length,
    falseWaitReadableSelectorCancellationWord_length,
    falseWaitReadableSourceMemoryWord_length]
  simp [falseWaitFirstHitSingletonTarget]
  omega

/-- The contracted base selector gives the complete monotone selector its exact numeric
length. -/
theorem falseWaitOneProbeMonotoneSelectorWord_length_exact
    (checks : List (Bool × Bool)) :
    (falseWaitOneProbeMonotoneSelectorWord checks).length =
      535570700 + (checks.map falseWaitMonotoneCheckCost).sum := by
  rw [falseWaitOneProbeMonotoneSelectorWord_length,
    falseWaitOneProbeSelectorWord_length]

/-- Exact numeric full-gate length after the contracted selector spelling. -/
theorem falseWaitReadableMonotoneGateWord_length_exact
    (checks : List (Bool × Bool)) (payload : List Bool) :
    (falseWaitReadableMonotoneGateWord checks payload).length =
      535731821 + (checks.map falseWaitMonotoneCheckCost).sum +
        4 * payload.length := by
  rw [falseWaitReadableMonotoneGateWord_length,
    falseWaitOneProbeSelectorWord_length]
  omega

end MatrixMortality.CubicReturn.NonPure
