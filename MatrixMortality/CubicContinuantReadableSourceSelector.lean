import MatrixMortality.CubicContinuantFreeSourceProbe

/-!
# A positive singleton selector for the readable cubic source memory

A terminal height-five loop supplies the denominator absent from the translation-only
selector.  Two exact terminal translations place its transported row on the one-wait address
`00`.  A positive inverse translation cancels the fixed source-return prefix, so the same gate
selects `00` from the complete readable source-memory family.
-/

namespace MatrixMortality.CubicReturn.NonPure

open scoped Matrix

/-- Translation inserted after the short row prefix. -/
def falseWaitReadableSelectorPreCounts : ContinuantTerminalTranslationCounts :=
  ⟨0, 0, 329030, 1845125⟩

/-- Translation to the left of the height-five terminal writer. -/
def falseWaitReadableSelectorLeftCounts : ContinuantTerminalTranslationCounts :=
  ⟨0, 0, 2015440, 11170318⟩

/-- Translation to the right of the height-five terminal writer. -/
def falseWaitReadableSelectorRightCounts : ContinuantTerminalTranslationCounts :=
  ⟨0, 0, 874404, 4846250⟩

/-- Short positive realization of the inverse source-return shift `41/90`. -/
def falseWaitReadableSelectorCancellationCounts :
    ContinuantTerminalTranslationCounts :=
  ⟨769, 21, 1669, 750⟩

/-- Translation inserted after the short row prefix. -/
def falseWaitReadableSelectorPreWord : List Nat :=
  continuantTerminalTranslationWord falseWaitReadableSelectorPreCounts

/-- Translation to the left of the height-five terminal writer. -/
def falseWaitReadableSelectorLeftWord : List Nat :=
  continuantTerminalTranslationWord falseWaitReadableSelectorLeftCounts

/-- Translation to the right of the height-five terminal writer. -/
def falseWaitReadableSelectorRightWord : List Nat :=
  continuantTerminalTranslationWord falseWaitReadableSelectorRightCounts

/-- Positive physical inverse of the fixed source-return translation. -/
def falseWaitReadableSelectorCancellationWord : List Nat :=
  continuantTerminalTranslationWord falseWaitReadableSelectorCancellationCounts

/-- Five false radix writers provide terminal height five. -/
def falseWaitReadableSelectorHeightWord : List Nat :=
  continuantRepeatWord (continuantRadixWord false) 5

/-- Terminal middle transported into the common-ray chart. -/
def falseWaitReadableSelectorMiddleWord : List Nat :=
  falseWaitReadableSelectorLeftWord ++
    (falseWaitReadableSelectorHeightWord ++ falseWaitReadableSelectorRightWord)

/-- Complete positive row word selecting the probed address `00`. -/
def falseWaitOneProbeSelectorWord : List Nat :=
  (falseWaitFirstHitSingletonPrefix ++ falseWaitReadableSelectorPreWord) ++
    falseWaitFirstHitRayTransportWord falseWaitReadableSelectorMiddleWord

/-- Complete positive gate for the readable source-memory family. -/
def falseWaitReadableSourceSelectorWord (bits : List Bool) : List Nat :=
  falseWaitOneProbeSelectorWord ++
    (falseWaitReadableSelectorCancellationWord ++
      falseWaitReadableSourceMemoryWord bits)

/-- Exact terminal matrix transported by the selector connector. -/
def falseWaitReadableSelectorMiddle : Square (Fin 2) ℚ :=
  !![1024, -38166180409 / 90; 0, 9765625]

/-- Common-chart loop produced by the height-five terminal middle. -/
def falseWaitReadableSelectorLoop : Square (Fin 2) ℚ :=
  !![1, -12968085961 / 139264; 0, 17578125 / 69632]

/-- Common-chart row annihilating the probed address `00`. -/
def falseWaitReadableSelectorRow : Fin 2 → ℚ :=
  ![1, -4133081074213 / 44425216]

/-- Common-chart row produced before the height-five connector. -/
def falseWaitReadableSelectorPrefixRow : Fin 2 → ℚ :=
  ![1, 623057891 / 1869140625]

/-- Exact shift inserted after the short row prefix. -/
theorem falseWaitReadableSelectorPre_shift :
    continuantTerminalTranslationShift falseWaitReadableSelectorPreCounts =
      -183270179 / 9720 := by
  norm_num [falseWaitReadableSelectorPreCounts,
    continuantTerminalTranslationShift]

/-- Exact shift to the left of the height-five writer. -/
theorem falseWaitReadableSelectorLeft_shift :
    continuantTerminalTranslationShift falseWaitReadableSelectorLeftCounts =
      -6760234 / 151875 := by
  norm_num [falseWaitReadableSelectorLeftCounts,
    continuantTerminalTranslationShift]

/-- Exact shift to the right of the height-five writer. -/
theorem falseWaitReadableSelectorRight_shift :
    continuantTerminalTranslationShift falseWaitReadableSelectorRightCounts =
      431 / 4860 := by
  norm_num [falseWaitReadableSelectorRightCounts,
    continuantTerminalTranslationShift]

/-- Exact inverse shift cancelling the fixed source-return prefix. -/
theorem falseWaitReadableSelectorCancellation_shift :
    continuantTerminalTranslationShift
        falseWaitReadableSelectorCancellationCounts = 41 / 90 := by
  norm_num [falseWaitReadableSelectorCancellationCounts,
    continuantTerminalTranslationShift]

/-- The terminal middle realizes its explicit height-five affine matrix. -/
theorem falseWaitReadableSelectorMiddleWord_projectivelyRealizes :
    continuantProjectivelyRealizes falseWaitReadableSelectorMiddleWord
      falseWaitReadableSelectorMiddle := by
  have left := continuantTerminalTranslationWord_projectivelyRealizes
    falseWaitReadableSelectorLeftCounts
  have right := continuantTerminalTranslationWord_projectivelyRealizes
    falseWaitReadableSelectorRightCounts
  have writer :
      continuantProjectivelyRealizes (continuantRadixWord false)
        (continuantRadixGenerator false) := by
    refine ⟨continuantRadixScale false, by norm_num [continuantRadixScale], ?_⟩
    exact continuantRadixWord_product false
  have height := continuantProjectivelyRealizes_repeat writer 5
  have combined := continuantProjectivelyRealizes_append left
    (continuantProjectivelyRealizes_append height right)
  have normalized :
      continuantDefectTranslation
            (continuantTerminalTranslationShift falseWaitReadableSelectorLeftCounts) *
          (continuantRadixGenerator false ^ 5 *
            continuantDefectTranslation
              (continuantTerminalTranslationShift
                falseWaitReadableSelectorRightCounts)) =
        falseWaitReadableSelectorMiddle := by
    rw [falseWaitReadableSelectorLeft_shift,
      falseWaitReadableSelectorRight_shift]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [continuantDefectTranslation, continuantRadixGenerator,
        continuantRadixDigit, falseWaitReadableSelectorMiddle,
        Matrix.mul_apply, Fin.sum_univ_succ, pow_succ]
  rw [normalized] at combined
  simpa only [falseWaitReadableSelectorMiddleWord,
    falseWaitReadableSelectorLeftWord, falseWaitReadableSelectorHeightWord,
    falseWaitReadableSelectorRightWord] using combined

/-- Ray transport normalizes the terminal middle to the displayed common-chart loop. -/
theorem falseWaitReadableSelectorLoop_eq_transport :
    falseWaitFirstHitRayTransportNormalized 1024
        (-38166180409 / 90) 9765625 =
      falseWaitReadableSelectorLoop := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [falseWaitFirstHitRayTransportNormalized,
      falseWaitReadableSelectorLoop]

/-- The translated short prefix has the displayed common-chart row. -/
theorem falseWaitReadableSelectorPrefix_row :
    ∃ scale : ℚ, scale ≠ 0 ∧
      (falseWaitSeparatorRow ᵥ*
            wordProduct falseWaitReturn
              (falseWaitFirstHitSingletonPrefix ++
                falseWaitReadableSelectorPreWord)) ᵥ*
          falseWaitFirstHitBinaryBasis =
        scale • falseWaitReadableSelectorPrefixRow := by
  rcases continuantTerminalTranslationWord_projectivelyRealizes
      falseWaitReadableSelectorPreCounts with ⟨scale, scale_ne, product⟩
  rw [falseWaitReadableSelectorPre_shift] at product
  refine ⟨scale * 25233398437500,
    mul_ne_zero scale_ne (by norm_num), ?_⟩
  rw [wordProduct_append, falseWaitReadableSelectorPreWord, product,
    Matrix.mul_smul, Matrix.vecMul_smul, Matrix.smul_vecMul]
  ext coordinate
  fin_cases coordinate
  · norm_num [falseWaitFirstHitSingletonPrefix,
      falseWaitReadableSelectorPrefixRow, continuantDefectTranslation,
      falseWaitSeparatorRow, falseWaitFirstHitBinaryBasis,
      wordProduct_cons, wordProduct_nil, falseWaitReturn_eq_state,
      falseWaitReturnOfState, cubicDefectState, CubicDefectState.next,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  · norm_num [falseWaitFirstHitSingletonPrefix,
      falseWaitReadableSelectorPrefixRow, continuantDefectTranslation,
      falseWaitSeparatorRow, falseWaitFirstHitBinaryBasis,
      wordProduct_cons, wordProduct_nil, falseWaitReturn_eq_state,
      falseWaitReturnOfState, cubicDefectState, CubicDefectState.next,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
    ring

/-- The transported height-five middle realizes its exact common-chart loop. -/
theorem falseWaitReadableSelectorConnector_chart :
    ∃ scale : ℚ, scale ≠ 0 ∧
      falseWaitFirstHitBinaryBasisInverse *
            wordProduct falseWaitReturn
              (falseWaitFirstHitRayTransportWord
                falseWaitReadableSelectorMiddleWord) *
        falseWaitFirstHitBinaryBasis =
          scale • falseWaitReadableSelectorLoop := by
  have transported :=
    falseWaitFirstHitRayTransport_projectivelyRealizes
      (by norm_num : (1024 : ℚ) ≠ 0)
      falseWaitReadableSelectorMiddleWord_projectivelyRealizes
  rw [falseWaitReadableSelectorLoop_eq_transport] at transported
  simpa [falseWaitReadableSelectorMiddle] using transported

/-- The pre-connector row lands on the one-wait `00` annihilator. -/
theorem falseWaitReadableSelectorPrefixRow_mul_loop :
    falseWaitReadableSelectorPrefixRow ᵥ* falseWaitReadableSelectorLoop =
      falseWaitReadableSelectorRow := by
  ext coordinate
  fin_cases coordinate <;>
    norm_num [falseWaitReadableSelectorPrefixRow,
      falseWaitReadableSelectorLoop, falseWaitReadableSelectorRow,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

/-- The complete positive selector has the one-wait `00` annihilator as its nonzero chart row. -/
theorem falseWaitOneProbeSelectorWord_row :
    ∃ scale : ℚ, scale ≠ 0 ∧
      (falseWaitSeparatorRow ᵥ*
            wordProduct falseWaitReturn falseWaitOneProbeSelectorWord) ᵥ*
          falseWaitFirstHitBinaryBasis =
        scale • falseWaitReadableSelectorRow := by
  rcases falseWaitReadableSelectorPrefix_row with
    ⟨prefixScale, prefixScale_ne, prefixRow⟩
  rcases falseWaitReadableSelectorConnector_chart with
    ⟨connectorScale, connectorScale_ne, connectorChart⟩
  refine ⟨prefixScale * connectorScale,
    mul_ne_zero prefixScale_ne connectorScale_ne, ?_⟩
  rw [falseWaitOneProbeSelectorWord, wordProduct_append,
    falseWaitFirstHitChart_conjugatedRow,
    prefixRow, connectorChart,
    falseWaitFirstHitChart_vecMul_smul,
    falseWaitReadableSelectorPrefixRow_mul_loop]

/-- The selected row annihilates exactly the normalized one-wait address `00`. -/
theorem falseWaitReadableSelectorRow_zero_iff (bits : List Bool) :
    falseWaitReadableSelectorRow ⬝ᵥ
          (wordProduct falseWaitFirstHitBinaryNormalizedLoop bits *ᵥ
            falseWaitOneProbeChartVector) = 0 ↔
      bits = falseWaitFirstHitSingletonTarget := by
  let source :=
    wordProduct falseWaitFirstHitBinaryNormalizedLoop bits *ᵥ
      falseWaitOneProbeChartVector
  have lower :
      source 1 = (bits.map falseWaitFirstHitBinaryRatio).prod := by
    dsimp [source]
    rw [falseWaitOneProbeNormalizedLoop_source]
    rfl
  have lower_ne : source 1 ≠ 0 := by
    rw [lower]
    exact falseWaitFirstHitBinaryRatioProduct_ne_zero bits
  have selected_coordinate :
      falseWaitOneProbeCoordinate falseWaitFirstHitSingletonTarget =
        4133081074213 / 44425216 := by
    norm_num [falseWaitFirstHitSingletonTarget, falseWaitOneProbeCoordinate,
      falseWaitOneProbeOffset, falseWaitFirstHitBinaryAffineCode,
      falseWaitFirstHitBinaryDigit, falseWaitFirstHitBinaryRatio]
  constructor
  · intro incidence
    have coordinate_eq :
        falseWaitOneProbeCoordinate bits =
          falseWaitOneProbeCoordinate falseWaitFirstHitSingletonTarget := by
      rw [falseWaitOneProbeCoordinate_eq_entries, selected_coordinate]
      change source 0 / source 1 = 4133081074213 / 44425216
      change ![1, -4133081074213 / 44425216] ⬝ᵥ source = 0 at incidence
      simp [dotProduct, Fin.sum_univ_succ] at incidence
      apply (div_eq_iff lower_ne).2
      linarith
    exact falseWaitOneProbeCoordinate_injective coordinate_eq
  · rintro rfl
    norm_num [falseWaitReadableSelectorRow,
      falseWaitFirstHitSingletonTarget, falseWaitOneProbeChartVector,
      falseWaitOneProbeOffset, falseWaitFirstHitBinaryNormalizedLoop,
      falseWaitFirstHitBinaryDigit, falseWaitFirstHitBinaryRatio,
      wordProduct_cons, wordProduct_nil, Matrix.mul_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Physical selector incidence is a nonzero scale times normalized one-wait incidence. -/
theorem falseWaitOneProbeSelectorWord_incidence (bits : List Bool) :
    ∃ scale : ℚ, scale ≠ 0 ∧
      falseWaitSeparatorRow ⬝ᵥ
          (wordProduct falseWaitReturn
            (falseWaitOneProbeSelectorWord ++ falseWaitOneProbeWord bits) *ᵥ
            falseWaitSeparatorColumn) =
        scale *
          (falseWaitReadableSelectorRow ⬝ᵥ
            (wordProduct falseWaitFirstHitBinaryNormalizedLoop bits *ᵥ
              falseWaitOneProbeChartVector)) := by
  rcases falseWaitOneProbeSelectorWord_row with
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
      wordProduct falseWaitReturn falseWaitOneProbeSelectorWord
  let physicalSource :=
    wordProduct falseWaitReturn (falseWaitOneProbeWord bits) *ᵥ
      falseWaitSeparatorColumn
  have pairing := falseWaitFirstHitBinaryBasis_pairing physicalRow physicalSource
  have sourceChart := falseWaitOneProbeWord_source_chart bits
  calc
    falseWaitSeparatorRow ⬝ᵥ
          (wordProduct falseWaitReturn
            (falseWaitOneProbeSelectorWord ++ falseWaitOneProbeWord bits) *ᵥ
            falseWaitSeparatorColumn) =
        physicalRow ⬝ᵥ physicalSource := by
          simp only [physicalRow, physicalSource, wordProduct_append,
            Matrix.vecMul_vecMul, Matrix.dotProduct_mulVec]
    _ = (physicalRow ᵥ* falseWaitFirstHitBinaryBasis) ⬝ᵥ
          (falseWaitFirstHitBinaryBasisInverse *ᵥ physicalSource) :=
        pairing.symm
    _ = (rowScale • falseWaitReadableSelectorRow) ⬝ᵥ
          (sourceScale •
            (wordProduct falseWaitFirstHitBinaryNormalizedLoop bits *ᵥ
              falseWaitOneProbeChartVector)) := by
        rw [show physicalRow ᵥ* falseWaitFirstHitBinaryBasis =
            rowScale • falseWaitReadableSelectorRow by
              simpa only [physicalRow] using rowChart,
          show falseWaitFirstHitBinaryBasisInverse *ᵥ physicalSource =
            sourceScale •
              (wordProduct falseWaitFirstHitBinaryNormalizedLoop bits *ᵥ
                falseWaitOneProbeChartVector) by
              simpa only [physicalSource, sourceScale] using sourceChart]
    _ = (rowScale * sourceScale) *
          (falseWaitReadableSelectorRow ⬝ᵥ
            (wordProduct falseWaitFirstHitBinaryNormalizedLoop bits *ᵥ
              falseWaitOneProbeChartVector)) := by
        rw [dotProduct_smul, smul_dotProduct]
        ring

/-- The positive one-wait selector vanishes exactly on the encoded address `00`. -/
theorem falseWaitOneProbeSelectorWord_zero_iff (bits : List Bool) :
    falseWaitSeparatorRow ⬝ᵥ
          (wordProduct falseWaitReturn
            (falseWaitOneProbeSelectorWord ++ falseWaitOneProbeWord bits) *ᵥ
            falseWaitSeparatorColumn) = 0 ↔
      bits = falseWaitFirstHitSingletonTarget := by
  rcases falseWaitOneProbeSelectorWord_incidence bits with
    ⟨scale, scale_ne, incidence⟩
  rw [incidence, mul_eq_zero, or_iff_right scale_ne,
    falseWaitReadableSelectorRow_zero_iff]

/-- The cancellation word and fixed source-return prefix multiply to a nonzero scalar identity. -/
theorem falseWaitReadableSelectorCancellationWord_mul_return :
    ∃ scale : ℚ, scale ≠ 0 ∧
      wordProduct falseWaitReturn
          (falseWaitReadableSelectorCancellationWord ++
            falseWaitFreeSourceReturnWord) =
        scale • (1 : Square (Fin 2) ℚ) := by
  have cancellation := continuantTerminalTranslationWord_projectivelyRealizes
    falseWaitReadableSelectorCancellationCounts
  rw [falseWaitReadableSelectorCancellation_shift] at cancellation
  have combined := continuantProjectivelyRealizes_append cancellation
    falseWaitFreeSourceReturnWord_projectivelyRealizes
  have normalized :
      continuantDefectTranslation (41 / 90) * falseWaitFreeSourceReturn =
        (1 : Square (Fin 2) ℚ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [continuantDefectTranslation, falseWaitFreeSourceReturn,
        Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]
  rw [normalized] at combined
  change continuantProjectivelyRealizes
    (falseWaitReadableSelectorCancellationWord ++
      falseWaitFreeSourceReturnWord) (1 : Square (Fin 2) ℚ)
  simpa only [falseWaitReadableSelectorCancellationWord] using combined

/-- The full positive readable-memory gate vanishes exactly on address `00`. -/
theorem falseWaitReadableSourceSelectorWord_zero_iff (bits : List Bool) :
    falseWaitSeparatorRow ⬝ᵥ
          (wordProduct falseWaitReturn
            (falseWaitReadableSourceSelectorWord bits) *ᵥ
            falseWaitSeparatorColumn) = 0 ↔
      bits = falseWaitFirstHitSingletonTarget := by
  rcases falseWaitReadableSelectorCancellationWord_mul_return with
    ⟨scale, scale_ne, cancellation⟩
  have word_eq :
      falseWaitReadableSourceSelectorWord bits =
        falseWaitOneProbeSelectorWord ++
          ((falseWaitReadableSelectorCancellationWord ++
              falseWaitFreeSourceReturnWord) ++ falseWaitOneProbeWord bits) := by
    simp [falseWaitReadableSourceSelectorWord,
      falseWaitReadableSourceMemoryWord, List.append_assoc]
  have product_eq :
      wordProduct falseWaitReturn (falseWaitReadableSourceSelectorWord bits) =
        scale • wordProduct falseWaitReturn
          (falseWaitOneProbeSelectorWord ++ falseWaitOneProbeWord bits) := by
    rw [word_eq, wordProduct_append, wordProduct_append,
      cancellation, Matrix.smul_mul, Matrix.mul_smul]
    rw [wordProduct_append, Matrix.one_mul]
  rw [product_eq, Matrix.smul_mulVec, dotProduct_smul]
  change scale *
      (falseWaitSeparatorRow ⬝ᵥ
        (wordProduct falseWaitReturn
          (falseWaitOneProbeSelectorWord ++ falseWaitOneProbeWord bits) *ᵥ
          falseWaitSeparatorColumn)) = 0 ↔ _
  rw [mul_eq_zero, or_iff_right scale_ne,
    falseWaitOneProbeSelectorWord_zero_iff]

/-- Prefixing the selected `00` marker makes the gate accept exactly an empty payload. -/
theorem falseWaitReadableSourceSelectorWord_marker_zero_iff
    (payload : List Bool) :
    falseWaitSeparatorRow ⬝ᵥ
          (wordProduct falseWaitReturn
            (falseWaitReadableSourceSelectorWord
              (falseWaitFirstHitSingletonTarget ++ payload)) *ᵥ
            falseWaitSeparatorColumn) = 0 ↔
      payload = [] := by
  simpa [falseWaitFirstHitSingletonTarget] using
    falseWaitReadableSourceSelectorWord_zero_iff
      (falseWaitFirstHitSingletonTarget ++ payload)

/-- Every wait in the height-five terminal middle is strictly positive. -/
theorem falseWaitReadableSelectorMiddleWord_positive :
    ∀ wait ∈ falseWaitReadableSelectorMiddleWord, 0 < wait := by
  have left := continuantTerminalTranslationWord_positive
    falseWaitReadableSelectorLeftCounts
  have right := continuantTerminalTranslationWord_positive
    falseWaitReadableSelectorRightCounts
  have writer : ∀ wait ∈ continuantRadixWord false, 0 < wait := by
    simp [continuantRadixWord]
  have height := continuantRepeatWord_positive writer 5
  intro wait membership
  rw [falseWaitReadableSelectorMiddleWord, List.mem_append] at membership
  exact membership.elim (left wait) fun remainder => by
    rw [List.mem_append] at remainder
    exact remainder.elim (height wait) (right wait)

/-- Every wait in the one-probe selector is strictly positive. -/
theorem falseWaitOneProbeSelectorWord_positive :
    ∀ wait ∈ falseWaitOneProbeSelectorWord, 0 < wait := by
  have pre := continuantTerminalTranslationWord_positive
    falseWaitReadableSelectorPreCounts
  have connector := falseWaitFirstHitRayTransportWord_positive
    falseWaitReadableSelectorMiddleWord_positive
  intro wait membership
  rw [falseWaitOneProbeSelectorWord, List.mem_append] at membership
  rcases membership with prefixMembership | transported
  · rw [List.mem_append] at prefixMembership
    rcases prefixMembership with short | translated
    · simp [falseWaitFirstHitSingletonPrefix] at short
      omega
    · exact pre wait translated
  · exact connector wait transported

/-- Every wait in the complete readable-memory selector is strictly positive. -/
theorem falseWaitReadableSourceSelectorWord_positive (bits : List Bool) :
    ∀ wait ∈ falseWaitReadableSourceSelectorWord bits, 0 < wait := by
  have cancellation := continuantTerminalTranslationWord_positive
    falseWaitReadableSelectorCancellationCounts
  intro wait membership
  rw [falseWaitReadableSourceSelectorWord, List.mem_append] at membership
  rcases membership with selector | remainder
  · exact falseWaitOneProbeSelectorWord_positive wait selector
  · rw [List.mem_append] at remainder
    exact remainder.elim (cancellation wait)
      (falseWaitReadableSourceMemoryWord_positive bits wait)

/-- The pre-connector translation has length `75,837,315`. -/
theorem falseWaitReadableSelectorPreWord_length :
    falseWaitReadableSelectorPreWord.length = 75837315 := by
  rw [falseWaitReadableSelectorPreWord,
    continuantTerminalTranslationWord_length]
  norm_num [falseWaitReadableSelectorPreCounts]

/-- The left height translation has length `459,656,886`. -/
theorem falseWaitReadableSelectorLeftWord_length :
    falseWaitReadableSelectorLeftWord.length = 459656886 := by
  rw [falseWaitReadableSelectorLeftWord,
    continuantTerminalTranslationWord_length]
  norm_num [falseWaitReadableSelectorLeftCounts]

/-- The right height translation has length `199,422,542`. -/
theorem falseWaitReadableSelectorRightWord_length :
    falseWaitReadableSelectorRightWord.length = 199422542 := by
  rw [falseWaitReadableSelectorRightWord,
    continuantTerminalTranslationWord_length]
  norm_num [falseWaitReadableSelectorRightCounts]

/-- The positive inverse source-return word has length `89,921`. -/
theorem falseWaitReadableSelectorCancellationWord_length :
    falseWaitReadableSelectorCancellationWord.length = 89921 := by
  rw [falseWaitReadableSelectorCancellationWord,
    continuantTerminalTranslationWord_length]
  norm_num [falseWaitReadableSelectorCancellationCounts]

/-- The positive one-probe selector has length `734,916,756`. -/
theorem falseWaitOneProbeSelectorWord_length :
    falseWaitOneProbeSelectorWord.length = 734916756 := by
  have short_length : falseWaitFirstHitSingletonPrefix.length = 4 := by
    rfl
  have height_length : falseWaitReadableSelectorHeightWord.length = 5 := by
    rw [falseWaitReadableSelectorHeightWord, continuantRepeatWord_length]
    norm_num [continuantRadixWord]
  have middle_length : falseWaitReadableSelectorMiddleWord.length = 659079433 := by
    calc
      falseWaitReadableSelectorMiddleWord.length =
          falseWaitReadableSelectorLeftWord.length +
            (falseWaitReadableSelectorHeightWord ++
              falseWaitReadableSelectorRightWord).length := by
            rw [falseWaitReadableSelectorMiddleWord, List.length_append]
      _ = falseWaitReadableSelectorLeftWord.length +
          (falseWaitReadableSelectorHeightWord.length +
            falseWaitReadableSelectorRightWord.length) := by
            rw [List.length_append]
      _ = 659079433 := by
            rw [falseWaitReadableSelectorLeftWord_length,
              height_length, falseWaitReadableSelectorRightWord_length]
  have connector_length :
      (falseWaitFirstHitRayTransportWord
        falseWaitReadableSelectorMiddleWord).length = 659079437 := by
    calc
      (falseWaitFirstHitRayTransportWord
            falseWaitReadableSelectorMiddleWord).length =
          (falseWaitFirstHitRayTransportHead ++
            falseWaitReadableSelectorMiddleWord).length +
              falseWaitFirstHitRayTransportTail.length := by
            rw [falseWaitFirstHitRayTransportWord, List.length_append]
      _ = (falseWaitFirstHitRayTransportHead.length +
            falseWaitReadableSelectorMiddleWord.length) +
          falseWaitFirstHitRayTransportTail.length := by
            rw [List.length_append]
      _ = 659079437 := by
            rw [middle_length]
            norm_num [falseWaitFirstHitRayTransportHead,
              falseWaitFirstHitRayTransportTail]
  calc
    falseWaitOneProbeSelectorWord.length =
        (falseWaitFirstHitSingletonPrefix ++
            falseWaitReadableSelectorPreWord).length +
          (falseWaitFirstHitRayTransportWord
            falseWaitReadableSelectorMiddleWord).length := by
          rw [falseWaitOneProbeSelectorWord, List.length_append]
    _ = (falseWaitFirstHitSingletonPrefix.length +
          falseWaitReadableSelectorPreWord.length) +
        (falseWaitFirstHitRayTransportWord
          falseWaitReadableSelectorMiddleWord).length := by
          rw [List.length_append]
    _ = 734916756 := by
          rw [short_length, falseWaitReadableSelectorPreWord_length,
            connector_length]

/-- The complete gate has length `735,077,869+4|β|`. -/
theorem falseWaitReadableSourceSelectorWord_length (bits : List Bool) :
    (falseWaitReadableSourceSelectorWord bits).length =
      735077869 + 4 * bits.length := by
  calc
    (falseWaitReadableSourceSelectorWord bits).length =
        falseWaitOneProbeSelectorWord.length +
          (falseWaitReadableSelectorCancellationWord ++
            falseWaitReadableSourceMemoryWord bits).length := by
          rw [falseWaitReadableSourceSelectorWord, List.length_append]
    _ = falseWaitOneProbeSelectorWord.length +
        (falseWaitReadableSelectorCancellationWord.length +
          (falseWaitReadableSourceMemoryWord bits).length) := by
          rw [List.length_append]
    _ = 735077869 + 4 * bits.length := by
          rw [falseWaitOneProbeSelectorWord_length,
            falseWaitReadableSelectorCancellationWord_length,
            falseWaitReadableSourceMemoryWord_length]
          omega

end MatrixMortality.CubicReturn.NonPure
