import MatrixMortality.CubicContinuantRayTransport

/-!
# A positive singleton selector for the cubic continuant source stack

A four-wait row prefix changes the affine residue class of the transported terminal
translations. An exact nonnegative combination of the positive and negative translations then
lands on the separator-source coordinate of the binary word `00`. The resulting positive
physical left word annihilates precisely that encoded source among all binary pump addresses.
-/

namespace MatrixMortality.CubicReturn.NonPure

open scoped Matrix

/-- Four-wait prefix whose separator row enters the required common-ray residue class. -/
def falseWaitFirstHitSingletonPrefix : List Nat := [26, 2, 5, 15]

/-- Number of negative terminal translations in the singleton selector. -/
def falseWaitFirstHitSingletonNegativeCount : Nat := 6484

/-- Number of positive terminal translations in the singleton selector. -/
def falseWaitFirstHitSingletonPositiveCount : Nat := 310371

/-- Terminal middle word whose normalized action is one exact upper translation. -/
def falseWaitFirstHitSingletonMiddle : List Nat :=
  continuantRepeatWord (continuantReaderNegativeWord false)
      falseWaitFirstHitSingletonNegativeCount ++
    continuantRepeatWord (continuantReaderPositiveWord false)
      falseWaitFirstHitSingletonPositiveCount

/-- Complete positive left word selecting the binary source address `00`. -/
def falseWaitFirstHitSingletonWord : List Nat :=
  falseWaitFirstHitSingletonPrefix ++
    falseWaitFirstHitRayTransportWord falseWaitFirstHitSingletonMiddle

/-- Binary source address selected by `falseWaitFirstHitSingletonWord`. -/
def falseWaitFirstHitSingletonTarget : List Bool := [false, false]

/-- Exact upper translation synthesized by the repeated terminal blocks. -/
def falseWaitFirstHitSingletonTranslation : Square (Fin 2) ℚ :=
  !![1, -762919 / 2; 0, 1]

/-- Common-ray connector loop produced by the singleton translation. -/
def falseWaitFirstHitSingletonLoop : Square (Fin 2) ℚ :=
  !![1, -85828079 / 1020; 0, 9 / 340]

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

/-- The compressed repeated middle word realizes the displayed exact translation. -/
theorem falseWaitFirstHitSingletonMiddle_projectivelyRealizes :
    continuantProjectivelyRealizes falseWaitFirstHitSingletonMiddle
      falseWaitFirstHitSingletonTranslation := by
  have negative := continuantProjectivelyRealizes_repeat
    (continuantReaderNegativeWord_projectivelyRealizes false)
    falseWaitFirstHitSingletonNegativeCount
  have positive := continuantProjectivelyRealizes_repeat
    (continuantReaderPositiveWord_projectivelyRealizes false)
    falseWaitFirstHitSingletonPositiveCount
  have combined := continuantProjectivelyRealizes_append negative positive
  have translation :
      continuantReaderNegative false ^ falseWaitFirstHitSingletonNegativeCount *
          continuantReaderPositive false ^ falseWaitFirstHitSingletonPositiveCount =
        falseWaitFirstHitSingletonTranslation := by
    rw [show continuantReaderNegative false = !![1, -189665 / 144; 0, 1] by rfl,
      show continuantReaderPositive false = !![1, 2839 / 108; 0, 1] by rfl,
      upperTranslation_pow, upperTranslation_pow]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [falseWaitFirstHitSingletonNegativeCount,
        falseWaitFirstHitSingletonPositiveCount,
        falseWaitFirstHitSingletonTranslation, Matrix.mul_apply,
        Fin.sum_univ_succ]
  rw [translation] at combined
  simpa only [falseWaitFirstHitSingletonMiddle] using combined

/-- The transported middle word realizes its exact common-ray selector loop. -/
theorem falseWaitFirstHitSingletonConnector_chart :
    ∃ scale : ℚ, scale ≠ 0 ∧
      falseWaitFirstHitBinaryBasisInverse *
            wordProduct falseWaitReturn
              (falseWaitFirstHitRayTransportWord falseWaitFirstHitSingletonMiddle) *
        falseWaitFirstHitBinaryBasis =
          scale • falseWaitFirstHitSingletonLoop := by
  have transported :=
    falseWaitFirstHitRayTransport_projectivelyRealizes (by norm_num : (1 : ℚ) ≠ 0)
      falseWaitFirstHitSingletonMiddle_projectivelyRealizes
  have normalized :
      falseWaitFirstHitRayTransportNormalized 1 (-762919 / 2) 1 =
        falseWaitFirstHitSingletonLoop := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [falseWaitFirstHitRayTransportNormalized,
        falseWaitFirstHitSingletonLoop]
  rw [normalized] at transported
  simpa [falseWaitFirstHitSingletonTranslation] using transported

/-- The short prefix has the displayed nonzero row coordinate in the common-ray basis. -/
theorem falseWaitFirstHitSingletonPrefix_row :
    (falseWaitSeparatorRow ᵥ*
          wordProduct falseWaitReturn falseWaitFirstHitSingletonPrefix) ᵥ*
        falseWaitFirstHitBinaryBasis =
      (-2905210800 : ℚ) • ![1, 937 / 3321] := by
  ext coordinate
  fin_cases coordinate <;>
    norm_num [falseWaitFirstHitSingletonPrefix, falseWaitSeparatorRow,
      falseWaitFirstHitBinaryBasis, wordProduct_cons, wordProduct_nil,
      falseWaitReturn_eq_state, falseWaitReturnOfState, cubicDefectState,
      CubicDefectState.next, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ]

/-- The selected binary source has the exact projective coordinate hit by the row prefix. -/
theorem falseWaitFirstHitSingletonTarget_coordinate :
    falseWaitFirstHitBinarySourceCoordinate falseWaitFirstHitSingletonTarget =
      -31049567 / 369 := by
  norm_num [falseWaitFirstHitSingletonTarget,
    falseWaitFirstHitBinarySourceCoordinate,
    falseWaitFirstHitBinaryAffineCode, falseWaitFirstHitBinaryDigit,
    falseWaitFirstHitBinaryRatio]

/-- The prefixed row followed by the normalized connector becomes the selected source
annihilator. -/
theorem falseWaitFirstHitSingletonLoop_row :
    ![1, 937 / 3321] ᵥ* falseWaitFirstHitSingletonLoop =
      ![1,
        falseWaitFirstHitBinarySourceCoordinate falseWaitFirstHitSingletonTarget] := by
  rw [falseWaitFirstHitSingletonTarget_coordinate]
  ext coordinate
  fin_cases coordinate <;>
    norm_num [falseWaitFirstHitSingletonLoop, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ]

/-- Conjugating a right factor transports the corresponding left row into the common-ray
chart. -/
theorem falseWaitFirstHitChart_conjugatedRow
    (row : Fin 2 → ℚ) (left right : Square (Fin 2) ℚ) :
    (row ᵥ* (left * right)) ᵥ* falseWaitFirstHitBinaryBasis =
      ((row ᵥ* left) ᵥ* falseWaitFirstHitBinaryBasis) ᵥ*
        (falseWaitFirstHitBinaryBasisInverse * right *
          falseWaitFirstHitBinaryBasis) := by
  simp only [Matrix.vecMul_vecMul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc falseWaitFirstHitBinaryBasis
      falseWaitFirstHitBinaryBasisInverse (right * falseWaitFirstHitBinaryBasis),
    falseWaitFirstHitBinaryBasis_inverse_right, Matrix.one_mul]

/-- Scaling a chart row and matrix multiplies the scale of their row action. -/
theorem falseWaitFirstHitChart_vecMul_smul
    (leftScale rightScale : ℚ) (row : Fin 2 → ℚ)
    (matrix : Square (Fin 2) ℚ) :
    (leftScale • row) ᵥ* (rightScale • matrix) =
      (leftScale * rightScale) • (row ᵥ* matrix) := by
  ext coordinate
  fin_cases coordinate <;>
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_succ] <;>
    ring

/-- The complete positive selector word has the chosen source annihilator as its nonzero
projective row. -/
theorem falseWaitFirstHitSingletonWord_row :
    ∃ scale : ℚ, scale ≠ 0 ∧
      (falseWaitSeparatorRow ᵥ*
            wordProduct falseWaitReturn falseWaitFirstHitSingletonWord) ᵥ*
          falseWaitFirstHitBinaryBasis =
        scale • ![1,
          falseWaitFirstHitBinarySourceCoordinate falseWaitFirstHitSingletonTarget] := by
  rcases falseWaitFirstHitSingletonConnector_chart with
    ⟨connectorScale, connectorScale_ne, connectorChart⟩
  refine ⟨(-2905210800 : ℚ) * connectorScale,
    mul_ne_zero (by norm_num) connectorScale_ne, ?_⟩
  rw [falseWaitFirstHitSingletonWord, wordProduct_append,
    falseWaitFirstHitChart_conjugatedRow,
    falseWaitFirstHitSingletonPrefix_row, connectorChart,
    falseWaitFirstHitChart_vecMul_smul, falseWaitFirstHitSingletonLoop_row]

/-- Repetition multiplies the compressed word length without expanding the list. -/
theorem continuantRepeatWord_length (word : List Nat) (repetitions : Nat) :
    (continuantRepeatWord word repetitions).length = repetitions * word.length := by
  induction repetitions with
  | zero => simp [continuantRepeatWord]
  | succ repetitions induction =>
      rw [continuantRepeatWord, List.length_append, induction]
      simp [Nat.succ_mul, Nat.add_comm]

/-- The exact positive selector has a finite compressed spelling of length `9,531,594`. -/
theorem falseWaitFirstHitSingletonWord_length :
    falseWaitFirstHitSingletonWord.length = 9531594 := by
  simp only [falseWaitFirstHitSingletonWord, falseWaitFirstHitRayTransportWord,
    falseWaitFirstHitRayTransportHead, falseWaitFirstHitRayTransportTail,
    falseWaitFirstHitSingletonMiddle, continuantRepeatWord_length,
    List.length_append]
  norm_num [falseWaitFirstHitSingletonPrefix,
    falseWaitFirstHitSingletonNegativeCount,
    falseWaitFirstHitSingletonPositiveCount,
    continuantReaderNegativeWord, continuantReaderPositiveWord]

/-- Every wait in the repeated terminal translation is strictly positive. -/
theorem falseWaitFirstHitSingletonMiddle_positive :
    ∀ wait ∈ falseWaitFirstHitSingletonMiddle, 0 < wait := by
  have negative :
      ∀ wait ∈ continuantReaderNegativeWord false, 0 < wait := by
    simp [continuantReaderNegativeWord]
  have positive :
      ∀ wait ∈ continuantReaderPositiveWord false, 0 < wait := by
    simp [continuantReaderPositiveWord]
  intro wait membership
  rw [falseWaitFirstHitSingletonMiddle, List.mem_append] at membership
  exact membership.elim
    (continuantRepeatWord_positive negative _ wait)
    (continuantRepeatWord_positive positive _ wait)

/-- Every wait in the exact singleton selector is strictly positive. -/
theorem falseWaitFirstHitSingletonWord_positive :
    ∀ wait ∈ falseWaitFirstHitSingletonWord, 0 < wait := by
  intro wait membership
  rw [falseWaitFirstHitSingletonWord, List.mem_append] at membership
  rcases membership with prefix_mem | connector_mem
  · simp only [falseWaitFirstHitSingletonPrefix, List.mem_cons,
      List.not_mem_nil, or_false] at prefix_mem
    omega
  · exact falseWaitFirstHitRayTransportWord_positive
      falseWaitFirstHitSingletonMiddle_positive wait connector_mem

/-- In the normalized chart, the row defined by any target source coordinate annihilates
exactly that binary source. -/
theorem falseWaitFirstHitBinarySourceRow_zero_iff
    (target bits : List Bool) :
    ![1, falseWaitFirstHitBinarySourceCoordinate target] ⬝ᵥ
          (wordProduct falseWaitFirstHitBinaryNormalizedLoop bits *ᵥ
            falseWaitFirstHitBinarySourceChartVector) = 0 ↔
      bits = target := by
  let source :=
    wordProduct falseWaitFirstHitBinaryNormalizedLoop bits *ᵥ
      falseWaitFirstHitBinarySourceChartVector
  have lower :
      source 1 = -123 * (bits.map falseWaitFirstHitBinaryRatio).prod := by
    dsimp [source]
    rw [falseWaitFirstHitBinaryNormalizedLoop_source]
    rfl
  have lower_ne : source 1 ≠ 0 := by
    rw [lower]
    exact mul_ne_zero (by norm_num)
      (falseWaitFirstHitBinaryRatioProduct_ne_zero bits)
  constructor
  · intro incidence
    have coordinate_eq :
        falseWaitFirstHitBinarySourceCoordinate bits =
          falseWaitFirstHitBinarySourceCoordinate target := by
      rw [falseWaitFirstHitBinarySourceCoordinate_eq_entries]
      change -(source 0 / source 1) =
        falseWaitFirstHitBinarySourceCoordinate target
      rw [show -(source 0 / source 1) = (-source 0) / source 1 by ring]
      apply (div_eq_iff lower_ne).2
      change ![1, falseWaitFirstHitBinarySourceCoordinate target] ⬝ᵥ source = 0 at incidence
      simp [dotProduct, Fin.sum_univ_succ] at incidence
      linarith
    exact falseWaitFirstHitBinarySourceCoordinate_injective coordinate_eq
  · rintro rfl
    rw [falseWaitFirstHitBinarySourceCoordinate_eq_entries]
    change ![1, -(source 0 / source 1)] ⬝ᵥ source = 0
    simp [dotProduct, Fin.sum_univ_succ]
    field_simp [lower_ne]
    ring

/-- The common-ray basis and its inverse preserve the row-column scalar pairing. -/
theorem falseWaitFirstHitBinaryBasis_pairing
    (row column : Fin 2 → ℚ) :
    ((row ᵥ* falseWaitFirstHitBinaryBasis) ⬝ᵥ
        (falseWaitFirstHitBinaryBasisInverse *ᵥ column)) =
      row ⬝ᵥ column := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    falseWaitFirstHitBinaryBasis_inverse_right]
  simp

/-- Any nonzero physical left-row chart factors incidence against an encoded source through
the normalized common-ray source action. -/
theorem falseWaitFirstHitChartRow_incidence
    (leftWord : List Nat) (chartRow : Fin 2 → ℚ)
    (rowScale : ℚ) (rowScale_ne : rowScale ≠ 0)
    (rowChart :
      (falseWaitSeparatorRow ᵥ* wordProduct falseWaitReturn leftWord) ᵥ*
          falseWaitFirstHitBinaryBasis = rowScale • chartRow)
    (bits : List Bool) :
    ∃ scale : ℚ, scale ≠ 0 ∧
      falseWaitSeparatorRow ⬝ᵥ
          (wordProduct falseWaitReturn
            (leftWord ++ falseWaitFirstHitBinaryEncoding bits) *ᵥ
            falseWaitSeparatorColumn) =
        scale *
          (chartRow ⬝ᵥ
            (wordProduct falseWaitFirstHitBinaryNormalizedLoop bits *ᵥ
              falseWaitFirstHitBinarySourceChartVector)) := by
  let sourceScale := (bits.map falseWaitFirstHitBinaryScale).prod
  have sourceScale_ne : sourceScale ≠ 0 :=
    falseWaitFirstHitBinaryEncoding_scale_ne_zero bits
  refine ⟨rowScale * sourceScale, mul_ne_zero rowScale_ne sourceScale_ne, ?_⟩
  let physicalRow :=
    falseWaitSeparatorRow ᵥ* wordProduct falseWaitReturn leftWord
  let physicalSource :=
    wordProduct falseWaitReturn (falseWaitFirstHitBinaryEncoding bits) *ᵥ
      falseWaitSeparatorColumn
  have pairing := falseWaitFirstHitBinaryBasis_pairing physicalRow physicalSource
  have sourceChart := falseWaitFirstHitBinaryEncoding_source_chart bits
  calc
    falseWaitSeparatorRow ⬝ᵥ
          (wordProduct falseWaitReturn
            (leftWord ++ falseWaitFirstHitBinaryEncoding bits) *ᵥ
            falseWaitSeparatorColumn) =
        physicalRow ⬝ᵥ physicalSource := by
          simp only [physicalRow, physicalSource, wordProduct_append,
            ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    _ = (physicalRow ᵥ* falseWaitFirstHitBinaryBasis) ⬝ᵥ
          (falseWaitFirstHitBinaryBasisInverse *ᵥ physicalSource) :=
        pairing.symm
    _ = (rowScale • chartRow) ⬝ᵥ
          (sourceScale •
            (wordProduct falseWaitFirstHitBinaryNormalizedLoop bits *ᵥ
              falseWaitFirstHitBinarySourceChartVector)) := by
        rw [show physicalRow ᵥ* falseWaitFirstHitBinaryBasis =
            rowScale • chartRow by simpa only [physicalRow] using rowChart,
          show falseWaitFirstHitBinaryBasisInverse *ᵥ physicalSource =
            sourceScale •
              (wordProduct falseWaitFirstHitBinaryNormalizedLoop bits *ᵥ
                falseWaitFirstHitBinarySourceChartVector) by
              simpa only [physicalSource, sourceScale] using sourceChart]
    _ = (rowScale * sourceScale) *
          (chartRow ⬝ᵥ
            (wordProduct falseWaitFirstHitBinaryNormalizedLoop bits *ᵥ
              falseWaitFirstHitBinarySourceChartVector)) := by
        simp [dotProduct, Fin.sum_univ_succ]
        ring

/-- Physical singleton incidence is one nonzero scale times its normalized source incidence. -/
theorem falseWaitFirstHitSingletonWord_incidence (bits : List Bool) :
    ∃ scale : ℚ, scale ≠ 0 ∧
      falseWaitSeparatorRow ⬝ᵥ
          (wordProduct falseWaitReturn
            (falseWaitFirstHitSingletonWord ++
              falseWaitFirstHitBinaryEncoding bits) *ᵥ
            falseWaitSeparatorColumn) =
        scale *
          (![1,
              falseWaitFirstHitBinarySourceCoordinate
                falseWaitFirstHitSingletonTarget] ⬝ᵥ
            (wordProduct falseWaitFirstHitBinaryNormalizedLoop bits *ᵥ
              falseWaitFirstHitBinarySourceChartVector)) := by
  rcases falseWaitFirstHitSingletonWord_row with
    ⟨rowScale, rowScale_ne, rowChart⟩
  exact falseWaitFirstHitChartRow_incidence
    falseWaitFirstHitSingletonWord
    ![1, falseWaitFirstHitBinarySourceCoordinate falseWaitFirstHitSingletonTarget]
    rowScale rowScale_ne rowChart bits

/-- The complete positive physical left word annihilates exactly the encoded binary source
`00`. -/
theorem falseWaitFirstHitSingletonWord_zero_iff (bits : List Bool) :
    falseWaitSeparatorRow ⬝ᵥ
          (wordProduct falseWaitReturn
            (falseWaitFirstHitSingletonWord ++
              falseWaitFirstHitBinaryEncoding bits) *ᵥ
            falseWaitSeparatorColumn) = 0 ↔
      bits = falseWaitFirstHitSingletonTarget := by
  rcases falseWaitFirstHitSingletonWord_incidence bits with
    ⟨scale, scale_ne, incidence⟩
  rw [incidence, mul_eq_zero, or_iff_right scale_ne]
  exact falseWaitFirstHitBinarySourceRow_zero_iff
    falseWaitFirstHitSingletonTarget bits

end MatrixMortality.CubicReturn.NonPure
