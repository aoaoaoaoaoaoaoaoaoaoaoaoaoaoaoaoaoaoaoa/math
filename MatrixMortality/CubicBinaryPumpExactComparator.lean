import MatrixMortality.CubicTruePumpInverseConnector

/-!
# Exact whole-word comparison for the cubic binary pump

The two transverse pump letters now have positive physical inverses.  Reversing a guessed bit
word and concatenating the corresponding inverse spellings realizes the inverse of its normalized
pump product.  Hence the inverse guess followed by a written word is projectively identity exactly
when the two bit words agree.  This comparison keeps all readers before all writers; it does not
permit the interleaved mismatch cancellations present in the ambient affine group.
-/

namespace MatrixMortality.CubicReturn.NonPure

open scoped Matrix

/-- Positive physical inverse spelling selected by one binary pump bit. -/
def falseWaitBinaryPumpInverseWord : Bool → List Nat
  | false => falseWaitFalsePumpInverseWord
  | true => falseWaitTruePumpInverseWord

/-- Exact normalized inverse selected by one binary pump bit. -/
def falseWaitBinaryPumpInverseLoop : Bool → Square (Fin 2) ℚ
  | false => falseWaitFalsePumpInverseLoop
  | true => falseWaitTruePumpInverseLoop

/-- Physical length of one inverse pump spelling. -/
def falseWaitBinaryPumpInverseWordLength : Bool → Nat
  | false => 37681
  | true => 306510

/-- Reverse-order physical reader for a guessed binary word. -/
def falseWaitBinaryPumpInverseEncoding (bits : List Bool) : List Nat :=
  bits.reverse.flatMap falseWaitBinaryPumpInverseWord

/-- Reader followed by writer is the physical whole-word comparison block. -/
def falseWaitBinaryPumpComparatorWord
    (guess written : List Bool) : List Nat :=
  falseWaitBinaryPumpInverseEncoding guess ++ falseWaitFirstHitBinaryEncoding written

/-- Common-ray chart realization with an unspecified nonzero physical scale. -/
def falseWaitBinaryPumpCommonRayRealizes
    (word : List Nat) (matrix : Square (Fin 2) ℚ) : Prop :=
  ∃ scale : ℚ, scale ≠ 0 ∧
    falseWaitFirstHitBinaryBasisInverse *
          wordProduct falseWaitReturn word *
      falseWaitFirstHitBinaryBasis = scale • matrix

private theorem falseWaitBinaryPump_chart_mul
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

/-- Common-ray realizations compose under physical concatenation. -/
theorem falseWaitBinaryPumpCommonRayRealizes_append
    {leftWord rightWord : List Nat} {leftMatrix rightMatrix : Square (Fin 2) ℚ}
    (left : falseWaitBinaryPumpCommonRayRealizes leftWord leftMatrix)
    (right : falseWaitBinaryPumpCommonRayRealizes rightWord rightMatrix) :
    falseWaitBinaryPumpCommonRayRealizes (leftWord ++ rightWord)
      (leftMatrix * rightMatrix) := by
  rcases left with ⟨leftScale, leftScale_ne, leftChart⟩
  rcases right with ⟨rightScale, rightScale_ne, rightChart⟩
  refine ⟨leftScale * rightScale, mul_ne_zero leftScale_ne rightScale_ne, ?_⟩
  rw [wordProduct_append, falseWaitBinaryPump_chart_mul, leftChart, rightChart]
  ext i j
  simp [Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_succ]
  ring

/-- Each positive inverse word realizes its selected normalized inverse. -/
theorem falseWaitBinaryPumpInverseWord_chart (bit : Bool) :
    falseWaitBinaryPumpCommonRayRealizes (falseWaitBinaryPumpInverseWord bit)
      (falseWaitBinaryPumpInverseLoop bit) := by
  cases bit
  · simpa [falseWaitBinaryPumpCommonRayRealizes, falseWaitBinaryPumpInverseWord,
      falseWaitBinaryPumpInverseLoop] using falseWaitFalsePumpInverseWord_chart
  · simpa [falseWaitBinaryPumpCommonRayRealizes, falseWaitBinaryPumpInverseWord,
      falseWaitBinaryPumpInverseLoop] using falseWaitTruePumpInverseWord_chart

/-- Every inverse letter cancels its matching normalized writer on the right. -/
theorem falseWaitBinaryPumpInverseLoop_mul_writer (bit : Bool) :
    falseWaitBinaryPumpInverseLoop bit *
      falseWaitFirstHitBinaryNormalizedLoop bit = 1 := by
  cases bit
  · exact falseWaitFalsePumpInverseLoop_isInverse.1
  · exact falseWaitTruePumpInverseLoop_isInverse.1

/-- Every normalized writer cancels its matching inverse letter on the right. -/
theorem falseWaitBinaryPump_writer_mul_inverseLoop (bit : Bool) :
    falseWaitFirstHitBinaryNormalizedLoop bit *
      falseWaitBinaryPumpInverseLoop bit = 1 := by
  cases bit
  · exact falseWaitFalsePumpInverseLoop_isInverse.2
  · exact falseWaitTruePumpInverseLoop_isInverse.2

/-- Reverse inverse product followed by its writer product is exactly identity. -/
theorem falseWaitBinaryPumpInverseProduct_mul_product (bits : List Bool) :
    wordProduct falseWaitBinaryPumpInverseLoop bits.reverse *
      wordProduct falseWaitFirstHitBinaryNormalizedLoop bits = 1 := by
  induction bits with
  | nil => simp
  | cons bit bits induction =>
      rw [List.reverse_cons, wordProduct_append]
      simp only [wordProduct_cons, wordProduct_nil, Matrix.mul_one]
      calc
        _ = wordProduct falseWaitBinaryPumpInverseLoop bits.reverse *
            ((falseWaitBinaryPumpInverseLoop bit *
                falseWaitFirstHitBinaryNormalizedLoop bit) *
              wordProduct falseWaitFirstHitBinaryNormalizedLoop bits) := by
          simp only [Matrix.mul_assoc]
        _ = wordProduct falseWaitBinaryPumpInverseLoop bits.reverse *
            wordProduct falseWaitFirstHitBinaryNormalizedLoop bits := by
          rw [falseWaitBinaryPumpInverseLoop_mul_writer]
          simp
        _ = 1 := induction

/-- A writer product followed by its reverse inverse product is exactly identity. -/
theorem falseWaitBinaryPumpProduct_mul_inverseProduct (bits : List Bool) :
    wordProduct falseWaitFirstHitBinaryNormalizedLoop bits *
      wordProduct falseWaitBinaryPumpInverseLoop bits.reverse = 1 := by
  induction bits with
  | nil => simp
  | cons bit bits induction =>
      rw [List.reverse_cons, wordProduct_append]
      simp only [wordProduct_cons, wordProduct_nil, Matrix.mul_one]
      calc
        _ = falseWaitFirstHitBinaryNormalizedLoop bit *
            ((wordProduct falseWaitFirstHitBinaryNormalizedLoop bits *
                wordProduct falseWaitBinaryPumpInverseLoop bits.reverse) *
              falseWaitBinaryPumpInverseLoop bit) := by
          simp only [Matrix.mul_assoc]
        _ = falseWaitFirstHitBinaryNormalizedLoop bit *
            falseWaitBinaryPumpInverseLoop bit := by
          rw [induction]
          simp
        _ = 1 := falseWaitBinaryPump_writer_mul_inverseLoop bit

/-- A normalized inverse guess and writer product are projectively identity exactly on equality. -/
theorem falseWaitBinaryPumpNormalizedComparator_identity_iff
    (guess written : List Bool) :
    (∃ scale : ℚ,
      wordProduct falseWaitBinaryPumpInverseLoop guess.reverse *
          wordProduct falseWaitFirstHitBinaryNormalizedLoop written =
        scale • (1 : Square (Fin 2) ℚ)) ↔
      guess = written := by
  constructor
  · rintro ⟨scale, comparison⟩
    have product_eq :
        wordProduct falseWaitFirstHitBinaryNormalizedLoop written =
          scale • wordProduct falseWaitFirstHitBinaryNormalizedLoop guess := by
      calc
        _ = (wordProduct falseWaitFirstHitBinaryNormalizedLoop guess *
              wordProduct falseWaitBinaryPumpInverseLoop guess.reverse) *
            wordProduct falseWaitFirstHitBinaryNormalizedLoop written := by
          rw [falseWaitBinaryPumpProduct_mul_inverseProduct]
          simp
        _ = wordProduct falseWaitFirstHitBinaryNormalizedLoop guess *
            (wordProduct falseWaitBinaryPumpInverseLoop guess.reverse *
              wordProduct falseWaitFirstHitBinaryNormalizedLoop written) := by
          simp only [Matrix.mul_assoc]
        _ = wordProduct falseWaitFirstHitBinaryNormalizedLoop guess *
            (scale • (1 : Square (Fin 2) ℚ)) := by
          rw [comparison]
        _ = scale • wordProduct falseWaitFirstHitBinaryNormalizedLoop guess := by
          simp only [Matrix.mul_smul, Matrix.mul_one]
    exact (falseWaitFirstHitBinaryNormalizedLoop_projectively_injective product_eq).symm
  · rintro rfl
    exact ⟨1, by
      rw [falseWaitBinaryPumpInverseProduct_mul_product]
      simp⟩

/-- The physical inverse encoding realizes the reverse normalized inverse product. -/
theorem falseWaitBinaryPumpInverseEncoding_chart (bits : List Bool) :
    falseWaitBinaryPumpCommonRayRealizes (falseWaitBinaryPumpInverseEncoding bits)
      (wordProduct falseWaitBinaryPumpInverseLoop bits.reverse) := by
  have direct : ∀ directBits : List Bool,
      falseWaitBinaryPumpCommonRayRealizes
        (directBits.flatMap falseWaitBinaryPumpInverseWord)
        (wordProduct falseWaitBinaryPumpInverseLoop directBits) := by
    intro directBits
    induction directBits with
    | nil =>
        refine ⟨1, one_ne_zero, ?_⟩
        simp [falseWaitFirstHitBinaryBasis_inverse_left]
    | cons bit directBits induction =>
        simpa only [List.flatMap_cons, wordProduct_cons] using
          falseWaitBinaryPumpCommonRayRealizes_append
            (falseWaitBinaryPumpInverseWord_chart bit) induction
  exact direct bits.reverse

/-- The physical comparison word realizes the normalized comparison product. -/
theorem falseWaitBinaryPumpComparatorWord_chart (guess written : List Bool) :
    falseWaitBinaryPumpCommonRayRealizes
      (falseWaitBinaryPumpComparatorWord guess written)
      (wordProduct falseWaitBinaryPumpInverseLoop guess.reverse *
        wordProduct falseWaitFirstHitBinaryNormalizedLoop written) := by
  have writer :
      falseWaitBinaryPumpCommonRayRealizes
        (falseWaitFirstHitBinaryEncoding written)
        (wordProduct falseWaitFirstHitBinaryNormalizedLoop written) := by
    refine ⟨(written.map falseWaitFirstHitBinaryScale).prod,
      falseWaitFirstHitBinaryEncoding_scale_ne_zero written, ?_⟩
    exact falseWaitFirstHitBinaryEncoding_chart written
  simpa [falseWaitBinaryPumpComparatorWord] using
    falseWaitBinaryPumpCommonRayRealizes_append
      (falseWaitBinaryPumpInverseEncoding_chart guess) writer

private theorem falseWaitBinaryPump_projectiveIdentity_of_chart
    {word : List Nat} {scale : ℚ}
    (chart :
      falseWaitFirstHitBinaryBasisInverse *
            wordProduct falseWaitReturn word *
        falseWaitFirstHitBinaryBasis =
          scale • (1 : Square (Fin 2) ℚ)) :
    wordProduct falseWaitReturn word = scale • (1 : Square (Fin 2) ℚ) := by
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

/-- The physical comparison block is projectively identity exactly when its words agree. -/
theorem falseWaitBinaryPumpComparatorWord_projectiveIdentity_iff
    (guess written : List Bool) :
    (∃ scale : ℚ,
      wordProduct falseWaitReturn (falseWaitBinaryPumpComparatorWord guess written) =
        scale • (1 : Square (Fin 2) ℚ)) ↔
      guess = written := by
  constructor
  · rintro ⟨physicalScale, physicalIdentity⟩
    rcases falseWaitBinaryPumpComparatorWord_chart guess written with
      ⟨chartScale, chartScale_ne, comparisonChart⟩
    have conjugatedIdentity :
        falseWaitFirstHitBinaryBasisInverse *
              wordProduct falseWaitReturn
                (falseWaitBinaryPumpComparatorWord guess written) *
            falseWaitFirstHitBinaryBasis =
          physicalScale • (1 : Square (Fin 2) ℚ) := by
      rw [physicalIdentity, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        falseWaitFirstHitBinaryBasis_inverse_left]
    have scaledComparison :
        chartScale •
            (wordProduct falseWaitBinaryPumpInverseLoop guess.reverse *
              wordProduct falseWaitFirstHitBinaryNormalizedLoop written) =
          physicalScale • (1 : Square (Fin 2) ℚ) :=
      comparisonChart.symm.trans conjugatedIdentity
    have normalizedComparison :
        wordProduct falseWaitBinaryPumpInverseLoop guess.reverse *
            wordProduct falseWaitFirstHitBinaryNormalizedLoop written =
          (physicalScale / chartScale) • (1 : Square (Fin 2) ℚ) := by
      ext i j
      have entry_eq := congrFun (congrFun scaledComparison i) j
      simp only [Matrix.smul_apply, smul_eq_mul] at entry_eq ⊢
      calc
        _ = chartScale⁻¹ *
            (chartScale *
              (wordProduct falseWaitBinaryPumpInverseLoop guess.reverse *
                wordProduct falseWaitFirstHitBinaryNormalizedLoop written) i j) := by
          field_simp
        _ = chartScale⁻¹ * (physicalScale * (1 : Square (Fin 2) ℚ) i j) := by
          rw [entry_eq]
        _ = physicalScale / chartScale * (1 : Square (Fin 2) ℚ) i j := by
          ring
    exact (falseWaitBinaryPumpNormalizedComparator_identity_iff guess written).1
      ⟨physicalScale / chartScale, normalizedComparison⟩
  · rintro rfl
    rcases falseWaitBinaryPumpComparatorWord_chart guess guess with
      ⟨chartScale, _, chart⟩
    rw [falseWaitBinaryPumpInverseProduct_mul_product] at chart
    exact ⟨chartScale,
      falseWaitBinaryPump_projectiveIdentity_of_chart chart⟩

/-- A positive continuation can be cancelled from a physical comparison. Thus the comparison
preserves that continuation projectively exactly when the guessed and written words agree. -/
theorem falseWaitBinaryPumpComparatorWord_suffix_iff
    (guess written : List Bool) (suffix : List Nat)
    (suffixPositive : ∀ wait ∈ suffix, 0 < wait) :
    (∃ scale : ℚ,
      wordProduct falseWaitReturn
          (falseWaitBinaryPumpComparatorWord guess written ++ suffix) =
        scale • wordProduct falseWaitReturn suffix) ↔
      guess = written := by
  have suffixUnit : IsUnit (wordProduct falseWaitReturn suffix) :=
    falseWaitReturn_wordProduct_isUnit_of_positive suffix suffixPositive
  constructor
  · rintro ⟨scale, contextualIdentity⟩
    apply (falseWaitBinaryPumpComparatorWord_projectiveIdentity_iff guess written).1
    refine ⟨scale, ?_⟩
    apply suffixUnit.mul_right_cancel
    simpa only [wordProduct_append, Matrix.smul_mul, Matrix.one_mul] using
      contextualIdentity
  · intro equality
    rcases (falseWaitBinaryPumpComparatorWord_projectiveIdentity_iff guess written).2 equality with
      ⟨scale, comparisonIdentity⟩
    refine ⟨scale, ?_⟩
    rw [wordProduct_append, comparisonIdentity, Matrix.smul_mul, Matrix.one_mul]

/-- Arbitrary positive physical context does not weaken exact whole-word comparison. -/
theorem falseWaitBinaryPumpComparatorWord_context_iff
    (initial : List Nat) (guess written : List Bool) (suffix : List Nat)
    (initialPositive : ∀ wait ∈ initial, 0 < wait)
    (suffixPositive : ∀ wait ∈ suffix, 0 < wait) :
    (∃ scale : ℚ,
      wordProduct falseWaitReturn
          (initial ++ falseWaitBinaryPumpComparatorWord guess written ++ suffix) =
        scale • wordProduct falseWaitReturn (initial ++ suffix)) ↔
      guess = written := by
  have initialUnit : IsUnit (wordProduct falseWaitReturn initial) :=
    falseWaitReturn_wordProduct_isUnit_of_positive initial initialPositive
  constructor
  · rintro ⟨scale, contextualIdentity⟩
    apply (falseWaitBinaryPumpComparatorWord_suffix_iff guess written suffix
      suffixPositive).1
    refine ⟨scale, ?_⟩
    apply initialUnit.mul_left_cancel
    simpa only [wordProduct_append, Matrix.mul_assoc, Matrix.mul_smul] using
      contextualIdentity
  · intro equality
    rcases (falseWaitBinaryPumpComparatorWord_suffix_iff guess written suffix
      suffixPositive).2 equality with ⟨scale, suffixIdentity⟩
    refine ⟨scale, ?_⟩
    calc
      wordProduct falseWaitReturn
          (initial ++ falseWaitBinaryPumpComparatorWord guess written ++ suffix) =
          wordProduct falseWaitReturn initial *
            wordProduct falseWaitReturn
              (falseWaitBinaryPumpComparatorWord guess written ++ suffix) := by
            rw [List.append_assoc, wordProduct_append]
      _ = wordProduct falseWaitReturn initial *
          (scale • wordProduct falseWaitReturn suffix) := by
            rw [suffixIdentity]
      _ = scale •
          (wordProduct falseWaitReturn initial *
            wordProduct falseWaitReturn suffix) := by
            rw [Matrix.mul_smul]
      _ = scale • wordProduct falseWaitReturn (initial ++ suffix) := by
            rw [wordProduct_append]

/-- Every wait in an inverse encoding is strictly positive. -/
theorem falseWaitBinaryPumpInverseEncoding_positive (bits : List Bool) :
    ∀ wait ∈ falseWaitBinaryPumpInverseEncoding bits, 0 < wait := by
  intro wait membership
  obtain ⟨bit, _, wait_mem⟩ := List.mem_flatMap.mp membership
  cases bit
  · exact falseWaitFalsePumpInverseWord_positive wait wait_mem
  · exact falseWaitTruePumpInverseWord_positive wait wait_mem

/-- Exact length of each inverse letter. -/
theorem falseWaitBinaryPumpInverseWord_length (bit : Bool) :
    (falseWaitBinaryPumpInverseWord bit).length =
      falseWaitBinaryPumpInverseWordLength bit := by
  cases bit
  · exact falseWaitFalsePumpInverseWord_length
  · exact falseWaitTruePumpInverseWord_length

/-- Exact variable-rate length of a reverse inverse encoding. -/
theorem falseWaitBinaryPumpInverseEncoding_length (bits : List Bool) :
    (falseWaitBinaryPumpInverseEncoding bits).length =
      (bits.map falseWaitBinaryPumpInverseWordLength).sum := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      rw [falseWaitBinaryPumpInverseEncoding, List.reverse_cons,
        List.flatMap_append, List.length_append, List.flatMap_singleton,
        falseWaitBinaryPumpInverseWord_length]
      change (bits.reverse.flatMap falseWaitBinaryPumpInverseWord).length +
          falseWaitBinaryPumpInverseWordLength bit =
        falseWaitBinaryPumpInverseWordLength bit +
          (bits.map falseWaitBinaryPumpInverseWordLength).sum
      rw [← falseWaitBinaryPumpInverseEncoding, induction]
      omega

/-- Exact physical length of the whole-word comparison block. -/
theorem falseWaitBinaryPumpComparatorWord_length (guess written : List Bool) :
    (falseWaitBinaryPumpComparatorWord guess written).length =
      (guess.map falseWaitBinaryPumpInverseWordLength).sum + 4 * written.length := by
  rw [falseWaitBinaryPumpComparatorWord, List.length_append,
    falseWaitBinaryPumpInverseEncoding_length,
    falseWaitFirstHitBinaryEncoding_length]

/-- Every wait in the whole-word comparison block is strictly positive. -/
theorem falseWaitBinaryPumpComparatorWord_positive (guess written : List Bool) :
    ∀ wait ∈ falseWaitBinaryPumpComparatorWord guess written, 0 < wait := by
  intro wait membership
  simp only [falseWaitBinaryPumpComparatorWord, List.mem_append] at membership
  exact membership.elim
    (falseWaitBinaryPumpInverseEncoding_positive guess wait)
    (falseWaitFirstHitBinaryEncoding_positive written wait)

end MatrixMortality.CubicReturn.NonPure
