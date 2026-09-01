import MatrixMortality.CubicContinuantSourceStabilizer

/-!
# A free binary positive stabilizer family of the cubic separator source

One fixed positive terminal translation sends the safe transverse pump ray to the original
separator-source ray. Sandwiching every free transverse binary address between that translation
and the safe suffix therefore gives a projectively free binary family of positive source
stabilizers. Prefixing the selected `00` source produces exponentially many projectively distinct
words in one observed source fibre.
-/

namespace MatrixMortality.CubicReturn.NonPure

open scoped Matrix

/-- Terminal-translation counts realizing the source-return shift `-41/90`. -/
def falseWaitFreeSourceReturnCounts : ContinuantTerminalTranslationCounts :=
  ⟨1003, 24, 1148, 375⟩

/-- Fixed positive terminal word that sends the safe pump ray back to the separator source. -/
def falseWaitFreeSourceReturnWord : List Nat :=
  continuantTerminalTranslationWord falseWaitFreeSourceReturnCounts

/-- Positive separator-source stabilizer carrying one arbitrary transverse binary address. -/
def falseWaitFreeSourceStabilizerWord (bits : List Bool) : List Nat :=
  falseWaitFreeSourceReturnWord ++
    (falseWaitFirstHitBinaryEncoding bits ++ falseWaitNonacceptingMergeShort)

/-- Selected `00` source followed by one free binary source stabilizer. -/
def falseWaitSelectedFreeSourceFibreWord (bits : List Bool) : List Nat :=
  falseWaitSelectedSourceWord ++ falseWaitFreeSourceStabilizerWord bits

/-- Normalized fixed translation sending the safe pump ray to the separator source ray. -/
def falseWaitFreeSourceReturn : Square (Fin 2) ℚ :=
  continuantDefectTranslation (-41 / 90)

/-- The fixed positive terminal word realizes the exact source-return translation. -/
theorem falseWaitFreeSourceReturnWord_projectivelyRealizes :
    continuantProjectivelyRealizes falseWaitFreeSourceReturnWord
      falseWaitFreeSourceReturn := by
  have realization := continuantTerminalTranslationWord_projectivelyRealizes
    falseWaitFreeSourceReturnCounts
  have shift :
      continuantTerminalTranslationShift falseWaitFreeSourceReturnCounts =
        -41 / 90 := by
    norm_num [falseWaitFreeSourceReturnCounts,
      continuantTerminalTranslationShift]
  rw [shift] at realization
  exact realization

/-- The normalized source-return translation sends the safe ray to `-1/30` times the separator
source. -/
theorem falseWaitFreeSourceReturn_ray :
    falseWaitFreeSourceReturn *ᵥ ![4, 3] =
      (-1 / 30 : ℚ) • falseWaitSeparatorColumn := by
  ext coordinate
  fin_cases coordinate <;>
    norm_num [falseWaitFreeSourceReturn, continuantDefectTranslation,
      falseWaitSeparatorColumn, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Every wait in the fixed source-return word is strictly positive. -/
theorem falseWaitFreeSourceReturnWord_positive :
    ∀ wait ∈ falseWaitFreeSourceReturnWord, 0 < wait := by
  exact continuantTerminalTranslationWord_positive falseWaitFreeSourceReturnCounts

/-- The fixed source-return word has exact physical length `71,185`. -/
theorem falseWaitFreeSourceReturnWord_length :
    falseWaitFreeSourceReturnWord.length = 71185 := by
  rw [falseWaitFreeSourceReturnWord,
    continuantTerminalTranslationWord_length]
  norm_num [falseWaitFreeSourceReturnCounts]

/-- Every free binary source-stabilizer spelling uses only strictly positive waits. -/
theorem falseWaitFreeSourceStabilizerWord_positive (bits : List Bool) :
    ∀ wait ∈ falseWaitFreeSourceStabilizerWord bits, 0 < wait := by
  intro wait membership
  simp only [falseWaitFreeSourceStabilizerWord,
    List.mem_append] at membership
  rcases membership with returnWord | encodedOrSuffix
  · exact falseWaitFreeSourceReturnWord_positive wait returnWord
  rcases encodedOrSuffix with encoded | suffix
  · exact falseWaitFirstHitBinaryEncoding_positive bits wait encoded
  · simp [falseWaitNonacceptingMergeShort] at suffix
    omega

/-- Exact physical length of a free binary source stabilizer. -/
theorem falseWaitFreeSourceStabilizerWord_length (bits : List Bool) :
    (falseWaitFreeSourceStabilizerWord bits).length =
      71191 + 4 * bits.length := by
  rw [falseWaitFreeSourceStabilizerWord, List.length_append,
    List.length_append, falseWaitFreeSourceReturnWord_length,
    falseWaitFirstHitBinaryEncoding_length]
  norm_num [falseWaitNonacceptingMergeShort]
  omega

/-- Every free binary word stabilizes the original separator source up to a nonzero scale. -/
theorem falseWaitFreeSourceStabilizerWord_source (bits : List Bool) :
    ∃ scale : ℚ, scale ≠ 0 ∧
      wordProduct falseWaitReturn (falseWaitFreeSourceStabilizerWord bits) *ᵥ
          falseWaitSeparatorColumn =
        scale • falseWaitSeparatorColumn := by
  rcases falseWaitFreeSourceReturnWord_projectivelyRealizes with
    ⟨returnScale, returnScale_ne, returnProduct⟩
  let binaryScale := (bits.map falseWaitFirstHitBinaryScale).prod
  have binaryScale_ne : binaryScale ≠ 0 :=
    falseWaitFirstHitBinaryEncoding_scale_ne_zero bits
  refine ⟨returnScale * (-72590904000000 * binaryScale) * (-1 / 30),
    mul_ne_zero
      (mul_ne_zero returnScale_ne
        (mul_ne_zero (by norm_num) binaryScale_ne))
      (by norm_num), ?_⟩
  rw [falseWaitFreeSourceStabilizerWord, wordProduct_append,
    ← Matrix.mulVec_mulVec,
    falseWaitFirstHitBinaryEncoding_suffix_source, Matrix.mulVec_smul,
    returnProduct, Matrix.smul_mulVec, falseWaitFreeSourceReturn_ray,
    smul_smul, smul_smul]
  congr 1
  dsimp [binaryScale]
  ring

/-- The free binary source-stabilizer family is projectively injective in its address. -/
theorem falseWaitFreeSourceStabilizerWord_projectively_injective
    {left right : List Bool} {scale : ℚ}
    (projective_eq :
      wordProduct falseWaitReturn (falseWaitFreeSourceStabilizerWord left) =
        scale •
          wordProduct falseWaitReturn (falseWaitFreeSourceStabilizerWord right)) :
    left = right := by
  let returnProduct :=
    wordProduct falseWaitReturn falseWaitFreeSourceReturnWord
  let suffixProduct :=
    wordProduct falseWaitReturn falseWaitNonacceptingMergeShort
  have returnUnit : IsUnit returnProduct :=
    falseWaitReturn_wordProduct_isUnit_of_positive _
      falseWaitFreeSourceReturnWord_positive
  have suffixPositive :
      ∀ wait ∈ falseWaitNonacceptingMergeShort, 0 < wait := by
    simp [falseWaitNonacceptingMergeShort]
  have suffixUnit : IsUnit suffixProduct :=
    falseWaitReturn_wordProduct_isUnit_of_positive _ suffixPositive
  have contextual_eq :
      returnProduct *
          (wordProduct falseWaitReturn (falseWaitFirstHitBinaryEncoding left) *
            suffixProduct) =
        returnProduct *
          ((scale •
              wordProduct falseWaitReturn (falseWaitFirstHitBinaryEncoding right)) *
            suffixProduct) := by
    calc
      returnProduct *
            (wordProduct falseWaitReturn (falseWaitFirstHitBinaryEncoding left) *
              suffixProduct) =
          wordProduct falseWaitReturn
            (falseWaitFreeSourceStabilizerWord left) := by
              simp [returnProduct, suffixProduct,
                falseWaitFreeSourceStabilizerWord,
                wordProduct_append]
      _ = scale •
          wordProduct falseWaitReturn
            (falseWaitFreeSourceStabilizerWord right) := projective_eq
      _ = returnProduct *
          ((scale •
              wordProduct falseWaitReturn (falseWaitFirstHitBinaryEncoding right)) *
            suffixProduct) := by
              simp [returnProduct, suffixProduct,
                falseWaitFreeSourceStabilizerWord,
                wordProduct_append]
  have afterReturn :
      wordProduct falseWaitReturn (falseWaitFirstHitBinaryEncoding left) *
          suffixProduct =
        (scale •
            wordProduct falseWaitReturn (falseWaitFirstHitBinaryEncoding right)) *
          suffixProduct :=
    returnUnit.mul_left_cancel contextual_eq
  have afterSuffix :
      wordProduct falseWaitReturn (falseWaitFirstHitBinaryEncoding left) =
        scale •
          wordProduct falseWaitReturn (falseWaitFirstHitBinaryEncoding right) :=
    suffixUnit.mul_right_cancel afterReturn
  exact falseWaitFirstHitBinaryEncoding_product_projectively_injective afterSuffix

/-- Every selected free source-fibre spelling uses only strictly positive waits. -/
theorem falseWaitSelectedFreeSourceFibreWord_positive (bits : List Bool) :
    ∀ wait ∈ falseWaitSelectedFreeSourceFibreWord bits, 0 < wait := by
  intro wait membership
  rw [falseWaitSelectedFreeSourceFibreWord,
    List.mem_append] at membership
  exact membership.elim
    (falseWaitFirstHitBinaryEncoding_positive
      falseWaitFirstHitSingletonTarget wait)
    (falseWaitFreeSourceStabilizerWord_positive bits wait)

/-- Exact physical length of a selected free source-fibre word. -/
theorem falseWaitSelectedFreeSourceFibreWord_length (bits : List Bool) :
    (falseWaitSelectedFreeSourceFibreWord bits).length =
      71199 + 4 * bits.length := by
  rw [falseWaitSelectedFreeSourceFibreWord, List.length_append,
    falseWaitFreeSourceStabilizerWord_length]
  norm_num [falseWaitSelectedSourceWord, falseWaitFirstHitSingletonTarget,
    falseWaitFirstHitBinaryEncoding, falseWaitFirstHitBinaryLoop]
  omega

/-- Every selected free source-fibre word induces the same source ray as the selected `00` word. -/
theorem falseWaitSelectedFreeSourceFibreWord_source (bits : List Bool) :
    ∃ scale : ℚ, scale ≠ 0 ∧
      wordProduct falseWaitReturn (falseWaitSelectedFreeSourceFibreWord bits) *ᵥ
          falseWaitSeparatorColumn =
        scale •
          (wordProduct falseWaitReturn falseWaitSelectedSourceWord *ᵥ
            falseWaitSeparatorColumn) := by
  rcases falseWaitFreeSourceStabilizerWord_source bits with
    ⟨scale, scale_ne, source⟩
  refine ⟨scale, scale_ne, ?_⟩
  rw [falseWaitSelectedFreeSourceFibreWord, wordProduct_append,
    ← Matrix.mulVec_mulVec, source, Matrix.mulVec_smul]

/-- The selected source-fibre family remains projectively injective in its binary address. -/
theorem falseWaitSelectedFreeSourceFibreWord_projectively_injective
    {left right : List Bool} {scale : ℚ}
    (projective_eq :
      wordProduct falseWaitReturn (falseWaitSelectedFreeSourceFibreWord left) =
        scale •
          wordProduct falseWaitReturn (falseWaitSelectedFreeSourceFibreWord right)) :
    left = right := by
  have selectedPositive :
      ∀ wait ∈ falseWaitSelectedSourceWord, 0 < wait :=
    falseWaitFirstHitBinaryEncoding_positive falseWaitFirstHitSingletonTarget
  have selectedUnit :
      IsUnit (wordProduct falseWaitReturn falseWaitSelectedSourceWord) :=
    falseWaitReturn_wordProduct_isUnit_of_positive _ selectedPositive
  have contextual_eq :
      wordProduct falseWaitReturn falseWaitSelectedSourceWord *
          wordProduct falseWaitReturn (falseWaitFreeSourceStabilizerWord left) =
        wordProduct falseWaitReturn falseWaitSelectedSourceWord *
          (scale •
            wordProduct falseWaitReturn
              (falseWaitFreeSourceStabilizerWord right)) := by
    calc
      wordProduct falseWaitReturn falseWaitSelectedSourceWord *
            wordProduct falseWaitReturn
              (falseWaitFreeSourceStabilizerWord left) =
          wordProduct falseWaitReturn
            (falseWaitSelectedFreeSourceFibreWord left) := by
              simp [falseWaitSelectedFreeSourceFibreWord,
                wordProduct_append]
      _ = scale •
          wordProduct falseWaitReturn
            (falseWaitSelectedFreeSourceFibreWord right) := projective_eq
      _ = wordProduct falseWaitReturn falseWaitSelectedSourceWord *
          (scale •
            wordProduct falseWaitReturn
              (falseWaitFreeSourceStabilizerWord right)) := by
              simp [falseWaitSelectedFreeSourceFibreWord,
                wordProduct_append]
  have afterSelected := selectedUnit.mul_left_cancel contextual_eq
  exact falseWaitFreeSourceStabilizerWord_projectively_injective afterSelected

/-- The selected free source-fibre spelling is literally injective in its binary address. -/
theorem falseWaitSelectedFreeSourceFibreWord_injective :
    Function.Injective falseWaitSelectedFreeSourceFibreWord := by
  intro left right word_eq
  have product_eq := congrArg (wordProduct falseWaitReturn) word_eq
  exact falseWaitSelectedFreeSourceFibreWord_projectively_injective
    (scale := 1) (by simpa using product_eq)

/-- Fixed-width vector indexing of the selected free source-fibre family. -/
def falseWaitSelectedFreeSourceFibreOfVector
    {width : Nat} (bits : Fin width → Bool) : List Nat :=
  falseWaitSelectedFreeSourceFibreWord (List.ofFn bits)

/-- Fixed-width selected source-fibre indexing is literally injective. -/
theorem falseWaitSelectedFreeSourceFibreOfVector_injective (width : Nat) :
    Function.Injective
      (falseWaitSelectedFreeSourceFibreOfVector (width := width)) :=
  falseWaitSelectedFreeSourceFibreWord_injective.comp List.ofFn_injective

/-- Fixed-width selected source-fibre products remain distinct even up to projective scale. -/
theorem falseWaitSelectedFreeSourceFibreOfVector_projectively_injective
    {width : Nat} {left right : Fin width → Bool} {scale : ℚ}
    (projective_eq :
      wordProduct falseWaitReturn (falseWaitSelectedFreeSourceFibreOfVector left) =
        scale •
          wordProduct falseWaitReturn
            (falseWaitSelectedFreeSourceFibreOfVector right)) :
    left = right := by
  apply List.ofFn_injective
  exact falseWaitSelectedFreeSourceFibreWord_projectively_injective projective_eq

/-- Every width-`n` selected source-fibre word has common length `71,199+4n`. -/
theorem falseWaitSelectedFreeSourceFibreOfVector_length
    {width : Nat} (bits : Fin width → Bool) :
    (falseWaitSelectedFreeSourceFibreOfVector bits).length = 71199 + 4 * width := by
  rw [falseWaitSelectedFreeSourceFibreOfVector,
    falseWaitSelectedFreeSourceFibreWord_length, List.length_ofFn]

/-- Every fixed-width selected source-fibre word induces the selected `00` source ray. -/
theorem falseWaitSelectedFreeSourceFibreOfVector_source
    {width : Nat} (bits : Fin width → Bool) :
    ∃ scale : ℚ, scale ≠ 0 ∧
      wordProduct falseWaitReturn (falseWaitSelectedFreeSourceFibreOfVector bits) *ᵥ
          falseWaitSeparatorColumn =
        scale •
          (wordProduct falseWaitReturn falseWaitSelectedSourceWord *ᵥ
            falseWaitSeparatorColumn) :=
  falseWaitSelectedFreeSourceFibreWord_source (List.ofFn bits)

/-- Finite width-`n` family of selected free source-fibre words. -/
def falseWaitSelectedFreeSourceFibreFamily (width : Nat) : Finset (List Nat) :=
  Finset.univ.image
    (falseWaitSelectedFreeSourceFibreOfVector (width := width))

/-- Width `n` supplies exactly `2^n` equal-length, projectively distinct products in the selected
source fibre. -/
theorem falseWaitSelectedFreeSourceFibreFamily_card (width : Nat) :
    (falseWaitSelectedFreeSourceFibreFamily width).card = 2 ^ width := by
  rw [falseWaitSelectedFreeSourceFibreFamily,
    Finset.card_image_of_injective _
      (falseWaitSelectedFreeSourceFibreOfVector_injective width)]
  simp

end MatrixMortality.CubicReturn.NonPure
