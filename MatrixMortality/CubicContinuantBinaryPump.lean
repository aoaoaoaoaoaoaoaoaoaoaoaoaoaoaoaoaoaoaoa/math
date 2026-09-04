import MatrixMortality.CubicContinuantInternalPump

/-!
# Binary first-hit bridge pumps in the fixed cubic continuant family

Two distinct positive four-letter loops stabilize the same nonaccepting internal ray, avoid the
accepting ray at every internal suffix, and form an injective literal binary code. Prefixing any
encoded loop word to the fixed safe suffix and then wait thirteen gives a distinct first-hit
bridge. Width `n` therefore supplies exactly `2^n` equal-length positive bridge words.
-/

namespace MatrixMortality.CubicReturn.NonPure

open scoped Matrix

/-- Two safe non-scalar loops on the same nonaccepting internal ray. -/
def falseWaitFirstHitBinaryLoop : Bool → List Nat
  | false => [1, 15, 7, 1]
  | true => [1, 15, 38, 6]

/-- Exact projective scales of the two safe internal loops. -/
def falseWaitFirstHitBinaryScale : Bool → ℚ
  | false => 777600000
  | true => 182891520000

/-- Concatenate the safe loop selected by every bit. -/
def falseWaitFirstHitBinaryEncoding (bits : List Bool) : List Nat :=
  bits.flatMap falseWaitFirstHitBinaryLoop

/-- Every binary loop preserves the common nonaccepting ray. -/
theorem falseWaitFirstHitBinaryLoop_ray (bit : Bool) :
    wordProduct falseWaitReturn (falseWaitFirstHitBinaryLoop bit) *ᵥ ![4, 3] =
      falseWaitFirstHitBinaryScale bit • ![4, 3] := by
  cases bit <;>
    ext coordinate <;>
    fin_cases coordinate <;>
      norm_num [falseWaitFirstHitBinaryLoop, falseWaitFirstHitBinaryScale,
        wordProduct_cons, wordProduct_nil, falseWaitReturn_eq_state,
        falseWaitReturnOfState, cubicDefectState, CubicDefectState.next,
        Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Binary-loop scales never vanish. -/
theorem falseWaitFirstHitBinaryScale_ne_zero (bit : Bool) :
    falseWaitFirstHitBinaryScale bit ≠ 0 := by
  cases bit <;> norm_num [falseWaitFirstHitBinaryScale]

/-- Neither safe binary loop is a global projective identity. -/
theorem falseWaitFirstHitBinaryLoop_not_projectiveIdentity (bit : Bool)
    (scale : ℚ) :
    wordProduct falseWaitReturn (falseWaitFirstHitBinaryLoop bit) ≠
      scale • (1 : Square (Fin 2) ℚ) := by
  intro identity
  have upper_right := congrFun (congrFun identity 0) 1
  cases bit <;>
    norm_num [falseWaitFirstHitBinaryLoop, wordProduct_cons, wordProduct_nil,
      falseWaitReturn_eq_state, falseWaitReturnOfState, cubicDefectState,
      CubicDefectState.next, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_succ] at upper_right

/-- Every binary loop word is a positive-wait word. -/
theorem falseWaitFirstHitBinaryEncoding_positive (bits : List Bool) :
    ∀ wait ∈ falseWaitFirstHitBinaryEncoding bits, 0 < wait := by
  intro wait membership
  obtain ⟨bit, _, wait_mem⟩ := List.mem_flatMap.mp membership
  cases bit <;> simp [falseWaitFirstHitBinaryLoop] at wait_mem <;> omega

/-- Binary loop encoding respects concatenation exactly. -/
theorem falseWaitFirstHitBinaryEncoding_append (left right : List Bool) :
    falseWaitFirstHitBinaryEncoding (left ++ right) =
      falseWaitFirstHitBinaryEncoding left ++
        falseWaitFirstHitBinaryEncoding right := by
  simp [falseWaitFirstHitBinaryEncoding, List.flatMap_append]

/-- A binary loop encoding acts on the common ray by the product of its letter scales. -/
theorem falseWaitFirstHitBinaryEncoding_ray (bits : List Bool) :
    wordProduct falseWaitReturn (falseWaitFirstHitBinaryEncoding bits) *ᵥ ![4, 3] =
      (bits.map falseWaitFirstHitBinaryScale).prod • ![4, 3] := by
  induction bits with
  | nil => simp [falseWaitFirstHitBinaryEncoding]
  | cons bit bits induction =>
      simp only [falseWaitFirstHitBinaryEncoding] at induction ⊢
      rw [List.flatMap_cons, wordProduct_append,
        ← Matrix.mulVec_mulVec, induction, Matrix.mulVec_smul,
        falseWaitFirstHitBinaryLoop_ray, List.map_cons, List.prod_cons,
        smul_smul]
      simp only [mul_comm]

/-- The scale product of any binary loop encoding is nonzero. -/
theorem falseWaitFirstHitBinaryEncoding_scale_ne_zero (bits : List Bool) :
    (bits.map falseWaitFirstHitBinaryScale).prod ≠ 0 := by
  apply List.prod_ne_zero
  intro zero_mem
  obtain ⟨bit, _, scale_zero⟩ := List.mem_map.mp zero_mem
  exact falseWaitFirstHitBinaryScale_ne_zero bit scale_zero

/-- Every binary loop encoding followed by the fixed suffix reaches the same nonaccepting ray. -/
theorem falseWaitFirstHitBinaryEncoding_suffix_source (bits : List Bool) :
    wordProduct falseWaitReturn
          (falseWaitFirstHitBinaryEncoding bits ++ falseWaitNonacceptingMergeShort) *ᵥ
        falseWaitSeparatorColumn =
      (-72590904000000 * (bits.map falseWaitFirstHitBinaryScale).prod : ℚ) •
        ![4, 3] := by
  have suffix_source :
      wordProduct falseWaitReturn falseWaitNonacceptingMergeShort *ᵥ
          falseWaitSeparatorColumn =
        (-72590904000000 : ℚ) • ![4, 3] := by
    simpa [falseWaitNonacceptingMergeShort, falseWaitInternalPumpSuffix,
      falseWaitInternalPumpSuffixScale, falseWaitInternalPumpRay] using
        falseWaitInternalPumpSuffix_source 0
  rw [wordProduct_append, ← Matrix.mulVec_mulVec, suffix_source,
    Matrix.mulVec_smul, falseWaitFirstHitBinaryEncoding_ray, smul_smul]

/-- Prefixing wait thirteen turns every binary-loop encoding into an exact accepting bridge. -/
theorem falseWaitFirstHitBinaryBridge_source (bits : List Bool) :
    wordProduct falseWaitReturn
          ([13] ++
            (falseWaitFirstHitBinaryEncoding bits ++ falseWaitNonacceptingMergeShort)) *ᵥ
        falseWaitSeparatorColumn =
      (29617088832000000 *
          (bits.map falseWaitFirstHitBinaryScale).prod : ℚ) • ![1, 0] := by
  have prefix_ray :
      wordProduct falseWaitReturn [13] *ᵥ ![4, 3] =
        (-408 : ℚ) • ![1, 0] := by
    simpa [falseWaitInternalPumpPrefix, falseWaitInternalPumpRay,
      falseWaitInternalPumpPrefixScale, wordProduct_cons] using
        falseWaitInternalPumpPrefix_ray 0
  rw [wordProduct_append, ← Matrix.mulVec_mulVec,
    falseWaitFirstHitBinaryEncoding_suffix_source, Matrix.mulVec_smul,
    prefix_ray, smul_smul]
  congr 1
  ring

/-- Every binary loop spelling yields an exact bridge zero between singular returns. -/
theorem falseWaitFirstHitBinaryBridge_zero (bits : List Bool) :
    falseWaitReturn 0 *
        wordProduct falseWaitReturn
          ([13] ++
            (falseWaitFirstHitBinaryEncoding bits ++ falseWaitNonacceptingMergeShort)) *
      falseWaitReturn 0 = 0 := by
  rw [falseWaitReturn_zero_eq_outer, outer_mul, outer_mul_outer]
  have scalar_zero :
      (falseWaitSeparatorRow ᵥ*
          wordProduct falseWaitReturn
            ([13] ++
              (falseWaitFirstHitBinaryEncoding bits ++ falseWaitNonacceptingMergeShort))) ⬝ᵥ
        falseWaitSeparatorColumn = 0 := by
    rw [← Matrix.dotProduct_mulVec, falseWaitFirstHitBinaryBridge_source]
    simp [falseWaitSeparatorRow, dotProduct]
  rw [scalar_zero, zero_smul]

/-- A word has no accepting state at any suffix encountered from a chosen source. -/
def falseWaitNoAcceptingSuffixFrom
    (word : List Nat) (source : Fin 2 → ℚ) : Prop :=
  ∀ suffix ∈ word.tails,
    falseWaitSeparatorRow ⬝ᵥ
      (wordProduct falseWaitReturn suffix *ᵥ source) ≠ 0

/-- Both binary loop blocks avoid the accepting ray at every internal step. -/
theorem falseWaitFirstHitBinaryLoop_noAcceptingSuffix (bit : Bool) :
    falseWaitNoAcceptingSuffixFrom (falseWaitFirstHitBinaryLoop bit) ![4, 3] := by
  cases bit <;>
    intro suffix membership <;>
    simp only [falseWaitFirstHitBinaryLoop, List.tails, List.mem_cons,
      List.not_mem_nil, or_false] at membership <;>
    rcases membership with rfl | rfl | rfl | rfl | rfl <;>
      norm_num [falseWaitSeparatorRow, wordProduct_cons, wordProduct_nil,
        falseWaitReturn_eq_state, falseWaitReturnOfState, cubicDefectState,
        CubicDefectState.next, Matrix.mul_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ]

/-- The fixed right suffix avoids the accepting ray from the separator source. -/
theorem falseWaitNonacceptingMergeShort_noAcceptingSuffix :
    falseWaitNoAcceptingSuffixFrom falseWaitNonacceptingMergeShort
      falseWaitSeparatorColumn := by
  intro suffix membership
  simp only [falseWaitNonacceptingMergeShort, List.tails, List.mem_cons,
    List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [falseWaitSeparatorRow, falseWaitSeparatorColumn, wordProduct_cons,
      wordProduct_nil, falseWaitReturn_eq_state, falseWaitReturnOfState,
      cubicDefectState, CubicDefectState.next, Matrix.mul_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]

/-- Safe suffix paths compose when the right word reaches the left word's source ray
nontrivially. -/
theorem falseWaitNoAcceptingSuffixFrom_append
    (left right : List Nat) (source ray : Fin 2 → ℚ) (scale : ℚ)
    (left_safe : falseWaitNoAcceptingSuffixFrom left ray)
    (right_safe : falseWaitNoAcceptingSuffixFrom right source)
    (right_source :
      wordProduct falseWaitReturn right *ᵥ source = scale • ray)
    (scale_ne_zero : scale ≠ 0) :
    falseWaitNoAcceptingSuffixFrom (left ++ right) source := by
  intro suffix membership
  rw [List.tails_append] at membership
  rcases List.mem_append.mp membership with left_membership | right_membership
  · obtain ⟨left_suffix, left_suffix_mem, rfl⟩ :=
      List.mem_map.mp left_membership
    rw [wordProduct_append, ← Matrix.mulVec_mulVec, right_source,
      Matrix.mulVec_smul, dotProduct_smul]
    simpa only [smul_eq_mul] using
      mul_ne_zero scale_ne_zero (left_safe left_suffix left_suffix_mem)
  · exact right_safe suffix (List.mem_of_mem_tail right_membership)

/-- Every binary loop spelling followed by the fixed suffix is a safe nonaccepting path. -/
theorem falseWaitFirstHitBinaryEncoding_suffix_noAccepting (bits : List Bool) :
    falseWaitNoAcceptingSuffixFrom
      (falseWaitFirstHitBinaryEncoding bits ++ falseWaitNonacceptingMergeShort)
      falseWaitSeparatorColumn := by
  induction bits with
  | nil => simpa [falseWaitFirstHitBinaryEncoding] using
      falseWaitNonacceptingMergeShort_noAcceptingSuffix
  | cons bit bits induction =>
      have right_source := falseWaitFirstHitBinaryEncoding_suffix_source bits
      have right_scale_ne :
          (-72590904000000 *
              (bits.map falseWaitFirstHitBinaryScale).prod : ℚ) ≠ 0 :=
        mul_ne_zero (by norm_num)
          (falseWaitFirstHitBinaryEncoding_scale_ne_zero bits)
      simpa [falseWaitFirstHitBinaryEncoding, List.flatMap_cons,
        List.append_assoc] using
          falseWaitNoAcceptingSuffixFrom_append
            (falseWaitFirstHitBinaryLoop bit)
            (falseWaitFirstHitBinaryEncoding bits ++ falseWaitNonacceptingMergeShort)
            falseWaitSeparatorColumn ![4, 3]
            (-72590904000000 *
              (bits.map falseWaitFirstHitBinaryScale).prod)
            (falseWaitFirstHitBinaryLoop_noAcceptingSuffix bit) induction
            right_source right_scale_ne

/-- The first-hit binary bridge word selected by a bit string. -/
def falseWaitFirstHitBinaryBridgeWord (bits : List Bool) : List Nat :=
  [13] ++
    (falseWaitFirstHitBinaryEncoding bits ++ falseWaitNonacceptingMergeShort)

/-- The direct word constructor has the explicit accepting-ray source formula. -/
theorem falseWaitFirstHitBinaryBridgeWord_source (bits : List Bool) :
    wordProduct falseWaitReturn (falseWaitFirstHitBinaryBridgeWord bits) *ᵥ
        falseWaitSeparatorColumn =
      (29617088832000000 *
          (bits.map falseWaitFirstHitBinaryScale).prod : ℚ) • ![1, 0] := by
  simpa [falseWaitFirstHitBinaryBridgeWord] using
    falseWaitFirstHitBinaryBridge_source bits

/-- The accepting scale of every binary bridge word is nonzero. -/
theorem falseWaitFirstHitBinaryBridgeWord_sourceScale_ne_zero (bits : List Bool) :
    (29617088832000000 *
        (bits.map falseWaitFirstHitBinaryScale).prod : ℚ) ≠ 0 :=
  mul_ne_zero (by norm_num)
    (falseWaitFirstHitBinaryEncoding_scale_ne_zero bits)

/-- The direct word constructor gives a zero between singular returns. -/
theorem falseWaitFirstHitBinaryBridgeWord_zero (bits : List Bool) :
    falseWaitReturn 0 *
        wordProduct falseWaitReturn (falseWaitFirstHitBinaryBridgeWord bits) *
      falseWaitReturn 0 = 0 := by
  simpa [falseWaitFirstHitBinaryBridgeWord] using
    falseWaitFirstHitBinaryBridge_zero bits

/-- Every proper suffix of a binary bridge word remains nonaccepting. -/
theorem falseWaitFirstHitBinaryBridgeWord_noAcceptingProperSuffix (bits : List Bool) :
    ∀ suffix ∈ (falseWaitFirstHitBinaryBridgeWord bits).tails.tail,
      falseWaitSeparatorRow ⬝ᵥ
        (wordProduct falseWaitReturn suffix *ᵥ falseWaitSeparatorColumn) ≠ 0 := by
  intro suffix membership
  have body_membership :
      suffix ∈
        (falseWaitFirstHitBinaryEncoding bits ++ falseWaitNonacceptingMergeShort).tails := by
    simpa [falseWaitFirstHitBinaryBridgeWord] using membership
  exact falseWaitFirstHitBinaryEncoding_suffix_noAccepting bits suffix body_membership

/-- Each binary loop block has exactly four positive waits. -/
theorem falseWaitFirstHitBinaryLoop_length (bit : Bool) :
    (falseWaitFirstHitBinaryLoop bit).length = 4 := by
  cases bit <;> rfl

/-- Binary loop encoding has constant rate four. -/
theorem falseWaitFirstHitBinaryEncoding_length (bits : List Bool) :
    (falseWaitFirstHitBinaryEncoding bits).length = 4 * bits.length := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      simp only [falseWaitFirstHitBinaryEncoding] at induction ⊢
      rw [List.flatMap_cons, List.length_append,
        falseWaitFirstHitBinaryLoop_length, induction, List.length_cons]
      omega

/-- The two fixed-length loop codewords give a literally injective binary spelling. -/
theorem falseWaitFirstHitBinaryEncoding_injective :
    Function.Injective falseWaitFirstHitBinaryEncoding := by
  intro left right encoding_eq
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons bit bits =>
          cases bit <;>
            simp [falseWaitFirstHitBinaryEncoding, falseWaitFirstHitBinaryLoop] at encoding_eq
  | cons left_bit left_bits induction =>
      cases right with
      | nil =>
          cases left_bit <;>
            simp [falseWaitFirstHitBinaryEncoding, falseWaitFirstHitBinaryLoop] at encoding_eq
      | cons right_bit right_bits =>
          cases left_bit <;> cases right_bit
          · have tail_eq :
                falseWaitFirstHitBinaryEncoding left_bits =
                  falseWaitFirstHitBinaryEncoding right_bits := by
              simpa [falseWaitFirstHitBinaryEncoding,
                falseWaitFirstHitBinaryLoop] using encoding_eq
            exact congrArg (List.cons false) (induction tail_eq)
          · simp [falseWaitFirstHitBinaryEncoding,
              falseWaitFirstHitBinaryLoop] at encoding_eq
          · simp [falseWaitFirstHitBinaryEncoding,
              falseWaitFirstHitBinaryLoop] at encoding_eq
          · have tail_eq :
                falseWaitFirstHitBinaryEncoding left_bits =
                  falseWaitFirstHitBinaryEncoding right_bits := by
              simpa [falseWaitFirstHitBinaryEncoding,
                falseWaitFirstHitBinaryLoop] using encoding_eq
            exact congrArg (List.cons true) (induction tail_eq)

/-- First-hit binary bridge words have length `7 + 4n`. -/
theorem falseWaitFirstHitBinaryBridgeWord_length (bits : List Bool) :
    (falseWaitFirstHitBinaryBridgeWord bits).length = 7 + 4 * bits.length := by
  rw [falseWaitFirstHitBinaryBridgeWord, List.length_append, List.length_singleton,
    List.length_append, falseWaitFirstHitBinaryEncoding_length]
  norm_num [falseWaitNonacceptingMergeShort]
  omega

/-- Every letter of a first-hit binary bridge is a strictly positive wait. -/
theorem falseWaitFirstHitBinaryBridgeWord_positive (bits : List Bool) :
    ∀ wait ∈ falseWaitFirstHitBinaryBridgeWord bits, 0 < wait := by
  intro wait membership
  simp only [falseWaitFirstHitBinaryBridgeWord, List.mem_append,
    List.mem_singleton] at membership
  rcases membership with rfl | encoded_or_suffix
  · norm_num
  · rcases encoded_or_suffix with encoded | suffix
    · exact falseWaitFirstHitBinaryEncoding_positive bits wait encoded
    · simp [falseWaitNonacceptingMergeShort] at suffix
      omega

/-- Distinct binary strings give distinct literal first-hit bridge words. -/
theorem falseWaitFirstHitBinaryBridgeWord_injective :
    Function.Injective falseWaitFirstHitBinaryBridgeWord := by
  intro left right bridge_eq
  have body_eq :
      falseWaitFirstHitBinaryEncoding left ++ falseWaitNonacceptingMergeShort =
        falseWaitFirstHitBinaryEncoding right ++ falseWaitNonacceptingMergeShort := by
    simpa [falseWaitFirstHitBinaryBridgeWord] using bridge_eq
  have encoding_eq :
      falseWaitFirstHitBinaryEncoding left = falseWaitFirstHitBinaryEncoding right :=
    List.append_cancel_right body_eq
  exact falseWaitFirstHitBinaryEncoding_injective encoding_eq

/-- Fixed-width bit vectors index the corresponding equal-length binary bridge words. -/
def falseWaitFirstHitBinaryBridgeOfVector {width : Nat}
    (bits : Fin width → Bool) : List Nat :=
  falseWaitFirstHitBinaryBridgeWord (List.ofFn bits)

/-- Fixed-width binary bridge indexing is injective. -/
theorem falseWaitFirstHitBinaryBridgeOfVector_injective (width : Nat) :
    Function.Injective
      (falseWaitFirstHitBinaryBridgeOfVector (width := width)) :=
  falseWaitFirstHitBinaryBridgeWord_injective.comp List.ofFn_injective

/-- Every width-`n` binary bridge has the common length `7 + 4n`. -/
theorem falseWaitFirstHitBinaryBridgeOfVector_length
    {width : Nat} (bits : Fin width → Bool) :
    (falseWaitFirstHitBinaryBridgeOfVector bits).length = 7 + 4 * width := by
  rw [falseWaitFirstHitBinaryBridgeOfVector,
    falseWaitFirstHitBinaryBridgeWord_length, List.length_ofFn]

/-- Every fixed-width bridge vector reaches the accepting ray with its exact nonzero scale. -/
theorem falseWaitFirstHitBinaryBridgeOfVector_source
    {width : Nat} (bits : Fin width → Bool) :
    wordProduct falseWaitReturn (falseWaitFirstHitBinaryBridgeOfVector bits) *ᵥ
        falseWaitSeparatorColumn =
      (29617088832000000 *
          ((List.ofFn bits).map falseWaitFirstHitBinaryScale).prod : ℚ) • ![1, 0] := by
  simpa [falseWaitFirstHitBinaryBridgeOfVector] using
    falseWaitFirstHitBinaryBridgeWord_source (List.ofFn bits)

/-- Any two fixed-width bridge vectors collide projectively on the accepting source image. -/
theorem falseWaitFirstHitBinaryBridgeOfVector_projective_collision
    {width : Nat} (left right : Fin width → Bool) :
    ∃ scale : ℚ, scale ≠ 0 ∧
      wordProduct falseWaitReturn (falseWaitFirstHitBinaryBridgeOfVector left) *ᵥ
          falseWaitSeparatorColumn =
        scale •
          (wordProduct falseWaitReturn (falseWaitFirstHitBinaryBridgeOfVector right) *ᵥ
            falseWaitSeparatorColumn) := by
  let left_scale : ℚ :=
    29617088832000000 *
      ((List.ofFn left).map falseWaitFirstHitBinaryScale).prod
  let right_scale : ℚ :=
    29617088832000000 *
      ((List.ofFn right).map falseWaitFirstHitBinaryScale).prod
  have left_ne : left_scale ≠ 0 := by
    exact mul_ne_zero (by norm_num)
      (falseWaitFirstHitBinaryEncoding_scale_ne_zero (List.ofFn left))
  have right_ne : right_scale ≠ 0 := by
    exact mul_ne_zero (by norm_num)
      (falseWaitFirstHitBinaryEncoding_scale_ne_zero (List.ofFn right))
  refine ⟨left_scale / right_scale, div_ne_zero left_ne right_ne, ?_⟩
  rw [falseWaitFirstHitBinaryBridgeOfVector_source,
    falseWaitFirstHitBinaryBridgeOfVector_source, smul_smul]
  change left_scale • ![1, 0] =
    (left_scale / right_scale * right_scale) • ![1, 0]
  rw [div_mul_cancel₀ left_scale right_ne]

/-- The finite family of width-`n` first-hit binary bridge words. -/
def falseWaitFirstHitBinaryBridgeFamily (width : Nat) : Finset (List Nat) :=
  Finset.univ.image (falseWaitFirstHitBinaryBridgeOfVector (width := width))

/-- Width `n` supplies exactly `2^n` distinct equal-length bridge words. -/
theorem falseWaitFirstHitBinaryBridgeFamily_card (width : Nat) :
    (falseWaitFirstHitBinaryBridgeFamily width).card = 2 ^ width := by
  rw [falseWaitFirstHitBinaryBridgeFamily,
    Finset.card_image_of_injective _
      (falseWaitFirstHitBinaryBridgeOfVector_injective width)]
  simp

end MatrixMortality.CubicReturn.NonPure
