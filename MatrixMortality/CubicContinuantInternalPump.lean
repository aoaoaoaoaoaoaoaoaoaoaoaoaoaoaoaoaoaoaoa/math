import MatrixMortality.CubicContinuantEndpoint

/-!
# Internal ray pumps in the fixed cubic continuant family

Two non-scalar positive loops stabilize internal source rays of the two shortest bridge cores.
Arbitrary repetition therefore gives two injective infinite families of exact bridge words. One
loop also yields a projective merge whose entire source-reading suffix path stays nonaccepting,
so even first-hit-safe source prefixes are not freely decodable modulo scalar identities alone.
-/

namespace MatrixMortality.CubicReturn.NonPure

open scoped Matrix

/-- A positive return block preserving an internal projective ray of a bridge core. -/
def falseWaitInternalPumpLoop : Fin 2 → List Nat :=
  ![[1, 15, 2], [8, 33, 12]]

/-- The internal ray preserved by each pump loop. -/
def falseWaitInternalPumpRay : Fin 2 → Fin 2 → ℚ :=
  ![![4, 3], ![1, 4]]

/-- Projective scale of each pump loop on its internal ray. -/
def falseWaitInternalPumpScale : Fin 2 → ℚ :=
  ![7776000, -32348160]

/-- Leftmost positive wait sending the internal ray to the accepting ray. -/
def falseWaitInternalPumpPrefix : Fin 2 → Nat :=
  ![13, 12]

/-- Right-hand word sending the separator source to the internal ray. -/
def falseWaitInternalPumpSuffix : Fin 2 → List Nat :=
  ![[15, 29, 11, 13, 7, 8], [12, 8, 12, 12, 15, 8]]

/-- Scale with which the right-hand word reaches the internal ray. -/
def falseWaitInternalPumpSuffixScale : Fin 2 → ℚ :=
  ![-72590904000000, 41923215360000]

/-- Scale with which the prefix sends the internal ray to the accepting ray. -/
def falseWaitInternalPumpPrefixScale : Fin 2 → ℚ :=
  ![-408, 312]

/-- Repeat one fixed positive wait block. -/
def falseWaitInternalPumpRepeat (block : List Nat) : Nat → List Nat
  | 0 => []
  | repetitions + 1 => block ++ falseWaitInternalPumpRepeat block repetitions

/-- A bridge core with an arbitrary number of nonterminal ray loops inserted. -/
def falseWaitInternalPumpWord (index : Fin 2) (repetitions : Nat) : List Nat :=
  [falseWaitInternalPumpPrefix index] ++
    (falseWaitInternalPumpRepeat (falseWaitInternalPumpLoop index) repetitions ++
      falseWaitInternalPumpSuffix index)

/-- Repeating a fixed block multiplies its length by the repetition count. -/
theorem falseWaitInternalPumpRepeat_length (block : List Nat) (repetitions : Nat) :
    (falseWaitInternalPumpRepeat block repetitions).length =
      repetitions * block.length := by
  induction repetitions with
  | zero => simp [falseWaitInternalPumpRepeat]
  | succ repetitions induction =>
      rw [falseWaitInternalPumpRepeat, List.length_append, induction]
      simp [Nat.succ_mul, Nat.add_comm]

/-- Both pumped families have exact length `7 + 3k`. -/
theorem falseWaitInternalPumpWord_length (index : Fin 2) (repetitions : Nat) :
    (falseWaitInternalPumpWord index repetitions).length = 7 + 3 * repetitions := by
  fin_cases index <;>
    simp [falseWaitInternalPumpWord, falseWaitInternalPumpPrefix,
      falseWaitInternalPumpLoop, falseWaitInternalPumpSuffix,
      falseWaitInternalPumpRepeat_length] <;>
    omega

/-- Distinct repetition counts give distinct literal bridge words. -/
theorem falseWaitInternalPumpWord_injective (index : Fin 2) :
    Function.Injective (falseWaitInternalPumpWord index) := by
  intro first second words_equal
  have lengths_equal := congrArg List.length words_equal
  rw [falseWaitInternalPumpWord_length, falseWaitInternalPumpWord_length] at lengths_equal
  omega

private theorem falseWaitInternalPumpLoop_positive (index : Fin 2) :
    ∀ wait ∈ falseWaitInternalPumpLoop index, 0 < wait := by
  fin_cases index <;> simp [falseWaitInternalPumpLoop]

private theorem falseWaitInternalPumpSuffix_positive (index : Fin 2) :
    ∀ wait ∈ falseWaitInternalPumpSuffix index, 0 < wait := by
  fin_cases index <;> simp [falseWaitInternalPumpSuffix]

private theorem falseWaitInternalPumpRepeat_positive
    {block : List Nat} (positive : ∀ wait ∈ block, 0 < wait) (repetitions : Nat) :
    ∀ wait ∈ falseWaitInternalPumpRepeat block repetitions, 0 < wait := by
  intro wait membership
  induction repetitions with
  | zero => simp [falseWaitInternalPumpRepeat] at membership
  | succ repetitions induction =>
      rw [falseWaitInternalPumpRepeat, List.mem_append] at membership
      rcases membership with block_membership | repeated_membership
      · exact positive wait block_membership
      · exact induction repeated_membership

/-- Every wait in every pumped bridge word is strictly positive. -/
theorem falseWaitInternalPumpWord_positive (index : Fin 2) (repetitions : Nat) :
    ∀ wait ∈ falseWaitInternalPumpWord index repetitions, 0 < wait := by
  intro wait membership
  simp only [falseWaitInternalPumpWord, List.mem_append, List.mem_singleton] at membership
  rcases membership with prefix_membership | remainder_membership
  · have prefix_positive : 0 < falseWaitInternalPumpPrefix index := by
      fin_cases index <;> norm_num [falseWaitInternalPumpPrefix]
    simpa [prefix_membership] using prefix_positive
  · rcases remainder_membership with repeated_membership | suffix_membership
    · exact falseWaitInternalPumpRepeat_positive
        (falseWaitInternalPumpLoop_positive index) repetitions wait repeated_membership
    · exact falseWaitInternalPumpSuffix_positive index wait suffix_membership

/-- Each displayed pump loop preserves its displayed internal ray exactly up to scale. -/
theorem falseWaitInternalPumpLoop_ray (index : Fin 2) :
    wordProduct falseWaitReturn (falseWaitInternalPumpLoop index) *ᵥ
        falseWaitInternalPumpRay index =
      falseWaitInternalPumpScale index • falseWaitInternalPumpRay index := by
  fin_cases index <;>
    ext coordinate <;>
    fin_cases coordinate <;>
      norm_num [falseWaitInternalPumpLoop, falseWaitInternalPumpRay,
        falseWaitInternalPumpScale, wordProduct_cons, wordProduct_nil,
        falseWaitReturn_eq_state, falseWaitReturnOfState, cubicDefectState,
        CubicDefectState.next, Matrix.mul_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ]

/-- The right-hand contexts land exactly on the two internal pump rays. -/
theorem falseWaitInternalPumpSuffix_source (index : Fin 2) :
    wordProduct falseWaitReturn (falseWaitInternalPumpSuffix index) *ᵥ
        falseWaitSeparatorColumn =
      falseWaitInternalPumpSuffixScale index • falseWaitInternalPumpRay index := by
  fin_cases index <;>
    ext coordinate <;>
    fin_cases coordinate <;>
      norm_num [falseWaitInternalPumpSuffix, falseWaitInternalPumpSuffixScale,
        falseWaitInternalPumpRay, falseWaitSeparatorColumn, wordProduct_cons,
        wordProduct_nil, falseWaitReturn_eq_state, falseWaitReturnOfState,
        cubicDefectState, CubicDefectState.next, Matrix.mul_apply, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ]

/-- Each left prefix sends its internal pump ray to the bridge's accepting ray. -/
theorem falseWaitInternalPumpPrefix_ray (index : Fin 2) :
    falseWaitReturn (falseWaitInternalPumpPrefix index) *ᵥ
        falseWaitInternalPumpRay index =
      falseWaitInternalPumpPrefixScale index • ![1, 0] := by
  fin_cases index <;>
    ext coordinate <;>
    fin_cases coordinate <;>
      norm_num [falseWaitInternalPumpPrefix, falseWaitInternalPumpRay,
        falseWaitInternalPumpPrefixScale, falseWaitReturn_eq_state,
        falseWaitReturnOfState, cubicDefectState, CubicDefectState.next,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Neither internal pump is a scalar identity; both have a nonzero upper-right entry. -/
theorem falseWaitInternalPumpLoop_not_projectiveIdentity (index : Fin 2)
    (scale : ℚ) :
    wordProduct falseWaitReturn (falseWaitInternalPumpLoop index) ≠
      scale • (1 : Square (Fin 2) ℚ) := by
  intro identity
  have upper_right := congrFun (congrFun identity 0) 1
  fin_cases index <;>
    norm_num [falseWaitInternalPumpLoop, wordProduct_cons, wordProduct_nil,
      falseWaitReturn_eq_state, falseWaitReturnOfState, cubicDefectState,
      CubicDefectState.next, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_succ] at upper_right

/-- Repeating a pump block raises its projective action scale to the repetition count. -/
theorem falseWaitInternalPumpRepeat_ray (index : Fin 2) (repetitions : Nat) :
    wordProduct falseWaitReturn
          (falseWaitInternalPumpRepeat (falseWaitInternalPumpLoop index) repetitions) *ᵥ
        falseWaitInternalPumpRay index =
      falseWaitInternalPumpScale index ^ repetitions •
        falseWaitInternalPumpRay index := by
  induction repetitions with
  | zero => simp [falseWaitInternalPumpRepeat]
  | succ repetitions induction =>
      rw [falseWaitInternalPumpRepeat, wordProduct_append,
        ← Matrix.mulVec_mulVec, induction, Matrix.mulVec_smul,
        falseWaitInternalPumpLoop_ray, smul_smul, pow_succ]

/-- Every pumped word sends the separator source to the accepting ray with explicit scale. -/
theorem falseWaitInternalPumpWord_source (index : Fin 2) (repetitions : Nat) :
    wordProduct falseWaitReturn (falseWaitInternalPumpWord index repetitions) *ᵥ
        falseWaitSeparatorColumn =
      (falseWaitInternalPumpSuffixScale index *
          falseWaitInternalPumpScale index ^ repetitions *
        falseWaitInternalPumpPrefixScale index) • ![1, 0] := by
  calc
    wordProduct falseWaitReturn (falseWaitInternalPumpWord index repetitions) *ᵥ
          falseWaitSeparatorColumn =
        falseWaitReturn (falseWaitInternalPumpPrefix index) *ᵥ
          (wordProduct falseWaitReturn
              (falseWaitInternalPumpRepeat
                (falseWaitInternalPumpLoop index) repetitions) *ᵥ
            (wordProduct falseWaitReturn (falseWaitInternalPumpSuffix index) *ᵥ
              falseWaitSeparatorColumn)) := by
          simp [falseWaitInternalPumpWord, wordProduct_append,
            ← Matrix.mulVec_mulVec]
    _ = falseWaitReturn (falseWaitInternalPumpPrefix index) *ᵥ
          (wordProduct falseWaitReturn
              (falseWaitInternalPumpRepeat
                (falseWaitInternalPumpLoop index) repetitions) *ᵥ
            (falseWaitInternalPumpSuffixScale index •
              falseWaitInternalPumpRay index)) := by
          rw [falseWaitInternalPumpSuffix_source]
    _ = falseWaitInternalPumpSuffixScale index •
          (falseWaitReturn (falseWaitInternalPumpPrefix index) *ᵥ
            (wordProduct falseWaitReturn
                (falseWaitInternalPumpRepeat
                  (falseWaitInternalPumpLoop index) repetitions) *ᵥ
              falseWaitInternalPumpRay index)) := by
          rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
    _ = falseWaitInternalPumpSuffixScale index •
          (falseWaitReturn (falseWaitInternalPumpPrefix index) *ᵥ
            (falseWaitInternalPumpScale index ^ repetitions •
              falseWaitInternalPumpRay index)) := by
          rw [falseWaitInternalPumpRepeat_ray]
    _ = (falseWaitInternalPumpSuffixScale index *
            falseWaitInternalPumpScale index ^ repetitions) •
          (falseWaitReturn (falseWaitInternalPumpPrefix index) *ᵥ
            falseWaitInternalPumpRay index) := by
          rw [Matrix.mulVec_smul, smul_smul]
    _ = (falseWaitInternalPumpSuffixScale index *
            falseWaitInternalPumpScale index ^ repetitions) •
          (falseWaitInternalPumpPrefixScale index • ![1, 0]) := by
          rw [falseWaitInternalPumpPrefix_ray]
    _ = (falseWaitInternalPumpSuffixScale index *
            falseWaitInternalPumpScale index ^ repetitions *
          falseWaitInternalPumpPrefixScale index) • ![1, 0] := by
          rw [smul_smul]

/-- The two pumped source-image formulas have the closed scales inherited from their base
length-seven cores. -/
theorem falseWaitInternalPumpWord_source_closed (repetitions : Nat) :
    wordProduct falseWaitReturn (falseWaitInternalPumpWord 0 repetitions) *ᵥ
        falseWaitSeparatorColumn =
          (29617088832000000 * 7776000 ^ repetitions : ℚ) • ![1, 0] ∧
      wordProduct falseWaitReturn (falseWaitInternalPumpWord 1 repetitions) *ᵥ
        falseWaitSeparatorColumn =
          (13080043192320000 * (-32348160) ^ repetitions : ℚ) • ![1, 0] := by
  constructor <;>
    rw [falseWaitInternalPumpWord_source] <;>
    norm_num [falseWaitInternalPumpSuffixScale, falseWaitInternalPumpScale,
      falseWaitInternalPumpPrefixScale] <;>
    ring

/-- The accepting scale of every pumped word is nonzero. -/
theorem falseWaitInternalPumpWord_sourceScale_ne_zero
    (index : Fin 2) (repetitions : Nat) :
    falseWaitInternalPumpSuffixScale index *
          falseWaitInternalPumpScale index ^ repetitions *
        falseWaitInternalPumpPrefixScale index ≠ 0 := by
  fin_cases index <;>
    norm_num [falseWaitInternalPumpSuffixScale, falseWaitInternalPumpScale,
      falseWaitInternalPumpPrefixScale, pow_ne_zero]

/-- Every repetition count gives an exact scalar bridge zero. -/
theorem falseWaitInternalPumpWord_scalar_zero (index : Fin 2) (repetitions : Nat) :
    (falseWaitSeparatorRow ᵥ*
        wordProduct falseWaitReturn (falseWaitInternalPumpWord index repetitions)) ⬝ᵥ
      falseWaitSeparatorColumn = 0 := by
  rw [← Matrix.dotProduct_mulVec, falseWaitInternalPumpWord_source]
  simp [falseWaitSeparatorRow, dotProduct]

/-- Every repetition count gives a mortality witness between two wait-zero separators. -/
theorem falseWaitInternalPumpWord_zero (index : Fin 2) (repetitions : Nat) :
    falseWaitReturn 0 *
        wordProduct falseWaitReturn (falseWaitInternalPumpWord index repetitions) *
      falseWaitReturn 0 = 0 := by
  rw [falseWaitReturn_zero_eq_outer, outer_mul, outer_mul_outer,
    falseWaitInternalPumpWord_scalar_zero, zero_smul]

/-- The shorter representative of a nonaccepting source-orbit merge. -/
def falseWaitNonacceptingMergeShort : List Nat :=
  [15, 29, 11, 13, 7, 8]

/-- Inserting the non-scalar internal loop produces the longer merge representative. -/
def falseWaitNonacceptingMergeLong : List Nat :=
  [1, 15, 2, 15, 29, 11, 13, 7, 8]

/-- The non-scalar loop gives an exact nonaccepting projective merge on the source orbit. -/
theorem falseWaitNonacceptingMerge_source :
    wordProduct falseWaitReturn falseWaitNonacceptingMergeLong *ᵥ
        falseWaitSeparatorColumn =
      (7776000 : ℚ) •
        (wordProduct falseWaitReturn falseWaitNonacceptingMergeShort *ᵥ
          falseWaitSeparatorColumn) := by
  change wordProduct falseWaitReturn
        (falseWaitInternalPumpLoop 0 ++ falseWaitInternalPumpSuffix 0) *ᵥ
      falseWaitSeparatorColumn =
    falseWaitInternalPumpScale 0 •
      (wordProduct falseWaitReturn (falseWaitInternalPumpSuffix 0) *ᵥ
        falseWaitSeparatorColumn)
  rw [wordProduct_append, ← Matrix.mulVec_mulVec,
    falseWaitInternalPumpSuffix_source, Matrix.mulVec_smul,
    falseWaitInternalPumpLoop_ray, smul_smul]
  simp only [smul_smul, mul_comm]

/-- The two merge representatives are distinct literal positive-wait words. -/
theorem falseWaitNonacceptingMerge_words_ne :
    falseWaitNonacceptingMergeLong ≠ falseWaitNonacceptingMergeShort := by
  decide

/-- Both nonaccepting merge representatives contain only strictly positive waits. -/
theorem falseWaitNonacceptingMerge_positive :
    (∀ wait ∈ falseWaitNonacceptingMergeShort, 0 < wait) ∧
      ∀ wait ∈ falseWaitNonacceptingMergeLong, 0 < wait := by
  simp [falseWaitNonacceptingMergeShort, falseWaitNonacceptingMergeLong]

/-- No suffix state encountered while reading the longer word from the source is accepting. -/
theorem falseWaitNonacceptingMergeLong_no_accepting_suffix :
    ∀ suffix ∈ falseWaitNonacceptingMergeLong.tails,
      (falseWaitSeparatorRow ᵥ* wordProduct falseWaitReturn suffix) ⬝ᵥ
        falseWaitSeparatorColumn ≠ 0 := by
  intro suffix membership
  simp only [falseWaitNonacceptingMergeLong, List.tails, List.mem_cons,
    List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [falseWaitSeparatorRow, falseWaitSeparatorColumn, wordProduct_cons,
      wordProduct_nil, falseWaitReturn_eq_state, falseWaitReturnOfState,
      cubicDefectState, CubicDefectState.next, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_succ]

end MatrixMortality.CubicReturn.NonPure
