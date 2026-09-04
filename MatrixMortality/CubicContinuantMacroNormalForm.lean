import MatrixMortality.CubicContinuantSelectedComparator

/-!
# Exact normal form for the cubic reader-writer quotient

The normalized cubic radix writers and their positive physical readers generate an affine group
image. Every word segmented over these four macros has a computable normal form consisting of an
integer height and one rational shift. Equality of these two fields is equivalent to projective
equality of the physical products. Thus projective-neutral insertions have a complete effective
quotient inside the reader-writer alphabet. This does not classify words using the independent
terminal translations or transverse pump macros, nor arbitrary unsegmented positive wait words.
-/

namespace MatrixMortality.CubicReturn.NonPure

open scoped Matrix

/-- One normalized operation in the cubic radix reader-writer alphabet. -/
inductive ContinuantRadixMacro
  /-- Append one radix digit. -/
  | writer (bit : Bool)
  /-- Apply the positive physical inverse of one radix digit. -/
  | reader (bit : Bool)
  deriving DecidableEq

/-- Common projective multiplier of a normalized radix writer. -/
def continuantRadixMacroRatio : ℚ := 4 / 25

/-- Signed multiplier exponent of one reader-writer macro. -/
def continuantRadixMacroHeight : ContinuantRadixMacro → ℤ
  | .writer _ => 1
  | .reader _ => -1

/-- Affine shift of one normalized reader-writer macro. -/
def continuantRadixMacroShift : ContinuantRadixMacro → ℚ
  | .writer bit => continuantRadixDigit bit / 300
  | .reader bit => -(continuantRadixDigit bit : ℚ) / 48

/-- Exact lower-right-one affine matrix of one reader-writer macro. -/
def continuantRadixMacroMatrix
    (op : ContinuantRadixMacro) : Square (Fin 2) ℚ :=
  !![continuantRadixMacroRatio ^ continuantRadixMacroHeight op,
      continuantRadixMacroShift op;
     0, 1]

/-- Positive physical spelling of one normalized reader-writer macro. -/
def continuantRadixMacroWord : ContinuantRadixMacro → List Nat
  | .writer bit => continuantRadixWord bit
  | .reader bit => continuantRadixReaderWord bit

/-- Flatten a segmented reader-writer macro word into positive physical waits. -/
def continuantRadixMacroEncoding
    (macros : List ContinuantRadixMacro) : List Nat :=
  macros.flatMap continuantRadixMacroWord

/-- The complete computable affine normal form of a segmented macro word. -/
structure ContinuantRadixMacroNormalForm where
  /-- Total writer count minus reader count. -/
  height : ℤ
  /-- Upper affine shift after normalization to lower-right entry one. -/
  shift : ℚ
  deriving DecidableEq

/-- Two affine macro normal forms are equal when both semantic fields are equal. -/
@[ext]
theorem continuantRadixMacroNormalForm_ext
    {left right : ContinuantRadixMacroNormalForm}
    (height_eq : left.height = right.height)
    (shift_eq : left.shift = right.shift) : left = right := by
  cases left with
  | mk leftHeight leftShift =>
      cases right with
      | mk rightHeight rightShift =>
          cases height_eq
          cases shift_eq
          rfl

/-- Recursively evaluate a segmented macro word in the affine semidirect product. -/
def continuantRadixMacroNormalForm :
    List ContinuantRadixMacro → ContinuantRadixMacroNormalForm
  | [] => ⟨0, 0⟩
  | op :: ops =>
      let tail := continuantRadixMacroNormalForm ops
      ⟨continuantRadixMacroHeight op + tail.height,
        continuantRadixMacroShift op +
          continuantRadixMacroRatio ^ continuantRadixMacroHeight op * tail.shift⟩

/-- Matrix represented by one affine macro normal form. -/
def ContinuantRadixMacroNormalForm.matrix
    (normal : ContinuantRadixMacroNormalForm) : Square (Fin 2) ℚ :=
  !![continuantRadixMacroRatio ^ normal.height, normal.shift; 0, 1]

private theorem continuantRadixMacroRatio_ne_zero :
    continuantRadixMacroRatio ≠ 0 := by
  norm_num [continuantRadixMacroRatio]

/-- Multiplication of normal-form matrices is the affine semidirect-product law. -/
theorem ContinuantRadixMacroNormalForm.matrix_mul
    (left right : ContinuantRadixMacroNormalForm) :
    left.matrix * right.matrix =
      (ContinuantRadixMacroNormalForm.mk
        (left.height + right.height)
        (left.shift + continuantRadixMacroRatio ^ left.height * right.shift)).matrix := by
  ext i j
  fin_cases i
  · fin_cases j
    · simp [ContinuantRadixMacroNormalForm.matrix, Matrix.mul_apply,
        Fin.sum_univ_succ, zpow_add₀ continuantRadixMacroRatio_ne_zero]
    · simp [ContinuantRadixMacroNormalForm.matrix, Matrix.mul_apply,
        Fin.sum_univ_succ, zpow_add₀ continuantRadixMacroRatio_ne_zero]
      ring
  · fin_cases j <;>
      simp [ContinuantRadixMacroNormalForm.matrix, Matrix.mul_apply,
        Fin.sum_univ_succ, zpow_add₀ continuantRadixMacroRatio_ne_zero]

/-- The product of normalized macro matrices is exactly its computed affine normal form. -/
theorem continuantRadixMacro_product_normalForm
    (macros : List ContinuantRadixMacro) :
    wordProduct continuantRadixMacroMatrix macros =
      (continuantRadixMacroNormalForm macros).matrix := by
  induction macros with
  | nil =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [continuantRadixMacroNormalForm,
          ContinuantRadixMacroNormalForm.matrix, Matrix.one_apply]
  | cons op ops induction =>
      rw [wordProduct_cons, induction]
      have head :
          continuantRadixMacroMatrix op =
            (ContinuantRadixMacroNormalForm.mk
              (continuantRadixMacroHeight op)
              (continuantRadixMacroShift op)).matrix := rfl
      rw [head, ContinuantRadixMacroNormalForm.matrix_mul]
      rfl

/-- Each positive physical macro realizes its lower-right-one normalized affine matrix. -/
theorem continuantRadixMacroWord_projectivelyRealizes
    (op : ContinuantRadixMacro) :
    continuantProjectivelyRealizes (continuantRadixMacroWord op)
      (continuantRadixMacroMatrix op) := by
  cases op with
  | writer bit =>
      refine ⟨continuantRadixScale bit * 25, ?_, ?_⟩
      · exact mul_ne_zero (by cases bit <;> norm_num [continuantRadixScale]) (by norm_num)
      · rw [continuantRadixMacroWord, continuantRadixWord_product]
        cases bit <;>
          ext i j <;> fin_cases i <;> fin_cases j <;>
          norm_num [continuantRadixMacroMatrix, continuantRadixMacroHeight,
            continuantRadixMacroShift, continuantRadixMacroRatio,
            continuantRadixGenerator, continuantRadixDigit,
            continuantRadixScale, Matrix.smul_apply]
  | reader bit =>
      have realizes := continuantRadixReaderWord_projectivelyRealizes bit
      have matrix_eq :
          continuantRadixMacroMatrix (.reader bit) = continuantRadixReader bit := by
        cases bit <;>
          ext i j <;> fin_cases i <;> fin_cases j <;>
          norm_num [continuantRadixMacroMatrix, continuantRadixMacroHeight,
            continuantRadixMacroShift, continuantRadixMacroRatio,
            continuantRadixReader, continuantRadixDigit]
      simpa only [continuantRadixMacroWord, matrix_eq] using realizes

/-- Every physical wait in a segmented macro encoding is strictly positive. -/
theorem continuantRadixMacroEncoding_positive
    (macros : List ContinuantRadixMacro) :
    ∀ wait ∈ continuantRadixMacroEncoding macros, 0 < wait := by
  intro wait membership
  obtain ⟨op, _, wait_mem⟩ := List.mem_flatMap.mp membership
  cases op with
  | writer bit =>
      exact continuantRadixEncoding_positive [bit] wait (by
        simpa [continuantRadixMacroWord, continuantRadixEncoding] using wait_mem)
  | reader bit =>
      exact continuantRadixReaderWord_positive bit wait wait_mem

/-- Every flattened positive physical macro word realizes its complete normalized product. -/
theorem continuantRadixMacroEncoding_projectivelyRealizes
    (macros : List ContinuantRadixMacro) :
    continuantProjectivelyRealizes (continuantRadixMacroEncoding macros)
      (wordProduct continuantRadixMacroMatrix macros) := by
  induction macros with
  | nil =>
      refine ⟨1, one_ne_zero, ?_⟩
      simp [continuantRadixMacroEncoding]
  | cons op ops induction =>
      rw [continuantRadixMacroEncoding, List.flatMap_cons]
      exact continuantProjectivelyRealizes_append
        (continuantRadixMacroWord_projectivelyRealizes op) induction

/-- Two normalized macro products are projectively equal exactly when their affine normal forms
are equal. -/
theorem continuantRadixMacro_product_projectively_eq_iff
    (left right : List ContinuantRadixMacro) :
    (∃ scale : ℚ, scale ≠ 0 ∧
      wordProduct continuantRadixMacroMatrix left =
        scale • wordProduct continuantRadixMacroMatrix right) ↔
      continuantRadixMacroNormalForm left = continuantRadixMacroNormalForm right := by
  rw [continuantRadixMacro_product_normalForm,
    continuantRadixMacro_product_normalForm]
  constructor
  · rintro ⟨scale, _, projective_eq⟩
    have lower_eq := congrFun (congrFun projective_eq 1) 1
    have upper_eq := congrFun (congrFun projective_eq 0) 0
    have shift_eq := congrFun (congrFun projective_eq 0) 1
    simp only [ContinuantRadixMacroNormalForm.matrix, Matrix.smul_apply,
      smul_eq_mul] at lower_eq upper_eq shift_eq
    have scale_eq : scale = 1 := by simpa using lower_eq.symm
    rw [scale_eq, one_mul] at upper_eq shift_eq
    have height_eq :
        (continuantRadixMacroNormalForm left).height =
          (continuantRadixMacroNormalForm right).height :=
      (zpow_right_injective₀
        (by norm_num [continuantRadixMacroRatio])
        (by norm_num [continuantRadixMacroRatio])) upper_eq
    exact continuantRadixMacroNormalForm_ext height_eq shift_eq
  · intro normal_eq
    refine ⟨1, one_ne_zero, ?_⟩
    rw [normal_eq]
    simp

/-- Projective equality of the positive physical encodings is decided exactly by equality of
their affine normal forms. -/
theorem continuantRadixMacroEncoding_projectively_eq_iff
    (left right : List ContinuantRadixMacro) :
    (∃ scale : ℚ, scale ≠ 0 ∧
      wordProduct falseWaitReturn (continuantRadixMacroEncoding left) =
        scale • wordProduct falseWaitReturn (continuantRadixMacroEncoding right)) ↔
      continuantRadixMacroNormalForm left = continuantRadixMacroNormalForm right := by
  rcases continuantRadixMacroEncoding_projectivelyRealizes left with
    ⟨leftScale, leftScale_ne, leftProduct⟩
  rcases continuantRadixMacroEncoding_projectivelyRealizes right with
    ⟨rightScale, rightScale_ne, rightProduct⟩
  constructor
  · rintro ⟨scale, scale_ne, projective_eq⟩
    have normalized_eq :
        wordProduct continuantRadixMacroMatrix left =
          (scale * rightScale / leftScale) •
            wordProduct continuantRadixMacroMatrix right := by
      ext i j
      have entry_eq := congrFun (congrFun projective_eq i) j
      rw [leftProduct, rightProduct] at entry_eq
      simp only [Matrix.smul_apply, smul_eq_mul] at entry_eq ⊢
      calc
        wordProduct continuantRadixMacroMatrix left i j =
            leftScale⁻¹ *
              (leftScale * wordProduct continuantRadixMacroMatrix left i j) := by
                field_simp
        _ = leftScale⁻¹ *
            (scale *
              (rightScale * wordProduct continuantRadixMacroMatrix right i j)) := by
                rw [entry_eq]
        _ = scale * rightScale / leftScale *
            wordProduct continuantRadixMacroMatrix right i j := by ring
    exact (continuantRadixMacro_product_projectively_eq_iff left right).mp
      ⟨scale * rightScale / leftScale,
        div_ne_zero (mul_ne_zero scale_ne rightScale_ne) leftScale_ne,
        normalized_eq⟩
  · intro normal_eq
    have normalized_eq :
        wordProduct continuantRadixMacroMatrix left =
          wordProduct continuantRadixMacroMatrix right := by
      rw [continuantRadixMacro_product_normalForm,
        continuantRadixMacro_product_normalForm, normal_eq]
    refine ⟨leftScale / rightScale,
      div_ne_zero leftScale_ne rightScale_ne, ?_⟩
    rw [leftProduct, rightProduct, normalized_eq]
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    field_simp

/-- A segmented macro word is projectively neutral exactly when its height and shift both
vanish. -/
theorem continuantRadixMacroEncoding_projectiveIdentity_iff
    (macros : List ContinuantRadixMacro) :
    (∃ scale : ℚ, scale ≠ 0 ∧
      wordProduct falseWaitReturn (continuantRadixMacroEncoding macros) =
        scale • (1 : Square (Fin 2) ℚ)) ↔
      (continuantRadixMacroNormalForm macros).height = 0 ∧
        (continuantRadixMacroNormalForm macros).shift = 0 := by
  have relation := continuantRadixMacroEncoding_projectively_eq_iff macros []
  have empty_normal :
      continuantRadixMacroNormalForm ([] : List ContinuantRadixMacro) = ⟨0, 0⟩ := rfl
  constructor
  · intro identity
    have normal_eq :
        continuantRadixMacroNormalForm macros =
          continuantRadixMacroNormalForm ([] : List ContinuantRadixMacro) := by
      apply relation.mp
      simpa [continuantRadixMacroEncoding] using identity
    rw [empty_normal] at normal_eq
    exact ⟨congrArg ContinuantRadixMacroNormalForm.height normal_eq,
      congrArg ContinuantRadixMacroNormalForm.shift normal_eq⟩
  · rintro ⟨height_zero, shift_zero⟩
    have normal_eq :
        continuantRadixMacroNormalForm macros =
          continuantRadixMacroNormalForm ([] : List ContinuantRadixMacro) := by
      rw [empty_normal]
      exact continuantRadixMacroNormalForm_ext height_zero shift_zero
    have physical := relation.mpr normal_eq
    simpa [continuantRadixMacroEncoding] using physical

/-- Exchange writers with readers while reversing their projective action. -/
def continuantRadixMacroInverse : ContinuantRadixMacro → ContinuantRadixMacro
  | .writer bit => .reader bit
  | .reader bit => .writer bit

/-- Reverse a segmented macro word and invert every operation. -/
def continuantRadixMacroInverseWord
    (macros : List ContinuantRadixMacro) : List ContinuantRadixMacro :=
  macros.reverse.map continuantRadixMacroInverse

/-- Each normalized writer and reader are exact two-sided inverses. -/
theorem continuantRadixMacroMatrix_inverse
    (op : ContinuantRadixMacro) :
    continuantRadixMacroMatrix op *
          continuantRadixMacroMatrix (continuantRadixMacroInverse op) = 1 ∧
      continuantRadixMacroMatrix (continuantRadixMacroInverse op) *
          continuantRadixMacroMatrix op = 1 := by
  cases op with
  | writer bit =>
      cases bit <;>
        constructor <;>
        ext i j <;> fin_cases i <;> fin_cases j <;>
        norm_num [continuantRadixMacroMatrix, continuantRadixMacroInverse,
          continuantRadixMacroHeight, continuantRadixMacroShift,
          continuantRadixMacroRatio, continuantRadixDigit,
          Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]
  | reader bit =>
      cases bit <;>
        constructor <;>
        ext i j <;> fin_cases i <;> fin_cases j <;>
        norm_num [continuantRadixMacroMatrix, continuantRadixMacroInverse,
          continuantRadixMacroHeight, continuantRadixMacroShift,
          continuantRadixMacroRatio, continuantRadixDigit,
          Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

/-- The normalized product of an inverse macro word is a right inverse. -/
theorem continuantRadixMacroInverseWord_right
    (macros : List ContinuantRadixMacro) :
    wordProduct continuantRadixMacroMatrix macros *
        wordProduct continuantRadixMacroMatrix
          (continuantRadixMacroInverseWord macros) = 1 := by
  induction macros with
  | nil => simp [continuantRadixMacroInverseWord]
  | cons op ops induction =>
      rw [continuantRadixMacroInverseWord, List.reverse_cons, List.map_append,
        wordProduct_cons, wordProduct_append]
      simp only [List.map_cons, List.map_nil, wordProduct_cons,
        wordProduct_nil, Matrix.mul_one, Matrix.mul_assoc]
      change
        continuantRadixMacroMatrix op *
            (wordProduct continuantRadixMacroMatrix ops *
              (wordProduct continuantRadixMacroMatrix
                  (continuantRadixMacroInverseWord ops) *
                continuantRadixMacroMatrix (continuantRadixMacroInverse op))) = 1
      calc
        continuantRadixMacroMatrix op *
              (wordProduct continuantRadixMacroMatrix ops *
                (wordProduct continuantRadixMacroMatrix
                    (continuantRadixMacroInverseWord ops) *
                  continuantRadixMacroMatrix (continuantRadixMacroInverse op))) =
            continuantRadixMacroMatrix op *
              ((wordProduct continuantRadixMacroMatrix ops *
                  wordProduct continuantRadixMacroMatrix
                    (continuantRadixMacroInverseWord ops)) *
                continuantRadixMacroMatrix (continuantRadixMacroInverse op)) := by
                  rw [Matrix.mul_assoc]
        _ = continuantRadixMacroMatrix op *
              (1 * continuantRadixMacroMatrix
                (continuantRadixMacroInverse op)) := by rw [induction]
        _ = continuantRadixMacroMatrix op *
              continuantRadixMacroMatrix (continuantRadixMacroInverse op) := by
                rw [Matrix.one_mul]
        _ = 1 := (continuantRadixMacroMatrix_inverse op).1

/-- The normalized product of an inverse macro word is a left inverse. -/
theorem continuantRadixMacroInverseWord_left
    (macros : List ContinuantRadixMacro) :
    wordProduct continuantRadixMacroMatrix
          (continuantRadixMacroInverseWord macros) *
        wordProduct continuantRadixMacroMatrix macros = 1 := by
  induction macros with
  | nil => simp [continuantRadixMacroInverseWord]
  | cons op ops induction =>
      rw [continuantRadixMacroInverseWord, List.reverse_cons, List.map_append,
        wordProduct_cons, wordProduct_append]
      simp only [List.map_cons, List.map_nil, wordProduct_cons,
        wordProduct_nil, Matrix.mul_one, Matrix.mul_assoc]
      change
        wordProduct continuantRadixMacroMatrix
              (continuantRadixMacroInverseWord ops) *
            (continuantRadixMacroMatrix (continuantRadixMacroInverse op) *
              (continuantRadixMacroMatrix op *
                wordProduct continuantRadixMacroMatrix ops)) = 1
      calc
        wordProduct continuantRadixMacroMatrix
                (continuantRadixMacroInverseWord ops) *
              (continuantRadixMacroMatrix (continuantRadixMacroInverse op) *
                (continuantRadixMacroMatrix op *
                  wordProduct continuantRadixMacroMatrix ops)) =
            wordProduct continuantRadixMacroMatrix
                (continuantRadixMacroInverseWord ops) *
              ((continuantRadixMacroMatrix (continuantRadixMacroInverse op) *
                  continuantRadixMacroMatrix op) *
                wordProduct continuantRadixMacroMatrix ops) := by
                  simp only [Matrix.mul_assoc]
        _ = wordProduct continuantRadixMacroMatrix
              (continuantRadixMacroInverseWord ops) *
            (1 * wordProduct continuantRadixMacroMatrix ops) := by
              rw [(continuantRadixMacroMatrix_inverse op).2]
        _ = wordProduct continuantRadixMacroMatrix
              (continuantRadixMacroInverseWord ops) *
            wordProduct continuantRadixMacroMatrix ops := by rw [Matrix.one_mul]
        _ = 1 := induction

/-- Equality of two macro products is equivalent to neutrality of their exact quotient word. -/
theorem continuantRadixMacro_quotient_eq_one_iff
    (left right : List ContinuantRadixMacro) :
    wordProduct continuantRadixMacroMatrix
        (left ++ continuantRadixMacroInverseWord right) = 1 ↔
      wordProduct continuantRadixMacroMatrix left =
        wordProduct continuantRadixMacroMatrix right := by
  rw [wordProduct_append]
  constructor
  · intro quotient_one
    calc
      wordProduct continuantRadixMacroMatrix left =
          wordProduct continuantRadixMacroMatrix left * 1 := by simp
      _ = wordProduct continuantRadixMacroMatrix left *
            (wordProduct continuantRadixMacroMatrix
                (continuantRadixMacroInverseWord right) *
              wordProduct continuantRadixMacroMatrix right) := by
          rw [continuantRadixMacroInverseWord_left]
      _ = (wordProduct continuantRadixMacroMatrix left *
            wordProduct continuantRadixMacroMatrix
              (continuantRadixMacroInverseWord right)) *
            wordProduct continuantRadixMacroMatrix right := by
          simp only [Matrix.mul_assoc]
      _ = wordProduct continuantRadixMacroMatrix right := by
          rw [quotient_one, Matrix.one_mul]
  · intro product_eq
    rw [product_eq, continuantRadixMacroInverseWord_right]

/-- Macro spelling of the opposite unclocked mismatch insertion from `R32-S71`. -/
def continuantNeutralMismatchMacros : List ContinuantRadixMacro :=
  [.reader false, .writer true, .reader true, .writer false]

/-- The `R32-S71` malformed insertion is exactly the physical encoding of its four macros. -/
theorem continuantNeutralMismatchMacros_encoding :
    continuantRadixMacroEncoding continuantNeutralMismatchMacros =
      falseWaitFirstHitNeutralMismatchWord := by
  simp [continuantNeutralMismatchMacros, continuantRadixMacroEncoding,
    continuantRadixMacroWord, falseWaitFirstHitNeutralMismatchWord,
    continuantReadWriteWord, List.append_assoc]

/-- The opposite unclocked mismatch insertion has the zero affine normal form. -/
theorem continuantNeutralMismatchMacros_normalForm :
    continuantRadixMacroNormalForm continuantNeutralMismatchMacros = ⟨0, 0⟩ := by
  ext <;>
    norm_num [continuantNeutralMismatchMacros, continuantRadixMacroNormalForm,
      continuantRadixMacroHeight, continuantRadixMacroShift,
      continuantRadixMacroRatio, continuantRadixDigit]

end MatrixMortality.CubicReturn.NonPure
