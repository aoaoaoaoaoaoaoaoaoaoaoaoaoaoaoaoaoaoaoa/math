import MatrixMortality.CubicReturnNonPure

/-!
# A free radix stack inside the non-pure cubic continuant

The false-wait return family for `X³+X²−1` contains two positive upper-triangular macro
returns with the same diagonal ratio `4/25` and different affine digits. Their products form
an injective binary positional code, so the terminal continuant language has `2^n` distinct
projective products at every macro depth.
-/

namespace MatrixMortality.CubicReturn.NonPure

open scoped Matrix

/-- Integer digit carried by one normalized cubic-continuant macro. -/
def continuantRadixDigit : Bool → ℕ
  | false => 274
  | true => 149

/-- Common normalized affine form of the two cubic-continuant macros. -/
def continuantRadixGenerator (bit : Bool) : Square (Fin 2) ℚ :=
  !![4, continuantRadixDigit bit / 12; 0, 25]

/-- Physical positive-wait block realizing one normalized radix letter. -/
def continuantRadixWord : Bool → List Nat
  | false => [5]
  | true => [8, 1, 15, 8, 1, 8, 15, 21, 15]

/-- Nonzero physical scale erased by projective normalization. -/
def continuantRadixScale : Bool → ℚ
  | false => -6
  | true => 1128443962982400000

/-- Flatten the fixed physical macro selected by each input bit. -/
def continuantRadixEncoding (bits : List Bool) : List Nat :=
  bits.flatMap continuantRadixWord

/-- Every physical letter in a radix encoding is a strictly positive wait. -/
theorem continuantRadixEncoding_positive (bits : List Bool) :
    ∀ wait ∈ continuantRadixEncoding bits, 0 < wait := by
  intro wait membership
  obtain ⟨bit, _, wait_mem⟩ := List.mem_flatMap.mp membership
  cases bit <;> simp [continuantRadixWord] at wait_mem <;> omega

/-- Base-`(4,25)` positional numerator of a binary macro word. -/
def continuantRadixCode : List Bool → ℕ
  | [] => 0
  | bit :: bits =>
      continuantRadixDigit bit * 25 ^ bits.length + 4 * continuantRadixCode bits

/-- The two physical blocks have the same normalized ratio and the displayed distinct digits. -/
theorem continuantRadixWord_product (bit : Bool) :
    wordProduct falseWaitReturn (continuantRadixWord bit) =
      continuantRadixScale bit • continuantRadixGenerator bit := by
  cases bit
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [continuantRadixWord, continuantRadixScale, continuantRadixGenerator,
        continuantRadixDigit, wordProduct_cons, wordProduct_nil,
        falseWaitReturn_eq_state, falseWaitReturnOfState, cubicDefectState,
        CubicDefectState.next, Matrix.smul_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [continuantRadixWord, continuantRadixScale, continuantRadixGenerator,
        continuantRadixDigit, wordProduct_cons, wordProduct_nil,
        falseWaitReturn_eq_state, falseWaitReturnOfState, cubicDefectState,
        CubicDefectState.next, Matrix.mul_apply, Matrix.smul_apply,
        Fin.sum_univ_succ]

private theorem continuantRadixEncoding_product (bits : List Bool) :
    wordProduct falseWaitReturn (continuantRadixEncoding bits) =
      wordProduct
        (fun bit => wordProduct falseWaitReturn (continuantRadixWord bit)) bits := by
  induction bits with
  | nil => simp [continuantRadixEncoding]
  | cons bit bits induction =>
      rw [continuantRadixEncoding, List.flatMap_cons, wordProduct_append,
        wordProduct_cons]
      simpa [continuantRadixEncoding] using
        congrArg
          (fun matrix => wordProduct falseWaitReturn (continuantRadixWord bit) * matrix)
          induction

/-- A physical encoded product is one nonzero scalar times its normalized radix product. -/
theorem continuantRadixEncoding_product_eq_smul (bits : List Bool) :
    wordProduct falseWaitReturn (continuantRadixEncoding bits) =
      (bits.map continuantRadixScale).prod •
        wordProduct continuantRadixGenerator bits := by
  rw [continuantRadixEncoding_product]
  have generators :
      (fun bit => wordProduct falseWaitReturn (continuantRadixWord bit)) =
        fun bit => continuantRadixScale bit • continuantRadixGenerator bit := by
    funext bit
    exact continuantRadixWord_product bit
  rw [generators, wordProduct_smulMatrix]

private theorem continuantRadixCode_mod_four (bit : Bool) (bits : List Bool) :
    continuantRadixCode (bit :: bits) % 4 = continuantRadixDigit bit % 4 := by
  cases bit <;>
    simp [continuantRadixCode, continuantRadixDigit, Nat.add_mod, Nat.mul_mod,
      Nat.pow_mod]

private theorem continuantRadixDigit_mod_four_injective :
    Function.Injective (fun bit => continuantRadixDigit bit % 4) := by
  intro left right equality
  cases left <;> cases right <;> simp_all [continuantRadixDigit]

/-- Equal-length radix words have different positional numerators. -/
theorem continuantRadixCode_injective_of_length_eq {left right : List Bool}
    (length_eq : left.length = right.length)
    (code_eq : continuantRadixCode left = continuantRadixCode right) :
    left = right := by
  induction left generalizing right with
  | nil =>
      have right_empty : right = [] := List.length_eq_zero_iff.mp length_eq.symm
      exact right_empty.symm
  | cons leftBit leftBits induction =>
      cases right with
      | nil => simp at length_eq
      | cons rightBit rightBits =>
          have tail_length : leftBits.length = rightBits.length := by simpa using length_eq
          have residue_eq :
              continuantRadixDigit leftBit % 4 = continuantRadixDigit rightBit % 4 := by
            rw [← continuantRadixCode_mod_four leftBit leftBits,
              ← continuantRadixCode_mod_four rightBit rightBits, code_eq]
          have bit_eq : leftBit = rightBit :=
            continuantRadixDigit_mod_four_injective residue_eq
          subst rightBit
          have tail_code : continuantRadixCode leftBits = continuantRadixCode rightBits := by
            simp only [continuantRadixCode] at code_eq
            rw [tail_length] at code_eq
            omega
          exact congrArg (List.cons leftBit) (induction tail_length tail_code)

/-- The normalized product exposes its length and positional numerator in three entries. -/
theorem continuantRadixGenerator_product_entries (bits : List Bool) :
    (wordProduct continuantRadixGenerator bits) 0 0 = 4 ^ bits.length ∧
      (wordProduct continuantRadixGenerator bits) 1 0 = 0 ∧
      (wordProduct continuantRadixGenerator bits) 1 1 = 25 ^ bits.length ∧
      (wordProduct continuantRadixGenerator bits) 0 1 = continuantRadixCode bits / 12 := by
  induction bits with
  | nil => norm_num [continuantRadixCode]
  | cons bit bits induction =>
      rcases induction with ⟨upperLeft, lowerLeft, lowerRight, upperRight⟩
      simp only [wordProduct_cons]
      constructor
      · rw [Matrix.mul_apply]
        simp [continuantRadixGenerator, Fin.sum_univ_succ, lowerLeft, upperLeft,
          pow_succ']
      constructor
      · rw [Matrix.mul_apply]
        simp [continuantRadixGenerator, Fin.sum_univ_succ, lowerLeft]
      constructor
      · rw [Matrix.mul_apply]
        simp [continuantRadixGenerator, Fin.sum_univ_succ, lowerRight,
          pow_succ']
      · rw [Matrix.mul_apply]
        simp [continuantRadixGenerator, Fin.sum_univ_succ, upperRight, lowerRight,
          continuantRadixCode]
        ring

/-- Distinct binary macro words give distinct normalized matrices even up to scalar. -/
theorem continuantRadixGenerator_projectively_injective
    {left right : List Bool} {scale : ℚ}
    (projective_eq :
      wordProduct continuantRadixGenerator left =
        scale • wordProduct continuantRadixGenerator right) :
    left = right := by
  rcases continuantRadixGenerator_product_entries left with
    ⟨leftUpper, _, leftLower, leftCode⟩
  rcases continuantRadixGenerator_product_entries right with
    ⟨rightUpper, _, rightLower, rightCode⟩
  have upper_eq := congrFun (congrFun projective_eq 0) 0
  have lower_eq := congrFun (congrFun projective_eq 1) 1
  simp only [Matrix.smul_apply, smul_eq_mul] at upper_eq lower_eq
  rw [leftUpper, rightUpper] at upper_eq
  rw [leftLower, rightLower] at lower_eq
  have scale_ne_zero : scale ≠ 0 := by
    intro scale_zero
    rw [scale_zero, zero_mul] at upper_eq
    exact (pow_ne_zero left.length (by norm_num : (4 : ℚ) ≠ 0)) upper_eq
  have ratio_eq :
      ((4 : ℚ) / 25) ^ left.length = ((4 : ℚ) / 25) ^ right.length := by
    rw [div_pow, div_pow, upper_eq, lower_eq]
    field_simp
  have length_eq : left.length = right.length :=
    (pow_right_strictAnti₀
      (by norm_num : (0 : ℚ) < 4 / 25)
      (by norm_num : (4 / 25 : ℚ) < 1)).injective ratio_eq
  have scale_eq_one : scale = 1 := by
    rw [length_eq] at lower_eq
    have power_ne_zero : (25 : ℚ) ^ right.length ≠ 0 := pow_ne_zero _ (by norm_num)
    exact (mul_left_cancel₀ power_ne_zero (by simpa [mul_comm] using lower_eq)).symm
  have code_entry_eq := congrFun (congrFun projective_eq 0) 1
  simp only [Matrix.smul_apply, smul_eq_mul, scale_eq_one, one_mul] at code_entry_eq
  rw [leftCode, rightCode] at code_entry_eq
  have code_cast_eq :
      (continuantRadixCode left : ℚ) = continuantRadixCode right := by
    linarith
  have code_eq : continuantRadixCode left = continuantRadixCode right := by
    exact_mod_cast code_cast_eq
  exact continuantRadixCode_injective_of_length_eq length_eq code_eq

private theorem continuantRadixScale_product_ne_zero (bits : List Bool) :
    (bits.map continuantRadixScale).prod ≠ 0 := by
  apply List.prod_ne_zero
  intro zero_mem
  obtain ⟨bit, _, scale_zero⟩ := List.mem_map.mp zero_mem
  cases bit <;> norm_num [continuantRadixScale] at scale_zero

/-- The physical cubic-continuant encoding is injective after arbitrary projective rescaling. -/
theorem continuantRadixEncoding_projectively_injective
    {left right : List Bool} {scale : ℚ}
    (projective_eq :
      wordProduct falseWaitReturn (continuantRadixEncoding left) =
        scale • wordProduct falseWaitReturn (continuantRadixEncoding right)) :
    left = right := by
  rw [continuantRadixEncoding_product_eq_smul,
    continuantRadixEncoding_product_eq_smul] at projective_eq
  let leftScale := (left.map continuantRadixScale).prod
  let rightScale := (right.map continuantRadixScale).prod
  have leftScale_ne : leftScale ≠ 0 := continuantRadixScale_product_ne_zero left
  have normalized_eq :
      wordProduct continuantRadixGenerator left =
        (scale * rightScale / leftScale) • wordProduct continuantRadixGenerator right := by
    ext i j
    have entry_eq := congrFun (congrFun projective_eq i) j
    simp only [Matrix.smul_apply, smul_eq_mul, leftScale, rightScale] at entry_eq ⊢
    calc
      wordProduct continuantRadixGenerator left i j =
          leftScale⁻¹ *
            (leftScale * wordProduct continuantRadixGenerator left i j) := by
        field_simp
      _ = leftScale⁻¹ *
          (scale * (rightScale * wordProduct continuantRadixGenerator right i j)) := by
        rw [entry_eq]
      _ = scale * rightScale / leftScale *
          wordProduct continuantRadixGenerator right i j := by ring
  exact continuantRadixGenerator_projectively_injective normalized_eq

/-- Every binary encoding is an upper-triangular positive-wait continuant. -/
theorem continuantRadixEncoding_lowerLeft (bits : List Bool) :
    (wordProduct falseWaitReturn (continuantRadixEncoding bits)) 1 0 = 0 := by
  rw [continuantRadixEncoding_product_eq_smul]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [(continuantRadixGenerator_product_entries bits).2.1]
  ring

private theorem falseWaitReturn_zero_absorbs_upperTriangular
    (matrix : Square (Fin 2) ℚ) (lowerLeft : matrix 1 0 = 0) :
    falseWaitReturn 0 * matrix = matrix 1 1 • falseWaitReturn 0 := by
  rw [falseWaitReturn_eq_state]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [falseWaitReturnOfState, cubicDefectState, Matrix.mul_apply,
      Matrix.smul_apply, Fin.sum_univ_succ, lowerLeft] <;> ring

/-- Prefixing the known endpoint bridge by any radix word gives another physical zero. -/
theorem continuantRadixEncoding_zero (bits : List Bool) :
    falseWaitReturn 0 *
        wordProduct falseWaitReturn (continuantRadixEncoding bits ++ falseWaitWord) *
      falseWaitReturn 0 = 0 := by
  rw [wordProduct_append]
  let radixProduct := wordProduct falseWaitReturn (continuantRadixEncoding bits)
  have absorption :
      falseWaitReturn 0 * radixProduct =
        radixProduct 1 1 • falseWaitReturn 0 :=
    falseWaitReturn_zero_absorbs_upperTriangular radixProduct
      (continuantRadixEncoding_lowerLeft bits)
  calc
    falseWaitReturn 0 *
          (radixProduct * wordProduct falseWaitReturn falseWaitWord) *
        falseWaitReturn 0 =
        (falseWaitReturn 0 * radixProduct) *
          wordProduct falseWaitReturn falseWaitWord * falseWaitReturn 0 := by
      simp only [Matrix.mul_assoc]
    _ = (radixProduct 1 1 • falseWaitReturn 0) *
          wordProduct falseWaitReturn falseWaitWord * falseWaitReturn 0 := by
      rw [absorption]
    _ = radixProduct 1 1 •
          (falseWaitReturn 0 * wordProduct falseWaitReturn falseWaitWord *
            falseWaitReturn 0) := by
      rw [Matrix.smul_mul, Matrix.smul_mul]
    _ = 0 := by rw [falseWait_zero, smul_zero]

private theorem falseWaitWord_product_isUnit :
    IsUnit (wordProduct falseWaitReturn falseWaitWord) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  apply isUnit_iff_ne_zero.mpr
  norm_num [falseWaitWord, wordProduct_cons, wordProduct_nil,
    falseWaitReturn_eq_state, falseWaitReturnOfState, cubicDefectState,
    CubicDefectState.next, Matrix.mul_apply, Matrix.det_fin_two,
    Fin.sum_univ_succ]

/-- The radix prefixes give projectively distinct transformations even after the fixed endpoint
bridge is appended. -/
theorem continuantRadixBridge_projectively_injective
    {left right : List Bool} {scale : ℚ}
    (projective_eq :
      wordProduct falseWaitReturn (continuantRadixEncoding left ++ falseWaitWord) =
        scale •
          wordProduct falseWaitReturn (continuantRadixEncoding right ++ falseWaitWord)) :
    left = right := by
  rw [wordProduct_append, wordProduct_append] at projective_eq
  have cancelled :
      wordProduct falseWaitReturn (continuantRadixEncoding left) =
        scale • wordProduct falseWaitReturn (continuantRadixEncoding right) := by
    apply falseWaitWord_product_isUnit.mul_right_cancel
    simpa only [Matrix.smul_mul] using projective_eq
  exact continuantRadixEncoding_projectively_injective cancelled

end MatrixMortality.CubicReturn.NonPure
