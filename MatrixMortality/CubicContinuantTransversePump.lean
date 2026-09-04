import MatrixMortality.CubicContinuantBinaryPump

/-!
# Transverse freeness and ray-stabilizer blindness

The two safe binary loops triangularize in a common-ray chart. Their normalized transverse
affine maps have disjoint invariant chambers, so their full physical matrix products form a
projectively free binary monoid even though every word fixes the same observed source ray.
A generic insertion theorem explains the blindness: once a right context reaches a ray, every
nonzero stabilizer of that ray is invisible to zero incidence in every left context.
-/

namespace MatrixMortality

open scoped Matrix

/-- A ray-stabilizing word scales every contextual source image after a right context reaches
that ray. -/
theorem wordProduct_rayStabilizer_insertion_mulVec
    {α : Type*} (generators : α → Square (Fin 2) ℚ)
    (left loop right : List α) (column ray : Fin 2 → ℚ)
    (loopScale rightScale : ℚ)
    (loop_ray :
      wordProduct generators loop *ᵥ ray = loopScale • ray)
    (right_ray :
      wordProduct generators right *ᵥ column = rightScale • ray) :
    wordProduct generators (left ++ loop ++ right) *ᵥ column =
      loopScale •
        (wordProduct generators (left ++ right) *ᵥ column) := by
  calc
    wordProduct generators (left ++ loop ++ right) *ᵥ column =
        wordProduct generators left *ᵥ
          (wordProduct generators loop *ᵥ
            (wordProduct generators right *ᵥ column)) := by
          simp [wordProduct_append, ← Matrix.mulVec_mulVec, List.append_assoc]
    _ = wordProduct generators left *ᵥ
          (wordProduct generators loop *ᵥ (rightScale • ray)) := by
          rw [right_ray]
    _ = rightScale •
          (wordProduct generators left *ᵥ
            (wordProduct generators loop *ᵥ ray)) := by
          rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
    _ = rightScale •
          (wordProduct generators left *ᵥ (loopScale • ray)) := by
          rw [loop_ray]
    _ = (rightScale * loopScale) •
          (wordProduct generators left *ᵥ ray) := by
          rw [Matrix.mulVec_smul, smul_smul]
    _ = loopScale •
          (rightScale • (wordProduct generators left *ᵥ ray)) := by
          rw [smul_smul]
          congr 1
          ring
    _ = loopScale •
          (wordProduct generators left *ᵥ
            (wordProduct generators right *ᵥ column)) := by
          rw [right_ray, Matrix.mulVec_smul]
    _ = loopScale •
          (wordProduct generators (left ++ right) *ᵥ column) := by
          rw [wordProduct_append, ← Matrix.mulVec_mulVec]

/-- Ray-stabilizer insertion multiplies the corresponding scalar incidence by the loop
eigenvalue. -/
theorem wordProduct_rayStabilizer_insertion_incidence
    {α : Type*} (generators : α → Square (Fin 2) ℚ)
    (left loop right : List α) (row column ray : Fin 2 → ℚ)
    (loopScale rightScale : ℚ)
    (loop_ray :
      wordProduct generators loop *ᵥ ray = loopScale • ray)
    (right_ray :
      wordProduct generators right *ᵥ column = rightScale • ray) :
    row ⬝ᵥ
        (wordProduct generators (left ++ loop ++ right) *ᵥ column) =
      loopScale *
        (row ⬝ᵥ (wordProduct generators (left ++ right) *ᵥ column)) := by
  rw [wordProduct_rayStabilizer_insertion_mulVec generators left loop right column ray
    loopScale rightScale loop_ray right_ray, dotProduct_smul]
  rfl

/-- Inserting a nonzero ray stabilizer preserves and reflects zero incidence in every left
context. -/
theorem wordProduct_rayStabilizer_insertion_zero_iff
    {α : Type*} (generators : α → Square (Fin 2) ℚ)
    (left loop right : List α) (row column ray : Fin 2 → ℚ)
    (loopScale rightScale : ℚ) (loopScale_ne_zero : loopScale ≠ 0)
    (loop_ray :
      wordProduct generators loop *ᵥ ray = loopScale • ray)
    (right_ray :
      wordProduct generators right *ᵥ column = rightScale • ray) :
    row ⬝ᵥ
          (wordProduct generators (left ++ loop ++ right) *ᵥ column) = 0 ↔
      row ⬝ᵥ (wordProduct generators (left ++ right) *ᵥ column) = 0 := by
  rw [wordProduct_rayStabilizer_insertion_incidence generators left loop right row
    column ray loopScale rightScale loop_ray right_ray]
  exact mul_eq_zero.trans (or_iff_right loopScale_ne_zero)

namespace CubicReturn.NonPure

/-- Unimodular basis whose first column is the common internal pump ray. -/
def falseWaitFirstHitBinaryBasis : Square (Fin 2) ℚ :=
  !![4, 1; 3, 1]

/-- Inverse of the common-ray basis. -/
def falseWaitFirstHitBinaryBasisInverse : Square (Fin 2) ℚ :=
  !![1, -1; -3, 4]

/-- Transverse contraction ratio of a normalized binary pump loop. -/
def falseWaitFirstHitBinaryRatio : Bool → ℚ
  | false => 1 / 625
  | true => 197 / 336000

/-- Both transverse ratios are strict contractions. -/
theorem falseWaitFirstHitBinaryRatio_mem_unit (bit : Bool) :
    0 < falseWaitFirstHitBinaryRatio bit ∧
      falseWaitFirstHitBinaryRatio bit < 1 := by
  cases bit <;> norm_num [falseWaitFirstHitBinaryRatio]

/-- Transverse affine digit of a normalized binary pump loop. -/
def falseWaitFirstHitBinaryDigit : Bool → ℚ
  | false => 1712 / 5625
  | true => 122527 / 432000

/-- Each normalized affine pump sends the unit interval into itself. -/
theorem falseWaitFirstHitBinaryAffineMap_bounds
    (bit : Bool) {coordinate : ℚ}
    (coordinate_mem : 0 ≤ coordinate ∧ coordinate ≤ 1) :
    0 ≤ falseWaitFirstHitBinaryDigit bit +
          falseWaitFirstHitBinaryRatio bit * coordinate ∧
      falseWaitFirstHitBinaryDigit bit +
          falseWaitFirstHitBinaryRatio bit * coordinate ≤ 1 := by
  rcases coordinate_mem with ⟨coordinate_nonnegative, coordinate_le_one⟩
  cases bit <;>
    norm_num [falseWaitFirstHitBinaryDigit, falseWaitFirstHitBinaryRatio] <;>
    constructor <;> linarith

/-- Common-ray triangular normalization of the two physical pump loops. -/
def falseWaitFirstHitBinaryNormalizedLoop (bit : Bool) : Square (Fin 2) ℚ :=
  !![1, falseWaitFirstHitBinaryDigit bit; 0, falseWaitFirstHitBinaryRatio bit]

/-- The displayed common-ray basis inverse is a left inverse. -/
theorem falseWaitFirstHitBinaryBasis_inverse_left :
    falseWaitFirstHitBinaryBasisInverse * falseWaitFirstHitBinaryBasis = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [falseWaitFirstHitBinaryBasisInverse, falseWaitFirstHitBinaryBasis,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

/-- The displayed common-ray basis inverse is a right inverse. -/
theorem falseWaitFirstHitBinaryBasis_inverse_right :
    falseWaitFirstHitBinaryBasis * falseWaitFirstHitBinaryBasisInverse = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [falseWaitFirstHitBinaryBasisInverse, falseWaitFirstHitBinaryBasis,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

/-- Each physical loop is its displayed triangular pump up to its nonzero eigenvalue scale. -/
theorem falseWaitFirstHitBinaryLoop_chart (bit : Bool) :
    falseWaitFirstHitBinaryBasisInverse *
        wordProduct falseWaitReturn (falseWaitFirstHitBinaryLoop bit) *
      falseWaitFirstHitBinaryBasis =
        falseWaitFirstHitBinaryScale bit •
          falseWaitFirstHitBinaryNormalizedLoop bit := by
  cases bit <;>
    ext i j <;>
    fin_cases i <;> fin_cases j <;>
      norm_num [falseWaitFirstHitBinaryBasisInverse, falseWaitFirstHitBinaryBasis,
        falseWaitFirstHitBinaryLoop, falseWaitFirstHitBinaryScale,
        falseWaitFirstHitBinaryNormalizedLoop, falseWaitFirstHitBinaryDigit,
        falseWaitFirstHitBinaryRatio, wordProduct_cons, wordProduct_nil,
        falseWaitReturn_eq_state, falseWaitReturnOfState, cubicDefectState,
        CubicDefectState.next, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The two affine pump chambers are disjoint throughout the unit interval. -/
theorem falseWaitFirstHitBinary_chambers_disjoint
    {lower upper : ℚ} (lower_mem : 0 ≤ lower ∧ lower ≤ 1)
    (upper_mem : 0 ≤ upper ∧ upper ≤ 1) :
    falseWaitFirstHitBinaryDigit true +
          falseWaitFirstHitBinaryRatio true * lower <
      falseWaitFirstHitBinaryDigit false +
        falseWaitFirstHitBinaryRatio false * upper := by
  rcases lower_mem with ⟨lower_nonnegative, lower_le_one⟩
  rcases upper_mem with ⟨upper_nonnegative, upper_le_one⟩
  norm_num [falseWaitFirstHitBinaryDigit, falseWaitFirstHitBinaryRatio]
  linarith

/-- Nested affine address of a normalized binary pump word. -/
def falseWaitFirstHitBinaryAffineCode : List Bool → ℚ
  | [] => 0
  | bit :: bits =>
      falseWaitFirstHitBinaryDigit bit +
        falseWaitFirstHitBinaryRatio bit * falseWaitFirstHitBinaryAffineCode bits

/-- Every affine pump address lies in the unit interval. -/
theorem falseWaitFirstHitBinaryAffineCode_bounds (bits : List Bool) :
    0 ≤ falseWaitFirstHitBinaryAffineCode bits ∧
      falseWaitFirstHitBinaryAffineCode bits ≤ 1 := by
  induction bits with
  | nil => norm_num [falseWaitFirstHitBinaryAffineCode]
  | cons bit bits induction =>
      simpa only [falseWaitFirstHitBinaryAffineCode] using
        falseWaitFirstHitBinaryAffineMap_bounds bit induction

/-- Every nonempty affine pump address is strictly positive. -/
theorem falseWaitFirstHitBinaryAffineCode_cons_positive
    (bit : Bool) (bits : List Bool) :
    0 < falseWaitFirstHitBinaryAffineCode (bit :: bits) := by
  rcases falseWaitFirstHitBinaryAffineCode_bounds bits with ⟨lower, _⟩
  cases bit <;>
    norm_num [falseWaitFirstHitBinaryAffineCode, falseWaitFirstHitBinaryDigit,
      falseWaitFirstHitBinaryRatio] <;>
    linarith

/-- Disjoint affine pump chambers decode the complete bit string. -/
theorem falseWaitFirstHitBinaryAffineCode_injective :
    Function.Injective falseWaitFirstHitBinaryAffineCode := by
  intro left right code_eq
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons bit bits =>
          have positive := falseWaitFirstHitBinaryAffineCode_cons_positive bit bits
          exact ((ne_of_gt positive) code_eq.symm).elim
  | cons left_bit left_bits induction =>
      cases right with
      | nil =>
          have positive :=
            falseWaitFirstHitBinaryAffineCode_cons_positive left_bit left_bits
          exact ((ne_of_gt positive) code_eq).elim
      | cons right_bit right_bits =>
          rcases falseWaitFirstHitBinaryAffineCode_bounds left_bits with
            ⟨left_lower, left_upper⟩
          rcases falseWaitFirstHitBinaryAffineCode_bounds right_bits with
            ⟨right_lower, right_upper⟩
          cases left_bit <;> cases right_bit
          · have tail_eq :
                falseWaitFirstHitBinaryAffineCode left_bits =
                  falseWaitFirstHitBinaryAffineCode right_bits := by
              norm_num [falseWaitFirstHitBinaryAffineCode,
                falseWaitFirstHitBinaryDigit, falseWaitFirstHitBinaryRatio] at code_eq
              linarith
            exact congrArg (List.cons false) (induction tail_eq)
          · exact ((ne_of_lt
              (falseWaitFirstHitBinary_chambers_disjoint
                ⟨right_lower, right_upper⟩ ⟨left_lower, left_upper⟩)) (by
                  simp only [falseWaitFirstHitBinaryAffineCode] at code_eq
                  exact code_eq.symm)).elim
          · exact ((ne_of_lt
              (falseWaitFirstHitBinary_chambers_disjoint
                ⟨left_lower, left_upper⟩ ⟨right_lower, right_upper⟩)) (by
                  simp only [falseWaitFirstHitBinaryAffineCode] at code_eq
                  exact code_eq)).elim
          · have tail_eq :
                falseWaitFirstHitBinaryAffineCode left_bits =
                  falseWaitFirstHitBinaryAffineCode right_bits := by
              norm_num [falseWaitFirstHitBinaryAffineCode,
                falseWaitFirstHitBinaryDigit, falseWaitFirstHitBinaryRatio] at code_eq
              linarith
            exact congrArg (List.cons true) (induction tail_eq)

/-- Appending one bit adds its digit at the accumulated transverse ratio. -/
theorem falseWaitFirstHitBinaryAffineCode_append_singleton
    (bits : List Bool) (bit : Bool) :
    falseWaitFirstHitBinaryAffineCode (bits ++ [bit]) =
      falseWaitFirstHitBinaryAffineCode bits +
        (bits.map falseWaitFirstHitBinaryRatio).prod *
          falseWaitFirstHitBinaryDigit bit := by
  induction bits with
  | nil => simp [falseWaitFirstHitBinaryAffineCode]
  | cons head bits induction =>
      simp only [List.cons_append, falseWaitFirstHitBinaryAffineCode,
        List.map_cons, List.prod_cons, induction]
      ring

/-- A normalized pump product exposes its transverse ratio and reversed affine address. -/
theorem falseWaitFirstHitBinaryNormalizedLoop_product_entries (bits : List Bool) :
    (wordProduct falseWaitFirstHitBinaryNormalizedLoop bits) 0 0 = 1 ∧
      (wordProduct falseWaitFirstHitBinaryNormalizedLoop bits) 1 0 = 0 ∧
      (wordProduct falseWaitFirstHitBinaryNormalizedLoop bits) 1 1 =
        (bits.map falseWaitFirstHitBinaryRatio).prod ∧
      (wordProduct falseWaitFirstHitBinaryNormalizedLoop bits) 0 1 =
        falseWaitFirstHitBinaryAffineCode bits.reverse := by
  induction bits with
  | nil =>
      norm_num [falseWaitFirstHitBinaryAffineCode, Matrix.one_apply]
  | cons bit bits induction =>
      rcases induction with ⟨upper_left, lower_left, lower_right, upper_right⟩
      simp only [wordProduct_cons]
      constructor
      · rw [Matrix.mul_apply]
        simp [falseWaitFirstHitBinaryNormalizedLoop, Fin.sum_univ_succ,
          upper_left, lower_left]
      constructor
      · rw [Matrix.mul_apply]
        simp [falseWaitFirstHitBinaryNormalizedLoop, Fin.sum_univ_succ,
          lower_left]
      constructor
      · rw [Matrix.mul_apply]
        simp [falseWaitFirstHitBinaryNormalizedLoop, Fin.sum_univ_succ,
          lower_right]
      · rw [Matrix.mul_apply]
        simp [falseWaitFirstHitBinaryNormalizedLoop, Fin.sum_univ_succ,
          upper_right, lower_right,
          falseWaitFirstHitBinaryAffineCode_append_singleton, mul_comm]

/-- The two normalized common-ray pumps generate a projectively free binary monoid. -/
theorem falseWaitFirstHitBinaryNormalizedLoop_projectively_injective
    {left right : List Bool} {scale : ℚ}
    (projective_eq :
      wordProduct falseWaitFirstHitBinaryNormalizedLoop left =
        scale • wordProduct falseWaitFirstHitBinaryNormalizedLoop right) :
    left = right := by
  rcases falseWaitFirstHitBinaryNormalizedLoop_product_entries left with
    ⟨left_upper, _, _, left_code⟩
  rcases falseWaitFirstHitBinaryNormalizedLoop_product_entries right with
    ⟨right_upper, _, _, right_code⟩
  have upper_eq := congrFun (congrFun projective_eq 0) 0
  simp only [Matrix.smul_apply, smul_eq_mul] at upper_eq
  rw [left_upper, right_upper] at upper_eq
  have scale_eq_one : scale = 1 := by linarith
  have code_entry_eq := congrFun (congrFun projective_eq 0) 1
  simp only [Matrix.smul_apply, smul_eq_mul, scale_eq_one, one_mul] at code_entry_eq
  rw [left_code, right_code] at code_entry_eq
  exact List.reverse_injective
    (falseWaitFirstHitBinaryAffineCode_injective code_entry_eq)

/-- Flattening the fixed physical pump blocks agrees with multiplying their block products. -/
theorem falseWaitFirstHitBinaryEncoding_product (bits : List Bool) :
    wordProduct falseWaitReturn (falseWaitFirstHitBinaryEncoding bits) =
      wordProduct
        (fun bit =>
          wordProduct falseWaitReturn (falseWaitFirstHitBinaryLoop bit)) bits := by
  induction bits with
  | nil => simp [falseWaitFirstHitBinaryEncoding]
  | cons bit bits induction =>
      rw [falseWaitFirstHitBinaryEncoding, List.flatMap_cons, wordProduct_append,
        wordProduct_cons]
      simpa [falseWaitFirstHitBinaryEncoding] using
        congrArg
          (fun matrix =>
            wordProduct falseWaitReturn (falseWaitFirstHitBinaryLoop bit) * matrix)
          induction

/-- Every physical binary pump product is the conjugate normalized product with explicit
scale. -/
theorem falseWaitFirstHitBinaryEncoding_chart (bits : List Bool) :
    falseWaitFirstHitBinaryBasisInverse *
        wordProduct falseWaitReturn (falseWaitFirstHitBinaryEncoding bits) *
      falseWaitFirstHitBinaryBasis =
        (bits.map falseWaitFirstHitBinaryScale).prod •
          wordProduct falseWaitFirstHitBinaryNormalizedLoop bits := by
  rw [falseWaitFirstHitBinaryEncoding_product,
    ← wordProduct_conjugate
      (fun bit =>
        wordProduct falseWaitReturn (falseWaitFirstHitBinaryLoop bit))
      falseWaitFirstHitBinaryBasis falseWaitFirstHitBinaryBasisInverse
      falseWaitFirstHitBinaryBasis_inverse_right
      falseWaitFirstHitBinaryBasis_inverse_left]
  have generator_eq :
      (fun bit =>
        falseWaitFirstHitBinaryBasisInverse *
            wordProduct falseWaitReturn (falseWaitFirstHitBinaryLoop bit) *
          falseWaitFirstHitBinaryBasis) =
        fun bit =>
          falseWaitFirstHitBinaryScale bit •
            falseWaitFirstHitBinaryNormalizedLoop bit := by
    funext bit
    exact falseWaitFirstHitBinaryLoop_chart bit
  rw [generator_eq, wordProduct_smulMatrix]

/-- The physical safe-loop products themselves form a projectively free binary monoid. -/
theorem falseWaitFirstHitBinaryEncoding_product_projectively_injective
    {left right : List Bool} {scale : ℚ}
    (projective_eq :
      wordProduct falseWaitReturn (falseWaitFirstHitBinaryEncoding left) =
        scale •
          wordProduct falseWaitReturn (falseWaitFirstHitBinaryEncoding right)) :
    left = right := by
  have conjugated := congrArg
    (fun matrix =>
      falseWaitFirstHitBinaryBasisInverse * matrix *
        falseWaitFirstHitBinaryBasis)
    projective_eq
  simp only [Matrix.mul_smul, Matrix.smul_mul] at conjugated
  rw [falseWaitFirstHitBinaryEncoding_chart,
    falseWaitFirstHitBinaryEncoding_chart] at conjugated
  simp only [smul_smul] at conjugated
  have left_scale_ne := falseWaitFirstHitBinaryEncoding_scale_ne_zero left
  have normalized_eq := congrArg
    (fun matrix =>
      (left.map falseWaitFirstHitBinaryScale).prod⁻¹ • matrix)
    conjugated
  simp only [smul_smul] at normalized_eq
  rw [inv_mul_cancel₀ left_scale_ne, one_smul] at normalized_eq
  exact falseWaitFirstHitBinaryNormalizedLoop_projectively_injective normalized_eq

/-- Every binary stabilizer spelling is invisible to every left context after the fixed suffix. -/
theorem falseWaitFirstHitBinaryEncoding_contextual_invisibility
    (left : List Nat) (bits : List Bool) :
    falseWaitSeparatorRow ⬝ᵥ
        (wordProduct falseWaitReturn
          (left ++ falseWaitFirstHitBinaryEncoding bits ++
            falseWaitNonacceptingMergeShort) *ᵥ falseWaitSeparatorColumn) =
      (bits.map falseWaitFirstHitBinaryScale).prod *
        (falseWaitSeparatorRow ⬝ᵥ
          (wordProduct falseWaitReturn (left ++ falseWaitNonacceptingMergeShort) *ᵥ
            falseWaitSeparatorColumn)) := by
  have suffix_source :
      wordProduct falseWaitReturn falseWaitNonacceptingMergeShort *ᵥ
          falseWaitSeparatorColumn =
        (-72590904000000 : ℚ) • ![4, 3] := by
    simpa [falseWaitNonacceptingMergeShort, falseWaitInternalPumpSuffix,
      falseWaitInternalPumpSuffixScale, falseWaitInternalPumpRay] using
        falseWaitInternalPumpSuffix_source 0
  exact wordProduct_rayStabilizer_insertion_incidence falseWaitReturn left
    (falseWaitFirstHitBinaryEncoding bits) falseWaitNonacceptingMergeShort
    falseWaitSeparatorRow falseWaitSeparatorColumn ![4, 3]
    (bits.map falseWaitFirstHitBinaryScale).prod (-72590904000000)
    (falseWaitFirstHitBinaryEncoding_ray bits) suffix_source

/-- No left incidence context can distinguish insertion of a binary stabilizer spelling after
the fixed suffix for purposes of zero detection. -/
theorem falseWaitFirstHitBinaryEncoding_contextual_zero_iff
    (left : List Nat) (bits : List Bool) :
    falseWaitSeparatorRow ⬝ᵥ
          (wordProduct falseWaitReturn
            (left ++ falseWaitFirstHitBinaryEncoding bits ++
              falseWaitNonacceptingMergeShort) *ᵥ falseWaitSeparatorColumn) = 0 ↔
      falseWaitSeparatorRow ⬝ᵥ
        (wordProduct falseWaitReturn (left ++ falseWaitNonacceptingMergeShort) *ᵥ
          falseWaitSeparatorColumn) = 0 := by
  rw [falseWaitFirstHitBinaryEncoding_contextual_invisibility]
  exact mul_eq_zero.trans
    (or_iff_right (falseWaitFirstHitBinaryEncoding_scale_ne_zero bits))

end CubicReturn.NonPure

end MatrixMortality
