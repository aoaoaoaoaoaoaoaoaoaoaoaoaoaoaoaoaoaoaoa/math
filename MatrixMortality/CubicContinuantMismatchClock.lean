import MatrixMortality.CubicContinuantReader

/-!
# A mismatch clock for the cubic continuant radix stack

Interleaving the true radix letter after every reader-writer pair turns the two opposite reader
defects into a signed base-`(4,25)` code. A final run of true-readers removes the known
clock baseline. Splitting the existing endpoint bridge at its first positive wait then detects
the remaining translation exactly, so the resulting physical word vanishes precisely when
every guessed bit matches its written bit.
-/

namespace MatrixMortality.CubicReturn.NonPure

open scoped Matrix

/-- Signed defect of one guessed and written bit. -/
def continuantReadError : Bool × Bool → ℤ
  | (false, false) => 0
  | (false, true) => -1
  | (true, false) => 1
  | (true, true) => 0

/-- Cleared signed base-`(4,25)` numerator of a mismatch schedule. -/
def continuantMismatchCode : List ℤ → ℤ
  | [] => 0
  | digit :: digits =>
      digit * 25 ^ digits.length + 4 * continuantMismatchCode digits

/-- Rational signed mismatch accumulated by the clocked affine product. -/
def continuantMismatchDefect : List ℤ → ℚ
  | [] => 0
  | digit :: digits =>
      digit + (4 / 25) * continuantMismatchDefect digits

/-- Upper translation carrying one normalized mismatch defect. -/
def continuantDefectTranslation (shift : ℚ) : Square (Fin 2) ℚ :=
  !![1, shift; 0, 1]

/-- One normalized reader-writer defect followed by the common radix clock. -/
def continuantClockedReadGenerator (digit : ℤ) : Square (Fin 2) ℚ :=
  continuantDefectTranslation ((125 / 48) * digit) * continuantRadixGenerator true

/-- Physical reader, writer, and wait-five clock for one guessed/written pair. -/
def continuantClockedReadWord (check : Bool × Bool) : List Nat :=
  continuantRadixReaderWord check.1 ++
    (continuantRadixWord check.2 ++ continuantRadixWord true)

/-- Physical clocked checks followed by exactly enough true-readers to erase the clock baseline. -/
def continuantBalancedReadWord (checks : List (Bool × Bool)) : List Nat :=
  checks.flatMap continuantClockedReadWord ++
    continuantRepeatWord (continuantRadixReaderWord true) checks.length

/-- Endpoint bridge with the balanced read word inserted after its first positive wait. -/
def continuantCheckedZeroWord (checks : List (Bool × Bool)) : List Nat :=
  [0, 12] ++
    (continuantBalancedReadWord checks ++ [12, 8, 12, 12, 15, 8, 0])

private theorem twentyFive_pow_emod_four (exponent : Nat) :
    (25 : ℤ) ^ exponent % 4 = 1 := by
  induction exponent with
  | zero => norm_num
  | succ exponent induction =>
      rw [pow_succ, Int.mul_emod, induction]
      norm_num

private theorem continuantMismatchCode_zero_forces_all_zero (digits : List ℤ)
    (digit_range : ∀ digit ∈ digits, digit = -1 ∨ digit = 0 ∨ digit = 1)
    (code_zero : continuantMismatchCode digits = 0) :
    ∀ digit ∈ digits, digit = 0 := by
  induction digits with
  | nil => simp
  | cons digit digits induction =>
      have head_range := digit_range digit (by simp)
      have tail_range : ∀ tail ∈ digits, tail = -1 ∨ tail = 0 ∨ tail = 1 := by
        intro tail membership
        exact digit_range tail (by simp [membership])
      have head_eq :
          digit * 25 ^ digits.length = -4 * continuantMismatchCode digits := by
        simp only [continuantMismatchCode] at code_zero
        linarith
      have code_mod := congrArg (fun value : ℤ => value % 4) head_eq
      rw [Int.mul_emod, twentyFive_pow_emod_four] at code_mod
      norm_num at code_mod
      have head_zero : digit = 0 := by
        rcases head_range with negative | zero | positive
        · subst digit
          norm_num at code_mod
        · exact zero
        · subst digit
          norm_num at code_mod
      have tail_zero : continuantMismatchCode digits = 0 := by
        rw [continuantMismatchCode, head_zero] at code_zero
        omega
      intro value membership
      simp only [List.mem_cons] at membership
      rcases membership with rfl | tail_membership
      · exact head_zero
      · exact induction tail_range tail_zero value tail_membership

private theorem continuantMismatchCode_eq_zero_of_all_zero (digits : List ℤ)
    (all_zero : ∀ digit ∈ digits, digit = 0) :
    continuantMismatchCode digits = 0 := by
  induction digits with
  | nil => rfl
  | cons digit digits induction =>
      have head_zero := all_zero digit (by simp)
      have tail_zero : ∀ tail ∈ digits, tail = 0 := by
        intro tail membership
        exact all_zero tail (by simp [membership])
      rw [continuantMismatchCode, head_zero, induction tail_zero]
      ring

private theorem continuantMismatchDefect_eq_scaledCode (digits : List ℤ) :
    continuantMismatchDefect digits =
      25 * continuantMismatchCode digits / 25 ^ digits.length := by
  induction digits with
  | nil => norm_num [continuantMismatchDefect, continuantMismatchCode]
  | cons digit digits induction =>
      rw [continuantMismatchDefect, continuantMismatchCode, induction,
        List.length_cons, pow_succ']
      push_cast
      field_simp

private theorem continuantMismatchDefect_eq_zero_iff (digits : List ℤ)
    (digit_range : ∀ digit ∈ digits, digit = -1 ∨ digit = 0 ∨ digit = 1) :
    continuantMismatchDefect digits = 0 ↔
      ∀ digit ∈ digits, digit = 0 := by
  rw [continuantMismatchDefect_eq_scaledCode]
  constructor
  · intro defect_zero
    have numerator_or_denominator := div_eq_zero_iff.mp defect_zero
    have numerator_zero : (25 : ℚ) * continuantMismatchCode digits = 0 :=
      numerator_or_denominator.resolve_right (pow_ne_zero _ (by norm_num))
    have code_cast_zero : (continuantMismatchCode digits : ℚ) = 0 :=
      (mul_eq_zero.mp numerator_zero).resolve_left (by norm_num)
    have code_zero : continuantMismatchCode digits = 0 := by
      exact_mod_cast code_cast_zero
    exact continuantMismatchCode_zero_forces_all_zero digits digit_range code_zero
  · intro all_zero
    rw [continuantMismatchCode_eq_zero_of_all_zero digits all_zero]
    norm_num

/-- A signed read error is zero exactly when the guessed and written bits agree. -/
theorem continuantReadError_eq_zero_iff (check : Bool × Bool) :
    continuantReadError check = 0 ↔ check.1 = check.2 := by
  rcases check with ⟨guess, actual⟩
  cases guess <;> cases actual <;> norm_num [continuantReadError]

private theorem continuantReadErrors_range (checks : List (Bool × Bool)) :
    ∀ digit ∈ checks.map continuantReadError,
      digit = -1 ∨ digit = 0 ∨ digit = 1 := by
  intro digit membership
  obtain ⟨check, _, rfl⟩ := List.mem_map.mp membership
  rcases check with ⟨guess, actual⟩
  cases guess <;> cases actual <;> simp [continuantReadError]

/-- The clocked signed defect vanishes exactly when every guessed bit matches its writer. -/
theorem continuantReadDefect_eq_zero_iff (checks : List (Bool × Bool)) :
    continuantMismatchDefect (checks.map continuantReadError) = 0 ↔
      ∀ check ∈ checks, check.1 = check.2 := by
  rw [continuantMismatchDefect_eq_zero_iff _ (continuantReadErrors_range checks)]
  constructor
  · intro all_zero check membership
    apply (continuantReadError_eq_zero_iff check).mp
    exact all_zero (continuantReadError check)
      (List.mem_map.mpr ⟨check, membership, rfl⟩)
  · intro matching digit membership
    obtain ⟨check, check_mem, rfl⟩ := List.mem_map.mp membership
    exact (continuantReadError_eq_zero_iff check).mpr (matching check check_mem)

private theorem continuantDefectTranslation_mul (left right : ℚ) :
    continuantDefectTranslation left * continuantDefectTranslation right =
      continuantDefectTranslation (left + right) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [continuantDefectTranslation, Matrix.mul_apply, Fin.sum_univ_succ, add_comm]

private theorem continuantClock_conjugates_translation (shift : ℚ) :
    continuantRadixGenerator true * continuantDefectTranslation shift *
        continuantRadixReader true =
      (25 : ℚ) • continuantDefectTranslation ((4 / 25) * shift) := by
  ext i j
  fin_cases i
  · fin_cases j
    · norm_num [continuantRadixGenerator, continuantRadixDigit,
        continuantDefectTranslation, continuantRadixReader, Matrix.mul_apply,
        Matrix.smul_apply, Fin.sum_univ_succ]
    · norm_num [continuantRadixGenerator, continuantRadixDigit,
        continuantDefectTranslation, continuantRadixReader, Matrix.mul_apply,
        Matrix.smul_apply, Fin.sum_univ_succ]
      ring
  · fin_cases j <;>
      norm_num [continuantRadixGenerator, continuantRadixDigit,
        continuantDefectTranslation, continuantRadixReader, Matrix.mul_apply,
        Matrix.smul_apply, Fin.sum_univ_succ]

private theorem continuantClockedReadProduct_clean (digits : List ℤ) :
    wordProduct continuantClockedReadGenerator digits *
        continuantRadixReader true ^ digits.length =
      (25 ^ digits.length : ℚ) •
        continuantDefectTranslation
          ((125 / 48) * continuantMismatchDefect digits) := by
  induction digits with
  | nil =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [continuantMismatchDefect, continuantDefectTranslation,
          Matrix.one_apply, Matrix.smul_apply]
  | cons digit digits induction =>
      rw [wordProduct_cons, continuantClockedReadGenerator, List.length_cons, pow_succ]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (wordProduct continuantClockedReadGenerator digits),
        induction, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul,
        ← Matrix.mul_assoc (continuantRadixGenerator true),
        continuantClock_conjugates_translation, Matrix.mul_smul,
        continuantDefectTranslation_mul]
      rw [pow_succ]
      ext i j
      fin_cases i
      · fin_cases j
        · simp [continuantMismatchDefect, continuantDefectTranslation,
            Matrix.smul_apply]
        · simp [continuantMismatchDefect, continuantDefectTranslation,
            Matrix.smul_apply]
          ring
      · fin_cases j <;>
          simp [continuantMismatchDefect, continuantDefectTranslation,
            Matrix.smul_apply]

private theorem continuantClockedRead_normalization (check : Bool × Bool) :
    continuantRadixReader check.1 *
        (continuantRadixGenerator check.2 * continuantRadixGenerator true) =
      (25 : ℚ) • continuantClockedReadGenerator (continuantReadError check) := by
  rcases check with ⟨guess, actual⟩
  cases guess <;> cases actual <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [continuantReadError, continuantClockedReadGenerator,
      continuantDefectTranslation, continuantRadixReader,
      continuantRadixGenerator, continuantRadixDigit, Matrix.mul_apply,
      Matrix.smul_apply, Fin.sum_univ_succ]

private theorem continuantClockedReadWord_projectivelyRealizes (check : Bool × Bool) :
    continuantProjectivelyRealizes (continuantClockedReadWord check)
      (continuantClockedReadGenerator (continuantReadError check)) := by
  have reader := continuantRadixReaderWord_projectivelyRealizes check.1
  have writer :
      continuantProjectivelyRealizes (continuantRadixWord check.2)
        (continuantRadixGenerator check.2) := by
    refine ⟨continuantRadixScale check.2, ?_, continuantRadixWord_product check.2⟩
    cases check.2 <;> norm_num [continuantRadixScale]
  have clock :
      continuantProjectivelyRealizes (continuantRadixWord true)
        (continuantRadixGenerator true) := by
    refine ⟨continuantRadixScale true, by norm_num [continuantRadixScale],
      continuantRadixWord_product true⟩
  rcases continuantProjectivelyRealizes_append reader
      (continuantProjectivelyRealizes_append writer clock) with
    ⟨scale, scale_ne, product⟩
  rw [continuantClockedRead_normalization check] at product
  refine ⟨scale * 25, mul_ne_zero scale_ne (by norm_num), ?_⟩
  rw [continuantClockedReadWord, product]
  simp only [smul_smul]

private theorem continuantClockedReadWords_projectivelyRealize
    (checks : List (Bool × Bool)) :
    continuantProjectivelyRealizes (checks.flatMap continuantClockedReadWord)
      (wordProduct continuantClockedReadGenerator (checks.map continuantReadError)) := by
  induction checks with
  | nil =>
      refine ⟨1, one_ne_zero, ?_⟩
      simp
  | cons check checks induction =>
      rw [List.flatMap_cons, List.map_cons, wordProduct_cons]
      exact continuantProjectivelyRealizes_append
        (continuantClockedReadWord_projectivelyRealizes check) induction

/-- The physical clocked-and-cleaned checker realizes exactly one signed defect translation. -/
theorem continuantBalancedReadWord_projectivelyRealizes (checks : List (Bool × Bool)) :
    continuantProjectivelyRealizes (continuantBalancedReadWord checks)
      (continuantDefectTranslation
        ((125 / 48) * continuantMismatchDefect (checks.map continuantReadError))) := by
  have clocked := continuantClockedReadWords_projectivelyRealize checks
  have cleanup := continuantProjectivelyRealizes_repeat
    (continuantRadixReaderWord_projectivelyRealizes true) checks.length
  rcases continuantProjectivelyRealizes_append clocked cleanup with
    ⟨scale, scale_ne, product⟩
  have clean := continuantClockedReadProduct_clean (checks.map continuantReadError)
  rw [List.length_map] at clean
  refine ⟨scale * 25 ^ checks.length,
    mul_ne_zero scale_ne (pow_ne_zero _ (by norm_num)), ?_⟩
  calc
    wordProduct falseWaitReturn (continuantBalancedReadWord checks) =
        scale •
          (wordProduct continuantClockedReadGenerator (checks.map continuantReadError) *
            continuantRadixReader true ^ checks.length) := by
      simpa only [continuantBalancedReadWord] using product
    _ = scale •
          ((25 ^ checks.length : ℚ) •
            continuantDefectTranslation
              ((125 / 48) *
                continuantMismatchDefect (checks.map continuantReadError))) := by
      rw [clean]
    _ = (scale * 25 ^ checks.length) •
          continuantDefectTranslation
            ((125 / 48) * continuantMismatchDefect (checks.map continuantReadError)) := by
      simp only [smul_smul]

private theorem continuantRadixWord_positive (bit : Bool) :
    ∀ wait ∈ continuantRadixWord bit, 0 < wait := by
  intro wait membership
  have encoded := continuantRadixEncoding_positive [bit]
  exact encoded wait (by simpa [continuantRadixEncoding] using membership)

/-- Every wait inside the clocked-and-cleaned checker is positive. -/
theorem continuantBalancedReadWord_positive (checks : List (Bool × Bool)) :
    ∀ wait ∈ continuantBalancedReadWord checks, 0 < wait := by
  intro wait membership
  rw [continuantBalancedReadWord, List.mem_append] at membership
  rcases membership with clocked_mem | cleanup_mem
  · obtain ⟨check, _, block_mem⟩ := List.mem_flatMap.mp clocked_mem
    rw [continuantClockedReadWord, List.mem_append] at block_mem
    rcases block_mem with reader_mem | writer_or_clock
    · exact continuantRadixReaderWord_positive check.1 wait reader_mem
    · rw [List.mem_append] at writer_or_clock
      exact writer_or_clock.elim
        (continuantRadixWord_positive check.2 wait)
        (continuantRadixWord_positive true wait)
  · exact continuantRepeatWord_positive
      (continuantRadixReaderWord_positive true) _ wait cleanup_mem

/-- The split endpoint bridge detects a nonzero translation by a nonzero scalar multiple of its
singular return. -/
theorem continuantMismatchBridge_detects (shift : ℚ) :
    falseWaitReturn 0 * falseWaitReturn 12 * continuantDefectTranslation shift *
          wordProduct falseWaitReturn [12, 8, 12, 12, 15, 8] *
        falseWaitReturn 0 =
      (-60369430118400000 * shift) • falseWaitReturn 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [continuantDefectTranslation, wordProduct_cons, wordProduct_nil,
      falseWaitReturn_eq_state, falseWaitReturnOfState, cubicDefectState,
      CubicDefectState.next, Matrix.mul_apply, Matrix.smul_apply,
      Fin.sum_univ_succ] <;>
    ring

private theorem falseWaitReturn_zero_smul_eq_zero_iff (scale : ℚ) :
    scale • falseWaitReturn 0 = 0 ↔ scale = 0 := by
  constructor
  · intro product_zero
    have upperRight := congrFun (congrFun product_zero 0) 1
    norm_num [falseWaitReturn_eq_state, falseWaitReturnOfState, cubicDefectState,
      CubicDefectState.next, Matrix.smul_apply] at upperRight
    linarith
  · rintro rfl
    exact zero_smul _ _

private theorem matrix_mul_smul_mul (scale : ℚ)
    (left middle right : Square (Fin 2) ℚ) :
    left * ((scale • middle) * right) = scale • (left * middle * right) := by
  rw [Matrix.smul_mul, Matrix.mul_smul]
  simp only [Matrix.mul_assoc]

/-- The physical endpoint word vanishes exactly when every guessed bit matches its written bit. -/
theorem continuantCheckedZeroWord_zero_iff (checks : List (Bool × Bool)) :
    wordProduct falseWaitReturn (continuantCheckedZeroWord checks) = 0 ↔
      ∀ check ∈ checks, check.1 = check.2 := by
  let defect := continuantMismatchDefect (checks.map continuantReadError)
  rcases continuantBalancedReadWord_projectivelyRealizes checks with
    ⟨scale, scale_ne, balancedProduct⟩
  have bridge :
      wordProduct falseWaitReturn [0, 12] *
          continuantDefectTranslation ((125 / 48) * defect) *
        wordProduct falseWaitReturn [12, 8, 12, 12, 15, 8, 0] =
      (-60369430118400000 * ((125 / 48) * defect)) • falseWaitReturn 0 := by
    simpa only [wordProduct_cons, wordProduct_nil, Matrix.mul_one, Matrix.mul_assoc] using
      continuantMismatchBridge_detects ((125 / 48) * defect)
  have product_eq :
      wordProduct falseWaitReturn (continuantCheckedZeroWord checks) =
        (scale * (-60369430118400000 * ((125 / 48) * defect))) •
          falseWaitReturn 0 := by
    rw [continuantCheckedZeroWord, wordProduct_append, wordProduct_append,
      balancedProduct]
    calc
      wordProduct falseWaitReturn [0, 12] *
            ((scale • continuantDefectTranslation ((125 / 48) * defect)) *
              wordProduct falseWaitReturn [12, 8, 12, 12, 15, 8, 0]) =
          scale •
            (wordProduct falseWaitReturn [0, 12] *
              continuantDefectTranslation ((125 / 48) * defect) *
              wordProduct falseWaitReturn [12, 8, 12, 12, 15, 8, 0]) :=
        matrix_mul_smul_mul scale _ _ _
      _ = scale •
            ((-60369430118400000 * ((125 / 48) * defect)) • falseWaitReturn 0) := by
        rw [bridge]
      _ = (scale * (-60369430118400000 * ((125 / 48) * defect))) •
            falseWaitReturn 0 := by
        simp only [smul_smul]
  rw [product_eq, falseWaitReturn_zero_smul_eq_zero_iff]
  constructor
  · intro product_scalar_zero
    have defect_zero : defect = 0 := by
      rcases mul_eq_zero.mp product_scalar_zero with scale_zero | rest_zero
      · exact (scale_ne scale_zero).elim
      · rcases mul_eq_zero.mp rest_zero with coefficient_zero | shifted_zero
        · norm_num at coefficient_zero
        · rcases mul_eq_zero.mp shifted_zero with digit_zero | defect_zero
          · norm_num at digit_zero
          · exact defect_zero
    exact (continuantReadDefect_eq_zero_iff checks).mp defect_zero
  · intro matching
    have defect_zero := (continuantReadDefect_eq_zero_iff checks).mpr matching
    change defect = 0 at defect_zero
    rw [defect_zero]
    ring

end MatrixMortality.CubicReturn.NonPure
