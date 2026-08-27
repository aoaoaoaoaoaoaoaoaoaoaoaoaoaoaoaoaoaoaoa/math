import MatrixMortality.ParabolicDefect

/-!
# Retuned parabolic semantic blade

The retuned open root moves the unique singular atom to gap two.  A leading-zero ternary
evaluation then makes the determinant of the exceptional bridge recognize the exact Neary
terminal equation inside one physical three-generator word.  The recognized word is nonzero;
closing mortality still requires a fixed one-sided annihilator and an arbitrary-word converse.
-/

namespace MatrixMortality

open scoped Matrix

namespace ParabolicRetuned

/-! ## Leading-zero ternary code -/

/-- Sparse ternary digit: `true` is zero and `false` is one. -/
def sparseDigit : Bool → Nat
  | true => 0
  | false => 1

@[simp] theorem sparseDigit_lt_three (bit : Bool) : sparseDigit bit < 3 := by
  cases bit <;> decide

theorem sparseDigit_injective : Function.Injective sparseDigit := by
  intro left right equality
  cases left <;> cases right <;> simp_all [sparseDigit]

/-- Left-to-right base-three evaluation with digits zero and one. -/
def sparseCode (word : List Bool) : Nat :=
  Nat.ofDigits 3 (word.reverse.map sparseDigit)

@[simp] theorem sparseCode_nil : sparseCode [] = 0 := by
  simp [sparseCode]

theorem sparseCode_append (left right : List Bool) :
    sparseCode (left ++ right) =
      3 ^ right.length * sparseCode left + sparseCode right := by
  simp [sparseCode, List.reverse_append, Nat.ofDigits_append, add_comm]

@[simp] theorem sparseCode_singleton (bit : Bool) : sparseCode [bit] = sparseDigit bit := by
  cases bit <;> decide

theorem sparseCode_append_singleton (word : List Bool) (bit : Bool) :
    sparseCode (word ++ [bit]) = 3 * sparseCode word + sparseDigit bit := by
  rw [sparseCode_append]
  simp

theorem sparseCode_cons (bit : Bool) (word : List Bool) :
    sparseCode (bit :: word) =
      3 ^ word.length * sparseDigit bit + sparseCode word := by
  simpa using sparseCode_append [bit] word

/-- A sparse code remains below the base-three scale fixed by its length. -/
theorem sparseCode_lt_pow_length (word : List Bool) :
    sparseCode word < 3 ^ word.length := by
  rw [sparseCode]
  have digit_bound :
      ∀ digit ∈ word.reverse.map sparseDigit, digit < 3 := by
    intro digit member
    obtain ⟨bit, _, rfl⟩ := List.mem_map.mp member
    exact sparseDigit_lt_three bit
  simpa using Nat.ofDigits_lt_base_pow_length (by norm_num : 1 < 3) digit_bound

/-- Leading zeroes are harmless once the word length is fixed. -/
theorem sparseCode_injective_of_length_eq {left right : List Bool}
    (length_eq : left.length = right.length)
    (code_eq : sparseCode left = sparseCode right) :
    left = right := by
  induction left using List.reverseRecOn generalizing right with
  | nil =>
      have right_empty : right = [] := List.length_eq_zero_iff.mp (by simpa using length_eq.symm)
      exact right_empty.symm
  | append_singleton left bit induction =>
      induction right using List.reverseRecOn with
      | nil => simp at length_eq
      | append_singleton right other =>
          have prefix_length : left.length = right.length := by simpa using length_eq
          rw [sparseCode_append_singleton, sparseCode_append_singleton] at code_eq
          have digit_eq : sparseDigit bit = sparseDigit other := by
            cases bit <;> cases other <;> simp_all [sparseDigit] <;> omega
          have prefix_code : sparseCode left = sparseCode right := by
            rw [digit_eq] at code_eq
            omega
          have bit_eq : bit = other := sparseDigit_injective digit_eq
          subst other
          rw [induction prefix_length prefix_code]

/-- Affine numerator whose reduced denominator remembers the sparse word length. -/
def sparseNumerator (word : List Bool) : Nat := 19 * sparseCode word + 1

private theorem sparseNumerator_append_false_mod_three (word : List Bool) :
    sparseNumerator (word ++ [false]) % 3 = 2 := by
  rw [sparseNumerator, sparseCode_append_singleton]
  simp [sparseDigit, Nat.add_mod, Nat.mul_mod]

private theorem sparseNumerator_append_false_coprime_three (word : List Bool) :
    Nat.Coprime 3 (sparseNumerator (word ++ [false])) := by
  apply Nat.prime_three.coprime_iff_not_dvd.mpr
  intro divides
  have residue_zero := Nat.mod_eq_zero_of_dvd divides
  rw [sparseNumerator_append_false_mod_three] at residue_zero
  norm_num at residue_zero

/-- Equality of the affine fractions `(19κ(z)+1)/3^|z|` is injective on words ending in
`false`. -/
theorem sparseFraction_cross_eq_iff (left right : List Bool) :
    sparseNumerator (left ++ [false]) * 3 ^ (right ++ [false]).length =
        sparseNumerator (right ++ [false]) * 3 ^ (left ++ [false]).length ↔
      left = right := by
  constructor
  · intro cross
    let leftPower := 3 ^ (left ++ [false]).length
    let rightPower := 3 ^ (right ++ [false]).length
    have left_coprime :
        Nat.Coprime leftPower (sparseNumerator (left ++ [false])) := by
      exact (sparseNumerator_append_false_coprime_three left).pow_left _
    have right_coprime :
        Nat.Coprime rightPower (sparseNumerator (right ++ [false])) := by
      exact (sparseNumerator_append_false_coprime_three right).pow_left _
    have left_dvd_right : leftPower ∣ rightPower := by
      apply left_coprime.dvd_of_dvd_mul_left
      rw [cross]
      exact dvd_mul_left _ _
    have right_dvd_left : rightPower ∣ leftPower := by
      apply right_coprime.dvd_of_dvd_mul_left
      rw [← cross]
      exact dvd_mul_left _ _
    have length_eq : (left ++ [false]).length = (right ++ [false]).length := by
      have left_le_right :
          (left ++ [false]).length ≤ (right ++ [false]).length :=
        (pow_dvd_pow_iff (by norm_num : (3 : Nat) ≠ 0)
          (by norm_num : ¬IsUnit (3 : Nat))).mp left_dvd_right
      have right_le_left :
          (right ++ [false]).length ≤ (left ++ [false]).length :=
        (pow_dvd_pow_iff (by norm_num : (3 : Nat) ≠ 0)
          (by norm_num : ¬IsUnit (3 : Nat))).mp right_dvd_left
      omega
    have numerator_eq :
        sparseNumerator (left ++ [false]) = sparseNumerator (right ++ [false]) := by
      let scale := 3 ^ (left ++ [false]).length
      have scale_pos : 0 < scale := pow_pos (by norm_num) _
      have scaled_eq :
          sparseNumerator (left ++ [false]) * scale =
            sparseNumerator (right ++ [false]) * scale := by
        simpa [scale, length_eq] using cross
      exact Nat.mul_right_cancel scale_pos scaled_eq
    have code_eq : sparseCode (left ++ [false]) = sparseCode (right ++ [false]) := by
      dsimp [sparseNumerator] at numerator_eq
      omega
    have word_eq := sparseCode_injective_of_length_eq length_eq code_eq
    exact List.append_cancel_right word_eq
  · rintro rfl
    rfl

/-! ## Retuned physical atoms -/

/-- Fixed open root of the retuned semantic blade. -/
def root : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0, -1, 0, 0;
     1, -1, 0, 0;
     0, 0, 1, 0;
     -19 / 24, 1 / 8, 2 / 3, 1]

/-- The retuned root has the same restricted cube as the original parabolic root. -/
theorem root_cube : root ^ 3 = ParabolicBlade.drift 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [root, ParabolicBlade.drift, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The root cube agrees with the phase toggle on the common image plane. -/
theorem root_cube_mul_injection :
    root ^ 3 * ParabolicBlade.injection =
      ParabolicBlade.normalToggle * ParabolicBlade.injection := by
  rw [root_cube]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ParabolicBlade.drift, ParabolicBlade.normalToggle,
      ParabolicBlade.injection, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem drift_mul (left right : ℚ) :
    ParabolicBlade.drift left * ParabolicBlade.drift right =
      ParabolicBlade.drift (left + right) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ParabolicBlade.drift, Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals ring

private theorem drift_zero : ParabolicBlade.drift 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ParabolicBlade.drift, Matrix.one_apply]

theorem root_pow_three_mul (j : Nat) : root ^ (3 * j) = ParabolicBlade.drift j := by
  induction j with
  | zero => exact drift_zero.symm
  | succ j induction =>
      rw [Nat.mul_succ, pow_add, induction, root_cube, drift_mul]
      norm_num

private theorem root_pow_three_mul_add_one (j : Nat) :
    root ^ (3 * j + 1) = ParabolicBlade.drift j * root := by
  rw [pow_add, root_pow_three_mul]
  simp

private theorem root_pow_three_mul_add_two (j : Nat) :
    root ^ (3 * j + 2) = ParabolicBlade.drift j * root ^ 2 := by
  rw [pow_add, root_pow_three_mul]

/-- Sparse value of the Neary marker. -/
def markerCode (β : Nat) : Nat := sparseCode (nearyMarker β)

/-- Sparse value of the long upper word carried by `b`. -/
def upperBCode (β : Nat) : Nat := sparseCode (tagCode β .b)

/-- Sparse value of the body-dependent lower rule word carried by `c`. -/
def lowerCCode (β : Nat) (body : List TagLetter) : Nat :=
  sparseCode (nearyLower β body (.rule .c))

/-- Base-three scale of the body-dependent lower rule word carried by `c`. -/
def lowerCScale (β : Nat) (body : List TagLetter) : Nat :=
  3 ^ (nearyLower β body (.rule .c)).length

theorem markerCode_relation (β : Nat) : 2 * markerCode β + 1 = 3 ^ β := by
  induction β with
  | zero => norm_num [markerCode, nearyMarker, sparseCode, sparseDigit]
  | succ β induction =>
      have marker_succ : nearyMarker (β + 1) = nearyMarker β ++ [false] := by
        simp [nearyMarker, List.replicate_succ']
      rw [markerCode, marker_succ, sparseCode_append_singleton]
      simp only [sparseDigit]
      rw [pow_succ]
      dsimp [markerCode] at induction
      omega

theorem upperBCode_relation (β : Nat) : 2 * upperBCode β + 3 = 3 * 3 ^ β := by
  have shape : tagCode β .b = nearyMarker β ++ [true] := by
    simp [tagCode, nearyMarker]
  have marker := markerCode_relation β
  dsimp [markerCode] at marker
  rw [upperBCode, shape, sparseCode_append_singleton, sparseDigit]
  omega

/-- Three-dimensional `b` flank for the sparse semantic code. -/
def bFlank (β : Nat) : Matrix (Fin 3) (Fin 4) ℚ :=
  let ρ : ℚ := 3 ^ β
  ParabolicBlade.flank 1 (3 * (ρ - 1) / 2) 1 (9 * ρ) 27 3

/-- Three-dimensional `c` flank for the sparse semantic code. -/
def cFlank (β : Nat) (body : List TagLetter) : Matrix (Fin 3) (Fin 4) ℚ :=
  ParabolicBlade.flank (lowerCCode β body) 0 1 3 (lowerCScale β body) 3

/-- Flank selected by a Neary tag letter. -/
def dataFlank (β : Nat) (body : List TagLetter) :
    TagLetter → Matrix (Fin 3) (Fin 4) ℚ
  | .b => bFlank β
  | .c => cFlank β body

/-- One of the two physical data generators in the common-image basis. -/
def dataGenerator (β : Nat) (body : List TagLetter) (letter : TagLetter) :
    Matrix (Fin 4) (Fin 4) ℚ :=
  ParabolicBlade.injection * dataFlank β body letter

/-- Reduced gap atom of the retuned three-generator family. -/
def atom (β : Nat) (body : List TagLetter) (letter : TagLetter) (gap : Nat) :
    Matrix (Fin 3) (Fin 3) ℚ :=
  dataFlank β body letter * root ^ gap * ParabolicBlade.injection

/-- Determinant pencil of residue-zero `b` atoms. -/
theorem atom_b_det_three_mul (β : Nat) (body : List TagLetter) (j : Nat) :
    (atom β body .b (3 * j)).det = 27 * (3 : ℚ) ^ β * (8 * j + 1) := by
  rw [atom, dataFlank, bFlank, root_pow_three_mul, Matrix.det_fin_three]
  norm_num [ParabolicBlade.flank, ParabolicBlade.drift, ParabolicBlade.injection,
    Matrix.mul_apply, Fin.sum_univ_succ, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail]
  ring

/-- Determinant pencil of residue-one `b` atoms. -/
theorem atom_b_det_three_mul_add_one (β : Nat) (body : List TagLetter) (j : Nat) :
    (atom β body .b (3 * j + 1)).det = 9 * (3 : ℚ) ^ β * (24 * j - 5) := by
  rw [atom, dataFlank, bFlank, root_pow_three_mul_add_one, Matrix.det_fin_three]
  norm_num [ParabolicBlade.flank, ParabolicBlade.drift, root,
    ParabolicBlade.injection, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  ring

/-- Determinant pencil of residue-two `b` atoms. -/
theorem atom_b_det_three_mul_add_two (β : Nat) (body : List TagLetter) (j : Nat) :
    (atom β body .b (3 * j + 2)).det = 216 * j * (3 : ℚ) ^ β := by
  rw [atom, dataFlank, bFlank, root_pow_three_mul_add_two, Matrix.det_fin_three]
  norm_num [ParabolicBlade.flank, ParabolicBlade.drift, root,
    ParabolicBlade.injection, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  ring

/-- Determinant pencil of residue-zero `c` atoms. -/
theorem atom_c_det_three_mul (β : Nat) (body : List TagLetter) (j : Nat) :
    (atom β body .c (3 * j)).det =
      3 * ((lowerCScale β body - 3 : ℚ) * j + 3) := by
  rw [atom, dataFlank, cFlank, root_pow_three_mul, Matrix.det_fin_three]
  norm_num [ParabolicBlade.flank, ParabolicBlade.drift, ParabolicBlade.injection,
    Matrix.mul_apply, Fin.sum_univ_succ, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail]
  ring

/-- Determinant pencil of residue-one `c` atoms. -/
theorem atom_c_det_three_mul_add_one (β : Nat) (body : List TagLetter) (j : Nat) :
    (atom β body .c (3 * j + 1)).det =
      6 * lowerCCode β body + 3 * lowerCScale β body * j -
        lowerCScale β body - 9 * j + 6 := by
  rw [atom, dataFlank, cFlank, root_pow_three_mul_add_one, Matrix.det_fin_three]
  norm_num [ParabolicBlade.flank, ParabolicBlade.drift, root,
    ParabolicBlade.injection, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  ring

/-- Determinant pencil of residue-two `c` atoms. -/
theorem atom_c_det_three_mul_add_two (β : Nat) (body : List TagLetter) (j : Nat) :
    (atom β body .c (3 * j + 2)).det =
      (3 / 8 : ℚ) *
        (19 * lowerCCode β body + 8 * lowerCScale β body * j -
          lowerCScale β body - 24 * j + 8) := by
  rw [atom, dataFlank, cFlank, root_pow_three_mul_add_two, Matrix.det_fin_three]
  norm_num [ParabolicBlade.flank, ParabolicBlade.drift, root,
    ParabolicBlade.injection, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  ring

private theorem lowerCScale_ge_twenty_seven (β : Nat) (body : List TagLetter) :
    27 ≤ lowerCScale β body := by
  have length_ge : 3 ≤ (nearyLower β body (.rule .c)).length := by
    simp [nearyLower]
  change 3 ^ 3 ≤ 3 ^ (nearyLower β body (.rule .c)).length
  exact Nat.pow_le_pow_right (by norm_num) length_ge

private theorem lowerC_nine_data (β : Nat) (body : List TagLetter) :
    ∃ code scale : Nat,
      lowerCCode β body = 9 * code + 1 ∧ lowerCScale β body = 9 * scale := by
  let stem := true :: tagEncode β body
  have shape : nearyLower β body (.rule .c) = stem ++ [true, false] := by
    simp [stem, nearyLower]
  refine ⟨sparseCode stem, 3 ^ stem.length, ?_, ?_⟩
  · rw [lowerCCode, shape, sparseCode_append]
    norm_num [sparseCode, sparseDigit, Nat.ofDigits]
  · rw [lowerCScale, shape, List.length_append, pow_add]
    norm_num
    ring

private theorem leading_tagEncode_eq_append_true (β : Nat) (body : List TagLetter) :
    ∃ stem, true :: tagEncode β body = stem ++ [true] := by
  induction body using List.reverseRecOn with
  | nil => exact ⟨[], rfl⟩
  | append_singleton body letter _ =>
      rw [tagEncode_append]
      cases letter
      · refine ⟨true :: tagEncode β body ++
          (true :: List.replicate β false), ?_⟩
        simp [tagCode]
      · refine ⟨true :: tagEncode β body, ?_⟩
        simp [tagCode]

private theorem lowerC_four_suffix
    (β : Nat) (body : List TagLetter) (β_pos : 0 < β) (body_nonempty : body ≠ []) :
    (∃ stem,
      nearyLower β body (.rule .c) = stem ++ [true, true, true, false]) ∨
    (∃ stem,
      nearyLower β body (.rule .c) = stem ++ [false, true, true, false]) := by
  induction body using List.reverseRecOn with
  | nil => exact False.elim (body_nonempty rfl)
  | append_singleton body letter _ =>
      cases letter
      · obtain ⟨prior, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : β ≠ 0)
        right
        refine ⟨true :: tagEncode (prior + 1) body ++
          (true :: List.replicate prior false), ?_⟩
        simp [nearyLower, tagEncode_append, tagCode, List.replicate_succ']
      · left
        obtain ⟨stem, stem_shape⟩ := leading_tagEncode_eq_append_true β body
        refine ⟨stem, ?_⟩
        rw [nearyLower, tagEncode_append]
        simp only [tagEncode_cons, tagEncode_nil, tagCode, List.append_nil,
          List.singleton_append]
        have extended := congrArg
          (fun word : List Bool => word ++ [true, true, false]) stem_shape
        simpa only [List.cons_append, List.append_assoc, List.nil_append] using extended

private theorem lowerC_eighty_one_data
    (β : Nat) (body : List TagLetter) (β_pos : 0 < β) (body_nonempty : body ≠ []) :
    ∃ code scale : Nat,
      (lowerCCode β body = 81 * code + 1 ∨
        lowerCCode β body = 81 * code + 28) ∧
      lowerCScale β body = 81 * scale := by
  obtain ⟨stem, shape⟩ | ⟨stem, shape⟩ :=
    lowerC_four_suffix β body β_pos body_nonempty
  · refine ⟨sparseCode stem, 3 ^ stem.length, Or.inl ?_, ?_⟩
    · rw [lowerCCode, shape, sparseCode_append]
      norm_num [sparseCode, sparseDigit, Nat.ofDigits]
    · rw [lowerCScale, shape, List.length_append, pow_add]
      norm_num
      ring
  · refine ⟨sparseCode stem, 3 ^ stem.length, Or.inr ?_, ?_⟩
    · rw [lowerCCode, shape, sparseCode_append]
      norm_num [sparseCode, sparseDigit, Nat.ofDigits]
    · rw [lowerCScale, shape, List.length_append, pow_add]
      norm_num
      ring

theorem atom_b_det_three_mul_ne_zero
    (β : Nat) (body : List TagLetter) (j : Nat) :
    (atom β body .b (3 * j)).det ≠ 0 := by
  rw [atom_b_det_three_mul]
  positivity

theorem atom_b_det_three_mul_add_one_ne_zero
    (β : Nat) (body : List TagLetter) (j : Nat) :
    (atom β body .b (3 * j + 1)).det ≠ 0 := by
  rw [atom_b_det_three_mul_add_one]
  apply mul_ne_zero (mul_ne_zero (by norm_num) (by positivity))
  intro factor_zero
  have natural_eq : 24 * j = 5 := by exact_mod_cast (sub_eq_zero.mp factor_zero)
  omega

theorem atom_b_det_three_mul_add_two_eq_zero_iff
    (β : Nat) (body : List TagLetter) (j : Nat) :
    (atom β body .b (3 * j + 2)).det = 0 ↔ j = 0 := by
  rw [atom_b_det_three_mul_add_two]
  simp

theorem atom_c_det_three_mul_ne_zero
    (β : Nat) (body : List TagLetter) (j : Nat) :
    (atom β body .c (3 * j)).det ≠ 0 := by
  rw [atom_c_det_three_mul]
  have scale_bound : (27 : ℚ) ≤ lowerCScale β body := by
    exact_mod_cast lowerCScale_ge_twenty_seven β body
  have index_nonnegative : (0 : ℚ) ≤ j := by positivity
  have product_nonnegative :
      0 ≤ (lowerCScale β body - 3 : ℚ) * j :=
    mul_nonneg (by linarith) index_nonnegative
  positivity

theorem atom_c_det_three_mul_add_one_ne_zero
    (β : Nat) (body : List TagLetter) (j : Nat) :
    (atom β body .c (3 * j + 1)).det ≠ 0 := by
  rw [atom_c_det_three_mul_add_one]
  cases j with
  | zero =>
      norm_num
      intro zero
      have natural_eq : lowerCScale β body = 6 * lowerCCode β body + 6 := by
        exact_mod_cast (by linarith :
          (lowerCScale β body : ℚ) = 6 * lowerCCode β body + 6)
      obtain ⟨code, scale, code_eq, scale_eq⟩ := lowerC_nine_data β body
      omega
  | succ j =>
      have scale_bound : (27 : ℚ) ≤ lowerCScale β body := by
        exact_mod_cast lowerCScale_ge_twenty_seven β body
      have factor_positive : (0 : ℚ) < 3 * (j + 1) - 1 := by
        linarith
      have scale_positive : (0 : ℚ) < lowerCScale β body - 3 := by linarith
      have product_positive :
          0 < (3 * (j + 1 : ℚ) - 1) * (lowerCScale β body - 3) :=
        mul_pos factor_positive scale_positive
      push_cast
      nlinarith

theorem atom_c_det_three_mul_add_two_ne_zero
    (β : Nat) (body : List TagLetter) (β_pos : 0 < β)
    (body_nonempty : body ≠ []) (j : Nat) :
    (atom β body .c (3 * j + 2)).det ≠ 0 := by
  rw [atom_c_det_three_mul_add_two]
  apply mul_ne_zero (by norm_num)
  cases j with
  | zero =>
      norm_num
      intro zero
      have natural_eq : lowerCScale β body = 19 * lowerCCode β body + 8 := by
        exact_mod_cast (by linarith :
          (lowerCScale β body : ℚ) = 19 * lowerCCode β body + 8)
      obtain ⟨code, scale, code_eq, scale_eq⟩ :=
        lowerC_eighty_one_data β body β_pos body_nonempty
      rcases code_eq with code_eq | code_eq <;> omega
  | succ j =>
      have scale_bound : (27 : ℚ) ≤ lowerCScale β body := by
        exact_mod_cast lowerCScale_ge_twenty_seven β body
      have factor_positive : (0 : ℚ) < 8 * (j + 1) - 1 := by
        linarith
      have scale_positive : (0 : ℚ) < lowerCScale β body - 3 := by linarith
      have product_positive :
          0 < (8 * (j + 1 : ℚ) - 1) * (lowerCScale β body - 3) :=
        mul_pos factor_positive scale_positive
      push_cast
      nlinarith

private theorem gap_mod_three_cases (gap : Nat) :
    gap % 3 = 0 ∨ gap % 3 = 1 ∨ gap % 3 = 2 := by
  have residue_lt := Nat.mod_lt gap (by norm_num : 0 < 3)
  omega

/-- Gap two after `b` is the unique singular reduced atom of the retuned family. -/
theorem atom_det_eq_zero_iff
    (β : Nat) (body : List TagLetter) (β_pos : 0 < β) (body_nonempty : body ≠ [])
    (letter : TagLetter) (gap : Nat) :
    (atom β body letter gap).det = 0 ↔ letter = .b ∧ gap = 2 := by
  obtain residue_zero | residue_one | residue_two := gap_mod_three_cases gap
  · have gap_shape : gap = 3 * (gap / 3) := by omega
    cases letter
    · simp only [true_and]
      constructor
      · intro determinant_zero
        rw [gap_shape] at determinant_zero
        exact False.elim
          (atom_b_det_three_mul_ne_zero β body (gap / 3) determinant_zero)
      · omega
    · simp only [reduceCtorEq, false_and]
      rw [gap_shape]
      exact ⟨atom_c_det_three_mul_ne_zero β body (gap / 3), False.elim⟩
  · have gap_shape : gap = 3 * (gap / 3) + 1 := by omega
    cases letter
    · simp only [true_and]
      constructor
      · intro determinant_zero
        rw [gap_shape] at determinant_zero
        exact False.elim
          (atom_b_det_three_mul_add_one_ne_zero β body (gap / 3) determinant_zero)
      · omega
    · simp only [reduceCtorEq, false_and]
      rw [gap_shape]
      exact ⟨atom_c_det_three_mul_add_one_ne_zero β body (gap / 3), False.elim⟩
  · have gap_shape : gap = 3 * (gap / 3) + 2 := by omega
    cases letter
    · simp only [true_and]
      rw [gap_shape, atom_b_det_three_mul_add_two_eq_zero_iff]
      omega
    · simp only [reduceCtorEq, false_and]
      rw [gap_shape]
      exact ⟨atom_c_det_three_mul_add_two_ne_zero β body β_pos body_nonempty (gap / 3),
        False.elim⟩

end ParabolicRetuned

end MatrixMortality
