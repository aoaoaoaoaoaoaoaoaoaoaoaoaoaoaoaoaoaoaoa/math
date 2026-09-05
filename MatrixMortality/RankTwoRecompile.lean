import Mathlib.Data.Matrix.ColumnRowPartitioned
import MatrixMortality.MixedBranchingPersistentGuard

/-!
# A rank-two fixed-body recompilation

The exact `bcbcbb` guarded recognizer admits a silent fourth coordinate.  The toggle acts as the
identity there and both data controls kill it.  This preserves the complete scalar zero language
while giving the four-dimensional roles ranks `4,3,2`. These ranks therefore do not rule out a
fixed-body exact recognizer. A source-uniform construction remains a separate obligation.
-/

namespace MatrixMortality.RankTwoRecompile

open scoped Matrix

/-- Three guarded coordinates plus one silent coordinate. -/
abbrev State := Fin 3 ⊕ Unit

/-- Rational form of the exact persistent-guard recognizer at memory two. -/
def coreGenerator (control : PairedControl) : Matrix (Fin 3) (Fin 3) ℚ :=
  (MixedBranchingPersistentGuard.generator 2 control).map (Int.castRingHom ℚ)

/-- Only the involutive toggle survives on the silent coordinate. -/
def silentGenerator : PairedControl → Matrix Unit Unit ℚ
  | .toggle => 1
  | .data _ => 0

/-- Four-dimensional block-diagonal extension of the fixed-body recognizer. -/
def generator (control : PairedControl) : Matrix State State ℚ :=
  Matrix.fromBlocks (coreGenerator control) 0 0 (silentGenerator control)

/-- Boundary row extended by zero on the silent coordinate. -/
def row : State → ℚ
  | .inl index => (MixedBranchingPersistentGuard.row index : ℚ)
  | .inr _ => 0

/-- Boundary column extended by zero on the silent coordinate. -/
def column : State → ℚ
  | .inl index => (MixedBranchingPersistentGuard.column index : ℚ)
  | .inr _ => 0

/-- Scalar coefficient of the four-dimensional extension. -/
def coefficient (word : List PairedControl) : ℚ :=
  linearCoefficient generator row column word

/-- Rank-one separator belonging to the recompiled boundary vectors. -/
def separator : Matrix State State ℚ := Matrix.vecMulVec column row

private def padZero (core : Matrix (Fin 3) (Fin 3) ℚ) : Matrix State State ℚ :=
  Matrix.fromBlocks core 0 0 0

private def inclusion : Matrix State (Fin 3) ℚ := Matrix.fromRows 1 0

private def projection : Matrix (Fin 3) State ℚ := Matrix.fromCols 1 0

private theorem projection_mul_inclusion : projection * inclusion = 1 := by
  change Matrix.fromCols 1 0 * Matrix.fromRows 1 0 = (1 : Matrix (Fin 3) (Fin 3) ℚ)
  rw [Matrix.fromCols_mul_fromRows]
  simp

private theorem padZero_rank (core : Matrix (Fin 3) (Fin 3) ℚ) :
    (padZero core).rank = core.rank := by
  have factor : padZero core = inclusion * core * projection := by
    symm
    calc
      inclusion * core * projection =
          Matrix.fromRows core 0 * projection := by
            rw [inclusion, Matrix.fromRows_mul]
            simp
      _ = Matrix.fromBlocks (core * 1) 0 0 0 := by
        rw [projection, Matrix.fromRows_mul_fromCols]
        simp
      _ = padZero core := by simp [padZero]
  have retract : projection * padZero core * inclusion = core := by
    rw [factor]
    calc
      projection * (inclusion * core * projection) * inclusion =
          (projection * inclusion) * core * (projection * inclusion) := by
            simp [Matrix.mul_assoc]
      _ = core := by rw [projection_mul_inclusion]; simp
  apply le_antisymm
  · rw [factor]
    exact (Matrix.rank_mul_le_left (inclusion * core) projection).trans
      (Matrix.rank_mul_le_right inclusion core)
  · calc
      core.rank = (projection * padZero core * inclusion).rank := congrArg Matrix.rank retract.symm
      _ ≤ (projection * padZero core).rank :=
        Matrix.rank_mul_le_left (projection * padZero core) inclusion
      _ ≤ (padZero core).rank := Matrix.rank_mul_le_right projection (padZero core)

private theorem wordProduct_generator (word : List PairedControl) :
    wordProduct generator word =
      Matrix.fromBlocks (wordProduct coreGenerator word) 0 0
        (wordProduct silentGenerator word) := by
  induction word with
  | nil => simp [wordProduct, Matrix.fromBlocks_one]
  | cons control word induction =>
      rw [wordProduct_cons, induction, generator, wordProduct_cons]
      simp [Matrix.fromBlocks_multiply]

private theorem coreDataB_rank : (coreGenerator (.data .b)).rank = 3 := by
  simpa [coreGenerator, MixedBranchingPersistentGuard.generator] using
    MixedBranchingPersistentGuard.data_b_rank_rat (by norm_num : (2 : ℤ) ≠ 0)

private def dataCInput : Matrix (Fin 3) (Fin 2) ℚ :=
  !![coreGenerator (.data .c) 0 1, coreGenerator (.data .c) 0 2;
     coreGenerator (.data .c) 1 1, coreGenerator (.data .c) 1 2;
     coreGenerator (.data .c) 2 1, coreGenerator (.data .c) 2 2]

private def dataCOutput : Matrix (Fin 2) (Fin 3) ℚ :=
  !![0, 1, 0;
     0, 0, 1]

private def dataCLeftInverse : Matrix (Fin 2) (Fin 3) ℚ :=
  !![0, 1 / 7, -(coreGenerator (.data .c) 1 2) / 7;
     0, 0, 1]

private theorem coreDataC_eq_factor :
    coreGenerator (.data .c) = dataCInput * dataCOutput := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coreGenerator, MixedBranchingPersistentGuard.generator,
      MixedBranchingPersistentGuard.data, MixedBranchingRecognizer.recognizerData,
      AffineRecognizer.Parameters.data, dataCInput, dataCOutput,
      Matrix.mul_apply, Fin.sum_univ_succ]

private theorem dataCLeftInverse_mul_input : dataCLeftInverse * dataCInput = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dataCLeftInverse, dataCInput, coreGenerator,
      MixedBranchingPersistentGuard.generator, MixedBranchingPersistentGuard.data,
      MixedBranchingRecognizer.recognizerData, AffineRecognizer.Parameters.data,
      Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two];
    norm_num;
    ring

private theorem dataCOutput_mul_transpose : dataCOutput * dataCOutput.transpose = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [dataCOutput, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

private theorem coreDataC_rank : (coreGenerator (.data .c)).rank = 2 := by
  apply le_antisymm
  · rw [coreDataC_eq_factor]
    exact (Matrix.rank_mul_le_left dataCInput dataCOutput).trans
      (Matrix.rank_le_width dataCInput)
  · have fullSplit :
        dataCLeftInverse * coreGenerator (.data .c) * dataCOutput.transpose = 1 := by
      rw [coreDataC_eq_factor]
      simp only [Matrix.mul_assoc]
      rw [dataCOutput_mul_transpose, Matrix.mul_one, dataCLeftInverse_mul_input]
    have outerBound := Matrix.rank_mul_le_left
      (dataCLeftInverse * coreGenerator (.data .c)) dataCOutput.transpose
    rw [fullSplit, Matrix.rank_one] at outerBound
    have innerBound := Matrix.rank_mul_le_right
      dataCLeftInverse (coreGenerator (.data .c))
    norm_num at outerBound ⊢
    exact outerBound.trans innerBound

/-- The data-`b` role has exact rank three after adjoining the silent coordinate. -/
theorem dataB_rank : (generator (.data .b)).rank = 3 := by
  rw [generator, silentGenerator, ← padZero, padZero_rank, coreDataB_rank]

/-- The data-`c` role has exact rank two after adjoining the silent coordinate. -/
theorem dataC_rank : (generator (.data .c)).rank = 2 := by
  rw [generator, silentGenerator, ← padZero, padZero_rank, coreDataC_rank]

/-- The four-dimensional toggle remains an involution. -/
theorem toggle_involutive : generator .toggle * generator .toggle = 1 := by
  ext (i | i) (j | j) <;>
    fin_cases i <;> fin_cases j <;>
      norm_num [generator, coreGenerator, silentGenerator,
        MixedBranchingPersistentGuard.generator,
        MixedBranchingRecognizer.recognizerGenerator,
        AffineRecognizer.Parameters.generator, Matrix.mul_apply, Matrix.one_apply,
        Fin.sum_univ_succ, Sum.inl_ne_inr, Sum.inr_ne_inl]

/-- The involutive toggle has full rank four. -/
theorem toggle_rank : (generator .toggle).rank = 4 := by
  have toggle_unit : IsUnit (generator .toggle) :=
    isUnit_iff_exists.mpr ⟨generator .toggle, toggle_involutive, toggle_involutive⟩
  simpa [State] using Matrix.rank_of_isUnit (generator .toggle) toggle_unit

/-- The recompiled separator has exact rank one. -/
theorem separator_rank : separator.rank = 1 := by
  apply le_antisymm (Matrix.rank_vecMulVec_le column row)
  let anchor : Unit → State := fun _ => Sum.inl 0
  have anchor_minor : separator.submatrix anchor anchor = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [separator, anchor, row, column, Matrix.vecMulVec, Matrix.one_apply,
      MixedBranchingPersistentGuard.column, MixedBranchingPersistentGuard.row,
      MixedBranchingRecognizer.recognizerColumn, MixedBranchingRecognizer.recognizerRow,
      AffineRecognizer.Parameters.column, AffineRecognizer.row]
  have minor_bound := Matrix.rank_submatrix_le separator anchor anchor
  rw [anchor_minor, Matrix.rank_one] at minor_bound
  norm_num at minor_bound ⊢
  exact minor_bound

/-- The silent extension leaves every rational scalar coefficient unchanged. -/
theorem coefficient_eq_core (word : List PairedControl) :
    coefficient word =
      linearCoefficient coreGenerator
        (fun index => (MixedBranchingPersistentGuard.row index : ℚ))
        (fun index => (MixedBranchingPersistentGuard.column index : ℚ)) word := by
  rw [coefficient, linearCoefficient, wordProduct_generator, linearCoefficient]
  rw [dotProduct, Fintype.sum_sum_type]
  have column_live :
      column ∘ Sum.inl =
        fun index => (MixedBranchingPersistentGuard.column index : ℚ) := by
    funext index
    rfl
  simp [row, Matrix.fromBlocks_mulVec, dotProduct, column_live]

/-- The four-dimensional fixed-body family has exactly the paired `bcbcbb` zero language on the
whole free control monoid. -/
theorem coefficient_eq_zero_iff_paired (word : List PairedControl) :
    coefficient word = 0 ↔
      pairedCoefficient ℚ 3 MixedBranchingRecognizer.mixedBody word = 0 := by
  rw [coefficient_eq_core]
  have mapped := linearCoefficient_map (Int.castRingHom ℚ)
    (MixedBranchingPersistentGuard.generator 2)
    MixedBranchingPersistentGuard.row MixedBranchingPersistentGuard.column word
  rw [show coreGenerator = fun control =>
      (MixedBranchingPersistentGuard.generator 2 control).map (Int.castRingHom ℚ) by rfl]
  have core_eq_cast :
      linearCoefficient
          (fun control =>
            (MixedBranchingPersistentGuard.generator 2 control).map (Int.castRingHom ℚ))
          (fun index => (MixedBranchingPersistentGuard.row index : ℚ))
          (fun index => (MixedBranchingPersistentGuard.column index : ℚ)) word =
        (MixedBranchingPersistentGuard.coefficient 2 word : ℚ) := by
    simpa [MixedBranchingPersistentGuard.coefficient, Function.comp_def] using mapped.symm
  rw [core_eq_cast, Int.cast_eq_zero]
  exact MixedBranchingPersistentGuard.coefficient_eq_zero_iff_paired
    (by exact ⟨1, by norm_num⟩) word

end MatrixMortality.RankTwoRecompile
