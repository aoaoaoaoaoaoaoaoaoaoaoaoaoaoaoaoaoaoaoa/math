import MatrixMortality.RunLengthHankel
import MatrixMortality.BoundaryTax

/-!
# Sparse transfer-moment Hankel obstruction

An exact transfer series which is eventually a fixed rank-one matrix pays at most one ambient
coordinate when that tail is subtracted. Four reversed time blocks expose any sufficiently late
rank-three exception as a nonsingular twelve-dimensional block-triangular section. Hence the
original series needs at least eleven states.
-/

namespace MatrixMortality

open scoped Matrix

namespace SparseTransferHankel

/-- Add one distinguished row to a rectangular matrix. -/
def prependRow {ι ν K : Type*} (row : ν → K) (matrix : Matrix ι ν K) :
    Matrix (Option ι) ν K
  | none, column => row column
  | some state, column => matrix state column

theorem prependColumn_mul_prependRow
    {Index State K : Type*} [CommRing K] [Fintype State]
    (left : Matrix Index State K) (right : Matrix State Index K)
    (column row : Index → K) :
    prependColumn column left * prependRow row right =
      Matrix.vecMulVec column row + left * right := by
  ext i j
  simp [prependColumn, prependRow, Matrix.mul_apply, Fintype.sum_option,
    Matrix.vecMulVec]

/-- Subtracting a rank-one series costs at most one realization state. -/
theorem card_le_add_one_of_rankOne_difference_det_ne_zero
    {Index State K : Type*} [Field K]
    [Fintype Index] [DecidableEq Index] [Fintype State]
    (left : Matrix Index State K) (right : Matrix State Index K)
    (column row : Index → K)
    (difference_det_ne_zero :
      (left * right - Matrix.vecMulVec column row).det ≠ 0) :
    Fintype.card Index ≤ Fintype.card State + 1 := by
  have augmented_det_ne_zero :
      (prependColumn (-column) left * prependRow row right).det ≠ 0 := by
    rw [prependColumn_mul_prependRow]
    have augmented_eq :
        Matrix.vecMulVec (-column) row + left * right =
          left * right - Matrix.vecMulVec column row := by
      ext i j
      simp [Matrix.vecMulVec]
      ring
    rw [augmented_eq]
    exact difference_det_ne_zero
  have cardinal_bound :=
    card_le_of_det_rectangular_product_ne_zero
      (prependColumn (-column) left) (prependRow row right)
      augmented_det_ne_zero
  simpa [Fintype.card_option] using cardinal_bound

/-- Four three-coordinate blocks. -/
abbrev BlockIndex := Fin 4 × Fin 3

/-- Reversed right times expose the last nonconstant moment on every diagonal block. -/
def fourBlockDifferenceSection
    {Interface K : Type*} [Sub K]
    (series : Nat → Matrix Interface Interface K)
    (tail : Matrix Interface Interface K) (lastTime : Nat)
    (rowCoordinate columnCoordinate : Fin 3 → Interface) :
    Matrix BlockIndex BlockIndex K :=
  fun row column =>
    (series (row.1.val + (lastTime - column.1.val)) - tail)
      (rowCoordinate row.2) (columnCoordinate column.2)

/-- The selected minor of the last deviation from the constant tail. -/
def lastDifferenceMinor
    {Interface K : Type*} [Sub K]
    (series : Nat → Matrix Interface Interface K)
    (tail : Matrix Interface Interface K) (lastTime : Nat)
    (rowCoordinate columnCoordinate : Fin 3 → Interface) :
    Matrix (Fin 3) (Fin 3) K :=
  fun row column =>
    (series lastTime - tail) (rowCoordinate row) (columnCoordinate column)

/-- Identify one time block's coordinate fibre with `Fin 3`. -/
def blockFiberEquiv (block : Fin 4) :
    {index : BlockIndex // index.1 = block} ≃ Fin 3 where
  toFun index := index.1.2
  invFun coordinate := ⟨(block, coordinate), rfl⟩
  left_inv index := by
    apply Subtype.ext
    exact Prod.ext index.2.symm rfl
  right_inv _ := rfl

/-- Three rows witnessing a rank-three toggle deviation from the separator. -/
def toggleDeviationRow : Fin 3 → Fin 4 := ![1, 2, 3]

/-- Three rows witnessing either data role's rank-three deviation from the separator. -/
def dataDeviationRow : Fin 3 → Fin 4 := ![0, 2, 3]

/-- The common three columns of the benchmark deviation certificates. -/
def deviationColumn : Fin 3 → Fin 4 := ![0, 1, 3]

/-- Explicit column of the absorbed rank-one separator. -/
def benchmarkTailColumn : Fin 4 → ℚ := ![67, 0, 81, -1]

/-- Explicit row of the absorbed rank-one separator. -/
def benchmarkTailRow : Fin 4 → ℚ := ![1, 0, 0, 0]

theorem benchmarkSeparator_eq_vecMulVec :
    RunLengthHankel.benchmarkSeparator =
      Matrix.vecMulVec benchmarkTailColumn benchmarkTailRow := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [RunLengthHankel.benchmarkSeparator, benchmarkTailColumn,
      benchmarkTailRow, Matrix.vecMulVec]

/-- The selected toggle deviation from the absorbed separator. -/
def toggleDeviationMinor (scale : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  (scale • RunLengthHankel.benchmarkToggle -
      RunLengthHankel.benchmarkSeparator).submatrix
    toggleDeviationRow deviationColumn

theorem toggleDeviationMinor_eq_explicit (scale : ℚ) :
    toggleDeviationMinor scale =
      !![0, 0, scale;
         -81, 0, 0;
         1, scale, 0] := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [toggleDeviationMinor, RunLengthHankel.benchmarkToggle,
      RunLengthHankel.benchmarkSeparator, toggleDeviationRow, deviationColumn,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]

theorem toggleDeviationMinor_det (scale : ℚ) :
    (toggleDeviationMinor scale).det = -81 * scale ^ 2 := by
  rw [toggleDeviationMinor_eq_explicit, Matrix.det_fin_three]
  simp
  ring

/-- The selected data-`b` deviation from the absorbed separator. -/
def dataBDeviationMinor (scale : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  (scale • RunLengthHankel.benchmarkDataB -
      RunLengthHankel.benchmarkSeparator).submatrix
    dataDeviationRow deviationColumn

theorem dataBDeviationMinor_eq_explicit (scale : ℚ) :
    dataBDeviationMinor scale =
      !![scale - 67, 25 * scale, scale;
         -81, 0, 0;
         1, 27 * scale, 3 * scale] := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [dataBDeviationMinor, RunLengthHankel.benchmarkDataB,
      RunLengthHankel.benchmarkSeparator, dataDeviationRow, deviationColumn,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] <;> ring

theorem dataBDeviationMinor_det (scale : ℚ) :
    (dataBDeviationMinor scale).det = 3888 * scale ^ 2 := by
  rw [dataBDeviationMinor_eq_explicit, Matrix.det_fin_three]
  simp
  ring

/-- The selected data-`c` deviation from the absorbed separator. -/
def dataCDeviationMinor (scale : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  (scale • RunLengthHankel.benchmarkDataC -
      RunLengthHankel.benchmarkSeparator).submatrix
    dataDeviationRow deviationColumn

theorem dataCDeviationMinor_eq_explicit (scale : ℚ) :
    dataCDeviationMinor scale =
      !![scale - 67, 1508677 * scale, scale;
         -81, 0, 0;
         1, 1594323 * scale, 3 * scale] := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [dataCDeviationMinor, RunLengthHankel.benchmarkDataC,
      RunLengthHankel.benchmarkSeparator, dataDeviationRow, deviationColumn,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] <;> ring

theorem dataCDeviationMinor_det (scale : ℚ) :
    (dataCDeviationMinor scale).det = 237468348 * scale ^ 2 := by
  rw [dataCDeviationMinor_eq_explicit, Matrix.det_fin_three]
  simp
  ring

theorem fourBlockDifferenceSection_blockTriangular
    {Interface K : Type*} [AddGroup K]
    (series : Nat → Matrix Interface Interface K)
    (tail : Matrix Interface Interface K) (lastTime : Nat)
    (rowCoordinate columnCoordinate : Fin 3 → Interface)
    (three_le_lastTime : 3 ≤ lastTime)
    (constant_after : ∀ time, lastTime < time → series time = tail) :
    (fourBlockDifferenceSection series tail lastTime
      rowCoordinate columnCoordinate).BlockTriangular Prod.fst := by
  intro row column column_lt_row
  have columnTime_le : column.1.val ≤ lastTime := by
    have columnTime_le_three : column.1.val ≤ 3 := by omega
    exact columnTime_le_three.trans three_le_lastTime
  have exponent_gt :
      lastTime < row.1.val + (lastTime - column.1.val) := by
    have column_lt_row_val : column.1.val < row.1.val := column_lt_row
    omega
  rw [fourBlockDifferenceSection, constant_after _ exponent_gt]
  simp

theorem reindex_fourBlockDifferenceSection_diagonal
    {Interface K : Type*} [AddGroup K]
    (series : Nat → Matrix Interface Interface K)
    (tail : Matrix Interface Interface K) (lastTime : Nat)
    (rowCoordinate columnCoordinate : Fin 3 → Interface)
    (three_le_lastTime : 3 ≤ lastTime) (block : Fin 4) :
    Matrix.reindex (blockFiberEquiv block) (blockFiberEquiv block)
        ((fourBlockDifferenceSection series tail lastTime
          rowCoordinate columnCoordinate).toSquareBlock Prod.fst block) =
      lastDifferenceMinor series tail lastTime rowCoordinate columnCoordinate := by
  ext row column
  have blockTime_le_three : block.val ≤ 3 := by omega
  have blockTime_le : block.val ≤ lastTime :=
    blockTime_le_three.trans three_le_lastTime
  have exponent_eq : block.val + (lastTime - block.val) = lastTime := by
    omega
  simp [Matrix.reindex_apply, Matrix.toSquareBlock_def, blockFiberEquiv,
    fourBlockDifferenceSection, lastDifferenceMinor, exponent_eq]

theorem fourBlockDifferenceSection_det_ne_zero
    {Interface K : Type*} [Field K]
    (series : Nat → Matrix Interface Interface K)
    (tail : Matrix Interface Interface K) (lastTime : Nat)
    (rowCoordinate columnCoordinate : Fin 3 → Interface)
    (three_le_lastTime : 3 ≤ lastTime)
    (constant_after : ∀ time, lastTime < time → series time = tail)
    (last_minor_det_ne_zero :
      (lastDifferenceMinor series tail lastTime
        rowCoordinate columnCoordinate).det ≠ 0) :
    (fourBlockDifferenceSection series tail lastTime
      rowCoordinate columnCoordinate).det ≠ 0 := by
  have blockTriangular :=
    fourBlockDifferenceSection_blockTriangular series tail lastTime
      rowCoordinate columnCoordinate three_le_lastTime constant_after
  rw [blockTriangular.det_fintype]
  apply Finset.prod_ne_zero_iff.mpr
  intro block _
  rw [← Matrix.det_reindex_self (blockFiberEquiv block)]
  rw [reindex_fourBlockDifferenceSection_diagonal series tail lastTime
    rowCoordinate columnCoordinate three_le_lastTime block]
  exact last_minor_det_ne_zero

/-- Selected future factors at times zero through three. -/
def lateFutureFactor
    {Interface State K : Type*} [Semiring K]
    [Fintype State] [DecidableEq State]
    (transition : Matrix State State K) (output : Matrix Interface State K)
    (rowCoordinate : Fin 3 → Interface) : Matrix BlockIndex State K :=
  fun index state =>
    (output * transition ^ index.1.val) (rowCoordinate index.2) state

/-- Selected past factors at the four reversed times ending at `lastTime`. -/
def latePastFactor
    {Interface State K : Type*} [Semiring K]
    [Fintype State] [DecidableEq State]
    (transition : Matrix State State K) (input : Matrix State Interface K)
    (lastTime : Nat) (columnCoordinate : Fin 3 → Interface) :
    Matrix State BlockIndex K :=
  fun state index =>
    (transition ^ (lastTime - index.1.val) * input)
      state (columnCoordinate index.2)

/-- The constant tail's selected output column. -/
def selectedTailColumn {Interface K : Type*}
    (tailColumn : Interface → K) (rowCoordinate : Fin 3 → Interface) :
    BlockIndex → K :=
  fun index => tailColumn (rowCoordinate index.2)

/-- The constant tail's selected input row. -/
def selectedTailRow {Interface K : Type*}
    (tailRow : Interface → K) (columnCoordinate : Fin 3 → Interface) :
    BlockIndex → K :=
  fun index => tailRow (columnCoordinate index.2)

theorem fourBlockDifferenceSection_factor
    {Interface State K : Type*} [CommRing K]
    [Fintype State] [DecidableEq State]
    (series : Nat → Matrix Interface Interface K)
    (transition : Matrix State State K)
    (input : Matrix State Interface K) (output : Matrix Interface State K)
    (tail : Matrix Interface Interface K) (tailColumn tailRow : Interface → K)
    (lastTime : Nat) (rowCoordinate columnCoordinate : Fin 3 → Interface)
    (moments : ∀ time, output * transition ^ time * input = series time)
    (tail_eq : Matrix.vecMulVec tailColumn tailRow = tail) :
    fourBlockDifferenceSection series tail lastTime rowCoordinate columnCoordinate =
      lateFutureFactor transition output rowCoordinate *
        latePastFactor transition input lastTime columnCoordinate -
      Matrix.vecMulVec
        (selectedTailColumn tailColumn rowCoordinate)
        (selectedTailRow tailRow columnCoordinate) := by
  ext row column
  change
    (series (row.1.val + (lastTime - column.1.val)) - tail)
        (rowCoordinate row.2) (columnCoordinate column.2) =
      ((output * transition ^ row.1.val) *
          (transition ^ (lastTime - column.1.val) * input))
          (rowCoordinate row.2) (columnCoordinate column.2) -
        tailColumn (rowCoordinate row.2) * tailRow (columnCoordinate column.2)
  rw [← moments, ← tail_eq]
  simp only [Matrix.sub_apply, Matrix.vecMulVec, pow_add, Matrix.mul_assoc]
  rfl

/-- A rank-three deviation at time at least three, followed by a constant rank-one tail,
forces at least eleven ambient states in every exact transfer realization. -/
theorem eleven_le_card_of_late_rank_three_moment
    {Interface State K : Type*} [Field K]
    [Fintype State] [DecidableEq State]
    (series : Nat → Matrix Interface Interface K)
    (transition : Matrix State State K)
    (input : Matrix State Interface K) (output : Matrix Interface State K)
    (tail : Matrix Interface Interface K) (tailColumn tailRow : Interface → K)
    (lastTime : Nat) (rowCoordinate columnCoordinate : Fin 3 → Interface)
    (three_le_lastTime : 3 ≤ lastTime)
    (moments : ∀ time, output * transition ^ time * input = series time)
    (tail_eq : Matrix.vecMulVec tailColumn tailRow = tail)
    (constant_after : ∀ time, lastTime < time → series time = tail)
    (last_minor_det_ne_zero :
      (lastDifferenceMinor series tail lastTime
        rowCoordinate columnCoordinate).det ≠ 0) :
    11 ≤ Fintype.card State := by
  have section_det_ne_zero :=
    fourBlockDifferenceSection_det_ne_zero series tail lastTime
      rowCoordinate columnCoordinate three_le_lastTime constant_after
      last_minor_det_ne_zero
  have factored_det_ne_zero :
      (lateFutureFactor transition output rowCoordinate *
          latePastFactor transition input lastTime columnCoordinate -
        Matrix.vecMulVec
          (selectedTailColumn tailColumn rowCoordinate)
          (selectedTailRow tailRow columnCoordinate)).det ≠ 0 := by
    rw [← fourBlockDifferenceSection_factor series transition input output
      tail tailColumn tailRow lastTime rowCoordinate columnCoordinate moments tail_eq]
    exact section_det_ne_zero
  have cardinal_bound :=
    card_le_add_one_of_rankOne_difference_det_ne_zero
      (lateFutureFactor transition output rowCoordinate)
      (latePastFactor transition input lastTime columnCoordinate)
      (selectedTailColumn tailColumn rowCoordinate)
      (selectedTailRow tailRow columnCoordinate)
      factored_det_ne_zero
  have twelve_le : 12 ≤ Fintype.card State + 1 := by
    simpa [BlockIndex] using cardinal_bound
  omega

theorem lastDifferenceMinor_eq_submatrix
    {Interface K : Type*} [Sub K]
    (series : Nat → Matrix Interface Interface K)
    (tail value : Matrix Interface Interface K) (lastTime : Nat)
    (rowCoordinate columnCoordinate : Fin 3 → Interface)
    (last_value : series lastTime = value) :
    lastDifferenceMinor series tail lastTime rowCoordinate columnCoordinate =
      (value - tail).submatrix rowCoordinate columnCoordinate := by
  ext row column
  simp only [lastDifferenceMinor, last_value, Matrix.submatrix_apply]

/-- A late nonzero toggle role followed by the absorbed separator needs at least eleven states. -/
theorem eleven_le_card_of_late_toggle_moment
    {State : Type*} [Fintype State] [DecidableEq State]
    (series : Nat → Matrix (Fin 4) (Fin 4) ℚ)
    (transition : Matrix State State ℚ)
    (input : Matrix State (Fin 4) ℚ) (output : Matrix (Fin 4) State ℚ)
    (lastTime : Nat) (scale : ℚ)
    (three_le_lastTime : 3 ≤ lastTime)
    (scale_ne_zero : scale ≠ 0)
    (moments : ∀ time, output * transition ^ time * input = series time)
    (last_value :
      series lastTime = scale • RunLengthHankel.benchmarkToggle)
    (constant_after : ∀ time, lastTime < time →
      series time = RunLengthHankel.benchmarkSeparator) :
    11 ≤ Fintype.card State := by
  apply eleven_le_card_of_late_rank_three_moment series transition input output
    RunLengthHankel.benchmarkSeparator benchmarkTailColumn benchmarkTailRow lastTime
    toggleDeviationRow deviationColumn three_le_lastTime moments
    benchmarkSeparator_eq_vecMulVec.symm constant_after
  rw [lastDifferenceMinor_eq_submatrix series RunLengthHankel.benchmarkSeparator
    (scale • RunLengthHankel.benchmarkToggle) lastTime toggleDeviationRow
    deviationColumn last_value]
  change (toggleDeviationMinor scale).det ≠ 0
  rw [toggleDeviationMinor_det]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 2 scale_ne_zero)

/-- A late nonzero data-`b` role followed by the absorbed separator needs at least eleven
states. -/
theorem eleven_le_card_of_late_dataB_moment
    {State : Type*} [Fintype State] [DecidableEq State]
    (series : Nat → Matrix (Fin 4) (Fin 4) ℚ)
    (transition : Matrix State State ℚ)
    (input : Matrix State (Fin 4) ℚ) (output : Matrix (Fin 4) State ℚ)
    (lastTime : Nat) (scale : ℚ)
    (three_le_lastTime : 3 ≤ lastTime)
    (scale_ne_zero : scale ≠ 0)
    (moments : ∀ time, output * transition ^ time * input = series time)
    (last_value :
      series lastTime = scale • RunLengthHankel.benchmarkDataB)
    (constant_after : ∀ time, lastTime < time →
      series time = RunLengthHankel.benchmarkSeparator) :
    11 ≤ Fintype.card State := by
  apply eleven_le_card_of_late_rank_three_moment series transition input output
    RunLengthHankel.benchmarkSeparator benchmarkTailColumn benchmarkTailRow lastTime
    dataDeviationRow deviationColumn three_le_lastTime moments
    benchmarkSeparator_eq_vecMulVec.symm constant_after
  rw [lastDifferenceMinor_eq_submatrix series RunLengthHankel.benchmarkSeparator
    (scale • RunLengthHankel.benchmarkDataB) lastTime dataDeviationRow
    deviationColumn last_value]
  change (dataBDeviationMinor scale).det ≠ 0
  rw [dataBDeviationMinor_det]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 2 scale_ne_zero)

/-- A late nonzero data-`c` role followed by the absorbed separator needs at least eleven
states. -/
theorem eleven_le_card_of_late_dataC_moment
    {State : Type*} [Fintype State] [DecidableEq State]
    (series : Nat → Matrix (Fin 4) (Fin 4) ℚ)
    (transition : Matrix State State ℚ)
    (input : Matrix State (Fin 4) ℚ) (output : Matrix (Fin 4) State ℚ)
    (lastTime : Nat) (scale : ℚ)
    (three_le_lastTime : 3 ≤ lastTime)
    (scale_ne_zero : scale ≠ 0)
    (moments : ∀ time, output * transition ^ time * input = series time)
    (last_value :
      series lastTime = scale • RunLengthHankel.benchmarkDataC)
    (constant_after : ∀ time, lastTime < time →
      series time = RunLengthHankel.benchmarkSeparator) :
    11 ≤ Fintype.card State := by
  apply eleven_le_card_of_late_rank_three_moment series transition input output
    RunLengthHankel.benchmarkSeparator benchmarkTailColumn benchmarkTailRow lastTime
    dataDeviationRow deviationColumn three_le_lastTime moments
    benchmarkSeparator_eq_vecMulVec.symm constant_after
  rw [lastDifferenceMinor_eq_submatrix series RunLengthHankel.benchmarkSeparator
    (scale • RunLengthHankel.benchmarkDataC) lastTime dataDeviationRow
    deviationColumn last_value]
  change (dataCDeviationMinor scale).det ≠ 0
  rw [dataCDeviationMinor_det]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 2 scale_ne_zero)

/-- The six possible assignments of three named roles to times zero, one, and two. -/
def permutesZeroOneTwo (toggleTime dataBTime dataCTime : Nat) : Prop :=
  (toggleTime = 0 ∧ dataBTime = 1 ∧ dataCTime = 2) ∨
  (toggleTime = 0 ∧ dataBTime = 2 ∧ dataCTime = 1) ∨
  (toggleTime = 1 ∧ dataBTime = 0 ∧ dataCTime = 2) ∨
  (toggleTime = 1 ∧ dataBTime = 2 ∧ dataCTime = 0) ∨
  (toggleTime = 2 ∧ dataBTime = 0 ∧ dataCTime = 1) ∨
  (toggleTime = 2 ∧ dataBTime = 1 ∧ dataCTime = 0)

/-- Three distinct natural-number positions either occupy exactly zero, one, and two, or one
of them is late enough for the four-block obstruction. -/
theorem distinct_positions_permute_zero_one_two_or_late
    (toggleTime dataBTime dataCTime : Nat)
    (toggle_ne_dataB : toggleTime ≠ dataBTime)
    (toggle_ne_dataC : toggleTime ≠ dataCTime)
    (dataB_ne_dataC : dataBTime ≠ dataCTime) :
    permutesZeroOneTwo toggleTime dataBTime dataCTime ∨
      3 ≤ toggleTime ∨ 3 ≤ dataBTime ∨ 3 ≤ dataCTime := by
  unfold permutesZeroOneTwo
  omega

/-- An exact transfer realization placing the three benchmark roles at distinct times either
uses the consecutive times zero, one, and two, or has at least eleven ambient states.  The
constant-tail hypothesis starts only after all three named positions. -/
theorem permutes_zero_one_two_or_eleven_le_card_of_sparse_benchmark_moments
    {State : Type*} [Fintype State] [DecidableEq State]
    (series : Nat → Matrix (Fin 4) (Fin 4) ℚ)
    (transition : Matrix State State ℚ)
    (input : Matrix State (Fin 4) ℚ) (output : Matrix (Fin 4) State ℚ)
    (toggleTime dataBTime dataCTime : Nat)
    (toggleScale dataBScale dataCScale : ℚ)
    (toggle_ne_dataB : toggleTime ≠ dataBTime)
    (toggle_ne_dataC : toggleTime ≠ dataCTime)
    (dataB_ne_dataC : dataBTime ≠ dataCTime)
    (toggleScale_ne_zero : toggleScale ≠ 0)
    (dataBScale_ne_zero : dataBScale ≠ 0)
    (dataCScale_ne_zero : dataCScale ≠ 0)
    (moments : ∀ time, output * transition ^ time * input = series time)
    (toggle_value :
      series toggleTime = toggleScale • RunLengthHankel.benchmarkToggle)
    (dataB_value :
      series dataBTime = dataBScale • RunLengthHankel.benchmarkDataB)
    (dataC_value :
      series dataCTime = dataCScale • RunLengthHankel.benchmarkDataC)
    (constant_beyond_roles : ∀ time,
      toggleTime < time → dataBTime < time → dataCTime < time →
        series time = RunLengthHankel.benchmarkSeparator) :
    permutesZeroOneTwo toggleTime dataBTime dataCTime ∨
      11 ≤ Fintype.card State := by
  rcases distinct_positions_permute_zero_one_two_or_late toggleTime dataBTime
      dataCTime toggle_ne_dataB toggle_ne_dataC dataB_ne_dataC with
    consecutive | late
  · exact Or.inl consecutive
  · right
    by_cases dataB_le_toggle : dataBTime ≤ toggleTime
    · by_cases dataC_le_toggle : dataCTime ≤ toggleTime
      · have three_le_toggle : 3 ≤ toggleTime := by
          rcases late with toggle_late | dataB_late | dataC_late <;> omega
        apply eleven_le_card_of_late_toggle_moment series transition input output
          toggleTime toggleScale three_le_toggle toggleScale_ne_zero moments toggle_value
        intro time toggle_lt_time
        exact constant_beyond_roles time toggle_lt_time
          (dataB_le_toggle.trans_lt toggle_lt_time)
          (dataC_le_toggle.trans_lt toggle_lt_time)
      · have toggle_lt_dataC : toggleTime < dataCTime :=
          Nat.lt_of_not_ge dataC_le_toggle
        have dataB_lt_dataC : dataBTime < dataCTime :=
          dataB_le_toggle.trans_lt toggle_lt_dataC
        have three_le_dataC : 3 ≤ dataCTime := by
          rcases late with toggle_late | dataB_late | dataC_late <;> omega
        apply eleven_le_card_of_late_dataC_moment series transition input output
          dataCTime dataCScale three_le_dataC dataCScale_ne_zero moments dataC_value
        intro time dataC_lt_time
        exact constant_beyond_roles time
          (toggle_lt_dataC.trans dataC_lt_time)
          (dataB_lt_dataC.trans dataC_lt_time) dataC_lt_time
    · have toggle_lt_dataB : toggleTime < dataBTime :=
        Nat.lt_of_not_ge dataB_le_toggle
      by_cases dataC_le_dataB : dataCTime ≤ dataBTime
      · have three_le_dataB : 3 ≤ dataBTime := by
          rcases late with toggle_late | dataB_late | dataC_late <;> omega
        apply eleven_le_card_of_late_dataB_moment series transition input output
          dataBTime dataBScale three_le_dataB dataBScale_ne_zero moments dataB_value
        intro time dataB_lt_time
        exact constant_beyond_roles time
          (toggle_lt_dataB.trans dataB_lt_time) dataB_lt_time
          (dataC_le_dataB.trans_lt dataB_lt_time)
      · have dataB_lt_dataC : dataBTime < dataCTime :=
          Nat.lt_of_not_ge dataC_le_dataB
        have toggle_lt_dataC : toggleTime < dataCTime :=
          toggle_lt_dataB.trans dataB_lt_dataC
        have three_le_dataC : 3 ≤ dataCTime := by
          rcases late with toggle_late | dataB_late | dataC_late <;> omega
        apply eleven_le_card_of_late_dataC_moment series transition input output
          dataCTime dataCScale three_le_dataC dataCScale_ne_zero moments dataC_value
        intro time dataC_lt_time
        exact constant_beyond_roles time
          (toggle_lt_dataC.trans dataC_lt_time)
          (dataB_lt_dataC.trans dataC_lt_time) dataC_lt_time

end SparseTransferHankel

end MatrixMortality
