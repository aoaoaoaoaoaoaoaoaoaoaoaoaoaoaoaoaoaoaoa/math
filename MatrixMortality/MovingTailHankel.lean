import MatrixMortality.SparseTransferHankel

/-!
# Moving-tail transfer-Hankel obstruction

Subtracting an independently realized tail adds its state dimension rather than one rank-one
coordinate. If the difference series vanishes after time `m` and its last value has a
nonsingular three-dimensional minor, all `m+1` reversed time blocks lie on the diagonal of a
nonsingular section. The two realization dimensions therefore sum to at least `3(m+1)`.
-/

namespace MatrixMortality

open scoped Matrix

namespace MovingTailHankel

/-- All reversed time blocks through the last exceptional moment. -/
abbrev BlockIndex (lastTime : Nat) := Fin (lastTime + 1) × Fin 3

/-- The selected block-Hankel section of one series minus a comparison tail. -/
def differenceSection
    {Interface K : Type*} [Sub K]
    (series tailSeries : Nat → Matrix Interface Interface K) (lastTime : Nat)
    (rowCoordinate columnCoordinate : Fin 3 → Interface) :
    Matrix (BlockIndex lastTime) (BlockIndex lastTime) K :=
  fun row column =>
    (series (row.1.val + (lastTime - column.1.val)) -
      tailSeries (row.1.val + (lastTime - column.1.val)))
      (rowCoordinate row.2) (columnCoordinate column.2)

/-- Identify one variable time block's coordinate fibre with `Fin 3`. -/
def blockFiberEquiv (lastTime : Nat) (block : Fin (lastTime + 1)) :
    {index : BlockIndex lastTime // index.1 = block} ≃ Fin 3 where
  toFun index := index.1.2
  invFun coordinate := ⟨(block, coordinate), rfl⟩
  left_inv index := by
    apply Subtype.ext
    exact Prod.ext index.2.symm rfl
  right_inv _ := rfl

theorem differenceSection_blockTriangular
    {Interface K : Type*} [AddGroup K]
    (series tailSeries : Nat → Matrix Interface Interface K) (lastTime : Nat)
    (rowCoordinate columnCoordinate : Fin 3 → Interface)
    (equal_after : ∀ time, lastTime < time → series time = tailSeries time) :
    (differenceSection series tailSeries lastTime
      rowCoordinate columnCoordinate).BlockTriangular Prod.fst := by
  intro row column column_lt_row
  have columnTime_le : column.1.val ≤ lastTime := by omega
  have exponent_gt :
      lastTime < row.1.val + (lastTime - column.1.val) := by
    have column_lt_row_val : column.1.val < row.1.val := column_lt_row
    omega
  rw [differenceSection, equal_after _ exponent_gt]
  simp

theorem reindex_differenceSection_diagonal
    {Interface K : Type*} [AddGroup K]
    (series tailSeries : Nat → Matrix Interface Interface K) (lastTime : Nat)
    (rowCoordinate columnCoordinate : Fin 3 → Interface)
    (block : Fin (lastTime + 1)) :
    Matrix.reindex (blockFiberEquiv lastTime block) (blockFiberEquiv lastTime block)
        ((differenceSection series tailSeries lastTime
          rowCoordinate columnCoordinate).toSquareBlock Prod.fst block) =
      SparseTransferHankel.lastDifferenceMinor series (tailSeries lastTime) lastTime
        rowCoordinate columnCoordinate := by
  ext row column
  have blockTime_le : block.val ≤ lastTime := by omega
  have exponent_eq : block.val + (lastTime - block.val) = lastTime := by omega
  simp [Matrix.reindex_apply, Matrix.toSquareBlock_def, blockFiberEquiv,
    differenceSection, SparseTransferHankel.lastDifferenceMinor, exponent_eq]

theorem differenceSection_det_ne_zero
    {Interface K : Type*} [Field K]
    (series tailSeries : Nat → Matrix Interface Interface K) (lastTime : Nat)
    (rowCoordinate columnCoordinate : Fin 3 → Interface)
    (equal_after : ∀ time, lastTime < time → series time = tailSeries time)
    (last_minor_det_ne_zero :
      (SparseTransferHankel.lastDifferenceMinor series (tailSeries lastTime) lastTime
        rowCoordinate columnCoordinate).det ≠ 0) :
    (differenceSection series tailSeries lastTime
      rowCoordinate columnCoordinate).det ≠ 0 := by
  have blockTriangular :=
    differenceSection_blockTriangular series tailSeries lastTime
      rowCoordinate columnCoordinate equal_after
  rw [blockTriangular.det_fintype]
  apply Finset.prod_ne_zero_iff.mpr
  intro block _
  rw [← Matrix.det_reindex_self (blockFiberEquiv lastTime block)]
  rw [reindex_differenceSection_diagonal series tailSeries lastTime
    rowCoordinate columnCoordinate block]
  exact last_minor_det_ne_zero

/-- Selected future factors for every time through `lastTime`. -/
def futureFactor
    {Interface State K : Type*} [Semiring K]
    [Fintype State] [DecidableEq State]
    (transition : Matrix State State K) (output : Matrix Interface State K)
    (lastTime : Nat) (rowCoordinate : Fin 3 → Interface) :
    Matrix (BlockIndex lastTime) State K :=
  fun index state =>
    (output * transition ^ index.1.val) (rowCoordinate index.2) state

/-- Selected past factors at the reversed times ending at `lastTime`. -/
def pastFactor
    {Interface State K : Type*} [Semiring K]
    [Fintype State] [DecidableEq State]
    (transition : Matrix State State K) (input : Matrix State Interface K)
    (lastTime : Nat) (columnCoordinate : Fin 3 → Interface) :
    Matrix State (BlockIndex lastTime) K :=
  fun state index =>
    (transition ^ (lastTime - index.1.val) * input)
      state (columnCoordinate index.2)

theorem differenceSection_factor
    {Interface State TailState K : Type*} [CommRing K]
    [Fintype State] [DecidableEq State]
    [Fintype TailState] [DecidableEq TailState]
    (series tailSeries : Nat → Matrix Interface Interface K)
    (transition : Matrix State State K)
    (input : Matrix State Interface K) (output : Matrix Interface State K)
    (tailTransition : Matrix TailState TailState K)
    (tailInput : Matrix TailState Interface K)
    (tailOutput : Matrix Interface TailState K)
    (lastTime : Nat) (rowCoordinate columnCoordinate : Fin 3 → Interface)
    (moments : ∀ time, output * transition ^ time * input = series time)
    (tail_moments : ∀ time,
      tailOutput * tailTransition ^ time * tailInput = tailSeries time) :
    differenceSection series tailSeries lastTime rowCoordinate columnCoordinate =
      futureFactor transition output lastTime rowCoordinate *
          pastFactor transition input lastTime columnCoordinate -
        futureFactor tailTransition tailOutput lastTime rowCoordinate *
          pastFactor tailTransition tailInput lastTime columnCoordinate := by
  ext row column
  change
    (series (row.1.val + (lastTime - column.1.val)) -
      tailSeries (row.1.val + (lastTime - column.1.val)))
        (rowCoordinate row.2) (columnCoordinate column.2) =
      ((output * transition ^ row.1.val) *
          (transition ^ (lastTime - column.1.val) * input))
          (rowCoordinate row.2) (columnCoordinate column.2) -
        ((tailOutput * tailTransition ^ row.1.val) *
          (tailTransition ^ (lastTime - column.1.val) * tailInput))
          (rowCoordinate row.2) (columnCoordinate column.2)
  rw [← moments, ← tail_moments]
  simp only [Matrix.sub_apply, pow_add, Matrix.mul_assoc]

/-- Join two left factors, negating the comparison-tail factor. -/
def differenceLeftFactor
    {Index State TailState K : Type*} [Neg K]
    (left : Matrix Index State K) (tailLeft : Matrix Index TailState K) :
    Matrix Index (State ⊕ TailState) K
  | index, Sum.inl state => left index state
  | index, Sum.inr state => -tailLeft index state

/-- Join the corresponding right factors. -/
def differenceRightFactor
    {Index State TailState K : Type*}
    (right : Matrix State Index K) (tailRight : Matrix TailState Index K) :
    Matrix (State ⊕ TailState) Index K
  | Sum.inl state, index => right state index
  | Sum.inr state, index => tailRight state index

theorem differenceLeftFactor_mul_differenceRightFactor
    {Index State TailState K : Type*} [CommRing K]
    [Fintype State] [Fintype TailState]
    (left : Matrix Index State K) (right : Matrix State Index K)
    (tailLeft : Matrix Index TailState K) (tailRight : Matrix TailState Index K) :
    differenceLeftFactor left tailLeft * differenceRightFactor right tailRight =
      left * right - tailLeft * tailRight := by
  ext row column
  simp [differenceLeftFactor, differenceRightFactor, Matrix.mul_apply,
    Fintype.sum_sum_type]
  ring

/-- A nonsingular difference of two rectangular products factors through the sum of their
intermediate state spaces. -/
theorem card_le_add_of_difference_det_ne_zero
    {Index State TailState K : Type*} [Field K]
    [Fintype Index] [DecidableEq Index]
    [Fintype State] [Fintype TailState]
    (left : Matrix Index State K) (right : Matrix State Index K)
    (tailLeft : Matrix Index TailState K) (tailRight : Matrix TailState Index K)
    (difference_det_ne_zero :
      (left * right - tailLeft * tailRight).det ≠ 0) :
    Fintype.card Index ≤ Fintype.card State + Fintype.card TailState := by
  have combined_det_ne_zero :
      (differenceLeftFactor left tailLeft *
        differenceRightFactor right tailRight).det ≠ 0 := by
    rw [differenceLeftFactor_mul_differenceRightFactor]
    exact difference_det_ne_zero
  have cardinal_bound :=
    card_le_of_det_rectangular_product_ne_zero
      (differenceLeftFactor left tailLeft)
      (differenceRightFactor right tailRight) combined_det_ne_zero
  simpa [Fintype.card_sum] using cardinal_bound

/-- If two exact transfer series agree after time `m` and their last difference has a
nonsingular `3 × 3` minor, their realization dimensions sum to at least `3(m+1)`. -/
theorem three_mul_succ_le_card_add_card_of_late_rank_three_difference
    {Interface State TailState K : Type*} [Field K]
    [Fintype State] [DecidableEq State]
    [Fintype TailState] [DecidableEq TailState]
    (series tailSeries : Nat → Matrix Interface Interface K)
    (transition : Matrix State State K)
    (input : Matrix State Interface K) (output : Matrix Interface State K)
    (tailTransition : Matrix TailState TailState K)
    (tailInput : Matrix TailState Interface K)
    (tailOutput : Matrix Interface TailState K)
    (lastTime : Nat) (rowCoordinate columnCoordinate : Fin 3 → Interface)
    (moments : ∀ time, output * transition ^ time * input = series time)
    (tail_moments : ∀ time,
      tailOutput * tailTransition ^ time * tailInput = tailSeries time)
    (equal_after : ∀ time, lastTime < time → series time = tailSeries time)
    (last_minor_det_ne_zero :
      (SparseTransferHankel.lastDifferenceMinor series (tailSeries lastTime) lastTime
        rowCoordinate columnCoordinate).det ≠ 0) :
    3 * (lastTime + 1) ≤ Fintype.card State + Fintype.card TailState := by
  have section_det_ne_zero :=
    differenceSection_det_ne_zero series tailSeries lastTime
      rowCoordinate columnCoordinate equal_after last_minor_det_ne_zero
  have factored_det_ne_zero :
      (futureFactor transition output lastTime rowCoordinate *
          pastFactor transition input lastTime columnCoordinate -
        futureFactor tailTransition tailOutput lastTime rowCoordinate *
          pastFactor tailTransition tailInput lastTime columnCoordinate).det ≠ 0 := by
    rw [← differenceSection_factor series tailSeries transition input output
      tailTransition tailInput tailOutput lastTime rowCoordinate columnCoordinate
      moments tail_moments]
    exact section_det_ne_zero
  have cardinal_bound :=
    card_le_add_of_difference_det_ne_zero
      (futureFactor transition output lastTime rowCoordinate)
      (pastFactor transition input lastTime columnCoordinate)
      (futureFactor tailTransition tailOutput lastTime rowCoordinate)
      (pastFactor tailTransition tailInput lastTime columnCoordinate)
      factored_det_ne_zero
  simpa [BlockIndex, Nat.mul_comm] using cardinal_bound

/-- A tail of realization dimension at most two cannot hide a rank-three exception at time at
least three inside fewer than ten ambient states. -/
theorem ten_le_card_of_late_rank_three_difference_of_tail_card_le_two
    {Interface State TailState K : Type*} [Field K]
    [Fintype State] [DecidableEq State]
    [Fintype TailState] [DecidableEq TailState]
    (series tailSeries : Nat → Matrix Interface Interface K)
    (transition : Matrix State State K)
    (input : Matrix State Interface K) (output : Matrix Interface State K)
    (tailTransition : Matrix TailState TailState K)
    (tailInput : Matrix TailState Interface K)
    (tailOutput : Matrix Interface TailState K)
    (lastTime : Nat) (rowCoordinate columnCoordinate : Fin 3 → Interface)
    (three_le_lastTime : 3 ≤ lastTime)
    (tail_card_le_two : Fintype.card TailState ≤ 2)
    (moments : ∀ time, output * transition ^ time * input = series time)
    (tail_moments : ∀ time,
      tailOutput * tailTransition ^ time * tailInput = tailSeries time)
    (equal_after : ∀ time, lastTime < time → series time = tailSeries time)
    (last_minor_det_ne_zero :
      (SparseTransferHankel.lastDifferenceMinor series (tailSeries lastTime) lastTime
        rowCoordinate columnCoordinate).det ≠ 0) :
    10 ≤ Fintype.card State := by
  have dimension_tax :=
    three_mul_succ_le_card_add_card_of_late_rank_three_difference
      series tailSeries transition input output tailTransition tailInput tailOutput
      lastTime rowCoordinate columnCoordinate moments tail_moments equal_after
      last_minor_det_ne_zero
  omega

/-- A late toggle against an independently realized tail of dimension at most two cannot fit
inside nine ambient states when the comparison tail equals the absorbed separator at the
exception. -/
theorem ten_le_card_of_late_toggle_against_small_tail
    {State TailState : Type*}
    [Fintype State] [DecidableEq State]
    [Fintype TailState] [DecidableEq TailState]
    (series tailSeries : Nat → Matrix (Fin 4) (Fin 4) ℚ)
    (transition : Matrix State State ℚ)
    (input : Matrix State (Fin 4) ℚ) (output : Matrix (Fin 4) State ℚ)
    (tailTransition : Matrix TailState TailState ℚ)
    (tailInput : Matrix TailState (Fin 4) ℚ)
    (tailOutput : Matrix (Fin 4) TailState ℚ)
    (lastTime : Nat) (scale : ℚ)
    (three_le_lastTime : 3 ≤ lastTime)
    (tail_card_le_two : Fintype.card TailState ≤ 2)
    (scale_ne_zero : scale ≠ 0)
    (moments : ∀ time, output * transition ^ time * input = series time)
    (tail_moments : ∀ time,
      tailOutput * tailTransition ^ time * tailInput = tailSeries time)
    (equal_after : ∀ time, lastTime < time → series time = tailSeries time)
    (last_value :
      series lastTime = scale • RunLengthHankel.benchmarkToggle)
    (tail_last_value :
      tailSeries lastTime = RunLengthHankel.benchmarkSeparator) :
    10 ≤ Fintype.card State := by
  apply ten_le_card_of_late_rank_three_difference_of_tail_card_le_two
    series tailSeries transition input output tailTransition tailInput tailOutput
    lastTime SparseTransferHankel.toggleDeviationRow
    SparseTransferHankel.deviationColumn three_le_lastTime tail_card_le_two
    moments tail_moments equal_after
  rw [SparseTransferHankel.lastDifferenceMinor_eq_submatrix series
    (tailSeries lastTime) (scale • RunLengthHankel.benchmarkToggle) lastTime
    SparseTransferHankel.toggleDeviationRow SparseTransferHankel.deviationColumn
    last_value, tail_last_value]
  change (SparseTransferHankel.toggleDeviationMinor scale).det ≠ 0
  rw [SparseTransferHankel.toggleDeviationMinor_det]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 2 scale_ne_zero)

/-- A late data-`b` role has the same ten-state lower bound against a tail of realization
dimension at most two. -/
theorem ten_le_card_of_late_dataB_against_small_tail
    {State TailState : Type*}
    [Fintype State] [DecidableEq State]
    [Fintype TailState] [DecidableEq TailState]
    (series tailSeries : Nat → Matrix (Fin 4) (Fin 4) ℚ)
    (transition : Matrix State State ℚ)
    (input : Matrix State (Fin 4) ℚ) (output : Matrix (Fin 4) State ℚ)
    (tailTransition : Matrix TailState TailState ℚ)
    (tailInput : Matrix TailState (Fin 4) ℚ)
    (tailOutput : Matrix (Fin 4) TailState ℚ)
    (lastTime : Nat) (scale : ℚ)
    (three_le_lastTime : 3 ≤ lastTime)
    (tail_card_le_two : Fintype.card TailState ≤ 2)
    (scale_ne_zero : scale ≠ 0)
    (moments : ∀ time, output * transition ^ time * input = series time)
    (tail_moments : ∀ time,
      tailOutput * tailTransition ^ time * tailInput = tailSeries time)
    (equal_after : ∀ time, lastTime < time → series time = tailSeries time)
    (last_value :
      series lastTime = scale • RunLengthHankel.benchmarkDataB)
    (tail_last_value :
      tailSeries lastTime = RunLengthHankel.benchmarkSeparator) :
    10 ≤ Fintype.card State := by
  apply ten_le_card_of_late_rank_three_difference_of_tail_card_le_two
    series tailSeries transition input output tailTransition tailInput tailOutput
    lastTime SparseTransferHankel.dataDeviationRow
    SparseTransferHankel.deviationColumn three_le_lastTime tail_card_le_two
    moments tail_moments equal_after
  rw [SparseTransferHankel.lastDifferenceMinor_eq_submatrix series
    (tailSeries lastTime) (scale • RunLengthHankel.benchmarkDataB) lastTime
    SparseTransferHankel.dataDeviationRow SparseTransferHankel.deviationColumn
    last_value, tail_last_value]
  change (SparseTransferHankel.dataBDeviationMinor scale).det ≠ 0
  rw [SparseTransferHankel.dataBDeviationMinor_det]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 2 scale_ne_zero)

/-- A late data-`c` role has the same ten-state lower bound against a tail of realization
dimension at most two. -/
theorem ten_le_card_of_late_dataC_against_small_tail
    {State TailState : Type*}
    [Fintype State] [DecidableEq State]
    [Fintype TailState] [DecidableEq TailState]
    (series tailSeries : Nat → Matrix (Fin 4) (Fin 4) ℚ)
    (transition : Matrix State State ℚ)
    (input : Matrix State (Fin 4) ℚ) (output : Matrix (Fin 4) State ℚ)
    (tailTransition : Matrix TailState TailState ℚ)
    (tailInput : Matrix TailState (Fin 4) ℚ)
    (tailOutput : Matrix (Fin 4) TailState ℚ)
    (lastTime : Nat) (scale : ℚ)
    (three_le_lastTime : 3 ≤ lastTime)
    (tail_card_le_two : Fintype.card TailState ≤ 2)
    (scale_ne_zero : scale ≠ 0)
    (moments : ∀ time, output * transition ^ time * input = series time)
    (tail_moments : ∀ time,
      tailOutput * tailTransition ^ time * tailInput = tailSeries time)
    (equal_after : ∀ time, lastTime < time → series time = tailSeries time)
    (last_value :
      series lastTime = scale • RunLengthHankel.benchmarkDataC)
    (tail_last_value :
      tailSeries lastTime = RunLengthHankel.benchmarkSeparator) :
    10 ≤ Fintype.card State := by
  apply ten_le_card_of_late_rank_three_difference_of_tail_card_le_two
    series tailSeries transition input output tailTransition tailInput tailOutput
    lastTime SparseTransferHankel.dataDeviationRow
    SparseTransferHankel.deviationColumn three_le_lastTime tail_card_le_two
    moments tail_moments equal_after
  rw [SparseTransferHankel.lastDifferenceMinor_eq_submatrix series
    (tailSeries lastTime) (scale • RunLengthHankel.benchmarkDataC) lastTime
    SparseTransferHankel.dataDeviationRow SparseTransferHankel.deviationColumn
    last_value, tail_last_value]
  change (SparseTransferHankel.dataCDeviationMinor scale).det ≠ 0
  rw [SparseTransferHankel.dataCDeviationMinor_det]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 2 scale_ne_zero)

end MovingTailHankel

end MatrixMortality
