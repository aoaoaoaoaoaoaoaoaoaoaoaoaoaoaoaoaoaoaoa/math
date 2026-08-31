import MatrixMortality.TransverseLineAtlas

/-!
# A nonprojective toggle generates infinitely many transverse carriers

The diagonal toggle with eigenvalues `1`, `2`, and `3` sends one explicit rank-two data image
through infinitely many distinct rational planes. This is the sharp counterexample to extending
the finite-carrier theorem of `TransverseLineAtlas` beyond projectively involutive toggles.
-/

namespace MatrixMortality
namespace TransverseInfiniteAtlas

open scoped Matrix

abbrev Interface := Fin 2
abbrev State := Fin 3 → ℚ
abbrev ControlMatrix := Matrix (Fin 3) (Fin 3) ℚ

/-- Diagonal toggle with three distinct rational eigenvalues. -/
def toggle : ControlMatrix :=
  !![1, 0, 0;
     0, 2, 0;
     0, 0, 3]

/-- Two independent columns spanning the source-parameter plane. -/
def dataInput (source : ℚ) : Matrix (Fin 3) Interface ℚ :=
  !![1, source;
     -1, 0;
     0, -1]

/-- Projection selecting the two active input coordinates. -/
def dataProjection : Matrix Interface (Fin 3) ℚ :=
  !![1, 0, 0;
     0, 1, 0]

/-- Left inverse of `dataInput`. -/
def dataLeftInverse : Matrix Interface (Fin 3) ℚ :=
  !![0, -1, 0;
     0, 0, -1]

/-- Right inverse of `dataProjection`. -/
def dataSection : Matrix (Fin 3) Interface ℚ :=
  !![1, 0;
     0, 1;
     0, 0]

/-- Rank-two data map whose image has normal `(1,1,source)`. -/
def data (source : ℚ) : ControlMatrix :=
  dataInput source * dataProjection

theorem dataLeftInverse_mul_dataInput (source : ℚ) :
    dataLeftInverse * dataInput source = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [dataLeftInverse, dataInput, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_succ]

theorem dataProjection_mul_dataSection : dataProjection * dataSection = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [dataProjection, dataSection, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_succ]

/-- The data map has rank exactly two for every source parameter. -/
theorem data_rank_eq_two (source : ℚ) : (data source).rank = 2 := by
  apply le_antisymm
  · calc
      (data source).rank ≤ (dataInput source).rank := by
        exact Matrix.rank_mul_le_left (dataInput source) dataProjection
      _ ≤ Fintype.card Interface := Matrix.rank_le_width (dataInput source)
      _ = 2 := by norm_num
  · have fullSplit : dataLeftInverse * data source * dataSection = 1 := by
      rw [data]
      simp only [Matrix.mul_assoc]
      rw [dataProjection_mul_dataSection, Matrix.mul_one,
        dataLeftInverse_mul_dataInput]
    have outerBound := Matrix.rank_mul_le_left (dataLeftInverse * data source) dataSection
    rw [fullSplit, Matrix.rank_one] at outerBound
    have innerBound := Matrix.rank_mul_le_right dataLeftInverse (data source)
    norm_num at outerBound ⊢
    exact outerBound.trans innerBound

theorem data_det (source : ℚ) : (data source).det = 0 := by
  by_contra det_ne
  have dataUnit : IsUnit (data source) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact det_ne
  have fullRank : (data source).rank = 3 := by
    apply Matrix.rank_of_isUnit
    exact dataUnit
  rw [data_rank_eq_two] at fullRank
  omega

/-- Closed form of the diagonal toggle powers. -/
def togglePower (power : Nat) : ControlMatrix :=
  !![1, 0, 0;
     0, (2 : ℚ) ^ power, 0;
     0, 0, (3 : ℚ) ^ power]

theorem toggle_pow (power : Nat) : toggle ^ power = togglePower power := by
  induction power with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [togglePower, Matrix.one_apply]
  | succ power induction =>
      rw [pow_succ, induction]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [togglePower, toggle, Matrix.mul_apply, Fin.sum_univ_succ, pow_succ]

theorem toggle_det : toggle.det = 6 := by
  norm_num [toggle, Matrix.det_fin_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]

theorem toggle_pow_det (power : Nat) : (toggle ^ power).det = (6 : ℚ) ^ power := by
  rw [Matrix.det_pow, toggle_det]

/-- The toggle is not projectively involutive: its square is no scalar matrix. -/
theorem toggle_sq_ne_smul_one (scalar : ℚ) : toggle * toggle ≠ scalar • 1 := by
  intro square
  have first := congrArg (fun matrix : ControlMatrix => matrix 0 0) square
  have second := congrArg (fun matrix : ControlMatrix => matrix 1 1) square
  norm_num [toggle, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] at first second
  linarith

/-- Carrier matrix reached after `power` leading toggles and one data control. -/
def carrierMatrix (source : ℚ) (power : Nat) : ControlMatrix :=
  toggle ^ power * data source

/-- Every carrier matrix retains exact rank two. -/
theorem carrierMatrix_rank_eq_two (source : ℚ) (power : Nat) :
    (carrierMatrix source power).rank = 2 := by
  rw [carrierMatrix,
    Matrix.rank_mul_eq_right_of_det_ne_zero (toggle ^ power) (data source)]
  · exact data_rank_eq_two source
  · rw [toggle_pow_det]
    exact pow_ne_zero _ (by norm_num)

/-- Integral normal of the carrier plane. -/
def normal (source : ℚ) (power : Nat) : State :=
  ![(6 : ℚ) ^ power, (3 : ℚ) ^ power, source * (2 : ℚ) ^ power]

/-- A distinguished vector in the carrier plane. -/
def witness (power : Nat) : State :=
  ![1, -(2 : ℚ) ^ power, 0]

/-- Input column which produces the distinguished carrier vector. -/
def witnessInput : State := ![1, 0, 0]

/-- The second spanning vector of the source-parameter carrier. -/
def sourceWitness (source : ℚ) (power : Nat) : State :=
  ![source, 0, -(3 : ℚ) ^ power]

/-- Input column which produces `sourceWitness`. -/
def sourceWitnessInput : State := ![0, 1, 0]

theorem carrierMatrix_mulVec (source : ℚ) (power : Nat) (state : State) :
    carrierMatrix source power *ᵥ state =
      ![state 0 + source * state 1,
        -(2 : ℚ) ^ power * state 0,
        -(3 : ℚ) ^ power * state 1] := by
  rw [carrierMatrix, toggle_pow]
  ext i
  fin_cases i <;>
    simp [togglePower, data, dataInput, dataProjection, Matrix.mulVec,
      Matrix.mul_apply, dotProduct, Fin.sum_univ_succ]

theorem carrierMatrix_mulVec_witnessInput (source : ℚ) (power : Nat) :
    carrierMatrix source power *ᵥ witnessInput = witness power := by
  rw [carrierMatrix_mulVec]
  ext i
  fin_cases i <;> simp [witnessInput, witness]

theorem carrierMatrix_mulVec_sourceWitnessInput (source : ℚ) (power : Nat) :
    carrierMatrix source power *ᵥ sourceWitnessInput = sourceWitness source power := by
  rw [carrierMatrix_mulVec]
  ext i
  fin_cases i <;> simp [sourceWitnessInput, sourceWitness]

/-- Every vector in the `power`-th carrier is annihilated by its displayed normal. -/
theorem normal_dotProduct_carrierMatrix_mulVec
    (source : ℚ) (power : Nat) (state : State) :
    normal source power ⬝ᵥ (carrierMatrix source power *ᵥ state) = 0 := by
  rw [carrierMatrix_mulVec]
  simp [normal, dotProduct, Fin.sum_univ_succ]
  have sixPower : (6 : ℚ) ^ power = (3 : ℚ) ^ power * (2 : ℚ) ^ power := by
    rw [← mul_pow]
    norm_num
  rw [sixPower]
  ring

/-- Linear carrier of one leading-toggle depth. -/
def carrier (source : ℚ) (power : Nat) : Submodule ℚ State :=
  LinearMap.range (Matrix.toLin' (carrierMatrix source power))

theorem witness_mem_carrier (source : ℚ) (power : Nat) :
    witness power ∈ carrier source power := by
  refine ⟨witnessInput, ?_⟩
  exact carrierMatrix_mulVec_witnessInput source power

theorem sourceWitness_mem_carrier (source : ℚ) (power : Nat) :
    sourceWitness source power ∈ carrier source power := by
  refine ⟨sourceWitnessInput, ?_⟩
  exact carrierMatrix_mulVec_sourceWitnessInput source power

theorem normal_dotProduct_eq_zero_of_mem_carrier
    (source : ℚ) (power : Nat) {state : State}
    (stateInCarrier : state ∈ carrier source power) :
    normal source power ⬝ᵥ state = 0 := by
  obtain ⟨preimage, rfl⟩ := stateInCarrier
  exact normal_dotProduct_carrierMatrix_mulVec source power preimage

/-- A later carrier normal does not annihilate an earlier distinguished vector. -/
theorem normal_dotProduct_witness_ne_zero (source : ℚ) {earlier later : Nat}
    (before : earlier < later) :
    normal source later ⬝ᵥ witness earlier ≠ 0 := by
  have power_lt : (2 : ℚ) ^ earlier < (2 : ℚ) ^ later :=
    pow_lt_pow_right₀ (a := (2 : ℚ)) (by norm_num) before
  have threePower_pos : 0 < (3 : ℚ) ^ later := pow_pos (by norm_num) _
  have product_pos :
      0 < (3 : ℚ) ^ later * ((2 : ℚ) ^ later - (2 : ℚ) ^ earlier) :=
    mul_pos threePower_pos (sub_pos.mpr power_lt)
  intro annihilates
  have sixPower : (6 : ℚ) ^ later = (3 : ℚ) ^ later * (2 : ℚ) ^ later := by
    rw [← mul_pow]
    norm_num
  have expanded :
      (6 : ℚ) ^ later +
        -((3 : ℚ) ^ later * (2 : ℚ) ^ earlier) = 0 := by
    simpa [normal, witness, dotProduct, Fin.sum_univ_succ] using annihilates
  have product_zero :
      (3 : ℚ) ^ later * ((2 : ℚ) ^ later - (2 : ℚ) ^ earlier) = 0 := by
    rw [sixPower] at expanded
    linarith
  linarith

/-- The source-parameter carrier planes are pairwise distinct with increasing toggle depth. -/
theorem carrier_ne_of_lt (source : ℚ) {earlier later : Nat} (before : earlier < later) :
    carrier source earlier ≠ carrier source later := by
  intro carriersEqual
  have witnessInLater : witness earlier ∈ carrier source later := by
    rw [← carriersEqual]
    exact witness_mem_carrier source earlier
  exact normal_dotProduct_witness_ne_zero source before
    (normal_dotProduct_eq_zero_of_mem_carrier source later witnessInLater)

/-- Every rational source parameter produces an injective infinite orbit of rank-two carrier
planes. -/
theorem carrier_injective (source : ℚ) : Function.Injective (carrier source) := by
  intro first second carriersEqual
  rcases lt_trichotomy first second with before | equal | after
  · exact False.elim ((carrier_ne_of_lt source before) carriersEqual)
  · exact equal
  · exact False.elim ((carrier_ne_of_lt source after) carriersEqual.symm)

/-- A row vanishes on one whole carrier plane. -/
def AnnihilatesCarrier (row : State) (source : ℚ) (power : Nat) : Prop :=
  ∀ state ∈ carrier source power, row ⬝ᵥ state = 0

/-- Whole-plane vanishing at two distinct depths forces the terminal row to be zero. -/
theorem row_eq_zero_of_annihilates_two
    (row : State) (source : ℚ) {earlier later : Nat} (before : earlier < later)
    (annihilatesEarlier : AnnihilatesCarrier row source earlier)
    (annihilatesLater : AnnihilatesCarrier row source later) :
    row = 0 := by
  have earlierFirst :=
    annihilatesEarlier (witness earlier) (witness_mem_carrier source earlier)
  have laterFirst :=
    annihilatesLater (witness later) (witness_mem_carrier source later)
  have earlierSecond :=
    annihilatesEarlier (sourceWitness source earlier)
      (sourceWitness_mem_carrier source earlier)
  simp [witness, dotProduct, Fin.sum_univ_succ] at earlierFirst laterFirst
  simp [sourceWitness, dotProduct, Fin.sum_univ_succ] at earlierSecond
  have firstEquation : row 0 = row 1 * (2 : ℚ) ^ earlier := by
    linarith
  have laterEquation : row 0 = row 1 * (2 : ℚ) ^ later := by
    linarith
  have scaledPowersEqual :
      row 1 * (2 : ℚ) ^ earlier = row 1 * (2 : ℚ) ^ later :=
    firstEquation.symm.trans laterEquation
  have factoredDifference :
      row 1 * ((2 : ℚ) ^ earlier - (2 : ℚ) ^ later) = 0 := by
    calc
      row 1 * ((2 : ℚ) ^ earlier - (2 : ℚ) ^ later) =
          row 1 * (2 : ℚ) ^ earlier - row 1 * (2 : ℚ) ^ later := by ring
      _ = 0 := sub_eq_zero.mpr scaledPowersEqual
  have powersDistinct : (2 : ℚ) ^ earlier - (2 : ℚ) ^ later ≠ 0 := by
    apply sub_ne_zero.mpr
    exact ne_of_lt (pow_lt_pow_right₀ (a := (2 : ℚ)) (by norm_num) before)
  have rowOneZero : row 1 = 0 :=
    (mul_eq_zero.mp factoredDifference).resolve_right powersDistinct
  have rowZeroZero : row 0 = 0 := by rw [firstEquation, rowOneZero, zero_mul]
  have rowTwoTimesPower : row 2 * (3 : ℚ) ^ earlier = 0 := by
    rw [rowZeroZero] at earlierSecond
    linarith
  have rowTwoZero : row 2 = 0 :=
    (mul_eq_zero.mp rowTwoTimesPower).resolve_right (pow_ne_zero _ (by norm_num))
  funext coordinate
  fin_cases coordinate
  · exact rowZeroZero
  · exact rowOneZero
  · exact rowTwoZero

/-- A nonzero terminal row can contain at most one whole carrier plane. -/
theorem annihilatesCarrier_at_most_one
    (row : State) (source : ℚ) (row_ne : row ≠ 0) {first second : Nat}
    (annihilatesFirst : AnnihilatesCarrier row source first)
    (annihilatesSecond : AnnihilatesCarrier row source second) :
    first = second := by
  rcases lt_trichotomy first second with before | equal | after
  · exact False.elim (row_ne
      (row_eq_zero_of_annihilates_two row source before annihilatesFirst annihilatesSecond))
  · exact equal
  · exact False.elim (row_ne
      (row_eq_zero_of_annihilates_two row source after annihilatesSecond annihilatesFirst))

/-- The set of whole-carrier depths of a nonzero row is a subsingleton. -/
theorem wholeCarrierDepths_subsingleton (row : State) (source : ℚ) (row_ne : row ≠ 0) :
    Set.Subsingleton {power | AnnihilatesCarrier row source power} := by
  intro first first_mem second second_mem
  exact annihilatesCarrier_at_most_one row source row_ne first_mem second_mem

/-- Generalized-Vandermonde minor governing three zero depths of a `2ⁿ,3ⁿ` scalar. -/
def exponentialMinor (firstGap secondGap : Nat) : ℚ :=
  ((2 : ℚ) ^ firstGap - 1) * ((3 : ℚ) ^ (firstGap + secondGap) - 1) -
    ((3 : ℚ) ^ firstGap - 1) * ((2 : ℚ) ^ (firstGap + secondGap) - 1)

theorem exponentialMinor_pos (firstGap secondGap : Nat)
    (firstGap_pos : 0 < firstGap) (secondGap_pos : 0 < secondGap) :
    0 < exponentialMinor firstGap secondGap := by
  induction secondGap with
  | zero => omega
  | succ gap induction =>
      by_cases gap_zero : gap = 0
      · subst gap
        have twoPower_ge : (2 : ℚ) ≤ (2 : ℚ) ^ firstGap := by
          simpa using pow_le_pow_right₀ (show (1 : ℚ) ≤ 2 by norm_num)
            (Nat.succ_le_iff.mpr firstGap_pos)
        have twoPower_pos : 0 < (2 : ℚ) ^ firstGap := pow_pos (by norm_num) _
        have threePower_nonneg : 0 ≤ (3 : ℚ) ^ firstGap := (pow_pos (by norm_num) _).le
        have product_nonneg :
            0 ≤ (3 : ℚ) ^ firstGap * ((2 : ℚ) ^ firstGap - 2) :=
          mul_nonneg threePower_nonneg (sub_nonneg.mpr twoPower_ge)
        have identity :
            exponentialMinor firstGap 1 =
              (3 : ℚ) ^ firstGap * ((2 : ℚ) ^ firstGap - 2) +
                (2 : ℚ) ^ firstGap := by
          simp only [exponentialMinor, Nat.add_one, pow_succ]
          ring
        rw [identity]
        positivity
      · have gap_pos : 0 < gap := Nat.pos_of_ne_zero gap_zero
        have previous_pos := induction gap_pos
        have twoPower_ge : (2 : ℚ) ≤ (2 : ℚ) ^ firstGap := by
          simpa using pow_le_pow_right₀ (show (1 : ℚ) ≤ 2 by norm_num)
            (Nat.succ_le_iff.mpr firstGap_pos)
        have twoPower_monotone :
            (2 : ℚ) ^ firstGap ≤ (2 : ℚ) ^ (firstGap + gap) := by
          exact pow_le_pow_right₀ (show (1 : ℚ) ≤ 2 by norm_num) (Nat.le_add_right _ _)
        have binaryRemainder_nonneg :
            0 ≤ (2 : ℚ) ^ (firstGap + gap) - 2 :=
          sub_nonneg.mpr (twoPower_ge.trans twoPower_monotone)
        have ternaryRemainder_nonneg :
            0 ≤ (3 : ℚ) ^ firstGap - 1 := by
          exact sub_nonneg.mpr (one_le_pow₀ (by norm_num))
        have recurrence :
            exponentialMinor firstGap (gap + 1) =
              3 * exponentialMinor firstGap gap +
                2 * ((2 : ℚ) ^ firstGap - 1) +
                ((3 : ℚ) ^ firstGap - 1) *
                  ((2 : ℚ) ^ (firstGap + gap) - 2) := by
          simp only [exponentialMinor]
          ring
        rw [recurrence]
        have binaryFirstRemainder_nonneg :
            0 ≤ (2 : ℚ) ^ firstGap - 1 := by
          exact sub_nonneg.mpr (one_le_pow₀ (by norm_num))
        positivity

/-- Three-term exponential scalar obtained from a fixed row-column terminal test. -/
def exponentialScalar (constant binary ternary : ℚ) (power : Nat) : ℚ :=
  constant - binary * (2 : ℚ) ^ power - ternary * (3 : ℚ) ^ power

theorem coefficients_eq_zero_of_three_zeros
    (constant binary ternary : ℚ) (offset firstGap secondGap : Nat)
    (firstGap_pos : 0 < firstGap) (secondGap_pos : 0 < secondGap)
    (zeroAtOffset : exponentialScalar constant binary ternary offset = 0)
    (zeroAtFirst : exponentialScalar constant binary ternary (offset + firstGap) = 0)
    (zeroAtSecond :
      exponentialScalar constant binary ternary (offset + firstGap + secondGap) = 0) :
    constant = 0 ∧ binary = 0 ∧ ternary = 0 := by
  have offsetEquation :
      constant - binary * (2 : ℚ) ^ offset - ternary * (3 : ℚ) ^ offset = 0 := by
    simpa only [exponentialScalar] using zeroAtOffset
  have firstEquation :
      constant - binary * (2 : ℚ) ^ (offset + firstGap) -
        ternary * (3 : ℚ) ^ (offset + firstGap) = 0 := by
    simpa only [exponentialScalar] using zeroAtFirst
  have secondEquation :
      constant - binary * (2 : ℚ) ^ (offset + firstGap + secondGap) -
        ternary * (3 : ℚ) ^ (offset + firstGap + secondGap) = 0 := by
    simpa only [exponentialScalar] using zeroAtSecond
  have firstDifference :
      binary * (2 : ℚ) ^ offset * ((2 : ℚ) ^ firstGap - 1) +
        ternary * (3 : ℚ) ^ offset * ((3 : ℚ) ^ firstGap - 1) = 0 := by
    have expandedFirstEquation :
        constant - binary * ((2 : ℚ) ^ offset * (2 : ℚ) ^ firstGap) -
          ternary * ((3 : ℚ) ^ offset * (3 : ℚ) ^ firstGap) = 0 := by
      simpa only [pow_add] using firstEquation
    linear_combination offsetEquation - expandedFirstEquation
  have secondDifference :
      binary * (2 : ℚ) ^ offset *
          ((2 : ℚ) ^ (firstGap + secondGap) - 1) +
        ternary * (3 : ℚ) ^ offset *
          ((3 : ℚ) ^ (firstGap + secondGap) - 1) = 0 := by
    have expandedSecondEquation :
        constant -
            binary * ((2 : ℚ) ^ offset * (2 : ℚ) ^ (firstGap + secondGap)) -
          ternary * ((3 : ℚ) ^ offset * (3 : ℚ) ^ (firstGap + secondGap)) = 0 := by
      simpa only [Nat.add_assoc, pow_add] using secondEquation
    linear_combination offsetEquation - expandedSecondEquation
  have ternary_times_minor :
      ternary * (3 : ℚ) ^ offset * exponentialMinor firstGap secondGap = 0 := by
    simp only [exponentialMinor, pow_add]
    linear_combination
      ((2 : ℚ) ^ firstGap - 1) * secondDifference -
        ((2 : ℚ) ^ (firstGap + secondGap) - 1) * firstDifference
  have minor_ne : exponentialMinor firstGap secondGap ≠ 0 :=
    ne_of_gt (exponentialMinor_pos firstGap secondGap firstGap_pos secondGap_pos)
  have ternary_zero : ternary = 0 := by
    rcases mul_eq_zero.mp ternary_times_minor with product_zero | minor_zero
    · rcases mul_eq_zero.mp product_zero with ternary_zero | threePower_zero
      · exact ternary_zero
      · exact False.elim ((pow_ne_zero _ (by norm_num)) threePower_zero)
    · exact False.elim (minor_ne minor_zero)
  have firstBinaryProduct :
      binary * (2 : ℚ) ^ offset * ((2 : ℚ) ^ firstGap - 1) = 0 := by
    simpa only [ternary_zero, zero_mul, add_zero] using firstDifference
  have firstGapPower_ne : (2 : ℚ) ^ firstGap - 1 ≠ 0 := by
    have one_lt : (1 : ℚ) < (2 : ℚ) ^ firstGap := by
      exact one_lt_pow₀ (by norm_num) (Nat.ne_of_gt firstGap_pos)
    exact sub_ne_zero.mpr (ne_of_gt one_lt)
  have binary_zero : binary = 0 := by
    rcases mul_eq_zero.mp firstBinaryProduct with product_zero | gapPower_zero
    · rcases mul_eq_zero.mp product_zero with binary_zero | offsetPower_zero
      · exact binary_zero
      · exact False.elim ((pow_ne_zero _ (by norm_num)) offsetPower_zero)
    · exact False.elim (firstGapPower_ne gapPower_zero)
  have constant_zero : constant = 0 := by
    simpa only [exponentialScalar, binary_zero, ternary_zero, zero_mul, sub_zero] using
      zeroAtOffset
  exact ⟨constant_zero, binary_zero, ternary_zero⟩

theorem no_three_ordered_zeros
    (constant binary ternary : ℚ)
    (nonidentity : ¬ (constant = 0 ∧ binary = 0 ∧ ternary = 0))
    {first middle last : Nat} (first_lt_middle : first < middle)
    (middle_lt_last : middle < last)
    (zeroAtFirst : exponentialScalar constant binary ternary first = 0)
    (zeroAtMiddle : exponentialScalar constant binary ternary middle = 0)
    (zeroAtLast : exponentialScalar constant binary ternary last = 0) : False := by
  have firstGap_pos : 0 < middle - first := by omega
  have secondGap_pos : 0 < last - middle := by omega
  have middle_eq : first + (middle - first) = middle := by omega
  have last_eq : first + (middle - first) + (last - middle) = last := by omega
  apply nonidentity
  apply coefficients_eq_zero_of_three_zeros constant binary ternary first
    (middle - first) (last - middle) firstGap_pos secondGap_pos zeroAtFirst
  · simpa only [middle_eq] using zeroAtMiddle
  · simpa only [last_eq] using zeroAtLast

theorem three_zeros_force_collision
    (constant binary ternary : ℚ)
    (nonidentity : ¬ (constant = 0 ∧ binary = 0 ∧ ternary = 0))
    {first second third : Nat}
    (zeroAtFirst : exponentialScalar constant binary ternary first = 0)
    (zeroAtSecond : exponentialScalar constant binary ternary second = 0)
    (zeroAtThird : exponentialScalar constant binary ternary third = 0) :
    first = second ∨ first = third ∨ second = third := by
  by_contra distinct
  have first_ne_second : first ≠ second := fun equal => distinct (Or.inl equal)
  have first_ne_third : first ≠ third := fun equal => distinct (Or.inr (Or.inl equal))
  have second_ne_third : second ≠ third := fun equal => distinct (Or.inr (Or.inr equal))
  rcases lt_or_gt_of_ne first_ne_second with first_lt_second | second_lt_first
  · rcases lt_or_gt_of_ne second_ne_third with second_lt_third | third_lt_second
    · exact no_three_ordered_zeros constant binary ternary nonidentity
        first_lt_second second_lt_third zeroAtFirst zeroAtSecond zeroAtThird
    · rcases lt_or_gt_of_ne first_ne_third with first_lt_third | third_lt_first
      · exact no_three_ordered_zeros constant binary ternary nonidentity
          first_lt_third third_lt_second zeroAtFirst zeroAtThird zeroAtSecond
      · exact no_three_ordered_zeros constant binary ternary nonidentity
          third_lt_first first_lt_second zeroAtThird zeroAtFirst zeroAtSecond
  · rcases lt_or_gt_of_ne first_ne_third with first_lt_third | third_lt_first
    · exact no_three_ordered_zeros constant binary ternary nonidentity
        second_lt_first first_lt_third zeroAtSecond zeroAtFirst zeroAtThird
    · rcases lt_or_gt_of_ne second_ne_third with second_lt_third | third_lt_second
      · exact no_three_ordered_zeros constant binary ternary nonidentity
          second_lt_third third_lt_first zeroAtSecond zeroAtThird zeroAtFirst
      · exact no_three_ordered_zeros constant binary ternary nonidentity
          third_lt_second second_lt_first zeroAtThird zeroAtSecond zeroAtFirst

theorem exponentialScalar_zeroSet_encard_le_two
    (constant binary ternary : ℚ)
    (nonidentity : ¬ (constant = 0 ∧ binary = 0 ∧ ternary = 0)) :
    Set.encard {power | exponentialScalar constant binary ternary power = 0} ≤ 2 := by
  by_contra cardinality
  have two_lt :
      (2 : ℕ∞) < Set.encard {power | exponentialScalar constant binary ternary power = 0} :=
    lt_of_not_ge cardinality
  have three_le :
      (3 : ℕ∞) ≤ Set.encard {power | exponentialScalar constant binary ternary power = 0} := by
    exact ENat.natCast_add_one_le_iff.mpr two_lt
  obtain ⟨triple, triple_subset, triple_card⟩ := Set.exists_subset_encard_eq three_le
  obtain ⟨first, second, third, first_ne_second, first_ne_third, second_ne_third, rfl⟩ :=
    Set.encard_eq_three.mp triple_card
  have zeroAtFirst : exponentialScalar constant binary ternary first = 0 :=
    triple_subset (by simp)
  have zeroAtSecond : exponentialScalar constant binary ternary second = 0 :=
    triple_subset (by simp)
  have zeroAtThird : exponentialScalar constant binary ternary third = 0 :=
    triple_subset (by simp)
  rcases three_zeros_force_collision constant binary ternary nonidentity zeroAtFirst
      zeroAtSecond zeroAtThird with equal | equal | equal
  · exact first_ne_second equal
  · exact first_ne_third equal
  · exact second_ne_third equal

theorem exponentialScalar_zeroSet_eq_univ_iff
    (constant binary ternary : ℚ) :
    {power | exponentialScalar constant binary ternary power = 0} = Set.univ ↔
      constant = 0 ∧ binary = 0 ∧ ternary = 0 := by
  constructor
  · intro allPowers
    have zeroAtZero : exponentialScalar constant binary ternary 0 = 0 := by
      exact allPowers.symm.subset (Set.mem_univ 0)
    have zeroAtOne : exponentialScalar constant binary ternary 1 = 0 := by
      exact allPowers.symm.subset (Set.mem_univ 1)
    have zeroAtTwo : exponentialScalar constant binary ternary 2 = 0 := by
      exact allPowers.symm.subset (Set.mem_univ 2)
    exact coefficients_eq_zero_of_three_zeros constant binary ternary 0 1 1
      (by norm_num) (by norm_num) zeroAtZero zeroAtOne zeroAtTwo
  · rintro ⟨rfl, rfl, rfl⟩
    ext power
    simp [exponentialScalar]

theorem exponentialScalar_binary_singleton (target power : Nat) :
    exponentialScalar ((2 : ℚ) ^ target) 1 0 power = 0 ↔ power = target := by
  rw [exponentialScalar]
  simp only [one_mul, zero_mul, sub_zero, sub_eq_zero]
  simpa only [eq_comm] using
    (pow_right_injective₀ (show (0 : ℚ) < 2 by norm_num) (by norm_num)).eq_iff

/-- Scalar tested by a terminal row after the explicit depth-`power` carrier prefix. -/
def terminalValue (row : State) (source : ℚ) (column : State) (power : Nat) : ℚ :=
  row ⬝ᵥ (carrierMatrix source power *ᵥ column)

/-- Depth-independent coefficient in the terminal exponential polynomial. -/
def terminalConstant (row column : State) (source : ℚ) : ℚ :=
  row 0 * (column 0 + source * column 1)

/-- Coefficient of `2ⁿ` in the terminal exponential polynomial. -/
def terminalBinary (row column : State) : ℚ :=
  row 1 * column 0

/-- Coefficient of `3ⁿ` in the terminal exponential polynomial. -/
def terminalTernary (row column : State) : ℚ :=
  row 2 * column 1

theorem terminalValue_eq_exponentialScalar
    (row : State) (source : ℚ) (column : State) (power : Nat) :
    terminalValue row source column power =
      exponentialScalar (terminalConstant row column source)
        (terminalBinary row column) (terminalTernary row column) power := by
  rw [terminalValue, carrierMatrix_mulVec]
  simp [terminalConstant, terminalBinary, terminalTernary, exponentialScalar,
    dotProduct, Fin.sum_univ_succ]
  ring

/-- Unless the terminal scalar is identically zero, its zero-depth set has cardinality at most
two. -/
theorem terminalValue_zeroSet_encard_le_two
    (row : State) (source : ℚ) (column : State)
    (nonidentity :
      ¬ (terminalConstant row column source = 0 ∧ terminalBinary row column = 0 ∧
        terminalTernary row column = 0)) :
    Set.encard {power | terminalValue row source column power = 0} ≤ 2 := by
  simpa only [terminalValue_eq_exponentialScalar] using
    exponentialScalar_zeroSet_encard_le_two (terminalConstant row column source)
      (terminalBinary row column) (terminalTernary row column) nonidentity

/-- The terminal scalar vanishes at every depth exactly when all three coefficients vanish. -/
theorem terminalValue_zeroSet_eq_univ_iff (row : State) (source : ℚ) (column : State) :
    {power | terminalValue row source column power = 0} = Set.univ ↔
      terminalConstant row column source = 0 ∧ terminalBinary row column = 0 ∧
        terminalTernary row column = 0 := by
  simpa only [terminalValue_eq_exponentialScalar] using
    exponentialScalar_zeroSet_eq_univ_iff (terminalConstant row column source)
      (terminalBinary row column) (terminalTernary row column)

/-- Rows realizing an arbitrarily delayed singleton terminal zero. -/
def delayedRow (target : Nat) : State :=
  ![(2 : ℚ) ^ target, 1, 0]

/-- There is no row-independent finite search horizon: `delayedRow target` vanishes on the
distinguished carrier column exactly at `target`. -/
theorem delayedRow_terminalValue_eq_zero_iff (source : ℚ) (target power : Nat) :
    terminalValue (delayedRow target) source witnessInput power = 0 ↔ power = target := by
  rw [terminalValue_eq_exponentialScalar]
  simp only [terminalConstant, terminalBinary, terminalTernary, delayedRow, witnessInput,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, mul_zero, add_zero, mul_one]
  exact exponentialScalar_binary_singleton target power

/-- The two-zero upper bound is sharp in the actual carrier architecture. -/
theorem terminalValue_two_distinct_zeros :
    terminalValue ![-1, -2, 1] 0 ![1, 1, 0] 0 = 0 ∧
      terminalValue ![-1, -2, 1] 0 ![1, 1, 0] 1 = 0 := by
  constructor <;> norm_num [terminalValue, carrierMatrix_mulVec, dotProduct, Fin.sum_univ_succ]

/-- The sharp example has exactly the two terminal depths zero and one. -/
theorem terminalValue_two_zeroSet_eq :
    {power | terminalValue ![-1, -2, 1] 0 ![1, 1, 0] power = 0} =
      ({0, 1} : Set Nat) := by
  ext power
  constructor
  · intro zeroAtPower
    have scalarAtPower : exponentialScalar (-1) (-2) 1 power = 0 := by
      simpa [terminalValue_eq_exponentialScalar, terminalConstant, terminalBinary,
        terminalTernary] using zeroAtPower
    have scalarAtZero : exponentialScalar (-1) (-2) 1 0 = 0 := by
      norm_num [exponentialScalar]
    have scalarAtOne : exponentialScalar (-1) (-2) 1 1 = 0 := by
      norm_num [exponentialScalar]
    have collision := three_zeros_force_collision (-1) (-2) 1 (by norm_num) scalarAtPower
      scalarAtZero scalarAtOne
    have power_eq : power = 0 ∨ power = 1 := by
      rcases collision with power_zero | power_one | zero_one
      · exact Or.inl power_zero
      · exact Or.inr power_one
      · exact False.elim (Nat.zero_ne_one zero_one)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using power_eq
  · intro power_mem
    have power_eq : power = 0 ∨ power = 1 := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using power_mem
    rcases power_eq with rfl | rfl
    · exact terminalValue_two_distinct_zeros.1
    · exact terminalValue_two_distinct_zeros.2

/-- Three coefficients governing a fixed terminal row-column test. -/
def terminalCoefficients (row : State) (source : ℚ) (column : State) : State :=
  ![terminalConstant row column source, terminalBinary row column, terminalTernary row column]

/-- Total source-dependent column for the rational coefficient section. -/
def coefficientSectionColumn (source : ℚ) : State :=
  ![source ^ 2 + 1, 1, 0]

/-- Total row section realizing any prescribed terminal coefficient triple. -/
def coefficientSectionRow (source : ℚ) (coefficients : State) : State :=
  ![coefficients 0 / (source ^ 2 + source + 1),
    coefficients 1 / (source ^ 2 + 1), coefficients 2]

theorem source_sq_add_one_pos (source : ℚ) : 0 < source ^ 2 + 1 := by
  nlinarith [sq_nonneg source]

theorem source_sq_add_source_add_one_pos (source : ℚ) :
    0 < source ^ 2 + source + 1 := by
  nlinarith [sq_nonneg (2 * source + 1)]

theorem coefficientSection_terminalConstant (source : ℚ) (coefficients : State) :
    terminalConstant (coefficientSectionRow source coefficients)
      (coefficientSectionColumn source) source = coefficients 0 := by
  have denominator_ne : source ^ 2 + source + 1 ≠ 0 :=
    ne_of_gt (source_sq_add_source_add_one_pos source)
  simp only [terminalConstant, coefficientSectionRow, coefficientSectionColumn,
    Matrix.cons_val_zero, Matrix.cons_val_one, mul_one]
  rw [show source ^ 2 + 1 + source = source ^ 2 + source + 1 by ring]
  exact div_mul_cancel₀ (coefficients 0) denominator_ne

theorem coefficientSection_terminalBinary (source : ℚ) (coefficients : State) :
    terminalBinary (coefficientSectionRow source coefficients)
      (coefficientSectionColumn source) = coefficients 1 := by
  have denominator_ne : source ^ 2 + 1 ≠ 0 := ne_of_gt (source_sq_add_one_pos source)
  simp [terminalBinary, coefficientSectionRow, coefficientSectionColumn, denominator_ne]

theorem coefficientSection_terminalTernary (source : ℚ) (coefficients : State) :
    terminalTernary (coefficientSectionRow source coefficients)
      (coefficientSectionColumn source) = coefficients 2 := by
  simp [terminalTernary, coefficientSectionRow, coefficientSectionColumn]

theorem terminalCoefficients_section (source : ℚ) (coefficients : State) :
    terminalCoefficients (coefficientSectionRow source coefficients) source
      (coefficientSectionColumn source) = coefficients := by
  funext coordinate
  fin_cases coordinate
  · exact coefficientSection_terminalConstant source coefficients
  · exact coefficientSection_terminalBinary source coefficients
  · exact coefficientSection_terminalTernary source coefficients

theorem terminalCoefficients_surjective (source : ℚ) :
    Function.Surjective
      (fun row => terminalCoefficients row source (coefficientSectionColumn source)) := by
  intro coefficients
  exact ⟨coefficientSectionRow source coefficients,
    terminalCoefficients_section source coefficients⟩

theorem coefficientSection_terminalValue
    (source : ℚ) (coefficients : State) (power : Nat) :
    terminalValue (coefficientSectionRow source coefficients) source
        (coefficientSectionColumn source) power =
      exponentialScalar (coefficients 0) (coefficients 1) (coefficients 2) power := by
  rw [terminalValue_eq_exponentialScalar, coefficientSection_terminalConstant,
    coefficientSection_terminalBinary, coefficientSection_terminalTernary]

theorem coefficientSection_sourceFamily_delayed_zero_iff
    {Source : Type*} (sourceParameter : Source → ℚ) (targetDepth : Source → Nat)
    (source : Source) (power : Nat) :
    terminalValue
        (coefficientSectionRow (sourceParameter source)
          ![(2 : ℚ) ^ targetDepth source, 1, 0])
        (sourceParameter source) (coefficientSectionColumn (sourceParameter source)) power = 0 ↔
      power = targetDepth source := by
  rw [coefficientSection_terminalValue]
  simpa using exponentialScalar_binary_singleton (targetDepth source) power

/-- Literal raw prefix spelling of the `power`-th carrier matrix. -/
def carrierWord (power : Nat) : List PairedControl :=
  List.replicate power .toggle ++ [.data .b]

/-- Use the same source-parameter data map for both data controls. -/
def generator (source : ℚ) : PairedControl → ControlMatrix :=
  TransverseLineAtlas.generator (fun _ => data source) toggle

theorem wordProduct_carrierWord (source : ℚ) (power : Nat) :
    wordProduct (generator source) (carrierWord power) = carrierMatrix source power := by
  simp [wordProduct, generator, carrierWord, TransverseLineAtlas.generator,
    carrierMatrix, List.map_replicate, List.prod_replicate]

end TransverseInfiniteAtlas
end MatrixMortality
