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
