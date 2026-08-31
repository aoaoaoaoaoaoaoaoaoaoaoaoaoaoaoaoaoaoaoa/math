import Mathlib.Order.Filter.AtTopBot.Basic
import MatrixMortality.InverseOrbitRecurrence

/-!
# A recurrent inverse reduction in a free dilation--parabolic orbit

The diagonal dilation `D(z)=5z` and the parabolic map

`U(z)=(-2z+3)/(-3z+4)`

generate a free subgroup of `PGL₂(ℚ)`.  The source `9/4` has trivial
stabilizer, while the primitive target `3/5` is fixed by the positive word
`UD` and therefore does not lie in the source orbit.  Canonical inverse
stripping at that target follows the exact cycle

`3/5 → 3 → 3/5`

with primitive heights `5 → 3 → 5`.  Thus the strict primitive-height
ratchet used for the step-three shear orbit does not extend to this explicit
non-elementary dilation--parabolic free product.  This recurrence does not
decide, or prove undecidable, the general orbit problem.

A second promised-empty target `11/25` has trivial stabilizer, yet unguided
inverse search admits the false ray `D⁻ⁿ(11/25)`.  Its primitive pairs are
`(11,5^(n+2))`, so height tends to infinity.  Proper height escape therefore
requires directional chamber control before it can prune inverse search.
-/

set_option autoImplicit false

namespace MatrixMortality.TransverseDilationOrbit

open scoped Matrix Pointwise

/-- Two-by-two square matrices. -/
abbrev Square₂ (R : Type*) := Matrix (Fin 2) (Fin 2) R

/-- The rational projective line. -/
abbrev RationalPoint := ProjectiveLine.Point ℚ

/-! ## Exact generators -/

/-- The signed powers of the diagonal dilation `D(z)=5z`. -/
def dilationMatrix (exponent : ℤ) : Square₂ ℚ :=
  !![(5 : ℚ) ^ exponent, 0; 0, 1]

/-- Signed powers of the parabolic conjugate of the step-three upper shear. -/
def transverseMatrix (exponent : ℤ) : Square₂ ℚ :=
  !![1 - 3 * exponent, 3 * exponent; -3 * exponent, 1 + 3 * exponent]

@[simp]
theorem dilationMatrix_mul (left right : ℤ) :
    dilationMatrix left * dilationMatrix right = dilationMatrix (left + right) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dilationMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
  rw [← zpow_add₀ (by norm_num : (5 : ℚ) ≠ 0)]

@[simp]
theorem transverseMatrix_mul (left right : ℤ) :
    transverseMatrix left * transverseMatrix right = transverseMatrix (left + right) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transverseMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

/-- The positive diagonal generator has determinant five. -/
theorem dilationGenerator_det : (dilationMatrix 1).det = 5 := by
  norm_num [dilationMatrix, Matrix.det_fin_two]

/-- The positive transverse generator is unipotent. -/
theorem transverseGenerator_det : (transverseMatrix 1).det = 1 := by
  norm_num [transverseMatrix, Matrix.det_fin_two]

/-- A signed diagonal power as an invertible rational matrix. -/
def dilationUnit (exponent : ℤ) : Matrix.GeneralLinearGroup (Fin 2) ℚ where
  val := dilationMatrix exponent
  inv := dilationMatrix (-exponent)
  val_inv := by
    rw [dilationMatrix_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dilationMatrix]
  inv_val := by
    rw [dilationMatrix_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dilationMatrix]

/-- A signed transverse-parabolic power as an invertible rational matrix. -/
def transverseUnit (exponent : ℤ) : Matrix.GeneralLinearGroup (Fin 2) ℚ where
  val := transverseMatrix exponent
  inv := transverseMatrix (-exponent)
  val_inv := by
    rw [transverseMatrix_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [transverseMatrix]
  inv_val := by
    rw [transverseMatrix_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [transverseMatrix]

/-- Diagonal powers form one infinite cyclic matrix factor. -/
def dilationFactor : Multiplicative ℤ →* Matrix.GeneralLinearGroup (Fin 2) ℚ where
  toFun exponent := dilationUnit (Multiplicative.toAdd exponent)
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dilationUnit, dilationMatrix]
  map_mul' left right := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [dilationUnit, dilationMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
    rw [← zpow_add₀ (by norm_num : (5 : ℚ) ≠ 0)]

/-- Transverse parabolic powers form the other infinite cyclic matrix factor. -/
def transverseFactor : Multiplicative ℤ →* Matrix.GeneralLinearGroup (Fin 2) ℚ where
  toFun exponent := transverseUnit (Multiplicative.toAdd exponent)
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [transverseUnit, transverseMatrix]
  map_mul' left right := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [transverseUnit, transverseMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;>
      ring

@[simp]
theorem dilationFactor_apply (exponent : ℤ) :
    dilationFactor (Multiplicative.ofAdd exponent) = dilationUnit exponent := rfl

@[simp]
theorem transverseFactor_apply (exponent : ℤ) :
    transverseFactor (Multiplicative.ofAdd exponent) = transverseUnit exponent := rfl

/-- The diagonal factor has index `false`; the transverse factor has index `true`. -/
def factor : (index : Bool) → Multiplicative ℤ →*
    Matrix.GeneralLinearGroup (Fin 2) ℚ
  | false => dilationFactor
  | true => transverseFactor

/-! ## Projective action and ping-pong chambers -/

/-- Projective points beyond the two exterior thresholds, together with infinity. -/
def DilationChamber : Set RationalPoint
  | some value => value < 1 / 2 ∨ 5 / 2 < value
  | none => True

/-- Projective points in the open interval `(1/2,2)`. -/
def TransverseChamber : Set RationalPoint
  | some value => 1 / 2 < value ∧ value < 2
  | none => False

/-- The primitive source ray `[9:4]`, chosen in the gap between the chambers. -/
def sourcePoint : RationalPoint := some (9 / 4)

/-- The primitive target ray `[3:5]`. -/
def targetPoint : RationalPoint := some (3 / 5)

/-- The intermediate primitive ray `[3:1]` in the inverse-reduction cycle. -/
def returnPoint : RationalPoint := some 3

/-- An integral determinant-one transporter from `[9:4]` to `[3:5]`. -/
def targetMatrix : Square₂ ℚ := !![-1, 3; -3, 8]

/-- The target transporter has determinant one. -/
theorem targetMatrix_det : targetMatrix.det = 1 := by
  norm_num [targetMatrix, Matrix.det_fin_two]

/-- Integral determinant-one coordinate change carrying infinity to `[9:4]`. -/
def sourceConjugatorMatrix : Square₂ ℚ := !![9, 2; 4, 1]

/-- The source coordinate change has determinant one. -/
theorem sourceConjugatorMatrix_det : sourceConjugatorMatrix.det = 1 := by
  norm_num [sourceConjugatorMatrix, Matrix.det_fin_two]

/-- The target transporter as an invertible rational matrix. -/
def targetUnit : Matrix.GeneralLinearGroup (Fin 2) ℚ where
  val := targetMatrix
  inv := !![8, -3; 3, -1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [targetMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [targetMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The source coordinate change as an invertible rational matrix. -/
def sourceConjugatorUnit : Matrix.GeneralLinearGroup (Fin 2) ℚ where
  val := sourceConjugatorMatrix
  inv := !![1, -2; -4, 9]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [sourceConjugatorMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [sourceConjugatorMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The canonical projective action of invertible rational matrices. -/
noncomputable local instance :
    MulAction (Matrix.GeneralLinearGroup (Fin 2) ℚ) RationalPoint where
  smul matrix point := ProjectiveLine.act matrix point
  one_smul point := ProjectiveLine.act_one point
  mul_smul left right point := by
    exact ProjectiveLine.act_mul left right right.isUnit point

@[simp]
theorem dilationUnit_smul_some (exponent : ℤ) (value : ℚ) :
    dilationUnit exponent • (some value : RationalPoint) =
      some ((5 : ℚ) ^ exponent * value) := by
  change ProjectiveLine.act (dilationMatrix exponent) (some value) = _
  simp [dilationMatrix, ProjectiveLine.act, ProjectiveLine.numerator,
    ProjectiveLine.denominator]

@[simp]
theorem dilationUnit_smul_none (exponent : ℤ) :
    dilationUnit exponent • (none : RationalPoint) = none := by
  change ProjectiveLine.act (dilationMatrix exponent) none = none
  simp [dilationMatrix, ProjectiveLine.act]

theorem transverseUnit_smul_some
    (exponent : ℤ) (value : ℚ)
    (denominator_ne : 1 + 3 * exponent * (1 - value) ≠ 0) :
    transverseUnit exponent • (some value : RationalPoint) =
      some ((value + 3 * exponent * (1 - value)) /
        (1 + 3 * exponent * (1 - value))) := by
  change ProjectiveLine.act (transverseMatrix exponent) (some value) = _
  simp only [ProjectiveLine.act]
  have denominator_eq :
      ProjectiveLine.denominator (transverseMatrix exponent) value =
        1 + 3 * exponent * (1 - value) := by
    simp [ProjectiveLine.denominator, transverseMatrix]
    ring
  have numerator_eq :
      ProjectiveLine.numerator (transverseMatrix exponent) value =
        value + 3 * exponent * (1 - value) := by
    simp [ProjectiveLine.numerator, transverseMatrix]
    ring
  rw [denominator_eq, numerator_eq, if_neg denominator_ne]

@[simp]
theorem transverseUnit_smul_none (exponent : ℤ) (exponent_ne : exponent ≠ 0) :
    transverseUnit exponent • (none : RationalPoint) =
      some (((1 : ℚ) - 3 * exponent) / (-3 * exponent)) := by
  have lower_left_ne : (-3 : ℚ) * exponent ≠ 0 := by
    exact_mod_cast mul_ne_zero (by norm_num : (-3 : ℤ) ≠ 0) exponent_ne
  change ProjectiveLine.act (transverseMatrix exponent) none = _
  simp only [ProjectiveLine.act]
  have lower_left_eq : transverseMatrix exponent 1 0 = (-3 : ℚ) * exponent := by
    simp [transverseMatrix]
  have upper_left_eq : transverseMatrix exponent 0 0 = (1 : ℚ) - 3 * exponent := by
    simp [transverseMatrix]
  rw [lower_left_eq, upper_left_eq, if_neg lower_left_ne]

private theorem dilation_scale_large
    (exponent : ℤ) (exponent_pos : 0 < exponent) :
    (5 : ℚ) ≤ (5 : ℚ) ^ exponent := by
  calc
    (5 : ℚ) = (5 : ℚ) ^ (1 : ℤ) := by norm_num
    _ ≤ (5 : ℚ) ^ exponent :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)

private theorem dilation_scale_small
    (exponent : ℤ) (exponent_neg : exponent < 0) :
    (5 : ℚ) ^ exponent ≤ 1 / 5 := by
  calc
    (5 : ℚ) ^ exponent ≤ (5 : ℚ) ^ (-1 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    _ = 1 / 5 := by norm_num

private theorem dilation_maps_transverse
    (exponent : ℤ) (exponent_ne : exponent ≠ 0)
    (point : RationalPoint) (point_mem : point ∈ TransverseChamber) :
    dilationUnit exponent • point ∈ DilationChamber := by
  cases point with
  | none => exact point_mem.elim
  | some value =>
      change 1 / 2 < value ∧ value < 2 at point_mem
      rw [dilationUnit_smul_some]
      change (5 : ℚ) ^ exponent * value < 1 / 2 ∨
        5 / 2 < (5 : ℚ) ^ exponent * value
      by_cases exponent_pos : 0 < exponent
      · right
        have scale_large := dilation_scale_large exponent exponent_pos
        have scale_pos : 0 < (5 : ℚ) ^ exponent := zpow_pos (by norm_num) exponent
        nlinarith
      · left
        have exponent_neg : exponent < 0 := by omega
        have scale_small := dilation_scale_small exponent exponent_neg
        have scale_pos : 0 < (5 : ℚ) ^ exponent := zpow_pos (by norm_num) exponent
        nlinarith

/-- The affine chart centered at the transverse parabolic fixed point. -/
private def transverseCoordinate : RationalPoint → ℚ
  | some value => value / (1 - value)
  | none => -1

private theorem dilationChamber_coordinate_bounds
    (point : RationalPoint) (point_mem : point ∈ DilationChamber) :
    -5 / 3 < transverseCoordinate point ∧ transverseCoordinate point < 1 := by
  cases point with
  | none => norm_num [transverseCoordinate]
  | some value =>
      change value < 1 / 2 ∨ 5 / 2 < value at point_mem
      change -5 / 3 < value / (1 - value) ∧ value / (1 - value) < 1
      rcases point_mem with value_small | value_large
      · have denominator_pos : 0 < (1 : ℚ) - value := by linarith
        constructor
        · apply (lt_div_iff₀ denominator_pos).mpr
          nlinarith
        · apply (div_lt_iff₀ denominator_pos).mpr
          linarith
      · have denominator_neg : (1 : ℚ) - value < 0 := by linarith
        constructor
        · apply (lt_div_iff_of_neg denominator_neg).mpr
          nlinarith
        · apply (div_lt_iff_of_neg denominator_neg).mpr
          linarith

private theorem translated_coordinate_ne_neg_one
    (exponent : ℤ) (exponent_ne : exponent ≠ 0)
    (coordinate : ℚ) (lower : -5 / 3 < coordinate) (upper : coordinate < 1) :
    1 + coordinate + 3 * exponent ≠ 0 := by
  by_cases exponent_pos : 0 < exponent
  · have exponent_one : (1 : ℚ) ≤ exponent := by exact_mod_cast (by omega : 1 ≤ exponent)
    nlinarith
  · have exponent_neg : exponent < 0 := by omega
    have exponent_neg_one : (exponent : ℚ) ≤ -1 := by exact_mod_cast (by omega : exponent ≤ -1)
    nlinarith

private theorem transverse_smul_eq_coordinate
    (exponent : ℤ) (exponent_ne : exponent ≠ 0)
    (point : RationalPoint) (point_mem : point ∈ DilationChamber) :
    transverseUnit exponent • point =
      some ((transverseCoordinate point + 3 * exponent) /
        (1 + transverseCoordinate point + 3 * exponent)) := by
  have coordinate_bounds := dilationChamber_coordinate_bounds point point_mem
  have translated_ne := translated_coordinate_ne_neg_one exponent exponent_ne
    (transverseCoordinate point) coordinate_bounds.1 coordinate_bounds.2
  cases point with
  | none =>
      rw [transverseUnit_smul_none exponent exponent_ne]
      simp only [transverseCoordinate]
      congr 1
      have exponent_cast_ne : (exponent : ℚ) ≠ 0 := by exact_mod_cast exponent_ne
      field_simp [exponent_cast_ne]
      ring
  | some value =>
      have value_ne_one : value ≠ 1 := by
        change value < 1 / 2 ∨ 5 / 2 < value at point_mem
        rcases point_mem with value_small | value_large <;> linarith
      have one_sub_ne : (1 : ℚ) - value ≠ 0 := sub_ne_zero.mpr value_ne_one.symm
      have denominator_identity :
          (1 - value) *
              (1 + transverseCoordinate (some value) + 3 * exponent) =
            1 + 3 * exponent * (1 - value) := by
        simp only [transverseCoordinate]
        field_simp
        ring
      have denominator_ne : 1 + 3 * exponent * (1 - value) ≠ 0 := by
        rw [← denominator_identity]
        exact mul_ne_zero one_sub_ne translated_ne
      rw [transverseUnit_smul_some exponent value denominator_ne]
      congr 1
      apply (div_eq_div_iff denominator_ne translated_ne).mpr
      simp only [transverseCoordinate]
      field_simp [one_sub_ne]
      ring

private theorem transverse_maps_dilation
    (exponent : ℤ) (exponent_ne : exponent ≠ 0)
    (point : RationalPoint) (point_mem : point ∈ DilationChamber) :
    transverseUnit exponent • point ∈ TransverseChamber := by
  have coordinate_bounds := dilationChamber_coordinate_bounds point point_mem
  rw [transverse_smul_eq_coordinate exponent exponent_ne point point_mem]
  change 1 / 2 <
      (transverseCoordinate point + 3 * exponent) /
        (1 + transverseCoordinate point + 3 * exponent) ∧
    (transverseCoordinate point + 3 * exponent) /
        (1 + transverseCoordinate point + 3 * exponent) < 2
  by_cases exponent_pos : 0 < exponent
  · have exponent_one : (1 : ℚ) ≤ exponent := by exact_mod_cast (by omega : 1 ≤ exponent)
    have translated_large : 1 < transverseCoordinate point + 3 * exponent := by
      nlinarith [coordinate_bounds.1]
    have denominator_pos :
        0 < 1 + transverseCoordinate point + 3 * exponent := by linarith
    constructor
    · apply (lt_div_iff₀ denominator_pos).mpr
      linarith
    · apply (div_lt_iff₀ denominator_pos).mpr
      linarith
  · have exponent_neg : exponent < 0 := by omega
    have exponent_neg_one : (exponent : ℚ) ≤ -1 := by exact_mod_cast (by omega : exponent ≤ -1)
    have translated_small : transverseCoordinate point + 3 * exponent < -2 := by
      nlinarith [coordinate_bounds.2]
    have denominator_neg :
        1 + transverseCoordinate point + 3 * exponent < 0 := by linarith
    constructor
    · apply (lt_div_iff_of_neg denominator_neg).mpr
      linarith
    · apply (div_lt_iff_of_neg denominator_neg).mpr
      linarith

private theorem factor_maps_other_chamber :
    Pairwise fun left right => ∀ power : Multiplicative ℤ, power ≠ 1 →
      factor left power • (if right then TransverseChamber else DilationChamber) ⊆
        if left then TransverseChamber else DilationChamber := by
  intro left right distinct power power_ne
  cases left <;> cases right
  · exact (distinct rfl).elim
  · rintro point ⟨origin, origin_mem, rfl⟩
    exact dilation_maps_transverse (Multiplicative.toAdd power) (by simpa using power_ne)
      origin origin_mem
  · rintro point ⟨origin, origin_mem, rfl⟩
    exact transverse_maps_dilation (Multiplicative.toAdd power) (by simpa using power_ne)
      origin origin_mem
  · exact (distinct rfl).elim

private theorem dilation_maps_source
    (exponent : ℤ) (exponent_ne : exponent ≠ 0) :
    dilationUnit exponent • sourcePoint ∈ DilationChamber := by
  rw [show sourcePoint = some (9 / 4) by rfl, dilationUnit_smul_some]
  change (5 : ℚ) ^ exponent * (9 / 4) < 1 / 2 ∨
    5 / 2 < (5 : ℚ) ^ exponent * (9 / 4)
  by_cases exponent_pos : 0 < exponent
  · right
    have scale_large := dilation_scale_large exponent exponent_pos
    nlinarith
  · left
    have exponent_neg : exponent < 0 := by omega
    have scale_small := dilation_scale_small exponent exponent_neg
    have scale_pos : 0 < (5 : ℚ) ^ exponent := zpow_pos (by norm_num) exponent
    nlinarith

private theorem transverse_maps_source
    (exponent : ℤ) (exponent_ne : exponent ≠ 0) :
    transverseUnit exponent • sourcePoint ∈ TransverseChamber := by
  have denominator_ne : (1 : ℚ) + 3 * exponent * (1 - 9 / 4) ≠ 0 := by
    intro denominator_zero
    have impossible : (15 : ℚ) * exponent = 4 := by linarith
    have impossible_int : (15 : ℤ) * exponent = 4 := by exact_mod_cast impossible
    omega
  rw [show sourcePoint = some (9 / 4) by rfl]
  rw [transverseUnit_smul_some exponent (9 / 4) denominator_ne]
  have action_eq :
      ((9 / 4 : ℚ) + 3 * exponent * (1 - 9 / 4)) /
          (1 + 3 * exponent * (1 - 9 / 4)) =
        ((9 : ℚ) - 15 * exponent) / (4 - 15 * exponent) := by
    field_simp
    ring
  rw [action_eq]
  change 1 / 2 < ((9 : ℚ) - 15 * exponent) / (4 - 15 * exponent) ∧
    ((9 : ℚ) - 15 * exponent) / (4 - 15 * exponent) < 2
  by_cases exponent_pos : 0 < exponent
  · have exponent_one : (1 : ℚ) ≤ exponent := by exact_mod_cast (by omega : 1 ≤ exponent)
    have denominator_neg : (4 : ℚ) - 15 * exponent < 0 := by nlinarith
    constructor
    · apply (lt_div_iff_of_neg denominator_neg).mpr
      nlinarith
    · apply (div_lt_iff_of_neg denominator_neg).mpr
      nlinarith
  · have exponent_neg : exponent < 0 := by omega
    have exponent_neg_one : (exponent : ℚ) ≤ -1 := by exact_mod_cast (by omega : exponent ≤ -1)
    have denominator_pos : 0 < (4 : ℚ) - 15 * exponent := by nlinarith
    constructor
    · apply (lt_div_iff₀ denominator_pos).mpr
      nlinarith
    · apply (div_lt_iff₀ denominator_pos).mpr
      nlinarith

private theorem factor_maps_source
    (index : Bool) (power : Multiplicative ℤ) (power_ne : power ≠ 1) :
    factor index power • sourcePoint ∈
      if index then TransverseChamber else DilationChamber := by
  cases index
  · exact dilation_maps_source (Multiplicative.toAdd power) (by simpa using power_ne)
  · exact transverse_maps_source (Multiplicative.toAdd power) (by simpa using power_ne)

/-! ## Free orbit and recurrent target -/

/-- The ping-pong chamber owned by one cyclic factor. -/
def chamber (index : Bool) : Set RationalPoint :=
  if index then TransverseChamber else DilationChamber

/-- Free product of the diagonal and transverse infinite cyclic factors. -/
abbrev DilationTransverseFreeProduct :=
  Monoid.CoprodI fun _ : Bool => Multiplicative ℤ

/-- Canonical representation of the abstract free product by the two rational generators. -/
def representation :
    DilationTransverseFreeProduct →* Matrix.GeneralLinearGroup (Fin 2) ℚ :=
  Monoid.CoprodI.lift factor

@[simp]
theorem representation_dilation (exponent : ℤ) :
    representation
        (Monoid.CoprodI.of (i := false) (Multiplicative.ofAdd exponent)) =
      dilationUnit exponent := by
  rw [representation, Monoid.CoprodI.lift_of]
  rfl

@[simp]
theorem representation_transverse (exponent : ℤ) :
    representation
        (Monoid.CoprodI.of (i := true) (Multiplicative.ofAdd exponent)) =
      transverseUnit exponent := by
  rw [representation, Monoid.CoprodI.lift_of]
  rfl

/-- A reduced free-product word sends any base point satisfying the two
factor-entry conditions into its first-factor chamber. -/
private theorem reducedWord_maps_base
    (base : RationalPoint)
    (factor_maps_base :
      ∀ (index : Bool) (power : Multiplicative ℤ), power ≠ 1 →
        factor index power • base ∈ chamber index)
    {first last : Bool}
    (word : Monoid.CoprodI.NeWord (fun _ : Bool => Multiplicative ℤ) first last) :
    representation word.prod • base ∈ chamber first := by
  induction word with
  | @singleton index power power_ne =>
      simpa [representation, chamber] using
        factor_maps_base index power power_ne
  | @append first middle next last left distinct right left_induction right_induction =>
      have mapped_chamber :
          representation left.prod • chamber next ⊆ chamber first := by
        simpa [representation, chamber] using
          Monoid.CoprodI.lift_word_ping_pong factor chamber
            (by simpa [chamber] using factor_maps_other_chamber) left distinct
      rw [Monoid.CoprodI.NeWord.append_prod, map_mul, mul_smul]
      exact mapped_chamber ⟨representation right.prod • base, right_induction, rfl⟩

private theorem reducedWord_maps_source
    {first last : Bool}
    (word : Monoid.CoprodI.NeWord (fun _ : Bool => Multiplicative ℤ) first last) :
    representation word.prod • sourcePoint ∈ chamber first :=
  reducedWord_maps_base sourcePoint
    (fun index power power_ne ↦ by
      simpa [chamber] using factor_maps_source index power power_ne)
    word

/-- The source lies outside both strict ping-pong chambers. -/
theorem source_outside_chambers (index : Bool) :
    sourcePoint ∉ chamber index := by
  cases index
  · change ¬((9 / 4 : ℚ) < 1 / 2 ∨ 5 / 2 < 9 / 4)
    norm_num
  · change ¬(1 / 2 < (9 / 4 : ℚ) ∧ 9 / 4 < 2)
    norm_num

/-- Every nonidentity word sends a lawful ping-pong base into some chamber. -/
theorem nontrivial_maps_base_into_chamber
    (base : RationalPoint)
    (factor_maps_base :
      ∀ (index : Bool) (power : Multiplicative ℤ), power ≠ 1 →
        factor index power • base ∈ chamber index)
    {word : DilationTransverseFreeProduct} (word_ne : word ≠ 1) :
    ∃ index, representation word • base ∈ chamber index := by
  let reduced := Monoid.CoprodI.Word.equiv word
  have reduced_ne : reduced ≠ Monoid.CoprodI.Word.empty := by
    intro reduced_empty
    have restored := congrArg Monoid.CoprodI.Word.equiv.symm reduced_empty
    have word_one : word = 1 := by
      calc
        word = Monoid.CoprodI.Word.equiv.symm Monoid.CoprodI.Word.empty := by
          simpa [reduced] using restored
        _ = 1 := by rfl
    exact word_ne word_one
  obtain ⟨first, last, normal, normal_eq⟩ :=
    Monoid.CoprodI.NeWord.of_word reduced reduced_ne
  have normal_prod : normal.prod = word := by
    change normal.toWord.prod = word
    rw [normal_eq]
    exact Monoid.CoprodI.Word.equiv.symm_apply_apply word
  refine ⟨first, ?_⟩
  simpa [normal_prod] using reducedWord_maps_base base factor_maps_base normal

/-- Every nonidentity abstract word moves the source into its first-factor chamber. -/
theorem nontrivial_maps_source_into_chamber
    {word : DilationTransverseFreeProduct} (word_ne : word ≠ 1) :
    ∃ index, representation word • sourcePoint ∈ chamber index :=
  nontrivial_maps_base_into_chamber sourcePoint
    (fun index power power_ne ↦ by
      simpa [chamber] using factor_maps_source index power power_ne)
    word_ne

/-- A lawful ping-pong base outside both chambers has trivial stabilizer. -/
theorem base_stabilizer_trivial
    (base : RationalPoint)
    (base_outside : ∀ index, base ∉ chamber index)
    (factor_maps_base :
      ∀ (index : Bool) (power : Multiplicative ℤ), power ≠ 1 →
        factor index power • base ∈ chamber index)
    {word : DilationTransverseFreeProduct}
    (fixed : representation word • base = base) :
    word = 1 := by
  by_contra word_ne
  obtain ⟨index, moved_mem⟩ :=
    nontrivial_maps_base_into_chamber base factor_maps_base word_ne
  rw [fixed] at moved_mem
  exact base_outside index moved_mem

/-- The source ray has trivial stabilizer in the abstract free product. -/
theorem sourcePoint_stabilizer_trivial
    {word : DilationTransverseFreeProduct}
    (fixed : representation word • sourcePoint = sourcePoint) :
    word = 1 :=
  base_stabilizer_trivial sourcePoint source_outside_chambers
    (fun index power power_ne ↦ by
      simpa [chamber] using factor_maps_source index power power_ne)
    fixed

/-- Ping-pong makes the dilation--transverse representation faithful. -/
theorem representation_injective : Function.Injective representation := by
  apply (injective_iff_map_eq_one representation).mpr
  intro word mapped_one
  apply sourcePoint_stabilizer_trivial
  rw [mapped_one, one_smul]

/-- The positive two-letter word `UD`. -/
def targetCycleWord : DilationTransverseFreeProduct :=
  Monoid.CoprodI.of (i := true) (Multiplicative.ofAdd 1) *
    Monoid.CoprodI.of (i := false) (Multiplicative.ofAdd 1)

/-- The represented positive cycle is the literal matrix product `UD`. -/
theorem representation_targetCycleWord :
    representation targetCycleWord = transverseUnit 1 * dilationUnit 1 := by
  simp [targetCycleWord]

/-- The positive word `UD` fixes the primitive target `[3:5]`. -/
theorem targetCycleWord_fixes_target :
    representation targetCycleWord • targetPoint = targetPoint := by
  rw [representation_targetCycleWord, mul_smul]
  change transverseUnit 1 • (dilationUnit 1 • some (3 / 5)) = some (3 / 5)
  rw [dilationUnit_smul_some]
  norm_num
  rw [transverseUnit_smul_some (denominator_ne := by norm_num)]
  norm_num

/-- The positive target cycle has determinant five. -/
theorem representation_targetCycleWord_det :
    (representation targetCycleWord : Square₂ ℚ).det = 5 := by
  rw [representation_targetCycleWord]
  norm_num [transverseUnit, transverseMatrix, dilationUnit, dilationMatrix,
    Matrix.mul_apply, Matrix.det_fin_two, Fin.sum_univ_succ]

/-- The positive target cycle is nonidentity. -/
theorem targetCycleWord_ne_one : targetCycleWord ≠ 1 := by
  intro cycle_one
  have represented_one := congrArg representation cycle_one
  rw [map_one] at represented_one
  have entry_eq := congrArg
    (fun unit : Matrix.GeneralLinearGroup (Fin 2) ℚ => (unit : Square₂ ℚ) 0 1)
    represented_one
  norm_num [targetCycleWord, representation_targetCycleWord, transverseUnit,
    transverseMatrix, dilationUnit, dilationMatrix, Matrix.mul_apply,
    Fin.sum_univ_succ] at entry_eq

/-- Every positive power of `UD` fixes the target. -/
theorem targetCycleWord_pow_fixes_target (exponent : ℕ) :
    representation (targetCycleWord ^ exponent) • targetPoint = targetPoint := by
  rw [map_pow]
  induction exponent with
  | zero => simp
  | succ exponent induction =>
      rw [pow_succ, mul_smul, targetCycleWord_fixes_target, induction]

/-- The primitive target does not lie in the free orbit of the fixed source. -/
theorem targetPoint_not_reachable (word : DilationTransverseFreeProduct) :
    representation word • sourcePoint ≠ targetPoint := by
  intro reachable
  let conjugate := word⁻¹ * targetCycleWord * word
  have conjugate_fixed : representation conjugate • sourcePoint = sourcePoint := by
    dsimp only [conjugate]
    simp only [map_mul, map_inv, mul_smul]
    rw [reachable, targetCycleWord_fixes_target, ← reachable, inv_smul_smul]
  have conjugate_one := sourcePoint_stabilizer_trivial conjugate_fixed
  apply targetCycleWord_ne_one
  calc
    targetCycleWord = word * conjugate * word⁻¹ := by
      dsimp only [conjugate]
      group
    _ = 1 := by rw [conjugate_one]; group

/-- The target transporter sends the source exactly to the primitive target. -/
theorem targetUnit_smul_source : targetUnit • sourcePoint = targetPoint := by
  change ProjectiveLine.act targetMatrix (some (9 / 4)) = some (3 / 5)
  norm_num [ProjectiveLine.act, ProjectiveLine.numerator,
    ProjectiveLine.denominator, targetMatrix]

/-- The integral source coordinate change sends infinity to `[9:4]`. -/
theorem sourceConjugatorUnit_smul_none :
    sourceConjugatorUnit • (none : RationalPoint) = sourcePoint := by
  change ProjectiveLine.act sourceConjugatorMatrix none = some (9 / 4)
  norm_num [ProjectiveLine.act, sourceConjugatorMatrix]

/-- No represented word lies in the target transporter times the source stabilizer. -/
theorem representation_ne_target_mul_stabilizer
    (word : DilationTransverseFreeProduct)
    (stabilizer : Matrix.GeneralLinearGroup (Fin 2) ℚ)
    (fixed : stabilizer • sourcePoint = sourcePoint) :
    representation word ≠ targetUnit * stabilizer := by
  intro representation_eq
  apply targetPoint_not_reachable word
  calc
    representation word • sourcePoint =
        (targetUnit * stabilizer) • sourcePoint := by rw [representation_eq]
    _ = targetUnit • (stabilizer • sourcePoint) := by rw [mul_smul]
    _ = targetUnit • sourcePoint := by rw [fixed]
    _ = targetPoint := targetUnit_smul_source

/-- Membership in the represented dilation--transverse subgroup. -/
def IsRepresented (matrix : Matrix.GeneralLinearGroup (Fin 2) ℚ) : Prop :=
  ∃ word, representation word = matrix

/-- Membership in the target transporter times the source-point stabilizer. -/
def InTargetCoset (matrix : Matrix.GeneralLinearGroup (Fin 2) ℚ) : Prop :=
  ∃ stabilizer, stabilizer • sourcePoint = sourcePoint ∧
    matrix = targetUnit * stabilizer

/-- The represented subgroup and the target stabilizer coset are disjoint. -/
theorem represented_targetCoset_disjoint
    (matrix : Matrix.GeneralLinearGroup (Fin 2) ℚ)
    (represented : IsRepresented matrix) :
    ¬InTargetCoset matrix := by
  rintro ⟨stabilizer, fixed, coset_eq⟩
  obtain ⟨word, word_eq⟩ := represented
  exact representation_ne_target_mul_stabilizer word stabilizer fixed
    (word_eq.trans coset_eq)

/-! ## Standard Borel coordinates -/

/-- Conjugated representation whose distinguished source is infinity. -/
def infinityRepresentation :
    DilationTransverseFreeProduct →* Matrix.GeneralLinearGroup (Fin 2) ℚ :=
  (MulAut.conj sourceConjugatorUnit⁻¹).toMonoidHom.comp representation

/-- The target transporter in the coordinate system whose source is infinity. -/
def infinityTargetUnit : Matrix.GeneralLinearGroup (Fin 2) ℚ :=
  sourceConjugatorUnit⁻¹ * targetUnit * sourceConjugatorUnit

/-- Conjugation expands the infinity-source representation literally. -/
theorem infinityRepresentation_apply (word : DilationTransverseFreeProduct) :
    infinityRepresentation word =
      sourceConjugatorUnit⁻¹ * representation word * sourceConjugatorUnit := by
  simp [infinityRepresentation]

/-- In standard coordinates, the represented group misses the target times `Stab(∞)`. -/
theorem infinityRepresentation_ne_target_mul_stabilizer
    (word : DilationTransverseFreeProduct)
    (stabilizer : Matrix.GeneralLinearGroup (Fin 2) ℚ)
    (fixed : stabilizer • (none : RationalPoint) = none) :
    infinityRepresentation word ≠ infinityTargetUnit * stabilizer := by
  intro conjugated_eq
  let sourceStabilizer := sourceConjugatorUnit * stabilizer * sourceConjugatorUnit⁻¹
  have sourceStabilizer_fixed : sourceStabilizer • sourcePoint = sourcePoint := by
    dsimp only [sourceStabilizer]
    rw [← sourceConjugatorUnit_smul_none]
    simp only [mul_smul]
    rw [inv_smul_smul, fixed]
  apply representation_ne_target_mul_stabilizer word sourceStabilizer sourceStabilizer_fixed
  calc
    representation word =
        sourceConjugatorUnit * infinityRepresentation word * sourceConjugatorUnit⁻¹ := by
      rw [infinityRepresentation_apply]
      group
    _ = sourceConjugatorUnit * (infinityTargetUnit * stabilizer) *
        sourceConjugatorUnit⁻¹ := by rw [conjugated_eq]
    _ = targetUnit * sourceStabilizer := by
      dsimp only [infinityTargetUnit, sourceStabilizer]
      group

/-! ## Exact inverse-reduction recurrence -/

/-- Removing the positive `U` syllable sends `[3:5]` to `[3:1]`. -/
theorem inverse_transverse_target :
    transverseUnit (-1) • targetPoint = returnPoint := by
  change transverseUnit (-1) • (some (3 / 5) : RationalPoint) = some 3
  rw [transverseUnit_smul_some (denominator_ne := by norm_num)]
  norm_num

/-- The target lies in the transverse chamber, so inverse normal-form stripping removes `U`. -/
theorem targetPoint_mem_transverseChamber : targetPoint ∈ TransverseChamber := by
  change 1 / 2 < (3 / 5 : ℚ) ∧ 3 / 5 < 2
  norm_num

/-- Removing the positive `D` syllable returns `[3:1]` to `[3:5]`. -/
theorem inverse_dilation_return :
    dilationUnit (-1) • returnPoint = targetPoint := by
  change dilationUnit (-1) • (some 3 : RationalPoint) = some (3 / 5)
  rw [dilationUnit_smul_some]
  norm_num

/-- The intermediate point lies in the dilation chamber, so inverse stripping removes `D`. -/
theorem returnPoint_mem_dilationChamber : returnPoint ∈ DilationChamber := by
  change (3 : ℚ) < 1 / 2 ∨ 5 / 2 < 3
  norm_num

/-- The two inverse syllables form an exact period-two reduction cycle. -/
theorem inverseReduction_period_two :
    transverseUnit (-1) • targetPoint = returnPoint ∧
      dilationUnit (-1) • returnPoint = targetPoint :=
  ⟨inverse_transverse_target, inverse_dilation_return⟩

/-- Primitive integral representative of the fixed source. -/
def sourcePair : ShearEuclidean.IntegralPair := (9, 4)

/-- Primitive integral representative of the recurrent target. -/
def targetPair : ShearEuclidean.IntegralPair := (3, 5)

/-- Primitive integral representative of the intermediate state `[3:1]`. -/
def returnPair : ShearEuclidean.IntegralPair := (3, 1)

/-- The source, target, and intermediate integral representatives are primitive. -/
theorem recurrentPairs_coprime :
    IsCoprime sourcePair.1 sourcePair.2 ∧
      IsCoprime targetPair.1 targetPair.2 ∧
      IsCoprime returnPair.1 returnPair.2 := by
  norm_num [sourcePair, targetPair, returnPair]

/-- Projectivization of the target pair is the named target point. -/
theorem targetPair_projectivizes :
    ProjectiveLine.ofPair (targetPair.1 : ℚ) (targetPair.2 : ℚ) = targetPoint := by
  norm_num [targetPair, targetPoint, ProjectiveLine.ofPair]

/-- Projectivization of the return pair is the named intermediate point. -/
theorem returnPair_projectivizes :
    ProjectiveLine.ofPair (returnPair.1 : ℚ) (returnPair.2 : ℚ) = returnPoint := by
  norm_num [returnPair, returnPoint, ProjectiveLine.ofPair]

/-- Primitive height follows the recurrent cycle `5 → 3 → 5`. -/
theorem inverseReduction_height_cycle :
    ShearEuclidean.pairHeight targetPair = 5 ∧
      ShearEuclidean.pairHeight returnPair = 3 ∧
      ShearEuclidean.pairHeight targetPair = 5 := by
  norm_num [targetPair, returnPair, ShearEuclidean.pairHeight]

/-! ## A proper false inverse ray with trivial endpoint stabilizers -/

/-- Neutral anchor for the proper false inverse ray. -/
def falseRayAnchor : RationalPoint := some (11 / 5)

/-- The target one inverse dilation below the neutral anchor. -/
def falseRayTarget : RationalPoint := some (11 / 25)

/-- Integral determinant-one transporter from the fixed source to the false-ray target. -/
def falseRayTargetMatrix : Square₂ ℚ := !![-17, 41; -39, 94]

/-- The false-ray transporter has determinant one. -/
theorem falseRayTargetMatrix_det : falseRayTargetMatrix.det = 1 := by
  norm_num [falseRayTargetMatrix, Matrix.det_fin_two]

/-- The false-ray transporter as an invertible rational matrix. -/
def falseRayTargetUnit : Matrix.GeneralLinearGroup (Fin 2) ℚ where
  val := falseRayTargetMatrix
  inv := !![94, -41; 39, -17]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [falseRayTargetMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [falseRayTargetMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The false-ray anchor lies outside both strict ping-pong chambers. -/
theorem falseRayAnchor_outside_chambers (index : Bool) :
    falseRayAnchor ∉ chamber index := by
  cases index
  · change ¬((11 / 5 : ℚ) < 1 / 2 ∨ 5 / 2 < 11 / 5)
    norm_num
  · change ¬(1 / 2 < (11 / 5 : ℚ) ∧ 11 / 5 < 2)
    norm_num

private theorem dilation_maps_falseRayAnchor
    (exponent : ℤ) (exponent_ne : exponent ≠ 0) :
    dilationUnit exponent • falseRayAnchor ∈ DilationChamber := by
  rw [show falseRayAnchor = some (11 / 5) by rfl, dilationUnit_smul_some]
  change (5 : ℚ) ^ exponent * (11 / 5) < 1 / 2 ∨
    5 / 2 < (5 : ℚ) ^ exponent * (11 / 5)
  by_cases exponent_pos : 0 < exponent
  · right
    have scale_large := dilation_scale_large exponent exponent_pos
    nlinarith
  · left
    have exponent_neg : exponent < 0 := by omega
    have scale_small := dilation_scale_small exponent exponent_neg
    have scale_pos : 0 < (5 : ℚ) ^ exponent := zpow_pos (by norm_num) exponent
    nlinarith

private theorem transverse_maps_falseRayAnchor
    (exponent : ℤ) (exponent_ne : exponent ≠ 0) :
    transverseUnit exponent • falseRayAnchor ∈ TransverseChamber := by
  have denominator_ne : (1 : ℚ) + 3 * exponent * (1 - 11 / 5) ≠ 0 := by
    intro denominator_zero
    have impossible : (18 : ℚ) * exponent = 5 := by linarith
    have impossible_int : (18 : ℤ) * exponent = 5 := by exact_mod_cast impossible
    omega
  rw [show falseRayAnchor = some (11 / 5) by rfl]
  rw [transverseUnit_smul_some exponent (11 / 5) denominator_ne]
  have action_eq :
      ((11 / 5 : ℚ) + 3 * exponent * (1 - 11 / 5)) /
          (1 + 3 * exponent * (1 - 11 / 5)) =
        ((11 : ℚ) - 18 * exponent) / (5 - 18 * exponent) := by
    field_simp
    ring
  rw [action_eq]
  change 1 / 2 < ((11 : ℚ) - 18 * exponent) / (5 - 18 * exponent) ∧
    ((11 : ℚ) - 18 * exponent) / (5 - 18 * exponent) < 2
  by_cases exponent_pos : 0 < exponent
  · have exponent_one : (1 : ℚ) ≤ exponent := by exact_mod_cast (by omega : 1 ≤ exponent)
    have denominator_neg : (5 : ℚ) - 18 * exponent < 0 := by nlinarith
    constructor
    · exact (lt_div_iff_of_neg denominator_neg).mpr (by nlinarith)
    · exact (div_lt_iff_of_neg denominator_neg).mpr (by nlinarith)
  · have exponent_neg : exponent < 0 := by omega
    have exponent_neg_one : (exponent : ℚ) ≤ -1 := by exact_mod_cast (by omega : exponent ≤ -1)
    have denominator_pos : 0 < (5 : ℚ) - 18 * exponent := by nlinarith
    constructor
    · exact (lt_div_iff₀ denominator_pos).mpr (by nlinarith)
    · exact (div_lt_iff₀ denominator_pos).mpr (by nlinarith)

private theorem factor_maps_falseRayAnchor
    (index : Bool) (power : Multiplicative ℤ) (power_ne : power ≠ 1) :
    factor index power • falseRayAnchor ∈ chamber index := by
  cases index
  · exact dilation_maps_falseRayAnchor (Multiplicative.toAdd power)
      (by simpa using power_ne)
  · exact transverse_maps_falseRayAnchor (Multiplicative.toAdd power)
      (by simpa using power_ne)

/-- The neutral false-ray anchor has trivial stabilizer. -/
theorem falseRayAnchor_stabilizer_trivial
    {word : DilationTransverseFreeProduct}
    (fixed : representation word • falseRayAnchor = falseRayAnchor) :
    word = 1 :=
  base_stabilizer_trivial falseRayAnchor falseRayAnchor_outside_chambers
    factor_maps_falseRayAnchor fixed

/-- The neutral false-ray anchor is outside the fixed source orbit. -/
theorem falseRayAnchor_not_reachable
    (word : DilationTransverseFreeProduct) :
    representation word • sourcePoint ≠ falseRayAnchor := by
  intro reaches
  by_cases word_one : word = 1
  · rw [word_one, map_one, one_smul] at reaches
    norm_num [sourcePoint, falseRayAnchor] at reaches
  · obtain ⟨index, moved_mem⟩ := nontrivial_maps_source_into_chamber word_one
    rw [reaches] at moved_mem
    exact falseRayAnchor_outside_chambers index moved_mem

/-- One pure dilation syllable in the abstract free product. -/
def pureDilationWord (exponent : ℤ) : DilationTransverseFreeProduct :=
  Monoid.CoprodI.of (i := false) (Multiplicative.ofAdd exponent)

@[simp]
theorem representation_pureDilationWord (exponent : ℤ) :
    representation (pureDilationWord exponent) = dilationUnit exponent := by
  simp [pureDilationWord]

/-- The target is exactly one inverse dilation below the neutral anchor. -/
theorem inverseDilation_anchor :
    representation (pureDilationWord (-1)) • falseRayAnchor = falseRayTarget := by
  rw [representation_pureDilationWord]
  change dilationUnit (-1) • (some (11 / 5) : RationalPoint) = some (11 / 25)
  rw [dilationUnit_smul_some]
  norm_num

/-- A forward dilation returns the false-ray target to its neutral anchor. -/
theorem forwardDilation_target :
    representation (pureDilationWord 1) • falseRayTarget = falseRayAnchor := by
  rw [representation_pureDilationWord]
  change dilationUnit 1 • (some (11 / 25) : RationalPoint) = some (11 / 5)
  rw [dilationUnit_smul_some]
  norm_num

/-- The false-ray target is outside the fixed source orbit. -/
theorem falseRayTarget_not_reachable
    (word : DilationTransverseFreeProduct) :
    representation word • sourcePoint ≠ falseRayTarget := by
  intro reaches
  have anchor_reached :
      representation (pureDilationWord 1 * word) • sourcePoint = falseRayAnchor := by
    rw [map_mul, mul_smul, reaches, forwardDilation_target]
  exact falseRayAnchor_not_reachable (pureDilationWord 1 * word) anchor_reached

/-- The determinant-one transporter sends the fixed source to the false-ray target. -/
theorem falseRayTargetUnit_smul_source :
    falseRayTargetUnit • sourcePoint = falseRayTarget := by
  change ProjectiveLine.act falseRayTargetMatrix (some (9 / 4)) = some (11 / 25)
  norm_num [ProjectiveLine.act, ProjectiveLine.numerator,
    ProjectiveLine.denominator, falseRayTargetMatrix]

/-- No represented word lies in the false-ray transporter coset of the source stabilizer. -/
theorem representation_ne_falseRayTarget_mul_stabilizer
    (word : DilationTransverseFreeProduct)
    (stabilizer : Matrix.GeneralLinearGroup (Fin 2) ℚ)
    (fixed : stabilizer • sourcePoint = sourcePoint) :
    representation word ≠ falseRayTargetUnit * stabilizer := by
  intro representation_eq
  have reaches : representation word • sourcePoint = falseRayTarget := by
    calc
      representation word • sourcePoint =
          (falseRayTargetUnit * stabilizer) • sourcePoint := by rw [representation_eq]
      _ = falseRayTargetUnit • (stabilizer • sourcePoint) := by rw [mul_smul]
      _ = falseRayTargetUnit • sourcePoint := by rw [fixed]
      _ = falseRayTarget := falseRayTargetUnit_smul_source
  exact falseRayTarget_not_reachable word reaches

/-- The false-ray target inherits trivial stabilizer from the neutral anchor. -/
theorem falseRayTarget_stabilizer_trivial
    {word : DilationTransverseFreeProduct}
    (fixed : representation word • falseRayTarget = falseRayTarget) :
    word = 1 := by
  let transporter := pureDilationWord (-1)
  have reaches : representation transporter • falseRayAnchor = falseRayTarget := by
    exact inverseDilation_anchor
  have conjugate_fixed :
      representation (transporter⁻¹ * word * transporter) • falseRayAnchor =
        falseRayAnchor := by
    calc
      representation (transporter⁻¹ * word * transporter) • falseRayAnchor =
          representation transporter⁻¹ • representation word •
            representation transporter • falseRayAnchor := by
              simp only [map_mul, mul_smul]
      _ = representation transporter⁻¹ • representation word • falseRayTarget := by
        rw [reaches]
      _ = representation transporter⁻¹ • falseRayTarget := by rw [fixed]
      _ = representation transporter⁻¹ •
          (representation transporter • falseRayAnchor) := by rw [reaches]
      _ = falseRayAnchor := by
        exact inv_smul_smul (representation transporter) falseRayAnchor
  have conjugate_one := falseRayAnchor_stabilizer_trivial conjugate_fixed
  calc
    word = transporter * (transporter⁻¹ * word * transporter) * transporter⁻¹ := by group
    _ = 1 := by rw [conjugate_one]; simp

/-- The `n`th unguided inverse-dilation prefix. -/
def falseRayPrefix (index : ℕ) : DilationTransverseFreeProduct :=
  pureDilationWord (-(index : ℤ))

/-- Rational point reached after `n` inverse dilations from the false target. -/
def falseRayPoint (index : ℕ) : RationalPoint :=
  some (11 / (25 * (5 : ℚ) ^ index))

/-- The abstract inverse prefix realizes the explicit false-ray point. -/
theorem falseRayPrefix_realizes (index : ℕ) :
    representation (falseRayPrefix index) • falseRayTarget = falseRayPoint index := by
  rw [falseRayPrefix, representation_pureDilationWord]
  change dilationUnit (-(index : ℤ)) • (some (11 / 25) : RationalPoint) =
    some (11 / (25 * (5 : ℚ) ^ index))
  rw [dilationUnit_smul_some]
  congr 1
  rw [zpow_neg, zpow_natCast]
  field_simp

/-- The pure inverse-dilation prefixes are pairwise distinct. -/
theorem falseRayPrefix_injective : Function.Injective falseRayPrefix := by
  intro left right words_eq
  have represented_eq := congrArg representation words_eq
  have powers_eq := congrArg
    (fun unit : Matrix.GeneralLinearGroup (Fin 2) ℚ => (unit : Square₂ ℚ) 0 0)
    represented_eq
  have exponents_eq : -(left : ℤ) = -(right : ℤ) :=
    (zpow_right_injective₀ (by norm_num : (0 : ℚ) < 5) (by norm_num : (5 : ℚ) ≠ 1))
      (by simpa [falseRayPrefix, representation_pureDilationWord,
        dilationUnit, dilationMatrix] using powers_eq)
  omega

/-- Primitive pair carried by the `n`th point of the false inverse ray. -/
def falseRayPair (index : ℕ) : InverseOrbitRecurrence.PrimitivePair :=
  ⟨(11, (5 : ℤ) ^ (index + 2)),
    (by norm_num : IsCoprime (11 : ℤ) 5).pow_right⟩

/-- Projectivization of the explicit false-ray pair. -/
theorem falseRayPair_projectivizes (index : ℕ) :
    InverseOrbitRecurrence.primitivePoint (falseRayPair index) = falseRayPoint index := by
  simp [InverseOrbitRecurrence.primitivePoint, falseRayPair, falseRayPoint,
    ProjectiveLine.ofPair, pow_add]
  ring

/-- Each inverse prefix realizes the projectivization of its primitive pair. -/
theorem falseRayPrefix_realizes_primitive (index : ℕ) :
    representation (falseRayPrefix index) • falseRayTarget =
      InverseOrbitRecurrence.primitivePoint (falseRayPair index) := by
  calc
    representation (falseRayPrefix index) • falseRayTarget = falseRayPoint index :=
      falseRayPrefix_realizes index
    _ = InverseOrbitRecurrence.primitivePoint (falseRayPair index) :=
      (falseRayPair_projectivizes index).symm

/-- The false-ray pair has exact primitive height `5^(n+2)`. -/
theorem falseRayPair_height (index : ℕ) :
    InverseOrbitRecurrence.primitiveHeight (falseRayPair index) = 5 ^ (index + 2) := by
  have power_large : 11 ≤ 5 ^ (index + 2) := by
    calc
      11 ≤ 5 ^ 2 := by norm_num
      _ ≤ 5 ^ (index + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  simp [InverseOrbitRecurrence.primitiveHeight, falseRayPair,
    ShearEuclidean.pairHeight, max_eq_right power_large]

/-- Primitive height along the false inverse ray tends to infinity. -/
theorem falseRayPair_height_tendsto_atTop :
    Filter.Tendsto
      (fun index ↦ InverseOrbitRecurrence.primitiveHeight (falseRayPair index))
      Filter.atTop Filter.atTop := by
  simpa [falseRayPair_height, Function.comp_def] using
    (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℕ) < 5 by norm_num)).comp
      (Filter.tendsto_add_atTop_nat 2)

end MatrixMortality.TransverseDilationOrbit
