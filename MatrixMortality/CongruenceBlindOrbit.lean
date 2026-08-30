import Mathlib.GroupTheory.CoprodI
import MatrixMortality.ProjectiveLine

/-!
# A free rational orbit invisible to every congruence quotient

The upper and lower shears of step three act freely on the rational projective point one.  The
point `10 / 13` lies outside that orbit, but its reduction lies in the orbit modulo every positive
integer.  Thus congruence separation cannot decide even a projective orbit with trivial
stabilizer.
-/

namespace MatrixMortality.CongruenceBlindOrbit

open scoped Matrix Pointwise

/-- Two-by-two square matrices. -/
abbrev Square₂ (R : Type*) := Matrix (Fin 2) (Fin 2) R

/-! ## Shear algebra -/

/-- Upper unipotent shear. -/
def upperShear {R : Type*} [Zero R] [One R] (shift : R) : Square₂ R :=
  !![1, shift; 0, 1]

/-- Lower unipotent shear. -/
def lowerShear {R : Type*} [Zero R] [One R] (shift : R) : Square₂ R :=
  !![1, 0; shift, 1]

/-- The homogeneous source ray `[1:1]`. -/
def sourceRay (R : Type*) [One R] : Fin 2 → R := ![1, 1]

/-- The homogeneous target ray `[10:13]`. -/
def targetRay (R : Type*) [OfNat R 10] [OfNat R 13] : Fin 2 → R := ![10, 13]

@[simp]
theorem upperShear_mul (R : Type*) [CommRing R] (left right : R) :
    upperShear left * upperShear right = upperShear (left + right) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperShear, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

@[simp]
theorem lowerShear_mul (R : Type*) [CommRing R] (left right : R) :
    lowerShear left * lowerShear right = lowerShear (left + right) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerShear, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Five shear blocks comprising the congruence witness.  When `x = 3rd`, these blocks are the
integer powers `B^(rd) A^(3rd) B^(2rd) A^(-3rdn) A^n`. -/
def bridgeMatrix {R : Type*} [CommRing R] (x n : R) : Square₂ R :=
  lowerShear x * upperShear (3 * x) * lowerShear (2 * x) *
    upperShear (-3 * x * n) * upperShear (3 * n)

/-- If the simulated inverse makes `x = 1`, the five-block bridge sends `[1:1]` exactly to
`[10:13]`. -/
theorem bridgeMatrix_one_mulVec_source
    {R : Type*} [CommRing R] (n : R) :
    bridgeMatrix 1 n *ᵥ sourceRay R = targetRay R := by
  ext i
  fin_cases i
  · simp [bridgeMatrix, upperShear, lowerShear, sourceRay, targetRay,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  · simp [bridgeMatrix, upperShear, lowerShear, sourceRay, targetRay,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring

/-- If `x = 0`, the four correction blocks vanish and only the terminal upper shear remains. -/
theorem bridgeMatrix_zero_mulVec_source
    {R : Type*} [CommRing R] (n : R) :
    bridgeMatrix 0 n *ᵥ sourceRay R = ![1 + 3 * n, 1] := by
  ext i
  fin_cases i <;>
    simp [bridgeMatrix, upperShear, lowerShear, sourceRay,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- On an idempotent CRT selector, the bridge interpolates its exact `x=1` and `x=0`
actions. -/
theorem bridgeMatrix_idempotent_mulVec_source
    {R : Type*} [CommRing R] (x n : R) (x_idempotent : x * x = x) :
    bridgeMatrix x n *ᵥ sourceRay R =
      ![x * 10 + (1 - x) * (1 + 3 * n), x * 13 + (1 - x)] := by
  ext i
  fin_cases i
  · simp [bridgeMatrix, upperShear, lowerShear, sourceRay,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    linear_combination 6 * (1 - 3 * n * x) * x_idempotent
  · simp [bridgeMatrix, upperShear, lowerShear, sourceRay,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    linear_combination (9 - 9 * n + 6 * x - 18 * n * x ^ 2) * x_idempotent

/-- CRT-local projective data turn the interpolated bridge into one scalar copy of the target
ray. -/
theorem bridgeMatrix_idempotent_projective_target
    {R : Type*} [CommRing R] (x n unit : R)
    (x_idempotent : x * x = x)
    (unit_on_left : x * unit = x)
    (unit_on_right : (1 - x) * (13 * unit) = 1 - x)
    (source_on_right :
      (1 - x) * (1 + 3 * n) = (1 - x) * (10 * unit)) :
    bridgeMatrix x n *ᵥ sourceRay R = unit • targetRay R := by
  rw [bridgeMatrix_idempotent_mulVec_source x n x_idempotent]
  ext i
  fin_cases i
  · simp [targetRay]
    calc
      x * 10 + (1 - x) * (1 + 3 * n) =
          x * 10 + (1 - x) * (10 * unit) := by rw [source_on_right]
      _ = 10 * (x + (1 - x) * unit) := by ring
      _ = 10 * (x * unit + (1 - x) * unit) := by rw [unit_on_left]
      _ = unit * 10 := by ring
  · simp [targetRay]
    calc
      x * 13 + (1 - x) = x * 13 + (1 - x) * (13 * unit) := by
        rw [unit_on_right]
      _ = 13 * (x + (1 - x) * unit) := by ring
      _ = 13 * (x * unit + (1 - x) * unit) := by rw [unit_on_left]
      _ = unit * 13 := by ring

/-! ## Rational ping-pong -/

/-- The rational projective line. -/
abbrev RationalPoint := ProjectiveLine.Point ℚ

/-- Projective points outside the closed unit interval, together with infinity. -/
def UpperChamber : Set RationalPoint
  | some value => 1 < |value|
  | none => True

/-- Projective points in the open interval of radius `2/3`. -/
def LowerChamber : Set RationalPoint
  | some value => |value| < 2 / 3
  | none => False

/-- The rational source point. -/
def sourcePoint : RationalPoint := some 1

/-- The rational target point. -/
def targetPoint : RationalPoint := some (10 / 13)

/-- Integral upper shears as rational invertible matrices. -/
def upperUnit (exponent : ℤ) : Matrix.GeneralLinearGroup (Fin 2) ℚ where
  val := upperShear (3 * exponent)
  inv := upperShear (-3 * exponent)
  val_inv := by
    rw [upperShear_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upperShear]
  inv_val := by
    rw [upperShear_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upperShear]

/-- Integral lower shears as rational invertible matrices. -/
def lowerUnit (exponent : ℤ) : Matrix.GeneralLinearGroup (Fin 2) ℚ where
  val := lowerShear (3 * exponent)
  inv := lowerShear (-3 * exponent)
  val_inv := by
    rw [lowerShear_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lowerShear]
  inv_val := by
    rw [lowerShear_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lowerShear]

/-- Upper powers form a homomorphism from the infinite cyclic group. -/
def upperFactor : Multiplicative ℤ →* Matrix.GeneralLinearGroup (Fin 2) ℚ where
  toFun exponent := upperUnit (Multiplicative.toAdd exponent)
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upperUnit, upperShear]
  map_mul' left right := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [upperUnit, upperShear, Matrix.mul_apply, Fin.sum_univ_succ]
    ring

/-- Lower powers form a homomorphism from the infinite cyclic group. -/
def lowerFactor : Multiplicative ℤ →* Matrix.GeneralLinearGroup (Fin 2) ℚ where
  toFun exponent := lowerUnit (Multiplicative.toAdd exponent)
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lowerUnit, lowerShear]
  map_mul' left right := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lowerUnit, lowerShear, Matrix.mul_apply, Fin.sum_univ_succ]
    ring

@[simp]
theorem upperFactor_apply (exponent : ℤ) :
    upperFactor (Multiplicative.ofAdd exponent) = upperUnit exponent := rfl

@[simp]
theorem lowerFactor_apply (exponent : ℤ) :
    lowerFactor (Multiplicative.ofAdd exponent) = lowerUnit exponent := rfl

/-- The two cyclic shear factors. -/
def factor : (index : Bool) → Multiplicative ℤ →*
    Matrix.GeneralLinearGroup (Fin 2) ℚ
  | false => upperFactor
  | true => lowerFactor

/-- The canonical rational projective action of invertible matrices. -/
noncomputable local instance :
    MulAction (Matrix.GeneralLinearGroup (Fin 2) ℚ) RationalPoint where
  smul matrix point := ProjectiveLine.act matrix point
  one_smul point := ProjectiveLine.act_one point
  mul_smul left right point := by
    exact ProjectiveLine.act_mul left right right.isUnit point

@[simp]
theorem upperUnit_smul_some (exponent : ℤ) (value : ℚ) :
    upperUnit exponent • (some value : RationalPoint) = some (value + 3 * exponent) := by
  change ProjectiveLine.act (upperUnit exponent).1 (some value) = _
  simp [upperUnit, upperShear, ProjectiveLine.act, ProjectiveLine.numerator,
    ProjectiveLine.denominator]

theorem lowerUnit_smul_some (exponent : ℤ) (value : ℚ)
    (denominator_ne : 3 * exponent * value + 1 ≠ 0) :
    lowerUnit exponent • (some value : RationalPoint) =
      some (value / (3 * exponent * value + 1)) := by
  change ProjectiveLine.act (lowerUnit exponent).1 (some value) = _
  simp [lowerUnit, lowerShear, ProjectiveLine.act, ProjectiveLine.numerator,
    ProjectiveLine.denominator, denominator_ne]

@[simp]
theorem lowerUnit_smul_none (exponent : ℤ) (exponent_ne : exponent ≠ 0) :
    lowerUnit exponent • (none : RationalPoint) =
      some ((1 : ℚ) / (3 * (exponent : ℚ))) := by
  have lower_left_ne : (3 : ℚ) * exponent ≠ 0 := by
    exact_mod_cast mul_ne_zero (by norm_num) exponent_ne
  change ProjectiveLine.act (lowerUnit exponent).1 none = _
  simp [lowerUnit, lowerShear, ProjectiveLine.act, lower_left_ne]

private theorem upper_maps_lower
    (exponent : ℤ) (exponent_ne : exponent ≠ 0)
    (point : RationalPoint) (point_mem : point ∈ LowerChamber) :
    upperUnit exponent • point ∈ UpperChamber := by
  cases point with
  | none => exact point_mem.elim
  | some value =>
    change |value| < 2 / 3 at point_mem
    rw [upperUnit_smul_some]
    change 1 < |value + 3 * exponent|
    have exponent_abs : (1 : ℚ) ≤ |(exponent : ℚ)| := by
      exact_mod_cast Int.one_le_abs exponent_ne
    calc
      1 < 3 * |(exponent : ℚ)| - |value| := by linarith
      _ = |3 * (exponent : ℚ)| - |value| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℚ) ≤ 3)]
      _ ≤ |value + 3 * exponent| := by
        simpa [add_comm] using
          abs_sub_abs_le_abs_sub (3 * (exponent : ℚ)) (-value)

private theorem lower_maps_upper
    (exponent : ℤ) (exponent_ne : exponent ≠ 0)
    (point : RationalPoint) (point_mem : point ∈ UpperChamber) :
    lowerUnit exponent • point ∈ LowerChamber := by
  cases point with
  | some value =>
    change 1 < |value| at point_mem
    have exponent_abs : (1 : ℚ) ≤ |(exponent : ℚ)| := by
      exact_mod_cast Int.one_le_abs exponent_ne
    have reverse_bound :
        3 * |(exponent : ℚ)| * |value| - 1 ≤
          |3 * exponent * value + 1| := by
      calc
        3 * |(exponent : ℚ)| * |value| - 1 =
            |3 * (exponent : ℚ) * value| - |(1 : ℚ)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℚ) ≤ 3), abs_one]
        _ ≤ |3 * exponent * value + 1| := by
          simpa only [abs_neg, sub_neg_eq_add] using
            abs_sub_abs_le_abs_sub (3 * exponent * value) (-1)
    have coefficient_pos : 0 < 3 * |(exponent : ℚ)| := by positivity
    have scaled_value :
        3 * |(exponent : ℚ)| <
          3 * |(exponent : ℚ)| * |value| := by
      simpa only [mul_one] using mul_lt_mul_of_pos_left point_mem coefficient_pos
    have product_gt_three :
        3 < 3 * |(exponent : ℚ)| * |value| := by
      have coefficient_lower : (3 : ℚ) ≤ 3 * |(exponent : ℚ)| := by nlinarith
      exact coefficient_lower.trans_lt scaled_value
    have denominator_abs : 2 < |3 * exponent * value + 1| := by linarith
    have denominator_ne : 3 * (exponent : ℚ) * value + 1 ≠ 0 := by
      intro denominator_zero
      rw [denominator_zero, abs_zero] at denominator_abs
      linarith
    rw [lowerUnit_smul_some exponent value denominator_ne]
    change |value / (3 * exponent * value + 1)| < 2 / 3
    rw [abs_div]
    have denominator_pos : 0 < |3 * (exponent : ℚ) * value + 1| := by linarith
    apply (div_lt_iff₀ denominator_pos).mpr
    have value_nonneg : 0 ≤ |value| := abs_nonneg value
    have scaled_exponent :
        |value| ≤ |(exponent : ℚ)| * |value| :=
      by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right exponent_abs value_nonneg
    nlinarith [reverse_bound, scaled_exponent]
  | none =>
    rw [lowerUnit_smul_none exponent exponent_ne]
    change |1 / (3 * (exponent : ℚ))| < 2 / 3
    rw [abs_div, abs_one, abs_mul, abs_of_nonneg (by norm_num : (0 : ℚ) ≤ 3)]
    have exponent_abs : (1 : ℚ) ≤ |(exponent : ℚ)| := by
      exact_mod_cast Int.one_le_abs exponent_ne
    have denominator_pos : 0 < 3 * |(exponent : ℚ)| := by positivity
    apply (div_lt_iff₀ denominator_pos).mpr
    norm_num
    nlinarith [exponent_abs]

private theorem factor_maps_other_chamber :
    Pairwise fun left right => ∀ power : Multiplicative ℤ, power ≠ 1 →
      factor left power • (if right then LowerChamber else UpperChamber) ⊆
        if left then LowerChamber else UpperChamber := by
  intro left right distinct power power_ne
  cases left <;> cases right
  · exact (distinct rfl).elim
  · rintro point ⟨origin, origin_mem, rfl⟩
    exact upper_maps_lower (Multiplicative.toAdd power) (by simpa using power_ne)
      origin origin_mem
  · rintro point ⟨origin, origin_mem, rfl⟩
    exact lower_maps_upper (Multiplicative.toAdd power) (by simpa using power_ne)
      origin origin_mem
  · exact (distinct rfl).elim

private theorem factor_maps_source
    (index : Bool) (power : Multiplicative ℤ) (power_ne : power ≠ 1) :
    factor index power • sourcePoint ∈ if index then LowerChamber else UpperChamber := by
  cases index
  · change upperUnit (Multiplicative.toAdd power) • sourcePoint ∈ UpperChamber
    rw [show sourcePoint = some 1 by rfl]
    rw [upperUnit_smul_some]
    change 1 < |(1 : ℚ) + 3 * Multiplicative.toAdd power|
    have exponent_ne : Multiplicative.toAdd power ≠ 0 := by simpa using power_ne
    by_cases exponent_pos : 0 < Multiplicative.toAdd power
    · have expression_pos :
          0 < (1 : ℚ) + 3 * Multiplicative.toAdd power := by
        exact_mod_cast show
          (0 : ℤ) < 1 + 3 * Multiplicative.toAdd power by omega
      rw [abs_of_pos expression_pos]
      exact_mod_cast show
        (1 : ℤ) < 1 + 3 * Multiplicative.toAdd power by omega
    · have exponent_neg : Multiplicative.toAdd power < 0 := by omega
      have expression_nonpos :
          (1 : ℚ) + 3 * Multiplicative.toAdd power ≤ 0 := by
        exact_mod_cast show
          (1 : ℤ) + 3 * Multiplicative.toAdd power ≤ 0 by omega
      rw [abs_of_nonpos expression_nonpos]
      exact_mod_cast show
        (1 : ℤ) < -(1 + 3 * Multiplicative.toAdd power) by omega
  · let exponent := Multiplicative.toAdd power
    have exponent_ne : exponent ≠ 0 := by simpa [exponent] using power_ne
    have denominator_ne : (3 : ℚ) * exponent + 1 ≠ 0 := by
      exact_mod_cast show (3 : ℤ) * exponent + 1 ≠ 0 by omega
    change lowerUnit exponent • sourcePoint ∈ LowerChamber
    rw [show sourcePoint = some 1 by rfl]
    rw [lowerUnit_smul_some exponent 1 (by simpa using denominator_ne)]
    change |1 / ((3 : ℚ) * exponent * 1 + 1)| < 2 / 3
    simp only [mul_one]
    rw [abs_div, abs_one]
    have denominator_abs_int : (2 : ℤ) ≤ |3 * exponent + 1| := by
      by_cases exponent_pos : 0 < exponent
      · rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ 3 * exponent + 1)]
        omega
      · have exponent_neg : exponent < 0 := by omega
        rw [abs_of_nonpos (by omega : (3 : ℤ) * exponent + 1 ≤ 0)]
        omega
    have denominator_abs : (2 : ℚ) ≤ |(3 : ℚ) * exponent + 1| := by
      exact_mod_cast denominator_abs_int
    have denominator_pos : 0 < |(3 : ℚ) * exponent + 1| := by linarith
    apply (div_lt_iff₀ denominator_pos).mpr
    nlinarith

/-! ## Free orbit -/

/-- The ping-pong chamber owned by one cyclic shear factor. -/
def chamber (index : Bool) : Set RationalPoint :=
  if index then LowerChamber else UpperChamber

/-- Free product of the two infinite cyclic shear factors. -/
abbrev ShearFreeProduct :=
  Monoid.CoprodI fun _ : Bool => Multiplicative ℤ

/-- Canonical representation of the two-factor free product by rational shears. -/
def shearRepresentation :
    ShearFreeProduct →* Matrix.GeneralLinearGroup (Fin 2) ℚ :=
  Monoid.CoprodI.lift factor

theorem shearRepresentation_upper (exponent : ℤ) :
    shearRepresentation
        (Monoid.CoprodI.of (i := false) (Multiplicative.ofAdd exponent)) =
      upperUnit exponent := by
  rw [shearRepresentation, Monoid.CoprodI.lift_of]
  rfl

theorem shearRepresentation_lower (exponent : ℤ) :
    shearRepresentation
        (Monoid.CoprodI.of (i := true) (Multiplicative.ofAdd exponent)) =
      lowerUnit exponent := by
  rw [shearRepresentation, Monoid.CoprodI.lift_of]
  rfl

/-- Five-factor free-product spelling of the congruence bridge. -/
def bridgeWord (exponent correction : ℤ) : ShearFreeProduct :=
  Monoid.CoprodI.of (i := true) (Multiplicative.ofAdd exponent) *
    Monoid.CoprodI.of (i := false) (Multiplicative.ofAdd (3 * exponent)) *
    Monoid.CoprodI.of (i := true) (Multiplicative.ofAdd (2 * exponent)) *
    Monoid.CoprodI.of (i := false)
      (Multiplicative.ofAdd (-3 * exponent * correction)) *
    Monoid.CoprodI.of (i := false) (Multiplicative.ofAdd correction)

/-- The abstract five-factor word is represented by the literal integral bridge matrix. -/
theorem shearRepresentation_bridgeWord (exponent correction : ℤ) :
    (shearRepresentation (bridgeWord exponent correction) : Square₂ ℚ) =
      bridgeMatrix (3 * (exponent : ℚ)) (correction : ℚ) := by
  simp only [bridgeWord, map_mul, shearRepresentation_upper,
    shearRepresentation_lower]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [upperUnit, lowerUnit, bridgeMatrix, upperShear, lowerShear,
      Matrix.mul_apply, Fin.sum_univ_succ]
    ring_nf
    simp
  · simp [upperUnit, lowerUnit, bridgeMatrix, upperShear, lowerShear,
      Matrix.mul_apply, Fin.sum_univ_succ]
    ring
  · simp [upperUnit, lowerUnit, bridgeMatrix, upperShear, lowerShear,
      Matrix.mul_apply, Fin.sum_univ_succ]
    ring_nf
    simp
  · simp [upperUnit, lowerUnit, bridgeMatrix, upperShear, lowerShear,
      Matrix.mul_apply, Fin.sum_univ_succ]
    ring

private theorem reducedWord_maps_source
    {first last : Bool}
    (word : Monoid.CoprodI.NeWord (fun _ : Bool => Multiplicative ℤ) first last) :
    shearRepresentation word.prod • sourcePoint ∈ chamber first := by
  induction word with
  | @singleton index power power_ne =>
      simpa [shearRepresentation, chamber] using
        factor_maps_source index power power_ne
  | @append first middle next last left distinct right left_induction right_induction =>
      have mapped_chamber :
          shearRepresentation left.prod • chamber next ⊆ chamber first := by
        simpa [shearRepresentation, chamber] using
          Monoid.CoprodI.lift_word_ping_pong factor chamber
            (by simpa [chamber] using factor_maps_other_chamber) left distinct
      rw [Monoid.CoprodI.NeWord.append_prod, map_mul, mul_smul]
      apply mapped_chamber
      exact ⟨shearRepresentation right.prod • sourcePoint, right_induction, rfl⟩

/-- The source and target rays both lie in the gap between the ping-pong chambers. -/
theorem source_target_outside_chambers (index : Bool) :
    sourcePoint ∉ chamber index ∧ targetPoint ∉ chamber index := by
  cases index
  · constructor
    · change ¬1 < |(1 : ℚ)|
      norm_num
    · change ¬1 < |(10 / 13 : ℚ)|
      norm_num [abs_of_nonneg]
  · constructor
    · change ¬|(1 : ℚ)| < 2 / 3
      norm_num
    · change ¬|(10 / 13 : ℚ)| < 2 / 3
      norm_num [abs_of_nonneg]

/-- Every nonidentity free-product word moves the source into the chamber of its first factor. -/
theorem nontrivial_maps_source_into_chamber
    {word : ShearFreeProduct} (word_ne : word ≠ 1) :
    ∃ index, shearRepresentation word • sourcePoint ∈ chamber index := by
  let reduced := Monoid.CoprodI.Word.equiv word
  have reduced_ne : reduced ≠ Monoid.CoprodI.Word.empty := by
    intro reduced_empty
    apply word_ne
    have restored := congrArg Monoid.CoprodI.Word.equiv.symm reduced_empty
    calc
      word = Monoid.CoprodI.Word.equiv.symm Monoid.CoprodI.Word.empty := by
        simpa [reduced] using restored
      _ = 1 := by rfl
  obtain ⟨first, last, normal, normal_eq⟩ :=
    Monoid.CoprodI.NeWord.of_word reduced reduced_ne
  have normal_prod : normal.prod = word := by
    change normal.toWord.prod = word
    rw [normal_eq]
    exact Monoid.CoprodI.Word.equiv.symm_apply_apply word
  refine ⟨first, ?_⟩
  simpa [normal_prod] using reducedWord_maps_source normal

/-- No word in the two rational shears sends `[1:1]` to `[10:13]`. -/
theorem targetPoint_not_reachable (word : ShearFreeProduct) :
    shearRepresentation word • sourcePoint ≠ targetPoint := by
  by_cases word_one : word = 1
  · subst word
    norm_num [sourcePoint, targetPoint]
  · obtain ⟨index, moved_mem⟩ := nontrivial_maps_source_into_chamber word_one
    intro target_eq
    rw [target_eq] at moved_mem
    exact (source_target_outside_chambers index).2 moved_mem

/-- The source ray has trivial stabilizer in the abstract shear free product. -/
theorem sourcePoint_stabilizer_trivial
    {word : ShearFreeProduct}
    (fixed : shearRepresentation word • sourcePoint = sourcePoint) :
    word = 1 := by
  by_contra word_ne
  obtain ⟨index, moved_mem⟩ := nontrivial_maps_source_into_chamber word_ne
  rw [fixed] at moved_mem
  exact (source_target_outside_chambers index).1 moved_mem

/-- Ping-pong makes the rational shear representation faithful. -/
theorem shearRepresentation_injective : Function.Injective shearRepresentation := by
  apply (injective_iff_map_eq_one shearRepresentation).mpr
  intro word mapped_one
  apply sourcePoint_stabilizer_trivial
  rw [mapped_one, one_smul]

end MatrixMortality.CongruenceBlindOrbit
