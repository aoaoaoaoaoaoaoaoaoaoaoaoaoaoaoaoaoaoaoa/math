import MatrixMortality.LinearRepresentation
import MatrixMortality.ScheduledBinary

/-!
# Exact rank of the width-three scheduled compiler

The scheduled compiler has five native coordinates when the deletion width is three. This file
certifies that all five are necessary whenever the tag body is nonempty. The lower bound does
not assume that a competing representation resembles the scheduled matrices: it applies to
every exact rational linear representation of the same coefficient series.
-/

namespace MatrixMortality

open scoped Matrix

/-- Prefixes exposing five independent rows of the width-three Hankel matrix. -/
def scheduledWidthThreePrefixes : Fin 5 → List Bool :=
  ![[], [false], [true], [false, false], [true, false]]

/-- Suffixes exposing five independent columns of the width-three Hankel matrix. -/
def scheduledWidthThreeSuffixes : Fin 5 → List Bool :=
  ![[], [false], [true], [false, false], [false, true]]

/-- The certified integer Hankel minor. -/
def scheduledWidthThreeHankel (body : List TagLetter) : Matrix (Fin 5) (Fin 5) ℤ :=
  finiteHankel (scheduledCoefficient ℤ 3 body (by decide))
    scheduledWidthThreePrefixes scheduledWidthThreeSuffixes

/-- Closed form of the certified Hankel minor. -/
def scheduledWidthThreeHankelClosed
    (body : List TagLetter) : Matrix (Fin 5) (Fin 5) ℤ :=
  let r := ternaryCode (nearyLower 3 body (.rule .c))
  !![67, 16509, 228, 4012155, 55872;
     16509, 4012155, 55872, 974954637, 13578093 - 9 * r;
     228, 49554, 711, 12036276, 167652 - 9 * r;
     4012155, 974954637, 13578093 - 9 * r, 236914032195, 3299477328;
     49554, 12036276, 167652 - 9 * r, 2924864154, 40733847]

theorem scheduledWidthThreeHankel_eq_closed (body : List TagLetter) :
    scheduledWidthThreeHankel body = scheduledWidthThreeHankelClosed body := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [scheduledWidthThreeHankel, scheduledWidthThreeHankelClosed,
      finiteHankel, scheduledWidthThreePrefixes, scheduledWidthThreeSuffixes,
      scheduledCoefficient_eq_sideCoefficient, sideCoefficient_eq_ternaryCode_sub,
      decodeScheduled, decodeScheduledFrom_nil, decodeScheduledFrom_cons,
      scheduledInitialPhase, scheduledNextPhase,
      scheduledTile, scheduledPhase, scheduledLetter, PairPhase.tile, spell, nearyMarker,
      nearyUpper, nearyLower, tagCode, ternaryCode_append, ternaryCode_cons, ternaryDigit,
      List.replicate_succ, pow_add] <;>
    ring

/-- Reachable-row factor of the certified minor. -/
def scheduledWidthThreeReachable : Matrix (Fin 5) (Fin 5) ℤ :=
  !![67, 81, -1, 0, 0;
     16509, 19683, 0, -3, 0;
     228, 243, 0, -3, 0;
     4012155, 4782969, 0, 0, -9;
     49554, 59049, 0, 0, -9]

/-- Observable-column factor of the certified minor. -/
def scheduledWidthThreeObservable
    (body : List TagLetter) : Matrix (Fin 5) (Fin 5) ℤ :=
  let r := ternaryCode (nearyLower 3 body (.rule .c))
  !![1, 1, 1, 1, 1;
     0, 203, 2, 49532, 689;
     0, 1, 1, 4, 4;
     0, 1, 1, 76, 3 * r + 1;
     0, 25, r, 52, 52]

theorem scheduledWidthThreeHankelClosed_factor (body : List TagLetter) :
    scheduledWidthThreeHankelClosed body =
      scheduledWidthThreeReachable * scheduledWidthThreeObservable body := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [scheduledWidthThreeHankelClosed, scheduledWidthThreeReachable,
      scheduledWidthThreeObservable, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

/-- A scaled inverse certificate for the reachable-row factor. -/
def scheduledWidthThreeReachableAdjugate : Matrix (Fin 5) (Fin 5) ℤ :=
  !![0, 127545840, -127545840, -524880, 524880;
     0, -106990227, 106990227, 439587, -439587;
     3316191840, -120637107, 120637107, 439587, -439587;
     0, 1027275453, 78121827, -4284333, 4284333;
     0, 304515693, -304515693, -5858973, 374324733]

theorem scheduledWidthThreeReachable_adjugate_mul :
    scheduledWidthThreeReachableAdjugate * scheduledWidthThreeReachable =
      (-3316191840 : ℤ) • (1 : Matrix (Fin 5) (Fin 5) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [scheduledWidthThreeReachableAdjugate, scheduledWidthThreeReachable,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
    simp [Fin.ext_iff] <;>
    omega

theorem scheduledWidthThreeReachable_det_ne_zero :
    scheduledWidthThreeReachable.det ≠ 0 := by
  have scaled_det :
      ((-3316191840 : ℤ) • (1 : Matrix (Fin 5) (Fin 5) ℤ)).det =
        (-3316191840 : ℤ) ^ 5 := by
    rw [Matrix.det_smul, Matrix.det_one]
    norm_num
  intro det_zero
  have product_det_zero :
      (scheduledWidthThreeReachableAdjugate * scheduledWidthThreeReachable).det = 0 := by
    rw [Matrix.det_mul, det_zero, mul_zero]
  have determinant_identity :=
    congrArg Matrix.det scheduledWidthThreeReachable_adjugate_mul
  rw [product_det_zero, scaled_det] at determinant_identity
  norm_num at determinant_identity

/-- The four-dimensional minor left after expanding the observable determinant. -/
def scheduledWidthThreeObservableMinor
    (body : List TagLetter) : Matrix (Fin 4) (Fin 4) ℤ :=
  let r := ternaryCode (nearyLower 3 body (.rule .c))
  !![203, 2, 49532, 689;
     1, 1, 4, 4;
     1, 1, 76, 3 * r + 1;
     25, r, 52, 52]

theorem scheduledWidthThreeObservable_det_eq_minor (body : List TagLetter) :
    (scheduledWidthThreeObservable body).det =
      (scheduledWidthThreeObservableMinor body).det := by
  rw [← Matrix.det_transpose]
  rw [Matrix.det_succ_row_zero]
  norm_num [scheduledWidthThreeObservable, Fin.sum_univ_succ, Matrix.submatrix,
    Matrix.transpose_apply]
  change ((scheduledWidthThreeObservableMinor body)ᵀ).det =
    (scheduledWidthThreeObservableMinor body).det
  exact Matrix.det_transpose _

theorem scheduledWidthThreeObservableMinor_det (body : List TagLetter) :
    (scheduledWidthThreeObservableMinor body).det =
      3 * (ternaryCode (nearyLower 3 body (.rule .c)) - 25) *
        (55416 - 48720 * ternaryCode (nearyLower 3 body (.rule .c))) := by
  have succAbove_two_two :
      Fin.succAbove (2 : Fin 4) (2 : Fin 3) = (3 : Fin 4) := rfl
  have succAbove_one_two :
      Fin.succAbove (1 : Fin 4) (2 : Fin 3) = (3 : Fin 4) := rfl
  have castSucc_two : Fin.castSucc (2 : Fin 3) = (2 : Fin 4) := rfl
  rw [Matrix.det_succ_row_zero]
  norm_num [scheduledWidthThreeObservableMinor, Fin.sum_univ_succ,
    Matrix.det_fin_three, succAbove_two_two, succAbove_one_two, castSucc_two]
  ring

theorem ternaryCode_nearyLower_three_rule_c_large (body : List TagLetter)
    (body_nonempty : body ≠ []) :
    25 < ternaryCode (nearyLower 3 body (.rule .c)) := by
  have encoded_nonempty : tagEncode 3 body ≠ [] :=
    (tagEncode_eq_nil_iff 3 body).not.mpr body_nonempty
  have lower_length : 4 ≤ (nearyLower 3 body (.rule .c)).length := by
    simp only [nearyLower, nearyBody, List.length_append, List.length_cons, List.length_nil]
    have encoded_length := List.length_pos.mpr encoded_nonempty
    omega
  have lower_nonempty : nearyLower 3 body (.rule .c) ≠ [] := by
    simp [nearyLower, nearyBody]
  have code_bound :=
    ternaryCode_lower_bound (nearyLower 3 body (.rule .c)) lower_nonempty
  have exponent_bound : 3 ≤ (nearyLower 3 body (.rule .c)).length - 1 := by
    omega
  have twenty_seven_le :
      27 ≤ 3 ^ ((nearyLower 3 body (.rule .c)).length - 1) := by
    change 3 ^ 3 ≤ 3 ^ ((nearyLower 3 body (.rule .c)).length - 1)
    exact Nat.pow_le_pow_right (by norm_num) exponent_bound
  omega

theorem scheduledWidthThreeObservable_det_ne_zero (body : List TagLetter)
    (lower_code_large : 25 < ternaryCode (nearyLower 3 body (.rule .c))) :
    (scheduledWidthThreeObservable body).det ≠ 0 := by
  rw [scheduledWidthThreeObservable_det_eq_minor,
    scheduledWidthThreeObservableMinor_det]
  have first_ne :
      (ternaryCode (nearyLower 3 body (.rule .c)) : ℤ) - 25 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast ne_of_gt lower_code_large)
  have second_ne :
      55416 - 48720 * (ternaryCode (nearyLower 3 body (.rule .c)) : ℤ) ≠ 0 := by
    omega
  exact mul_ne_zero (mul_ne_zero (by norm_num) first_ne) second_ne

/-- A nonempty body makes the certified integer Hankel minor nonsingular. -/
theorem scheduledWidthThreeHankel_det_ne_zero (body : List TagLetter)
    (body_nonempty : body ≠ []) :
    (scheduledWidthThreeHankel body).det ≠ 0 := by
  rw [scheduledWidthThreeHankel_eq_closed, scheduledWidthThreeHankelClosed_factor,
    Matrix.det_mul]
  exact mul_ne_zero scheduledWidthThreeReachable_det_ne_zero
    (scheduledWidthThreeObservable_det_ne_zero body
      (ternaryCode_nearyLower_three_rule_c_large body body_nonempty))

/-- Rational form of the certified Hankel minor. -/
def scheduledWidthThreeHankelRat
    (body : List TagLetter) : Matrix (Fin 5) (Fin 5) ℚ :=
  finiteHankel (scheduledCoefficient ℚ 3 body (by decide))
    scheduledWidthThreePrefixes scheduledWidthThreeSuffixes

theorem scheduledWidthThreeHankelRat_eq_castMatrix (body : List TagLetter) :
    scheduledWidthThreeHankelRat body =
      castMatrix (scheduledWidthThreeHankel body) := by
  ext i j
  simp only [scheduledWidthThreeHankelRat, finiteHankel, castMatrix, Matrix.map_apply,
    scheduledWidthThreeHankel]
  rw [scheduledCoefficient_eq_sideCoefficient ℚ,
    sideCoefficient_eq_ternaryCode_sub ℚ]
  rw [scheduledCoefficient_eq_sideCoefficient ℤ,
    sideCoefficient_eq_ternaryCode_sub ℤ]
  norm_num

theorem scheduledWidthThreeHankelRat_det_ne_zero (body : List TagLetter)
    (body_nonempty : body ≠ []) :
    (scheduledWidthThreeHankelRat body).det ≠ 0 := by
  rw [scheduledWidthThreeHankelRat_eq_castMatrix, castMatrix_det]
  exact Int.cast_ne_zero.mpr
    (scheduledWidthThreeHankel_det_ne_zero body body_nonempty)

/-- Every exact rational representation has at least five states. -/
theorem scheduledWidthThree_exact_state_lower_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (body : List TagLetter) (body_nonempty : body ≠ [])
    (generators : Bool → Matrix ι ι ℚ) (row column : ι → ℚ)
    (exact : RepresentsSeries
      (scheduledCoefficient ℚ 3 body (by decide)) generators row column) :
    5 ≤ Fintype.card ι := by
  exact
    finiteHankel_card_le (scheduledCoefficient ℚ 3 body (by decide))
      scheduledWidthThreePrefixes scheduledWidthThreeSuffixes generators row column exact
      (scheduledWidthThreeHankelRat_det_ne_zero body body_nonempty)

/-- The native scheduled representation has exactly five coordinates. -/
theorem scheduledWidthThree_native_state_card :
    Fintype.card (ScheduledIndex 3) = 5 := by
  simp [ScheduledIndex]

/-- The native matrices realize the series exactly. -/
theorem scheduledWidthThree_native_represents (body : List TagLetter) :
    RepresentsSeries (scheduledCoefficient ℚ 3 body (by decide))
      (scheduledGenerator ℚ 3 body (by decide))
      (scheduledBoundaryRow ℚ 3 (by decide))
      (scheduledBoundaryColumn ℚ 3) := by
  intro word
  rfl

end MatrixMortality
