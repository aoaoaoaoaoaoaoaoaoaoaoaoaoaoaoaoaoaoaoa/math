import MatrixMortality.LinearRepresentation
import MatrixMortality.NearySideNormal
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

@[simp] private theorem scheduledWidthThreePrefixes_zero :
    scheduledWidthThreePrefixes 0 = [] := rfl

@[simp] private theorem scheduledWidthThreePrefixes_one :
    scheduledWidthThreePrefixes 1 = [false] := rfl

@[simp] private theorem scheduledWidthThreePrefixes_two :
    scheduledWidthThreePrefixes 2 = [true] := rfl

@[simp] private theorem scheduledWidthThreePrefixes_three :
    scheduledWidthThreePrefixes 3 = [false, false] := rfl

@[simp] private theorem scheduledWidthThreePrefixes_four :
    scheduledWidthThreePrefixes 4 = [true, false] := rfl

@[simp] private theorem scheduledWidthThreeSuffixes_zero :
    scheduledWidthThreeSuffixes 0 = [] := rfl

@[simp] private theorem scheduledWidthThreeSuffixes_one :
    scheduledWidthThreeSuffixes 1 = [false] := rfl

@[simp] private theorem scheduledWidthThreeSuffixes_two :
    scheduledWidthThreeSuffixes 2 = [true] := rfl

@[simp] private theorem scheduledWidthThreeSuffixes_three :
    scheduledWidthThreeSuffixes 3 = [false, false] := rfl

@[simp] private theorem scheduledWidthThreeSuffixes_four :
    scheduledWidthThreeSuffixes 4 = [false, true] := rfl

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

local macro "crush_scheduled_decode" : tactic =>
  `(tactic|
    norm_num [decodeScheduled, decodeScheduledFrom_nil, decodeScheduledFrom_cons,
      scheduledInitialPhase, scheduledNextPhase, scheduledTile, scheduledPhase,
      scheduledLetter, PairPhase.tile])

@[simp] private theorem decodeScheduled_three_nil :
    decodeScheduled (β := 3) (by decide) [] = [] := by
  crush_scheduled_decode

@[simp] private theorem decodeScheduled_three_false :
    decodeScheduled (β := 3) (by decide) [false] = [.erase .b] := by
  crush_scheduled_decode

@[simp] private theorem decodeScheduled_three_true :
    decodeScheduled (β := 3) (by decide) [true] = [.erase .c] := by
  crush_scheduled_decode

@[simp] private theorem decodeScheduled_three_false_false :
    decodeScheduled (β := 3) (by decide) [false, false] = [.erase .b, .erase .b] := by
  crush_scheduled_decode

@[simp] private theorem decodeScheduled_three_false_true :
    decodeScheduled (β := 3) (by decide) [false, true] = [.erase .c, .erase .b] := by
  crush_scheduled_decode

@[simp] private theorem decodeScheduled_three_true_false :
    decodeScheduled (β := 3) (by decide) [true, false] = [.erase .b, .erase .c] := by
  crush_scheduled_decode

@[simp] private theorem decodeScheduled_three_true_true :
    decodeScheduled (β := 3) (by decide) [true, true] = [.erase .c, .erase .c] := by
  crush_scheduled_decode

@[simp] private theorem decodeScheduled_three_false_false_false :
    decodeScheduled (β := 3) (by decide) [false, false, false] =
      [.rule .b, .erase .b, .erase .b] := by
  crush_scheduled_decode

@[simp] private theorem decodeScheduled_three_false_false_true :
    decodeScheduled (β := 3) (by decide) [false, false, true] =
      [.rule .c, .erase .b, .erase .b] := by
  crush_scheduled_decode

@[simp] private theorem decodeScheduled_three_true_false_false :
    decodeScheduled (β := 3) (by decide) [true, false, false] =
      [.rule .b, .erase .b, .erase .c] := by
  crush_scheduled_decode

@[simp] private theorem decodeScheduled_three_true_false_true :
    decodeScheduled (β := 3) (by decide) [true, false, true] =
      [.rule .c, .erase .b, .erase .c] := by
  crush_scheduled_decode

@[simp] private theorem decodeScheduled_three_false_false_false_false :
    decodeScheduled (β := 3) (by decide) [false, false, false, false] =
      [.erase .b, .rule .b, .erase .b, .erase .b] := by
  crush_scheduled_decode

@[simp] private theorem decodeScheduled_three_false_false_false_true :
    decodeScheduled (β := 3) (by decide) [false, false, false, true] =
      [.erase .c, .rule .b, .erase .b, .erase .b] := by
  crush_scheduled_decode

@[simp] private theorem decodeScheduled_three_true_false_false_false :
    decodeScheduled (β := 3) (by decide) [true, false, false, false] =
      [.erase .b, .rule .b, .erase .b, .erase .c] := by
  crush_scheduled_decode

@[simp] private theorem decodeScheduled_three_true_false_false_true :
    decodeScheduled (β := 3) (by decide) [true, false, false, true] =
      [.erase .c, .rule .b, .erase .b, .erase .c] := by
  crush_scheduled_decode

@[simp] private theorem nearyLower_three_rule_b_length (body : List TagLetter) :
    (nearyLower 3 body (.rule .b)).length = 3 := by
  simp [nearyLower]

@[simp] private theorem nearyLower_three_erase_length (body : List TagLetter)
    (letter : TagLetter) :
    (nearyLower 3 body (.erase letter)).length = 1 := by
  cases letter <;> simp [nearyLower]

local macro "crush_scheduled_hankel_entry" : tactic =>
  `(tactic|
    norm_num [scheduledWidthThreeHankel, scheduledWidthThreeHankelClosed,
      finiteHankel, scheduledWidthThreePrefixes, scheduledWidthThreeSuffixes,
      scheduledCoefficient_eq_sideCoefficient, sideCoefficient_eq_ternaryCode_sub,
      spell, nearyMarker,
      nearyUpper, tagCode, ternaryCode_append, ternaryCode_cons, ternaryDigit,
      ternaryCode_neary_rule_b, ternaryCode_neary_erase,
      List.replicate_succ, pow_add, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four] <;>
    ring)

@[simp] private theorem scheduledWidthThreeHankel_entry_zero_zero (body : List TagLetter) :
    scheduledWidthThreeHankel body 0 0 = scheduledWidthThreeHankelClosed body 0 0 := by
  crush_scheduled_hankel_entry

@[simp] private theorem scheduledWidthThreeHankel_entry_zero_one (body : List TagLetter) :
    scheduledWidthThreeHankel body 0 1 = scheduledWidthThreeHankelClosed body 0 1 := by
  crush_scheduled_hankel_entry

@[simp] private theorem scheduledWidthThreeHankel_entry_zero_two (body : List TagLetter) :
    scheduledWidthThreeHankel body 0 2 = scheduledWidthThreeHankelClosed body 0 2 := by
  crush_scheduled_hankel_entry

@[simp] private theorem scheduledWidthThreeHankel_entry_zero_three (body : List TagLetter) :
    scheduledWidthThreeHankel body 0 3 = scheduledWidthThreeHankelClosed body 0 3 := by
  crush_scheduled_hankel_entry

@[simp] private theorem scheduledWidthThreeHankel_entry_zero_four (body : List TagLetter) :
    scheduledWidthThreeHankel body 0 4 = scheduledWidthThreeHankelClosed body 0 4 := by
  crush_scheduled_hankel_entry

@[simp] private theorem scheduledWidthThreeHankel_entry_one_zero (body : List TagLetter) :
    scheduledWidthThreeHankel body 1 0 = scheduledWidthThreeHankelClosed body 1 0 := by
  crush_scheduled_hankel_entry

@[simp] private theorem scheduledWidthThreeHankel_entry_one_one (body : List TagLetter) :
    scheduledWidthThreeHankel body 1 1 = scheduledWidthThreeHankelClosed body 1 1 := by
  crush_scheduled_hankel_entry

@[simp] private theorem scheduledWidthThreeHankel_entry_one_two (body : List TagLetter) :
    scheduledWidthThreeHankel body 1 2 = scheduledWidthThreeHankelClosed body 1 2 := by
  crush_scheduled_hankel_entry

@[simp] private theorem scheduledWidthThreeHankel_entry_one_three (body : List TagLetter) :
    scheduledWidthThreeHankel body 1 3 = scheduledWidthThreeHankelClosed body 1 3 := by
  crush_scheduled_hankel_entry

@[simp] private theorem scheduledWidthThreeHankel_entry_one_four (body : List TagLetter) :
    scheduledWidthThreeHankel body 1 4 = scheduledWidthThreeHankelClosed body 1 4 := by
  crush_scheduled_hankel_entry

@[simp] private theorem scheduledWidthThreeHankel_entry_two_zero (body : List TagLetter) :
    scheduledWidthThreeHankel body 2 0 = scheduledWidthThreeHankelClosed body 2 0 := by
  crush_scheduled_hankel_entry

@[simp] private theorem scheduledWidthThreeHankel_entry_two_one (body : List TagLetter) :
    scheduledWidthThreeHankel body 2 1 = scheduledWidthThreeHankelClosed body 2 1 := by
  crush_scheduled_hankel_entry

@[simp] private theorem scheduledWidthThreeHankel_entry_two_two (body : List TagLetter) :
    scheduledWidthThreeHankel body 2 2 = scheduledWidthThreeHankelClosed body 2 2 := by
  crush_scheduled_hankel_entry

@[simp] private theorem scheduledWidthThreeHankel_entry_two_three (body : List TagLetter) :
    scheduledWidthThreeHankel body 2 3 = scheduledWidthThreeHankelClosed body 2 3 := by
  crush_scheduled_hankel_entry

@[simp] private theorem scheduledWidthThreeHankel_entry_two_four (body : List TagLetter) :
    scheduledWidthThreeHankel body 2 4 = scheduledWidthThreeHankelClosed body 2 4 := by
  crush_scheduled_hankel_entry

@[simp] private theorem scheduledWidthThreeHankel_entry_three_zero (body : List TagLetter) :
    scheduledWidthThreeHankel body 3 0 = scheduledWidthThreeHankelClosed body 3 0 := by
  crush_scheduled_hankel_entry

@[simp] private theorem scheduledWidthThreeHankel_entry_three_one (body : List TagLetter) :
    scheduledWidthThreeHankel body 3 1 = scheduledWidthThreeHankelClosed body 3 1 := by
  crush_scheduled_hankel_entry

@[simp] private theorem scheduledWidthThreeHankel_entry_three_two (body : List TagLetter) :
    scheduledWidthThreeHankel body 3 2 = scheduledWidthThreeHankelClosed body 3 2 := by
  crush_scheduled_hankel_entry

@[simp] private theorem scheduledWidthThreeHankel_entry_three_three (body : List TagLetter) :
    scheduledWidthThreeHankel body 3 3 = scheduledWidthThreeHankelClosed body 3 3 := by
  crush_scheduled_hankel_entry

@[simp] private theorem scheduledWidthThreeHankel_entry_three_four (body : List TagLetter) :
    scheduledWidthThreeHankel body 3 4 = scheduledWidthThreeHankelClosed body 3 4 := by
  crush_scheduled_hankel_entry

@[simp] private theorem scheduledWidthThreeHankel_entry_four_zero (body : List TagLetter) :
    scheduledWidthThreeHankel body 4 0 = scheduledWidthThreeHankelClosed body 4 0 := by
  crush_scheduled_hankel_entry

@[simp] private theorem scheduledWidthThreeHankel_entry_four_one (body : List TagLetter) :
    scheduledWidthThreeHankel body 4 1 = scheduledWidthThreeHankelClosed body 4 1 := by
  crush_scheduled_hankel_entry

@[simp] private theorem scheduledWidthThreeHankel_entry_four_two (body : List TagLetter) :
    scheduledWidthThreeHankel body 4 2 = scheduledWidthThreeHankelClosed body 4 2 := by
  crush_scheduled_hankel_entry

@[simp] private theorem scheduledWidthThreeHankel_entry_four_three (body : List TagLetter) :
    scheduledWidthThreeHankel body 4 3 = scheduledWidthThreeHankelClosed body 4 3 := by
  crush_scheduled_hankel_entry

@[simp] private theorem scheduledWidthThreeHankel_entry_four_four (body : List TagLetter) :
    scheduledWidthThreeHankel body 4 4 = scheduledWidthThreeHankelClosed body 4 4 := by
  crush_scheduled_hankel_entry

private theorem scheduledWidthThreeHankel_row_zero (body : List TagLetter) :
    scheduledWidthThreeHankel body 0 = scheduledWidthThreeHankelClosed body 0 := by
  ext j
  fin_cases j <;> simp

private theorem scheduledWidthThreeHankel_row_one (body : List TagLetter) :
    scheduledWidthThreeHankel body 1 = scheduledWidthThreeHankelClosed body 1 := by
  ext j
  fin_cases j <;> simp

private theorem scheduledWidthThreeHankel_row_two (body : List TagLetter) :
    scheduledWidthThreeHankel body 2 = scheduledWidthThreeHankelClosed body 2 := by
  ext j
  fin_cases j <;> simp

private theorem scheduledWidthThreeHankel_row_three (body : List TagLetter) :
    scheduledWidthThreeHankel body 3 = scheduledWidthThreeHankelClosed body 3 := by
  ext j
  fin_cases j <;> simp

private theorem scheduledWidthThreeHankel_row_four (body : List TagLetter) :
    scheduledWidthThreeHankel body 4 = scheduledWidthThreeHankelClosed body 4 := by
  ext j
  fin_cases j <;> simp

theorem scheduledWidthThreeHankel_eq_closed (body : List TagLetter) :
    scheduledWidthThreeHankel body = scheduledWidthThreeHankelClosed body := by
  funext i
  fin_cases i
  · exact scheduledWidthThreeHankel_row_zero body
  · exact scheduledWidthThreeHankel_row_one body
  · exact scheduledWidthThreeHankel_row_two body
  · exact scheduledWidthThreeHankel_row_three body
  · exact scheduledWidthThreeHankel_row_four body

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
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

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
    Matrix.det_fin_three, succAbove_two_two, succAbove_one_two, castSucc_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three]
  ring

theorem ternaryCode_nearyLower_three_rule_c_large (body : List TagLetter)
    (body_nonempty : body ≠ []) :
    25 < ternaryCode (nearyLower 3 body (.rule .c)) := by
  have encoded_nonempty : tagEncode 3 body ≠ [] :=
    (tagEncode_eq_nil_iff 3 body).not.mpr body_nonempty
  have lower_length : 4 ≤ (nearyLower 3 body (.rule .c)).length := by
    simp only [nearyLower, List.length_append, List.length_cons, List.length_nil]
    have encoded_length := List.length_pos_of_ne_nil encoded_nonempty
    omega
  have lower_nonempty : nearyLower 3 body (.rule .c) ≠ [] := by
    simp [nearyLower]
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
  exact (scheduledCoefficient_map (Int.castRingHom ℚ) 3 body (by decide) _).symm

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
