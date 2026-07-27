import MatrixMortality.LinearRepresentation
import MatrixMortality.PairedCompression

/-!
# Exact rank of the paired-role series

Four prefixes and four suffixes already expose every state of the paired `4 × 4` compiler.  Their
determinants are nonzero uniformly in the tag body and every deletion width at least three.
-/

namespace MatrixMortality

open scoped Matrix

/-- Prefixes exposing four independent rows of the paired series. -/
def pairedRankPrefixes : Fin 4 → List PairedControl :=
  ![[], [.data .b], [.data .b, .data .b], [.data .b, .toggle]]

/-- Suffixes exposing four independent columns of the paired series. -/
def pairedRankSuffixes : Fin 4 → List PairedControl :=
  ![[], [.toggle], [.data .b], [.data .b, .toggle]]

/-- Positional value of the Neary marker, viewed as an integer. -/
def pairedMarkerValue (β : Nat) : ℤ := ternaryCode (nearyMarker β)

/-- Base-three scale at deletion width `β`. -/
def pairedWidthScale (β : Nat) : ℤ := (3 : ℤ) ^ β

/-- Appending one zero triples the marker value and adds one. -/
theorem pairedMarkerValue_succ (β : Nat) :
    pairedMarkerValue (β + 1) = 3 * pairedMarkerValue β + 1 := by
  have marker_succ :
      nearyMarker (β + 1) = nearyMarker β ++ [false] := by
    simp [nearyMarker, List.replicate_succ']
  rw [pairedMarkerValue, marker_succ, ternaryCode_append]
  norm_num [pairedMarkerValue, ternaryCode_singleton, ternaryDigit]

/-- The marker value satisfies `2m+1=5·3^β`. -/
theorem pairedMarkerValue_relation (β : Nat) :
    2 * pairedMarkerValue β + 1 = 5 * pairedWidthScale β := by
  induction β with
  | zero =>
      norm_num [pairedMarkerValue, pairedWidthScale, nearyMarker, ternaryCode, ternaryDigit]
  | succ β induction =>
      rw [pairedMarkerValue_succ]
      change 2 * (3 * pairedMarkerValue β + 1) + 1 =
        5 * pairedWidthScale (β + 1)
      rw [pairedWidthScale, pow_succ, ← pairedWidthScale]
      nlinarith

/-- Positional value of the encoded tag letter `b`. -/
theorem ternaryCode_tagCode_b (β : Nat) :
    (ternaryCode (tagCode β .b) : ℤ) = 3 * pairedMarkerValue β + 2 := by
  have code_eq : tagCode β .b = nearyMarker β ++ [true] := by
    simp [tagCode, nearyMarker]
  rw [code_eq, ternaryCode_append]
  norm_num [pairedMarkerValue, ternaryCode, ternaryDigit]

@[simp] theorem nearyMarker_length (β : Nat) : (nearyMarker β).length = β + 1 := by
  simp [nearyMarker]

@[simp] theorem tagCode_b_length (β : Nat) : (tagCode β .b).length = β + 2 := by
  simp [tagCode]

@[simp] theorem ternaryCode_neary_rule_b (β : Nat) (body : List TagLetter) :
    ternaryCode (nearyLower β body (.rule .b)) = 25 := by
  norm_num [nearyLower, ternaryCode_cons, ternaryDigit]

@[simp] theorem ternaryCode_neary_erase (β : Nat) (body : List TagLetter)
    (letter : TagLetter) :
    ternaryCode (nearyLower β body (.erase letter)) = 1 := by
  norm_num [nearyLower, ternaryCode_singleton, ternaryDigit]

/-- Closed reachable-row factor of the paired Hankel certificate. -/
def pairedRankReachable (β : Nat) : Matrix (Fin 4) (Fin 4) ℤ :=
  let m := pairedMarkerValue β
  let s := pairedWidthScale β
  let u := 3 * m + 2
  let a := 9 * s
  !![1, 0, 0, 0;
     1, 25, u, 1;
     1, 52, (a + 1) * u, 4;
     1, 1, u, 25]

/-- Closed observable-column factor of the paired Hankel certificate. -/
def pairedRankObservable (β : Nat) : Matrix (Fin 4) (Fin 4) ℤ :=
  let m := pairedMarkerValue β
  let s := pairedWidthScale β
  let p := 3 * s
  let u := 3 * m + 2
  let a := 9 * s
  !![m, m, m + p * u - 25, m + p * u - 1;
     -1, 0, 0, 0;
     p, p, a * p, a * p;
     0, -1, -27, -3]

/-- Native reachable rows selected by `pairedRankPrefixes`. -/
def pairedRankReachableNative (β : Nat) (body : List TagLetter) :
    Matrix (Fin 4) (Fin 4) ℤ :=
  finitePrefixStates (pairedGenerator ℤ β body) (pairedRow ℤ) pairedRankPrefixes

/-- Native observable columns selected by `pairedRankSuffixes`. -/
def pairedRankObservableNative (β : Nat) (body : List TagLetter) :
    Matrix (Fin 4) (Fin 4) ℤ :=
  finiteSuffixStates (pairedGenerator ℤ β body) (pairedColumn ℤ β) pairedRankSuffixes

theorem pairedRankReachableNative_eq (β : Nat) (body : List TagLetter) :
    pairedRankReachableNative β body = pairedRankReachable β := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairedRankReachableNative, finitePrefixStates, pairedRankPrefixes,
      pairedRankReachable, pairedGenerator, pairedDataMatrix_eq_explicit,
      pairedToggleMatrix_eq_explicit,
      pairedRow, wordProduct, nearyUpper, nearyLower, ternaryCode_tagCode_b,
      ternaryCode_cons, ternaryCode_singleton, ternaryDigit, pairedWidthScale, pow_succ,
      Matrix.vecHead, Matrix.vecTail, Matrix.vecMul_one, Matrix.vecMul, Matrix.dotProduct,
      Matrix.one_apply, Fin.ext_iff, Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals
    solve
    | ring
    | omega

theorem pairedRankObservableNative_eq (β : Nat) (body : List TagLetter) :
    pairedRankObservableNative β body = pairedRankObservable β := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairedRankObservableNative, finiteSuffixStates, pairedRankSuffixes,
      pairedRankObservable, pairedGenerator, pairedDataMatrix_eq_explicit,
      pairedToggleMatrix_eq_explicit,
      pairedColumn, phaseVector, controllerVector, pairControllerEquiv,
      sideTerminalColumn, sidePcpMatrix, sideTailBasis,
      wordProduct, nearyUpper, nearyLower, ternaryCode_tagCode_b,
      ternaryCode_cons, ternaryCode_singleton, ternaryDigit,
      pairedMarkerValue, pairedWidthScale, pow_succ,
      Matrix.vecHead, Matrix.vecTail, Matrix.one_mulVec, Matrix.mulVec, Matrix.dotProduct,
      Matrix.one_apply, Fin.ext_iff, Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals
    solve
    | ring
    | omega

/-- Three-dimensional minor left by the sparse first reachable row. -/
def pairedRankReachableMinor (β : Nat) : Matrix (Fin 3) (Fin 3) ℤ :=
  let m := pairedMarkerValue β
  let s := pairedWidthScale β
  let u := 3 * m + 2
  let a := 9 * s
  !![25, u, 1;
     52, (a + 1) * u, 4;
     1, u, 25]

theorem pairedRankReachable_det_eq_minor (β : Nat) :
    (pairedRankReachable β).det = (pairedRankReachableMinor β).det := by
  rw [Matrix.det_succ_row_zero]
  norm_num [pairedRankReachable, pairedRankReachableMinor, Fin.sum_univ_succ,
    Matrix.submatrix]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem pairedRankReachable_det (β : Nat) :
    (pairedRankReachable β).det =
      48 * (3 * pairedMarkerValue β + 2) *
        (13 * (9 * pairedWidthScale β) - 15) := by
  rw [pairedRankReachable_det_eq_minor, Matrix.det_fin_three]
  norm_num [pairedRankReachableMinor]
  ring

/-- Three-dimensional minor left by the sparse second observable row. -/
def pairedRankObservableMinor (β : Nat) : Matrix (Fin 3) (Fin 3) ℤ :=
  let m := pairedMarkerValue β
  let s := pairedWidthScale β
  let p := 3 * s
  let u := 3 * m + 2
  let a := 9 * s
  !![m, m + p * u - 25, m + p * u - 1;
     p, a * p, a * p;
     -1, -27, -3]

theorem pairedRankObservable_det_eq_minor (β : Nat) :
    (pairedRankObservable β).det = (pairedRankObservableMinor β).det := by
  rw [Matrix.det_succ_row (pairedRankObservable β) 1]
  norm_num [pairedRankObservable, pairedRankObservableMinor, Fin.sum_univ_succ,
    Matrix.submatrix]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem pairedRankObservableMinor_det (β : Nat) :
    (pairedRankObservableMinor β).det =
      -24 * (3 * pairedWidthScale β) *
        (pairedMarkerValue β - 3 * pairedWidthScale β + 2) := by
  rw [Matrix.det_fin_three]
  norm_num [pairedRankObservableMinor]
  ring

theorem pairedRankObservable_det (β : Nat) :
    (pairedRankObservable β).det =
      12 * (3 * pairedWidthScale β) * (pairedWidthScale β - 3) := by
  rw [pairedRankObservable_det_eq_minor, pairedRankObservableMinor_det]
  linear_combination
    (-36 * pairedWidthScale β) * pairedMarkerValue_relation β

theorem pairedRankReachable_det_ne_zero (β : Nat) :
    (pairedRankReachable β).det ≠ 0 := by
  rw [pairedRankReachable_det]
  have marker_nonnegative : 0 ≤ pairedMarkerValue β := by
    unfold pairedMarkerValue
    positivity
  have scale_positive : 0 < pairedWidthScale β := by
    unfold pairedWidthScale
    positivity
  have upper_value_positive : 0 < 3 * pairedMarkerValue β + 2 := by omega
  have scale_factor_positive : 0 < 13 * (9 * pairedWidthScale β) - 15 := by
    nlinarith
  exact mul_ne_zero
    (mul_ne_zero (by norm_num) (ne_of_gt upper_value_positive))
    (ne_of_gt scale_factor_positive)

theorem pairedRankObservable_det_ne_zero (β : Nat) (three_le : 3 ≤ β) :
    (pairedRankObservable β).det ≠ 0 := by
  rw [pairedRankObservable_det]
  have power_bound_nat : 3 ^ 3 ≤ 3 ^ β :=
    Nat.pow_le_pow_right (by norm_num) three_le
  have scale_gt_three : (3 : ℤ) < pairedWidthScale β := by
    rw [pairedWidthScale]
    exact_mod_cast (show 3 < 3 ^ β by omega)
  have scale_positive : 0 < pairedWidthScale β := by omega
  exact mul_ne_zero
    (mul_ne_zero (by norm_num) (mul_ne_zero (by norm_num) (ne_of_gt scale_positive)))
    (sub_ne_zero.mpr (ne_of_gt scale_gt_three))

/-- Certified integer Hankel section of the paired scalar series. -/
def pairedRankHankel (β : Nat) (body : List TagLetter) :
    Matrix (Fin 4) (Fin 4) ℤ :=
  finiteHankel (pairedCoefficient ℤ β body) pairedRankPrefixes pairedRankSuffixes

theorem pairedRankHankel_factor (β : Nat) (body : List TagLetter) :
    pairedRankHankel β body = pairedRankReachable β * pairedRankObservable β := by
  rw [pairedRankHankel, finiteHankel_factor
    (pairedCoefficient ℤ β body) (pairedGenerator ℤ β body)
    (pairedRow ℤ) (pairedColumn ℤ β) pairedRankPrefixes pairedRankSuffixes]
  · change pairedRankReachableNative β body * pairedRankObservableNative β body =
      pairedRankReachable β * pairedRankObservable β
    rw [pairedRankReachableNative_eq, pairedRankObservableNative_eq]
  · intro word
    rfl

theorem pairedRankHankel_det_ne_zero (β : Nat) (body : List TagLetter)
    (three_le : 3 ≤ β) :
    (pairedRankHankel β body).det ≠ 0 := by
  rw [pairedRankHankel_factor, Matrix.det_mul]
  exact mul_ne_zero (pairedRankReachable_det_ne_zero β)
    (pairedRankObservable_det_ne_zero β three_le)

/-- Rational Hankel section of the paired scalar series. -/
def pairedRankHankelRat (β : Nat) (body : List TagLetter) :
    Matrix (Fin 4) (Fin 4) ℚ :=
  finiteHankel (pairedCoefficient ℚ β body) pairedRankPrefixes pairedRankSuffixes

theorem pairedRankHankelRat_eq_castMatrix (β : Nat) (body : List TagLetter) :
    pairedRankHankelRat β body = castMatrix (pairedRankHankel β body) := by
  ext i j
  simp only [pairedRankHankelRat, finiteHankel, castMatrix, Matrix.map_apply,
    pairedRankHankel]
  rw [pairedCoefficient_eq_sideCoefficient ℚ,
    sideCoefficient_eq_ternaryCode_sub ℚ]
  rw [pairedCoefficient_eq_sideCoefficient ℤ,
    sideCoefficient_eq_ternaryCode_sub ℤ]
  norm_num

theorem pairedRankHankelRat_det_ne_zero (β : Nat) (body : List TagLetter)
    (three_le : 3 ≤ β) :
    (pairedRankHankelRat β body).det ≠ 0 := by
  rw [pairedRankHankelRat_eq_castMatrix, castMatrix_det]
  exact Int.cast_ne_zero.mpr (pairedRankHankel_det_ne_zero β body three_le)

/-- Every exact rational realization of the paired series needs at least four states. -/
theorem paired_exact_state_lower_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : Nat) (body : List TagLetter) (three_le : 3 ≤ β)
    (generators : PairedControl → Matrix ι ι ℚ) (row column : ι → ℚ)
    (exact : RepresentsSeries (pairedCoefficient ℚ β body) generators row column) :
    4 ≤ Fintype.card ι := by
  have bound :=
    finiteHankel_card_le (pairedCoefficient ℚ β body)
      pairedRankPrefixes pairedRankSuffixes generators row column exact
      (pairedRankHankelRat_det_ne_zero β body three_le)
  simpa using bound

/-- The native paired representation has exactly four coordinates. -/
theorem paired_native_state_card : Fintype.card (Fin 4) = 4 := by simp

/-- The native paired matrices realize their coefficient series exactly. -/
theorem paired_native_represents (β : Nat) (body : List TagLetter) :
    RepresentsSeries (pairedCoefficient ℚ β body)
      (pairedGenerator ℚ β body) (pairedRow ℚ) (pairedColumn ℚ β) := by
  intro word
  rfl

end MatrixMortality
