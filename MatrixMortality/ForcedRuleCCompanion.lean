import MatrixMortality.PairedRank
import MatrixMortality.TwoStateObstructions

/-!
# Forced-rule-c companion obstruction

Every Neary terminal match begins with the rule-`c` role.  Prefixing that role lowers the
three-state side series, but it does not remove the phase coordinate needed by a binary paired
tail.  A four-by-four Hankel minor supported on isolated-toggle words remains nonsingular.

Adding the constant channel required by the off-diagonal companion makes those five channels
minimal already on the same isolated-toggle probes.  Consequently the physical toggle in every
exact five-state realization is nonsingular.  It cannot also be a bordered delimiter whose cube
has rank two.
-/

namespace MatrixMortality

open scoped Matrix

/-- The side boundary row after the forced initial rule-`c`, expressed on the paired pushout. -/
def forcedRuleCRow (R : Type*) [CommRing R] (β : Nat)
    (body : List TagLetter) : Fin 4 → R :=
  let lower := ternaryCode (nearyLower β body (.rule .c))
  ![1, lower, 2, lower]

/-- The paired physical tail series after absorbing the forced initial rule-`c`. -/
def forcedRuleCCoefficient (R : Type*) [CommRing R] (β : Nat)
    (body : List TagLetter) (word : List PairedControl) : R :=
  linearCoefficient (pairedGenerator R β body)
    (forcedRuleCRow R β body) (pairedColumn R β) word

theorem forcedRuleCRow_dot_phaseVector (R : Type*) [CommRing R]
    (β : Nat) (body : List TagLetter) (phase : PairPhase) (vector : Fin 3 → R) :
    forcedRuleCRow R β body ⬝ᵥ phaseVector R phase vector =
      (![1, ternaryCode (nearyLower β body (.rule .c)), 2] : Fin 3 → R) ⬝ᵥ vector := by
  cases phase with
  | rule =>
      simp [forcedRuleCRow, phaseVector, controllerVector, pairControllerEquiv,
        dotProduct, Fin.sum_univ_succ]
  | erase =>
      simp [forcedRuleCRow, phaseVector, controllerVector, pairControllerEquiv,
        dotProduct, Fin.sum_univ_succ]
      ring

/-- The new row is exactly semantic prefixing by the rule-`c` tile, not prefixing one physical
`c` control whose role would still depend on the suffix phase. -/
theorem forcedRuleCCoefficient_eq_sideCoefficient (R : Type*) [CommRing R]
    (β : Nat) (body : List TagLetter) (word : List PairedControl) :
    forcedRuleCCoefficient R β body word =
      sideCoefficient R β body (.rule .c :: decodePairedWord word) := by
  change forcedRuleCRow R β body ⬝ᵥ
    pairedProduct R β body word *ᵥ pairedColumn R β = _
  rw [pairedProduct_mulVec_column]
  rw [forcedRuleCRow_dot_phaseVector]
  simp only [sideCoefficient, sideTileProduct, wordProduct_cons]
  rw [← Matrix.mulVec_mulVec]
  simp [sidePcpMatrix, nearyUpper, nearyLower, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ]

theorem forcedRuleCCoefficient_map {R S : Type*} [CommRing R] [CommRing S]
    (hom : R →+* S) (β : Nat) (body : List TagLetter) (word : List PairedControl) :
    hom (forcedRuleCCoefficient R β body word) =
      forcedRuleCCoefficient S β body word := by
  rw [forcedRuleCCoefficient_eq_sideCoefficient,
    forcedRuleCCoefficient_eq_sideCoefficient]
  exact sideCoefficient_map hom β body (.rule .c :: decodePairedWord word)

/-- Prefix probes exposing all four states of the forced-role paired tail.  Every nonempty probe
ends in data, so inserting one further toggle never creates an adjacent toggle. -/
def forcedRuleCPrefixes : Fin 4 → List PairedControl :=
  ![[], [.data .b], [.data .b, .data .b],
    [.data .b, .toggle, .data .b]]

/-- Suffix probes exposing all four states of the forced-role paired tail.  Every nonempty probe
begins in data. -/
def forcedRuleCSuffixes : Fin 4 → List PairedControl :=
  ![[], [.data .b], [.data .b, .data .b], [.data .b, .toggle]]

/-- Prefix each suffix-facing probe by one isolated physical toggle. -/
def forcedRuleCInsertedPrefixes : Fin 4 → List PairedControl :=
  fun index => forcedRuleCPrefixes index ++ [.toggle]

/-- Closed reachable-row factor for the forced rule-`c` derivative. -/
def forcedRuleCReachable (β : Nat) (body : List TagLetter) :
    Matrix (Fin 4) (Fin 4) ℤ :=
  let x : ℤ := ternaryCode (nearyLower β body (.rule .c))
  let m := nearyMarkerValueInt β
  let s := nearyWidthScaleInt β
  let u := 3 * m + 2
  let a := 9 * s
  !![1, x, 2, x;
     1, 27 * x + 25, 2 * a + u, 3 * x + 1;
     1, 81 * x + 52, a * (2 * a + u) + u, 9 * x + 4;
     1, 729 * x + 700, a * (2 * a + u) + u, 81 * x + 76]

/-- Closed observable-column factor supported on data-leading suffixes. -/
def forcedRuleCObservable (β : Nat) : Matrix (Fin 4) (Fin 4) ℤ :=
  let m := nearyMarkerValueInt β
  let s := nearyWidthScaleInt β
  let p := 3 * s
  let u := 3 * m + 2
  let a := 9 * s
  !![m, m + p * u - 25, m + p * (a * u + u) - 52, m + p * u - 1;
     -1, 0, 0, 0;
     p, a * p, a ^ 2 * p, a * p;
     0, -27, -81, -3]

/-- Native reachable rows selected by `forcedRuleCPrefixes`. -/
def forcedRuleCReachableNative (β : Nat) (body : List TagLetter) :
    Matrix (Fin 4) (Fin 4) ℤ :=
  finitePrefixStates (pairedGenerator ℤ β body)
    (forcedRuleCRow ℤ β body) forcedRuleCPrefixes

/-- Native observable columns selected by `forcedRuleCSuffixes`. -/
def forcedRuleCObservableNative (β : Nat) (body : List TagLetter) :
    Matrix (Fin 4) (Fin 4) ℤ :=
  finiteSuffixStates (pairedGenerator ℤ β body)
    (pairedColumn ℤ β) forcedRuleCSuffixes

theorem forcedRuleCReachableNative_eq (β : Nat) (body : List TagLetter) :
    forcedRuleCReachableNative β body = forcedRuleCReachable β body := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [forcedRuleCReachableNative, forcedRuleCReachable, forcedRuleCPrefixes,
      finitePrefixStates, forcedRuleCRow, pairedGenerator,
      pairedDataMatrix_eq_explicit, pairedToggleMatrix_eq_explicit,
      wordProduct, nearyUpper, nearyLower, ternaryCode_tagCode_b,
      ternaryCode_cons, ternaryDigit, nearyMarkerValueInt,
      nearyWidthScaleInt, pow_succ, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ, Matrix.one_apply] <;>
    ring

theorem forcedRuleCObservableNative_eq (β : Nat) (body : List TagLetter) :
    forcedRuleCObservableNative β body = forcedRuleCObservable β := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [forcedRuleCObservableNative, forcedRuleCObservable, forcedRuleCSuffixes,
      finiteSuffixStates, pairedColumn, phaseVector, controllerVector,
      pairControllerEquiv, sideTerminalColumn, sidePcpMatrix, sideTailBasis,
      pairedGenerator, pairedDataMatrix_eq_explicit,
      pairedToggleMatrix_eq_explicit, wordProduct, nearyUpper, nearyLower,
      ternaryCode_tagCode_b, ternaryCode_cons, ternaryDigit,
      nearyMarkerValueInt, nearyWidthScaleInt, pow_succ,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.one_apply] <;>
    ring

/-- A unit-determinant column operation which exposes the sparse first reachable row. -/
def forcedRuleCColumnEliminator (β : Nat) (body : List TagLetter) :
    Matrix (Fin 4) (Fin 4) ℤ :=
  let x : ℤ := ternaryCode (nearyLower β body (.rule .c))
  !![1, -x, -2, -x;
     0, 1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

/-- Reachable factor after the sparse-row column operation. -/
def forcedRuleCReachableReduced (β : Nat) (body : List TagLetter) :
    Matrix (Fin 4) (Fin 4) ℤ :=
  let x : ℤ := ternaryCode (nearyLower β body (.rule .c))
  let m := nearyMarkerValueInt β
  let s := nearyWidthScaleInt β
  let u := 3 * m + 2
  let a := 9 * s
  !![1, 0, 0, 0;
     1, 26 * x + 25, 2 * a + u - 2, 2 * x + 1;
     1, 80 * x + 52, 2 * a ^ 2 + a * u + u - 2, 8 * x + 4;
     1, 728 * x + 700, 2 * a ^ 2 + a * u + u - 2, 80 * x + 76]

/-- Three-dimensional determinant left after exposing the sparse first row. -/
def forcedRuleCReachableMinor (β : Nat) (body : List TagLetter) :
    Matrix (Fin 3) (Fin 3) ℤ :=
  let x : ℤ := ternaryCode (nearyLower β body (.rule .c))
  let m := nearyMarkerValueInt β
  let s := nearyWidthScaleInt β
  let u := 3 * m + 2
  let a := 9 * s
  !![26 * x + 25, 2 * a + u - 2, 2 * x + 1;
     80 * x + 52, 2 * a ^ 2 + a * u + u - 2, 8 * x + 4;
     728 * x + 700, 2 * a ^ 2 + a * u + u - 2, 80 * x + 76]

theorem forcedRuleCColumnEliminator_det (β : Nat) (body : List TagLetter) :
    (forcedRuleCColumnEliminator β body).det = 1 := by
  rw [Matrix.det_succ_column_zero]
  norm_num [forcedRuleCColumnEliminator, Matrix.det_fin_three,
    Matrix.submatrix, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]

theorem forcedRuleCReachable_mul_eliminator (β : Nat)
    (body : List TagLetter) :
    forcedRuleCReachable β body * forcedRuleCColumnEliminator β body =
      forcedRuleCReachableReduced β body := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [forcedRuleCReachable, forcedRuleCColumnEliminator,
      forcedRuleCReachableReduced, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

theorem forcedRuleCReachableReduced_det_eq_minor (β : Nat)
    (body : List TagLetter) :
    (forcedRuleCReachableReduced β body).det =
      (forcedRuleCReachableMinor β body).det := by
  rw [Matrix.det_succ_row_zero]
  norm_num [forcedRuleCReachableReduced, forcedRuleCReachableMinor,
    Fin.sum_univ_succ, Matrix.submatrix]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem forcedRuleCReachableMinor_det (β : Nat) (body : List TagLetter) :
    (forcedRuleCReachableMinor β body).det =
      let x : ℤ := ternaryCode (nearyLower β body (.rule .c))
      let m := nearyMarkerValueInt β
      let s := nearyWidthScaleInt β
      let u := 3 * m + 2
      let a := 9 * s
      576 * a * (x + 1) * (x + 2) * (2 * a + u - 2) := by
  rw [Matrix.det_fin_three]
  norm_num [forcedRuleCReachableMinor, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  ring

theorem forcedRuleCReachable_det (β : Nat) (body : List TagLetter) :
    (forcedRuleCReachable β body).det =
      let x : ℤ := ternaryCode (nearyLower β body (.rule .c))
      let m := nearyMarkerValueInt β
      let s := nearyWidthScaleInt β
      let u := 3 * m + 2
      let a := 9 * s
      576 * a * (x + 1) * (x + 2) * (2 * a + u - 2) := by
  calc
    (forcedRuleCReachable β body).det =
        (forcedRuleCReachable β body *
          forcedRuleCColumnEliminator β body).det := by
            rw [Matrix.det_mul, forcedRuleCColumnEliminator_det, mul_one]
    _ = (forcedRuleCReachableReduced β body).det := by
      rw [forcedRuleCReachable_mul_eliminator]
    _ = (forcedRuleCReachableMinor β body).det :=
      forcedRuleCReachableReduced_det_eq_minor β body
    _ = _ := forcedRuleCReachableMinor_det β body

/-- Minor left by the sparse second observable row. -/
def forcedRuleCObservableMinor (β : Nat) : Matrix (Fin 3) (Fin 3) ℤ :=
  let m := nearyMarkerValueInt β
  let s := nearyWidthScaleInt β
  let p := 3 * s
  let u := 3 * m + 2
  let a := 9 * s
  !![m + p * u - 25, m + p * (a * u + u) - 52, m + p * u - 1;
     a * p, a ^ 2 * p, a * p;
     -27, -81, -3]

theorem forcedRuleCObservable_det_eq_minor (β : Nat) :
    (forcedRuleCObservable β).det = (forcedRuleCObservableMinor β).det := by
  rw [Matrix.det_succ_row (forcedRuleCObservable β) 1]
  norm_num [forcedRuleCObservable, forcedRuleCObservableMinor,
    Fin.sum_univ_succ, Matrix.submatrix]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem forcedRuleCObservableMinor_det (β : Nat) :
    (forcedRuleCObservableMinor β).det =
      let s := nearyWidthScaleInt β
      let p := 3 * s
      let a := 9 * s
      76 * a * p * (p - 9) := by
  rw [Matrix.det_fin_three]
  norm_num [forcedRuleCObservableMinor, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  linear_combination
    (-324 * nearyWidthScaleInt β ^ 2) * nearyMarkerValueInt_relation β

theorem forcedRuleCObservable_det (β : Nat) :
    (forcedRuleCObservable β).det =
      let s := nearyWidthScaleInt β
      let p := 3 * s
      let a := 9 * s
      76 * a * p * (p - 9) := by
  rw [forcedRuleCObservable_det_eq_minor, forcedRuleCObservableMinor_det]

theorem forcedRuleCReachable_det_ne_zero (β : Nat) (body : List TagLetter) :
    (forcedRuleCReachable β body).det ≠ 0 := by
  rw [forcedRuleCReachable_det]
  simp only
  have lower_nonnegative :
      (0 : ℤ) ≤ ternaryCode (nearyLower β body (.rule .c)) := by positivity
  have scale_positive : (0 : ℤ) < nearyWidthScaleInt β := by
    unfold nearyWidthScaleInt
    positivity
  have upper_value_nonnegative : (0 : ℤ) ≤ nearyMarkerValueInt β := by
    unfold nearyMarkerValueInt
    positivity
  have last_factor_positive :
      0 < 2 * (9 * nearyWidthScaleInt β) +
          (3 * nearyMarkerValueInt β + 2) - 2 := by
    nlinarith
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (by norm_num) (mul_ne_zero (by norm_num)
          (ne_of_gt scale_positive)))
        (ne_of_gt (show (0 : ℤ) <
          ternaryCode (nearyLower β body (.rule .c)) + 1 by omega)))
      (ne_of_gt (show (0 : ℤ) <
        ternaryCode (nearyLower β body (.rule .c)) + 2 by omega)))
    (ne_of_gt last_factor_positive)

theorem forcedRuleCObservable_det_ne_zero (β : Nat) (three_le : 3 ≤ β) :
    (forcedRuleCObservable β).det ≠ 0 := by
  rw [forcedRuleCObservable_det]
  simp only
  have power_bound_nat : 3 ^ 3 ≤ 3 ^ β :=
    Nat.pow_le_pow_right (by norm_num) three_le
  have scale_gt_three : (3 : ℤ) < nearyWidthScaleInt β := by
    rw [nearyWidthScaleInt]
    exact_mod_cast (show 3 < 3 ^ β by omega)
  have scale_positive : (0 : ℤ) < nearyWidthScaleInt β := by omega
  have marker_scale_gt_nine :
      (9 : ℤ) < 3 * nearyWidthScaleInt β := by omega
  have first_scale_positive :
      (0 : ℤ) < 9 * nearyWidthScaleInt β := by positivity
  have marker_scale_positive :
      (0 : ℤ) < 3 * nearyWidthScaleInt β := by positivity
  have last_factor_positive :
      (0 : ℤ) < 3 * nearyWidthScaleInt β - 9 := by omega
  exact ne_of_gt (mul_pos
    (mul_pos (mul_pos (by norm_num) first_scale_positive) marker_scale_positive)
    last_factor_positive)

/-- Hankel section after inserting one isolated toggle between every prefix and suffix probe. -/
def forcedRuleCInsertedHankel (β : Nat) (body : List TagLetter) :
    Matrix (Fin 4) (Fin 4) ℤ :=
  finiteHankel (forcedRuleCCoefficient ℤ β body)
    forcedRuleCInsertedPrefixes forcedRuleCSuffixes

theorem forcedRuleCInsertedPrefixStates_eq (β : Nat)
    (body : List TagLetter) :
    finitePrefixStates (pairedGenerator ℤ β body) (forcedRuleCRow ℤ β body)
        forcedRuleCInsertedPrefixes =
      forcedRuleCReachable β body * pairedToggleMatrix ℤ := by
  rw [← forcedRuleCReachableNative_eq]
  ext i j
  change (forcedRuleCRow ℤ β body ᵥ*
      wordProduct (pairedGenerator ℤ β body)
        (forcedRuleCPrefixes i ++ [.toggle])) j =
    ((forcedRuleCRow ℤ β body ᵥ*
        wordProduct (pairedGenerator ℤ β body) (forcedRuleCPrefixes i)) ᵥ*
      pairedToggleMatrix ℤ) j
  rw [wordProduct_append]
  simp only [wordProduct_cons, wordProduct_nil, Matrix.mul_one, pairedGenerator]
  rw [← Matrix.vecMul_vecMul]

theorem forcedRuleCInsertedHankel_factor (β : Nat) (body : List TagLetter) :
    forcedRuleCInsertedHankel β body =
      (forcedRuleCReachable β body * pairedToggleMatrix ℤ) *
        forcedRuleCObservable β := by
  rw [forcedRuleCInsertedHankel, finiteHankel_factor
    (forcedRuleCCoefficient ℤ β body) (pairedGenerator ℤ β body)
    (forcedRuleCRow ℤ β body) (pairedColumn ℤ β)
    forcedRuleCInsertedPrefixes forcedRuleCSuffixes]
  · rw [forcedRuleCInsertedPrefixStates_eq]
    change (forcedRuleCReachable β body * pairedToggleMatrix ℤ) *
        forcedRuleCObservableNative β body = _
    rw [forcedRuleCObservableNative_eq]
  · intro word
    rfl

theorem pairedToggleMatrix_det_int : (pairedToggleMatrix ℤ).det = -1 := by
  rw [pairedToggleMatrix_eq_explicit, Matrix.det_succ_row_zero]
  norm_num [Fin.sum_univ_succ, Matrix.submatrix, Matrix.det_fin_three,
    Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]

theorem forcedRuleCInsertedHankel_det_ne_zero (β : Nat)
    (body : List TagLetter) (three_le : 3 ≤ β) :
    (forcedRuleCInsertedHankel β body).det ≠ 0 := by
  rw [forcedRuleCInsertedHankel_factor, Matrix.det_mul, Matrix.det_mul,
    pairedToggleMatrix_det_int]
  exact mul_ne_zero
    (mul_ne_zero (forcedRuleCReachable_det_ne_zero β body) (by norm_num))
    (forcedRuleCObservable_det_ne_zero β three_le)

/-- Rational form of the inserted-toggle Hankel certificate. -/
def forcedRuleCInsertedHankelRat (β : Nat) (body : List TagLetter) :
    Matrix (Fin 4) (Fin 4) ℚ :=
  finiteHankel (forcedRuleCCoefficient ℚ β body)
    forcedRuleCInsertedPrefixes forcedRuleCSuffixes

theorem forcedRuleCInsertedHankelRat_eq_castMatrix (β : Nat)
    (body : List TagLetter) :
    forcedRuleCInsertedHankelRat β body =
      castMatrix (forcedRuleCInsertedHankel β body) := by
  ext i j
  simp only [forcedRuleCInsertedHankelRat, finiteHankel, castMatrix,
    Matrix.map_apply, forcedRuleCInsertedHankel]
  exact (forcedRuleCCoefficient_map (Int.castRingHom ℚ) β body _).symm

theorem forcedRuleCInsertedHankelRat_det_ne_zero (β : Nat)
    (body : List TagLetter) (three_le : 3 ≤ β) :
    (forcedRuleCInsertedHankelRat β body).det ≠ 0 := by
  rw [forcedRuleCInsertedHankelRat_eq_castMatrix, castMatrix_det]
  exact Int.cast_ne_zero.mpr
    (forcedRuleCInsertedHankel_det_ne_zero β body three_le)

/-- The forced rule-`c` derivative on binary paired tails still has four-state Hankel rank. -/
theorem forcedRuleC_exact_state_lower_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : Nat) (body : List TagLetter) (three_le : 3 ≤ β)
    (generators : PairedControl → Matrix ι ι ℚ) (row column : ι → ℚ)
    (exact : RepresentsSeries (forcedRuleCCoefficient ℚ β body)
      generators row column) :
    4 ≤ Fintype.card ι := by
  have bound := finiteHankel_card_le
    (forcedRuleCCoefficient ℚ β body)
    forcedRuleCInsertedPrefixes forcedRuleCSuffixes generators row column exact
    (forcedRuleCInsertedHankelRat_det_ne_zero β body three_le)
  simpa using bound

/-! ## Five-channel rigidity on the isolated-toggle probe language -/

/-- Two-channel behavior of one five-state physical family. -/
def forcedRuleCTwoChannelBehavior
    (generators : PairedControl → Square (Fin 4 ⊕ Unit) ℚ)
    (output : Matrix (Fin 2) (Fin 4 ⊕ Unit) ℚ)
    (input : Matrix (Fin 4 ⊕ Unit) (Fin 2) ℚ)
    (word : List PairedControl) : Square (Fin 2) ℚ :=
  output * wordProduct generators word * input

/-- The active derivative channel together with the compulsory constant companion channel. -/
def forcedRuleCDiagonalCompanion (coefficient : ℚ) : Square (Fin 2) ℚ :=
  !![coefficient, 0;
     0, 1]

/-- The off-diagonal companion used by the fracture grammar. -/
def forcedRuleCOffDiagonalCompanion (coefficient : ℚ) : Square (Fin 2) ℚ :=
  !![0, coefficient;
     1, 0]

/-- Swapping the two input channels exposes the derivative and constant channels diagonally. -/
def forcedRuleCChannelSwap : Square (Fin 2) ℚ :=
  !![0, 1;
     1, 0]

theorem forcedRuleCOffDiagonalCompanion_mul_channelSwap (coefficient : ℚ) :
    forcedRuleCOffDiagonalCompanion coefficient * forcedRuleCChannelSwap =
      forcedRuleCDiagonalCompanion coefficient := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [forcedRuleCOffDiagonalCompanion, forcedRuleCChannelSwap,
      forcedRuleCDiagonalCompanion, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Five probe rows: four active derivative prefixes and one constant-channel row. -/
def forcedRuleCCompanionProbeRows
    (generators : PairedControl → Square (Fin 4 ⊕ Unit) ℚ)
    (output : Matrix (Fin 2) (Fin 4 ⊕ Unit) ℚ) :
    Matrix (Fin 4 ⊕ Unit) (Fin 4 ⊕ Unit) ℚ
  | .inl pidx, state =>
      (output * wordProduct generators (forcedRuleCPrefixes pidx)) 0 state
  | .inr _, state => output 1 state

/-- Five probe columns: four active derivative suffixes and one constant-channel column. -/
def forcedRuleCCompanionProbeColumns
    (generators : PairedControl → Square (Fin 4 ⊕ Unit) ℚ)
    (input : Matrix (Fin 4 ⊕ Unit) (Fin 2) ℚ) :
    Matrix (Fin 4 ⊕ Unit) (Fin 4 ⊕ Unit) ℚ
  | state, .inl sidx =>
      (wordProduct generators (forcedRuleCSuffixes sidx) * input) state 0
  | state, .inr _ => input state 1

/-- The sixteen exact isolated-toggle companion probes assemble into one bordered Hankel
factorization through the physical toggle. -/
theorem forcedRuleCCompanion_probe_factor
    (β : Nat) (body : List TagLetter)
    (generators : PairedControl → Square (Fin 4 ⊕ Unit) ℚ)
    (output : Matrix (Fin 2) (Fin 4 ⊕ Unit) ℚ)
    (input : Matrix (Fin 4 ⊕ Unit) (Fin 2) ℚ)
    (scale : ℚ)
    (exact : ∀ pidx sidx,
      forcedRuleCTwoChannelBehavior generators output input
          (forcedRuleCPrefixes pidx ++ .toggle :: forcedRuleCSuffixes sidx) =
        forcedRuleCDiagonalCompanion
          (scale * forcedRuleCCoefficient ℚ β body
            (forcedRuleCPrefixes pidx ++ .toggle :: forcedRuleCSuffixes sidx))) :
    forcedRuleCCompanionProbeRows generators output * generators .toggle *
        forcedRuleCCompanionProbeColumns generators input =
      Matrix.fromBlocks (scale • forcedRuleCInsertedHankelRat β body) 0 0 1 := by
  ext left right
  rcases left with pidx | extra <;> rcases right with sidx | extra
  · have entry := congrFun (congrFun (exact pidx sidx) 0) 0
    calc
      (forcedRuleCCompanionProbeRows generators output * generators .toggle *
          forcedRuleCCompanionProbeColumns generators input) (.inl pidx) (.inl sidx) =
          (forcedRuleCCompanionProbeRows generators output *
            (generators .toggle *
              forcedRuleCCompanionProbeColumns generators input))
              (.inl pidx) (.inl sidx) := by rw [Matrix.mul_assoc]
      _ = ((output * wordProduct generators (forcedRuleCPrefixes pidx)) *
          (generators .toggle *
            (wordProduct generators (forcedRuleCSuffixes sidx) * input))) 0 0 := by
              simp only [Matrix.mul_apply, forcedRuleCCompanionProbeRows,
                forcedRuleCCompanionProbeColumns]
      _ = (output * wordProduct generators (forcedRuleCPrefixes pidx) *
          generators .toggle *
          wordProduct generators (forcedRuleCSuffixes sidx) * input) 0 0 := by
            simp only [Matrix.mul_assoc]
      _ = (Matrix.fromBlocks (scale • forcedRuleCInsertedHankelRat β body)
          (0 : Matrix (Fin 4) Unit ℚ) 0 1) (.inl pidx) (.inl sidx) := by
            simpa [forcedRuleCTwoChannelBehavior,
              forcedRuleCDiagonalCompanion, forcedRuleCInsertedHankelRat,
              finiteHankel, forcedRuleCInsertedPrefixes, wordProduct_append,
              Matrix.mul_assoc, List.append_assoc] using entry
  · cases extra
    have entry := congrFun (congrFun (exact pidx 0) 0) 1
    calc
      (forcedRuleCCompanionProbeRows generators output * generators .toggle *
          forcedRuleCCompanionProbeColumns generators input) (.inl pidx) (.inr ()) =
          (forcedRuleCCompanionProbeRows generators output *
            (generators .toggle *
              forcedRuleCCompanionProbeColumns generators input))
              (.inl pidx) (.inr ()) := by rw [Matrix.mul_assoc]
      _ = ((output * wordProduct generators (forcedRuleCPrefixes pidx)) *
          (generators .toggle * input)) 0 1 := by
            simp only [Matrix.mul_apply, forcedRuleCCompanionProbeRows,
              forcedRuleCCompanionProbeColumns]
      _ = (output * wordProduct generators (forcedRuleCPrefixes pidx) *
          generators .toggle * input) 0 1 := by
            simp only [Matrix.mul_assoc]
      _ = (Matrix.fromBlocks (scale • forcedRuleCInsertedHankelRat β body)
          (0 : Matrix (Fin 4) Unit ℚ) 0 1) (.inl pidx) (.inr ()) := by
            simpa [forcedRuleCTwoChannelBehavior,
              forcedRuleCDiagonalCompanion, forcedRuleCSuffixes,
              wordProduct_append, Matrix.mul_assoc, List.append_assoc] using entry
  · cases extra
    have entry := congrFun (congrFun (exact 0 sidx) 1) 0
    calc
      (forcedRuleCCompanionProbeRows generators output * generators .toggle *
          forcedRuleCCompanionProbeColumns generators input) (.inr ()) (.inl sidx) =
          (forcedRuleCCompanionProbeRows generators output *
            (generators .toggle *
              forcedRuleCCompanionProbeColumns generators input))
              (.inr ()) (.inl sidx) := by rw [Matrix.mul_assoc]
      _ = (output * (generators .toggle *
          (wordProduct generators (forcedRuleCSuffixes sidx) * input))) 1 0 := by
            simp only [Matrix.mul_apply, forcedRuleCCompanionProbeRows,
              forcedRuleCCompanionProbeColumns]
      _ = (output * generators .toggle *
          wordProduct generators (forcedRuleCSuffixes sidx) * input) 1 0 := by
            simp only [Matrix.mul_assoc]
      _ = (Matrix.fromBlocks (scale • forcedRuleCInsertedHankelRat β body)
          (0 : Matrix (Fin 4) Unit ℚ) 0 1) (.inr ()) (.inl sidx) := by
            simpa [forcedRuleCTwoChannelBehavior,
              forcedRuleCDiagonalCompanion, forcedRuleCPrefixes,
              wordProduct_append, Matrix.mul_assoc, List.append_assoc] using entry
  · cases extra
    have entry := congrFun (congrFun (exact 0 0) 1) 1
    calc
      (forcedRuleCCompanionProbeRows generators output * generators .toggle *
          forcedRuleCCompanionProbeColumns generators input) (.inr ()) (.inr ()) =
          (forcedRuleCCompanionProbeRows generators output *
            (generators .toggle *
              forcedRuleCCompanionProbeColumns generators input))
              (.inr ()) (.inr ()) := by rw [Matrix.mul_assoc]
      _ = (output * (generators .toggle * input)) 1 1 := by
            simp only [Matrix.mul_apply, forcedRuleCCompanionProbeRows,
              forcedRuleCCompanionProbeColumns]
      _ = (output * generators .toggle * input) 1 1 := by
            simp only [Matrix.mul_assoc]
      _ = (Matrix.fromBlocks (scale • forcedRuleCInsertedHankelRat β body)
          (0 : Matrix (Fin 4) Unit ℚ) 0 1) (.inr ()) (.inr ()) := by
            simpa [forcedRuleCTwoChannelBehavior,
              forcedRuleCDiagonalCompanion, forcedRuleCPrefixes,
              forcedRuleCSuffixes, wordProduct_append, Matrix.mul_assoc,
              List.append_assoc] using entry

private theorem forcedRuleCCompanion_target_det_ne_zero
    (β : Nat) (body : List TagLetter) (three_le : 3 ≤ β)
    (scale : ℚ) (scale_ne : scale ≠ 0) :
    (Matrix.fromBlocks (scale • forcedRuleCInsertedHankelRat β body)
      (0 : Matrix (Fin 4) Unit ℚ) 0 1).det ≠ 0 := by
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one,
    Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ scale_ne)
    (forcedRuleCInsertedHankelRat_det_ne_zero β body three_le)

/-- Exact joint realization of the forced derivative and its constant companion channel on the
sixteen isolated-toggle probes forces the physical toggle to be nonsingular. -/
theorem exactForcedRuleCCompanion_toggle_det_ne_zero
    (β : Nat) (body : List TagLetter) (three_le : 3 ≤ β)
    (generators : PairedControl → Square (Fin 4 ⊕ Unit) ℚ)
    (output : Matrix (Fin 2) (Fin 4 ⊕ Unit) ℚ)
    (input : Matrix (Fin 4 ⊕ Unit) (Fin 2) ℚ)
    (scale : ℚ) (scale_ne : scale ≠ 0)
    (exact : ∀ pidx sidx,
      forcedRuleCTwoChannelBehavior generators output input
          (forcedRuleCPrefixes pidx ++ .toggle :: forcedRuleCSuffixes sidx) =
        forcedRuleCDiagonalCompanion
          (scale * forcedRuleCCoefficient ℚ β body
            (forcedRuleCPrefixes pidx ++ .toggle :: forcedRuleCSuffixes sidx))) :
    (generators .toggle).det ≠ 0 := by
  have factor := forcedRuleCCompanion_probe_factor β body generators output input
    scale exact
  have target_ne :=
    forcedRuleCCompanion_target_det_ne_zero β body three_le scale scale_ne
  intro toggle_det_zero
  apply target_ne
  rw [← factor, Matrix.det_mul, Matrix.det_mul, toggle_det_zero]
  simp

/-- A rank-two delimiter cube cannot carry the exact forced-rule companion, even before any
adjacent-toggle word enters the grammar. -/
theorem exactForcedRuleCCompanion_not_rankTwoCube
    (β : Nat) (body : List TagLetter) (three_le : 3 ≤ β)
    (generators : PairedControl → Square (Fin 4 ⊕ Unit) ℚ)
    (output : Matrix (Fin 2) (Fin 4 ⊕ Unit) ℚ)
    (input : Matrix (Fin 4 ⊕ Unit) (Fin 2) ℚ)
    (scale : ℚ) (scale_ne : scale ≠ 0)
    (exact : ∀ pidx sidx,
      forcedRuleCTwoChannelBehavior generators output input
          (forcedRuleCPrefixes pidx ++ .toggle :: forcedRuleCSuffixes sidx) =
        forcedRuleCDiagonalCompanion
          (scale * forcedRuleCCoefficient ℚ β body
            (forcedRuleCPrefixes pidx ++ .toggle :: forcedRuleCSuffixes sidx)))
    (cube_rank : Matrix.rank (generators .toggle ^ 3) = 2) : False := by
  have toggle_det_ne := exactForcedRuleCCompanion_toggle_det_ne_zero
    β body three_le generators output input scale scale_ne exact
  have cube_det_ne : (generators .toggle ^ 3).det ≠ 0 := by
    rw [Matrix.det_pow]
    exact pow_ne_zero _ toggle_det_ne
  have cube_full := Matrix.rank_of_det_ne_zero cube_det_ne
  have cube_rank_five : Matrix.rank (generators .toggle ^ 3) = 5 := by
    simpa using cube_full
  omega

/-- The native off-diagonal companion contract is impossible for a rank-two delimiter cube. -/
theorem exactForcedRuleCOffDiagonalCompanion_not_rankTwoCube
    (β : Nat) (body : List TagLetter) (three_le : 3 ≤ β)
    (generators : PairedControl → Square (Fin 4 ⊕ Unit) ℚ)
    (output : Matrix (Fin 2) (Fin 4 ⊕ Unit) ℚ)
    (input : Matrix (Fin 4 ⊕ Unit) (Fin 2) ℚ)
    (scale : ℚ) (scale_ne : scale ≠ 0)
    (exact : ∀ pidx sidx,
      forcedRuleCTwoChannelBehavior generators output input
          (forcedRuleCPrefixes pidx ++ .toggle :: forcedRuleCSuffixes sidx) =
        forcedRuleCOffDiagonalCompanion
          (scale * forcedRuleCCoefficient ℚ β body
            (forcedRuleCPrefixes pidx ++ .toggle :: forcedRuleCSuffixes sidx)))
    (cube_rank : Matrix.rank (generators .toggle ^ 3) = 2) : False := by
  have diagonal_exact : ∀ pidx sidx,
      forcedRuleCTwoChannelBehavior generators output
          (input * forcedRuleCChannelSwap)
          (forcedRuleCPrefixes pidx ++ .toggle :: forcedRuleCSuffixes sidx) =
        forcedRuleCDiagonalCompanion
          (scale * forcedRuleCCoefficient ℚ β body
            (forcedRuleCPrefixes pidx ++ .toggle :: forcedRuleCSuffixes sidx)) := by
    intro pidx sidx
    calc
      forcedRuleCTwoChannelBehavior generators output
          (input * forcedRuleCChannelSwap)
          (forcedRuleCPrefixes pidx ++ .toggle :: forcedRuleCSuffixes sidx) =
          forcedRuleCTwoChannelBehavior generators output input
            (forcedRuleCPrefixes pidx ++ .toggle :: forcedRuleCSuffixes sidx) *
              forcedRuleCChannelSwap := by
                simp only [forcedRuleCTwoChannelBehavior, Matrix.mul_assoc]
      _ = forcedRuleCOffDiagonalCompanion
          (scale * forcedRuleCCoefficient ℚ β body
            (forcedRuleCPrefixes pidx ++ .toggle :: forcedRuleCSuffixes sidx)) *
              forcedRuleCChannelSwap := by rw [exact pidx sidx]
      _ = _ := forcedRuleCOffDiagonalCompanion_mul_channelSwap _
  exact exactForcedRuleCCompanion_not_rankTwoCube β body three_le generators output
    (input * forcedRuleCChannelSwap) scale scale_ne diagonal_exact cube_rank

end MatrixMortality
