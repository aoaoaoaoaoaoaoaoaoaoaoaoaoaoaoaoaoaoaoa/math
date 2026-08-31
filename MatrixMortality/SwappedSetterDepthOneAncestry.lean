import MatrixMortality.SwappedSetterPositiveDepthOne
import MatrixMortality.SwappedSetterMultitransfer

/-!
# Depth-one ancestry after a double deletion

The surviving first multi-transfer middle `D_c²` reaches a rational depth-one carrier. The
raw-fringe theorem consumes an integral discrepancy, so an ancestry bridge must first prove that
this rational normalization is integral. This file isolates that gate and gives a locally physical
repeated-`D_c²` recurrence state for which it fails at every admissible width.
-/

namespace MatrixMortality.SwappedSetterDepthOneAncestry

open SwappedSetterMultitransfer
open SwappedSetterFringe

/-- The literal two-erasure `c` block surviving the first multi-transfer phase sieve. -/
def doubleCDeletion : List NearyTile := [.erase .c, .erase .c]

/-- Projective normalization which turns a nonzero depth-one carrier `(X,Y)` into the
discrepancy used by the raw-fringe pole equation. -/
def normalizedDepthOneDiscrepancy (width : Nat) (x y : ℚ) : ℚ :=
  -3 * y / ((widthScale width - 2) * x)

/-- Exact normalized carrier after applying `D_c²` to the centered state determined by `first`. -/
def afterDoubleCDiscrepancy (width : Nat) (body : List TagLetter)
    (first : List NearyTile) : ℚ :=
  let firstX : ℚ := 3 ^ upperLength width first
  let firstY : ℚ := centeredCoefficient width * swappedUpperCode width first
  normalizedDepthOneDiscrepancy width
    (nextX (3 ^ upperLength width doubleCDeletion) firstY)
    (nextY (blockCoefficient width body doubleCDeletion)
      (centeredCoupling width) (swappedLowerCode width body doubleCDeletion)
      firstX firstY)

/-- A locally physical repeated-`D_c²` entry into the rational depth-one carrier. -/
def repeatedDoubleCDiscrepancy (width : Nat) (body : List TagLetter) : ℚ :=
  afterDoubleCDiscrepancy width body doubleCDeletion

@[simp] theorem upperLength_doubleCDeletion (width : Nat) :
    upperLength width doubleCDeletion = 2 := by
  exact upperLength_double_c (by simp [doubleCDeletion, NearyTile.letter])

@[simp] theorem swappedUpperCode_doubleCDeletion (width : Nat) :
    swappedUpperCode width doubleCDeletion = 14 * widthScale width - 1 := by
  exact swappedUpperCode_double_c (by simp [doubleCDeletion, NearyTile.letter])

@[simp] theorem swappedLowerCode_doubleCDeletion
    (width : Nat) (body : List TagLetter) :
    swappedLowerCode width body doubleCDeletion = 8 := by
  norm_num [doubleCDeletion, swappedLowerCode, spell, nearyLower, ternaryCode,
    ternaryDigit, Nat.ofDigits]

theorem blockCoefficient_doubleCDeletion (width : Nat) (body : List TagLetter) :
    blockCoefficient width body doubleCDeletion =
      centeredCoefficient width * (14 * widthScale width - 1) -
        8 * terminalDiscrepancy width := by
  rw [blockCoefficient, swappedUpperCode_doubleCDeletion,
    swappedLowerCode_doubleCDeletion]
  ring

private theorem centeredCoefficient_ne_zero
    {width : Nat} (width_large : 3 ≤ width) :
    centeredCoefficient width ≠ 0 := by
  have scale_ge_nat : 3 ^ 3 ≤ 3 ^ width :=
    Nat.pow_le_pow_right (by norm_num) width_large
  have scale_ge : (27 : ℤ) ≤ widthScale width := by
    have casted : ((3 ^ 3 : Nat) : ℤ) ≤ ((3 ^ width : Nat) : ℤ) := by
      exact_mod_cast scale_ge_nat
    simpa [widthScale] using casted
  simp only [centeredCoefficient]
  omega

private theorem swappedUpperCode_ne_zero (width : Nat) (block : List NearyTile) :
    swappedUpperCode width block ≠ 0 := by
  let word := (spell (nearyUpper width) block ++ nearyMarker width).map not
  have word_ne : word ≠ [] := by
    dsimp [word]
    simp [nearyMarker]
  have code_ne : ternaryCode word ≠ 0 := by
    intro code_zero
    have word_empty : word = [] := by
      apply ternaryCode_injective
      simpa using code_zero
    exact word_ne word_empty
  have code_ne_int : (ternaryCode word : ℤ) ≠ 0 := by
    exact_mod_cast code_ne
  simpa [swappedUpperCode, word] using code_ne_int

/-- Every physical punctuated upper code is the residue two modulo three. -/
theorem swappedUpperCode_mod_three
    {width : Nat} (width_pos : 0 < width) (block : List NearyTile) :
    swappedUpperCode width block ≡ 2 [ZMOD 3] := by
  have marker_eq :
      (ternaryCode ((nearyMarker width).map not) : ℤ) = setterMarker width := by
    have natural_eq := swappedCode_nearyMarker width
    have power_pos : 0 < 3 ^ width := pow_pos (by omega) width
    have one_le : 1 ≤ 2 * 3 ^ width := by omega
    calc
      (ternaryCode ((nearyMarker width).map not) : ℤ) =
          ((2 * 3 ^ width - 1 : Nat) : ℤ) := by exact_mod_cast natural_eq
      _ = 2 * (3 : ℤ) ^ width - 1 := by
        rw [Nat.cast_sub one_le]
        norm_num
      _ = setterMarker width := by rw [setterMarker, widthScale]
  have code_eq :
      swappedUpperCode width block =
        (3 : ℤ) ^ (width + 1) *
            ternaryCode ((spell (nearyUpper width) block).map not) +
          setterMarker width := by
    rw [swappedUpperCode, List.map_append, ternaryCode_append, List.length_map]
    push_cast
    rw [marker_eq]
    simp only [nearyMarker, List.length_cons, List.length_replicate]
  have power_zero : (3 : ℤ) ^ (width + 1) ≡ 0 [ZMOD 3] := by
    rw [pow_succ]
    exact (Int.ModEq.refl ((3 : ℤ) ^ width)).mul
      (by norm_num : (3 : ℤ) ≡ 0 [ZMOD 3])
  have leading_zero :
      (3 : ℤ) ^ (width + 1) *
          ternaryCode ((spell (nearyUpper width) block).map not) ≡ 0 [ZMOD 3] := by
    simpa using power_zero.mul
      (Int.ModEq.refl (ternaryCode ((spell (nearyUpper width) block).map not) : ℤ))
  obtain ⟨offset, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt width_pos)
  have scale_zero : widthScale offset.succ ≡ 0 [ZMOD 3] := by
    simpa [widthScale, pow_succ, mul_comm] using
      (Int.ModEq.refl ((3 : ℤ) ^ offset)).mul
        (by norm_num : (3 : ℤ) ≡ 0 [ZMOD 3])
  have marker_two : setterMarker offset.succ ≡ 2 [ZMOD 3] := by
    have raw :=
      ((Int.ModEq.refl (2 : ℤ)).mul scale_zero).sub (Int.ModEq.refl (1 : ℤ))
    simpa [setterMarker] using raw.trans (by norm_num)
  rw [code_eq]
  exact (leading_zero.add marker_two).trans (by norm_num)

/-- Closed rational form of the normalized state after a `D_c²` middle. -/
theorem afterDoubleCDiscrepancy_eq
    {width : Nat} (width_large : 3 ≤ width) (body : List TagLetter)
    (first : List NearyTile) :
    afterDoubleCDiscrepancy width body first =
      ((blockCoefficient width body doubleCDeletion : ℚ) *
            swappedUpperCode width first +
          8 * terminalDiscrepancy width * setterMarker width *
            (3 : ℚ) ^ upperLength width first) /
        (3 * centeredCoefficient width * swappedUpperCode width first) := by
  have centered_ne : (centeredCoefficient width : ℚ) ≠ 0 := by
    exact_mod_cast centeredCoefficient_ne_zero width_large
  have punctuated_ne : (swappedUpperCode width first : ℚ) ≠ 0 := by
    exact_mod_cast swappedUpperCode_ne_zero width first
  have scale_opposite :
      ((widthScale width : ℤ) : ℚ) - 2 =
        -(centeredCoefficient width : ℚ) := by
    simp [centeredCoefficient]
  rw [afterDoubleCDiscrepancy, normalizedDepthOneDiscrepancy,
    upperLength_doubleCDeletion, swappedLowerCode_doubleCDeletion]
  norm_num [nextX, nextY, centeredCoupling]
  rw [scale_opposite]
  field_simp [centered_ne, punctuated_ne]
  ring

/-- Integrality of the post-`D_c²` depth-one normalization forces the incoming punctuated code
to divide one fixed terminal product times its upper power. This divisibility is the exact
arithmetic gate hidden by a putative raw-fringe ancestry map. -/
theorem afterDoubleCDiscrepancy_integer_dvd
    {width : Nat} (width_large : 3 ≤ width) (body : List TagLetter)
    (first : List NearyTile) (integer : ℤ)
    (integral : afterDoubleCDiscrepancy width body first = integer) :
    swappedUpperCode width first ∣
      8 * terminalDiscrepancy width * setterMarker width *
        (3 : ℤ) ^ upperLength width first := by
  have centered_ne_int := centeredCoefficient_ne_zero width_large
  have punctuated_ne_int := swappedUpperCode_ne_zero width first
  have denominator_ne :
      (3 * (centeredCoefficient width : ℚ) *
        (swappedUpperCode width first : ℚ)) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast centered_ne_int))
      (by exact_mod_cast punctuated_ne_int)
  have quotient_eq :
      (((blockCoefficient width body doubleCDeletion : ℚ) *
              swappedUpperCode width first +
            8 * terminalDiscrepancy width * setterMarker width *
              (3 : ℚ) ^ upperLength width first) /
          (3 * centeredCoefficient width * swappedUpperCode width first)) =
        (integer : ℚ) := by
    rw [← afterDoubleCDiscrepancy_eq width_large body first]
    exact integral
  have cross_rat :
      (blockCoefficient width body doubleCDeletion : ℚ) *
            swappedUpperCode width first +
          8 * terminalDiscrepancy width * setterMarker width *
            (3 : ℚ) ^ upperLength width first =
        (integer : ℚ) *
          (3 * centeredCoefficient width * swappedUpperCode width first) :=
    (div_eq_iff denominator_ne).mp quotient_eq
  have cross_int :
      blockCoefficient width body doubleCDeletion *
            swappedUpperCode width first +
          8 * terminalDiscrepancy width * setterMarker width *
            (3 : ℤ) ^ upperLength width first =
        integer *
          (3 * centeredCoefficient width * swappedUpperCode width first) := by
    exact_mod_cast cross_rat
  refine ⟨3 * centeredCoefficient width * integer -
    blockCoefficient width body doubleCDeletion, ?_⟩
  nlinarith [cross_int]

private theorem not_dvd_three_of_mod_two {value : ℤ}
    (value_mod : value ≡ 2 [ZMOD 3]) : ¬(3 : ℤ) ∣ value := by
  intro divides
  have value_zero : value ≡ 0 [ZMOD 3] := divides.modEq_zero_int
  have two_zero : (2 : ℤ) ≡ 0 [ZMOD 3] := value_mod.symm.trans value_zero
  norm_num [Int.ModEq] at two_zero

/-- Since every punctuated code is a three-adic unit, the upper power in the raw integrality
gate cancels. Any integral post-`D_c²` discrepancy therefore forces the incoming code to divide
the fixed product `8Hμ`. -/
theorem afterDoubleCDiscrepancy_integer_dvd_terminal
    {width : Nat} (width_large : 3 ≤ width) (body : List TagLetter)
    (first : List NearyTile) (integer : ℤ)
    (integral : afterDoubleCDiscrepancy width body first = integer) :
    swappedUpperCode width first ∣
      8 * terminalDiscrepancy width * setterMarker width := by
  have punctuated_not_dvd : ¬(3 : ℤ) ∣ swappedUpperCode width first :=
    not_dvd_three_of_mod_two <|
      swappedUpperCode_mod_three (show 0 < width by omega) first
  have coprime_power :
      IsCoprime (swappedUpperCode width first)
        ((3 : ℤ) ^ upperLength width first) := by
    exact Int.prime_three.irreducible.coprime_pow_of_not_dvd
      (upperLength width first) punctuated_not_dvd
  exact coprime_power.dvd_of_dvd_mul_right <|
    afterDoubleCDiscrepancy_integer_dvd width_large body first integer integral

private theorem doubleC_punctuated_not_dvd_terminal
    {width : Nat} (width_large : 3 ≤ width) :
    ¬(14 * widthScale width - 1) ∣
      8 * terminalDiscrepancy width * setterMarker width := by
  intro divides
  by_cases width_eq : width = 3
  · subst width
    norm_num [widthScale, terminalDiscrepancy, setterMarker] at divides
  · have width_four : 4 ≤ width := by omega
    obtain ⟨quotient, quotient_eq⟩ := divides
    have remainder_divides : (14 * widthScale width - 1) ∣ (864 : ℤ) := by
      refine ⟨196 * quotient - (1120 * widthScale width - 704), ?_⟩
      calc
        (864 : ℤ) =
            196 * (8 * terminalDiscrepancy width * setterMarker width) -
              (1120 * widthScale width - 704) *
                (14 * widthScale width - 1) := by
          simp only [terminalDiscrepancy, setterMarker]
          ring
        _ = 196 * ((14 * widthScale width - 1) * quotient) -
              (1120 * widthScale width - 704) *
                (14 * widthScale width - 1) := by rw [quotient_eq]
        _ = (14 * widthScale width - 1) *
              (196 * quotient - (1120 * widthScale width - 704)) := by ring
    have scale_ge_nat : 3 ^ 4 ≤ 3 ^ width :=
      Nat.pow_le_pow_right (by norm_num) width_four
    have scale_ge : (81 : ℤ) ≤ widthScale width := by
      have casted : ((3 ^ 4 : Nat) : ℤ) ≤ ((3 ^ width : Nat) : ℤ) := by
        exact_mod_cast scale_ge_nat
      simpa [widthScale] using casted
    have remainder_small : |(864 : ℤ)| < 14 * widthScale width - 1 := by
      rw [abs_of_nonneg (by norm_num : (0 : ℤ) ≤ 864)]
      omega
    have remainder_zero :=
      Int.eq_zero_of_abs_lt_dvd remainder_divides remainder_small
    norm_num at remainder_zero

/-- The locally physical state obtained from two consecutive `D_c²` blocks has no integral
depth-one normalization. -/
theorem repeatedDoubleCDiscrepancy_not_integer
    {width : Nat} (width_large : 3 ≤ width) (body : List TagLetter) :
    ¬∃ integer : ℤ, repeatedDoubleCDiscrepancy width body = integer := by
  rintro ⟨integer, integral⟩
  have punctuated_dvd :=
    afterDoubleCDiscrepancy_integer_dvd_terminal width_large body doubleCDeletion integer <| by
      simpa [repeatedDoubleCDiscrepancy] using integral
  rw [swappedUpperCode_doubleCDeletion] at punctuated_dvd
  exact doubleC_punctuated_not_dvd_terminal width_large punctuated_dvd

/-- In particular, the repeated-`D_c²` normalization is not the difference of two raw swapped
ternary codes. -/
theorem repeatedDoubleCDiscrepancy_ne_rawCodeDifference
    {width : Nat} (width_large : 3 ≤ width) (body : List TagLetter)
    (upper lower : List Bool) :
    repeatedDoubleCDiscrepancy width body ≠
      (((swappedCode upper : ℤ) - swappedCode lower : ℤ) : ℚ) := by
  intro discrepancy_eq
  exact repeatedDoubleCDiscrepancy_not_integer width_large body
    ⟨(swappedCode upper : ℤ) - swappedCode lower, discrepancy_eq⟩

/-- The discrepancy carried by any positive depth-one raw-fringe witness cannot equal the
normalized recurrence state produced by two consecutive `D_c²` blocks. -/
theorem repeatedDoubleCDiscrepancy_ne_witnessDiscrepancy
    {width : Nat} (width_large : 3 ≤ width) (body : List TagLetter)
    (witness : PositiveDepthOnePoleWitness width body) :
    repeatedDoubleCDiscrepancy width body ≠
      (((swappedCode witness.upperPrefix : ℤ) -
          swappedCode witness.sourcePrefix : ℤ) : ℚ) :=
  repeatedDoubleCDiscrepancy_ne_rawCodeDifference width_large body
    witness.upperPrefix witness.sourcePrefix

/-- The normalized carrier equation is exactly the rational depth-one pole equation. This is the
maximal algebraic bridge: it assumes only that the projective normalization denominator is
nonzero. -/
theorem carrierPole_iff_rationalDepthOnePole
    (width : Nat) (body : List TagLetter) (targetWord : List NearyTile)
    {x y : ℚ} (carrier_ne : ((widthScale width : ℚ) - 2) * x ≠ 0)
    (discrepancy : ℚ)
    (normalization : normalizedDepthOneDiscrepancy width x y = discrepancy) :
    nextY (blockCoefficient width body targetWord) (centeredCoupling width)
        (swappedLowerCode width body targetWord) x y = 0 ↔
      discrepancy * (widthScale width - 2) * swappedUpperCode width targetWord =
        terminalDiscrepancy width * (3 * setterMarker width - discrepancy) *
          swappedLowerCode width body targetWord := by
  let D : ℚ := widthScale width - 2
  let H : ℚ := terminalDiscrepancy width
  let μ : ℚ := setterMarker width
  let P : ℚ := swappedUpperCode width targetWord
  let V : ℚ := swappedLowerCode width body targetWord
  have normalization_cross :
      -3 * y = discrepancy * D * x := by
    rw [normalizedDepthOneDiscrepancy] at normalization
    change -3 * y / (D * x) = discrepancy at normalization
    have cross := (div_eq_iff carrier_ne).mp normalization
    simpa [mul_assoc] using cross
  change
    nextY (blockCoefficient width body targetWord) (centeredCoupling width) V x y = 0 ↔
      discrepancy * D * P = H * (3 * μ - discrepancy) * V
  have factorization :
      3 * nextY (blockCoefficient width body targetWord) (centeredCoupling width) V x y =
        D * x * (discrepancy * D * P - H * (3 * μ - discrepancy) * V) := by
    have y_cross : 3 * y = -discrepancy * D * x := by
      linarith [normalization_cross]
    rw [nextY, blockCoefficient, centeredCoupling]
    push_cast
    change
      3 * (((centeredCoefficient width : ℚ) * P - H * V) * y +
          (centeredCoefficient width : ℚ) * H * μ * V * x) = _
    have centered_eq : (centeredCoefficient width : ℚ) = -D := by
      dsimp [D]
      simp [centeredCoefficient]
    rw [centered_eq]
    calc
      3 * ((-D * P - H * V) * y + -D * H * μ * V * x) =
          (-D * P - H * V) * (3 * y) + 3 * (-D * H * μ * V * x) := by ring
      _ = (-D * P - H * V) * (-discrepancy * D * x) +
          3 * (-D * H * μ * V * x) := by rw [y_cross]
      _ = D * x * (discrepancy * D * P - H * (3 * μ - discrepancy) * V) := by ring
  constructor
  · intro physical_pole
    have product_zero :
        D * x * (discrepancy * D * P - H * (3 * μ - discrepancy) * V) = 0 := by
      rw [← factorization, physical_pole]
      ring
    have gap_zero :
        discrepancy * D * P - H * (3 * μ - discrepancy) * V = 0 :=
      (mul_eq_zero.mp product_zero).resolve_left carrier_ne
    exact sub_eq_zero.mp gap_zero
  · intro raw_pole
    have gap_zero :
        discrepancy * D * P - H * (3 * μ - discrepancy) * V = 0 :=
      sub_eq_zero.mpr raw_pole
    have triple_zero :
        3 * nextY (blockCoefficient width body targetWord) (centeredCoupling width) V x y = 0 := by
      rw [factorization, gap_zero]
      ring
    nlinarith

/-- Once the normalized carrier discrepancy is an integer, the physical next-block pole equation
is exactly the raw-fringe `PositiveDepthOnePole` equation. Thus integrality is the sole algebraic
coordinate condition in the carrier-to-fringe bridge; the remaining witness fields encode the
physical ancestry grammar. -/
theorem carrierPole_iff_positiveDepthOnePole
    (width : Nat) (body : List TagLetter) (targetWord : List NearyTile)
    {x y : ℚ} (carrier_ne : ((widthScale width : ℚ) - 2) * x ≠ 0) (integer : ℤ)
    (integral : normalizedDepthOneDiscrepancy width x y = integer) :
    nextY (blockCoefficient width body targetWord) (centeredCoupling width)
        (swappedLowerCode width body targetWord) x y = 0 ↔
      PositiveDepthOnePole width body integer targetWord := by
  rw [carrierPole_iff_rationalDepthOnePole width body targetWord carrier_ne integer integral]
  unfold PositiveDepthOnePole
  change
    ((integer : ℚ) * (widthScale width - 2) * swappedUpperCode width targetWord =
        terminalDiscrepancy width * (3 * setterMarker width - integer) *
          swappedLowerCode width body targetWord) ↔
      integer * (widthScale width - 2) * swappedUpperCode width targetWord =
        terminalDiscrepancy width * (3 * setterMarker width - integer) *
          swappedLowerCode width body targetWord
  constructor <;> intro pole <;> exact_mod_cast pole

end MatrixMortality.SwappedSetterDepthOneAncestry
