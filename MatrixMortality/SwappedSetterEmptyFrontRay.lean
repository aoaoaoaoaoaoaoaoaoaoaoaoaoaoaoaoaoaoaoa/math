import Mathlib.RingTheory.EuclideanDomain
import MatrixMortality.SwappedSetterTargetResidue

set_option autoImplicit false

/-!
# Empty-front local backward rays for the swapped setter

This module records a uniform obstruction to closing the empty-front branch by local
three-adic shells. Every erasure target admits the same body-independent projective pullback
through two singleton `D_c` blocks and one singleton `D_b` block. These are local backward
rays only: the construction proves neither forward reachability from the encoded entry nor a
target pole.
-/

namespace MatrixMortality.SwappedSetterEmptyFrontRay

open PadicValuation SwappedSetterMultitransfer SwappedSetterThresholdCarry
  SwappedSetterCarrierGap SwappedSetterCylinderCharge

private instance factPrimeThree : Fact (Nat.Prime 3) :=
  ⟨by norm_num⟩

private theorem signedSwappedCode_true_run (count : Nat) :
    2 * signedSwappedCode (List.replicate count true) + 1 = (3 : ℤ) ^ count := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ', signedSwappedCode_append, List.length_singleton,
        pow_one, pow_succ]
      have singleton : signedSwappedCode [true] = 1 := by
        norm_num [signedSwappedCode, ternaryCode, ternaryDigit]
      rw [singleton]
      linear_combination 3 * induction

theorem twice_signedSwappedCode_append_trueRun_add_one
    (front : List Bool) (count : Nat) :
    2 * signedSwappedCode (front ++ List.replicate count true) + 1 =
      (3 : ℤ) ^ count * (2 * signedSwappedCode front + 1) := by
  rw [signedSwappedCode_append, List.length_replicate]
  linear_combination signedSwappedCode_true_run count

private theorem tagEncode_replicate_c (width count : Nat) :
    tagEncode width (List.replicate count .c) = List.replicate count true := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ, tagEncode_cons, induction]
      simp [tagCode, List.replicate_succ]

private theorem trailingC_upperPrefix_decomposition
    (width : Nat) (stem : List TagLetter) (trailing : Nat) :
    tagEncode width (stem ++ .b :: List.replicate trailing .c) ++ [true] =
      (tagEncode width stem ++ [true] ++ List.replicate width false) ++
        List.replicate (trailing + 2) true := by
  rw [tagEncode_append, tagEncode_cons, tagEncode_replicate_c]
  simp only [tagCode, List.singleton_append, List.append_assoc]
  have tail_eq :
      (true :: List.replicate trailing true) ++ [true] =
        List.replicate (trailing + 2) true := by
    rw [show trailing + 2 = (trailing + 1) + 1 by omega,
      List.replicate_succ', List.replicate_succ]
  rw [tail_eq]

private theorem trailingC_cofactor_mod_three
    {width : Nat} (width_pos : 0 < width) (stem : List TagLetter) :
    2 * signedSwappedCode
          (tagEncode width stem ++ [true] ++ List.replicate width false) + 1 ≡
      2 [ZMOD 3] := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt width_pos)
  have word_eq :
      tagEncode (offset + 1) stem ++ [true] ++ List.replicate (offset + 1) false =
        (tagEncode (offset + 1) stem ++ [true] ++ List.replicate offset false) ++
          [false] := by
    simp [List.replicate_succ', List.append_assoc]
  rw [word_eq, signedSwappedCode_append]
  have singleton : signedSwappedCode [false] = 2 := by
    norm_num [signedSwappedCode, ternaryCode, ternaryDigit]
  rw [List.length_singleton, pow_one, singleton]
  rw [Int.modEq_iff_dvd]
  refine ⟨-(2 * signedSwappedCode
    (tagEncode (offset + 1) stem ++ [true] ++ List.replicate offset false) + 1), ?_⟩
  ring

theorem trailingC_upperPrefix_factorization
    {width : Nat} (width_pos : 0 < width)
    (stem : List TagLetter) (trailing : Nat) :
    ∃ cofactor : ℤ,
      2 * signedSwappedCode
            (tagEncode width (stem ++ .b :: List.replicate trailing .c) ++ [true]) + 1 =
          (3 : ℤ) ^ (trailing + 2) * cofactor ∧
        ¬(3 : ℤ) ∣ cofactor := by
  let cofactor : ℤ :=
    2 * signedSwappedCode
      (tagEncode width stem ++ [true] ++ List.replicate width false) + 1
  refine ⟨cofactor, ?_, ?_⟩
  · rw [trailingC_upperPrefix_decomposition,
      twice_signedSwappedCode_append_trueRun_add_one]
  · intro cofactor_dvd
    have cofactor_zero : cofactor ≡ 0 [ZMOD 3] := cofactor_dvd.modEq_zero_int
    have cofactor_two : cofactor ≡ 2 [ZMOD 3] := by
      simpa only [cofactor] using trailingC_cofactor_mod_three width_pos stem
    have two_zero : (2 : ℤ) ≡ 0 [ZMOD 3] := cofactor_two.symm.trans cofactor_zero
    norm_num [Int.ModEq] at two_zero

theorem trailingC_upperPrefix_padicValInt
    {width : Nat} (width_pos : 0 < width)
    (stem : List TagLetter) (trailing : Nat) :
    padicValInt 3
        (2 * signedSwappedCode
          (tagEncode width (stem ++ .b :: List.replicate trailing .c) ++ [true]) + 1) =
      trailing + 2 := by
  obtain ⟨cofactor, factorization, cofactor_not_dvd⟩ :=
    trailingC_upperPrefix_factorization width_pos stem trailing
  have power_value : HasValue 3 (((3 : ℤ) ^ (trailing + 2) : ℤ) : ℚ)
      (trailing + 2) := by
    simpa using primePower_hasValue (prime := 3) (trailing + 2)
  have cofactor_unit : IsUnit 3 (cofactor : ℚ) :=
    intCast_isUnit_of_not_dvd cofactor_not_dvd
  have product_value := mul_hasValue power_value cofactor_unit
  rw [factorization]
  have valuation := product_value.2
  have valuation' :
      padicValRat 3
          ((((3 : ℤ) ^ (trailing + 2) * cofactor : ℤ) : ℚ)) =
        ((trailing + 2 : Nat) : ℤ) + 0 := by
    simpa using valuation
  rw [padicValRat.of_int] at valuation'
  norm_num at valuation'
  exact_mod_cast valuation'

theorem allC_upperPrefix_factorization (width : Nat) :
    2 * signedSwappedCode
          (tagEncode width (List.replicate width .c) ++ [true]) + 1 =
      (3 : ℤ) ^ (width + 1) := by
  rw [tagEncode_replicate_c]
  have word_eq : List.replicate width true ++ [true] =
      List.replicate (width + 1) true := by
    simp [List.replicate_succ']
  rw [word_eq, signedSwappedCode_true_run]

theorem allC_upperPrefix_padicValInt (width : Nat) :
    padicValInt 3
        (2 * signedSwappedCode
          (tagEncode width (List.replicate width .c) ++ [true]) + 1) =
      width + 1 := by
  have value := primePower_valuation (prime := 3) (width + 1)
  rw [allC_upperPrefix_factorization]
  have value' :
      padicValRat 3 ((((3 : ℤ) ^ (width + 1) : ℤ) : ℚ)) =
        ((width + 1 : Nat) : ℤ) := by
    simpa using value
  rw [padicValRat.of_int] at value'
  exact_mod_cast value'

/-! ## The body-independent `D_c;D_c;D_b` backward family -/

/-- The punctuated upper target coordinate with discarded-prefix code `upperPrefix`. -/
def emptyTargetUpper (offset : Nat) (upperPrefix : ℤ) : ℤ :=
  widthScale (offset + 1) * (upperPrefix + 1) - 1

/-- The lower coordinate of an empty-front erasure target. -/
def emptyTargetLower (offset : Nat) : ℤ :=
  widthScale (offset + 1) - 1

/-- First `D_c` inverse numerator after removing its forced factor three. -/
def firstDeletionInverseNumerator (offset : Nat) (upperPrefix : ℤ) : ℤ :=
  terminalDiscrepancy (offset + 1) * centeredCoefficient (offset + 1) *
    3 ^ offset * upperPrefix

/-- The integral quotient of `RP-HV` by three in the first `D_c` inverse. -/
def firstDeletionResidual (offset : Nat) (upperPrefix : ℤ) : ℤ :=
  let scale : ℤ := 3 ^ offset
  (-3 * upperPrefix * scale ^ 2 + 2 * upperPrefix * scale -
    18 * scale ^ 2 + 9 * scale - 1)

/-- First `D_c` inverse denominator after removing its forced factor three. -/
def firstDeletionInverseDenominator (offset : Nat) (upperPrefix : ℤ) : ℤ :=
  2 * firstDeletionResidual offset upperPrefix

/-- Numerator of the second raw `D_c` inverse. -/
def secondDeletionInverseNumerator (offset : Nat) (upperPrefix : ℤ) : ℤ :=
  terminalDiscrepancy (offset + 1) * centeredCoefficient (offset + 1) *
    (firstDeletionInverseNumerator offset upperPrefix -
      firstDeletionInverseDenominator offset upperPrefix)

/-- Denominator of the second raw `D_c` inverse. -/
def secondDeletionInverseDenominator (offset : Nat) (upperPrefix : ℤ) : ℤ :=
  2 * (centeredCoefficient (offset + 1) *
      firstDeletionInverseNumerator offset upperPrefix -
    terminalDiscrepancy (offset + 1) *
      firstDeletionInverseDenominator offset upperPrefix)

/-- Polynomial controlling the exact gap after two inverse `D_c` steps. -/
def secondDeletionGapCore (offset : Nat) (upperPrefix : ℤ) : ℤ :=
  let scale : ℤ := 3 ^ offset
  45 * scale ^ 3 * upperPrefix - 75 * scale ^ 2 * upperPrefix +
    36 * scale * upperPrefix - 4 * upperPrefix - 36 * scale ^ 2 +
    18 * scale - 2

/-- The cofactor in `RP_b-H²=-3μF` for the `D_b` inverse. -/
def deletionBCofactor (offset : Nat) : ℤ :=
  3 * widthScale (offset + 1) ^ 2 - widthScale (offset + 1) - 1

/-- Projective numerator after removing the exact factor three from the raw `D_b`
inverse. -/
def deletionBInverseNumerator (offset : Nat) (upperPrefix : ℤ) : ℤ :=
  -setterMarker (offset + 1) * deletionBCofactor offset *
      secondDeletionInverseNumerator offset upperPrefix +
    3 ^ offset * terminalDiscrepancy (offset + 1) ^ 3 *
      secondDeletionGapCore offset upperPrefix

/-- Projective denominator after removing the exact factor three from the raw `D_b`
inverse. -/
def deletionBInverseDenominator (offset : Nat) (upperPrefix : ℤ) : ℤ :=
  -2 * setterMarker (offset + 1) *
      secondDeletionInverseNumerator offset upperPrefix +
    2 * 3 ^ offset * terminalDiscrepancy (offset + 1) ^ 2 *
      secondDeletionGapCore offset upperPrefix

private theorem scale_mod_three {offset : Nat} (offset_pos : 0 < offset) :
    (3 : ℤ) ^ offset ≡ 0 [ZMOD 3] := by
  obtain ⟨predecessor, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt offset_pos)
  simpa [pow_succ, mul_comm] using
    (Int.ModEq.refl ((3 : ℤ) ^ predecessor)).mul
      (by norm_num : (3 : ℤ) ≡ 0 [ZMOD 3])

private theorem not_dvd_three_of_mod_one {value : ℤ}
    (value_mod : value ≡ 1 [ZMOD 3]) : ¬(3 : ℤ) ∣ value := by
  intro value_dvd
  have value_zero : value ≡ 0 [ZMOD 3] := value_dvd.modEq_zero_int
  have one_zero : (1 : ℤ) ≡ 0 [ZMOD 3] := value_mod.symm.trans value_zero
  norm_num [Int.ModEq] at one_zero

private theorem not_dvd_three_of_mod_two {value : ℤ}
    (value_mod : value ≡ 2 [ZMOD 3]) : ¬(3 : ℤ) ∣ value := by
  intro value_dvd
  have value_zero : value ≡ 0 [ZMOD 3] := value_dvd.modEq_zero_int
  have two_zero : (2 : ℤ) ≡ 0 [ZMOD 3] := value_mod.symm.trans value_zero
  norm_num [Int.ModEq] at two_zero

private theorem mul_not_dvd_three
    {left right : ℤ} (left_not_dvd : ¬(3 : ℤ) ∣ left)
    (right_not_dvd : ¬(3 : ℤ) ∣ right) :
    ¬(3 : ℤ) ∣ left * right := by
  intro product_dvd
  rcases (by norm_num : Prime (3 : ℤ)).dvd_mul.mp product_dvd with
    left_dvd | right_dvd
  · exact left_not_dvd left_dvd
  · exact right_not_dvd right_dvd

/-- A projective integer pair with a three-adic-unit denominator admits a primitive reduction
whose cancelled common scale is also a three-adic unit. -/
theorem exists_primitiveReduction_of_denominator_not_dvd_three
    {numerator denominator : ℤ} (denominator_not_dvd : ¬(3 : ℤ) ∣ denominator) :
    ∃ common reducedNumerator reducedDenominator : ℤ,
      numerator = common * reducedNumerator ∧
        denominator = common * reducedDenominator ∧
        IsCoprime reducedNumerator reducedDenominator ∧
        ¬(3 : ℤ) ∣ common := by
  have denominator_ne : denominator ≠ 0 := by
    intro denominator_zero
    exact denominator_not_dvd (denominator_zero ▸ dvd_zero 3)
  let common : ℤ := gcd numerator denominator
  let reducedNumerator : ℤ := numerator / common
  let reducedDenominator : ℤ := denominator / common
  have common_ne : common ≠ 0 := by
    dsimp only [common]
    exact gcd_ne_zero_of_right denominator_ne
  have numerator_eq : numerator = common * reducedNumerator := by
    simpa only [reducedNumerator] using
      (EuclideanDomain.mul_div_cancel' common_ne
        (gcd_dvd_left numerator denominator)).symm
  have denominator_eq : denominator = common * reducedDenominator := by
    simpa only [reducedDenominator] using
      (EuclideanDomain.mul_div_cancel' common_ne
        (gcd_dvd_right numerator denominator)).symm
  have reduced_coprime : IsCoprime reducedNumerator reducedDenominator := by
    dsimp only [reducedNumerator, reducedDenominator, common]
    exact isCoprime_div_gcd_div_gcd_of_gcd_ne_zero common_ne
  have common_not_dvd : ¬(3 : ℤ) ∣ common := by
    intro common_dvd
    have common_dvd_denominator : common ∣ denominator := by
      dsimp only [common]
      exact gcd_dvd_right numerator denominator
    exact denominator_not_dvd (common_dvd.trans common_dvd_denominator)
  exact ⟨common, reducedNumerator, reducedDenominator, numerator_eq,
    denominator_eq, reduced_coprime, common_not_dvd⟩

/-- The first raw `D_c` adjugate is exactly three times the displayed integral pair. -/
theorem firstDeletionInverse_raw
    (offset : Nat) (upperPrefix : ℤ) :
    terminalDiscrepancy (offset + 1) * centeredCoefficient (offset + 1) *
          (emptyTargetUpper offset upperPrefix - emptyTargetLower offset) =
        3 * firstDeletionInverseNumerator offset upperPrefix ∧
      2 * (centeredCoefficient (offset + 1) *
            emptyTargetUpper offset upperPrefix -
          terminalDiscrepancy (offset + 1) * emptyTargetLower offset) =
        3 * firstDeletionInverseDenominator offset upperPrefix := by
  simp only [emptyTargetUpper, emptyTargetLower, firstDeletionInverseNumerator,
    firstDeletionInverseDenominator, firstDeletionResidual, widthScale,
    centeredCoefficient, terminalDiscrepancy]
  rw [pow_succ]
  constructor <;> ring

/-- After the forced factor three is removed, the first inverse denominator is a `3`-adic
unit. -/
theorem firstDeletionInverseDenominator_not_dvd_three
    {offset : Nat} (offset_pos : 0 < offset) (upperPrefix : ℤ) :
    ¬(3 : ℤ) ∣ firstDeletionInverseDenominator offset upperPrefix := by
  have scale_mod := scale_mod_three offset_pos
  have square_mod := scale_mod.mul scale_mod
  have residual_mod : firstDeletionResidual offset upperPrefix ≡ 2 [ZMOD 3] := by
    have raw :=
      ((((((Int.ModEq.refl (-3 : ℤ)).mul (Int.ModEq.refl upperPrefix)).mul square_mod).add
        (((Int.ModEq.refl (2 : ℤ)).mul (Int.ModEq.refl upperPrefix)).mul scale_mod)).sub
          ((Int.ModEq.refl (18 : ℤ)).mul square_mod)).add
            ((Int.ModEq.refl (9 : ℤ)).mul scale_mod)).sub (Int.ModEq.refl (1 : ℤ))
    norm_num at raw
    have reduced := raw.trans (by norm_num : (-1 : ℤ) ≡ 2 [ZMOD 3])
    simpa [firstDeletionResidual, pow_two] using reduced
  have denominator_mod : firstDeletionInverseDenominator offset upperPrefix ≡ 1 [ZMOD 3] := by
    have raw := (Int.ModEq.refl (2 : ℤ)).mul residual_mod
    simpa [firstDeletionInverseDenominator] using raw.trans (by norm_num)
  exact not_dvd_three_of_mod_one denominator_mod

/-- Both coordinates after the second raw `D_c` inverse are `3`-adic units. -/
theorem secondDeletionInverse_not_dvd_three
    {offset : Nat} (offset_pos : 0 < offset) (upperPrefix : ℤ) :
    ¬(3 : ℤ) ∣ secondDeletionInverseNumerator offset upperPrefix ∧
      ¬(3 : ℤ) ∣ secondDeletionInverseDenominator offset upperPrefix := by
  have scale_mod := scale_mod_three offset_pos
  have width_scale_mod : widthScale (offset + 1) ≡ 0 [ZMOD 3] := by
    simpa [widthScale, pow_succ, mul_comm] using
      scale_mod.mul (by norm_num : (3 : ℤ) ≡ 0 [ZMOD 3])
  have centered_mod : centeredCoefficient (offset + 1) ≡ 2 [ZMOD 3] := by
    simpa [centeredCoefficient] using
      ((Int.ModEq.refl (2 : ℤ)).sub width_scale_mod).trans (by norm_num)
  have terminal_mod : terminalDiscrepancy (offset + 1) ≡ 2 [ZMOD 3] := by
    have raw := ((Int.ModEq.refl (5 : ℤ)).mul width_scale_mod).sub
      (Int.ModEq.refl (1 : ℤ))
    simpa [terminalDiscrepancy] using raw.trans (by norm_num)
  have first_numerator_mod :
      firstDeletionInverseNumerator offset upperPrefix ≡ 0 [ZMOD 3] := by
    have raw := ((terminal_mod.mul centered_mod).mul scale_mod).mul
      (Int.ModEq.refl upperPrefix)
    simpa [firstDeletionInverseNumerator, mul_assoc] using raw.trans (by norm_num)
  have first_denominator_mod :
      firstDeletionInverseDenominator offset upperPrefix ≡ 1 [ZMOD 3] := by
    have residual_mod : firstDeletionResidual offset upperPrefix ≡ 2 [ZMOD 3] := by
      have square_mod := scale_mod.mul scale_mod
      have raw :=
        ((((((Int.ModEq.refl (-3 : ℤ)).mul (Int.ModEq.refl upperPrefix)).mul square_mod).add
          (((Int.ModEq.refl (2 : ℤ)).mul (Int.ModEq.refl upperPrefix)).mul scale_mod)).sub
            ((Int.ModEq.refl (18 : ℤ)).mul square_mod)).add
              ((Int.ModEq.refl (9 : ℤ)).mul scale_mod)).sub (Int.ModEq.refl (1 : ℤ))
      norm_num at raw
      have reduced := raw.trans (by norm_num : (-1 : ℤ) ≡ 2 [ZMOD 3])
      simpa [firstDeletionResidual, pow_two] using reduced
    have raw := (Int.ModEq.refl (2 : ℤ)).mul residual_mod
    have result : firstDeletionInverseDenominator offset upperPrefix ≡ 1 [ZMOD 3] := by
      simpa [firstDeletionInverseDenominator] using raw.trans (by norm_num)
    exact result
  have second_numerator_mod :
      secondDeletionInverseNumerator offset upperPrefix ≡ 2 [ZMOD 3] := by
    have difference := first_numerator_mod.sub first_denominator_mod
    have raw := (terminal_mod.mul centered_mod).mul difference
    simpa [secondDeletionInverseNumerator, mul_assoc] using raw.trans (by norm_num)
  have second_denominator_mod :
      secondDeletionInverseDenominator offset upperPrefix ≡ 2 [ZMOD 3] := by
    have left := centered_mod.mul first_numerator_mod
    have right := terminal_mod.mul first_denominator_mod
    have raw := (Int.ModEq.refl (2 : ℤ)).mul (left.sub right)
    simpa [secondDeletionInverseDenominator] using raw.trans (by norm_num)
  exact ⟨not_dvd_three_of_mod_two second_numerator_mod,
    not_dvd_three_of_mod_two second_denominator_mod⟩

/-- The second inverse gap factors into the width power and one explicit target polynomial. -/
theorem secondDeletionInverse_gap
    (offset : Nat) (upperPrefix : ℤ) :
    secondDeletionInverseDenominator offset upperPrefix -
        secondDeletionInverseNumerator offset upperPrefix =
      -3 * 3 ^ offset * terminalDiscrepancy (offset + 1) *
        secondDeletionGapCore offset upperPrefix := by
  simp [secondDeletionInverseDenominator, secondDeletionInverseNumerator,
    firstDeletionInverseNumerator, firstDeletionInverseDenominator,
    firstDeletionResidual, secondDeletionGapCore, terminalDiscrepancy,
    centeredCoefficient, widthScale, pow_succ]
  ring

/-- The second-inverse gap core is a unit multiple of `2U+1`, up to a term of depth
`2·offset+1`. -/
theorem secondDeletionGapCore_split
    (offset : Nat) (upperPrefix : ℤ) :
    secondDeletionGapCore offset upperPrefix =
      2 * (9 * 3 ^ offset - 1) * (2 * upperPrefix + 1) +
        3 * (3 ^ offset) ^ 2 * (15 * 3 ^ offset * upperPrefix -
          25 * upperPrefix - 12) := by
  simp [secondDeletionGapCore]
  ring

/-- The gap-core depth equals the depth of the target suffix factor `2U+1` throughout the
empty-front range. -/
theorem secondDeletionGapCore_padicValInt
    {offset exponent : Nat} (offset_two : 2 ≤ offset) (upperPrefix : ℤ)
    (exponent_bound : exponent ≤ offset + 2)
    (prefix_factorization :
      ∃ cofactor : ℤ,
        2 * upperPrefix + 1 = (3 : ℤ) ^ exponent * cofactor ∧
          ¬(3 : ℤ) ∣ cofactor) :
    padicValInt 3 (secondDeletionGapCore offset upperPrefix) = exponent := by
  obtain ⟨cofactor, prefix_eq, cofactor_not_dvd⟩ := prefix_factorization
  let correction : ℤ :=
    15 * 3 ^ offset * upperPrefix - 25 * upperPrefix - 12
  let leadingUnit : ℤ := 2 * (9 * 3 ^ offset - 1) * cofactor
  let remainderExponent : Nat := 2 * offset + 1 - exponent
  have exponent_le : exponent ≤ 2 * offset + 1 := by omega
  have remainder_pos : 0 < remainderExponent := by
    simp only [remainderExponent]
    omega
  have remainder_power_dvd :
      (3 : ℤ) ∣ (3 : ℤ) ^ remainderExponent * correction := by
    exact dvd_mul_of_dvd_left
      (dvd_pow_self 3 (Nat.ne_of_gt remainder_pos)) correction
  have scale_mod := scale_mod_three (show 0 < offset by omega)
  have bracket_mod : (9 * (3 : ℤ) ^ offset - 1) ≡ 2 [ZMOD 3] := by
    have raw := ((Int.ModEq.refl (9 : ℤ)).mul scale_mod).sub
      (Int.ModEq.refl (1 : ℤ))
    exact raw.trans (by norm_num)
  have bracket_not_dvd : ¬(3 : ℤ) ∣ 9 * (3 : ℤ) ^ offset - 1 :=
    not_dvd_three_of_mod_two bracket_mod
  have leading_not_dvd : ¬(3 : ℤ) ∣ leadingUnit := by
    exact mul_not_dvd_three
      (mul_not_dvd_three (by norm_num) bracket_not_dvd) cofactor_not_dvd
  have quotient_not_dvd :
      ¬(3 : ℤ) ∣ leadingUnit + (3 : ℤ) ^ remainderExponent * correction := by
    intro quotient_dvd
    have leading_dvd := quotient_dvd.sub remainder_power_dvd
    have cancellation :
        leadingUnit + (3 : ℤ) ^ remainderExponent * correction -
            (3 : ℤ) ^ remainderExponent * correction = leadingUnit := by ring
    rw [cancellation] at leading_dvd
    exact leading_not_dvd leading_dvd
  have core_factorization :
      secondDeletionGapCore offset upperPrefix =
        (3 : ℤ) ^ exponent *
          (leadingUnit + (3 : ℤ) ^ remainderExponent * correction) := by
    rw [secondDeletionGapCore_split, prefix_eq]
    have high_power :
        3 * ((3 : ℤ) ^ offset) ^ 2 = (3 : ℤ) ^ (2 * offset + 1) := by
      rw [pow_two, ← pow_add, pow_succ]
      ring
    rw [high_power]
    have exponent_sum : exponent + remainderExponent = 2 * offset + 1 := by
      simp only [remainderExponent]
      omega
    rw [← exponent_sum, pow_add]
    simp only [leadingUnit, correction]
    ring
  have power_value : HasValue 3 (((3 : ℤ) ^ exponent : ℤ) : ℚ) exponent := by
    simpa using primePower_hasValue (prime := 3) exponent
  have quotient_unit :
      IsUnit 3
        ((leadingUnit + (3 : ℤ) ^ remainderExponent * correction : ℤ) : ℚ) :=
    intCast_isUnit_of_not_dvd quotient_not_dvd
  have core_value := mul_hasValue power_value quotient_unit
  rw [core_factorization]
  have valuation := core_value.2
  have valuation' :
      padicValRat 3
          ((((3 : ℤ) ^ exponent *
            (leadingUnit + (3 : ℤ) ^ remainderExponent * correction) : ℤ) : ℚ)) =
        ((exponent : Nat) : ℤ) + 0 := by
    simpa using valuation
  rw [padicValRat.of_int] at valuation'
  norm_num at valuation'
  exact_mod_cast valuation'

/-- The two-`D_c` antecedent gap adds the complete width power to the target-suffix depth. -/
theorem secondDeletionInverse_gap_padicValInt
    {offset exponent : Nat} (offset_two : 2 ≤ offset) (exponent_pos : 0 < exponent)
    (upperPrefix : ℤ) (exponent_bound : exponent ≤ offset + 2)
    (prefix_factorization :
      ∃ cofactor : ℤ,
        2 * upperPrefix + 1 = (3 : ℤ) ^ exponent * cofactor ∧
          ¬(3 : ℤ) ∣ cofactor) :
    padicValInt 3
        (secondDeletionInverseDenominator offset upperPrefix -
          secondDeletionInverseNumerator offset upperPrefix) =
      offset + 1 + exponent := by
  have core_valuation := secondDeletionGapCore_padicValInt offset_two upperPrefix
    exponent_bound prefix_factorization
  have core_ne : secondDeletionGapCore offset upperPrefix ≠ 0 := by
    intro core_zero
    rw [core_zero, padicValInt.zero] at core_valuation
    omega
  have core_value :
      HasValue 3 ((secondDeletionGapCore offset upperPrefix : ℤ) : ℚ) exponent := by
    refine ⟨by exact_mod_cast core_ne, ?_⟩
    rw [padicValRat.of_int]
    exact_mod_cast core_valuation
  have width_scale_mod : widthScale (offset + 1) ≡ 0 [ZMOD 3] := by
    have scale_mod := scale_mod_three (show 0 < offset by omega)
    simpa [widthScale, pow_succ, mul_comm] using
      scale_mod.mul (by norm_num : (3 : ℤ) ≡ 0 [ZMOD 3])
  have terminal_mod : terminalDiscrepancy (offset + 1) ≡ 2 [ZMOD 3] := by
    simpa [terminalDiscrepancy] using
      (((Int.ModEq.refl (5 : ℤ)).mul width_scale_mod).sub
        (Int.ModEq.refl (1 : ℤ))).trans (by norm_num)
  have terminal_unit :
      IsUnit 3 ((terminalDiscrepancy (offset + 1) : ℤ) : ℚ) :=
    intCast_isUnit_of_not_dvd (not_dvd_three_of_mod_two terminal_mod)
  have power_value :
      HasValue 3 (((3 : ℤ) ^ (offset + 1) : ℤ) : ℚ) (offset + 1) := by
    simpa using primePower_hasValue (prime := 3) (offset + 1)
  have negative_power_value :
      HasValue 3 (-(((3 : ℤ) ^ (offset + 1) : ℤ) : ℚ)) (offset + 1) :=
    neg_hasValue power_value
  have gap_value :=
    mul_hasValue (mul_hasValue negative_power_value terminal_unit) core_value
  rw [secondDeletionInverse_gap]
  have scale_eq :
      (-3 : ℤ) * 3 ^ offset = -(3 : ℤ) ^ (offset + 1) := by
    rw [pow_succ]
    ring
  rw [scale_eq]
  have valuation := gap_value.2
  have valuation' :
      padicValRat 3
          (((-(3 : ℤ) ^ (offset + 1) * terminalDiscrepancy (offset + 1) *
            secondDeletionGapCore offset upperPrefix : ℤ) : ℚ)) =
        (((offset + 1 : Nat) : ℤ) + 0) + exponent := by
    simpa using valuation
  rw [padicValRat.of_int] at valuation'
  norm_num at valuation'
  have converted :
      padicValInt 3
          (-((3 : ℤ) ^ (offset + 1) * terminalDiscrepancy (offset + 1) *
            secondDeletionGapCore offset upperPrefix)) =
        offset + 1 + exponent := by
    exact_mod_cast valuation'
  simpa only [neg_mul] using converted

/-- The raw `D_b` inverse has exactly one common factor three after the two `D_c` inverses;
the displayed quotient coordinates are both `3`-adic units. -/
theorem deletionBInverse_raw_and_units
    {offset : Nat} (offset_pos : 0 < offset) (upperPrefix : ℤ) :
    let punctuatedB :=
      18 * widthScale (offset + 1) ^ 2 - 4 * widthScale (offset + 1) - 1
    let rawNumerator :=
      centeredCoefficient (offset + 1) * punctuatedB *
          secondDeletionInverseNumerator offset upperPrefix -
        terminalDiscrepancy (offset + 1) ^ 2 *
          secondDeletionInverseDenominator offset upperPrefix
    let rawDenominator :=
      2 * centeredCoefficient (offset + 1) *
          secondDeletionInverseNumerator offset upperPrefix -
        2 * terminalDiscrepancy (offset + 1) *
          secondDeletionInverseDenominator offset upperPrefix
    rawNumerator = 3 * deletionBInverseNumerator offset upperPrefix ∧
      rawDenominator = 3 * deletionBInverseDenominator offset upperPrefix ∧
      ¬(3 : ℤ) ∣ deletionBInverseNumerator offset upperPrefix ∧
      ¬(3 : ℤ) ∣ deletionBInverseDenominator offset upperPrefix := by
  dsimp only
  have gap_eq := secondDeletionInverse_gap offset upperPrefix
  have scale_mod := scale_mod_three offset_pos
  have second_units := secondDeletionInverse_not_dvd_three offset_pos upperPrefix
  have second_numerator_mod :
      secondDeletionInverseNumerator offset upperPrefix ≡ 2 [ZMOD 3] := by
    have scale_mod' := scale_mod
    have width_scale_mod : widthScale (offset + 1) ≡ 0 [ZMOD 3] := by
      simpa [widthScale, pow_succ, mul_comm] using
        scale_mod'.mul (by norm_num : (3 : ℤ) ≡ 0 [ZMOD 3])
    have centered_mod : centeredCoefficient (offset + 1) ≡ 2 [ZMOD 3] := by
      simpa [centeredCoefficient] using
        ((Int.ModEq.refl (2 : ℤ)).sub width_scale_mod).trans (by norm_num)
    have terminal_mod : terminalDiscrepancy (offset + 1) ≡ 2 [ZMOD 3] := by
      have raw := ((Int.ModEq.refl (5 : ℤ)).mul width_scale_mod).sub
        (Int.ModEq.refl (1 : ℤ))
      simpa [terminalDiscrepancy] using raw.trans (by norm_num)
    have first_numerator_mod :
        firstDeletionInverseNumerator offset upperPrefix ≡ 0 [ZMOD 3] := by
      have raw := ((terminal_mod.mul centered_mod).mul scale_mod).mul
        (Int.ModEq.refl upperPrefix)
      simpa [firstDeletionInverseNumerator, mul_assoc] using raw.trans (by norm_num)
    have first_residual_mod : firstDeletionResidual offset upperPrefix ≡ 2 [ZMOD 3] := by
      have square_mod := scale_mod.mul scale_mod
      have raw :=
        ((((((Int.ModEq.refl (-3 : ℤ)).mul (Int.ModEq.refl upperPrefix)).mul square_mod).add
          (((Int.ModEq.refl (2 : ℤ)).mul (Int.ModEq.refl upperPrefix)).mul scale_mod)).sub
            ((Int.ModEq.refl (18 : ℤ)).mul square_mod)).add
              ((Int.ModEq.refl (9 : ℤ)).mul scale_mod)).sub (Int.ModEq.refl (1 : ℤ))
      norm_num at raw
      have reduced := raw.trans (by norm_num : (-1 : ℤ) ≡ 2 [ZMOD 3])
      simpa [firstDeletionResidual, pow_two] using reduced
    have first_denominator_mod :
        firstDeletionInverseDenominator offset upperPrefix ≡ 1 [ZMOD 3] := by
      have raw := (Int.ModEq.refl (2 : ℤ)).mul first_residual_mod
      simpa [firstDeletionInverseDenominator] using raw.trans (by norm_num)
    have difference := first_numerator_mod.sub first_denominator_mod
    have raw := (terminal_mod.mul centered_mod).mul difference
    simpa [secondDeletionInverseNumerator, mul_assoc] using raw.trans (by norm_num)
  have width_scale_mod : widthScale (offset + 1) ≡ 0 [ZMOD 3] := by
    simpa [widthScale, pow_succ, mul_comm] using
      scale_mod.mul (by norm_num : (3 : ℤ) ≡ 0 [ZMOD 3])
  have marker_mod : setterMarker (offset + 1) ≡ 2 [ZMOD 3] := by
    have raw := ((Int.ModEq.refl (2 : ℤ)).mul width_scale_mod).sub
      (Int.ModEq.refl (1 : ℤ))
    simpa [setterMarker] using raw.trans (by norm_num)
  have terminal_mod : terminalDiscrepancy (offset + 1) ≡ 2 [ZMOD 3] := by
    have raw := ((Int.ModEq.refl (5 : ℤ)).mul width_scale_mod).sub
      (Int.ModEq.refl (1 : ℤ))
    simpa [terminalDiscrepancy] using raw.trans (by norm_num)
  have deletion_cofactor_mod : deletionBCofactor offset ≡ 2 [ZMOD 3] := by
    have square_mod := width_scale_mod.mul width_scale_mod
    have raw := (((Int.ModEq.refl (3 : ℤ)).mul square_mod).sub width_scale_mod).sub
      (Int.ModEq.refl (1 : ℤ))
    norm_num at raw
    simpa [deletionBCofactor, pow_two] using raw.trans (by norm_num)
  have numerator_mod : deletionBInverseNumerator offset upperPrefix ≡ 1 [ZMOD 3] := by
    have first := ((Int.ModEq.refl (0 : ℤ)).sub
      ((marker_mod.mul deletion_cofactor_mod).mul second_numerator_mod))
    have second := ((scale_mod.mul (terminal_mod.mul (terminal_mod.mul terminal_mod))).mul
      (Int.ModEq.refl (secondDeletionGapCore offset upperPrefix)))
    have combined := first.add second
    norm_num at combined
    have reduced := combined.trans (by norm_num : (-8 : ℤ) ≡ 1 [ZMOD 3])
    simpa [deletionBInverseNumerator, pow_succ, pow_two, mul_assoc, mul_comm,
      mul_left_comm] using reduced
  have denominator_mod : deletionBInverseDenominator offset upperPrefix ≡ 1 [ZMOD 3] := by
    have first := ((Int.ModEq.refl (-2 : ℤ)).mul marker_mod).mul second_numerator_mod
    have second := (((Int.ModEq.refl (2 : ℤ)).mul scale_mod).mul
      (terminal_mod.mul terminal_mod)).mul
        (Int.ModEq.refl (secondDeletionGapCore offset upperPrefix))
    have combined := first.add second
    norm_num at combined
    have reduced := combined.trans (by norm_num : (-8 : ℤ) ≡ 1 [ZMOD 3])
    simpa [deletionBInverseDenominator, pow_two, mul_assoc, mul_comm,
      mul_left_comm] using reduced
  have coefficient_eq :
      centeredCoefficient (offset + 1) *
          (18 * widthScale (offset + 1) ^ 2 -
            4 * widthScale (offset + 1) - 1) -
        terminalDiscrepancy (offset + 1) ^ 2 =
      -3 * setterMarker (offset + 1) * deletionBCofactor offset := by
    simp [centeredCoefficient, terminalDiscrepancy, setterMarker,
      deletionBCofactor]
    ring
  have center_terminal_eq :
      centeredCoefficient (offset + 1) - terminalDiscrepancy (offset + 1) =
        -3 * setterMarker (offset + 1) := by
    simp [centeredCoefficient, terminalDiscrepancy, setterMarker]
    ring
  refine ⟨?_, ?_, not_dvd_three_of_mod_one numerator_mod,
    not_dvd_three_of_mod_one denominator_mod⟩
  · simp only [deletionBInverseNumerator]
    linear_combination
      secondDeletionInverseNumerator offset upperPrefix * coefficient_eq -
        terminalDiscrepancy (offset + 1) ^ 2 * gap_eq
  · simp only [deletionBInverseDenominator]
    linear_combination
      2 * secondDeletionInverseNumerator offset upperPrefix * center_terminal_eq -
        2 * terminalDiscrepancy (offset + 1) * gap_eq

/-! ## Exact projective transitions -/

/-- Unit normalization scale on the `D_c` block adjacent to the target. -/
def targetDeletionScale (offset : Nat) : ℤ :=
  -2 * terminalDiscrepancy (offset + 1) * centeredCoefficient (offset + 1) *
    setterMarker (offset + 1)

/-- Normalization scale on the preceding `D_c` block. -/
def middleDeletionScale (offset : Nat) : ℤ :=
  3 * targetDeletionScale offset

/-- Normalization scale on the preceding `D_b` block. -/
def initialDeletionBScale (offset : Nat) : ℤ :=
  3 ^ (offset + 2) * targetDeletionScale offset

private theorem spell_nearyUpper_erase_map
    (width : Nat) (letters : List TagLetter) :
    spell (nearyUpper width) (letters.map NearyTile.erase) =
      tagEncode width letters := by
  rw [spell_nearyUpper]
  simp [List.map_map, Function.comp_def, NearyTile.letter]

/-- An empty-front erasure target has the displayed upper and lower coordinates. -/
theorem emptyTarget_codes
    (offset : Nat) (body letters : List TagLetter)
    (letters_length : letters.length = offset + 1) :
    swappedUpperCode (offset + 1) (letters.map NearyTile.erase) =
        emptyTargetUpper offset
          (signedSwappedCode (tagEncode (offset + 1) letters ++ [true])) ∧
      swappedLowerCode (offset + 1) body (letters.map NearyTile.erase) =
        emptyTargetLower offset := by
  constructor
  · rw [swappedUpperCode_markerTail_factorization,
      spell_nearyUpper_erase_map]
    rfl
  · have factorization :=
      erasureTail_swappedLowerCode_factorization body letters_length
        (target := letters.map NearyTile.erase) (front := []) (by simp)
    simpa [emptyTargetLower, widthScale, spell, signedSwappedCode, ternaryCode] using
      factorization

/-- The two displayed `D_c` preimages implement the exact body-independent carrier
transitions with shell depths zero and one. -/
theorem deletionInverse_forward
    (offset : Nat) (body : List TagLetter) (upperPrefix : ℤ) :
    nextCarrierNumerator (offset + 1) body [.erase .c]
          (firstDeletionInverseNumerator offset upperPrefix)
          (firstDeletionInverseDenominator offset upperPrefix) =
        targetDeletionScale offset * emptyTargetUpper offset upperPrefix ∧
      nextCarrierDenominator (offset + 1) body [.erase .c]
          (firstDeletionInverseNumerator offset upperPrefix)
          (firstDeletionInverseDenominator offset upperPrefix) =
        targetDeletionScale offset * emptyTargetLower offset ∧
      nextCarrierNumerator (offset + 1) body [.erase .c]
          (secondDeletionInverseNumerator offset upperPrefix)
          (secondDeletionInverseDenominator offset upperPrefix) =
        middleDeletionScale offset *
          firstDeletionInverseNumerator offset upperPrefix ∧
      nextCarrierDenominator (offset + 1) body [.erase .c]
          (secondDeletionInverseNumerator offset upperPrefix)
          (secondDeletionInverseDenominator offset upperPrefix) =
        middleDeletionScale offset *
          firstDeletionInverseDenominator offset upperPrefix := by
  simp only [nextCarrierNumerator, nextCarrierDenominator,
    swappedUpperCode_singleton_c, swappedLowerCode_singleton,
    upperLength_singleton_erase_c, pow_one]
  simp [emptyTargetUpper, emptyTargetLower, firstDeletionInverseNumerator,
    firstDeletionInverseDenominator, firstDeletionResidual,
    secondDeletionInverseNumerator, secondDeletionInverseDenominator,
    targetDeletionScale, middleDeletionScale, widthScale, setterMarker,
    terminalDiscrepancy, centeredCoefficient, pow_succ]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- The displayed `D_b` preimage implements the exact body-independent carrier transition at
shell depth `offset+2`. -/
theorem deletionBInverse_forward
    {offset : Nat} (offset_pos : 0 < offset) (body : List TagLetter)
    (upperPrefix : ℤ) :
    nextCarrierNumerator (offset + 1) body [.erase .b]
          (deletionBInverseNumerator offset upperPrefix)
          (deletionBInverseDenominator offset upperPrefix) =
        initialDeletionBScale offset *
          secondDeletionInverseNumerator offset upperPrefix ∧
      nextCarrierDenominator (offset + 1) body [.erase .b]
          (deletionBInverseNumerator offset upperPrefix)
          (deletionBInverseDenominator offset upperPrefix) =
        initialDeletionBScale offset *
          secondDeletionInverseDenominator offset upperPrefix := by
  obtain ⟨rawNumerator, rawDenominator, -, -⟩ :=
    deletionBInverse_raw_and_units offset_pos upperPrefix
  simp only [nextCarrierNumerator, nextCarrierDenominator,
    swappedUpperCode_singleton_b, swappedLowerCode_singleton,
    upperLength_singleton_erase_b]
  have upper_power : (3 : ℤ) ^ (offset + 1 + 2) =
      9 * widthScale (offset + 1) := by
    simp [widthScale, pow_succ]
    ring
  have shifted_upper :
      18 * widthScale (offset + 1) ^ 2 -
          4 * widthScale (offset + 1) - 1 -
          setterMarker (offset + 1) *
            (9 * widthScale (offset + 1)) =
        terminalDiscrepancy (offset + 1) := by
    simp [setterMarker, terminalDiscrepancy]
    ring
  rw [upper_power, shifted_upper]
  have determinant :
      -2 * terminalDiscrepancy (offset + 1) *
            (centeredCoefficient (offset + 1) *
              (18 * widthScale (offset + 1) ^ 2 -
                4 * widthScale (offset + 1) - 1)) +
          terminalDiscrepancy (offset + 1) ^ 2 *
            (2 * centeredCoefficient (offset + 1)) =
        3 * initialDeletionBScale offset := by
    simp [initialDeletionBScale, targetDeletionScale, widthScale,
      setterMarker, terminalDiscrepancy, centeredCoefficient, pow_succ]
    ring
  constructor
  · apply mul_left_cancel₀ (show (3 : ℤ) ≠ 0 by norm_num)
    calc
      3 * (terminalDiscrepancy (offset + 1) *
            (terminalDiscrepancy (offset + 1) *
                deletionBInverseDenominator offset upperPrefix -
              2 * deletionBInverseNumerator offset upperPrefix)) =
          terminalDiscrepancy (offset + 1) *
            (terminalDiscrepancy (offset + 1) *
                (3 * deletionBInverseDenominator offset upperPrefix) -
              2 * (3 * deletionBInverseNumerator offset upperPrefix)) := by ring
      _ = terminalDiscrepancy (offset + 1) *
            (terminalDiscrepancy (offset + 1) *
                (2 * centeredCoefficient (offset + 1) *
                    secondDeletionInverseNumerator offset upperPrefix -
                  2 * terminalDiscrepancy (offset + 1) *
                    secondDeletionInverseDenominator offset upperPrefix) -
              2 *
                (centeredCoefficient (offset + 1) *
                    (18 * widthScale (offset + 1) ^ 2 -
                      4 * widthScale (offset + 1) - 1) *
                      secondDeletionInverseNumerator offset upperPrefix -
                  terminalDiscrepancy (offset + 1) ^ 2 *
                    secondDeletionInverseDenominator offset upperPrefix)) := by
              rw [← rawDenominator, ← rawNumerator]
      _ = (3 * initialDeletionBScale offset) *
            secondDeletionInverseNumerator offset upperPrefix := by
              rw [← determinant]
              ring
      _ = 3 * (initialDeletionBScale offset *
            secondDeletionInverseNumerator offset upperPrefix) := by ring
  · apply mul_left_cancel₀ (show (3 : ℤ) ≠ 0 by norm_num)
    calc
      3 * (centeredCoefficient (offset + 1) *
            ((18 * widthScale (offset + 1) ^ 2 -
                  4 * widthScale (offset + 1) - 1) *
                deletionBInverseDenominator offset upperPrefix -
              2 * deletionBInverseNumerator offset upperPrefix)) =
          centeredCoefficient (offset + 1) *
            ((18 * widthScale (offset + 1) ^ 2 -
                  4 * widthScale (offset + 1) - 1) *
                (3 * deletionBInverseDenominator offset upperPrefix) -
              2 * (3 * deletionBInverseNumerator offset upperPrefix)) := by ring
      _ = centeredCoefficient (offset + 1) *
            ((18 * widthScale (offset + 1) ^ 2 -
                  4 * widthScale (offset + 1) - 1) *
                (2 * centeredCoefficient (offset + 1) *
                    secondDeletionInverseNumerator offset upperPrefix -
                  2 * terminalDiscrepancy (offset + 1) *
                    secondDeletionInverseDenominator offset upperPrefix) -
              2 *
                (centeredCoefficient (offset + 1) *
                    (18 * widthScale (offset + 1) ^ 2 -
                      4 * widthScale (offset + 1) - 1) *
                      secondDeletionInverseNumerator offset upperPrefix -
                  terminalDiscrepancy (offset + 1) ^ 2 *
                    secondDeletionInverseDenominator offset upperPrefix)) := by
              rw [← rawDenominator, ← rawNumerator]
      _ = (3 * initialDeletionBScale offset) *
            secondDeletionInverseDenominator offset upperPrefix := by
              rw [← determinant]
              ring
      _ = 3 * (initialDeletionBScale offset *
            secondDeletionInverseDenominator offset upperPrefix) := by ring

/-- The three local normalization scales have depths `0`, `1`, and `offset+2`, with one
common unit cofactor. -/
theorem localScale_shells
    {offset : Nat} (offset_pos : 0 < offset) :
    ¬(3 : ℤ) ∣ targetDeletionScale offset ∧
      middleDeletionScale offset = 3 * targetDeletionScale offset ∧
      initialDeletionBScale offset =
        3 ^ (offset + 2) * targetDeletionScale offset := by
  have scale_mod := scale_mod_three offset_pos
  have width_scale_mod : widthScale (offset + 1) ≡ 0 [ZMOD 3] := by
    simpa [widthScale, pow_succ, mul_comm] using
      scale_mod.mul (by norm_num : (3 : ℤ) ≡ 0 [ZMOD 3])
  have terminal_mod : terminalDiscrepancy (offset + 1) ≡ 2 [ZMOD 3] := by
    simpa [terminalDiscrepancy] using
      (((Int.ModEq.refl (5 : ℤ)).mul width_scale_mod).sub
        (Int.ModEq.refl (1 : ℤ))).trans (by norm_num)
  have centered_mod : centeredCoefficient (offset + 1) ≡ 2 [ZMOD 3] := by
    simpa [centeredCoefficient] using
      ((Int.ModEq.refl (2 : ℤ)).sub width_scale_mod).trans (by norm_num)
  have marker_mod : setterMarker (offset + 1) ≡ 2 [ZMOD 3] := by
    simpa [setterMarker] using
      (((Int.ModEq.refl (2 : ℤ)).mul width_scale_mod).sub
        (Int.ModEq.refl (1 : ℤ))).trans (by norm_num)
  have target_mod : targetDeletionScale offset ≡ 2 [ZMOD 3] := by
    have raw := (((Int.ModEq.refl (-2 : ℤ)).mul terminal_mod).mul centered_mod).mul
      marker_mod
    simpa [targetDeletionScale, mul_assoc] using raw.trans (by norm_num)
  exact ⟨not_dvd_three_of_mod_two target_mod, rfl, rfl⟩

/-- The `D_b` predecessor cylinder is an explicit width-square multiple. This is the local
survivor required by the three-block frontier, not a reachable carrier. -/
theorem deletionB_predecessorCylinder
    {offset : Nat} (offset_pos : 0 < offset) (body : List TagLetter)
    (upperPrefix : ℤ) :
    predecessorCylinder (offset + 1) body [.erase .b] (offset + 2)
        (deletionBInverseNumerator offset upperPrefix)
        (deletionBInverseDenominator offset upperPrefix) =
      (3 : ℤ) ^ (2 * (offset + 1)) *
        (-2 * terminalDiscrepancy (offset + 1) ^ 2 *
          centeredCoefficient (offset + 1) *
          secondDeletionGapCore offset upperPrefix) := by
  have transition := deletionBInverse_forward offset_pos body upperPrefix
  have transport := normalizedTransition_gap_transport body [.erase .b]
    (scaleDepth := offset + 2)
    (show upperLength (offset + 1) [.erase .b] = offset + 2 + 1 by simp)
    transition.1 transition.2
  have marker_ne : setterMarker (offset + 1) ≠ 0 := by
    have scale_pos : (0 : ℤ) < widthScale (offset + 1) := by
      simp [widthScale]
    simp only [setterMarker]
    omega
  have coefficient_ne : -3 * setterMarker (offset + 1) ≠ 0 :=
    mul_ne_zero (by norm_num) marker_ne
  apply mul_left_cancel₀ coefficient_ne
  calc
    (-3 * setterMarker (offset + 1)) *
          predecessorCylinder (offset + 1) body [.erase .b] (offset + 2)
            (deletionBInverseNumerator offset upperPrefix)
            (deletionBInverseDenominator offset upperPrefix) =
        initialDeletionBScale offset *
          (secondDeletionInverseDenominator offset upperPrefix -
            secondDeletionInverseNumerator offset upperPrefix) := transport.symm
    _ = (-3 * setterMarker (offset + 1)) *
        ((3 : ℤ) ^ (2 * (offset + 1)) *
          (-2 * terminalDiscrepancy (offset + 1) ^ 2 *
            centeredCoefficient (offset + 1) *
            secondDeletionGapCore offset upperPrefix)) := by
      rw [secondDeletionInverse_gap]
      simp [initialDeletionBScale, targetDeletionScale, pow_succ]
      ring

/-- Exact local data carried by an empty-front backward ray. The record contains no forward
entry state and no pole hypothesis. -/
structure EmptyFrontLocalRay
    (offset : Nat) (body letters : List TagLetter) : Prop where
  letters_length : letters.length = offset + 1
  target_upper_code :
    swappedUpperCode (offset + 1) (letters.map NearyTile.erase) =
      emptyTargetUpper offset
        (signedSwappedCode (tagEncode (offset + 1) letters ++ [true]))
  target_lower_code :
    swappedLowerCode (offset + 1) body (letters.map NearyTile.erase) =
      emptyTargetLower offset
  target_cross_product :
    emptyTargetLower offset *
        swappedUpperCode (offset + 1) (letters.map NearyTile.erase) =
      emptyTargetUpper offset
          (signedSwappedCode (tagEncode (offset + 1) letters ++ [true])) *
        swappedLowerCode (offset + 1) body (letters.map NearyTile.erase)
  target_transition_numerator :
    nextCarrierNumerator (offset + 1) body [.erase .c]
        (firstDeletionInverseNumerator offset
          (signedSwappedCode (tagEncode (offset + 1) letters ++ [true])))
        (firstDeletionInverseDenominator offset
          (signedSwappedCode (tagEncode (offset + 1) letters ++ [true]))) =
      targetDeletionScale offset *
        emptyTargetUpper offset
          (signedSwappedCode (tagEncode (offset + 1) letters ++ [true]))
  target_transition_denominator :
    nextCarrierDenominator (offset + 1) body [.erase .c]
        (firstDeletionInverseNumerator offset
          (signedSwappedCode (tagEncode (offset + 1) letters ++ [true])))
        (firstDeletionInverseDenominator offset
          (signedSwappedCode (tagEncode (offset + 1) letters ++ [true]))) =
      targetDeletionScale offset * emptyTargetLower offset
  middle_transition_numerator :
    nextCarrierNumerator (offset + 1) body [.erase .c]
        (secondDeletionInverseNumerator offset
          (signedSwappedCode (tagEncode (offset + 1) letters ++ [true])))
        (secondDeletionInverseDenominator offset
          (signedSwappedCode (tagEncode (offset + 1) letters ++ [true]))) =
      middleDeletionScale offset *
        firstDeletionInverseNumerator offset
          (signedSwappedCode (tagEncode (offset + 1) letters ++ [true]))
  middle_transition_denominator :
    nextCarrierDenominator (offset + 1) body [.erase .c]
        (secondDeletionInverseNumerator offset
          (signedSwappedCode (tagEncode (offset + 1) letters ++ [true])))
        (secondDeletionInverseDenominator offset
          (signedSwappedCode (tagEncode (offset + 1) letters ++ [true]))) =
      middleDeletionScale offset *
        firstDeletionInverseDenominator offset
          (signedSwappedCode (tagEncode (offset + 1) letters ++ [true]))
  initial_transition_numerator :
    nextCarrierNumerator (offset + 1) body [.erase .b]
        (deletionBInverseNumerator offset
          (signedSwappedCode (tagEncode (offset + 1) letters ++ [true])))
        (deletionBInverseDenominator offset
          (signedSwappedCode (tagEncode (offset + 1) letters ++ [true]))) =
      initialDeletionBScale offset *
        secondDeletionInverseNumerator offset
          (signedSwappedCode (tagEncode (offset + 1) letters ++ [true]))
  initial_transition_denominator :
    nextCarrierDenominator (offset + 1) body [.erase .b]
        (deletionBInverseNumerator offset
          (signedSwappedCode (tagEncode (offset + 1) letters ++ [true])))
        (deletionBInverseDenominator offset
          (signedSwappedCode (tagEncode (offset + 1) letters ++ [true]))) =
      initialDeletionBScale offset *
        secondDeletionInverseDenominator offset
          (signedSwappedCode (tagEncode (offset + 1) letters ++ [true]))
  target_scale_unit : ¬(3 : ℤ) ∣ targetDeletionScale offset
  middle_scale_shell : middleDeletionScale offset = 3 * targetDeletionScale offset
  initial_scale_shell :
    initialDeletionBScale offset = 3 ^ (offset + 2) * targetDeletionScale offset
  first_denominator_unit :
    ¬(3 : ℤ) ∣ firstDeletionInverseDenominator offset
      (signedSwappedCode (tagEncode (offset + 1) letters ++ [true]))
  second_coordinates_unit :
    ¬(3 : ℤ) ∣ secondDeletionInverseNumerator offset
        (signedSwappedCode (tagEncode (offset + 1) letters ++ [true])) ∧
      ¬(3 : ℤ) ∣ secondDeletionInverseDenominator offset
        (signedSwappedCode (tagEncode (offset + 1) letters ++ [true]))
  initial_coordinates_unit :
    ¬(3 : ℤ) ∣ deletionBInverseNumerator offset
        (signedSwappedCode (tagEncode (offset + 1) letters ++ [true])) ∧
      ¬(3 : ℤ) ∣ deletionBInverseDenominator offset
        (signedSwappedCode (tagEncode (offset + 1) letters ++ [true]))
  antecedent_gap :
    secondDeletionInverseDenominator offset
          (signedSwappedCode (tagEncode (offset + 1) letters ++ [true])) -
        secondDeletionInverseNumerator offset
          (signedSwappedCode (tagEncode (offset + 1) letters ++ [true])) =
      -3 * 3 ^ offset * terminalDiscrepancy (offset + 1) *
        secondDeletionGapCore offset
          (signedSwappedCode (tagEncode (offset + 1) letters ++ [true]))
  initial_cylinder :
    predecessorCylinder (offset + 1) body [.erase .b] (offset + 2)
        (deletionBInverseNumerator offset
          (signedSwappedCode (tagEncode (offset + 1) letters ++ [true])))
        (deletionBInverseDenominator offset
          (signedSwappedCode (tagEncode (offset + 1) letters ++ [true]))) =
      (3 : ℤ) ^ (2 * (offset + 1)) *
        (-2 * terminalDiscrepancy (offset + 1) ^ 2 *
          centeredCoefficient (offset + 1) *
          secondDeletionGapCore offset
            (signedSwappedCode (tagEncode (offset + 1) letters ++ [true])))

/-- Every empty-front erasure target has a body-independent local backward ray through
`D_b;D_c;D_c`. This is neither a reachability theorem nor a pole theorem. -/
theorem exists_emptyFrontLocalRay
    {offset : Nat} (offset_pos : 0 < offset) (body letters : List TagLetter)
    (letters_length : letters.length = offset + 1) :
    EmptyFrontLocalRay offset body letters := by
  let upperPrefix :=
    signedSwappedCode (tagEncode (offset + 1) letters ++ [true])
  have target_codes := emptyTarget_codes offset body letters letters_length
  have deletion_transitions := deletionInverse_forward offset body upperPrefix
  have initial_transitions := deletionBInverse_forward offset_pos body upperPrefix
  have scale_shells := localScale_shells offset_pos
  have first_unit :=
    firstDeletionInverseDenominator_not_dvd_three offset_pos upperPrefix
  have second_units := secondDeletionInverse_not_dvd_three offset_pos upperPrefix
  obtain ⟨-, -, initial_numerator_unit, initial_denominator_unit⟩ :=
    deletionBInverse_raw_and_units offset_pos upperPrefix
  refine
    { letters_length := letters_length
      target_upper_code := target_codes.1
      target_lower_code := target_codes.2
      target_cross_product := ?_
      target_transition_numerator := deletion_transitions.1
      target_transition_denominator := deletion_transitions.2.1
      middle_transition_numerator := deletion_transitions.2.2.1
      middle_transition_denominator := deletion_transitions.2.2.2
      initial_transition_numerator := initial_transitions.1
      initial_transition_denominator := initial_transitions.2
      target_scale_unit := scale_shells.1
      middle_scale_shell := scale_shells.2.1
      initial_scale_shell := scale_shells.2.2
      first_denominator_unit := first_unit
      second_coordinates_unit := second_units
      initial_coordinates_unit := ⟨initial_numerator_unit, initial_denominator_unit⟩
      antecedent_gap := secondDeletionInverse_gap offset upperPrefix
      initial_cylinder := deletionB_predecessorCylinder offset_pos body upperPrefix }
  rw [target_codes.1, target_codes.2]
  ring

private theorem tagWord_trailingC_cases (letters : List TagLetter) :
    letters = List.replicate letters.length .c ∨
      ∃ stem trailing,
        letters = stem ++ .b :: List.replicate trailing .c := by
  induction letters using List.reverseRecOn with
  | nil => exact Or.inl rfl
  | append_singleton letters letter induction =>
      cases letter with
      | b =>
          exact Or.inr ⟨letters, 0, by simp⟩
      | c =>
          rcases induction with all_c | ⟨stem, trailing, shape⟩
          · apply Or.inl
            rw [all_c]
            simp [List.replicate_succ']
          · apply Or.inr
            refine ⟨stem, trailing + 1, ?_⟩
            rw [shape]
            simp [List.replicate_succ', List.append_assoc]

/-- The complete empty-front family has one exact depth determined by its terminal run of
`c` letters. The all-`c` target has depth `offset+2`; otherwise a suffix of `trailing` many
`c` letters has depth `trailing+2`. -/
theorem emptyTarget_gapCore_padicValInt_cases
    {offset : Nat} (offset_two : 2 ≤ offset) (letters : List TagLetter)
    (letters_length : letters.length = offset + 1) :
    (letters = List.replicate (offset + 1) .c ∧
        padicValInt 3
            (2 * signedSwappedCode
              (tagEncode (offset + 1) letters ++ [true]) + 1) = offset + 2 ∧
        padicValInt 3
            (secondDeletionGapCore offset
              (signedSwappedCode (tagEncode (offset + 1) letters ++ [true]))) =
          offset + 2) ∨
      ∃ stem trailing,
        letters = stem ++ .b :: List.replicate trailing .c ∧
          trailing ≤ offset ∧
          padicValInt 3
              (2 * signedSwappedCode
                (tagEncode (offset + 1) letters ++ [true]) + 1) = trailing + 2 ∧
          padicValInt 3
              (secondDeletionGapCore offset
                (signedSwappedCode (tagEncode (offset + 1) letters ++ [true]))) =
            trailing + 2 := by
  rcases tagWord_trailingC_cases letters with all_c | ⟨stem, trailing, shape⟩
  · have all_c' : letters = List.replicate (offset + 1) .c := by
      simpa [letters_length] using all_c
    apply Or.inl
    refine ⟨all_c', ?_, ?_⟩
    · rw [all_c']
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        allC_upperPrefix_padicValInt (offset + 1)
    · apply secondDeletionGapCore_padicValInt offset_two
        (exponent := offset + 2)
      · omega
      · refine ⟨1, ?_, by norm_num⟩
        rw [all_c', allC_upperPrefix_factorization]
        ring
  · have trailing_le : trailing ≤ offset := by
      rw [shape] at letters_length
      simp only [List.length_append, List.length_cons, List.length_replicate] at letters_length
      omega
    apply Or.inr
    refine ⟨stem, trailing, shape, trailing_le, ?_, ?_⟩
    · rw [shape]
      exact trailingC_upperPrefix_padicValInt (by omega) stem trailing
    · apply secondDeletionGapCore_padicValInt offset_two
        (exponent := trailing + 2)
      · omega
      · simpa [shape] using
          trailingC_upperPrefix_factorization (show 0 < offset + 1 by omega)
            stem trailing

/-- The corresponding antecedent gap depths are `2·offset+3` for the all-`c` target and
`offset+trailing+3` otherwise. -/
theorem emptyTarget_antecedentGap_padicValInt_cases
    {offset : Nat} (offset_two : 2 ≤ offset) (letters : List TagLetter)
    (letters_length : letters.length = offset + 1) :
    (letters = List.replicate (offset + 1) .c ∧
        padicValInt 3
            (secondDeletionInverseDenominator offset
                (signedSwappedCode (tagEncode (offset + 1) letters ++ [true])) -
              secondDeletionInverseNumerator offset
                (signedSwappedCode (tagEncode (offset + 1) letters ++ [true]))) =
          2 * offset + 3) ∨
      ∃ stem trailing,
        letters = stem ++ .b :: List.replicate trailing .c ∧
          trailing ≤ offset ∧
          padicValInt 3
              (secondDeletionInverseDenominator offset
                  (signedSwappedCode (tagEncode (offset + 1) letters ++ [true])) -
                secondDeletionInverseNumerator offset
                  (signedSwappedCode (tagEncode (offset + 1) letters ++ [true]))) =
            offset + trailing + 3 := by
  rcases tagWord_trailingC_cases letters with all_c | ⟨stem, trailing, shape⟩
  · have all_c' : letters = List.replicate (offset + 1) .c := by
      simpa [letters_length] using all_c
    apply Or.inl
    refine ⟨all_c', ?_⟩
    have gap_valuation := secondDeletionInverse_gap_padicValInt offset_two
      (show 0 < offset + 2 by omega)
      (signedSwappedCode (tagEncode (offset + 1) letters ++ [true]))
      (show offset + 2 ≤ offset + 2 by omega)
      (show ∃ cofactor : ℤ,
          2 * signedSwappedCode (tagEncode (offset + 1) letters ++ [true]) + 1 =
              (3 : ℤ) ^ (offset + 2) * cofactor ∧
            ¬(3 : ℤ) ∣ cofactor by
        refine ⟨1, ?_, by norm_num⟩
        rw [all_c', allC_upperPrefix_factorization]
        ring)
    omega
  · have trailing_le : trailing ≤ offset := by
      rw [shape] at letters_length
      simp only [List.length_append, List.length_cons, List.length_replicate] at letters_length
      omega
    apply Or.inr
    refine ⟨stem, trailing, shape, trailing_le, ?_⟩
    have gap_valuation := secondDeletionInverse_gap_padicValInt offset_two
      (show 0 < trailing + 2 by omega)
      (signedSwappedCode (tagEncode (offset + 1) letters ++ [true]))
      (show trailing + 2 ≤ offset + 2 by omega)
      (by
        simpa [shape] using
          trailingC_upperPrefix_factorization (show 0 < offset + 1 by omega)
            stem trailing)
    omega

end MatrixMortality.SwappedSetterEmptyFrontRay
