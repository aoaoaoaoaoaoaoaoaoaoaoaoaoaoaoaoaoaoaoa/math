import MatrixMortality.SwappedSetterDeletionCContraction
import MatrixMortality.SwappedSetterEmptyFrontChamber

set_option autoImplicit false

/-!
# Primitive physical pullbacks for the swapped setter

This module isolates the arithmetic lost when an inverse physical block is immediately reduced
to primitive coordinates.  Raw divisibility by the half-head is only the first condition: the
normalizing gcd must leave no residual half-head factor in the denominator.  The final section
records the affine upper-code recurrence which governs that residual channel.
-/

namespace MatrixMortality.SwappedSetterPrimitivePullback

open SwappedSetterMultitransfer SwappedSetterEmptyFrontChamber
  SwappedSetterDeletionCContraction

/-! ## Raw inverse coordinates -/

/-- Positive affine time in the inverse physical-block formula. -/
def pullbackTime (width numerator denominator : Nat) : Nat :=
  deletionCRadius width * numerator + deletionCHead width * denominator

/-- Raw positive numerator of an inverse physical block in the chamber where the subtraction
succeeds. -/
def pullbackRawNumerator
    (width punctuated upperPower numerator denominator : Nat) : Nat :=
  punctuated * pullbackTime width numerator denominator -
    deletionCHead width * deletionCMarker width * upperPower * denominator

/-- Raw positive denominator of an inverse physical block. -/
def pullbackRawDenominator
    (width lower numerator denominator : Nat) : Nat :=
  lower * pullbackTime width numerator denominator

/-- Clearing one inverse affine denominator gives the raw physical pullback pair. -/
theorem inverseFraction_eq_rawRatio
    {head radius marker punctuated lower upperPower numerator denominator : ℚ}
    (lower_ne : lower ≠ 0) (denominator_ne : denominator ≠ 0)
    (time_ne : radius * numerator + head * denominator ≠ 0) :
    punctuated / lower -
        head * marker * upperPower /
          (lower * (head + radius * (numerator / denominator))) =
      (punctuated * (radius * numerator + head * denominator) -
          head * marker * upperPower * denominator) /
        (lower * (radius * numerator + head * denominator)) := by
  have time_ne' : head * denominator + radius * numerator ≠ 0 := by
    simpa only [add_comm] using time_ne
  field_simp [lower_ne, denominator_ne, time_ne, time_ne']
  ring_nf

/-! ## Exact primitive cancellation -/

/-- Primitive numerator obtained by cancelling the complete natural gcd. -/
def primitiveNumerator (numerator denominator : Nat) : Nat :=
  numerator / Nat.gcd numerator denominator

/-- Splitting the residual by `gcd(residual, denominator)` isolates the exact part of the raw
gcd supported on `halfHead`. -/
theorem gcd_mul_residual_split
    {halfHead residual denominator : Nat} (denominator_pos : 0 < denominator) :
    Nat.gcd (halfHead * residual) denominator =
      Nat.gcd residual denominator *
        Nat.gcd halfHead (denominator / Nat.gcd residual denominator) := by
  let common := Nat.gcd residual denominator
  let reducedResidual := residual / common
  let reducedDenominator := denominator / common
  have common_pos : 0 < common := Nat.gcd_pos_of_pos_right residual denominator_pos
  have residual_eq : residual = reducedResidual * common := by
    dsimp only [reducedResidual, common]
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_left residual denominator)).symm
  have denominator_eq : denominator = reducedDenominator * common := by
    dsimp only [reducedDenominator, common]
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_right residual denominator)).symm
  have reduced_coprime : reducedResidual.Coprime reducedDenominator :=
    Nat.coprime_div_gcd_div_gcd common_pos
  calc
    Nat.gcd (halfHead * residual) denominator =
        Nat.gcd (common * (reducedResidual * halfHead))
          (common * reducedDenominator) := by rw [residual_eq, denominator_eq]; ring_nf
    _ = common * Nat.gcd (reducedResidual * halfHead) reducedDenominator := by
      rw [Nat.gcd_mul_left]
    _ = common * Nat.gcd halfHead reducedDenominator := by
      rw [reduced_coprime.gcd_mul_left_cancel]
    _ = Nat.gcd residual denominator *
        Nat.gcd halfHead (denominator / Nat.gcd residual denominator) := rfl

/-- After raw half-head divisibility, the reduced numerator retains the whole half-head exactly
when the denominator left after residual cancellation is coprime to it. -/
theorem halfHead_dvd_primitiveNumerator_iff
    {halfHead residual denominator : Nat} (halfHead_pos : 0 < halfHead)
    (denominator_pos : 0 < denominator) :
    halfHead ∣ primitiveNumerator (halfHead * residual) denominator ↔
      halfHead.Coprime (denominator / Nat.gcd residual denominator) := by
  let common := Nat.gcd residual denominator
  let reducedResidual := residual / common
  let reducedDenominator := denominator / common
  let headCommon := Nat.gcd halfHead reducedDenominator
  have common_pos : 0 < common := Nat.gcd_pos_of_pos_right residual denominator_pos
  have residual_eq : residual = reducedResidual * common := by
    dsimp only [reducedResidual, common]
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_left residual denominator)).symm
  have denominator_eq : denominator = reducedDenominator * common := by
    dsimp only [reducedDenominator, common]
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_right residual denominator)).symm
  have reduced_coprime : reducedResidual.Coprime reducedDenominator :=
    Nat.coprime_div_gcd_div_gcd common_pos
  have raw_gcd_eq :
      Nat.gcd (halfHead * residual) denominator = common * headCommon := by
    simpa only [common, reducedDenominator, headCommon] using
      gcd_mul_residual_split (halfHead := halfHead) (residual := residual)
        denominator_pos
  constructor
  · intro head_dvd
    obtain ⟨quotient, quotient_eq⟩ := head_dvd
    have raw_reconstitution :
        Nat.gcd (halfHead * residual) denominator *
            primitiveNumerator (halfHead * residual) denominator =
          halfHead * residual := by
      exact Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    have headCommon_dvd_reducedResidual : headCommon ∣ reducedResidual := by
      refine ⟨quotient, ?_⟩
      apply Nat.eq_of_mul_eq_mul_left (mul_pos halfHead_pos common_pos)
      calc
        halfHead * common * reducedResidual = halfHead * residual := by
          rw [residual_eq]
          ring_nf
        _ = Nat.gcd (halfHead * residual) denominator *
            primitiveNumerator (halfHead * residual) denominator := raw_reconstitution.symm
        _ = (common * headCommon) * (halfHead * quotient) := by
          rw [raw_gcd_eq, quotient_eq]
        _ = halfHead * common * (headCommon * quotient) := by ring_nf
    have headCommon_dvd_reducedDenominator : headCommon ∣ reducedDenominator :=
      Nat.gcd_dvd_right _ _
    have headCommon_eq : headCommon = 1 :=
      Nat.eq_one_of_dvd_coprimes reduced_coprime headCommon_dvd_reducedResidual
        headCommon_dvd_reducedDenominator
    rw [Nat.coprime_iff_gcd_eq_one]
    simpa only [common, reducedDenominator, headCommon] using headCommon_eq
  · intro coprime
    have headCommon_eq : headCommon = 1 := by
      rw [Nat.coprime_iff_gcd_eq_one] at coprime
      simpa only [common, reducedDenominator, headCommon] using coprime
    refine ⟨reducedResidual, ?_⟩
    apply Nat.eq_of_mul_eq_mul_left common_pos
    have raw_reconstitution :
        Nat.gcd (halfHead * residual) denominator *
            primitiveNumerator (halfHead * residual) denominator =
          halfHead * residual :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    calc
      common * primitiveNumerator (halfHead * residual) denominator =
          Nat.gcd (halfHead * residual) denominator *
            primitiveNumerator (halfHead * residual) denominator := by
              rw [raw_gcd_eq, headCommon_eq, mul_one]
      _ = halfHead * residual := raw_reconstitution
      _ = common * (halfHead * reducedResidual) := by rw [residual_eq]; ring_nf

/-- Removing the gcd with a known factor gives the exact modulus which must divide its
coefficient. -/
theorem div_gcd_dvd_iff_dvd_mul
    {modulus factor coefficient : Nat} (modulus_pos : 0 < modulus) :
    modulus / Nat.gcd modulus factor ∣ coefficient ↔
      modulus ∣ coefficient * factor := by
  let common := Nat.gcd modulus factor
  let reducedModulus := modulus / common
  let reducedFactor := factor / common
  have common_pos : 0 < common := Nat.gcd_pos_of_pos_left factor modulus_pos
  have modulus_eq : modulus = reducedModulus * common := by
    dsimp only [reducedModulus, common]
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_left modulus factor)).symm
  have factor_eq : factor = reducedFactor * common := by
    dsimp only [reducedFactor, common]
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_right modulus factor)).symm
  have reduced_coprime : reducedModulus.Coprime reducedFactor :=
    Nat.coprime_div_gcd_div_gcd common_pos
  constructor
  · rintro ⟨quotient, coefficient_eq⟩
    have coefficient_eq_reduced : coefficient = reducedModulus * quotient := by
      simpa only [reducedModulus, common] using coefficient_eq
    refine ⟨quotient * reducedFactor, ?_⟩
    rw [modulus_eq, factor_eq, coefficient_eq_reduced]
    ring_nf
  · intro modulus_dvd
    rw [modulus_eq, factor_eq] at modulus_dvd
    obtain ⟨quotient, quotient_eq⟩ := modulus_dvd
    have reduced_dvd_product : reducedModulus ∣ coefficient * reducedFactor := by
      refine ⟨quotient, ?_⟩
      apply Nat.eq_of_mul_eq_mul_right common_pos
      calc
        coefficient * reducedFactor * common =
            coefficient * (reducedFactor * common) := by ring_nf
        _ = reducedModulus * common * quotient := quotient_eq
        _ = reducedModulus * quotient * common := by ring_nf
    exact reduced_coprime.dvd_mul_right.mp reduced_dvd_product

/-! ## Physical pullback congruence -/

/-- Once the natural subtraction is genuine, the raw physical numerator retains only the
punctuated code, radius, and incoming numerator modulo the half-head. -/
theorem pullbackRawNumerator_modEq
    {width punctuated upperPower numerator denominator : Nat}
    (correction_le :
      deletionCHead width * deletionCMarker width * upperPower * denominator ≤
        punctuated * pullbackTime width numerator denominator) :
    pullbackRawNumerator width punctuated upperPower numerator denominator ≡
      punctuated * deletionCRadius width * numerator
        [MOD deletionCHalfHead width] := by
  have head_zero :
      deletionCHead width ≡ 0 [MOD deletionCHalfHead width] := by
    rw [deletionCHead_eq_twice_halfHead]
    exact (dvd_mul_left (deletionCHalfHead width) 2).modEq_zero_nat
  have time_mod :
      pullbackTime width numerator denominator ≡
        deletionCRadius width * numerator [MOD deletionCHalfHead width] := by
    simp only [pullbackTime]
    simpa only [zero_mul, add_zero] using
      (Nat.ModEq.refl (deletionCRadius width * numerator)).add
        (head_zero.mul_right denominator)
  have minuend_mod :
      punctuated * pullbackTime width numerator denominator ≡
        punctuated * deletionCRadius width * numerator
          [MOD deletionCHalfHead width] := by
    simpa only [mul_assoc] using time_mod.mul_left punctuated
  have correction_mod :
      deletionCHead width * deletionCMarker width * upperPower * denominator ≡
        0 [MOD deletionCHalfHead width] := by
    simpa only [mul_assoc, zero_mul] using
      head_zero.mul_right (deletionCMarker width * upperPower * denominator)
  have subtraction_compatible :
      deletionCHead width * deletionCMarker width * upperPower * denominator ≤
          punctuated * pullbackTime width numerator denominator ↔
        0 ≤ punctuated * deletionCRadius width * numerator :=
    iff_of_true correction_le (Nat.zero_le _)
  exact Nat.ModEq.sub' subtraction_compatible minuend_mod correction_mod

/-- Exact raw half-head divisibility is the incoming-numerator gcd channel.  Coprimality of the
radius removes it from the congruence. -/
theorem deletionCHalfHead_dvd_pullbackRawNumerator_iff
    {width punctuated upperPower numerator denominator : Nat} (width_two : 2 ≤ width)
    (correction_le :
      deletionCHead width * deletionCMarker width * upperPower * denominator ≤
        punctuated * pullbackTime width numerator denominator) :
    deletionCHalfHead width ∣
        pullbackRawNumerator width punctuated upperPower numerator denominator ↔
      deletionCHalfHead width / Nat.gcd (deletionCHalfHead width) numerator ∣
        punctuated := by
  have raw_mod := pullbackRawNumerator_modEq correction_le
  have raw_dvd_iff :
      deletionCHalfHead width ∣
          pullbackRawNumerator width punctuated upperPower numerator denominator ↔
        deletionCHalfHead width ∣
          punctuated * deletionCRadius width * numerator := by
    constructor
    · intro raw_dvd
      exact Nat.modEq_zero_iff_dvd.mp
        (raw_mod.symm.trans raw_dvd.modEq_zero_nat)
    · intro product_dvd
      exact Nat.modEq_zero_iff_dvd.mp
        (raw_mod.trans product_dvd.modEq_zero_nat)
  rw [raw_dvd_iff]
  have radius_coprime := deletionCHalfHead_coprime_radius width_two
  rw [show punctuated * deletionCRadius width * numerator =
    (punctuated * numerator) * deletionCRadius width by ring_nf]
  rw [radius_coprime.dvd_mul_right]
  exact
    (div_gcd_dvd_iff_dvd_mul
      (modulus := deletionCHalfHead width) (factor := numerator)
      (coefficient := punctuated) (deletionCHalfHead_pos width)).symm

/-- Instantiation of the exact survival criterion for a sign-normalized physical pullback. -/
theorem deletionCHalfHead_dvd_primitivePullback_iff
    {width punctuated lower upperPower numerator denominator residual : Nat}
    (raw_eq :
      pullbackRawNumerator width punctuated upperPower numerator denominator =
        deletionCHalfHead width * residual)
    (raw_denominator_pos :
      0 < pullbackRawDenominator width lower numerator denominator) :
    deletionCHalfHead width ∣
        primitiveNumerator
          (pullbackRawNumerator width punctuated upperPower numerator denominator)
          (pullbackRawDenominator width lower numerator denominator) ↔
      (deletionCHalfHead width).Coprime
        (pullbackRawDenominator width lower numerator denominator /
          Nat.gcd residual
            (pullbackRawDenominator width lower numerator denominator)) := by
  rw [raw_eq]
  exact halfHead_dvd_primitiveNumerator_iff
    (deletionCHalfHead_pos width) raw_denominator_pos

/-! ## Upper-code automaton -/

/-- Swapped ternary code of an unpunctuated encoded tag word. -/
def upperLetterCode (width : Nat) (letters : List TagLetter) : Nat :=
  ternaryCode ((tagEncode width letters).map not)

/-- Appending `c` is the affine ternary step `Z ↦ 3Z + 1`. -/
theorem upperLetterCode_append_c (width : Nat) (letters : List TagLetter) :
    upperLetterCode width (letters ++ [.c]) =
      3 * upperLetterCode width letters + 1 := by
  rw [upperLetterCode, tagEncode_append, List.map_append, ternaryCode_append]
  norm_num [tagEncode_cons, tagCode, upperLetterCode, ternaryCode, ternaryDigit]

/-- Appending `b` is the affine step `Z ↦ 9·3^width·Z + 6·3^width - 2`. -/
theorem upperLetterCode_append_b (width : Nat) (letters : List TagLetter) :
    upperLetterCode width (letters ++ [.b]) =
      9 * 3 ^ width * upperLetterCode width letters + (6 * 3 ^ width - 2) := by
  rw [upperLetterCode, tagEncode_append, List.map_append, ternaryCode_append,
    List.length_map]
  simp only [tagEncode_cons, tagEncode_nil, List.append_nil]
  rw [swappedCode_tagCode_b]
  simp only [tagCode, List.length_append, List.length_cons, List.length_replicate,
    List.length_nil]
  rw [pow_add]
  norm_num
  simp only [upperLetterCode]
  rw [show 1 + width = width + 1 by omega, pow_succ]
  ring_nf

/-- The residue `1` is fixed by the appended-`b` affine step modulo the half-head. -/
theorem upperLetterCode_append_b_modEq_one
    {width : Nat} {letters : List TagLetter}
    (code_mod : upperLetterCode width letters ≡ 1 [MOD deletionCHalfHead width]) :
    upperLetterCode width (letters ++ [.b]) ≡ 1 [MOD deletionCHalfHead width] := by
  rw [upperLetterCode_append_b]
  have affine_mod :
      9 * 3 ^ width * upperLetterCode width letters + (6 * 3 ^ width - 2) ≡
        9 * 3 ^ width * 1 + (6 * 3 ^ width - 2)
          [MOD deletionCHalfHead width] :=
    (code_mod.mul_left (9 * 3 ^ width)).add_right (6 * 3 ^ width - 2)
  have fixed_point :
      9 * 3 ^ width + (6 * 3 ^ width - 2) =
        6 * deletionCHalfHead width + 1 := by
    have head_eq := deletionCHead_eq_twice_halfHead width
    simp only [deletionCHead] at head_eq
    have power_pos : 0 < 3 ^ width := pow_pos (by omega) width
    omega
  have fixed_mod :
      9 * 3 ^ width + (6 * 3 ^ width - 2) ≡
        1 [MOD deletionCHalfHead width] := by
    rw [fixed_point]
    simpa only [zero_add] using
      ((dvd_mul_left (deletionCHalfHead width) 6).modEq_zero_nat.add_right 1)
  have fixed_mod' :
      9 * 3 ^ width * 1 + (6 * 3 ^ width - 2) ≡
        1 [MOD deletionCHalfHead width] := by
    simpa only [mul_one] using fixed_mod
  exact affine_mod.trans fixed_mod'

end MatrixMortality.SwappedSetterPrimitivePullback
