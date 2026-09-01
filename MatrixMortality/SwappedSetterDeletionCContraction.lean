import MatrixMortality.SwappedSetterEmptyFrontRay

set_option autoImplicit false

/-!
# The exact singleton-`D_c` contraction chamber
-/

namespace MatrixMortality.SwappedSetterDeletionCContraction

open SwappedSetterMultitransfer SwappedSetterThresholdCarry
  SwappedSetterCarrierGap

/-- Positive head coefficient of the swapped setter. -/
def deletionCHead (width : Nat) : Nat :=
  5 * 3 ^ width - 1

/-- Half of the even head coefficient. -/
def deletionCHalfHead (width : Nat) : Nat :=
  deletionCHead width / 2

/-- Positive magnitude of the centered coefficient. -/
def deletionCRadius (width : Nat) : Nat :=
  3 ^ width - 2

/-- Positive setter marker. -/
def deletionCMarker (width : Nat) : Nat :=
  2 * 3 ^ width - 1

/-- Absolute raw numerator of an inverse singleton `D_c` transition in the chamber `d < n`. -/
def deletionCRawNumerator (width numerator denominator : Nat) : Nat :=
  deletionCHead width * deletionCRadius width * (numerator - denominator)

/-- Absolute raw denominator of an inverse singleton `D_c` transition in the chamber `d < n`. -/
def deletionCRawDenominator (width numerator denominator : Nat) : Nat :=
  2 * (deletionCRadius width * numerator + deletionCHead width * denominator)

/-- Farey-triangle height of a nonnegative integral carrier. -/
def fareyHeight (numerator denominator : Nat) : Nat :=
  max numerator (max denominator (numerator.dist denominator))

/-- Limiting Farey contraction ratio in the exact `3H` normalization channel. -/
def deletionCContractionFactor (width : Nat) : ℚ :=
  (2 * deletionCMarker width : Nat) / deletionCHead width

private theorem width_power_odd (width : Nat) : Odd (3 ^ width : Nat) :=
  (by norm_num : Odd (3 : Nat)).pow

private theorem natCoprime_of_isCoprime_int {left right : Nat}
    (coprime : IsCoprime (left : ℤ) (right : ℤ)) : left.Coprime right := by
  rw [Nat.coprime_iff_gcd_eq_one]
  have integer_gcd := Int.isCoprime_iff_gcd_eq_one.mp coprime
  simpa [Int.gcd_eq_natAbs] using integer_gcd

theorem deletionCHead_eq_twice_halfHead (width : Nat) :
    deletionCHead width = 2 * deletionCHalfHead width := by
  have power_odd := width_power_odd width
  obtain ⟨half, power_eq⟩ := power_odd
  simp only [deletionCHead, deletionCHalfHead]
  rw [power_eq]
  omega

theorem deletionCHalfHead_pos (width : Nat) : 0 < deletionCHalfHead width := by
  have power_pos : 0 < 3 ^ width := pow_pos (by omega) _
  have head_eq := deletionCHead_eq_twice_halfHead width
  simp only [deletionCHead] at head_eq
  omega

theorem deletionCRadius_pos
    {width : Nat} (width_pos : 0 < width) : 0 < deletionCRadius width := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt width_pos)
  simp only [deletionCRadius, pow_succ]
  have power_pos : 0 < 3 ^ offset := pow_pos (by omega) _
  omega

/-- The positive raw pair is the sign-normalized adjugate pullback of singleton `D_c`. -/
theorem deletionC_rawAdjugate
    {width numerator denominator : Nat} (width_two : 2 ≤ width)
    (denominator_lt_numerator : denominator < numerator) :
    terminalDiscrepancy width * centeredCoefficient width *
          ((numerator : ℤ) - denominator) =
        -(deletionCRawNumerator width numerator denominator : ℤ) ∧
      2 * (centeredCoefficient width * numerator -
          terminalDiscrepancy width * denominator) =
        -(deletionCRawDenominator width numerator denominator : ℤ) := by
  have denominator_le : denominator ≤ numerator := denominator_lt_numerator.le
  have power_two : 2 ≤ 3 ^ width := by
    obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le width_two
    simp only [pow_add]
    have power_pos : 0 < 3 ^ offset := pow_pos (by omega) _
    nlinarith
  have head_cast : (deletionCHead width : ℤ) = terminalDiscrepancy width := by
    simp only [deletionCHead, terminalDiscrepancy, widthScale]
    rw [Nat.cast_sub]
    · norm_num
    · nlinarith
  have radius_cast : (deletionCRadius width : ℤ) = -centeredCoefficient width := by
    simp only [deletionCRadius, centeredCoefficient, widthScale]
    rw [Nat.cast_sub power_two]
    push_cast
    ring
  have centered_cast : centeredCoefficient width = -(deletionCRadius width : ℤ) := by
    linear_combination radius_cast
  constructor
  · rw [← head_cast, centered_cast]
    simp only [deletionCRawNumerator]
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub denominator_le]
    ring
  · rw [← head_cast, centered_cast]
    simp only [deletionCRawDenominator]
    push_cast
    ring

/-- Applying the existing singleton-`D_c` carrier recurrence to the adjugate pullback restores
the target pair with its exact positive determinant. -/
theorem deletionC_rawAdjugate_forward
    {width numerator denominator : Nat} (width_two : 2 ≤ width)
    (denominator_lt_numerator : denominator < numerator) (body : List TagLetter) :
    let rawNumerator : ℤ := -(deletionCRawNumerator width numerator denominator : ℤ)
    let rawDenominator : ℤ := -(deletionCRawDenominator width numerator denominator : ℤ)
    let determinant : ℤ :=
      -6 * terminalDiscrepancy width * centeredCoefficient width * setterMarker width
    nextCarrierNumerator width body [.erase .c] rawNumerator rawDenominator =
        determinant * numerator ∧
      nextCarrierDenominator width body [.erase .c] rawNumerator rawDenominator =
        determinant * denominator := by
  dsimp only
  obtain ⟨raw_numerator, raw_denominator⟩ :=
    deletionC_rawAdjugate width_two denominator_lt_numerator
  rw [← raw_numerator, ← raw_denominator]
  simp only [nextCarrierNumerator, nextCarrierDenominator,
    swappedUpperCode_singleton_c, swappedLowerCode_singleton,
    upperLength_singleton_erase_c, pow_one]
  simp only [terminalDiscrepancy, centeredCoefficient, setterMarker, widthScale]
  constructor <;> ring

theorem deletionCHead_add_radius
    {width : Nat} (width_pos : 0 < width) :
    deletionCHead width + deletionCRadius width = 3 * deletionCMarker width := by
  have power_two : 2 ≤ 3 ^ width := by
    obtain ⟨offset, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt width_pos)
    rw [pow_succ]
    have power_pos : 0 < 3 ^ offset := pow_pos (by omega) _
    omega
  simp only [deletionCHead, deletionCRadius, deletionCMarker]
  omega

theorem deletionCMarker_lt_head (width : Nat) :
    2 * deletionCMarker width < deletionCHead width := by
  simp only [deletionCMarker, deletionCHead]
  have power_pos : 0 < 3 ^ width := pow_pos (by omega) _
  omega

theorem fareyHeight_eq_max (numerator denominator : Nat) :
    fareyHeight numerator denominator = max numerator denominator := by
  simp only [fareyHeight]
  rcases le_total numerator denominator with ordered | ordered
  · rw [Nat.dist_eq_sub_of_le ordered]
    omega
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le ordered]
    omega

private theorem deletionCHead_two_add_cast (offset : Nat) :
    (deletionCHead (2 + offset) : ℤ) = 45 * (3 : ℤ) ^ offset - 1 := by
  have power_pos : 0 < 3 ^ offset := pow_pos (by omega) _
  have head_rhs : 1 ≤ 45 * 3 ^ offset := by nlinarith
  have head_eq_nat : deletionCHead (2 + offset) = 45 * 3 ^ offset - 1 := by
    simp only [deletionCHead, pow_add]
    congr 1
    ring
  calc
    (deletionCHead (2 + offset) : ℤ) =
        ((45 * 3 ^ offset - 1 : Nat) : ℤ) := by rw [head_eq_nat]
    _ = 45 * (3 : ℤ) ^ offset - 1 := by
      rw [Nat.cast_sub head_rhs]
      norm_num

private theorem deletionCRadius_two_add_cast (offset : Nat) :
    (deletionCRadius (2 + offset) : ℤ) = 9 * (3 : ℤ) ^ offset - 2 := by
  have power_pos : 0 < 3 ^ offset := pow_pos (by omega) _
  have radius_rhs : 2 ≤ 9 * 3 ^ offset := by nlinarith
  have radius_eq_nat : deletionCRadius (2 + offset) = 9 * 3 ^ offset - 2 := by
    simp [deletionCRadius, pow_add]
  calc
    (deletionCRadius (2 + offset) : ℤ) =
        ((9 * 3 ^ offset - 2 : Nat) : ℤ) := by rw [radius_eq_nat]
    _ = 9 * (3 : ℤ) ^ offset - 2 := by
      rw [Nat.cast_sub radius_rhs]
      norm_num

private theorem deletionCMarker_two_add_cast (offset : Nat) :
    (deletionCMarker (2 + offset) : ℤ) = 18 * (3 : ℤ) ^ offset - 1 := by
  have power_pos : 0 < 3 ^ offset := pow_pos (by omega) _
  have marker_rhs : 1 ≤ 18 * 3 ^ offset := by nlinarith
  have marker_eq_nat : deletionCMarker (2 + offset) = 18 * 3 ^ offset - 1 := by
    simp only [deletionCMarker, pow_add]
    congr 1
    ring
  calc
    (deletionCMarker (2 + offset) : ℤ) =
        ((18 * 3 ^ offset - 1 : Nat) : ℤ) := by rw [marker_eq_nat]
    _ = 18 * (3 : ℤ) ^ offset - 1 := by
      rw [Nat.cast_sub marker_rhs]
      norm_num

theorem deletionCHalfHead_coprime_radius
    {width : Nat} (width_two : 2 ≤ width) :
    (deletionCHalfHead width).Coprime (deletionCRadius width) := by
  obtain ⟨offset, width_eq⟩ := Nat.exists_eq_add_of_le width_two
  subst width
  apply natCoprime_of_isCoprime_int
  let power : ℤ := (3 : ℤ) ^ offset
  refine ⟨2 - 8 * power, 20 * power - 1, ?_⟩
  have head_eq :
      (2 : ℤ) * deletionCHalfHead (2 + offset) = 45 * power - 1 := by
    have head_eq_nat :
        2 * deletionCHalfHead (2 + offset) = 45 * 3 ^ offset - 1 := by
      rw [← deletionCHead_eq_twice_halfHead]
      simp only [deletionCHead, pow_add]
      congr 1
      ring
    have power_pos : 0 < 3 ^ offset := pow_pos (by omega) _
    have head_rhs_pos : 1 ≤ 45 * 3 ^ offset := by nlinarith
    calc
      (2 : ℤ) * deletionCHalfHead (2 + offset) =
          ((2 * deletionCHalfHead (2 + offset) : Nat) : ℤ) := by norm_num
      _ = ((45 * 3 ^ offset - 1 : Nat) : ℤ) := by rw [head_eq_nat]
      _ = 45 * power - 1 := by
        rw [Nat.cast_sub head_rhs_pos]
        norm_num [power]
  have radius_eq : (deletionCRadius (2 + offset) : ℤ) = 9 * power - 2 := by
    simpa only [power] using deletionCRadius_two_add_cast offset
  calc
    (2 - 8 * power) * deletionCHalfHead (2 + offset) +
        (20 * power - 1) * deletionCRadius (2 + offset) =
      (1 - 4 * power) * (2 * deletionCHalfHead (2 + offset)) +
        (20 * power - 1) * deletionCRadius (2 + offset) := by ring
    _ = (1 - 4 * power) * (45 * power - 1) +
        (20 * power - 1) * (9 * power - 2) := by rw [head_eq, radius_eq]
    _ = 1 := by ring

theorem deletionCRadius_coprime_three_mul_marker
    {width : Nat} (width_two : 2 ≤ width) :
    (deletionCRadius width).Coprime (3 * deletionCMarker width) := by
  obtain ⟨offset, width_eq⟩ := Nat.exists_eq_add_of_le width_two
  subst width
  apply natCoprime_of_isCoprime_int
  let power : ℤ := (3 : ℤ) ^ offset
  refine ⟨24 * power - 2, 1 - 4 * power, ?_⟩
  have radius_eq : (deletionCRadius (2 + offset) : ℤ) = 9 * power - 2 := by
    simpa only [power] using deletionCRadius_two_add_cast offset
  have marker_eq : (deletionCMarker (2 + offset) : ℤ) = 18 * power - 1 := by
    simpa only [power] using deletionCMarker_two_add_cast offset
  rw [radius_eq]
  push_cast
  rw [marker_eq]
  ring

theorem deletionCMarker_coprime_head
    {width : Nat} (width_two : 2 ≤ width) :
    (deletionCMarker width).Coprime (deletionCHead width) := by
  obtain ⟨offset, width_eq⟩ := Nat.exists_eq_add_of_le width_two
  subst width
  apply natCoprime_of_isCoprime_int
  let power : ℤ := (3 : ℤ) ^ offset
  refine ⟨60 * power - 3, 2 - 24 * power, ?_⟩
  have marker_eq : (deletionCMarker (2 + offset) : ℤ) = 18 * power - 1 := by
    simpa only [power] using deletionCMarker_two_add_cast offset
  have head_eq : (deletionCHead (2 + offset) : ℤ) = 45 * power - 1 := by
    simpa only [power] using deletionCHead_two_add_cast offset
  rw [marker_eq, head_eq]
  ring

theorem deletionCHalfHead_coprime_three
    {width : Nat} (width_two : 2 ≤ width) :
    (deletionCHalfHead width).Coprime 3 := by
  obtain ⟨offset, width_eq⟩ := Nat.exists_eq_add_of_le width_two
  subst width
  apply natCoprime_of_isCoprime_int
  let power : ℤ := (3 : ℤ) ^ offset
  refine ⟨-2, 15 * power, ?_⟩
  have head_eq :
      (2 : ℤ) * deletionCHalfHead (2 + offset) = 45 * power - 1 := by
    have doubled := deletionCHead_eq_twice_halfHead (2 + offset)
    have head_cast := deletionCHead_two_add_cast offset
    have doubled_int : (deletionCHead (2 + offset) : ℤ) =
        2 * deletionCHalfHead (2 + offset) := by exact_mod_cast doubled
    rw [doubled_int] at head_cast
    exact head_cast
  rw [show (-2 : ℤ) * deletionCHalfHead (2 + offset) =
      -(2 * deletionCHalfHead (2 + offset)) by ring, head_eq]
  ring

theorem deletionCRadius_coprime_two
    {width : Nat} (width_two : 2 ≤ width) :
    (deletionCRadius width).Coprime 2 := by
  obtain ⟨offset, width_eq⟩ := Nat.exists_eq_add_of_le width_two
  subst width
  obtain ⟨half, power_eq⟩ := width_power_odd offset
  apply natCoprime_of_isCoprime_int
  refine ⟨1, -(9 * (half : ℤ) + 3), ?_⟩
  have power_eq_int : (3 : ℤ) ^ offset = 2 * half + 1 := by
    exact_mod_cast power_eq
  have radius_eq : (deletionCRadius (2 + offset) : ℤ) =
      18 * half + 7 := by
    rw [deletionCRadius_two_add_cast, power_eq_int]
    ring
  rw [radius_eq]
  ring

theorem deletionC_threeMarker_gcd_sixHalfHead
    {width : Nat} (width_two : 2 ≤ width) :
    Nat.gcd (3 * deletionCMarker width) (6 * deletionCHalfHead width) = 3 := by
  have marker_head := deletionCMarker_coprime_head width_two
  have head_eq := deletionCHead_eq_twice_halfHead width
  have marker_twice_half :
      (deletionCMarker width).Coprime (2 * deletionCHalfHead width) := by
    simpa only [← head_eq] using marker_head
  rw [show 6 * deletionCHalfHead width =
    3 * (2 * deletionCHalfHead width) by ring]
  rw [Nat.gcd_mul_left]
  rw [Nat.coprime_iff_gcd_eq_one.mp marker_twice_half]

private theorem deletionCRadius_coprime_six_mul_halfHead
    {width : Nat} (width_two : 2 ≤ width) :
    (deletionCRadius width).Coprime (6 * deletionCHalfHead width) := by
  have radius_threeMarker := deletionCRadius_coprime_three_mul_marker width_two
  have radius_three : (deletionCRadius width).Coprime 3 :=
    Nat.Coprime.of_dvd (dvd_refl _) (dvd_mul_right 3 (deletionCMarker width))
      radius_threeMarker
  have radius_two := deletionCRadius_coprime_two width_two
  have radius_half := (deletionCHalfHead_coprime_radius width_two).symm
  have radius_six : (deletionCRadius width).Coprime 6 := by
    simpa only [show 6 = 2 * 3 by norm_num] using radius_two.mul_right radius_three
  simpa only [mul_assoc] using radius_six.mul_right radius_half

theorem deletionC_gcd_eq_three_mul_head
    {width numerator denominator : Nat} (width_two : 2 ≤ width)
    (denominator_lt_numerator : denominator < numerator)
    (primitive : numerator.Coprime denominator)
    (halfHead_dvd : deletionCHalfHead width ∣ numerator)
    (radius_coprime : (deletionCRadius width).Coprime denominator)
    (gap_channel :
      Nat.gcd (numerator - denominator) (3 * deletionCMarker width) = 3) :
    Nat.gcd (deletionCRawNumerator width numerator denominator)
        (deletionCRawDenominator width numerator denominator) =
      3 * deletionCHead width := by
  let halfHead := deletionCHalfHead width
  let radius := deletionCRadius width
  let marker := deletionCMarker width
  let gap := numerator - denominator
  obtain ⟨quotient, numerator_eq⟩ := halfHead_dvd
  have denominator_le : denominator ≤ numerator := denominator_lt_numerator.le
  have gap_add_denominator : gap + denominator = numerator := by
    exact Nat.sub_add_cancel denominator_le
  have gap_coprime_denominator : gap.Coprime denominator := by
    apply (Nat.coprime_sub_self_left denominator_le).mpr
    exact primitive
  have head_eq : deletionCHead width = 2 * halfHead := by
    exact deletionCHead_eq_twice_halfHead width
  have coefficient_sum : 2 * halfHead + radius = 3 * marker := by
    simpa only [← head_eq, halfHead, radius, marker] using
      deletionCHead_add_radius (show 0 < width by omega)
  let affine := radius * quotient + 2 * denominator
  have raw_numerator_eq :
      deletionCRawNumerator width numerator denominator =
        2 * halfHead * (radius * gap) := by
    simp only [deletionCRawNumerator, head_eq, halfHead, radius, gap]
    ring
  have raw_denominator_eq :
      deletionCRawDenominator width numerator denominator = 2 * halfHead * affine := by
    simp only [deletionCRawDenominator, head_eq, halfHead, radius, affine]
    rw [numerator_eq]
    ring
  have affine_identity :
      halfHead * affine = radius * gap + 3 * marker * denominator := by
    calc
      halfHead * affine = radius * (halfHead * quotient) +
          2 * halfHead * denominator := by simp [affine]; ring
      _ = radius * numerator + 2 * halfHead * denominator := by rw [numerator_eq]
      _ = radius * (gap + denominator) + 2 * halfHead * denominator := by
        rw [gap_add_denominator]
      _ = radius * gap + (2 * halfHead + radius) * denominator := by ring
      _ = radius * gap + 3 * marker * denominator := by rw [coefficient_sum]
  let common := Nat.gcd (radius * gap) affine
  have common_dvd_radius_gap : common ∣ radius * gap := Nat.gcd_dvd_left _ _
  have common_dvd_affine : common ∣ affine := Nat.gcd_dvd_right _ _
  have common_dvd_scaled_affine : common ∣ halfHead * affine :=
    dvd_mul_of_dvd_right common_dvd_affine _
  have common_dvd_marker_denominator : common ∣ 3 * marker * denominator := by
    have common_dvd_sum : common ∣ radius * gap + 3 * marker * denominator := by
      rwa [← affine_identity]
    exact (Nat.dvd_add_iff_left common_dvd_radius_gap).mpr <| by
      simpa [add_comm] using common_dvd_sum
  have radius_gap_coprime_denominator :
      (radius * gap).Coprime denominator :=
    radius_coprime.mul_left gap_coprime_denominator
  have common_coprime_denominator : common.Coprime denominator :=
    Nat.Coprime.of_dvd common_dvd_radius_gap (dvd_refl denominator)
      radius_gap_coprime_denominator
  have common_dvd_marker : common ∣ 3 * marker :=
    common_coprime_denominator.dvd_of_dvd_mul_right common_dvd_marker_denominator
  have radius_coprime_marker :=
    deletionCRadius_coprime_three_mul_marker width_two
  have common_coprime_radius : common.Coprime radius :=
    Nat.Coprime.of_dvd common_dvd_marker (dvd_refl radius)
      radius_coprime_marker.symm
  have common_dvd_gap : common ∣ gap :=
    common_coprime_radius.dvd_of_dvd_mul_left common_dvd_radius_gap
  have common_dvd_three : common ∣ 3 := by
    have common_dvd_channel := Nat.dvd_gcd common_dvd_gap common_dvd_marker
    rwa [gap_channel] at common_dvd_channel
  have three_dvd_gap : 3 ∣ gap := by
    rw [← gap_channel]
    exact Nat.gcd_dvd_left _ _
  have three_dvd_radius_gap : 3 ∣ radius * gap := dvd_mul_of_dvd_right three_dvd_gap _
  have three_dvd_marker_denominator : 3 ∣ 3 * marker * denominator := by
    rw [mul_assoc]
    exact dvd_mul_right 3 (marker * denominator)
  have three_dvd_scaled_affine : 3 ∣ halfHead * affine := by
    rw [affine_identity]
    exact dvd_add three_dvd_radius_gap three_dvd_marker_denominator
  have halfHead_coprime_three := deletionCHalfHead_coprime_three width_two
  have three_dvd_affine : 3 ∣ affine :=
    halfHead_coprime_three.symm.dvd_of_dvd_mul_left three_dvd_scaled_affine
  have three_dvd_common : 3 ∣ common :=
    Nat.dvd_gcd three_dvd_radius_gap three_dvd_affine
  have common_eq : common = 3 := dvd_antisymm common_dvd_three three_dvd_common
  rw [raw_numerator_eq, raw_denominator_eq, Nat.gcd_mul_left]
  change 2 * halfHead * common = 3 * deletionCHead width
  rw [common_eq, head_eq]
  ring

theorem deletionC_channel_of_gcd_eq_three_mul_head
    {width numerator denominator : Nat} (width_two : 2 ≤ width)
    (denominator_lt_numerator : denominator < numerator)
    (primitive : numerator.Coprime denominator)
    (common_eq :
      Nat.gcd (deletionCRawNumerator width numerator denominator)
          (deletionCRawDenominator width numerator denominator) =
        3 * deletionCHead width) :
    deletionCHalfHead width ∣ numerator ∧
      (deletionCRadius width).Coprime denominator ∧
      Nat.gcd (numerator - denominator) (3 * deletionCMarker width) = 3 := by
  let halfHead := deletionCHalfHead width
  let radius := deletionCRadius width
  let marker := deletionCMarker width
  let gap := numerator - denominator
  have denominator_le : denominator ≤ numerator := denominator_lt_numerator.le
  have gap_coprime_denominator : gap.Coprime denominator := by
    apply (Nat.coprime_sub_self_left denominator_le).mpr
    exact primitive
  have head_eq : deletionCHead width = 2 * halfHead :=
    deletionCHead_eq_twice_halfHead width
  have raw_numerator_eq :
      deletionCRawNumerator width numerator denominator =
        2 * halfHead * (radius * gap) := by
    simp only [deletionCRawNumerator, head_eq, halfHead, radius, gap]
    ring
  have raw_denominator_eq :
      deletionCRawDenominator width numerator denominator =
        2 * (radius * numerator + 2 * halfHead * denominator) := by
    simp only [deletionCRawDenominator, head_eq, halfHead, radius]
  have coefficient_sum : 2 * halfHead + radius = 3 * marker := by
    simpa only [← head_eq, halfHead, radius, marker] using
      deletionCHead_add_radius (show 0 < width by omega)
  have gap_add_denominator : gap + denominator = numerator :=
    Nat.sub_add_cancel denominator_le
  have raw_denominator_gap_eq :
      deletionCRawDenominator width numerator denominator =
        2 * (radius * gap + 3 * marker * denominator) := by
    rw [raw_denominator_eq, ← gap_add_denominator]
    calc
      2 * (radius * (gap + denominator) + 2 * halfHead * denominator) =
          2 * (radius * gap + (2 * halfHead + radius) * denominator) := by ring
      _ = 2 * (radius * gap + 3 * marker * denominator) := by rw [coefficient_sum]
  have common_eq' :
      Nat.gcd (deletionCRawNumerator width numerator denominator)
          (deletionCRawDenominator width numerator denominator) = 6 * halfHead := by
    rw [common_eq, head_eq]
    ring
  have common_dvd_raw_denominator :
      6 * halfHead ∣ deletionCRawDenominator width numerator denominator := by
    rw [← common_eq']
    exact Nat.gcd_dvd_right _ _
  have threeHalf_dvd_affine :
      3 * halfHead ∣ radius * numerator + 2 * halfHead * denominator := by
    rw [raw_denominator_eq] at common_dvd_raw_denominator
    have doubled :
        2 * (3 * halfHead) ∣
          2 * (radius * numerator + 2 * halfHead * denominator) := by
      rw [show 2 * (3 * halfHead) = 6 * halfHead by ring]
      exact common_dvd_raw_denominator
    exact Nat.dvd_of_mul_dvd_mul_left (by omega) doubled
  have halfHead_dvd_affine :
      halfHead ∣ radius * numerator + 2 * halfHead * denominator :=
    dvd_trans (dvd_mul_left halfHead 3) threeHalf_dvd_affine
  have halfHead_dvd_tail : halfHead ∣ 2 * halfHead * denominator := by
    exact ⟨2 * denominator, by ring⟩
  have halfHead_dvd_radius_numerator : halfHead ∣ radius * numerator :=
    (Nat.dvd_add_iff_left halfHead_dvd_tail).mpr halfHead_dvd_affine
  have halfHead_coprime_radius := deletionCHalfHead_coprime_radius width_two
  have halfHead_dvd_numerator : halfHead ∣ numerator :=
    halfHead_coprime_radius.dvd_of_dvd_mul_right <| by
      simpa [mul_comm] using halfHead_dvd_radius_numerator
  refine ⟨halfHead_dvd_numerator, ?_, ?_⟩
  · let radiusCommon := Nat.gcd radius denominator
    have radiusCommon_dvd_radius : radiusCommon ∣ radius := Nat.gcd_dvd_left _ _
    have radiusCommon_dvd_denominator : radiusCommon ∣ denominator :=
      Nat.gcd_dvd_right _ _
    have radiusCommon_dvd_raw_numerator :
        radiusCommon ∣ deletionCRawNumerator width numerator denominator := by
      rw [raw_numerator_eq]
      exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left radiusCommon_dvd_radius gap) _
    have radiusCommon_dvd_raw_denominator :
        radiusCommon ∣ deletionCRawDenominator width numerator denominator := by
      rw [raw_denominator_eq]
      apply dvd_mul_of_dvd_right
      exact dvd_add (dvd_mul_of_dvd_left radiusCommon_dvd_radius numerator)
        (dvd_mul_of_dvd_right radiusCommon_dvd_denominator (2 * halfHead))
    have radiusCommon_dvd_common : radiusCommon ∣ 6 * halfHead := by
      rw [← common_eq']
      exact Nat.dvd_gcd radiusCommon_dvd_raw_numerator radiusCommon_dvd_raw_denominator
    have radius_coprime_sixHalf :=
      deletionCRadius_coprime_six_mul_halfHead width_two
    have radiusCommon_coprime_sixHalf : radiusCommon.Coprime (6 * halfHead) :=
      Nat.Coprime.of_dvd radiusCommon_dvd_radius (dvd_refl _) radius_coprime_sixHalf
    have radiusCommon_eq : radiusCommon = 1 :=
      radiusCommon_coprime_sixHalf.eq_one_of_dvd radiusCommon_dvd_common
    exact Nat.coprime_iff_gcd_eq_one.mpr radiusCommon_eq
  · let gapCommon := Nat.gcd gap (3 * marker)
    have gapCommon_dvd_gap : gapCommon ∣ gap := Nat.gcd_dvd_left _ _
    have gapCommon_dvd_marker : gapCommon ∣ 3 * marker := Nat.gcd_dvd_right _ _
    have gapCommon_dvd_raw_numerator :
        gapCommon ∣ deletionCRawNumerator width numerator denominator := by
      rw [raw_numerator_eq]
      exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right gapCommon_dvd_gap radius) _
    have gapCommon_dvd_raw_denominator :
        gapCommon ∣ deletionCRawDenominator width numerator denominator := by
      rw [raw_denominator_gap_eq]
      apply dvd_mul_of_dvd_right
      apply dvd_add
      · simpa [mul_comm] using dvd_mul_of_dvd_left gapCommon_dvd_gap radius
      · simpa [mul_comm] using dvd_mul_of_dvd_right gapCommon_dvd_marker denominator
    have gapCommon_dvd_common : gapCommon ∣ 6 * halfHead := by
      rw [← common_eq']
      exact Nat.dvd_gcd gapCommon_dvd_raw_numerator gapCommon_dvd_raw_denominator
    have gapCommon_dvd_three : gapCommon ∣ 3 := by
      have gapCommon_dvd_gcd := Nat.dvd_gcd gapCommon_dvd_marker gapCommon_dvd_common
      rwa [deletionC_threeMarker_gcd_sixHalfHead width_two] at gapCommon_dvd_gcd
    have common_dvd_raw_numerator :
        6 * halfHead ∣ deletionCRawNumerator width numerator denominator := by
      rw [← common_eq']
      exact Nat.gcd_dvd_left _ _
    have three_dvd_radius_gap : 3 ∣ radius * gap := by
      rw [raw_numerator_eq] at common_dvd_raw_numerator
      have scaled : 2 * halfHead * 3 ∣ 2 * halfHead * (radius * gap) := by
        rw [show 2 * halfHead * 3 = 6 * halfHead by ring]
        exact common_dvd_raw_numerator
      exact Nat.dvd_of_mul_dvd_mul_left
        (mul_pos (by omega) (deletionCHalfHead_pos width)) scaled
    have radius_coprime_three : radius.Coprime 3 :=
      Nat.Coprime.of_dvd (dvd_refl radius) (dvd_mul_right 3 marker)
        (deletionCRadius_coprime_three_mul_marker width_two)
    have three_dvd_gap : 3 ∣ gap :=
      radius_coprime_three.symm.dvd_of_dvd_mul_left three_dvd_radius_gap
    have three_dvd_gapCommon : 3 ∣ gapCommon :=
      Nat.dvd_gcd three_dvd_gap (dvd_mul_right 3 marker)
    have gapCommon_eq : gapCommon = 3 :=
      dvd_antisymm gapCommon_dvd_three three_dvd_gapCommon
    exact gapCommon_eq

theorem deletionC_gcd_eq_three_mul_head_iff
    {width numerator denominator : Nat} (width_two : 2 ≤ width)
    (denominator_lt_numerator : denominator < numerator)
    (primitive : numerator.Coprime denominator) :
    Nat.gcd (deletionCRawNumerator width numerator denominator)
        (deletionCRawDenominator width numerator denominator) =
        3 * deletionCHead width ↔
      deletionCHalfHead width ∣ numerator ∧
        (deletionCRadius width).Coprime denominator ∧
        Nat.gcd (numerator - denominator) (3 * deletionCMarker width) = 3 := by
  constructor
  · exact deletionC_channel_of_gcd_eq_three_mul_head width_two
      denominator_lt_numerator primitive
  · rintro ⟨halfHead_dvd, radius_coprime, gap_channel⟩
    exact deletionC_gcd_eq_three_mul_head width_two denominator_lt_numerator primitive
      halfHead_dvd radius_coprime gap_channel

theorem deletionC_fareyHeight_contracts_iff
    {width numerator denominator : Nat} (width_two : 2 ≤ width)
    (denominator_lt_numerator : denominator < numerator)
    (common_eq :
      Nat.gcd (deletionCRawNumerator width numerator denominator)
          (deletionCRawDenominator width numerator denominator) =
        3 * deletionCHead width) :
    fareyHeight
          (deletionCRawNumerator width numerator denominator /
            Nat.gcd (deletionCRawNumerator width numerator denominator)
              (deletionCRawDenominator width numerator denominator))
          (deletionCRawDenominator width numerator denominator /
            Nat.gcd (deletionCRawNumerator width numerator denominator)
              (deletionCRawDenominator width numerator denominator)) <
        fareyHeight numerator denominator ↔
      deletionCRadius width * (numerator - denominator) < 3 * numerator := by
  let head := deletionCHead width
  let radius := deletionCRadius width
  let marker := deletionCMarker width
  let gap := numerator - denominator
  let common := Nat.gcd (deletionCRawNumerator width numerator denominator)
    (deletionCRawDenominator width numerator denominator)
  have numerator_pos : 0 < numerator := by omega
  have head_pos : 0 < head := by
    simpa only [head] using
      (show 0 < deletionCHead width by
        rw [deletionCHead_eq_twice_halfHead]
        exact mul_pos (by omega) (deletionCHalfHead_pos width))
  have common_eq_local : common = 3 * head := by
    simpa only [common, head] using common_eq
  have common_pos : 0 < common := by
    rw [common_eq_local]
    exact mul_pos (by omega) head_pos
  have coefficient_sum : head + radius = 3 * marker := by
    simpa only [head, radius, marker] using
      deletionCHead_add_radius (show 0 < width by omega)
  have marker_contraction : 2 * marker < head := by
    simpa only [head, marker] using deletionCMarker_lt_head width
  have raw_denominator_lt :
      deletionCRawDenominator width numerator denominator <
        numerator * (3 * head) := by
    have denominator_term_lt : head * denominator < head * numerator :=
      (Nat.mul_lt_mul_left head_pos).mpr denominator_lt_numerator
    calc
      deletionCRawDenominator width numerator denominator =
          2 * (radius * numerator + head * denominator) := by
        rfl
      _ < 2 * (radius * numerator + head * numerator) := by omega
      _ = 2 * (head + radius) * numerator := by ring
      _ = 6 * marker * numerator := by rw [coefficient_sum]; ring
      _ < 3 * head * numerator := by
        have scaled := (Nat.mul_lt_mul_right numerator_pos).mpr marker_contraction
        nlinarith
      _ = numerator * (3 * head) := by ring
  have normalized_denominator_lt :
      deletionCRawDenominator width numerator denominator / common < numerator := by
    rw [Nat.div_lt_iff_lt_mul common_pos, common_eq_local]
    exact raw_denominator_lt
  have normalized_numerator_iff :
      deletionCRawNumerator width numerator denominator / common < numerator ↔
        radius * gap < 3 * numerator := by
    rw [Nat.div_lt_iff_lt_mul common_pos, common_eq_local]
    change head * radius * gap < numerator * (3 * head) ↔ _
    rw [show head * radius * gap = head * (radius * gap) by ring,
      show numerator * (3 * head) = head * (3 * numerator) by ring,
      Nat.mul_lt_mul_left head_pos]
  change fareyHeight
      (deletionCRawNumerator width numerator denominator / common)
      (deletionCRawDenominator width numerator denominator / common) <
      fareyHeight numerator denominator ↔ radius * gap < 3 * numerator
  rw [fareyHeight_eq_max, fareyHeight_eq_max,
    max_eq_left denominator_lt_numerator.le, max_lt_iff]
  constructor
  · exact fun contracted => normalized_numerator_iff.mp contracted.1
  · intro gap_small
    exact ⟨normalized_numerator_iff.mpr gap_small, normalized_denominator_lt⟩

theorem deletionC_fareyHeight_contracts_iff_channel
    {width numerator denominator : Nat} (width_two : 2 ≤ width)
    (denominator_lt_numerator : denominator < numerator)
    (primitive : numerator.Coprime denominator)
    (halfHead_dvd : deletionCHalfHead width ∣ numerator)
    (radius_coprime : (deletionCRadius width).Coprime denominator)
    (gap_channel :
      Nat.gcd (numerator - denominator) (3 * deletionCMarker width) = 3) :
    fareyHeight
          (deletionCRawNumerator width numerator denominator /
            Nat.gcd (deletionCRawNumerator width numerator denominator)
              (deletionCRawDenominator width numerator denominator))
          (deletionCRawDenominator width numerator denominator /
            Nat.gcd (deletionCRawNumerator width numerator denominator)
              (deletionCRawDenominator width numerator denominator)) <
        fareyHeight numerator denominator ↔
      deletionCRadius width * (numerator - denominator) < 3 * numerator := by
  have common_eq := deletionC_gcd_eq_three_mul_head width_two denominator_lt_numerator
    primitive halfHead_dvd radius_coprime gap_channel
  exact deletionC_fareyHeight_contracts_iff width_two denominator_lt_numerator common_eq

theorem deletionC_denominator_ratio
    {width numerator denominator : Nat} (width_two : 2 ≤ width)
    (denominator_lt_numerator : denominator < numerator) :
    (deletionCRawDenominator width numerator denominator : ℚ) /
          (3 * deletionCHead width * numerator : Nat) =
        deletionCContractionFactor width -
          (2 * (numerator - denominator) : Nat) / (3 * numerator : Nat) := by
  let head := deletionCHead width
  let radius := deletionCRadius width
  let marker := deletionCMarker width
  let gap := numerator - denominator
  have denominator_le : denominator ≤ numerator := denominator_lt_numerator.le
  have numerator_pos : 0 < numerator := by omega
  have head_pos : 0 < head := by
    simpa only [head] using
      (show 0 < deletionCHead width by
        rw [deletionCHead_eq_twice_halfHead]
        exact mul_pos (by omega) (deletionCHalfHead_pos width))
  have head_ne_rat : (deletionCHead width : ℚ) ≠ 0 := by
    exact_mod_cast (show deletionCHead width ≠ 0 by
      simpa only [head] using ne_of_gt head_pos)
  have coefficient_sum : head + radius = 3 * marker := by
    simpa only [head, radius, marker] using
      deletionCHead_add_radius (show 0 < width by omega)
  have gap_add_denominator : gap + denominator = numerator :=
    Nat.sub_add_cancel denominator_le
  have raw_denominator_eq :
      deletionCRawDenominator width numerator denominator =
        2 * (radius * gap + 3 * marker * denominator) := by
    change 2 * (radius * numerator + head * denominator) = _
    rw [← gap_add_denominator]
    calc
      2 * (radius * (gap + denominator) + head * denominator) =
          2 * (radius * gap + (head + radius) * denominator) := by ring
      _ = 2 * (radius * gap + 3 * marker * denominator) := by rw [coefficient_sum]
  have coefficient_sum_cast : (head : ℚ) + radius = 3 * marker := by
    exact_mod_cast coefficient_sum
  have gap_add_denominator_cast : (gap : ℚ) + denominator = numerator := by
    exact_mod_cast gap_add_denominator
  have raw_cast_identity :
      (deletionCRawDenominator width numerator denominator : ℚ) =
        6 * marker * numerator - 2 * head * gap := by
    rw [raw_denominator_eq]
    push_cast
    rw [← gap_add_denominator_cast]
    linear_combination 2 * (gap : ℚ) * coefficient_sum_cast
  rw [raw_cast_identity]
  simp only [deletionCContractionFactor, head, marker, gap]
  push_cast
  field_simp [head_ne_rat]
  ring

theorem deletionC_asymptoticFactor_eq (width : Nat) :
    deletionCContractionFactor width =
      4 / 5 - 6 / (5 * deletionCHead width) := by
  have head_pos : 0 < deletionCHead width := by
    rw [deletionCHead_eq_twice_halfHead]
    exact mul_pos (by omega) (deletionCHalfHead_pos width)
  have factor_identity :
      5 * (2 * deletionCMarker width) + 6 = 4 * deletionCHead width := by
    simp only [deletionCMarker, deletionCHead]
    have power_pos : 0 < 3 ^ width := pow_pos (by omega) _
    omega
  have factor_identity_cast :
      (5 : ℚ) * (2 * deletionCMarker width) + 6 = 4 * deletionCHead width := by
    exact_mod_cast factor_identity
  simp only [deletionCContractionFactor]
  push_cast
  field_simp
  linarith

theorem deletionC_asymptoticFactor_lt_four_fifths (width : Nat) :
    deletionCContractionFactor width < 4 / 5 := by
  rw [deletionC_asymptoticFactor_eq]
  have head_pos : (0 : ℚ) < deletionCHead width := by
    exact_mod_cast (show 0 < deletionCHead width by
      rw [deletionCHead_eq_twice_halfHead]
      exact mul_pos (by omega) (deletionCHalfHead_pos width))
  have correction_pos : (0 : ℚ) < 6 / (5 * deletionCHead width) := by positivity
  linarith

end MatrixMortality.SwappedSetterDeletionCContraction
