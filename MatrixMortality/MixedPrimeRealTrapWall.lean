import MatrixMortality.MixedPrimeRealTrapMantissa

/-!
# Finite nucleus of the mixed-prime secondary wall

A reduced five-adic-unit mantissa on the exact wall `v₂(b)=1` has the form `a/(2c)`
with `c` odd. If its lower predecessor normalizes to another such mantissa `a'/(2c')`,
then `c=3^k c'` for a bounded exponent. Every consecutive wall orbit from a fixed target
therefore lies in an explicit finite rectangle and is eventually periodic. The fixed family from
the centered-recurrence analysis is identified as singleton components of this finite graph.
-/

namespace MatrixMortality.MixedPrimeDebt

open PadicValuation

private local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
private local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Odd residual after the exact two-adic wall cancellation. -/
def lowerWallResidual (depth a c : ℕ) : ℕ :=
  (5 * a - 9 * c) / 2 ^ (depth - 2)

/-- Cancelling the exact wall power exposes a numerator with no remaining factor of two. -/
theorem lowerNormalizedMantissa_eq_secondaryWallResidual
    {depth a c : ℕ} (depth_lower : 3 ≤ depth) (positive : 18 * c < 10 * a)
    (wall_dvd : 2 ^ (depth - 2) ∣ 5 * a - 9 * c) :
    lowerNormalizedMantissa depth a (2 * c) =
      (3 ^ (depth - 3) * lowerWallResidual depth a c : ℕ) / (2 * c) := by
  have exponent : depth - 2 + 1 = depth - 1 := by omega
  rw [lowerNormalizedMantissa, lowerCenteredNumerator_eq_twice_center positive]
  simp only [lowerWallResidual]
  rw [← Nat.mul_div_cancel' wall_dvd]
  rw [← exponent, pow_add]
  norm_num
  field_simp

private theorem lowerWall_crossProduct
    {depth a c nextA nextC : ℕ}
    (depth_lower : 3 ≤ depth) (c_ne : c ≠ 0) (nextC_ne : nextC ≠ 0)
    (positive : 18 * c < 10 * a)
    (wall_dvd : 2 ^ (depth - 2) ∣ 5 * a - 9 * c)
    (next_eq : lowerNormalizedMantissa depth a (2 * c) =
      (nextA : ℚ) / (2 * nextC)) :
    (3 ^ (depth - 3) * lowerWallResidual depth a c) * nextC = nextA * c := by
  let residualNumerator := 3 ^ (depth - 3) * lowerWallResidual depth a c
  have cancelled := lowerNormalizedMantissa_eq_secondaryWallResidual
    depth_lower positive wall_dvd
  have fractions_eq :
      (residualNumerator : ℚ) / (2 * c) = (nextA : ℚ) / (2 * nextC) := by
    exact cancelled.symm.trans next_eq
  have left_denominator_ne : (2 : ℚ) * c ≠ 0 := by
    exact mul_ne_zero (by norm_num) (by exact_mod_cast c_ne)
  have right_denominator_ne : (2 : ℚ) * nextC ≠ 0 := by
    exact mul_ne_zero (by norm_num) (by exact_mod_cast nextC_ne)
  have cross_rat :=
    (div_eq_div_iff left_denominator_ne right_denominator_ne).mp fractions_eq
  have cross_nat : residualNumerator * (2 * nextC) = nextA * (2 * c) := by
    exact_mod_cast cross_rat
  change residualNumerator * nextC = nextA * c
  nlinarith

private theorem lowerWall_nextOddDenominator_dvd
    {depth a c nextA nextC : ℕ}
    (depth_lower : 3 ≤ depth) (c_ne : c ≠ 0) (nextC_ne : nextC ≠ 0)
    (positive : 18 * c < 10 * a)
    (wall_dvd : 2 ^ (depth - 2) ∣ 5 * a - 9 * c)
    (next_coprime : nextA.Coprime (2 * nextC))
    (next_eq : lowerNormalizedMantissa depth a (2 * c) =
      (nextA : ℚ) / (2 * nextC)) :
    nextC ∣ c := by
  have cross := lowerWall_crossProduct depth_lower c_ne nextC_ne positive wall_dvd next_eq
  have nextC_dvd_product : nextC ∣ nextA * c := by
    rw [← cross]
    exact dvd_mul_left nextC (3 ^ (depth - 3) * lowerWallResidual depth a c)
  have nextA_coprime_nextC : nextA.Coprime nextC :=
    next_coprime.of_dvd_right (dvd_mul_left nextC 2)
  exact nextA_coprime_nextC.symm.dvd_of_dvd_mul_left nextC_dvd_product

private theorem reducedExactlyOneDenominator_twoValue
    {a c : ℕ} (ab : a.Coprime (2 * c)) (c_odd : Odd c) :
    HasValue 2 ((a : ℚ) / (2 * c)) (-1) := by
  have two_dvd_b : 2 ∣ 2 * c := by simp
  have a_odd : Odd a := (ab.of_dvd_right two_dvd_b).odd_of_right
  have a_ne : a ≠ 0 := by
    rintro rfl
    simp at a_odd
  have a_unit : IsUnit 2 (a : ℚ) := by
    refine ⟨by exact_mod_cast a_ne, ?_⟩
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd a_odd.not_two_dvd_nat]
    norm_num
  have c_ne : c ≠ 0 := by
    rintro rfl
    simp at c_odd
  have denominator_ne : 2 * c ≠ 0 := mul_ne_zero (by norm_num) c_ne
  have denominator_value_nat : padicValNat 2 (2 * c) = 1 := by
    rw [padicValNat.mul (by norm_num : (2 : ℕ) ≠ 0) c_ne,
      padicValNat_self, padicValNat.eq_zero_of_not_dvd]
    exact Nat.prime_two.coprime_iff_not_dvd.mp c_odd.coprime_two_left
  have denominator_value : HasValue 2 ((2 * c : ℕ) : ℚ) 1 := by
    refine ⟨by exact_mod_cast denominator_ne, ?_⟩
    rw [padicValRat.of_nat, denominator_value_nat]
    norm_num
  simpa using div_hasValue a_unit denominator_value

/-- A transition between reduced secondary-wall coordinates fixes the source residual's exact
two-adic value. -/
theorem lowerWall_to_lowerWall_secondaryCenter_twoValue
    {depth a c nextA nextC : ℕ}
    (depth_lower : 3 ≤ depth) (ab : a.Coprime (2 * c)) (c_odd : Odd c)
    (positive : 18 * c < 10 * a)
    (next_coprime : nextA.Coprime (2 * nextC)) (nextC_odd : Odd nextC)
    (next_eq : lowerNormalizedMantissa depth a (2 * c) =
      (nextA : ℚ) / (2 * nextC)) :
    padicValNat 2 (5 * a - 9 * c) = depth - 2 := by
  have outgoing_value :=
    lowerNormalizedMantissa_twoValue_of_exactlyOne_denominator
      (depth := depth) ab c_odd positive
  have next_value := reducedExactlyOneDenominator_twoValue next_coprime nextC_odd
  rw [next_eq] at outgoing_value
  have valuation_eq :
      (padicValNat 2 (5 * a - 9 * c) : ℤ) - ((depth - 1 : ℕ) : ℤ) = -1 :=
    outgoing_value.2.symm.trans next_value.2
  have residual_ne : 5 * a - 9 * c ≠ 0 := by omega
  omega

private theorem lowerWall_to_lowerWall_wallDvd
    {depth a c nextA nextC : ℕ}
    (depth_lower : 3 ≤ depth) (ab : a.Coprime (2 * c)) (c_odd : Odd c)
    (positive : 18 * c < 10 * a)
    (next_coprime : nextA.Coprime (2 * nextC)) (nextC_odd : Odd nextC)
    (next_eq : lowerNormalizedMantissa depth a (2 * c) =
      (nextA : ℚ) / (2 * nextC)) :
    2 ^ (depth - 2) ∣ 5 * a - 9 * c := by
  have residual_ne : 5 * a - 9 * c ≠ 0 := by omega
  have residual_value := lowerWall_to_lowerWall_secondaryCenter_twoValue depth_lower ab c_odd
    positive next_coprime nextC_odd next_eq
  exact (padicValNat_dvd_iff_le (p := 2) (n := depth - 2) residual_ne).mpr (by
    rw [residual_value])

private theorem lowerWall_to_lowerWall_oddDenominator_dvd
    {depth a c nextA nextC : ℕ}
    (depth_lower : 3 ≤ depth) (ab : a.Coprime (2 * c)) (c_odd : Odd c)
    (positive : 18 * c < 10 * a)
    (next_coprime : nextA.Coprime (2 * nextC)) (nextC_odd : Odd nextC)
    (next_eq : lowerNormalizedMantissa depth a (2 * c) =
      (nextA : ℚ) / (2 * nextC)) :
    nextC ∣ c := by
  have wall_dvd := lowerWall_to_lowerWall_wallDvd depth_lower ab c_odd positive
    next_coprime nextC_odd next_eq
  have c_ne : c ≠ 0 := by
    rintro rfl
    simp at c_odd
  have nextC_ne : nextC ≠ 0 := by
    rintro rfl
    simp at nextC_odd
  exact lowerWall_nextOddDenominator_dvd depth_lower c_ne nextC_ne positive wall_dvd
    next_coprime next_eq

private theorem lowerWallResidual_coprime
    {depth a c : ℕ} (ab : a.Coprime (2 * c)) (five_c : Nat.Coprime 5 c)
    (positive : 18 * c < 10 * a)
    (wall_dvd : 2 ^ (depth - 2) ∣ 5 * a - 9 * c) :
    (lowerWallResidual depth a c).Coprime c := by
  have a_coprime_c : a.Coprime c :=
    ab.of_dvd_right (dvd_mul_left c 2)
  have fiveA_coprime_c : (5 * a).Coprime c := five_c.mul_left a_coprime_c
  have decomposition : (5 * a - 9 * c) + 9 * c = 5 * a := by omega
  have residual_coprime_c : (5 * a - 9 * c).Coprime c := by
    apply (Nat.add_coprime_iff_left (dvd_mul_left c 9)).mp
    rw [decomposition]
    exact fiveA_coprime_c
  exact residual_coprime_c.of_dvd_left (Nat.div_dvd_of_dvd wall_dvd)

/-- A lower-wall transition to another reduced lower-wall coordinate can remove only a bounded
power of three from the odd half-denominator. -/
theorem lowerWall_to_lowerWall_oddDenominator_eq_threePow_mul
    {depth a c nextA nextC : ℕ}
    (depth_lower : 3 ≤ depth) (ab : a.Coprime (2 * c)) (c_odd : Odd c)
    (five_c : Nat.Coprime 5 c) (positive : 18 * c < 10 * a)
    (next_coprime : nextA.Coprime (2 * nextC)) (nextC_odd : Odd nextC)
    (next_eq : lowerNormalizedMantissa depth a (2 * c) =
      (nextA : ℚ) / (2 * nextC)) :
    ∃ exponent ≤ depth - 3, c = 3 ^ exponent * nextC := by
  have wall_dvd := lowerWall_to_lowerWall_wallDvd depth_lower ab c_odd positive
    next_coprime nextC_odd next_eq
  have c_ne : c ≠ 0 := by
    rintro rfl
    simp at c_odd
  have nextC_ne : nextC ≠ 0 := by
    rintro rfl
    simp at nextC_odd
  have cross := lowerWall_crossProduct depth_lower c_ne nextC_ne positive wall_dvd next_eq
  have residual_coprime_c := lowerWallResidual_coprime ab five_c positive wall_dvd
  have c_dvd_raw :
      c ∣ (3 ^ (depth - 3) * lowerWallResidual depth a c) * nextC := by
    rw [cross]
    exact dvd_mul_left c nextA
  have c_dvd_reordered :
      c ∣ lowerWallResidual depth a c * (3 ^ (depth - 3) * nextC) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using c_dvd_raw
  have c_dvd_three_nextC : c ∣ 3 ^ (depth - 3) * nextC :=
    residual_coprime_c.symm.dvd_of_dvd_mul_left c_dvd_reordered
  have nextC_dvd := lowerWall_to_lowerWall_oddDenominator_dvd depth_lower ab c_odd
    positive next_coprime nextC_odd next_eq
  have quotient_dvd : c / nextC ∣ 3 ^ (depth - 3) :=
    (Nat.div_dvd_iff_dvd_mul nextC_dvd (Nat.pos_of_ne_zero nextC_ne)).mpr (by
      simpa [mul_comm] using c_dvd_three_nextC)
  obtain ⟨exponent, exponent_le, quotient_eq⟩ :=
    (Nat.dvd_prime_pow Nat.prime_three).mp quotient_dvd
  refine ⟨exponent, exponent_le, ?_⟩
  calc
    c = (c / nextC) * nextC := (Nat.div_mul_cancel nextC_dvd).symm
    _ = 3 ^ exponent * nextC := by rw [quotient_eq]

/-- Finite target-dependent rectangle containing every reduced lower-wall successor pair. -/
def lowerWallCandidatePairs (c : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (2 * c + 1)).product (Finset.range (c + 1))

/-- Every normalized reduced lower-wall successor lies in an explicit finite set determined by
the current odd half-denominator. -/
private theorem lowerWall_to_lowerWall_reducedPair_mem_candidates
    {depth a c nextA nextC : ℕ}
    (depth_lower : 3 ≤ depth) (ab : a.Coprime (2 * c)) (c_odd : Odd c)
    (positive : 18 * c < 10 * a)
    (next_coprime : nextA.Coprime (2 * nextC)) (nextC_odd : Odd nextC)
    (next_eq : lowerNormalizedMantissa depth a (2 * c) =
      (nextA : ℚ) / (2 * nextC))
    (next_upper : (nextA : ℚ) / (2 * nextC) ≤ 1) :
    (nextA, nextC) ∈ lowerWallCandidatePairs c := by
  have nextC_dvd := lowerWall_to_lowerWall_oddDenominator_dvd depth_lower ab c_odd
    positive next_coprime nextC_odd next_eq
  have nextC_le : nextC ≤ c := Nat.le_of_dvd (by
    obtain ⟨half, rfl⟩ := c_odd
    omega) nextC_dvd
  have next_denominator_positive : (0 : ℚ) < 2 * nextC := by
    obtain ⟨half, rfl⟩ := nextC_odd
    positivity
  have nextA_le_nextDenominator : nextA ≤ 2 * nextC := by
    have rational_bound : (nextA : ℚ) ≤ 2 * nextC :=
      (div_le_one next_denominator_positive).mp next_upper
    exact_mod_cast rational_bound
  have nextA_le : nextA ≤ 2 * c :=
    nextA_le_nextDenominator.trans (Nat.mul_le_mul_left 2 nextC_le)
  unfold lowerWallCandidatePairs
  apply Finset.mem_product.mpr
  exact ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩

/-- Reduced five-adic-unit normalized mantissa on the active secondary wall and above the lower
predecessor threshold. -/
structure IsLowerWallMantissa (a c : ℕ) : Prop where
  reduced : a.Coprime (2 * c)
  odd_denominator : Odd c
  five_coprime_numerator : Nat.Coprime 5 a
  five_coprime_denominator : Nat.Coprime 5 c
  lower : 18 * c < 10 * a
  upper : a ≤ 2 * c

/-- Rational value represented by one secondary-wall numerator and odd half-denominator. -/
def lowerWallValue (point : ℕ × ℕ) : ℚ :=
  (point.1 : ℚ) / (2 * point.2)

/-- One consecutive lower-branch transition whose source and normalized successor both remain
on the reduced five-adic-unit secondary wall. -/
def LowerWallTransition (current next : ℕ × ℕ) : Prop :=
  IsLowerWallMantissa current.1 current.2 ∧
    IsLowerWallMantissa next.1 next.2 ∧
      ∃ depth, 3 ≤ depth ∧
        lowerNormalizedMantissa depth current.1 (2 * current.2) = lowerWallValue next

/-- The unique depth at which a secondary-wall source can return to the secondary wall. -/
def lowerWallCanonicalDepth (current : ℕ × ℕ) : ℕ :=
  padicValNat 2 (5 * current.1 - 9 * current.2) + 2

private theorem IsLowerWallMantissa.denominator_ne
    {a c : ℕ} (wall : IsLowerWallMantissa a c) : c ≠ 0 := by
  rintro rfl
  have odd := wall.odd_denominator
  simp at odd

/-- A valid lower-wall mantissa lies in `(9/10,1]`. -/
theorem IsLowerWallMantissa.value_normalized
    {a c : ℕ} (wall : IsLowerWallMantissa a c) :
    9 / 10 < lowerWallValue (a, c) ∧ lowerWallValue (a, c) ≤ 1 := by
  have denominator_positive : (0 : ℚ) < 2 * c := by
    exact_mod_cast mul_pos (by norm_num : 0 < (2 : ℕ)) (Nat.pos_of_ne_zero wall.denominator_ne)
  constructor
  · rw [lowerWallValue, lt_div_iff₀ denominator_positive]
    have lower_rat : (18 * c : ℚ) < 10 * a := by exact_mod_cast wall.lower
    nlinarith
  · rw [lowerWallValue, div_le_one denominator_positive]
    exact_mod_cast wall.upper

private theorem IsLowerWallMantissa.value_fiveUnit
    {a c : ℕ} (wall : IsLowerWallMantissa a c) :
    IsUnit 5 (lowerWallValue (a, c)) := by
  have numerator_not_dvd_nat : ¬5 ∣ a :=
    Nat.prime_five.coprime_iff_not_dvd.mp wall.five_coprime_numerator
  have numerator_not_dvd_int : ¬(5 : ℤ) ∣ (a : ℤ) := by
    exact_mod_cast numerator_not_dvd_nat
  have numerator_unit : IsUnit 5 (a : ℚ) := by
    simpa using intCast_isUnit_of_not_dvd (prime := 5) numerator_not_dvd_int
  have denominator_not_dvd_nat : ¬5 ∣ c :=
    Nat.prime_five.coprime_iff_not_dvd.mp wall.five_coprime_denominator
  have denominator_not_dvd_int : ¬(5 : ℤ) ∣ (c : ℤ) := by
    exact_mod_cast denominator_not_dvd_nat
  have two_unit : IsUnit 5 (2 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have c_unit : IsUnit 5 (c : ℚ) := by
    simpa using intCast_isUnit_of_not_dvd (prime := 5) denominator_not_dvd_int
  exact div_hasValue numerator_unit (mul_hasValue two_unit c_unit)

private theorem lowerWallPair_eq_of_value_eq
    {left right : ℕ × ℕ}
    (left_wall : IsLowerWallMantissa left.1 left.2)
    (right_wall : IsLowerWallMantissa right.1 right.2)
    (value_eq : lowerWallValue left = lowerWallValue right) :
    left = right := by
  have left_denominator_ne : (2 : ℚ) * left.2 ≠ 0 := by
    exact mul_ne_zero (by norm_num) (by exact_mod_cast left_wall.denominator_ne)
  have right_denominator_ne : (2 : ℚ) * right.2 ≠ 0 := by
    exact mul_ne_zero (by norm_num) (by exact_mod_cast right_wall.denominator_ne)
  have fractions_eq :
      (left.1 : ℚ) / (2 * left.2) = (right.1 : ℚ) / (2 * right.2) := by
    simpa only [lowerWallValue] using value_eq
  have cross_rat :=
    (div_eq_div_iff left_denominator_ne right_denominator_ne).mp fractions_eq
  have cross_twice : left.1 * (2 * right.2) = right.1 * (2 * left.2) := by
    exact_mod_cast cross_rat
  have cross : left.1 * right.2 = right.1 * left.2 := by
    nlinarith
  have left_numerator_coprime_denominator : left.1.Coprime left.2 :=
    left_wall.reduced.of_dvd_right (dvd_mul_left left.2 2)
  have right_numerator_coprime_denominator : right.1.Coprime right.2 :=
    right_wall.reduced.of_dvd_right (dvd_mul_left right.2 2)
  have left_dvd_right : left.2 ∣ right.2 := by
    apply left_numerator_coprime_denominator.symm.dvd_of_dvd_mul_left
    rw [cross]
    exact dvd_mul_left left.2 right.1
  have right_dvd_left : right.2 ∣ left.2 := by
    apply right_numerator_coprime_denominator.symm.dvd_of_dvd_mul_left
    rw [← cross]
    exact dvd_mul_left right.2 left.1
  have denominator_eq : left.2 = right.2 := Nat.dvd_antisymm left_dvd_right right_dvd_left
  have numerator_eq : left.1 = right.1 := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero right_wall.denominator_ne)
    simpa only [denominator_eq] using cross
  exact Prod.ext numerator_eq denominator_eq

private theorem lowerWallTransition_state_eq
    {current next : ℕ × ℕ} (current_wall : IsLowerWallMantissa current.1 current.2)
    {depth : ℕ} (depth_lower : 3 ≤ depth)
    (next_eq : lowerNormalizedMantissa depth current.1 (2 * current.2) =
      lowerWallValue next) :
    realTrapBandPoint depth (lowerWallValue next) = 2 * lowerWallValue current / 9 := by
  have current_denominator_ne : 2 * current.2 ≠ 0 :=
    mul_ne_zero (by norm_num) current_wall.denominator_ne
  have current_positive := current_wall.lower
  have state_eq := realTrapBandPoint_lowerNormalizedMantissa
    depth_lower current_denominator_ne (by omega : 9 * (2 * current.2) ≤ 10 * current.1)
  rw [next_eq] at state_eq
  simpa [lowerWallValue] using state_eq

/-- Every transition strips a bounded power of three from the odd half-denominator. -/
theorem LowerWallTransition.oddDenominator_eq_threePow_mul
    {current next : ℕ × ℕ} (transition : LowerWallTransition current next) :
    ∃ depth exponent, 3 ≤ depth ∧ exponent ≤ depth - 3 ∧
      current.2 = 3 ^ exponent * next.2 := by
  obtain ⟨depth, depth_lower, next_eq⟩ := transition.2.2
  obtain ⟨exponent, exponent_le, denominator_eq⟩ :=
    lowerWall_to_lowerWall_oddDenominator_eq_threePow_mul depth_lower
      transition.1.reduced transition.1.odd_denominator
      transition.1.five_coprime_denominator transition.1.lower
      transition.2.1.reduced transition.2.1.odd_denominator next_eq
  exact ⟨depth, exponent, depth_lower, exponent_le, denominator_eq⟩

/-- Every successor coordinate lies in the finite rectangle determined by its source. -/
theorem LowerWallTransition.next_mem_candidates
    {current next : ℕ × ℕ} (transition : LowerWallTransition current next) :
    next ∈ lowerWallCandidatePairs current.2 := by
  obtain ⟨depth, depth_lower, next_eq⟩ := transition.2.2
  have next_upper := transition.2.1.value_normalized.2
  exact lowerWall_to_lowerWall_reducedPair_mem_candidates depth_lower
    transition.1.reduced transition.1.odd_denominator transition.1.lower
    transition.2.1.reduced transition.2.1.odd_denominator next_eq next_upper

/-- Product of the target-dependent wall rectangle with the twelve canonical real-trap depth
classes. -/
def lowerWallDepthCandidates (c : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  (lowerWallCandidatePairs c).product (Finset.range 12)

/-- Each lower-wall transition has a checked twelve-class depth label paired with its finite
target-dependent successor coordinate. -/
theorem LowerWallTransition.exists_depthRepresentative_mem_candidates
    {current next : ℕ × ℕ} (transition : LowerWallTransition current next) :
    ∃ depth, 3 ≤ depth ∧
      lowerNormalizedMantissa depth current.1 (2 * current.2) = lowerWallValue next ∧
      (next, realTrapDepthRepresentative depth) ∈ lowerWallDepthCandidates current.2 := by
  obtain ⟨depth, depth_lower, next_eq⟩ := transition.2.2
  have representative_bounds := realTrapDepthRepresentative_bounds depth
  refine ⟨depth, depth_lower, next_eq, ?_⟩
  unfold lowerWallDepthCandidates
  apply Finset.mem_product.mpr
  exact ⟨transition.next_mem_candidates, Finset.mem_range.mpr (by omega)⟩

/-- The real-trap state represented by the successor coordinate remains inside the five-adic
shell guard. -/
theorem LowerWallTransition.nextState_fiveUnit
    {current next : ℕ × ℕ} (transition : LowerWallTransition current next) :
    ∃ depth, 3 ≤ depth ∧ IsUnit 5 (realTrapBandPoint depth (lowerWallValue next)) := by
  obtain ⟨depth, depth_lower, next_eq⟩ := transition.2.2
  have state_eq := lowerWallTransition_state_eq transition.1 depth_lower next_eq
  have two_unit : IsUnit 5 (2 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have nine_unit : IsUnit 5 (9 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have state_unit : IsUnit 5 (realTrapBandPoint depth (lowerWallValue next)) := by
    rw [state_eq]
    simpa [lowerWallValue] using
      div_hasValue (mul_hasValue two_unit transition.1.value_fiveUnit) nine_unit
  exact ⟨depth, depth_lower, state_unit⟩

/-- Any witness depth for a lower-wall transition equals the source's computable canonical
depth. -/
theorem LowerWallTransition.depth_eq_canonical
    {current next : ℕ × ℕ} (transition : LowerWallTransition current next)
    {depth : ℕ} (depth_lower : 3 ≤ depth)
    (next_eq : lowerNormalizedMantissa depth current.1 (2 * current.2) =
      lowerWallValue next) :
    depth = lowerWallCanonicalDepth current := by
  have residual_value := lowerWall_to_lowerWall_secondaryCenter_twoValue depth_lower
    transition.1.reduced transition.1.odd_denominator transition.1.lower
    transition.2.1.reduced transition.2.1.odd_denominator (by
      simpa only [lowerWallValue] using next_eq)
  unfold lowerWallCanonicalDepth
  omega

/-- The existential transition relation is equivalent to one check at the source's canonical
depth. -/
theorem lowerWallTransition_iff_canonicalDepth
    {current next : ℕ × ℕ} :
    LowerWallTransition current next ↔
      IsLowerWallMantissa current.1 current.2 ∧
        IsLowerWallMantissa next.1 next.2 ∧
          3 ≤ lowerWallCanonicalDepth current ∧
            lowerNormalizedMantissa (lowerWallCanonicalDepth current)
                current.1 (2 * current.2) =
              lowerWallValue next := by
  constructor
  · intro transition
    obtain ⟨depth, depth_lower, next_eq⟩ := transition.2.2
    have depth_eq := transition.depth_eq_canonical depth_lower next_eq
    subst depth
    exact ⟨transition.1, transition.2.1, depth_lower, next_eq⟩
  · rintro ⟨current_wall, next_wall, depth_lower, next_eq⟩
    exact ⟨current_wall, next_wall, lowerWallCanonicalDepth current, depth_lower, next_eq⟩

/-- The normalized lower-wall successor is unique. -/
theorem lowerWallTransition_next_unique
    {current left right : ℕ × ℕ}
    (left_transition : LowerWallTransition current left)
    (right_transition : LowerWallTransition current right) :
    left = right := by
  obtain ⟨leftDepth, leftDepth_lower, left_eq⟩ := left_transition.2.2
  obtain ⟨rightDepth, rightDepth_lower, right_eq⟩ := right_transition.2.2
  have left_state :=
    lowerWallTransition_state_eq left_transition.1 leftDepth_lower left_eq
  have right_state :=
    lowerWallTransition_state_eq right_transition.1 rightDepth_lower right_eq
  have states_eq := left_state.trans right_state.symm
  have left_bounds := left_transition.2.1.value_normalized
  have right_bounds := right_transition.2.1.value_normalized
  have left_mantissa_lower : 2 / 3 < lowerWallValue left := by
    linarith [left_bounds.1]
  have right_mantissa_lower : 2 / 3 < lowerWallValue right := by
    linarith [right_bounds.1]
  have depth_eq : leftDepth = rightDepth := by
    have max_eq := congrArg realTrapMaxPredecessorWait states_eq
    rw [realTrapMaxPredecessorWait_bandPoint leftDepth left_mantissa_lower left_bounds.2,
      realTrapMaxPredecessorWait_bandPoint rightDepth right_mantissa_lower right_bounds.2] at max_eq
    exact max_eq
  subst rightDepth
  have values_eq : lowerWallValue left = lowerWallValue right := left_eq.symm.trans right_eq
  exact lowerWallPair_eq_of_value_eq left_transition.2.1 right_transition.2.1 values_eq

/-- Every consecutive lower-wall orbit remains in the finite rectangle fixed by its initial odd
half-denominator. -/
theorem lowerWallOrbit_mem_candidates
    (orbit : ℕ → ℕ × ℕ)
    (step : ∀ index, LowerWallTransition (orbit index) (orbit (index + 1)))
    (index : ℕ) :
    orbit index ∈ lowerWallCandidatePairs (orbit 0).2 := by
  have denominator_dvd : ∀ position, (orbit position).2 ∣ (orbit 0).2 := by
    intro position
    induction position with
    | zero => exact dvd_refl _
    | succ position induction =>
        obtain ⟨_, exponent, _, _, denominator_eq⟩ :=
          (step position).oddDenominator_eq_threePow_mul
        have next_dvd_current : (orbit (position + 1)).2 ∣ (orbit position).2 :=
          ⟨3 ^ exponent, by simpa [mul_comm] using denominator_eq⟩
        exact next_dvd_current.trans induction
  have initial_wall := (step 0).1
  have denominator_le : (orbit index).2 ≤ (orbit 0).2 :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero initial_wall.denominator_ne) (denominator_dvd index)
  have current_wall := (step index).1
  have numerator_le : (orbit index).1 ≤ 2 * (orbit 0).2 :=
    current_wall.upper.trans (Nat.mul_le_mul_left 2 denominator_le)
  unfold lowerWallCandidatePairs
  apply Finset.mem_product.mpr
  exact ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩

private theorem lowerWallOrbit_periodic_of_repeat
    (orbit : ℕ → ℕ × ℕ)
    (step : ∀ index, LowerWallTransition (orbit index) (orbit (index + 1)))
    {left right : ℕ} (left_lt_right : left < right)
    (repeated : orbit left = orbit right) :
    ∃ start period, 0 < period ∧
      ∀ offset, orbit (start + offset) = orbit (start + period + offset) := by
  have repeated_shift : ∀ offset, orbit (left + offset) = orbit (right + offset) := by
    intro offset
    induction offset with
    | zero => simpa using repeated
    | succ offset induction =>
        have left_step := step (left + offset)
        have right_step := step (right + offset)
        rw [induction] at left_step
        have next_eq := lowerWallTransition_next_unique left_step right_step
        simpa only [Nat.add_assoc] using next_eq
  refine ⟨left, right - left, Nat.sub_pos_of_lt left_lt_right, ?_⟩
  intro offset
  have shifted := repeated_shift offset
  rw [show left + (right - left) + offset = right + offset by omega]
  exact shifted

/-- Every infinite consecutive lower-wall orbit is eventually periodic. -/
theorem lowerWallOrbit_eventually_periodic
    (orbit : ℕ → ℕ × ℕ)
    (step : ∀ index, LowerWallTransition (orbit index) (orbit (index + 1))) :
    ∃ start period, 0 < period ∧
      ∀ offset, orbit (start + offset) = orbit (start + period + offset) := by
  have orbit_mem := lowerWallOrbit_mem_candidates orbit step
  let trapped : ℕ → {point // point ∈ lowerWallCandidatePairs (orbit 0).2} :=
    fun index => ⟨orbit index, orbit_mem index⟩
  obtain ⟨left, right, distinct, repeated⟩ :=
    Finite.exists_ne_map_eq_of_infinite trapped
  have repeated_values : orbit left = orbit right := congrArg Subtype.val repeated
  rcases lt_or_gt_of_ne distinct with left_lt_right | right_lt_left
  · exact lowerWallOrbit_periodic_of_repeat orbit step left_lt_right repeated_values
  · exact lowerWallOrbit_periodic_of_repeat orbit step right_lt_left repeated_values.symm

/-- Secondary-wall coordinate pair of the explicit lower fixed point. -/
def lowerFixedWallPair (depth : ℕ) : ℕ × ℕ :=
  (lowerFixedNumerator depth, lowerFixedDenominator depth / 2)

private theorem lowerFixedDenominator_data
    {depth : ℕ} (depth_lower : 7 ≤ depth) :
    lowerFixedDenominator depth ≠ 0 ∧
      2 ∣ lowerFixedDenominator depth ∧
      2 * (lowerFixedDenominator depth / 2) = lowerFixedDenominator depth ∧
      Odd (lowerFixedDenominator depth / 2) := by
  have denominator_value := lowerFixed_denominator_twoValue depth_lower
  have denominator_ne : lowerFixedDenominator depth ≠ 0 := by
    intro denominator_zero
    rw [denominator_zero] at denominator_value
    simp at denominator_value
  have one_le : 1 ≤ padicValNat 2 (lowerFixedDenominator depth) := by omega
  have two_dvd : 2 ∣ lowerFixedDenominator depth :=
    (padicValNat_dvd_iff_le (p := 2) (n := 1) denominator_ne).mpr one_le
  have denominator_eq :
      2 * (lowerFixedDenominator depth / 2) = lowerFixedDenominator depth :=
    Nat.mul_div_cancel' two_dvd
  have half_not_even : ¬2 ∣ lowerFixedDenominator depth / 2 := by
    intro half_even
    have four_dvd : 2 ^ 2 ∣ lowerFixedDenominator depth := by
      rw [← denominator_eq, pow_two]
      exact Nat.mul_dvd_mul_left 2 half_even
    have two_le :=
      (padicValNat_dvd_iff_le (p := 2) (n := 2) denominator_ne).mp four_dvd
    omega
  have half_odd : Odd (lowerFixedDenominator depth / 2) :=
    Nat.prime_two.coprime_iff_not_dvd.mpr half_not_even |>.odd_of_left
  exact ⟨denominator_ne, two_dvd, denominator_eq, half_odd⟩

/-- The explicit fixed family occupies the reduced five-adic-unit secondary wall. -/
theorem lowerFixedWallPair_isLowerWallMantissa
    {depth : ℕ} (depth_lower : 7 ≤ depth) :
    IsLowerWallMantissa (lowerFixedWallPair depth).1 (lowerFixedWallPair depth).2 := by
  obtain ⟨_, two_dvd, denominator_eq, half_odd⟩ :=
    lowerFixedDenominator_data depth_lower
  have reduced : (lowerFixedNumerator depth).Coprime
      (2 * (lowerFixedDenominator depth / 2)) := by
    rw [denominator_eq]
    exact lowerFixed_coprime depth_lower
  have five_numerator : Nat.Coprime 5 (lowerFixedNumerator depth) := by
    simpa only [lowerFixedNumerator] using
      (by norm_num : Nat.Coprime 5 3).pow_right (depth - 1)
  have half_dvd : lowerFixedDenominator depth / 2 ∣ lowerFixedDenominator depth :=
    Nat.div_dvd_of_dvd two_dvd
  have five_half : Nat.Coprime 5 (lowerFixedDenominator depth / 2) :=
    (lowerFixed_five_coprime_denominator depth_lower).of_dvd_right half_dvd
  have normalized := lowerFixedMantissa_normalized depth_lower
  have half_ne : lowerFixedDenominator depth / 2 ≠ 0 := by
    intro half_zero
    have odd := half_odd
    rw [half_zero] at odd
    simp at odd
  have denominator_positive :
      (0 : ℚ) < (2 : ℚ) * ((lowerFixedDenominator depth / 2 : ℕ) : ℚ) := by
    exact_mod_cast mul_pos (by norm_num : 0 < (2 : ℕ)) (Nat.pos_of_ne_zero half_ne)
  have denominator_eq_rat :
      (2 : ℚ) * ((lowerFixedDenominator depth / 2 : ℕ) : ℚ) =
        lowerFixedDenominator depth := by
    exact_mod_cast denominator_eq
  have value_eq :
      (lowerFixedNumerator depth : ℚ) /
          ((2 : ℚ) * ((lowerFixedDenominator depth / 2 : ℕ) : ℚ)) =
        lowerFixedMantissa depth := by
    rw [denominator_eq_rat]
    rfl
  have lower_rat :
      ((18 * (lowerFixedDenominator depth / 2) : ℕ) : ℚ) <
        ((10 * lowerFixedNumerator depth : ℕ) : ℚ) := by
    rw [← value_eq] at normalized
    have divided_lower :=
      (lt_div_iff₀ denominator_positive).mp normalized.1
    norm_num at divided_lower ⊢
    nlinarith
  have upper_rat :
      (lowerFixedNumerator depth : ℚ) ≤
        ((2 * (lowerFixedDenominator depth / 2) : ℕ) : ℚ) := by
    rw [← value_eq] at normalized
    have divided_upper := (div_le_one denominator_positive).mp normalized.2
    norm_num at divided_upper ⊢
    exact divided_upper
  exact ⟨reduced, half_odd, five_numerator, five_half,
    by exact_mod_cast lower_rat, by exact_mod_cast upper_rat⟩

/-- Every explicit fixed coordinate has a lower-wall self-transition. -/
theorem lowerFixedWallPair_transition
    {depth : ℕ} (depth_lower : 7 ≤ depth) :
    LowerWallTransition (lowerFixedWallPair depth) (lowerFixedWallPair depth) := by
  have wall := lowerFixedWallPair_isLowerWallMantissa depth_lower
  refine ⟨wall, wall, depth, by omega, ?_⟩
  obtain ⟨_, _, denominator_eq, _⟩ := lowerFixedDenominator_data depth_lower
  have fixed := lowerNormalizedMantissa_fixed depth_lower
  have denominator_eq_rat :
      (2 : ℚ) * ((lowerFixedDenominator depth / 2 : ℕ) : ℚ) =
        lowerFixedDenominator depth := by
    exact_mod_cast denominator_eq
  simp only [lowerFixedWallPair, lowerWallValue]
  rw [denominator_eq, denominator_eq_rat]
  exact fixed

/-- The explicit lower-wall fixed coordinate has no distinct successor. -/
theorem lowerFixedWallPair_next_eq
    {depth : ℕ} (depth_lower : 7 ≤ depth) {next : ℕ × ℕ}
    (transition : LowerWallTransition (lowerFixedWallPair depth) next) :
    next = lowerFixedWallPair depth :=
  lowerWallTransition_next_unique transition (lowerFixedWallPair_transition depth_lower)

end MatrixMortality.MixedPrimeDebt
