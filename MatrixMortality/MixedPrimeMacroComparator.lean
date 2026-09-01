import MatrixMortality.GuardedMixedPrimeFork
import MatrixMortality.MixedPrimeMacroAddress

/-!
# Exact address comparison in the mixed-prime affine monoid

The affine offset at zero is a globally injective code for words over the free macro alphabet
`DT,TD`: zero isolates the empty address; otherwise the reduced five-adic denominator recovers
length, then its radix numerator recovers the address. At equal length, commutation and the
reduced five-factor `bcbc` fork are exact equality comparators for every intervening raw toggle.
-/

set_option autoImplicit false

namespace MatrixMortality.MixedPrimeMacroComparator

open GuardedMixedPrimeFork
open MixedPrimeKernel
open MixedPrimeMacroAddress

private theorem wordAction_affine (word : List Letter) (state : ℚ) :
    wordAction word state = wordScale word * state + wordAction word 0 := by
  linarith [wordAction_sub word state 0]

private theorem affineCommuteOffset_eq_iff
    (multiplier leftOffset rightOffset : ℚ) (multiplier_lt_one : multiplier < 1) :
    multiplier * rightOffset + leftOffset = multiplier * leftOffset + rightOffset ↔
      leftOffset = rightOffset := by
  constructor
  · intro commutes
    nlinarith
  · intro offsets_eq
    rw [offsets_eq]

private theorem affineForkOffset_eq_iff
    (multiplier toggleScale leftOffset rightOffset toggleOffset : ℚ)
    (multiplier_pos : 0 < multiplier) (multiplier_lt_one : multiplier < 1)
    (toggle_scale_le_one : toggleScale ≤ 1) :
    multiplier *
          (toggleScale * (multiplier * (multiplier * leftOffset + rightOffset) +
            leftOffset) + toggleOffset) + rightOffset =
        multiplier *
          (toggleScale * (multiplier * (multiplier * rightOffset + leftOffset) +
            rightOffset) + toggleOffset) + leftOffset ↔
      leftOffset = rightOffset := by
  have core_pos : 0 < multiplier ^ 3 - multiplier ^ 2 + multiplier := by
    have quadratic_pos : 0 < multiplier ^ 2 - multiplier + 1 := by
      nlinarith [sq_nonneg (multiplier - 1 / 2)]
    nlinarith [mul_pos multiplier_pos quadratic_pos]
  have core_lt_one : multiplier ^ 3 - multiplier ^ 2 + multiplier < 1 := by
    have one_minus_pos : 0 < 1 - multiplier := by linarith
    have one_add_square_pos : 0 < 1 + multiplier ^ 2 := by positivity
    nlinarith [mul_pos one_minus_pos one_add_square_pos]
  have coefficient_lt_zero :
      toggleScale * multiplier ^ 3 - toggleScale * multiplier ^ 2 +
          toggleScale * multiplier - 1 < 0 := by
    have scaled_core_le :
        toggleScale * (multiplier ^ 3 - multiplier ^ 2 + multiplier) ≤
          multiplier ^ 3 - multiplier ^ 2 + multiplier := by
      exact mul_le_of_le_one_left core_pos.le toggle_scale_le_one
    nlinarith
  constructor
  · intro fork_eq
    have factor_zero :
        (leftOffset - rightOffset) *
            (toggleScale * multiplier ^ 3 - toggleScale * multiplier ^ 2 +
              toggleScale * multiplier - 1) = 0 := by
      calc
        _ =
            (multiplier *
                (toggleScale * (multiplier * (multiplier * leftOffset + rightOffset) +
                  leftOffset) + toggleOffset) + rightOffset) -
              (multiplier *
                (toggleScale * (multiplier * (multiplier * rightOffset + leftOffset) +
                  rightOffset) + toggleOffset) + leftOffset) := by ring
        _ = 0 := sub_eq_zero.mpr fork_eq
    rcases mul_eq_zero.mp factor_zero with offsets_zero | coefficient_zero
    · exact sub_eq_zero.mp offsets_zero
    · exact False.elim (ne_of_lt coefficient_lt_zero coefficient_zero)
  · intro offsets_eq
    rw [offsets_eq]

/-- The affine multiplier of a macro address is the pure length clock `(2/5)^n`. -/
theorem wordScale_expandAddress (address : List Bool) :
    wordScale (expandAddress address) = (2 / 5 : ℚ) ^ address.length := by
  induction address with
  | nil => simp [expandAddress, wordScale]
  | cons bit tail induction =>
      rw [expandAddress, wordScale_append, induction]
      cases bit <;>
        norm_num [addressMacro, wordScale, actionScale, pow_succ']

/-- Equality of macro-address multipliers is exactly equality of address lengths. -/
theorem wordScale_expandAddress_eq_iff_length_eq (left right : List Bool) :
    wordScale (expandAddress left) = wordScale (expandAddress right) ↔
      left.length = right.length := by
  rw [wordScale_expandAddress, wordScale_expandAddress]
  constructor
  · intro powers_eq
    exact pow_right_injective₀ (a := (2 / 5 : ℚ)) (by norm_num) (by norm_num) powers_eq
  · intro length_eq
    rw [length_eq]

/-- A nonempty address code is a unit modulo five, so its affine offset retains its length. -/
theorem five_not_dvd_addressCode (address : List Bool) (address_ne : address ≠ []) :
    ¬5 ∣ addressCode address := by
  let last := address.getLast address_ne
  have decomposition := List.dropLast_append_getLast address_ne
  have code_cast_ne :
      (addressCode (address.dropLast ++ [last]) : ZMod 5) ≠ 0 := by
    rw [addressCode_append_cast_zmod_five]
    have cast_eq :
        (addressDigit last * (2 : ZMod 5) ^ address.dropLast.length) =
          ((addressDigit last * 2 ^ address.dropLast.length : ℕ) : ZMod 5) := by
      push_cast
      rfl
    rw [cast_eq, ne_eq, ZMod.natCast_eq_zero_iff]
    cases last with
    | false =>
        simp only [addressDigit]
        intro divides
        rcases Nat.prime_five.dvd_mul.mp divides with digit_dvd | power_dvd
        · norm_num at digit_dvd
        · have two_dvd := Nat.prime_five.dvd_of_dvd_pow power_dvd
          norm_num at two_dvd
    | true =>
        simp only [addressDigit]
        intro divides
        rcases Nat.prime_five.dvd_mul.mp divides with digit_dvd | power_dvd
        · norm_num at digit_dvd
        · have two_dvd := Nat.prime_five.dvd_of_dvd_pow power_dvd
          norm_num at two_dvd
  intro five_dvd
  apply code_cast_ne
  rw [decomposition]
  exact (ZMod.natCast_eq_zero_iff _ _).2 five_dvd

private theorem addressCode_cross_eq_of_addressOffset_eq
    (left right : List Bool) (offsets_eq : addressOffset left = addressOffset right) :
    addressCode left * 5 ^ right.length = addressCode right * 5 ^ left.length := by
  have left_scaled := addressOffset_scaled left
  have right_scaled := addressOffset_scaled right
  have cross_with_five :
      (5 : ℚ) * addressCode left * 5 ^ right.length =
        5 * addressCode right * 5 ^ left.length := by
    calc
      (5 : ℚ) * addressCode left * 5 ^ right.length =
          (3 * 5 ^ left.length * addressOffset left) * 5 ^ right.length := by
        rw [left_scaled]
      _ = (3 * 5 ^ right.length * addressOffset right) * 5 ^ left.length := by
        rw [offsets_eq]
        ring
      _ = 5 * addressCode right * 5 ^ left.length := by rw [right_scaled]
  have cross :
      (addressCode left : ℚ) * 5 ^ right.length =
        addressCode right * 5 ^ left.length := by
    nlinarith
  exact_mod_cast cross

private theorem not_exponent_lt_of_fiveUnit_cross
    (leftCode rightCode leftExponent rightExponent : ℕ)
    (right_unit : ¬5 ∣ rightCode)
    (cross : leftCode * 5 ^ rightExponent = rightCode * 5 ^ leftExponent) :
    ¬leftExponent < rightExponent := by
  intro exponents_lt
  have exponent_split :
      5 ^ rightExponent = 5 ^ leftExponent * 5 ^ (rightExponent - leftExponent) := by
    rw [← pow_add]
    congr 1
    omega
  have reduced : leftCode * 5 ^ (rightExponent - leftExponent) = rightCode := by
    apply Nat.mul_left_cancel (n := 5 ^ leftExponent)
      (pow_pos (by norm_num : 0 < (5 : ℕ)) leftExponent)
    calc
      5 ^ leftExponent * (leftCode * 5 ^ (rightExponent - leftExponent)) =
          leftCode * (5 ^ leftExponent * 5 ^ (rightExponent - leftExponent)) := by
        ac_rfl
      _ = leftCode * 5 ^ rightExponent := by rw [exponent_split]
      _ = rightCode * 5 ^ leftExponent := cross
      _ = 5 ^ leftExponent * rightCode := by ac_rfl
  have gap_ne : rightExponent - leftExponent ≠ 0 := by omega
  have five_dvd_power : 5 ∣ 5 ^ (rightExponent - leftExponent) :=
    dvd_pow_self 5 gap_ne
  have five_dvd_right : 5 ∣ rightCode := by
    rw [← reduced]
    exact five_dvd_power.mul_left leftCode
  exact right_unit five_dvd_right

private theorem exponent_eq_of_fiveUnit_cross
    (leftCode rightCode leftExponent rightExponent : ℕ)
    (left_unit : ¬5 ∣ leftCode) (right_unit : ¬5 ∣ rightCode)
    (cross : leftCode * 5 ^ rightExponent = rightCode * 5 ^ leftExponent) :
    leftExponent = rightExponent := by
  have no_left_lt := not_exponent_lt_of_fiveUnit_cross leftCode rightCode
    leftExponent rightExponent right_unit cross
  have no_right_lt := not_exponent_lt_of_fiveUnit_cross rightCode leftCode
    rightExponent leftExponent left_unit cross.symm
  omega

/-- The affine offset alone is injective on nonempty macro addresses; its exact five-adic
denominator recovers the address length before the radix code recovers the digits. -/
theorem addressOffset_injective_of_ne_nil
    (left right : List Bool) (left_ne : left ≠ []) (right_ne : right ≠ [])
    (offsets_eq : addressOffset left = addressOffset right) :
    left = right := by
  have cross := addressCode_cross_eq_of_addressOffset_eq left right offsets_eq
  have length_eq : left.length = right.length :=
    exponent_eq_of_fiveUnit_cross (addressCode left) (addressCode right)
      left.length right.length (five_not_dvd_addressCode left left_ne)
      (five_not_dvd_addressCode right right_ne) cross
  apply expandAddress_wordAction_injective_of_length_eq _ _ length_eq
  intro state
  rw [wordAction_expandAddress, wordAction_expandAddress, length_eq, offsets_eq]

/-- Every macro-address offset is nonnegative. -/
theorem addressOffset_nonneg (address : List Bool) : 0 ≤ addressOffset address := by
  induction address with
  | nil => norm_num [addressOffset]
  | cons bit tail induction =>
      cases bit <;> norm_num [addressOffset, addressDigit] <;> positivity

/-- Every nonempty macro address has a strictly positive offset. -/
theorem addressOffset_pos_of_ne_nil (address : List Bool) (address_ne : address ≠ []) :
    0 < addressOffset address := by
  cases address with
  | nil => exact False.elim (address_ne rfl)
  | cons bit tail =>
      have tail_nonneg := addressOffset_nonneg tail
      cases bit <;> norm_num [addressOffset, addressDigit] <;> positivity

/-- The affine offset is a globally injective one-coordinate code for macro addresses, including
the empty address. -/
theorem addressOffset_injective : Function.Injective addressOffset := by
  intro left right offsets_eq
  by_cases left_nil : left = []
  · subst left
    have right_nil : right = [] := by
      by_contra right_ne
      have right_pos := addressOffset_pos_of_ne_nil right right_ne
      norm_num [addressOffset] at offsets_eq
      linarith
    exact right_nil.symm
  · by_cases right_nil : right = []
    · subst right
      have left_pos := addressOffset_pos_of_ne_nil left left_nil
      norm_num [addressOffset] at offsets_eq
      linarith
    · exact addressOffset_injective_of_ne_nil left right left_nil right_nil offsets_eq

/-- Evaluation at zero is an injective scalar reader for arbitrary macro addresses. -/
theorem expandAddress_at_zero_injective :
    Function.Injective (fun address => wordAction (expandAddress address) 0) := by
  intro left right values_eq
  change wordAction (expandAddress left) 0 = wordAction (expandAddress right) 0 at values_eq
  rw [wordAction_expandAddress, wordAction_expandAddress] at values_eq
  norm_num at values_eq
  exact addressOffset_injective values_eq

/-- Evaluation at zero detects whether two equal-length macro addresses commute. -/
theorem expandAddress_commute_at_zero_eq_iff_of_length_eq
    (left right : List Bool) (length_eq : left.length = right.length) :
    wordAction (expandAddress left)
          (wordAction (expandAddress right) 0) =
        wordAction (expandAddress right)
          (wordAction (expandAddress left) 0) ↔
      left = right := by
  constructor
  · intro at_zero
    cases left with
    | nil => simpa using length_eq.symm
    | cons leftHead leftTail =>
        have length_pos : 0 < (leftHead :: leftTail).length := by simp
        have multiplier_lt_one : (2 / 5 : ℚ) ^ (leftHead :: leftTail).length < 1 := by
          exact pow_lt_one₀ (by norm_num) (by norm_num) (Nat.ne_of_gt length_pos)
        simp only [List.length_cons] at multiplier_lt_one
        rw [wordAction_expandAddress, wordAction_expandAddress,
          wordAction_expandAddress, wordAction_expandAddress] at at_zero
        rw [← length_eq] at at_zero
        norm_num at at_zero
        let multiplier : ℚ := (2 / 5 : ℚ) ^ (leftTail.length + 1)
        let leftOffset := addressOffset (leftHead :: leftTail)
        let rightOffset := addressOffset right
        change multiplier < 1 at multiplier_lt_one
        change multiplier * rightOffset + leftOffset =
          multiplier * leftOffset + rightOffset at at_zero
        have offsets_eq : addressOffset (leftHead :: leftTail) = addressOffset right := by
          change leftOffset = rightOffset
          exact (affineCommuteOffset_eq_iff multiplier leftOffset rightOffset
            multiplier_lt_one).mp at_zero
        apply expandAddress_wordAction_injective_of_length_eq _ _ length_eq
        intro state
        rw [wordAction_expandAddress, wordAction_expandAddress, length_eq, offsets_eq]
  · intro addresses_eq
    rw [addresses_eq]

/-- Two equal-length macro addresses commute as affine actions exactly when they are equal. -/
theorem expandAddress_commute_iff_of_length_eq
    (left right : List Bool) (length_eq : left.length = right.length) :
    (∀ state : ℚ,
      wordAction (expandAddress left)
          (wordAction (expandAddress right) state) =
        wordAction (expandAddress right)
          (wordAction (expandAddress left) state)) ↔
      left = right := by
  constructor
  · intro commutes
    exact (expandAddress_commute_at_zero_eq_iff_of_length_eq left right length_eq).mp
      (commutes 0)
  · rintro rfl
    intro state
    rfl

/-- Word-product form of scalar equal-length address comparison by commutation at zero. -/
theorem wordAction_addressCommutator_at_zero_eq_iff_of_length_eq
    (left right : List Bool) (length_eq : left.length = right.length) :
    wordAction (expandAddress left ++ expandAddress right) 0 =
        wordAction (expandAddress right ++ expandAddress left) 0 ↔
      left = right := by
  simpa only [wordAction_append] using
    expandAddress_commute_at_zero_eq_iff_of_length_eq left right length_eq

/-- Word-product form of exact equal-length address comparison by commutation. -/
theorem wordAction_addressCommutator_eq_iff_of_length_eq
    (left right : List Bool) (length_eq : left.length = right.length) :
    (∀ state : ℚ,
      wordAction (expandAddress left ++ expandAddress right) state =
        wordAction (expandAddress right ++ expandAddress left) state) ↔
      left = right := by
  simpa only [wordAction_append] using
    expandAddress_commute_iff_of_length_eq left right length_eq

/-- At scalar state zero, the reduced five-factor `bcbc` fork compares two equal-length macro
addresses independently of the intervening raw toggle word. -/
theorem addressFork_at_zero_eq_iff_of_length_eq
    (left right : List Bool) (toggle : List Letter)
    (length_eq : left.length = right.length) :
    wordAction (expandAddress right)
          (wordAction toggle
            (wordAction (expandAddress left)
              (wordAction (expandAddress right)
                (wordAction (expandAddress left) 0)))) =
        wordAction (expandAddress left)
          (wordAction toggle
            (wordAction (expandAddress right)
              (wordAction (expandAddress left)
                (wordAction (expandAddress right) 0)))) ↔
      left = right := by
  constructor
  · intro at_zero
    cases left with
    | nil => simpa using length_eq.symm
    | cons leftHead leftTail =>
        have length_pos : 0 < (leftHead :: leftTail).length := by simp
        have multiplier_pos : 0 < (2 / 5 : ℚ) ^ (leftHead :: leftTail).length := by
          positivity
        have multiplier_lt_one : (2 / 5 : ℚ) ^ (leftHead :: leftTail).length < 1 := by
          exact pow_lt_one₀ (by norm_num) (by norm_num) (Nat.ne_of_gt length_pos)
        have toggle_scale_le_one : wordScale toggle ≤ 1 := wordScale_le_one toggle
        simp only [List.length_cons] at multiplier_pos multiplier_lt_one
        have left_toggle := wordAction_affine toggle
          (wordAction (expandAddress (leftHead :: leftTail))
            (wordAction (expandAddress right)
              (wordAction (expandAddress (leftHead :: leftTail)) 0)))
        have right_toggle := wordAction_affine toggle
          (wordAction (expandAddress right)
            (wordAction (expandAddress (leftHead :: leftTail))
              (wordAction (expandAddress right) 0)))
        rw [left_toggle, right_toggle] at at_zero
        simp_rw [wordAction_expandAddress] at at_zero
        rw [← length_eq] at at_zero
        norm_num at at_zero
        let multiplier : ℚ := (2 / 5 : ℚ) ^ (leftTail.length + 1)
        let toggleScale := wordScale toggle
        let leftOffset := addressOffset (leftHead :: leftTail)
        let rightOffset := addressOffset right
        let toggleOffset := wordAction toggle 0
        change 0 < multiplier at multiplier_pos
        change multiplier < 1 at multiplier_lt_one
        change toggleScale ≤ 1 at toggle_scale_le_one
        change multiplier *
              (toggleScale * (multiplier * (multiplier * leftOffset + rightOffset) +
                leftOffset) + toggleOffset) + rightOffset =
            multiplier *
              (toggleScale * (multiplier * (multiplier * rightOffset + leftOffset) +
                rightOffset) + toggleOffset) + leftOffset at at_zero
        have offsets_eq : addressOffset (leftHead :: leftTail) = addressOffset right := by
          change leftOffset = rightOffset
          exact (affineForkOffset_eq_iff multiplier toggleScale leftOffset rightOffset
            toggleOffset multiplier_pos multiplier_lt_one toggle_scale_le_one).mp at_zero
        apply expandAddress_wordAction_injective_of_length_eq _ _ length_eq
        intro state
        rw [wordAction_expandAddress, wordAction_expandAddress, length_eq, offsets_eq]
  · intro addresses_eq
    rw [addresses_eq]

/-- The reduced five-factor `bcbc` fork compares two equal-length macro addresses as affine
actions, independently of the intervening raw toggle word. -/
theorem addressFork_eq_iff_of_length_eq
    (left right : List Bool) (toggle : List Letter)
    (length_eq : left.length = right.length) :
    (∀ state : ℚ,
      wordAction (expandAddress right)
          (wordAction toggle
            (wordAction (expandAddress left)
              (wordAction (expandAddress right)
                (wordAction (expandAddress left) state)))) =
        wordAction (expandAddress left)
          (wordAction toggle
            (wordAction (expandAddress right)
              (wordAction (expandAddress left)
                (wordAction (expandAddress right) state))))) ↔
      left = right := by
  constructor
  · intro fork_eq
    exact (addressFork_at_zero_eq_iff_of_length_eq left right toggle length_eq).mp
      (fork_eq 0)
  · rintro rfl
    intro state
    rfl

/-- Literal-word scalar form of the equal-length address comparator inside the reduced `bcbc`
fork. -/
theorem wordAction_addressFork_at_zero_eq_iff_of_length_eq
    (left right : List Bool) (toggle : List Letter)
    (length_eq : left.length = right.length) :
    wordAction
          (expandAddress right ++ toggle ++ expandAddress left ++
            expandAddress right ++ expandAddress left) 0 =
        wordAction
          (expandAddress left ++ toggle ++ expandAddress right ++
            expandAddress left ++ expandAddress right) 0 ↔
      left = right := by
  simpa only [wordAction_append] using
    addressFork_at_zero_eq_iff_of_length_eq left right toggle length_eq

/-- Literal-word form of the equal-length address comparator inside the reduced `bcbc` fork. -/
theorem wordAction_addressFork_eq_iff_of_length_eq
    (left right : List Bool) (toggle : List Letter)
    (length_eq : left.length = right.length) :
    (∀ state : ℚ,
      wordAction
          (expandAddress right ++ toggle ++ expandAddress left ++
            expandAddress right ++ expandAddress left) state =
        wordAction
          (expandAddress left ++ toggle ++ expandAddress right ++
            expandAddress left ++ expandAddress right) state) ↔
      left = right := by
  simpa only [wordAction_append] using
    addressFork_eq_iff_of_length_eq left right toggle length_eq

end MatrixMortality.MixedPrimeMacroComparator
