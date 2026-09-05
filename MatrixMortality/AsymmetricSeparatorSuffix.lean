import Mathlib.Data.Nat.ModEq
import MatrixMortality.AsymmetricSeparatorTail

/-!
# Terminal digits of a vanishing asymmetric coefficient

The two phase slopes have a denominator coprime to three. Clearing it and reducing modulo
the shorter length scale forces suffix comparability, even for unrestricted control words.
-/

namespace MatrixMortality.AsymmetricSeparatorRealization

open ChangedSeparatorTail

private theorem periodDenominator_coprime (length : Nat) (positive : 0 < length) :
    Nat.Coprime (3 ^ length - 1) 3 := by
  have full : Nat.Coprime (3 ^ length - 1) (3 ^ length) :=
    (Nat.coprime_self_sub_left (Nat.one_le_pow _ _ (by decide))).mpr (Nat.coprime_one_left _)
  exact full.of_dvd_right (dvd_pow_self 3 (by omega : length ≠ 0))

/-- A mixed-slope equality retains every terminal digit of the shorter word. -/
theorem asymmetric_suffix_comparable (body first second : List Bool)
    (nonempty : body ≠ [])
    (equal : tiltedTernaryCode (-1 - periodicTernaryCode body) first =
      tiltedTernaryCode (7 - 9 * periodicTernaryCode body) second) :
    first <:+ second ∨ second <:+ first := by
  let denominator := 3 ^ body.length - 1
  let numerator := ternaryCode body
  have power_positive : 0 < 3 ^ body.length := by positivity
  have denominator_cast : (denominator : ℚ) = 3 ^ body.length - 1 := by
    dsimp [denominator]
    rw [Nat.cast_sub (by omega)]
    norm_num
  have denominator_ne_zero : (denominator : ℚ) ≠ 0 := by
    rw [denominator_cast]
    exact (ternaryPeriodDenominator_pos body nonempty).ne'
  have rational_equation :
      (denominator : ℚ) * ternaryCode first + 9 * numerator * 3 ^ second.length =
        denominator * ternaryCode second +
          (denominator + numerator) * 3 ^ first.length + 7 * denominator * 3 ^ second.length := by
    have normalized :
        (ternaryCode first : ℚ) + (-1 - numerator / denominator) * 3 ^ first.length =
          ternaryCode second + (7 - 9 * (numerator / denominator)) * 3 ^ second.length := by
      simpa only [tiltedTernaryCode, periodicTernaryCode, denominator_cast, numerator] using equal
    have cleared :
        (denominator : ℚ) * ternaryCode first -
          (denominator + numerator) * 3 ^ first.length =
            denominator * ternaryCode second +
              (7 * denominator - 9 * numerator) * 3 ^ second.length := by
      calc
        _ = (denominator : ℚ) *
            (ternaryCode first + (-1 - numerator / denominator) * 3 ^ first.length) := by
              field_simp
              ring
        _ = denominator *
            (ternaryCode second + (7 - 9 * (numerator / denominator)) * 3 ^ second.length) :=
              congrArg (fun value : ℚ => denominator * value) normalized
        _ = _ := by
          field_simp
    nlinarith [cleared]
  have equation :
      denominator * ternaryCode first + 9 * numerator * 3 ^ second.length =
        denominator * ternaryCode second +
          (denominator + numerator) * 3 ^ first.length + 7 * denominator * 3 ^ second.length := by
    exact_mod_cast rational_equation
  let length := min first.length second.length
  have first_mod : 3 ^ first.length % 3 ^ length = 0 :=
    Nat.mod_eq_zero_of_dvd (pow_dvd_pow 3 (Nat.min_le_left _ _))
  have second_mod : 3 ^ second.length % 3 ^ length = 0 :=
    Nat.mod_eq_zero_of_dvd (pow_dvd_pow 3 (Nat.min_le_right _ _))
  have multiples : Nat.ModEq (3 ^ length)
      (denominator * ternaryCode first) (denominator * ternaryCode second) := by
    have residues := congrArg (fun value => value % 3 ^ length) equation
    simpa [Nat.ModEq, Nat.add_mod, Nat.mul_mod, first_mod, second_mod] using residues
  have coprime : Nat.Coprime (3 ^ length) denominator :=
    ((periodDenominator_coprime body.length (List.length_pos_iff.mpr nonempty)).pow_right
      length).symm
  have codes : Nat.ModEq (3 ^ length) (ternaryCode first) (ternaryCode second) :=
    multiples.cancel_left_of_coprime coprime
  rcases le_total first.length second.length with first_shorter | second_shorter
  · have residues : ternaryCode first = ternaryCode second % 3 ^ first.length := by
      simpa only [Nat.ModEq, length, Nat.min_eq_left first_shorter,
        Nat.mod_eq_of_lt (ternaryCode_lt_pow_length first)] using codes
    exact Or.inl (isSuffix_of_ternaryCode_mod first second first_shorter residues)
  · have residues : ternaryCode second = ternaryCode first % 3 ^ second.length := by
      simpa only [Nat.ModEq, length, Nat.min_eq_right second_shorter,
        Nat.mod_eq_of_lt (ternaryCode_lt_pow_length second)] using codes.symm
    exact Or.inr (isSuffix_of_ternaryCode_mod second first second_shorter residues)

/-- Appending a common suffix factors its length scale out of a mixed-slope equality. -/
theorem tiltedTernaryCode_append (slope : ℚ) (first second : List Bool) :
    tiltedTernaryCode slope (first ++ second) =
      ternaryCode second + 3 ^ second.length * tiltedTernaryCode slope first := by
  simp only [tiltedTernaryCode, ternaryCode_append, List.length_append,
    Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_add]
  ring

/-- Nonempty words lie below `-2` in the injective slope chamber. -/
theorem tiltedTernaryCode_lt_neg_two (slope : ℚ) (slope_lt : slope < -3 / 2)
    (word : List Bool) (nonempty : word ≠ []) : tiltedTernaryCode slope word < -2 := by
  have code_bound : (ternaryCode word : ℚ) + 1 ≤ 3 ^ word.length := by
    exact_mod_cast ternaryCode_lt_pow_length word
  have scale_bound : (3 : ℚ) ≤ 3 ^ word.length := by
    exact_mod_cast (Nat.pow_le_pow_right (by decide : 0 < 3)
      (List.length_pos_iff.mpr nonempty))
  have scaled := mul_lt_mul_of_pos_right slope_lt
    (by positivity : (0 : ℚ) < 3 ^ word.length)
  rw [tiltedTernaryCode]
  nlinarith

end MatrixMortality.AsymmetricSeparatorRealization
