import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import MatrixMortality.TernaryEncoding

/-!
# Periodic ternary values and finite word commutation

Equality of two periodic fractions is equivalent to commutation of their finite blocks.
This replaces arguments about infinite radix expansions by ternary-code injectivity.
-/

namespace MatrixMortality

/-- The repeating ternary fraction associated with a nonempty block. -/
def periodicTernaryCode (word : List Bool) : ℚ :=
  ternaryCode word / (3 ^ word.length - 1)

theorem ternaryPeriodDenominator_pos (word : List Bool) (nonempty : word ≠ []) :
    (0 : ℚ) < 3 ^ word.length - 1 := by
  have length_ne_zero : word.length ≠ 0 := (List.length_pos_iff.mpr nonempty).ne'
  exact sub_pos.mpr (one_lt_pow₀ (by norm_num) length_ne_zero)

/-- Periodic fractions agree exactly when concatenating the blocks commutes. -/
theorem periodicTernaryCode_eq_iff_commute (first second : List Bool)
    (first_nonempty : first ≠ []) (second_nonempty : second ≠ []) :
    periodicTernaryCode first = periodicTernaryCode second ↔
      first ++ second = second ++ first := by
  have first_denominator := (ternaryPeriodDenominator_pos first first_nonempty).ne'
  have second_denominator := (ternaryPeriodDenominator_pos second second_nonempty).ne'
  rw [periodicTernaryCode, periodicTernaryCode,
    div_eq_div_iff first_denominator second_denominator]
  constructor
  · intro cross
    have codes_equal : (ternaryCode (first ++ second) : ℚ) =
        ternaryCode (second ++ first) := by
      simp only [ternaryCode_append, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      nlinarith [cross]
    exact ternaryCode_injective (by exact_mod_cast codes_equal)
  · intro words_equal
    have codes_equal := congrArg (fun word => (ternaryCode word : ℚ)) words_equal
    have expanded :
        (3 : ℚ) ^ second.length * ternaryCode first + ternaryCode second =
          3 ^ first.length * ternaryCode second + ternaryCode first := by
      simpa only [ternaryCode_append, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
        Nat.cast_ofNat] using codes_equal
    nlinarith [expanded]

/-- A word's final digits are its code modulo the corresponding power of three. -/
theorem ternaryCode_drop_mod (word : List Bool) (length : Nat) (within : length ≤ word.length) :
    ternaryCode (word.drop (word.length - length)) = ternaryCode word % 3 ^ length := by
  have suffix_length : (word.drop (word.length - length)).length = length := by
    simp only [List.length_drop]
    omega
  have code_bound := ternaryCode_lt_pow_length (word.drop (word.length - length))
  have code_split := ternaryCode_append (word.take (word.length - length))
    (word.drop (word.length - length))
  have equation : ternaryCode word =
      3 ^ length * ternaryCode (word.take (word.length - length)) +
        ternaryCode (word.drop (word.length - length)) := by
    simpa only [List.take_append_drop, suffix_length] using code_split
  rw [equation]
  simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_mod]
  have bounded : ternaryCode (word.drop (word.length - length)) < 3 ^ length := by
    simpa only [suffix_length] using code_bound
  exact (Nat.mod_eq_of_lt bounded).symm

/-- Matching terminal code residues force the shorter word to be a suffix of the longer. -/
theorem isSuffix_of_ternaryCode_mod (short long : List Bool)
    (length_le : short.length ≤ long.length)
    (codes_equal : ternaryCode short = ternaryCode long % 3 ^ short.length) :
    short <:+ long := by
  have suffix_equal : short = long.drop (long.length - short.length) :=
    ternaryCode_injective
      (codes_equal.trans (ternaryCode_drop_mod long short.length length_le).symm)
  rw [suffix_equal]
  exact List.drop_suffix _ _

end MatrixMortality
