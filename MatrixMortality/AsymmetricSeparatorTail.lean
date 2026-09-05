import MatrixMortality.AsymmetricSeparatorRegularity
import MatrixMortality.TernaryPeriodic

/-!
# Source slope of the asymmetric separator

The periodic value of the encoded body determines the separator row. Its slope lies in the
injective chamber, and its arithmetic agrees with the fixed return chart's code parameter.
-/

namespace MatrixMortality.AsymmetricSeparatorRealization

/-- The body selects the common slope of the erase phase. -/
def bodySlope (β : Nat) (body : List TagLetter) : ℚ :=
  -1 - periodicTernaryCode (tagEncode β body)

/-- Every nonempty encoded tag word starts with binary one. -/
theorem tagEncode_starts_true (β : Nat) (body : List TagLetter) (nonempty : body ≠ []) :
    ∃ tail, tagEncode β body = true :: tail := by
  cases body with
  | nil => exact False.elim (nonempty rfl)
  | cons letter rest => cases letter <;> simp [tagCode]

/-- A body containing `b` has a nonmaximal digit, making its periodic value strictly below one. -/
theorem bodySlope_gt_neg_two (β : Nat) (positive : 0 < β)
    (body : List TagLetter) (b_mem : .b ∈ body) : -2 < bodySlope β body := by
  have false_mem := ChangedSeparatorTail.false_mem_tagEncode_of_b_mem β positive body b_mem
  have code_bound :=
    ChangedSeparatorTail.ternaryCode_succ_lt_pow_length_of_false_mem
      (tagEncode β body) false_mem
  have bound : (ternaryCode (tagEncode β body) : ℚ) + 1 < 3 ^ (tagEncode β body).length := by
    exact_mod_cast code_bound
  have denominator_positive : (0 : ℚ) < 3 ^ (tagEncode β body).length - 1 := by
    have code_nonnegative : (0 : ℚ) ≤ ternaryCode (tagEncode β body) := by positivity
    linarith
  have ratio_lt : periodicTernaryCode (tagEncode β body) < 1 := by
    rw [periodicTernaryCode, div_lt_iff₀ denominator_positive]
    linarith
  dsimp [bodySlope]
  linarith

/-- The leading binary one puts every nonempty body in the injective slope chamber. -/
theorem bodySlope_lt_neg_three_halves (β : Nat) (body : List TagLetter)
    (nonempty : body ≠ []) : bodySlope β body < -3 / 2 := by
  obtain ⟨tail, encoded_eq⟩ := tagEncode_starts_true β body nonempty
  have denominator_positive := ternaryPeriodDenominator_pos (true :: tail) (by simp)
  have scale_positive : (0 : ℚ) < 3 ^ tail.length := by positivity
  have code_nonnegative : (0 : ℚ) ≤ ternaryCode tail := by positivity
  have ratio_gt : (1 / 2 : ℚ) < periodicTernaryCode (true :: tail) := by
    rw [periodicTernaryCode, lt_div_iff₀ denominator_positive]
    simp only [ternaryCode_cons, ternaryDigit, List.length_cons, Nat.cast_add,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_succ]
    nlinarith
  rw [bodySlope, encoded_eq]
  linarith

/-- The lower `c` word adds three letters to the encoded body. -/
theorem source_scale (β : Nat) (body : List TagLetter) :
    ChangedSeparatorTail.lowerCScale β body = 27 * (3 : ℚ) ^ (tagEncode β body).length := by
  simp [ChangedSeparatorTail.lowerCScale, nearySideLowerCScale, nearyLower, pow_add]
  ring

/-- Appending and prepending the lower marker gives the chart's affine code formula. -/
theorem source_code (β : Nat) (body : List TagLetter) :
    ChangedSeparatorTail.lowerCCode β body =
      18 * (3 : ℚ) ^ (tagEncode β body).length + 9 * ternaryCode (tagEncode β body) + 7 := by
  simp [ChangedSeparatorTail.lowerCCode, nearySideLowerC, nearyLower, ternaryCode_cons,
    ternaryCode_append, ternaryDigit, pow_add]
  ring

/-- The periodic slope selects exactly the lower code used by the inherited data matrix. -/
theorem lowerCode_bodySlope (β : Nat) (body : List TagLetter) (nonempty : body ≠ []) :
    lowerCode (bodySlope β body) (ChangedSeparatorTail.lowerCScale β body) =
      ChangedSeparatorTail.lowerCCode β body := by
  have encoded_nonempty : tagEncode β body ≠ [] :=
    fun empty => nonempty ((tagEncode_eq_nil_iff β body).mp empty)
  have denominator_ne_zero := (ternaryPeriodDenominator_pos _ encoded_nonempty).ne'
  rw [source_scale, source_code, bodySlope, periodicTernaryCode, lowerCode]
  field_simp [denominator_ne_zero]
  ring

/-- Every sufficiently wide body containing `b` lies in the fixed chart's regular locus. -/
theorem regularChart_of_b_mem (β : Nat) (width : 3 ≤ β)
    (body : List TagLetter) (b_mem : .b ∈ body) :
    RegularChart (3 ^ β) (bodySlope β body) (ChangedSeparatorTail.lowerCScale β body) := by
  have body_nonempty : body ≠ [] := List.ne_nil_of_mem b_mem
  have encoded_nonempty : tagEncode β body ≠ [] :=
    fun empty => body_nonempty ((tagEncode_eq_nil_iff β body).mp empty)
  have width_scale : (27 : ℚ) ≤ 3 ^ β := by
    exact_mod_cast (Nat.pow_le_pow_right (by norm_num : 0 < 3) width)
  have source_scale_gt : 27 < ChangedSeparatorTail.lowerCScale β body := by
    rw [source_scale]
    nlinarith [ternaryPeriodDenominator_pos _ encoded_nonempty]
  exact regularChart _ _ _ width_scale
    (bodySlope_lt_neg_three_halves β body body_nonempty) source_scale_gt

end MatrixMortality.AsymmetricSeparatorRealization
