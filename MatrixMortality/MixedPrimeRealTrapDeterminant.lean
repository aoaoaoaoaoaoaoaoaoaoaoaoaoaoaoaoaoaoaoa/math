import MatrixMortality.MixedPrimeRealTrapAntichain

/-!
# Cleared determinant carry and endpoint stripping

The affine determinant governing accepted same-length cross-grade collisions has an exact
integer-power normalization. Shared initial waits strip multiplicatively; shared terminal waits
strip from the endpoint equation by injectivity.
-/

namespace MatrixMortality.MixedPrimeDebt

open PadicValuation
open PeriodicShell

private local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Affine determinant after clearing both forced five-power denominators. -/
def shellClearedDeterminant (left right : List ℕ) : ℚ :=
  shellGain left * shellOffset right - shellGain right * shellOffset left

@[simp]
theorem shellGain_cons (wait : ℕ) (waits : List ℕ) :
    shellGain (wait :: waits) = shellScale wait * shellGain waits := by
  simp only [shellGain, shellScale, List.length_cons, List.sum_cons, pow_succ, pow_add]
  ring

@[simp]
theorem shellGain_append_singleton (waits : List ℕ) (wait : ℕ) :
    shellGain (waits ++ [wait]) = shellScale wait * shellGain waits := by
  simp only [shellGain, shellScale, List.length_append, List.length_cons, List.length_nil,
    List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero, pow_add, pow_succ]
  ring

theorem shellOffset_append_singleton (waits : List ℕ) (wait : ℕ) :
    shellOffset (waits ++ [wait]) =
      shellScale wait * shellOffset waits + 5 ^ waits.length := by
  rw [shellOffset, shellIntercept, shellRun_append, shellRun_singleton]
  simp only [List.length_append, List.length_cons, List.length_nil, pow_succ]
  rw [shellOffset, shellStep, shellIntercept, shellScale]
  ring

/-- For equal-length schedules, the affine determinant is the cleared determinant divided by
the common squared five-power denominator. -/
theorem shellDeterminant_eq_cleared
    {left right : List ℕ} (length_eq : left.length = right.length) :
    shellSlope left * shellIntercept right -
        shellSlope right * shellIntercept left =
      shellClearedDeterminant left right / 5 ^ (2 * left.length) := by
  rw [shellSlope_eq_gain_div, shellSlope_eq_gain_div, shellClearedDeterminant,
    shellOffset, shellOffset, ← length_eq]
  have denominator_ne : (5 : ℚ) ^ left.length ≠ 0 := by positivity
  rw [show 2 * left.length = left.length + left.length by omega, pow_add]
  field_simp

private theorem determinant_unit_pow
    {value : ℚ} (value_unit : IsUnit 5 value) (exponent : ℕ) :
    IsUnit 5 (value ^ exponent) := by
  refine ⟨pow_ne_zero exponent value_unit.1, ?_⟩
  rw [padicValRat.pow, value_unit.2]
  simp

private theorem five_mul_shellScale_hasValue (wait : ℕ) :
    HasValue 5 (5 * shellScale wait) 1 := by
  have five_value : HasValue 5 (5 : ℚ) 1 := by
    simpa using (primePower_hasValue (prime := 5) 1)
  have two_unit : IsUnit 5 (2 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have three_unit : IsUnit 5 (3 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have ratio_unit : IsUnit 5 ((2 : ℚ) / 3) := div_hasValue two_unit three_unit
  have scale_unit : IsUnit 5 (shellScale wait) := by
    simp only [shellScale]
    exact mul_hasValue three_unit (determinant_unit_pow ratio_unit wait)
  simpa using mul_hasValue five_value scale_unit

/-- Prefixing both schedules by one wait multiplies the cleared determinant by one five-power
and a five-adic unit. -/
theorem shellClearedDeterminant_cons_same (wait : ℕ) (left right : List ℕ) :
    shellClearedDeterminant (wait :: left) (wait :: right) =
      5 * shellScale wait * shellClearedDeterminant left right := by
  rw [shellClearedDeterminant, shellGain_cons, shellGain_cons,
    shellOffset_cons, shellOffset_cons]
  change
    shellScale wait * shellGain left * (shellGain right + 5 * shellOffset right) -
        shellScale wait * shellGain right * (shellGain left + 5 * shellOffset left) =
      5 * shellScale wait *
        (shellGain left * shellOffset right - shellGain right * shellOffset left)
  ring

/-- The cleared determinant valuation shifts by exactly one under a shared first wait. -/
theorem shellClearedDeterminant_cons_same_hasValue_iff
    (wait : ℕ) (left right : List ℕ) (valuation : ℤ) :
    HasValue 5
        (shellClearedDeterminant (wait :: left) (wait :: right))
        (valuation + 1) ↔
      HasValue 5 (shellClearedDeterminant left right) valuation := by
  have factor_value := five_mul_shellScale_hasValue wait
  rw [shellClearedDeterminant_cons_same]
  constructor
  · intro product_value
    have quotient_value := div_hasValue product_value factor_value
    have quotient_eq :
        (5 * shellScale wait * shellClearedDeterminant left right) /
            (5 * shellScale wait) =
          shellClearedDeterminant left right := by
      apply (div_eq_iff factor_value.1).2
      ring
    rw [quotient_eq] at quotient_value
    convert quotient_value using 1
    ring
  · intro determinant_value
    simpa [add_comm] using mul_hasValue factor_value determinant_value

/-- Appending one shared terminal wait has one exact inhomogeneous determinant recurrence. -/
theorem shellClearedDeterminant_append_same (left right : List ℕ) (wait : ℕ) :
    shellClearedDeterminant (left ++ [wait]) (right ++ [wait]) =
      shellScale wait ^ 2 * shellClearedDeterminant left right +
        shellScale wait *
          (shellGain left * 5 ^ right.length - shellGain right * 5 ^ left.length) := by
  simp only [shellClearedDeterminant, shellGain_append_singleton,
    shellOffset_append_singleton]
  ring

/-- At equal length, a shared terminal wait adds the gain difference against one common
five-power to the scaled determinant. -/
theorem shellClearedDeterminant_append_same_of_length_eq
    {left right : List ℕ} (length_eq : left.length = right.length) (wait : ℕ) :
    shellClearedDeterminant (left ++ [wait]) (right ++ [wait]) =
      shellScale wait ^ 2 * shellClearedDeterminant left right +
        shellScale wait * 5 ^ left.length * (shellGain left - shellGain right) := by
  rw [shellClearedDeterminant_append_same, ← length_eq]
  ring

/-- For equal-length cross-grade pairs, target acceptance is the positive valuation
`length + κ(Δ)` of the cleared determinant. -/
theorem sameLengthCollisionClearedDeterminant_fiveUnit_iff
    {left right : List ℕ} (length_eq : left.length = right.length)
    (sum_ne : left.sum ≠ right.sum) :
    IsUnit 5 (shellRun left (collisionSource left right)) ↔
      HasValue 5 (shellClearedDeterminant left right)
        ((left.length : ℤ) +
          shellSlopeGapFiveDepth (shellSlopeSumGap left right)) := by
  have denominator_value :
      HasValue 5 ((5 : ℚ) ^ (2 * left.length)) (2 * left.length) :=
    primePower_hasValue (2 * left.length)
  have determinant_eq := shellDeterminant_eq_cleared length_eq
  rw [sameLengthCollisionTarget_fiveUnit_iff length_eq sum_ne]
  constructor
  · intro determinant_value
    have product_value := mul_hasValue determinant_value denominator_value
    have product_eq :
        (shellSlope left * shellIntercept right -
            shellSlope right * shellIntercept left) *
            5 ^ (2 * left.length) =
          shellClearedDeterminant left right := by
      rw [determinant_eq]
      exact div_mul_cancel₀ _ denominator_value.1
    rw [product_eq] at product_value
    convert product_value using 1
    ring
  · intro cleared_value
    rw [determinant_eq]
    have quotient_value := div_hasValue cleared_value denominator_value
    convert quotient_value using 1
    ring

/-- A shared first wait reduces endpoint equality to the tail pair at the advanced source. -/
theorem shellRun_cons_same_eq_iff
    (wait : ℕ) (left right : List ℕ) (source : ℚ) :
    shellRun (wait :: left) source = shellRun (wait :: right) source ↔
      shellRun left (shellStep wait source) =
        shellRun right (shellStep wait source) := by
  rw [shellRun_cons, shellRun_cons]

/-- The tail collision source is the image of the prefixed pair's collision source under the
shared first wait. -/
theorem collisionSource_cons_same_step
    {left right : List ℕ} (sum_ne : left.sum ≠ right.sum) (wait : ℕ) :
    shellStep wait (collisionSource (wait :: left) (wait :: right)) =
      collisionSource left right := by
  have tail_slope_ne : shellSlope left ≠ shellSlope right := by
    intro slope_eq
    exact sum_ne ((shellSlope_eq_iff_length_sum left right).1 slope_eq).2
  have head_slope_ne : shellSlope (wait :: left) ≠ shellSlope (wait :: right) := by
    intro slope_eq
    have vector_eq :=
      (shellSlope_eq_iff_length_sum (wait :: left) (wait :: right)).1 slope_eq
    exact sum_ne (Nat.add_left_cancel vector_eq.2)
  have collision := shellRun_collisionSource (wait :: left) (wait :: right) head_slope_ne
  rw [shellRun_cons, shellRun_cons] at collision
  exact (collisionSource_eq_of_shellRun_eq left right tail_slope_ne collision).symm

/-- A shared terminal wait reduces endpoint equality at the same source by injectivity. -/
theorem shellRun_append_same_eq_iff
    (left right : List ℕ) (wait : ℕ) (source : ℚ) :
    shellRun (left ++ [wait]) source = shellRun (right ++ [wait]) source ↔
      shellRun left source = shellRun right source := by
  rw [shellRun_append, shellRun_append, shellRun_singleton, shellRun_singleton]
  constructor
  · intro equal
    exact shellStep_injective wait equal
  · intro equal
    exact congrArg (shellStep wait) equal

/-- A shared terminal wait leaves the unique cross-grade collision source unchanged. -/
theorem collisionSource_append_same
    {left right : List ℕ} (sum_ne : left.sum ≠ right.sum) (wait : ℕ) :
    collisionSource (left ++ [wait]) (right ++ [wait]) =
      collisionSource left right := by
  have tail_sum_ne : (left ++ [wait]).sum ≠ (right ++ [wait]).sum := by
    simp only [List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
    intro sum_eq
    exact sum_ne (Nat.add_right_cancel sum_eq)
  have tail_slope_ne :
      shellSlope (left ++ [wait]) ≠ shellSlope (right ++ [wait]) := by
    intro slope_eq
    exact tail_sum_ne
      ((shellSlope_eq_iff_length_sum (left ++ [wait]) (right ++ [wait])).1 slope_eq).2
  have base_slope_ne : shellSlope left ≠ shellSlope right := by
    intro slope_eq
    exact sum_ne ((shellSlope_eq_iff_length_sum left right).1 slope_eq).2
  have base_collision := shellRun_collisionSource left right base_slope_ne
  have appended_collision :
      shellRun (left ++ [wait]) (collisionSource left right) =
        shellRun (right ++ [wait]) (collisionSource left right) :=
    (shellRun_append_same_eq_iff left right wait (collisionSource left right)).2
      base_collision
  exact collisionSource_eq_of_shellRun_eq
    (left ++ [wait]) (right ++ [wait]) tail_slope_ne appended_collision

end MatrixMortality.MixedPrimeDebt
