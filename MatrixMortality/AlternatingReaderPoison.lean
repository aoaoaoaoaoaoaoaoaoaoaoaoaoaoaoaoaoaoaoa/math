import MatrixMortality.PadicValuation

/-!
# Poison invariance for affine return charts

An integral affine projective map with unit slope preserves every negative valuation shell.
Consequently, a denominator prime introduced outside the active register primes can never be
removed by subsequent affine-isometric returns.
-/

namespace MatrixMortality.AlternatingReaderPoison

open PadicValuation

/-- An affine return with unit leading and denominator coefficients preserves the exact
negative valuation of its input when its offset is integral. -/
theorem integralAffine_negative_hasValue
    {prime : ℕ} [Fact prime.Prime]
    {leading offset denominator state : ℚ}
    (leading_unit : IsUnit prime leading)
    (offset_integral : offset = 0 ∨ 0 ≤ padicValRat prime offset)
    (denominator_unit : IsUnit prime denominator)
    (state_negative : IsNegative prime state) :
    HasValue prime ((leading * state + offset) / denominator)
      (padicValRat prime state) := by
  have state_value : HasValue prime state (padicValRat prime state) :=
    ⟨state_negative.1, rfl⟩
  have leading_value :
      HasValue prime (leading * state) (padicValRat prime state) := by
    simpa using mul_hasValue leading_unit state_value
  have numerator_value :
      HasValue prime (leading * state + offset) (padicValRat prime state) := by
    by_cases offset_zero : offset = 0
    · subst offset
      simpa using leading_value
    · have offset_value : HasValue prime offset (padicValRat prime offset) :=
        ⟨offset_zero, rfl⟩
      exact add_hasValue_left leading_value offset_value
        (state_negative.2.trans_le (offset_integral.resolve_left offset_zero))
  simpa using div_hasValue numerator_value denominator_unit

/-- The negative valuation chamber is forward-invariant under an integral affine isometry. -/
theorem integralAffine_negative_forward
    {prime : ℕ} [Fact prime.Prime]
    {leading offset denominator state : ℚ}
    (leading_unit : IsUnit prime leading)
    (offset_integral : offset = 0 ∨ 0 ≤ padicValRat prime offset)
    (denominator_unit : IsUnit prime denominator)
    (state_negative : IsNegative prime state) :
    IsNegative prime ((leading * state + offset) / denominator) := by
  have output_value := integralAffine_negative_hasValue leading_unit offset_integral
    denominator_unit state_negative
  exact ⟨output_value.1, output_value.2.trans_lt state_negative.2⟩

end MatrixMortality.AlternatingReaderPoison
