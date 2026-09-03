import MatrixMortality.PadicValuation

/-!
# The two-place reader's poison wall

Affine returns integral at a prime preserve its negative valuation chamber. A finite pole
integral at the same prime is incompatible with both this infinity gate and unit determinant,
independently of the two register primes or the number of ambient modes.
-/

namespace MatrixMortality.TwoPlaceReader

open PadicValuation

/-- The valuation ring at `prime`, with zero represented explicitly because `padicValRat`
assigns zero valuation to zero. -/
def PoisonIntegral (prime : Nat) (value : ℚ) : Prop :=
  value = 0 ∨ 0 ≤ padicValRat prime value

namespace PoisonIntegral

/-- Zero belongs to every rational valuation ring. -/
theorem zero (prime : Nat) : PoisonIntegral prime 0 :=
  Or.inl rfl

/-- A valuation ring is closed under negation. -/
theorem neg {prime : Nat} {value : ℚ}
    (integral : PoisonIntegral prime value) :
    PoisonIntegral prime (-value) := by
  rcases integral with value_zero | value_nonnegative
  · exact Or.inl (by simp [value_zero])
  · exact Or.inr (by simpa only [padicValRat.neg] using value_nonnegative)

/-- A rational valuation ring is closed under multiplication. -/
theorem mul {prime : Nat} [Fact prime.Prime] {left right : ℚ}
    (left_integral : PoisonIntegral prime left)
    (right_integral : PoisonIntegral prime right) :
    PoisonIntegral prime (left * right) := by
  by_cases left_zero : left = 0
  · exact Or.inl (by simp [left_zero])
  by_cases right_zero : right = 0
  · exact Or.inl (by simp [right_zero])
  right
  rw [padicValRat.mul left_zero right_zero]
  exact add_nonneg (left_integral.resolve_left left_zero)
    (right_integral.resolve_left right_zero)

/-- A rational valuation ring is closed under addition. -/
theorem add {prime : Nat} [Fact prime.Prime] {left right : ℚ}
    (left_integral : PoisonIntegral prime left)
    (right_integral : PoisonIntegral prime right) :
    PoisonIntegral prime (left + right) := by
  rcases left_integral with left_zero | left_nonnegative
  · simpa [left_zero] using right_integral
  rcases right_integral with right_zero | right_nonnegative
  · simpa [PoisonIntegral, right_zero] using Or.inr left_nonnegative
  by_cases sum_zero : left + right = 0
  · exact Or.inl sum_zero
  · right
    have minimum_nonnegative :
        0 ≤ min (padicValRat prime left) (padicValRat prime right) :=
      le_min left_nonnegative right_nonnegative
    have minimum_bound :
        min (padicValRat prime left) (padicValRat prime right) ≤
          padicValRat prime (left + right) :=
      padicValRat.min_le_padicValRat_add sum_zero
    exact minimum_nonnegative.trans minimum_bound

end PoisonIntegral

/-- An affine return with unit slope and denominator preserves the exact negative valuation of
its input when its offset is integral. -/
theorem integralAffine_negative_hasValue
    {prime : Nat} [Fact prime.Prime]
    {leading offset denominator state : ℚ}
    (leading_unit : IsUnit prime leading)
    (offset_integral : PoisonIntegral prime offset)
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
    · simpa [offset_zero] using leading_value
    · have offset_value : HasValue prime offset (padicValRat prime offset) :=
        ⟨offset_zero, rfl⟩
      exact add_hasValue_left leading_value offset_value
        (state_negative.2.trans_le (offset_integral.resolve_left offset_zero))
  simpa using div_hasValue numerator_value denominator_unit

/-- The negative poison chamber is forward-invariant under an integral affine isometry. -/
theorem integralAffine_negative_forward
    {prime : Nat} [Fact prime.Prime]
    {leading offset denominator state : ℚ}
    (leading_unit : IsUnit prime leading)
    (offset_integral : PoisonIntegral prime offset)
    (denominator_unit : IsUnit prime denominator)
    (state_negative : IsNegative prime state) :
    IsNegative prime ((leading * state + offset) / denominator) := by
  have output_value := integralAffine_negative_hasValue leading_unit offset_integral
    denominator_unit state_negative
  exact ⟨output_value.1, output_value.2.trans_lt state_negative.2⟩

/-- A finite integral pole destroys the unit determinant required by an integral poison gate.
Here `lower = 0 ∨ vπ(lower) > 0` is the exact lower-left condition used to stabilize the
negative chamber at infinity. -/
theorem finiteIntegralPole_determinant_not_unit
    {prime : Nat} [Fact prime.Prime]
    {leading offset lower denominator pole : ℚ}
    (leading_integral : PoisonIntegral prime leading)
    (offset_integral : PoisonIntegral prime offset)
    (lower_stabilizes : lower = 0 ∨ IsPositive prime lower)
    (pole_integral : PoisonIntegral prime pole)
    (pole_denominator : lower * pole + denominator = 0) :
    ¬IsUnit prime (leading * denominator - offset * lower) := by
  intro determinant_unit
  rcases lower_stabilizes with lower_zero | lower_positive
  · have denominator_zero : denominator = 0 := by
      simpa [lower_zero] using pole_denominator
    exact determinant_unit.1 (by simp [lower_zero, denominator_zero])
  · have denominator_eq : denominator = -lower * pole := by
      linarith only [pole_denominator]
    have determinant_eq :
        leading * denominator - offset * lower =
          -(lower * (leading * pole + offset)) := by
      rw [denominator_eq]
      ring
    have bracket_integral :
        PoisonIntegral prime (leading * pole + offset) :=
      PoisonIntegral.add (PoisonIntegral.mul leading_integral pole_integral) offset_integral
    by_cases bracket_zero : leading * pole + offset = 0
    · exact determinant_unit.1 (by simp [determinant_eq, bracket_zero])
    · have lower_value :
          HasValue prime lower (padicValRat prime lower) :=
        ⟨lower_positive.1, rfl⟩
      have bracket_value :
          HasValue prime (leading * pole + offset)
            (padicValRat prime (leading * pole + offset)) :=
        ⟨bracket_zero, rfl⟩
      have determinant_value :=
        neg_hasValue (mul_hasValue lower_value bracket_value)
      have determinant_positive :
          0 < padicValRat prime (leading * denominator - offset * lower) := by
        rw [determinant_eq, determinant_value.2]
        exact add_pos_of_pos_of_nonneg lower_positive.2
          (bracket_integral.resolve_left bracket_zero)
      rw [determinant_unit.2] at determinant_positive
      exact (lt_irrefl 0 determinant_positive)

end MatrixMortality.TwoPlaceReader
