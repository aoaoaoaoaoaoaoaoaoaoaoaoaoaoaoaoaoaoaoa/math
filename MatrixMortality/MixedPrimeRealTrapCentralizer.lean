import MatrixMortality.MixedPrimeRealTrapSaturation

/-!
# Fixed-endpoint shell centralizers

Two nonempty shell schedules have the same rational periodic point exactly when their affine
actions commute globally.  The slope records exactly the schedule length and total wait, so the
common-point problem splits into an equal-slope affine-kernel fibre and an unequal-slope explicit
collision-source fibre.
-/

namespace MatrixMortality.MixedPrimeDebt

open PadicValuation
open PeriodicShell

private local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
private local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

private theorem centralizer_hasValue_pow
    {prime : ℕ} [Fact prime.Prime] {value : ℚ} {valuation : ℤ}
    (value_hasValue : HasValue prime value valuation) (exponent : ℕ) :
    HasValue prime (value ^ exponent) (exponent * valuation) := by
  refine ⟨pow_ne_zero exponent value_hasValue.1, ?_⟩
  rw [padicValRat.pow, value_hasValue.2]

/-- The two-adic value of a schedule slope is exactly its total wait. -/
theorem shellSlope_hasValue_two (waits : List ℕ) :
    HasValue 2 (shellSlope waits) waits.sum := by
  have two_value : HasValue 2 (2 : ℚ) 1 := by
    simpa using (primePower_hasValue (prime := 2) 1)
  have three_unit : IsUnit 2 (3 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have five_unit : IsUnit 2 (5 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have ratio_value : HasValue 2 ((2 : ℚ) / 3) 1 := by
    simpa using div_hasValue two_value three_unit
  have three_power_unit : IsUnit 2 ((3 : ℚ) ^ waits.length) := by
    simpa using centralizer_hasValue_pow three_unit waits.length
  have ratio_power_value :
      HasValue 2 ((2 / 3 : ℚ) ^ waits.sum) waits.sum := by
    simpa using centralizer_hasValue_pow ratio_value waits.sum
  have five_power_unit : IsUnit 2 ((5 : ℚ) ^ waits.length) := by
    simpa using centralizer_hasValue_pow five_unit waits.length
  rw [shellSlope_eq_length_sum]
  simpa only [zero_add, sub_zero] using
    div_hasValue (mul_hasValue three_power_unit ratio_power_value) five_power_unit

/-- Two schedules have the same slope exactly when they have the same length and total wait. -/
theorem shellSlope_eq_iff_length_sum (left right : List ℕ) :
    shellSlope left = shellSlope right ↔
      left.length = right.length ∧ left.sum = right.sum := by
  constructor
  · intro slope_eq
    have five_value_eq := congrArg (padicValRat 5) slope_eq
    have two_value_eq := congrArg (padicValRat 2) slope_eq
    rw [(shellSlope_hasValue_five left).2, (shellSlope_hasValue_five right).2] at five_value_eq
    rw [(shellSlope_hasValue_two left).2, (shellSlope_hasValue_two right).2] at two_value_eq
    constructor <;> omega
  · rintro ⟨length_eq, sum_eq⟩
    exact shellSlope_eq_of_length_sum length_eq sum_eq

private theorem shellSlope_ne_one {waits : List ℕ} (waits_ne : waits ≠ []) :
    shellSlope waits ≠ 1 := by
  have length_ne : waits.length ≠ ([] : List ℕ).length := by
    have length_positive : 0 < waits.length := List.length_pos_of_ne_nil waits_ne
    simp only [List.length_nil]
    omega
  have slope_ne := shellSlope_ne_of_length_ne length_ne
  simpa [shellSlope] using slope_ne

/-- A nonempty shell schedule has only its canonical periodic point as a rational fixed point. -/
theorem shellRun_fixedPoint_unique
    {waits : List ℕ} (waits_ne : waits ≠ []) {state : ℚ}
    (fixed : shellRun waits state = state) :
    state = shellPeriodicPoint waits := by
  have periodic_fixed :
      shellRun waits (shellPeriodicPoint waits) = shellPeriodicPoint waits :=
    (shellPeriodicCycle waits_ne).2.1
  have displacement :=
    shellRun_sub_shellRun waits state (shellPeriodicPoint waits)
  rw [fixed, periodic_fixed] at displacement
  have factor_ne : 1 - shellSlope waits ≠ 0 :=
    sub_ne_zero.mpr (shellSlope_ne_one waits_ne).symm
  have product_zero :
      (1 - shellSlope waits) * (state - shellPeriodicPoint waits) = 0 := by
    nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp product_zero).resolve_left factor_ne)

/-- Global commutation of two chronological shell schedules. -/
def ShellSchedulesCommute (left right : List ℕ) : Prop :=
  ∀ state,
    shellRun (left ++ right) state = shellRun (right ++ left) state

/-- Two nonempty schedules have the same periodic point exactly when their affine actions
commute globally. -/
theorem shellPeriodicPoint_eq_iff_commute
    {left right : List ℕ} (left_ne : left ≠ []) (right_ne : right ≠ []) :
    shellPeriodicPoint left = shellPeriodicPoint right ↔
      ShellSchedulesCommute left right := by
  constructor
  · intro point_eq state
    let point := shellPeriodicPoint left
    have left_fixed : shellRun left point = point := (shellPeriodicCycle left_ne).2.1
    have right_fixed : shellRun right point = point := by
      dsimp only [point]
      rw [point_eq]
      exact (shellPeriodicCycle right_ne).2.1
    have left_intercept :
        shellIntercept left = (1 - shellSlope left) * point := by
      rw [shellRun_eq_slope_mul_add_intercept] at left_fixed
      linarith
    have right_intercept :
        shellIntercept right = (1 - shellSlope right) * point := by
      rw [shellRun_eq_slope_mul_add_intercept] at right_fixed
      linarith
    rw [shellRun_append, shellRun_append,
      shellRun_eq_slope_mul_add_intercept, shellRun_eq_slope_mul_add_intercept,
      shellRun_eq_slope_mul_add_intercept, shellRun_eq_slope_mul_add_intercept,
      left_intercept, right_intercept]
    ring
  · intro commute
    let point := shellPeriodicPoint left
    have left_fixed : shellRun left point = point := (shellPeriodicCycle left_ne).2.1
    have commute_at := commute point
    simp only [shellRun_append, left_fixed] at commute_at
    have right_point_fixed_by_left :
        shellRun left (shellRun right point) = shellRun right point := commute_at.symm
    have right_fixed : shellRun right point = point :=
      shellRun_fixedPoint_unique left_ne right_point_fixed_by_left
    exact shellRun_fixedPoint_unique right_ne right_fixed

/-- In an equal-slope fibre, equality of periodic points is exactly a global affine relation. -/
theorem shellPeriodicPoint_eq_iff_globalRelation_of_length_sum
    {left right : List ℕ} (left_ne : left ≠ []) (right_ne : right ≠ [])
    (length_eq : left.length = right.length) (sum_eq : left.sum = right.sum) :
    shellPeriodicPoint left = shellPeriodicPoint right ↔
      ∀ state, shellRun left state = shellRun right state := by
  have slope_eq : shellSlope left = shellSlope right :=
    shellSlope_eq_of_length_sum length_eq sum_eq
  constructor
  · intro point_eq state
    let point := shellPeriodicPoint left
    have left_fixed : shellRun left point = point := (shellPeriodicCycle left_ne).2.1
    have right_fixed : shellRun right point = point := by
      dsimp only [point]
      rw [point_eq]
      exact (shellPeriodicCycle right_ne).2.1
    have left_displacement := shellRun_sub_shellRun left state point
    have right_displacement := shellRun_sub_shellRun right state point
    rw [left_fixed, slope_eq] at left_displacement
    rw [right_fixed] at right_displacement
    linarith
  · intro relation
    have left_fixed := (shellPeriodicCycle left_ne).2.1
    have right_fixed :
        shellRun right (shellPeriodicPoint left) = shellPeriodicPoint left := by
      rw [← relation]
      exact left_fixed
    exact shellRun_fixedPoint_unique right_ne right_fixed

/-- In an unequal-slope fibre, equality of periodic points is exactly equality with the explicit
collision source. -/
theorem shellPeriodicPoint_eq_iff_collisionSource
    {left right : List ℕ} (left_ne : left ≠ []) (right_ne : right ≠ [])
    (slope_ne : shellSlope left ≠ shellSlope right) :
    shellPeriodicPoint left = shellPeriodicPoint right ↔
      collisionSource left right = shellPeriodicPoint left := by
  constructor
  · intro point_eq
    have left_fixed := (shellPeriodicCycle left_ne).2.1
    have right_fixed :
        shellRun right (shellPeriodicPoint left) = shellPeriodicPoint left := by
      rw [point_eq]
      exact (shellPeriodicCycle right_ne).2.1
    exact collisionSource_eq_of_shellRun_eq left right slope_ne
      (left_fixed.trans right_fixed.symm)
  · intro source_eq
    have collision := shellRun_collisionSource left right slope_ne
    rw [source_eq] at collision
    have left_fixed := (shellPeriodicCycle left_ne).2.1
    have right_fixed :
        shellRun right (shellPeriodicPoint left) = shellPeriodicPoint left :=
      collision.symm.trans left_fixed
    exact shellRun_fixedPoint_unique right_ne right_fixed

end MatrixMortality.MixedPrimeDebt
