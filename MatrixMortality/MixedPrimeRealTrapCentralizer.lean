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

/-! ## Arbitrary fixed-endpoint fibres -/

/-- Inside one length/sum grade, equality at one rational source is already a global affine
relation. -/
theorem shellRun_eq_iff_globalRelation_of_length_sum
    {left right : List ℕ} (length_eq : left.length = right.length)
    (sum_eq : left.sum = right.sum) (source : ℚ) :
    shellRun left source = shellRun right source ↔
      ∀ state, shellRun left state = shellRun right state := by
  have slope_eq : shellSlope left = shellSlope right :=
    shellSlope_eq_of_length_sum length_eq sum_eq
  constructor
  · intro collision state
    have left_displacement := shellRun_sub_shellRun left state source
    have right_displacement := shellRun_sub_shellRun right state source
    rw [slope_eq, collision] at left_displacement
    linarith
  · intro relation
    exact relation source

/-- Every pair in an arbitrary fixed-source/fixed-target fibre is exactly either one balanced
global affine relation or one unequal-slope collision-source equality. -/
theorem shellRun_eq_iff_kernel_or_collisionSource
    (left right : List ℕ) (source : ℚ) :
    shellRun left source = shellRun right source ↔
      ((left.length = right.length ∧ left.sum = right.sum) ∧
        ∀ state, shellRun left state = shellRun right state) ∨
      (¬(left.length = right.length ∧ left.sum = right.sum) ∧
        collisionSource left right = source) := by
  constructor
  · intro collision
    by_cases vector_eq : left.length = right.length ∧ left.sum = right.sum
    · exact Or.inl ⟨vector_eq,
        (shellRun_eq_iff_globalRelation_of_length_sum
          vector_eq.1 vector_eq.2 source).1 collision⟩
    · have slope_ne : shellSlope left ≠ shellSlope right := by
        exact fun slope_eq => vector_eq ((shellSlope_eq_iff_length_sum left right).1 slope_eq)
      exact Or.inr ⟨vector_eq,
        collisionSource_eq_of_shellRun_eq left right slope_ne collision⟩
  · rintro (⟨_, relation⟩ | ⟨vector_ne, source_eq⟩)
    · exact relation source
    · have slope_ne : shellSlope left ≠ shellSlope right := by
        exact fun slope_eq => vector_ne ((shellSlope_eq_iff_length_sum left right).1 slope_eq)
      have collision := shellRun_collisionSource left right slope_ne
      simpa only [source_eq] using collision

/-! ## Determinant fork inside one periodic-point centralizer -/

/-- Concatenate a fixed number of copies of one shell schedule. -/
def shellSchedulePower (waits : List ℕ) (exponent : ℕ) : List ℕ :=
  (List.replicate exponent waits).flatten

@[simp]
theorem shellSchedulePower_length (waits : List ℕ) (exponent : ℕ) :
    (shellSchedulePower waits exponent).length = exponent * waits.length := by
  simp [shellSchedulePower, List.length_flatten]

@[simp]
theorem shellSchedulePower_sum (waits : List ℕ) (exponent : ℕ) :
    (shellSchedulePower waits exponent).sum = exponent * waits.sum := by
  simp [shellSchedulePower, List.sum_flatten]

private theorem shellSchedulePower_ne_nil
    {waits : List ℕ} (waits_ne : waits ≠ []) {exponent : ℕ}
    (exponent_positive : 0 < exponent) :
    shellSchedulePower waits exponent ≠ [] := by
  have waits_length_positive : 0 < waits.length := List.length_pos_of_ne_nil waits_ne
  apply List.ne_nil_of_length_pos
  simp only [shellSchedulePower_length]
  positivity

/-- Every positive power of a nonempty schedule has the same periodic point. -/
theorem shellPeriodicPoint_schedulePower
    {waits : List ℕ} (waits_ne : waits ≠ []) {exponent : ℕ}
    (exponent_positive : 0 < exponent) :
    shellPeriodicPoint (shellSchedulePower waits exponent) =
      shellPeriodicPoint waits := by
  have power_ne := shellSchedulePower_ne_nil waits_ne exponent_positive
  have displacement :=
    shellRun_repeat_sub_periodicPoint waits_ne exponent (shellPeriodicPoint waits)
  have power_fixed :
      shellRun (shellSchedulePower waits exponent) (shellPeriodicPoint waits) =
        shellPeriodicPoint waits := by
    change shellRun (List.replicate exponent waits).flatten (shellPeriodicPoint waits) = _
    simpa only [sub_self, mul_zero, sub_eq_zero] using displacement
  exact (shellRun_fixedPoint_unique power_ne power_fixed).symm

/-- Every two-parameter product of schedules with one periodic point is a guarded loop at that
point. -/
theorem commonPeriodicPoint_bipower_loop
    {left right : List ℕ} (left_ne : left ≠ []) (right_ne : right ≠ [])
    (point_eq : shellPeriodicPoint left = shellPeriodicPoint right)
    (leftExponent rightExponent : ℕ) :
    let schedule :=
      shellSchedulePower left leftExponent ++ shellSchedulePower right rightExponent
    shellRun schedule (shellPeriodicPoint left) = shellPeriodicPoint left ∧
      ∀ front back,
        schedule = front ++ back →
          IsUnit 5 (shellRun front (shellPeriodicPoint left)) := by
  let point := shellPeriodicPoint left
  have left_displacement :=
    shellRun_repeat_sub_periodicPoint left_ne leftExponent point
  have left_fixed : shellRun (shellSchedulePower left leftExponent) point = point := by
    change shellRun (List.replicate leftExponent left).flatten point = point
    dsimp only [point] at left_displacement ⊢
    simpa only [sub_self, mul_zero, sub_eq_zero] using left_displacement
  have right_point_eq : point = shellPeriodicPoint right := point_eq
  have right_displacement :=
    shellRun_repeat_sub_periodicPoint right_ne rightExponent point
  have right_fixed : shellRun (shellSchedulePower right rightExponent) point = point := by
    change shellRun (List.replicate rightExponent right).flatten point = point
    rw [right_point_eq] at right_displacement ⊢
    simpa only [sub_self, mul_zero, sub_eq_zero] using right_displacement
  have combined_fixed :
      shellRun
          (shellSchedulePower left leftExponent ++
            shellSchedulePower right rightExponent) point = point := by
    rw [shellRun_append, left_fixed, right_fixed]
  have point_unit : IsUnit 5 point := (shellPeriodicCycle left_ne).1
  have output_unit :
      IsUnit 5
        (shellRun
          (shellSchedulePower left leftExponent ++
            shellSchedulePower right rightExponent) point) := by
    rw [combined_fixed]
    exact point_unit
  exact ⟨combined_fixed,
    (shellPrefixesUnit_iff
      (shellSchedulePower left leftExponent ++ shellSchedulePower right rightExponent)
      point).2 output_unit⟩

private theorem natLinearPair_injective
    {leftLength leftSum rightLength rightSum : ℕ}
    (determinant_ne : rightLength * leftSum ≠ leftLength * rightSum) :
    Function.Injective
      (fun exponents : ℕ × ℕ =>
        (exponents.1 * leftLength + exponents.2 * rightLength,
          exponents.1 * leftSum + exponents.2 * rightSum)) := by
  rintro ⟨leftExponent, rightExponent⟩ ⟨leftExponent', rightExponent'⟩ pair_eq
  have length_eq := congrArg Prod.fst pair_eq
  have sum_eq := congrArg Prod.snd pair_eq
  simp only at length_eq sum_eq
  have determinant_ne' :
      (rightLength : ℤ) * leftSum - leftLength * rightSum ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast determinant_ne)
  have length_eq' :
      (leftExponent : ℤ) * leftLength + rightExponent * rightLength =
        leftExponent' * leftLength + rightExponent' * rightLength := by
    exact_mod_cast length_eq
  have sum_eq' :
      (leftExponent : ℤ) * leftSum + rightExponent * rightSum =
        leftExponent' * leftSum + rightExponent' * rightSum := by
    exact_mod_cast sum_eq
  have left_product_zero :
      ((leftExponent : ℤ) - leftExponent') *
          ((rightLength : ℤ) * leftSum - leftLength * rightSum) = 0 := by
    linear_combination rightLength * sum_eq' - rightSum * length_eq'
  have right_product_zero :
      ((rightExponent : ℤ) - rightExponent') *
          ((rightLength : ℤ) * leftSum - leftLength * rightSum) = 0 := by
    linear_combination leftSum * length_eq' - leftLength * sum_eq'
  have left_eq : (leftExponent : ℤ) = leftExponent' :=
    sub_eq_zero.mp
      ((mul_eq_zero.mp left_product_zero).resolve_right determinant_ne')
  have right_eq : (rightExponent : ℤ) = rightExponent' :=
    sub_eq_zero.mp
      ((mul_eq_zero.mp right_product_zero).resolve_right determinant_ne')
  congr
  · exact_mod_cast left_eq
  · exact_mod_cast right_eq

/-- Independent length/sum vectors give an injective two-parameter family of schedule slopes. -/
theorem shellSlope_bipower_injective
    {left right : List ℕ}
    (determinant_ne : right.length * left.sum ≠ left.length * right.sum) :
    Function.Injective
      (fun exponents : ℕ × ℕ =>
        shellSlope
          (shellSchedulePower left exponents.1 ++
            shellSchedulePower right exponents.2)) := by
  intro first second slope_eq
  have length_sum_eq :=
    (shellSlope_eq_iff_length_sum
      (shellSchedulePower left first.1 ++ shellSchedulePower right first.2)
      (shellSchedulePower left second.1 ++ shellSchedulePower right second.2)).1 slope_eq
  have vector_eq :
      (first.1 * left.length + first.2 * right.length,
        first.1 * left.sum + first.2 * right.sum) =
      (second.1 * left.length + second.2 * right.length,
        second.1 * left.sum + second.2 * right.sum) := by
    apply Prod.ext
    · simpa only [List.length_append, shellSchedulePower_length] using length_sum_eq.1
    · simpa only [List.sum_append, shellSchedulePower_sum] using length_sum_eq.2
  exact natLinearPair_injective determinant_ne vector_eq

/-- Dependent length/sum vectors turn a common periodic point into an explicit global power
relation. -/
theorem commonPeriodicPoint_powerRelation_of_determinant_zero
    {left right : List ℕ} (left_ne : left ≠ []) (right_ne : right ≠ [])
    (point_eq : shellPeriodicPoint left = shellPeriodicPoint right)
    (determinant_zero : right.length * left.sum = left.length * right.sum) :
    ∀ state,
      shellRun (shellSchedulePower left right.length) state =
        shellRun (shellSchedulePower right left.length) state := by
  have left_length_positive : 0 < left.length := List.length_pos_of_ne_nil left_ne
  have right_length_positive : 0 < right.length := List.length_pos_of_ne_nil right_ne
  have left_power_ne := shellSchedulePower_ne_nil left_ne right_length_positive
  have right_power_ne := shellSchedulePower_ne_nil right_ne left_length_positive
  have power_point_eq :
      shellPeriodicPoint (shellSchedulePower left right.length) =
        shellPeriodicPoint (shellSchedulePower right left.length) := by
    rw [shellPeriodicPoint_schedulePower left_ne right_length_positive,
      shellPeriodicPoint_schedulePower right_ne left_length_positive]
    exact point_eq
  have power_length_eq :
      (shellSchedulePower left right.length).length =
        (shellSchedulePower right left.length).length := by
    simp only [shellSchedulePower_length, Nat.mul_comm]
  have power_sum_eq :
      (shellSchedulePower left right.length).sum =
        (shellSchedulePower right left.length).sum := by
    simpa only [shellSchedulePower_sum] using determinant_zero
  exact (shellPeriodicPoint_eq_iff_globalRelation_of_length_sum
    left_power_ne right_power_ne power_length_eq power_sum_eq).1 power_point_eq

/-- Independent length/sum vectors and one common periodic point produce an injective `ℕ²`
family of distinct guarded loops. -/
theorem commonPeriodicPoint_rankTwo_loops
    {left right : List ℕ} (left_ne : left ≠ []) (right_ne : right ≠ [])
    (point_eq : shellPeriodicPoint left = shellPeriodicPoint right)
    (determinant_ne : right.length * left.sum ≠ left.length * right.sum) :
    (∀ exponents : ℕ × ℕ,
      let schedule :=
        shellSchedulePower left exponents.1 ++ shellSchedulePower right exponents.2
      shellRun schedule (shellPeriodicPoint left) = shellPeriodicPoint left ∧
        ∀ front back,
          schedule = front ++ back →
            IsUnit 5 (shellRun front (shellPeriodicPoint left))) ∧
      Function.Injective
        (fun exponents : ℕ × ℕ =>
          shellSlope
            (shellSchedulePower left exponents.1 ++
              shellSchedulePower right exponents.2)) := by
  exact ⟨fun exponents =>
    commonPeriodicPoint_bipower_loop left_ne right_ne point_eq exponents.1 exponents.2,
    shellSlope_bipower_injective determinant_ne⟩

end MatrixMortality.MixedPrimeDebt
