import MatrixMortality.MixedPrimeRealTrapReturn

/-!
# Arbitrary finite excursions anchored at the secondary wall

Every finite shell schedule occurs verbatim inside a guarded periodic excursion from the
secondary wall. A closing wait of at least seven forces the periodic source into `(1/5,2/9]`;
its associated mantissa lies in `(9/10,1]`. The positive closing wait also forces the source to
be a two-adic unit, so the mantissa lies exactly on the secondary wall.
-/

namespace MatrixMortality.MixedPrimeDebt

open PadicValuation
open PeriodicShell

private local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
private local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- A finite body wrapped by its lower-wall entry wait and deep closing wait. -/
def wallExcursionSchedule (entryWait : ℕ) (body : List ℕ) (closingWait : ℕ) : List ℕ :=
  entryWait :: body ++ [closingWait]

/-- Periodic source of a wrapped wall-excursion schedule. -/
def wallExcursionSource (entryWait : ℕ) (body : List ℕ) (closingWait : ℕ) : ℚ :=
  shellPeriodicPoint (wallExcursionSchedule entryWait body closingWait)

/-- Mantissa whose lower predecessor is the wrapped schedule's periodic source. -/
def wallExcursionMantissa (entryWait : ℕ) (body : List ℕ) (closingWait : ℕ) : ℚ :=
  9 * wallExcursionSource entryWait body closingWait / 2

private theorem threeFifths_pow_lt_one
    {length : ℕ} (length_positive : 0 < length) :
    (3 / 5 : ℚ) ^ length < 1 := by
  exact pow_lt_one₀ (by norm_num) (by norm_num) (Nat.ne_of_gt length_positive)

private theorem shellStep_oneFifth_lt
    (wait : ℕ) {state : ℚ} (state_positive : 0 < state) :
    1 / 5 < shellStep wait state := by
  have power_positive : 0 < (2 / 3 : ℚ) ^ wait := by positivity
  have scaled_positive : 0 < (2 / 3 : ℚ) ^ wait * state :=
    mul_pos power_positive state_positive
  simp only [shellStep]
  nlinarith

private theorem shellRun_oneFifth_lt
    (waits : List ℕ) {state : ℚ} (state_lower : 1 / 5 < state) :
    1 / 5 < shellRun waits state := by
  induction waits generalizing state with
  | nil => exact state_lower
  | cons wait waits induction =>
      rw [shellRun_cons]
      exact induction (shellStep_oneFifth_lt wait (by linarith))

/-- Every nonempty periodic shell schedule lies in the half-open real trap. -/
theorem shellPeriodicPoint_mem_realTrap
    {waits : List ℕ} (waits_ne : waits ≠ []) :
    shellPeriodicPoint waits ∈ Set.Ioc (1 / 5 : ℚ) (1 / 2) := by
  let source := shellPeriodicPoint waits
  have fixed : shellRun waits source = source := (shellPeriodicCycle waits_ne).2.1
  have length_positive : 0 < waits.length := List.length_pos_of_ne_nil waits_ne
  have contraction_lt := threeFifths_pow_lt_one length_positive
  have source_upper : source ≤ 1 / 2 := by
    by_contra source_not_upper
    have source_above : 1 / 2 < source := lt_of_not_ge source_not_upper
    have envelope := shellRun_above_half_envelope waits source (fixed.symm ▸ source_above)
    rw [fixed] at envelope
    have distance_positive : 0 < source - 1 / 2 := by linarith
    have strict_contraction :
        (3 / 5 : ℚ) ^ waits.length * (source - 1 / 2) < source - 1 / 2 :=
      mul_lt_of_lt_one_left distance_positive contraction_lt
    linarith
  have source_lower_closed : 1 / 5 ≤ source := by
    by_contra source_not_lower
    have source_below : source < 1 / 5 := lt_of_not_ge source_not_lower
    have envelope := shellRun_below_one_fifth_envelope waits source
      (fixed.symm ▸ source_below)
    rw [fixed] at envelope
    have distance_positive : 0 < 1 / 2 - source := by linarith
    have strict_contraction :
        (3 / 5 : ℚ) ^ waits.length * (1 / 2 - source) < 1 / 2 - source :=
      mul_lt_of_lt_one_left distance_positive contraction_lt
    nlinarith
  obtain ⟨wait, tail, waits_eq⟩ := List.exists_cons_of_ne_nil waits_ne
  have first_positive :
      1 / 5 < shellStep wait source := shellStep_oneFifth_lt wait (by linarith)
  have source_lower : 1 / 5 < source := by
    rw [waits_eq, shellRun_cons] at fixed
    rw [← fixed]
    exact shellRun_oneFifth_lt tail first_positive
  exact ⟨source_lower, source_upper⟩

private theorem twoThirds_pow_le_seven
    {wait : ℕ} (wait_lower : 7 ≤ wait) :
    (2 / 3 : ℚ) ^ wait ≤ 128 / 2187 := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le wait_lower
  have offset_power_le : (2 / 3 : ℚ) ^ offset ≤ 1 := by
    exact pow_le_one₀ (by norm_num) (by norm_num)
  calc
    (2 / 3 : ℚ) ^ (7 + offset) = (2 / 3) ^ 7 * (2 / 3) ^ offset := by
      rw [pow_add]
    _ ≤ (2 / 3) ^ 7 * 1 :=
      mul_le_mul_of_nonneg_left offset_power_le (by positivity)
    _ = 128 / 2187 := by norm_num

/-- A deep closing wait puts the wrapped schedule's periodic source in `(1/5,2/9]`. -/
theorem wallExcursionSource_mem_lowerWindow
    (entryWait : ℕ) (body : List ℕ) {closingWait : ℕ}
    (closingWait_lower : 7 ≤ closingWait) :
    wallExcursionSource entryWait body closingWait ∈ Set.Ioc (1 / 5 : ℚ) (2 / 9) := by
  let schedule := wallExcursionSchedule entryWait body closingWait
  let source := wallExcursionSource entryWait body closingWait
  let front := entryWait :: body
  have schedule_ne : schedule ≠ [] := by simp [schedule, wallExcursionSchedule]
  have source_mem := shellPeriodicPoint_mem_realTrap schedule_ne
  have source_mem_closed : source ∈ Set.Icc (1 / 5 : ℚ) (1 / 2) :=
    ⟨source_mem.1.le, source_mem.2⟩
  have front_mem : shellRun front source ∈ Set.Icc (1 / 5 : ℚ) (1 / 2) :=
    shellRun_mem_realTrap front source_mem_closed
  have fixed : shellRun schedule source = source := (shellPeriodicCycle schedule_ne).2.1
  have closing_eq : shellStep closingWait (shellRun front source) = source := by
    change shellRun (entryWait :: body ++ [closingWait]) source = source at fixed
    rw [show entryWait :: body ++ [closingWait] = front ++ [closingWait] by simp [front],
      shellRun_append, shellRun_singleton] at fixed
    exact fixed
  have power_nonnegative : 0 ≤ (2 / 3 : ℚ) ^ closingWait := by positivity
  have power_bound := twoThirds_pow_le_seven closingWait_lower
  have scaled_state_le :
      (2 / 3 : ℚ) ^ closingWait * shellRun front source ≤
        (2 / 3) ^ closingWait * (1 / 2) :=
    mul_le_mul_of_nonneg_left front_mem.2 power_nonnegative
  have bounded_state_le :
      (2 / 3 : ℚ) ^ closingWait * shellRun front source ≤
        (128 / 2187) * (1 / 2) := by
    calc
      (2 / 3 : ℚ) ^ closingWait * shellRun front source ≤
          (2 / 3) ^ closingWait * (1 / 2) := scaled_state_le
      _ ≤ (128 / 2187) * (1 / 2) :=
        mul_le_mul_of_nonneg_right power_bound (by norm_num)
  have source_upper : source ≤ 2 / 9 := by
    rw [← closing_eq]
    simp only [shellStep]
    nlinarith
  exact ⟨source_mem.1, source_upper⟩

private theorem wallSaturation_hasValue_pow
    {prime : ℕ} [Fact prime.Prime] {value : ℚ} {valuation : ℤ}
    (value_hasValue : HasValue prime value valuation) (exponent : ℕ) :
    HasValue prime (value ^ exponent) (exponent * valuation) := by
  refine ⟨pow_ne_zero exponent value_hasValue.1, ?_⟩
  rw [padicValRat.pow, value_hasValue.2]

private theorem shellScale_twoValue (wait : ℕ) :
    HasValue 2 (3 * (2 / 3 : ℚ) ^ wait) wait := by
  have two_value : HasValue 2 (2 : ℚ) 1 := by
    simpa using (primePower_hasValue (prime := 2) 1)
  have three_unit : IsUnit 2 (3 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have ratio_value : HasValue 2 ((2 : ℚ) / 3) 1 := by
    simpa using div_hasValue two_value three_unit
  simpa using mul_hasValue three_unit (wallSaturation_hasValue_pow ratio_value wait)

private theorem shellStep_two_nonnegative
    (wait : ℕ) (state : ℚ) (state_nonnegative : 0 ≤ padicValRat 2 state) :
    0 ≤ padicValRat 2 (shellStep wait state) := by
  have five_unit : IsUnit 2 (5 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  by_cases state_zero : state = 0
  · subst state
    have output_unit : IsUnit 2 (shellStep wait 0) := by
      simpa [shellStep] using div_hasValue
        (show IsUnit 2 (1 : ℚ) from ⟨one_ne_zero, padicValRat.one⟩) five_unit
    rw [output_unit.2]
  have state_value : HasValue 2 state (padicValRat 2 state) := ⟨state_zero, rfl⟩
  have leading_value := mul_hasValue (shellScale_twoValue wait) state_value
  have leading_nonnegative :
      0 ≤ (wait : ℤ) + padicValRat 2 state := by
    exact add_nonneg (by positivity) state_nonnegative
  let numerator := 3 * (2 / 3 : ℚ) ^ wait * state + 1
  by_cases numerator_zero : numerator = 0
  · have output_zero : shellStep wait state = 0 := by
      simp only [shellStep, numerator] at numerator_zero ⊢
      rw [numerator_zero]
      simp
    rw [output_zero, padicValRat.zero]
  · have numerator_lower :=
      padicValRat.min_le_padicValRat_add (p := 2) numerator_zero
    have numerator_nonnegative : 0 ≤ padicValRat 2 numerator := by
      simpa only [numerator, leading_value.2, padicValRat.one,
        min_eq_right leading_nonnegative] using numerator_lower
    rw [shellStep, padicValRat.div numerator_zero five_unit.1, five_unit.2, sub_zero]
    exact numerator_nonnegative

private theorem shellRun_two_nonnegative
    (waits : List ℕ) (state : ℚ) (state_nonnegative : 0 ≤ padicValRat 2 state) :
    0 ≤ padicValRat 2 (shellRun waits state) := by
  induction waits generalizing state with
  | nil => exact state_nonnegative
  | cons wait waits induction =>
      rw [shellRun_cons]
      exact induction _ (shellStep_two_nonnegative wait state state_nonnegative)

private theorem wallExcursionIntercept_twoUnit
    (entryWait : ℕ) (body : List ℕ) {closingWait : ℕ}
    (closingWait_positive : 0 < closingWait) :
    IsUnit 2 (shellIntercept (wallExcursionSchedule entryWait body closingWait)) := by
  let front := entryWait :: body
  let frontState := shellRun front 0
  have front_nonnegative : 0 ≤ padicValRat 2 frontState := by
    exact shellRun_two_nonnegative front 0 (by rw [padicValRat.zero])
  have intercept_eq :
      shellIntercept (wallExcursionSchedule entryWait body closingWait) =
        shellStep closingWait frontState := by
    simp only [shellIntercept, wallExcursionSchedule]
    rw [show entryWait :: body ++ [closingWait] = front ++ [closingWait] by simp [front],
      shellRun_append, shellRun_singleton]
  rw [intercept_eq]
  by_cases front_zero : frontState = 0
  · rw [front_zero]
    have one_unit : IsUnit 2 (1 : ℚ) := ⟨one_ne_zero, padicValRat.one⟩
    have five_unit : IsUnit 2 (5 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
    simpa [shellStep] using div_hasValue one_unit five_unit
  · exact shellStep_two_aboveWall closingWait ⟨front_zero, rfl⟩ (by omega)

private theorem wallExcursionSlope_twoPositive
    (entryWait : ℕ) (body : List ℕ) {closingWait : ℕ}
    (closingWait_positive : 0 < closingWait) :
    IsPositive 2 (shellSlope (wallExcursionSchedule entryWait body closingWait)) := by
  let schedule := wallExcursionSchedule entryWait body closingWait
  have three_unit : IsUnit 2 (3 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have five_unit : IsUnit 2 (5 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have two_value : HasValue 2 (2 : ℚ) 1 := by
    simpa using (primePower_hasValue (prime := 2) 1)
  have ratio_value : HasValue 2 ((2 : ℚ) / 3) 1 := by
    simpa using div_hasValue two_value three_unit
  have three_power_unit : IsUnit 2 ((3 : ℚ) ^ schedule.length) := by
    simpa using wallSaturation_hasValue_pow three_unit schedule.length
  have ratio_power_value :
      HasValue 2 ((2 / 3 : ℚ) ^ schedule.sum) schedule.sum := by
    simpa using wallSaturation_hasValue_pow ratio_value schedule.sum
  have five_power_unit : IsUnit 2 ((5 : ℚ) ^ schedule.length) := by
    simpa using wallSaturation_hasValue_pow five_unit schedule.length
  have slope_value : HasValue 2 (shellSlope schedule) schedule.sum := by
    rw [shellSlope_eq_length_sum]
    simpa only [zero_add, sub_zero] using
      div_hasValue (mul_hasValue three_power_unit ratio_power_value) five_power_unit
  have sum_positive : 0 < schedule.sum := by
    simp only [schedule, wallExcursionSchedule, List.sum_cons, List.sum_append]
    omega
  exact ⟨slope_value.1, slope_value.2.symm ▸ (by exact_mod_cast sum_positive)⟩

/-- A positive closing wait forces the wrapped schedule's periodic source to be a two-adic
unit. -/
theorem wallExcursionSource_twoUnit
    (entryWait : ℕ) (body : List ℕ) {closingWait : ℕ}
    (closingWait_positive : 0 < closingWait) :
    IsUnit 2 (wallExcursionSource entryWait body closingWait) := by
  let schedule := wallExcursionSchedule entryWait body closingWait
  let source := wallExcursionSource entryWait body closingWait
  have schedule_ne : schedule ≠ [] := by simp [schedule, wallExcursionSchedule]
  have intercept_unit :=
    wallExcursionIntercept_twoUnit entryWait body closingWait_positive
  have slope_positive :=
    wallExcursionSlope_twoPositive entryWait body closingWait_positive
  have denominator_unit : IsUnit 2 (1 - shellSlope schedule) :=
    one_sub_positive slope_positive
  have fixed : shellRun schedule source = source := (shellPeriodicCycle schedule_ne).2.1
  rw [shellRun_eq_slope_mul_add_intercept] at fixed
  have source_eq : source = shellIntercept schedule / (1 - shellSlope schedule) := by
    apply (eq_div_iff denominator_unit.1).2
    nlinarith
  change IsUnit 2 source
  rw [source_eq]
  exact div_hasValue intercept_unit denominator_unit

/-- The wrapped schedule's periodic source remains a five-adic unit. -/
theorem wallExcursionSource_fiveUnit
    (entryWait : ℕ) (body : List ℕ) (closingWait : ℕ) :
    IsUnit 5 (wallExcursionSource entryWait body closingWait) := by
  have schedule_ne : wallExcursionSchedule entryWait body closingWait ≠ [] := by
    simp [wallExcursionSchedule]
  exact (shellPeriodicCycle schedule_ne).1

/-- A deep closing wait makes the anchored mantissa lie in `(9/10,1]`. -/
theorem wallExcursionMantissa_normalized
    (entryWait : ℕ) (body : List ℕ) {closingWait : ℕ}
    (closingWait_lower : 7 ≤ closingWait) :
    9 / 10 < wallExcursionMantissa entryWait body closingWait ∧
      wallExcursionMantissa entryWait body closingWait ≤ 1 := by
  have source_mem :=
    wallExcursionSource_mem_lowerWindow entryWait body closingWait_lower
  simp only [wallExcursionMantissa]
  norm_num at source_mem ⊢
  constructor <;> nlinarith

/-- A positive closing wait puts the anchored mantissa exactly on the secondary two-adic
wall. -/
theorem wallExcursionMantissa_twoValue
    (entryWait : ℕ) (body : List ℕ) {closingWait : ℕ}
    (closingWait_positive : 0 < closingWait) :
    HasValue 2 (wallExcursionMantissa entryWait body closingWait) (-1) := by
  have source_unit := wallExcursionSource_twoUnit entryWait body closingWait_positive
  have nine_unit : IsUnit 2 (9 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have two_value : HasValue 2 (2 : ℚ) 1 := by
    simpa using (primePower_hasValue (prime := 2) 1)
  simpa [wallExcursionMantissa] using
    div_hasValue (mul_hasValue nine_unit source_unit) two_value

/-- The anchored mantissa is a five-adic unit. -/
theorem wallExcursionMantissa_fiveUnit
    (entryWait : ℕ) (body : List ℕ) (closingWait : ℕ) :
    IsUnit 5 (wallExcursionMantissa entryWait body closingWait) := by
  have source_unit := wallExcursionSource_fiveUnit entryWait body closingWait
  have nine_unit : IsUnit 5 (9 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have two_unit : IsUnit 5 (2 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  simpa [wallExcursionMantissa] using
    div_hasValue (mul_hasValue nine_unit source_unit) two_unit

/-- The periodic source is the lower-predecessor coordinate of its anchored mantissa. -/
theorem wallExcursionSource_eq_lowerPredecessor
    (entryWait : ℕ) (body : List ℕ) (closingWait : ℕ) :
    wallExcursionSource entryWait body closingWait =
      2 * wallExcursionMantissa entryWait body closingWait / 9 := by
  simp only [wallExcursionMantissa]
  ring

/-- The entry step is exactly the lower predecessor of the anchored wall mantissa. -/
theorem wallExcursion_entryStep
    (entryWait : ℕ) (body : List ℕ) (closingWait : ℕ) :
    shellStep entryWait (wallExcursionSource entryWait body closingWait) =
      realTrapBandPoint (entryWait + 2)
        (wallExcursionMantissa entryWait body closingWait) := by
  rw [wallExcursionSource_eq_lowerPredecessor]
  exact shellStep_lowerPredecessor entryWait
    (wallExcursionMantissa entryWait body closingWait)

/-- The wrapped schedule closes and every one of its phases satisfies the five-adic guard. -/
theorem wallExcursion_cycle
    (entryWait : ℕ) (body : List ℕ) (closingWait : ℕ) :
    shellRun (wallExcursionSchedule entryWait body closingWait)
        (wallExcursionSource entryWait body closingWait) =
      wallExcursionSource entryWait body closingWait ∧
    ∀ front back,
      wallExcursionSchedule entryWait body closingWait = front ++ back →
        IsUnit 5
          (shellRun front (wallExcursionSource entryWait body closingWait)) := by
  have schedule_ne : wallExcursionSchedule entryWait body closingWait ≠ [] := by
    simp [wallExcursionSchedule]
  exact (shellPeriodicCycle schedule_ne).2

/-- A schedule with a guarded periodic source whose first step enters the normalized secondary
wall through its lower predecessor. -/
structure WallAnchoredScheduleCertificate (waits : List ℕ) where
  /-- The wait used to enter the anchored wall excursion. -/
  entryWait : ℕ
  /-- The unrestricted finite schedule realized between entry and closure. -/
  body : List ℕ
  /-- The final wait that returns the excursion to its periodic source. -/
  closingWait : ℕ
  shape : waits = wallExcursionSchedule entryWait body closingWait
  closingWait_lower : 7 ≤ closingWait
  /-- The periodic source of the certified schedule. -/
  source : ℚ
  /-- The normalized secondary-wall mantissa reached from the source. -/
  mantissa : ℚ
  source_eq : source = wallExcursionSource entryWait body closingWait
  mantissa_eq : mantissa = wallExcursionMantissa entryWait body closingWait
  mantissa_normalized : 9 / 10 < mantissa ∧ mantissa ≤ 1
  mantissa_twoValue : HasValue 2 mantissa (-1)
  mantissa_fiveUnit : IsUnit 5 mantissa
  lowerPredecessor : source = 2 * mantissa / 9
  entryStep : shellStep entryWait source = realTrapBandPoint (entryWait + 2) mantissa
  closes : shellRun waits source = source
  guarded : ∀ front back, waits = front ++ back → IsUnit 5 (shellRun front source)

/-- A schedule carrying at least one wall-anchored cycle certificate. -/
def IsWallAnchoredSchedule (waits : List ℕ) : Prop :=
  Nonempty (WallAnchoredScheduleCertificate waits)

/-- Every wrapped body with a closing wait of at least seven is wall-anchored. -/
theorem wallExcursionSchedule_isWallAnchored
    (entryWait : ℕ) (body : List ℕ) {closingWait : ℕ}
    (closingWait_lower : 7 ≤ closingWait) :
    IsWallAnchoredSchedule (wallExcursionSchedule entryWait body closingWait) := by
  let source := wallExcursionSource entryWait body closingWait
  let mantissa := wallExcursionMantissa entryWait body closingWait
  have cycle := wallExcursion_cycle entryWait body closingWait
  refine ⟨
    { entryWait := entryWait
      body := body
      closingWait := closingWait
      shape := rfl
      closingWait_lower := closingWait_lower
      source := source
      mantissa := mantissa
      source_eq := rfl
      mantissa_eq := rfl
      mantissa_normalized := wallExcursionMantissa_normalized
        entryWait body closingWait_lower
      mantissa_twoValue := wallExcursionMantissa_twoValue entryWait body (by omega)
      mantissa_fiveUnit := wallExcursionMantissa_fiveUnit entryWait body closingWait
      lowerPredecessor := wallExcursionSource_eq_lowerPredecessor
        entryWait body closingWait
      entryStep := wallExcursion_entryStep entryWait body closingWait
      closes := cycle.1
      guarded := cycle.2 }⟩

/-- Every finite wait word occurs as the middle factor of a guarded wall-anchored schedule. -/
theorem wallAnchoredSchedules_factorUniversal (body : List ℕ) :
    ∃ before after,
      IsWallAnchoredSchedule (before ++ body ++ after) := by
  refine ⟨[0], [7], ?_⟩
  simpa [wallExcursionSchedule] using
    wallExcursionSchedule_isWallAnchored 0 body (by norm_num : 7 ≤ 7)

/-- No finite word can be forbidden from every guarded wall-anchored schedule. -/
theorem not_forall_wallAnchoredSchedule_avoids_factor (forbidden : List ℕ) :
    ¬∀ waits, IsWallAnchoredSchedule waits →
      ¬∃ before after, waits = before ++ forbidden ++ after := by
  intro avoids
  obtain ⟨before, after, anchored⟩ := wallAnchoredSchedules_factorUniversal forbidden
  exact (avoids (before ++ forbidden ++ after) anchored) ⟨before, after, rfl⟩

end MatrixMortality.MixedPrimeDebt
