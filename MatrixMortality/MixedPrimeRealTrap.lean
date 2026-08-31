import MatrixMortality.MixedPrimeExit

/-!
# Real trap for the mixed-prime shell

Every shell block preserves `[1/5, 1/2]`. Outside this interval the zero-wait block is extremal,
so any fixed exterior target imposes an explicit computable bound on the number of shell blocks.
Inside, every rational unit target has guarded rational predecessors of every block length.
-/

namespace MatrixMortality.MixedPrimeDebt

open PadicValuation
open PeriodicShell

private local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

private theorem shellRatio_pow_nonneg (wait : ℕ) :
    0 ≤ (2 / 3 : ℚ) ^ wait := by
  positivity

private theorem shellRatio_pow_le_one (wait : ℕ) :
    (2 / 3 : ℚ) ^ wait ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

private theorem exists_realTrap_contract {threshold : ℚ} (threshold_positive : 0 < threshold) :
    ∃ exponent : ℕ, (3 / 5 : ℚ) ^ exponent < threshold :=
  exists_pow_lt_of_lt_one threshold_positive (by norm_num)

/-- The first power of `3/5` below `targetDistance/sourceDistance`. -/
def realTrapLengthBound (sourceDistance targetDistance : ℚ) : ℕ :=
  if positive : 0 < targetDistance / sourceDistance then
    Nat.find (exists_realTrap_contract positive)
  else 0

private theorem realTrapLengthBound_spec
    {sourceDistance targetDistance : ℚ} (source_positive : 0 < sourceDistance)
    (target_positive : 0 < targetDistance) :
    (3 / 5 : ℚ) ^ realTrapLengthBound sourceDistance targetDistance <
      targetDistance / sourceDistance := by
  rw [realTrapLengthBound, dif_pos (div_pos target_positive source_positive)]
  exact Nat.find_spec (exists_realTrap_contract (div_pos target_positive source_positive))

private theorem length_lt_realTrapLengthBound
    {sourceDistance targetDistance : ℚ} (source_positive : 0 < sourceDistance)
    (target_positive : 0 < targetDistance) {length : ℕ}
    (distance_bound :
      targetDistance ≤ (3 / 5 : ℚ) ^ length * sourceDistance) :
    length < realTrapLengthBound sourceDistance targetDistance := by
  let bound := realTrapLengthBound sourceDistance targetDistance
  have bound_contracts := realTrapLengthBound_spec source_positive target_positive
  by_contra length_not_lt
  have bound_le_length : bound ≤ length := Nat.le_of_not_gt length_not_lt
  have power_le : (3 / 5 : ℚ) ^ length ≤ (3 / 5 : ℚ) ^ bound :=
    (pow_le_pow_iff_right_of_lt_one₀ (by norm_num) (by norm_num)).2 bound_le_length
  have scaled_power_le :
      (3 / 5 : ℚ) ^ length * sourceDistance ≤
        (3 / 5 : ℚ) ^ bound * sourceDistance :=
    mul_le_mul_of_nonneg_right power_le source_positive.le
  have bound_below_target :
      (3 / 5 : ℚ) ^ bound * sourceDistance < targetDistance :=
    (lt_div_iff₀ source_positive).mp bound_contracts
  exact (not_lt_of_ge (distance_bound.trans scaled_power_le)) bound_below_target

private theorem shellStep_le_half
    (wait : ℕ) {state : ℚ} (state_le : state ≤ 1 / 2) :
    shellStep wait state ≤ 1 / 2 := by
  have ratio_nonneg := shellRatio_pow_nonneg wait
  have ratio_le := shellRatio_pow_le_one wait
  have scaled_le : (2 / 3 : ℚ) ^ wait * state ≤ 1 / 2 := by
    by_cases state_nonneg : 0 ≤ state
    · have scaled_le_state : (2 / 3 : ℚ) ^ wait * state ≤ state := by
        simpa using mul_le_mul_of_nonneg_right ratio_le state_nonneg
      exact scaled_le_state.trans state_le
    · have state_nonpos : state ≤ 0 := le_of_not_ge state_nonneg
      have scaled_nonpos : (2 / 3 : ℚ) ^ wait * state ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ratio_nonneg state_nonpos
      linarith
  simp only [shellStep]
  linarith

private theorem shellStep_one_fifth_le
    (wait : ℕ) {state : ℚ} (state_nonneg : 0 ≤ state) :
    1 / 5 ≤ shellStep wait state := by
  have scaled_nonneg : 0 ≤ (2 / 3 : ℚ) ^ wait * state :=
    mul_nonneg (shellRatio_pow_nonneg wait) state_nonneg
  simp only [shellStep]
  linarith

private theorem shellRun_le_half
    (waits : List ℕ) {state : ℚ} (state_le : state ≤ 1 / 2) :
    shellRun waits state ≤ 1 / 2 := by
  induction waits generalizing state with
  | nil => exact state_le
  | cons wait waits induction =>
      rw [shellRun_cons]
      exact induction (shellStep_le_half wait state_le)

private theorem shellRun_one_fifth_le
    (waits : List ℕ) {state : ℚ} (state_lower : 1 / 5 ≤ state) :
    1 / 5 ≤ shellRun waits state := by
  induction waits generalizing state with
  | nil => exact state_lower
  | cons wait waits induction =>
      rw [shellRun_cons]
      have state_nonneg : 0 ≤ state := by linarith
      exact induction (shellStep_one_fifth_le wait state_nonneg)

private theorem shellRun_one_fifth_le_of_nonnegative_nonempty
    {waits : List ℕ} (waits_ne : waits ≠ []) {state : ℚ} (state_nonneg : 0 ≤ state) :
    1 / 5 ≤ shellRun waits state := by
  obtain ⟨wait, tail, rfl⟩ := List.exists_cons_of_ne_nil waits_ne
  rw [shellRun_cons]
  exact shellRun_one_fifth_le tail (shellStep_one_fifth_le wait state_nonneg)

/-- The closed interval `[1/5, 1/2]` is invariant under every shell schedule. -/
theorem shellRun_mem_realTrap
    (waits : List ℕ) {state : ℚ} (state_mem : state ∈ Set.Icc (1 / 5) (1 / 2)) :
    shellRun waits state ∈ Set.Icc (1 / 5) (1 / 2) :=
  ⟨shellRun_one_fifth_le waits state_mem.1, shellRun_le_half waits state_mem.2⟩

private theorem shellStep_above_half_envelope
    (wait : ℕ) {state : ℚ} (state_positive : 0 < state) :
    shellStep wait state - 1 / 2 ≤ (3 / 5 : ℚ) * (state - 1 / 2) := by
  have ratio_le := shellRatio_pow_le_one wait
  have scaled_le_state : (2 / 3 : ℚ) ^ wait * state ≤ state := by
    exact mul_le_of_le_one_left state_positive.le ratio_le
  simp only [shellStep]
  linarith

/-- A schedule ending above the trap is bounded by the all-zero-wait trajectory. -/
theorem shellRun_above_half_envelope
    (waits : List ℕ) (state : ℚ)
    (output_above : 1 / 2 < shellRun waits state) :
    shellRun waits state - 1 / 2 ≤
      (3 / 5 : ℚ) ^ waits.length * (state - 1 / 2) := by
  induction waits generalizing state with
  | nil =>
      have run_nil : shellRun [] state = state := rfl
      rw [run_nil]
      norm_num
  | cons wait waits induction =>
      rw [shellRun_cons] at output_above ⊢
      have next_above : 1 / 2 < shellStep wait state := by
        by_contra next_not_above
        have tail_le := shellRun_le_half waits (le_of_not_gt next_not_above)
        exact (not_lt_of_ge tail_le) output_above
      have state_above : 1 / 2 < state := by
        by_contra state_not_above
        have next_le := shellStep_le_half wait (le_of_not_gt state_not_above)
        exact (not_lt_of_ge next_le) next_above
      have tail_bound := induction (shellStep wait state) output_above
      have step_bound := shellStep_above_half_envelope wait (by linarith : 0 < state)
      have power_nonneg : 0 ≤ (3 / 5 : ℚ) ^ waits.length := by positivity
      calc
        shellRun waits (shellStep wait state) - 1 / 2 ≤
            (3 / 5 : ℚ) ^ waits.length * (shellStep wait state - 1 / 2) :=
          tail_bound
        _ ≤ (3 / 5 : ℚ) ^ waits.length * ((3 / 5 : ℚ) * (state - 1 / 2)) :=
          mul_le_mul_of_nonneg_left step_bound power_nonneg
        _ = (3 / 5 : ℚ) ^ (wait :: waits).length * (state - 1 / 2) := by
          simp [pow_succ]
          ring

/-- A target above the trap can only be reached from a source above the trap. -/
theorem shellRun_above_half_forces_source
    (waits : List ℕ) {source target : ℚ}
    (reaches : shellRun waits source = target) (target_above : 1 / 2 < target) :
    1 / 2 < source := by
  by_contra source_not_above
  have output_le := shellRun_le_half waits (le_of_not_gt source_not_above)
  rw [reaches] at output_le
  exact (not_lt_of_ge output_le) target_above

/-- The explicit contraction search bounds every schedule reaching above the trap. -/
theorem shellRun_above_half_length_lt_bound
    {source target : ℚ} (source_above : 1 / 2 < source)
    (target_above : 1 / 2 < target) (waits : List ℕ)
    (reaches : shellRun waits source = target) :
    waits.length < realTrapLengthBound (source - 1 / 2) (target - 1 / 2) := by
  let sourceDistance := source - 1 / 2
  let targetDistance := target - 1 / 2
  have sourceDistance_positive : 0 < sourceDistance := by
    simp only [sourceDistance]
    linarith
  have targetDistance_positive : 0 < targetDistance := by
    simp only [targetDistance]
    linarith
  have output_above : (1 / 2 : ℚ) < shellRun waits source := by
    rw [reaches]
    exact target_above
  have orbit_bound := shellRun_above_half_envelope waits source output_above
  rw [reaches] at orbit_bound
  apply length_lt_realTrapLengthBound sourceDistance_positive targetDistance_positive
  simpa only [sourceDistance, targetDistance] using orbit_bound

private theorem shellStep_below_one_fifth_envelope
    (wait : ℕ) {state : ℚ} (state_nonpos : state ≤ 0) :
    (3 / 5 : ℚ) * (state - 1 / 2) ≤ shellStep wait state - 1 / 2 := by
  have ratio_le := shellRatio_pow_le_one wait
  have state_le_scaled : state ≤ (2 / 3 : ℚ) ^ wait * state := by
    simpa using mul_le_mul_of_nonpos_right ratio_le state_nonpos
  simp only [shellStep]
  linarith

/-- A schedule ending below the trap is bounded below by the all-zero-wait trajectory. -/
theorem shellRun_below_one_fifth_envelope
    (waits : List ℕ) (state : ℚ)
    (output_below : shellRun waits state < 1 / 5) :
    (3 / 5 : ℚ) ^ waits.length * (state - 1 / 2) ≤
      shellRun waits state - 1 / 2 := by
  induction waits generalizing state with
  | nil =>
      have run_nil : shellRun [] state = state := rfl
      rw [run_nil]
      norm_num
  | cons wait waits induction =>
      rw [shellRun_cons] at output_below ⊢
      have state_negative : state < 0 := by
        by_contra state_not_negative
        have output_lower := shellRun_one_fifth_le_of_nonnegative_nonempty
          (waits := wait :: waits) (by simp) (le_of_not_gt state_not_negative)
        rw [shellRun_cons] at output_lower
        exact (not_lt_of_ge output_lower) output_below
      have tail_bound := induction (shellStep wait state) output_below
      have step_bound := shellStep_below_one_fifth_envelope wait state_negative.le
      have power_nonneg : 0 ≤ (3 / 5 : ℚ) ^ waits.length := by positivity
      calc
        (3 / 5 : ℚ) ^ (wait :: waits).length * (state - 1 / 2) =
            (3 / 5 : ℚ) ^ waits.length * ((3 / 5 : ℚ) * (state - 1 / 2)) := by
          simp [pow_succ]
          ring
        _ ≤ (3 / 5 : ℚ) ^ waits.length * (shellStep wait state - 1 / 2) :=
          mul_le_mul_of_nonneg_left step_bound power_nonneg
        _ ≤ shellRun waits (shellStep wait state) - 1 / 2 := tail_bound

/-- A target below the trap can only be reached from a source below one half. -/
theorem shellRun_below_one_fifth_forces_source
    (waits : List ℕ) {source target : ℚ}
    (reaches : shellRun waits source = target) (target_below : target < 1 / 5) :
    source < 1 / 2 := by
  have output_below : shellRun waits source < (1 / 5 : ℚ) := by
    rw [reaches]
    exact target_below
  have orbit_bound := shellRun_below_one_fifth_envelope waits source output_below
  rw [reaches] at orbit_bound
  have power_positive : 0 < (3 / 5 : ℚ) ^ waits.length := by positivity
  by_contra source_not_below
  have source_nonnegative : 0 ≤ source - 1 / 2 := by
    have half_le_source := le_of_not_gt source_not_below
    linarith
  have left_nonnegative :
      0 ≤ (3 / 5 : ℚ) ^ waits.length * (source - 1 / 2) :=
    mul_nonneg power_positive.le source_nonnegative
  linarith

/-- The explicit contraction search bounds every schedule reaching below the trap. -/
theorem shellRun_below_one_fifth_length_lt_bound
    {source target : ℚ} (source_below : source < 1 / 2)
    (target_below : target < 1 / 5) (waits : List ℕ)
    (reaches : shellRun waits source = target) :
    waits.length < realTrapLengthBound (1 / 2 - source) (1 / 2 - target) := by
  let sourceDistance := 1 / 2 - source
  let targetDistance := 1 / 2 - target
  have sourceDistance_positive : 0 < sourceDistance := by
    simp only [sourceDistance]
    linarith
  have targetDistance_positive : 0 < targetDistance := by
    simp only [targetDistance]
    linarith
  have output_below : shellRun waits source < (1 / 5 : ℚ) := by
    rw [reaches]
    exact target_below
  have orbit_bound := shellRun_below_one_fifth_envelope waits source output_below
  rw [reaches] at orbit_bound
  have distance_bound :
      targetDistance ≤ (3 / 5 : ℚ) ^ waits.length * sourceDistance := by
    simp only [sourceDistance, targetDistance]
    linarith
  exact length_lt_realTrapLengthBound sourceDistance_positive targetDistance_positive
    distance_bound

/-- Every rational point in the half-open real trap has a one-block predecessor in the same
trap. -/
theorem exists_shellStep_realTrap_predecessor
    {target : ℚ} (target_lower : 1 / 5 < target) (target_upper : target ≤ 1 / 2) :
    ∃ wait state, state ∈ Set.Ioc (1 / 5 : ℚ) (1 / 2) ∧
      shellStep wait state = target := by
  let displacement := target - 1 / 5
  let threshold := (10 / 3 : ℚ) * displacement
  have displacement_positive : 0 < displacement := by
    simp only [displacement]
    linarith
  have threshold_positive : 0 < threshold := by
    simp only [threshold]
    positivity
  have threshold_le_one : threshold ≤ 1 := by
    simp only [threshold, displacement]
    linarith
  obtain ⟨wait, next_power_lt, threshold_le_power⟩ :=
    exists_nat_pow_near_of_lt_one threshold_positive threshold_le_one
      (by norm_num : (0 : ℚ) < 2 / 3) (by norm_num)
  let ratioPower := (2 / 3 : ℚ) ^ wait
  let slope := (3 / 5 : ℚ) * ratioPower
  let state := displacement / slope
  have ratioPower_positive : 0 < ratioPower := by
    simp only [ratioPower]
    positivity
  have slope_positive : 0 < slope := by
    simp only [slope]
    positivity
  have lower_displacement : (3 / 25 : ℚ) * ratioPower < displacement := by
    simp only [threshold] at next_power_lt
    rw [pow_succ] at next_power_lt
    nlinarith
  have upper_displacement : displacement ≤ (3 / 10 : ℚ) * ratioPower := by
    simp only [threshold] at threshold_le_power
    linarith
  have state_lower : (1 / 5 : ℚ) < state := by
    change (1 / 5 : ℚ) < displacement / slope
    rw [lt_div_iff₀ slope_positive]
    simp only [slope]
    linarith
  have state_upper : state ≤ (1 / 2 : ℚ) := by
    change displacement / slope ≤ (1 / 2 : ℚ)
    rw [div_le_iff₀ slope_positive]
    simp only [slope]
    linarith
  refine ⟨wait, state, ⟨state_lower, state_upper⟩, ?_⟩
  simp only [state, slope, displacement, shellStep]
  field_simp
  ring

/-- A five-adic unit target in the half-open real trap has a unit predecessor there. -/
theorem exists_shellStep_realTrap_unit_predecessor
    {target : ℚ} (target_lower : 1 / 5 < target) (target_upper : target ≤ 1 / 2)
    (target_unit : IsUnit 5 target) :
    ∃ wait state, state ∈ Set.Ioc (1 / 5 : ℚ) (1 / 2) ∧ IsUnit 5 state ∧
      shellStep wait state = target := by
  obtain ⟨wait, state, state_mem, step_eq⟩ :=
    exists_shellStep_realTrap_predecessor target_lower target_upper
  have output_unit : IsUnit 5 (shellRun [wait] state) := by
    rw [shellRun_singleton, step_eq]
    exact target_unit
  have prefixes := (shellPrefixesUnit_iff [wait] state).2 output_unit
  have state_unit : IsUnit 5 (shellRun [] state) := prefixes [] [wait] rfl
  have run_nil : shellRun [] state = state := rfl
  rw [run_nil] at state_unit
  exact ⟨wait, state, state_mem, state_unit, step_eq⟩

/-- Every five-adic unit target in the half-open real trap has guarded rational predecessor
schedules of every prescribed block length. -/
theorem exists_shellRun_realTrap_unit_predecessor_of_length
    {target : ℚ} (target_lower : 1 / 5 < target) (target_upper : target ≤ 1 / 2)
    (target_unit : IsUnit 5 target) (length : ℕ) :
    ∃ source waits, waits.length = length ∧
      source ∈ Set.Ioc (1 / 5 : ℚ) (1 / 2) ∧
        (∀ front back, waits = front ++ back → IsUnit 5 (shellRun front source)) ∧
        shellRun waits source = target := by
  induction length generalizing target with
  | zero =>
      have output_unit : IsUnit 5 (shellRun [] target) := by
        have run_nil : shellRun [] target = target := rfl
        rw [run_nil]
        exact target_unit
      have guarded := (shellPrefixesUnit_iff [] target).2 output_unit
      exact ⟨target, [], rfl, ⟨target_lower, target_upper⟩, guarded, rfl⟩
  | succ length induction =>
      obtain ⟨wait, middle, middle_mem, middle_unit, step_eq⟩ :=
        exists_shellStep_realTrap_unit_predecessor target_lower target_upper target_unit
      obtain ⟨source, waits, waits_length, source_mem, _, reaches_middle⟩ :=
        induction middle_mem.1 middle_mem.2 middle_unit
      have reaches_target : shellRun (waits ++ [wait]) source = target := by
        rw [shellRun_append, reaches_middle, shellRun_singleton, step_eq]
      have output_unit : IsUnit 5 (shellRun (waits ++ [wait]) source) := by
        rw [reaches_target]
        exact target_unit
      have guarded := (shellPrefixesUnit_iff (waits ++ [wait]) source).2 output_unit
      exact ⟨source, waits ++ [wait], by simp [waits_length], source_mem, guarded,
        reaches_target⟩

end MatrixMortality.MixedPrimeDebt
