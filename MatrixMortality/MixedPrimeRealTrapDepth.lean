import MatrixMortality.MixedPrimeFiveCarry

/-!
# Target-depth collapse in the mixed-prime real trap

For nonempty reachability, every normalized target band of depth at least two has the same
predecessor set as every deeper band with the same mantissa. Raising the target depth only raises
the final wait. Five-adic acceptance is periodic under depth shifts by ten, so guarded fixed-source
reachability reduces to twelve canonical target-depth classes: depths zero and one, followed by
residues represented by depths two through eleven.
-/

namespace MatrixMortality.MixedPrimeDebt

open PadicValuation
open PeriodicShell

private local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Raising both a wait and its target-band depth by the same amount preserves the exact
one-step equality. -/
theorem shellStep_realTrapBandPoint_shift_iff
    (wait shift depth : ℕ) (state mantissa : ℚ) :
    shellStep (wait + shift) state = realTrapBandPoint (depth + shift) mantissa ↔
      shellStep wait state = realTrapBandPoint depth mantissa := by
  have ratio_power_ne : (2 / 3 : ℚ) ^ shift ≠ 0 := by positivity
  have difference_factorization :
      shellStep (wait + shift) state - realTrapBandPoint (depth + shift) mantissa =
        (2 / 3 : ℚ) ^ shift *
          (shellStep wait state - realTrapBandPoint depth mantissa) := by
    simp only [shellStep, realTrapBandPoint, pow_add]
    ring
  constructor
  · intro shifted
    have shifted_zero :
        shellStep (wait + shift) state -
            realTrapBandPoint (depth + shift) mantissa = 0 :=
      sub_eq_zero.mpr shifted
    rw [difference_factorization] at shifted_zero
    exact sub_eq_zero.mp ((mul_eq_zero.mp shifted_zero).resolve_left ratio_power_ne)
  · intro unshifted
    apply sub_eq_zero.mp
    rw [difference_factorization, sub_eq_zero.mpr unshifted, mul_zero]

private theorem shellStep_one_fifth_lt
    (wait : ℕ) {state : ℚ} (state_positive : 0 < state) :
    1 / 5 < shellStep wait state := by
  have ratio_power_positive : 0 < (2 / 3 : ℚ) ^ wait := by positivity
  simp only [shellStep]
  nlinarith

private theorem shellRun_one_fifth_lt
    (waits : List ℕ) {state : ℚ} (state_lower : 1 / 5 < state) :
    1 / 5 < shellRun waits state := by
  induction waits generalizing state with
  | nil => exact state_lower
  | cons wait waits induction =>
      rw [shellRun_cons]
      apply induction
      exact shellStep_one_fifth_lt wait (by linarith)

private theorem shellRun_mem_halfOpenRealTrap
    (waits : List ℕ) {state : ℚ} (state_mem : state ∈ Set.Ioc (1 / 5) (1 / 2)) :
    shellRun waits state ∈ Set.Ioc (1 / 5) (1 / 2) := by
  refine ⟨shellRun_one_fifth_lt waits state_mem.1, ?_⟩
  exact (shellRun_mem_realTrap waits ⟨state_mem.1.le, state_mem.2⟩).2

/-- At target depth at least two, increasing the depth does not change the nonempty source set. The
last wait absorbs the entire depth shift. -/
theorem exists_nonempty_shellRun_realTrapBandPoint_shift_iff
    {source mantissa : ℚ} (source_mem : source ∈ Set.Ioc (1 / 5) (1 / 2))
    (mantissa_lower : 2 / 3 < mantissa) (mantissa_upper : mantissa ≤ 1)
    (depth shift : ℕ) (depth_lower : 2 ≤ depth) :
    (∃ waits : List ℕ, waits ≠ [] ∧
        shellRun waits source = realTrapBandPoint (depth + shift) mantissa) ↔
      ∃ waits : List ℕ, waits ≠ [] ∧
        shellRun waits source = realTrapBandPoint depth mantissa := by
  constructor
  · rintro ⟨waits, waits_ne, reaches_shifted⟩
    let front := waits.dropLast
    let last := waits.getLast waits_ne
    have waits_eq : front ++ [last] = waits :=
      List.dropLast_append_getLast waits_ne
    have middle_mem := shellRun_mem_halfOpenRealTrap front source_mem
    have target_mem :=
      realTrapBandPoint_mem (depth + shift) mantissa_lower mantissa_upper
    have last_step :
        shellStep last (shellRun front source) =
          realTrapBandPoint (depth + shift) mantissa := by
      rw [← waits_eq] at reaches_shifted
      simpa only [shellRun_append, shellRun_singleton] using reaches_shifted
    have wait_window := shellStep_realTrap_wait_window
      target_mem.1 target_mem.2 middle_mem last_step
    rw [realTrapMaxPredecessorWait_bandPoint
      (depth + shift) mantissa_lower mantissa_upper] at wait_window
    have shift_le_last : shift ≤ last := by omega
    let reducedLast := last - shift
    have last_eq : reducedLast + shift = last :=
      Nat.sub_add_cancel shift_le_last
    have reduced_step :
        shellStep reducedLast (shellRun front source) =
          realTrapBandPoint depth mantissa := by
      apply (shellStep_realTrapBandPoint_shift_iff
        reducedLast shift depth (shellRun front source) mantissa).mp
      rw [last_eq]
      exact last_step
    refine ⟨front ++ [reducedLast], by simp, ?_⟩
    rw [shellRun_append, shellRun_singleton, reduced_step]
  · rintro ⟨waits, waits_ne, reaches_base⟩
    let front := waits.dropLast
    let last := waits.getLast waits_ne
    have waits_eq : front ++ [last] = waits :=
      List.dropLast_append_getLast waits_ne
    have last_step :
        shellStep last (shellRun front source) = realTrapBandPoint depth mantissa := by
      rw [← waits_eq] at reaches_base
      simpa only [shellRun_append, shellRun_singleton] using reaches_base
    have shifted_step :
        shellStep (last + shift) (shellRun front source) =
          realTrapBandPoint (depth + shift) mantissa :=
      (shellStep_realTrapBandPoint_shift_iff
        last shift depth (shellRun front source) mantissa).mpr last_step
    refine ⟨front ++ [last + shift], by simp, ?_⟩
    rw [shellRun_append, shellRun_singleton, shifted_step]

private theorem shellStep_source_fiveUnit_of_output_fiveUnit
    (wait : ℕ) {state : ℚ} (output_unit : IsUnit 5 (shellStep wait state)) :
    IsUnit 5 state := by
  have prefixes := (shellPrefixesUnit_iff [wait] state).2 (by
    simpa only [shellRun_singleton] using output_unit)
  have source_unit := prefixes [] [wait] rfl
  change IsUnit 5 state at source_unit
  exact source_unit

/-- Five-adic acceptance of a normalized target ray depends on its band depth only modulo ten. -/
theorem realTrapBandPoint_fiveUnit_add_ten_mul_iff
    (depth period : ℕ) (mantissa : ℚ) :
    IsUnit 5 (realTrapBandPoint (depth + 10 * period) mantissa) ↔
      IsUnit 5 (realTrapBandPoint depth mantissa) := by
  let predecessor := mantissa / 2
  have base_step :
      shellStep depth predecessor = realTrapBandPoint depth mantissa := by
    simp only [predecessor, shellStep, realTrapBandPoint]
    ring
  have shifted_step :
      shellStep (depth + 10 * period) predecessor =
        realTrapBandPoint (depth + 10 * period) mantissa := by
    simp only [predecessor, shellStep, realTrapBandPoint, pow_add]
    ring
  constructor
  · intro shifted_unit
    have shifted_step_unit :
        IsUnit 5 (shellStep (depth + 10 * period) predecessor) := by
      rw [shifted_step]
      exact shifted_unit
    have predecessor_unit :=
      shellStep_source_fiveUnit_of_output_fiveUnit
        (depth + 10 * period) shifted_step_unit
    have base_unit :=
      (shellStep_fiveUnit_add_ten_mul_iff depth period predecessor_unit).mp
        shifted_step_unit
    rw [base_step] at base_unit
    exact base_unit
  · intro base_unit
    have base_step_unit : IsUnit 5 (shellStep depth predecessor) := by
      rw [base_step]
      exact base_unit
    have predecessor_unit :=
      shellStep_source_fiveUnit_of_output_fiveUnit depth base_step_unit
    have shifted_unit :=
      (shellStep_fiveUnit_add_ten_mul_iff depth period predecessor_unit).mpr
        base_step_unit
    rw [shifted_step] at shifted_unit
    exact shifted_unit

/-- Guarded nonempty reachability on one normalized target ray depends on the target depth only
modulo ten once the depth is at least two. -/
theorem exists_guarded_shellRun_realTrapBandPoint_add_ten_mul_iff
    {source mantissa : ℚ} (source_mem : source ∈ Set.Ioc (1 / 5) (1 / 2))
    (mantissa_lower : 2 / 3 < mantissa) (mantissa_upper : mantissa ≤ 1)
    (depth period : ℕ) (depth_lower : 2 ≤ depth) :
    (∃ waits : List ℕ, waits ≠ [] ∧
        (∀ front back, waits = front ++ back → IsUnit 5 (shellRun front source)) ∧
        shellRun waits source = realTrapBandPoint (depth + 10 * period) mantissa) ↔
      ∃ waits : List ℕ, waits ≠ [] ∧
        (∀ front back, waits = front ++ back → IsUnit 5 (shellRun front source)) ∧
        shellRun waits source = realTrapBandPoint depth mantissa := by
  have reachability := exists_nonempty_shellRun_realTrapBandPoint_shift_iff
    source_mem mantissa_lower mantissa_upper depth (10 * period) depth_lower
  have target_units := realTrapBandPoint_fiveUnit_add_ten_mul_iff depth period mantissa
  constructor
  · rintro ⟨waits, waits_ne, guarded, reaches_shifted⟩
    have shifted_unit :
        IsUnit 5 (realTrapBandPoint (depth + 10 * period) mantissa) := by
      rw [← reaches_shifted]
      exact guarded waits [] (by simp)
    obtain ⟨baseWaits, baseWaits_ne, reaches_base⟩ :=
      reachability.mp ⟨waits, waits_ne, reaches_shifted⟩
    have base_unit : IsUnit 5 (realTrapBandPoint depth mantissa) :=
      target_units.mp shifted_unit
    have base_guarded := (shellPrefixesUnit_iff baseWaits source).2 (by
      rw [reaches_base]
      exact base_unit)
    exact ⟨baseWaits, baseWaits_ne, base_guarded, reaches_base⟩
  · rintro ⟨waits, waits_ne, guarded, reaches_base⟩
    have base_unit : IsUnit 5 (realTrapBandPoint depth mantissa) := by
      rw [← reaches_base]
      exact guarded waits [] (by simp)
    obtain ⟨shiftedWaits, shiftedWaits_ne, reaches_shifted⟩ :=
      reachability.mpr ⟨waits, waits_ne, reaches_base⟩
    have shifted_unit :
        IsUnit 5 (realTrapBandPoint (depth + 10 * period) mantissa) :=
      target_units.mpr base_unit
    have shifted_guarded := (shellPrefixesUnit_iff shiftedWaits source).2 (by
      rw [reaches_shifted]
      exact shifted_unit)
    exact ⟨shiftedWaits, shiftedWaits_ne, shifted_guarded, reaches_shifted⟩

/-- Canonical representative of a target depth at least two. -/
def realTrapDepthRepresentative (depth : ℕ) : ℕ :=
  2 + (depth - 2) % 10

/-- The canonical representative lies among depths two through eleven. -/
theorem realTrapDepthRepresentative_bounds (depth : ℕ) :
    2 ≤ realTrapDepthRepresentative depth ∧ realTrapDepthRepresentative depth ≤ 11 := by
  simp only [realTrapDepthRepresentative]
  have residue_lt : (depth - 2) % 10 < 10 := Nat.mod_lt _ (by omega)
  omega

/-- Every depth at least two is its representative plus a multiple of ten. -/
theorem realTrapDepthRepresentative_decomposition
    {depth : ℕ} (depth_lower : 2 ≤ depth) :
    depth = realTrapDepthRepresentative depth + 10 * ((depth - 2) / 10) := by
  have decomposition := Nat.mod_add_div (depth - 2) 10
  have depth_eq : depth - 2 + 2 = depth := Nat.sub_add_cancel depth_lower
  simp only [realTrapDepthRepresentative]
  omega

/-- Every guarded nonempty fixed-source query in a deep normalized band reduces to the same
mantissa at one of the ten depths two through eleven. -/
theorem exists_guarded_shellRun_realTrapBandPoint_representative_iff
    {source mantissa : ℚ} (source_mem : source ∈ Set.Ioc (1 / 5) (1 / 2))
    (mantissa_lower : 2 / 3 < mantissa) (mantissa_upper : mantissa ≤ 1)
    {depth : ℕ} (depth_lower : 2 ≤ depth) :
    (∃ waits : List ℕ, waits ≠ [] ∧
        (∀ front back, waits = front ++ back → IsUnit 5 (shellRun front source)) ∧
        shellRun waits source = realTrapBandPoint depth mantissa) ↔
      ∃ waits : List ℕ, waits ≠ [] ∧
        (∀ front back, waits = front ++ back → IsUnit 5 (shellRun front source)) ∧
        shellRun waits source =
          realTrapBandPoint (realTrapDepthRepresentative depth) mantissa := by
  have representative_bounds := realTrapDepthRepresentative_bounds depth
  have depth_decomposition := realTrapDepthRepresentative_decomposition depth_lower
  simpa only [← depth_decomposition] using
    (exists_guarded_shellRun_realTrapBandPoint_add_ten_mul_iff
      source_mem mantissa_lower mantissa_upper (realTrapDepthRepresentative depth)
        ((depth - 2) / 10) representative_bounds.1)

end MatrixMortality.MixedPrimeDebt
