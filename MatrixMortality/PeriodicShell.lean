import Mathlib.Tactic
import MatrixMortality.PadicValuation

/-!
# Periodic critical-shell schedules

Every nonempty finite schedule of waits in the mixed-prime affine benchmark has a rational periodic
orbit wholly inside the 5-adic unit shell.
-/

namespace MatrixMortality.PeriodicShell

open PadicValuation

private local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

private def step (scale state : ℚ) : ℚ :=
  (scale * state + 1) / 5

private def run : List ℚ → ℚ → ℚ
  | [], state => state
  | scale :: scales, state => run scales (step scale state)

private def product : List ℚ → ℚ
  | [] => 1
  | scale :: scales => product scales * scale

private def offset : List ℚ → ℚ
  | [] => 0
  | _ :: scales => product scales + 5 * offset scales

private def periodicPoint (scales : List ℚ) : ℚ :=
  offset scales / ((5 : ℚ) ^ scales.length - product scales)

private theorem run_append (left right : List ℚ) (state : ℚ) :
    run (left ++ right) state = run right (run left state) := by
  induction left generalizing state with
  | nil => rfl
  | cons scale scales induction =>
      simp only [List.cons_append, run]
      exact induction (step scale state)

private theorem run_eq (scales : List ℚ) (state : ℚ) :
    run scales state =
      (product scales * state + offset scales) / (5 : ℚ) ^ scales.length := by
  induction scales generalizing state with
  | nil => simp [run, product, offset]
  | cons scale scales induction =>
      rw [run, induction]
      simp only [product, offset, List.length_cons, step, pow_succ]
      ring

private theorem one_unit : IsUnit 5 (1 : ℚ) :=
  ⟨one_ne_zero, padicValRat.one⟩

private theorem five_mul_unit_positive {value : ℚ} (value_unit : IsUnit 5 value) :
    IsPositive 5 (5 * value) := by
  have five_value : HasValue 5 (5 : ℚ) 1 := by
    simpa using (primePower_hasValue (prime := 5) 1)
  have product_value : HasValue 5 (5 * value) (1 + 0) :=
    mul_hasValue five_value value_unit
  refine ⟨product_value.1, ?_⟩
  rw [product_value.2]
  norm_num

private theorem product_unit
    (scales : List ℚ) (scales_unit : ∀ scale ∈ scales, IsUnit 5 scale) :
    IsUnit 5 (product scales) := by
  induction scales with
  | nil => exact one_unit
  | cons scale scales induction =>
      have tail_unit : ∀ value ∈ scales, IsUnit 5 value := by
        intro value member
        exact scales_unit value (List.mem_cons_of_mem scale member)
      exact mul_hasValue (induction tail_unit)
        (scales_unit scale List.mem_cons_self)

private theorem offset_unit
    {scales : List ℚ} (scales_ne : scales ≠ [])
    (scales_unit : ∀ scale ∈ scales, IsUnit 5 scale) :
    IsUnit 5 (offset scales) := by
  induction scales with
  | nil => exact (scales_ne rfl).elim
  | cons scale scales induction =>
      cases scales with
      | nil => simpa [offset, product] using one_unit
      | cons next scales =>
          let tail := next :: scales
          have tail_unit : ∀ value ∈ tail, IsUnit 5 value := by
            intro value member
            exact scales_unit value (List.mem_cons_of_mem scale member)
          have tail_offset_unit : IsUnit 5 (offset tail) :=
            induction (by simp) tail_unit
          exact unit_add_positive (product_unit tail tail_unit)
            (five_mul_unit_positive tail_offset_unit)

private theorem denominator_unit
    {scales : List ℚ} (scales_ne : scales ≠ [])
    (scales_unit : ∀ scale ∈ scales, IsUnit 5 scale) :
    IsUnit 5 ((5 : ℚ) ^ scales.length - product scales) := by
  have length_positive : 0 < scales.length := List.length_pos_of_ne_nil scales_ne
  have power_positive : IsPositive 5 ((5 : ℚ) ^ scales.length) := by
    have power_value : HasValue 5 ((5 : ℚ) ^ scales.length) scales.length :=
      primePower_hasValue scales.length
    exact ⟨power_value.1, by rw [power_value.2]; exact_mod_cast length_positive⟩
  have difference_unit :=
    unit_sub_positive (product_unit scales scales_unit) power_positive
  simpa only [neg_sub] using neg_hasValue difference_unit

private theorem periodicPoint_unit
    {scales : List ℚ} (scales_ne : scales ≠ [])
    (scales_unit : ∀ scale ∈ scales, IsUnit 5 scale) :
    IsUnit 5 (periodicPoint scales) := by
  exact div_hasValue (offset_unit scales_ne scales_unit)
    (denominator_unit scales_ne scales_unit)

private theorem run_periodicPoint
    {scales : List ℚ} (scales_ne : scales ≠ [])
    (scales_unit : ∀ scale ∈ scales, IsUnit 5 scale) :
    run scales (periodicPoint scales) = periodicPoint scales := by
  rw [run_eq, periodicPoint]
  have denominator_ne := (denominator_unit scales_ne scales_unit).1
  have five_power_ne : (5 : ℚ) ^ scales.length ≠ 0 := by norm_num
  field_simp
  ring

private theorem input_unit_of_run_unit
    {scales : List ℚ} {state : ℚ}
    (scales_unit : ∀ scale ∈ scales, IsUnit 5 scale)
    (output_unit : IsUnit 5 (run scales state)) :
    IsUnit 5 state := by
  induction scales generalizing state with
  | nil => exact output_unit
  | cons scale scales induction =>
      have step_unit : IsUnit 5 (step scale state) := by
        apply induction
        · intro value member
          exact scales_unit value (List.mem_cons_of_mem scale member)
        · exact output_unit
      have five_step_positive := five_mul_unit_positive step_unit
      have numerator_unit : IsUnit 5 (5 * step scale state - 1) :=
        positive_sub_one five_step_positive
      have scale_unit : IsUnit 5 scale := scales_unit scale List.mem_cons_self
      have quotient_unit : IsUnit 5 ((5 * step scale state - 1) / scale) :=
        div_hasValue numerator_unit scale_unit
      convert quotient_unit using 1
      simp [step]
      field_simp [scale_unit.1]
      ring

private theorem runFront_unit_of_run_unit
    {scales front back : List ℚ} {state : ℚ} (split : scales = front ++ back)
    (scales_unit : ∀ scale ∈ scales, IsUnit 5 scale)
    (output_unit : IsUnit 5 (run scales state)) :
    IsUnit 5 (run front state) := by
  have back_unit : ∀ scale ∈ back, IsUnit 5 scale := by
    intro scale member
    exact scales_unit scale (split ▸ List.mem_append_right front member)
  apply input_unit_of_run_unit back_unit
  rw [← run_append, ← split]
  exact output_unit

/-- Unit coefficient carried by one wait block. -/
def shellScale (wait : ℕ) : ℚ :=
  3 * (2 / 3) ^ wait

/-- Execute a finite wait schedule on the normalized critical-shell coordinate. -/
def shellRun (waits : List ℕ) (state : ℚ) : ℚ :=
  run (waits.map shellScale) state

/-- Schedule concatenation acts by successive shell execution. -/
theorem shellRun_append (left right : List ℕ) (state : ℚ) :
    shellRun (left ++ right) state = shellRun right (shellRun left state) := by
  simpa only [shellRun, List.map_append] using
    run_append (left.map shellScale) (right.map shellScale) state

/-- Explicit rational fixed point of one repeated finite wait schedule. -/
def shellPeriodicPoint (waits : List ℕ) : ℚ :=
  periodicPoint (waits.map shellScale)

private theorem shellScale_unit (wait : ℕ) : IsUnit 5 (shellScale wait) := by
  have two_unit : IsUnit 5 (2 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have three_unit : IsUnit 5 (3 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have ratio_unit : IsUnit 5 ((2 : ℚ) / 3) := div_hasValue two_unit three_unit
  have power_unit : IsUnit 5 ((2 / 3 : ℚ) ^ wait) := by
    induction wait with
    | zero => simpa only [pow_zero] using one_unit
    | succ wait induction =>
        rw [pow_succ]
        exact mul_hasValue induction ratio_unit
  exact mul_hasValue three_unit power_unit

private theorem shellScales_unit (waits : List ℕ) :
    ∀ scale ∈ waits.map shellScale, IsUnit 5 scale := by
  intro scale member
  obtain ⟨wait, _, rfl⟩ := List.mem_map.mp member
  exact shellScale_unit wait

/-- Every phase of a shell schedule is a unit exactly when its final phase is a unit. -/
theorem shellPrefixesUnit_iff (waits : List ℕ) (state : ℚ) :
    (∀ front back, waits = front ++ back → IsUnit 5 (shellRun front state)) ↔
      IsUnit 5 (shellRun waits state) := by
  constructor
  · intro phases
    exact phases waits [] (by simp)
  · intro output_unit front back split
    apply runFront_unit_of_run_unit (scales := waits.map shellScale)
      (front := front.map shellScale) (back := back.map shellScale)
    · simp [split]
    · exact shellScales_unit waits
    · exact output_unit

/-- Every nonempty finite schedule has a rational periodic orbit whose every phase is a 5-adic
unit. -/
theorem shellPeriodicCycle
    {waits : List ℕ} (waits_ne : waits ≠ []) :
    IsUnit 5 (shellPeriodicPoint waits) ∧
      shellRun waits (shellPeriodicPoint waits) = shellPeriodicPoint waits ∧
      ∀ front back, waits = front ++ back →
        IsUnit 5 (shellRun front (shellPeriodicPoint waits)) := by
  have scales_ne : waits.map shellScale ≠ [] := by simpa using waits_ne
  have scales_unit := shellScales_unit waits
  refine ⟨periodicPoint_unit scales_ne scales_unit,
    run_periodicPoint scales_ne scales_unit, ?_⟩
  apply (shellPrefixesUnit_iff waits (shellPeriodicPoint waits)).2
  rw [shellRun, shellPeriodicPoint, run_periodicPoint scales_ne scales_unit]
  exact periodicPoint_unit scales_ne scales_unit

/-- Left schedule in a published relation for the mixed-prime affine benchmark. -/
def benchmarkRelationLeft : List ℕ :=
  [10, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

/-- Right schedule in a published relation for the mixed-prime affine benchmark. -/
def benchmarkRelationRight : List ℕ :=
  [0, 0, 1, 2, 0, 2, 1, 1, 2, 0, 6, 0, 0]

/-- The two benchmark relation schedules are distinct. -/
theorem benchmarkRelation_ne : benchmarkRelationLeft ≠ benchmarkRelationRight := by
  decide

/-- The distinct benchmark schedules induce the same rational affine map. -/
theorem shellRun_benchmarkRelation (state : ℚ) :
    shellRun benchmarkRelationLeft state = shellRun benchmarkRelationRight state := by
  norm_num [shellRun, benchmarkRelationLeft, benchmarkRelationRight, run, step, shellScale]
  ring

/-- The benchmark relation remains an affine equality inside every schedule context. -/
theorem shellRun_benchmarkRelationContext
    (before after : List ℕ) (state : ℚ) :
    shellRun (before ++ benchmarkRelationLeft ++ after) state =
      shellRun (before ++ benchmarkRelationRight ++ after) state := by
  simp only [shellRun_append]
  rw [shellRun_benchmarkRelation]

/-- Contextual substitution of the benchmark relation preserves every intermediate shell
guard. -/
theorem benchmarkRelationContextGuard
    (before after : List ℕ) (state : ℚ) :
    (∀ front back, before ++ benchmarkRelationLeft ++ after = front ++ back →
      IsUnit 5 (shellRun front state)) ↔
      ∀ front back, before ++ benchmarkRelationRight ++ after = front ++ back →
        IsUnit 5 (shellRun front state) := by
  rw [shellPrefixesUnit_iff, shellPrefixesUnit_iff,
    shellRun_benchmarkRelationContext]

/-- The benchmark relation is realized by two all-unit cycles from one rational source. -/
theorem benchmarkRelationCycle :
    let source := shellPeriodicPoint benchmarkRelationLeft
    IsUnit 5 source ∧
      shellPeriodicPoint benchmarkRelationRight = source ∧
      shellRun benchmarkRelationLeft source = source ∧
      shellRun benchmarkRelationRight source = source ∧
      (∀ front back, benchmarkRelationLeft = front ++ back →
        IsUnit 5 (shellRun front source)) ∧
      ∀ front back, benchmarkRelationRight = front ++ back →
        IsUnit 5 (shellRun front source) := by
  have left_ne : benchmarkRelationLeft ≠ [] := by decide
  have right_ne : benchmarkRelationRight ≠ [] := by decide
  have left_cycle := shellPeriodicCycle left_ne
  have right_cycle := shellPeriodicCycle right_ne
  have source_eq :
      shellPeriodicPoint benchmarkRelationRight =
        shellPeriodicPoint benchmarkRelationLeft := by
    norm_num [shellPeriodicPoint, benchmarkRelationLeft, benchmarkRelationRight,
      periodicPoint, offset, product, shellScale]
  dsimp only
  refine ⟨left_cycle.1, source_eq, left_cycle.2.1, ?_, left_cycle.2.2, ?_⟩
  · simpa only [source_eq] using right_cycle.2.1
  simpa only [source_eq] using right_cycle.2.2

end MatrixMortality.PeriodicShell
