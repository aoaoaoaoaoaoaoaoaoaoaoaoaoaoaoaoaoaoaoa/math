import Mathlib.Tactic
import MatrixMortality.MixedPrimeKernel
import MatrixMortality.PadicValuation

/-!
# Periodic critical-shell schedules

Every nonempty finite schedule of waits in the mixed-prime affine benchmark has a rational periodic
orbit wholly inside the 5-adic unit shell.
-/

namespace MatrixMortality.PeriodicShell

open PadicValuation
open MixedPrimeKernel

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

/-- Raw matrix-product block corresponding to one shell wait. -/
def shellRawBlock (wait : ℕ) : List Letter :=
  [.translate] ++ List.replicate wait .dilate

/-- Raw matrix-product word corresponding to a chronological shell schedule. -/
def shellRawWord : List ℕ → List Letter
  | [] => []
  | wait :: waits => shellRawWord waits ++ shellRawBlock wait

/-- Chronological schedule concatenation reverses into matrix-product word order. -/
theorem shellRawWord_append (left right : List ℕ) :
    shellRawWord (left ++ right) = shellRawWord right ++ shellRawWord left := by
  induction left with
  | nil => simp [shellRawWord]
  | cons wait left induction =>
      simp [shellRawWord, induction, List.append_assoc]

private theorem pumpWord_append_pair (pump : ℕ) :
    pumpWord pump ++ [.dilate, .translate] =
      [.dilate, .translate] ++ pumpWord pump := by
  induction pump with
  | zero => rfl
  | succ pump induction =>
      simp only [pumpWord, List.append_assoc]
      rw [induction]

private theorem shellRawWord_replicate_one_bridge (pump : ℕ) :
    shellRawWord (List.replicate pump 1) ++ [.translate] =
      [.translate] ++ pumpWord pump := by
  induction pump with
  | zero => rfl
  | succ pump induction =>
      have extended := congrArg
        (fun word => word ++ [.dilate, .translate]) induction
      simp only [List.append_assoc] at extended
      rw [pumpWord_append_pair] at extended
      simpa [List.replicate_succ, shellRawWord, shellRawBlock, pumpWord,
        List.append_assoc] using extended

private theorem wordAction_replicate_dilate (wait : ℕ) (state : ℚ) :
    wordAction (List.replicate wait .dilate) state = (2 / 3 : ℚ) ^ wait * state := by
  induction wait with
  | zero => simp [wordAction]
  | succ wait induction =>
      rw [List.replicate_succ, wordAction, action, induction, pow_succ]
      ring

private theorem wordAction_shellRawBlock (wait : ℕ) (state : ℚ) :
    wordAction (shellRawBlock wait) (5 * state) / 5 =
      (shellScale wait * state + 1) / 5 := by
  rw [shellRawBlock, wordAction_append]
  simp only [wordAction, action]
  rw [wordAction_replicate_dilate]
  simp only [shellScale]
  ring

/-- Shell execution is the raw `D,T` word action conjugated by `state ↦ 5 * state`. -/
theorem shellRun_eq_wordAction (waits : List ℕ) (state : ℚ) :
    shellRun waits state = wordAction (shellRawWord waits) (5 * state) / 5 := by
  induction waits generalizing state with
  | nil =>
      change state = 5 * state / 5
      ring
  | cons wait waits induction =>
      change shellRun waits ((shellScale wait * state + 1) / 5) = _
      rw [induction, shellRawWord, wordAction_append]
      have block := wordAction_shellRawBlock wait state
      rw [show wordAction (shellRawBlock wait) (5 * state) =
        5 * ((shellScale wait * state + 1) / 5) by linarith]

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

/-- Left shell schedule induced by prefixing the odd raw kernel family with `T`. -/
def kernelOddScheduleLeft (pump : ℕ) : List ℕ :=
  [2] ++ List.replicate pump 1 ++ [9, 2, 2] ++ List.replicate 9 0 ++ [1]

/-- Right shell schedule induced by prefixing the odd raw kernel family with `T`. -/
def kernelOddScheduleRight (pump : ℕ) : List ℕ :=
  [0, 0, 2] ++ List.replicate pump 1 ++ [0, 2, 0, 2, 1, 1, 2, 0, 6, 0, 0]

/-- Every odd-family shell pair consists of distinct schedules. -/
theorem kernelOddSchedule_ne (pump : ℕ) :
    kernelOddScheduleLeft pump ≠ kernelOddScheduleRight pump := by
  simp [kernelOddScheduleLeft, kernelOddScheduleRight]

/-- Prefixing the left odd-family word by `T` is exactly its shell schedule word. -/
theorem shellRawWord_kernelOddScheduleLeft (pump : ℕ) :
    shellRawWord (kernelOddScheduleLeft pump) =
      [.translate] ++ kernelOddFamilyLeft pump := by
  have bridge := shellRawWord_replicate_one_bridge pump
  have contextual := congrArg
    (fun word =>
      shellRawWord ([9, 2, 2] ++ List.replicate 9 0 ++ [1]) ++ word ++
        List.replicate 2 .dilate) bridge
  simpa [kernelOddScheduleLeft, shellRawWord_append, shellRawWord, shellRawBlock,
    kernelOddFamilyLeft, List.append_assoc] using contextual

/-- Prefixing the right odd-family word by `T` is exactly its shell schedule word. -/
theorem shellRawWord_kernelOddScheduleRight (pump : ℕ) :
    shellRawWord (kernelOddScheduleRight pump) =
      [.translate] ++ kernelOddFamilyRight pump := by
  have bridge := shellRawWord_replicate_one_bridge pump
  have contextual := congrArg
    (fun word =>
      shellRawWord [0, 2, 0, 2, 1, 1, 2, 0, 6, 0, 0] ++ word ++
        [.dilate, .dilate, .translate, .translate]) bridge
  simpa [kernelOddScheduleRight, shellRawWord_append, shellRawWord, shellRawBlock,
    kernelOddFamilyRight, List.append_assoc] using contextual

/-- Every odd-family shell pair induces the same rational affine map. -/
theorem shellRun_kernelOddSchedule (pump : ℕ) (state : ℚ) :
    shellRun (kernelOddScheduleLeft pump) state =
      shellRun (kernelOddScheduleRight pump) state := by
  rw [shellRun_eq_wordAction, shellRun_eq_wordAction,
    shellRawWord_kernelOddScheduleLeft, shellRawWord_kernelOddScheduleRight]
  simp only [wordAction_append]
  rw [wordAction_kernelOddFamily]

/-- Every odd-family shell equality remains valid inside an arbitrary schedule context. -/
theorem shellRun_kernelOddScheduleContext
    (pump : ℕ) (before after : List ℕ) (state : ℚ) :
    shellRun (before ++ kernelOddScheduleLeft pump ++ after) state =
      shellRun (before ++ kernelOddScheduleRight pump ++ after) state := by
  simp only [shellRun_append]
  rw [shellRun_kernelOddSchedule]

/-- Contextual substitution of an odd-family relation preserves every shell guard. -/
theorem kernelOddScheduleContextGuard
    (pump : ℕ) (before after : List ℕ) (state : ℚ) :
    (∀ front back, before ++ kernelOddScheduleLeft pump ++ after = front ++ back →
      IsUnit 5 (shellRun front state)) ↔
      ∀ front back, before ++ kernelOddScheduleRight pump ++ after = front ++ back →
        IsUnit 5 (shellRun front state) := by
  rw [shellPrefixesUnit_iff, shellPrefixesUnit_iff,
    shellRun_kernelOddScheduleContext]

/-- Every odd-family relation is realized by two all-unit cycles from one rational source. -/
theorem kernelOddScheduleCycle (pump : ℕ) :
    let left := kernelOddScheduleLeft pump
    let right := kernelOddScheduleRight pump
    let source := shellPeriodicPoint left
    IsUnit 5 source ∧
      shellRun left source = source ∧
      shellRun right source = source ∧
      (∀ front back, left = front ++ back → IsUnit 5 (shellRun front source)) ∧
      ∀ front back, right = front ++ back → IsUnit 5 (shellRun front source) := by
  have left_ne : kernelOddScheduleLeft pump ≠ [] := by
    simp [kernelOddScheduleLeft]
  have left_cycle := shellPeriodicCycle left_ne
  have left_phases :
      ∀ front back,
        [] ++ kernelOddScheduleLeft pump ++ [] = front ++ back →
          IsUnit 5 (shellRun front (shellPeriodicPoint (kernelOddScheduleLeft pump))) := by
    simpa only [List.nil_append, List.append_nil] using left_cycle.2.2
  have right_phases :=
    (kernelOddScheduleContextGuard pump [] []
      (shellPeriodicPoint (kernelOddScheduleLeft pump))).mp left_phases
  dsimp only
  refine ⟨left_cycle.1, left_cycle.2.1, ?_, left_cycle.2.2, ?_⟩
  · rw [← shellRun_kernelOddSchedule]
    exact left_cycle.2.1
  simpa only [List.nil_append, List.append_nil] using right_phases

/-- Two-parameter boundary shift of the published relation's left schedule. -/
def benchmarkRelationShiftLeft (first last : ℕ) : List ℕ :=
  [10 + first, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 + last]

/-- Two-parameter boundary shift of the published relation's right schedule. -/
def benchmarkRelationShiftRight (first last : ℕ) : List ℕ :=
  [first, 0, 1, 2, 0, 2, 1, 1, 2, 0, 6, 0, last]

/-- Every boundary-shifted pair consists of distinct schedules. -/
theorem benchmarkRelationShift_ne (first last : ℕ) :
    benchmarkRelationShiftLeft first last ≠ benchmarkRelationShiftRight first last := by
  simp [benchmarkRelationShiftLeft, benchmarkRelationShiftRight]

/-- The shifted left schedule is the published raw rule in a `D^last _ D^first`
context, after the common shell-prefix `T`. -/
theorem shellRawWord_benchmarkRelationShiftLeft (first last : ℕ) :
    shellRawWord (benchmarkRelationShiftLeft first last) =
      [.translate] ++ List.replicate last .dilate ++ cassaigneLeft ++
        List.replicate first .dilate := by
  have last_wait :
      List.replicate (1 + last) Letter.dilate =
        List.replicate last .dilate ++ [.dilate] := by
    rw [Nat.add_comm, List.replicate_succ']
  have first_wait :
      List.replicate (10 + first) Letter.dilate =
        List.replicate 10 .dilate ++ List.replicate first .dilate := by
    rw [List.replicate_add]
  simp [shellRawWord, shellRawBlock, benchmarkRelationShiftLeft, cassaigneLeft,
    last_wait, first_wait]

/-- The shifted right schedule is the other side of the same contextual raw rule. -/
theorem shellRawWord_benchmarkRelationShiftRight (first last : ℕ) :
    shellRawWord (benchmarkRelationShiftRight first last) =
      [.translate] ++ List.replicate last .dilate ++ cassaigneRight ++
        List.replicate first .dilate := by
  simp [shellRawWord, shellRawBlock, benchmarkRelationShiftRight, cassaigneRight]

/-- Every boundary shift is one two-sided raw context of the published relation. -/
theorem shellRun_benchmarkRelationShift (first last : ℕ) (state : ℚ) :
    shellRun (benchmarkRelationShiftLeft first last) state =
      shellRun (benchmarkRelationShiftRight first last) state := by
  rw [shellRun_eq_wordAction, shellRun_eq_wordAction,
    shellRawWord_benchmarkRelationShiftLeft, shellRawWord_benchmarkRelationShiftRight]
  rw [wordAction_context wordAction_cassaigne]

/-- The benchmark relation remains an affine equality inside every schedule context. -/
theorem shellRun_benchmarkRelationContext
    (before after : List ℕ) (state : ℚ) :
    shellRun (before ++ benchmarkRelationLeft ++ after) state =
      shellRun (before ++ benchmarkRelationRight ++ after) state := by
  simp only [shellRun_append]
  rw [shellRun_benchmarkRelation]

/-- Every boundary-shifted relation remains an affine equality inside every schedule context. -/
theorem shellRun_benchmarkRelationShiftContext
    (first last : ℕ) (before after : List ℕ) (state : ℚ) :
    shellRun (before ++ benchmarkRelationShiftLeft first last ++ after) state =
      shellRun (before ++ benchmarkRelationShiftRight first last ++ after) state := by
  simp only [shellRun_append]
  rw [shellRun_benchmarkRelationShift]

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

/-- Contextual substitution of every boundary-shifted relation preserves every shell guard. -/
theorem benchmarkRelationShiftContextGuard
    (first last : ℕ) (before after : List ℕ) (state : ℚ) :
    (∀ front back,
      before ++ benchmarkRelationShiftLeft first last ++ after = front ++ back →
        IsUnit 5 (shellRun front state)) ↔
      ∀ front back,
        before ++ benchmarkRelationShiftRight first last ++ after = front ++ back →
          IsUnit 5 (shellRun front state) := by
  rw [shellPrefixesUnit_iff, shellPrefixesUnit_iff,
    shellRun_benchmarkRelationShiftContext]

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

/-- Every boundary-shifted relation has a common rational all-unit cycle. -/
theorem benchmarkRelationShiftCycle (first last : ℕ) :
    let left := benchmarkRelationShiftLeft first last
    let right := benchmarkRelationShiftRight first last
    let source := shellPeriodicPoint left
    IsUnit 5 source ∧
      shellRun left source = source ∧
      shellRun right source = source ∧
      (∀ front back, left = front ++ back → IsUnit 5 (shellRun front source)) ∧
      ∀ front back, right = front ++ back → IsUnit 5 (shellRun front source) := by
  have left_ne : benchmarkRelationShiftLeft first last ≠ [] := by
    simp [benchmarkRelationShiftLeft]
  have left_cycle := shellPeriodicCycle left_ne
  have right_phases :=
    (benchmarkRelationShiftContextGuard first last [] []
      (shellPeriodicPoint (benchmarkRelationShiftLeft first last))).mp left_cycle.2.2
  dsimp only
  refine ⟨left_cycle.1, left_cycle.2.1, ?_, left_cycle.2.2, ?_⟩
  · rw [← shellRun_benchmarkRelationShift]
    exact left_cycle.2.1
  simpa only [List.nil_append, List.append_nil] using right_phases

/-- One schedule expands its displacement from its unique periodic point by its exact affine
slope. -/
theorem shellRun_sub_periodicPoint
    {waits : List ℕ} (waits_ne : waits ≠ []) (state : ℚ) :
    shellRun waits state - shellPeriodicPoint waits =
      product (waits.map shellScale) / (5 : ℚ) ^ waits.length *
        (state - shellPeriodicPoint waits) := by
  have scales_ne : waits.map shellScale ≠ [] := by simpa using waits_ne
  have fixed := run_periodicPoint scales_ne (shellScales_unit waits)
  calc
    shellRun waits state - shellPeriodicPoint waits =
        run (waits.map shellScale) state -
          run (waits.map shellScale) (periodicPoint (waits.map shellScale)) := by
      rw [fixed]
      rfl
    _ = product (waits.map shellScale) / (5 : ℚ) ^ waits.length *
          (state - shellPeriodicPoint waits) := by
      rw [run_eq, run_eq]
      simp only [shellPeriodicPoint, List.length_map]
      ring

/-- Repeating one schedule multiplies displacement from its periodic point by the corresponding
power of the schedule slope. -/
theorem shellRun_repeat_sub_periodicPoint
    {waits : List ℕ} (waits_ne : waits ≠ []) (repetitions : ℕ) (state : ℚ) :
    shellRun (List.replicate repetitions waits).flatten state - shellPeriodicPoint waits =
      (product (waits.map shellScale) / (5 : ℚ) ^ waits.length) ^ repetitions *
        (state - shellPeriodicPoint waits) := by
  induction repetitions generalizing state with
  | zero => simp [shellRun, run]
  | succ repetitions induction =>
      rw [List.replicate_succ, List.flatten_cons, shellRun_append, induction,
        shellRun_sub_periodicPoint waits_ne, pow_succ]
      ring

/-- Away from the unique periodic point, every full repetition consumes exactly the schedule
length from the 5-adic valuation of the displacement. -/
theorem shellRun_repeat_sub_periodicPoint_value
    {waits : List ℕ} (waits_ne : waits ≠ []) (repetitions : ℕ) {state : ℚ}
    (state_ne : state ≠ shellPeriodicPoint waits) :
    padicValRat 5
        (shellRun (List.replicate repetitions waits).flatten state - shellPeriodicPoint waits) =
      padicValRat 5 (state - shellPeriodicPoint waits) - repetitions * waits.length := by
  let slope := product (waits.map shellScale) / (5 : ℚ) ^ waits.length
  have slope_value : HasValue 5 slope (-(waits.length : ℤ)) := by
    have numerator_unit := product_unit (waits.map shellScale) (shellScales_unit waits)
    have denominator_value : HasValue 5 ((5 : ℚ) ^ waits.length) waits.length :=
      primePower_hasValue waits.length
    simpa [slope] using div_hasValue numerator_unit denominator_value
  have displacement_ne : state - shellPeriodicPoint waits ≠ 0 := sub_ne_zero.mpr state_ne
  rw [shellRun_repeat_sub_periodicPoint waits_ne]
  change padicValRat 5 (slope ^ repetitions * (state - shellPeriodicPoint waits)) = _
  rw [padicValRat.mul (pow_ne_zero repetitions slope_value.1) displacement_ne,
    padicValRat.pow, slope_value.2]
  ring

/-- A rational source distinct from the periodic point can follow a repeated schedule inside the
unit shell only for the computable number of periods allowed by its initial displacement. -/
theorem shellRun_repeat_unit_bound
    {waits : List ℕ} (waits_ne : waits ≠ []) (repetitions : ℕ) {state : ℚ}
    (state_ne : state ≠ shellPeriodicPoint waits)
    (output_unit :
      IsUnit 5 (shellRun (List.replicate repetitions waits).flatten state)) :
    (repetitions * waits.length : ℤ) ≤
      padicValRat 5 (state - shellPeriodicPoint waits) := by
  have periodic_unit := (shellPeriodicCycle waits_ne).1
  have difference_ne :
      shellRun (List.replicate repetitions waits).flatten state -
          shellPeriodicPoint waits ≠ 0 := by
    rw [shellRun_repeat_sub_periodicPoint waits_ne]
    exact mul_ne_zero
      (pow_ne_zero repetitions (div_ne_zero
        (product_unit (waits.map shellScale) (shellScales_unit waits)).1
        (pow_ne_zero waits.length (by norm_num))))
      (sub_ne_zero.mpr state_ne)
  have difference_nonnegative :
      0 ≤ padicValRat 5
        (shellRun (List.replicate repetitions waits).flatten state -
          shellPeriodicPoint waits) := by
    have lower := min_le_sub (prime := 5) difference_ne
    rw [output_unit.2, periodic_unit.2] at lower
    exact lower
  rw [shellRun_repeat_sub_periodicPoint_value waits_ne repetitions
    state_ne] at difference_nonnegative
  omega

end MatrixMortality.PeriodicShell
