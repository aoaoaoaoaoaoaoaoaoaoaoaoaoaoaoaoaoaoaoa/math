import MatrixMortality.TagQueue

/-!
# Two-tag systems and cyclic tag systems

This file gives a phase-indexed cyclic-tag semantics and the one-hot compiler from a two-tag
system.  Appendant phases are represented by `Fin`; an out-of-range phase is therefore not a
configuration.  The central prefix theorem evaluates an arbitrary complete data prefix, after
which one two-tag step reduces to two applications of that theorem.
-/

namespace MatrixMortality
namespace Undecidability

/-- A two-tag system over an alphabet of cardinality `alphabet`. -/
structure TwoTag (alphabet : Nat) where
  /-- Word appended when the deleted head has the selected label. -/
  production : Fin alphabet → List (Fin alphabet)

namespace TwoTag

/-- One two-tag transition, using the generic fixed-width queue semantics. -/
def Step {alphabet : Nat} (system : TwoTag alphabet) :
    List (Fin alphabet) → List (Fin alphabet) → Prop :=
  TagStep 2 system.production

/-- Reflexive-transitive two-tag reachability. -/
def Reaches {alphabet : Nat} (system : TwoTag alphabet) :
    List (Fin alphabet) → List (Fin alphabet) → Prop :=
  Relation.ReflTransGen system.Step

theorem step_cons_cons {alphabet : Nat} (system : TwoTag alphabet)
    (head wake : Fin alphabet) (tail : List (Fin alphabet)) :
    system.Step (head :: wake :: tail) (tail ++ system.production head) := by
  refine ⟨⟨head, [wake], rfl⟩, tail, rfl, rfl⟩

theorem step_iff {alphabet : Nat} (system : TwoTag alphabet) (before after : List (Fin alphabet)) :
    system.Step before after ↔
      ∃ head wake tail,
        before = head :: wake :: tail ∧ after = tail ++ system.production head := by
  constructor
  · rintro ⟨⟨head, wake, width⟩, tail, before_eq, after_eq⟩
    have wake_length : wake.length = 1 := by omega
    obtain ⟨wakeHead, rfl⟩ := List.length_eq_one.mp wake_length
    exact ⟨head, wakeHead, tail, before_eq, after_eq⟩
  · rintro ⟨head, wake, tail, rfl, rfl⟩
    exact system.step_cons_cons head wake tail

/-- Reachability of a word with a selected first symbol. -/
def ReachesHead {alphabet : Nat} (system : TwoTag alphabet)
    (initial : List (Fin alphabet)) (symbol : Fin alphabet) : Prop :=
  ∃ tail, system.Reaches initial (symbol :: tail)

end TwoTag

/-- A cyclic tag system with an intrinsically bounded phase. -/
structure CyclicTag (period : Nat) where
  /-- Binary word attached to each program phase. -/
  appendant : Fin period → List Bool

namespace CyclicTag

/-- A cyclic-tag configuration consists of a dataword and a valid program phase. -/
structure Config (period : Nat) where
  /-- Current binary queue. -/
  data : List Bool
  /-- Current cyclic program position. -/
  phase : Fin period
  deriving DecidableEq

/-- Add an arbitrary displacement to a cyclic phase. -/
def shift {period : Nat} (phase : Fin period) (displacement : Nat) : Fin period :=
  ⟨(phase + displacement) % period, Nat.mod_lt _ (Nat.zero_lt_of_lt phase.isLt)⟩

@[simp]
theorem shift_zero {period : Nat} (phase : Fin period) : shift phase 0 = phase := by
  apply Fin.ext
  simp [shift, Nat.mod_eq_of_lt phase.isLt]

theorem shift_add {period : Nat} (phase : Fin period) (m n : Nat) :
    shift (shift phase m) n = shift phase (m + n) := by
  apply Fin.ext
  simp only [shift, Fin.val_mk]
  calc
    ((phase.val + m) % period + n) % period = ((phase.val + m) + n) % period := by
      rw [Nat.add_mod]
      simp only [Nat.mod_mod]
      rw [← Nat.add_mod]
    _ = (phase.val + (m + n)) % period := by rw [Nat.add_assoc]

@[simp]
theorem shift_period {period : Nat} (phase : Fin period) : shift phase period = phase := by
  apply Fin.ext
  simp [shift, Nat.add_mod, Nat.mod_eq_of_lt phase.isLt]

/-- Execute one cyclic-tag transition, or halt on the empty dataword. -/
def next {period : Nat} (system : CyclicTag period) : Config period → Option (Config period)
  | ⟨[], _⟩ => none
  | ⟨bit :: tail, phase⟩ =>
      some
        { data := tail ++ if bit then system.appendant phase else []
          phase := shift phase 1 }

/-- Execute exactly `steps` transitions, failing if the dataword becomes empty too soon. -/
def run {period : Nat} (system : CyclicTag period) : Nat → Config period → Option (Config period)
  | 0, config => some config
  | steps + 1, config => system.next config >>= system.run steps

theorem run_add {period : Nat} (system : CyclicTag period) (m n : Nat)
    (config : Config period) :
    system.run (m + n) config = system.run m config >>= system.run n := by
  induction m generalizing config with
  | zero => simp [run]
  | succ m ih =>
      simp only [Nat.succ_add, run]
      cases system.next config with
      | none => rfl
      | some next => exact ih next

/-- Appendant output generated while consuming a fixed data prefix. -/
def discharge {period : Nat} (system : CyclicTag period) :
    Fin period → List Bool → List Bool
  | _, [] => []
  | phase, bit :: bits =>
      (if bit then system.appendant phase else []) ++
        system.discharge (shift phase 1) bits

/-- Consuming a complete prefix cannot inspect output appended by that prefix. -/
theorem run_prefix {period : Nat} (system : CyclicTag period) (phase : Fin period)
    (front tail : List Bool) :
    system.run front.length { data := front ++ tail, phase } =
      some
        { data := tail ++ system.discharge phase front
          phase := shift phase front.length } := by
  induction front generalizing phase tail with
  | nil => simp [run, discharge]
  | cons bit front ih =>
      change system.run front.length
          { data := (front ++ tail) ++ if bit then system.appendant phase else []
            phase := shift phase 1 } = _
      rw [show (front ++ tail) ++ (if bit then system.appendant phase else []) =
          front ++ (tail ++ if bit then system.appendant phase else []) by
        simp [List.append_assoc]]
      rw [ih]
      congr 1
      simp [discharge, List.append_assoc, shift_add, Nat.add_comm]

/-- Discharge is a phase-indexed list morphism. -/
theorem discharge_append {period : Nat} (system : CyclicTag period) (phase : Fin period)
    (left right : List Bool) :
    system.discharge phase (left ++ right) =
      system.discharge phase left ++ system.discharge (shift phase left.length) right := by
  induction left generalizing phase with
  | nil => simp [discharge]
  | cons bit left ih =>
      simp only [List.cons_append, List.length_cons, discharge]
      change (if bit then system.appendant phase else []) ++
          system.discharge (shift phase 1) (left ++ right) = _
      rw [ih (shift phase 1)]
      simp only [List.append_assoc]
      congr 1
      rw [show shift (shift phase 1) left.length = shift phase (left.length + 1) by
        simpa [Nat.add_comm] using shift_add phase 1 left.length]

theorem discharge_false_replicate {period : Nat} (system : CyclicTag period)
    (phase : Fin period) (length : Nat) :
    system.discharge phase (List.replicate length false) = [] := by
  induction length generalizing phase with
  | zero => rfl
  | succ length ih => simp [discharge, ih]

/-- One-hot encoding with the selected bit exposed between two false runs. -/
def oneHot {alphabet : Nat} (symbol : Fin alphabet) : List Bool :=
  List.replicate symbol false ++ true :: List.replicate (alphabet - symbol - 1) false

@[simp]
theorem oneHot_length {alphabet : Nat} (symbol : Fin alphabet) :
    (oneHot symbol).length = alphabet := by
  simp [oneHot]
  omega

/-- Extend the one-hot code morphically to tag words. -/
def encodeWord {alphabet : Nat} (word : List (Fin alphabet)) : List Bool :=
  (word.map oneHot).join

@[simp]
theorem encodeWord_nil {alphabet : Nat} : encodeWord ([] : List (Fin alphabet)) = [] := rfl

@[simp]
theorem encodeWord_cons {alphabet : Nat} (symbol : Fin alphabet)
    (word : List (Fin alphabet)) :
    encodeWord (symbol :: word) = oneHot symbol ++ encodeWord word := rfl

theorem encodeWord_append {alphabet : Nat} (left right : List (Fin alphabet)) :
    encodeWord (left ++ right) = encodeWord left ++ encodeWord right := by
  simp [encodeWord, List.map_append]

/-- Cook's compiler: production appendants followed by one empty phase per alphabet symbol. -/
def ofTwoTag {alphabet : Nat} (system : TwoTag alphabet) : CyclicTag (alphabet + alphabet) where
  appendant phase :=
    if inFirstHalf : phase < alphabet then
      encodeWord (system.production ⟨phase, inFirstHalf⟩)
    else
      []

/-- Initial cyclic-tag phase. -/
def initialPhase {alphabet : Nat} (alphabet_nonempty : 0 < alphabet) : Fin (alphabet + alphabet) :=
  ⟨0, by omega⟩

theorem shift_initial_val {alphabet displacement : Nat} (alphabet_nonempty : 0 < alphabet)
    (displacement_lt : displacement < alphabet + alphabet) :
    (shift (initialPhase alphabet_nonempty) displacement).val = displacement := by
  simp [shift, initialPhase, Nat.mod_eq_of_lt displacement_lt]

theorem shift_initial_alphabet {alphabet : Nat} (alphabet_nonempty : 0 < alphabet) :
    shift (initialPhase alphabet_nonempty) alphabet = ⟨alphabet, by omega⟩ := by
  apply Fin.ext
  exact shift_initial_val alphabet_nonempty (by omega)

theorem shift_initial_period {alphabet : Nat} (alphabet_nonempty : 0 < alphabet) :
    shift (initialPhase alphabet_nonempty) (alphabet + alphabet) =
      initialPhase alphabet_nonempty := by
  apply Fin.ext
  simp [shift, initialPhase]

theorem ofTwoTag_appendant_first {alphabet : Nat} (system : TwoTag alphabet)
    (alphabet_nonempty : 0 < alphabet) (symbol : Fin alphabet) :
    (ofTwoTag system).appendant (shift (initialPhase alphabet_nonempty) symbol) =
      encodeWord (system.production symbol) := by
  rw [ofTwoTag]
  simp only
  have shifted : (shift (initialPhase alphabet_nonempty) symbol).val = symbol :=
    shift_initial_val alphabet_nonempty (by omega)
  split
  · congr
  · rename_i outside
    exact False.elim (outside (shifted.symm ▸ symbol.isLt))

theorem ofTwoTag_appendant_second {alphabet : Nat} (system : TwoTag alphabet)
    (alphabet_nonempty : 0 < alphabet) (symbol : Fin alphabet) :
    (ofTwoTag system).appendant
        (shift (shift (initialPhase alphabet_nonempty) alphabet) symbol) = [] := by
  rw [ofTwoTag]
  simp only
  split
  · rename_i inside
    have phase_value :
        (shift (shift (initialPhase alphabet_nonempty) alphabet) symbol).val =
          alphabet + symbol := by
      rw [shift_add]
      exact shift_initial_val alphabet_nonempty (by omega)
    omega
  · rfl

theorem discharge_oneHot_first {alphabet : Nat} (system : TwoTag alphabet)
    (alphabet_nonempty : 0 < alphabet) (symbol : Fin alphabet) :
    (ofTwoTag system).discharge (initialPhase alphabet_nonempty) (oneHot symbol) =
      encodeWord (system.production symbol) := by
  rw [oneHot, discharge_append]
  simp only [discharge_false_replicate, List.nil_append, List.length_replicate, discharge]
  rw [show shift (initialPhase alphabet_nonempty) symbol.val =
      shift (initialPhase alphabet_nonempty) symbol from rfl]
  rw [ofTwoTag_appendant_first system alphabet_nonempty symbol]
  simp [discharge_false_replicate]

theorem discharge_oneHot_second {alphabet : Nat} (system : TwoTag alphabet)
    (alphabet_nonempty : 0 < alphabet) (symbol : Fin alphabet) :
    (ofTwoTag system).discharge (shift (initialPhase alphabet_nonempty) alphabet)
        (oneHot symbol) = [] := by
  rw [oneHot, discharge_append]
  simp only [discharge_false_replicate, List.nil_append, List.length_replicate, discharge]
  rw [show shift (shift (initialPhase alphabet_nonempty) alphabet) symbol.val =
      shift (shift (initialPhase alphabet_nonempty) alphabet) symbol from rfl]
  rw [ofTwoTag_appendant_second system alphabet_nonempty symbol]
  simp [discharge_false_replicate]

theorem run_oneHot_first {alphabet : Nat} (system : TwoTag alphabet)
    (alphabet_nonempty : 0 < alphabet) (symbol : Fin alphabet) (tail : List Bool) :
    (ofTwoTag system).run alphabet
        { data := oneHot symbol ++ tail
          phase := initialPhase alphabet_nonempty } =
      some
        { data := tail ++ encodeWord (system.production symbol)
          phase := shift (initialPhase alphabet_nonempty) alphabet } := by
  simpa only [oneHot_length, discharge_oneHot_first] using
    run_prefix (ofTwoTag system) (initialPhase alphabet_nonempty) (oneHot symbol) tail

theorem run_oneHot_second {alphabet : Nat} (system : TwoTag alphabet)
    (alphabet_nonempty : 0 < alphabet) (symbol : Fin alphabet) (tail : List Bool) :
    (ofTwoTag system).run alphabet
        { data := oneHot symbol ++ tail
          phase := shift (initialPhase alphabet_nonempty) alphabet } =
      some
        { data := tail
          phase := initialPhase alphabet_nonempty } := by
  simpa only [oneHot_length, discharge_oneHot_second, List.append_nil, shift_add,
      shift_initial_period] using
    run_prefix (ofTwoTag system) (shift (initialPhase alphabet_nonempty) alphabet)
      (oneHot symbol) tail

/-- One two-tag step is exactly one complete cycle of the compiled cyclic tag system. -/
theorem simulate_step {alphabet : Nat} (system : TwoTag alphabet)
    (alphabet_nonempty : 0 < alphabet) (head wake : Fin alphabet)
    (tail : List (Fin alphabet)) :
    (ofTwoTag system).run (alphabet + alphabet)
        { data := encodeWord (head :: wake :: tail)
          phase := initialPhase alphabet_nonempty } =
      some
        { data := encodeWord (tail ++ system.production head)
          phase := initialPhase alphabet_nonempty } := by
  rw [run_add]
  rw [show encodeWord (head :: wake :: tail) =
      oneHot head ++ (oneHot wake ++ encodeWord tail) by rfl]
  rw [run_oneHot_first]
  rw [show (oneHot wake ++ encodeWord tail) ++ encodeWord (system.production head) =
      oneHot wake ++ (encodeWord tail ++ encodeWord (system.production head)) by
    simp [List.append_assoc]]
  change (ofTwoTag system).run alphabet
      { data := oneHot wake ++ (encodeWord tail ++ encodeWord (system.production head))
        phase := shift (initialPhase alphabet_nonempty) alphabet } = _
  rw [run_oneHot_second]
  congr 1
  rw [encodeWord_append]

/-- Any finite two-tag execution is simulated by the corresponding number of complete cycles. -/
theorem simulate_reaches {alphabet : Nat} (system : TwoTag alphabet)
    (alphabet_nonempty : 0 < alphabet) {before after : List (Fin alphabet)}
    (reach : system.Reaches before after) :
    ∃ steps,
      (ofTwoTag system).run (steps * (alphabet + alphabet))
          { data := encodeWord before
            phase := initialPhase alphabet_nonempty } =
        some
          { data := encodeWord after
            phase := initialPhase alphabet_nonempty } := by
  induction reach with
  | refl => exact ⟨0, by simp [run]⟩
  | @tail middle after reach step ih =>
      obtain ⟨steps, hsteps⟩ := ih
      obtain ⟨head, wake, tail, rfl, rfl⟩ := (TwoTag.step_iff system middle after).mp step
      refine ⟨steps + 1, ?_⟩
      rw [show (steps + 1) * (alphabet + alphabet) =
          steps * (alphabet + alphabet) + (alphabet + alphabet) by ring]
      rw [run_add, hsteps]
      exact simulate_step system alphabet_nonempty head wake tail

/-- Stop immediately before the unique true pulse in one one-hot codeword. -/
theorem run_oneHot_to_pulse {alphabet : Nat} (system : TwoTag alphabet)
    (alphabet_nonempty : 0 < alphabet) (symbol : Fin alphabet) (tail : List Bool) :
    (ofTwoTag system).run symbol.val
        { data := oneHot symbol ++ tail
          phase := initialPhase alphabet_nonempty } =
      some
        { data := true :: List.replicate (alphabet - symbol - 1) false ++ tail
          phase := shift (initialPhase alphabet_nonempty) symbol } := by
  rw [oneHot, List.append_assoc]
  have pulse := run_prefix (ofTwoTag system) (initialPhase alphabet_nonempty)
    (List.replicate symbol false)
    (true :: List.replicate (alphabet - symbol - 1) false ++ tail)
  rw [discharge_false_replicate] at pulse
  simpa [List.append_assoc] using pulse

/-- Reaching a selected two-tag head reaches its firing phase in the compiled cyclic system. -/
theorem reaches_firing_phase {alphabet : Nat} (system : TwoTag alphabet)
    (alphabet_nonempty : 0 < alphabet) (initial : List (Fin alphabet))
    (symbol : Fin alphabet) (reach : system.ReachesHead initial symbol) :
    ∃ steps tail,
      (ofTwoTag system).run steps
          { data := encodeWord initial
            phase := initialPhase alphabet_nonempty } =
        some
          { data := true :: tail
            phase := shift (initialPhase alphabet_nonempty) symbol } := by
  obtain ⟨wordTail, hreach⟩ := reach
  obtain ⟨cycles, hcycles⟩ := simulate_reaches system alphabet_nonempty hreach
  refine ⟨cycles * (alphabet + alphabet) + symbol.val,
    List.replicate (alphabet - symbol - 1) false ++ encodeWord wordTail, ?_⟩
  rw [run_add, hcycles]
  exact run_oneHot_to_pulse system alphabet_nonempty symbol (encodeWord wordTail)

end CyclicTag
end Undecidability
end MatrixMortality
