import MatrixMortality.Undecidability.CyclicTag
import MatrixMortality.Undecidability.TagExecution

/-!
# Avoidance through the one-hot cyclic-tag compiler

A two-tag execution whose read heads avoid one distinguished label compiles to a cyclic-tag
execution that avoids the corresponding true phase.  The second deleted two-tag symbol is
scanned in the empty half of the cyclic program, so it need not avoid the label.
-/

namespace MatrixMortality
namespace Undecidability
namespace CyclicTag

/-- One pulse-avoiding semantic step agrees with one executable cyclic-tag step. -/
theorem run_one_of_avoidingStep {period : Nat} {system : CyclicTag period}
    {haltPhase : Fin period} {before after : Config period}
    (step : FiringAvoidingStep system haltPhase before after) :
    system.run 1 before = some after := by
  cases step
  simp [run, next]

/-- Every pulse-avoiding semantic execution has an exact executable length. -/
theorem run_of_avoidingReaches {period : Nat} {system : CyclicTag period}
    {haltPhase : Fin period} {before after : Config period}
    (reach : system.FiringAvoidingReaches haltPhase before after) :
    ∃ steps, system.run steps before = some after := by
  induction reach with
  | refl => exact ⟨0, by simp [run]⟩
  | tail _ step ih =>
      obtain ⟨steps, execution⟩ := ih
      refine ⟨steps + 1, ?_⟩
      rw [run_add, execution]
      exact run_one_of_avoidingStep step

/-- A successful run advances the phase by exactly its transition count. -/
theorem phase_of_run {period : Nat} (system : CyclicTag period) (steps : Nat)
    (initial final : Config period) (execution : system.run steps initial = some final) :
    final.phase = shift initial.phase steps := by
  induction steps generalizing initial with
  | zero =>
      have initial_eq : initial = final := by
        simpa [run] using Option.some.inj execution
      subst final
      simp
  | succ steps ih =>
      obtain ⟨data, phase⟩ := initial
      cases data with
      | nil => simp [run, next] at execution
      | cons value tail =>
          let successor : Config period :=
            { data := tail ++ if value then system.appendant phase else []
              phase := shift phase 1 }
          have remaining : system.run steps successor = some final := by
            simpa [run, next, successor] using execution
          rw [ih successor remaining]
          simp [successor, shift_add, Nat.add_comm]

/-- A false prefix advances the program without emitting data or firing any phase. -/
theorem avoiding_false_run {period : Nat} (system : CyclicTag period)
    (haltPhase phase : Fin period) (count : Nat) (tail : List Bool) :
    system.FiringAvoidingReaches haltPhase
      { data := List.replicate count false ++ tail, phase }
      { data := tail, phase := shift phase count } := by
  induction count generalizing phase with
  | zero =>
      simpa using
        (Relation.ReflTransGen.refl :
          system.FiringAvoidingReaches haltPhase
            { data := tail, phase } { data := tail, phase })
  | succ count ih =>
      apply Relation.ReflTransGen.head
      · simpa [List.replicate_succ] using
          (FiringAvoidingStep.advance phase false
            (List.replicate count false ++ tail) (by simp))
      · simpa [List.replicate_succ, shift_add, Nat.add_comm] using
          ih (shift phase 1)

theorem discharge_oneHot_eq {period alphabet : Nat} (system : CyclicTag period)
    (phase : Fin period) (symbol : Fin alphabet) :
    system.discharge phase (oneHot symbol) =
      system.appendant (shift phase symbol) := by
  rw [oneHot, discharge_append, discharge_false_replicate]
  simp only [List.nil_append, List.length_replicate, discharge]
  rw [show shift phase symbol.val = shift phase symbol from rfl]
  simp [discharge_false_replicate]

/-- The last position of a non-last one-hot codeword is false. -/
theorem oneHot_drop_last_of_ne {alphabet : Nat} (target head : Fin alphabet)
    (target_last : target.val + 1 = alphabet) (head_ne : head ≠ target) :
    (oneHot head).drop target.val = [false] := by
  have head_lt : head.val < target.val := by
    have := head.isLt
    omega
  let gap := target.val - head.val
  have gap_pos : 0 < gap := Nat.sub_pos_of_lt head_lt
  have target_eq : target.val = head.val + gap := by
    simp [gap]
    omega
  have suffix_eq : alphabet - head.val - 1 = gap := by
    simp [gap]
    omega
  rw [target_eq, oneHot, suffix_eq]
  rw [show head.val + gap = (List.replicate head.val false).length + gap by simp]
  rw [List.drop_append]
  obtain ⟨smaller, gap_eq⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt gap_pos)
  rw [gap_eq]
  simp

/-- The last position of the last-labelled one-hot codeword is true. -/
theorem oneHot_drop_last {alphabet : Nat} (target : Fin alphabet)
    (target_last : target.val + 1 = alphabet) :
    (oneHot target).drop target.val = [true] := by
  have suffix_zero : alphabet - target.val - 1 = 0 := by omega
  simp [oneHot, suffix_zero]

/-- One one-hot codeword is pulse-free when its unique true phase is not distinguished. -/
theorem avoiding_oneHot {period alphabet : Nat} (system : CyclicTag period)
    (haltPhase phase : Fin period) (symbol : Fin alphabet) (tail : List Bool)
    (true_phase_ne : shift phase symbol ≠ haltPhase) :
    system.FiringAvoidingReaches haltPhase
      { data := oneHot symbol ++ tail, phase := phase }
      { data := tail ++ system.discharge phase (oneHot symbol),
        phase := shift phase alphabet } := by
  let suffixLength := alphabet - symbol - 1
  have frontReach :=
    avoiding_false_run system haltPhase phase symbol.val
      (true :: List.replicate suffixLength false ++ tail)
  have pulseStep : FiringAvoidingStep system haltPhase
      { data := true :: List.replicate suffixLength false ++ tail,
        phase := shift phase symbol }
      { data :=
          (List.replicate suffixLength false ++ tail) ++
            system.appendant (shift phase symbol),
        phase := shift (shift phase symbol) 1 } := by
    exact .advance (shift phase symbol) true
      (List.replicate suffixLength false ++ tail) fun _ => true_phase_ne
  have suffixReach :=
    avoiding_false_run system haltPhase (shift (shift phase symbol) 1) suffixLength
      (tail ++ system.appendant (shift phase symbol))
  apply Relation.ReflTransGen.trans
    (b :=
      { data := true :: List.replicate suffixLength false ++ tail,
        phase := shift phase symbol })
  · simpa [oneHot, suffixLength] using frontReach
  · apply Relation.ReflTransGen.head pulseStep
    have phase_eq :
        shift (shift (shift phase symbol) 1) suffixLength = shift phase alphabet := by
      rw [shift_add, shift_add]
      congr 1
      simp [suffixLength]
      omega
    simpa [List.append_assoc, phase_eq, discharge_oneHot_eq] using suffixReach

private theorem first_half_phase_ne {alphabet : Nat} (alphabet_nonempty : 0 < alphabet)
    {head target : Fin alphabet} (head_ne : head ≠ target) :
    shift (initialPhase alphabet_nonempty) head ≠
      shift (initialPhase alphabet_nonempty) target := by
  intro equality
  apply head_ne
  apply Fin.ext
  have values := congrArg Fin.val equality
  have head_value :
      (shift (initialPhase alphabet_nonempty) head).val = head.val :=
    shift_initial_val alphabet_nonempty (by omega)
  have target_value :
      (shift (initialPhase alphabet_nonempty) target).val = target.val :=
    shift_initial_val alphabet_nonempty (by omega)
  rw [head_value, target_value] at values
  exact values

private theorem second_half_phase_ne {alphabet : Nat} (alphabet_nonempty : 0 < alphabet)
    (wake target : Fin alphabet) :
    shift (shift (initialPhase alphabet_nonempty) alphabet) wake ≠
      shift (initialPhase alphabet_nonempty) target := by
  intro equality
  have values := congrArg Fin.val equality
  rw [shift_add] at values
  have first_value :
      (shift (initialPhase alphabet_nonempty) (alphabet + wake)).val =
        alphabet + wake := shift_initial_val alphabet_nonempty (by omega)
  have target_value :
      (shift (initialPhase alphabet_nonempty) target).val =
        target := shift_initial_val alphabet_nonempty (by omega)
  rw [first_value, target_value] at values
  omega

/-- One head-avoiding two-tag step compiles to one pulse-avoiding cyclic program cycle. -/
theorem simulate_avoiding_step {alphabet : Nat} (system : TwoTag alphabet)
    (alphabet_nonempty : 0 < alphabet) (target head wake : Fin alphabet)
    (tail : List (Fin alphabet)) (head_ne : head ≠ target) :
    (ofTwoTag system).FiringAvoidingReaches
      (shift (initialPhase alphabet_nonempty) target)
      { data := encodeWord (head :: wake :: tail),
        phase := initialPhase alphabet_nonempty }
      { data := encodeWord (tail ++ system.production head),
        phase := initialPhase alphabet_nonempty } := by
  have first :=
    avoiding_oneHot (ofTwoTag system)
      (shift (initialPhase alphabet_nonempty) target)
      (initialPhase alphabet_nonempty) head
      (oneHot wake ++ encodeWord tail)
      (first_half_phase_ne alphabet_nonempty head_ne)
  have second :=
    avoiding_oneHot (ofTwoTag system)
      (shift (initialPhase alphabet_nonempty) target)
      (shift (initialPhase alphabet_nonempty) alphabet) wake
      (encodeWord tail ++ encodeWord (system.production head))
      (second_half_phase_ne alphabet_nonempty wake target)
  apply Relation.ReflTransGen.trans
    (b :=
      { data := oneHot wake ++ encodeWord tail ++ encodeWord (system.production head),
        phase := shift (initialPhase alphabet_nonempty) alphabet })
  · simpa [discharge_oneHot_first, List.append_assoc] using first
  · simpa [discharge_oneHot_second, shift_add, shift_initial_period,
      encodeWord_append, List.append_assoc] using second

/-- Every head-avoiding two-tag execution compiles to a pulse-avoiding cyclic execution. -/
theorem simulate_avoiding_reaches {alphabet : Nat} (system : TwoTag alphabet)
    (alphabet_nonempty : 0 < alphabet) (target : Fin alphabet)
    {before after : List (Fin alphabet)}
    (reach : system.HeadAvoidingReaches target before after) :
    (ofTwoTag system).FiringAvoidingReaches
      (shift (initialPhase alphabet_nonempty) target)
      { data := encodeWord before, phase := initialPhase alphabet_nonempty }
      { data := encodeWord after, phase := initialPhase alphabet_nonempty } := by
  induction reach with
  | refl => exact Relation.ReflTransGen.refl
  | @tail middle after reach step ih =>
      obtain ⟨head, wake, tail, head_ne, rfl, rfl⟩ :=
        (TwoTag.avoidingStep_iff system target middle after).mp step
      exact ih.trans
        (simulate_avoiding_step system alphabet_nonempty target head wake tail head_ne)

/-- Complete cyclic program cycles either expose a two-tag halt or mirror two-tag reachability. -/
theorem run_cycles_reflects {alphabet : Nat} (system : TwoTag alphabet)
    (alphabet_nonempty : 0 < alphabet) (cycles : Nat)
    (before : List (Fin alphabet)) (final : Config (alphabet + alphabet))
    (execution :
      (ofTwoTag system).run (cycles * (alphabet + alphabet))
          { data := encodeWord before, phase := initialPhase alphabet_nonempty } =
        some final) :
    TagHaltsFrom 2 system.production before ∨
      ∃ after,
        system.QueueReaches before after ∧
          final =
            { data := encodeWord after
              phase := initialPhase alphabet_nonempty } := by
  induction cycles generalizing before with
  | zero =>
      exact Or.inr ⟨before, Relation.ReflTransGen.refl, by simpa [run] using execution.symm⟩
  | succ cycles ih =>
      rw [show (cycles + 1) * (alphabet + alphabet) =
          (alphabet + alphabet) + cycles * (alphabet + alphabet) by
        simp [Nat.add_mul, Nat.add_comm],
        run_add] at execution
      cases before with
      | nil => exact Or.inl (.stop (by simp))
      | cons head rest =>
          cases rest with
          | nil => exact Or.inl (.stop (by simp))
          | cons wake tail =>
              rw [simulate_step system alphabet_nonempty head wake tail] at execution
              rcases ih (tail ++ system.production head) execution with
                laterHalts | ⟨after, laterReach, final_eq⟩
              · exact Or.inl (.step (system.step_cons_cons head wake tail) laterHalts)
              · exact Or.inr
                  ⟨after,
                    Relation.ReflTransGen.head
                      (system.step_cons_cons head wake tail) laterReach,
                    final_eq⟩

/-- A distinguished last-phase pulse reflects either two-tag halting or the target head. -/
theorem avoiding_firing_reflects {alphabet : Nat} (system : TwoTag alphabet)
    (alphabet_nonempty : 0 < alphabet) (target : Fin alphabet)
    (target_last : target.val + 1 = alphabet)
    (initial : List (Fin alphabet)) (firing : Config (alphabet + alphabet))
    (reach :
      (ofTwoTag system).FiringAvoidingReaches
        (shift (initialPhase alphabet_nonempty) target)
        { data := encodeWord initial, phase := initialPhase alphabet_nonempty }
        firing)
    (fires : FiresAt (shift (initialPhase alphabet_nonempty) target) firing) :
    TagHaltsFrom 2 system.production initial ∨ system.CanReachHead initial target := by
  obtain ⟨steps, execution⟩ := run_of_avoidingReaches reach
  obtain ⟨firingTail, firingData, firingPhase⟩ := fires
  have runPhase := phase_of_run (ofTwoTag system) steps _ _ execution
  have phase_eq :
      shift (initialPhase alphabet_nonempty) steps =
        shift (initialPhase alphabet_nonempty) target := runPhase.symm.trans firingPhase
  have steps_mod : steps % (alphabet + alphabet) = target.val := by
    have values := congrArg Fin.val phase_eq
    have target_mod :
        target.val % (alphabet + alphabet) = target.val :=
      Nat.mod_eq_of_lt <| target.isLt.trans <| by omega
    simpa [shift, initialPhase, target_mod] using values
  let cycles := steps / (alphabet + alphabet)
  have steps_eq :
      steps = cycles * (alphabet + alphabet) + target.val := by
    have division := Nat.mod_add_div steps (alphabet + alphabet)
    rw [steps_mod] at division
    simp only [cycles]
    calc
      steps = target.val + (alphabet + alphabet) * (steps / (alphabet + alphabet)) :=
        division.symm
      _ = (steps / (alphabet + alphabet)) * (alphabet + alphabet) + target.val := by
        ac_rfl
  rw [steps_eq, run_add] at execution
  cases fullExecution :
      (ofTwoTag system).run (cycles * (alphabet + alphabet))
        { data := encodeWord initial, phase := initialPhase alphabet_nonempty } with
  | none => simp [fullExecution] at execution
  | some boundary =>
      have prefixExecution :
          (ofTwoTag system).run (cycles * (alphabet + alphabet))
              { data := encodeWord initial, phase := initialPhase alphabet_nonempty } =
            some boundary := fullExecution
      have suffixExecution :
          (ofTwoTag system).run target.val boundary = some firing := by
        simpa [fullExecution] using execution
      rcases run_cycles_reflects system alphabet_nonempty cycles initial boundary
          prefixExecution with
        initialHalts | ⟨after, tagReach, boundary_eq⟩
      · exact Or.inl initialHalts
      · subst boundary
        cases after with
        | nil =>
            exact Or.inl <| tagHaltsFrom_of_reaches tagReach (.stop (by simp))
        | cons head rest =>
            have frontLength :
                ((oneHot head).take target.val).length = target.val := by
              simp [List.length_take, oneHot_length,
                Nat.min_eq_left (Nat.le_of_lt target.isLt)]
            have split :
                (oneHot head).take target.val ++
                    ((oneHot head).drop target.val ++ encodeWord rest) =
                  encodeWord (head :: rest) := by
              rw [← List.append_assoc, List.take_append_drop]
              rfl
            have prefixRun :=
              run_prefix (ofTwoTag system) (initialPhase alphabet_nonempty)
                ((oneHot head).take target.val)
                ((oneHot head).drop target.val ++ encodeWord rest)
            rw [frontLength, split] at prefixRun
            rw [prefixRun] at suffixExecution
            have final_eq :
                { data :=
                    ((oneHot head).drop target.val ++ encodeWord rest) ++
                      (ofTwoTag system).discharge (initialPhase alphabet_nonempty)
                        ((oneHot head).take target.val)
                  phase := shift (initialPhase alphabet_nonempty) target.val } =
                  firing :=
              Option.some.inj suffixExecution
            have head_eq : head = target := by
              by_contra head_ne
              have falseHead : firing.data.head? = some false := by
                rw [← final_eq]
                rw [oneHot_drop_last_of_ne target head target_last head_ne]
                rfl
              have trueHead : firing.data.head? = some true := by
                rw [firingData]
                rfl
              rw [trueHead] at falseHead
              contradiction
            subst head
            exact Or.inr ⟨rest, tagReach⟩

/-- A last-labelled singleton queue reaches its exact true pulse through only false bits. -/
theorem avoiding_reaches_last_firing {alphabet : Nat} (system : TwoTag alphabet)
    (alphabet_nonempty : 0 < alphabet) (target : Fin alphabet)
    (target_last : target.val + 1 = alphabet) (initial : List (Fin alphabet))
    (reach : system.HeadAvoidingReaches target initial [target]) :
    (ofTwoTag system).FiringAvoidingReaches
      (shift (initialPhase alphabet_nonempty) target)
      { data := encodeWord initial, phase := initialPhase alphabet_nonempty }
      { data := [true], phase := shift (initialPhase alphabet_nonempty) target } := by
  have compiled := simulate_avoiding_reaches system alphabet_nonempty target reach
  have final :=
    avoiding_false_run (ofTwoTag system)
      (shift (initialPhase alphabet_nonempty) target)
      (initialPhase alphabet_nonempty) target.val [true]
  apply compiled.trans
  have suffix_zero : alphabet - target.val - 1 = 0 := by omega
  simpa [oneHot, suffix_zero] using final

end CyclicTag
end Undecidability
end MatrixMortality
