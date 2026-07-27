import MatrixMortality.Undecidability.NearyExecution

/-!
# No-spurious-halting converse for Neary's compiler

Positive versions of the semantic traversals expose strict progress between macro boundaries.
They rule out finite halting while the compiler remains in its garbage reserve and recover a
distinguished cyclic firing from every halting restricted-tag execution.
-/

namespace MatrixMortality.Undecidability.NearyCompiler

/-- A queue at a garbage-only semantic boundary retains two complete garbage atoms. -/
def GarbageBoundary {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) (queue : List TagLetter) : Prop :=
  ∃ instruction : Fin period, ∃ code : List JunkAtom,
    2 ≤ code.length ∧ queue =
      (encodeJunk system input haltPhase period_pos code).drop
        (objectEntryPhase instruction).val

/-- A garbage-only semantic boundary always reaches another such boundary nontrivially. -/
theorem GarbageBoundary.progress {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase : Fin period) (period_pos : 0 < period)
    {queue : List TagLetter}
    (boundary : GarbageBoundary system input haltPhase period_pos queue) :
    ∃ next,
      GarbageBoundary system input haltPhase period_pos next ∧
        Relation.TransGen
          (TagStep (deletionWidth period)
            (compiledOutput system input haltPhase period_pos))
  queue next := by
  obtain ⟨instruction, code, reserve, rfl⟩ := boundary
  have code_nonempty : code ≠ [] := by
    intro code_empty
    subst code
    simp at reserve
  obtain ⟨atom, restCode, rfl⟩ := List.exists_cons_of_ne_nil code_nonempty
  have restCode_nonempty : restCode ≠ [] := by
    intro rest_empty
    subst restCode
    simp at reserve
  let rest := encodeJunk system input haltPhase period_pos restCode
  have rest_long : deletionWidth period ≤ rest.length :=
    encodeJunk_nonempty_long system input haltPhase period_pos restCode restCode_nonempty
  obtain ⟨emitted, emitted_nonempty, execution⟩ :=
    read_junkAtom_transGen system input haltPhase instruction period_pos atom rest rest_long
  let next := rest.drop (objectEntryPhase instruction).val ++
    encodeJunk system input haltPhase period_pos emitted
  have phase_le_rest : (objectEntryPhase instruction).val ≤ rest.length :=
    (Nat.le_of_lt (objectEntryPhase instruction).isLt).trans rest_long
  have next_eq : next =
      (encodeJunk system input haltPhase period_pos (restCode ++ emitted)).drop
        (objectEntryPhase instruction).val := by
    simp only [next, encodeJunk_append]
    rw [List.drop_append_of_le_length phase_le_rest]
  refine ⟨next, ⟨instruction, restCode ++ emitted, ?_, next_eq⟩, ?_⟩
  · have restCode_pos := List.length_pos.mpr restCode_nonempty
    have emitted_pos := List.length_pos.mpr emitted_nonempty
    simp only [List.length_append]
    omega
  · simpa [rest, next, encodeJunk_cons] using execution

/-- A garbage-only semantic boundary cannot halt. -/
theorem GarbageBoundary.not_tagHaltsFrom {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase : Fin period) (period_pos : 0 < period)
    {queue : List TagLetter}
    (boundary : GarbageBoundary system input haltPhase period_pos queue) :
    ¬TagHaltsFrom (deletionWidth period)
      (compiledOutput system input haltPhase period_pos) queue := by
  exact not_tagHaltsFrom_of_transGen_progress
    (GarbageBoundary system input haltPhase period_pos)
    (GarbageBoundary.progress system input haltPhase period_pos) boundary

/-- A stable semantic queue with no data bits lies in the perpetual garbage regime. -/
theorem stable_no_data_not_tagHaltsFrom {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase instruction : Fin period) (period_pos : 0 < period)
    (tokens : List DataToken) (stable : StableData tokens)
    (bits_empty : dataBits tokens = []) :
    ¬TagHaltsFrom (deletionWidth period)
      (compiledOutput system input haltPhase period_pos)
      ((encodeData system input haltPhase period_pos tokens).drop
        (objectEntryPhase instruction).val) := by
  obtain ⟨code, tokens_eq⟩ := exists_junkCode_of_dataBits_nil tokens bits_empty
  have reserve : 2 ≤ code.length := by
    have := stable.reserve bits_empty
    simpa [tokens_eq] using this
  apply GarbageBoundary.not_tagHaltsFrom system input haltPhase period_pos
  refine ⟨instruction, code, reserve, ?_⟩
  rw [tokens_eq, encodeData_junk]

/-- Halting from a stable semantic boundary forces a reachable distinguished cyclic pulse. -/
theorem semantic_haltsIn_implies_firing {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase : Fin period) (period_pos : 0 < period)
    (appendant_nonempty_at_zero :
      ∀ instruction : Fin period,
        instruction.val = 0 → system.appendant instruction ≠ [])
    (steps : Nat) (instruction : Fin period) (tokens : List DataToken)
    (stable : StableData tokens)
    (halts : TagHaltsIn (deletionWidth period)
      (compiledOutput system input haltPhase period_pos) steps
      ((encodeData system input haltPhase period_pos tokens).drop
        (objectEntryPhase instruction).val)) :
    ∃ firing,
      system.AvoidingReaches haltPhase
          { data := dataBits tokens, phase := instruction } firing ∧
        CyclicTag.FiresAt haltPhase firing := by
  induction steps using Nat.strong_induction_on generalizing instruction tokens with
  | h steps ih =>
      cases bits_eq : dataBits tokens with
      | nil =>
          exact False.elim <|
            stable_no_data_not_tagHaltsFrom system input haltPhase instruction period_pos
              tokens stable bits_eq <|
                tagHaltsFrom_iff_exists_tagHaltsIn.mpr ⟨steps, halts⟩
      | cons value bits =>
          by_cases fires_here : value = true ∧ instruction = haltPhase
          · obtain ⟨value_true, instruction_eq⟩ := fires_here
            subst value
            refine ⟨{ data := true :: bits, phase := instruction }, ?_, ?_⟩
            · exact Relation.ReflTransGen.refl
            · exact ⟨bits, rfl, instruction_eq⟩
          · have not_halting : value = true → instruction ≠ haltPhase := by
              intro value_true instruction_eq
              exact fires_here ⟨value_true, instruction_eq⟩
            obtain ⟨nextTokens, nextStable, nextBits, execution⟩ :=
              read_next_dataBit_transGen system input haltPhase instruction period_pos
                (appendant_nonempty_at_zero instruction) tokens stable value bits bits_eq
                not_halting
            obtain ⟨laterSteps, later_lt, laterHalts⟩ :=
              tagHaltsIn_after_transGen execution halts
            obtain ⟨firing, laterReach, firing_at_halt⟩ :=
              ih laterSteps later_lt (CyclicTag.shift instruction 1) nextTokens nextStable
                laterHalts
            rw [nextBits] at laterReach
            have first : CyclicTag.AvoidingStep system haltPhase
                { data := value :: bits, phase := instruction }
                { data := bits ++ if value then system.appendant instruction else [],
                  phase := CyclicTag.shift instruction 1 } :=
              .advance instruction value bits not_halting
            refine ⟨firing, ?_, firing_at_halt⟩
            exact Relation.ReflTransGen.head first laterReach

/-- Eventual halting from a stable semantic boundary forces a distinguished cyclic pulse. -/
theorem semantic_halts_implies_firing {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase : Fin period) (period_pos : 0 < period)
    (appendant_nonempty_at_zero :
      ∀ instruction : Fin period,
        instruction.val = 0 → system.appendant instruction ≠ [])
    (instruction : Fin period) (tokens : List DataToken) (stable : StableData tokens)
    (halts : TagHaltsFrom (deletionWidth period)
      (compiledOutput system input haltPhase period_pos)
      ((encodeData system input haltPhase period_pos tokens).drop
        (objectEntryPhase instruction).val)) :
    ∃ firing,
      system.AvoidingReaches haltPhase
          { data := dataBits tokens, phase := instruction } firing ∧
        CyclicTag.FiresAt haltPhase firing := by
  obtain ⟨steps, indexed⟩ := tagHaltsFrom_iff_exists_tagHaltsIn.mp halts
  exact semantic_haltsIn_implies_firing system input haltPhase period_pos
    appendant_nonempty_at_zero steps instruction tokens stable indexed

/-- Every halting execution of the emitted restricted tag system reflects a distinguished firing
of the source cyclic-tag system. -/
theorem compiled_halts_implies_firing {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase : Fin period) (period_pos : 0 < period)
    (input_nonempty : input ≠ [])
    (appendant_nonempty_at_zero :
      ∀ instruction : Fin period,
        instruction.val = 0 → system.appendant instruction ≠ [])
    (halts : TagHaltsFrom (deletionWidth period)
      (compiledOutput system input haltPhase period_pos)
      ((body system input haltPhase period_pos).drop (deletionWidth period - 1) ++ [.b])) :
    ∃ firing,
      system.AvoidingReaches haltPhase
          { data := input, phase := ⟨0, period_pos⟩ } firing ∧
        CyclicTag.FiresAt haltPhase firing := by
  have initialRead := read_initialQueue system input haltPhase period_pos input_nonempty
  have semanticHalts := tagHaltsFrom_after_reaches initialRead halts
  have startEntry : (objectEntryPhase (⟨0, period_pos⟩ : Fin period)).val = 1 :=
    objectEntryPhase_zero _ rfl
  rw [← startEntry] at semanticHalts
  obtain ⟨firing, reach, fires⟩ :=
    semantic_halts_implies_firing system input haltPhase period_pos
      appendant_nonempty_at_zero ⟨0, period_pos⟩ (initialTokens system input)
        (initialTokens_stable system input input_nonempty) semanticHalts
  simpa using ⟨firing, dataBits_initialTokens system input ▸ reach, fires⟩

end MatrixMortality.Undecidability.NearyCompiler
