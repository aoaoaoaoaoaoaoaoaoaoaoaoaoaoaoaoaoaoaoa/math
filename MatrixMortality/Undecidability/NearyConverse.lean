import MatrixMortality.Undecidability.NearyExecution

/-!
# No-spurious-halting converse for Neary's compiler

Positive versions of the semantic traversals expose strict progress between macro boundaries.
They rule out finite halting while the compiler remains in its garbage reserve and recover a
distinguished cyclic firing from every halting restricted-tag execution.
-/

namespace MatrixMortality.Undecidability.NearyCompiler

/-- Reading a zero token is a nonempty semantic execution. -/
theorem read_zeroToken_transGen {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase instruction : Fin period) (period_pos : 0 < period)
    (rest : List TagLetter) (rest_long : deletionWidth period ≤ rest.length) :
    Relation.TransGen
      (TagStep (deletionWidth period) (compiledOutput system input haltPhase period_pos))
      ((dataTokenWord system input haltPhase period_pos (.bit false) ++ rest).drop
        (objectEntryPhase instruction).val)
      (rest.drop (objectEntryPhase (CyclicTag.shift instruction 1)).val ++
        encodeData system input haltPhase period_pos
          ((silentJunkCode system input instruction).map .junk)) := by
  have track_fits : (zeroPhase instruction).val ≤
      (List.replicate 4 TagLetter.b ++ rest).length := by
    have phase_le := (Nat.le_of_lt (zeroPhase instruction).isLt).trans rest_long
    simp only [List.length_append, List.length_replicate]
    omega
  have token_long :
      deletionWidth period ≤ (bitObject system input haltPhase period_pos false).length := by
    rw [bitObject_eq_false]
    simp only [List.length_append, List.length_replicate, wholeAppendant_length]
    have core := Nat.le_mul_of_pos_right
      (deletionWidth period) (trackWidth_pos system input)
    omega
  have phase_le_token :
      (objectEntryPhase instruction).val ≤
        (bitObject system input haltPhase period_pos false).length :=
    (Nat.le_of_lt (objectEntryPhase instruction).isLt).trans token_long
  have read := read_zeroObject_transGen system input haltPhase instruction period_pos rest
    track_fits
  rw [silentEmission_eq_encodeData] at read
  rw [dataTokenWord, List.drop_append_of_le_length phase_le_token]
  exact read

/-- Reading an ordinary true token is a nonempty semantic execution. -/
theorem read_oneToken_transGen {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase instruction : Fin period) (period_pos : 0 < period)
    (not_halting : instruction ≠ haltPhase)
    (appendant_nonempty_at_zero : instruction.val = 0 → system.appendant instruction ≠ [])
    (rest : List TagLetter) (rest_long : deletionWidth period ≤ rest.length) :
    Relation.TransGen
      (TagStep (deletionWidth period) (compiledOutput system input haltPhase period_pos))
      ((dataTokenWord system input haltPhase period_pos (.bit true) ++ rest).drop
        (objectEntryPhase instruction).val)
      (rest.drop (objectEntryPhase (CyclicTag.shift instruction 1)).val ++
        encodeData system input haltPhase period_pos
          ((system.appendant instruction).map .bit ++
            (appendantJunkCode system input instruction).map .junk)) := by
  have track_fits : (onePhase instruction).val ≤
      (List.replicate 2 TagLetter.b ++ rest).length := by
    have phase_le := (Nat.le_of_lt (onePhase instruction).isLt).trans rest_long
    simp only [List.length_append, List.length_replicate]
    omega
  have token_long :
      deletionWidth period ≤ (bitObject system input haltPhase period_pos true).length := by
    rw [bitObject_eq_true]
    simp only [List.length_append, List.length_replicate, wholeAppendant_length]
    have core := Nat.le_mul_of_pos_right
      (deletionWidth period) (trackWidth_pos system input)
    omega
  have phase_le_token :
      (objectEntryPhase instruction).val ≤
        (bitObject system input haltPhase period_pos true).length :=
    (Nat.le_of_lt (objectEntryPhase instruction).isLt).trans token_long
  have read := read_oneObject_transGen system input haltPhase instruction period_pos not_halting
    appendant_nonempty_at_zero rest track_fits
  rw [appendantEmission_eq_encodeData] at read
  rw [dataTokenWord, List.drop_append_of_le_length phase_le_token]
  exact read

/-- Reading any ordinary cyclic data token makes nonempty semantic progress. -/
theorem read_bitToken_transGen {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase instruction : Fin period) (period_pos : 0 < period)
    (appendant_nonempty_at_zero : instruction.val = 0 → system.appendant instruction ≠ [])
    (value : Bool) (not_halting : value = true → instruction ≠ haltPhase)
    (rest : List TagLetter) (rest_long : deletionWidth period ≤ rest.length) :
    Relation.TransGen
      (TagStep (deletionWidth period) (compiledOutput system input haltPhase period_pos))
      ((dataTokenWord system input haltPhase period_pos (.bit value) ++ rest).drop
        (objectEntryPhase instruction).val)
      (rest.drop (objectEntryPhase (CyclicTag.shift instruction 1)).val ++
        encodeData system input haltPhase period_pos
          (ordinaryBitEmission system input instruction value)) := by
  cases value with
  | false =>
      simpa [ordinaryBitEmission] using
        read_zeroToken_transGen system input haltPhase instruction period_pos rest rest_long
  | true =>
      simpa [ordinaryBitEmission] using
        read_oneToken_transGen system input haltPhase instruction period_pos (not_halting rfl)
          appendant_nonempty_at_zero rest rest_long

/-- Consuming the next ordinary data pulse makes nonempty progress through arbitrary leading
garbage. -/
theorem read_dataPulse_transGen {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase instruction : Fin period) (period_pos : 0 < period)
    (appendant_nonempty_at_zero : instruction.val = 0 → system.appendant instruction ≠ [])
    (leading : List JunkAtom) (value : Bool)
    (not_halting : value = true → instruction ≠ haltPhase) (tail : List DataToken)
    (tailAtom : JunkAtom) (tail_has_junk : .junk tailAtom ∈ tail) :
    ∃ emittedLeading : List JunkAtom,
      Relation.TransGen
        (TagStep (deletionWidth period) (compiledOutput system input haltPhase period_pos))
        ((encodeData system input haltPhase period_pos
          (leading.map .junk ++ .bit value :: tail)).drop
            (objectEntryPhase instruction).val)
        ((encodeData system input haltPhase period_pos
          (tail ++ emittedLeading.map .junk ++
            ordinaryBitEmission system input instruction value)).drop
              (objectEntryPhase (CyclicTag.shift instruction 1)).val) := by
  let bitWord := dataTokenWord system input haltPhase period_pos (.bit value)
  let tailWord := encodeData system input haltPhase period_pos tail
  have tail_long : deletionWidth period ≤ tailWord.length :=
    encodeData_long_of_junk_mem system input haltPhase period_pos tail tailAtom tail_has_junk
  have protected_long : deletionWidth period ≤ (bitWord ++ tailWord).length :=
    tail_long.trans (by simp)
  obtain ⟨emittedLeading, _, leadingRead⟩ :=
    read_junk system input haltPhase instruction period_pos leading (bitWord ++ tailWord)
      protected_long
  let leadingEmission := encodeJunk system input haltPhase period_pos emittedLeading
  have entry_le_bit : (objectEntryPhase instruction).val ≤ bitWord.length :=
    (Nat.le_of_lt (objectEntryPhase instruction).isLt).trans
      (dataTokenWord_bit_long system input haltPhase period_pos value)
  have leadingTarget :
      (bitWord ++ tailWord).drop (objectEntryPhase instruction).val ++ leadingEmission =
        (bitWord ++ (tailWord ++ leadingEmission)).drop
          (objectEntryPhase instruction).val := by
    rw [List.drop_append_of_le_length entry_le_bit]
    rw [List.drop_append_of_le_length entry_le_bit]
    simp [List.append_assoc]
  have leadingRead' : TagReaches (deletionWidth period)
      (compiledOutput system input haltPhase period_pos)
      ((encodeData system input haltPhase period_pos
        (leading.map .junk ++ .bit value :: tail)).drop
          (objectEntryPhase instruction).val)
      ((bitWord ++ (tailWord ++ leadingEmission)).drop
        (objectEntryPhase instruction).val) := by
    rw [← leadingTarget]
    simpa [encodeData_append, encodeData_junk, bitWord, tailWord,
      leadingEmission, List.append_assoc] using leadingRead
  have extended_long : deletionWidth period ≤ (tailWord ++ leadingEmission).length :=
    tail_long.trans (by simp)
  have bitRead := read_bitToken_transGen system input haltPhase instruction period_pos
    appendant_nonempty_at_zero value not_halting (tailWord ++ leadingEmission) extended_long
  let nextInstruction := CyclicTag.shift instruction 1
  let bitEmission := encodeData system input haltPhase period_pos
    (ordinaryBitEmission system input instruction value)
  have next_entry_le_tail : (objectEntryPhase nextInstruction).val ≤ tailWord.length :=
    (Nat.le_of_lt (objectEntryPhase nextInstruction).isLt).trans tail_long
  have finalShape :
      (tailWord ++ leadingEmission).drop (objectEntryPhase nextInstruction).val ++ bitEmission =
        (encodeData system input haltPhase period_pos
          (tail ++ emittedLeading.map .junk ++
            ordinaryBitEmission system input instruction value)).drop
              (objectEntryPhase nextInstruction).val := by
    calc
      (tailWord ++ leadingEmission).drop (objectEntryPhase nextInstruction).val ++
          bitEmission =
        (tailWord.drop (objectEntryPhase nextInstruction).val ++ leadingEmission) ++
          bitEmission := by rw [List.drop_append_of_le_length next_entry_le_tail]
      _ = (tailWord ++ (leadingEmission ++ bitEmission)).drop
          (objectEntryPhase nextInstruction).val := by
        rw [List.drop_append_of_le_length next_entry_le_tail]
        simp [List.append_assoc]
      _ = (encodeData system input haltPhase period_pos
          (tail ++ emittedLeading.map .junk ++
            ordinaryBitEmission system input instruction value)).drop
              (objectEntryPhase nextInstruction).val := by
        simp [encodeData_append, encodeData_junk, bitEmission, leadingEmission,
          List.append_assoc]
  rw [finalShape] at bitRead
  exact ⟨emittedLeading, Relation.TransGen.trans_right leadingRead' bitRead⟩

/-- One ordinary cyclic pulse preserves the stable token invariant by a nonempty execution. -/
theorem read_next_dataBit_transGen {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase instruction : Fin period) (period_pos : 0 < period)
    (appendant_nonempty_at_zero : instruction.val = 0 → system.appendant instruction ≠ [])
    (tokens : List DataToken) (stable : StableData tokens) (value : Bool) (bits : List Bool)
    (bits_eq : dataBits tokens = value :: bits)
    (not_halting : value = true → instruction ≠ haltPhase) :
    ∃ nextTokens : List DataToken,
      StableData nextTokens ∧
        dataBits nextTokens = bits ++ (if value then system.appendant instruction else []) ∧
          Relation.TransGen
            (TagStep (deletionWidth period)
              (compiledOutput system input haltPhase period_pos))
            ((encodeData system input haltPhase period_pos tokens).drop
              (objectEntryPhase instruction).val)
            ((encodeData system input haltPhase period_pos nextTokens).drop
              (objectEntryPhase (CyclicTag.shift instruction 1)).val) := by
  obtain ⟨leading, tail, token_eq, tail_eq, tail_ends⟩ :=
    split_first_dataBit stable.endsInJunk value bits bits_eq
  obtain ⟨tailAtom, tail_has_junk⟩ := EndsInJunk.exists_mem tail_ends
  obtain ⟨emittedLeading, read⟩ :=
    read_dataPulse_transGen system input haltPhase instruction period_pos
      appendant_nonempty_at_zero leading value not_halting tail tailAtom tail_has_junk
  let emission := ordinaryBitEmission system input instruction value
  let nextTokens := tail ++ emittedLeading.map .junk ++ emission
  have next_ends : EndsInJunk nextTokens :=
    EndsInJunk.prepend _ <|
      ordinaryBitEmission_endsInJunk system input period_pos instruction value
  have tail_length_pos : 0 < tail.length := List.length_pos_of_mem tail_has_junk
  have emission_length_pos : 0 < emission.length :=
    EndsInJunk.length_pos <|
      ordinaryBitEmission_endsInJunk system input period_pos instruction value
  have next_stable : StableData nextTokens := ⟨next_ends, by
    intro _empty
    simp only [nextTokens, List.length_append, List.length_map]
    omega⟩
  refine ⟨nextTokens, next_stable, ?_, ?_⟩
  · simp [nextTokens, emission, tail_eq]
  · rw [token_eq]
    exact read

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
