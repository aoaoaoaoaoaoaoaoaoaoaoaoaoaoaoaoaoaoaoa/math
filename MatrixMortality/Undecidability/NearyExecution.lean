import MatrixMortality.Undecidability.NearyData

/-!
# Global execution of Neary's compiler

This file connects the literal restricted-tag initial queue to the semantic token invariant,
lifts nonfiring cyclic-tag executions, and consumes the first distinguished pulse.
-/

namespace MatrixMortality.Undecidability.NearyCompiler

/-- The truncated compiler word executes the input track and enters the semantic data encoding. -/
theorem read_initialTrack {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) (input_nonempty : input ≠ []) :
    TagReaches (deletionWidth period) (compiledOutput system input haltPhase period_pos)
      ((wholeAppendant system input haltPhase period_pos).drop (deletionWidth period - 1))
      (spell (compiledOutput system input haltPhase period_pos)
        ((inputTrack system input period_pos).val.drop (deletionWidth period - 1))) := by
  let β := deletionWidth period
  let s := trackWidth system input
  let output := compiledOutput system input haltPhase period_pos
  let word := wholeAppendant system input haltPhase period_pos
  let track := (inputTrack system input period_pos).val
  let phase := lastPhase period_pos
  let count := s - 1
  let front := word.drop phase.val
  let remainder := front.drop (count * β)
  have β_pos : 0 < β := deletionWidth_pos period_pos
  have s_pos : 0 < s := trackWidth_pos system input
  have phase_value : phase.val = β - 1 := by rfl
  have count_value : count + 1 = s := by
    simp only [count]
    omega
  have word_length : word.length = β * s := by
    exact wholeAppendant_length system input haltPhase period_pos
  have front_length : front.length = count * β + 1 := by
    simp only [front, List.length_drop]
    rw [word_length, phase_value]
    calc
      β * s - (β - 1) = β * (count + 1) - (β - 1) := by rw [count_value]
      _ = count * β + 1 := by
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm β count]
        omega
  have enough : count * β ≤ front.length := by rw [front_length]; omega
  have chunks := tagReaches_chunks β β_pos output count front remainder enough
  have source_eq : front.take (count * β) ++ remainder = front :=
    List.take_append_drop (count * β) front
  rw [source_eq] at chunks
  let grid : Fin β → Fin s → TagLetter := fun row column =>
    (tableTrack system input haltPhase period_pos row).get column
  have fits : 0 + count ≤ s := by simp only [count]; omega
  have samples := sampleHeads_weave_slice β_pos grid phase 0 count fits [] (by
    simpa [front, word, wholeAppendant, β, s, phase] using enough)
  have samples_eq : sampleHeads β β_pos count front enough = track.take count := by
    have sliced := samples
    simp only [List.append_nil, Nat.mul_zero, Nat.add_zero] at sliced
    rw [gridTrackSlice_zero grid phase count (by omega)] at sliced
    have prescribed : gridTrack grid phase = track := by
      change gridTrack
          (fun row column =>
            (tableTrack system input haltPhase period_pos row).get column)
          (lastPhase period_pos) = (inputTrack system input period_pos).val
      rw [gridTrack_tableTrack, tableTrack_lastPhase]
    rw [prescribed] at sliced
    simpa [front, word, wholeAppendant, β, s, phase, grid] using sliced
  rw [samples_eq] at chunks
  have body_index : count * β + phase.val =
      (body system input haltPhase period_pos).length := by
    have body_size : (body system input haltPhase period_pos).length = β * s - 1 := by
      rw [body, List.length_dropLast, wholeAppendant_length]
    rw [body_size, phase_value]
    calc
      count * β + (β - 1) = (count + 1) * β - 1 := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      _ = s * β - 1 := by rw [count_value]
      _ = β * s - 1 := by rw [Nat.mul_comm]
  have remainder_eq : remainder = [.b] := by
    simp only [remainder, front, List.drop_drop]
    rw [body_index]
    change (wholeAppendant system input haltPhase period_pos).drop
      (body system input haltPhase period_pos).length = [.b]
    rw [wholeAppendant_eq_body_append]
    simp
  rw [remainder_eq, List.singleton_append] at chunks
  have count_take : track.take count = track.dropLast := by
    rw [List.dropLast_eq_take]
    congr
    change count = (inputTrack system input period_pos).val.length - 1
    rw [(inputTrack system input period_pos).property]
  rw [count_take] at chunks
  have track_long : β ≤ track.length := by
    change β ≤ (inputTrack system input period_pos).val.length
    rw [(inputTrack system input period_pos).property]
    exact deletionWidth_le_trackWidth system input period_pos
  have track_prefix : track.take (β - 1) = List.replicate (β - 1) .b :=
    inputTrack_take_initialPadding system input period_pos input_nonempty
  have track_terminal :
      track.getLast (List.ne_nil_of_length_pos (β_pos.trans_le track_long)) = .b := by
    change (inputTrack system input period_pos).val.getLast _ = .b
    have terminal := inputTrack_getLast? system input period_pos
    rw [List.getLast?_eq_getLast_of_ne_nil] at terminal
    exact Option.some.inj terminal
  have rotated := tagReaches_rotate_terminal β β_pos output .b track track_long track_prefix
    track_terminal (by rfl)
  have composed := Relation.ReflTransGen.trans chunks rotated
  simpa [front, word, phase, β, output, track] using composed

/-- Neary's literal initial queue reaches the stable semantic encoding of the cyclic input. -/
theorem read_initialQueue {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) (input_nonempty : input ≠ []) :
    TagReaches (deletionWidth period) (compiledOutput system input haltPhase period_pos)
      ((body system input haltPhase period_pos).drop (deletionWidth period - 1) ++ [.b])
      ((encodeData system input haltPhase period_pos (initialTokens system input)).drop 1) := by
  rw [initial_eq_drop_whole]
  have execution := read_initialTrack system input haltPhase period_pos input_nonempty
  rw [spell_inputTrack_drop_initial system input haltPhase period_pos input_nonempty] at execution
  exact execution

/-- Read a positive number of complete compiler words through one fixed physical track. -/
theorem read_repeatWhole_track_succ {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase : Fin period) (period_pos : 0 < period)
    (phase : Fin (deletionWidth period)) (count : Nat) (tail : List TagLetter)
    (phase_fits : phase.val ≤ tail.length) :
    TagReaches (deletionWidth period)
      (compiledOutput system input haltPhase period_pos)
      ((repeatWord (count + 1) (wholeAppendant system input haltPhase period_pos)).drop
          phase.val ++ tail)
      (tail.drop phase.val ++
        repeatWord (count + 1)
          (spell (compiledOutput system input haltPhase period_pos)
            (tableTrack system input haltPhase period_pos phase).val)) := by
  let word := wholeAppendant system input haltPhase period_pos
  let output := compiledOutput system input haltPhase period_pos
  let emission := spell output (tableTrack system input haltPhase period_pos phase).val
  have phase_le_word : phase.val ≤ word.length := by
    change phase.val ≤ (wholeAppendant system input haltPhase period_pos).length
    rw [wholeAppendant_length]
    exact (Nat.le_of_lt phase.isLt).trans
      (Nat.le_mul_of_pos_right _ (trackWidth_pos system input))
  induction count generalizing tail with
  | zero =>
      simpa [repeatWord, word, output, emission] using
        read_wholeAppendant_track system input haltPhase period_pos phase tail phase_fits
  | succ count ih =>
      let repeated := repeatWord (count + 1) word
      have phase_le_repeated : phase.val ≤ repeated.length := by
        exact phase_le_word.trans (by
          change word.length ≤ (repeatWord (count + 1) word).length
          rw [repeatWord_length]
          exact Nat.le_mul_of_pos_left _ (by omega))
      have first := read_wholeAppendant_track system input haltPhase period_pos phase
        (repeated ++ tail) (phase_le_repeated.trans (by simp))
      have first' : TagReaches (deletionWidth period) output
          ((word ++ repeated).drop phase.val ++ tail)
          (repeated.drop phase.val ++ tail ++ emission) := by
        rw [List.drop_append_of_le_length phase_le_word]
        rw [List.drop_append_of_le_length phase_le_repeated] at first
        simpa [word, output, emission, List.append_assoc] using first
      have later := ih (tail ++ emission) (phase_fits.trans (by simp))
      have later' : TagReaches (deletionWidth period) output
          (repeated.drop phase.val ++ tail ++ emission)
          (tail.drop phase.val ++ emission ++ repeatWord (count + 1) emission) := by
        rw [List.drop_append_of_le_length phase_fits] at later
        simpa [repeated, output, emission, List.append_assoc] using later
      have composed := Relation.ReflTransGen.trans first' later'
      simpa [repeatWord_succ_left, repeated, word, output, emission,
        List.append_assoc] using composed

/-- The one-symbol phase disturbance followed by `s − 1` complete compiler words. -/
def haltingSeed {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) : List TagLetter :=
  [.b] ++ repeatWord (trackWidth system input - 1)
    (wholeAppendant system input haltPhase period_pos)

theorem haltingSeed_long {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) :
    deletionWidth period ≤ (haltingSeed system input haltPhase period_pos).length := by
  have width_two : 2 ≤ trackWidth system input :=
    (Nat.le_of_lt (deletionWidth_large period_pos)).trans
      (deletionWidth_le_trackWidth system input period_pos)
  have copies_pos : 0 < trackWidth system input - 1 := by omega
  have word_long : deletionWidth period ≤
      (wholeAppendant system input haltPhase period_pos).length := by
    rw [wholeAppendant_length]
    exact Nat.le_mul_of_pos_right _ (trackWidth_pos system input)
  have copies_long : deletionWidth period ≤
      (repeatWord (trackWidth system input - 1)
        (wholeAppendant system input haltPhase period_pos)).length := by
    rw [repeatWord_length]
    exact word_long.trans (Nat.le_mul_of_pos_left _ copies_pos)
  exact copies_long.trans (by simp [haltingSeed])

/-- Move a junk-only semantic suffix behind the protected halting seed. -/
theorem drain_junk_before_haltingSeed {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase instruction : Fin period) (period_pos : 0 < period)
    (tokens : List DataToken) (tokens_end : EndsInJunk tokens)
    (bits_empty : dataBits tokens = []) :
    ∃ emitted : List JunkAtom,
      emitted ≠ [] ∧
        TagReaches (deletionWidth period) (compiledOutput system input haltPhase period_pos)
          ((encodeData system input haltPhase period_pos tokens).drop
              (objectEntryPhase instruction).val ++
            haltingSeed system input haltPhase period_pos)
          ((haltingSeed system input haltPhase period_pos).drop
              (objectEntryPhase instruction).val ++
            encodeJunk system input haltPhase period_pos emitted) := by
  obtain ⟨code, tokens_eq⟩ := exists_junkCode_of_dataBits_nil tokens bits_empty
  have code_nonempty : code ≠ [] := by
    intro code_empty
    subst code
    simp at tokens_eq
    exact (EndsInJunk.length_pos tokens_end).ne' (congrArg List.length tokens_eq)
  obtain ⟨atom, atom_mem⟩ := EndsInJunk.exists_mem tokens_end
  have encoded_long : deletionWidth period ≤
      (encodeData system input haltPhase period_pos tokens).length :=
    encodeData_long_of_junk_mem system input haltPhase period_pos tokens atom atom_mem
  have phase_le_encoded : (objectEntryPhase instruction).val ≤
      (encodeData system input haltPhase period_pos tokens).length :=
    (Nat.le_of_lt (objectEntryPhase instruction).isLt).trans encoded_long
  obtain ⟨emitted, emitted_condition, execution⟩ :=
    read_junk system input haltPhase instruction period_pos code
      (haltingSeed system input haltPhase period_pos)
      (haltingSeed_long system input haltPhase period_pos)
  have emitted_nonempty : emitted ≠ [] := emitted_condition.resolve_left code_nonempty
  refine ⟨emitted, emitted_nonempty, ?_⟩
  rw [tokens_eq, encodeData_junk] at phase_le_encoded ⊢
  rw [← List.drop_append_of_le_length phase_le_encoded]
  exact execution

/-- Consume the distinguished true object and append Neary's halting seed. -/
theorem read_haltingToken {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) (haltPhase_nonzero : haltPhase.val ≠ 0)
    (rest : List TagLetter) (rest_long : deletionWidth period ≤ rest.length) :
    TagReaches (deletionWidth period) (compiledOutput system input haltPhase period_pos)
      ((dataTokenWord system input haltPhase period_pos (.bit true) ++ rest).drop
        (objectEntryPhase haltPhase).val)
      (rest.drop (objectEntryPhase (CyclicTag.shift haltPhase 1)).val ++
        haltingSeed system input haltPhase period_pos) := by
  have track_fits : (onePhase haltPhase).val ≤
      (List.replicate 2 TagLetter.b ++ rest).length := by
    have := (Nat.le_of_lt (onePhase haltPhase).isLt).trans rest_long
    simp only [List.length_append, List.length_replicate]
    omega
  have token_long : deletionWidth period ≤
      (bitObject system input haltPhase period_pos true).length := by
    rw [bitObject_eq_true]
    simp only [List.length_append, List.length_replicate, wholeAppendant_length]
    have core := Nat.le_mul_of_pos_right (deletionWidth period) (trackWidth_pos system input)
    omega
  have phase_le_token : (objectEntryPhase haltPhase).val ≤
      (bitObject system input haltPhase period_pos true).length :=
    (Nat.le_of_lt (objectEntryPhase haltPhase).isLt).trans token_long
  have execution := read_haltingObject system input haltPhase period_pos haltPhase_nonzero rest
    track_fits
  rw [dataTokenWord, List.drop_append_of_le_length phase_le_token]
  simpa [haltingSeed, List.append_assoc] using execution

/-- Consume all garbage before the distinguished true object, preserving the unconsumed token
suffix in front of the halting seed. -/
theorem read_haltingPulse {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) (haltPhase_nonzero : haltPhase.val ≠ 0)
    (leading : List JunkAtom) (tail : List DataToken)
    (tailAtom : JunkAtom) (tail_has_junk : .junk tailAtom ∈ tail) :
    ∃ emittedLeading : List JunkAtom,
      TagReaches (deletionWidth period) (compiledOutput system input haltPhase period_pos)
        ((encodeData system input haltPhase period_pos
          (leading.map .junk ++ .bit true :: tail)).drop
            (objectEntryPhase haltPhase).val)
        ((encodeData system input haltPhase period_pos
          (tail ++ emittedLeading.map .junk)).drop
            (objectEntryPhase (CyclicTag.shift haltPhase 1)).val ++
              haltingSeed system input haltPhase period_pos) := by
  let bitWord := dataTokenWord system input haltPhase period_pos (.bit true)
  let tailWord := encodeData system input haltPhase period_pos tail
  have tail_long : deletionWidth period ≤ tailWord.length :=
    encodeData_long_of_junk_mem system input haltPhase period_pos tail tailAtom tail_has_junk
  have protected_long : deletionWidth period ≤ (bitWord ++ tailWord).length :=
    tail_long.trans (by simp)
  obtain ⟨emittedLeading, _, leadingRead⟩ :=
    read_junk system input haltPhase haltPhase period_pos leading (bitWord ++ tailWord)
      protected_long
  let leadingEmission := encodeJunk system input haltPhase period_pos emittedLeading
  have entry_le_bit : (objectEntryPhase haltPhase).val ≤ bitWord.length :=
    (Nat.le_of_lt (objectEntryPhase haltPhase).isLt).trans
      (dataTokenWord_bit_long system input haltPhase period_pos true)
  have leadingTarget :
      (bitWord ++ tailWord).drop (objectEntryPhase haltPhase).val ++ leadingEmission =
        (bitWord ++ (tailWord ++ leadingEmission)).drop
          (objectEntryPhase haltPhase).val := by
    rw [List.drop_append_of_le_length entry_le_bit]
    rw [List.drop_append_of_le_length entry_le_bit]
    simp [List.append_assoc]
  have leadingRead' : TagReaches (deletionWidth period)
      (compiledOutput system input haltPhase period_pos)
      ((encodeData system input haltPhase period_pos
        (leading.map .junk ++ .bit true :: tail)).drop
          (objectEntryPhase haltPhase).val)
      ((bitWord ++ (tailWord ++ leadingEmission)).drop
        (objectEntryPhase haltPhase).val) := by
    rw [← leadingTarget]
    simpa [encodeData_append, encodeData_junk, bitWord, tailWord,
      leadingEmission, List.append_assoc] using leadingRead
  have extended_long : deletionWidth period ≤ (tailWord ++ leadingEmission).length :=
    tail_long.trans (by simp)
  have haltingRead := read_haltingToken system input haltPhase period_pos haltPhase_nonzero
    (tailWord ++ leadingEmission) extended_long
  have remainingShape :
      encodeData system input haltPhase period_pos (tail ++ emittedLeading.map .junk) =
        tailWord ++ leadingEmission := by
    simp [encodeData_append, encodeData_junk, tailWord, leadingEmission]
  have haltingRead' : TagReaches (deletionWidth period)
      (compiledOutput system input haltPhase period_pos)
      ((bitWord ++ (tailWord ++ leadingEmission)).drop (objectEntryPhase haltPhase).val)
      ((encodeData system input haltPhase period_pos
          (tail ++ emittedLeading.map .junk)).drop
            (objectEntryPhase (CyclicTag.shift haltPhase 1)).val ++
              haltingSeed system input haltPhase period_pos) := by
    rw [remainingShape]
    simpa [bitWord, List.append_assoc] using haltingRead
  exact ⟨emittedLeading, Relation.ReflTransGen.trans leadingRead' haltingRead'⟩

/-- Locate and consume the first distinguished true data token in a stable semantic stream. -/
theorem read_next_firing {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) (haltPhase_nonzero : haltPhase.val ≠ 0)
    (tokens : List DataToken) (stable : StableData tokens) (bits : List Bool)
    (bits_eq : dataBits tokens = true :: bits) :
    ∃ remainingTokens : List DataToken,
      EndsInJunk remainingTokens ∧
        dataBits remainingTokens = bits ∧
        TagReaches (deletionWidth period) (compiledOutput system input haltPhase period_pos)
          ((encodeData system input haltPhase period_pos tokens).drop
            (objectEntryPhase haltPhase).val)
          ((encodeData system input haltPhase period_pos remainingTokens).drop
              (objectEntryPhase (CyclicTag.shift haltPhase 1)).val ++
                haltingSeed system input haltPhase period_pos) := by
  obtain ⟨leading, tail, token_eq, tail_eq, tail_ends⟩ :=
    split_first_dataBit stable.endsInJunk true bits bits_eq
  obtain ⟨tailAtom, tail_has_junk⟩ := EndsInJunk.exists_mem tail_ends
  obtain ⟨emittedLeading, execution⟩ :=
    read_haltingPulse system input haltPhase period_pos haltPhase_nonzero leading tail
      tailAtom tail_has_junk
  let remainingTokens := tail ++ emittedLeading.map .junk
  refine ⟨remainingTokens, EndsInJunk.append_junk tail emittedLeading tail_ends, ?_, ?_⟩
  · simp [remainingTokens, tail_eq]
  · rw [token_eq]
    exact execution

/-- Every nonfiring cyclic execution is mirrored between semantic restricted-tag queues. -/
theorem read_avoidingReaches {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period)
    (appendant_nonempty_at_zero :
      ∀ instruction : Fin period,
        instruction.val = 0 → system.appendant instruction ≠ [])
    {before after : CyclicTag.Config period}
    (reach : system.AvoidingReaches haltPhase before after)
    (tokens : List DataToken) (stable : StableData tokens)
    (represented : dataBits tokens = before.data) :
    ∃ nextTokens : List DataToken,
      StableData nextTokens ∧
        dataBits nextTokens = after.data ∧
          TagReaches (deletionWidth period)
            (compiledOutput system input haltPhase period_pos)
            ((encodeData system input haltPhase period_pos tokens).drop
              (objectEntryPhase before.phase).val)
            ((encodeData system input haltPhase period_pos nextTokens).drop
              (objectEntryPhase after.phase).val) := by
  induction reach with
  | refl =>
      exact ⟨tokens, stable, represented, Relation.ReflTransGen.refl⟩
  | @tail middle after reach step ih =>
      obtain ⟨middleTokens, middleStable, middleRepresented, frontReach⟩ := ih
      cases step with
      | advance instruction value bits not_firing =>
          obtain ⟨afterTokens, afterStable, afterRepresented, suffix⟩ :=
            read_next_dataBit system input haltPhase instruction period_pos
              (appendant_nonempty_at_zero instruction) middleTokens middleStable value bits
              middleRepresented not_firing
          exact ⟨afterTokens, afterStable, afterRepresented,
            Relation.ReflTransGen.trans frontReach suffix⟩

/-- A cyclic run reaching the distinguished pulse drives the restricted tag system to its first
corresponding semantic true object. -/
theorem read_until_firing {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) (input_nonempty : input ≠ [])
    (appendant_nonempty_at_zero :
      ∀ instruction : Fin period,
        instruction.val = 0 → system.appendant instruction ≠ [])
    (steps : Nat) (final : CyclicTag.Config period)
    (execution : system.run steps { data := input, phase := ⟨0, period_pos⟩ } = some final)
    (final_fires : CyclicTag.FiresAt haltPhase final) :
    ∃ firingTokens : List DataToken, ∃ tail : List Bool,
      StableData firingTokens ∧
        dataBits firingTokens = true :: tail ∧
          TagReaches (deletionWidth period)
            (compiledOutput system input haltPhase period_pos)
            ((body system input haltPhase period_pos).drop (deletionWidth period - 1) ++ [.b])
            ((encodeData system input haltPhase period_pos firingTokens).drop
              (objectEntryPhase haltPhase).val) := by
  obtain ⟨firing, beforeFiring, fires⟩ :=
    CyclicTag.exists_avoidingReaches_firing_of_run system haltPhase steps
      { data := input, phase := ⟨0, period_pos⟩ } final execution final_fires
  obtain ⟨tail, firingData, firingPhase⟩ := fires
  obtain ⟨firingTokens, firingStable, represented, semanticRead⟩ :=
    read_avoidingReaches system input haltPhase period_pos appendant_nonempty_at_zero
      beforeFiring (initialTokens system input) (initialTokens_stable system input input_nonempty)
      (dataBits_initialTokens system input)
  have initialRead := read_initialQueue system input haltPhase period_pos input_nonempty
  have startEntry :
      (objectEntryPhase (⟨0, period_pos⟩ : Fin period)).val = 1 :=
    objectEntryPhase_zero _ rfl
  rw [startEntry] at semanticRead
  rw [firingPhase] at semanticRead
  have combined := Relation.ReflTransGen.trans initialRead semanticRead
  refine ⟨firingTokens, tail, firingStable, ?_, combined⟩
  rw [represented, firingData]

/-- A distinguished cyclic pulse appends Neary's halting seed behind the remaining semantic
queue. -/
theorem read_to_haltingSeed {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) (input_nonempty : input ≠ [])
    (haltPhase_nonzero : haltPhase.val ≠ 0)
    (appendant_nonempty_at_zero :
      ∀ instruction : Fin period,
        instruction.val = 0 → system.appendant instruction ≠ [])
    (steps : Nat) (final : CyclicTag.Config period)
    (execution : system.run steps { data := input, phase := ⟨0, period_pos⟩ } = some final)
    (final_fires : CyclicTag.FiresAt haltPhase final) :
    ∃ remainingTokens : List DataToken, ∃ bits : List Bool,
      EndsInJunk remainingTokens ∧
        dataBits remainingTokens = bits ∧
        TagReaches (deletionWidth period) (compiledOutput system input haltPhase period_pos)
          ((body system input haltPhase period_pos).drop (deletionWidth period - 1) ++ [.b])
          ((encodeData system input haltPhase period_pos remainingTokens).drop
              (objectEntryPhase (CyclicTag.shift haltPhase 1)).val ++
                haltingSeed system input haltPhase period_pos) := by
  obtain ⟨firingTokens, tail, firingStable, firingBits, beforePulse⟩ :=
    read_until_firing system input haltPhase period_pos input_nonempty
      appendant_nonempty_at_zero steps final execution final_fires
  obtain ⟨remainingTokens, remainingEnds, remainingBits, pulse⟩ :=
    read_next_firing system input haltPhase period_pos haltPhase_nonzero firingTokens
      firingStable tail firingBits
  exact ⟨remainingTokens, tail, remainingEnds, remainingBits,
    Relation.ReflTransGen.trans beforePulse pulse⟩

/-- Exact-empty firing leaves only junk in front of Neary's halting seed. -/
theorem read_exact_firing_to_haltingSeed {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase : Fin period) (period_pos : 0 < period)
    (input_nonempty : input ≠ []) (haltPhase_nonzero : haltPhase.val ≠ 0)
    (appendant_nonempty_at_zero :
      ∀ instruction : Fin period,
        instruction.val = 0 → system.appendant instruction ≠ [])
    (beforeFiring : system.AvoidingReaches haltPhase
      { data := input, phase := ⟨0, period_pos⟩ }
      { data := [true], phase := haltPhase }) :
    ∃ remainingTokens : List DataToken,
      EndsInJunk remainingTokens ∧
        dataBits remainingTokens = [] ∧
          TagReaches (deletionWidth period)
            (compiledOutput system input haltPhase period_pos)
            ((body system input haltPhase period_pos).drop (deletionWidth period - 1) ++ [.b])
            ((encodeData system input haltPhase period_pos remainingTokens).drop
                (objectEntryPhase (CyclicTag.shift haltPhase 1)).val ++
                  haltingSeed system input haltPhase period_pos) := by
  obtain ⟨firingTokens, firingStable, firingBits, beforePulse⟩ :=
    read_avoidingReaches system input haltPhase period_pos appendant_nonempty_at_zero
      beforeFiring (initialTokens system input) (initialTokens_stable system input input_nonempty)
      (dataBits_initialTokens system input)
  have initialRead := read_initialQueue system input haltPhase period_pos input_nonempty
  have startEntry :
      (objectEntryPhase (⟨0, period_pos⟩ : Fin period)).val = 1 :=
    objectEntryPhase_zero _ rfl
  rw [startEntry] at beforePulse
  have enteredPulse := Relation.ReflTransGen.trans initialRead beforePulse
  obtain ⟨remainingTokens, remainingEnds, remainingBits, pulse⟩ :=
    read_next_firing system input haltPhase period_pos haltPhase_nonzero firingTokens
      firingStable [] firingBits
  exact ⟨remainingTokens, remainingEnds, remainingBits,
    Relation.ReflTransGen.trans enteredPulse pulse⟩

end MatrixMortality.Undecidability.NearyCompiler
