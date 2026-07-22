import MatrixMortality.Undecidability.NearyCompiler

/-!
# Correctness of Neary's Table 2 compiler

The compiler word is read through one of its fixed-stride tracks.  This file identifies the
physical tracks used by the three encoded objects and lifts their exact emissions to a simulation
of cyclic-tag configurations.
-/

namespace MatrixMortality.Undecidability.NearyCompiler

theorem inputTrack_take_initialPadding {period : Nat} (system : CyclicTag period)
    (input : List Bool) (period_pos : 0 < period) (input_nonempty : input ≠ []) :
    (inputTrack system input period_pos).val.take (deletionWidth period - 1) =
      List.replicate (deletionWidth period - 1) .b := by
  obtain ⟨bit, bits, rfl⟩ := List.exists_cons_of_ne_nil input_nonempty
  have beta_large := deletionWidth_large period_pos
  have split : deletionWidth period - 1 = deletionWidth period - 2 + 1 := by omega
  rw [split]
  cases bit <;>
    simp [inputTrack, padBetween, encodePrimes, bitPrime, List.take_append_eq_append_take,
      List.replicate_add]

/-- Physical compiler track reached inside an object whose leading padding has shift `offset + 1`.
The quotient is the reversed cyclic instruction and the remainder is `10 - offset`. -/
def objectTrackPhase {period : Nat} (instruction : Fin period) (offset : Fin 10)
    (offset_pos : 0 < offset.val) : Fin (deletionWidth period) :=
  ⟨10 * (period - instruction.val - 1) + (10 - offset.val), by
    have instruction_bound := instruction.isLt
    simp only [deletionWidth]
    omega⟩

/-- Shift at which the next encoded data object is entered. -/
def objectEntryPhase {period : Nat} (instruction : Fin period) : Fin (deletionWidth period) :=
  if instruction_zero : instruction.val = 0 then
    ⟨1, by
      have := instruction.isLt
      simp only [deletionWidth]
      omega⟩
  else
    ⟨10 * (period - instruction.val) + 1, by
      have := instruction.isLt
      simp only [deletionWidth]
      omega⟩

@[simp]
theorem objectEntryPhase_zero {period : Nat} (instruction : Fin period)
    (instruction_zero : instruction.val = 0) :
    (objectEntryPhase instruction).val = 1 := by
  simp [objectEntryPhase, instruction_zero]

theorem objectEntryPhase_nonzero {period : Nat} (instruction : Fin period)
    (instruction_nonzero : instruction.val ≠ 0) :
    (objectEntryPhase instruction).val = 10 * (period - instruction.val) + 1 := by
  simp [objectEntryPhase, instruction_nonzero]

@[simp]
theorem objectEntryPhase_mod {period : Nat} (instruction : Fin period) :
    (objectEntryPhase instruction).val % 10 = 1 := by
  by_cases instruction_zero : instruction.val = 0
  · rw [objectEntryPhase_zero instruction instruction_zero]
  · rw [objectEntryPhase_nonzero instruction instruction_zero]
    simp [Nat.add_mod, Nat.mul_mod]

theorem objectEntryPhase_sub_padding {period : Nat} (instruction : Fin period)
    (instruction_nonzero : instruction.val ≠ 0) (offset : Fin 10)
    (offset_pos : 0 < offset.val) :
    (objectEntryPhase instruction).val - (offset.val + 1) =
      (objectTrackPhase instruction offset offset_pos).val := by
  rw [objectEntryPhase_nonzero instruction instruction_nonzero]
  simp only [objectTrackPhase]
  have instruction_bound := instruction.isLt
  omega

theorem objectTrackPhase_zero {period : Nat} (instruction : Fin period)
    (instruction_zero : instruction.val = 0)
    (offset : Fin 10) (offset_pos : 0 < offset.val) :
    (objectTrackPhase instruction offset offset_pos).val =
      deletionWidth period - offset.val := by
  simp only [objectTrackPhase, deletionWidth]
  omega

theorem objectTrackPhase_sub_suffix {period : Nat} (instruction : Fin period)
    (offset : Fin 10) (offset_pos : 0 < offset.val) :
    (objectTrackPhase instruction offset offset_pos).val - (9 - offset.val) =
    (objectEntryPhase (CyclicTag.shift instruction 1)).val := by
  have instruction_bound := instruction.isLt
  by_cases next_inside : instruction.val + 1 < period
  · have shifted : (CyclicTag.shift instruction 1).val = instruction.val + 1 := by
      simp [CyclicTag.shift, Nat.mod_eq_of_lt next_inside]
    have shifted_nonzero : (CyclicTag.shift instruction 1).val ≠ 0 := by omega
    rw [objectEntryPhase_nonzero _ shifted_nonzero, shifted]
    simp only [objectTrackPhase]
    omega
  · have at_end : instruction.val + 1 = period := by omega
    have shifted : (CyclicTag.shift instruction 1).val = 0 := by
      simp [CyclicTag.shift, at_end]
    rw [objectEntryPhase_zero _ shifted]
    simp only [objectTrackPhase]
    omega

/-- An encoded object with `offset + 1` leading and `9 - offset` trailing `b` symbols. -/
def paddedObject {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) (offset : Fin 10) : List TagLetter :=
  List.replicate (offset.val + 1) .b ++
    wholeAppendant system input haltPhase period_pos ++
      List.replicate (9 - offset.val) .b

theorem paddedObject_drop_nonzero {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase instruction : Fin period) (period_pos : 0 < period)
    (offset : Fin 10) (offset_pos : 0 < offset.val)
    (instruction_nonzero : instruction.val ≠ 0) :
    (paddedObject system input haltPhase period_pos offset).drop
        (objectEntryPhase instruction).val =
      (wholeAppendant system input haltPhase period_pos).drop
          (objectTrackPhase instruction offset offset_pos).val ++
        List.replicate (9 - offset.val) .b := by
  have prefix_le : offset.val + 1 ≤ (objectEntryPhase instruction).val := by
    rw [objectEntryPhase_nonzero instruction instruction_nonzero]
    have instruction_bound := instruction.isLt
    omega
  have prefix_le' : (List.replicate (offset.val + 1) TagLetter.b).length ≤
      (objectEntryPhase instruction).val := by
    simpa using prefix_le
  have track_le : (objectTrackPhase instruction offset offset_pos).val ≤
      (wholeAppendant system input haltPhase period_pos).length := by
    rw [wholeAppendant_length]
    exact (Nat.le_of_lt (objectTrackPhase instruction offset offset_pos).isLt).trans
      (Nat.le_mul_of_pos_right _ (trackWidth_pos system input))
  unfold paddedObject
  rw [List.append_assoc]
  rw [List.drop_append_eq_append_drop]
  rw [List.drop_eq_nil_iff_le.mpr prefix_le', List.nil_append]
  rw [List.length_replicate]
  rw [objectEntryPhase_sub_padding instruction instruction_nonzero offset offset_pos]
  rw [List.drop_append_of_le_length track_le]

theorem paddedObject_eq_epsilonObject {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase : Fin period) (period_pos : 0 < period) :
    paddedObject system input haltPhase period_pos ⟨3, by decide⟩ =
      epsilonObject system input haltPhase period_pos := by
  rw [epsilonObject_eq]
  rfl

theorem paddedObject_eq_bitObject_false {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase : Fin period) (period_pos : 0 < period) :
    paddedObject system input haltPhase period_pos ⟨5, by decide⟩ =
      bitObject system input haltPhase period_pos false := by
  rw [bitObject_eq_false]
  rfl

theorem paddedObject_eq_bitObject_true {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase : Fin period) (period_pos : 0 < period) :
    paddedObject system input haltPhase period_pos ⟨7, by decide⟩ =
      bitObject system input haltPhase period_pos true := by
  rw [bitObject_eq_true]
  rfl

/-- Read a padded object at a nonzero cyclic instruction. -/
theorem read_paddedObject_nonzero {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase instruction : Fin period) (period_pos : 0 < period)
    (offset : Fin 10) (offset_pos : 0 < offset.val)
    (instruction_nonzero : instruction.val ≠ 0) (rest : List TagLetter)
    (track_fits : (objectTrackPhase instruction offset offset_pos).val ≤
      (List.replicate (9 - offset.val) TagLetter.b ++ rest).length) :
    TagReaches (deletionWidth period) (compiledOutput system input haltPhase period_pos)
        ((paddedObject system input haltPhase period_pos offset).drop
            (objectEntryPhase instruction).val ++ rest)
        (rest.drop (objectEntryPhase (CyclicTag.shift instruction 1)).val ++
          spell (compiledOutput system input haltPhase period_pos)
            (tableTrack system input haltPhase period_pos
              (objectTrackPhase instruction offset offset_pos)).val) := by
  have traversal := read_wholeAppendant_track system input haltPhase period_pos
    (objectTrackPhase instruction offset offset_pos)
    (List.replicate (9 - offset.val) .b ++ rest) track_fits
  have suffix_le : 9 - offset.val ≤
      (objectTrackPhase instruction offset offset_pos).val := by
    simp only [objectTrackPhase]
    omega
  have suffix_le' : (List.replicate (9 - offset.val) TagLetter.b).length ≤
      (objectTrackPhase instruction offset offset_pos).val := by
    simpa using suffix_le
  have dropped :
      (List.replicate (9 - offset.val) TagLetter.b ++ rest).drop
          (objectTrackPhase instruction offset offset_pos).val =
        rest.drop (objectEntryPhase (CyclicTag.shift instruction 1)).val := by
    rw [List.drop_append_eq_append_drop]
    rw [List.drop_eq_nil_iff_le.mpr suffix_le', List.nil_append, List.length_replicate]
    rw [objectTrackPhase_sub_suffix]
  rw [dropped] at traversal
  rw [paddedObject_drop_nonzero system input haltPhase instruction period_pos offset offset_pos
    instruction_nonzero]
  simpa [List.append_assoc] using traversal

theorem paddedObject_drop_one {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase : Fin period) (period_pos : 0 < period)
    (offset : Fin 10) :
    (paddedObject system input haltPhase period_pos offset).drop 1 =
      List.replicate offset.val .b ++
        wholeAppendant system input haltPhase period_pos ++
          List.replicate (9 - offset.val) .b := by
  unfold paddedObject
  rw [List.replicate_succ]
  rfl

/-- Read a padded object at cyclic instruction zero, including its leading external `b` step. -/
theorem read_paddedObject_zero {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase instruction : Fin period) (period_pos : 0 < period)
    (instruction_zero : instruction.val = 0) (offset : Fin 10)
    (offset_pos : 0 < offset.val) (rest : List TagLetter)
    (track_fits : (objectTrackPhase instruction offset offset_pos).val ≤
      (List.replicate (9 - offset.val) TagLetter.b ++ rest).length) :
    TagReaches (deletionWidth period) (compiledOutput system input haltPhase period_pos)
        ((paddedObject system input haltPhase period_pos offset).drop
            (objectEntryPhase instruction).val ++ rest)
        (rest.drop (objectEntryPhase (CyclicTag.shift instruction 1)).val ++ [.b] ++
          spell (compiledOutput system input haltPhase period_pos)
            (tableTrack system input haltPhase period_pos
              (objectTrackPhase instruction offset offset_pos)).val) := by
  let queue :=
    (paddedObject system input haltPhase period_pos offset).drop
      (objectEntryPhase instruction).val ++ rest
  have entry_eq : (objectEntryPhase instruction).val = 1 :=
    objectEntryPhase_zero instruction instruction_zero
  have queue_shape : queue =
      List.replicate offset.val .b ++
        wholeAppendant system input haltPhase period_pos ++
          List.replicate (9 - offset.val) .b ++ rest := by
    simp only [queue, entry_eq, paddedObject_drop_one]
  have queue_long : deletionWidth period ≤ queue.length := by
    rw [queue_shape]
    simp only [List.length_append, List.length_replicate, wholeAppendant_length]
    have width_pos := trackWidth_pos system input
    have core : deletionWidth period ≤ deletionWidth period * trackWidth system input :=
      Nat.le_mul_of_pos_right _ width_pos
    omega
  have first := tagReaches_one (deletionWidth period) (deletionWidth_pos period_pos)
    (compiledOutput system input haltPhase period_pos) queue queue_long
  have queue_head : queue.get ⟨0, (deletionWidth_pos period_pos).trans_le queue_long⟩ = .b := by
    obtain ⟨offset, offset_eq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt offset_pos)
    rw [List.get_eq_getElem]
    simp [queue_shape, offset_eq, List.replicate_succ]
  rw [queue_head] at first
  change TagReaches (deletionWidth period) (compiledOutput system input haltPhase period_pos)
      queue (queue.drop (deletionWidth period) ++ [.b]) at first
  have prefix_lt : offset.val < deletionWidth period := by
    simp only [deletionWidth]
    omega
  have prefix_le : (List.replicate offset.val TagLetter.b).length ≤ deletionWidth period := by
    simpa using Nat.le_of_lt prefix_lt
  have phase_le_word : deletionWidth period - offset.val ≤
      (wholeAppendant system input haltPhase period_pos).length := by
    rw [wholeAppendant_length]
    exact (Nat.sub_le _ _).trans
      (Nat.le_mul_of_pos_right _ (trackWidth_pos system input))
  have drop_queue : queue.drop (deletionWidth period) =
      (wholeAppendant system input haltPhase period_pos).drop
          (objectTrackPhase instruction offset offset_pos).val ++
        List.replicate (9 - offset.val) .b ++ rest := by
    rw [queue_shape]
    rw [show List.replicate offset.val TagLetter.b ++
        wholeAppendant system input haltPhase period_pos ++
          List.replicate (9 - offset.val) .b ++ rest =
        List.replicate offset.val .b ++
          (wholeAppendant system input haltPhase period_pos ++
            (List.replicate (9 - offset.val) .b ++ rest)) by
      simp [List.append_assoc]]
    rw [List.drop_append_eq_append_drop]
    rw [List.drop_eq_nil_iff_le.mpr prefix_le, List.nil_append, List.length_replicate]
    rw [objectTrackPhase_zero instruction instruction_zero]
    rw [List.drop_append_of_le_length phase_le_word]
    simp [List.append_assoc]
  rw [drop_queue] at first
  have first' : TagReaches (deletionWidth period)
      (compiledOutput system input haltPhase period_pos) queue
      ((wholeAppendant system input haltPhase period_pos).drop
          (objectTrackPhase instruction offset offset_pos).val ++
        (List.replicate (9 - offset.val) .b ++ rest ++ [.b])) := by
    simpa [List.append_assoc] using first
  have extended_fits : (objectTrackPhase instruction offset offset_pos).val ≤
      (List.replicate (9 - offset.val) TagLetter.b ++ rest ++ [TagLetter.b]).length := by
    exact track_fits.trans (by simp)
  have traversal := read_wholeAppendant_track system input haltPhase period_pos
    (objectTrackPhase instruction offset offset_pos)
    (List.replicate (9 - offset.val) TagLetter.b ++ rest ++ [TagLetter.b]) extended_fits
  have prefix_tail_fits : (objectTrackPhase instruction offset offset_pos).val ≤
      (List.replicate (9 - offset.val) TagLetter.b ++ rest).length := track_fits
  rw [List.drop_append_of_le_length prefix_tail_fits] at traversal
  have suffix_le : (List.replicate (9 - offset.val) TagLetter.b).length ≤
      (objectTrackPhase instruction offset offset_pos).val := by
    simp only [List.length_replicate, objectTrackPhase]
    omega
  rw [List.drop_append_eq_append_drop,
    List.drop_eq_nil_iff_le.mpr suffix_le, List.nil_append, List.length_replicate,
    objectTrackPhase_sub_suffix] at traversal
  have composed := Relation.ReflTransGen.trans first' traversal
  simpa [TagReaches, queue, List.append_assoc] using composed

/-- Uniform padded-object traversal; instruction zero contributes the external leading `b`. -/
theorem read_paddedObject {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase instruction : Fin period) (period_pos : 0 < period)
    (offset : Fin 10) (offset_pos : 0 < offset.val) (rest : List TagLetter)
    (track_fits : (objectTrackPhase instruction offset offset_pos).val ≤
      (List.replicate (9 - offset.val) TagLetter.b ++ rest).length) :
    TagReaches (deletionWidth period) (compiledOutput system input haltPhase period_pos)
        ((paddedObject system input haltPhase period_pos offset).drop
            (objectEntryPhase instruction).val ++ rest)
        (rest.drop (objectEntryPhase (CyclicTag.shift instruction 1)).val ++
          (if instruction.val = 0 then [.b] else []) ++
            spell (compiledOutput system input haltPhase period_pos)
              (tableTrack system input haltPhase period_pos
                (objectTrackPhase instruction offset offset_pos)).val) := by
  by_cases instruction_zero : instruction.val = 0
  · simpa [instruction_zero, List.append_assoc] using
      read_paddedObject_zero system input haltPhase instruction period_pos instruction_zero
        offset offset_pos rest track_fits
  · simpa [instruction_zero] using
      read_paddedObject_nonzero system input haltPhase instruction period_pos offset offset_pos
        instruction_zero rest track_fits

@[simp]
theorem objectTrackPhase_mod {period : Nat} (instruction : Fin period) (offset : Fin 10)
    (offset_pos : 0 < offset.val) :
    (objectTrackPhase instruction offset offset_pos).val % 10 = 10 - offset.val := by
  have remainder_lt : 10 - offset.val < 10 := by omega
  simp [objectTrackPhase, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt remainder_lt]

@[simp]
theorem phaseBlock_objectTrackPhase {period : Nat} (instruction : Fin period)
    (offset : Fin 10) (offset_pos : 0 < offset.val) :
    phaseBlock (objectTrackPhase instruction offset offset_pos) =
      ⟨period - instruction.val - 1, by omega⟩ := by
  apply Fin.ext
  change (10 * (period - instruction.val - 1) + (10 - offset.val)) / 10 = _
  rw [Nat.add_comm,
    Nat.add_mul_div_left (10 - offset.val) (period - instruction.val - 1) (by decide)]
  rw [Nat.div_eq_of_lt (by omega : 10 - offset.val < 10)]
  simp

@[simp]
theorem instructionAt_objectTrackPhase {period : Nat} (instruction : Fin period)
    (offset : Fin 10) (offset_pos : 0 < offset.val) :
    instructionAt (objectTrackPhase instruction offset offset_pos) = instruction := by
  apply Fin.ext
  simp [instructionAt, Fin.rev, phaseBlock_objectTrackPhase]
  omega

/-- Track read inside an epsilon object. -/
def epsilonPhase {period : Nat} (instruction : Fin period) : Fin (deletionWidth period) :=
  objectTrackPhase instruction ⟨3, by decide⟩ (by decide)

/-- Track read inside a zero object. -/
def zeroPhase {period : Nat} (instruction : Fin period) : Fin (deletionWidth period) :=
  objectTrackPhase instruction ⟨5, by decide⟩ (by decide)

/-- Track read inside a one object. -/
def onePhase {period : Nat} (instruction : Fin period) : Fin (deletionWidth period) :=
  objectTrackPhase instruction ⟨7, by decide⟩ (by decide)

@[simp]
theorem epsilonPhase_mod {period : Nat} (instruction : Fin period) :
    (epsilonPhase instruction).val % 10 = 7 := by
  simp only [epsilonPhase, objectTrackPhase_mod]

@[simp]
theorem zeroPhase_mod {period : Nat} (instruction : Fin period) :
    (zeroPhase instruction).val % 10 = 5 := by
  simp only [zeroPhase, objectTrackPhase_mod]

@[simp]
theorem onePhase_mod {period : Nat} (instruction : Fin period) :
    (onePhase instruction).val % 10 = 3 := by
  simp only [onePhase, objectTrackPhase_mod]

@[simp]
theorem instructionAt_epsilonPhase {period : Nat} (instruction : Fin period) :
    instructionAt (epsilonPhase instruction) = instruction := by
  simp [epsilonPhase]

@[simp]
theorem instructionAt_zeroPhase {period : Nat} (instruction : Fin period) :
    instructionAt (zeroPhase instruction) = instruction := by
  simp [zeroPhase]

@[simp]
theorem instructionAt_onePhase {period : Nat} (instruction : Fin period) :
    instructionAt (onePhase instruction) = instruction := by
  simp [onePhase]

theorem deletionWidth_sub_one_mod {period : Nat} (period_pos : 0 < period) :
    (deletionWidth period - 1) % 10 = 9 := by
  have normal : deletionWidth period - 1 = 10 * (period - 1) + 9 := by
    simp only [deletionWidth]
    omega
  rw [normal]
  simp [Nat.add_mod, Nat.mul_mod]

theorem epsilonPhase_ne_last {period : Nat} (period_pos : 0 < period)
    (instruction : Fin period) :
    (epsilonPhase instruction).val ≠ deletionWidth period - 1 := by
  intro equality
  have residues := congrArg (· % 10) equality
  change (epsilonPhase instruction).val % 10 = (deletionWidth period - 1) % 10 at residues
  rw [epsilonPhase_mod, deletionWidth_sub_one_mod period_pos] at residues
  omega

theorem zeroPhase_ne_last {period : Nat} (period_pos : 0 < period)
    (instruction : Fin period) :
    (zeroPhase instruction).val ≠ deletionWidth period - 1 := by
  intro equality
  have residues := congrArg (· % 10) equality
  change (zeroPhase instruction).val % 10 = (deletionWidth period - 1) % 10 at residues
  rw [zeroPhase_mod, deletionWidth_sub_one_mod period_pos] at residues
  omega

theorem onePhase_ne_last {period : Nat} (period_pos : 0 < period)
    (instruction : Fin period) :
    (onePhase instruction).val ≠ deletionWidth period - 1 := by
  intro equality
  have residues := congrArg (· % 10) equality
  change (onePhase instruction).val % 10 = (deletionWidth period - 1) % 10 at residues
  rw [onePhase_mod, deletionWidth_sub_one_mod period_pos] at residues
  omega

theorem objectEntryPhase_ne_last {period : Nat} (period_pos : 0 < period)
    (instruction : Fin period) :
    (objectEntryPhase instruction).val ≠ deletionWidth period - 1 := by
  intro equality
  have residues := congrArg (· % 10) equality
  change (objectEntryPhase instruction).val % 10 = (deletionWidth period - 1) % 10 at residues
  rw [objectEntryPhase_mod, deletionWidth_sub_one_mod period_pos] at residues
  omega

@[simp]
theorem tableTrack_objectEntryPhase {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase instruction : Fin period) (period_pos : 0 < period) :
    tableTrack system input haltPhase period_pos (objectEntryPhase instruction) =
      ⟨List.replicate (trackWidth system input) .c, by simp⟩ := by
  simp [tableTrack, objectEntryPhase_ne_last period_pos, objectEntryPhase_mod]

@[simp]
theorem tableTrack_epsilonPhase {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase instruction : Fin period) (period_pos : 0 < period) :
    tableTrack system input haltPhase period_pos (epsilonPhase instruction) =
      epsilonTrack system input period_pos (instruction.val = 0) := by
  simp [tableTrack, epsilonPhase_ne_last period_pos, epsilonPhase_mod,
    instructionAt_epsilonPhase]

@[simp]
theorem tableTrack_zeroPhase {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase instruction : Fin period) (period_pos : 0 < period) :
    tableTrack system input haltPhase period_pos (zeroPhase instruction) =
      epsilonTrack system input period_pos (instruction.val = 0) := by
  simp [tableTrack, zeroPhase_ne_last period_pos, zeroPhase_mod, instructionAt_zeroPhase]

@[simp]
theorem tableTrack_onePhase {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase instruction : Fin period) (period_pos : 0 < period) :
    tableTrack system input haltPhase period_pos (onePhase instruction) =
      if instruction = haltPhase then
        haltingTrack system input
      else
        appendantTrack system input period_pos instruction (instruction.val = 0) := by
  simp [tableTrack, onePhase_ne_last period_pos, onePhase_mod, instructionAt_onePhase]

/-- A raw compiler word is shift-neutral and emits only raw compiler words. -/
theorem read_rawObject {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase instruction : Fin period) (period_pos : 0 < period) (rest : List TagLetter)
    (phase_fits : (objectEntryPhase instruction).val ≤ rest.length) :
    TagReaches (deletionWidth period) (compiledOutput system input haltPhase period_pos)
        ((wholeAppendant system input haltPhase period_pos).drop
            (objectEntryPhase instruction).val ++ rest)
        (rest.drop (objectEntryPhase instruction).val ++
          repeatWord (trackWidth system input)
            (wholeAppendant system input haltPhase period_pos)) := by
  have traversal := read_wholeAppendant_track system input haltPhase period_pos
    (objectEntryPhase instruction) rest phase_fits
  rw [tableTrack_objectEntryPhase] at traversal
  change TagReaches (deletionWidth period) (compiledOutput system input haltPhase period_pos)
      _ (rest.drop (objectEntryPhase instruction).val ++
        expandPrime system input haltPhase period_pos
          (List.replicate (trackWidth system input) .c)) at traversal
  rw [expandPrime_replicate_c] at traversal
  exact traversal

theorem spell_padRight {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) (width : Nat)
    (stem : List TagLetter) :
    spell (compiledOutput system input haltPhase period_pos) (padRight width .c stem) =
      expandPrime system input haltPhase period_pos stem ++
        repeatWord (width - stem.length)
          (wholeAppendant system input haltPhase period_pos) := by
  rw [padRight, spell_append]
  change expandPrime system input haltPhase period_pos stem ++
      expandPrime system input haltPhase period_pos
        (List.replicate (width - stem.length) .c) = _
  rw [expandPrime_replicate_c]

theorem spell_epsilonTrack_nonwrap {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase : Fin period) (period_pos : 0 < period) :
    spell (compiledOutput system input haltPhase period_pos)
        (epsilonTrack system input period_pos false).val =
      repeatWord period (epsilonObject system input haltPhase period_pos) ++
        repeatWord (trackWidth system input - 11 * period)
          (wholeAppendant system input haltPhase period_pos) := by
  rw [show (epsilonTrack system input period_pos false).val =
      padRight (trackWidth system input) .c (repeatWord period epsilonPrime) by
    rfl]
  rw [spell_padRight, expandPrime_repeatWord]
  change repeatWord period (epsilonObject system input haltPhase period_pos) ++
      repeatWord
          (trackWidth system input - (repeatWord period epsilonPrime).length)
          (wholeAppendant system input haltPhase period_pos) = _
  rw [repeatWord_length, epsilonPrime_length]
  rw [Nat.mul_comm period 11]

theorem epsilonPrime_restore {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase : Fin period) (period_pos : 0 < period) :
    [.b] ++ expandPrime system input haltPhase period_pos epsilonPrime.tail =
      epsilonObject system input haltPhase period_pos := by
  simp [epsilonObject, expandPrime, epsilonPrime, spell, compiledOutput]

theorem spell_epsilonTrack_wrap {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase : Fin period) (period_pos : 0 < period) :
    [.b] ++ spell (compiledOutput system input haltPhase period_pos)
        (epsilonTrack system input period_pos true).val =
      repeatWord period (epsilonObject system input haltPhase period_pos) ++
        repeatWord (trackWidth system input - 11 * period + 1)
          (wholeAppendant system input haltPhase period_pos) := by
  rw [show (epsilonTrack system input period_pos true).val =
      padRight (trackWidth system input) .c
        (epsilonPrime.tail ++ repeatWord (period - 1) epsilonPrime) by rfl]
  rw [spell_padRight, expandPrime_append]
  change [.b] ++
      (expandPrime system input haltPhase period_pos epsilonPrime.tail ++
        expandPrime system input haltPhase period_pos
          (repeatWord (period - 1) epsilonPrime)) ++ _ = _
  rw [expandPrime_repeatWord, ← List.append_assoc, epsilonPrime_restore]
  have period_split : period = period - 1 + 1 := by omega
  rw [show repeatWord period (epsilonObject system input haltPhase period_pos) =
      epsilonObject system input haltPhase period_pos ++
        repeatWord (period - 1) (epsilonObject system input haltPhase period_pos) by
    calc
      repeatWord period (epsilonObject system input haltPhase period_pos) =
          repeatWord (period - 1 + 1)
            (epsilonObject system input haltPhase period_pos) :=
        congrArg (fun count => repeatWord count
          (epsilonObject system input haltPhase period_pos)) period_split
      _ = _ := repeatWord_succ_left _ _]
  congr 1
  have stem_length :
      (epsilonPrime.tail ++ repeatWord (period - 1) epsilonPrime).length =
        11 * period - 1 := by
    rw [List.length_append, List.length_tail, epsilonPrime_length, repeatWord_length,
      epsilonPrime_length]
    omega
  rw [stem_length]
  congr 1
  have width_bound := epsilon_fixed_fits system input period_pos
  rw [repeatWord_length, epsilonPrime_length] at width_bound
  omega

theorem encodePrimes_starts_b (bit : Bool) (bits : List Bool) :
    encodePrimes (bit :: bits) = .b :: (encodePrimes (bit :: bits)).tail := by
  cases bit <;> simp [encodePrimes, bitPrime]

theorem encodePrimes_restore {period : Nat} (system : CyclicTag period)
    (input bits : List Bool) (haltPhase : Fin period) (period_pos : 0 < period)
    (bits_nonempty : bits ≠ []) :
    [.b] ++ expandPrime system input haltPhase period_pos (encodePrimes bits).tail =
      expandPrime system input haltPhase period_pos (encodePrimes bits) := by
  obtain ⟨bit, bits, rfl⟩ := List.exists_cons_of_ne_nil bits_nonempty
  rw [encodePrimes_starts_b]
  simp [expandPrime, spell, compiledOutput]

theorem spell_appendantTrack_nonwrap {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase instruction : Fin period) (period_pos : 0 < period) :
    spell (compiledOutput system input haltPhase period_pos)
        (appendantTrack system input period_pos instruction false).val =
      ((system.appendant instruction).map
          (bitObject system input haltPhase period_pos)).join ++
        repeatWord
          (trackWidth system input - 11 * (system.appendant instruction).length)
          (wholeAppendant system input haltPhase period_pos) := by
  rw [show (appendantTrack system input period_pos instruction false).val =
      padRight (trackWidth system input) .c
        (encodePrimes (system.appendant instruction)) by rfl]
  rw [spell_padRight, expandPrime_encodePrimes, encodePrimes_length]

theorem spell_appendantTrack_wrap {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase instruction : Fin period) (period_pos : 0 < period)
    (appendant_nonempty : system.appendant instruction ≠ []) :
    [.b] ++ spell (compiledOutput system input haltPhase period_pos)
        (appendantTrack system input period_pos instruction true).val =
      ((system.appendant instruction).map
          (bitObject system input haltPhase period_pos)).join ++
        repeatWord
          (trackWidth system input - 11 * (system.appendant instruction).length + 1)
          (wholeAppendant system input haltPhase period_pos) := by
  rw [show (appendantTrack system input period_pos instruction true).val =
      padRight (trackWidth system input) .c
        (encodePrimes (system.appendant instruction)).tail by rfl]
  rw [spell_padRight]
  change [.b] ++
      (expandPrime system input haltPhase period_pos
          (encodePrimes (system.appendant instruction)).tail ++ _) = _
  rw [← List.append_assoc,
    encodePrimes_restore system input _ haltPhase period_pos appendant_nonempty]
  rw [expandPrime_encodePrimes]
  congr 1
  have tail_length : (encodePrimes (system.appendant instruction)).tail.length =
      11 * (system.appendant instruction).length - 1 := by
    rw [List.length_tail, encodePrimes_length]
  rw [tail_length]
  congr 1
  have width_bound := appendant_fixed_fits system input period_pos instruction
  rw [encodePrimes_length] at width_bound
  have scaled_pos : 0 < 11 * (system.appendant instruction).length :=
    Nat.mul_pos (by decide) (List.length_pos.mpr appendant_nonempty)
  omega

theorem spell_haltingTrack {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) :
    spell (compiledOutput system input haltPhase period_pos) (haltingTrack system input).val =
      [.b] ++ repeatWord (trackWidth system input - 1)
        (wholeAppendant system input haltPhase period_pos) := by
  change spell (compiledOutput system input haltPhase period_pos)
      (.b :: List.replicate (trackWidth system input - 1) .c) = _
  simp [spell, compiledOutput, repeatWord]

/-- Garbage packet emitted when a zero or epsilon object is read. -/
def silentEmission {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase instruction : Fin period) (period_pos : 0 < period) : List TagLetter :=
  repeatWord period (epsilonObject system input haltPhase period_pos) ++
    repeatWord
      (trackWidth system input - 11 * period + if instruction.val = 0 then 1 else 0)
      (wholeAppendant system input haltPhase period_pos)

theorem silentEmission_eq {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase instruction : Fin period) (period_pos : 0 < period) :
    (if instruction.val = 0 then [.b] else []) ++
        spell (compiledOutput system input haltPhase period_pos)
          (epsilonTrack system input period_pos (instruction.val = 0)).val =
      silentEmission system input haltPhase instruction period_pos := by
  by_cases instruction_zero : instruction.val = 0
  · simp only [instruction_zero, ↓reduceIte]
    simpa [silentEmission, instruction_zero] using
      spell_epsilonTrack_wrap system input haltPhase period_pos
  · simp only [instruction_zero, ↓reduceIte, List.nil_append]
    simpa [silentEmission, instruction_zero] using
      spell_epsilonTrack_nonwrap system input haltPhase period_pos

/-- Normal emission of a one object: encoded appendant followed by shift-neutral garbage. -/
def appendantEmission {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase instruction : Fin period) (period_pos : 0 < period) : List TagLetter :=
  ((system.appendant instruction).map
      (bitObject system input haltPhase period_pos)).join ++
    repeatWord
      (trackWidth system input - 11 * (system.appendant instruction).length +
        if instruction.val = 0 then 1 else 0)
      (wholeAppendant system input haltPhase period_pos)

theorem appendantEmission_eq {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase instruction : Fin period) (period_pos : 0 < period)
    (appendant_nonempty_at_zero : instruction.val = 0 → system.appendant instruction ≠ []) :
    (if instruction.val = 0 then [.b] else []) ++
        spell (compiledOutput system input haltPhase period_pos)
          (appendantTrack system input period_pos instruction (instruction.val = 0)).val =
      appendantEmission system input haltPhase instruction period_pos := by
  by_cases instruction_zero : instruction.val = 0
  · simp only [instruction_zero, ↓reduceIte]
    simpa [appendantEmission, instruction_zero] using
      spell_appendantTrack_wrap system input haltPhase instruction period_pos
        (appendant_nonempty_at_zero instruction_zero)
  · simp only [instruction_zero, ↓reduceIte, List.nil_append]
    simpa [appendantEmission, instruction_zero] using
      spell_appendantTrack_nonwrap system input haltPhase instruction period_pos

/-- Reading an epsilon object emits only shift-neutral garbage. -/
theorem read_epsilonObject {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase instruction : Fin period) (period_pos : 0 < period) (rest : List TagLetter)
    (track_fits : (epsilonPhase instruction).val ≤
      (List.replicate 6 TagLetter.b ++ rest).length) :
    TagReaches (deletionWidth period) (compiledOutput system input haltPhase period_pos)
        ((epsilonObject system input haltPhase period_pos).drop
            (objectEntryPhase instruction).val ++ rest)
        (rest.drop (objectEntryPhase (CyclicTag.shift instruction 1)).val ++
          silentEmission system input haltPhase instruction period_pos) := by
  have read := read_paddedObject system input haltPhase instruction period_pos
    ⟨3, by decide⟩ (by decide) rest track_fits
  rw [paddedObject_eq_epsilonObject] at read
  have phase_eq : objectTrackPhase instruction ⟨3, by decide⟩ (by decide) =
      epsilonPhase instruction := rfl
  rw [phase_eq] at read
  rw [tableTrack_epsilonPhase] at read
  rw [List.append_assoc] at read
  rw [silentEmission_eq] at read
  exact read

/-- Reading a zero object has the same garbage-only emission as an epsilon object. -/
theorem read_zeroObject {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase instruction : Fin period) (period_pos : 0 < period) (rest : List TagLetter)
    (track_fits : (zeroPhase instruction).val ≤
      (List.replicate 4 TagLetter.b ++ rest).length) :
    TagReaches (deletionWidth period) (compiledOutput system input haltPhase period_pos)
        ((bitObject system input haltPhase period_pos false).drop
            (objectEntryPhase instruction).val ++ rest)
        (rest.drop (objectEntryPhase (CyclicTag.shift instruction 1)).val ++
          silentEmission system input haltPhase instruction period_pos) := by
  have read := read_paddedObject system input haltPhase instruction period_pos
    ⟨5, by decide⟩ (by decide) rest track_fits
  rw [paddedObject_eq_bitObject_false] at read
  have phase_eq : objectTrackPhase instruction ⟨5, by decide⟩ (by decide) =
      zeroPhase instruction := rfl
  rw [phase_eq] at read
  rw [tableTrack_zeroPhase] at read
  rw [List.append_assoc] at read
  rw [silentEmission_eq] at read
  exact read

/-- Reading an ordinary one object emits the selected cyclic appendant and trailing garbage. -/
theorem read_oneObject {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase instruction : Fin period) (period_pos : 0 < period)
    (not_halting : instruction ≠ haltPhase)
    (appendant_nonempty_at_zero : instruction.val = 0 → system.appendant instruction ≠ [])
    (rest : List TagLetter)
    (track_fits : (onePhase instruction).val ≤
      (List.replicate 2 TagLetter.b ++ rest).length) :
    TagReaches (deletionWidth period) (compiledOutput system input haltPhase period_pos)
        ((bitObject system input haltPhase period_pos true).drop
            (objectEntryPhase instruction).val ++ rest)
        (rest.drop (objectEntryPhase (CyclicTag.shift instruction 1)).val ++
          appendantEmission system input haltPhase instruction period_pos) := by
  have read := read_paddedObject system input haltPhase instruction period_pos
    ⟨7, by decide⟩ (by decide) rest track_fits
  rw [paddedObject_eq_bitObject_true] at read
  have phase_eq : objectTrackPhase instruction ⟨7, by decide⟩ (by decide) =
      onePhase instruction := rfl
  rw [phase_eq] at read
  rw [tableTrack_onePhase, if_neg not_halting] at read
  rw [List.append_assoc] at read
  rw [appendantEmission_eq system input haltPhase instruction period_pos
    appendant_nonempty_at_zero] at read
  exact read

/-- Reading a one at the distinguished phase initiates the all-`b` halting cascade. -/
theorem read_haltingObject {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) (haltPhase_nonzero : haltPhase.val ≠ 0)
    (rest : List TagLetter)
    (track_fits : (onePhase haltPhase).val ≤
      (List.replicate 2 TagLetter.b ++ rest).length) :
    TagReaches (deletionWidth period) (compiledOutput system input haltPhase period_pos)
        ((bitObject system input haltPhase period_pos true).drop
            (objectEntryPhase haltPhase).val ++ rest)
        (rest.drop (objectEntryPhase (CyclicTag.shift haltPhase 1)).val ++ [.b] ++
          repeatWord (trackWidth system input - 1)
            (wholeAppendant system input haltPhase period_pos)) := by
  have read := read_paddedObject system input haltPhase haltPhase period_pos
    ⟨7, by decide⟩ (by decide) rest track_fits
  rw [paddedObject_eq_bitObject_true] at read
  have phase_eq : objectTrackPhase haltPhase ⟨7, by decide⟩ (by decide) =
      onePhase haltPhase := rfl
  rw [phase_eq] at read
  rw [tableTrack_onePhase, if_pos rfl] at read
  simp only [haltPhase_nonzero, ↓reduceIte, List.nil_append] at read
  rw [spell_haltingTrack] at read
  simpa [List.append_assoc] using read

end MatrixMortality.Undecidability.NearyCompiler
