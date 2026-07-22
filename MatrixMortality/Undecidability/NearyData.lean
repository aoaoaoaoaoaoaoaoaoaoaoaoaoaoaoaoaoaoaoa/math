import MatrixMortality.Undecidability.NearySimulation

/-!
# Semantic data layer for Neary's compiler

The exact object traversals are assembled into a typed stream of cyclic data and shift-neutral
garbage. The terminal theorem simulates one arbitrary ordinary cyclic-tag pulse, including every
garbage prefix, while preserving a final garbage reserve.
-/

namespace MatrixMortality.Undecidability.NearyCompiler

/-- Two shift-neutral garbage atoms used by Neary's simulation invariant. -/
inductive JunkAtom where
  | raw
  | packet
  deriving DecidableEq, Repr

/-- Concrete word represented by one garbage atom. -/
def junkAtomWord {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) : JunkAtom → List TagLetter
  | .raw => wholeAppendant system input haltPhase period_pos
  | .packet => repeatWord period (epsilonObject system input haltPhase period_pos)

/-- Number of deletion blocks in one garbage atom. -/
def junkAtomWeight {period : Nat} (system : CyclicTag period) (input : List Bool) :
    JunkAtom → Nat
  | .raw => trackWidth system input
  | .packet => period * trackWidth system input + 1

/-- Concatenate a finite garbage code. -/
def encodeJunk {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) (code : List JunkAtom) :
    List TagLetter :=
  spell (junkAtomWord system input haltPhase period_pos) code

@[simp]
theorem encodeJunk_nil {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) :
    encodeJunk system input haltPhase period_pos [] = [] := rfl

@[simp]
theorem encodeJunk_cons {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) (atom : JunkAtom)
    (code : List JunkAtom) :
    encodeJunk system input haltPhase period_pos (atom :: code) =
      junkAtomWord system input haltPhase period_pos atom ++
        encodeJunk system input haltPhase period_pos code := rfl

theorem encodeJunk_append {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) (left right : List JunkAtom) :
    encodeJunk system input haltPhase period_pos (left ++ right) =
      encodeJunk system input haltPhase period_pos left ++
        encodeJunk system input haltPhase period_pos right := by
  exact spell_append _ _ _

theorem epsilonObject_length {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase : Fin period) (period_pos : 0 < period) :
    (epsilonObject system input haltPhase period_pos).length =
      deletionWidth period * trackWidth system input + 10 := by
  rw [epsilonObject_eq]
  simp [wholeAppendant_length]

theorem junkAtomWord_length {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase : Fin period) (period_pos : 0 < period)
    (atom : JunkAtom) :
    (junkAtomWord system input haltPhase period_pos atom).length =
      deletionWidth period * junkAtomWeight system input atom := by
  cases atom with
  | raw => exact wholeAppendant_length system input haltPhase period_pos
  | packet =>
      rw [junkAtomWord, repeatWord_length, epsilonObject_length]
      simp only [junkAtomWeight, deletionWidth]
      ring

theorem junkAtomWord_long {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase : Fin period) (period_pos : 0 < period)
    (atom : JunkAtom) :
    deletionWidth period ≤ (junkAtomWord system input haltPhase period_pos atom).length := by
  rw [junkAtomWord_length]
  exact Nat.le_mul_of_pos_right _ <| by
    cases atom with
    | raw => exact trackWidth_pos system input
    | packet => simp [junkAtomWeight]

theorem encodeJunk_nonempty_long {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase : Fin period) (period_pos : 0 < period)
    (code : List JunkAtom) (code_nonempty : code ≠ []) :
    deletionWidth period ≤ (encodeJunk system input haltPhase period_pos code).length := by
  obtain ⟨atom, code, rfl⟩ := List.exists_cons_of_ne_nil code_nonempty
  rw [encodeJunk_cons, List.length_append]
  exact (junkAtomWord_long system input haltPhase period_pos atom).trans
    (Nat.le_add_right _ _)

theorem encodeJunk_replicate_raw {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase : Fin period) (period_pos : 0 < period) (count : Nat) :
    encodeJunk system input haltPhase period_pos (List.replicate count .raw) =
      repeatWord count (wholeAppendant system input haltPhase period_pos) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, encodeJunk_cons, ih]
      exact repeatWord_succ_left _ _ |>.symm

theorem silentEmission_eq_encodeJunk {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase instruction : Fin period) (period_pos : 0 < period) :
    silentEmission system input haltPhase instruction period_pos =
      encodeJunk system input haltPhase period_pos
        (.packet :: List.replicate
          (trackWidth system input - 11 * period + if instruction.val = 0 then 1 else 0)
          .raw) := by
  rw [encodeJunk_cons, encodeJunk_replicate_raw]
  rfl

theorem appendantEmission_eq_objects_junk {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase instruction : Fin period) (period_pos : 0 < period) :
    appendantEmission system input haltPhase instruction period_pos =
      ((system.appendant instruction).map
          (bitObject system input haltPhase period_pos)).join ++
        encodeJunk system input haltPhase period_pos
          (List.replicate
            (trackWidth system input - 11 * (system.appendant instruction).length +
              if instruction.val = 0 then 1 else 0)
            .raw) := by
  rw [appendantEmission, encodeJunk_replicate_raw]

/-- A run of epsilon objects preserves the abstract phase and emits a garbage code. -/
theorem read_epsilonRun {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) (count : Nat)
    (instruction : Fin period) (rest : List TagLetter)
    (rest_long : deletionWidth period ≤ rest.length) :
    ∃ code : List JunkAtom,
      (count = 0 ∨ code ≠ []) ∧
        TagReaches (deletionWidth period) (compiledOutput system input haltPhase period_pos)
          ((repeatWord count (epsilonObject system input haltPhase period_pos) ++ rest).drop
            (objectEntryPhase instruction).val)
          (rest.drop (objectEntryPhase (CyclicTag.shift instruction count)).val ++
            encodeJunk system input haltPhase period_pos code) := by
  induction count generalizing instruction rest with
  | zero =>
      refine ⟨[], Or.inl rfl, ?_⟩
      simp only [repeatWord, List.replicate_zero, List.join_nil, List.nil_append,
        CyclicTag.shift_zero, encodeJunk_nil, List.append_nil]
      exact Relation.ReflTransGen.refl
  | succ count ih =>
      let epsilon := epsilonObject system input haltPhase period_pos
      let remainder := repeatWord count epsilon
      let nextInstruction := CyclicTag.shift instruction 1
      let emission := silentEmission system input haltPhase instruction period_pos
      let emissionCode : List JunkAtom :=
        .packet :: List.replicate
          (trackWidth system input - 11 * period + if instruction.val = 0 then 1 else 0)
          .raw
      have epsilon_long : deletionWidth period ≤ epsilon.length := by
        change deletionWidth period ≤
          (epsilonObject system input haltPhase period_pos).length
        rw [epsilonObject_length]
        exact (Nat.le_mul_of_pos_right _ (trackWidth_pos system input)).trans
          (Nat.le_add_right _ _)
      have entry_le_epsilon : (objectEntryPhase instruction).val ≤ epsilon.length :=
        (Nat.le_of_lt (objectEntryPhase instruction).isLt).trans epsilon_long
      have start_split :
          ((repeatWord (count + 1) epsilon ++ rest).drop
              (objectEntryPhase instruction).val) =
            epsilon.drop (objectEntryPhase instruction).val ++ remainder ++ rest := by
        rw [repeatWord_succ_left]
        rw [show epsilon ++ remainder ++ rest = epsilon ++ (remainder ++ rest) by
          simp [List.append_assoc]]
        rw [List.drop_append_of_le_length entry_le_epsilon]
        simp [List.append_assoc]
      have track_fits : (epsilonPhase instruction).val ≤
          (List.replicate 6 TagLetter.b ++ (remainder ++ rest)).length := by
        have phase_lt := (epsilonPhase instruction).isLt
        have rest_le : rest.length ≤
            (List.replicate 6 TagLetter.b ++ (remainder ++ rest)).length := by
          simp only [List.length_append, List.length_replicate]
          omega
        exact (Nat.le_of_lt phase_lt).trans (rest_long.trans rest_le)
      have first := read_epsilonObject system input haltPhase instruction period_pos
        (remainder ++ rest) track_fits
      have emission_eq : emission =
          encodeJunk system input haltPhase period_pos emissionCode := by
        exact silentEmission_eq_encodeJunk system input haltPhase instruction period_pos
      have next_phase_le : (objectEntryPhase nextInstruction).val ≤
          (remainder ++ rest).length := by
        have phase_lt := (objectEntryPhase nextInstruction).isLt
        exact (Nat.le_of_lt phase_lt).trans (rest_long.trans (by simp))
      have intermediate :
          (remainder ++ rest).drop (objectEntryPhase nextInstruction).val ++ emission =
            (remainder ++ (rest ++ emission)).drop
              (objectEntryPhase nextInstruction).val := by
        rw [show remainder ++ (rest ++ emission) = (remainder ++ rest) ++ emission by
          simp [List.append_assoc]]
        rw [List.drop_append_of_le_length next_phase_le]
      have first' : TagReaches (deletionWidth period)
          (compiledOutput system input haltPhase period_pos)
          ((repeatWord (count + 1) epsilon ++ rest).drop
            (objectEntryPhase instruction).val)
          ((remainder ++ (rest ++ emission)).drop
            (objectEntryPhase nextInstruction).val) := by
        rw [start_split]
        rw [← intermediate]
        simpa [List.append_assoc] using first
      have extended_long : deletionWidth period ≤ (rest ++ emission).length :=
        rest_long.trans (by simp)
      obtain ⟨laterCode, _, later⟩ := ih nextInstruction (rest ++ emission) extended_long
      have shifted : CyclicTag.shift nextInstruction count =
          CyclicTag.shift instruction (count + 1) := by
        change CyclicTag.shift (CyclicTag.shift instruction 1) count = _
        rw [CyclicTag.shift_add]
        congr 1
        omega
      rw [shifted] at later
      have final_phase_le :
          (objectEntryPhase (CyclicTag.shift instruction (count + 1))).val ≤ rest.length :=
        (Nat.le_of_lt (objectEntryPhase
          (CyclicTag.shift instruction (count + 1))).isLt).trans rest_long
      rw [List.drop_append_of_le_length final_phase_le] at later
      have composed := Relation.ReflTransGen.trans first' later
      refine ⟨emissionCode ++ laterCode, Or.inr ?_, ?_⟩
      · simp [emissionCode]
      rw [encodeJunk_append, ← emission_eq]
      simpa [TagReaches, epsilon, remainder, nextInstruction, emission,
        List.append_assoc] using composed

/-- Reading one garbage atom preserves the current cyclic instruction and emits garbage. -/
theorem read_junkAtom {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase instruction : Fin period) (period_pos : 0 < period) (atom : JunkAtom)
    (rest : List TagLetter) (rest_long : deletionWidth period ≤ rest.length) :
    ∃ code : List JunkAtom,
      code ≠ [] ∧
        TagReaches (deletionWidth period) (compiledOutput system input haltPhase period_pos)
          ((junkAtomWord system input haltPhase period_pos atom ++ rest).drop
            (objectEntryPhase instruction).val)
          (rest.drop (objectEntryPhase instruction).val ++
            encodeJunk system input haltPhase period_pos code) := by
  cases atom with
  | raw =>
      let rawCode := List.replicate (trackWidth system input) JunkAtom.raw
      have raw_long := junkAtomWord_long system input haltPhase period_pos JunkAtom.raw
      have phase_le : (objectEntryPhase instruction).val ≤
          (wholeAppendant system input haltPhase period_pos).length :=
        (Nat.le_of_lt (objectEntryPhase instruction).isLt).trans raw_long
      have read := read_rawObject system input haltPhase instruction period_pos rest
        ((Nat.le_of_lt (objectEntryPhase instruction).isLt).trans rest_long)
      refine ⟨rawCode, ?_, ?_⟩
      · simp [rawCode, Nat.ne_of_gt (trackWidth_pos system input)]
      rw [show junkAtomWord system input haltPhase period_pos JunkAtom.raw =
          wholeAppendant system input haltPhase period_pos by rfl]
      rw [List.drop_append_of_le_length phase_le]
      rw [encodeJunk_replicate_raw]
      exact read
  | packet =>
      obtain ⟨code, code_nonempty, read⟩ :=
        read_epsilonRun system input haltPhase period_pos period instruction rest rest_long
      refine ⟨code, code_nonempty.resolve_left (Nat.ne_of_gt period_pos), ?_⟩
      rw [CyclicTag.shift_period] at read
      exact read

/-- Reading a garbage code preserves the current cyclic instruction and emits another code. -/
theorem read_junk {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase instruction : Fin period) (period_pos : 0 < period) (code : List JunkAtom)
    (rest : List TagLetter) (rest_long : deletionWidth period ≤ rest.length) :
    ∃ emitted : List JunkAtom,
      (code = [] ∨ emitted ≠ []) ∧
        TagReaches (deletionWidth period) (compiledOutput system input haltPhase period_pos)
          ((encodeJunk system input haltPhase period_pos code ++ rest).drop
            (objectEntryPhase instruction).val)
          (rest.drop (objectEntryPhase instruction).val ++
            encodeJunk system input haltPhase period_pos emitted) := by
  induction code generalizing rest with
  | nil =>
      refine ⟨[], Or.inl rfl, ?_⟩
      simp only [encodeJunk_nil, List.nil_append, List.append_nil]
      exact Relation.ReflTransGen.refl
  | cons atom code ih =>
      let suffix := encodeJunk system input haltPhase period_pos code
      obtain ⟨firstCode, firstCode_nonempty, first⟩ :=
        read_junkAtom system input haltPhase instruction period_pos atom (suffix ++ rest)
          (rest_long.trans (by simp))
      have firstPhaseFits : (objectEntryPhase instruction).val ≤ (suffix ++ rest).length :=
        (Nat.le_of_lt (objectEntryPhase instruction).isLt).trans (rest_long.trans (by simp))
      have intermediate :
          (suffix ++ rest).drop (objectEntryPhase instruction).val ++
              encodeJunk system input haltPhase period_pos firstCode =
            (suffix ++
              (rest ++ encodeJunk system input haltPhase period_pos firstCode)).drop
                (objectEntryPhase instruction).val := by
        rw [show suffix ++
            (rest ++ encodeJunk system input haltPhase period_pos firstCode) =
          (suffix ++ rest) ++ encodeJunk system input haltPhase period_pos firstCode by
            simp [List.append_assoc]]
        rw [List.drop_append_of_le_length firstPhaseFits]
      have first' : TagReaches (deletionWidth period)
          (compiledOutput system input haltPhase period_pos)
          ((encodeJunk system input haltPhase period_pos (atom :: code) ++ rest).drop
            (objectEntryPhase instruction).val)
          ((suffix ++
            (rest ++ encodeJunk system input haltPhase period_pos firstCode)).drop
              (objectEntryPhase instruction).val) := by
        rw [encodeJunk_cons]
        rw [← intermediate]
        simpa [suffix, List.append_assoc] using first
      have extended_long : deletionWidth period ≤
          (rest ++ encodeJunk system input haltPhase period_pos firstCode).length :=
        rest_long.trans (by simp)
      obtain ⟨laterCode, _, later⟩ := ih
        (rest ++ encodeJunk system input haltPhase period_pos firstCode) extended_long
      have finalPhaseFits : (objectEntryPhase instruction).val ≤ rest.length :=
        (Nat.le_of_lt (objectEntryPhase instruction).isLt).trans rest_long
      rw [List.drop_append_of_le_length finalPhaseFits] at later
      have composed := Relation.ReflTransGen.trans first' later
      refine ⟨firstCode ++ laterCode, Or.inr ?_, ?_⟩
      · exact List.append_ne_nil_of_left_ne_nil firstCode_nonempty laterCode
      rw [encodeJunk_append]
      simpa [suffix, List.append_assoc] using composed

/-- Token stream used by the semantic invariant: cyclic data bits interspersed with garbage. -/
inductive DataToken where
  | bit (value : Bool)
  | junk (atom : JunkAtom)
  deriving DecidableEq, Repr

/-- Concrete restricted-tag word represented by one semantic token. -/
def dataTokenWord {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) : DataToken → List TagLetter
  | .bit value => bitObject system input haltPhase period_pos value
  | .junk atom => junkAtomWord system input haltPhase period_pos atom

/-- Concrete restricted-tag word represented by a semantic token stream. -/
def encodeData {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) (tokens : List DataToken) :
    List TagLetter :=
  spell (dataTokenWord system input haltPhase period_pos) tokens

@[simp]
theorem encodeData_nil {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) :
    encodeData system input haltPhase period_pos [] = [] := rfl

@[simp]
theorem encodeData_cons {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) (token : DataToken)
    (tokens : List DataToken) :
    encodeData system input haltPhase period_pos (token :: tokens) =
      dataTokenWord system input haltPhase period_pos token ++
        encodeData system input haltPhase period_pos tokens := rfl

theorem encodeData_append {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) (left right : List DataToken) :
    encodeData system input haltPhase period_pos (left ++ right) =
      encodeData system input haltPhase period_pos left ++
        encodeData system input haltPhase period_pos right := by
  exact spell_append _ _ _

theorem encodeData_junk {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) (code : List JunkAtom) :
    encodeData system input haltPhase period_pos (code.map .junk) =
      encodeJunk system input haltPhase period_pos code := by
  induction code with
  | nil => rfl
  | cons atom code ih => simp [ih, dataTokenWord]

theorem encodeData_bits {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) (bits : List Bool) :
    encodeData system input haltPhase period_pos (bits.map .bit) =
      (bits.map (bitObject system input haltPhase period_pos)).join := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp [ih, dataTokenWord]

/-- Raw-object padding between the encoded cyclic input and the final epsilon packet. -/
def inputGarbageCount {period : Nat} (system : CyclicTag period) (input : List Bool) : Nat :=
  trackWidth system input -
    (deletionWidth period - 2 + (encodePrimes input).length) -
      (repeatWord period epsilonPrime).length

/-- Initial garbage reserve emitted by the input track. -/
def initialJunkCode {period : Nat} (system : CyclicTag period) (input : List Bool) :
    List JunkAtom :=
  List.replicate (inputGarbageCount system input) .raw ++ [.packet]

/-- Initial semantic token stream emitted by the input track. -/
def initialTokens {period : Nat} (system : CyclicTag period) (input : List Bool) :
    List DataToken :=
  input.map .bit ++ (initialJunkCode system input).map .junk

theorem spell_inputTrack {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) :
    spell (compiledOutput system input haltPhase period_pos)
        (inputTrack system input period_pos).val =
      List.replicate (deletionWidth period - 2) .b ++
        encodeData system input haltPhase period_pos (initialTokens system input) := by
  change spell (compiledOutput system input haltPhase period_pos)
      (padBetween (trackWidth system input) .c
        (List.replicate (deletionWidth period - 2) .b ++ encodePrimes input)
        (repeatWord period epsilonPrime)) = _
  unfold padBetween
  simp only [List.length_append, List.length_replicate]
  change spell (compiledOutput system input haltPhase period_pos)
      (List.replicate (deletionWidth period - 2) .b ++ encodePrimes input ++
        List.replicate (inputGarbageCount system input) .c ++
          repeatWord period epsilonPrime) = _
  simp only [spell_append, Function.comp_apply]
  rw [show spell (compiledOutput system input haltPhase period_pos)
      (List.replicate (deletionWidth period - 2) TagLetter.b) =
        List.replicate (deletionWidth period - 2) .b by
      induction deletionWidth period - 2 with
      | zero => rfl
      | succ count ih => simp [spell, compiledOutput, ih]]
  rw [← expandPrime, expandPrime_encodePrimes]
  rw [← expandPrime, expandPrime_replicate_c]
  rw [← expandPrime, expandPrime_repeatWord]
  rw [show expandPrime system input haltPhase period_pos epsilonPrime =
      epsilonObject system input haltPhase period_pos by rfl]
  unfold initialTokens
  rw [encodeData_append, encodeData_bits, encodeData_junk]
  unfold initialJunkCode
  rw [encodeJunk_append, encodeJunk_replicate_raw]
  simp [initialTokens, initialJunkCode, junkAtomWord, inputGarbageCount,
    epsilonObject, List.append_assoc]

/-- Cyclic data obtained by deleting garbage from a semantic token stream. -/
def dataBits : List DataToken → List Bool
  | [] => []
  | .bit value :: tokens => value :: dataBits tokens
  | .junk _ :: tokens => dataBits tokens

@[simp]
theorem dataBits_append (left right : List DataToken) :
    dataBits (left ++ right) = dataBits left ++ dataBits right := by
  induction left with
  | nil => rfl
  | cons token left ih => cases token <;> simp [dataBits, ih]

@[simp]
theorem dataBits_junk (code : List JunkAtom) : dataBits (code.map .junk) = [] := by
  induction code with
  | nil => rfl
  | cons _atom code ih => simp [dataBits, ih]

@[simp]
theorem dataBits_bits (bits : List Bool) : dataBits (bits.map .bit) = bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp [dataBits, ih]

theorem initialJunkCode_nonempty {period : Nat} (system : CyclicTag period)
    (input : List Bool) : initialJunkCode system input ≠ [] := by
  simp [initialJunkCode]

@[simp]
theorem dataBits_initialTokens {period : Nat} (system : CyclicTag period)
    (input : List Bool) : dataBits (initialTokens system input) = input := by
  simp [initialTokens]

theorem spell_inputTrack_drop_initial {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase : Fin period) (period_pos : 0 < period)
    (input_nonempty : input ≠ []) :
    spell (compiledOutput system input haltPhase period_pos)
        ((inputTrack system input period_pos).val.drop (deletionWidth period - 1)) =
      (encodeData system input haltPhase period_pos (initialTokens system input)).drop 1 := by
  let track := (inputTrack system input period_pos).val
  let output := compiledOutput system input haltPhase period_pos
  let count := deletionWidth period - 1
  have take_eq : track.take count = List.replicate count .b :=
    inputTrack_take_initialPadding system input period_pos input_nonempty
  have spell_take : spell output (track.take count) = List.replicate count .b := by
    rw [take_eq]
    induction count with
    | zero => rfl
    | succ count ih => simp [spell, output, compiledOutput, ih]
  have split : spell output track =
      spell output (track.take count) ++ spell output (track.drop count) := by
    rw [← spell_append, List.take_append_drop]
  have dropped : spell output (track.drop count) = (spell output track).drop count := by
    rw [split, spell_take]
    simp
  rw [dropped, spell_inputTrack]
  have beta_large := deletionWidth_large period_pos
  have count_split : count = deletionWidth period - 2 + 1 := by
    simp only [count]
    omega
  rw [count_split]
  simp [List.drop_append_eq_append_drop]

/-- Any stream containing a garbage token represents at least one complete deletion block. -/
theorem encodeData_long_of_junk_mem {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase : Fin period) (period_pos : 0 < period)
    (tokens : List DataToken) (atom : JunkAtom) (member : .junk atom ∈ tokens) :
    deletionWidth period ≤ (encodeData system input haltPhase period_pos tokens).length := by
  induction tokens with
  | nil => simp at member
  | cons token tokens ih =>
      simp only [List.mem_cons] at member
      rw [encodeData_cons, List.length_append]
      rcases member with equality | member
      · subst token
        exact (junkAtomWord_long system input haltPhase period_pos atom).trans
          (Nat.le_add_right _ _)
      · exact (ih member).trans (Nat.le_add_left _ _)

/-- Garbage emitted by an epsilon or zero object. -/
def silentJunkCode {period : Nat} (system : CyclicTag period) (input : List Bool)
    (instruction : Fin period) : List JunkAtom :=
  .packet :: List.replicate
    (trackWidth system input - 11 * period + if instruction.val = 0 then 1 else 0) .raw

/-- Trailing garbage emitted after one nonhalting true bit. -/
def appendantJunkCode {period : Nat} (system : CyclicTag period) (input : List Bool)
    (instruction : Fin period) : List JunkAtom :=
  List.replicate
    (trackWidth system input - 11 * (system.appendant instruction).length +
      if instruction.val = 0 then 1 else 0) .raw

theorem appendantJunkCode_nonempty {period : Nat} (system : CyclicTag period)
    (input : List Bool) (period_pos : 0 < period) (instruction : Fin period) :
    appendantJunkCode system input instruction ≠ [] := by
  have appendant_bounded := appendant_length_le_mass system instruction
  have safety_bounded := safetyBound_le_trackWidth system input period_pos
  have count_pos : 0 <
      trackWidth system input - 11 * (system.appendant instruction).length +
        (if instruction.val = 0 then 1 else 0) := by
    unfold safetyBound at safety_bounded
    omega
  simp [appendantJunkCode, Nat.ne_of_gt count_pos]

theorem silentEmission_eq_encodeData {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase instruction : Fin period) (period_pos : 0 < period) :
    silentEmission system input haltPhase instruction period_pos =
      encodeData system input haltPhase period_pos
        ((silentJunkCode system input instruction).map .junk) := by
  rw [encodeData_junk, silentEmission_eq_encodeJunk]
  rfl

theorem appendantEmission_eq_encodeData {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase instruction : Fin period) (period_pos : 0 < period) :
    appendantEmission system input haltPhase instruction period_pos =
      encodeData system input haltPhase period_pos
        ((system.appendant instruction).map .bit ++
          (appendantJunkCode system input instruction).map .junk) := by
  rw [encodeData_append, encodeData_bits, encodeData_junk,
    appendantEmission_eq_objects_junk]
  rfl

/-- Read one zero data token and advance the cyclic instruction. -/
theorem read_zeroToken {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase instruction : Fin period) (period_pos : 0 < period) (rest : List TagLetter)
    (rest_long : deletionWidth period ≤ rest.length) :
    TagReaches (deletionWidth period) (compiledOutput system input haltPhase period_pos)
      ((dataTokenWord system input haltPhase period_pos (.bit false) ++ rest).drop
        (objectEntryPhase instruction).val)
      (rest.drop (objectEntryPhase (CyclicTag.shift instruction 1)).val ++
        encodeData system input haltPhase period_pos
          ((silentJunkCode system input instruction).map .junk)) := by
  have track_fits : (zeroPhase instruction).val ≤
      (List.replicate 4 TagLetter.b ++ rest).length := by
    have := (Nat.le_of_lt (zeroPhase instruction).isLt).trans rest_long
    simp only [List.length_append, List.length_replicate]
    omega
  have token_long : deletionWidth period ≤
      (bitObject system input haltPhase period_pos false).length := by
    rw [bitObject_eq_false]
    simp only [List.length_append, List.length_replicate, wholeAppendant_length]
    have core := Nat.le_mul_of_pos_right (deletionWidth period) (trackWidth_pos system input)
    omega
  have phase_le_token : (objectEntryPhase instruction).val ≤
      (bitObject system input haltPhase period_pos false).length :=
    (Nat.le_of_lt (objectEntryPhase instruction).isLt).trans token_long
  have read := read_zeroObject system input haltPhase instruction period_pos rest track_fits
  rw [silentEmission_eq_encodeData] at read
  rw [dataTokenWord, List.drop_append_of_le_length phase_le_token]
  exact read

/-- Read one ordinary true data token and advance the cyclic instruction. -/
theorem read_oneToken {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase instruction : Fin period) (period_pos : 0 < period)
    (not_halting : instruction ≠ haltPhase)
    (appendant_nonempty_at_zero : instruction.val = 0 → system.appendant instruction ≠ [])
    (rest : List TagLetter) (rest_long : deletionWidth period ≤ rest.length) :
    TagReaches (deletionWidth period) (compiledOutput system input haltPhase period_pos)
      ((dataTokenWord system input haltPhase period_pos (.bit true) ++ rest).drop
        (objectEntryPhase instruction).val)
      (rest.drop (objectEntryPhase (CyclicTag.shift instruction 1)).val ++
        encodeData system input haltPhase period_pos
          ((system.appendant instruction).map .bit ++
            (appendantJunkCode system input instruction).map .junk)) := by
  have track_fits : (onePhase instruction).val ≤
      (List.replicate 2 TagLetter.b ++ rest).length := by
    have := (Nat.le_of_lt (onePhase instruction).isLt).trans rest_long
    simp only [List.length_append, List.length_replicate]
    omega
  have token_long : deletionWidth period ≤
      (bitObject system input haltPhase period_pos true).length := by
    rw [bitObject_eq_true]
    simp only [List.length_append, List.length_replicate, wholeAppendant_length]
    have core := Nat.le_mul_of_pos_right (deletionWidth period) (trackWidth_pos system input)
    omega
  have phase_le_token : (objectEntryPhase instruction).val ≤
      (bitObject system input haltPhase period_pos true).length :=
    (Nat.le_of_lt (objectEntryPhase instruction).isLt).trans token_long
  have read := read_oneObject system input haltPhase instruction period_pos not_halting
    appendant_nonempty_at_zero rest track_fits
  rw [appendantEmission_eq_encodeData] at read
  rw [dataTokenWord, List.drop_append_of_le_length phase_le_token]
  exact read

/-- Semantic tokens appended after one ordinary cyclic data bit. -/
def ordinaryBitEmission {period : Nat} (system : CyclicTag period) (input : List Bool)
    (instruction : Fin period) : Bool → List DataToken
  | false => (silentJunkCode system input instruction).map .junk
  | true =>
      (system.appendant instruction).map .bit ++
        (appendantJunkCode system input instruction).map .junk

@[simp]
theorem dataBits_ordinaryBitEmission {period : Nat} (system : CyclicTag period)
    (input : List Bool) (instruction : Fin period) (value : Bool) :
    dataBits (ordinaryBitEmission system input instruction value) =
      if value then system.appendant instruction else [] := by
  cases value <;> simp [ordinaryBitEmission]

theorem ordinaryBitEmission_has_junk {period : Nat} (system : CyclicTag period)
    (input : List Bool) (period_pos : 0 < period) (instruction : Fin period)
    (value : Bool) :
    ∃ atom, .junk atom ∈ ordinaryBitEmission system input instruction value := by
  cases value with
  | false => exact ⟨.packet, by simp [ordinaryBitEmission, silentJunkCode]⟩
  | true =>
      obtain ⟨atom, code, code_eq⟩ :=
        List.exists_cons_of_ne_nil (appendantJunkCode_nonempty system input period_pos instruction)
      refine ⟨atom, ?_⟩
      simp [ordinaryBitEmission, code_eq]

/-- Uniform traversal of an ordinary, nonhalting cyclic data bit. -/
theorem read_bitToken {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase instruction : Fin period) (period_pos : 0 < period)
    (not_halting : instruction ≠ haltPhase)
    (appendant_nonempty_at_zero : instruction.val = 0 → system.appendant instruction ≠ [])
    (value : Bool) (rest : List TagLetter) (rest_long : deletionWidth period ≤ rest.length) :
    TagReaches (deletionWidth period) (compiledOutput system input haltPhase period_pos)
      ((dataTokenWord system input haltPhase period_pos (.bit value) ++ rest).drop
        (objectEntryPhase instruction).val)
      (rest.drop (objectEntryPhase (CyclicTag.shift instruction 1)).val ++
        encodeData system input haltPhase period_pos
          (ordinaryBitEmission system input instruction value)) := by
  cases value with
  | false =>
      simpa [ordinaryBitEmission] using
        read_zeroToken system input haltPhase instruction period_pos rest rest_long
  | true =>
      simpa [ordinaryBitEmission] using
        read_oneToken system input haltPhase instruction period_pos not_halting
          appendant_nonempty_at_zero rest rest_long

theorem dataTokenWord_bit_long {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase : Fin period) (period_pos : 0 < period) (value : Bool) :
    deletionWidth period ≤
      (dataTokenWord system input haltPhase period_pos (.bit value)).length := by
  cases value with
  | false =>
      change deletionWidth period ≤
        (bitObject system input haltPhase period_pos false).length
      rw [bitObject_eq_false]
      simp only [List.length_append, List.length_replicate, wholeAppendant_length]
      have core := Nat.le_mul_of_pos_right (deletionWidth period) (trackWidth_pos system input)
      omega
  | true =>
      change deletionWidth period ≤
        (bitObject system input haltPhase period_pos true).length
      rw [bitObject_eq_true]
      simp only [List.length_append, List.length_replicate, wholeAppendant_length]
      have core := Nat.le_mul_of_pos_right (deletionWidth period) (trackWidth_pos system input)
      omega

/-- Consume all garbage before the next data bit, then simulate that cyclic-tag transition. -/
theorem read_dataPulse {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase instruction : Fin period) (period_pos : 0 < period)
    (not_halting : instruction ≠ haltPhase)
    (appendant_nonempty_at_zero : instruction.val = 0 → system.appendant instruction ≠ [])
    (leading : List JunkAtom) (value : Bool) (tail : List DataToken)
    (tailAtom : JunkAtom) (tail_has_junk : .junk tailAtom ∈ tail) :
    ∃ emittedLeading : List JunkAtom,
      TagReaches (deletionWidth period) (compiledOutput system input haltPhase period_pos)
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
  have bitRead := read_bitToken system input haltPhase instruction period_pos not_halting
    appendant_nonempty_at_zero value (tailWord ++ leadingEmission) extended_long
  let nextInstruction := CyclicTag.shift instruction 1
  let bitEmission :=
    encodeData system input haltPhase period_pos
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
      (tailWord ++ leadingEmission).drop (objectEntryPhase nextInstruction).val ++ bitEmission =
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
  exact ⟨emittedLeading, Relation.ReflTransGen.trans leadingRead' bitRead⟩

/-- A token stream ends in a garbage token. -/
inductive EndsInJunk : List DataToken → Prop
  | last (atom : JunkAtom) : EndsInJunk [.junk atom]
  | cons (token : DataToken) {tokens : List DataToken} :
      EndsInJunk tokens → EndsInJunk (token :: tokens)

namespace EndsInJunk

theorem prepend (front : List DataToken) {tokens : List DataToken}
    (ends : EndsInJunk tokens) : EndsInJunk (front ++ tokens) := by
  induction front with
  | nil => exact ends
  | cons token _frontTail ih => exact .cons token ih

theorem length_pos {tokens : List DataToken} (ends : EndsInJunk tokens) : 0 < tokens.length := by
  cases ends with
  | last => simp
  | cons => simp

theorem junk_map {code : List JunkAtom} (code_nonempty : code ≠ []) :
    EndsInJunk (code.map .junk) := by
  induction code with
  | nil => exact False.elim (code_nonempty rfl)
  | cons atom code ih =>
      by_cases tail_empty : code = []
      · subst code
        exact .last atom
      · exact .cons (.junk atom) (ih tail_empty)

theorem exists_mem {tokens : List DataToken} (ends : EndsInJunk tokens) :
    ∃ atom, .junk atom ∈ tokens := by
  induction ends with
  | last atom => exact ⟨atom, by simp⟩
  | cons token _ ih =>
      obtain ⟨atom, member⟩ := ih
      exact ⟨atom, by simp [member]⟩

end EndsInJunk

/-- Token streams used at macro boundaries retain a final garbage reserve. -/
structure StableData (tokens : List DataToken) : Prop where
  /-- The final token is garbage. -/
  endsInJunk : EndsInJunk tokens
  /-- With no cyclic data left, two garbage tokens remain to sustain the simulation. -/
  reserve : dataBits tokens = [] → 2 ≤ tokens.length

theorem initialTokens_stable {period : Nat} (system : CyclicTag period)
    (input : List Bool) (input_nonempty : input ≠ []) :
    StableData (initialTokens system input) := by
  refine ⟨EndsInJunk.prepend _ <|
    EndsInJunk.junk_map (initialJunkCode_nonempty system input), ?_⟩
  intro no_bits
  exact False.elim (input_nonempty (dataBits_initialTokens system input ▸ no_bits))

theorem ordinaryBitEmission_endsInJunk {period : Nat} (system : CyclicTag period)
    (input : List Bool) (period_pos : 0 < period) (instruction : Fin period)
    (value : Bool) :
    EndsInJunk (ordinaryBitEmission system input instruction value) := by
  cases value with
  | false =>
      exact EndsInJunk.junk_map (by simp [silentJunkCode])
  | true =>
      exact EndsInJunk.prepend _ <|
        EndsInJunk.junk_map (appendantJunkCode_nonempty system input period_pos instruction)

/-- Locate the first cyclic data bit without assuming any shape for the preceding garbage. -/
theorem split_first_dataBit {tokens : List DataToken} (ends : EndsInJunk tokens)
    (value : Bool) (bits : List Bool) (bits_eq : dataBits tokens = value :: bits) :
    ∃ leading : List JunkAtom, ∃ tail : List DataToken,
      tokens = leading.map .junk ++ .bit value :: tail ∧
        dataBits tail = bits ∧ EndsInJunk tail := by
  induction ends with
  | last atom => simp [dataBits] at bits_eq
  | @cons token tokens ends ih =>
      cases token with
      | bit tokenValue =>
          simp only [dataBits, List.cons.injEq] at bits_eq
          obtain ⟨value_eq, tail_eq⟩ := bits_eq
          subst tokenValue
          exact ⟨[], tokens, by simp, tail_eq, ends⟩
      | junk atom =>
          simp only [dataBits] at bits_eq
          obtain ⟨leading, tail, token_eq, tail_eq, tail_ends⟩ := ih bits_eq
          refine ⟨atom :: leading, tail, ?_, tail_eq, tail_ends⟩
          simp [token_eq]

/-- One ordinary pulse preserves the token invariant and realizes the cyclic-tag data update. -/
theorem read_next_dataBit {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase instruction : Fin period) (period_pos : 0 < period)
    (not_halting : instruction ≠ haltPhase)
    (appendant_nonempty_at_zero : instruction.val = 0 → system.appendant instruction ≠ [])
    (tokens : List DataToken) (stable : StableData tokens) (value : Bool) (bits : List Bool)
    (bits_eq : dataBits tokens = value :: bits) :
    ∃ nextTokens : List DataToken,
      StableData nextTokens ∧
        dataBits nextTokens = bits ++ (if value then system.appendant instruction else []) ∧
          TagReaches (deletionWidth period)
            (compiledOutput system input haltPhase period_pos)
            ((encodeData system input haltPhase period_pos tokens).drop
              (objectEntryPhase instruction).val)
            ((encodeData system input haltPhase period_pos nextTokens).drop
              (objectEntryPhase (CyclicTag.shift instruction 1)).val) := by
  obtain ⟨leading, tail, token_eq, tail_eq, tail_ends⟩ :=
    split_first_dataBit stable.endsInJunk value bits bits_eq
  obtain ⟨tailAtom, tail_has_junk⟩ := EndsInJunk.exists_mem tail_ends
  obtain ⟨emittedLeading, read⟩ :=
    read_dataPulse system input haltPhase instruction period_pos not_halting
      appendant_nonempty_at_zero leading value tail tailAtom tail_has_junk
  let emission := ordinaryBitEmission system input instruction value
  let nextTokens := tail ++ emittedLeading.map .junk ++ emission
  have next_ends : EndsInJunk nextTokens := by
    exact EndsInJunk.prepend _ <|
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

end MatrixMortality.Undecidability.NearyCompiler
