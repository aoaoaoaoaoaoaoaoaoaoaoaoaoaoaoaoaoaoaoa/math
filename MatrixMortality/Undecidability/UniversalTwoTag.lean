import MatrixMortality.Undecidability.CockeMinskyAvoidance
import MatrixMortality.Undecidability.TM0ToRead
import MatrixMortality.Undecidability.Problems
import MatrixMortality.Undecidability.UniversalTM0

/-!
# A fixed universal two-tag system

The fixed universal binary `TM0` machine is normalized to a read-state machine and then compiled
by the Cocke–Minsky construction.  A final finite relabelling places the unique halt symbol last
in a canonical `Fin` alphabet.  Exact reachability of that symbol is therefore equivalent to
halting of the source code.
-/

open Turing

namespace MatrixMortality
namespace Undecidability
namespace UniversalTwoTag

open scoped Classical

/-- A fixed mathlib interpreter for every encoded source program. -/
noncomputable def interpreter : ToPartrec.Code :=
  exists_universalTM2.choose

/-- Specification of the fixed universal interpreter. -/
theorem interpreter_spec (source : Nat.Partrec.Code) (input : Nat) :
    UniversalTM2Halts
        (PartrecToTM2.init interpreter [Encodable.encode source, input]) ↔
      (Nat.Partrec.Code.eval source input).Dom :=
  exists_universalTM2.choose_spec source input

/-- Finite labels of the fixed universal binary `TM0` machine. -/
abbrev BinaryState :=
  FiniteTM0.State (UniversalTM0.postSupport interpreter)

/-- The fixed finite-state universal binary `TM0` machine. -/
noncomputable def binaryMachine : TM0.Machine Bool BinaryState :=
  FiniteTM0.machine (UniversalTM0.postMachine interpreter)
    (UniversalTM0.postSupport interpreter)

/-- Control states after write-then-move normalization. -/
abbrev ReadState := TM0ToRead.State BinaryState

/-- The fixed universal read-state machine. -/
noncomputable def readMachine : CockeMinsky.Machine ReadState :=
  TM0ToRead.machine binaryMachine

/-- Initial read-state configuration for a source code at input zero. -/
noncomputable def initialConfig (source : Nat.Partrec.Code) :
    CockeMinsky.Config ReadState :=
  TM0ToRead.config
    (TM0.init
      (UniversalTM0.binaryInput [Encodable.encode source, 0]) :
      TM0.Cfg Bool BinaryState)

private noncomputable def sourceInput (source : Nat.Partrec.Code) : List Bool :=
  UniversalTM0.binaryInput [Encodable.encode source, 0]

private noncomputable def sourceState (source : Nat.Partrec.Code) : ReadState :=
  .normal default (sourceInput source).headI

private noncomputable def sourceRight (source : Nat.Partrec.Code) : Nat :=
  TM0ToRead.bitsNatList (sourceInput source).tail

private noncomputable def sourceCounters (source : Nat.Partrec.Code) : Nat × Nat :=
  match CockeMinsky.direction readMachine (sourceState source) with
  | .right => (0, sourceRight source)
  | .left => (sourceRight source, 0)

private theorem initialConfig_eq (source : Nat.Partrec.Code) :
    initialConfig source =
      { state := sourceState source
        left := 0
        right := sourceRight source } := by
  simp [initialConfig, sourceInput, sourceState, sourceRight, TM0.init, TM0ToRead.config,
    Tape.mk₁, Tape.mk₂, Tape.mk', TM0ToRead.bitsNatList]

/-- The fixed read-state machine halts exactly on source codes halting at input zero. -/
theorem readMachine_halts_iff (source : Nat.Partrec.Code) :
    CockeMinsky.Halts readMachine (initialConfig source) ↔ CodeHalts source := by
  change
    CockeMinsky.Halts
        (TM0ToRead.machine
          (FiniteTM0.machine (UniversalTM0.postMachine interpreter)
            (UniversalTM0.postSupport interpreter)))
        (TM0ToRead.config
          (TM0.init
            (UniversalTM0.binaryInput [Encodable.encode source, 0]) :
            TM0.Cfg Bool BinaryState)) ↔
      (source.eval 0).Dom
  rw [TM0ToRead.halts_iff_eval_dom]
  rw [UniversalTM0.eval_dom_iff_tm2]
  exact interpreter_spec source 0

/-- Cardinality of the Cocke–Minsky tag alphabet. -/
noncomputable def alphabet : Nat :=
  Fintype.card (CockeMinsky.Symbol ReadState)

theorem alphabet_one_lt : 1 < alphabet := by
  rw [alphabet, Fintype.one_lt_card_iff]
  exact ⟨.halt, .pad (.normal (.inl ()) false), by simp⟩

/-- Last alphabet label, reserved for the unique Cocke–Minsky halt symbol. -/
noncomputable def haltLabel : Fin alphabet :=
  ⟨alphabet - 1, by have := alphabet_one_lt; omega⟩

/-- First alphabet label, reserved for a production that is always nonempty. -/
noncomputable def zeroLabel : Fin alphabet :=
  ⟨0, by have := alphabet_one_lt; omega⟩

theorem haltLabel_nonzero : haltLabel.val ≠ 0 := by
  simp only [haltLabel, Fin.val_mk]
  have := alphabet_one_lt
  omega

theorem haltLabel_last : haltLabel.val + 1 = alphabet := by
  simp only [haltLabel, Fin.val_mk]
  have := alphabet_one_lt
  omega

/-- A concrete read-state used only to select an always-live tag production. -/
def liveState : ReadState :=
  .normal (.inl ()) false

/-- This symbol has an unconditional two-symbol production. -/
def liveSymbol : CockeMinsky.Symbol ReadState :=
  .doubledAnchor liveState

/-- A finite relabelling that sends the halt symbol to the last alphabet position. -/
noncomputable def symbolEquiv : CockeMinsky.Symbol ReadState ≃ Fin alphabet :=
  let raw := Fintype.equivFin (CockeMinsky.Symbol ReadState)
  let exposeLive := Equiv.swap (raw liveSymbol) zeroLabel
  raw.trans <| exposeLive.trans <| Equiv.swap (exposeLive (raw .halt)) haltLabel

@[simp]
theorem symbolEquiv_halt :
    symbolEquiv (.halt : CockeMinsky.Symbol ReadState) = haltLabel := by
  simp only [symbolEquiv, Equiv.trans_apply]
  exact Equiv.swap_apply_left _ _

@[simp]
theorem symbolEquiv_symm_haltLabel :
    symbolEquiv.symm haltLabel = (.halt : CockeMinsky.Symbol ReadState) :=
  symbolEquiv.symm_apply_eq.mpr symbolEquiv_halt.symm

@[simp]
theorem symbolEquiv_live : symbolEquiv liveSymbol = zeroLabel := by
  simp only [symbolEquiv, Equiv.trans_apply]
  rw [Equiv.swap_apply_left]
  apply Equiv.swap_apply_of_ne_of_ne
  · intro equality
    have exposed_eq :
        (Equiv.swap
            ((Fintype.equivFin (CockeMinsky.Symbol ReadState)) liveSymbol)
            zeroLabel)
            ((Fintype.equivFin (CockeMinsky.Symbol ReadState)) liveSymbol) =
          (Equiv.swap
            ((Fintype.equivFin (CockeMinsky.Symbol ReadState)) liveSymbol)
            zeroLabel)
            ((Fintype.equivFin (CockeMinsky.Symbol ReadState))
              (CockeMinsky.Symbol.halt)) := by
      rw [Equiv.swap_apply_left]
      exact equality
    have halt_eq_live := (Equiv.swap _ _).injective exposed_eq
    have := (Fintype.equivFin (CockeMinsky.Symbol ReadState)).injective halt_eq_live
    simp [liveSymbol] at this
  · intro equality
    apply haltLabel_nonzero
    rw [← equality]
    rfl

/-- Relabel a Cocke–Minsky queue by `symbolEquiv`. -/
noncomputable def encodeWord (word : List (CockeMinsky.Symbol ReadState)) :
    List (Fin alphabet) :=
  word.map symbolEquiv

/-- Relabel a finite-alphabet queue back to Cocke–Minsky symbols. -/
noncomputable def decodeWord (word : List (Fin alphabet)) :
    List (CockeMinsky.Symbol ReadState) :=
  word.map symbolEquiv.symm

/-- Canonical two-tag queue encoding one source program. -/
noncomputable def initialWord (source : Nat.Partrec.Code) :
    List (Fin alphabet) :=
  encodeWord (CockeMinsky.encode readMachine (initialConfig source))

/-- A compiled source program always begins with the two-symbol anchor cell. -/
theorem initialWord_nonempty (source : Nat.Partrec.Code) :
    initialWord source ≠ [] := by
  simp [initialWord, encodeWord, CockeMinsky.encode, CockeMinsky.cell]

private theorem initialWord_eq_frame (source : Nat.Partrec.Code) :
    initialWord source =
      encodeWord
        (CockeMinsky.frame (sourceState source) (sourceCounters source).1
          (sourceCounters source).2) := by
  rw [initialWord, CockeMinsky.encode_eq_frame, initialConfig_eq]
  simp [CockeMinsky.orientedCounters, sourceCounters]
  rfl

/-- The fixed two-tag input compiler is primitive recursive in the source code. -/
theorem initialWord_primrec : Primrec initialWord := by
  letI : Primcodable ReadState := finitePrimcodable ReadState
  letI : Primcodable (CockeMinsky.Symbol ReadState) :=
    finitePrimcodable (CockeMinsky.Symbol ReadState)
  have encodedSource :
      Primrec fun source : Nat.Partrec.Code => [Encodable.encode source, 0] :=
    Primrec.list_cons.comp Primrec.encode (Primrec.const [0])
  have inputRec : Primrec sourceInput :=
    UniversalTM0.binaryInput_primrec.comp encodedSource
  have stateOfBit :
      Primrec fun bit : Bool => (TM0ToRead.State.normal default bit : ReadState) :=
    Primrec.dom_fintype _
  have stateRec : Primrec sourceState :=
    stateOfBit.comp (Primrec.list_headI.comp inputRec)
  have rightRec : Primrec sourceRight :=
    TM0ToRead.bitsNatList_primrec.comp (Primrec.list_tail.comp inputRec)
  have movesRight :
      Primrec fun state : ReadState =>
        match CockeMinsky.direction readMachine state with
        | .right => true
        | .left => false :=
    Primrec.dom_fintype _
  have movesRightSource :
      Primrec fun source =>
        match CockeMinsky.direction readMachine (sourceState source) with
        | .right => true
        | .left => false :=
    movesRight.comp stateRec
  have countersRec : Primrec sourceCounters :=
    (Primrec.cond movesRightSource
      (Primrec.pair (Primrec.const 0) rightRec)
      (Primrec.pair rightRec (Primrec.const 0))).of_eq fun source => by
        simp only [sourceCounters]
        split <;> rfl
  have anchorCell :
      Primrec fun state : ReadState =>
        CockeMinsky.cell (CockeMinsky.Symbol.anchor state) (CockeMinsky.Symbol.pad state) :=
    Primrec.dom_fintype _
  have digitCell :
      Primrec fun state : ReadState =>
        CockeMinsky.cell (CockeMinsky.Symbol.digit state) (CockeMinsky.Symbol.pad state) :=
    Primrec.dom_fintype _
  have boundaryCell :
      Primrec fun state : ReadState =>
        CockeMinsky.cell (CockeMinsky.Symbol.boundary state) (CockeMinsky.Symbol.pad state) :=
    Primrec.dom_fintype _
  have boundaryDigitCell :
      Primrec fun state : ReadState =>
        CockeMinsky.cell
          (CockeMinsky.Symbol.boundaryDigit state) (CockeMinsky.Symbol.pad state) :=
    Primrec.dom_fintype _
  have digitCells :
      Primrec fun source =>
        (List.replicate (sourceCounters source).1
          (CockeMinsky.cell
            (CockeMinsky.Symbol.digit (sourceState source))
            (CockeMinsky.Symbol.pad (sourceState source)))).join :=
    Primrec.list_join.comp <|
      (MatrixMortality.Primrec.list_replicate).comp
        (Primrec.fst.comp countersRec) (digitCell.comp stateRec)
  have boundaryDigitCells :
      Primrec fun source =>
        (List.replicate (sourceCounters source).2
          (CockeMinsky.cell
            (CockeMinsky.Symbol.boundaryDigit (sourceState source))
            (CockeMinsky.Symbol.pad (sourceState source)))).join :=
    Primrec.list_join.comp <|
      (MatrixMortality.Primrec.list_replicate).comp
        (Primrec.snd.comp countersRec) (boundaryDigitCell.comp stateRec)
  have frameRec :
      Primrec fun source =>
        CockeMinsky.frame (sourceState source) (sourceCounters source).1
          (sourceCounters source).2 :=
    (Primrec.list_append.comp (anchorCell.comp stateRec)
      (Primrec.list_append.comp digitCells
        (Primrec.list_append.comp (boundaryCell.comp stateRec)
          boundaryDigitCells))).of_eq fun source => by
            simp only [CockeMinsky.frame, CockeMinsky.cells, List.append_assoc]
  have symbolRec :
      Primrec fun symbol : CockeMinsky.Symbol ReadState => symbolEquiv symbol :=
    Primrec.dom_fintype _
  exact
    (Primrec.list_map frameRec (symbolRec.comp₂ Primrec₂.right)).of_eq fun source =>
      (initialWord_eq_frame source).symm

@[simp]
theorem decodeWord_encodeWord (word : List (CockeMinsky.Symbol ReadState)) :
    decodeWord (encodeWord word) = word := by
  simp [decodeWord, encodeWord]

@[simp]
theorem encodeWord_decodeWord (word : List (Fin alphabet)) :
    encodeWord (decodeWord word) = word := by
  simp [decodeWord, encodeWord]

/-- The fixed universal two-tag system on its canonical finite alphabet. -/
noncomputable def system : TwoTag alphabet where
  production label :=
    (CockeMinsky.production readMachine (symbolEquiv.symm label)).map symbolEquiv

@[simp]
theorem system_production_encode (symbol : CockeMinsky.Symbol ReadState) :
    system.production (symbolEquiv symbol) =
      encodeWord (CockeMinsky.production readMachine symbol) := by
  simp [system, encodeWord]

theorem system_production_zero_nonempty :
    system.production zeroLabel ≠ [] := by
  rw [← symbolEquiv_live, system_production_encode]
  simp [CockeMinsky.production, liveSymbol, encodeWord]

theorem tagStep_two_iff {α : Type*} (output : α → List α) (before after : List α) :
    TagStep 2 output before after ↔
      ∃ head wake tail,
        before = head :: wake :: tail ∧ after = tail ++ output head := by
  constructor
  · rintro ⟨⟨head, wake, width⟩, tail, before_eq, after_eq⟩
    have wake_length : wake.length = 1 := by omega
    obtain ⟨wakeHead, rfl⟩ := List.length_eq_one.mp wake_length
    exact ⟨head, wakeHead, tail, before_eq, after_eq⟩
  · rintro ⟨head, wake, tail, rfl, rfl⟩
    exact ⟨⟨head, [wake], rfl⟩, tail, rfl, rfl⟩

theorem step_encode_iff (before after : List (CockeMinsky.Symbol ReadState)) :
    system.Step (encodeWord before) (encodeWord after) ↔
      CockeMinsky.Step readMachine before after := by
  rw [TwoTag.Step, CockeMinsky.Step, tagStep_two_iff, tagStep_two_iff]
  constructor
  · rintro ⟨head, wake, tail, before_eq, after_eq⟩
    refine ⟨symbolEquiv.symm head, symbolEquiv.symm wake, decodeWord tail, ?_, ?_⟩
    · apply_fun decodeWord at before_eq
      simpa [decodeWord, encodeWord] using before_eq
    · apply_fun decodeWord at after_eq
      simpa [decodeWord, encodeWord, system] using after_eq
  · rintro ⟨head, wake, tail, rfl, rfl⟩
    refine ⟨symbolEquiv head, symbolEquiv wake, encodeWord tail, ?_, ?_⟩
    · simp [encodeWord]
    · simp [encodeWord, system, List.map_append]

theorem decode_reaches {before after : List (Fin alphabet)}
    (reach : system.Reaches before after) :
    CockeMinsky.TagReaches readMachine (decodeWord before) (decodeWord after) := by
  induction reach with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih =>
      apply Relation.ReflTransGen.tail ih
      apply (step_encode_iff (decodeWord _) (decodeWord _)).mp
      simpa using step

/-- Finite relabelling reflects every terminating two-tag execution. -/
theorem decode_tagHaltsFrom {before : List (Fin alphabet)}
    (halts : TagHaltsFrom 2 system.production before) :
    TagHaltsFrom 2 (CockeMinsky.production readMachine) (decodeWord before) := by
  induction halts with
  | @stop queue short =>
      exact .stop <| by simpa [decodeWord] using short
  | @step queue after step _ ih =>
      apply TagHaltsFrom.step
      · apply (step_encode_iff (decodeWord queue) (decodeWord after)).mp
        simpa using step
      · exact ih

theorem encode_reaches {before after : List (CockeMinsky.Symbol ReadState)}
    (reach : CockeMinsky.TagReaches readMachine before after) :
    system.Reaches (encodeWord before) (encodeWord after) := by
  induction reach with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih =>
      exact Relation.ReflTransGen.tail ih ((step_encode_iff _ _).mpr step)

/-- Finite relabelling preserves a tag step whose read head is not the halt symbol. -/
theorem avoidingStep_encode_iff
    (before after : List (CockeMinsky.Symbol ReadState)) :
    HeadAvoidingTagStep 2 system.production haltLabel
        (encodeWord before) (encodeWord after) ↔
      HeadAvoidingTagStep 2 (CockeMinsky.production readMachine)
        (.halt : CockeMinsky.Symbol ReadState) before after := by
  rw [TwoTag.avoidingStep_iff]
  rw [headAvoidingTagStep_two_iff]
  constructor
  · rintro ⟨head, wake, tail, head_ne, before_eq, after_eq⟩
    refine ⟨symbolEquiv.symm head, symbolEquiv.symm wake, decodeWord tail, ?_, ?_, ?_⟩
    · intro equality
      apply head_ne
      simpa using congrArg symbolEquiv equality
    · apply_fun decodeWord at before_eq
      simpa [decodeWord, encodeWord] using before_eq
    · apply_fun decodeWord at after_eq
      simpa [decodeWord, encodeWord, system] using after_eq
  · rintro ⟨head, wake, tail, head_ne, rfl, rfl⟩
    refine ⟨symbolEquiv head, symbolEquiv wake, encodeWord tail, ?_, ?_, ?_⟩
    · intro equality
      apply head_ne
      apply symbolEquiv.injective
      simpa using equality
    · simp [encodeWord]
    · simp [encodeWord, system, List.map_append]

theorem encode_avoiding_reaches {before after : List (CockeMinsky.Symbol ReadState)}
    (reach : CockeMinsky.HaltAvoidingReaches readMachine before after) :
    system.AvoidingReaches haltLabel (encodeWord before) (encodeWord after) := by
  induction reach with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih =>
      exact Relation.ReflTransGen.tail ih ((avoidingStep_encode_iff _ _).mpr step)

/-- Finite relabelling preserves and reflects every tag execution. -/
theorem reaches_encode_iff (before after : List (CockeMinsky.Symbol ReadState)) :
    system.Reaches (encodeWord before) (encodeWord after) ↔
      CockeMinsky.TagReaches readMachine before after := by
  constructor
  · intro reach
    simpa using decode_reaches reach
  · exact encode_reaches

/-- Exact reachability of the last alphabet label recognizes code halting. -/
theorem reaches_halt_iff (source : Nat.Partrec.Code) :
    system.Reaches
        (encodeWord (CockeMinsky.encode readMachine (initialConfig source)))
        [haltLabel] ↔
      CodeHalts source := by
  rw [show [haltLabel] =
      encodeWord ([.halt] : List (CockeMinsky.Symbol ReadState)) by
    simp [encodeWord]]
  rw [reaches_encode_iff]
  rw [CockeMinsky.tag_reaches_halt_iff]
  exact readMachine_halts_iff source

/-- Source-code halting reaches the singleton halt label without reading that label earlier. -/
theorem halts_implies_halt_avoiding (source : Nat.Partrec.Code) (halts : CodeHalts source) :
    system.AvoidingReaches haltLabel
      (encodeWord (CockeMinsky.encode readMachine (initialConfig source))) [haltLabel] := by
  rw [show [haltLabel] =
      encodeWord ([.halt] : List (CockeMinsky.Symbol ReadState)) by
    simp [encodeWord]]
  apply encode_avoiding_reaches
  rw [← readMachine_halts_iff] at halts
  exact CockeMinsky.halts_implies_halt_avoiding readMachine (initialConfig source) halts

/-- Any terminating execution from the universal two-tag encoding reflects source-code
halting. -/
theorem tagHaltsFrom_implies_halts (source : Nat.Partrec.Code)
    (halts :
      TagHaltsFrom 2 system.production
        (encodeWord (CockeMinsky.encode readMachine (initialConfig source)))) :
    CodeHalts source := by
  have decoded := decode_tagHaltsFrom halts
  rw [decodeWord_encodeWord] at decoded
  obtain ⟨steps, indexed⟩ := tagHaltsFrom_iff_exists_tagHaltsIn.mp decoded
  apply (readMachine_halts_iff source).mp
  exact
    CockeMinsky.tagHaltsIn_encode_implies_halts readMachine steps (initialConfig source) indexed

/-- Reaching any queue headed by the universal halt label reflects source-code halting. -/
theorem reachesHead_halt_implies_halts (source : Nat.Partrec.Code)
    (reach :
      system.ReachesHead
        (encodeWord (CockeMinsky.encode readMachine (initialConfig source))) haltLabel) :
    CodeHalts source := by
  obtain ⟨tail, execution⟩ := reach
  have decoded := decode_reaches execution
  rw [decodeWord_encodeWord] at decoded
  apply (readMachine_halts_iff source).mp
  apply CockeMinsky.tag_reaches_head_halt_implies_halts readMachine (initialConfig source)
    (decodeWord tail)
  simpa [decodeWord] using decoded

end UniversalTwoTag
end Undecidability
end MatrixMortality
