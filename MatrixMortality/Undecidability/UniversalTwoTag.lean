import MatrixMortality.Undecidability.CockeMinskyAvoidance
import MatrixMortality.Undecidability.TM0ToRead
import MatrixMortality.Undecidability.Problems
import MatrixMortality.Undecidability.TwoTagSource
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

namespace Construction

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
  let raw : CockeMinsky.Symbol ReadState ≃ Fin alphabet :=
    Fintype.equivFin (CockeMinsky.Symbol ReadState)
  let exposeLive := Equiv.swap (raw liveSymbol) zeroLabel
  change
    (Equiv.swap (exposeLive (raw (.halt : CockeMinsky.Symbol ReadState))) haltLabel)
        (exposeLive (raw liveSymbol)) = zeroLabel
  rw [show exposeLive (raw liveSymbol) = zeroLabel by
    exact Equiv.swap_apply_left _ _]
  apply Equiv.swap_apply_of_ne_of_ne
  · intro equality
    have exposed_eq :
        exposeLive (raw liveSymbol) =
          exposeLive (raw (.halt : CockeMinsky.Symbol ReadState)) := by
      rw [show exposeLive (raw liveSymbol) = zeroLabel by
        exact Equiv.swap_apply_left _ _]
      exact equality
    have halt_eq_live := exposeLive.injective exposed_eq
    have := raw.injective halt_eq_live
    simp [liveSymbol] at this
  · intro equality
    apply haltLabel_nonzero
    simpa [zeroLabel] using congrArg Fin.val equality.symm

/-- Relabel a Cocke–Minsky queue by `symbolEquiv`. -/
noncomputable def encodeWord (word : List (CockeMinsky.Symbol ReadState)) :
    List (Fin alphabet) :=
  word.map symbolEquiv

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
  let _ : Primcodable ReadState := finitePrimcodable ReadState
  let _ : Primcodable (CockeMinsky.Symbol ReadState) :=
    finitePrimcodable (CockeMinsky.Symbol ReadState)
  have encodedSource :
      Primrec fun source : Nat.Partrec.Code => [Encodable.encode source, 0] :=
    Primrec.list_cons.comp Primrec.encode (Primrec.const [0])
  have inputRec : Primrec sourceInput :=
    UniversalTM0.binaryInput_primrec.comp encodedSource
  have stateOfBit :
      Primrec fun bit : Bool => (TM0ToRead.State.normal default bit : ReadState) :=
    Primrec.dom_finite _
  have stateRec : Primrec sourceState :=
    stateOfBit.comp (Primrec.list_headI.comp inputRec)
  have rightRec : Primrec sourceRight :=
    TM0ToRead.bitsNatList_primrec.comp (Primrec.list_tail.comp inputRec)
  have movesRight :
      Primrec fun state : ReadState =>
        match CockeMinsky.direction readMachine state with
        | .right => true
        | .left => false :=
    Primrec.dom_finite _
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
    Primrec.dom_finite _
  have digitCell :
      Primrec fun state : ReadState =>
        CockeMinsky.cell (CockeMinsky.Symbol.digit state) (CockeMinsky.Symbol.pad state) :=
    Primrec.dom_finite _
  have boundaryCell :
      Primrec fun state : ReadState =>
        CockeMinsky.cell (CockeMinsky.Symbol.boundary state) (CockeMinsky.Symbol.pad state) :=
    Primrec.dom_finite _
  have boundaryDigitCell :
      Primrec fun state : ReadState =>
        CockeMinsky.cell
          (CockeMinsky.Symbol.boundaryDigit state) (CockeMinsky.Symbol.pad state) :=
    Primrec.dom_finite _
  have digitCells :
      Primrec fun source =>
        (List.replicate (sourceCounters source).1
          (CockeMinsky.cell
            (CockeMinsky.Symbol.digit (sourceState source))
            (CockeMinsky.Symbol.pad (sourceState source)))).flatten :=
    Primrec.list_flatten.comp <|
      (MatrixMortality.Primrec.list_replicate).comp
        (Primrec.fst.comp countersRec) (digitCell.comp stateRec)
  have boundaryDigitCells :
      Primrec fun source =>
        (List.replicate (sourceCounters source).2
          (CockeMinsky.cell
            (CockeMinsky.Symbol.boundaryDigit (sourceState source))
            (CockeMinsky.Symbol.pad (sourceState source)))).flatten :=
    Primrec.list_flatten.comp <|
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
    Primrec.dom_finite _
  exact
    (Primrec.list_map frameRec (symbolRec.comp₂ Primrec₂.right)).of_eq fun source =>
      (initialWord_eq_frame source).symm

/-- The fixed universal two-tag system on its canonical finite alphabet. -/
noncomputable def system : TwoTag alphabet where
  production := relabelTagOutput symbolEquiv (CockeMinsky.production readMachine)

@[simp]
theorem system_production_encode (symbol : CockeMinsky.Symbol ReadState) :
    system.production (symbolEquiv symbol) =
      encodeWord (CockeMinsky.production readMachine symbol) := by
  simp [system, encodeWord]

theorem system_production_zero_nonempty :
    system.production zeroLabel ≠ [] := by
  rw [← symbolEquiv_live, system_production_encode]
  simp [CockeMinsky.production, liveSymbol, encodeWord]

/-- Source-code halting reaches the singleton halt label without reading that label earlier. -/
theorem halts_implies_halt_avoiding (source : Nat.Partrec.Code) (halts : CodeHalts source) :
    system.HeadAvoidingReaches haltLabel
      (encodeWord (CockeMinsky.encode readMachine (initialConfig source))) [haltLabel] := by
  rw [show [haltLabel] =
      encodeWord ([.halt] : List (CockeMinsky.Symbol ReadState)) by
    simp [encodeWord]]
  rw [← readMachine_halts_iff] at halts
  have sourceReach :=
    CockeMinsky.halts_implies_halt_avoiding readMachine (initialConfig source) halts
  simpa [TwoTag.HeadAvoidingReaches, system, encodeWord,
    CockeMinsky.HaltHeadAvoidingReaches] using
    sourceReach.relabel symbolEquiv

/-- Any terminating execution from the universal two-tag encoding reflects source-code
halting. -/
theorem tagHaltsFrom_implies_halts (source : Nat.Partrec.Code)
    (halts :
      TagHaltsFrom 2 system.production
        (encodeWord (CockeMinsky.encode readMachine (initialConfig source)))) :
    CodeHalts source := by
  have decoded :
      TagHaltsFrom 2 (CockeMinsky.production readMachine)
        (CockeMinsky.encode readMachine (initialConfig source)) :=
    (tagHaltsFrom_relabel_iff symbolEquiv (CockeMinsky.production readMachine)
      (CockeMinsky.encode readMachine (initialConfig source))).mp <| by
        simpa [system, encodeWord] using halts
  obtain ⟨steps, indexed⟩ := tagHaltsFrom_iff_exists_tagHaltsIn.mp decoded
  apply (readMachine_halts_iff source).mp
  exact
    CockeMinsky.tagHaltsIn_encode_implies_halts readMachine steps (initialConfig source) indexed

/-- Reaching any queue headed by the universal halt label reflects source-code halting. -/
theorem reachesHead_halt_implies_halts (source : Nat.Partrec.Code)
    (reach :
      system.CanReachHead
        (encodeWord (CockeMinsky.encode readMachine (initialConfig source))) haltLabel) :
    CodeHalts source := by
  obtain ⟨tail, execution⟩ := reach
  have raw :
      TagReaches 2 (relabelTagOutput symbolEquiv (CockeMinsky.production readMachine))
        (encodeWord (CockeMinsky.encode readMachine (initialConfig source)))
        (haltLabel :: tail) := by
    simpa [TwoTag.QueueReaches, TwoTag.Step, system] using execution
  have decoded := raw.relabel symbolEquiv.symm
  apply (readMachine_halts_iff source).mp
  apply CockeMinsky.tag_reaches_head_halt_implies_halts readMachine (initialConfig source)
    (tail.map symbolEquiv.symm)
  simpa [relabelTagOutput, encodeWord] using decoded

end Construction

/-- Fixed finite two-tag source recognizing mathlib code halting. -/
noncomputable def source : TwoTagSource Nat.Partrec.Code CodeHalts where
  alphabet := Construction.alphabet
  alphabet_one_lt := Construction.alphabet_one_lt
  system := Construction.system
  haltLabel := Construction.haltLabel
  liveLabel := Construction.zeroLabel
  liveLabel_zero := rfl
  haltLabel_last := Construction.haltLabel_last
  liveProduction_nonempty := Construction.system_production_zero_nonempty
  input := Construction.initialWord
  input_primrec := Construction.initialWord_primrec
  input_nonempty := Construction.initialWord_nonempty
  accepts_implies_avoidingHalt := Construction.halts_implies_halt_avoiding
  accepts_of_tagTermination := Construction.tagHaltsFrom_implies_halts
  accepts_of_haltHead := Construction.reachesHead_halt_implies_halts

/-- Exact reachability of the last alphabet label recognizes code halting. -/
theorem reaches_halt_iff (index : Nat.Partrec.Code) :
    source.system.QueueReaches (source.input index) [source.haltLabel] ↔
      CodeHalts index :=
  source.reachesHalt_iff index

end UniversalTwoTag
end Undecidability
end MatrixMortality
