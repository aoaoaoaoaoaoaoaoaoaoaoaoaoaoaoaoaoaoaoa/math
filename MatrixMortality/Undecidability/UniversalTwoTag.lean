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

theorem encode_reaches {before after : List (CockeMinsky.Symbol ReadState)}
    (reach : CockeMinsky.TagReaches readMachine before after) :
    system.Reaches (encodeWord before) (encodeWord after) := by
  induction reach with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih =>
      exact Relation.ReflTransGen.tail ih ((step_encode_iff _ _).mpr step)

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

end UniversalTwoTag
end Undecidability
end MatrixMortality
