import Mathlib.Computability.TuringMachine.StackTuringMachine

/-!
# Finite restriction of supported TM0 machines

Mathlib permits infinite program-state types and records effective finiteness by a support
finset.  The downstream tag compiler needs an actual `Fintype`.  This file replaces a supported
machine by a finite state type with one canonical root state and one state for each supported
label.  The duplicate representation of the default label is harmless and keeps the construction
inhabited without choosing an element of a subtype.
-/

open Turing

namespace MatrixMortality
namespace Undecidability
namespace FiniteTM0

/-- A canonical initial state plus the labels in a finite support. -/
abbrev State {label : Type*} (support : Finset label) :=
  Unit ⊕ { q // q ∈ support }

instance {label : Type*} {support : Finset label} : Inhabited (State support) :=
  Sum.inhabitedLeft

/-- Erase the finite wrapper back to the source label type. -/
def State.value {label : Type*} [Inhabited label]
    {support : Finset label} : State support → label
  | .inl _ => default
  | .inr q => q

/-- Every wrapped state denotes a member of the support. -/
theorem State.value_mem {label : Type*} [Inhabited label]
    {source : TM0.Machine Bool label} {support : Finset label}
    (supported : TM0.Supports source ↑support) (q : State support) :
    q.value ∈ support := by
  cases q with
  | inl _ => exact supported.1
  | inr q => exact q.property

/-- Restrict a supported binary machine to an actual finite state type. -/
def machine {label : Type*} [Inhabited label] [DecidableEq label]
    (source : TM0.Machine Bool label) (support : Finset label) :
    TM0.Machine Bool (State support)
  | q, bit =>
      (source q.value bit).bind fun command =>
        if command_supported : command.1 ∈ support then
          some (.inr ⟨command.1, command_supported⟩, command.2)
        else
          none

theorem machine_eq_none {label : Type*} [Inhabited label] [DecidableEq label]
    (source : TM0.Machine Bool label) (support : Finset label)
    (q : State support) (bit : Bool)
    (transition : source q.value bit = none) :
    machine source support q bit = none := by
  simp [machine, transition]

theorem machine_eq_some {label : Type*} [Inhabited label] [DecidableEq label]
    (source : TM0.Machine Bool label) (support : Finset label)
    (supported : TM0.Supports source ↑support) (q : State support) (bit : Bool)
    (q' : label) (statement : TM0.Stmt Bool)
    (transition : source q.value bit = some (q', statement)) :
    machine source support q bit =
      some
        (.inr ⟨q', supported.2 (by simpa [transition]) (q.value_mem supported)⟩,
          statement) := by
  have q'_supported : q' ∈ support :=
    supported.2 (by simpa [transition]) (q.value_mem supported)
  simp [machine, transition, q'_supported]

/-- Erase a finite-state configuration back to the source machine. -/
def config {label : Type*} [Inhabited label]
    {support : Finset label} (source : TM0.Cfg Bool (State support)) :
    TM0.Cfg Bool label where
  q := source.q.value
  Tape := source.Tape

/-- The finite restriction and source machine have identical transition behavior. -/
theorem respects {label : Type*} [Inhabited label] [DecidableEq label]
    (source : TM0.Machine Bool label) (support : Finset label)
    (supported : TM0.Supports source ↑support) :
    StateTransition.Respects (TM0.step (machine source support)) (TM0.step source)
      fun finiteConfig sourceConfig => config finiteConfig = sourceConfig := by
  rw [StateTransition.fun_respects]
  rintro ⟨q, tape⟩
  cases transition : source q.value tape.head with
  | none =>
      have restricted_none := machine_eq_none source support q tape.head transition
      simp [StateTransition.FRespects, TM0.step, restricted_none, config, transition]
  | some command =>
      obtain ⟨q', statement⟩ := command
      have restricted_some :=
        machine_eq_some source support supported q tape.head q' statement transition
      cases statement with
      | move direction =>
        simp only [TM0.step, restricted_some, Option.map_some, StateTransition.FRespects]
        apply Relation.TransGen.single
        simp [TM0.step, transition, config]
        rfl
      | write symbol =>
        simp only [TM0.step, restricted_some, Option.map_some, StateTransition.FRespects]
        apply Relation.TransGen.single
        simp [TM0.step, transition, config]
        rfl

/-- The wrapped initial configuration erases to the original initial configuration. -/
theorem config_init {label : Type*} [Inhabited label]
    (support : Finset label) (input : List Bool) :
    config (TM0.init input : TM0.Cfg Bool (State support)) =
      (TM0.init input : TM0.Cfg Bool label) := rfl

/-- Finite restriction preserves and reflects halting from every input. -/
theorem eval_dom_iff {label : Type*} [Inhabited label] [DecidableEq label]
    (source : TM0.Machine Bool label) (support : Finset label)
    (supported : TM0.Supports source ↑support) (input : List Bool) :
    (StateTransition.eval (TM0.step (machine source support))
        (TM0.init input : TM0.Cfg Bool (State support))).Dom ↔
      (StateTransition.eval (TM0.step source) (TM0.init input)).Dom := by
  exact StateTransition.tr_eval_dom (respects source support supported) (config_init support input)
    |>.symm

end FiniteTM0
end Undecidability
end MatrixMortality
