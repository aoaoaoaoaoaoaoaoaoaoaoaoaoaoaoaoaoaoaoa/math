import Mathlib.Computability.TuringMachine

/-!
# Rooting a TM2 machine at an arbitrary label

Mathlib's `TM2.init` starts at the default label.  A fixed universal program instead needs an
instance-selected root without replacing the ambient `Inhabited` instance.  This construction
adds one canonical root state and otherwise embeds the source labels.  The root executes the
source root statement directly, so the refinement is step-for-step rather than stuttering.
-/

open Turing

namespace MatrixMortality
namespace Undecidability
namespace SeededTM2

/-- One canonical root plus an embedded source label. -/
inductive Label (source : Type*)
  | root
  | source : source → Label source
  deriving DecidableEq

instance {source : Type*} : Inhabited (Label source) := ⟨.root⟩

/-- Erase the added root to its selected source label. -/
def Label.value {source : Type*} (root : source) : Label source → source
  | .root => root
  | .source q => q

/-- Relabel every jump in a `TM2` statement. -/
def liftStmt {stack : Type*} {symbol : stack → Type*} {source target store : Type*}
    (embed : source → target) :
    TM2.Stmt symbol source store → TM2.Stmt symbol target store
  | .push k write continuation => .push k write (liftStmt embed continuation)
  | .peek k read continuation => .peek k read (liftStmt embed continuation)
  | .pop k read continuation => .pop k read (liftStmt embed continuation)
  | .load update continuation => .load update (liftStmt embed continuation)
  | .branch test yes no => .branch test (liftStmt embed yes) (liftStmt embed no)
  | .goto next => .goto fun store => embed (next store)
  | .halt => .halt

/-- Execute a source machine from the selected root. -/
def machine {stack : Type*} {symbol : stack → Type*} {source store : Type*}
    (sourceMachine : source → TM2.Stmt symbol source store) (root : source) :
    Label source → TM2.Stmt symbol (Label source) store :=
  fun q => liftStmt .source (sourceMachine (q.value root))

/-- Erase a rooted configuration to the source configuration. -/
def config {stack : Type*} {symbol : stack → Type*} {source store : Type*}
    (root : source) :
    TM2.Cfg symbol (Label source) store → TM2.Cfg symbol source store
  | ⟨label, storeValue, stacks⟩ => ⟨label.map (Label.value root), storeValue, stacks⟩

theorem config_stepAux_liftStmt {stack : Type*} [DecidableEq stack]
    {symbol : stack → Type*} {source store : Type*}
    (embed : source → Label source) (root : source)
    (embed_value : ∀ q, Label.value root (embed q) = q)
    (statement : TM2.Stmt symbol source store) (storeValue : store)
    (stacks : ∀ k, List (symbol k)) :
    config root (TM2.stepAux (liftStmt embed statement) storeValue stacks) =
      TM2.stepAux statement storeValue stacks := by
  induction statement generalizing storeValue stacks with
  | push k write _continuation ih =>
      exact ih _ _
  | peek k read _continuation ih =>
      exact ih _ _
  | pop k read _continuation ih =>
      exact ih _ _
  | load update _continuation ih =>
      exact ih _ _
  | branch test yes no yes_ih no_ih =>
      by_cases test_true : test storeValue
      · simpa [liftStmt, TM2.stepAux, test_true] using yes_ih storeValue stacks
      · simpa [liftStmt, TM2.stepAux, test_true] using no_ih storeValue stacks
  | goto next =>
      simp [liftStmt, config, embed_value]
  | halt =>
      rfl

/-- Rooting preserves and reflects every machine transition. -/
theorem respects {stack : Type*} [DecidableEq stack]
    {symbol : stack → Type*} {source store : Type*}
    (sourceMachine : source → TM2.Stmt symbol source store) (root : source) :
    Turing.Respects (TM2.step (machine sourceMachine root)) (TM2.step sourceMachine)
      fun rooted sourceConfig => config root rooted = sourceConfig := by
  rw [Turing.fun_respects]
  rintro ⟨label, storeValue, stacks⟩
  cases label with
  | none =>
      rfl
  | some label =>
      simp only [TM2.step, machine, Turing.FRespects]
      apply Relation.TransGen.single
      simp only [Option.mem_def, Option.some.injEq]
      simpa [TM2.step, config] using congrArg some
        (config_stepAux_liftStmt Label.source root (fun _ => rfl)
          (sourceMachine (label.value root)) storeValue stacks).symm

theorem supportsStmt_liftStmt {stack : Type*} {symbol : stack → Type*}
    {source store : Type*} [DecidableEq source] (support : Finset source)
    (statement : TM2.Stmt symbol source store)
    (supported : TM2.SupportsStmt support statement) :
    TM2.SupportsStmt (insert .root (support.image Label.source))
      (liftStmt Label.source statement) := by
  induction statement with
  | push k write continuation ih | peek k write continuation ih
  | pop k write continuation ih | load write continuation ih =>
      exact ih supported
  | branch test yes no yes_ih no_ih =>
      exact ⟨yes_ih supported.1, no_ih supported.2⟩
  | goto next =>
      intro storeValue
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨next storeValue,
        supported storeValue, rfl⟩)
  | halt =>
      trivial

/-- A finite source support lifts to a finite support containing the added root. -/
theorem supports {stack : Type*} {symbol : stack → Type*}
    {source store : Type*} [DecidableEq source] [Inhabited source]
    (sourceMachine : source → TM2.Stmt symbol source store) (root : source)
    (support : Finset source) (supported : TM2.Supports sourceMachine support)
    (root_supported : root ∈ support) :
    TM2.Supports (machine sourceMachine root)
      (insert .root (support.image Label.source)) := by
  constructor
  · change Label.root ∈ insert Label.root (support.image Label.source)
    simp
  · intro label label_mem
    apply supportsStmt_liftStmt support
    apply supported.2
    cases label with
    | root => exact root_supported
    | source q =>
        simp only [Finset.mem_insert, Label.source.injEq, reduceCtorEq, false_or,
          Finset.mem_image] at label_mem
        obtain ⟨sourceLabel, source_mem, source_eq⟩ := label_mem
        exact source_eq ▸ source_mem

end SeededTM2
end Undecidability
end MatrixMortality
