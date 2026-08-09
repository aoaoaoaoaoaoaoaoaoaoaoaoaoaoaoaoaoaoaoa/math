import MatrixMortality.WordMorphism
import Mathlib.Algebra.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Endpoint-forcing normal-system compilation

A trace in a prefix normal system always yields one telescoping endpoint equation.  The converse
holds exactly when that endpoint equation forces every intermediate rule prefix.  Underflow is
the obstruction: an endpoint equality may hold even though its first rule is not applicable.
-/

namespace MatrixMortality

namespace EndpointPrefixCompiler

/-- A prefix normal system consumes a rule word from the left and appends its output on the
right. -/
structure NormalSystem (Rule Symbol : Type*) where
  /-- Word required at the left edge before the rule fires. -/
  consume : Rule → List Symbol
  /-- Word appended at the right edge after the rule fires. -/
  produce : Rule → List Symbol

/-- The aggregate word consumed by a rule trace. -/
def consumed {Rule Symbol : Type*} (system : NormalSystem Rule Symbol) : List Rule → List Symbol
  | [] => []
  | rule :: trace => system.consume rule ++ consumed system trace

/-- The aggregate word produced by a rule trace. -/
def produced {Rule Symbol : Type*} (system : NormalSystem Rule Symbol) : List Rule → List Symbol
  | [] => []
  | rule :: trace => system.produce rule ++ produced system trace

@[simp]
theorem consumed_append {Rule Symbol : Type*} (system : NormalSystem Rule Symbol)
    (left right : List Rule) :
    consumed system (left ++ right) = consumed system left ++ consumed system right := by
  induction left with
  | nil => rfl
  | cons rule left induction =>
      simp [consumed, induction, List.append_assoc]

@[simp]
theorem produced_append {Rule Symbol : Type*} (system : NormalSystem Rule Symbol)
    (left right : List Rule) :
    produced system (left ++ right) = produced system left ++ produced system right := by
  induction left with
  | nil => rfl
  | cons rule left induction =>
      simp [produced, induction, List.append_assoc]

/-- One lawful normal-system step `αX ⟶ Xβ`. -/
def NormalStep {Rule Symbol : Type*} (system : NormalSystem Rule Symbol)
    (rule : Rule) (source target : List Symbol) : Prop :=
  ∃ residual,
    source = system.consume rule ++ residual ∧
      target = residual ++ system.produce rule

/-- A derivation whose rule names are fixed by the displayed trace. -/
inductive DerivesAlong {Rule Symbol : Type*} (system : NormalSystem Rule Symbol) :
    List Rule → List Symbol → List Symbol → Prop
  | nil (word : List Symbol) : DerivesAlong system [] word word
  | cons {rule : Rule} {trace : List Rule} {source middle target : List Symbol}
      (step : NormalStep system rule source middle)
      (tail : DerivesAlong system trace middle target) :
      DerivesAlong system (rule :: trace) source target

/-- The fixed-boundary equality exposed by a complete rule trace. -/
def EndpointEquation {Rule Symbol : Type*} (system : NormalSystem Rule Symbol)
    (source target : List Symbol) (trace : List Rule) : Prop :=
  source ++ produced system trace = consumed system trace ++ target

/-- Every lawful derivation satisfies its telescoping endpoint equation. -/
theorem DerivesAlong.endpointEquation {Rule Symbol : Type*} (system : NormalSystem Rule Symbol)
    {trace : List Rule} {source target : List Symbol}
    (derivation : DerivesAlong system trace source target) :
    EndpointEquation system source target trace := by
  induction derivation with
  | nil word => simp [EndpointEquation, consumed, produced]
  | @cons rule trace source middle target step tail induction =>
      rcases step with ⟨residual, source_eq, middle_eq⟩
      subst source
      subst middle
      simp only [EndpointEquation, consumed, produced] at induction ⊢
      simpa only [List.append_assoc] using
        congrArg (fun word => system.consume rule ++ word) induction

/-- Endpoint prefix forcing says that a terminal equality forbids every premature rule. -/
def EndpointPrefixForcing {Rule Symbol : Type*} (system : NormalSystem Rule Symbol)
    (source target : List Symbol) : Prop :=
  ∀ (past : List Rule) (rule : Rule) (suffix : List Rule),
    EndpointEquation system source target (past ++ rule :: suffix) →
      consumed system (past ++ [rule]) <+: source ++ produced system past

private theorem derivesSuffix_of_endpointEquation {Rule Symbol : Type*}
    (system : NormalSystem Rule Symbol) (source target : List Symbol)
    (forcing : EndpointPrefixForcing system source target)
    (past remaining : List Rule) (current : List Symbol)
    (endpoint : EndpointEquation system source target (past ++ remaining))
    (pastState :
      source ++ produced system past = consumed system past ++ current) :
    DerivesAlong system remaining current target := by
  induction remaining generalizing past current with
  | nil =>
      have endpoint' :
          source ++ produced system past = consumed system past ++ target := by
        simpa using endpoint
      have current_eq : current = target := by
        apply List.append_cancel_left (as := consumed system past)
        exact pastState.symm.trans endpoint'
      subst target
      exact DerivesAlong.nil current
  | cons rule remaining induction =>
      obtain ⟨residual, forced⟩ := forcing past rule remaining endpoint
      have current_eq : current = system.consume rule ++ residual := by
        apply List.append_cancel_left (as := consumed system past)
        calc
          consumed system past ++ current = source ++ produced system past :=
            pastState.symm
          _ = consumed system (past ++ [rule]) ++ residual := forced.symm
          _ = consumed system past ++ (system.consume rule ++ residual) := by
            simp [consumed, List.append_assoc]
      let next := residual ++ system.produce rule
      have nextState :
          source ++ produced system (past ++ [rule]) =
            consumed system (past ++ [rule]) ++ next := by
        calc
          source ++ produced system (past ++ [rule]) =
              (source ++ produced system past) ++ system.produce rule := by
            simp [produced, List.append_assoc]
          _ = (consumed system (past ++ [rule]) ++ residual) ++
              system.produce rule := by rw [← forced]
          _ = consumed system (past ++ [rule]) ++ next := by
            simp [next, List.append_assoc]
      have nextEndpoint :
          EndpointEquation system source target ((past ++ [rule]) ++ remaining) := by
        simpa [List.append_assoc] using endpoint
      apply DerivesAlong.cons (middle := next)
      · exact ⟨residual, current_eq, rfl⟩
      · exact induction (past ++ [rule]) next nextEndpoint nextState

/-- Endpoint prefix forcing is the exact converse needed by the three-pair direct compiler. -/
theorem endpointEquation_iff_derivesAlong {Rule Symbol : Type*}
    (system : NormalSystem Rule Symbol) (source target : List Symbol)
    (forcing : EndpointPrefixForcing system source target) (trace : List Rule) :
    EndpointEquation system source target trace ↔
      DerivesAlong system trace source target := by
  constructor
  · intro endpoint
    apply derivesSuffix_of_endpointEquation system source target forcing [] trace source
    · simpa using endpoint
    · simp [consumed, produced]
  · exact DerivesAlong.endpointEquation system

/-! ## The unrestricted telescope admits underflow -/

/-- Symbols in the explicit endpoint-underflow counterexample. -/
inductive UnderflowSymbol
  | zero
  | one
  | mark
  deriving DecidableEq

/-- Rule names in the explicit endpoint-underflow counterexample. -/
inductive UnderflowRule
  | a
  | b
  | c
  deriving DecidableEq

/-- A three-production normal system whose first rule has a false endpoint witness. -/
def underflowSystem : NormalSystem UnderflowRule UnderflowSymbol where
  consume
    | .a => [.zero, .one]
    | .b => [.mark]
    | .c => [.mark, .mark]
  produce
    | .a => [.one]
    | .b => [.mark]
    | .c => [.mark, .mark]

/-- The trace `a` satisfies the aggregate boundary equality. -/
theorem underflow_endpointEquation :
    EndpointEquation underflowSystem [.zero] [] [.a] := by
  rfl

/-- The same trace is not executable: its first left side is longer than the source. -/
theorem underflow_not_derivesAlong :
    ¬DerivesAlong underflowSystem [.a] [.zero] [] := by
  intro derivation
  cases derivation with
  | cons step _ =>
      obtain ⟨residual, source_eq, _⟩ := step
      have length_eq := congrArg List.length source_eq
      simp [underflowSystem] at length_eq

/-- A nonnegative corrected drift spends at most its complete endpoint budget on every prefix. -/
theorem nonnegative_prefix_budget {Rule : Type*} (cost : Rule → ℤ)
    (past suffix : List Rule)
    (nonnegative : ∀ rule ∈ past ++ suffix, 0 ≤ cost rule) :
    (past.map cost).sum ≤ ((past ++ suffix).map cost).sum := by
  rw [List.map_append, List.sum_append]
  have suffix_nonnegative : 0 ≤ (suffix.map cost).sum := by
    apply List.sum_nonneg
    intro value member
    obtain ⟨rule, rule_mem, rfl⟩ := List.mem_map.mp member
    exact nonnegative rule (List.mem_append_right past rule_mem)
  omega

end EndpointPrefixCompiler

end MatrixMortality
