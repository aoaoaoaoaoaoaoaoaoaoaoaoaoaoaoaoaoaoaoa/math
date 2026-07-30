import Mathlib.Logic.Relation

/-!
# Exact finite executions

`Relation.ReachesIn relation steps before after` is the `steps`-fold relational composition.
Reflexive-transitive and positive-transitive closure are existential views of this indexed
evidence, not independent execution notions.
-/

namespace Relation

/-- Reachability by exactly `steps` applications of `relation`. -/
inductive ReachesIn {α : Type*} (relation : α → α → Prop) : Nat → α → α → Prop
  | refl (state : α) : ReachesIn relation 0 state state
  | head {steps : Nat} {before middle after : α} :
      relation before middle →
      ReachesIn relation steps middle after →
      ReachesIn relation (steps + 1) before after

namespace ReachesIn

/-- Append one transition to an exact execution. -/
theorem tail {α : Type*} {relation : α → α → Prop} {steps : Nat}
    {before middle after : α} (execution : ReachesIn relation steps before middle)
    (step : relation middle after) :
    ReachesIn relation (steps + 1) before after := by
  induction execution with
  | refl => exact .head step (.refl _)
  | head first _ ih => exact .head first (ih step)

/-- Concatenate exact executions, adding their transition counts. -/
theorem trans {α : Type*} {relation : α → α → Prop} {leftSteps rightSteps : Nat}
    {before middle after : α} (left : ReachesIn relation leftSteps before middle)
    (right : ReachesIn relation rightSteps middle after) :
    ReachesIn relation (leftSteps + rightSteps) before after := by
  induction left with
  | refl => simpa using right
  | head step _ ih =>
      simpa [Nat.add_assoc, Nat.add_comm rightSteps 1] using
        ReachesIn.head step (ih right)

/-- Transport an exact execution through a relation homomorphism. -/
theorem map {α β : Type*} {source : α → α → Prop} {target : β → β → Prop}
    (mapState : α → β)
    (mapStep : ∀ {before after}, source before after →
      target (mapState before) (mapState after))
    {steps : Nat} {before after : α} (execution : ReachesIn source steps before after) :
    ReachesIn target steps (mapState before) (mapState after) := by
  induction execution with
  | refl => exact .refl _
  | head step _ ih => exact .head (mapStep step) ih

/-- Enlarge the one-step relation without changing an execution. -/
theorem mono {α : Type*} {source target : α → α → Prop}
    (embed : ∀ {before after}, source before after → target before after)
    {steps : Nat} {before after : α} (execution : ReachesIn source steps before after) :
    ReachesIn target steps before after :=
  execution.map id embed

/-- A relation-closed set contains the endpoint of every exact execution which starts in it. -/
theorem target_mem {α : Type*} {relation : α → α → Prop}
    {states : Set α} {steps : Nat} {before after : α}
    (closed : ∀ {source target}, source ∈ states →
      relation source target → target ∈ states)
    (source_mem : before ∈ states)
    (execution : ReachesIn relation steps before after) :
    after ∈ states := by
  induction execution with
  | refl => exact source_mem
  | head first _ induction =>
      exact induction (closed source_mem first)

/-- Forget the exact transition count. -/
theorem toReflTransGen {α : Type*} {relation : α → α → Prop} {steps : Nat}
    {before after : α} (execution : ReachesIn relation steps before after) :
    ReflTransGen relation before after := by
  induction execution with
  | refl => exact .refl
  | head step _ ih => exact .head step ih

/-- Forget a positive exact transition count. -/
theorem toTransGen {α : Type*} {relation : α → α → Prop} {steps : Nat}
    {before after : α} (execution : ReachesIn relation steps before after)
    (positive : 0 < steps) :
    TransGen relation before after := by
  cases execution with
  | refl => simp at positive
  | head step later => exact .head' step later.toReflTransGen

end ReachesIn

/-- Reflexive-transitive reachability is existential exact reachability. -/
theorem reflTransGen_iff_exists_reachesIn {α : Type*} {relation : α → α → Prop}
    {before after : α} :
    ReflTransGen relation before after ↔
      ∃ steps, ReachesIn relation steps before after := by
  constructor
  · intro reach
    induction reach using ReflTransGen.head_induction_on with
    | refl => exact ⟨0, .refl _⟩
    | @head before middle step _ ih =>
        obtain ⟨steps, later⟩ := ih
        exact ⟨steps + 1, .head step later⟩
  · rintro ⟨_, execution⟩
    exact execution.toReflTransGen

/-- Positive-transitive reachability is existential positive exact reachability. -/
theorem transGen_iff_exists_pos_reachesIn {α : Type*} {relation : α → α → Prop}
    {before after : α} :
    TransGen relation before after ↔
      ∃ steps, 0 < steps ∧ ReachesIn relation steps before after := by
  constructor
  · intro reach
    induction reach with
    | single step => exact ⟨1, by decide, .head step (.refl _)⟩
    | tail _ step ih =>
        obtain ⟨steps, _, earlier⟩ := ih
        exact ⟨steps + 1, Nat.zero_lt_succ _, earlier.tail step⟩
  · rintro ⟨_, positive, execution⟩
    exact execution.toTransGen positive

end Relation
