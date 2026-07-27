import Mathlib.Data.List.Basic
import Mathlib.Logic.Equiv.Defs
import MatrixMortality.IndexedExecution

/-!
# Fixed-width tag queues

This file isolates the semantic core of the tag-system reduction.  A `Stroke` records the
exact block of `β` symbols deleted by one tag step.  The history equation

`consumed ++ final = initial ++ produced`

is then a complete certificate for a finite queue execution.  Its converse deliberately stops
at the first queue shorter than `β`; no post-halting transition is ever inferred.
-/

namespace MatrixMortality

/-- One deletion block of width `β`, with its rule-selecting head exposed. -/
structure Stroke (α : Type*) (β : Nat) where
  /-- The first deleted symbol, which selects the tag rule. -/
  head : α
  /-- The remaining deleted symbols after the rule-selecting head. -/
  wake : List α
  /-- The head and wake together have deletion width `β`. -/
  width : wake.length + 1 = β

namespace Stroke

/-- Reassemble the complete deleted block represented by a stroke. -/
def letters {α : Type*} {β : Nat} (stroke : Stroke α β) : List α :=
  stroke.head :: stroke.wake

/-- Relabel every symbol of a deletion stroke. -/
def map {α γ : Type*} {β : Nat} (relabel : α → γ) (stroke : Stroke α β) :
    Stroke γ β where
  head := relabel stroke.head
  wake := stroke.wake.map relabel
  width := by simpa using stroke.width

@[simp] theorem head_map {α γ : Type*} {β : Nat} (relabel : α → γ)
    (stroke : Stroke α β) :
    (stroke.map relabel).head = relabel stroke.head := rfl

@[simp] theorem length_letters {α : Type*} {β : Nat} (stroke : Stroke α β) :
    stroke.letters.length = β := by
  simpa [letters, Nat.add_comm] using stroke.width

@[simp] theorem letters_map {α γ : Type*} {β : Nat} (relabel : α → γ)
    (stroke : Stroke α β) :
    (stroke.map relabel).letters = stroke.letters.map relabel := rfl

end Stroke

/-- The symbols deleted by a finite stroke history. -/
def consumed {α : Type*} {β : Nat} (history : List (Stroke α β)) : List α :=
  (history.map Stroke.letters).join

/-- The rule words appended by a finite stroke history. -/
def produced {α : Type*} {β : Nat} (output : α → List α)
    (history : List (Stroke α β)) : List α :=
  (history.map fun stroke => output stroke.head).join

@[simp] theorem consumed_nil {α : Type*} {β : Nat} :
    consumed ([] : List (Stroke α β)) = [] := rfl

@[simp] theorem consumed_cons {α : Type*} {β : Nat} (stroke : Stroke α β)
    (history : List (Stroke α β)) :
    consumed (stroke :: history) = stroke.letters ++ consumed history := rfl

@[simp] theorem produced_nil {α : Type*} {β : Nat} (output : α → List α) :
    produced output ([] : List (Stroke α β)) = [] := rfl

@[simp] theorem produced_cons {α : Type*} {β : Nat} (output : α → List α)
    (stroke : Stroke α β) (history : List (Stroke α β)) :
    produced output (stroke :: history) = output stroke.head ++ produced output history := rfl

theorem common_prefix_of_length_le {α : Type*} {x y common : List α}
    (hx : x <+: common) (hy : y <+: common) (hlen : x.length ≤ y.length) : x <+: y := by
  obtain hxy | hyx := List.prefix_or_prefix_of_prefix hx hy
  · exact hxy
  · have heq : y = x := hyx.eq_of_length <| Nat.le_antisymm hyx.length_le hlen
    simp [heq]

/-- One lawful fixed-width tag step. -/
def TagStep {α : Type*} (β : Nat) (output : α → List α)
    (before after : List α) : Prop :=
  ∃ stroke : Stroke α β, ∃ rest,
    before = stroke.letters ++ rest ∧ after = rest ++ output stroke.head

/-- Relabel a tag system along an alphabet equivalence. -/
def relabelTagOutput {α γ : Type*} (relabel : α ≃ γ) (output : α → List α) :
    γ → List γ :=
  fun symbol => (output (relabel.symm symbol)).map relabel

@[simp] theorem relabelTagOutput_apply {α γ : Type*} (relabel : α ≃ γ)
    (output : α → List α) (symbol : α) :
    relabelTagOutput relabel output (relabel symbol) = (output symbol).map relabel := by
  simp [relabelTagOutput]

@[simp] theorem relabelTagOutput_symm {α γ : Type*} (relabel : α ≃ γ)
    (output : α → List α) :
    relabelTagOutput relabel.symm (relabelTagOutput relabel output) = output := by
  funext symbol
  simp [relabelTagOutput]

/-- Relabelling a lawful tag transition preserves its exact queue semantics. -/
theorem TagStep.relabel {α γ : Type*} {β : Nat} {output : α → List α}
    {before after : List α} (relabel : α ≃ γ) (step : TagStep β output before after) :
    TagStep β (relabelTagOutput relabel output)
      (before.map relabel) (after.map relabel) := by
  obtain ⟨stroke, rest, before_eq, after_eq⟩ := step
  refine ⟨stroke.map relabel, rest.map relabel, ?_, ?_⟩
  · simp [before_eq, List.map_append]
  · simp [after_eq, List.map_append]

/-- Tag transitions are conjugate under alphabet equivalence. -/
theorem tagStep_relabel_iff {α γ : Type*} {β : Nat} (relabel : α ≃ γ)
    (output : α → List α) (before after : List α) :
    TagStep β (relabelTagOutput relabel output)
        (before.map relabel) (after.map relabel) ↔
      TagStep β output before after := by
  constructor
  · intro step
    simpa [relabelTagOutput] using step.relabel relabel.symm
  · exact TagStep.relabel relabel

/-- A fixed-width tag system has at most one successor from each queue. -/
theorem tagStep_deterministic {α : Type*} {β : Nat} {output : α → List α}
    {before after₁ after₂ : List α} (first : TagStep β output before after₁)
    (second : TagStep β output before after₂) :
    after₁ = after₂ := by
  obtain ⟨stroke₁, rest₁, before₁, after₁_eq⟩ := first
  obtain ⟨stroke₂, rest₂, before₂, after₂_eq⟩ := second
  have prefix₁ : stroke₁.letters <+: before := ⟨rest₁, before₁.symm⟩
  have prefix₂ : stroke₂.letters <+: before := ⟨rest₂, before₂.symm⟩
  have letters_length : stroke₁.letters.length = stroke₂.letters.length := by
    simp
  have letters_eq : stroke₁.letters = stroke₂.letters :=
    (common_prefix_of_length_le prefix₁ prefix₂ letters_length.le).eq_of_length letters_length
  have heads_eq : stroke₁.head = stroke₂.head := by
    have := congrArg List.head? letters_eq
    simpa [Stroke.letters] using this
  have rests_eq : rest₁ = rest₂ := by
    have append_eq :
        stroke₁.letters ++ rest₁ = stroke₂.letters ++ rest₂ :=
      before₁.symm.trans before₂
    rw [letters_eq] at append_eq
    exact List.append_cancel_left append_eq
  rw [after₁_eq, after₂_eq, rests_eq, heads_eq]

/-- One lawful tag step whose rule-selecting head is not the distinguished symbol. -/
def HeadAvoidingTagStep {α : Type*} (β : Nat) (output : α → List α) (target : α)
    (before after : List α) : Prop :=
  ∃ stroke : Stroke α β, ∃ rest,
    stroke.head ≠ target ∧
      before = stroke.letters ++ rest ∧ after = rest ++ output stroke.head

/-- Relabelling preserves a tag transition and its distinguished-head exclusion. -/
theorem HeadAvoidingTagStep.relabel {α γ : Type*} {β : Nat} {output : α → List α}
    {target : α} {before after : List α} (relabel : α ≃ γ)
    (step : HeadAvoidingTagStep β output target before after) :
    HeadAvoidingTagStep β (relabelTagOutput relabel output) (relabel target)
      (before.map relabel) (after.map relabel) := by
  obtain ⟨stroke, rest, head_ne, before_eq, after_eq⟩ := step
  refine ⟨stroke.map relabel, rest.map relabel, ?_, ?_, ?_⟩
  · exact fun equality => head_ne (relabel.injective equality)
  · simp [before_eq, List.map_append]
  · simp [after_eq, List.map_append]

/-- Head-avoiding tag transitions are conjugate under alphabet equivalence. -/
theorem headAvoidingTagStep_relabel_iff {α γ : Type*} {β : Nat}
    (relabel : α ≃ γ) (output : α → List α) (target : α)
    (before after : List α) :
    HeadAvoidingTagStep β (relabelTagOutput relabel output) (relabel target)
        (before.map relabel) (after.map relabel) ↔
      HeadAvoidingTagStep β output target before after := by
  constructor
  · intro step
    simpa [relabelTagOutput] using step.relabel relabel.symm
  · exact HeadAvoidingTagStep.relabel relabel

/-- Reflexive-transitive reachability under one fixed-width tag step. -/
def TagReaches {α : Type*} (β : Nat) (output : α → List α) : List α → List α → Prop :=
  Relation.ReflTransGen (TagStep β output)

/-- Reflexive-transitive tag execution that never reads the distinguished symbol. -/
def HeadAvoidingTagReaches {α : Type*} (β : Nat) (output : α → List α) (target : α) :
    List α → List α → Prop :=
  Relation.ReflTransGen (HeadAvoidingTagStep β output target)

/-- A tag execution indexed by its exact number of transitions. -/
abbrev TagReachesIn {α : Type*} (β : Nat) (output : α → List α) :=
  Relation.ReachesIn (TagStep β output)

/-- A head-avoiding tag execution indexed by its exact number of transitions. -/
abbrev HeadAvoidingTagReachesIn {α : Type*} (β : Nat) (output : α → List α)
    (target : α) :=
  Relation.ReachesIn (HeadAvoidingTagStep β output target)

/-- Relabel an exact tag execution without changing its transition count. -/
theorem TagReachesIn.relabel {α γ : Type*} {β : Nat} {output : α → List α}
    {steps : Nat} {before after : List α} (relabel : α ≃ γ)
    (reach : TagReachesIn β output steps before after) :
    TagReachesIn β (relabelTagOutput relabel output) steps
      (before.map relabel) (after.map relabel) :=
  reach.map (List.map relabel) (TagStep.relabel relabel)

/-- Exact tag executions are conjugate under alphabet equivalence. -/
theorem tagReachesIn_relabel_iff {α γ : Type*} {β : Nat} (relabel : α ≃ γ)
    (output : α → List α) (steps : Nat) (before after : List α) :
    TagReachesIn β (relabelTagOutput relabel output) steps
        (before.map relabel) (after.map relabel) ↔
      TagReachesIn β output steps before after := by
  constructor
  · intro reach
    simpa [relabelTagOutput] using reach.relabel relabel.symm
  · exact TagReachesIn.relabel relabel

/-- Relabel a finite tag execution. -/
theorem TagReaches.relabel {α γ : Type*} {β : Nat} {output : α → List α}
    {before after : List α} (relabel : α ≃ γ)
    (reach : TagReaches β output before after) :
    TagReaches β (relabelTagOutput relabel output)
      (before.map relabel) (after.map relabel) := by
  induction reach with
  | refl => exact .refl
  | tail _ step earlier =>
      exact .tail earlier (step.relabel relabel)

/-- Finite tag executions are conjugate under alphabet equivalence. -/
theorem tagReaches_relabel_iff {α γ : Type*} {β : Nat} (relabel : α ≃ γ)
    (output : α → List α) (before after : List α) :
    TagReaches β (relabelTagOutput relabel output)
        (before.map relabel) (after.map relabel) ↔
      TagReaches β output before after := by
  constructor
  · intro reach
    simpa [relabelTagOutput] using reach.relabel relabel.symm
  · exact TagReaches.relabel relabel

/-- Relabel a finite head-avoiding tag execution. -/
theorem HeadAvoidingTagReaches.relabel {α γ : Type*} {β : Nat}
    {output : α → List α} {target : α} {before after : List α}
    (relabel : α ≃ γ) (reach : HeadAvoidingTagReaches β output target before after) :
    HeadAvoidingTagReaches β (relabelTagOutput relabel output) (relabel target)
      (before.map relabel) (after.map relabel) := by
  induction reach with
  | refl => exact .refl
  | tail _ step earlier =>
      exact .tail earlier (step.relabel relabel)

/-- Head-avoiding tag executions are conjugate under alphabet equivalence. -/
theorem headAvoidingTagReaches_relabel_iff {α γ : Type*} {β : Nat}
    (relabel : α ≃ γ) (output : α → List α) (target : α)
    (before after : List α) :
    HeadAvoidingTagReaches β (relabelTagOutput relabel output) (relabel target)
        (before.map relabel) (after.map relabel) ↔
      HeadAvoidingTagReaches β output target before after := by
  constructor
  · intro reach
    simpa [relabelTagOutput] using reach.relabel relabel.symm
  · exact HeadAvoidingTagReaches.relabel relabel

theorem HeadAvoidingTagStep.toTagStep {α : Type*} {β : Nat} {output : α → List α}
    {target : α} {before after : List α}
    (step : HeadAvoidingTagStep β output target before after) :
    TagStep β output before after := by
  obtain ⟨stroke, rest, _, before_eq, after_eq⟩ := step
  exact ⟨stroke, rest, before_eq, after_eq⟩

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

theorem headAvoidingTagStep_two_iff {α : Type*} (output : α → List α) (target : α)
    (before after : List α) :
    HeadAvoidingTagStep 2 output target before after ↔
      ∃ head wake tail,
        head ≠ target ∧
          before = head :: wake :: tail ∧ after = tail ++ output head := by
  constructor
  · rintro ⟨⟨head, wake, width⟩, tail, head_ne, before_eq, after_eq⟩
    have wake_length : wake.length = 1 := by omega
    obtain ⟨wakeHead, rfl⟩ := List.length_eq_one.mp wake_length
    exact ⟨head, wakeHead, tail, head_ne, before_eq, after_eq⟩
  · rintro ⟨head, wake, tail, head_ne, rfl, rfl⟩
    exact ⟨⟨head, [wake], rfl⟩, tail, head_ne, rfl, rfl⟩

theorem HeadAvoidingTagStep.source_ne_cons {α : Type*} {β : Nat}
    {output : α → List α} {target : α} {before after : List α}
    (step : HeadAvoidingTagStep β output target before after) (tail : List α) :
    before ≠ target :: tail := by
  obtain ⟨stroke, rest, head_ne, before_eq, _⟩ := step
  intro target_eq
  apply head_ne
  have heads := congrArg List.head? (before_eq.symm.trans target_eq)
  simpa [Stroke.letters] using heads

theorem HeadAvoidingTagReaches.toReaches {α : Type*} {β : Nat}
    {output : α → List α} {target : α} {before after : List α}
    (reach : HeadAvoidingTagReaches β output target before after) :
    TagReaches β output before after := by
  induction reach with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih step.toTagStep

/-- Forget the exact transition count. -/
theorem TagReachesIn.toReaches {α : Type*} {β : Nat} {output : α → List α}
    {steps : Nat} {before after : List α} (reach : TagReachesIn β output steps before after) :
    TagReaches β output before after :=
  reach.toReflTransGen

/-- Every finite tag execution has an exact transition count. -/
theorem exists_tagReachesIn_of_reaches {α : Type*} {β : Nat} {output : α → List α}
    {before after : List α} (reach : TagReaches β output before after) :
    ∃ steps, TagReachesIn β output steps before after :=
  Relation.reflTransGen_iff_exists_reachesIn.mp reach

/-- Forget avoidance and the exact transition count. -/
theorem HeadAvoidingTagReachesIn.toTagReachesIn {α : Type*} {β : Nat}
    {output : α → List α} {target : α} {steps : Nat} {before after : List α}
    (reach : HeadAvoidingTagReachesIn β output target steps before after) :
    TagReachesIn β output steps before after :=
  reach.mono HeadAvoidingTagStep.toTagStep

theorem TagReachesIn.tail {α : Type*} {β : Nat} {output : α → List α}
    {steps : Nat} {before middle after : List α}
    (reach : TagReachesIn β output steps before middle)
    (step : TagStep β output middle after) :
    TagReachesIn β output (steps + 1) before after :=
  Relation.ReachesIn.tail reach step

theorem HeadAvoidingTagReachesIn.tail {α : Type*} {β : Nat}
    {output : α → List α} {target : α} {steps : Nat}
    {before middle after : List α}
    (reach : HeadAvoidingTagReachesIn β output target steps before middle)
    (step : HeadAvoidingTagStep β output target middle after) :
    HeadAvoidingTagReachesIn β output target (steps + 1) before after :=
  Relation.ReachesIn.tail reach step

/-- Every finite head-avoiding execution has an exact transition count. -/
theorem exists_headAvoidingTagReachesIn_of_reaches {α : Type*} {β : Nat}
    {output : α → List α} {target : α} {before after : List α}
    (reach : HeadAvoidingTagReaches β output target before after) :
    ∃ steps, HeadAvoidingTagReachesIn β output target steps before after :=
  Relation.reflTransGen_iff_exists_reachesIn.mp reach

/-- Every nonempty head-avoiding execution has a positive exact transition count. -/
theorem exists_headAvoidingTagReachesIn_of_transGen {α : Type*} {β : Nat}
    {output : α → List α} {target : α} {before after : List α}
    (reach : Relation.TransGen (HeadAvoidingTagStep β output target) before after) :
    ∃ steps, 0 < steps ∧
      HeadAvoidingTagReachesIn β output target steps before after :=
  Relation.transGen_iff_exists_pos_reachesIn.mp reach

/-- Compare a protected deterministic path with any path from the same source. -/
theorem HeadAvoidingTagReachesIn.compare {α : Type*} {β : Nat}
    {output : α → List α} {target : α} {safeSteps pathSteps : Nat}
    {before safeAfter pathAfter : List α}
    (safe : HeadAvoidingTagReachesIn β output target safeSteps before safeAfter)
    (path : TagReachesIn β output pathSteps before pathAfter) :
    (∃ remaining,
        pathSteps = safeSteps + remaining ∧
          TagReachesIn β output remaining safeAfter pathAfter) ∨
      (pathSteps < safeSteps ∧ ∀ tail, pathAfter ≠ target :: tail) := by
  induction safe generalizing pathSteps pathAfter with
  | refl =>
      exact Or.inl ⟨pathSteps, by simp, path⟩
  | @head safeSteps before middle safeAfter safeStep _ ih =>
      cases path with
      | refl =>
          exact Or.inr ⟨by omega, safeStep.source_ne_cons⟩
      | @head pathSteps _ pathMiddle pathAfter pathStep pathLater =>
          have middle_eq : pathMiddle = middle :=
            tagStep_deterministic pathStep safeStep.toTagStep
          subst pathMiddle
          rcases ih pathLater with
            ⟨remaining, steps_eq, later⟩ | ⟨steps_lt, avoids⟩
          · exact Or.inl ⟨remaining, by omega, later⟩
          · exact Or.inr ⟨by omega, avoids⟩

/-- A queue reaches a word shorter than the deletion width after finitely many lawful steps. -/
inductive TagHaltsFrom {α : Type*} (β : Nat) (output : α → List α) : List α → Prop
  | stop {queue} : queue.length < β → TagHaltsFrom β output queue
  | step {queue next} : TagStep β output queue next →
      TagHaltsFrom β output next → TagHaltsFrom β output queue

/-- Relabel a terminating tag execution. -/
theorem TagHaltsFrom.relabel {α γ : Type*} {β : Nat} {output : α → List α}
    {queue : List α} (relabel : α ≃ γ) (halts : TagHaltsFrom β output queue) :
    TagHaltsFrom β (relabelTagOutput relabel output) (queue.map relabel) := by
  induction halts with
  | stop short =>
      exact .stop <| by simpa using short
  | step step _ later =>
      exact .step (step.relabel relabel) later

/-- Tag termination is conjugate under alphabet equivalence. -/
theorem tagHaltsFrom_relabel_iff {α γ : Type*} {β : Nat} (relabel : α ≃ γ)
    (output : α → List α) (queue : List α) :
    TagHaltsFrom β (relabelTagOutput relabel output) (queue.map relabel) ↔
      TagHaltsFrom β output queue := by
  constructor
  · intro halts
    simpa [relabelTagOutput] using halts.relabel relabel.symm
  · exact TagHaltsFrom.relabel relabel

/-- Pull termination backward along a finite tag execution. -/
theorem TagHaltsFrom.before {α : Type*} {β : Nat} {output : α → List α}
    {before after : List α} (halts : TagHaltsFrom β output after)
    (reach : TagReaches β output before after) :
    TagHaltsFrom β output before := by
  induction reach with
  | refl => exact halts
  | tail _ step earlier => exact earlier (.step step halts)

/-- A history equation is sound: it describes lawful steps until its prescribed short final
queue is reached, or until an even earlier short queue is encountered. -/
theorem tagHaltsFrom_of_history {α : Type*} {β : Nat} (output : α → List α)
    (history : List (Stroke α β)) (initial final : List α) (hfinal : final.length < β)
    (hequation : consumed history ++ final = initial ++ produced output history) :
    TagHaltsFrom β output initial := by
  induction history generalizing initial with
  | nil =>
      simp only [consumed_nil, produced_nil, List.nil_append, List.append_nil] at hequation
      subst initial
      exact .stop hfinal
  | cons stroke history ih =>
      by_cases hshort : initial.length < β
      · exact .stop hshort
      · have hwidth : β ≤ initial.length := Nat.le_of_not_gt hshort
        have hstrokePrefix : stroke.letters <+:
            consumed (stroke :: history) ++ final := by
          simp only [consumed_cons, List.append_assoc]
          exact List.prefix_append _ _
        have hinitialPrefix : initial <+: consumed (stroke :: history) ++ final := by
          rw [hequation]
          exact List.prefix_append _ _
        have hprefix : stroke.letters <+: initial :=
          common_prefix_of_length_le hstrokePrefix hinitialPrefix <| by
            simpa using hwidth
        obtain ⟨rest, hinitial⟩ := hprefix
        have htail : consumed history ++ final =
            (rest ++ output stroke.head) ++ produced output history := by
          rw [consumed_cons, ← hinitial, produced_cons, List.append_assoc] at hequation
          have hnormalized : stroke.letters ++ (consumed history ++ final) =
              stroke.letters ++ ((rest ++ output stroke.head) ++ produced output history) := by
            simpa [List.append_assoc] using hequation
          exact List.append_cancel_left hnormalized
        apply TagHaltsFrom.step
        · exact ⟨stroke, rest, hinitial.symm, rfl⟩
        · exact ih (rest ++ output stroke.head) htail

/-- A terminating tag computation emits a stroke history satisfying the global queue
equation. -/
theorem history_of_tagHaltsFrom {α : Type*} {β : Nat} (output : α → List α)
    {initial : List α} (hhalts : TagHaltsFrom β output initial) :
    ∃ history : List (Stroke α β), ∃ final : List α,
      final.length < β ∧ consumed history ++ final = initial ++ produced output history := by
  induction hhalts with
  | stop hshort => exact ⟨[], _, hshort, by simp⟩
  | @step queue next hstep _ ih =>
      obtain ⟨stroke, rest, hqueue, hnext⟩ := hstep
      obtain ⟨history, final, hfinal, hequation⟩ := ih
      refine ⟨stroke :: history, final, hfinal, ?_⟩
      simp only [consumed_cons, produced_cons]
      calc
        (stroke.letters ++ consumed history) ++ final =
            stroke.letters ++ (consumed history ++ final) := by simp [List.append_assoc]
        _ = stroke.letters ++ (next ++ produced output history) := by rw [hequation]
        _ = (stroke.letters ++ rest) ++ output stroke.head ++ produced output history := by
          rw [hnext]
          simp [List.append_assoc]
        _ = queue ++ (output stroke.head ++ produced output history) := by
          rw [hqueue]
          simp [List.append_assoc]

/-- If an invariant identifies every short queue with a chosen terminal word, a terminating
execution yields a history ending at exactly that terminal. -/
theorem terminal_history_of_tagHaltsFrom {α : Type*} {β : Nat} (output : α → List α)
    (invariant : List α → Prop) (terminal initial : List α)
    (hpreserve : ∀ {before after}, invariant before →
      TagStep β output before after → invariant after)
    (hterminal : ∀ {queue}, invariant queue → queue.length < β → queue = terminal)
    (hinitial : invariant initial) (hhalts : TagHaltsFrom β output initial) :
    ∃ history : List (Stroke α β),
      consumed history ++ terminal = initial ++ produced output history := by
  induction hhalts with
  | @stop queue hshort =>
      exact ⟨[], by simp [hterminal hinitial hshort]⟩
  | @step queue next hstep _ ih =>
      obtain ⟨history, hequation⟩ := ih (hpreserve hinitial hstep)
      obtain ⟨stroke, rest, hqueue, hnextQueue⟩ := hstep
      refine ⟨stroke :: history, ?_⟩
      simp only [consumed_cons, produced_cons]
      calc
        (stroke.letters ++ consumed history) ++ terminal =
            stroke.letters ++ (consumed history ++ terminal) := by simp [List.append_assoc]
        _ = stroke.letters ++ (next ++ produced output history) := by rw [hequation]
        _ = (stroke.letters ++ rest) ++ output stroke.head ++ produced output history := by
          rw [hnextQueue]
          simp [List.append_assoc]
        _ = queue ++ (output stroke.head ++ produced output history) := by
          rw [hqueue]
          simp [List.append_assoc]

end MatrixMortality
