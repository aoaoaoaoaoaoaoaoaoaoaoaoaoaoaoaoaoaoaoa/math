import MatrixMortality.MarkedTerminal

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

@[simp] theorem length_letters {α : Type*} {β : Nat} (stroke : Stroke α β) :
    stroke.letters.length = β := by
  simpa [letters, Nat.add_comm] using stroke.width

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

/-- One lawful fixed-width tag step. -/
def TagStep {α : Type*} (β : Nat) (output : α → List α)
    (before after : List α) : Prop :=
  ∃ stroke : Stroke α β, ∃ rest,
    before = stroke.letters ++ rest ∧ after = rest ++ output stroke.head

/-- A queue reaches a word shorter than the deletion width after finitely many lawful steps. -/
inductive TagHaltsFrom {α : Type*} (β : Nat) (output : α → List α) : List α → Prop
  | stop {queue} : queue.length < β → TagHaltsFrom β output queue
  | step {queue next} : TagStep β output queue next →
      TagHaltsFrom β output next → TagHaltsFrom β output queue

theorem common_prefix_of_length_le {α : Type*} {x y common : List α}
    (hx : x <+: common) (hy : y <+: common) (hlen : x.length ≤ y.length) : x <+: y := by
  obtain hxy | hyx := List.prefix_or_prefix_of_prefix hx hy
  · exact hxy
  · have heq : y = x := hyx.eq_of_length <| Nat.le_antisymm hyx.length_le hlen
    simp [heq]

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
