import MatrixMortality.TagQueue

/-!
# Prefix residuals for fixed-width tag histories

Two words known to be prefixes of a common word differ by a unique oriented suffix. This file
packages that elementary cancellation state and its evolution under a fixed-width tag history.
Recognizers may therefore classify their finite residual graph without rebuilding the generic
prefix calculus.
-/

namespace MatrixMortality

namespace PrefixResidual

variable {α : Type*} {β : Nat}

/-- The oriented suffix left after cancelling the common prefix of two words. -/
inductive Residual (α : Type*) where
  | flush
  | left (head : α) (tail : List α)
  | right (head : α) (tail : List α)
  deriving DecidableEq

namespace Residual

/-- The unmatched word on the left side of a residual. -/
def leftWord : Residual α → List α
  | .flush | .right _ _ => []
  | .left head tail => head :: tail

/-- The unmatched word on the right side of a residual. -/
def rightWord : Residual α → List α
  | .flush | .left _ _ => []
  | .right head tail => head :: tail

/-- A residual realizes the result of cancelling the common prefix of two words. -/
def Realizes (residual : Residual α) (left right : List α) : Prop :=
  left ++ residual.rightWord = right ++ residual.leftWord

end Residual

/-- One residual transition after extending the input and output prefixes by a tag stroke. -/
def Step (output : α → List α) (before : Residual α) (stroke : Stroke α β)
    (after : Residual α) : Prop :=
  before.leftWord ++ stroke.letters ++ after.rightWord =
    before.rightWord ++ output stroke.head ++ after.leftWord

/-- A left-to-right residual path, presented by its final stroke for exact backward analysis. -/
inductive Path (output : α → List α) (initial : Residual α) :
    List (Stroke α β) → Residual α → Prop where
  | nil : Path output initial [] initial
  | snoc {history before stroke after} :
      Path output initial history before →
      Step output before stroke after →
      Path output initial (history ++ [stroke]) after

namespace Path

/-- Prepend a residual transition to a path. -/
theorem cons {output : α → List α} {initial before after : Residual α}
    {stroke : Stroke α β} {history : List (Stroke α β)}
    (step : Step output initial stroke before)
    (path : Path output before history after) :
    Path output initial (stroke :: history) after := by
  induction path with
  | nil => simpa using Path.snoc Path.nil step
  | @snoc history middle last final _ lastStep induction =>
      exact Path.snoc induction lastStep

/-- Concatenate two residual paths meeting at a common residual. -/
theorem append {output : α → List α} {initial middle final : Residual α}
    {left right : List (Stroke α β)}
    (leftPath : Path output initial left middle)
    (rightPath : Path output middle right final) :
    Path output initial (left ++ right) final := by
  induction rightPath with
  | nil => simpa using leftPath
  | snoc _ step induction =>
      simpa [List.append_assoc] using Path.snoc induction step

/-- Expose the last transition of a nonempty residual path. -/
theorem snoc_of_ne_nil {output : α → List α} {initial final : Residual α}
    {history : List (Stroke α β)} (path : Path output initial history final)
    (nonempty : history ≠ []) :
    ∃ priorHistory before stroke,
      history = priorHistory ++ [stroke] ∧
        Path output initial priorHistory before ∧ Step output before stroke final := by
  cases path with
  | nil => exact False.elim (nonempty rfl)
  | snoc priorPath step => exact ⟨_, _, _, rfl, priorPath, step⟩

end Path

/-- Comparable words possess an oriented prefix residual. -/
theorem exists_of_comparable {left right : List α}
    (comparable : left <+: right ∨ right <+: left) :
    ∃ residual, Residual.Realizes residual left right := by
  rcases comparable with leftPrefix | rightPrefix
  · obtain ⟨suffix, equality⟩ := leftPrefix
    cases suffix with
    | nil =>
        refine ⟨.flush, ?_⟩
        simpa [Residual.Realizes, Residual.leftWord, Residual.rightWord] using equality
    | cons head tail =>
        refine ⟨.right head tail, ?_⟩
        simpa [Residual.Realizes, Residual.leftWord, Residual.rightWord] using equality
  · obtain ⟨suffix, equality⟩ := rightPrefix
    cases suffix with
    | nil =>
        refine ⟨.flush, ?_⟩
        simpa [Residual.Realizes, Residual.leftWord, Residual.rightWord] using equality.symm
    | cons head tail =>
        refine ⟨.left head tail, ?_⟩
        simpa [Residual.Realizes, Residual.leftWord, Residual.rightWord] using equality.symm

/-- Two consecutive realized residuals determine their residual transition. -/
theorem step_of_realizes {output : α → List α} {before after : Residual α}
    {left right : List α} {stroke : Stroke α β}
    (beforeRealizes : Residual.Realizes before left right)
    (afterRealizes : Residual.Realizes after (left ++ stroke.letters)
      (right ++ output stroke.head)) :
    Step output before stroke after := by
  cases before with
  | flush =>
      have left_eq_right : left = right := by
        simpa [Residual.Realizes, Residual.leftWord, Residual.rightWord] using beforeRealizes
      subst right
      have reduced := List.append_cancel_left (as := left) (by
        simpa [Residual.Realizes, Residual.leftWord, Residual.rightWord,
          List.append_assoc] using afterRealizes)
      simpa [Step, Residual.leftWord, Residual.rightWord, List.append_assoc] using reduced
  | left head tail =>
      have left_eq : left = right ++ head :: tail := by
        simpa [Residual.Realizes, Residual.leftWord, Residual.rightWord] using beforeRealizes
      subst left
      have reduced := List.append_cancel_left (as := right) (by
        simpa [Residual.Realizes, Residual.leftWord, Residual.rightWord,
          List.append_assoc] using afterRealizes)
      simpa [Step, Residual.leftWord, Residual.rightWord, List.append_assoc] using reduced
  | right head tail =>
      have right_eq : right = left ++ head :: tail := by
        simpa [Residual.Realizes, Residual.leftWord, Residual.rightWord] using
          beforeRealizes.symm
      subst right
      have reduced := List.append_cancel_left (as := left) (by
        simpa [Residual.Realizes, Residual.leftWord, Residual.rightWord,
          List.append_assoc] using afterRealizes)
      simpa [Step, Residual.leftWord, Residual.rightWord, List.append_assoc] using reduced

/-- A residual transition advances every realization by the corresponding tag stroke. -/
theorem realizes_after_step {output : α → List α} {before after : Residual α}
    {left right : List α} {stroke : Stroke α β}
    (realizes : Residual.Realizes before left right)
    (step : Step output before stroke after) :
    Residual.Realizes after (left ++ stroke.letters) (right ++ output stroke.head) := by
  cases before with
  | flush =>
      have left_eq_right : left = right := by
        simpa [Residual.Realizes, Residual.leftWord, Residual.rightWord] using realizes
      subst right
      simpa [Residual.Realizes, Step, Residual.leftWord, Residual.rightWord,
        List.append_assoc] using congrArg (fun suffix => left ++ suffix) step
  | left head tail =>
      have left_eq : left = right ++ head :: tail := by
        simpa [Residual.Realizes, Residual.leftWord, Residual.rightWord] using realizes
      subst left
      simpa [Residual.Realizes, Step, Residual.leftWord, Residual.rightWord,
        List.append_assoc] using congrArg (fun suffix => right ++ suffix) step
  | right head tail =>
      have right_eq : right = left ++ head :: tail := by
        simpa [Residual.Realizes, Residual.leftWord, Residual.rightWord] using realizes.symm
      subst right
      simpa [Residual.Realizes, Step, Residual.leftWord, Residual.rightWord,
        List.append_assoc] using congrArg (fun suffix => left ++ suffix) step

/-- A one-letter right boundary determines the corresponding canonical residual. -/
theorem eq_right_of_boundary {residual : Residual α} {left right : List α}
    (terminal : α) (realizes : Residual.Realizes residual left right)
    (boundary : left ++ [terminal] = right) : residual = .right terminal [] := by
  cases residual with
  | flush =>
      have equality : left = right := by
        simpa [Residual.Realizes, Residual.leftWord, Residual.rightWord] using realizes
      have lengths := congrArg List.length boundary
      rw [equality] at lengths
      simp at lengths
  | left head tail =>
      have equality : left = right ++ head :: tail := by
        simpa [Residual.Realizes, Residual.leftWord, Residual.rightWord] using realizes
      have lengths := congrArg List.length boundary
      rw [equality] at lengths
      simp at lengths
  | right head tail =>
      have equality : left ++ head :: tail = right := by
        simpa [Residual.Realizes, Residual.leftWord, Residual.rightWord] using realizes
      have suffix : head :: tail = [terminal] := by
        apply List.append_cancel_left (as := left)
        exact equality.trans boundary.symm
      have canonical := congrArg
        (fun word => match word with
          | [] => Residual.flush
          | first :: rest => Residual.right first rest) suffix
      simpa using canonical

/-- A completed prefix equation induces a residual path to its one-letter boundary state. -/
theorem path_of_completion (output : α → List α) (terminal : α) (initial : Residual α)
    (left right : List α) (history : List (Stroke α β))
    (realizes : Residual.Realizes initial left right)
    (completion : left ++ consumed history ++ [terminal] =
      right ++ produced output history) :
    Path output initial history (.right terminal []) := by
  induction history generalizing initial left right with
  | nil =>
      have initial_eq := eq_right_of_boundary terminal realizes (by simpa using completion)
      subst initial
      exact Path.nil
  | cons stroke history induction =>
      let nextLeft := left ++ stroke.letters
      let nextRight := right ++ output stroke.head
      have nextLeftPrefix : nextLeft <+: right ++ produced output (stroke :: history) := by
        refine ⟨consumed history ++ [terminal], ?_⟩
        simpa [nextLeft, consumed_cons, List.append_assoc] using completion
      have nextRightPrefix : nextRight <+: right ++ produced output (stroke :: history) := by
        refine ⟨produced output history, ?_⟩
        simp [nextRight, produced_cons, List.append_assoc]
      obtain ⟨next, nextRealizes⟩ := exists_of_comparable
        (List.prefix_or_prefix_of_prefix nextLeftPrefix nextRightPrefix)
      apply Path.cons (step_of_realizes realizes nextRealizes)
      apply induction next nextLeft nextRight nextRealizes
      simpa [nextLeft, nextRight, consumed_cons, produced_cons,
        List.append_assoc] using completion

private theorem consumed_append (left right : List (Stroke α β)) :
    consumed (left ++ right) = consumed left ++ consumed right := by
  simp [consumed]

private theorem produced_append (output : α → List α) (left right : List (Stroke α β)) :
    produced output (left ++ right) = produced output left ++ produced output right := by
  simp [produced]

/-- A residual path realizes the tag-history extensions of its initial word pair. -/
theorem Path.realizes {output : α → List α} {initial final : Residual α}
    {history : List (Stroke α β)} {left right : List α}
    (path : Path output initial history final)
    (realizes : Residual.Realizes initial left right) :
    Residual.Realizes final (left ++ consumed history) (right ++ produced output history) := by
  induction path with
  | nil => simpa using realizes
  | @snoc history before stroke after _ step induction =>
      have advanced := realizes_after_step induction step
      simpa [consumed_append, produced_append, consumed, produced,
        List.append_assoc] using advanced

end PrefixResidual

end MatrixMortality
