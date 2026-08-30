import Mathlib.Data.List.Basic

/-!
# Free-monoid morphisms

The Kleisli extension `spell side` is the unique monoid morphism from source words that sends
each source letter `letter` to `side letter`. This file owns its source-independent laws.
-/

namespace MatrixMortality

/-- Extend a letter-to-word map to source words by concatenation. -/
def spell {α β : Type*} (side : α → List β) (word : List α) : List β :=
  word.flatMap side

theorem spell_append {α β : Type*} (side : α → List β) (left right : List α) :
    spell side (left ++ right) = spell side left ++ spell side right := by
  simp [spell]

theorem spell_map {α β γ : Type*} (map : β → γ) (side : α → List β) (word : List α) :
    spell (fun letter => (side letter).map map) word = (spell side word).map map := by
  simpa [spell] using (List.map_flatMap (f := map) (g := side) (l := word)).symm

theorem spell_comp_spell {α β γ : Type*}
    (outer : β → List γ) (inner : α → List β) (word : List α) :
    spell outer (spell inner word) =
      spell (fun letter => spell outer (inner letter)) word := by
  exact List.flatMap_assoc

theorem spell_comp_map {α β γ : Type*} (side : β → List γ) (map : α → β)
    (word : List α) :
    spell (side ∘ map) word = spell side (word.map map) := by
  exact (List.flatMap_map map side word).symm

private theorem fixedBoundary_repeat_of_zero_one {α : Type*}
    (leftBoundary leftBody leftTail rightBoundary rightBody rightTail : List α)
    (atZero : leftBoundary ++ leftTail = rightBoundary ++ rightTail)
    (atOne : leftBoundary ++ leftBody ++ leftTail =
      rightBoundary ++ rightBody ++ rightTail) (count : Nat) :
    leftBoundary ++ (List.replicate count leftBody).flatten ++ leftTail =
      rightBoundary ++ (List.replicate count rightBody).flatten ++ rightTail := by
  rcases List.append_eq_append_iff.mp atZero with
    ⟨debt, rightBoundary_eq, leftTail_eq⟩ |
      ⟨debt, leftBoundary_eq, rightTail_eq⟩
  · have bridge : leftBody ++ debt = debt ++ rightBody := by
      apply List.append_cancel_right
      apply List.append_cancel_left
      simpa only [rightBoundary_eq, leftTail_eq, List.append_assoc] using atOne
    have iterate : ∀ n,
        (List.replicate n leftBody).flatten ++ debt =
          debt ++ (List.replicate n rightBody).flatten := by
      intro n
      induction n with
      | zero => simp
      | succ n induction =>
          simp only [List.replicate_succ, List.flatten_cons]
          rw [List.append_assoc, induction, ← List.append_assoc, bridge,
            List.append_assoc]
    rw [rightBoundary_eq, leftTail_eq]
    simp only [List.append_assoc]
    apply congrArg (leftBoundary ++ ·)
    rw [← List.append_assoc, iterate, List.append_assoc]
  · have bridge : debt ++ leftBody = rightBody ++ debt := by
      apply List.append_cancel_right
      apply List.append_cancel_left
      simpa only [leftBoundary_eq, rightTail_eq, List.append_assoc] using atOne
    have iterate : ∀ n,
        debt ++ (List.replicate n leftBody).flatten =
          (List.replicate n rightBody).flatten ++ debt := by
      intro n
      induction n with
      | zero => simp
      | succ n induction =>
          simp only [List.replicate_succ, List.flatten_cons]
          rw [← List.append_assoc, bridge, List.append_assoc, induction,
            ← List.append_assoc]
    rw [leftBoundary_eq, rightTail_eq]
    simp only [List.append_assoc, iterate]

/-- If a fixed-boundary word equation holds at two consecutive repetitions, it holds at every
later repetition. -/
theorem fixedBoundary_consecutive_repeat_tail {α : Type*}
    (leftBoundary leftBody leftTail rightBoundary rightBody rightTail : List α)
    (offset : Nat)
    (atOffset :
      leftBoundary ++ (List.replicate offset leftBody).flatten ++ leftTail =
        rightBoundary ++ (List.replicate offset rightBody).flatten ++ rightTail)
    (atSuccessor :
      leftBoundary ++ (List.replicate (offset + 1) leftBody).flatten ++ leftTail =
        rightBoundary ++ (List.replicate (offset + 1) rightBody).flatten ++ rightTail)
    (tail : Nat) :
    leftBoundary ++ (List.replicate (offset + tail) leftBody).flatten ++ leftTail =
      rightBoundary ++ (List.replicate (offset + tail) rightBody).flatten ++ rightTail := by
  have pumped := fixedBoundary_repeat_of_zero_one
    (leftBoundary ++ (List.replicate offset leftBody).flatten) leftBody leftTail
    (rightBoundary ++ (List.replicate offset rightBody).flatten) rightBody rightTail
    (by simpa only [List.append_assoc] using atOffset)
    (by simpa only [List.replicate_add, List.replicate_one, List.flatten_append,
        List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]
      using atSuccessor)
    tail
  simpa only [List.replicate_add, List.flatten_append, List.append_assoc] using pumped

end MatrixMortality
