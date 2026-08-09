import MatrixMortality.WordMorphism

/-!
# Exact free-monoid discrepancy laws

Prefix discrepancy is the semantic state used by the global GPCP obstruction.  A first internal
mismatch is permanent, and every same-sign or sign-changing update is an exact word equation on
the unmatched suffix.
-/

namespace MatrixMortality

namespace WordDiscrepancy

variable {α : Type*}

/-- Two words are prefix-comparable when one is the other followed by a residual word. -/
def PrefixComparable (left right : List α) : Prop :=
  (∃ residual, right = left ++ residual) ∨
    ∃ residual, left = right ++ residual

/-- Equality after arbitrary continuations already forces the original words to be
prefix-comparable. -/
theorem prefixComparable_of_append_eq (left right leftTail rightTail : List α)
    (equal : left ++ leftTail = right ++ rightTail) :
    PrefixComparable left right := by
  induction left generalizing right with
  | nil =>
      left
      exact ⟨right, rfl⟩
  | cons leftHead left leftInduction =>
      cases right with
      | nil =>
          right
          exact ⟨leftHead :: left, rfl⟩
      | cons rightHead right =>
          change leftHead :: (left ++ leftTail) =
            rightHead :: (right ++ rightTail) at equal
          have head_eq := (List.cons.inj equal).1
          have tail_eq := (List.cons.inj equal).2
          subst rightHead
          rcases leftInduction right tail_eq with
            (⟨residual, right_eq⟩ | ⟨residual, left_eq⟩)
          · left
            exact ⟨residual, by simp [right_eq]⟩
          · right
            exact ⟨residual, by simp [left_eq]⟩

/-- Once two free-monoid prefixes disagree internally, no pair of continuations can repair them. -/
theorem mismatch_persists {left right : List α}
    (incomparable : ¬PrefixComparable left right) (leftTail rightTail : List α) :
    left ++ leftTail ≠ right ++ rightTail := by
  intro equal
  exact incomparable (prefixComparable_of_append_eq left right leftTail rightTail equal)

/-- Exact positive-to-positive residual update. -/
theorem positive_positive_transition {upper lower residual upperImage lowerImage next : List α}
    (current : upper = lower ++ residual) :
    upper ++ upperImage = lower ++ lowerImage ++ next ↔
      residual ++ upperImage = lowerImage ++ next := by
  subst upper
  simp [List.append_assoc]

/-- Exact positive-to-negative residual update. -/
theorem positive_negative_transition {upper lower residual upperImage lowerImage next : List α}
    (current : upper = lower ++ residual) :
    lower ++ lowerImage = upper ++ upperImage ++ next ↔
      lowerImage = residual ++ upperImage ++ next := by
  subst upper
  simp [List.append_assoc]

/-- Exact negative-to-negative residual update. -/
theorem negative_negative_transition {upper lower residual upperImage lowerImage next : List α}
    (current : lower = upper ++ residual) :
    lower ++ lowerImage = upper ++ upperImage ++ next ↔
      residual ++ lowerImage = upperImage ++ next := by
  subst lower
  simp [List.append_assoc]

/-- Exact negative-to-positive residual update. -/
theorem negative_positive_transition {upper lower residual upperImage lowerImage next : List α}
    (current : lower = upper ++ residual) :
    upper ++ upperImage = lower ++ lowerImage ++ next ↔
      upperImage = residual ++ lowerImage ++ next := by
  subst lower
  simp [List.append_assoc]

/-- Exact terminal test from a positive discrepancy. -/
theorem positive_terminal {upper lower residual upperBoundary lowerBoundary : List α}
    (current : upper = lower ++ residual) :
    upper ++ upperBoundary = lower ++ lowerBoundary ↔
      residual ++ upperBoundary = lowerBoundary := by
  subst upper
  simp [List.append_assoc]

/-- Exact terminal test from a negative discrepancy. -/
theorem negative_terminal {upper lower residual upperBoundary lowerBoundary : List α}
    (current : lower = upper ++ residual) :
    upper ++ upperBoundary = lower ++ lowerBoundary ↔
      upperBoundary = residual ++ lowerBoundary := by
  subst lower
  simp [List.append_assoc]

end WordDiscrepancy

end MatrixMortality
