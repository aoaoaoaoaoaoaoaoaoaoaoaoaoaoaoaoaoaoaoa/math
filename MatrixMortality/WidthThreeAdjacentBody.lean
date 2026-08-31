import MatrixMortality.Undecidability.TagExecution
import MatrixMortality.WidthThreeSparseBody

/-!
# Adjacent two-`c` width-three bodies

Every even body `b^p c c b^s` has two explicit periodic queues. This is the first source
stratum in which the one-`c` shrinking-defect argument can fail: the two `c` letters reproduce
exactly after one macro traversal.
-/

namespace MatrixMortality
namespace WidthThreeAdjacentBody

open WidthThreeSparseBody

/-- A restricted width-three body with two adjacent `c` letters. -/
def adjacentBody (left right : Nat) : List TagLetter :=
  bRun left ++ [.c, .c] ++ bRun right

private def doubleQueue (left right : Nat) : List TagLetter :=
  bRun left ++ [.c, .c] ++ bRun right

private def singleQueue (left right : Nat) : List TagLetter :=
  bRun left ++ [.c] ++ bRun right

private theorem bRun_add (left right : Nat) :
    bRun (left + right) = bRun left ++ bRun right := by
  change List.replicate (left + right) TagLetter.b =
    List.replicate left TagLetter.b ++ List.replicate right TagLetter.b
  exact List.replicate_add left right TagLetter.b

private theorem bRun_snoc (length : Nat) :
    bRun (length + 1) = bRun length ++ [.b] :=
  List.replicate_succ'

private theorem doubleQueue_step_three (body : List TagLetter) (left right : Nat) :
    TagStep 3 (tagOutput body) (doubleQueue (left + 3) right)
      (doubleQueue left (right + 1)) := by
  refine ⟨⟨.b, [.b, .b], rfl⟩, doubleQueue left right, ?_, ?_⟩
  · change doubleQueue (left + 3) right = [.b, .b, .b] ++ doubleQueue left right
    simp only [doubleQueue]
    rw [show left + 3 = 3 + left by omega, bRun_add]
    rfl
  · change doubleQueue left (right + 1) = doubleQueue left right ++ [.b]
    simp only [doubleQueue, List.append_assoc]
    rw [bRun_snoc]

private theorem doubleQueue_step_zero (bodyLeft bodyRight tail : Nat) :
    TagStep 3 (tagOutput (adjacentBody bodyLeft bodyRight))
      (doubleQueue 0 (tail + 1)) (doubleQueue (tail + bodyLeft) (bodyRight + 1)) := by
  refine ⟨⟨.c, [.c, .b], rfl⟩, bRun tail, ?_, ?_⟩
  · change doubleQueue 0 (tail + 1) = [.c, .c, .b] ++ bRun tail
    simp only [doubleQueue, bRun_zero, List.nil_append]
    rw [show tail + 1 = 1 + tail by omega, bRun_add]
    rfl
  · change doubleQueue (tail + bodyLeft) (bodyRight + 1) =
      bRun tail ++ tagOutput (adjacentBody bodyLeft bodyRight) .c
    simp only [doubleQueue, adjacentBody, tagOutput, nearyBody, List.append_assoc]
    rw [bRun_add, bRun_snoc]
    simp [List.append_assoc]

private theorem doubleQueue_step_two (body : List TagLetter) (right : Nat) :
    TagStep 3 (tagOutput body) (doubleQueue 2 right) (singleQueue 0 (right + 1)) := by
  refine ⟨⟨.b, [.b, .c], rfl⟩, .c :: bRun right, ?_, ?_⟩
  · simp [doubleQueue, bRun, Stroke.letters]
  · change singleQueue 0 (right + 1) = (.c :: bRun right) ++ [.b]
    simp only [singleQueue, bRun_zero, List.nil_append, List.singleton_append]
    rw [bRun_snoc]
    simp

private theorem singleQueue_step_zero (bodyLeft bodyRight tail : Nat) :
    TagStep 3 (tagOutput (adjacentBody bodyLeft bodyRight))
      (singleQueue 0 (tail + 2)) (doubleQueue (tail + bodyLeft) (bodyRight + 1)) := by
  refine ⟨⟨.c, [.b, .b], rfl⟩, bRun tail, ?_, ?_⟩
  · change singleQueue 0 (tail + 2) = [.c, .b, .b] ++ bRun tail
    simp only [singleQueue, bRun_zero, List.nil_append]
    rw [show tail + 2 = 2 + tail by omega, bRun_add]
    rfl
  · change doubleQueue (tail + bodyLeft) (bodyRight + 1) =
      bRun tail ++ tagOutput (adjacentBody bodyLeft bodyRight) .c
    simp only [doubleQueue, adjacentBody, tagOutput, nearyBody, List.append_assoc]
    rw [bRun_add, bRun_snoc]
    simp [List.append_assoc]

private theorem doubleQueue_leading_reachesIn (body : List TagLetter)
    (count left right : Nat) :
    TagReachesIn 3 (tagOutput body) count
      (doubleQueue (left + 3 * count) right) (doubleQueue left (right + count)) := by
  induction count generalizing right with
  | zero => simp only [Nat.mul_zero, Nat.add_zero]; exact .refl _
  | succ count induction =>
      have source_eq : left + 3 * (count + 1) = (left + 3 * count) + 3 := by omega
      have target_eq : right + 1 + count = right + (count + 1) := by omega
      rw [source_eq]
      exact Relation.ReachesIn.head
        (doubleQueue_step_three body (left + 3 * count) right) <| by
          have later := induction (right + 1)
          rw [target_eq] at later
          exact later

/-- The lower adjacent-`c` periodic queue. -/
def lowerCycleQueue (halfTail right : Nat) : List TagLetter :=
  doubleQueue (3 * halfTail - 1) (right + 1)

/-- The upper adjacent-`c` periodic queue. -/
def upperCycleQueue (halfTail right : Nat) : List TagLetter :=
  doubleQueue (3 * halfTail) (right + 1)

/-- The lower periodic queue returns after exactly `halfTail + 1` tag steps. -/
theorem lowerCycleQueue_reachesIn (bodyLeft bodyRight halfTail : Nat)
    (halfTail_pos : 0 < halfTail) (body_sum : bodyLeft + bodyRight = 2 * halfTail) :
    TagReachesIn 3 (tagOutput (adjacentBody bodyLeft bodyRight)) (halfTail + 1)
      (lowerCycleQueue halfTail bodyRight) (lowerCycleQueue halfTail bodyRight) := by
  have leading := doubleQueue_leading_reachesIn (adjacentBody bodyLeft bodyRight)
    (halfTail - 1) 2 (bodyRight + 1)
  have leading_source : 2 + 3 * (halfTail - 1) = 3 * halfTail - 1 := by omega
  have leading_target : bodyRight + 1 + (halfTail - 1) = bodyRight + halfTail := by omega
  rw [leading_source, leading_target] at leading
  have after_first := leading.tail <|
    doubleQueue_step_two (adjacentBody bodyLeft bodyRight) (bodyRight + halfTail)
  have second_step :=
    singleQueue_step_zero bodyLeft bodyRight (bodyRight + halfTail - 1)
  have second_source : bodyRight + halfTail - 1 + 2 = bodyRight + halfTail + 1 := by
    omega
  rw [second_source] at second_step
  have after_second := after_first.tail second_step
  have count_eq : halfTail - 1 + 1 + 1 = halfTail + 1 := by omega
  have endpoint_left : bodyRight + halfTail - 1 + bodyLeft = 3 * halfTail - 1 := by
    omega
  rw [count_eq, endpoint_left] at after_second
  simpa only [lowerCycleQueue] using after_second

/-- The upper periodic queue returns after exactly `halfTail + 1` tag steps. -/
theorem upperCycleQueue_reachesIn (bodyLeft bodyRight halfTail : Nat)
    (body_sum : bodyLeft + bodyRight = 2 * halfTail) :
    TagReachesIn 3 (tagOutput (adjacentBody bodyLeft bodyRight)) (halfTail + 1)
      (upperCycleQueue halfTail bodyRight) (upperCycleQueue halfTail bodyRight) := by
  have leading := doubleQueue_leading_reachesIn (adjacentBody bodyLeft bodyRight)
    halfTail 0 (bodyRight + 1)
  have leading_source : 0 + 3 * halfTail = 3 * halfTail := by omega
  have leading_target : bodyRight + 1 + halfTail = bodyRight + halfTail + 1 := by omega
  rw [leading_source, leading_target] at leading
  have after := leading.tail <|
    doubleQueue_step_zero bodyLeft bodyRight (bodyRight + halfTail)
  have endpoint_left : bodyRight + halfTail + bodyLeft = 3 * halfTail := by omega
  rw [endpoint_left] at after
  simpa only [upperCycleQueue] using after

/-- The lower periodic queue never halts. -/
theorem lowerCycleQueue_not_halts (bodyLeft bodyRight halfTail : Nat)
    (halfTail_pos : 0 < halfTail) (body_sum : bodyLeft + bodyRight = 2 * halfTail) :
    ¬TagHaltsFrom 3 (tagOutput (adjacentBody bodyLeft bodyRight))
      (lowerCycleQueue halfTail bodyRight) := by
  let cycle := lowerCycleQueue halfTail bodyRight
  have execution := lowerCycleQueue_reachesIn bodyLeft bodyRight halfTail
    halfTail_pos body_sum
  have progress : Relation.TransGen (TagStep 3 (tagOutput (adjacentBody bodyLeft bodyRight)))
      cycle cycle := execution.toTransGen (by omega)
  apply Undecidability.not_tagHaltsFrom_of_transGen_progress (· = cycle)
  · rintro queue rfl
    exact ⟨cycle, rfl, progress⟩
  · rfl

/-- The upper periodic queue never halts. -/
theorem upperCycleQueue_not_halts (bodyLeft bodyRight halfTail : Nat)
    (body_sum : bodyLeft + bodyRight = 2 * halfTail) :
    ¬TagHaltsFrom 3 (tagOutput (adjacentBody bodyLeft bodyRight))
      (upperCycleQueue halfTail bodyRight) := by
  let cycle := upperCycleQueue halfTail bodyRight
  have execution := upperCycleQueue_reachesIn bodyLeft bodyRight halfTail body_sum
  have progress : Relation.TransGen (TagStep 3 (tagOutput (adjacentBody bodyLeft bodyRight)))
      cycle cycle := execution.toTransGen (by omega)
  apply Undecidability.not_tagHaltsFrom_of_transGen_progress (· = cycle)
  · rintro queue rfl
    exact ⟨cycle, rfl, progress⟩
  · rfl

end WidthThreeAdjacentBody
end MatrixMortality
