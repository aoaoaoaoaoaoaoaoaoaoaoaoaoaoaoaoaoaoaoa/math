import MatrixMortality.Undecidability.TagExecution
import MatrixMortality.WidthThreeSparseBody

/-!
# Adjacent two-`c` width-three bodies

For `p+s=2k`, the body `b^p c c b^s` has two explicit periodic queues. When `k>0`, its
coupled initial queue either halts or enters the lower cycle. The decision follows from the
canonical macro map on `b^i c c b^(s+1)`: residue one modulo three drains to a unary queue,
while residues zero and two send `i` to `2k+⌊i/3⌋`.
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

private theorem doubleQueue_step_one (body : List TagLetter) (right : Nat) :
    TagStep 3 (tagOutput body) (doubleQueue 1 right) (bRun (right + 1)) := by
  refine ⟨⟨.b, [.c, .c], rfl⟩, bRun right, ?_, ?_⟩
  · simp [doubleQueue, bRun, Stroke.letters]
  · change bRun (right + 1) = bRun right ++ [.b]
    exact bRun_snoc right

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

private theorem doubleQueue_macro_zero (bodyLeft bodyRight left : Nat)
    (mod_zero : left % 3 = 0) :
    TagReaches 3 (tagOutput (adjacentBody bodyLeft bodyRight))
      (doubleQueue left (bodyRight + 1))
      (doubleQueue (bodyLeft + bodyRight + left / 3) (bodyRight + 1)) := by
  have division := Nat.mod_add_div left 3
  have left_eq : 0 + 3 * (left / 3) = left := by omega
  have leading := doubleQueue_leading_reachesIn (adjacentBody bodyLeft bodyRight)
    (left / 3) 0 (bodyRight + 1)
  have middle_eq : bodyRight + 1 + left / 3 = bodyRight + left / 3 + 1 := by omega
  rw [left_eq, middle_eq] at leading
  have after := leading.tail <|
    doubleQueue_step_zero bodyLeft bodyRight (bodyRight + left / 3)
  have endpoint_eq : bodyRight + left / 3 + bodyLeft =
      bodyLeft + bodyRight + left / 3 := by omega
  rw [endpoint_eq] at after
  exact after.toReaches

private theorem doubleQueue_macro_two (bodyLeft bodyRight left : Nat)
    (mod_two : left % 3 = 2) :
    TagReaches 3 (tagOutput (adjacentBody bodyLeft bodyRight))
      (doubleQueue left (bodyRight + 1))
      (doubleQueue (bodyLeft + bodyRight + left / 3) (bodyRight + 1)) := by
  have division := Nat.mod_add_div left 3
  have left_eq : 2 + 3 * (left / 3) = left := by omega
  have leading := doubleQueue_leading_reachesIn (adjacentBody bodyLeft bodyRight)
    (left / 3) 2 (bodyRight + 1)
  rw [left_eq] at leading
  have after_first := leading.tail <|
    doubleQueue_step_two (adjacentBody bodyLeft bodyRight)
      (bodyRight + 1 + left / 3)
  have second := singleQueue_step_zero bodyLeft bodyRight (bodyRight + left / 3)
  have second_source : bodyRight + left / 3 + 2 =
      bodyRight + 1 + left / 3 + 1 := by omega
  rw [second_source] at second
  have after_second := after_first.tail second
  have endpoint_eq : bodyRight + left / 3 + bodyLeft =
      bodyLeft + bodyRight + left / 3 := by omega
  rw [endpoint_eq] at after_second
  exact after_second.toReaches

private theorem doubleQueue_halts_of_mod_one (bodyLeft bodyRight left : Nat)
    (mod_one : left % 3 = 1) :
    TagHaltsFrom 3 (tagOutput (adjacentBody bodyLeft bodyRight))
      (doubleQueue left (bodyRight + 1)) := by
  have division := Nat.mod_add_div left 3
  have left_eq : 1 + 3 * (left / 3) = left := by omega
  have leading := doubleQueue_leading_reachesIn (adjacentBody bodyLeft bodyRight)
    (left / 3) 1 (bodyRight + 1)
  rw [left_eq] at leading
  have after := leading.tail <|
    doubleQueue_step_one (adjacentBody bodyLeft bodyRight)
      (bodyRight + 1 + left / 3)
  have pure_halts :
      TagHaltsFrom 3 (tagOutput (adjacentBody bodyLeft bodyRight))
        (bRun (bodyRight + 1 + left / 3 + 1)) :=
    Undecidability.tagHaltsFrom_replicate_fixed 3 (by omega)
      (tagOutput (adjacentBody bodyLeft bodyRight)) .b rfl _
  exact TagHaltsFrom.before pure_halts after.toReaches

/-- The lower adjacent-`c` periodic queue. -/
def lowerCycleQueue (halfTail right : Nat) : List TagLetter :=
  doubleQueue (3 * halfTail - 1) (right + 1)

/-- The upper adjacent-`c` periodic queue. -/
def upperCycleQueue (halfTail right : Nat) : List TagLetter :=
  doubleQueue (3 * halfTail) (right + 1)

private inductive OrbitClassification (halts reaches : Prop) : Type
  | halts (proof : halts)
  | reaches (proof : reaches)

private def classifyDoubleQueueBelow (bodyLeft bodyRight halfTail left : Nat)
    (halfTail_pos : 0 < halfTail) (body_sum : bodyLeft + bodyRight = 2 * halfTail)
    (below : left ≤ 3 * halfTail - 1) :
    OrbitClassification
      (TagHaltsFrom 3 (tagOutput (adjacentBody bodyLeft bodyRight))
        (doubleQueue left (bodyRight + 1)))
      (TagReaches 3 (tagOutput (adjacentBody bodyLeft bodyRight))
        (doubleQueue left (bodyRight + 1)) (lowerCycleQueue halfTail bodyRight)) := by
  by_cases at_cycle : left = 3 * halfTail - 1
  · subst left
    exact .reaches Relation.ReflTransGen.refl
  · have strict_below : left < 3 * halfTail - 1 := by omega
    by_cases mod_one : left % 3 = 1
    · exact .halts (doubleQueue_halts_of_mod_one bodyLeft bodyRight left mod_one)
    · have mod_lt : left % 3 < 3 := Nat.mod_lt left (by omega)
      have mod_cases : left % 3 = 0 ∨ left % 3 = 2 := by omega
      let nextLeft := 2 * halfTail + left / 3
      have next_eq : bodyLeft + bodyRight + left / 3 = nextLeft := by
        dsimp only [nextLeft]
        omega
      have macroReach :
          TagReaches 3 (tagOutput (adjacentBody bodyLeft bodyRight))
            (doubleQueue left (bodyRight + 1))
            (doubleQueue nextLeft (bodyRight + 1)) := by
        rw [← next_eq]
        rcases mod_cases with mod_zero | mod_two
        · exact doubleQueue_macro_zero bodyLeft bodyRight left mod_zero
        · exact doubleQueue_macro_two bodyLeft bodyRight left mod_two
      have division := Nat.mod_add_div left 3
      have next_greater : left < nextLeft := by
        dsimp only [nextLeft]
        omega
      have next_below : nextLeft ≤ 3 * halfTail - 1 := by
        dsimp only [nextLeft]
        omega
      have classified := classifyDoubleQueueBelow bodyLeft bodyRight halfTail nextLeft
        halfTail_pos body_sum next_below
      cases classified with
      | halts halts => exact .halts (TagHaltsFrom.before halts macroReach)
      | reaches reaches =>
          exact .reaches (Relation.ReflTransGen.trans macroReach reaches)
termination_by 3 * halfTail - 1 - left
decreasing_by omega

private def classifyCoupledAdjacentBody (bodyLeft bodyRight halfTail : Nat)
    (halfTail_pos : 0 < halfTail) (body_sum : bodyLeft + bodyRight = 2 * halfTail) :
    OrbitClassification
      (TagHaltsFrom 3 (tagOutput (adjacentBody bodyLeft bodyRight))
        ((adjacentBody bodyLeft bodyRight).drop 2 ++ [.b]))
      (TagReaches 3 (tagOutput (adjacentBody bodyLeft bodyRight))
        ((adjacentBody bodyLeft bodyRight).drop 2 ++ [.b])
        (lowerCycleQueue halfTail bodyRight)) := by
  by_cases bodyLeft_small : bodyLeft < 2
  · interval_cases bodyLeft
    · have initial_eq :
          (adjacentBody 0 bodyRight).drop 2 ++ [.b] = bRun (bodyRight + 1) := by
        change ([TagLetter.c, TagLetter.c] ++ bRun bodyRight).drop 2 ++ [.b] =
          bRun (bodyRight + 1)
        rw [bRun_snoc]
        rfl
      apply OrbitClassification.halts
      rw [initial_eq]
      exact Undecidability.tagHaltsFrom_replicate_fixed 3 (by omega)
        (tagOutput (adjacentBody 0 bodyRight)) .b rfl _
    · have bodyRight_pos : 0 < bodyRight := by omega
      have initial_eq :
          (adjacentBody 1 bodyRight).drop 2 ++ [.b] =
            singleQueue 0 (bodyRight + 1) := by
        change ([TagLetter.b, TagLetter.c, TagLetter.c] ++ bRun bodyRight).drop 2 ++ [.b] =
          [.c] ++ bRun (bodyRight + 1)
        rw [bRun_snoc]
        rfl
      have first := singleQueue_step_zero 1 bodyRight (bodyRight - 1)
      have source_eq : bodyRight - 1 + 2 = bodyRight + 1 := by omega
      have endpoint_eq : bodyRight - 1 + 1 = bodyRight := by omega
      rw [source_eq, endpoint_eq] at first
      have below : bodyRight ≤ 3 * halfTail - 1 := by omega
      have classified := classifyDoubleQueueBelow 1 bodyRight halfTail bodyRight
        halfTail_pos body_sum below
      cases classified with
      | halts halts =>
          apply OrbitClassification.halts
          rw [initial_eq]
          exact .step first halts
      | reaches reaches =>
          apply OrbitClassification.reaches
          rw [initial_eq]
          exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single first) reaches
  · have two_le : 2 ≤ bodyLeft := Nat.le_of_not_gt bodyLeft_small
    let initialLeft := bodyLeft - 2
    have bodyLeft_eq : bodyLeft = initialLeft + 2 := by
      dsimp only [initialLeft]
      omega
    rw [bodyLeft_eq] at body_sum ⊢
    have initial_eq :
        (adjacentBody (initialLeft + 2) bodyRight).drop 2 ++ [.b] =
          doubleQueue initialLeft (bodyRight + 1) := by
      change (bRun (initialLeft + 2) ++ [TagLetter.c, TagLetter.c] ++
          bRun bodyRight).drop 2 ++ [.b] =
        bRun initialLeft ++ [TagLetter.c, TagLetter.c] ++ bRun (bodyRight + 1)
      rw [show initialLeft + 2 = 2 + initialLeft by omega, bRun_add,
        bRun_snoc bodyRight]
      simp [List.append_assoc]
    have below : initialLeft ≤ 3 * halfTail - 1 := by omega
    rw [initial_eq]
    exact classifyDoubleQueueBelow (initialLeft + 2) bodyRight halfTail initialLeft
      halfTail_pos body_sum below

/-- The coupled initial queue of every nontrivial even adjacent-two-`c` body either halts or
enters the lower periodic orbit. -/
theorem adjacentBody_coupled_normal_form (bodyLeft bodyRight halfTail : Nat)
    (halfTail_pos : 0 < halfTail) (body_sum : bodyLeft + bodyRight = 2 * halfTail) :
    TagHaltsFrom 3 (tagOutput (adjacentBody bodyLeft bodyRight))
        ((adjacentBody bodyLeft bodyRight).drop 2 ++ [.b]) ∨
      TagReaches 3 (tagOutput (adjacentBody bodyLeft bodyRight))
        ((adjacentBody bodyLeft bodyRight).drop 2 ++ [.b])
        (lowerCycleQueue halfTail bodyRight) := by
  cases classifyCoupledAdjacentBody bodyLeft bodyRight halfTail halfTail_pos body_sum with
  | halts halts => exact Or.inl halts
  | reaches reaches => exact Or.inr reaches

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

/-- Halting of the coupled initial queue is decidable for every nontrivial even
adjacent-two-`c` body. -/
def adjacentBodyCoupledHaltsDecidable (bodyLeft bodyRight halfTail : Nat)
    (halfTail_pos : 0 < halfTail) (body_sum : bodyLeft + bodyRight = 2 * halfTail) :
    Decidable <|
      TagHaltsFrom 3 (tagOutput (adjacentBody bodyLeft bodyRight))
        ((adjacentBody bodyLeft bodyRight).drop 2 ++ [.b]) :=
  match classifyCoupledAdjacentBody bodyLeft bodyRight halfTail halfTail_pos body_sum with
  | .halts halts => isTrue halts
  | .reaches reaches => isFalse fun halts =>
      lowerCycleQueue_not_halts bodyLeft bodyRight halfTail halfTail_pos body_sum <|
        Undecidability.tagHaltsFrom_after_reaches reaches halts

end WidthThreeAdjacentBody
end MatrixMortality
