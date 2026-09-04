import MatrixMortality.BranchingHistory
import MatrixMortality.Undecidability.TagExecution

/-!
# Separated two-c nonhalting orbits

For the width-three restricted tag system with coupled body and input, the diagonal separated
family

`qₙ = bb c bⁿ c bⁿ`

has an explicit nonhalting orbit whenever `n` is positive and not congruent to two modulo three.
The coupled initial queue first reaches `Cₙ = c b^(2n+2)`. One `c`-headed step expands this to
`Dₙ = b^(2n+2) c bⁿ c b^(n+1)`; an exact sequence of `b`-headed strokes returns to `Cₙ`.
-/

namespace MatrixMortality

namespace SeparatedTwoCOrbit

open BranchingHistory PeriodicHistory

/-- A unary run of `b` letters. -/
def bRun (length : Nat) : List TagLetter := List.replicate length .b

@[simp] private theorem bRun_append (left right : Nat) :
    bRun left ++ bRun right = bRun (left + right) := by
  exact (List.replicate_add left right TagLetter.b).symm

@[simp] private theorem bRun_cons (length : Nat) :
    .b :: bRun length = bRun (length + 1) := by
  rw [show length + 1 = 1 + length by omega, ← bRun_append]
  rfl

private theorem bRun_snoc (length : Nat) :
    bRun length ++ [.b] = bRun (length + 1) := by
  simpa [bRun] using bRun_append length 1

@[simp] private theorem bRun_append_b_cons (length : Nat) (tail : List TagLetter) :
    bRun length ++ .b :: tail = bRun (length + 1) ++ tail := by
  calc
    bRun length ++ .b :: tail = (bRun length ++ [.b]) ++ tail := by
      simp only [List.append_assoc, List.singleton_append]
    _ = bRun (length + 1) ++ tail := by rw [bRun_snoc]

@[simp] private theorem b_cons_bRun_append (length : Nat) (tail : List TagLetter) :
    TagLetter.b :: (bRun length ++ tail) = bRun (length + 1) ++ tail := by
  calc
    TagLetter.b :: (bRun length ++ tail) = (TagLetter.b :: bRun length) ++ tail := rfl
    _ = bRun (length + 1) ++ tail := by rw [bRun_cons]

private theorem replicate_b_append (left right : Nat) :
    List.replicate left TagLetter.b ++ List.replicate right TagLetter.b =
      List.replicate (left + right) TagLetter.b := by
  exact (List.replicate_add left right TagLetter.b).symm

@[simp] private theorem replicate_b_cons (length : Nat) :
    TagLetter.b :: List.replicate length TagLetter.b =
      List.replicate (length + 1) TagLetter.b := by
  simpa [bRun] using bRun_cons length

@[simp] private theorem replicate_b_append_b_cons
    (length : Nat) (tail : List TagLetter) :
    List.replicate length TagLetter.b ++ TagLetter.b :: tail =
      List.replicate (length + 1) TagLetter.b ++ tail := by
  simpa [bRun] using bRun_append_b_cons length tail

@[simp] private theorem b_cons_replicate_b_append
    (length : Nat) (tail : List TagLetter) :
    TagLetter.b :: (List.replicate length TagLetter.b ++ tail) =
      List.replicate (length + 1) TagLetter.b ++ tail := by
  simpa [bRun] using b_cons_bRun_append length tail

/-- The separated two-`c` body `bb c bⁿ c bⁿ`. -/
def separatedBody (n : Nat) : List TagLetter :=
  [.b, .b, .c] ++ bRun n ++ [.c] ++ bRun n

/-- The initial queue coupled to `separatedBody`. -/
def coupledInitial (n : Nat) : List TagLetter :=
  (separatedBody n).drop 2 ++ [.b]

/-- The short phase of the periodic orbit. -/
def cycleQueue (n : Nat) : List TagLetter :=
  [.c] ++ bRun (2 * n + 2)

/-- The expanded phase reached from `cycleQueue` by firing its leading `c`. -/
def expandedQueue (n : Nat) : List TagLetter :=
  bRun (2 * n + 2) ++ [.c] ++ bRun n ++ [.c] ++ bRun (n + 1)

/-- The `bbc` crossing stroke. -/
def strokeBBC : Stroke TagLetter 3 := stroke₃ .b .b .c

private def zeroEntryBridge (k : Nat) : List TagLetter :=
  bRun (3 * k + 1) ++ [.c] ++ bRun (3 * k + 6) ++ [.c] ++
    bRun (3 * k + 3) ++ [.c] ++ bRun (3 * k + 4)

private def oneEntryBridge (k : Nat) : List TagLetter :=
  bRun (3 * k + 2) ++ [.c] ++ bRun (3 * k + 7) ++ [.c] ++
    bRun (3 * k + 4) ++ [.c] ++ bRun (3 * k + 5)

private def zeroEntryHistory (k : Nat) : List (Stroke TagLetter 3) :=
  List.replicate k strokeBBB ++ [strokeBCB] ++
    List.replicate (k + 1) strokeBBB ++ [strokeBBC] ++
      List.replicate (k + 1) strokeBBB

private def oneEntryHistory (k : Nat) : List (Stroke TagLetter 3) :=
  List.replicate k strokeBBB ++ [strokeBBC] ++
    List.replicate (k + 2) strokeBBB ++ [strokeBCB] ++
      List.replicate (k + 1) strokeBBB

private def zeroReturnHistory (k : Nat) : List (Stroke TagLetter 3) :=
  List.replicate (2 * k + 2) strokeBBB ++ [strokeBBC] ++
    List.replicate (k + 1) strokeBBB

private def oneReturnHistory (k : Nat) : List (Stroke TagLetter 3) :=
  List.replicate (2 * k + 1) strokeBBB ++ [strokeBCB] ++
    List.replicate k strokeBBB

@[simp] private theorem consumed_append (left right : List (Stroke TagLetter 3)) :
    consumed (left ++ right) = consumed left ++ consumed right := by
  simp [consumed]

private theorem produced_append (body : List TagLetter)
    (left right : List (Stroke TagLetter 3)) :
    produced (tagOutput body) (left ++ right) =
      produced (tagOutput body) left ++ produced (tagOutput body) right := by
  simp [produced]


@[simp] private theorem produced_replicate_strokeBBB (body : List TagLetter) (count : Nat) :
    produced (tagOutput body) (List.replicate count strokeBBB) = bRun count := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ, produced_cons, induction]
      simp [strokeBBB, stroke₃, tagOutput, nearyBody]

@[simp] private theorem zeroEntryHistory_length (k : Nat) :
    (zeroEntryHistory k).length = 3 * k + 4 := by
  simp [zeroEntryHistory]
  omega

private theorem zeroEntryHistory_consumed (k : Nat) :
    consumed (zeroEntryHistory k) =
      bRun (3 * k + 1) ++ [.c] ++ bRun (3 * k + 6) ++ [.c] ++ bRun (3 * k + 3) := by
  simp [zeroEntryHistory, strokeBCB, strokeBBC, stroke₃, Stroke.letters,
    List.append_assoc]
  congr 2

private theorem zeroEntryHistory_produced (body : List TagLetter) (k : Nat) :
    produced (tagOutput body) (zeroEntryHistory k) = bRun (3 * k + 4) := by
  simp [zeroEntryHistory, produced_append, strokeBCB, strokeBBC, stroke₃, tagOutput,
    nearyBody, List.append_assoc]
  congr 1
  omega

@[simp] private theorem oneEntryHistory_length (k : Nat) :
    (oneEntryHistory k).length = 3 * k + 5 := by
  simp [oneEntryHistory]
  omega

private theorem oneEntryHistory_consumed (k : Nat) :
    consumed (oneEntryHistory k) =
      bRun (3 * k + 2) ++ [.c] ++ bRun (3 * k + 7) ++ [.c] ++ bRun (3 * k + 4) := by
  simp [oneEntryHistory, strokeBCB, strokeBBC, stroke₃, Stroke.letters,
    List.append_assoc]
  congr 2

private theorem oneEntryHistory_produced (body : List TagLetter) (k : Nat) :
    produced (tagOutput body) (oneEntryHistory k) = bRun (3 * k + 5) := by
  simp [oneEntryHistory, produced_append, strokeBCB, strokeBBC, stroke₃, tagOutput,
    nearyBody, List.append_assoc]
  congr 1
  omega

@[simp] private theorem zeroReturnHistory_length (k : Nat) :
    (zeroReturnHistory k).length = 3 * k + 4 := by
  simp [zeroReturnHistory]
  omega

private theorem zeroReturnHistory_consumed (k : Nat) :
    consumed (zeroReturnHistory k) =
      bRun (6 * k + 8) ++ [.c] ++ bRun (3 * k + 3) := by
  simp [zeroReturnHistory, strokeBBC, stroke₃, Stroke.letters, List.append_assoc]
  congr 2
  omega

private theorem zeroReturnHistory_produced (body : List TagLetter) (k : Nat) :
    produced (tagOutput body) (zeroReturnHistory k) = bRun (3 * k + 4) := by
  simp [zeroReturnHistory, produced_append, strokeBBC, stroke₃, tagOutput, nearyBody,
    List.append_assoc]
  congr 1
  omega

@[simp] private theorem oneReturnHistory_length (k : Nat) :
    (oneReturnHistory k).length = 3 * k + 2 := by
  simp [oneReturnHistory]
  omega

private theorem oneReturnHistory_consumed (k : Nat) :
    consumed (oneReturnHistory k) = bRun (6 * k + 4) ++ [.c] ++ bRun (3 * k + 1) := by
  simp [oneReturnHistory, strokeBCB, stroke₃, Stroke.letters, List.append_assoc]
  congr 2
  omega

private theorem oneReturnHistory_produced (body : List TagLetter) (k : Nat) :
    produced (tagOutput body) (oneReturnHistory k) = bRun (3 * k + 2) := by
  simp [oneReturnHistory, produced_append, strokeBCB, stroke₃, tagOutput, nearyBody,
    List.append_assoc]
  congr 1
  omega

@[simp] theorem coupledInitial_eq (n : Nat) :
    coupledInitial n = [.c] ++ bRun n ++ [.c] ++ bRun (n + 1) := by
  simp [coupledInitial, separatedBody]

theorem cycleQueue_step (n : Nat) :
    TagStep 3 (tagOutput (separatedBody n)) (cycleQueue n) (expandedQueue n) := by
  refine ⟨strokeCBB, bRun (2 * n), ?_, ?_⟩
  · simp [cycleQueue, strokeCBB, stroke₃, Stroke.letters]
  · simp [expandedQueue, separatedBody, strokeCBB, stroke₃, tagOutput, nearyBody,
      List.append_assoc]

private theorem zeroEntry_step (k : Nat) :
    TagStep 3 (tagOutput (separatedBody (3 * (k + 1))))
      (coupledInitial (3 * (k + 1))) (zeroEntryBridge k) := by
  refine ⟨strokeCBB, bRun (3 * k + 1) ++ [.c] ++ bRun (3 * k + 4), ?_, ?_⟩
  · simp [coupledInitial_eq, strokeCBB, stroke₃, Stroke.letters, List.append_assoc]
    congr 2
  · simp [zeroEntryBridge, separatedBody, strokeCBB, stroke₃, tagOutput, nearyBody,
      List.append_assoc]
    congr 2

private theorem oneEntry_step (k : Nat) :
    TagStep 3 (tagOutput (separatedBody (3 * (k + 1) + 1)))
      (coupledInitial (3 * (k + 1) + 1)) (oneEntryBridge k) := by
  refine ⟨strokeCBB, bRun (3 * k + 2) ++ [.c] ++ bRun (3 * k + 5), ?_, ?_⟩
  · simp [coupledInitial_eq, strokeCBB, stroke₃, Stroke.letters, List.append_assoc]
    congr 2
  · simp [oneEntryBridge, separatedBody, strokeCBB, stroke₃, tagOutput, nearyBody,
      List.append_assoc]
    congr 2

private theorem zeroEntryHistory_reaches (k : Nat) :
    TagReachesIn 3 (tagOutput (separatedBody (3 * (k + 1)))) (3 * k + 4)
      (zeroEntryBridge k) (cycleQueue (3 * (k + 1))) := by
  have reach := Undecidability.tagReachesIn_history
    (tagOutput (separatedBody (3 * (k + 1)))) (zeroEntryHistory k)
    ([.c] ++ bRun (3 * k + 4))
  rw [zeroEntryHistory_length, zeroEntryHistory_consumed,
    zeroEntryHistory_produced] at reach
  have target_eq :
      [.c] ++ bRun (3 * k + 4) ++ bRun (3 * k + 4) =
        cycleQueue (3 * (k + 1)) := by
    simp [cycleQueue]
    congr 1
    omega
  rw [target_eq] at reach
  simpa [zeroEntryBridge, cycleQueue, List.append_assoc] using reach

private theorem oneEntryHistory_reaches (k : Nat) :
    TagReachesIn 3 (tagOutput (separatedBody (3 * (k + 1) + 1))) (3 * k + 5)
      (oneEntryBridge k) (cycleQueue (3 * (k + 1) + 1)) := by
  have reach := Undecidability.tagReachesIn_history
    (tagOutput (separatedBody (3 * (k + 1) + 1))) (oneEntryHistory k)
    ([.c] ++ bRun (3 * k + 5))
  rw [oneEntryHistory_length, oneEntryHistory_consumed,
    oneEntryHistory_produced] at reach
  have target_eq :
      [.c] ++ bRun (3 * k + 5) ++ bRun (3 * k + 5) =
        cycleQueue (3 * (k + 1) + 1) := by
    simp [cycleQueue]
    congr 1
    omega
  rw [target_eq] at reach
  simpa [oneEntryBridge, cycleQueue, List.append_assoc] using reach

/-- The positive zero-residue coupled input reaches its explicit periodic orbit. -/
theorem zeroResidue_initial_reaches_cycle (k : Nat) :
    TagReaches 3 (tagOutput (separatedBody (3 * (k + 1))))
      (coupledInitial (3 * (k + 1))) (cycleQueue (3 * (k + 1))) := by
  exact (Relation.ReflTransGen.single (zeroEntry_step k)).trans
    (zeroEntryHistory_reaches k).toReaches

private theorem oneInitial_step_zero :
    TagStep 3 (tagOutput (separatedBody 1)) (coupledInitial 1) (expandedQueue 1) := by
  refine ⟨strokeCBC, List.replicate 2 .b, ?_, ?_⟩
  · decide
  · decide

/-- Every one-residue coupled input reaches its explicit periodic orbit. -/
theorem oneResidue_initial_reaches_cycle (k : Nat) :
    TagReaches 3 (tagOutput (separatedBody (3 * k + 1)))
      (coupledInitial (3 * k + 1)) (cycleQueue (3 * k + 1)) := by
  cases k with
  | zero =>
      have return_reach :
          TagReaches 3 (tagOutput (separatedBody 1)) (expandedQueue 1) (cycleQueue 1) := by
        have exact_reach := Undecidability.tagReachesIn_history
          (tagOutput (separatedBody 1)) (oneReturnHistory 0) ([.c] ++ bRun 2)
        rw [oneReturnHistory_length, oneReturnHistory_consumed,
          oneReturnHistory_produced] at exact_reach
        have return_exact :
            TagReachesIn 3 (tagOutput (separatedBody 1)) 2
              (expandedQueue 1) (cycleQueue 1) := by
          simpa [expandedQueue, cycleQueue, List.append_assoc] using exact_reach
        exact return_exact.toReaches
      exact (Relation.ReflTransGen.single oneInitial_step_zero).trans
        return_reach
  | succ k =>
      have entry :
          TagStep 3 (tagOutput (separatedBody (3 * (k + 1) + 1)))
            (coupledInitial (3 * (k + 1) + 1)) (oneEntryBridge k) :=
        oneEntry_step k
      exact (Relation.ReflTransGen.single entry).trans
        (oneEntryHistory_reaches k).toReaches

/-- The expanded zero-residue queue returns in exactly `n+1` steps. -/
theorem zeroResidue_expanded_reaches_cycle (k : Nat) :
    TagReachesIn 3 (tagOutput (separatedBody (3 * (k + 1)))) (3 * k + 4)
      (expandedQueue (3 * (k + 1))) (cycleQueue (3 * (k + 1))) := by
  have reach := Undecidability.tagReachesIn_history
    (tagOutput (separatedBody (3 * (k + 1)))) (zeroReturnHistory k)
    ([.c] ++ bRun (3 * k + 4))
  rw [zeroReturnHistory_length, zeroReturnHistory_consumed,
    zeroReturnHistory_produced] at reach
  have source_eq :
      bRun (6 * k + 8) ++ [.c] ++ bRun (3 * k + 3) ++
          ([.c] ++ bRun (3 * k + 4)) =
        expandedQueue (3 * (k + 1)) := by
    simp [expandedQueue, List.append_assoc]
    congr 2
    omega
  have target_eq :
      [.c] ++ bRun (3 * k + 4) ++ bRun (3 * k + 4) =
        cycleQueue (3 * (k + 1)) := by
    simp [cycleQueue]
    congr 1
    omega
  rw [source_eq, target_eq] at reach
  exact reach

/-- The expanded one-residue queue returns in exactly `n+1` steps. -/
theorem oneResidue_expanded_reaches_cycle (k : Nat) :
    TagReachesIn 3 (tagOutput (separatedBody (3 * k + 1))) (3 * k + 2)
      (expandedQueue (3 * k + 1)) (cycleQueue (3 * k + 1)) := by
  have reach := Undecidability.tagReachesIn_history
    (tagOutput (separatedBody (3 * k + 1))) (oneReturnHistory k)
    ([.c] ++ bRun (3 * k + 2))
  rw [oneReturnHistory_length, oneReturnHistory_consumed,
    oneReturnHistory_produced] at reach
  have source_eq :
      bRun (6 * k + 4) ++ [.c] ++ bRun (3 * k + 1) ++
          ([.c] ++ bRun (3 * k + 2)) =
        expandedQueue (3 * k + 1) := by
    have expanded_length : 6 * k + 4 = 2 * (3 * k + 1) + 2 := by omega
    have final_length : 3 * k + 2 = 3 * k + 1 + 1 := by omega
    simp [expandedQueue, List.append_assoc, expanded_length, final_length]
  have target_eq :
      [.c] ++ bRun (3 * k + 2) ++ bRun (3 * k + 2) =
        cycleQueue (3 * k + 1) := by
    simp [cycleQueue]
    congr 1
    omega
  rw [source_eq, target_eq] at reach
  exact reach

private theorem not_halts_of_cycle {body queue : List TagLetter} {steps : Nat}
    (steps_pos : 0 < steps)
    (cycle : TagReachesIn 3 (tagOutput body) steps queue queue) :
    ¬TagHaltsFrom 3 (tagOutput body) queue := by
  apply Undecidability.not_tagHaltsFrom_of_transGen_progress (fun candidate => candidate = queue)
  · intro candidate candidate_eq
    subst candidate
    exact ⟨queue, rfl, cycle.toTransGen steps_pos⟩
  · rfl

/-- For `n=3(k+1)`, `Cₙ → Dₙ → Cₙ` is an exact cycle of length `n+2`. -/
theorem zeroResidue_cycle (k : Nat) :
    TagReachesIn 3 (tagOutput (separatedBody (3 * (k + 1)))) (3 * (k + 1) + 2)
      (cycleQueue (3 * (k + 1))) (cycleQueue (3 * (k + 1))) := by
  exact Relation.ReachesIn.head (cycleQueue_step (3 * (k + 1)))
    (zeroResidue_expanded_reaches_cycle k)

/-- For `n=3k+1`, `Cₙ → Dₙ → Cₙ` is an exact cycle of length `n+2`. -/
theorem oneResidue_cycle (k : Nat) :
    TagReachesIn 3 (tagOutput (separatedBody (3 * k + 1))) (3 * k + 1 + 2)
      (cycleQueue (3 * k + 1)) (cycleQueue (3 * k + 1)) := by
  exact Relation.ReachesIn.head (cycleQueue_step (3 * k + 1))
    (oneResidue_expanded_reaches_cycle k)

/-- Every positive zero-residue member of the separated diagonal family is nonhalting. -/
theorem zeroResidue_not_tagHaltsFrom (k : Nat) :
    ¬TagHaltsFrom 3 (tagOutput (separatedBody (3 * (k + 1))))
      (coupledInitial (3 * (k + 1))) := by
  intro halts
  have cycle_halts := Undecidability.tagHaltsFrom_after_reaches
    (zeroResidue_initial_reaches_cycle k) halts
  exact not_halts_of_cycle (steps := 3 * (k + 1) + 2) (by omega)
    (zeroResidue_cycle k) cycle_halts

/-- Every one-residue member of the separated diagonal family is nonhalting. -/
theorem oneResidue_not_tagHaltsFrom (k : Nat) :
    ¬TagHaltsFrom 3 (tagOutput (separatedBody (3 * k + 1)))
      (coupledInitial (3 * k + 1)) := by
  intro halts
  have cycle_halts := Undecidability.tagHaltsFrom_after_reaches
    (oneResidue_initial_reaches_cycle k) halts
  exact not_halts_of_cycle (steps := 3 * k + 1 + 2) (by omega)
    (oneResidue_cycle k) cycle_halts

/-- The separated diagonal body is admissible for the width-three scheduled compiler. -/
theorem separatedBody_length (n : Nat) : (separatedBody n).length = 2 * n + 4 := by
  simp [separatedBody, bRun]
  omega

/-- Every separated diagonal body satisfies the scheduled compiler's length envelope. -/
theorem separatedBody_admissible (n : Nat) :
    2 ≤ (separatedBody n).length ∧ 2 ∣ (separatedBody n).length := by
  rw [separatedBody_length]
  exact ⟨by omega, ⟨n + 2, by omega⟩⟩

/-- Every positive separated diagonal body outside residue two has a nonhalting coupled input. -/
theorem separated_not_tagHaltsFrom (n : Nat) (n_pos : 0 < n) (residue_ne : n % 3 ≠ 2) :
    ¬TagHaltsFrom 3 (tagOutput (separatedBody n))
      ((separatedBody n).drop 2 ++ [.b]) := by
  change ¬TagHaltsFrom 3 (tagOutput (separatedBody n)) (coupledInitial n)
  have residue_lt : n % 3 < 3 := Nat.mod_lt n (by omega)
  have residue_cases : n % 3 = 0 ∨ n % 3 = 1 := by omega
  rcases residue_cases with residue_zero | residue_one
  · obtain ⟨multiple, n_eq⟩ := (Nat.dvd_iff_mod_eq_zero.mpr residue_zero : 3 ∣ n)
    have multiple_pos : 0 < multiple := by
      rw [n_eq] at n_pos
      omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt multiple_pos)
    rw [n_eq]
    exact zeroResidue_not_tagHaltsFrom k
  · have decomposition := Nat.mod_add_div n 3
    have n_eq : n = 3 * (n / 3) + 1 := by omega
    rw [n_eq]
    exact oneResidue_not_tagHaltsFrom (n / 3)

end SeparatedTwoCOrbit

end MatrixMortality
