import MatrixMortality.Undecidability.CockeMinsky

/-!
# Halt-avoiding Cocke–Minsky executions

The ordinary compiler theorem records only its endpoints.  Neary's downstream cyclic-tag
compiler also needs the stronger fact that no simulated sweep reads the distinguished halt
symbol before the exact terminal queue is reached.  The pair-aligned construction exposes that
fact directly: every read member of every preterminal pair has a non-halt constructor.
-/

namespace MatrixMortality
namespace Undecidability
namespace CockeMinsky

/-- A pair-aligned sweep avoids a target whenever none of its read members is that target. -/
theorem sweep_avoiding {α : Type*} (output : α → List α) (target : α)
    (pairs : List (α × α)) (tail : List α)
    (heads_avoid : ∀ pair ∈ pairs, pair.1 ≠ target) :
    HeadAvoidingTagReaches 2 output target
      (pairWord pairs ++ tail) (tail ++ pairOutput output pairs) := by
  induction pairs generalizing tail with
  | nil =>
      simpa [pairWord, pairOutput] using
        (Relation.ReflTransGen.refl :
          HeadAvoidingTagReaches 2 output target tail tail)
  | cons pair pairs ih =>
      apply Relation.ReflTransGen.head
      · refine ⟨⟨pair.1, [pair.2], rfl⟩, pairWord pairs ++ tail,
          heads_avoid pair (by simp), ?_, rfl⟩
        simp [pairWord, Stroke.letters]
      · simpa [pairWord, pairOutput, List.append_assoc] using
          ih (tail ++ output pair.1) fun later member =>
            heads_avoid later (by simp [member])

/-- A unary sweep avoids a target distinct from both of its read symbols. -/
theorem sweep_run_avoiding {α : Type*} (output : α → List α) (target head digit wake : α)
    (count : Nat) (tail : List α) (head_ne : head ≠ target) (digit_ne : digit ≠ target) :
    HeadAvoidingTagReaches 2 output target
      (cell head wake ++ cells digit wake count ++ tail)
      (tail ++ output head ++ (List.replicate count (output digit)).join) := by
  have heads :
      ∀ pair ∈ (head, wake) :: List.replicate count (digit, wake),
        pair.1 ≠ target := by
    intro pair member
    simp only [List.mem_cons, List.mem_replicate] at member
    rcases member with rfl | ⟨_, rfl⟩
    · exact head_ne
    · exact digit_ne
  simpa [pairWord, pairOutput, cell, cells, List.map_replicate, List.append_assoc] using
    sweep_avoiding output target
      ((head, wake) :: List.replicate count (digit, wake)) tail heads

/-- A target-avoiding unary sweep contains at least its distinguished first transition. -/
theorem sweep_run_avoiding_strict {α : Type*} (output : α → List α)
    (target head digit wake : α) (count : Nat) (tail : List α)
    (head_ne : head ≠ target) (digit_ne : digit ≠ target) :
    Relation.TransGen (HeadAvoidingTagStep 2 output target)
      (cell head wake ++ cells digit wake count ++ tail)
      (tail ++ output head ++ (List.replicate count (output digit)).join) := by
  apply Relation.TransGen.head'
    (b := cells digit wake count ++ tail ++ output head)
  · refine ⟨⟨head, [wake], rfl⟩, cells digit wake count ++ tail, head_ne, ?_, rfl⟩
    simp [cell, Stroke.letters, List.append_assoc]
  · have remaining := sweep_avoiding output target
      (List.replicate count (digit, wake)) (tail ++ output head) (by
        intro pair member
        simp only [List.mem_replicate] at member
        exact member.2 ▸ digit_ne)
    simpa [pairWord, pairOutput, cells, List.map_replicate, List.append_assoc] using remaining

/-- Cocke–Minsky tag execution before the unique halt symbol is read. -/
def HaltAvoidingReaches {state : Type*} (machine : Machine state) :
    List (Symbol state) → List (Symbol state) → Prop :=
  HeadAvoidingTagReaches 2 (production machine) .halt

private theorem sweep_write_avoiding {state : Type*} (machine : Machine state) (q : state)
    (action : Action state) (behind ahead : Nat) (at_q : machine q = some action) :
    HaltAvoidingReaches machine (frame q behind ahead)
      (cell (.boundary q) (.pad q) ++ cells (.boundaryDigit q) (.pad q) ahead ++
        doubledBlock q (written action.write behind)) := by
  have run :=
    sweep_run_avoiding (production machine) (.halt : Symbol state)
      (.anchor q) (.digit q) (.pad q) behind
      (cell (.boundary q) (.pad q) ++ cells (.boundaryDigit q) (.pad q) ahead)
      (by simp) (by simp)
  cases write_eq : action.write <;>
    simpa [HaltAvoidingReaches, frame, doubledBlock, production, at_q, write_eq, written,
      List.append_assoc, join_replicate_double_cell, cells_succ] using run

private theorem sweep_write_avoiding_strict {state : Type*} (machine : Machine state)
    (q : state) (action : Action state) (behind ahead : Nat)
    (at_q : machine q = some action) :
    Relation.TransGen
      (HeadAvoidingTagStep 2 (production machine) (.halt : Symbol state))
      (frame q behind ahead)
      (cell (.boundary q) (.pad q) ++ cells (.boundaryDigit q) (.pad q) ahead ++
        doubledBlock q (written action.write behind)) := by
  have run :=
    sweep_run_avoiding_strict (production machine) (.halt : Symbol state)
      (.anchor q) (.digit q) (.pad q) behind
      (cell (.boundary q) (.pad q) ++ cells (.boundaryDigit q) (.pad q) ahead)
      (by simp) (by simp)
  cases write_eq : action.write <;>
    simpa [frame, doubledBlock, production, at_q, write_eq, written,
      List.append_assoc, join_replicate_double_cell, cells_succ] using run

private theorem sweep_to_halving_avoiding {state : Type*} (machine : Machine state) (q : state)
    (action : Action state) (writtenCount ahead : Nat) (at_q : machine q = some action) :
    HaltAvoidingReaches machine
      (cell (.boundary q) (.pad q) ++ cells (.boundaryDigit q) (.pad q) ahead ++
        doubledBlock q writtenCount)
      (doubledBlock q writtenCount ++ halvingBlock q ahead) := by
  have run :=
    sweep_run_avoiding (production machine) (.halt : Symbol state)
      (.boundary q) (.boundaryDigit q) (.pad q) ahead (doubledBlock q writtenCount)
      (by simp) (by simp)
  simpa [HaltAvoidingReaches, halvingBlock, production, at_q, List.append_assoc] using run

private theorem sweep_to_parity_avoiding {state : Type*} (machine : Machine state) (q : state)
    (writtenCount ahead : Nat) :
    HaltAvoidingReaches machine
      (doubledBlock q writtenCount ++ halvingBlock q ahead)
      (halvingBlock q ahead ++ parityBlock q writtenCount) := by
  have run :=
    sweep_run_avoiding (production machine) (.halt : Symbol state)
      (.doubledAnchor q) (.doubledDigit q) (.pad q) writtenCount (halvingBlock q ahead)
      (by simp) (by simp)
  simpa [HaltAvoidingReaches, doubledBlock, parityBlock, production,
    List.append_assoc] using run

private theorem sweep_odd_front_avoiding {state : Type*} (machine : Machine state) (q : state)
    (writtenCount half : Nat) :
    HaltAvoidingReaches machine
      (halvingBlock q (2 * half + 1) ++ parityBlock q writtenCount)
      (parityBlock q writtenCount ++ branchBlock q half) := by
  let pairs : List (Symbol state × Symbol state) :=
    ((.halvingAnchor q, .halvingDigit q) ::
      List.replicate half (.halvingDigit q, .halvingDigit q))
  have heads : ∀ pair ∈ pairs, pair.1 ≠ (.halt : Symbol state) := by
    intro pair member
    simp [pairs] at member
    rcases member with rfl | ⟨_, rfl⟩ <;> simp
  have run := sweep_avoiding (production machine) (.halt : Symbol state) pairs
    (parityBlock q writtenCount) heads
  simpa [pairs, HaltAvoidingReaches, halvingBlock, branchBlock, pairWord_oddRun,
    pairOutput_oddRun, production, List.append_assoc] using run

private theorem sweep_even_front_avoiding {state : Type*} (machine : Machine state) (q : state)
    (writtenCount half : Nat) :
    HaltAvoidingReaches machine
      (halvingBlock q (2 * half) ++ parityBlock q writtenCount)
      (.parityAnchor false q ::
        cells (.parityDigit true q) (.parityDigit false q) writtenCount ++
          branchBlock q half) := by
  cases half with
  | zero =>
      have run := sweep_avoiding (production machine) (.halt : Symbol state)
        [(.halvingAnchor q, .parityAnchor true q)]
        (.parityAnchor false q ::
          cells (.parityDigit true q) (.parityDigit false q) writtenCount) (by simp)
      simpa [HaltAvoidingReaches, halvingBlock, branchBlock, pairWord, pairOutput,
        production, List.append_assoc] using run
  | succ half =>
      let pairs : List (Symbol state × Symbol state) :=
        ((.halvingAnchor q, .halvingDigit q) ::
          List.replicate half (.halvingDigit q, .halvingDigit q)) ++
            [(.halvingDigit q, .parityAnchor true q)]
      have heads : ∀ pair ∈ pairs, pair.1 ≠ (.halt : Symbol state) := by
        intro pair member
        simp [pairs] at member
        rcases member with rfl | ⟨_, rfl⟩ | rfl <;> simp
      have run := sweep_avoiding (production machine) (.halt : Symbol state) pairs
        (.parityAnchor false q ::
          cells (.parityDigit true q) (.parityDigit false q) writtenCount) heads
      dsimp only [pairs] at run
      rw [pairWord_evenRun, pairOutput_evenRun] at run
      simpa [HaltAvoidingReaches, halvingBlock, branchBlock, production,
        List.append_assoc] using run

private theorem sweep_odd_written_avoiding {state : Type*} (machine : Machine state) (q : state)
    (action : Action state) (writtenCount half : Nat) (at_q : machine q = some action) :
    HaltAvoidingReaches machine
      (parityBlock q writtenCount ++ branchBlock q half)
      (branchBlock q half ++
        pendingFirst (reverses machine action true) (action.next true) writtenCount) := by
  let pairs : List (Symbol state × Symbol state) :=
    (.parityAnchor true q, .parityAnchor false q) ::
      List.replicate writtenCount (.parityDigit true q, .parityDigit false q)
  have heads : ∀ pair ∈ pairs, pair.1 ≠ (.halt : Symbol state) := by
    intro pair member
    simp [pairs] at member
    rcases member with rfl | ⟨_, rfl⟩ <;> simp
  have run := sweep_avoiding (production machine) (.halt : Symbol state) pairs
    (branchBlock q half) heads
  simpa [pairs, HaltAvoidingReaches, parityBlock, pendingFirst, pairWord, pairOutput,
    production, at_q, List.map_replicate, List.append_assoc] using run

private theorem sweep_even_written_avoiding {state : Type*} (machine : Machine state)
    (q : state) (action : Action state) (writtenCount half : Nat)
    (at_q : machine q = some action) :
    HaltAvoidingReaches machine
      (.parityAnchor false q ::
        cells (.parityDigit true q) (.parityDigit false q) writtenCount ++
          branchBlock q half)
      (.branchAnchor false q ::
        cells (.branchDigit true q) (.branchDigit false q) half ++
          .pad (action.next false) ::
            pendingFirst (reverses machine action false) (action.next false) writtenCount) := by
  cases writtenCount with
  | zero =>
      have run := sweep_avoiding (production machine) (.halt : Symbol state)
        [(.parityAnchor false q, .branchAnchor true q)]
        (.branchAnchor false q ::
          cells (.branchDigit true q) (.branchDigit false q) half) (by simp)
      simpa [HaltAvoidingReaches, branchBlock, pendingFirst, pairWord, pairOutput,
        production, at_q, List.append_assoc] using run
  | succ writtenCount =>
      let pairs : List (Symbol state × Symbol state) :=
        ((.parityAnchor false q, .parityDigit true q) ::
          List.replicate writtenCount (.parityDigit false q, .parityDigit true q)) ++
            [(.parityDigit false q, .branchAnchor true q)]
      have heads : ∀ pair ∈ pairs, pair.1 ≠ (.halt : Symbol state) := by
        intro pair member
        simp [pairs] at member
        rcases member with rfl | ⟨_, rfl⟩ | rfl <;> simp
      have run := sweep_avoiding (production machine) (.halt : Symbol state) pairs
        (.branchAnchor false q ::
          cells (.branchDigit true q) (.branchDigit false q) half) heads
      dsimp only [pairs] at run
      rw [pairWord_staggeredRun, pairOutput_staggeredRun] at run
      simp only [List.cons_append, List.nil_append, List.append_assoc] at run
      rw [cons_cells_cons] at run
      simpa [HaltAvoidingReaches, branchBlock, pendingFirst, production, at_q,
        List.append_assoc] using run

private theorem sweep_odd_branch_avoiding {state : Type*} (machine : Machine state) (q : state)
    (action : Action state) (writtenCount half : Nat) (at_q : machine q = some action) :
    HaltAvoidingReaches machine
      (branchBlock q half ++
        pendingFirst (reverses machine action true) (action.next true) writtenCount)
      (pendingFrame (reverses machine action true) (action.next true) writtenCount half) := by
  let pairs : List (Symbol state × Symbol state) :=
    (.branchAnchor true q, .branchAnchor false q) ::
      List.replicate half (.branchDigit true q, .branchDigit false q)
  have heads : ∀ pair ∈ pairs, pair.1 ≠ (.halt : Symbol state) := by
    intro pair member
    simp [pairs] at member
    rcases member with rfl | ⟨_, rfl⟩ <;> simp
  have run := sweep_avoiding (production machine) (.halt : Symbol state) pairs
    (pendingFirst (reverses machine action true) (action.next true) writtenCount) heads
  simpa [pairs, HaltAvoidingReaches, branchBlock, pendingFrame_eq, pendingSecond, pairWord,
    pairOutput, production, at_q, List.map_replicate, List.append_assoc] using run

private theorem sweep_even_branch_avoiding {state : Type*} (machine : Machine state)
    (q : state) (action : Action state) (writtenCount half : Nat)
    (at_q : machine q = some action) :
    HaltAvoidingReaches machine
      (.branchAnchor false q ::
        cells (.branchDigit true q) (.branchDigit false q) half ++
          .pad (action.next false) ::
            pendingFirst (reverses machine action false) (action.next false) writtenCount)
      (pendingFrame (reverses machine action false) (action.next false) writtenCount half) := by
  cases half with
  | zero =>
      have run := sweep_avoiding (production machine) (.halt : Symbol state)
        [(.branchAnchor false q, .pad (action.next false))]
        (pendingFirst (reverses machine action false) (action.next false) writtenCount)
        (by simp)
      simpa [HaltAvoidingReaches, pendingFrame_eq, pendingSecond, pairWord, pairOutput,
        production, at_q, List.append_assoc] using run
  | succ half =>
      let pairs : List (Symbol state × Symbol state) :=
        ((.branchAnchor false q, .branchDigit true q) ::
          List.replicate half (.branchDigit false q, .branchDigit true q)) ++
            [(.branchDigit false q, .pad (action.next false))]
      have heads : ∀ pair ∈ pairs, pair.1 ≠ (.halt : Symbol state) := by
        intro pair member
        simp [pairs] at member
        rcases member with rfl | ⟨_, rfl⟩ | rfl <;> simp
      have run := sweep_avoiding (production machine) (.halt : Symbol state) pairs
        (pendingFirst (reverses machine action false) (action.next false) writtenCount) heads
      dsimp only [pairs] at run
      rw [pairWord_staggeredRun, pairOutput_staggeredRun] at run
      simp only [List.cons_append, List.nil_append, List.append_assoc] at run
      rw [cons_cells_cons] at run
      simpa [HaltAvoidingReaches, pendingFrame_eq, pendingSecond, production, at_q,
        List.append_assoc] using run

private theorem sweep_pending_false_avoiding {state : Type*} (machine : Machine state)
    (q : state) (firstCount secondCount : Nat) :
    HaltAvoidingReaches machine (pendingFrame false q firstCount secondCount)
      (frame q firstCount secondCount) := by
  have firstSweep :=
    sweep_run_avoiding (production machine) (.halt : Symbol state)
      (.first false q) (.firstDigit false q) (.pad q) firstCount
      (pendingSecond false q secondCount) (by simp) (by simp)
  have secondSweep :=
    sweep_run_avoiding (production machine) (.halt : Symbol state)
      (.second false q) (.secondDigit false q) (.pad q) secondCount
      (anchorBlock q firstCount) (by simp) (by simp)
  apply Relation.ReflTransGen.trans
    (b := pendingSecond false q secondCount ++ anchorBlock q firstCount)
  · simpa [HaltAvoidingReaches, pendingFrame_eq, pendingFirst, anchorBlock, production,
      List.append_assoc] using firstSweep
  · simpa [HaltAvoidingReaches, pendingSecond, boundaryBlock, frame_eq_blocks, production,
      List.append_assoc] using secondSweep

private theorem sweep_pending_true_avoiding {state : Type*} (machine : Machine state)
    (q : state) (firstCount secondCount : Nat) :
    HaltAvoidingReaches machine (pendingFrame true q firstCount secondCount)
      (frame q secondCount firstCount) := by
  have firstSweep :=
    sweep_run_avoiding (production machine) (.halt : Symbol state)
      (.first true q) (.firstDigit true q) (.pad q) firstCount
      (pendingSecond true q secondCount) (by simp) (by simp)
  have secondSweep :=
    sweep_run_avoiding (production machine) (.halt : Symbol state)
      (.second true q) (.secondDigit true q) (.pad q) secondCount
      (delayedBlock q firstCount) (by simp) (by simp)
  have delayedSweep :=
    sweep_run_avoiding (production machine) (.halt : Symbol state)
      (.delayedFirst q) (.delayedFirstDigit q) (.pad q) firstCount
      (anchorBlock q secondCount) (by simp) (by simp)
  apply Relation.ReflTransGen.trans
    (b := pendingSecond true q secondCount ++ delayedBlock q firstCount)
  · simpa [HaltAvoidingReaches, pendingFrame_eq, pendingFirst, delayedBlock, production,
      List.append_assoc] using firstSweep
  · apply Relation.ReflTransGen.trans
      (b := delayedBlock q firstCount ++ anchorBlock q secondCount)
    · simpa [HaltAvoidingReaches, pendingSecond, anchorBlock, production,
        List.append_assoc] using secondSweep
    · simpa [HaltAvoidingReaches, delayedBlock, boundaryBlock, frame_eq_blocks, production,
        List.append_assoc] using delayedSweep

private theorem sweep_pending_avoiding {state : Type*} (machine : Machine state) (swap : Bool)
    (q : state) (firstCount secondCount : Nat) :
    HaltAvoidingReaches machine (pendingFrame swap q firstCount secondCount)
      (if swap then frame q secondCount firstCount else frame q firstCount secondCount) := by
  cases swap
  · simpa using sweep_pending_false_avoiding machine q firstCount secondCount
  · simpa using sweep_pending_true_avoiding machine q firstCount secondCount

private theorem frame_to_pending_avoiding {state : Type*} (machine : Machine state) (q : state)
    (action : Action state) (behind ahead : Nat) (at_q : machine q = some action) :
    HaltAvoidingReaches machine (frame q behind ahead)
      (pendingFrame (reverses machine action ahead.bodd) (action.next ahead.bodd)
        (written action.write behind) ahead.div2) := by
  rcases ahead.even_or_odd' with ⟨half, rfl | rfl⟩
  · apply Relation.ReflTransGen.trans
      (b := cell (Symbol.boundary q) (Symbol.pad q) ++
        cells (Symbol.boundaryDigit q) (Symbol.pad q) (2 * half) ++
          doubledBlock q (written action.write behind))
      (sweep_write_avoiding machine q action behind (2 * half) at_q)
    apply Relation.ReflTransGen.trans
      (b := doubledBlock q (written action.write behind) ++ halvingBlock q (2 * half))
      (sweep_to_halving_avoiding machine q action
        (written action.write behind) (2 * half) at_q)
    apply Relation.ReflTransGen.trans
      (b := halvingBlock q (2 * half) ++ parityBlock q (written action.write behind))
      (sweep_to_parity_avoiding machine q (written action.write behind) (2 * half))
    apply Relation.ReflTransGen.trans
      (b := Symbol.parityAnchor false q ::
        cells (Symbol.parityDigit true q) (Symbol.parityDigit false q)
            (written action.write behind) ++
          branchBlock q half)
      (sweep_even_front_avoiding machine q (written action.write behind) half)
    apply Relation.ReflTransGen.trans
      (b := Symbol.branchAnchor false q ::
        cells (Symbol.branchDigit true q) (Symbol.branchDigit false q) half ++
          Symbol.pad (action.next false) ::
            pendingFirst (reverses machine action false) (action.next false)
              (written action.write behind))
      (sweep_even_written_avoiding machine q action
        (written action.write behind) half at_q)
    simpa using
      sweep_even_branch_avoiding machine q action (written action.write behind) half at_q
  · apply Relation.ReflTransGen.trans
      (b := cell (Symbol.boundary q) (Symbol.pad q) ++
        cells (Symbol.boundaryDigit q) (Symbol.pad q) (2 * half + 1) ++
          doubledBlock q (written action.write behind))
      (sweep_write_avoiding machine q action behind (2 * half + 1) at_q)
    apply Relation.ReflTransGen.trans
      (b := doubledBlock q (written action.write behind) ++ halvingBlock q (2 * half + 1))
      (sweep_to_halving_avoiding machine q action
        (written action.write behind) (2 * half + 1) at_q)
    apply Relation.ReflTransGen.trans
      (b := halvingBlock q (2 * half + 1) ++ parityBlock q (written action.write behind))
      (sweep_to_parity_avoiding machine q (written action.write behind) (2 * half + 1))
    apply Relation.ReflTransGen.trans
      (b := parityBlock q (written action.write behind) ++ branchBlock q half)
      (sweep_odd_front_avoiding machine q (written action.write behind) half)
    apply Relation.ReflTransGen.trans
      (b := branchBlock q half ++
        pendingFirst (reverses machine action true) (action.next true)
          (written action.write behind))
      (sweep_odd_written_avoiding machine q action (written action.write behind) half at_q)
    simpa using
      sweep_odd_branch_avoiding machine q action (written action.write behind) half at_q

private theorem frame_to_pending_avoiding_strict {state : Type*} (machine : Machine state)
    (q : state) (action : Action state) (behind ahead : Nat)
    (at_q : machine q = some action) :
    Relation.TransGen
      (HeadAvoidingTagStep 2 (production machine) (.halt : Symbol state))
      (frame q behind ahead)
      (pendingFrame (reverses machine action ahead.bodd) (action.next ahead.bodd)
        (written action.write behind) ahead.div2) := by
  rcases ahead.even_or_odd' with ⟨half, rfl | rfl⟩
  · apply Relation.TransGen.trans_left
      (b := cell (Symbol.boundary q) (Symbol.pad q) ++
        cells (Symbol.boundaryDigit q) (Symbol.pad q) (2 * half) ++
          doubledBlock q (written action.write behind))
      (sweep_write_avoiding_strict machine q action behind (2 * half) at_q)
    apply Relation.ReflTransGen.trans
      (b := doubledBlock q (written action.write behind) ++ halvingBlock q (2 * half))
      (sweep_to_halving_avoiding machine q action
        (written action.write behind) (2 * half) at_q)
    apply Relation.ReflTransGen.trans
      (b := halvingBlock q (2 * half) ++ parityBlock q (written action.write behind))
      (sweep_to_parity_avoiding machine q (written action.write behind) (2 * half))
    apply Relation.ReflTransGen.trans
      (b := Symbol.parityAnchor false q ::
        cells (Symbol.parityDigit true q) (Symbol.parityDigit false q)
            (written action.write behind) ++
          branchBlock q half)
      (sweep_even_front_avoiding machine q (written action.write behind) half)
    apply Relation.ReflTransGen.trans
      (b := Symbol.branchAnchor false q ::
        cells (Symbol.branchDigit true q) (Symbol.branchDigit false q) half ++
          Symbol.pad (action.next false) ::
            pendingFirst (reverses machine action false) (action.next false)
              (written action.write behind))
      (sweep_even_written_avoiding machine q action
        (written action.write behind) half at_q)
    simpa using
      sweep_even_branch_avoiding machine q action (written action.write behind) half at_q
  · apply Relation.TransGen.trans_left
      (b := cell (Symbol.boundary q) (Symbol.pad q) ++
        cells (Symbol.boundaryDigit q) (Symbol.pad q) (2 * half + 1) ++
          doubledBlock q (written action.write behind))
      (sweep_write_avoiding_strict machine q action behind (2 * half + 1) at_q)
    apply Relation.ReflTransGen.trans
      (b := doubledBlock q (written action.write behind) ++ halvingBlock q (2 * half + 1))
      (sweep_to_halving_avoiding machine q action
        (written action.write behind) (2 * half + 1) at_q)
    apply Relation.ReflTransGen.trans
      (b := halvingBlock q (2 * half + 1) ++ parityBlock q (written action.write behind))
      (sweep_to_parity_avoiding machine q (written action.write behind) (2 * half + 1))
    apply Relation.ReflTransGen.trans
      (b := parityBlock q (written action.write behind) ++ branchBlock q half)
      (sweep_odd_front_avoiding machine q (written action.write behind) half)
    apply Relation.ReflTransGen.trans
      (b := branchBlock q half ++
        pendingFirst (reverses machine action true) (action.next true)
          (written action.write behind))
      (sweep_odd_written_avoiding machine q action (written action.write behind) half at_q)
    simpa using
      sweep_odd_branch_avoiding machine q action (written action.write behind) half at_q

/-- One nonhalting machine transition is simulated without reading the halt symbol. -/
theorem simulate_action_avoiding {state : Type*} (machine : Machine state)
    (config : Config state) (action : Action state)
    (at_state : machine config.state = some action) :
    HaltAvoidingReaches machine (encode machine config)
      (encode machine (applyAction action config)) := by
  cases actionDirection : action.direction with
  | left =>
      have arithmetic :=
        frame_to_pending_avoiding machine config.state action config.right config.left at_state
      have normalize :=
        sweep_pending_avoiding machine (reverses machine action config.left.bodd)
          (action.next config.left.bodd) (written action.write config.right) config.left.div2
      have simulation := arithmetic.trans normalize
      cases nextDirection : direction machine (action.next config.left.bodd) with
      | left =>
          simpa [encode, orientedCounters, direction_eq_action machine config.state action at_state,
            applyAction, actionDirection, reverses, nextDirection, written_eq_bit, frame,
            Nat.div2_val, List.append_assoc] using simulation
      | right =>
          simpa [encode, orientedCounters, direction_eq_action machine config.state action at_state,
            applyAction, actionDirection, reverses, nextDirection, written_eq_bit, frame,
            Nat.div2_val, List.append_assoc] using simulation
  | right =>
      have arithmetic :=
        frame_to_pending_avoiding machine config.state action config.left config.right at_state
      have normalize :=
        sweep_pending_avoiding machine (reverses machine action config.right.bodd)
          (action.next config.right.bodd) (written action.write config.left) config.right.div2
      have simulation := arithmetic.trans normalize
      cases nextDirection : direction machine (action.next config.right.bodd) with
      | left =>
          simpa [encode, orientedCounters, direction_eq_action machine config.state action at_state,
            applyAction, actionDirection, reverses, nextDirection, written_eq_bit, frame,
            Nat.div2_val, List.append_assoc] using simulation
      | right =>
          simpa [encode, orientedCounters, direction_eq_action machine config.state action at_state,
            applyAction, actionDirection, reverses, nextDirection, written_eq_bit, frame,
            Nat.div2_val, List.append_assoc] using simulation

/-- One nonhalting machine transition has a nonempty halt-avoiding simulation. -/
theorem simulate_action_avoiding_strict {state : Type*} (machine : Machine state)
    (config : Config state) (action : Action state)
    (at_state : machine config.state = some action) :
    Relation.TransGen
      (HeadAvoidingTagStep 2 (production machine) (.halt : Symbol state))
      (encode machine config) (encode machine (applyAction action config)) := by
  cases actionDirection : action.direction with
  | left =>
      have arithmetic :=
        frame_to_pending_avoiding_strict machine config.state action
          config.right config.left at_state
      have normalize :=
        sweep_pending_avoiding machine (reverses machine action config.left.bodd)
          (action.next config.left.bodd) (written action.write config.right) config.left.div2
      have simulation := arithmetic.trans_left normalize
      cases nextDirection : direction machine (action.next config.left.bodd) with
      | left =>
          simpa [encode, orientedCounters, direction_eq_action machine config.state action at_state,
            applyAction, actionDirection, reverses, nextDirection, written_eq_bit, frame,
            Nat.div2_val, List.append_assoc] using simulation
      | right =>
          simpa [encode, orientedCounters, direction_eq_action machine config.state action at_state,
            applyAction, actionDirection, reverses, nextDirection, written_eq_bit, frame,
            Nat.div2_val, List.append_assoc] using simulation
  | right =>
      have arithmetic :=
        frame_to_pending_avoiding_strict machine config.state action
          config.left config.right at_state
      have normalize :=
        sweep_pending_avoiding machine (reverses machine action config.right.bodd)
          (action.next config.right.bodd) (written action.write config.left) config.right.div2
      have simulation := arithmetic.trans_left normalize
      cases nextDirection : direction machine (action.next config.right.bodd) with
      | left =>
          simpa [encode, orientedCounters, direction_eq_action machine config.state action at_state,
            applyAction, actionDirection, reverses, nextDirection, written_eq_bit, frame,
            Nat.div2_val, List.append_assoc] using simulation
      | right =>
          simpa [encode, orientedCounters, direction_eq_action machine config.state action at_state,
            applyAction, actionDirection, reverses, nextDirection, written_eq_bit, frame,
            Nat.div2_val, List.append_assoc] using simulation

private theorem halt_frame_avoiding {state : Type*} (machine : Machine state) (q : state)
    (behind ahead : Nat) (at_q : machine q = none) :
    HaltAvoidingReaches machine (frame q behind ahead) [.halt] := by
  let pairs : List (Symbol state × Symbol state) :=
    ((.anchor q, .pad q) :: List.replicate behind (.digit q, .pad q)) ++
      ((.boundary q, .pad q) ::
        List.replicate ahead (.boundaryDigit q, .pad q))
  have heads : ∀ pair ∈ pairs, pair.1 ≠ (.halt : Symbol state) := by
    intro pair member
    simp [pairs] at member
    rcases member with rfl | ⟨_, rfl⟩ | rfl | ⟨_, rfl⟩ <;> simp
  have run := sweep_avoiding (production machine) (.halt : Symbol state) pairs [] heads
  simpa [pairs, HaltAvoidingReaches, frame, pairWord_append, pairOutput_append, pairWord,
    pairOutput, production, at_q, List.map_replicate, List.append_assoc] using run

private theorem halt_encode_avoiding {state : Type*} (machine : Machine state)
    (config : Config state) (at_state : machine config.state = none) :
    HaltAvoidingReaches machine (encode machine config) [.halt] := by
  rw [encode_eq_frame]
  exact halt_frame_avoiding machine config.state _ _ at_state

private theorem simulate_reaches_avoiding {state : Type*} (machine : Machine state)
    {initial final : Config state} (execution : Reaches machine initial final) :
    HaltAvoidingReaches machine (encode machine initial) (encode machine final) := by
  induction execution with
  | refl => exact Relation.ReflTransGen.refl
  | @tail middle final _ step ih =>
      cases at_state : machine middle.state with
      | none =>
          simp [next, at_state] at step
      | some action =>
          have final_eq : final = applyAction action middle := by
            have successor := next_eq_some_applyAction machine middle action at_state
            simp [successor] at step
            exact step.symm
          exact ih.trans (final_eq ▸ simulate_action_avoiding machine middle action at_state)

/-- Machine halting reaches the singleton halt queue without ever reading the halt symbol. -/
theorem halts_implies_halt_avoiding {state : Type*} (machine : Machine state)
    (initial : Config state) (halts : Halts machine initial) :
    HaltAvoidingReaches machine (encode machine initial) [.halt] := by
  obtain ⟨final, execution, at_final⟩ := halts
  exact
    (simulate_reaches_avoiding machine execution).trans
      (halt_encode_avoiding machine final at_final)

/-- Reaching a queue headed by the unique halt symbol reflects machine halting. -/
theorem tag_reaches_head_halt_implies_halts {state : Type*} (machine : Machine state)
    (initial : Config state) (tail : List (Symbol state))
    (reach : TagReaches machine (encode machine initial) (.halt :: tail)) :
    Halts machine initial := by
  obtain ⟨steps, indexed⟩ := exists_tagReachesIn_of_reaches reach
  induction steps using Nat.strong_induction_on generalizing initial tail with
  | h steps ih =>
      cases at_state : machine initial.state with
      | none =>
          exact ⟨initial, Relation.ReflTransGen.refl, at_state⟩
      | some action =>
          have protectedPath :=
            simulate_action_avoiding_strict machine initial action at_state
          obtain ⟨protectedSteps, protected_pos, protectedIndexed⟩ :=
            exists_headAvoidingTagReachesIn_of_transGen protectedPath
          rcases protectedIndexed.compare indexed with
            ⟨remaining, steps_eq, later⟩ | ⟨_, target_avoided⟩
          · have remaining_lt : remaining < steps := by omega
            obtain ⟨final, laterExecution, at_final⟩ :=
              ih remaining remaining_lt (applyAction action initial) tail
                later.toReaches later
            have first :
                applyAction action initial ∈ next machine initial := by
              simp [next_eq_some_applyAction machine initial action at_state]
            exact
              ⟨final, Relation.ReflTransGen.head first laterExecution, at_final⟩
          · exact False.elim (target_avoided tail rfl)

end CockeMinsky
end Undecidability
end MatrixMortality
