import MatrixMortality.Undecidability.CyclicTag
import MatrixMortality.Undecidability.TagExecution
import Mathlib.Computability.TuringMachine

/-!
# The Cocke–Minsky compiler

This file gives the deletion-width-two tag compiler used at the remaining universality seam.
The source machine keeps the scanned bit in its finite control and represents the two finite
binary tape halves by natural numbers.  A tag round doubles the half behind the head, divides
the half in front of it by two, and branches on the discarded low bit.

The original construction treats head reversals by “mutatis mutandis”.  Here configurations are
oriented by the direction of their next action.  When consecutive actions disagree, an explicit
final pass swaps the two unary blocks before exposing the next configuration.  Hence every
direction case is covered by one definition.
-/

open Turing

namespace MatrixMortality
namespace Undecidability
namespace CockeMinsky

/-- One action of a binary machine whose current scanned bit is already in its control state. -/
structure Action (state : Type*) where
  /-- Bit written before moving. -/
  write : Bool
  /-- Direction of the move. -/
  direction : Dir
  /-- Next control state, selected by the newly scanned bit. -/
  next : Bool → state

/-- A finite-control binary machine in read-state normal form. -/
abbrev Machine (state : Type*) := state → Option (Action state)

/-- A read-state configuration.  Low binary digits are nearest the tape head. -/
structure Config (state : Type*) where
  /-- Current finite-control state. -/
  state : state
  /-- Tape strictly left of the scanned square. -/
  left : Nat
  /-- Tape strictly right of the scanned square. -/
  right : Nat

/-- Halting states are oriented right; this convention affects only their inert encoding. -/
def direction {state : Type*} (machine : Machine state) (q : state) : Dir :=
  (machine q).map Action.direction |>.getD .right

theorem direction_eq_action {state : Type*} (machine : Machine state) (q : state)
    (action : Action state) (at_q : machine q = some action) :
    direction machine q = action.direction := by
  simp [direction, at_q]

/-- One read-state transition. -/
def next {state : Type*} (machine : Machine state) (config : Config state) :
    Option (Config state) :=
  (machine config.state).map fun action =>
    match action.direction with
    | .right =>
        { state := action.next config.right.bodd
          left := Nat.bit action.write config.left
          right := config.right / 2 }
    | .left =>
        { state := action.next config.left.bodd
          left := config.left / 2
          right := Nat.bit action.write config.right }

/-- The concrete successor determined by a nonhalting action. -/
def applyAction {state : Type*} (action : Action state) (config : Config state) :
    Config state :=
  match action.direction with
  | .right =>
      { state := action.next config.right.bodd
        left := Nat.bit action.write config.left
        right := config.right / 2 }
  | .left =>
      { state := action.next config.left.bodd
        left := config.left / 2
        right := Nat.bit action.write config.right }

theorem next_eq_some_applyAction {state : Type*} (machine : Machine state)
    (config : Config state) (action : Action state)
    (at_state : machine config.state = some action) :
    next machine config = some (applyAction action config) := by
  simp [next, applyAction, at_state]

/-- Reflexive-transitive machine execution. -/
def Reaches {state : Type*} (machine : Machine state) : Config state → Config state → Prop :=
  Turing.Reaches (next machine)

/-- The two counters in motion-relative order: behind the head, then in front of it. -/
def orientedCounters {state : Type*} (machine : Machine state) (config : Config state) :
    Nat × Nat :=
  match direction machine config.state with
  | .right => (config.left, config.right)
  | .left => (config.right, config.left)

/-- The tag alphabet.  Every constructor except `halt` is indexed by a machine state. -/
inductive Symbol (state : Type*)
  | pad : state → Symbol state
  | anchor : state → Symbol state
  | digit : state → Symbol state
  | boundary : state → Symbol state
  | boundaryDigit : state → Symbol state
  | doubledAnchor : state → Symbol state
  | doubledDigit : state → Symbol state
  | parityAnchor : Bool → state → Symbol state
  | parityDigit : Bool → state → Symbol state
  | halvingAnchor : state → Symbol state
  | halvingDigit : state → Symbol state
  | branchAnchor : Bool → state → Symbol state
  | branchDigit : Bool → state → Symbol state
  | first : Bool → state → Symbol state
  | firstDigit : Bool → state → Symbol state
  | second : Bool → state → Symbol state
  | secondDigit : Bool → state → Symbol state
  | delayedFirst : state → Symbol state
  | delayedFirstDigit : state → Symbol state
  | halt : Symbol state
  deriving DecidableEq, Fintype

/-- A two-symbol cell whose second symbol is never read at a configuration boundary. -/
def cell {α : Type*} (head wake : α) : List α := [head, wake]

/-- A unary run of pair-aligned cells. -/
def cells {α : Type*} (head wake : α) (count : Nat) : List α :=
  (List.replicate count (cell head wake)).join

@[simp]
theorem cells_zero {α : Type*} (head wake : α) :
    cells head wake 0 = [] := rfl

theorem cells_succ {α : Type*} (head wake : α) (count : Nat) :
    cells head wake (count + 1) = cell head wake ++ cells head wake count := by
  simp [cells, List.replicate_succ]

theorem cells_succ_snoc {α : Type*} (head wake : α) (count : Nat) :
    cells head wake (count + 1) = cells head wake count ++ cell head wake := by
  simp [cells, List.replicate_succ']

theorem cons_cells_append {α : Type*} (head wake : α) (count : Nat) :
    head :: cells wake head count ++ [wake] = cells head wake (count + 1) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [cells_succ wake head count, cells_succ head wake (count + 1)]
      simpa [cell, List.append_assoc] using congrArg (fun suffix => head :: wake :: suffix) ih

theorem cons_cells_cons {α : Type*} (head wake : α) (count : Nat) (tail : List α) :
    head :: (cells wake head count ++ wake :: tail) =
      cells head wake (count + 1) ++ tail := by
  calc
    head :: (cells wake head count ++ wake :: tail) =
        (head :: cells wake head count ++ [wake]) ++ tail := by
          simp [List.append_assoc]
    _ = cells head wake (count + 1) ++ tail := by rw [cons_cells_append]

theorem cells_add {α : Type*} (head wake : α) (m n : Nat) :
    cells head wake (m + n) = cells head wake m ++ cells head wake n := by
  unfold cells
  rw [List.replicate_add, List.join_append]

theorem join_replicate_double_cell {α : Type*} (head wake : α) (count : Nat) :
    (List.replicate count (cell head wake ++ cell head wake)).join =
      cells head wake (2 * count) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.join_cons, ih]
      rw [show 2 * (count + 1) = 2 + 2 * count by omega, cells_add]
      rfl

/-- Pair encoding of a read-state configuration, oriented by its next move. -/
def encode {state : Type*} (machine : Machine state) (config : Config state) :
    List (Symbol state) :=
  let counters := orientedCounters machine config
  cell (.anchor config.state) (.pad config.state) ++
    cells (.digit config.state) (.pad config.state) counters.1 ++
    cell (.boundary config.state) (.pad config.state) ++
    cells (.boundaryDigit config.state) (.pad config.state) counters.2

/-- Configuration-shaped word with its counters already in motion-relative order. -/
def frame {state : Type*} (q : state) (behind ahead : Nat) : List (Symbol state) :=
  cell (.anchor q) (.pad q) ++ cells (.digit q) (.pad q) behind ++
    cell (.boundary q) (.pad q) ++ cells (.boundaryDigit q) (.pad q) ahead

theorem encode_eq_frame {state : Type*} (machine : Machine state) (config : Config state) :
    encode machine config =
      frame config.state (orientedCounters machine config).1
        (orientedCounters machine config).2 := rfl

/-- First transformed unary block. -/
def doubledBlock {state : Type*} (q : state) (count : Nat) : List (Symbol state) :=
  cell (.doubledAnchor q) (.pad q) ++ cells (.doubledDigit q) (.pad q) count

/-- Second unary block before its parity is read. -/
def halvingBlock {state : Type*} (q : state) (count : Nat) : List (Symbol state) :=
  .halvingAnchor q :: List.replicate count (.halvingDigit q)

/-- The doubled block after its two branch copies have been exposed. -/
def parityBlock {state : Type*} (q : state) (count : Nat) : List (Symbol state) :=
  cell (.parityAnchor true q) (.parityAnchor false q) ++
    cells (.parityDigit true q) (.parityDigit false q) count

/-- The halved block after its two branch copies have been exposed. -/
def branchBlock {state : Type*} (q : state) (count : Nat) : List (Symbol state) :=
  cell (.branchAnchor true q) (.branchAnchor false q) ++
    cells (.branchDigit true q) (.branchDigit false q) count

/-- Output just before its optional counter-order repair pass. -/
def pendingFrame {state : Type*} (swap : Bool) (q : state) (firstCount secondCount : Nat) :
    List (Symbol state) :=
  cell (.first swap q) (.pad q) ++ cells (.firstDigit swap q) (.pad q) firstCount ++
    cell (.second swap q) (.pad q) ++ cells (.secondDigit swap q) (.pad q) secondCount

/-- First half of a pending frame. -/
def pendingFirst {state : Type*} (swap : Bool) (q : state) (count : Nat) :
    List (Symbol state) :=
  cell (.first swap q) (.pad q) ++ cells (.firstDigit swap q) (.pad q) count

/-- Second half of a pending frame. -/
def pendingSecond {state : Type*} (swap : Bool) (q : state) (count : Nat) :
    List (Symbol state) :=
  cell (.second swap q) (.pad q) ++ cells (.secondDigit swap q) (.pad q) count

def anchorBlock {state : Type*} (q : state) (count : Nat) : List (Symbol state) :=
  cell (.anchor q) (.pad q) ++ cells (.digit q) (.pad q) count

def boundaryBlock {state : Type*} (q : state) (count : Nat) : List (Symbol state) :=
  cell (.boundary q) (.pad q) ++ cells (.boundaryDigit q) (.pad q) count

def delayedBlock {state : Type*} (q : state) (count : Nat) : List (Symbol state) :=
  cell (.delayedFirst q) (.pad q) ++ cells (.delayedFirstDigit q) (.pad q) count

theorem pendingFrame_eq {state : Type*} (swap : Bool) (q : state) (m n : Nat) :
    pendingFrame swap q m n = pendingFirst swap q m ++ pendingSecond swap q n := by
  simp [pendingFrame, pendingFirst, pendingSecond, List.append_assoc]

theorem frame_eq_blocks {state : Type*} (q : state) (m n : Nat) :
    frame q m n = anchorBlock q m ++ boundaryBlock q n := by
  simp [frame, anchorBlock, boundaryBlock, List.append_assoc]

/-- Whether the next configuration reverses the motion-relative counter order. -/
def reverses {state : Type*} (machine : Machine state) (action : Action state)
    (read : Bool) : Bool :=
  decide (direction machine (action.next read) ≠ action.direction)

/-- Unary counter after writing the low bit behind the moving head. -/
def written (bit : Bool) (counter : Nat) : Nat :=
  2 * counter + if bit then 1 else 0

theorem written_eq_bit (bit : Bool) (counter : Nat) :
    written bit counter = Nat.bit bit counter := by
  cases bit <;> simp [written, Nat.bit]

/-- Cocke–Minsky productions, including an explicit final counter-swap pass. -/
def production {state : Type*} (machine : Machine state) : Symbol state → List (Symbol state)
  | .anchor q =>
      match machine q with
      | none => [.halt]
      | some action =>
          cell (.doubledAnchor q) (.pad q) ++
            if action.write then cell (.doubledDigit q) (.pad q) else []
  | .digit q =>
      match machine q with
      | none => []
      | some _ =>
          cell (.doubledDigit q) (.pad q) ++ cell (.doubledDigit q) (.pad q)
  | .boundary q =>
      match machine q with
      | none => []
      | some _ => [.halvingAnchor q]
  | .boundaryDigit q =>
      match machine q with
      | none => []
      | some _ => [.halvingDigit q]
  | .doubledAnchor q => [.parityAnchor true q, .parityAnchor false q]
  | .doubledDigit q => [.parityDigit true q, .parityDigit false q]
  | .halvingAnchor q => [.branchAnchor true q, .branchAnchor false q]
  | .halvingDigit q => [.branchDigit true q, .branchDigit false q]
  | .parityAnchor read q =>
      match machine q with
      | none => []
      | some action =>
          let q' := action.next read
          let swap := reverses machine action read
          if read then
            cell (.first swap q') (.pad q')
          else
            [.pad q', .first swap q', .pad q']
  | .parityDigit read q =>
      match machine q with
      | none => []
      | some action =>
          let q' := action.next read
          cell (.firstDigit (reverses machine action read) q') (.pad q')
  | .branchAnchor read q =>
      match machine q with
      | none => []
      | some action =>
          let q' := action.next read
          cell (.second (reverses machine action read) q') (.pad q')
  | .branchDigit read q =>
      match machine q with
      | none => []
      | some action =>
          let q' := action.next read
          cell (.secondDigit (reverses machine action read) q') (.pad q')
  | .first swap q =>
      if swap then cell (.delayedFirst q) (.pad q)
      else cell (.anchor q) (.pad q)
  | .firstDigit swap q =>
      if swap then cell (.delayedFirstDigit q) (.pad q)
      else cell (.digit q) (.pad q)
  | .second swap q =>
      if swap then cell (.anchor q) (.pad q)
      else cell (.boundary q) (.pad q)
  | .secondDigit swap q =>
      if swap then cell (.digit q) (.pad q)
      else cell (.boundaryDigit q) (.pad q)
  | .delayedFirst q => cell (.boundary q) (.pad q)
  | .delayedFirstDigit q => cell (.boundaryDigit q) (.pad q)
  | _ => []

/-- Typed deletion-width-two step relation. -/
def Step {state : Type*} (machine : Machine state) :
    List (Symbol state) → List (Symbol state) → Prop :=
  TagStep 2 (production machine)

/-- Typed reflexive-transitive tag execution. -/
def TagReaches {state : Type*} (machine : Machine state) :
    List (Symbol state) → List (Symbol state) → Prop :=
  Relation.ReflTransGen (Step machine)

/-- Flatten pair cells in their queue order. -/
def pairWord {α : Type*} (pairs : List (α × α)) : List α :=
  (pairs.map fun pair => [pair.1, pair.2]).join

/-- Outputs emitted by the read member of each pair. -/
def pairOutput {α : Type*} (output : α → List α) (pairs : List (α × α)) : List α :=
  (pairs.map fun pair => output pair.1).join

theorem pairWord_append {α : Type*} (left right : List (α × α)) :
    pairWord (left ++ right) = pairWord left ++ pairWord right := by
  simp [pairWord, List.map_append]

theorem pairOutput_append {α : Type*} (output : α → List α)
    (left right : List (α × α)) :
    pairOutput output (left ++ right) =
      pairOutput output left ++ pairOutput output right := by
  simp [pairOutput, List.map_append]

theorem pairWord_replicate_same {α : Type*} (digit : α) (count : Nat) :
    pairWord (List.replicate count (digit, digit)) = List.replicate (2 * count) digit := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, pairWord, List.map_cons, List.join_cons]
      change digit :: digit :: pairWord (List.replicate count (digit, digit)) =
        List.replicate (2 * (count + 1)) digit
      rw [ih]
      change List.replicate 2 digit ++ List.replicate (2 * count) digit =
        List.replicate (2 * (count + 1)) digit
      rw [← List.replicate_add, show 2 + 2 * count = 2 * (count + 1) by omega]

theorem pairWord_oddRun {α : Type*} (anchor digit : α) (count : Nat) :
    pairWord ((anchor, digit) :: List.replicate count (digit, digit)) =
      anchor :: List.replicate (2 * count + 1) digit := by
  change [anchor, digit] ++ pairWord (List.replicate count (digit, digit)) =
    anchor :: List.replicate (2 * count + 1) digit
  rw [pairWord_replicate_same]
  change anchor :: digit :: List.replicate (2 * count) digit =
    anchor :: List.replicate (2 * count + 1) digit
  congr 1

theorem pairOutput_oddRun {α : Type*} (output : α → List α)
    (anchor digit : α) (count : Nat) :
    pairOutput output ((anchor, digit) :: List.replicate count (digit, digit)) =
      output anchor ++ (List.replicate count (output digit)).join := by
  simp [pairOutput, List.map_replicate]

theorem pairWord_evenRun {α : Type*} (anchor digit sentinel : α) (count : Nat) :
    pairWord
        (((anchor, digit) :: List.replicate count (digit, digit)) ++ [(digit, sentinel)]) =
      anchor :: List.replicate (2 * (count + 1)) digit ++ [sentinel] := by
  calc
    pairWord
          (((anchor, digit) :: List.replicate count (digit, digit)) ++ [(digit, sentinel)]) =
        pairWord ((anchor, digit) :: List.replicate count (digit, digit)) ++
          [digit, sentinel] := by
            rw [pairWord_append]
            rfl
    _ = (anchor :: List.replicate (2 * count + 1) digit) ++ [digit, sentinel] := by
          rw [pairWord_oddRun]
    _ = anchor :: List.replicate (2 * (count + 1)) digit ++ [sentinel] := by
          rw [show 2 * (count + 1) = (2 * count + 1) + 1 by omega,
            List.replicate_succ' (2 * count + 1), List.replicate_succ' (2 * count)]
          simp [List.append_assoc]

theorem pairOutput_evenRun {α : Type*} (output : α → List α)
    (anchor digit sentinel : α) (count : Nat) :
    pairOutput output
        (((anchor, digit) :: List.replicate count (digit, digit)) ++ [(digit, sentinel)]) =
      output anchor ++ (List.replicate (count + 1) (output digit)).join := by
  rw [pairOutput_append, pairOutput_oddRun]
  rw [List.replicate_succ']
  simp [pairOutput, List.append_assoc]

theorem pairWord_staggeredRun {α : Type*} (anchorHead digitHead wake sentinel : α)
    (count : Nat) :
    pairWord
        (((anchorHead, wake) :: List.replicate count (digitHead, wake)) ++
          [(digitHead, sentinel)]) =
      [anchorHead, wake] ++ cells digitHead wake count ++ [digitHead, sentinel] := by
  simp [pairWord_append, pairWord, cell, cells, List.map_replicate]

theorem pairOutput_staggeredRun {α : Type*} (output : α → List α)
    (anchorHead digitHead wake sentinel : α) (count : Nat) :
    pairOutput output
        (((anchorHead, wake) :: List.replicate count (digitHead, wake)) ++
          [(digitHead, sentinel)]) =
      output anchorHead ++ (List.replicate (count + 1) (output digitHead)).join := by
  rw [pairOutput_append]
  simp [pairOutput, List.map_replicate, List.replicate_succ', List.append_assoc]

/-- One complete pair-aligned sweep leaves its old tail in front of all emitted output. -/
theorem sweep {α : Type*} (output : α → List α) (pairs : List (α × α)) (tail : List α) :
    Relation.ReflTransGen (TagStep 2 output)
      (pairWord pairs ++ tail) (tail ++ pairOutput output pairs) := by
  induction pairs generalizing tail with
  | nil =>
      simpa [pairWord, pairOutput] using
        (Relation.ReflTransGen.refl : Relation.ReflTransGen (TagStep 2 output) tail tail)
  | cons pair pairs ih =>
      apply Relation.ReflTransGen.head
      · refine ⟨⟨pair.1, [pair.2], rfl⟩, pairWord pairs ++ tail, ?_, rfl⟩
        simp [pairWord, Stroke.letters]
      · simpa [pairWord, pairOutput, List.append_assoc] using
          ih (tail ++ output pair.1)

/-- A sweep specialized to one distinguished cell followed by a unary run. -/
theorem sweep_run {α : Type*} (output : α → List α) (head digit wake : α)
    (count : Nat) (tail : List α) :
    Relation.ReflTransGen (TagStep 2 output)
      (cell head wake ++ cells digit wake count ++ tail)
      (tail ++ output head ++ (List.replicate count (output digit)).join) := by
  simpa [pairWord, pairOutput, cell, cells, List.map_replicate, List.append_assoc] using
    sweep output ((head, wake) :: List.replicate count (digit, wake)) tail

/-- A sweep over a distinguished cell is nonempty, even when its unary suffix is empty. -/
theorem sweep_run_strict {α : Type*} (output : α → List α) (head digit wake : α)
    (count : Nat) (tail : List α) :
    Relation.TransGen (TagStep 2 output)
      (cell head wake ++ cells digit wake count ++ tail)
      (tail ++ output head ++ (List.replicate count (output digit)).join) := by
  apply Relation.TransGen.head'
    (b := cells digit wake count ++ tail ++ output head)
  · refine ⟨⟨head, [wake], rfl⟩, cells digit wake count ++ tail, ?_, rfl⟩
    simp [cell, Stroke.letters, List.append_assoc]
  · have remaining :=
      sweep output (List.replicate count (digit, wake)) (tail ++ output head)
    simpa [pairWord, pairOutput, cells, List.map_replicate, List.append_assoc] using remaining

/-- The first sweep writes one binary digit and doubles the behind-head counter. -/
theorem sweep_write {state : Type*} (machine : Machine state) (q : state)
    (action : Action state) (behind ahead : Nat) (at_q : machine q = some action) :
    TagReaches machine (frame q behind ahead)
      (cell (.boundary q) (.pad q) ++ cells (.boundaryDigit q) (.pad q) ahead ++
        doubledBlock q (written action.write behind)) := by
  have run := sweep_run (production machine) (.anchor q) (.digit q) (.pad q) behind
    (cell (.boundary q) (.pad q) ++ cells (.boundaryDigit q) (.pad q) ahead)
  cases write_eq : action.write <;>
    simpa [TagReaches, Step, frame, doubledBlock, production, at_q, write_eq, written,
      List.append_assoc,
      join_replicate_double_cell, cells_succ] using run

/-- The first simulated sweep contains at least one concrete tag step. -/
theorem sweep_write_strict {state : Type*} (machine : Machine state) (q : state)
    (action : Action state) (behind ahead : Nat) (at_q : machine q = some action) :
    Relation.TransGen (Step machine) (frame q behind ahead)
      (cell (.boundary q) (.pad q) ++ cells (.boundaryDigit q) (.pad q) ahead ++
        doubledBlock q (written action.write behind)) := by
  have run := sweep_run_strict (production machine) (.anchor q) (.digit q) (.pad q) behind
    (cell (.boundary q) (.pad q) ++ cells (.boundaryDigit q) (.pad q) ahead)
  cases write_eq : action.write <;>
    simpa [Step, frame, doubledBlock, production, at_q, write_eq, written,
      List.append_assoc, join_replicate_double_cell, cells_succ] using run

/-- The second sweep rotates the doubled block in front of the counter to be halved. -/
theorem sweep_to_halving {state : Type*} (machine : Machine state) (q : state)
    (action : Action state) (writtenCount ahead : Nat) (at_q : machine q = some action) :
    TagReaches machine
      (cell (.boundary q) (.pad q) ++ cells (.boundaryDigit q) (.pad q) ahead ++
        doubledBlock q writtenCount)
      (doubledBlock q writtenCount ++ halvingBlock q ahead) := by
  have run := sweep_run (production machine) (.boundary q) (.boundaryDigit q) (.pad q) ahead
    (doubledBlock q writtenCount)
  simpa [TagReaches, Step, halvingBlock, production, at_q, List.append_assoc] using run

/-- The third sweep duplicates branch symbols on the written counter. -/
theorem sweep_to_parity {state : Type*} (machine : Machine state) (q : state)
    (writtenCount ahead : Nat) :
    TagReaches machine
      (doubledBlock q writtenCount ++ halvingBlock q ahead)
      (halvingBlock q ahead ++ parityBlock q writtenCount) := by
  have run :=
    sweep_run (production machine) (.doubledAnchor q) (.doubledDigit q) (.pad q)
      writtenCount (halvingBlock q ahead)
  simpa [TagReaches, Step, doubledBlock, parityBlock, production, List.append_assoc] using run

/-- An odd front counter preserves the `true` branch copy of the written block. -/
theorem sweep_odd_front {state : Type*} (machine : Machine state) (q : state)
    (action : Action state) (writtenCount half : Nat) (at_q : machine q = some action) :
    TagReaches machine
      (halvingBlock q (2 * half + 1) ++ parityBlock q writtenCount)
      (parityBlock q writtenCount ++ branchBlock q half) := by
  let pairs : List (Symbol state × Symbol state) :=
    ((.halvingAnchor q, .halvingDigit q) ::
      List.replicate half (.halvingDigit q, .halvingDigit q))
  have run := sweep (production machine) pairs (parityBlock q writtenCount)
  simpa [pairs, TagReaches, Step, halvingBlock, branchBlock, pairWord_oddRun,
    pairOutput_oddRun, production, at_q, List.append_assoc] using run

/-- An even front counter consumes the `true` branch copy of the written block. -/
theorem sweep_even_front {state : Type*} (machine : Machine state) (q : state)
    (action : Action state) (writtenCount half : Nat) (at_q : machine q = some action) :
    TagReaches machine
      (halvingBlock q (2 * half) ++ parityBlock q writtenCount)
      (.parityAnchor false q ::
        cells (.parityDigit true q) (.parityDigit false q) writtenCount ++
          branchBlock q half) := by
  cases half with
  | zero =>
      have run := sweep (production machine)
        [(.halvingAnchor q, .parityAnchor true q)]
        (.parityAnchor false q ::
          cells (.parityDigit true q) (.parityDigit false q) writtenCount)
      simpa [TagReaches, Step, halvingBlock, branchBlock, pairWord, pairOutput, production,
        at_q, List.append_assoc] using run
  | succ half =>
      let pairs : List (Symbol state × Symbol state) :=
        ((.halvingAnchor q, .halvingDigit q) ::
          List.replicate half (.halvingDigit q, .halvingDigit q)) ++
            [(.halvingDigit q, .parityAnchor true q)]
      have run := sweep (production machine) pairs
        (.parityAnchor false q ::
          cells (.parityDigit true q) (.parityDigit false q) writtenCount)
      dsimp only [pairs] at run
      rw [pairWord_evenRun, pairOutput_evenRun] at run
      simpa [TagReaches, Step, halvingBlock, branchBlock, production, at_q,
        List.append_assoc] using run

/-- The surviving odd branch writes the first pending unary block. -/
theorem sweep_odd_written {state : Type*} (machine : Machine state) (q : state)
    (action : Action state) (writtenCount half : Nat) (at_q : machine q = some action) :
    TagReaches machine
      (parityBlock q writtenCount ++ branchBlock q half)
      (branchBlock q half ++
        pendingFirst (reverses machine action true) (action.next true) writtenCount) := by
  let pairs : List (Symbol state × Symbol state) :=
    (.parityAnchor true q, .parityAnchor false q) ::
      List.replicate writtenCount (.parityDigit true q, .parityDigit false q)
  have run := sweep (production machine) pairs (branchBlock q half)
  simpa [pairs, TagReaches, Step, parityBlock, pendingFirst, pairWord, pairOutput,
    production, at_q, List.map_replicate, List.append_assoc] using run

/-- The shifted even branch writes the first pending unary block behind one sacrificial pad. -/
theorem sweep_even_written {state : Type*} (machine : Machine state) (q : state)
    (action : Action state) (writtenCount half : Nat) (at_q : machine q = some action) :
    TagReaches machine
      (.parityAnchor false q ::
        cells (.parityDigit true q) (.parityDigit false q) writtenCount ++
          branchBlock q half)
      (.branchAnchor false q ::
        cells (.branchDigit true q) (.branchDigit false q) half ++
          .pad (action.next false) ::
            pendingFirst (reverses machine action false) (action.next false) writtenCount) := by
  cases writtenCount with
  | zero =>
      have run := sweep (production machine)
        [(.parityAnchor false q, .branchAnchor true q)]
        (.branchAnchor false q ::
          cells (.branchDigit true q) (.branchDigit false q) half)
      simpa [TagReaches, Step, branchBlock, pendingFirst, pairWord, pairOutput, production,
        at_q, List.append_assoc] using run
  | succ writtenCount =>
      let pairs : List (Symbol state × Symbol state) :=
        ((.parityAnchor false q, .parityDigit true q) ::
          List.replicate writtenCount (.parityDigit false q, .parityDigit true q)) ++
            [(.parityDigit false q, .branchAnchor true q)]
      have run := sweep (production machine) pairs
        (.branchAnchor false q ::
          cells (.branchDigit true q) (.branchDigit false q) half)
      dsimp only [pairs] at run
      rw [pairWord_staggeredRun, pairOutput_staggeredRun] at run
      simp only [List.cons_append, List.nil_append, List.append_assoc] at run
      rw [cons_cells_cons] at run
      simpa [TagReaches, Step, branchBlock, pendingFirst, production, at_q,
        List.append_assoc] using run

/-- The unshifted odd branch appends the second pending block. -/
theorem sweep_odd_branch {state : Type*} (machine : Machine state) (q : state)
    (action : Action state) (writtenCount half : Nat) (at_q : machine q = some action) :
    TagReaches machine
      (branchBlock q half ++
        pendingFirst (reverses machine action true) (action.next true) writtenCount)
      (pendingFrame (reverses machine action true) (action.next true) writtenCount half) := by
  let pairs : List (Symbol state × Symbol state) :=
    (.branchAnchor true q, .branchAnchor false q) ::
      List.replicate half (.branchDigit true q, .branchDigit false q)
  have run := sweep (production machine) pairs
    (pendingFirst (reverses machine action true) (action.next true) writtenCount)
  simpa [pairs, TagReaches, Step, branchBlock, pendingFrame_eq, pendingSecond, pairWord,
    pairOutput, production, at_q, List.map_replicate, List.append_assoc] using run

/-- The shifted even branch consumes its sacrificial pad and appends the second pending block. -/
theorem sweep_even_branch {state : Type*} (machine : Machine state) (q : state)
    (action : Action state) (writtenCount half : Nat) (at_q : machine q = some action) :
    TagReaches machine
      (.branchAnchor false q ::
        cells (.branchDigit true q) (.branchDigit false q) half ++
          .pad (action.next false) ::
            pendingFirst (reverses machine action false) (action.next false) writtenCount)
      (pendingFrame (reverses machine action false) (action.next false) writtenCount half) := by
  cases half with
  | zero =>
      have run := sweep (production machine)
        [(.branchAnchor false q, .pad (action.next false))]
        (pendingFirst (reverses machine action false) (action.next false) writtenCount)
      simpa [TagReaches, Step, pendingFrame_eq, pendingSecond, pairWord, pairOutput, production,
        at_q, List.append_assoc] using run
  | succ half =>
      let pairs : List (Symbol state × Symbol state) :=
        ((.branchAnchor false q, .branchDigit true q) ::
          List.replicate half (.branchDigit false q, .branchDigit true q)) ++
            [(.branchDigit false q, .pad (action.next false))]
      have run := sweep (production machine) pairs
        (pendingFirst (reverses machine action false) (action.next false) writtenCount)
      dsimp only [pairs] at run
      rw [pairWord_staggeredRun, pairOutput_staggeredRun] at run
      simp only [List.cons_append, List.nil_append, List.append_assoc] at run
      rw [cons_cells_cons] at run
      simpa [TagReaches, Step, pendingFrame_eq, pendingSecond, production, at_q,
        List.append_assoc] using run

/-- A pending frame that keeps its orientation normalizes in two sweeps. -/
theorem sweep_pending_false {state : Type*} (machine : Machine state) (q : state)
    (firstCount secondCount : Nat) :
    TagReaches machine (pendingFrame false q firstCount secondCount)
      (frame q firstCount secondCount) := by
  have firstSweep :=
    sweep_run (production machine) (.first false q) (.firstDigit false q) (.pad q)
      firstCount (pendingSecond false q secondCount)
  have secondSweep :=
    sweep_run (production machine) (.second false q) (.secondDigit false q) (.pad q)
      secondCount (anchorBlock q firstCount)
  apply Relation.ReflTransGen.trans
    (b := pendingSecond false q secondCount ++ anchorBlock q firstCount)
  · simpa [TagReaches, Step, pendingFrame_eq, pendingFirst, anchorBlock, production,
      List.append_assoc] using firstSweep
  · simpa [TagReaches, Step, pendingSecond, boundaryBlock, frame_eq_blocks, production,
      List.append_assoc] using secondSweep

/-- A pending frame that reverses direction swaps its unary blocks in three sweeps. -/
theorem sweep_pending_true {state : Type*} (machine : Machine state) (q : state)
    (firstCount secondCount : Nat) :
    TagReaches machine (pendingFrame true q firstCount secondCount)
      (frame q secondCount firstCount) := by
  have firstSweep :=
    sweep_run (production machine) (.first true q) (.firstDigit true q) (.pad q)
      firstCount (pendingSecond true q secondCount)
  have secondSweep :=
    sweep_run (production machine) (.second true q) (.secondDigit true q) (.pad q)
      secondCount (delayedBlock q firstCount)
  have delayedSweep :=
    sweep_run (production machine) (.delayedFirst q) (.delayedFirstDigit q) (.pad q)
      firstCount (anchorBlock q secondCount)
  apply Relation.ReflTransGen.trans
    (b := pendingSecond true q secondCount ++ delayedBlock q firstCount)
  · simpa [TagReaches, Step, pendingFrame_eq, pendingFirst, delayedBlock, production,
      List.append_assoc] using firstSweep
  · apply Relation.ReflTransGen.trans
      (b := delayedBlock q firstCount ++ anchorBlock q secondCount)
    · simpa [TagReaches, Step, pendingSecond, anchorBlock, production,
        List.append_assoc] using secondSweep
    · simpa [TagReaches, Step, delayedBlock, boundaryBlock, frame_eq_blocks, production,
        List.append_assoc] using delayedSweep

/-- Every pending frame normalizes, swapping its counters exactly when requested. -/
theorem sweep_pending {state : Type*} (machine : Machine state) (swap : Bool) (q : state)
    (firstCount secondCount : Nat) :
    TagReaches machine (pendingFrame swap q firstCount secondCount)
      (if swap then frame q secondCount firstCount else frame q firstCount secondCount) := by
  cases swap
  · simpa using sweep_pending_false machine q firstCount secondCount
  · simpa using sweep_pending_true machine q firstCount secondCount

/-- Six pair sweeps implement the arithmetic part of one nonhalting machine transition. -/
theorem frame_to_pending {state : Type*} (machine : Machine state) (q : state)
    (action : Action state) (behind ahead : Nat) (at_q : machine q = some action) :
    TagReaches machine (frame q behind ahead)
      (pendingFrame (reverses machine action ahead.bodd) (action.next ahead.bodd)
        (written action.write behind) ahead.div2) := by
  rcases ahead.even_or_odd' with ⟨half, rfl | rfl⟩
  · apply Relation.ReflTransGen.trans
      (b := cell (Symbol.boundary q) (Symbol.pad q) ++
        cells (Symbol.boundaryDigit q) (Symbol.pad q) (2 * half) ++
          doubledBlock q (written action.write behind))
      (sweep_write machine q action behind (2 * half) at_q)
    apply Relation.ReflTransGen.trans
      (b := doubledBlock q (written action.write behind) ++ halvingBlock q (2 * half))
      (sweep_to_halving machine q action (written action.write behind) (2 * half) at_q)
    apply Relation.ReflTransGen.trans
      (b := halvingBlock q (2 * half) ++ parityBlock q (written action.write behind))
      (sweep_to_parity machine q (written action.write behind) (2 * half))
    apply Relation.ReflTransGen.trans
      (b := Symbol.parityAnchor false q ::
        cells (Symbol.parityDigit true q) (Symbol.parityDigit false q)
            (written action.write behind) ++
          branchBlock q half)
      (sweep_even_front machine q action (written action.write behind) half at_q)
    apply Relation.ReflTransGen.trans
      (b := Symbol.branchAnchor false q ::
        cells (Symbol.branchDigit true q) (Symbol.branchDigit false q) half ++
          Symbol.pad (action.next false) ::
            pendingFirst (reverses machine action false) (action.next false)
              (written action.write behind))
      (sweep_even_written machine q action (written action.write behind) half at_q)
    simpa using sweep_even_branch machine q action (written action.write behind) half at_q
  · apply Relation.ReflTransGen.trans
      (b := cell (Symbol.boundary q) (Symbol.pad q) ++
        cells (Symbol.boundaryDigit q) (Symbol.pad q) (2 * half + 1) ++
          doubledBlock q (written action.write behind))
      (sweep_write machine q action behind (2 * half + 1) at_q)
    apply Relation.ReflTransGen.trans
      (b := doubledBlock q (written action.write behind) ++ halvingBlock q (2 * half + 1))
      (sweep_to_halving machine q action (written action.write behind) (2 * half + 1) at_q)
    apply Relation.ReflTransGen.trans
      (b := halvingBlock q (2 * half + 1) ++ parityBlock q (written action.write behind))
      (sweep_to_parity machine q (written action.write behind) (2 * half + 1))
    apply Relation.ReflTransGen.trans
      (b := parityBlock q (written action.write behind) ++ branchBlock q half)
      (sweep_odd_front machine q action (written action.write behind) half at_q)
    apply Relation.ReflTransGen.trans
      (b := branchBlock q half ++
        pendingFirst (reverses machine action true) (action.next true)
          (written action.write behind))
      (sweep_odd_written machine q action (written action.write behind) half at_q)
    simpa using sweep_odd_branch machine q action (written action.write behind) half at_q

/-- The arithmetic simulation of a nonhalting transition contains a concrete tag step. -/
theorem frame_to_pending_strict {state : Type*} (machine : Machine state) (q : state)
    (action : Action state) (behind ahead : Nat) (at_q : machine q = some action) :
    Relation.TransGen (Step machine) (frame q behind ahead)
      (pendingFrame (reverses machine action ahead.bodd) (action.next ahead.bodd)
        (written action.write behind) ahead.div2) := by
  rcases ahead.even_or_odd' with ⟨half, rfl | rfl⟩
  · apply Relation.TransGen.trans_left
      (b := cell (Symbol.boundary q) (Symbol.pad q) ++
        cells (Symbol.boundaryDigit q) (Symbol.pad q) (2 * half) ++
          doubledBlock q (written action.write behind))
      (sweep_write_strict machine q action behind (2 * half) at_q)
    apply Relation.ReflTransGen.trans
      (b := doubledBlock q (written action.write behind) ++ halvingBlock q (2 * half))
      (sweep_to_halving machine q action (written action.write behind) (2 * half) at_q)
    apply Relation.ReflTransGen.trans
      (b := halvingBlock q (2 * half) ++ parityBlock q (written action.write behind))
      (sweep_to_parity machine q (written action.write behind) (2 * half))
    apply Relation.ReflTransGen.trans
      (b := Symbol.parityAnchor false q ::
        cells (Symbol.parityDigit true q) (Symbol.parityDigit false q)
            (written action.write behind) ++
          branchBlock q half)
      (sweep_even_front machine q action (written action.write behind) half at_q)
    apply Relation.ReflTransGen.trans
      (b := Symbol.branchAnchor false q ::
        cells (Symbol.branchDigit true q) (Symbol.branchDigit false q) half ++
          Symbol.pad (action.next false) ::
            pendingFirst (reverses machine action false) (action.next false)
              (written action.write behind))
      (sweep_even_written machine q action (written action.write behind) half at_q)
    simpa using sweep_even_branch machine q action (written action.write behind) half at_q
  · apply Relation.TransGen.trans_left
      (b := cell (Symbol.boundary q) (Symbol.pad q) ++
        cells (Symbol.boundaryDigit q) (Symbol.pad q) (2 * half + 1) ++
          doubledBlock q (written action.write behind))
      (sweep_write_strict machine q action behind (2 * half + 1) at_q)
    apply Relation.ReflTransGen.trans
      (b := doubledBlock q (written action.write behind) ++ halvingBlock q (2 * half + 1))
      (sweep_to_halving machine q action (written action.write behind) (2 * half + 1) at_q)
    apply Relation.ReflTransGen.trans
      (b := halvingBlock q (2 * half + 1) ++ parityBlock q (written action.write behind))
      (sweep_to_parity machine q (written action.write behind) (2 * half + 1))
    apply Relation.ReflTransGen.trans
      (b := parityBlock q (written action.write behind) ++ branchBlock q half)
      (sweep_odd_front machine q action (written action.write behind) half at_q)
    apply Relation.ReflTransGen.trans
      (b := branchBlock q half ++
        pendingFirst (reverses machine action true) (action.next true)
          (written action.write behind))
      (sweep_odd_written machine q action (written action.write behind) half at_q)
    simpa using sweep_odd_branch machine q action (written action.write behind) half at_q

/-- One nonhalting read-state transition is simulated exactly between configuration frames. -/
theorem simulate_action {state : Type*} (machine : Machine state) (config : Config state)
    (action : Action state) (at_state : machine config.state = some action) :
    TagReaches machine (encode machine config) (encode machine (applyAction action config)) := by
  cases actionDirection : action.direction with
  | left =>
      have arithmetic :=
        frame_to_pending machine config.state action config.right config.left at_state
      have normalize :=
        sweep_pending machine (reverses machine action config.left.bodd)
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
        frame_to_pending machine config.state action config.left config.right at_state
      have normalize :=
        sweep_pending machine (reverses machine action config.right.bodd)
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

/-- One nonhalting machine transition is simulated by a nonempty tag execution. -/
theorem simulate_action_strict {state : Type*} (machine : Machine state) (config : Config state)
    (action : Action state) (at_state : machine config.state = some action) :
    Relation.TransGen (Step machine) (encode machine config)
      (encode machine (applyAction action config)) := by
  cases actionDirection : action.direction with
  | left =>
      have arithmetic :=
        frame_to_pending_strict machine config.state action config.right config.left at_state
      have normalize :=
        sweep_pending machine (reverses machine action config.left.bodd)
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
        frame_to_pending_strict machine config.state action config.left config.right at_state
      have normalize :=
        sweep_pending machine (reverses machine action config.right.bodd)
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

/-- A halting machine frame drains to the unique one-symbol halt queue. -/
theorem halt_frame {state : Type*} (machine : Machine state) (q : state)
    (behind ahead : Nat) (at_q : machine q = none) :
    TagReaches machine (frame q behind ahead) [.halt] := by
  let pairs : List (Symbol state × Symbol state) :=
    ((.anchor q, .pad q) :: List.replicate behind (.digit q, .pad q)) ++
      ((.boundary q, .pad q) ::
        List.replicate ahead (.boundaryDigit q, .pad q))
  have run := sweep (production machine) pairs []
  simpa [pairs, TagReaches, Step, frame, pairWord_append, pairOutput_append, pairWord,
    pairOutput, production, at_q, List.map_replicate, List.append_assoc] using run

/-- A halting read-state configuration drains to the unique halt symbol. -/
theorem halt_encode {state : Type*} (machine : Machine state) (config : Config state)
    (at_state : machine config.state = none) :
    TagReaches machine (encode machine config) [.halt] := by
  rw [encode_eq_frame]
  exact halt_frame machine config.state _ _ at_state

/-- A finite machine execution is simulated by a finite tag execution. -/
theorem simulate_reaches {state : Type*} (machine : Machine state)
    {initial final : Config state} (execution : Reaches machine initial final) :
    TagReaches machine (encode machine initial) (encode machine final) := by
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
          exact ih.trans (final_eq ▸ simulate_action machine middle action at_state)

/-- Eventual arrival at a machine state with no outgoing action. -/
def Halts {state : Type*} (machine : Machine state) (initial : Config state) : Prop :=
  ∃ final, Reaches machine initial final ∧ machine final.state = none

/-- The relational halting predicate agrees with mathlib's evaluator. -/
theorem halts_iff_eval_dom {state : Type*} (machine : Machine state) (initial : Config state) :
    Halts machine initial ↔ (Turing.eval (next machine) initial).Dom := by
  constructor
  · rintro ⟨final, execution, at_final⟩
    rw [Part.dom_iff_mem]
    refine ⟨final, Turing.mem_eval.mpr ⟨execution, ?_⟩⟩
    simp [next, at_final]
  · rw [Part.dom_iff_mem]
    rintro ⟨final, evaluated⟩
    obtain ⟨execution, terminal⟩ := Turing.mem_eval.mp evaluated
    refine ⟨final, execution, ?_⟩
    cases at_final : machine final.state with
    | none => rfl
    | some action => simp [next, at_final] at terminal

/-- Machine halting produces the exact one-symbol tag halt queue. -/
theorem halts_implies_tag_reaches_halt {state : Type*} (machine : Machine state)
    (initial : Config state) (halts : Halts machine initial) :
    TagReaches machine (encode machine initial) [.halt] := by
  obtain ⟨final, execution, at_final⟩ := halts
  exact (simulate_reaches machine execution).trans (halt_encode machine final at_final)

/-- Eventual tag halting pulls backward along a finite execution. -/
theorem tagHaltsFrom_before_reaches {state : Type*} (machine : Machine state)
    {before after : List (Symbol state)} (execution : TagReaches machine before after)
    (halts : TagHaltsFrom 2 (production machine) after) :
    TagHaltsFrom 2 (production machine) before := by
  induction execution with
  | refl => exact halts
  | tail _ step ih => exact ih (.step step halts)

/-- A halting tag derivation from a configuration frame reflects machine halting. -/
theorem tagHaltsIn_encode_implies_halts {state : Type*} (machine : Machine state)
    (steps : Nat) (initial : Config state)
    (halts : TagHaltsIn 2 (production machine) steps (encode machine initial)) :
    Halts machine initial := by
  induction steps using Nat.strong_induction_on generalizing initial with
  | h steps ih =>
      cases at_state : machine initial.state with
      | none =>
          exact ⟨initial, Relation.ReflTransGen.refl, at_state⟩
      | some action =>
          have strict := simulate_action_strict machine initial action at_state
          obtain ⟨laterSteps, later_lt, later_halts⟩ :=
            tagHaltsIn_after_transGen strict halts
          obtain ⟨final, later_execution, at_final⟩ :=
            ih laterSteps later_lt (applyAction action initial) later_halts
          have first :
              applyAction action initial ∈ next machine initial := by
            simp [next_eq_some_applyAction machine initial action at_state]
          exact ⟨final, Relation.ReflTransGen.head first later_execution, at_final⟩

/-- Exact tag reachability of the halt symbol is equivalent to machine halting. -/
theorem tag_reaches_halt_iff {state : Type*} (machine : Machine state)
    (initial : Config state) :
    TagReaches machine (encode machine initial) [.halt] ↔ Halts machine initial := by
  constructor
  · intro execution
    have final_halts : TagHaltsFrom 2 (production machine) [.halt] :=
      .stop (by simp)
    have initial_halts := tagHaltsFrom_before_reaches machine execution final_halts
    obtain ⟨steps, indexed⟩ := tagHaltsFrom_iff_exists_tagHaltsIn.mp initial_halts
    exact tagHaltsIn_encode_implies_halts machine steps initial indexed
  · exact halts_implies_tag_reaches_halt machine initial

end CockeMinsky
end Undecidability
end MatrixMortality
