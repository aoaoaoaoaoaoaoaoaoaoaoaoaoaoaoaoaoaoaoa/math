import MatrixMortality.Undecidability.CyclicTag
import MatrixMortality.Undecidability.TagExecution
import Mathlib.Computability.TuringMachine
import Mathlib.Tactic.DeriveFintype

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

/-- Reconstructed leading unary block after normalization. -/
def anchorBlock {state : Type*} (q : state) (count : Nat) : List (Symbol state) :=
  cell (.anchor q) (.pad q) ++ cells (.digit q) (.pad q) count

/-- Reconstructed trailing unary block after normalization. -/
def boundaryBlock {state : Type*} (q : state) (count : Nat) : List (Symbol state) :=
  cell (.boundary q) (.pad q) ++ cells (.boundaryDigit q) (.pad q) count

/-- Leading unary block held aside during a counter-order swap. -/
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
  MatrixMortality.TagReaches 2 (production machine)

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

end CockeMinsky
end Undecidability
end MatrixMortality
