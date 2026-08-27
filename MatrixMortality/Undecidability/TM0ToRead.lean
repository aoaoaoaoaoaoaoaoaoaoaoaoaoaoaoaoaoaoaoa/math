import MatrixMortality.Computability
import MatrixMortality.Undecidability.CockeMinsky

/-!
# Binary TM0 normalization

Mathlib's `TM0` machine may either move or write during one transition.  The read-state machine
used by the Cocke–Minsky compiler always writes and then moves.  This file implements the exact
normalization: moves take one read-state transition, while writes take a right-left excursion of
two transitions.

The two finite tape halves are encoded as natural numbers with the nearest cell in the low binary
digit.  Trailing blank cells therefore disappear canonically.
-/

open Turing

namespace MatrixMortality
namespace Undecidability
namespace TM0ToRead

/-- Interpret a low-bit-first Boolean list as a natural number. -/
def bitsNatList : List Bool → Nat
  | [] => 0
  | bit :: bits => Nat.bit bit (bitsNatList bits)

/-- The low-bit-first numeral interpretation is primitive recursive. -/
theorem bitsNatList_primrec : Primrec bitsNatList := by
  exact
    (Primrec.list_foldr Primrec.id (Primrec.const 0)
      ((MatrixMortality.Primrec.nat_bit).comp
        (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun bits => by
          induction bits with
          | nil => rfl
          | cons bit bits ih =>
              simpa only [List.foldr_cons, id_eq, bitsNatList] using
                congrArg (Nat.bit bit) ih

theorem bitsNatList_append_false (bits : List Bool) (count : Nat) :
    bitsNatList (bits ++ List.replicate count false) = bitsNatList bits := by
  induction bits with
  | nil =>
      induction count with
      | zero => rfl
      | succ count ih => simpa [bitsNatList, List.replicate_succ] using ih
  | cons bit bits ih =>
      simp [bitsNatList, ih]

/-- Interpret a blank-extended Boolean half-tape as a natural number. -/
def bitsNat (bits : ListBlank Bool) : Nat :=
  bits.liftOn bitsNatList fun before after extension => by
    obtain ⟨count, rfl⟩ := extension
    simpa using (bitsNatList_append_false before count).symm

@[simp]
theorem bitsNat_mk (bits : List Bool) :
    bitsNat (ListBlank.mk bits) = bitsNatList bits := rfl

@[simp]
theorem bitsNat_cons (bit : Bool) (bits : ListBlank Bool) :
    bitsNat (bits.cons bit) = Nat.bit bit (bitsNat bits) := by
  induction bits using ListBlank.induction_on with
  | _ bits => rfl

@[simp]
theorem bodd_bitsNat (bits : ListBlank Bool) :
    (bitsNat bits).bodd = bits.head := by
  induction bits using ListBlank.induction_on with
  | _ bits =>
      cases bits with
      | nil => rfl
      | cons bit bits => exact Nat.bodd_bit bit (bitsNatList bits)

@[simp]
theorem div2_bitsNat (bits : ListBlank Bool) :
    (bitsNat bits).div2 = bitsNat bits.tail := by
  induction bits using ListBlank.induction_on with
  | _ bits =>
      cases bits with
      | nil => rfl
      | cons bit bits => exact Nat.div2_bit bit (bitsNatList bits)

@[simp]
theorem bitsNat_div_two (bits : ListBlank Bool) :
    bitsNat bits / 2 = bitsNat bits.tail := by
  rw [← Nat.div2_val, div2_bitsNat]

@[simp]
theorem bit_head_tail_bitsNat (bits : ListBlank Bool) :
    Nat.bit bits.head (bitsNat bits.tail) = bitsNat bits := by
  rw [← bitsNat_cons, ListBlank.cons_head_tail]

/-- Finite control for the write-then-move normal form. -/
inductive State (label : Type*)
  | normal : label → Bool → State label
  | restore : label → Bool → State label
  deriving DecidableEq, Fintype

/-- Translate a binary `TM0` machine into read-state normal form. -/
def machine {label : Type*} [Inhabited label] (source : TM0.Machine Bool label) :
    CockeMinsky.Machine (State label)
  | .normal q scanned =>
      match source q scanned with
      | none => none
      | some (q', .move direction) =>
          some
            { write := scanned
              direction
              next := State.normal q' }
      | some (q', .write bit) =>
          some
            { write := bit
              direction := .right
              next := State.restore q' }
  | .restore q scanned =>
      some
        { write := scanned
          direction := .left
          next := State.normal q }

/-- Translate a binary `TM0` configuration into the two-counter read-state representation. -/
def config {label : Type*} (source : TM0.Cfg Bool label) :
    CockeMinsky.Config (State label) where
  state := .normal source.q source.Tape.head
  left := bitsNat source.Tape.left
  right := bitsNat source.Tape.right

/-- The read-state normal form refines every `TM0` transition by one or two transitions. -/
theorem respects {label : Type*} [Inhabited label] (source : TM0.Machine Bool label) :
    StateTransition.Respects (TM0.step source) (CockeMinsky.next (machine source))
      fun sourceConfig readConfig => config sourceConfig = readConfig := by
  rw [StateTransition.fun_respects]
  rintro ⟨q, ⟨head, left, right⟩⟩
  cases transition : source q head with
  | none =>
      simp [StateTransition.FRespects, TM0.step, CockeMinsky.next, machine, config, transition]
  | some command =>
      obtain ⟨q', statement⟩ := command
      cases statement with
      | move moveDirection =>
          simp only [TM0.step, transition, Option.map_some, StateTransition.FRespects]
          cases moveDirection
          · apply Relation.TransGen.single
            simp [CockeMinsky.next, machine, config, transition, Tape.move]
          · apply Relation.TransGen.single
            simp [CockeMinsky.next, machine, config, transition, Tape.move]
      | write bit =>
          simp only [TM0.step, transition, Option.map_some, StateTransition.FRespects]
          let middle : CockeMinsky.Config (State label) :=
            { state := .restore q' right.head
              left := Nat.bit bit (bitsNat left)
              right := (bitsNat right).div2 }
          have first :
              middle ∈ CockeMinsky.next (machine source)
                (config ⟨q, ⟨head, left, right⟩⟩) := by
            simp [middle, CockeMinsky.next, machine, config, transition]
          have second :
              config ⟨q', (⟨head, left, right⟩ : Tape Bool).write bit⟩ ∈
                CockeMinsky.next (machine source) middle := by
            simp [middle, CockeMinsky.next, machine, config, Tape.write, Nat.bodd_bit,
              Nat.div2_val]
          exact Relation.TransGen.head first (Relation.TransGen.single second)

/-- The normalized read-state machine halts exactly when the source `TM0` machine halts. -/
theorem halts_iff_eval_dom {label : Type*} [Inhabited label]
    (source : TM0.Machine Bool label) (initial : TM0.Cfg Bool label) :
    CockeMinsky.Halts (machine source) (config initial) ↔
      (StateTransition.eval (TM0.step source) initial).Dom := by
  rw [CockeMinsky.halts_iff_eval_dom]
  exact StateTransition.tr_eval_dom (respects source) rfl

end TM0ToRead
end Undecidability
end MatrixMortality
