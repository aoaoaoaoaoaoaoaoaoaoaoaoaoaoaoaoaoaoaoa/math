import Mathlib.Computability.Partrec
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Lemmas
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Bitwise

/-!
# Primitive-recursive closure lemmas

Mathlib's computability library deliberately exposes a small basis. This file records the list
and binary-numeration operations used by the explicit undecidability compilers.
-/

namespace MatrixMortality

/-- Canonical primitive-recursive coding for a finite type. Keep it local when an imported type
does not already own a `Primcodable` instance. -/
@[instance_reducible]
noncomputable def finitePrimcodable (α : Type*) [Fintype α] : Primcodable α :=
  Primcodable.ofEquiv (Fin (Fintype.card α)) (Fintype.equivFin α)

namespace Primrec

variable {α : Type*} [Primcodable α]

/-- Appending one low binary digit is primitive recursive. -/
theorem nat_bit : _root_.Primrec₂ Nat.bit := by
  have digit : _root_.Primrec fun bit : Bool => if bit then 1 else 0 :=
    _root_.Primrec.dom_bool _
  exact
    (_root_.Primrec.nat_add.comp
      (_root_.Primrec.nat_mul.comp (_root_.Primrec.const 2) _root_.Primrec.snd)
      (digit.comp _root_.Primrec.fst)).to₂.of_eq fun bit number => by
        cases bit <;> simp [Nat.bit]

/-- Natural exponentiation is primitive recursive in its base and exponent. -/
theorem nat_pow : _root_.Primrec₂ Nat.pow :=
  _root_.Primrec₂.unpaired'.1 Nat.Primrec.pow

/-- The inclusion of natural numbers into integers is primitive recursive. -/
theorem int_ofNat : _root_.Primrec Int.ofNat := by
  have decodeInt : _root_.Primrec Equiv.intEquivNat.symm :=
    _root_.Primrec.of_equiv_symm
  exact
    (decodeInt.comp
      (_root_.Primrec.nat_mul.comp (_root_.Primrec.const 2)
        _root_.Primrec.id)).of_eq fun number => by
          simp [Equiv.intEquivNat, Equiv.intEquivNatSumNat,
            Equiv.natSumNatEquivNat]

/-- The negative-successor constructor of the integer encoding is primitive recursive. -/
theorem int_negSucc : _root_.Primrec Int.negSucc := by
  have decodeInt : _root_.Primrec Equiv.intEquivNat.symm :=
    _root_.Primrec.of_equiv_symm
  exact
    (decodeInt.comp
      (_root_.Primrec.nat_add.comp
        (_root_.Primrec.nat_mul.comp (_root_.Primrec.const 2)
          _root_.Primrec.id)
        (_root_.Primrec.const 1))).of_eq fun number => by
          simp [Equiv.intEquivNat, Equiv.intEquivNatSumNat,
            Equiv.natSumNatEquivNat]

private theorem int_subNatNat : _root_.Primrec₂ Int.subNatNat := by
  have right_le_left :
      _root_.PrimrecPred fun pair : Nat × Nat => pair.2 ≤ pair.1 :=
    _root_.Primrec.nat_le.comp _root_.Primrec.snd _root_.Primrec.fst
  have nonnegative :
      _root_.Primrec fun pair : Nat × Nat =>
        Int.ofNat (pair.1 - pair.2) :=
    int_ofNat.comp <|
      _root_.Primrec.nat_sub.comp _root_.Primrec.fst _root_.Primrec.snd
  have negative :
      _root_.Primrec fun pair : Nat × Nat =>
        Int.negSucc (pair.2 - pair.1 - 1) :=
    int_negSucc.comp <|
      _root_.Primrec.nat_sub.comp
        (_root_.Primrec.nat_sub.comp _root_.Primrec.snd _root_.Primrec.fst)
        (_root_.Primrec.const 1)
  have choice :
      _root_.Primrec₂ fun left right =>
        if right ≤ left then Int.ofNat (left - right)
        else Int.negSucc (right - left - 1) :=
    (_root_.Primrec.ite right_le_left nonnegative negative).to₂
  exact choice.of_eq fun left right => by
      by_cases ordered : right ≤ left
      · rw [if_pos ordered, Int.subNatNat_of_le ordered]
        rfl
      · have strict : left < right := Nat.lt_of_not_ge ordered
        rw [if_neg ordered, Int.subNatNat_of_lt strict]
        simp [Nat.pred_eq_sub_one]

/-- Integer subtraction of two embedded natural numbers is primitive recursive. -/
theorem int_subNat :
    _root_.Primrec₂ fun left right => Int.ofNat left - Int.ofNat right :=
  int_subNatNat.of_eq fun _ _ => Int.subNatNat_eq_coe

/-- Repetition is primitive recursive in the count and repeated value. -/
theorem list_replicate : _root_.Primrec₂ (@List.replicate α) := by
  have step :
      _root_.Primrec₂ (fun (value : α) (state : Nat × List α) => value :: state.2) :=
    _root_.Primrec₂.mk <|
      _root_.Primrec.list_cons.comp _root_.Primrec.fst
        (_root_.Primrec.snd.comp _root_.Primrec.snd)
  have repetition :
      _root_.Primrec₂ (fun (value : α) count => List.replicate count value) :=
    (_root_.Primrec.nat_rec (_root_.Primrec.const []) step).of_eq fun value count => by
      induction count with
      | zero => rfl
      | succ count ih => simp [List.replicate_succ, ih]
  exact repetition.swap

/-- Removing the last list element is primitive recursive. -/
theorem list_dropLast : _root_.Primrec (@List.dropLast α) := by
  exact
    (_root_.Primrec.list_reverse.comp
      (_root_.Primrec.list_tail.comp _root_.Primrec.list_reverse)).of_eq fun list => by
        rw [List.tail_reverse, List.reverse_reverse]

/-- A finite function-valued map is primitive recursive when each component is. -/
theorem fin_function {β : Type*} [Primcodable β] {n : Nat}
    {f : α → Fin n → β} (components : ∀ index, _root_.Primrec fun input => f input index) :
    _root_.Primrec f :=
  _root_.Primrec.fin_curry.mpr
    (_root_.Primrec₂.swap <| _root_.Primrec.fin_curry₁.mpr components)

private def bitsStep (_ : Unit) (history : List (List Bool)) : Option (List Bool) :=
  if history = [] then
    some []
  else
    some (history.length.bodd :: history.getI history.length.div2)

private theorem bitsStep_primrec : _root_.Primrec₂ bitsStep := by
  apply _root_.Primrec₂.mk
  unfold bitsStep
  apply _root_.Primrec.ite
  · exact
      _root_.Primrec.eq.comp _root_.Primrec.snd (_root_.Primrec.const [])
  · exact _root_.Primrec.const (some [])
  · apply _root_.Primrec.option_some.comp
    apply _root_.Primrec.list_cons.comp
    · exact
        _root_.Primrec.nat_bodd.comp
          (_root_.Primrec.list_length.comp _root_.Primrec.snd)
    · exact
        _root_.Primrec.list_getI.comp _root_.Primrec.snd
          (_root_.Primrec.nat_div2.comp
            (_root_.Primrec.list_length.comp _root_.Primrec.snd))

/-- Little-endian binary digits are primitive recursive. -/
theorem nat_bits : _root_.Primrec Nat.bits := by
  have strong :
      _root_.Primrec₂ (fun (_ : Unit) number => Nat.bits number) :=
    _root_.Primrec.nat_strong_rec (fun (_ : Unit) number => Nat.bits number)
      bitsStep_primrec fun _ number => by
        cases number with
        | zero => simp [bitsStep, Nat.bits]
        | succ number =>
            have positive : number + 1 ≠ 0 := Nat.succ_ne_zero number
            have half_lt : (number + 1).div2 < number + 1 :=
              Nat.binaryRec_decreasing positive
            have history_ne :
                List.map Nat.bits (List.range (number + 1)) ≠ [] := by simp
            have half_lt_history :
                (number + 1).div2 <
                  (List.map Nat.bits (List.range (number + 1))).length := by
              simpa using half_lt
            rw [bitsStep, if_neg history_ne]
            simp only [List.length_map, List.length_range, Option.some.injEq]
            rw [List.getI_eq_getElem
              (List.map Nat.bits (List.range (number + 1))) half_lt_history]
            simp only [List.getElem_map, List.getElem_range]
            conv_rhs => rw [Nat.bits]
            rw [Nat.binaryRec_of_ne_zero [] (fun bit _ digits => bit :: digits) positive]
            simp
            rw [Nat.bits]
  exact (strong.comp (_root_.Primrec.const ()) _root_.Primrec.id)

end Primrec

end MatrixMortality
