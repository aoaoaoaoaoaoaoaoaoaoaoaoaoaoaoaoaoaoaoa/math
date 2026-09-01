import MatrixMortality.Computability
import MatrixMortality.MatrixSemigroup

/-!
# Primitive-recursive unreduced fractions

An effective integer is represented as the difference of two primitive-recursive natural
functions. Effective fractions retain a proof that this integer denominator never vanishes.
Their deliberately unreduced arithmetic avoids any gcd normalization while preserving exact
rational values. A finite family can then be cleared with one common nonzero denominator.
-/

namespace MatrixMortality

/-- The operation-only fragment needed to evaluate a fixed rational expression. No algebraic laws
are required: this admits the certified unreduced-fraction interpreter below. -/
class FractionArithmetic (R : Type*) extends
    Zero R, One R, NatCast R, Add R, Sub R, Mul R, Div R, Neg R, Pow R Nat

instance (priority := 100) {R : Type*} [DivisionRing R] : FractionArithmetic R where
  toZero := inferInstance
  toOne := inferInstance
  toNatCast := inferInstance
  toAdd := inferInstance
  toSub := inferInstance
  toMul := inferInstance
  toDiv := inferInstance
  toNeg := inferInstance
  toPow := inferInstance

/-- An integer-valued function represented as a difference of primitive-recursive naturals. -/
structure EffectiveInteger (α : Type*) [Primcodable α] where
  /-- Positive coordinate of the signed value. -/
  positive : α → Nat
  /-- Negative coordinate subtracted from the positive coordinate. -/
  negative : α → Nat
  /-- Primitive-recursive certificate for the positive coordinate. -/
  positive_primrec : Primrec positive
  /-- Primitive-recursive certificate for the negative coordinate. -/
  negative_primrec : Primrec negative

namespace EffectiveInteger

variable {α : Type*} [Primcodable α]

/-- Integer denoted by the two natural coordinates. -/
def value (integer : EffectiveInteger α) (input : α) : Int :=
  Int.ofNat (integer.positive input) - Int.ofNat (integer.negative input)

theorem value_primrec (integer : EffectiveInteger α) : Primrec integer.value :=
  MatrixMortality.Primrec.int_subNat.comp
    integer.positive_primrec integer.negative_primrec

/-- Constant nonnegative effective integer. -/
def ofNat (number : Nat) : EffectiveInteger α where
  positive := fun _ => number
  negative := fun _ => 0
  positive_primrec := Primrec.const number
  negative_primrec := Primrec.const 0

/-- Embed a primitive-recursive natural-valued function as a nonnegative effective integer. -/
def ofNatFunction (function : α → Nat) (function_primrec : Primrec function) :
    EffectiveInteger α where
  positive := function
  negative := fun _ => 0
  positive_primrec := function_primrec
  negative_primrec := Primrec.const 0

/-- Coordinatewise realization of integer addition. -/
def add (left right : EffectiveInteger α) : EffectiveInteger α where
  positive input := left.positive input + right.positive input
  negative input := left.negative input + right.negative input
  positive_primrec := Primrec.nat_add.comp left.positive_primrec right.positive_primrec
  negative_primrec := Primrec.nat_add.comp left.negative_primrec right.negative_primrec

/-- Swap the two natural coordinates to negate an effective integer. -/
def neg (integer : EffectiveInteger α) : EffectiveInteger α where
  positive := integer.negative
  negative := integer.positive
  positive_primrec := integer.negative_primrec
  negative_primrec := integer.positive_primrec

/-- Effective integer subtraction. -/
def sub (left right : EffectiveInteger α) : EffectiveInteger α :=
  add left (neg right)

/-- Signed distributive product in two natural coordinates. -/
def mul (left right : EffectiveInteger α) : EffectiveInteger α where
  positive input :=
    left.positive input * right.positive input +
      left.negative input * right.negative input
  negative input :=
    left.positive input * right.negative input +
      left.negative input * right.positive input
  positive_primrec :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp left.positive_primrec right.positive_primrec)
      (Primrec.nat_mul.comp left.negative_primrec right.negative_primrec)
  negative_primrec :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp left.positive_primrec right.negative_primrec)
      (Primrec.nat_mul.comp left.negative_primrec right.positive_primrec)

/-- Primitive-recursive conditional selection between effective integers. -/
def select (predicate : α → Prop) [DecidablePred predicate]
    (predicate_primrec : PrimrecPred predicate)
    (yes no : EffectiveInteger α) : EffectiveInteger α where
  positive input := if predicate input then yes.positive input else no.positive input
  negative input := if predicate input then yes.negative input else no.negative input
  positive_primrec :=
    Primrec.ite predicate_primrec yes.positive_primrec no.positive_primrec
  negative_primrec :=
    Primrec.ite predicate_primrec yes.negative_primrec no.negative_primrec

theorem isZero_primrec (integer : EffectiveInteger α) :
    PrimrecPred fun input => integer.value input = 0 := by
  have coordinates_equal :
      PrimrecPred fun input => integer.positive input = integer.negative input :=
    Primrec.eq.comp integer.positive_primrec integer.negative_primrec
  exact coordinates_equal.of_eq fun input => by
    simp [value, sub_eq_zero]

@[simp] theorem value_ofNat (number : Nat) (input : α) :
    (ofNat number : EffectiveInteger α).value input = number := by
  simp [ofNat, value]

@[simp] theorem value_ofNatFunction (function : α → Nat)
    (function_primrec : Primrec function) (input : α) :
    (ofNatFunction function function_primrec).value input = function input := by
  simp [ofNatFunction, value]

@[simp] theorem value_add (left right : EffectiveInteger α) (input : α) :
    (add left right).value input = left.value input + right.value input := by
  simp [add, value]
  ring

@[simp] theorem value_neg (integer : EffectiveInteger α) (input : α) :
    (neg integer).value input = -integer.value input := by
  simp [neg, value]

@[simp] theorem value_sub (left right : EffectiveInteger α) (input : α) :
    (sub left right).value input = left.value input - right.value input := by
  simp [sub, sub_eq_add_neg]

@[simp] theorem value_mul (left right : EffectiveInteger α) (input : α) :
    (mul left right).value input = left.value input * right.value input := by
  simp [mul, value]
  ring

@[simp] theorem value_select (predicate : α → Prop) [DecidablePred predicate]
    (predicate_primrec : PrimrecPred predicate) (yes no : EffectiveInteger α)
    (input : α) :
    (select predicate predicate_primrec yes no).value input =
      if predicate input then yes.value input else no.value input := by
  by_cases accepted : predicate input <;> simp [select, value, accepted]

end EffectiveInteger

/-- A primitive-recursive unreduced fraction with a pointwise nonzero denominator. -/
structure EffectiveFraction (α : Type*) [Primcodable α] where
  /-- Effective signed numerator. -/
  numerator : EffectiveInteger α
  /-- Effective signed denominator. -/
  denominator : EffectiveInteger α
  /-- Certificate that every denominator value is nonzero. -/
  denominator_ne_zero : ∀ input, denominator.value input ≠ 0

namespace EffectiveFraction

variable {α : Type*} [Primcodable α]

/-- Rational value of an effective unreduced fraction. -/
def value (fraction : EffectiveFraction α) (input : α) : Rat :=
  fraction.numerator.value input / fraction.denominator.value input

/-- Constant natural fraction with denominator one. -/
def ofNat (number : Nat) : EffectiveFraction α where
  numerator := EffectiveInteger.ofNat number
  denominator := EffectiveInteger.ofNat 1
  denominator_ne_zero input := by simp

/-- Embed a primitive-recursive natural-valued function as a fraction with denominator one. -/
def ofNatFunction (function : α → Nat) (function_primrec : Primrec function) :
    EffectiveFraction α where
  numerator := EffectiveInteger.ofNatFunction function function_primrec
  denominator := EffectiveInteger.ofNat 1
  denominator_ne_zero input := by simp

/-- Unreduced cross-multiplication sum. -/
def add (left right : EffectiveFraction α) : EffectiveFraction α where
  numerator :=
    EffectiveInteger.add
      (EffectiveInteger.mul left.numerator right.denominator)
      (EffectiveInteger.mul right.numerator left.denominator)
  denominator := EffectiveInteger.mul left.denominator right.denominator
  denominator_ne_zero input := by
    simp [left.denominator_ne_zero input, right.denominator_ne_zero input]

/-- Negate the numerator of an effective fraction. -/
def neg (fraction : EffectiveFraction α) : EffectiveFraction α where
  numerator := EffectiveInteger.neg fraction.numerator
  denominator := fraction.denominator
  denominator_ne_zero := fraction.denominator_ne_zero

/-- Effective fraction subtraction. -/
def sub (left right : EffectiveFraction α) : EffectiveFraction α :=
  add left (neg right)

/-- Unreduced product of effective fractions. -/
def mul (left right : EffectiveFraction α) : EffectiveFraction α where
  numerator := EffectiveInteger.mul left.numerator right.numerator
  denominator := EffectiveInteger.mul left.denominator right.denominator
  denominator_ne_zero input := by
    simp [left.denominator_ne_zero input, right.denominator_ne_zero input]

/-- Total division agrees with rational division. At a zero divisor it emits the canonical zero
fraction, matching the division-ring convention. -/
def div (left right : EffectiveFraction α) : EffectiveFraction α :=
  let numeratorZero := fun input => right.numerator.value input = 0
  let numeratorZeroPrimrec := EffectiveInteger.isZero_primrec right.numerator
  {
    numerator := EffectiveInteger.select numeratorZero numeratorZeroPrimrec
      (EffectiveInteger.ofNat 0)
      (EffectiveInteger.mul left.numerator right.denominator)
    denominator := EffectiveInteger.select numeratorZero numeratorZeroPrimrec
      (EffectiveInteger.ofNat 1)
      (EffectiveInteger.mul left.denominator right.numerator)
    denominator_ne_zero := fun input => by
      by_cases numerator_zero : right.numerator.value input = 0
      · rw [EffectiveInteger.value_select, if_pos numerator_zero]
        simp
      · rw [EffectiveInteger.value_select, if_neg numerator_zero,
          EffectiveInteger.value_mul]
        exact mul_ne_zero (left.denominator_ne_zero input) numerator_zero }

/-- Natural powers under unreduced multiplication. -/
def pow (fraction : EffectiveFraction α) : Nat → EffectiveFraction α
  | 0 => ofNat 1
  | exponent + 1 => mul (pow fraction exponent) fraction

instance : FractionArithmetic (EffectiveFraction α) where
  zero := ofNat 0
  one := ofNat 1
  natCast := ofNat
  add := add
  sub := sub
  mul := mul
  div := div
  neg := neg
  pow := pow

@[simp] theorem value_ofNat (number : Nat) (input : α) :
    (ofNat number : EffectiveFraction α).value input = number := by
  simp [ofNat, value]

@[simp] theorem value_ofNatFunction (function : α → Nat)
    (function_primrec : Primrec function) (input : α) :
    (ofNatFunction function function_primrec).value input = function input := by
  simp [ofNatFunction, value]

@[simp] theorem value_add (left right : EffectiveFraction α) (input : α) :
    (add left right).value input = left.value input + right.value input := by
  rw [value, value, value]
  simp only [add, EffectiveInteger.value_add, EffectiveInteger.value_mul]
  field_simp [left.denominator_ne_zero input, right.denominator_ne_zero input]
  push_cast
  ring

@[simp] theorem value_neg (fraction : EffectiveFraction α) (input : α) :
    (neg fraction).value input = -fraction.value input := by
  simp [neg, value, neg_div]

@[simp] theorem value_sub (left right : EffectiveFraction α) (input : α) :
    (sub left right).value input = left.value input - right.value input := by
  simp [sub, sub_eq_add_neg]

@[simp] theorem value_mul (left right : EffectiveFraction α) (input : α) :
    (mul left right).value input = left.value input * right.value input := by
  rw [value, value, value]
  simp only [mul, EffectiveInteger.value_mul]
  field_simp [left.denominator_ne_zero input, right.denominator_ne_zero input]
  push_cast
  ring

@[simp] theorem value_div (left right : EffectiveFraction α) (input : α) :
    (div left right).value input = left.value input / right.value input := by
  by_cases numerator_zero : right.numerator.value input = 0
  · simp [div, value, EffectiveInteger.value_select, numerator_zero]
  · rw [value, value, value]
    simp only [div, EffectiveInteger.value_select, numerator_zero, if_false,
      EffectiveInteger.value_mul]
    field_simp [left.denominator_ne_zero input, right.denominator_ne_zero input,
      numerator_zero]
    push_cast
    ring

@[simp] theorem value_pow (fraction : EffectiveFraction α) (exponent : Nat)
    (input : α) :
    (pow fraction exponent).value input = fraction.value input ^ exponent := by
  induction exponent with
  | zero => simp [pow]
  | succ exponent induction => simp [pow, induction, pow_succ]

@[simp] theorem value_zero (input : α) :
    (0 : EffectiveFraction α).value input = 0 :=
  value_ofNat 0 input

@[simp] theorem value_one (input : α) :
    (1 : EffectiveFraction α).value input = 1 :=
  value_ofNat 1 input

@[simp] theorem value_natCast (number : Nat) (input : α) :
    (Nat.cast number : EffectiveFraction α).value input = number :=
  value_ofNat number input

@[simp] theorem value_ofNatLiteral (number : Nat) [number.AtLeastTwo] (input : α) :
    (ofNat(number) : EffectiveFraction α).value input = number :=
  value_ofNat number input

@[simp] theorem value_add_notation (left right : EffectiveFraction α) (input : α) :
    (left + right).value input = left.value input + right.value input :=
  value_add left right input

@[simp] theorem value_sub_notation (left right : EffectiveFraction α) (input : α) :
    (left - right).value input = left.value input - right.value input :=
  value_sub left right input

@[simp] theorem value_mul_notation (left right : EffectiveFraction α) (input : α) :
    (left * right).value input = left.value input * right.value input :=
  value_mul left right input

@[simp] theorem value_div_notation (left right : EffectiveFraction α) (input : α) :
    (left / right).value input = left.value input / right.value input :=
  value_div left right input

@[simp] theorem value_neg_notation (fraction : EffectiveFraction α) (input : α) :
    (-fraction).value input = -fraction.value input :=
  value_neg fraction input

@[simp] theorem value_pow_notation (fraction : EffectiveFraction α) (exponent : Nat)
    (input : α) :
    (fraction ^ exponent).value input = fraction.value input ^ exponent :=
  value_pow fraction exponent input

end EffectiveFraction

/-- One common-denominator clearing of a fixed finite vector of effective fractions. -/
structure ClearedFin {α : Type*} [Primcodable α] {n : Nat}
    (fractions : Fin n → EffectiveFraction α) where
  /-- Common effective denominator of the finite family. -/
  denominator : EffectiveInteger α
  /-- Integer coordinate obtained after multiplying by the common denominator. -/
  entry : Fin n → EffectiveInteger α
  /-- Pointwise nonvanishing certificate for the common denominator. -/
  denominator_ne_zero : ∀ input, denominator.value input ≠ 0
  /-- Exact rational semantics of every cleared coordinate. -/
  cast_entry : ∀ index input,
    (entry index).value input =
      denominator.value input * (fractions index).value input

/-- Clear a finite vector recursively, multiplying earlier cleared entries by each new
denominator. This exposes primitive-recursive integer coordinates by construction. -/
def clearFin {α : Type*} [Primcodable α] :
    {n : Nat} → (fractions : Fin n → EffectiveFraction α) → ClearedFin fractions
  | 0, fractions =>
      { denominator := EffectiveInteger.ofNat 1
        entry := Fin.elim0
        denominator_ne_zero := by simp
        cast_entry := fun index => Fin.elim0 index }
  | n + 1, fractions =>
      let tailFractions : Fin n → EffectiveFraction α := fun index => fractions index.succ
      let tail := clearFin tailFractions
      {
        denominator := EffectiveInteger.mul (fractions 0).denominator tail.denominator
        entry := Fin.cases
          (EffectiveInteger.mul (fractions 0).numerator tail.denominator)
          (fun index => EffectiveInteger.mul (fractions 0).denominator (tail.entry index))
        denominator_ne_zero := fun input => by
          simp only [EffectiveInteger.value_mul]
          exact mul_ne_zero ((fractions 0).denominator_ne_zero input)
            (tail.denominator_ne_zero input)
        cast_entry := fun index input => by
          refine Fin.cases ?_ (fun tailIndex => ?_) index
          · simp only [Fin.cases_zero, EffectiveInteger.value_mul,
              EffectiveFraction.value]
            field_simp [(fractions 0).denominator_ne_zero input]
            push_cast
            ring
          · simp only [Fin.cases_succ, EffectiveInteger.value_mul]
            push_cast
            rw [tail.cast_entry tailIndex input]
            ring }

end MatrixMortality
