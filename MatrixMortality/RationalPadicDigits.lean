import Mathlib.FieldTheory.Finite.Basic

/-!
# Periodic denominator digits

Let `b` be coprime to a base `p`.  Multiplication by `p⁻¹` permutes `ZMod b`; lifting its
successive residues to `[0,b)` produces digits

```text
dₙ = (p rₙ₊₁ - rₙ) / b.
```

Each digit lies in `[0,p)`, and

```text
-rₙ/b = dₙ + p(-rₙ₊₁/b).
```

This is the ordinary base-`p` expansion recurrence for the negative rational remainder.
Euler's theorem makes both the remainder orbit and the digit stream periodic with period
dividing `φ(b)`.  Applying the construction coordinatewise gives one common periodic stream
for every rational pair whose denominators are prime to `p`.
-/

namespace MatrixMortality.RationalPadicDigits

/-- Remainder obtained after `index` inverse-base shifts modulo `denominator`. -/
def inverseRemainder
    (base denominator : Nat)
    (coprime : base.Coprime denominator)
    (initial : ZMod denominator) (index : Nat) : ZMod denominator :=
  (((ZMod.unitOfCoprime base coprime)⁻¹ ^ index :
      (ZMod denominator)ˣ) : ZMod denominator) * initial

/-- One integer digit extracted from successive inverse-base remainders. -/
def denominatorDigit
    (base denominator : Nat)
    (coprime : base.Coprime denominator)
    (initial : ZMod denominator) (index : Nat) : Int :=
  (((base *
      (inverseRemainder base denominator coprime initial (index + 1)).val :
      Nat) : Int) -
    ((inverseRemainder base denominator coprime initial index).val : Int)) /
      denominator

/-- Euler's theorem makes the inverse-remainder orbit periodic. -/
theorem inverseRemainder_add_totient
    (base denominator : Nat)
    (coprime : base.Coprime denominator)
    (initial : ZMod denominator) (index : Nat) :
    inverseRemainder base denominator coprime initial
        (index + denominator.totient) =
      inverseRemainder base denominator coprime initial index := by
  simp [inverseRemainder, pow_add, ZMod.pow_totient]

/-- Any multiple of Euler's period preserves the inverse remainder. -/
theorem inverseRemainder_add_mul_totient
    (base denominator : Nat)
    (coprime : base.Coprime denominator)
    (initial : ZMod denominator) (index multiple : Nat) :
    inverseRemainder base denominator coprime initial
        (index + multiple * denominator.totient) =
      inverseRemainder base denominator coprime initial index := by
  simp [inverseRemainder, pow_add, pow_mul, ZMod.pow_totient]

/-- One inverse-remainder step is multiplication by the inverse base. -/
theorem inverseRemainder_step
    (base denominator : Nat)
    (coprime : base.Coprime denominator)
    (initial : ZMod denominator) (index : Nat) :
    (base : ZMod denominator) *
        inverseRemainder base denominator coprime initial (index + 1) =
      inverseRemainder base denominator coprime initial index := by
  let unit := ZMod.unitOfCoprime base coprime
  have unit_step : unit * unit⁻¹ ^ (index + 1) = unit⁻¹ ^ index := by
    rw [pow_succ']
    group
  simpa [inverseRemainder, unit, mul_assoc] using
    (congrArg
      (fun value : (ZMod denominator)ˣ =>
        (value : ZMod denominator) * initial)
      unit_step : _)

/-- The denominator digit stream has Euler period. -/
theorem denominatorDigit_add_totient
    (base denominator : Nat)
    (coprime : base.Coprime denominator)
    (initial : ZMod denominator) (index : Nat) :
    denominatorDigit base denominator coprime initial
        (index + denominator.totient) =
      denominatorDigit base denominator coprime initial index := by
  simp only [denominatorDigit]
  rw [show index + denominator.totient + 1 =
      (index + 1) + denominator.totient by omega,
    inverseRemainder_add_totient,
    inverseRemainder_add_totient]

/-- The denominator digit stream is unchanged by every multiple of Euler's period. -/
theorem denominatorDigit_add_mul_totient
    (base denominator : Nat)
    (coprime : base.Coprime denominator)
    (initial : ZMod denominator) (index multiple : Nat) :
    denominatorDigit base denominator coprime initial
        (index + multiple * denominator.totient) =
      denominatorDigit base denominator coprime initial index := by
  simp only [denominatorDigit]
  rw [show index + multiple * denominator.totient + 1 =
      (index + 1) + multiple * denominator.totient by omega,
    inverseRemainder_add_mul_totient,
    inverseRemainder_add_mul_totient]

/-- The numerator defining a denominator digit is divisible by the denominator. -/
theorem denominator_dvd_difference
    (base denominator : Nat) [NeZero denominator]
    (coprime : base.Coprime denominator)
    (initial : ZMod denominator) (index : Nat) :
    (denominator : Int) ∣
      (base *
          (inverseRemainder base denominator coprime initial
            (index + 1)).val : Nat) -
        (inverseRemainder base denominator coprime initial index).val := by
  apply
    (ZMod.intCast_eq_intCast_iff_dvd_sub
      ((inverseRemainder base denominator coprime initial index).val : Int)
      ((base *
        (inverseRemainder base denominator coprime initial
          (index + 1)).val : Nat) : Int)
      denominator).mp
  push_cast
  symm
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  exact inverseRemainder_step base denominator coprime initial index

/-- Multiplying a digit by the denominator recovers its defining difference. -/
theorem denominatorDigit_mul
    (base denominator : Nat) [NeZero denominator]
    (coprime : base.Coprime denominator)
    (initial : ZMod denominator) (index : Nat) :
    denominatorDigit base denominator coprime initial index * denominator =
      (base *
          (inverseRemainder base denominator coprime initial
            (index + 1)).val : Nat) -
        (inverseRemainder base denominator coprime initial index).val :=
  Int.ediv_mul_cancel
    (denominator_dvd_difference base denominator coprime initial index)

/-- The current least residue does not exceed the unreduced next remainder. -/
theorem inverseRemainder_val_le
    (base denominator : Nat)
    (coprime : base.Coprime denominator)
    (initial : ZMod denominator) (index : Nat) :
    (inverseRemainder base denominator coprime initial index).val ≤
      base *
        (inverseRemainder base denominator coprime initial
          (index + 1)).val := by
  have val_eq :=
    congrArg ZMod.val
      (inverseRemainder_step base denominator coprime initial index)
  have mod_eq :
      (base *
          (inverseRemainder base denominator coprime initial
            (index + 1)).val) %
          denominator =
        (inverseRemainder base denominator coprime initial index).val := by
    simpa [ZMod.val_mul, ZMod.val_natCast, Nat.mul_mod] using val_eq
  rw [← mod_eq]
  exact Nat.mod_le _ _

/-- Every denominator digit is nonnegative. -/
theorem denominatorDigit_nonneg
    (base denominator : Nat)
    (coprime : base.Coprime denominator)
    (initial : ZMod denominator) (index : Nat) :
    0 ≤ denominatorDigit base denominator coprime initial index := by
  apply Int.ediv_nonneg
  · exact sub_nonneg.mpr (by
      exact_mod_cast
        inverseRemainder_val_le base denominator coprime initial index)
  · exact_mod_cast Nat.zero_le denominator

/-- In a nontrivial base, every denominator digit is smaller than the base. -/
theorem denominatorDigit_lt
    (base denominator : Nat) [NeZero denominator]
    (coprime : base.Coprime denominator)
    (initial : ZMod denominator) (index : Nat)
    (base_one : 1 < base) :
    denominatorDigit base denominator coprime initial index < base := by
  apply Int.ediv_lt_of_lt_mul
    (show (0 : Int) < denominator by exact_mod_cast NeZero.pos denominator)
  have next_lt :
      base *
          (inverseRemainder base denominator coprime initial
            (index + 1)).val <
        base * denominator :=
    (Nat.mul_lt_mul_left (Nat.zero_lt_of_lt base_one)).mpr
      (inverseRemainder base denominator coprime initial
        (index + 1)).val_lt
  exact
    (sub_le_self
      ((base *
        (inverseRemainder base denominator coprime initial
          (index + 1)).val : Nat) : Int)
      (by positivity)).trans_lt (by exact_mod_cast next_lt)

/-- Successive remainders and their digit satisfy the standard base-expansion recurrence. -/
theorem negativeRemainder_recurrence
    (base denominator : Nat) [NeZero denominator]
    (coprime : base.Coprime denominator)
    (initial : ZMod denominator) (index : Nat) :
    -((inverseRemainder base denominator coprime initial index).val : ℚ) /
          denominator =
        denominatorDigit base denominator coprime initial index +
          base *
            (-((inverseRemainder base denominator coprime initial
                (index + 1)).val : ℚ) /
              denominator) := by
  have denominator_ne : (denominator : ℚ) ≠ 0 := by
    exact_mod_cast NeZero.ne denominator
  have digit_mul :=
    denominatorDigit_mul base denominator coprime initial index
  have digit_mul_rat :
      (denominatorDigit base denominator coprime initial index : ℚ) *
          denominator =
        base *
            (inverseRemainder base denominator coprime initial
              (index + 1)).val -
          (inverseRemainder base denominator coprime initial index).val := by
    exact_mod_cast digit_mul
  calc
    _ =
        ((denominatorDigit base denominator coprime initial index : ℚ) *
            denominator -
          base *
            (inverseRemainder base denominator coprime initial
              (index + 1)).val) /
          denominator := by
            rw [digit_mul_rat]
            ring
    _ = _ := by
      field_simp [denominator_ne]
      ring

/-- Initial modular remainder attached canonically to a rational number. -/
def rationalInitialRemainder (value : ℚ) : ZMod value.den :=
  -value.num

/-- A rational number is an integer plus the negative remainder whose digits are extracted
above.  Thus `rationalDigit` is a genuine eventual base expansion of the rational, not merely
an unrelated periodic residue sequence. -/
theorem exists_intCast_sub_initialRemainder (value : ℚ) :
    ∃ integer : Int,
      value =
        (integer : ℚ) -
          ((rationalInitialRemainder value).val : ℚ) / value.den := by
  letI : NeZero value.den := ⟨Rat.den_ne_zero value⟩
  let remainder := rationalInitialRemainder value
  change
    ∃ integer : Int,
      value = (integer : ℚ) - (remainder.val : ℚ) / value.den
  have cast_eq :
      ((-value.num : Int) : ZMod value.den) =
        (((remainder.val : Nat) : Int) : ZMod value.den) := by
    calc
      ((-value.num : Int) : ZMod value.den) =
          rationalInitialRemainder value := by
            simp [rationalInitialRemainder]
      _ = remainder := rfl
      _ = (remainder.val : ZMod value.den) :=
        (ZMod.natCast_zmod_val remainder).symm
      _ = (((remainder.val : Nat) : Int) : ZMod value.den) := by
        norm_cast
  have denominator_dvd :
      (value.den : Int) ∣ value.num + remainder.val := by
    have raw :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub
        (-value.num) remainder.val value.den).mp cast_eq
    convert raw using 1
    ring
  refine ⟨(value.num + remainder.val) / value.den, ?_⟩
  have denominator_ne : (value.den : ℚ) ≠ 0 := by
    exact_mod_cast Rat.den_ne_zero value
  have quotient_mul :
      (value.num + remainder.val) / (value.den : Int) * value.den =
      value.num + remainder.val :=
    Int.ediv_mul_cancel denominator_dvd
  have quotient_mul_rat :
      (((value.num + remainder.val) / (value.den : Int) : Int) : ℚ) *
          value.den =
        value.num + remainder.val := by
    exact_mod_cast quotient_mul
  have numerator_eq :
      (value.num : ℚ) =
        (((value.num + remainder.val) / (value.den : Int) : Int) : ℚ) *
            value.den -
          remainder.val := by
    linarith [quotient_mul_rat]
  change
    value =
      (((value.num + remainder.val) / value.den : Int) : ℚ) -
        (remainder.val : ℚ) / value.den
  calc
    value = (value.num : ℚ) / value.den := (Rat.num_div_den value).symm
    _ = _ := by
      rw [numerator_eq]
      field_simp [denominator_ne]

/-- Periodic denominator digit stream canonically attached to a rational number. -/
def rationalDigit
    (base : Nat) (value : ℚ) (coprime : base.Coprime value.den)
    (index : Nat) : Int :=
  letI : NeZero value.den := ⟨Rat.den_ne_zero value⟩
  denominatorDigit base value.den coprime
    (rationalInitialRemainder value) index

/-- Every rational denominator digit stream is periodic with Euler period. -/
theorem rationalDigit_add_totient
    (base : Nat) (value : ℚ) (coprime : base.Coprime value.den)
    (index : Nat) :
    rationalDigit base value coprime (index + value.den.totient) =
      rationalDigit base value coprime index := by
  letI : NeZero value.den := ⟨Rat.den_ne_zero value⟩
  exact
    denominatorDigit_add_totient base value.den coprime
      (rationalInitialRemainder value) index

/-- Coordinatewise periodic denominator digits of a rational parameter pair. -/
def rationalPairDigit
    (base : Nat) (parameters : Fin 2 → ℚ)
    (coprime : ∀ i, base.Coprime (parameters i).den)
    (index : Nat) : Fin 2 → Int :=
  ![
    rationalDigit base (parameters 0) (coprime 0) index,
    rationalDigit base (parameters 1) (coprime 1) index
  ]

/-- A rational pair has one common digit period, the product of its two Euler periods. -/
theorem rationalPairDigit_add_commonPeriod
    (base : Nat) (parameters : Fin 2 → ℚ)
    (coprime : ∀ i, base.Coprime (parameters i).den)
    (index : Nat) :
    rationalPairDigit base parameters coprime
        (index + (parameters 0).den.totient * (parameters 1).den.totient) =
      rationalPairDigit base parameters coprime index := by
  ext i
  fin_cases i
  · letI : NeZero (parameters 0).den :=
      ⟨Rat.den_ne_zero (parameters 0)⟩
    simpa [rationalPairDigit, rationalDigit, mul_comm] using
      denominatorDigit_add_mul_totient base (parameters 0).den
        (coprime 0) (rationalInitialRemainder (parameters 0)) index
        (parameters 1).den.totient
  · letI : NeZero (parameters 1).den :=
      ⟨Rat.den_ne_zero (parameters 1)⟩
    simpa [rationalPairDigit, rationalDigit] using
      denominatorDigit_add_mul_totient base (parameters 1).den
        (coprime 1) (rationalInitialRemainder (parameters 1)) index
        (parameters 0).den.totient

end MatrixMortality.RationalPadicDigits
