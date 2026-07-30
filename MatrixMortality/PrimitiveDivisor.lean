import Mathlib.NumberTheory.Multiplicity
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval

/-!
# Primitive divisors of powers

This file isolates the arithmetic content of Bang–Zsigmondy from its matrix-semigroup use.
A primitive prime divisor of `aⁿ - 1` divides no earlier positive power difference.
-/

namespace MatrixMortality

open Polynomial

noncomputable section

/-- Absolute integral value of the `exponent`-th cyclotomic polynomial at `base`. -/
def cyclotomicValue (base exponent : Nat) : Nat :=
  ((cyclotomic exponent ℤ).eval (base : ℤ)).natAbs

/-- A prime divisor of `base ^ exponent - 1` absent from every earlier positive exponent. -/
def IsPrimitivePrimeDivisor (prime base exponent : Nat) : Prop :=
  1 < base ∧
    0 < exponent ∧
    prime.Prime ∧
    prime ∣ base ^ exponent - 1 ∧
    ∀ earlier : Nat, 0 < earlier → earlier < exponent →
      ¬prime ∣ base ^ earlier - 1

/-- A prime factor of a cyclotomic value makes the base a cyclotomic root in the residue
field. -/
theorem isRoot_cyclotomic_of_prime_dvd_value
    {prime base exponent : Nat} (prime_spec : prime.Prime)
    (divides : prime ∣ cyclotomicValue base exponent) :
    IsRoot (cyclotomic exponent (ZMod prime)) (base : ZMod prime) := by
  letI : Fact prime.Prime := ⟨prime_spec⟩
  rw [IsRoot.def, ← map_cyclotomic_int exponent (ZMod prime), eval_map]
  rw [show (base : ZMod prime) =
    (Int.castRingHom (ZMod prime)) (base : ℤ) by simp, Polynomial.eval₂_hom]
  change ((eval (base : ℤ) (cyclotomic exponent ℤ) : ℤ) : ZMod prime) = 0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  apply Int.dvd_natAbs.mp
  exact_mod_cast divides

/-- A cyclotomic prime factor is coprime to the evaluated base. -/
theorem coprime_of_prime_dvd_cyclotomicValue
    {prime base exponent : Nat} (prime_spec : prime.Prime)
    (exponent_positive : 0 < exponent)
    (divides : prime ∣ cyclotomicValue base exponent) :
    base.Coprime prime := by
  letI : Fact prime.Prime := ⟨prime_spec⟩
  exact Polynomial.coprime_of_root_cyclotomic exponent_positive
    (isRoot_cyclotomic_of_prime_dvd_value prime_spec divides)

/-- In characteristic `prime`, a root of the `exponent`-th cyclotomic polynomial has order
equal to the prime-free part of `exponent`. -/
theorem isPrimitiveRoot_ordCompl_of_prime_dvd_cyclotomicValue
    {prime base exponent : Nat} (prime_spec : prime.Prime)
    (exponent_positive : 0 < exponent)
    (divides : prime ∣ cyclotomicValue base exponent) :
    IsPrimitiveRoot (base : ZMod prime) (ord_compl[prime] exponent) := by
  letI : Fact prime.Prime := ⟨prime_spec⟩
  let core := ord_compl[prime] exponent
  have exponent_ne : exponent ≠ 0 := exponent_positive.ne'
  have core_not_dvd : ¬prime ∣ core :=
    Nat.not_dvd_ord_compl prime_spec exponent_ne
  letI : NeZero (core : ZMod prime) :=
    NeZero.of_not_dvd (ZMod prime) core_not_dvd
  have root :=
    isRoot_cyclotomic_of_prime_dvd_value prime_spec divides
  have decomposition :
      prime ^ exponent.factorization prime * core = exponent :=
    Nat.ord_proj_mul_ord_compl_eq_self exponent prime
  rw [← decomposition] at root
  exact Polynomial.isRoot_cyclotomic_prime_pow_mul_iff_of_charP.mp root

/-- A cyclotomic prime factor not dividing the exponent is primitive. -/
theorem primitivePrimeDivisor_of_prime_dvd_cyclotomicValue
    {prime base exponent : Nat} (prime_spec : prime.Prime)
    (base_gt_one : 1 < base) (exponent_positive : 0 < exponent)
    (divides : prime ∣ cyclotomicValue base exponent)
    (not_dvd_exponent : ¬prime ∣ exponent) :
    IsPrimitivePrimeDivisor prime base exponent := by
  have core_eq : ord_compl[prime] exponent = exponent := by
    simp [Nat.factorization_eq_zero_of_not_dvd not_dvd_exponent]
  have primitive_root : IsPrimitiveRoot (base : ZMod prime) exponent := by
    simpa [core_eq] using
      isPrimitiveRoot_ordCompl_of_prime_dvd_cyclotomicValue
        prime_spec exponent_positive divides
  refine ⟨base_gt_one, exponent_positive, prime_spec, ?_, ?_⟩
  · apply (Nat.modEq_iff_dvd'
      (Nat.one_le_pow exponent base (Nat.zero_lt_of_lt base_gt_one))).mp
    apply Nat.ModEq.symm
    exact (ZMod.natCast_eq_natCast_iff (base ^ exponent) 1 prime).mp
      (by simpa using primitive_root.pow_eq_one)
  · intro earlier earlier_positive earlier_lt earlier_divides
    have earlier_modEq : base ^ earlier ≡ 1 [MOD prime] := by
      apply Nat.ModEq.symm
      rw [Nat.modEq_iff_dvd'
        (Nat.one_le_pow earlier base (Nat.zero_lt_of_lt base_gt_one))]
      exact earlier_divides
    have earlier_power : (base : ZMod prime) ^ earlier = 1 := by
      simpa using
        (ZMod.natCast_eq_natCast_iff (base ^ earlier) 1 prime).mpr earlier_modEq
    exact (Nat.not_dvd_of_pos_of_lt earlier_positive earlier_lt)
      (primitive_root.dvd_of_pow_eq_one earlier earlier_power)

/-- A nonprimitive cyclotomic prime factor is larger than every other prime factor of the
exponent. Hence at most one prime can occur nonprimitively in a cyclotomic value. -/
theorem other_prime_lt_of_dvd_cyclotomicValue
    {prime other base exponent : Nat}
    (prime_spec : prime.Prime) (other_spec : other.Prime)
    (exponent_positive : 0 < exponent)
    (prime_value : prime ∣ cyclotomicValue base exponent)
    (other_exponent : other ∣ exponent) (other_ne : other ≠ prime) :
    other < prime := by
  letI : Fact prime.Prime := ⟨prime_spec⟩
  let core := ord_compl[prime] exponent
  have root : IsPrimitiveRoot (base : ZMod prime) core :=
    isPrimitiveRoot_ordCompl_of_prime_dvd_cyclotomicValue
      prime_spec exponent_positive prime_value
  have core_positive : 0 < core :=
    Nat.ord_compl_pos prime exponent_positive.ne'
  have base_nonzero : (base : ZMod prime) ≠ 0 :=
    root.ne_zero core_positive.ne'
  have core_dvd_pred : core ∣ prime - 1 := by
    rw [root.eq_orderOf]
    exact ZMod.orderOf_dvd_card_sub_one base_nonzero
  have core_lt : core < prime := by
    have prime_two : 2 ≤ prime := prime_spec.two_le
    have core_le : core ≤ prime - 1 :=
      Nat.le_of_dvd (by omega : 0 < prime - 1) core_dvd_pred
    omega
  have prime_not_dvd_other : ¬prime ∣ other := by
    intro prime_dvd_other
    exact other_ne
      ((Nat.prime_dvd_prime_iff_eq prime_spec other_spec).mp prime_dvd_other).symm
  exact (Nat.le_of_dvd core_positive
    (Nat.dvd_ord_compl_of_dvd_not_dvd other_exponent prime_not_dvd_other)).trans_lt
      core_lt

/-- If an exponent has no primitive divisor, its cyclotomic value is a power of the unique
nonprimitive prime dividing both the value and the exponent. -/
theorem cyclotomicValue_isPrimePow_of_no_primitive
    {base exponent : Nat} (base_gt_one : 1 < base) (exponent_gt_one : 1 < exponent)
    (no_primitive : ∀ prime, ¬IsPrimitivePrimeDivisor prime base exponent) :
    IsPrimePow (cyclotomicValue base exponent) := by
  let value := cyclotomicValue base exponent
  have value_gt_one : 1 < value := by
    have lower :=
      Polynomial.sub_one_lt_natAbs_cyclotomic_eval exponent_gt_one base_gt_one.ne'
    dsimp [value, cyclotomicValue]
    omega
  let prime := value.minFac
  have prime_spec : prime.Prime := Nat.minFac_prime value_gt_one.ne'
  have prime_value : prime ∣ value := Nat.minFac_dvd value
  have prime_exponent : prime ∣ exponent := by
    by_contra not_dvd
    exact no_primitive prime
      (primitivePrimeDivisor_of_prime_dvd_cyclotomicValue
        prime_spec base_gt_one (by omega) prime_value not_dvd)
  rw [isPrimePow_iff_unique_prime_dvd]
  refine ⟨prime, ⟨prime_spec, prime_value⟩, ?_⟩
  intro other other_data
  obtain ⟨other_spec, other_value⟩ := other_data
  have other_exponent : other ∣ exponent := by
    by_contra not_dvd
    exact no_primitive other
      (primitivePrimeDivisor_of_prime_dvd_cyclotomicValue
        other_spec base_gt_one (by omega) other_value not_dvd)
  by_contra other_ne
  have other_lt :=
    other_prime_lt_of_dvd_cyclotomicValue
      prime_spec other_spec (by omega) prime_value other_exponent other_ne
  have prime_lt :=
    other_prime_lt_of_dvd_cyclotomicValue
      other_spec prime_spec (by omega) other_value prime_exponent (Ne.symm other_ne)
  omega

/-- A cyclotomic value, multiplied by any earlier divisor difference, divides the full power
difference. This is the arithmetic bridge from polynomial factorization to valuations. -/
theorem pow_sub_one_mul_cyclotomicValue_dvd
    {base divisor exponent : Nat} (base_gt_one : 1 < base)
    (divisor_proper : divisor ∈ exponent.properDivisors) :
    (base ^ divisor - 1) * cyclotomicValue base exponent ∣
      base ^ exponent - 1 := by
  have polynomial_dvd :
      (X ^ divisor - 1) * cyclotomic exponent ℤ ∣ X ^ exponent - 1 :=
    Polynomial.X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd
      ℤ divisor_proper
  obtain ⟨quotient, quotient_eq⟩ := polynomial_dvd
  apply_fun eval (base : ℤ) at quotient_eq
  have base_positive : 0 < base := by omega
  have eval_positive :
      0 < eval (base : ℤ) (cyclotomic exponent ℤ) :=
    Polynomial.cyclotomic_pos' exponent (by exact_mod_cast base_gt_one)
  have eval_eq :
      eval (base : ℤ) (cyclotomic exponent ℤ) =
        (cyclotomicValue base exponent : ℤ) := by
    dsimp [cyclotomicValue]
    rw [Int.natCast_natAbs, abs_of_pos eval_positive]
  have divisor_power_one : 1 ≤ base ^ divisor :=
    Nat.one_le_pow divisor base base_positive
  have exponent_power_one : 1 ≤ base ^ exponent :=
    Nat.one_le_pow exponent base base_positive
  have integer_dvd :
      (((base ^ divisor - 1) * cyclotomicValue base exponent : Nat) : ℤ) ∣
        ((base ^ exponent - 1 : Nat) : ℤ) := by
    use eval (base : ℤ) quotient
    rw [Nat.cast_mul, Nat.cast_sub divisor_power_one, Nat.cast_pow, Nat.cast_one,
      Nat.cast_sub exponent_power_one, Nat.cast_pow, Nat.cast_one, ← eval_eq]
    simpa [eval_mul, eval_sub, eval_pow] using quotient_eq
  exact_mod_cast integer_dvd

namespace IsPrimitivePrimeDivisor

theorem one_lt_base {prime base exponent : Nat}
    (primitive : IsPrimitivePrimeDivisor prime base exponent) :
    1 < base :=
  primitive.1

theorem prime {prime base exponent : Nat}
    (primitive : IsPrimitivePrimeDivisor prime base exponent) :
    prime.Prime :=
  primitive.2.2.1

theorem exponent_positive {prime base exponent : Nat}
    (primitive : IsPrimitivePrimeDivisor prime base exponent) :
    0 < exponent :=
  primitive.2.1

theorem dvd {prime base exponent : Nat}
    (primitive : IsPrimitivePrimeDivisor prime base exponent) :
    prime ∣ base ^ exponent - 1 :=
  primitive.2.2.2.1

theorem not_dvd_of_pos_of_lt {prime base exponent earlier : Nat}
    (primitive : IsPrimitivePrimeDivisor prime base exponent)
    (earlier_positive : 0 < earlier) (earlier_lt : earlier < exponent) :
    ¬prime ∣ base ^ earlier - 1 :=
  primitive.2.2.2.2 earlier earlier_positive earlier_lt

theorem base_coprime {prime base exponent : Nat}
    (primitive : IsPrimitivePrimeDivisor prime base exponent) :
    base.Coprime prime := by
  apply Nat.Coprime.symm
  apply primitive.prime.coprime_iff_not_dvd.mpr
  intro prime_dvd_base
  have prime_dvd_power : prime ∣ base ^ exponent :=
    dvd_pow prime_dvd_base primitive.exponent_positive.ne'
  have prime_dvd_one : prime ∣ 1 := by
    have difference := Nat.dvd_sub' prime_dvd_power primitive.dvd
    have power_one_le : 1 ≤ base ^ exponent :=
      Nat.one_le_pow exponent base (Nat.zero_lt_of_lt primitive.one_lt_base)
    rw [Nat.sub_sub_self power_one_le] at difference
    exact difference
  exact primitive.prime.not_dvd_one prime_dvd_one

theorem modEq_one {prime base exponent : Nat}
    (primitive : IsPrimitivePrimeDivisor prime base exponent) :
    base ^ exponent ≡ 1 [MOD prime] := by
  apply Nat.ModEq.symm
  rw [Nat.modEq_iff_dvd'
    (Nat.one_le_pow exponent base (Nat.zero_lt_of_lt primitive.one_lt_base))]
  exact primitive.dvd

/-- The residue class of the base has exactly the primitive exponent as its multiplicative
order. -/
theorem unit_orderOf_eq_exponent {prime base exponent : Nat}
    (primitive : IsPrimitivePrimeDivisor prime base exponent) :
    orderOf (ZMod.unitOfCoprime base primitive.base_coprime) = exponent := by
  let unit := ZMod.unitOfCoprime base primitive.base_coprime
  have unit_exponent : unit ^ exponent = 1 := by
    apply Units.ext
    simpa [unit, ZMod.coe_unitOfCoprime] using
      (ZMod.natCast_eq_natCast_iff (base ^ exponent) 1 prime).mpr
        primitive.modEq_one
  have order_dvd_exponent : orderOf unit ∣ exponent :=
    orderOf_dvd_of_pow_eq_one unit_exponent
  have exponent_le_order : exponent ≤ orderOf unit := by
    apply le_of_not_gt
    intro order_lt
    exact primitive.not_dvd_of_pos_of_lt (orderOf_pos unit)
      order_lt (by
        apply (Nat.modEq_iff_dvd'
          (Nat.one_le_pow (orderOf unit) base
            (Nat.zero_lt_of_lt primitive.one_lt_base))).mp
        apply Nat.ModEq.symm
        exact (ZMod.natCast_eq_natCast_iff
          (base ^ orderOf unit) 1 prime).mp (by
            simpa [unit, ZMod.coe_unitOfCoprime] using
              congrArg Units.val (pow_orderOf_eq_one unit)))
  exact le_antisymm
    (Nat.le_of_dvd primitive.exponent_positive order_dvd_exponent)
    exponent_le_order

/-- A primitive exponent divides the order of the residue field's unit group. -/
theorem exponent_dvd_prime_sub_one {prime base exponent : Nat}
    (primitive : IsPrimitivePrimeDivisor prime base exponent) :
    exponent ∣ prime - 1 := by
  letI : Fact prime.Prime := ⟨primitive.prime⟩
  let unit := ZMod.unitOfCoprime base primitive.base_coprime
  have order_dvd :
      orderOf unit ∣ Fintype.card (ZMod prime)ˣ :=
    orderOf_dvd_card
  simpa [unit, primitive.unit_orderOf_eq_exponent,
    Nat.totient_prime primitive.prime] using order_dvd

/-- A primitive divisor detects every exponent not divisible by its primitive exponent. -/
theorem not_modEq_one_of_not_dvd {prime base exponent power : Nat}
    (primitive : IsPrimitivePrimeDivisor prime base exponent)
    (not_divides : ¬exponent ∣ power) :
    ¬base ^ power ≡ 1 [MOD prime] := by
  intro congruent
  have base_coprime := primitive.base_coprime
  let unit := ZMod.unitOfCoprime base base_coprime
  have unit_power : unit ^ power = 1 := by
    apply Units.ext
    simpa [unit, ZMod.coe_unitOfCoprime] using
      (ZMod.natCast_eq_natCast_iff (base ^ power) 1 prime).mpr congruent
  have order_dvd_power : orderOf unit ∣ power :=
    orderOf_dvd_of_pow_eq_one unit_power
  have order_eq : orderOf unit = exponent :=
    primitive.unit_orderOf_eq_exponent
  exact not_divides (order_eq ▸ order_dvd_power)

end IsPrimitivePrimeDivisor

/-- Removing one copy of a prime from an exponent leaves its prime-free part as a divisor. -/
theorem ord_compl_dvd_div_of_prime_dvd
    {prime exponent : Nat} (prime_spec : prime.Prime) (exponent_positive : 0 < exponent)
    (prime_dvd : prime ∣ exponent) :
    ord_compl[prime] exponent ∣ exponent / prime := by
  apply (Nat.dvd_div_iff_mul_dvd prime_dvd).2
  have factor_positive : 0 < exponent.factorization prime :=
    prime_spec.factorization_pos_of_dvd exponent_positive.ne' prime_dvd
  have prime_dvd_projection : prime ∣ prime ^ exponent.factorization prime :=
    dvd_pow_self prime factor_positive.ne'
  have product_dvd :
      prime * ord_compl[prime] exponent ∣
        prime ^ exponent.factorization prime * ord_compl[prime] exponent :=
    Nat.mul_dvd_mul_right prime_dvd_projection (ord_compl[prime] exponent)
  have decomposition :
      prime ^ exponent.factorization prime * ord_compl[prime] exponent = exponent :=
    Nat.ord_proj_mul_ord_compl_eq_self exponent prime
  rw [decomposition] at product_dvd
  exact product_dvd

/-- A prime dividing both an exponent and its cyclotomic value already divides the power
difference one prime step earlier. -/
theorem prime_dvd_pow_div_sub_one
    {prime base exponent : Nat} (prime_spec : prime.Prime) (base_gt_one : 1 < base)
    (exponent_positive : 0 < exponent)
    (prime_dvd_value : prime ∣ cyclotomicValue base exponent)
    (prime_dvd_exponent : prime ∣ exponent) :
    prime ∣ base ^ (exponent / prime) - 1 := by
  letI : Fact prime.Prime := ⟨prime_spec⟩
  let core := ord_compl[prime] exponent
  have root : IsPrimitiveRoot (base : ZMod prime) core :=
    isPrimitiveRoot_ordCompl_of_prime_dvd_cyclotomicValue
      prime_spec exponent_positive prime_dvd_value
  have core_dvd : core ∣ exponent / prime :=
    ord_compl_dvd_div_of_prime_dvd prime_spec exponent_positive prime_dvd_exponent
  have power_eq : (base : ZMod prime) ^ (exponent / prime) = 1 := by
    obtain ⟨k, hk⟩ := core_dvd
    rw [hk, pow_mul, root.pow_eq_one, one_pow]
  apply (Nat.modEq_iff_dvd'
      (Nat.one_le_pow (exponent / prime) base (Nat.zero_lt_of_lt base_gt_one))).mp
  apply Nat.ModEq.symm
  exact (ZMod.natCast_eq_natCast_iff (base ^ (exponent / prime)) 1 prime).mp
    (by simpa only [Nat.cast_pow, Nat.cast_one] using power_eq)

/-- An odd nonprimitive prime occurs to the first power in a cyclotomic value. This is the
cyclotomic form of lifting the exponent. -/
theorem cyclotomicValue_primePower_exponent_one_of_odd
    {prime k base exponent : Nat} (prime_spec : prime.Prime) (prime_odd : Odd prime)
    (base_gt_one : 1 < base) (exponent_gt_one : 1 < exponent)
    (prime_dvd_exponent : prime ∣ exponent) (k_positive : 0 < k)
    (value_eq : cyclotomicValue base exponent = prime ^ k) :
    k = 1 := by
  let divisor := exponent / prime
  have exponent_positive : 0 < exponent := by omega
  have prime_le_exponent : prime ≤ exponent :=
    Nat.le_of_dvd exponent_positive prime_dvd_exponent
  have divisor_positive : 0 < divisor :=
    Nat.div_pos prime_le_exponent prime_spec.pos
  have exponent_eq : divisor * prime = exponent :=
    Nat.div_mul_cancel prime_dvd_exponent
  have divisor_dvd_exponent : divisor ∣ exponent := ⟨prime, exponent_eq.symm⟩
  have divisor_lt_exponent : divisor < exponent := by
    rw [← exponent_eq]
    nlinarith [prime_spec.two_le]
  have divisor_proper : divisor ∈ exponent.properDivisors :=
    Nat.mem_properDivisors.mpr ⟨divisor_dvd_exponent, divisor_lt_exponent⟩
  have product_dvd :
      (base ^ divisor - 1) * prime ^ k ∣ base ^ exponent - 1 := by
    rw [← value_eq]
    exact pow_sub_one_mul_cyclotomicValue_dvd base_gt_one divisor_proper
  have base_power_gt_one : 1 < base ^ divisor :=
    one_lt_pow base_gt_one divisor_positive.ne'
  have base_power_sub_ne : base ^ divisor - 1 ≠ 0 :=
    Nat.sub_ne_zero_of_lt base_power_gt_one
  have full_sub_ne : base ^ exponent - 1 ≠ 0 :=
    Nat.sub_ne_zero_of_lt (one_lt_pow base_gt_one exponent_positive.ne')
  have factor_le :
      ((base ^ divisor - 1) * prime ^ k).factorization prime ≤
        (base ^ exponent - 1).factorization prime :=
    (Nat.factorization_le_iff_dvd
      (mul_ne_zero base_power_sub_ne (pow_ne_zero k prime_spec.ne_zero))
      full_sub_ne).mpr product_dvd prime
  have prime_dvd_value : prime ∣ cyclotomicValue base exponent := by
    rw [value_eq]
    exact dvd_pow_self prime k_positive.ne'
  have base_not_dvd : ¬prime ∣ base ^ divisor := by
    have base_coprime : base.Coprime prime :=
      coprime_of_prime_dvd_cyclotomicValue
        prime_spec exponent_positive prime_dvd_value
    exact prime_spec.coprime_iff_not_dvd.mp (base_coprime.pow_left divisor).symm
  letI : Fact prime.Prime := ⟨prime_spec⟩
  have lte := padicValNat.pow_sub_pow prime_odd
    (show (1 : Nat) < base ^ divisor from base_power_gt_one)
    (prime_dvd_pow_div_sub_one prime_spec base_gt_one exponent_positive
      prime_dvd_value prime_dvd_exponent)
    base_not_dvd prime_spec.ne_zero
  rw [one_pow, ← pow_mul, exponent_eq] at lte
  rw [Nat.factorization_mul base_power_sub_ne (pow_ne_zero k prime_spec.ne_zero),
    Finsupp.add_apply, prime_spec.factorization_pow, Finsupp.single_eq_same] at factor_le
  rw [Nat.factorization_def _ prime_spec, Nat.factorization_def _ prime_spec] at factor_le
  rw [lte, padicValNat_self] at factor_le
  omega

/-- If an exponent has no primitive divisor, its cyclotomic value is a power of the unique
largest prime shared by the value and the exponent. -/
theorem cyclotomicValue_structure_of_no_primitive
    {base exponent : Nat} (base_gt_one : 1 < base) (exponent_gt_one : 1 < exponent)
    (no_primitive : ∀ prime, ¬IsPrimitivePrimeDivisor prime base exponent) :
    ∃ prime k : Nat, prime.Prime ∧ 0 < k ∧ prime ∣ exponent ∧
      cyclotomicValue base exponent = prime ^ k ∧
      ∀ other : Nat, other.Prime → other ∣ exponent → other ≠ prime → other < prime := by
  have prime_power := cyclotomicValue_isPrimePow_of_no_primitive
    base_gt_one exponent_gt_one no_primitive
  obtain ⟨prime, k, prime_spec, k_positive, value_eq⟩ :=
    (isPrimePow_nat_iff (cyclotomicValue base exponent)).mp prime_power
  have prime_dvd_value : prime ∣ cyclotomicValue base exponent := by
    rw [← value_eq]
    exact dvd_pow_self prime k_positive.ne'
  have prime_dvd_exponent : prime ∣ exponent := by
    by_contra not_dvd
    exact no_primitive prime
      (primitivePrimeDivisor_of_prime_dvd_cyclotomicValue prime_spec base_gt_one
        (by omega) prime_dvd_value not_dvd)
  refine ⟨prime, k, prime_spec, k_positive, prime_dvd_exponent, value_eq.symm, ?_⟩
  intro other other_spec other_dvd other_ne
  exact other_prime_lt_of_dvd_cyclotomicValue prime_spec other_spec (by omega)
    prime_dvd_value other_dvd other_ne

/-- An integer with prime divisor `2` and no other possible prime divisor is a positive power
of two. -/
theorem eq_two_pow_of_unique_two
    {n : Nat} (two_dvd : 2 ∣ n)
    (other_lt : ∀ other : Nat, other.Prime → other ∣ n → other ≠ 2 → other < 2) :
    ∃ power : Nat, 0 < power ∧ n = 2 ^ power := by
  have prime_power : IsPrimePow n := by
    rw [isPrimePow_iff_unique_prime_dvd]
    refine ⟨2, ⟨Nat.prime_two, two_dvd⟩, ?_⟩
    intro other other_data
    obtain ⟨other_spec, other_dvd⟩ := other_data
    by_contra other_ne
    exact (Nat.not_lt_of_ge other_spec.two_le)
      (other_lt other other_spec other_dvd other_ne)
  obtain ⟨prime, power, prime_spec, power_positive, power_eq⟩ :=
    (isPrimePow_nat_iff n).mp prime_power
  have prime_dvd_n : prime ∣ n := by
    rw [← power_eq]
    exact dvd_pow_self prime power_positive.ne'
  have prime_eq : prime = 2 := by
    by_contra prime_ne
    exact (Nat.not_lt_of_ge prime_spec.two_le)
      (other_lt prime prime_spec prime_dvd_n prime_ne)
  exact ⟨power, power_positive, by simpa [prime_eq] using power_eq.symm⟩

/-- Evaluation of a two-power cyclotomic polynomial. -/
theorem cyclotomicValue_two_pow_succ (base power : Nat) :
    cyclotomicValue base (2 ^ (power + 1)) = base ^ (2 ^ power) + 1 := by
  rw [cyclotomicValue, cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
  norm_num [Polynomial.eval_finset_sum, Polynomial.eval_pow, Polynomial.eval_X,
    Int.natAbs_ofNat]
  rw [show (base : ℤ) ^ (2 ^ power) + 1 =
    (base ^ (2 ^ power) + 1 : Nat) by norm_cast, Int.natAbs_ofNat]

/-- The prime `2` also occurs only once in a nonprimitive cyclotomic value above exponent
two. -/
theorem cyclotomicValue_primePower_exponent_one_of_two
    {k base exponent : Nat} (exponent_gt_two : 2 < exponent)
    (two_dvd_exponent : 2 ∣ exponent) (k_positive : 0 < k)
    (value_eq : cyclotomicValue base exponent = 2 ^ k)
    (other_lt : ∀ other : Nat, other.Prime → other ∣ exponent → other ≠ 2 → other < 2) :
    k = 1 := by
  obtain ⟨power, power_positive, exponent_eq⟩ :=
    eq_two_pow_of_unique_two two_dvd_exponent other_lt
  obtain ⟨halfPower, rfl⟩ := Nat.exists_eq_succ_of_ne_zero power_positive.ne'
  rw [exponent_eq, cyclotomicValue_two_pow_succ] at value_eq
  rw [exponent_eq] at exponent_gt_two
  have halfPower_positive : 0 < halfPower := by
    by_contra halfPower_zero
    have : halfPower = 0 := Nat.eq_zero_of_not_pos halfPower_zero
    subst halfPower
    norm_num at exponent_gt_two
  have base_odd : Odd base := by
    have two_dvd_value : 2 ∣ base ^ (2 ^ halfPower) + 1 := by
      rw [value_eq]
      exact dvd_pow_self 2 k_positive.ne'
    have power_odd : Odd (base ^ (2 ^ halfPower)) := by
      exact Nat.not_even_iff_odd.mp fun base_power_even => by
        have sum_odd : Odd (base ^ (2 ^ halfPower) + 1) :=
          base_power_even.add_odd odd_one
        exact (Nat.not_even_iff_odd.mpr sum_odd)
          (even_iff_two_dvd.mpr two_dvd_value)
    exact Nat.not_even_iff_odd.mp fun base_even =>
      (Nat.not_even_iff_odd.mpr power_odd)
        (base_even.pow_of_ne_zero (pow_ne_zero halfPower (by decide : (2 : Nat) ≠ 0)))
  have base_power_mod_four : base ^ (2 ^ halfPower) % 4 = 1 := by
    obtain ⟨tail, rfl⟩ := Nat.exists_eq_succ_of_ne_zero halfPower_positive.ne'
    have odd_power : Odd (base ^ (2 ^ tail)) := base_odd.pow
    obtain ⟨j, odd_eq⟩ := odd_power
    have power_eq :
        base ^ (2 ^ (tail + 1)) = (2 * j + 1) ^ 2 := by
      calc
        base ^ (2 ^ (tail + 1)) = base ^ (2 ^ tail * 2) := by rw [pow_succ]
        _ = (base ^ (2 ^ tail)) ^ 2 := by rw [pow_mul]
        _ = (2 * j + 1) ^ 2 := by rw [odd_eq]
    rw [power_eq, show (2 * j + 1) ^ 2 = 4 * (j ^ 2 + j) + 1 by ring]
    simp [Nat.add_mod]
  have value_mod_four : (2 ^ k) % 4 = 2 := by
    rw [← value_eq]
    omega
  have k_le_one : k ≤ 1 := by
    by_contra k_gt
    have two_le_k : 2 ≤ k := by omega
    obtain ⟨j, k_eq⟩ := Nat.exists_eq_add_of_le two_le_k
    rw [k_eq, pow_add] at value_mod_four
    norm_num at value_mod_four
  omega

/-- Above exponent two, absence of a primitive divisor forces the cyclotomic value to equal
one prime divisor of the exponent. -/
theorem cyclotomicValue_eq_prime_of_no_primitive
    {base exponent : Nat} (base_gt_one : 1 < base) (exponent_gt_two : 2 < exponent)
    (no_primitive : ∀ prime, ¬IsPrimitivePrimeDivisor prime base exponent) :
    ∃ prime : Nat, prime.Prime ∧ prime ∣ exponent ∧
      cyclotomicValue base exponent = prime ∧
      ∀ other : Nat, other.Prime → other ∣ exponent → other ≠ prime → other < prime := by
  obtain ⟨prime, k, prime_spec, k_positive, prime_dvd_exponent, value_eq, other_lt⟩ :=
    cyclotomicValue_structure_of_no_primitive base_gt_one (by omega) no_primitive
  have k_eq : k = 1 := by
    by_cases prime_two : prime = 2
    · subst prime
      exact cyclotomicValue_primePower_exponent_one_of_two exponent_gt_two
        prime_dvd_exponent k_positive value_eq other_lt
    · exact cyclotomicValue_primePower_exponent_one_of_odd prime_spec
        (prime_spec.odd_of_ne_two prime_two) base_gt_one (by omega) prime_dvd_exponent
        k_positive value_eq
  refine ⟨prime, prime_spec, prime_dvd_exponent, ?_, other_lt⟩
  simpa [k_eq] using value_eq

/-- Bang's theorem when `base - 1 > 1`: every exponent above two has a primitive prime
divisor. -/
theorem exists_primitivePrimeDivisor_of_base_gt_two
    {base exponent : Nat} (base_gt_two : 2 < base) (exponent_gt_two : 2 < exponent) :
    ∃ prime : Nat, IsPrimitivePrimeDivisor prime base exponent := by
  by_contra none
  push_neg at none
  obtain ⟨prime, prime_spec, prime_dvd_exponent, value_eq, _⟩ :=
    cyclotomicValue_eq_prime_of_no_primitive (by omega) exponent_gt_two none
  have totient_positive : 0 < exponent.totient :=
    Nat.totient_pos.mpr (by omega)
  have totient_divides : prime - 1 ∣ exponent.totient := by
    rw [← Nat.totient_prime prime_spec]
    exact Nat.totient_dvd_of_dvd prime_dvd_exponent
  have prime_pred_le_totient : prime - 1 ≤ exponent.totient :=
    Nat.le_of_dvd totient_positive totient_divides
  have prime_le_two_pow : prime ≤ 2 ^ (prime - 1) := by
    have strict := Nat.lt_two_pow (prime - 1)
    have recover : prime - 1 + 1 = prime := Nat.sub_add_cancel prime_spec.one_le
    omega
  have two_pow_le : 2 ^ (prime - 1) ≤ 2 ^ exponent.totient :=
    Nat.pow_le_pow_right (by decide) prime_pred_le_totient
  have base_pred_ge_two : 2 ≤ base - 1 := by omega
  have lower_ge : prime ≤ (base - 1) ^ exponent.totient :=
    prime_le_two_pow.trans <| two_pow_le.trans <|
      Nat.pow_le_pow_left base_pred_ge_two exponent.totient
  have lower_lt : (base - 1) ^ exponent.totient < cyclotomicValue base exponent :=
    Polynomial.sub_one_pow_totient_lt_natAbs_cyclotomic_eval
      (by omega) (by omega)
  rw [value_eq] at lower_lt
  omega

/-- Iterated cyclotomic expansion moves a prime-power factor of the index into the
evaluation point. -/
theorem eval_cyclotomic_prime_pow_mul
    {R : Type*} [CommRing R] (prime : Nat) (prime_spec : prime.Prime)
    (core power : Nat) (x : R) :
    eval x (cyclotomic (prime ^ (power + 1) * core) R) =
      eval (x ^ (prime ^ power)) (cyclotomic (prime * core) R) := by
  induction power generalizing x with
  | zero => simp
  | succ power induction =>
      have prime_dvd : prime ∣ prime ^ (power + 1) * core :=
        dvd_mul_of_dvd_left (dvd_pow_self prime (by omega)) core
      have expand_eq := cyclotomic_expand_eq_cyclotomic prime_spec prime_dvd R
      have evaluated := congrArg (eval x) expand_eq
      rw [expand_eval] at evaluated
      calc
        eval x (cyclotomic (prime ^ (Nat.succ power + 1) * core) R) =
            eval x (cyclotomic ((prime ^ (power + 1) * core) * prime) R) := by
              congr 2
              rw [pow_succ]
              ring
        _ = eval (x ^ prime) (cyclotomic (prime ^ (power + 1) * core) R) :=
          evaluated.symm
        _ = eval ((x ^ prime) ^ (prime ^ power)) (cyclotomic (prime * core) R) :=
          induction (x ^ prime)
        _ = eval (x ^ (prime ^ (Nat.succ power)))
              (cyclotomic (prime * core) R) := by
          apply congrArg (fun z => eval z (cyclotomic (prime * core) R))
          rw [← pow_mul, pow_succ]
          congr 1
          exact Nat.mul_comm prime (prime ^ power)

/-- Integral specialization of iterated cyclotomic expansion. -/
theorem cyclotomicValue_prime_pow_mul
    (base prime core power : Nat) (prime_spec : prime.Prime) :
    cyclotomicValue base (prime ^ (power + 1) * core) =
      cyclotomicValue (base ^ (prime ^ power)) (prime * core) := by
  unfold cyclotomicValue
  rw [eval_cyclotomic_prime_pow_mul prime prime_spec core power (base : ℤ)]
  norm_cast

/-- A cyclotomic prime factor's prime-free exponent part is strictly smaller than the
factor. -/
theorem ord_compl_lt_of_prime_dvd_cyclotomicValue
    {prime base exponent : Nat} (prime_spec : prime.Prime)
    (exponent_positive : 0 < exponent)
    (prime_dvd_value : prime ∣ cyclotomicValue base exponent) :
    ord_compl[prime] exponent < prime := by
  letI : Fact prime.Prime := ⟨prime_spec⟩
  let core := ord_compl[prime] exponent
  have root : IsPrimitiveRoot (base : ZMod prime) core :=
    isPrimitiveRoot_ordCompl_of_prime_dvd_cyclotomicValue
      prime_spec exponent_positive prime_dvd_value
  have core_positive : 0 < core :=
    Nat.ord_compl_pos prime exponent_positive.ne'
  have base_nonzero : (base : ZMod prime) ≠ 0 :=
    root.ne_zero core_positive.ne'
  have core_dvd_pred : core ∣ prime - 1 := by
    rw [root.eq_orderOf]
    exact ZMod.orderOf_dvd_card_sub_one base_nonzero
  have prime_two : 2 ≤ prime := prime_spec.two_le
  have core_le : core ≤ prime - 1 :=
    Nat.le_of_dvd (by omega : 0 < prime - 1) core_dvd_pred
  omega

/-- If `Φₙ(2)` equals a prime dividing `n`, that prime occurs only once in `n`. -/
theorem factorization_eq_one_of_cyclotomicValue_two_eq_prime
    {prime exponent : Nat} (prime_spec : prime.Prime) (exponent_gt_two : 2 < exponent)
    (prime_dvd_exponent : prime ∣ exponent)
    (value_eq : cyclotomicValue 2 exponent = prime) :
    exponent.factorization prime = 1 := by
  let power := exponent.factorization prime
  let core := ord_compl[prime] exponent
  have exponent_positive : 0 < exponent := by omega
  have power_positive : 0 < power :=
    prime_spec.factorization_pos_of_dvd exponent_positive.ne' prime_dvd_exponent
  have decomposition : prime ^ power * core = exponent :=
    Nat.ord_proj_mul_ord_compl_eq_self exponent prime
  have core_positive : 0 < core :=
    Nat.ord_compl_pos prime exponent_positive.ne'
  apply le_antisymm ?_ (by omega)
  by_contra power_not_le
  have power_at_least_two : 2 ≤ power := by omega
  obtain ⟨extra, power_eq⟩ := Nat.exists_eq_add_of_le power_at_least_two
  have shifted_value :
      cyclotomicValue 2 exponent =
        cyclotomicValue (2 ^ (prime ^ (extra + 1))) (prime * core) := by
    calc
      cyclotomicValue 2 exponent =
          cyclotomicValue 2 (prime ^ (extra + 1 + 1) * core) := by
            congr 2
            rw [← decomposition, power_eq]
            rw [show extra + 1 + 1 = 2 + extra by omega]
      _ = cyclotomicValue (2 ^ (prime ^ (extra + 1))) (prime * core) :=
        cyclotomicValue_prime_pow_mul 2 prime core (extra + 1) prime_spec
  let shiftedBase := 2 ^ (prime ^ (extra + 1))
  have prime_le_power : prime ≤ prime ^ (extra + 1) :=
    Nat.le_self_pow (by omega) prime
  have prime_lt_shifted : prime < shiftedBase :=
    (Nat.lt_two_pow prime).trans_le
      (Nat.pow_le_pow_right (by decide) prime_le_power)
  have shifted_gt_one : 1 < shiftedBase :=
    lt_trans prime_spec.one_lt prime_lt_shifted
  have index_gt_one : 1 < prime * core := by
    nlinarith [prime_spec.two_le]
  have totient_positive : 0 < (prime * core).totient :=
    Nat.totient_pos.mpr (mul_pos prime_spec.pos core_positive)
  have lower_ge : prime ≤ (shiftedBase - 1) ^ (prime * core).totient := by
    have prime_le_pred : prime ≤ shiftedBase - 1 := by omega
    exact prime_le_pred.trans
      (Nat.le_self_pow totient_positive.ne' (shiftedBase - 1))
  have lower_lt :
      (shiftedBase - 1) ^ (prime * core).totient <
        cyclotomicValue shiftedBase (prime * core) :=
    Polynomial.sub_one_pow_totient_lt_natAbs_cyclotomic_eval
      index_gt_one shifted_gt_one.ne'
  rw [← shifted_value, value_eq] at lower_lt
  omega

/-- Cyclotomic expansion evaluated in absolute value. -/
theorem cyclotomicValue_expand_mul
    (base prime core : Nat) (prime_spec : prime.Prime) (not_dvd : ¬prime ∣ core) :
    cyclotomicValue (base ^ prime) core =
      cyclotomicValue base (core * prime) * cyclotomicValue base core := by
  have polynomial := cyclotomic_expand_eq_cyclotomic_mul prime_spec not_dvd ℤ
  have evaluated := congrArg (eval (base : ℤ)) polynomial
  rw [expand_eval, eval_mul] at evaluated
  unfold cyclotomicValue
  rw [show ((base ^ prime : Nat) : ℤ) = (base : ℤ) ^ prime by norm_cast]
  change
    (eval ((base : ℤ) ^ prime) (cyclotomic core ℤ)).natAbs =
      (eval (base : ℤ) (cyclotomic (core * prime) ℤ)).natAbs *
        (eval (base : ℤ) (cyclotomic core ℤ)).natAbs
  rw [evaluated, Int.natAbs_mul]

/-- Real casting removes the absolute value from a positive integral cyclotomic
evaluation. -/
theorem cast_cyclotomicValue_real
    {base exponent : Nat} (base_gt_one : 1 < base) :
    (cyclotomicValue base exponent : ℝ) =
      eval (base : ℝ) (cyclotomic exponent ℝ) := by
  have integer_positive :
      0 < eval (base : ℤ) (cyclotomic exponent ℤ) :=
    Polynomial.cyclotomic_pos' exponent (by exact_mod_cast base_gt_one)
  rw [cyclotomicValue]
  calc
    ((eval (base : ℤ) (cyclotomic exponent ℤ)).natAbs : ℝ) =
        ((eval (base : ℤ) (cyclotomic exponent ℤ) : ℤ) : ℝ) := by
          rw [Int.cast_natAbs, abs_of_pos integer_positive]
    _ = eval (base : ℝ) (cyclotomic exponent ℝ) := by
      simpa using
        (cyclotomic.eval_apply (base : ℤ) exponent (algebraMap ℤ ℝ)).symm

/-- Upper cyclotomic evaluation bound over naturals. -/
theorem cyclotomicValue_le_add_one_pow_totient
    {base exponent : Nat} (base_gt_one : 1 < base) :
    cyclotomicValue base exponent ≤ (base + 1) ^ exponent.totient := by
  have upper := Polynomial.cyclotomic_eval_le_add_one_pow_totient
    (n := exponent) (q := (base : ℝ)) (by exact_mod_cast base_gt_one)
  rw [← cast_cyclotomicValue_real base_gt_one] at upper
  exact_mod_cast upper

/-- Lower cyclotomic evaluation bound over naturals. -/
theorem sub_one_pow_totient_le_cyclotomicValue
    {base exponent : Nat} (base_gt_one : 1 < base) :
    (base - 1) ^ exponent.totient ≤ cyclotomicValue base exponent := by
  have lower := Polynomial.sub_one_pow_totient_le_cyclotomic_eval
    (n := exponent) (q := (base : ℝ)) (by exact_mod_cast base_gt_one)
  rw [← cast_cyclotomicValue_real base_gt_one] at lower
  have cast_sub : ((base - 1 : Nat) : ℝ) = (base : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [← cast_sub] at lower
  exact_mod_cast lower

/-- Elementary growth bound used in Bang's unit-gap case. -/
theorem three_mul_add_one_lt_two_pow {n : Nat} (at_least_four : 4 ≤ n) :
    3 * n + 1 < 2 ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le at_least_four
  induction k with
  | zero => norm_num
  | succ k induction =>
      rw [show 4 + (k + 1) = (4 + k) + 1 by omega, pow_succ]
      nlinarith [induction (by omega), show 0 < 2 ^ (4 + k) by positivity]

/-- If `Φₙ(2)` is a nonprimitive prime factor of `n`, that prime is at most `3`. -/
theorem nonprimitive_cyclotomic_prime_le_three_at_two
    {prime exponent : Nat} (prime_spec : prime.Prime) (exponent_gt_two : 2 < exponent)
    (prime_dvd_exponent : prime ∣ exponent)
    (value_eq : cyclotomicValue 2 exponent = prime) :
    prime ≤ 3 := by
  let core := ord_compl[prime] exponent
  have exponent_positive : 0 < exponent := by omega
  have factorization_eq :=
    factorization_eq_one_of_cyclotomicValue_two_eq_prime
      prime_spec exponent_gt_two prime_dvd_exponent value_eq
  have decomposition : prime * core = exponent := by
    have full := Nat.ord_proj_mul_ord_compl_eq_self exponent prime
    rw [factorization_eq, pow_one] at full
    dsimp [core]
    rw [factorization_eq, pow_one]
    exact full
  have core_positive : 0 < core :=
    Nat.ord_compl_pos prime exponent_positive.ne'
  have core_not_dvd : ¬prime ∣ core :=
    Nat.not_dvd_ord_compl prime_spec exponent_positive.ne'
  have expanded :=
    cyclotomicValue_expand_mul 2 prime core prime_spec core_not_dvd
  have index_eq : core * prime = exponent := by rw [mul_comm, decomposition]
  rw [index_eq, value_eq] at expanded
  by_contra prime_not_le
  have prime_at_least_four : 4 ≤ prime := by omega
  let shiftedBase := 2 ^ prime
  have shifted_gt_one : 1 < shiftedBase :=
    one_lt_pow (by decide : (1 : Nat) < 2) prime_spec.ne_zero
  have totient_positive : 0 < core.totient :=
    Nat.totient_pos.mpr core_positive
  have lower_le :
      (shiftedBase - 1) ^ core.totient ≤ cyclotomicValue shiftedBase core :=
    sub_one_pow_totient_le_cyclotomicValue shifted_gt_one
  have upper_le : cyclotomicValue 2 core ≤ 3 ^ core.totient := by
    simpa using cyclotomicValue_le_add_one_pow_totient
      (base := 2) (exponent := core) (by decide)
  have base_strict : 3 * prime < shiftedBase - 1 := by
    have := three_mul_add_one_lt_two_pow (n := prime) prime_at_least_four
    dsimp [shiftedBase]
    omega
  have product_lt :
      prime * cyclotomicValue 2 core <
        (shiftedBase - 1) ^ core.totient := by
    calc
      prime * cyclotomicValue 2 core ≤ prime * 3 ^ core.totient :=
        Nat.mul_le_mul_left prime upper_le
      _ ≤ prime ^ core.totient * 3 ^ core.totient := by
        exact Nat.mul_le_mul_right (3 ^ core.totient)
          (Nat.le_self_pow totient_positive.ne' prime)
      _ = (3 * prime) ^ core.totient := by rw [mul_pow]; ring
      _ < (shiftedBase - 1) ^ core.totient :=
        Nat.pow_lt_pow_left base_strict totient_positive.ne'
  rw [expanded] at lower_le
  omega

/-- Bang's unit-gap case at base `2`: exponent `6` is the only exception above exponent
two. -/
theorem exists_primitivePrimeDivisor_two
    {exponent : Nat} (exponent_gt_two : 2 < exponent) (not_six : exponent ≠ 6) :
    ∃ prime : Nat, IsPrimitivePrimeDivisor prime 2 exponent := by
  by_contra none
  push_neg at none
  obtain ⟨prime, prime_spec, prime_dvd_exponent, value_eq, _⟩ :=
    cyclotomicValue_eq_prime_of_no_primitive (by decide) exponent_gt_two none
  have exponent_positive : 0 < exponent := by omega
  have prime_dvd_value : prime ∣ cyclotomicValue 2 exponent := by rw [value_eq]
  have prime_ne_two : prime ≠ 2 := by
    intro prime_two
    have coprime := coprime_of_prime_dvd_cyclotomicValue
      prime_spec exponent_positive prime_dvd_value
    rw [prime_two] at coprime
    norm_num at coprime
  have prime_le_three := nonprimitive_cyclotomic_prime_le_three_at_two
    prime_spec exponent_gt_two prime_dvd_exponent value_eq
  have prime_eq : prime = 3 := by
    have prime_two := prime_spec.two_le
    omega
  have factorization_eq :=
    factorization_eq_one_of_cyclotomicValue_two_eq_prime
      prime_spec exponent_gt_two prime_dvd_exponent value_eq
  let core := ord_compl[prime] exponent
  have decomposition : prime * core = exponent := by
    have full := Nat.ord_proj_mul_ord_compl_eq_self exponent prime
    rw [factorization_eq, pow_one] at full
    dsimp [core]
    rw [factorization_eq, pow_one]
    exact full
  have core_positive : 0 < core :=
    Nat.ord_compl_pos prime exponent_positive.ne'
  have core_lt : core < prime :=
    ord_compl_lt_of_prime_dvd_cyclotomicValue
      prime_spec exponent_positive prime_dvd_value
  have core_cases : core = 1 ∨ core = 2 := by omega
  rcases core_cases with core_one | core_two
  · have exponent_eq : exponent = 3 := by
      rw [← decomposition, prime_eq, core_one]
    rw [exponent_eq, prime_eq] at value_eq
    have computed : cyclotomicValue 2 3 = 7 := by
      norm_num [cyclotomicValue, cyclotomic_prime, Finset.sum_range_succ]
    rw [computed] at value_eq
    omega
  · apply not_six
    rw [← decomposition, prime_eq, core_two]

/-- Bang–Zsigmondy above exponent two. The sole exception is `2⁶ - 1`; the separate
exponent-two exceptions are outside this theorem's range. -/
theorem exists_primitivePrimeDivisor
    {base exponent : Nat} (base_gt_one : 1 < base) (exponent_gt_two : 2 < exponent)
    (not_exception : base ≠ 2 ∨ exponent ≠ 6) :
    ∃ prime : Nat, IsPrimitivePrimeDivisor prime base exponent := by
  by_cases base_two : base = 2
  · subst base
    exact exists_primitivePrimeDivisor_two exponent_gt_two
      (not_exception.resolve_left (by simp))
  · exact exists_primitivePrimeDivisor_of_base_gt_two
      (lt_of_le_of_ne (by omega) (Ne.symm base_two)) exponent_gt_two

end

end MatrixMortality
