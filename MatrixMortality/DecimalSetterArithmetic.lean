import MatrixMortality.PadicValuation
import Mathlib.Tactic

/-!
# Decimal carry arithmetic for the five-state setter

The decimal setter's negative J-fraction transfer has an integral two-coordinate lift.  This
file isolates its centered recurrence and the coupled `2`/`5`-adic shells forced by the final
decimal digits of a block.  The results are arithmetic interfaces; they do not prove that every
malformed setter orbit avoids every pole.
-/

namespace MatrixMortality.DecimalSetterArithmetic

open MatrixMortality.PadicValuation

private instance factPrimeFive : Fact (Nat.Prime 5) :=
  ⟨by norm_num⟩

/-- Simultaneous finite valuations at the two prime factors of ten. -/
def HasDecimalShell (value : ℚ) (twoValue fiveValue : ℤ) : Prop :=
  HasValue 2 value twoValue ∧ HasValue 5 value fiveValue

private theorem hasValue_pow
    {prime : Nat} [Fact prime.Prime] {value : ℚ} {valuation : ℤ}
    (value_shell : HasValue prime value valuation) (exponent : Nat) :
    HasValue prime (value ^ exponent) (exponent * valuation) :=
  ⟨pow_ne_zero exponent value_shell.1, by
    rw [padicValRat.pow, value_shell.2]⟩

/-- Decimal shells add under multiplication. -/
theorem HasDecimalShell.mul
    {left right : ℚ} {leftTwo leftFive rightTwo rightFive : ℤ}
    (left_shell : HasDecimalShell left leftTwo leftFive)
    (right_shell : HasDecimalShell right rightTwo rightFive) :
    HasDecimalShell (left * right) (leftTwo + rightTwo) (leftFive + rightFive) :=
  ⟨mul_hasValue left_shell.1 right_shell.1,
    mul_hasValue left_shell.2 right_shell.2⟩

/-- Decimal shells scale under natural powers. -/
theorem HasDecimalShell.pow
    {value : ℚ} {twoValue fiveValue : ℤ}
    (value_shell : HasDecimalShell value twoValue fiveValue) (exponent : Nat) :
    HasDecimalShell (value ^ exponent) (exponent * twoValue) (exponent * fiveValue) :=
  ⟨hasValue_pow value_shell.1 exponent, hasValue_pow value_shell.2 exponent⟩

private theorem two_hasDecimalShell : HasDecimalShell 2 1 0 := by
  refine ⟨?_, intCast_isUnit_of_not_dvd (by norm_num)⟩
  simpa using (primePower_hasValue (prime := 2) 1)

private theorem five_hasDecimalShell : HasDecimalShell 5 0 1 := by
  refine ⟨intCast_isUnit_of_not_dvd (by norm_num), ?_⟩
  simpa using (primePower_hasValue (prime := 5) 1)

/-- Ten has valuation one at both of its prime factors. -/
theorem ten_hasDecimalShell : HasDecimalShell 10 1 1 := by
  convert two_hasDecimalShell.mul five_hasDecimalShell using 1 <;> norm_num

private theorem integerUnit_hasDecimalShell
    {unit : ℤ} (unit_two : ¬(2 : ℤ) ∣ unit) (unit_five : ¬(5 : ℤ) ∣ unit) :
    HasDecimalShell unit 0 0 :=
  ⟨intCast_isUnit_of_not_dvd unit_two, intCast_isUnit_of_not_dvd unit_five⟩

/-- An integer ending in decimal digit seven is a unit at both prime factors of ten. -/
theorem intCast_hasDecimalShell_of_mod_seven
    {value : ℤ} (value_mod : value ≡ 7 [ZMOD 10]) :
    HasDecimalShell (value : ℚ) 0 0 := by
  rw [Int.modEq_iff_dvd] at value_mod
  obtain ⟨carry, carry_eq⟩ := value_mod
  have value_eq : value = 7 - 10 * carry := by omega
  apply integerUnit_hasDecimalShell
  · rw [value_eq]
    rintro ⟨quotient, quotient_eq⟩
    omega
  · rw [value_eq]
    rintro ⟨quotient, quotient_eq⟩
    omega

/-- An integer ending in decimal digit three is a unit at both prime factors of ten. -/
theorem intCast_hasDecimalShell_of_mod_three
    {value : ℤ} (value_mod : value ≡ 3 [ZMOD 10]) :
    HasDecimalShell (value : ℚ) 0 0 := by
  rw [Int.modEq_iff_dvd] at value_mod
  obtain ⟨carry, carry_eq⟩ := value_mod
  have value_eq : value = 3 - 10 * carry := by omega
  apply integerUnit_hasDecimalShell
  · rw [value_eq]
    rintro ⟨quotient, quotient_eq⟩
    omega
  · rw [value_eq]
    rintro ⟨quotient, quotient_eq⟩
    omega

private theorem modEq_ten_hasDecimalShell
    {value : ℤ} (value_mod : value ≡ 10 [ZMOD 100]) :
    HasDecimalShell value 1 1 := by
  rw [Int.modEq_iff_dvd] at value_mod
  obtain ⟨carry, carry_eq⟩ := value_mod
  have value_eq : value = 10 * (1 - 10 * carry) := by omega
  have unit_two : ¬(2 : ℤ) ∣ 1 - 10 * carry := by
    rintro ⟨quotient, quotient_eq⟩
    omega
  have unit_five : ¬(5 : ℤ) ∣ 1 - 10 * carry := by
    rintro ⟨quotient, quotient_eq⟩
    omega
  rw [value_eq, Int.cast_mul]
  exact ten_hasDecimalShell.mul (integerUnit_hasDecimalShell unit_two unit_five)

/-- Numerator of the sum `P/(μA) + (G/E)V/(μA)`. -/
def transferTrace {R : Type*} [CommRing R] (E G P V : R) : R :=
  E * P + G * V

/-- Numerator of one lifted J-fraction step on the homogeneous state `t=X/Y`. -/
def nextNumerator {R : Type*} [CommRing R]
    (E G P V X Y : R) : R :=
  transferTrace E G P V * X - G * V * Y

/-- Denominator of one lifted J-fraction step on the homogeneous state `t=X/Y`. -/
def nextDenominator {R : Type*} [CommRing R]
    (E μ A X : R) : R :=
  E * μ * A * X

/-- Replacing `Y` by the centered defect `Δ=Y-X` removes the transfer trace. -/
theorem nextNumerator_centered
    {R : Type*} [CommRing R] (E G P V X Δ : R) :
    nextNumerator E G P V X (X + Δ) = E * P * X - G * V * Δ := by
  simp [nextNumerator, transferTrace]
  ring

/-- The next centered defect has the same two coefficients as the next numerator. -/
theorem nextDefect_centered
    {R : Type*} [CommRing R] (E G μ A P V X Δ : R) :
    nextDenominator E μ A X - nextNumerator E G P V X (X + Δ) =
      E * (μ * A - P) * X + G * V * Δ := by
  simp [nextDenominator, nextNumerator, transferTrace]
  ring

/-- A centered step conserves the prescribed next denominator. -/
theorem centered_sum
    {R : Type*} [CommRing R] (E G μ A P V X Δ : R) :
    (E * P * X - G * V * Δ) +
        (E * (μ * A - P) * X + G * V * Δ) =
      E * μ * A * X := by
  ring

/-- At the distinguished centered reset `(X,Δ)=(G,E)`, a pole is exactly `P=V`. -/
theorem distinguished_pole_iff
    {R : Type*} [CommRing R] [NoZeroDivisors R]
    {E G P V : R} (E_ne : E ≠ 0) (G_ne : G ≠ 0) :
    E * P * G - G * V * E = 0 ↔ P = V := by
  rw [show E * P * G - G * V * E = E * G * (P - V) by ring]
  simp [E_ne, G_ne, sub_eq_zero]

/-- The centered projective coordinate `Z=(G/E)Δ/X`. -/
def centeredCoordinate {K : Type*} [Field K] (E G X Δ : K) : K :=
  G * Δ / (E * X)

/-- The ordinary and distinguished reset pairs have centered coordinates zero and one. -/
theorem centeredCoordinate_resets
    {K : Type*} [Field K] {E G : K} (E_ne : E ≠ 0) (G_ne : G ≠ 0) :
    centeredCoordinate E G 1 0 = 0 ∧ centeredCoordinate E G G E = 1 := by
  constructor
  · simp [centeredCoordinate]
  · simp [centeredCoordinate, E_ne, G_ne, mul_comm]

/-- A centered pole is the exact correspondence ratio `Z=P/V`. -/
theorem centered_pole_iff
    {K : Type*} [Field K] {E G P V X Δ : K}
    (E_ne : E ≠ 0) (X_ne : X ≠ 0) :
    E * P * X - G * V * Δ = 0 ↔ P = V * centeredCoordinate E G X Δ := by
  rw [centeredCoordinate,
    show V * (G * Δ / (E * X)) = V * G * Δ / (E * X) by ring,
    eq_div_iff (mul_ne_zero E_ne X_ne)]
  constructor <;> intro equality <;> linear_combination equality

/-- Exact centered Möbius recurrence away from its next pole. -/
theorem centeredCoordinate_step
    {K : Type*} [Field K] {E G μ A P V X Δ : K}
    (E_ne : E ≠ 0) (X_ne : X ≠ 0)
    (pole_ne : P - V * centeredCoordinate E G X Δ ≠ 0) :
    centeredCoordinate E G
        (E * P * X - G * V * Δ)
        (E * (μ * A - P) * X + G * V * Δ) =
      (G / E) *
        (μ * A - P + V * centeredCoordinate E G X Δ) /
          (P - V * centeredCoordinate E G X Δ) := by
  let Z := centeredCoordinate E G X Δ
  have G_mul_delta : G * Δ = E * X * Z := by
    dsimp [Z, centeredCoordinate]
    field_simp [E_ne, X_ne]
  have next_numerator :
      E * P * X - G * V * Δ = E * X * (P - V * Z) := by
    rw [show G * V * Δ = V * (G * Δ) by ring, G_mul_delta]
    ring
  have next_defect :
      E * (μ * A - P) * X + G * V * Δ =
        E * X * (μ * A - P + V * Z) := by
    rw [show G * V * Δ = V * (G * Δ) by ring, G_mul_delta]
    ring
  have next_numerator_ne : E * P * X - G * V * Δ ≠ 0 := by
    rw [next_numerator]
    exact mul_ne_zero (mul_ne_zero E_ne X_ne) pole_ne
  rw [next_numerator, next_defect]
  dsimp [Z] at pole_ne ⊢
  unfold centeredCoordinate
  field_simp [E_ne, X_ne, next_numerator_ne, pole_ne]

/-- Reciprocal carry coordinate `W=GY/X`; in centered coordinates, `W=EZ+G`. -/
def reciprocalCoordinate {K : Type*} [Field K] (G X Y : K) : K :=
  G * Y / X

/-- The reciprocal and centered carry charts agree exactly. -/
theorem reciprocalCoordinate_eq_centered
    {K : Type*} [Field K] {E G X Δ : K}
    (E_ne : E ≠ 0) (X_ne : X ≠ 0) :
    reciprocalCoordinate G X (X + Δ) =
      E * centeredCoordinate E G X Δ + G := by
  unfold reciprocalCoordinate centeredCoordinate
  field_simp [E_ne, X_ne]
  ring

/-- In the reciprocal chart a pole is the trace ratio `W=T/V`. -/
theorem reciprocal_pole_iff
    {K : Type*} [Field K] {E G P V X Y : K} (X_ne : X ≠ 0) :
    nextNumerator E G P V X Y = 0 ↔
      transferTrace E G P V = V * reciprocalCoordinate G X Y := by
  rw [reciprocalCoordinate,
    show V * (G * Y / X) = V * G * Y / X by ring, eq_div_iff X_ne]
  unfold nextNumerator
  constructor <;> intro equality <;> linear_combination equality

/-- Every nonpole step is the reciprocal recurrence
`W′=EGμA/(T−VW)`. -/
theorem reciprocalCoordinate_step
    {K : Type*} [Field K] {E G μ A P V X Y : K}
    (X_ne : X ≠ 0) (next_ne : nextNumerator E G P V X Y ≠ 0) :
    reciprocalCoordinate G
        (nextNumerator E G P V X Y) (nextDenominator E μ A X) =
      E * G * μ * A /
        (transferTrace E G P V - V * reciprocalCoordinate G X Y) := by
  have denominator_ne :
      transferTrace E G P V - V * reciprocalCoordinate G X Y ≠ 0 := by
    intro denominator_zero
    apply next_ne
    unfold reciprocalCoordinate at denominator_zero
    unfold nextNumerator
    field_simp [X_ne] at denominator_zero
    linear_combination denominator_zero
  unfold reciprocalCoordinate nextNumerator nextDenominator
  field_simp [X_ne, next_ne, denominator_ne]

/-- If one centered step is followed by a pole, its trace absorbs the entire decimal scale. -/
theorem successive_pole_identity
    {R : Type*} [CommRing R] {E G μ A P V X₀ X₁ Δ₁ : R}
    (previous_sum : X₁ + Δ₁ = E * μ * A * X₀)
    (next_pole : E * P * X₁ = G * V * Δ₁) :
    transferTrace E G P V * X₁ = E * G * μ * V * A * X₀ := by
  calc
    transferTrace E G P V * X₁ = G * V * (X₁ + Δ₁) := by
      rw [transferTrace]
      linear_combination next_pole
    _ = E * G * μ * V * A * X₀ := by rw [previous_sum]; ring

/-- A prospective pole balances each target trace valuation against the preceding decimal
scale. -/
theorem successive_pole_shellBalance
    {E G μ P V X₀ X₁ Δ₁ : ℚ} {m : Nat}
    {targetTwo targetFive sourceTwo sourceFive nextTwo nextFive : ℤ}
    (E_unit : HasDecimalShell E 0 0)
    (G_unit : HasDecimalShell G 0 0)
    (μ_unit : HasDecimalShell μ 0 0)
    (V_unit : HasDecimalShell V 0 0)
    (target_shell : HasDecimalShell (transferTrace E G P V) targetTwo targetFive)
    (source_shell : HasDecimalShell X₀ sourceTwo sourceFive)
    (next_shell : HasDecimalShell X₁ nextTwo nextFive)
    (previous_sum : X₁ + Δ₁ = E * μ * 10 ^ m * X₀)
    (next_pole : E * P * X₁ = G * V * Δ₁) :
    targetTwo + nextTwo = m + sourceTwo ∧
      targetFive + nextFive = m + sourceFive := by
  have identity :
      transferTrace E G P V * X₁ = E * G * μ * V * 10 ^ m * X₀ :=
    successive_pole_identity previous_sum next_pole
  have scale_shell : HasDecimalShell ((10 : ℚ) ^ m) m m := by
    simpa using ten_hasDecimalShell.pow m
  have coefficient_shell : HasDecimalShell (E * G * μ * V) 0 0 := by
    simpa only [zero_add] using ((E_unit.mul G_unit).mul μ_unit).mul V_unit
  have left_shell := target_shell.mul next_shell
  have right_shell := (coefficient_shell.mul scale_shell).mul source_shell
  constructor
  · calc
      targetTwo + nextTwo = padicValRat 2 (transferTrace E G P V * X₁) :=
        left_shell.1.2.symm
      _ = padicValRat 2 (E * G * μ * V * 10 ^ m * X₀) := congrArg _ identity
      _ = m + sourceTwo := by
        simpa only [zero_add] using right_shell.1.2
  · calc
      targetFive + nextFive = padicValRat 5 (transferTrace E G P V * X₁) :=
        left_shell.2.2.symm
      _ = padicValRat 5 (E * G * μ * V * 10 ^ m * X₀) := congrArg _ identity
      _ = m + sourceFive := by
        simpa only [zero_add] using right_shell.2.2

/-- Consequently the `5`-minus-`2` valuation gap shifts by the target shell imbalance. -/
theorem successive_pole_gapShift
    {targetTwo targetFive sourceTwo sourceFive nextTwo nextFive m : ℤ}
    (two_balance : targetTwo + nextTwo = m + sourceTwo)
    (five_balance : targetFive + nextFive = m + sourceFive) :
    (nextFive - nextTwo) - (sourceFive - sourceTwo) = targetTwo - targetFive := by
  omega

/-- The decimal setter's two integral scaling numerators. -/
def decimalGap (ρ : ℤ) : ℤ := 9 * (2 * ρ - 7)

/-- Numerator of the decimal setter's projective shift. -/
def decimalLift (ρ : ℤ) : ℤ := 502 * ρ - 7

/-- The setter calibration gives `G+E=90μ`. -/
theorem decimalLift_add_gap
    {ρ μ : ℤ} (marker_relation : 9 * μ + 7 = 52 * ρ) :
    decimalLift ρ + decimalGap ρ = 90 * μ := by
  simp [decimalLift, decimalGap]
  linarith

/-- Any multi-role erasure target lies in the simultaneous shell `(1,1)`.  The hypotheses are
exactly its last two decimal digits: `ρ≡0`, `P≡77`, and `V≡77` modulo `100`. -/
theorem multiErasure_trace_hasDecimalShell
    {ρ P V : ℤ}
    (ρ_mod : ρ ≡ 0 [ZMOD 100])
    (P_mod : P ≡ 77 [ZMOD 100])
    (V_mod : V ≡ 77 [ZMOD 100]) :
    HasDecimalShell (transferTrace (decimalGap ρ) (decimalLift ρ) P V) 1 1 := by
  have gap_mod : decimalGap ρ ≡ 37 [ZMOD 100] := by
    have gap_eq : decimalGap ρ = ρ * 18 - 63 := by
      simp [decimalGap]
      ring
    calc
      decimalGap ρ = ρ * 18 - 63 := gap_eq
      _ ≡ -63 [ZMOD 100] := by
        simpa using (ρ_mod.mul (Int.ModEq.refl 18)).sub (Int.ModEq.refl 63)
      _ ≡ 37 [ZMOD 100] := by norm_num
  have lift_mod : decimalLift ρ ≡ 93 [ZMOD 100] := by
    have lift_eq : decimalLift ρ = ρ * 502 - 7 := by
      simp [decimalLift]
      ring
    calc
      decimalLift ρ = ρ * 502 - 7 := lift_eq
      _ ≡ -7 [ZMOD 100] := by
        simpa using (ρ_mod.mul (Int.ModEq.refl 502)).sub (Int.ModEq.refl 7)
      _ ≡ 93 [ZMOD 100] := by norm_num
  have integer_shell :
      HasDecimalShell
        ((transferTrace (decimalGap ρ) (decimalLift ρ) P V : ℤ) : ℚ) 1 1 :=
    modEq_ten_hasDecimalShell
      (((gap_mod.mul P_mod).add (lift_mod.mul V_mod)).trans (by norm_num))
  have cast_trace :
      ((transferTrace (decimalGap ρ) (decimalLift ρ) P V : ℤ) : ℚ) =
        transferTrace (decimalGap ρ : ℚ) (decimalLift ρ : ℚ) (P : ℚ) (V : ℚ) := by
    norm_num [transferTrace]
  rw [← cast_trace]
  exact integer_shell

/-- A closed trace `2·10^β·unit` with final unit digit three lies in shell `(β+1,β)`. -/
theorem singleErasure_trace_hasDecimalShell
    {β : Nat} {trace unit : ℤ}
    (trace_eq : trace = 2 * 10 ^ β * unit)
    (unit_mod : unit ≡ 3 [ZMOD 10]) :
    HasDecimalShell trace (β + 1) β := by
  rw [Int.modEq_iff_dvd] at unit_mod
  obtain ⟨carry, carry_eq⟩ := unit_mod
  have unit_eq : unit = 3 - 10 * carry := by omega
  have unit_two : ¬(2 : ℤ) ∣ unit := by
    rw [unit_eq]
    rintro ⟨quotient, quotient_eq⟩
    omega
  have unit_five : ¬(5 : ℤ) ∣ unit := by
    rw [unit_eq]
    rintro ⟨quotient, quotient_eq⟩
    omega
  have scale_shell : HasDecimalShell ((10 : ℚ) ^ β) β β := by
    simpa using ten_hasDecimalShell.pow β
  rw [trace_eq, Int.cast_mul, Int.cast_mul, Int.cast_pow]
  simpa [add_comm, add_left_comm, add_assoc] using
    (two_hasDecimalShell.mul scale_shell).mul
      (integerUnit_hasDecimalShell unit_two unit_five)

/-- The single `c` erasure has shell `(β+1,β)`. -/
theorem singleCErasure_trace_hasDecimalShell (β : Nat) (β_positive : 0 < β) :
    HasDecimalShell
      ((2 * 10 ^ β * (502 * 10 ^ β - 7) : ℤ) : ℚ) (β + 1) β := by
  apply singleErasure_trace_hasDecimalShell rfl
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt β_positive)
  have width_mod : (10 : ℤ) ^ offset.succ ≡ 0 [ZMOD 10] := by
    simpa [pow_succ] using
      (Int.ModEq.refl ((10 : ℤ) ^ offset)).mul
        (by norm_num : (10 : ℤ) ≡ 0 [ZMOD 10])
  simpa [mul_comm] using
    ((width_mod.mul (Int.ModEq.refl 502)).sub (Int.ModEq.refl 7)).trans
      (by norm_num : (-7 : ℤ) ≡ 3 [ZMOD 10])

/-- The single `b` erasure has the same shell `(β+1,β)`. -/
theorem singleBErasure_trace_hasDecimalShell (β : Nat) (β_positive : 0 < β) :
    HasDecimalShell
      ((2 * 10 ^ β *
        (5200 * (10 ^ β : ℤ) ^ 2 - 18398 * 10 ^ β + 2443) : ℤ) : ℚ)
        (β + 1) β := by
  apply singleErasure_trace_hasDecimalShell rfl
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt β_positive)
  have width_mod : (10 : ℤ) ^ offset.succ ≡ 0 [ZMOD 10] := by
    simpa [pow_succ] using
      (Int.ModEq.refl ((10 : ℤ) ^ offset)).mul
        (by norm_num : (10 : ℤ) ≡ 0 [ZMOD 10])
  have square_mod : ((10 : ℤ) ^ offset.succ) ^ 2 ≡ 0 [ZMOD 10] := by
    simpa [pow_two] using width_mod.mul width_mod
  simpa [mul_comm] using
    (((square_mod.mul (Int.ModEq.refl 5200)).sub
      (width_mod.mul (Int.ModEq.refl 18398))).add
        (Int.ModEq.refl 2443)).trans
          (by norm_num : (2443 : ℤ) ≡ 3 [ZMOD 10])

end MatrixMortality.DecimalSetterArithmetic
