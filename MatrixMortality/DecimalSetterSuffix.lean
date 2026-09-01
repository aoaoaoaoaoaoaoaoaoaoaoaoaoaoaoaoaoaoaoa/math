import MatrixMortality.DecimalSetterDepth
import Mathlib.Tactic

/-!
# Generalized decimal carrier suffixes

The recursive decimal carrier has no obstruction at any fixed decimal precision. For one
multi-role block, the stationary ratio equation is a quadratic whose derivative is `-1`
modulo ten, so its root lifts coherently through all powers of ten. Backward blocks nevertheless
contract exactly: a word gains the sum of its shifts in both decimal valuations, and one block
maps the unit domain onto an exact suffix cylinder. The physical blocks `R_b R_c D_b` and
`D_b R_c D_b` have identical first cylinders for every compiler-emitted body. Thus the first
unbounded cylinder does not uniquely decode a physical block itinerary.
-/

namespace MatrixMortality.DecimalSetterSuffix

open MatrixMortality.DecimalSetterArithmetic
open MatrixMortality.DecimalSetterCarry
open MatrixMortality.DecimalSetterChamber
open MatrixMortality.PadicValuation

private instance factPrimeFive : Fact (Nat.Prime 5) :=
  ⟨by norm_num⟩

/-- Defect in the stationary ratio equation for a generalized carrier block. Here `shift` is
the number of decimal digits removed from the normalized residual. -/
def cycleDefect (shift : Nat) (E τ C x : ℤ) : ℤ :=
  10 ^ shift * E * x ^ 2 - τ * x + C

/-- Rational form of the stationary carrier defect. -/
def rationalCycleDefect (shift : Nat) (E τ C x : ℚ) : ℚ :=
  10 ^ shift * E * x ^ 2 - τ * x + C

/-- Discriminant of the stationary carrier quadratic. -/
def cycleDiscriminant (shift : Nat) (E τ C : ℚ) : ℚ :=
  τ ^ 2 - 4 * 10 ^ shift * E * C

/-- Backward carrier map determined by one normalized multi-role block. -/
def inverseCarrier (shift : Nat) (E τ C tail : ℚ) : ℚ :=
  C / (τ - 10 ^ shift * E * tail)

/-- Center of the first suffix cylinder for one backward carrier block. -/
def carrierCenter (τ C : ℚ) : ℚ :=
  C / τ

/-- Exact joint `2`/`5` suffix cylinder cut out by one backward block. -/
def CarrierCylinder (shift : Nat) (τ C x : ℚ) : Prop :=
  HasDecimalShell (x - carrierCenter τ C) shift shift

/-- Center of a physical block with punctuated upper code `P` and lower code `V`. -/
def physicalCarrierCenter (E G μ P V : ℚ) : ℚ :=
  10 * μ * G * V / (E * P + G * V)

private theorem two_hasDecimalShell : HasDecimalShell (2 : ℚ) 1 0 := by
  refine ⟨?_, intCast_isUnit_of_not_dvd (by norm_num)⟩
  simpa using (primePower_hasValue (prime := 2) 1)

private theorem five_hasDecimalShell : HasDecimalShell (5 : ℚ) 0 1 := by
  refine ⟨intCast_isUnit_of_not_dvd (by norm_num), ?_⟩
  simpa using (primePower_hasValue (prime := 5) 1)

private theorem eleven_hasDecimalShell : HasDecimalShell (11 : ℚ) 0 0 :=
  ⟨intCast_isUnit_of_not_dvd (by norm_num), intCast_isUnit_of_not_dvd (by norm_num)⟩

private theorem fiveHundredFifty_hasDecimalShell : HasDecimalShell (550 : ℚ) 1 2 := by
  have product_shell :=
    (((two_hasDecimalShell.mul five_hasDecimalShell).mul five_hasDecimalShell).mul
      eleven_hasDecimalShell)
  convert product_shell using 1 <;> norm_num

private theorem code_append_false_false_mod_hundred (stem : List Bool) :
    (code (stem ++ [false, false]) : ℤ) ≡ 77 [ZMOD 100] := by
  rw [code_append]
  norm_num [code, digit, Nat.ofDigits]

private theorem cycleDenominator_hasDecimalShell
    {shift : Nat} {E : ℚ}
    (E_unit : HasDecimalShell E 0 0) :
    HasDecimalShell (2 * 10 ^ shift * E) (shift + 1) shift := by
  have scale_shell : HasDecimalShell ((10 : ℚ) ^ shift) shift shift := by
    simpa using ten_hasDecimalShell.pow shift
  have product_shell := (two_hasDecimalShell.mul scale_shell).mul E_unit
  simpa [add_comm] using product_shell

private theorem ten_dvd_ten_pow_mul {shift : Nat} (shift_pos : 1 ≤ shift) (E : ℤ) :
    (10 : ℤ) ∣ 10 ^ shift * E := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le shift_pos
  refine ⟨10 ^ offset * E, ?_⟩
  rw [show 1 + offset = offset + 1 by omega, pow_succ]
  ring

/-- A stationary suffix root modulo `10^depth` lifts to one modulo `10^(depth+1)` without
changing its previous `depth` digits. -/
theorem cycleDefect_lift
    {shift depth : Nat} {E τ C x : ℤ}
    (shift_pos : 1 ≤ shift)
    (tau_unit : (10 : ℤ) ∣ τ - 1)
    (root : (10 : ℤ) ^ depth ∣ cycleDefect shift E τ C x) :
    ∃ y : ℤ,
      (10 : ℤ) ^ depth ∣ y - x ∧
        (10 : ℤ) ^ (depth + 1) ∣ cycleDefect shift E τ C y := by
  obtain ⟨quotient, root_eq⟩ := root
  obtain ⟨tauCarry, tau_eq⟩ := tau_unit
  let scale : ℤ := 10 ^ depth
  let y : ℤ := x + quotient * scale
  have coefficient_dvd : (10 : ℤ) ∣ 10 ^ shift * E :=
    ten_dvd_ten_pow_mul shift_pos E
  obtain ⟨coefficient, coefficient_eq⟩ := coefficient_dvd
  have root_scaled : cycleDefect shift E τ C x = scale * quotient := by
    simpa [scale, mul_comm] using root_eq
  have tau_split : τ = 1 + 10 * tauCarry := by
    omega
  refine ⟨y, ⟨quotient, by simp [y, scale]; ring⟩, ?_⟩
  refine ⟨quotient * (-tauCarry + 2 * coefficient * x +
      coefficient * quotient * scale), ?_⟩
  rw [show (10 : ℤ) ^ (depth + 1) = scale * 10 by
    simp [scale, pow_succ]]
  simp only [cycleDefect]
  rw [show (10 : ℤ) ^ shift * E = 10 * coefficient by
    simpa [mul_comm] using coefficient_eq]
  simp only [cycleDefect] at root_scaled
  rw [tau_split]
  dsimp only [y]
  rw [coefficient_eq, tau_split] at root_scaled
  linear_combination root_scaled

/-- The stationary suffix root is unique at each decimal precision. The quotient of the
difference of two defects is congruent to `-1` modulo ten, hence is coprime to every power of
ten. -/
theorem cycleDefect_roots_congruent
    {shift depth : Nat} {E τ C x y : ℤ}
    (shift_pos : 1 ≤ shift)
    (tau_unit : (10 : ℤ) ∣ τ - 1)
    (x_root : (10 : ℤ) ^ depth ∣ cycleDefect shift E τ C x)
    (y_root : (10 : ℤ) ^ depth ∣ cycleDefect shift E τ C y) :
    (10 : ℤ) ^ depth ∣ x - y := by
  obtain ⟨coefficient, coefficient_eq⟩ := ten_dvd_ten_pow_mul shift_pos E
  obtain ⟨tauCarry, tau_eq⟩ := tau_unit
  let unit : ℤ := 10 ^ shift * E * (x + y) - τ
  have tau_split : τ = 1 + 10 * tauCarry := by omega
  have unit_eq : unit = 10 * (coefficient * (x + y) - tauCarry) - 1 := by
    dsimp only [unit]
    rw [coefficient_eq, tau_split]
    ring
  have unit_coprime : IsCoprime ((10 : ℤ) ^ depth) unit := by
    have ten_coprime : IsCoprime (10 : ℤ) unit := by
      refine ⟨coefficient * (x + y) - tauCarry, -1, ?_⟩
      rw [unit_eq]
      ring
    exact (ten_coprime.pow_left : IsCoprime ((10 : ℤ) ^ depth) unit)
  have product_dvd : (10 : ℤ) ^ depth ∣ (x - y) * unit := by
    have defect_factor :
        cycleDefect shift E τ C x - cycleDefect shift E τ C y =
          (x - y) * unit := by
      dsimp only [unit]
      unfold cycleDefect
      ring
    rw [← defect_factor]
    exact dvd_sub x_root y_root
  exact unit_coprime.dvd_of_dvd_mul_right product_dvd

/-- A diagonal rational unit fixed point exists exactly when one rational square root of the
discriminant has the simultaneous numerator shell needed to cancel `2 * 10^shift * E`.
Allowing the square root to have either sign includes both algebraic roots. If the `2`-adic and
`5`-adic Hensel roots select opposite signs, the right side is empty although each local root
exists. -/
theorem exists_rationalUnitCycle_iff_discriminantShell
    {shift : Nat} {E τ C : ℚ}
    (E_unit : HasDecimalShell E 0 0) :
    (∃ x : ℚ,
      HasDecimalShell x 0 0 ∧ rationalCycleDefect shift E τ C x = 0) ↔
      ∃ squareRoot : ℚ,
        squareRoot ^ 2 = cycleDiscriminant shift E τ C ∧
          HasDecimalShell (τ + squareRoot) (shift + 1) shift := by
  let coefficient : ℚ := 10 ^ shift * E
  have coefficient_ne : coefficient ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero shift (by norm_num)) E_unit.1.1
  have denominator_shell := cycleDenominator_hasDecimalShell (shift := shift) E_unit
  constructor
  · rintro ⟨x, x_unit, root⟩
    let squareRoot : ℚ := 2 * coefficient * x - τ
    refine ⟨squareRoot, ?_, ?_⟩
    · have defect_identity :
          squareRoot ^ 2 - cycleDiscriminant shift E τ C =
            4 * coefficient * rationalCycleDefect shift E τ C x := by
        dsimp only [squareRoot, coefficient]
        unfold cycleDiscriminant rationalCycleDefect
        ring
      rw [root, mul_zero, sub_eq_zero] at defect_identity
      exact defect_identity
    · have numerator_eq : τ + squareRoot = 2 * 10 ^ shift * E * x := by
        dsimp only [squareRoot, coefficient]
        ring
      rw [numerator_eq]
      have numerator_shell := denominator_shell.mul x_unit
      convert numerator_shell using 1 <;> norm_num
  · rintro ⟨squareRoot, square_eq, numerator_shell⟩
    let denominator : ℚ := 2 * coefficient
    have denominator_ne : denominator ≠ 0 := mul_ne_zero (by norm_num) coefficient_ne
    have denominator_eq : denominator = 2 * 10 ^ shift * E := by
      dsimp only [denominator, coefficient]
      ring
    have denominator_shell' :
        HasDecimalShell denominator (shift + 1) shift := by
      rw [denominator_eq]
      exact denominator_shell
    let x : ℚ := (τ + squareRoot) / denominator
    have x_unit : HasDecimalShell x 0 0 := by
      constructor
      · have quotient_shell := div_hasValue numerator_shell.1 denominator_shell'.1
        simpa [x] using quotient_shell
      · have quotient_shell := div_hasValue numerator_shell.2 denominator_shell'.2
        simpa [x] using quotient_shell
    refine ⟨x, x_unit, ?_⟩
    dsimp only [x, denominator, coefficient]
    unfold cycleDiscriminant at square_eq
    unfold rationalCycleDefect
    field_simp [E_unit.1.1]
    nlinarith

private theorem inverseCarrier_denominator_hasDecimalShell
    {shift : Nat} {E τ tail : ℚ}
    (shift_pos : 1 ≤ shift)
    (E_unit : HasDecimalShell E 0 0)
    (tau_unit : HasDecimalShell τ 0 0)
    (tail_unit : HasDecimalShell tail 0 0) :
    HasDecimalShell (τ - 10 ^ shift * E * tail) 0 0 := by
  have scale_shell : HasDecimalShell ((10 : ℚ) ^ shift) shift shift := by
    simpa using ten_hasDecimalShell.pow shift
  have shifted_shell :
      HasDecimalShell (10 ^ shift * E * tail) shift shift := by
    simpa only [zero_add, add_zero] using (scale_shell.mul E_unit).mul tail_unit
  have shift_int_pos : (0 : ℤ) < shift := by
    exact_mod_cast Nat.zero_lt_of_lt shift_pos
  exact
    ⟨unit_sub_positive tau_unit.1 ⟨shifted_shell.1.1, by
        rw [shifted_shell.1.2]
        exact shift_int_pos⟩,
      unit_sub_positive tau_unit.2 ⟨shifted_shell.2.1, by
        rw [shifted_shell.2.2]
        exact shift_int_pos⟩⟩

/-- One backward carrier step is an exact simultaneous `2`/`5`-adic contraction. If two tail
states differ in decimal shell `(r,r)`, their preimages differ in shell `(r+shift,r+shift)`.
The theorem is compositional: a backward block word gains the sum of its shifts. -/
theorem inverseCarrier_sub_hasDecimalShell
    {shift : Nat} {E τ C tail₁ tail₂ : ℚ} {depth : ℤ}
    (shift_pos : 1 ≤ shift)
    (E_unit : HasDecimalShell E 0 0)
    (tau_unit : HasDecimalShell τ 0 0)
    (C_unit : HasDecimalShell C 0 0)
    (tail1_unit : HasDecimalShell tail₁ 0 0)
    (tail2_unit : HasDecimalShell tail₂ 0 0)
    (difference_shell : HasDecimalShell (tail₁ - tail₂) depth depth) :
    HasDecimalShell
      (inverseCarrier shift E τ C tail₁ - inverseCarrier shift E τ C tail₂)
      (depth + shift) (depth + shift) := by
  have scale_shell : HasDecimalShell ((10 : ℚ) ^ shift) shift shift := by
    simpa using ten_hasDecimalShell.pow shift
  have denominator1_shell :
      HasDecimalShell (τ - 10 ^ shift * E * tail₁) 0 0 :=
    inverseCarrier_denominator_hasDecimalShell shift_pos E_unit tau_unit tail1_unit
  have denominator2_shell :
      HasDecimalShell (τ - 10 ^ shift * E * tail₂) 0 0 :=
    inverseCarrier_denominator_hasDecimalShell shift_pos E_unit tau_unit tail2_unit
  have difference_identity :
      inverseCarrier shift E τ C tail₁ - inverseCarrier shift E τ C tail₂ =
        C * 10 ^ shift * E * (tail₁ - tail₂) /
          ((τ - 10 ^ shift * E * tail₁) *
            (τ - 10 ^ shift * E * tail₂)) := by
    unfold inverseCarrier
    field_simp [denominator1_shell.1.1, denominator2_shell.1.1]
    ring
  rw [difference_identity]
  have numerator_shell := ((C_unit.mul scale_shell).mul E_unit).mul difference_shell
  have denominator_shell := denominator1_shell.mul denominator2_shell
  constructor
  · have quotient_shell := div_hasValue numerator_shell.1 denominator_shell.1
    convert quotient_shell using 1
    ring
  · have quotient_shell := div_hasValue numerator_shell.2 denominator_shell.2
    convert quotient_shell using 1
    ring

/-- A backward block maps every decimal-unit tail to the exact shell of depth `shift` around
its center `C / τ`. -/
theorem inverseCarrier_mem_carrierCylinder
    {shift : Nat} {E τ C tail : ℚ}
    (shift_pos : 1 ≤ shift)
    (E_unit : HasDecimalShell E 0 0)
    (tau_unit : HasDecimalShell τ 0 0)
    (C_unit : HasDecimalShell C 0 0)
    (tail_unit : HasDecimalShell tail 0 0) :
    CarrierCylinder shift τ C (inverseCarrier shift E τ C tail) := by
  have scale_shell : HasDecimalShell ((10 : ℚ) ^ shift) shift shift := by
    simpa using ten_hasDecimalShell.pow shift
  have denominator_shell :
      HasDecimalShell (τ - 10 ^ shift * E * tail) 0 0 :=
    inverseCarrier_denominator_hasDecimalShell shift_pos E_unit tau_unit tail_unit
  have difference_identity :
      inverseCarrier shift E τ C tail - carrierCenter τ C =
        C * 10 ^ shift * E * tail /
          ((τ - 10 ^ shift * E * tail) * τ) := by
    unfold inverseCarrier carrierCenter
    field_simp [denominator_shell.1.1, tau_unit.1.1]
    ring
  rw [CarrierCylinder, difference_identity]
  have numerator_shell := ((C_unit.mul scale_shell).mul E_unit).mul tail_unit
  have denominator_product_shell := denominator_shell.mul tau_unit
  constructor
  · have quotient_shell := div_hasValue numerator_shell.1 denominator_product_shell.1
    convert quotient_shell using 1
    omega
  · have quotient_shell := div_hasValue numerator_shell.2 denominator_product_shell.2
    convert quotient_shell using 1
    omega

/-- A backward block preserves the decimal-unit carrier domain. -/
theorem inverseCarrier_hasDecimalShell
    {shift : Nat} {E τ C tail : ℚ}
    (shift_pos : 1 ≤ shift)
    (E_unit : HasDecimalShell E 0 0)
    (tau_unit : HasDecimalShell τ 0 0)
    (C_unit : HasDecimalShell C 0 0)
    (tail_unit : HasDecimalShell tail 0 0) :
    HasDecimalShell (inverseCarrier shift E τ C tail) 0 0 := by
  have denominator_shell :
      HasDecimalShell (τ - 10 ^ shift * E * tail) 0 0 :=
    inverseCarrier_denominator_hasDecimalShell shift_pos E_unit tau_unit tail_unit
  unfold inverseCarrier
  exact
    ⟨by simpa using div_hasValue C_unit.1 denominator_shell.1,
      by simpa using div_hasValue C_unit.2 denominator_shell.2⟩

/-- One inverse block is injective on the decimal-unit tail domain. -/
theorem inverseCarrier_injective_of_decimalUnits
    {shift : Nat} {E τ C tail₁ tail₂ : ℚ}
    (shift_pos : 1 ≤ shift)
    (E_unit : HasDecimalShell E 0 0)
    (tau_unit : HasDecimalShell τ 0 0)
    (C_unit : HasDecimalShell C 0 0)
    (tail1_unit : HasDecimalShell tail₁ 0 0)
    (tail2_unit : HasDecimalShell tail₂ 0 0)
    (images_eq : inverseCarrier shift E τ C tail₁ = inverseCarrier shift E τ C tail₂) :
    tail₁ = tail₂ := by
  have denominator1_shell :=
    inverseCarrier_denominator_hasDecimalShell shift_pos E_unit tau_unit tail1_unit
  have denominator2_shell :=
    inverseCarrier_denominator_hasDecimalShell shift_pos E_unit tau_unit tail2_unit
  have cross_product :
      C * (τ - 10 ^ shift * E * tail₂) =
        C * (τ - 10 ^ shift * E * tail₁) := by
    exact (div_eq_div_iff denominator1_shell.1.1 denominator2_shell.1.1).mp images_eq
  have denominator_eq :
      τ - 10 ^ shift * E * tail₂ = τ - 10 ^ shift * E * tail₁ :=
    mul_left_cancel₀ C_unit.1.1 cross_product
  have coefficient_ne : (10 : ℚ) ^ shift * E ≠ 0 :=
    mul_ne_zero (pow_ne_zero shift (by norm_num)) E_unit.1.1
  apply mul_left_cancel₀ coefficient_ne
  linear_combination denominator_eq

/-- Conversely, every rational decimal unit in a block's exact first cylinder has a unique
decimal-unit tail under that inverse block. Thus `CarrierCylinder` is the exact local image,
not merely a containing ball. -/
theorem exists_inverseCarrier_unit_iff_carrierCylinder
    {shift : Nat} {E τ C x : ℚ}
    (shift_pos : 1 ≤ shift)
    (E_unit : HasDecimalShell E 0 0)
    (tau_unit : HasDecimalShell τ 0 0)
    (C_unit : HasDecimalShell C 0 0)
    (x_unit : HasDecimalShell x 0 0) :
    (∃ tail : ℚ,
      HasDecimalShell tail 0 0 ∧ inverseCarrier shift E τ C tail = x) ↔
      CarrierCylinder shift τ C x := by
  constructor
  · rintro ⟨tail, tail_unit, rfl⟩
    exact inverseCarrier_mem_carrierCylinder shift_pos E_unit tau_unit C_unit tail_unit
  · intro cylinder
    let tail : ℚ := (τ * x - C) / (10 ^ shift * E * x)
    have scale_shell : HasDecimalShell ((10 : ℚ) ^ shift) shift shift := by
      simpa using ten_hasDecimalShell.pow shift
    have numerator_identity : τ * x - C = τ * (x - carrierCenter τ C) := by
      unfold carrierCenter
      field_simp [tau_unit.1.1]
    have numerator_shell : HasDecimalShell (τ * x - C) shift shift := by
      rw [numerator_identity]
      simpa only [zero_add] using tau_unit.mul cylinder
    have denominator_shell :
        HasDecimalShell (10 ^ shift * E * x) shift shift := by
      simpa only [zero_add, add_zero] using (scale_shell.mul E_unit).mul x_unit
    have tail_unit : HasDecimalShell tail 0 0 := by
      constructor
      · have quotient_shell := div_hasValue numerator_shell.1 denominator_shell.1
        simpa [tail] using quotient_shell
      · have quotient_shell := div_hasValue numerator_shell.2 denominator_shell.2
        simpa [tail] using quotient_shell
    refine ⟨tail, tail_unit, ?_⟩
    unfold inverseCarrier
    dsimp only [tail]
    field_simp [E_unit.1.1, C_unit.1.1, x_unit.1.1]
    ring

/-- Every rational unit in the first cylinder has exactly one decimal-unit tail. -/
theorem existsUnique_inverseCarrier_unit_iff_carrierCylinder
    {shift : Nat} {E τ C x : ℚ}
    (shift_pos : 1 ≤ shift)
    (E_unit : HasDecimalShell E 0 0)
    (tau_unit : HasDecimalShell τ 0 0)
    (C_unit : HasDecimalShell C 0 0)
    (x_unit : HasDecimalShell x 0 0) :
    (∃! tail : ℚ,
      HasDecimalShell tail 0 0 ∧ inverseCarrier shift E τ C tail = x) ↔
      CarrierCylinder shift τ C x := by
  constructor
  · rintro ⟨tail, tail_property, _⟩
    exact (exists_inverseCarrier_unit_iff_carrierCylinder
      shift_pos E_unit tau_unit C_unit x_unit).mp ⟨tail, tail_property⟩
  · intro cylinder
    obtain ⟨tail, tail_unit, tail_image⟩ :=
      (exists_inverseCarrier_unit_iff_carrierCylinder
        shift_pos E_unit tau_unit C_unit x_unit).mpr cylinder
    refine ⟨tail, ⟨tail_unit, tail_image⟩, ?_⟩
    intro other other_property
    exact inverseCarrier_injective_of_decimalUnits
      shift_pos E_unit tau_unit C_unit other_property.1 tail_unit
        (other_property.2.trans tail_image.symm)

/-- One coefficient package in a backward generalized-carrier word. -/
structure BackwardBlock where
  /-- Decimal depth gained by this inverse step. -/
  shift : Nat
  /-- Coefficient multiplying the tail after decimal scaling. -/
  gap : ℚ
  /-- Normalized trace. -/
  trace : ℚ
  /-- Constant product `μGV`. -/
  constant : ℚ
  /-- Every surviving non-singleton block has positive shift. -/
  shift_pos : 1 ≤ shift
  /-- The gap coefficient is a decimal unit. -/
  gap_unit : HasDecimalShell gap 0 0
  /-- The normalized trace is a decimal unit. -/
  trace_unit : HasDecimalShell trace 0 0
  /-- The constant product is a decimal unit. -/
  constant_unit : HasDecimalShell constant 0 0

namespace BackwardBlock

/-- Apply one bundled backward block. -/
def pullback (block : BackwardBlock) (tail : ℚ) : ℚ :=
  inverseCarrier block.shift block.gap block.trace block.constant tail

/-- Apply a backward block word from its first block toward its future tail. -/
def pullbackWord : List BackwardBlock → ℚ → ℚ
  | [], tail => tail
  | block :: blocks, tail => block.pullback (pullbackWord blocks tail)

/-- Cumulative decimal depth gained by a backward block word. -/
def totalShift : List BackwardBlock → Nat
  | [] => 0
  | block :: blocks => block.shift + totalShift blocks

theorem pullbackWord_hasDecimalShell
    (blocks : List BackwardBlock) {tail : ℚ}
    (tail_unit : HasDecimalShell tail 0 0) :
    HasDecimalShell (pullbackWord blocks tail) 0 0 := by
  induction blocks with
  | nil => exact tail_unit
  | cons block blocks induction =>
      exact inverseCarrier_hasDecimalShell block.shift_pos block.gap_unit block.trace_unit
        block.constant_unit induction

/-- A backward word gains exactly the sum of its block shifts in both decimal valuations. -/
theorem pullbackWord_sub_hasDecimalShell
    (blocks : List BackwardBlock) {tail₁ tail₂ : ℚ} {depth : ℤ}
    (tail1_unit : HasDecimalShell tail₁ 0 0)
    (tail2_unit : HasDecimalShell tail₂ 0 0)
    (difference_shell : HasDecimalShell (tail₁ - tail₂) depth depth) :
    HasDecimalShell
      (pullbackWord blocks tail₁ - pullbackWord blocks tail₂)
      (depth + totalShift blocks) (depth + totalShift blocks) := by
  induction blocks generalizing depth with
  | nil => simpa [pullbackWord, totalShift] using difference_shell
  | cons block blocks induction =>
      have pulled1_unit := pullbackWord_hasDecimalShell blocks tail1_unit
      have pulled2_unit := pullbackWord_hasDecimalShell blocks tail2_unit
      have pulled_difference := induction difference_shell
      have one_step := inverseCarrier_sub_hasDecimalShell
        block.shift_pos block.gap_unit block.trace_unit block.constant_unit
        pulled1_unit pulled2_unit pulled_difference
      simpa [pullbackWord, pullback, totalShift, add_assoc, add_left_comm, add_comm] using one_step

end BackwardBlock

/-- The difference of two physical cylinder centers cancels the quadratic `G * V₁ * V₂`
term. Separation is controlled only by the cross-discrepancy `V₁P₂ - V₂P₁`. -/
theorem physicalCarrierCenter_sub
    {E G μ P₁ P₂ V₁ V₂ : ℚ}
    (trace1_ne : E * P₁ + G * V₁ ≠ 0)
    (trace2_ne : E * P₂ + G * V₂ ≠ 0) :
    physicalCarrierCenter E G μ P₁ V₁ -
        physicalCarrierCenter E G μ P₂ V₂ =
      10 * μ * G * E * (V₁ * P₂ - V₂ * P₁) /
        ((E * P₁ + G * V₁) * (E * P₂ + G * V₂)) := by
  unfold physicalCarrierCenter
  field_simp [trace1_ne, trace2_ne]
  ring

/-- For two blocks with the same upper code, a prescribed shell of the lower-code difference
passes to their center difference after one factor of ten is gained and two trace factors are
removed. -/
theorem physicalCarrierCenter_sameUpper_sub_hasDecimalShell
    {E G μ P V₁ V₂ : ℚ} {depth : ℤ}
    (E_unit : HasDecimalShell E 0 0)
    (G_unit : HasDecimalShell G 0 0)
    (mu_unit : HasDecimalShell μ 0 0)
    (P_unit : HasDecimalShell P 0 0)
    (trace1_shell : HasDecimalShell (E * P + G * V₁) 1 1)
    (trace2_shell : HasDecimalShell (E * P + G * V₂) 1 1)
    (lower_difference_shell :
      HasDecimalShell (V₁ - V₂) (depth + 1) (depth + 2)) :
    HasDecimalShell
      (physicalCarrierCenter E G μ P V₁ -
        physicalCarrierCenter E G μ P V₂)
      depth (depth + 1) := by
  have center_identity := physicalCarrierCenter_sub
    (E := E) (G := G) (μ := μ) (P₁ := P) (P₂ := P) (V₁ := V₁) (V₂ := V₂)
    trace1_shell.1.1 trace2_shell.1.1
  have center_identity' :
      physicalCarrierCenter E G μ P V₁ - physicalCarrierCenter E G μ P V₂ =
        10 * μ * G * E * P * (V₁ - V₂) /
          ((E * P + G * V₁) * (E * P + G * V₂)) := by
    rw [center_identity]
    ring
  rw [center_identity']
  have numerator_shell :=
    ((((ten_hasDecimalShell.mul mu_unit).mul G_unit).mul E_unit).mul P_unit).mul
      lower_difference_shell
  have denominator_shell := trace1_shell.mul trace2_shell
  constructor
  · have quotient_shell := div_hasValue numerator_shell.1 denominator_shell.1
    convert quotient_shell using 1
    ring
  · have quotient_shell := div_hasValue numerator_shell.2 denominator_shell.2
    convert quotient_shell using 1
    ring

/-- Moving a center by a quantity deeper than a joint decimal shell does not change that shell. -/
theorem sub_center_hasDecimalShell_iff_of_center_sub_deeper
    {shift : Nat} {center₁ center₂ x : ℚ} {twoDepth fiveDepth : ℤ}
    (center_shell :
      HasDecimalShell (center₁ - center₂) twoDepth fiveDepth)
    (two_deeper : (shift : ℤ) < twoDepth)
    (five_deeper : (shift : ℤ) < fiveDepth) :
    HasDecimalShell (x - center₁) shift shift ↔
      HasDecimalShell (x - center₂) shift shift := by
  have opposite_shell :
      HasDecimalShell (center₂ - center₁) twoDepth fiveDepth := by
    rw [show center₂ - center₁ = -(center₁ - center₂) by ring]
    exact ⟨neg_hasValue center_shell.1, neg_hasValue center_shell.2⟩
  constructor
  · intro first_cylinder
    rw [show x - center₂ = (x - center₁) + (center₁ - center₂) by ring]
    exact
      ⟨add_hasValue_left first_cylinder.1 center_shell.1 two_deeper,
        add_hasValue_left first_cylinder.2 center_shell.2 five_deeper⟩
  · intro second_cylinder
    rw [show x - center₁ = (x - center₂) + (center₂ - center₁) by ring]
    exact
      ⟨add_hasValue_left second_cylinder.1 opposite_shell.1 two_deeper,
        add_hasValue_left second_cylinder.2 opposite_shell.2 five_deeper⟩

/-- Moving a carrier-cylinder center by a quantity deeper than the cylinder at both decimal
primes does not change the cylinder. -/
theorem carrierCylinder_iff_of_center_sub_deeper
    {shift : Nat} {τ₁ C₁ τ₂ C₂ x : ℚ} {twoDepth fiveDepth : ℤ}
    (center_shell :
      HasDecimalShell
        (carrierCenter τ₁ C₁ - carrierCenter τ₂ C₂) twoDepth fiveDepth)
    (two_deeper : (shift : ℤ) < twoDepth)
    (five_deeper : (shift : ℤ) < fiveDepth) :
    CarrierCylinder shift τ₁ C₁ x ↔ CarrierCylinder shift τ₂ C₂ x := by
  exact sub_center_hasDecimalShell_iff_of_center_sub_deeper
    center_shell two_deeper five_deeper

/-! ## A physical first-cylinder collision -/

/-- Lawful block whose first `b` role is a rule and whose long common suffix is `R_c D_b`. -/
def hiddenRuleBlock : List NearyTile :=
  [.rule .b, .rule .c, .erase .b]

/-- Companion block with the same upper spelling and `D_b` in place of the first rule. -/
def hiddenEraseBlock : List NearyTile :=
  [.erase .b, .rule .c, .erase .b]

/-- Punctuated upper code of the rule-first collision block. -/
def hiddenRuleUpperCode (β : Nat) : Nat :=
  code (spell (nearyUpper β) hiddenRuleBlock ++ nearyMarker β)

/-- Punctuated upper code of the erasure-first collision block. -/
def hiddenEraseUpperCode (β : Nat) : Nat :=
  code (spell (nearyUpper β) hiddenEraseBlock ++ nearyMarker β)

/-- Lower code of the rule-first collision block. -/
def hiddenRuleLowerCode (β : Nat) (body : List TagLetter) : Nat :=
  code (spell (nearyLower β body) hiddenRuleBlock)

/-- Lower code of the erasure-first collision block. -/
def hiddenEraseLowerCode (β : Nat) (body : List TagLetter) : Nat :=
  code (spell (nearyLower β body) hiddenEraseBlock)

/-- Lower spelling shared after the first role of the two hidden-phase blocks. -/
def hiddenPhaseLowerSuffix (β : Nat) (body : List TagLetter) : List Bool :=
  nearyLower β body (.rule .c) ++ nearyLower β body (.erase .b)

private theorem hiddenUpper_ends_false_false
    {β : Nat} (beta_large : 2 ≤ β) :
    ∃ stem : List Bool,
      spell (nearyUpper β) hiddenRuleBlock ++ nearyMarker β =
        stem ++ [false, false] := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le beta_large
  let stem :=
    spell (nearyUpper (2 + offset)) hiddenRuleBlock ++
      true :: List.replicate offset false
  refine ⟨stem, ?_⟩
  dsimp only [stem]
  simp [nearyMarker, List.replicate_add, List.append_assoc, Nat.add_comm]

private theorem hiddenRuleLower_ends_false_false (β : Nat) (body : List TagLetter) :
    ∃ stem : List Bool,
      spell (nearyLower β body) hiddenRuleBlock = stem ++ [false, false] := by
  let stem := [true, true, false, true] ++ tagEncode β body ++ [true]
  refine ⟨stem, ?_⟩
  simp [stem, hiddenRuleBlock, spell, nearyLower, List.append_assoc]

private theorem hiddenEraseLower_ends_false_false (β : Nat) (body : List TagLetter) :
    ∃ stem : List Bool,
      spell (nearyLower β body) hiddenEraseBlock = stem ++ [false, false] := by
  let stem := [false, true] ++ tagEncode β body ++ [true]
  refine ⟨stem, ?_⟩
  simp [stem, hiddenEraseBlock, spell, nearyLower, List.append_assoc]

private theorem ten_pow_mod_ten {β : Nat} (beta_pos : 1 ≤ β) :
    (10 : ℤ) ^ β ≡ 0 [ZMOD 10] := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le beta_pos
  rw [show 1 + offset = offset + 1 by omega, pow_succ]
  simpa [mul_comm] using
    (Int.ModEq.refl ((10 : ℤ) ^ offset)).mul (by norm_num : (10 : ℤ) ≡ 0 [ZMOD 10])

private theorem ten_pow_mod_hundred {β : Nat} (beta_large : 2 ≤ β) :
    (10 : ℤ) ^ β ≡ 0 [ZMOD 100] := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le beta_large
  have square_mod : (10 : ℤ) ^ 2 ≡ 0 [ZMOD 100] := by norm_num
  simpa [pow_add, mul_comm] using
    square_mod.mul (Int.ModEq.refl ((10 : ℤ) ^ offset))

@[simp] theorem hiddenRuleBlock_last : hiddenRuleBlock.getLast? = some (.erase .b) := by
  rfl

@[simp] theorem hiddenEraseBlock_last : hiddenEraseBlock.getLast? = some (.erase .b) := by
  rfl

/-- Rule and erasure phases carry the same upper `b`, so the two complete upper spellings are
identical. -/
theorem hiddenBlocks_upper_eq (β : Nat) :
    spell (nearyUpper β) hiddenRuleBlock =
      spell (nearyUpper β) hiddenEraseBlock := by
  rfl

@[simp] theorem hiddenBlocks_upperCode_eq (β : Nat) :
    hiddenRuleUpperCode β = hiddenEraseUpperCode β := by
  unfold hiddenRuleUpperCode hiddenEraseUpperCode
  rw [hiddenBlocks_upper_eq]

theorem hiddenRuleUpperCode_decimalUnit {β : Nat} (beta_large : 2 ≤ β) :
    HasDecimalShell (hiddenRuleUpperCode β : ℚ) 0 0 := by
  obtain ⟨stem, word_eq⟩ := hiddenUpper_ends_false_false beta_large
  unfold hiddenRuleUpperCode
  rw [word_eq, show stem ++ [false, false] = (stem ++ [false]) ++ [false] by simp]
  exact code_append_false_hasDecimalShell (stem ++ [false])

theorem hiddenRuleUpperCode_mod_hundred {β : Nat} (beta_large : 2 ≤ β) :
    (hiddenRuleUpperCode β : ℤ) ≡ 77 [ZMOD 100] := by
  obtain ⟨stem, word_eq⟩ := hiddenUpper_ends_false_false beta_large
  unfold hiddenRuleUpperCode
  rw [word_eq]
  exact code_append_false_false_mod_hundred stem

theorem hiddenRuleLowerCode_mod_hundred (β : Nat) (body : List TagLetter) :
    (hiddenRuleLowerCode β body : ℤ) ≡ 77 [ZMOD 100] := by
  obtain ⟨stem, word_eq⟩ := hiddenRuleLower_ends_false_false β body
  unfold hiddenRuleLowerCode
  rw [word_eq]
  exact code_append_false_false_mod_hundred stem

theorem hiddenEraseLowerCode_mod_hundred (β : Nat) (body : List TagLetter) :
    (hiddenEraseLowerCode β body : ℤ) ≡ 77 [ZMOD 100] := by
  obtain ⟨stem, word_eq⟩ := hiddenEraseLower_ends_false_false β body
  unfold hiddenEraseLowerCode
  rw [word_eq]
  exact code_append_false_false_mod_hundred stem

/-- The calibrated gap, lift, marker, and common upper code are decimal units for the physical
hidden-phase pair. -/
theorem hiddenBlocks_calibrated_decimalUnits {β : Nat} (beta_large : 2 ≤ β) :
    HasDecimalShell (decimalGap ((10 : ℤ) ^ β) : ℚ) 0 0 ∧
      HasDecimalShell (decimalLift ((10 : ℤ) ^ β) : ℚ) 0 0 ∧
      HasDecimalShell (code (nearyMarker β) : ℚ) 0 0 ∧
      HasDecimalShell (hiddenRuleUpperCode β : ℚ) 0 0 := by
  have rho_mod := ten_pow_mod_ten (show 1 ≤ β by omega)
  have gap_mod : decimalGap ((10 : ℤ) ^ β) ≡ 7 [ZMOD 10] := by
    calc
      decimalGap ((10 : ℤ) ^ β) = (10 : ℤ) ^ β * 18 - 63 := by
        simp [decimalGap]
        ring
      _ ≡ 0 * 18 - 63 [ZMOD 10] :=
        (rho_mod.mul (Int.ModEq.refl 18)).sub (Int.ModEq.refl 63)
      _ ≡ 7 [ZMOD 10] := by norm_num
  have lift_mod : decimalLift ((10 : ℤ) ^ β) ≡ 3 [ZMOD 10] := by
    calc
      decimalLift ((10 : ℤ) ^ β) = (10 : ℤ) ^ β * 502 - 7 := by
        simp [decimalLift]
        ring
      _ ≡ 0 * 502 - 7 [ZMOD 10] :=
        (rho_mod.mul (Int.ModEq.refl 502)).sub (Int.ModEq.refl 7)
      _ ≡ 3 [ZMOD 10] := by norm_num
  obtain ⟨offset, beta_eq⟩ := Nat.exists_eq_add_of_le beta_large
  let markerStem := true :: List.replicate (1 + offset) false
  have marker_eq : nearyMarker β = markerStem ++ [false] := by
    rw [beta_eq]
    simp [markerStem, nearyMarker, List.replicate_add, List.append_assoc, Nat.add_comm]
  have marker_unit : HasDecimalShell (code (nearyMarker β) : ℚ) 0 0 := by
    rw [marker_eq]
    exact code_append_false_hasDecimalShell markerStem
  exact
    ⟨intCast_hasDecimalShell_of_mod_seven gap_mod,
      intCast_hasDecimalShell_of_mod_three lift_mod,
      marker_unit, hiddenRuleUpperCode_decimalUnit beta_large⟩

/-- Both collision blocks have the physical multi-role trace shell `(1,1)`. -/
theorem hiddenBlocks_trace_hasDecimalShell
    {β : Nat} (body : List TagLetter) (beta_large : 2 ≤ β) :
    HasDecimalShell
        (transferTrace
          (decimalGap ((10 : ℤ) ^ β) : ℚ)
          (decimalLift ((10 : ℤ) ^ β) : ℚ)
          (hiddenRuleUpperCode β) (hiddenRuleLowerCode β body)) 1 1 ∧
      HasDecimalShell
        (transferTrace
          (decimalGap ((10 : ℤ) ^ β) : ℚ)
          (decimalLift ((10 : ℤ) ^ β) : ℚ)
          (hiddenEraseUpperCode β) (hiddenEraseLowerCode β body)) 1 1 := by
  have rho_mod := ten_pow_mod_hundred beta_large
  have rule_upper_mod := hiddenRuleUpperCode_mod_hundred beta_large
  have erase_upper_mod : (hiddenEraseUpperCode β : ℤ) ≡ 77 [ZMOD 100] := by
    rw [← hiddenBlocks_upperCode_eq β]
    exact rule_upper_mod
  have rule_trace := multiErasure_trace_hasDecimalShell rho_mod rule_upper_mod
    (hiddenRuleLowerCode_mod_hundred β body)
  have erase_trace := multiErasure_trace_hasDecimalShell rho_mod erase_upper_mod
    (hiddenEraseLowerCode_mod_hundred β body)
  exact ⟨rule_trace, erase_trace⟩

/-- Both hidden-phase blocks have upper length `2β+5`, hence carrier shift `2β+3`. -/
theorem hiddenBlocks_upper_length (β : Nat) :
    (spell (nearyUpper β) hiddenRuleBlock).length = 2 * β + 5 ∧
      (spell (nearyUpper β) hiddenEraseBlock).length = 2 * β + 5 := by
  rw [spell_nearyUpper, spell_nearyUpper]
  simp [hiddenRuleBlock, hiddenEraseBlock, NearyTile.letter, tagEncode_cons, tagCode]
  omega

@[simp] theorem hiddenPhaseLowerSuffix_length (β : Nat) (body : List TagLetter) :
    (hiddenPhaseLowerSuffix β body).length = (tagEncode β body).length + 4 := by
  simp [hiddenPhaseLowerSuffix, nearyLower]

/-- The two lower codes differ only in the hidden first phase. The rule prefix is `557`, the
erasure prefix is `7`, and their common suffix contributes its full decimal place scale. -/
theorem hiddenBlocks_lowerCode_sub
    (β : Nat) (body : List TagLetter) :
    (code (spell (nearyLower β body) hiddenRuleBlock) : ℤ) -
        code (spell (nearyLower β body) hiddenEraseBlock) =
      550 * 10 ^ ((tagEncode β body).length + 4) := by
  have rule_lower :
      spell (nearyLower β body) hiddenRuleBlock =
        [true, true, false] ++ hiddenPhaseLowerSuffix β body := by
    rfl
  have erase_lower :
      spell (nearyLower β body) hiddenEraseBlock =
        [false] ++ hiddenPhaseLowerSuffix β body := by
    rfl
  rw [rule_lower, erase_lower, code_append, code_append, hiddenPhaseLowerSuffix_length]
  norm_num [code, digit, Nat.ofDigits]
  ring

/-- The hidden-phase lower-code difference has one more factor of two and two more factors of
five than its common decimal suffix. -/
theorem hiddenBlocks_lowerCode_sub_hasDecimalShell
    (β : Nat) (body : List TagLetter) :
    HasDecimalShell
      ((code (spell (nearyLower β body) hiddenRuleBlock) : ℚ) -
        code (spell (nearyLower β body) hiddenEraseBlock))
      ((tagEncode β body).length + 5) ((tagEncode β body).length + 6) := by
  have identity :
      (code (spell (nearyLower β body) hiddenRuleBlock) : ℚ) -
          code (spell (nearyLower β body) hiddenEraseBlock) =
        550 * 10 ^ ((tagEncode β body).length + 4) := by
    exact_mod_cast hiddenBlocks_lowerCode_sub β body
  rw [identity]
  have scale_shell := ten_hasDecimalShell.pow ((tagEncode β body).length + 4)
  have product_shell := fiveHundredFifty_hasDecimalShell.mul scale_shell
  convert product_shell using 1
  · push_cast
    omega
  · push_cast
    omega

/-- The two lawful emitted blocks `R_b R_c D_b` and `D_b R_c D_b` cut out the same first
carrier cylinder whenever the encoded body has the compiler's length bound. Their upper codes
are identical; the long lower suffix hides the first phase beyond the cylinder depth. -/
theorem hiddenBlocks_firstCylinder_collision
    {β : Nat} (body : List TagLetter) {E G μ x : ℚ}
    (E_unit : HasDecimalShell E 0 0)
    (G_unit : HasDecimalShell G 0 0)
    (mu_unit : HasDecimalShell μ 0 0)
    (upper_unit : HasDecimalShell (hiddenRuleUpperCode β : ℚ) 0 0)
    (rule_trace_shell :
      HasDecimalShell
        (E * hiddenRuleUpperCode β + G * hiddenRuleLowerCode β body) 1 1)
    (erase_trace_shell :
      HasDecimalShell
        (E * hiddenEraseUpperCode β + G * hiddenEraseLowerCode β body) 1 1)
    (body_length : 2 * β ≤ (tagEncode β body).length) :
    HasDecimalShell
        (x - physicalCarrierCenter E G μ
          (hiddenRuleUpperCode β) (hiddenRuleLowerCode β body))
        (2 * β + 3) (2 * β + 3) ↔
      HasDecimalShell
        (x - physicalCarrierCenter E G μ
          (hiddenEraseUpperCode β) (hiddenEraseLowerCode β body))
        (2 * β + 3) (2 * β + 3) := by
  have upper_eq : (hiddenEraseUpperCode β : ℚ) = hiddenRuleUpperCode β := by
    norm_cast
  have lower_difference_shell :
      HasDecimalShell
        ((hiddenRuleLowerCode β body : ℚ) - hiddenEraseLowerCode β body)
        ((tagEncode β body).length + 5) ((tagEncode β body).length + 6) := by
    simpa [hiddenRuleLowerCode, hiddenEraseLowerCode] using
      hiddenBlocks_lowerCode_sub_hasDecimalShell β body
  have erase_trace_shell' :
      HasDecimalShell
        (E * hiddenRuleUpperCode β + G * hiddenEraseLowerCode β body) 1 1 := by
    rw [← upper_eq]
    exact erase_trace_shell
  have center_shell :
      HasDecimalShell
        (physicalCarrierCenter E G μ
            (hiddenRuleUpperCode β) (hiddenRuleLowerCode β body) -
          physicalCarrierCenter E G μ
            (hiddenRuleUpperCode β) (hiddenEraseLowerCode β body))
        ((tagEncode β body).length + 4) ((tagEncode β body).length + 5) := by
    exact physicalCarrierCenter_sameUpper_sub_hasDecimalShell
      E_unit G_unit mu_unit upper_unit rule_trace_shell erase_trace_shell'
        lower_difference_shell
  have two_deeper :
      ((2 * β + 3 : Nat) : ℤ) < ((tagEncode β body).length + 4 : Nat) := by
    exact_mod_cast (show 2 * β + 3 < (tagEncode β body).length + 4 by omega)
  have five_deeper :
      ((2 * β + 3 : Nat) : ℤ) < ((tagEncode β body).length + 5 : Nat) := by
    exact_mod_cast (show 2 * β + 3 < (tagEncode β body).length + 5 by omega)
  rw [upper_eq]
  exact sub_center_hasDecimalShell_iff_of_center_sub_deeper
    center_shell two_deeper five_deeper

/-- The body hypotheses discharged by Neary's compiler imply the collision length bound. -/
theorem hiddenBlocks_firstCylinder_collision_of_emittedBody
    {β : Nat} (body : List TagLetter) {E G μ x : ℚ}
    (E_unit : HasDecimalShell E 0 0)
    (G_unit : HasDecimalShell G 0 0)
    (mu_unit : HasDecimalShell μ 0 0)
    (upper_unit : HasDecimalShell (hiddenRuleUpperCode β : ℚ) 0 0)
    (rule_trace_shell :
      HasDecimalShell
        (E * hiddenRuleUpperCode β + G * hiddenRuleLowerCode β body) 1 1)
    (erase_trace_shell :
      HasDecimalShell
        (E * hiddenEraseUpperCode β + G * hiddenEraseLowerCode β body) 1 1)
    (body_long : β - 1 ≤ body.length)
    (body_head : body.head? = some .b) :
    HasDecimalShell
        (x - physicalCarrierCenter E G μ
          (hiddenRuleUpperCode β) (hiddenRuleLowerCode β body))
        (2 * β + 3) (2 * β + 3) ↔
      HasDecimalShell
        (x - physicalCarrierCenter E G μ
          (hiddenEraseUpperCode β) (hiddenEraseLowerCode β body))
        (2 * β + 3) (2 * β + 3) := by
  exact hiddenBlocks_firstCylinder_collision body E_unit G_unit mu_unit upper_unit
    rule_trace_shell erase_trace_shell (tagEncode_length_of_head_b body_long body_head)

/-- Fully calibrated collision for every compiler-emitted body. No external shell premise
remains: the physical decimal constants and both lawful block traces discharge them. -/
theorem emittedHiddenBlocks_firstCylinder_collision
    {β : Nat} (body : List TagLetter) {x : ℚ}
    (beta_large : 2 ≤ β)
    (body_long : β - 1 ≤ body.length)
    (body_head : body.head? = some .b) :
    HasDecimalShell
        (x - physicalCarrierCenter
          (decimalGap ((10 : ℤ) ^ β) : ℚ)
          (decimalLift ((10 : ℤ) ^ β) : ℚ)
          (code (nearyMarker β) : ℚ)
          (hiddenRuleUpperCode β) (hiddenRuleLowerCode β body))
        (2 * β + 3) (2 * β + 3) ↔
      HasDecimalShell
        (x - physicalCarrierCenter
          (decimalGap ((10 : ℤ) ^ β) : ℚ)
          (decimalLift ((10 : ℤ) ^ β) : ℚ)
          (code (nearyMarker β) : ℚ)
          (hiddenEraseUpperCode β) (hiddenEraseLowerCode β body))
        (2 * β + 3) (2 * β + 3) := by
  obtain ⟨gap_unit, lift_unit, marker_unit, upper_unit⟩ :=
    hiddenBlocks_calibrated_decimalUnits beta_large
  obtain ⟨rule_trace_shell, erase_trace_shell⟩ :=
    hiddenBlocks_trace_hasDecimalShell body beta_large
  apply hiddenBlocks_firstCylinder_collision_of_emittedBody body
    gap_unit lift_unit marker_unit upper_unit
  · simpa [transferTrace] using rule_trace_shell
  · simpa [transferTrace] using erase_trace_shell
  · exact body_long
  · exact body_head

private theorem cycleDefect_seven
    {shift : Nat} {E τ C : ℤ}
    (shift_pos : 1 ≤ shift)
    (tau_unit : (10 : ℤ) ∣ τ - 1)
    (constant_unit : (10 : ℤ) ∣ C - 7) :
    (10 : ℤ) ∣ cycleDefect shift E τ C 7 := by
  obtain ⟨coefficient, coefficient_eq⟩ := ten_dvd_ten_pow_mul shift_pos E
  obtain ⟨tauCarry, tau_eq⟩ := tau_unit
  obtain ⟨constantCarry, constant_eq⟩ := constant_unit
  refine ⟨49 * coefficient - 7 * tauCarry + constantCarry, ?_⟩
  norm_num [cycleDefect]
  rw [show (10 : ℤ) ^ shift * E = 10 * coefficient by
    simpa [mul_comm] using coefficient_eq]
  omega

/-- Every positive decimal precision admits a stationary suffix root congruent to seven.
Successive roots can be chosen coherently because `cycleDefect_lift` preserves all previous
digits. -/
theorem exists_cycleDefect_root
    {shift : Nat} {E τ C : ℤ}
    (shift_pos : 1 ≤ shift)
    (tau_unit : (10 : ℤ) ∣ τ - 1)
    (constant_unit : (10 : ℤ) ∣ C - 7)
    (depth : Nat) (depth_pos : 1 ≤ depth) :
    ∃ x : ℤ,
      (10 : ℤ) ∣ x - 7 ∧
        (10 : ℤ) ^ depth ∣ cycleDefect shift E τ C x := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le depth_pos
  clear depth_pos
  induction offset with
  | zero =>
      exact ⟨7, by simp, cycleDefect_seven shift_pos tau_unit constant_unit⟩
  | succ offset induction =>
      obtain ⟨x, x_unit, root⟩ := induction
      obtain ⟨y, stable, lifted⟩ :=
        cycleDefect_lift shift_pos tau_unit root
      have ten_dvd_scale : (10 : ℤ) ∣ 10 ^ (offset + 1) := by
        refine ⟨10 ^ offset, ?_⟩
        rw [pow_succ]
        ring
      have y_unit : (10 : ℤ) ∣ y - 7 := by
        have stable' : (10 : ℤ) ^ (offset + 1) ∣ y - x := by
          simpa [Nat.add_comm] using stable
        have ten_dvd_difference : (10 : ℤ) ∣ y - x :=
          dvd_trans ten_dvd_scale stable'
        have sum_dvd := dvd_add ten_dvd_difference x_unit
        rw [show y - x + (x - 7) = y - 7 by ring] at sum_dvd
        exact sum_dvd
      refine ⟨y, y_unit, ?_⟩
      simpa [Nat.add_assoc] using lifted

/-- At every suffix precision, the abstract stationary root gives an exact normalized
residual factorization whose next numerator has the same carrier ratio modulo that precision.
Thus the fixed block contributes a self-loop to every bounded decimal-suffix quotient. -/
theorem exists_approximate_cycle
    {shift : Nat} {E τ C : ℤ}
    (shift_pos : 1 ≤ shift)
    (tau_unit : (10 : ℤ) ∣ τ - 1)
    (constant_unit : (10 : ℤ) ∣ C - 7)
    (precision : Nat) :
    ∃ x nextNumerator : ℤ,
      (10 : ℤ) ∣ x - 7 ∧
        τ * x - C = 10 ^ shift * nextNumerator ∧
        (10 : ℤ) ^ precision ∣ nextNumerator - E * x ^ 2 := by
  have total_pos : 1 ≤ shift + precision := by omega
  obtain ⟨x, x_unit, root⟩ :=
    exists_cycleDefect_root (E := E) (shift := shift) (C := C)
      shift_pos tau_unit constant_unit
      (shift + precision) total_pos
  obtain ⟨error, error_eq⟩ := root
  let nextNumerator : ℤ := E * x ^ 2 - 10 ^ precision * error
  refine ⟨x, nextNumerator, x_unit, ?_, ?_⟩
  · simp only [cycleDefect] at error_eq
    dsimp only [nextNumerator]
    rw [show (10 : ℤ) ^ (shift + precision) =
        10 ^ shift * 10 ^ precision by rw [pow_add]] at error_eq
    linear_combination -error_eq
  · refine ⟨-error, ?_⟩
    dsimp only [nextNumerator]
    ring

/-- Restoring the trace factor ten turns a normalized suffix factorization into the literal
generalized carrier residual consumed by `DecimalSetterDepth.peeledStep_factor`. -/
theorem peeledNumerator_factor
    {shift : Nat} {G μ τ V x nextNumerator : ℤ}
    (normalized_factor : τ * x - μ * G * V = 10 ^ shift * nextNumerator) :
    DecimalSetterDepth.peeledNumerator x 1 μ G (10 * τ) V =
      10 ^ (shift + 1) * nextNumerator := by
  rw [show DecimalSetterDepth.peeledNumerator x 1 μ G (10 * τ) V =
      10 * (τ * x - μ * G * V) by
    unfold DecimalSetterDepth.peeledNumerator
    ring]
  rw [normalized_factor, pow_succ]
  ring

/-- The residues emitted by every multi-role decimal block meet the approximate-cycle
hypotheses. In particular, the normalized trace `τ=T/10` and the product `μGV` support a
stationary carrier suffix at every finite precision. -/
theorem emittedBlock_exists_approximate_cycle
    {shift : Nat} {E τ μ G V : ℤ}
    (shift_pos : 1 ≤ shift)
    (E_unit : E ≡ 7 [ZMOD 10])
    (tau_unit : τ ≡ 1 [ZMOD 10])
    (mu_unit : μ ≡ 7 [ZMOD 10])
    (G_unit : G ≡ 3 [ZMOD 10])
    (V_unit : V ≡ 7 [ZMOD 10])
    (precision : Nat) :
    ∃ x nextNumerator nextDenominator : ℤ,
      x ≡ 7 [ZMOD 10] ∧
        nextDenominator = E * x ∧
        nextDenominator ≡ 9 [ZMOD 10] ∧
        τ * x - μ * G * V = 10 ^ shift * nextNumerator ∧
        DecimalSetterDepth.peeledNumerator x 1 μ G (10 * τ) V =
          10 ^ (shift + 1) * nextNumerator ∧
        nextNumerator ≡ x * nextDenominator [ZMOD 10 ^ precision] := by
  have tau_dvd : (10 : ℤ) ∣ τ - 1 := by
    rw [Int.modEq_iff_dvd] at tau_unit
    rw [show τ - 1 = -(1 - τ) by ring]
    exact dvd_neg.mpr tau_unit
  have constant_mod : μ * G * V ≡ 7 [ZMOD 10] := by
    calc
      μ * G * V ≡ 7 * 3 * 7 [ZMOD 10] := (mu_unit.mul G_unit).mul V_unit
      _ ≡ 7 [ZMOD 10] := by norm_num
  have constant_dvd : (10 : ℤ) ∣ μ * G * V - 7 := by
    rw [Int.modEq_iff_dvd] at constant_mod
    rw [show μ * G * V - 7 = -(7 - μ * G * V) by ring]
    exact dvd_neg.mpr constant_mod
  obtain ⟨x, nextNumerator, x_unit, factor, cycle⟩ :=
    exists_approximate_cycle shift_pos tau_dvd constant_dvd precision
  have x_mod : x ≡ 7 [ZMOD 10] := by
    rw [Int.modEq_iff_dvd]
    rw [show 7 - x = -(x - 7) by ring]
    exact dvd_neg.mpr x_unit
  have denominator_mod : E * x ≡ 9 [ZMOD 10] := by
    exact (E_unit.mul x_mod).trans (by norm_num)
  have cycle_mod : nextNumerator ≡ x * (E * x) [ZMOD 10 ^ precision] := by
    rw [Int.modEq_iff_dvd]
    rw [show x * (E * x) - nextNumerator =
        -(nextNumerator - E * x ^ 2) by ring]
    exact dvd_neg.mpr cycle
  have residual_factor := peeledNumerator_factor factor
  exact
    ⟨x, nextNumerator, E * x, x_mod, rfl, denominator_mod, factor, residual_factor,
      cycle_mod⟩

end MatrixMortality.DecimalSetterSuffix
