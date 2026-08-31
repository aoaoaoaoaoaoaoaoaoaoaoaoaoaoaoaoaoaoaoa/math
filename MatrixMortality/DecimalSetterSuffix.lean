import MatrixMortality.DecimalSetterDepth
import Mathlib.Tactic

/-!
# Generalized decimal carrier suffixes

The recursive decimal carrier has no obstruction at any fixed decimal precision. For one
multi-role block, the stationary ratio equation is a quadratic whose derivative is `-1`
modulo ten. Every root therefore lifts coherently through all powers of ten. The resulting
integer factorization gives an approximate carrier self-loop at every bounded suffix depth.
-/

namespace MatrixMortality.DecimalSetterSuffix

/-- Defect in the stationary ratio equation for a generalized carrier block. Here `shift` is
the number of decimal digits removed from the normalized residual. -/
def cycleDefect (shift : Nat) (E τ C x : ℤ) : ℤ :=
  10 ^ shift * E * x ^ 2 - τ * x + C

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
