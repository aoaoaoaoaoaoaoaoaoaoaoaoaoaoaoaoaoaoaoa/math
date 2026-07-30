import MatrixMortality.ReturnGuardValuation

/-!
# Local jets through primitive cancellation

An ordinary projective quotient loses an orbit precisely when both homogeneous output
coordinates vanish modulo its prime.  The loss is removable.  Divide both coordinates by the
largest common prime power and compare the terminal-defect depth with the cyclotomic
displacement depth.  Unequal depths force one of two canonical projective exits; equal depth
retains one residue of tangent data.

The algebraic core below is independent of the guard parameters.  It is the local blow-up of a
two-coordinate transfer at one common prime-power factor.
-/

namespace MatrixMortality.ReturnGuard

noncomputable section

/-- Removing the smaller of two prime-power depths exposes the exact local output pair.

`nextDenominator` is the terminal term `π^terminalDepth * terminalUnit`, while
`power * nextNumerator - nextDenominator` is the displacement term
`π^displacementDepth * displacementUnit`.  Dividing both output coordinates by
`π ^ min terminalDepth displacementDepth` gives the displayed strict transform. -/
theorem cancellationJet_eq
    {π power terminalUnit displacementUnit nextNumerator nextDenominator
      reducedNumerator reducedDenominator : ℤ}
    {terminalDepth displacementDepth : Nat}
    (π_ne : π ≠ 0)
    (denominator_eq :
      nextDenominator = π ^ terminalDepth * terminalUnit)
    (difference_eq :
      power * nextNumerator - nextDenominator =
        π ^ displacementDepth * displacementUnit)
    (numerator_reduced :
      nextNumerator =
        π ^ min terminalDepth displacementDepth * reducedNumerator)
    (denominator_reduced :
      nextDenominator =
        π ^ min terminalDepth displacementDepth * reducedDenominator) :
    reducedDenominator =
        π ^ (terminalDepth - min terminalDepth displacementDepth) *
          terminalUnit ∧
      power * reducedNumerator =
        π ^ (terminalDepth - min terminalDepth displacementDepth) *
            terminalUnit +
          π ^ (displacementDepth - min terminalDepth displacementDepth) *
            displacementUnit := by
  let commonDepth := min terminalDepth displacementDepth
  have common_le_terminal : commonDepth ≤ terminalDepth :=
    min_le_left _ _
  have common_le_displacement : commonDepth ≤ displacementDepth :=
    min_le_right _ _
  have common_power_ne : π ^ commonDepth ≠ 0 :=
    pow_ne_zero commonDepth π_ne
  have terminal_factorization :
      π ^ terminalDepth * terminalUnit =
        π ^ commonDepth *
          (π ^ (terminalDepth - commonDepth) * terminalUnit) := by
    rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le common_le_terminal]
  have displacement_factorization :
      π ^ displacementDepth * displacementUnit =
        π ^ commonDepth *
          (π ^ (displacementDepth - commonDepth) * displacementUnit) := by
    rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le common_le_displacement]
  have reduced_denominator_eq :
      reducedDenominator =
        π ^ (terminalDepth - commonDepth) * terminalUnit := by
    apply mul_left_cancel₀ common_power_ne
    rw [← denominator_reduced, denominator_eq, terminal_factorization]
  refine ⟨reduced_denominator_eq, ?_⟩
  apply mul_left_cancel₀ common_power_ne
  calc
    π ^ commonDepth * (power * reducedNumerator) =
        power * nextNumerator := by
          rw [numerator_reduced]
          ring
    _ =
        nextDenominator + π ^ displacementDepth * displacementUnit := by
          linear_combination difference_eq
    _ =
        π ^ terminalDepth * terminalUnit +
          π ^ displacementDepth * displacementUnit := by
            rw [denominator_eq]
    _ =
        π ^ commonDepth *
          (π ^ (terminalDepth - commonDepth) * terminalUnit +
            π ^ (displacementDepth - commonDepth) *
              displacementUnit) := by
            rw [terminal_factorization, displacement_factorization]
            ring

/-- If the terminal term is shallower, cancellation exits at the projective reset ray. -/
theorem cancellationJet_of_terminalDepth_lt
    {π power terminalUnit displacementUnit nextNumerator nextDenominator
      reducedNumerator reducedDenominator : ℤ}
    {terminalDepth displacementDepth : Nat}
    (π_ne : π ≠ 0)
    (depth_lt : terminalDepth < displacementDepth)
    (denominator_eq :
      nextDenominator = π ^ terminalDepth * terminalUnit)
    (difference_eq :
      power * nextNumerator - nextDenominator =
        π ^ displacementDepth * displacementUnit)
    (numerator_reduced :
      nextNumerator = π ^ terminalDepth * reducedNumerator)
    (denominator_reduced :
      nextDenominator = π ^ terminalDepth * reducedDenominator) :
    reducedDenominator = terminalUnit ∧
      power * reducedNumerator =
        terminalUnit +
          π ^ (displacementDepth - terminalDepth) * displacementUnit := by
  have numerator_reduced' :
      nextNumerator =
        π ^ min terminalDepth displacementDepth * reducedNumerator := by
    simpa [min_eq_left depth_lt.le] using numerator_reduced
  have denominator_reduced' :
      nextDenominator =
        π ^ min terminalDepth displacementDepth * reducedDenominator := by
    simpa [min_eq_left depth_lt.le] using denominator_reduced
  simpa [min_eq_left depth_lt.le] using
    cancellationJet_eq π_ne denominator_eq difference_eq
      numerator_reduced' denominator_reduced'

/-- If the cyclotomic displacement is shallower, cancellation exits at infinity. -/
theorem cancellationJet_of_displacementDepth_lt
    {π power terminalUnit displacementUnit nextNumerator nextDenominator
      reducedNumerator reducedDenominator : ℤ}
    {terminalDepth displacementDepth : Nat}
    (π_ne : π ≠ 0)
    (depth_lt : displacementDepth < terminalDepth)
    (denominator_eq :
      nextDenominator = π ^ terminalDepth * terminalUnit)
    (difference_eq :
      power * nextNumerator - nextDenominator =
        π ^ displacementDepth * displacementUnit)
    (numerator_reduced :
      nextNumerator = π ^ displacementDepth * reducedNumerator)
    (denominator_reduced :
      nextDenominator = π ^ displacementDepth * reducedDenominator) :
    reducedDenominator =
        π ^ (terminalDepth - displacementDepth) * terminalUnit ∧
      power * reducedNumerator =
        π ^ (terminalDepth - displacementDepth) * terminalUnit +
          displacementUnit := by
  have numerator_reduced' :
      nextNumerator =
        π ^ min terminalDepth displacementDepth * reducedNumerator := by
    simpa [min_eq_right depth_lt.le] using numerator_reduced
  have denominator_reduced' :
      nextDenominator =
        π ^ min terminalDepth displacementDepth * reducedDenominator := by
    simpa [min_eq_right depth_lt.le] using denominator_reduced
  simpa [min_eq_right depth_lt.le] using
    cancellationJet_eq π_ne denominator_eq difference_eq
      numerator_reduced' denominator_reduced'

/-- Equal terminal and displacement depths retain one tangent residue. -/
theorem cancellationJet_of_depth_eq
    {π power terminalUnit displacementUnit nextNumerator nextDenominator
      reducedNumerator reducedDenominator : ℤ}
    {depth : Nat}
    (π_ne : π ≠ 0)
    (denominator_eq :
      nextDenominator = π ^ depth * terminalUnit)
    (difference_eq :
      power * nextNumerator - nextDenominator =
        π ^ depth * displacementUnit)
    (numerator_reduced :
      nextNumerator = π ^ depth * reducedNumerator)
    (denominator_reduced :
      nextDenominator = π ^ depth * reducedDenominator) :
    reducedDenominator = terminalUnit ∧
      power * reducedNumerator = terminalUnit + displacementUnit := by
  have numerator_reduced' :
      nextNumerator = π ^ min depth depth * reducedNumerator := by
    simpa using numerator_reduced
  have denominator_reduced' :
      nextDenominator = π ^ min depth depth * reducedDenominator := by
    simpa using denominator_reduced
  simpa using
    cancellationJet_eq π_ne denominator_eq difference_eq
      numerator_reduced' denominator_reduced'

/-- A positive power of the quotient modulus vanishes in its prime field. -/
private theorem cast_modulus_pow_eq_zero
    {factor exponent : Nat} [Fact factor.Prime]
    (exponent_positive : 0 < exponent) :
    (factor : ZMod factor) ^ exponent = 0 := by
  obtain ⟨prior, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt exponent_positive)
  simp [pow_succ]

/-- A shallower terminal term exits primitive cancellation at the affine ray one. -/
theorem cancellationJet_terminalDepth_lt_mod
    {factor : Nat} [Fact factor.Prime]
    {power terminalUnit displacementUnit nextNumerator nextDenominator
      reducedNumerator reducedDenominator : ℤ}
    {terminalDepth displacementDepth : Nat}
    (power_mod : (power : ZMod factor) = 1)
    (depth_lt : terminalDepth < displacementDepth)
    (denominator_eq :
      nextDenominator = (factor : ℤ) ^ terminalDepth * terminalUnit)
    (difference_eq :
      power * nextNumerator - nextDenominator =
        (factor : ℤ) ^ displacementDepth * displacementUnit)
    (numerator_reduced :
      nextNumerator =
        (factor : ℤ) ^ terminalDepth * reducedNumerator)
    (denominator_reduced :
      nextDenominator =
        (factor : ℤ) ^ terminalDepth * reducedDenominator) :
    (reducedNumerator : ZMod factor) =
      (reducedDenominator : ZMod factor) := by
  have jet :=
    cancellationJet_of_terminalDepth_lt
      (show (factor : ℤ) ≠ 0 by
        exact_mod_cast (Fact.out : Nat.Prime factor).ne_zero)
      depth_lt denominator_eq difference_eq
      numerator_reduced denominator_reduced
  have cast_equation :=
    congrArg (fun value : ℤ => (value : ZMod factor)) jet.2
  push_cast at cast_equation
  rw [power_mod,
    cast_modulus_pow_eq_zero (Nat.sub_pos_of_lt depth_lt)] at cast_equation
  have cast_denominator :=
    congrArg (fun value : ℤ => (value : ZMod factor)) jet.1
  have numerator_terminal :
      (reducedNumerator : ZMod factor) = (terminalUnit : ZMod factor) := by
    simpa using cast_equation
  have denominator_terminal :
      (reducedDenominator : ZMod factor) =
        (terminalUnit : ZMod factor) := by
    simpa using cast_denominator
  exact numerator_terminal.trans denominator_terminal.symm

/-- If the terminal leading coefficient is a unit, the shallower-terminal exit is exactly the
finite projective point one. -/
theorem cancellationJet_terminalDepth_lt_ofPair
    {factor : Nat} [Fact factor.Prime]
    {power terminalUnit displacementUnit nextNumerator nextDenominator
      reducedNumerator reducedDenominator : ℤ}
    {terminalDepth displacementDepth : Nat}
    (power_mod : (power : ZMod factor) = 1)
    (depth_lt : terminalDepth < displacementDepth)
    (terminal_unit : ¬(factor : ℤ) ∣ terminalUnit)
    (denominator_eq :
      nextDenominator = (factor : ℤ) ^ terminalDepth * terminalUnit)
    (difference_eq :
      power * nextNumerator - nextDenominator =
        (factor : ℤ) ^ displacementDepth * displacementUnit)
    (numerator_reduced :
      nextNumerator =
        (factor : ℤ) ^ terminalDepth * reducedNumerator)
    (denominator_reduced :
      nextDenominator =
        (factor : ℤ) ^ terminalDepth * reducedDenominator) :
    ProjectiveLine.ofPair
        (reducedNumerator : ZMod factor)
        (reducedDenominator : ZMod factor) =
      some 1 := by
  have jet :=
    cancellationJet_of_terminalDepth_lt
      (show (factor : ℤ) ≠ 0 by
        exact_mod_cast (Fact.out : Nat.Prime factor).ne_zero)
      depth_lt denominator_eq difference_eq
      numerator_reduced denominator_reduced
  have denominator_ne :
      (reducedDenominator : ZMod factor) ≠ 0 := by
    rw [jet.1]
    exact
      (ZMod.intCast_zmod_eq_zero_iff_dvd terminalUnit factor).not.mpr
        terminal_unit
  have numerator_eq :=
    cancellationJet_terminalDepth_lt_mod power_mod depth_lt
      denominator_eq difference_eq numerator_reduced denominator_reduced
  simp [ProjectiveLine.ofPair, denominator_ne, numerator_eq]

/-- A shallower displacement term kills the reduced denominator and retains its own leading
coefficient in the reduced numerator. -/
theorem cancellationJet_displacementDepth_lt_mod
    {factor : Nat} [Fact factor.Prime]
    {power terminalUnit displacementUnit nextNumerator nextDenominator
      reducedNumerator reducedDenominator : ℤ}
    {terminalDepth displacementDepth : Nat}
    (power_mod : (power : ZMod factor) = 1)
    (depth_lt : displacementDepth < terminalDepth)
    (denominator_eq :
      nextDenominator = (factor : ℤ) ^ terminalDepth * terminalUnit)
    (difference_eq :
      power * nextNumerator - nextDenominator =
        (factor : ℤ) ^ displacementDepth * displacementUnit)
    (numerator_reduced :
      nextNumerator =
        (factor : ℤ) ^ displacementDepth * reducedNumerator)
    (denominator_reduced :
      nextDenominator =
        (factor : ℤ) ^ displacementDepth * reducedDenominator) :
    (reducedDenominator : ZMod factor) = 0 ∧
      (reducedNumerator : ZMod factor) =
        (displacementUnit : ZMod factor) := by
  have jet :=
    cancellationJet_of_displacementDepth_lt
      (show (factor : ℤ) ≠ 0 by
        exact_mod_cast (Fact.out : Nat.Prime factor).ne_zero)
      depth_lt denominator_eq difference_eq
      numerator_reduced denominator_reduced
  constructor
  · have cast_equation :=
      congrArg (fun value : ℤ => (value : ZMod factor)) jet.1
    push_cast at cast_equation
    rw [cast_modulus_pow_eq_zero (Nat.sub_pos_of_lt depth_lt)] at cast_equation
    simpa using cast_equation
  · have cast_equation :=
      congrArg (fun value : ℤ => (value : ZMod factor)) jet.2
    push_cast at cast_equation
    rw [power_mod,
      cast_modulus_pow_eq_zero (Nat.sub_pos_of_lt depth_lt)] at cast_equation
    simpa using cast_equation

/-- If the displacement leading coefficient is a unit, the shallower-displacement exit is
projective infinity. -/
theorem cancellationJet_displacementDepth_lt_ofPair
    {factor : Nat} [Fact factor.Prime]
    {power terminalUnit displacementUnit nextNumerator nextDenominator
      reducedNumerator reducedDenominator : ℤ}
    {terminalDepth displacementDepth : Nat}
    (power_mod : (power : ZMod factor) = 1)
    (depth_lt : displacementDepth < terminalDepth)
    (displacement_unit : ¬(factor : ℤ) ∣ displacementUnit)
    (denominator_eq :
      nextDenominator = (factor : ℤ) ^ terminalDepth * terminalUnit)
    (difference_eq :
      power * nextNumerator - nextDenominator =
        (factor : ℤ) ^ displacementDepth * displacementUnit)
    (numerator_reduced :
      nextNumerator =
        (factor : ℤ) ^ displacementDepth * reducedNumerator)
    (denominator_reduced :
      nextDenominator =
        (factor : ℤ) ^ displacementDepth * reducedDenominator) :
    ProjectiveLine.ofPair
        (reducedNumerator : ZMod factor)
        (reducedDenominator : ZMod factor) =
      none ∧
      (reducedNumerator : ZMod factor) ≠ 0 := by
  obtain ⟨denominator_zero, numerator_eq⟩ :=
    cancellationJet_displacementDepth_lt_mod power_mod depth_lt
      denominator_eq difference_eq numerator_reduced denominator_reduced
  have numerator_ne :
      (reducedNumerator : ZMod factor) ≠ 0 := by
    rw [numerator_eq]
    exact
      (ZMod.intCast_zmod_eq_zero_iff_dvd displacementUnit factor).not.mpr
        displacement_unit
  exact ⟨by simp [ProjectiveLine.ofPair, denominator_zero], numerator_ne⟩

/-- Equal depths expose the tangent residue `[terminalUnit + displacementUnit : terminalUnit]`.
This is the sole noncanonical exit from primitive cancellation. -/
theorem cancellationJet_depth_eq_mod
    {factor : Nat} [Fact factor.Prime]
    {power terminalUnit displacementUnit nextNumerator nextDenominator
      reducedNumerator reducedDenominator : ℤ}
    {depth : Nat}
    (power_mod : (power : ZMod factor) = 1)
    (denominator_eq :
      nextDenominator = (factor : ℤ) ^ depth * terminalUnit)
    (difference_eq :
      power * nextNumerator - nextDenominator =
        (factor : ℤ) ^ depth * displacementUnit)
    (numerator_reduced :
      nextNumerator = (factor : ℤ) ^ depth * reducedNumerator)
    (denominator_reduced :
      nextDenominator = (factor : ℤ) ^ depth * reducedDenominator) :
    (reducedDenominator : ZMod factor) = (terminalUnit : ZMod factor) ∧
      (reducedNumerator : ZMod factor) =
        (terminalUnit + displacementUnit : ℤ) := by
  have jet :=
    cancellationJet_of_depth_eq
      (show (factor : ℤ) ≠ 0 by
        exact_mod_cast (Fact.out : Nat.Prime factor).ne_zero)
      denominator_eq difference_eq numerator_reduced denominator_reduced
  constructor
  · simpa using
      congrArg (fun value : ℤ => (value : ZMod factor)) jet.1
  · have cast_equation :=
      congrArg (fun value : ℤ => (value : ZMod factor)) jet.2
    push_cast at cast_equation
    simpa [power_mod] using cast_equation

/-- A cyclotomic divisor makes the full depth-scaled transfer power equal to one in its
quotient field. -/
theorem depthPower_mod_eq_one_of_cyclotomic
    {factor prime depth wait : Nat} [Fact factor.Prime]
    (cyclotomic_divides :
      (factor : ℤ) ∣ (prime : ℤ) ^ wait - 1) :
    (((prime : ℤ) ^ (depth * wait) : ℤ) : ZMod factor) = 1 := by
  have wait_power :
      (((prime : ℤ) ^ wait : ℤ) : ZMod factor) = 1 := by
    rw [← sub_eq_zero, ← Int.cast_one, ← Int.cast_sub,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact cyclotomic_divides
  push_cast at wait_power ⊢
  rw [Nat.mul_comm depth wait, pow_mul, wait_power, one_pow]

/-- The local projective state exposed by cancelling the smaller of two valuation depths. -/
noncomputable def localCancellationExit
    {K : Type*} [Field K] (terminalDepth displacementDepth : Nat)
    (terminalUnit displacementUnit : K) :
    ProjectiveLine.Point K :=
  if terminalDepth < displacementDepth then some 1
  else if displacementDepth < terminalDepth then none
  else
    ProjectiveLine.ofPair (terminalUnit + displacementUnit) terminalUnit

/-- The finite local state exposed by primitive integer cancellation modulo a prime factor. -/
noncomputable def cancellationExit
    (factor terminalDepth displacementDepth : Nat) [Fact factor.Prime]
    (terminalUnit displacementUnit : ℤ) :
    ProjectiveLine.Point (ZMod factor) :=
  localCancellationExit terminalDepth displacementDepth
    (terminalUnit : ZMod factor) (displacementUnit : ZMod factor)

/-- Over every field, the cancellation exceptional divisor covers the full projective line
while both leading coefficients remain nonzero. -/
theorem localCancellationExit_surjective
    {K : Type*} [Field K] (point : ProjectiveLine.Point K) :
    ∃ terminalDepth displacementDepth : Nat,
      0 < terminalDepth ∧
        0 < displacementDepth ∧
          ∃ terminalUnit displacementUnit : K,
            terminalUnit ≠ 0 ∧
              displacementUnit ≠ 0 ∧
                localCancellationExit terminalDepth displacementDepth
                    terminalUnit displacementUnit =
                  point := by
  cases point with
  | none =>
      exact ⟨2, 1, by omega, by omega, 1, 1, one_ne_zero, one_ne_zero, by
        simp [localCancellationExit]⟩
  | some value =>
      by_cases value_one : value = 1
      · subst value
        exact ⟨1, 2, by omega, by omega, 1, 1, one_ne_zero, one_ne_zero, by
          simp [localCancellationExit]⟩
      · refine ⟨1, 1, by omega, by omega, 1, value - 1,
          one_ne_zero, sub_ne_zero.mpr value_one, ?_⟩
        simp [localCancellationExit, ProjectiveLine.ofPair]

/-- The exceptional divisor of primitive cancellation maps onto the entire projective line.

Both leading coefficients remain prime-local units and both depths are positive.  Thus no
first-order quotient state can discard any projective exit after a collision: `1` and infinity
come from unequal depths, while the equal-depth tangent covers every other affine point. -/
theorem cancellationExit_surjective
    (factor : Nat) [Fact factor.Prime]
    (point : ProjectiveLine.Point (ZMod factor)) :
    ∃ terminalDepth displacementDepth : Nat,
      0 < terminalDepth ∧
        0 < displacementDepth ∧
          ∃ terminalUnit displacementUnit : ℤ,
            ¬(factor : ℤ) ∣ terminalUnit ∧
              ¬(factor : ℤ) ∣ displacementUnit ∧
                cancellationExit factor terminalDepth displacementDepth
                    terminalUnit displacementUnit =
                  point := by
  have one_unit : ¬(factor : ℤ) ∣ (1 : ℤ) := by
    intro divides
    have cast_zero :
        (1 : ZMod factor) = 0 :=
      by simpa using
        (ZMod.intCast_zmod_eq_zero_iff_dvd 1 factor).mpr divides
    exact one_ne_zero cast_zero
  cases point with
  | none =>
      exact ⟨2, 1, by omega, by omega, 1, 1, one_unit, one_unit, by
        simp [cancellationExit, localCancellationExit]⟩
  | some value =>
      by_cases value_one : value = 1
      · subst value
        exact ⟨1, 2, by omega, by omega, 1, 1, one_unit, one_unit, by
          simp [cancellationExit, localCancellationExit]⟩
      · obtain ⟨displacementUnit, displacement_eq⟩ :=
          ZMod.intCast_surjective (value - 1)
        have displacement_unit :
            ¬(factor : ℤ) ∣ displacementUnit := by
          intro divides
          have cast_zero :
              (displacementUnit : ZMod factor) = 0 :=
            (ZMod.intCast_zmod_eq_zero_iff_dvd displacementUnit factor).mpr
              divides
          rw [displacement_eq] at cast_zero
          exact value_one (sub_eq_zero.mp cast_zero)
        refine ⟨1, 1, by omega, by omega, 1, displacementUnit,
          one_unit, displacement_unit, ?_⟩
        simp [cancellationExit, localCancellationExit, ProjectiveLine.ofPair,
          displacement_eq]

/-- No fixed congruence depth determines continuation through a collision at that depth.

The two raw terminal/displacement pairs below are both zero modulo `factor ^ jetDepth`, but one
has equal leading depths and exits at zero while the other has a shallower terminal term and
exits at one.  Any complete deterministic continuation must therefore retain information beyond
every a priori fixed truncation. -/
theorem cancellationExit_escapes_fixed_truncation
    (factor jetDepth : Nat) [Fact factor.Prime] :
    ((((factor : ℤ) ^ jetDepth : ℤ) : ZMod (factor ^ jetDepth)),
        (-((factor : ℤ) ^ jetDepth) : ZMod (factor ^ jetDepth))) =
      ((((factor : ℤ) ^ jetDepth : ℤ) : ZMod (factor ^ jetDepth)),
        (((factor : ℤ) ^ (jetDepth + 1) : ℤ) :
          ZMod (factor ^ jetDepth))) ∧
      cancellationExit factor jetDepth jetDepth 1 (-1) ≠
        cancellationExit factor jetDepth (jetDepth + 1) 1 1 := by
  constructor
  · apply Prod.ext
    · rfl
    · have base_zero :
          (((factor : ℤ) ^ jetDepth : ℤ) :
              ZMod (factor ^ jetDepth)) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        simp
      have successor_zero :
          (((factor : ℤ) ^ (jetDepth + 1) : ℤ) :
              ZMod (factor ^ jetDepth)) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        simp [pow_succ]
      push_cast at base_zero successor_zero
      simp only [Prod.snd]
      push_cast
      rw [base_zero, successor_zero, neg_zero]
  · have factor_nontrivial :
        (0 : ZMod factor) ≠ 1 :=
      zero_ne_one
    simp [cancellationExit, localCancellationExit,
      ProjectiveLine.ofPair, factor_nontrivial]

/-- The fixed base `5` realizes every positive `3`-adic cyclotomic depth along the waits
`2 * 3 ^ (depth - 1)`. -/
theorem padicValNat_five_pow_twice_three_pow_sub_one
    (depth : Nat) (depth_positive : 0 < depth) :
    padicValNat 3 (5 ^ (2 * 3 ^ (depth - 1)) - 1) = depth := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have value_twenty_four : padicValNat 3 24 = 1 := by
    apply le_antisymm
    · by_contra not_le
      have two_le : 2 ≤ padicValNat 3 24 := by omega
      have nine_divides : 3 ^ 2 ∣ 24 :=
        (padicValNat_dvd_iff_le (by norm_num)).mpr two_le
      norm_num at nine_divides
    · exact
        (padicValNat_dvd_iff_le (by norm_num)).mp (by norm_num)
  have lte :=
    padicValNat_pow_mul_sub_one
      (factor := 3) (base := 5) (period := 2)
      (multiplier := 3 ^ (depth - 1))
      (by decide) (by norm_num) (by norm_num) (by norm_num)
      (pow_ne_zero _ (by norm_num))
  norm_num at lte
  rw [lte, value_twenty_four]
  omega

/-- Any exact cyclotomic prime-power factor can be realized as the full common factor of one
primitive integral guard step, with normalized exit zero.

The construction is uniform in the base, center, wait, and prime factor.  It proves that the
three local blow-up exits are not artifacts of unconstrained homogeneous coordinates: equal
depth occurs inside the actual integral recurrence. -/
theorem primitive_integralStep_of_exact_cyclotomicDepth
    {base factor wait cancellationDepth : Nat} [Fact factor.Prime]
    (centerNumerator cyclotomicUnit : ℤ)
    (cyclotomic_eq :
      (base : ℤ) ^ wait - 1 =
        (factor : ℤ) ^ cancellationDepth * cyclotomicUnit)
    (cyclotomic_unit : ¬(factor : ℤ) ∣ cyclotomicUnit) :
    ∃ sourceDenominator reducedDenominator displacementUnit : ℤ,
      IntegralStep base 2 centerNumerator 1 1 wait 1 sourceDenominator
          ((factor : ℤ) ^ cancellationDepth * factor)
          ((factor : ℤ) ^ cancellationDepth * reducedDenominator) ∧
        IsCoprime (1 : ℤ) sourceDenominator ∧
        IsCoprime (factor : ℤ) reducedDenominator ∧
        1 * (1 - (base : ℤ) ^ wait) * 1 =
          (factor : ℤ) ^ cancellationDepth * displacementUnit ∧
        ¬(factor : ℤ) ∣ displacementUnit ∧
        ProjectiveLine.ofPair
            ((factor : ℤ) : ZMod factor)
            (reducedDenominator : ZMod factor) =
          some 0 := by
  let reducedDenominator : ℤ :=
    cyclotomicUnit + factor * (base : ℤ) ^ (2 * wait)
  let terminal : ℤ :=
    (factor : ℤ) ^ cancellationDepth * reducedDenominator
  let sourceDenominator := terminal - (centerNumerator - 1)
  let displacementUnit : ℤ := -cyclotomicUnit
  have terminal_expansion :
      terminal =
        (base : ℤ) ^ wait - 1 +
          (base : ℤ) ^ (2 * wait) *
            ((factor : ℤ) ^ cancellationDepth * factor) := by
    dsimp [terminal, reducedDenominator]
    rw [cyclotomic_eq]
    ring
  have step :
      IntegralStep base 2 centerNumerator 1 1 wait 1 sourceDenominator
        ((factor : ℤ) ^ cancellationDepth * factor) terminal := by
    constructor
    · dsimp [integralStepNumerator, sourceDenominator]
      rw [terminal_expansion]
      ring
    · dsimp [terminalDefect, sourceDenominator]
      ring
  have source_primitive :
      IsCoprime (1 : ℤ) sourceDenominator :=
    ⟨1, 0, by ring⟩
  have reduced_not_divisible :
      ¬(factor : ℤ) ∣ reducedDenominator := by
    intro divides
    have divides_tail :
        (factor : ℤ) ∣ factor * (base : ℤ) ^ (2 * wait) :=
      dvd_mul_right (factor : ℤ) ((base : ℤ) ^ (2 * wait))
    have difference := dvd_sub divides divides_tail
    apply cyclotomic_unit
    simpa [reducedDenominator] using difference
  have reduced_primitive :
      IsCoprime (factor : ℤ) reducedDenominator :=
    (Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime factor))
      |>.coprime_iff_not_dvd.mpr reduced_not_divisible
  have displacement_factorization :
      1 * (1 - (base : ℤ) ^ wait) * 1 =
        (factor : ℤ) ^ cancellationDepth * displacementUnit := by
    dsimp [displacementUnit]
    linear_combination -cyclotomic_eq
  have displacement_unit :
      ¬(factor : ℤ) ∣ displacementUnit := by
    intro divides
    exact cyclotomic_unit (dvd_neg.mp divides)
  have reduced_cast_ne :
      (reducedDenominator : ZMod factor) ≠ 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd reducedDenominator factor).not.mpr
      reduced_not_divisible
  have numerator_zero :
      ((factor : ℤ) : ZMod factor) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd factor factor).mpr (dvd_refl _)
  refine ⟨sourceDenominator, reducedDenominator, displacementUnit,
    ?_, source_primitive, reduced_primitive, displacement_factorization,
    displacement_unit, ?_⟩
  · simpa [terminal] using step
  · rw [numerator_zero]
    simp [ProjectiveLine.ofPair, reduced_cast_ne]

/-- One fixed guarded integral recurrence has primitive inputs with every positive
`3`-adic cancellation depth.

The parameters `(p, s, A, D, L) = (5, 2, 29, 1, 1)` satisfy the usual guard unit
conditions.  At depth `d`, the wait `2 * 3 ^ (d - 1)` creates an exact cyclotomic
`3 ^ d` factor.  The source pair is primitive, the reduced output pair is primitive,
and its first coordinate is still divisible by `3`; hence the normalized exit is the
affine point zero. -/
theorem exists_primitive_integralStep_with_three_cancellationDepth
    (cancellationDepth : Nat) (depth_positive : 0 < cancellationDepth) :
    ∃ wait : Nat,
      ∃ sourceDenominator reducedDenominator displacementUnit : ℤ,
        IntegralStep 5 2 29 1 1 wait 1 sourceDenominator
            ((3 : ℤ) ^ cancellationDepth * 3)
            ((3 : ℤ) ^ cancellationDepth * reducedDenominator) ∧
          IsCoprime (1 : ℤ) sourceDenominator ∧
          IsCoprime (3 : ℤ) reducedDenominator ∧
          1 * (1 - (5 : ℤ) ^ wait) * 1 =
            (3 : ℤ) ^ cancellationDepth * displacementUnit ∧
          ¬(3 : ℤ) ∣ displacementUnit ∧
          ProjectiveLine.ofPair
              ((3 : ℤ) : ZMod 3)
              (reducedDenominator : ZMod 3) =
            some 0 := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let wait := 2 * 3 ^ (cancellationDepth - 1)
  have valuation :
      padicValNat 3 (5 ^ wait - 1) = cancellationDepth := by
    exact
      padicValNat_five_pow_twice_three_pow_sub_one
        cancellationDepth depth_positive
  have wait_positive : 0 < wait := by
    dsimp [wait]
    positivity
  have power_gt_one : 1 < 5 ^ wait :=
    one_lt_pow (by norm_num) (Nat.ne_of_gt wait_positive)
  have power_sub_ne : 5 ^ wait - 1 ≠ 0 :=
    Nat.sub_ne_zero_of_lt power_gt_one
  have depth_power_divides :
      3 ^ cancellationDepth ∣ 5 ^ wait - 1 := by
    rw [padicValNat_dvd_iff_le power_sub_ne, valuation]
  obtain ⟨cyclotomicUnit, cyclotomic_eq⟩ := depth_power_divides
  have cyclotomic_unit : ¬3 ∣ cyclotomicUnit := by
    intro divides
    have deeper_divides :
        3 ^ (cancellationDepth + 1) ∣ 5 ^ wait - 1 := by
      rw [cyclotomic_eq, pow_succ]
      exact Nat.mul_dvd_mul_left (3 ^ cancellationDepth) divides
    have maximal :=
      pow_succ_padicValNat_not_dvd (p := 3) power_sub_ne
    rw [valuation] at maximal
    exact maximal deeper_divides
  have cyclotomic_eq_int :
      (5 : ℤ) ^ wait - 1 =
        (3 : ℤ) ^ cancellationDepth * cyclotomicUnit := by
    have cast_sub :
        (((5 ^ wait - 1 : Nat) : ℤ)) =
          (5 : ℤ) ^ wait - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [← cast_sub]
    exact_mod_cast cyclotomic_eq
  have cyclotomic_unit_int :
      ¬(3 : ℤ) ∣ (cyclotomicUnit : ℤ) := by
    exact_mod_cast cyclotomic_unit
  obtain ⟨sourceDenominator, reducedDenominator, displacementUnit,
      properties⟩ :=
    primitive_integralStep_of_exact_cyclotomicDepth
      (base := 5) (factor := 3) (wait := wait)
      (cancellationDepth := cancellationDepth)
      29 cyclotomicUnit cyclotomic_eq_int cyclotomic_unit_int
  exact
    ⟨wait, sourceDenominator, reducedDenominator, displacementUnit,
      properties⟩

/-- Exact local continuation through a swallowed cyclotomic factor.

The conclusion uses the output pair after removing only the common power of `factor`; any
remaining common factor is a unit modulo `factor` and therefore does not alter the displayed
projective point. -/
theorem integralStep_cancellationExit
    {factor prime depth : Nat} [Fact factor.Prime]
    {centerNumerator driftNumerator scale : ℤ}
    {wait terminalDepth displacementDepth : Nat}
    {numerator denominator nextNumerator nextDenominator
      terminalUnit displacementUnit reducedNumerator reducedDenominator : ℤ}
    (step :
      IntegralStep prime depth centerNumerator driftNumerator scale
        wait numerator denominator nextNumerator nextDenominator)
    (cyclotomic_divides :
      (factor : ℤ) ∣ (prime : ℤ) ^ wait - 1)
    (terminal_factorization :
      terminalDefect centerNumerator driftNumerator scale
          numerator denominator =
        (factor : ℤ) ^ terminalDepth * terminalUnit)
    (displacement_factorization :
      scale * (1 - (prime : ℤ) ^ wait) * numerator =
        (factor : ℤ) ^ displacementDepth * displacementUnit)
    (terminal_unit : ¬(factor : ℤ) ∣ terminalUnit)
    (displacement_unit : ¬(factor : ℤ) ∣ displacementUnit)
    (numerator_reduced :
      nextNumerator =
        (factor : ℤ) ^ min terminalDepth displacementDepth *
          reducedNumerator)
    (denominator_reduced :
      nextDenominator =
        (factor : ℤ) ^ min terminalDepth displacementDepth *
          reducedDenominator) :
    ProjectiveLine.ofPair
        (reducedNumerator : ZMod factor)
        (reducedDenominator : ZMod factor) =
      cancellationExit factor terminalDepth displacementDepth
        terminalUnit displacementUnit := by
  have power_mod :
      (((prime : ℤ) ^ (depth * wait) : ℤ) : ZMod factor) = 1 :=
    depthPower_mod_eq_one_of_cyclotomic cyclotomic_divides
  have denominator_eq :
      nextDenominator =
        (factor : ℤ) ^ terminalDepth * terminalUnit := by
    rw [step.2, terminal_factorization]
  have difference_eq :
      (prime : ℤ) ^ (depth * wait) * nextNumerator - nextDenominator =
        (factor : ℤ) ^ displacementDepth * displacementUnit := by
    rw [integralStep_difference step, displacement_factorization]
  rcases lt_trichotomy terminalDepth displacementDepth with
    terminal_lt | depths_eq | displacement_lt
  · have numerator_reduced' :
        nextNumerator =
          (factor : ℤ) ^ terminalDepth * reducedNumerator := by
      simpa [min_eq_left terminal_lt.le] using numerator_reduced
    have denominator_reduced' :
        nextDenominator =
          (factor : ℤ) ^ terminalDepth * reducedDenominator := by
      simpa [min_eq_left terminal_lt.le] using denominator_reduced
    rw [cancellationExit, localCancellationExit, if_pos terminal_lt]
    exact
      cancellationJet_terminalDepth_lt_ofPair power_mod terminal_lt
        terminal_unit denominator_eq difference_eq
        numerator_reduced' denominator_reduced'
  · subst displacementDepth
    have point_coordinates :=
      cancellationJet_depth_eq_mod power_mod denominator_eq difference_eq
        (by simpa using numerator_reduced)
        (by simpa using denominator_reduced)
    rw [cancellationExit, localCancellationExit,
      if_neg (lt_irrefl terminalDepth),
      if_neg (lt_irrefl terminalDepth), point_coordinates.1,
      point_coordinates.2]
    push_cast
    rfl
  · have numerator_reduced' :
        nextNumerator =
          (factor : ℤ) ^ displacementDepth * reducedNumerator := by
      simpa [min_eq_right displacement_lt.le] using numerator_reduced
    have denominator_reduced' :
        nextDenominator =
          (factor : ℤ) ^ displacementDepth * reducedDenominator := by
      simpa [min_eq_right displacement_lt.le] using denominator_reduced
    rw [cancellationExit, localCancellationExit,
      if_neg (not_lt_of_ge displacement_lt.le),
      if_pos displacement_lt]
    exact
      (cancellationJet_displacementDepth_lt_ofPair power_mod displacement_lt
        displacement_unit denominator_eq difference_eq
        numerator_reduced' denominator_reduced').1

end
end MatrixMortality.ReturnGuard
