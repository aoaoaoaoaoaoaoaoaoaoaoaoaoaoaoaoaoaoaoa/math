import MatrixMortality.ReturnGuardCocycle

/-!
# Tangent cocycle through primitive cancellation

Primitive reduction does not destroy the terminal/cyclotomic collision.  After one decoded
step, record the reduced denominator together with the displacement of the reduced numerator
from the affine ray one.  Consecutive steps transport this pair by an explicit `2 × 2` matrix.

The determinant of that matrix is supported on the fixed parameter product and the *next*
cyclotomic factor.  Thus the blow-up from `ReturnGuardCancellationJet` is recursive: a swallowed
prime resumes as a primitive two-dimensional tangent recurrence, and another collision is
exactly passage through one kernel line of the next tangent matrix.
-/

namespace MatrixMortality.ReturnGuard

open scoped Matrix

noncomputable section

/-- Terminal and cyclotomic leading coordinates of a reduced pair.

If `power = p^(s*a)`, the two entries are the reduced terminal coordinate and the reduced
difference `power * numerator - denominator`. -/
def cancellationTangent
    {R : Type*} [Ring R] (power numerator denominator : R) : Fin 2 → R :=
  ![denominator, power * numerator - denominator]

/-- Exact transfer of tangent coordinates across the next wait.

`power` belongs to the preceding wait, while `nextWaitPower` is `p^b` for the next wait `b`.
The depth-scaled power of the next wait occurs in the *next* tangent coordinates rather than in
this matrix. -/
def tangentTransfer
    {R : Type*} [CommRing R]
    (centerNumerator driftNumerator scale power nextWaitPower : R) :
    Square (Fin 2) R :=
  !![
    centerNumerator - scale + driftNumerator * power,
      centerNumerator - scale;
    scale * (1 - nextWaitPower), scale * (1 - nextWaitPower)]

/-- Tangent coordinates are a change of basis on a homogeneous pair. -/
theorem cancellationTangent_eq
    {R : Type*} [Ring R] (power numerator denominator : R) :
    cancellationTangent power numerator denominator =
      ![denominator, power * numerator - denominator] :=
  rfl

/-- The tangent matrix transports a reduced pair to its next terminal defect and displacement. -/
theorem tangentTransfer_mulVec
    {R : Type*} [CommRing R]
    (centerNumerator driftNumerator scale power nextWaitPower : R)
    (numerator denominator : R) :
    tangentTransfer centerNumerator driftNumerator scale power nextWaitPower *ᵥ
        cancellationTangent power numerator denominator =
      power •
        ![
          (centerNumerator - scale) * numerator +
            driftNumerator * denominator,
          scale * (1 - nextWaitPower) * numerator] := by
  ext i
  fin_cases i <;>
    simp [tangentTransfer, cancellationTangent, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_succ, smul_eq_mul]
  all_goals ring

/-- The tangent transfer degenerates precisely at the fixed support or the next cyclotomic
factor. -/
theorem tangentTransfer_det
    {R : Type*} [CommRing R]
    (centerNumerator driftNumerator scale power nextWaitPower : R) :
    (tangentTransfer centerNumerator driftNumerator scale power
      nextWaitPower).det =
        driftNumerator * scale * power * (1 - nextWaitPower) := by
  rw [Matrix.det_fin_two]
  simp [tangentTransfer]
  ring

/-- Once the fixed determinant factor is a unit, the tangent determinant is associated to the
next cyclotomic term. -/
theorem tangentTransfer_det_associated_cyclotomic
    {R : Type*} [CommRing R]
    (centerNumerator driftNumerator scale power nextWaitPower : R)
    (fixed_unit : IsUnit (driftNumerator * scale * power)) :
    Associated
      (tangentTransfer centerNumerator driftNumerator scale power
        nextWaitPower).det
      (1 - nextWaitPower) := by
  rw [tangentTransfer_det]
  exact
    associated_unit_mul_left (1 - nextWaitPower)
      (driftNumerator * scale * power) fixed_unit

/-- Over a fixed-support localization, tangent transport is invertible exactly when the next
cyclotomic term is a unit. -/
theorem tangentTransfer_isUnit_iff_cyclotomic
    {R : Type*} [CommRing R]
    (centerNumerator driftNumerator scale power nextWaitPower : R)
    (fixed_unit : IsUnit (driftNumerator * scale * power)) :
    IsUnit
        (tangentTransfer centerNumerator driftNumerator scale power
          nextWaitPower) ↔
      IsUnit (1 - nextWaitPower) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  exact
    (tangentTransfer_det_associated_cyclotomic
      centerNumerator driftNumerator scale power nextWaitPower
      fixed_unit).isUnit_iff

/-- Primitive reduction divides the terminal/displacement pair by exactly the same scalar. -/
theorem cancellationTangent_of_reducedIntegralStep
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat}
    {numerator denominator nextNumerator nextDenominator
      common reducedNumerator reducedDenominator : ℤ}
    (step :
      IntegralStep prime depth centerNumerator driftNumerator scale
        wait numerator denominator nextNumerator nextDenominator)
    (numerator_reduced : nextNumerator = common * reducedNumerator)
    (denominator_reduced : nextDenominator = common * reducedDenominator) :
    common •
        cancellationTangent ((prime : ℤ) ^ (depth * wait))
          reducedNumerator reducedDenominator =
      ![
        terminalDefect centerNumerator driftNumerator scale
          numerator denominator,
        scale * (1 - (prime : ℤ) ^ wait) * numerator] := by
  ext i
  fin_cases i
  · simp [cancellationTangent, smul_eq_mul, ← denominator_reduced, step.2]
  · change
      common *
          (((prime : ℤ) ^ (depth * wait)) * reducedNumerator -
            reducedDenominator) =
        scale * (1 - (prime : ℤ) ^ wait) * numerator
    rw [← integralStep_difference step, numerator_reduced,
      denominator_reduced]
    ring

/-- Consecutive primitively reduced guard steps form one exact tangent cocycle.

The first wait contributes only its depth-scaled power.  The second wait chooses the tangent
matrix and the next tangent chart.  The normalization scalar of the second step is retained
explicitly; no quotient or nonvanishing assumption is hidden. -/
theorem tangentTransfer_of_consecutive_reduction
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {priorWait nextWait : Nat}
    {numerator denominator nextNumerator nextDenominator
      common reducedNumerator reducedDenominator : ℤ}
    (step :
      IntegralStep prime depth centerNumerator driftNumerator scale
        nextWait numerator denominator nextNumerator nextDenominator)
    (numerator_reduced : nextNumerator = common * reducedNumerator)
    (denominator_reduced : nextDenominator = common * reducedDenominator) :
    tangentTransfer centerNumerator driftNumerator scale
        ((prime : ℤ) ^ (depth * priorWait)) ((prime : ℤ) ^ nextWait) *ᵥ
          cancellationTangent ((prime : ℤ) ^ (depth * priorWait))
            numerator denominator =
      (((prime : ℤ) ^ (depth * priorWait)) * common) •
        cancellationTangent ((prime : ℤ) ^ (depth * nextWait))
          reducedNumerator reducedDenominator := by
  rw [tangentTransfer_mulVec]
  have normalized :=
    cancellationTangent_of_reducedIntegralStep step
      numerator_reduced denominator_reduced
  ext i
  fin_cases i
  · have coordinate :=
      congrFun normalized (0 : Fin 2)
    have scaled :=
      congrArg
        (fun value : ℤ =>
          (prime : ℤ) ^ (depth * priorWait) * value)
        coordinate.symm
    simpa [cancellationTangent, terminalDefect, smul_eq_mul,
      mul_assoc] using scaled
  · have coordinate :=
      congrFun normalized (1 : Fin 2)
    have scaled :=
      congrArg
        (fun value : ℤ =>
          (prime : ℤ) ^ (depth * priorWait) * value)
        coordinate.symm
    simpa [cancellationTangent, smul_eq_mul, mul_assoc] using scaled

/-- A primitive homogeneous pair remains primitive in tangent coordinates whenever its
denominator is coprime to the chart power. -/
theorem cancellationTangent_isCoprime
    {power numerator denominator : ℤ}
    (pair_primitive : IsCoprime numerator denominator)
    (denominator_power : IsCoprime denominator power) :
    IsCoprime
      (cancellationTangent power numerator denominator 0)
      (cancellationTangent power numerator denominator 1) := by
  have denominator_numerator : IsCoprime denominator numerator :=
    pair_primitive.symm
  have denominator_product : IsCoprime denominator (power * numerator) :=
    denominator_power.mul_right denominator_numerator
  have denominator_difference :
      IsCoprime denominator (power * numerator - denominator) := by
    simpa [sub_eq_add_neg, mul_comm] using
      denominator_product.add_mul_right_right (-1)
  simpa [cancellationTangent] using denominator_difference

/-- A primitive pair whose denominator survives the base prime has primitive tangent
coordinates in every depth-scaled chart. -/
theorem cancellationTangent_isCoprime_of_base
    {prime depth wait : Nat} {numerator denominator : ℤ}
    (pair_primitive : IsCoprime numerator denominator)
    (denominator_base : IsCoprime denominator (prime : ℤ)) :
    IsCoprime
      (cancellationTangent ((prime : ℤ) ^ (depth * wait))
        numerator denominator 0)
      (cancellationTangent ((prime : ℤ) ^ (depth * wait))
        numerator denominator 1) :=
  cancellationTangent_isCoprime pair_primitive denominator_base.pow_right

/-- Every common divisor created by the tangent recurrence is supported by its determinant.

This is the recursive analogue of `integralStep_commonDivisor_dvd_fullSupport`: once a
collision is blown up, the resumed primitive pair can lose only fixed parameter factors or
factors of the *next* cyclotomic term. -/
theorem tangent_commonDivisor_dvd_support
    {centerNumerator driftNumerator scale power nextWaitPower
      terminal displacement divisor : ℤ}
    (tangent_primitive : IsCoprime terminal displacement)
    (divides_top :
      divisor ∣
        (centerNumerator - scale + driftNumerator * power) * terminal +
          (centerNumerator - scale) * displacement)
    (divides_bottom :
      divisor ∣
        scale * (1 - nextWaitPower) * terminal +
          scale * (1 - nextWaitPower) * displacement) :
    divisor ∣ driftNumerator * scale * power * (1 - nextWaitPower) := by
  convert
    commonDivisor_dvd_det tangent_primitive divides_top divides_bottom using 1
  ring

/-- A scalar removed after tangent transport divides the same fixed/cyclotomic support.

The reduced output need not be assumed primitive for this one-sided conclusion: the displayed
factorization already makes `common` divide both transported coordinates. -/
theorem tangent_reductionFactor_dvd_support
    {centerNumerator driftNumerator scale power nextWaitPower
      terminal displacement common reducedTerminal reducedDisplacement : ℤ}
    (tangent_primitive : IsCoprime terminal displacement)
    (top_reduced :
      (centerNumerator - scale + driftNumerator * power) * terminal +
          (centerNumerator - scale) * displacement =
        common * reducedTerminal)
    (bottom_reduced :
      scale * (1 - nextWaitPower) * terminal +
          scale * (1 - nextWaitPower) * displacement =
        common * reducedDisplacement) :
    common ∣ driftNumerator * scale * power * (1 - nextWaitPower) := by
  apply tangent_commonDivisor_dvd_support tangent_primitive
  · exact ⟨reducedTerminal, top_reduced⟩
  · exact ⟨reducedDisplacement, bottom_reduced⟩

/-- Away from fixed parameter primes and the preceding chart power, tangent cancellation is
again purely cyclotomic. -/
theorem tangent_novelDivisor_dvd_cyclotomic
    {driftNumerator scale power nextWaitPower divisor : ℤ}
    (fixed_coprime :
      IsCoprime divisor (driftNumerator * scale * power))
    (divides_support :
      divisor ∣ driftNumerator * scale * power * (1 - nextWaitPower)) :
    divisor ∣ nextWaitPower - 1 := by
  have divides_negative :
      divisor ∣ 1 - nextWaitPower :=
    fixed_coprime.dvd_of_dvd_mul_left divides_support
  simpa only [neg_sub] using dvd_neg.mpr divides_negative

/-- At a cyclotomic specialization the tangent transfer has one explicit kernel line. -/
theorem tangentTransfer_one_mulVec_eq_zero_iff
    {K : Type*} [Field K]
    (centerNumerator driftNumerator scale power terminal displacement : K) :
    tangentTransfer centerNumerator driftNumerator scale power 1 *ᵥ
        ![terminal, displacement] = 0 ↔
      (centerNumerator - scale + driftNumerator * power) * terminal +
        (centerNumerator - scale) * displacement = 0 := by
  constructor
  · intro annihilates
    have first := congrFun annihilates (0 : Fin 2)
    simpa [tangentTransfer, Matrix.mulVec, Matrix.dotProduct,
      Fin.sum_univ_succ] using first
  · intro kernel
    ext i
    fin_cases i
    · simpa [tangentTransfer, Matrix.mulVec, Matrix.dotProduct,
        Fin.sum_univ_succ] using kernel
    · simp [tangentTransfer, Matrix.mulVec, Matrix.dotProduct,
        Fin.sum_univ_succ]

/-- Modulo a cyclotomic prime, a second swallowed factor is exactly annihilation of the
normalized tangent by the next tangent transfer.

The prior depth-scaled power is a unit, so the first tangent coordinate vanishes precisely when
the next terminal defect does; the second coordinate vanishes automatically because
`p^nextWait = 1`. -/
theorem tangentTransfer_mod_eq_zero_iff_terminal
    {factor prime depth : Nat} [Fact factor.Prime]
    {centerNumerator driftNumerator scale : ℤ}
    {priorWait nextWait : Nat} {numerator denominator : ℤ}
    (nextWait_positive : 0 < nextWait)
    (next_cyclotomic :
      (factor : ℤ) ∣ (prime : ℤ) ^ nextWait - 1) :
    tangentTransfer
        (centerNumerator : ZMod factor)
        (driftNumerator : ZMod factor)
        (scale : ZMod factor)
        (((prime : ℤ) ^ (depth * priorWait) : ℤ) : ZMod factor)
        (((prime : ℤ) ^ nextWait : ℤ) : ZMod factor) *ᵥ
      cancellationTangent
        (((prime : ℤ) ^ (depth * priorWait) : ℤ) : ZMod factor)
        (numerator : ZMod factor) (denominator : ZMod factor) =
        0 ↔
      (factor : ℤ) ∣
        terminalDefect centerNumerator driftNumerator scale
          numerator denominator := by
  have next_power_one :
      (((prime : ℤ) ^ nextWait : ℤ) : ZMod factor) = 1 := by
    rw [← sub_eq_zero, ← Int.cast_one, ← Int.cast_sub,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact next_cyclotomic
  have prime_ne : (prime : ZMod factor) ≠ 0 := by
    intro prime_zero
    obtain ⟨prior, rfl⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt nextWait_positive)
    push_cast at next_power_one
    rw [pow_succ, prime_zero, mul_zero] at next_power_one
    exact zero_ne_one next_power_one
  have prior_power_ne :
      ((((prime : ℤ) ^ (depth * priorWait) : ℤ) : ZMod factor)) ≠ 0 := by
    push_cast
    exact pow_ne_zero _ prime_ne
  rw [next_power_one, tangentTransfer_mulVec]
  constructor
  · intro annihilates
    have first := congrFun annihilates (0 : Fin 2)
    simp only [Matrix.head_cons, Pi.smul_apply, smul_eq_mul] at first
    have terminal_zero :
        ((centerNumerator - scale) * numerator +
          driftNumerator * denominator : ZMod factor) = 0 :=
      (mul_eq_zero.mp first).resolve_left prior_power_ne
    apply
      (ZMod.intCast_zmod_eq_zero_iff_dvd
        (terminalDefect centerNumerator driftNumerator scale
          numerator denominator) factor).mp
    simpa [terminalDefect] using terminal_zero
  · intro divides
    have terminal_zero :
        ((terminalDefect centerNumerator driftNumerator scale
          numerator denominator : ℤ) : ZMod factor) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr divides
    ext i
    fin_cases i
    · simpa [terminalDefect] using
        congrArg
          (fun value : ZMod factor =>
            ((((prime : ℤ) ^ (depth * priorWait) : ℤ) : ZMod factor)) * value)
          terminal_zero
    · simp

end
end MatrixMortality.ReturnGuard
