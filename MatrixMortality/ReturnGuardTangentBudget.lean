import MatrixMortality.ReturnGuardIntegralLift
import MatrixMortality.ReturnGuardTangent

/-!
# Products and prescribed cancellation in the tangent cocycle

A projective trajectory retains every scalar removed by primitive reduction.  Composing its
transfer laws shows that their product is exactly the content of the final primitive ray in the
image of the initial ray.

This identity does not furnish a parameter-uniform bound.  A canonical residual source can be
made to swallow any prescribed divisor of one cyclotomic factor on its first step, while that
divisor remains coprime to the fixed determinant support.
-/

namespace MatrixMortality.ReturnGuard

open scoped Matrix

noncomputable section

/-- Matrix product in the order in which a column trajectory encounters its transfers. -/
def chronologicalProduct
    {R : Type*} [Semiring R] : List (Square (Fin 2) R) → Square (Fin 2) R
  | [] => 1
  | transfer :: transfers => chronologicalProduct transfers * transfer

/-- A sequence of projective transfer laws with every removed scalar retained. -/
inductive ScaledTrajectory
    {R : Type*} [Semiring R] :
    (Fin 2 → R) →
      List (Square (Fin 2) R) → List R → (Fin 2 → R) → Prop
  | nil (state : Fin 2 → R) :
      ScaledTrajectory state [] [] state
  | cons
      {source next target : Fin 2 → R}
      {transfer : Square (Fin 2) R}
      {transfers : List (Square (Fin 2) R)}
      {scalar : R} {scalars : List R}
      (step : transfer *ᵥ source = scalar • next)
      (rest : ScaledTrajectory next transfers scalars target) :
      ScaledTrajectory source
        (transfer :: transfers) (scalar :: scalars) target

/-- A complete transfer product removes exactly the product of its leg scalars. -/
theorem ScaledTrajectory.chronologicalProduct_mulVec
    {R : Type*} [CommSemiring R]
    {source target : Fin 2 → R}
    {transfers : List (Square (Fin 2) R)} {scalars : List R}
    (trajectory : ScaledTrajectory source transfers scalars target) :
    chronologicalProduct transfers *ᵥ source = scalars.prod • target := by
  induction trajectory with
  | nil state =>
      simp [chronologicalProduct]
  | @cons source next target transfer transfers scalar scalars step rest induction =>
      rw [chronologicalProduct, ← Matrix.mulVec_mulVec, step,
        Matrix.mulVec_smul, induction, smul_smul, List.prod_cons]

/-- If the terminal ray is primitive, the accumulated scalar is exactly the content of the
composed image. -/
theorem ScaledTrajectory.image_gcd
    {source target : Fin 2 → ℤ}
    {transfers : List (Square (Fin 2) ℤ)} {scalars : List ℤ}
    (trajectory : ScaledTrajectory source transfers scalars target)
    (target_primitive : IsCoprime (target 0) (target 1)) :
    Int.gcd
        ((chronologicalProduct transfers *ᵥ source) 0)
        ((chronologicalProduct transfers *ᵥ source) 1) =
      scalars.prod.natAbs := by
  rw [trajectory.chronologicalProduct_mulVec]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Int.gcd_mul_left,
    Int.isCoprime_iff_gcd_eq_one.mp target_primitive, mul_one]

/-- Drift numerator whose reset is `p^a + q p^(s a)` at scale one. -/
def prescribedResetDrift
    (prime depth wait : Nat) (centerNumerator factor : ℤ) : ℤ :=
  (prime : ℤ) ^ wait +
    factor * (prime : ℤ) ^ (depth * wait) - centerNumerator

/-- Primitive denominator after the prescribed factor has been removed. -/
def prescribedResetTargetDenominator
    (prime depth wait : Nat) (cyclotomicQuotient : ℤ) : ℤ :=
  (prime : ℤ) ^ (depth * wait) + cyclotomicQuotient

/-- The canonical source pair `(1,1)` removes the prescribed cyclotomic factor in one exact
integral guard step. -/
theorem prescribedReset_integralStep
    (prime depth wait : Nat)
    (centerNumerator factor cyclotomicQuotient : ℤ)
    (cyclotomic :
      (prime : ℤ) ^ wait - 1 = factor * cyclotomicQuotient) :
    IntegralStep prime depth centerNumerator
      (prescribedResetDrift prime depth wait centerNumerator factor) 1
      wait 1 1 factor
        (factor *
          prescribedResetTargetDenominator
            prime depth wait cyclotomicQuotient) := by
  constructor
  · simp [integralStepNumerator, prescribedResetDrift]
    ring
  · simp [terminalDefect, prescribedResetDrift,
      prescribedResetTargetDenominator]
    rw [show
      (prime : ℤ) ^ wait =
        factor * cyclotomicQuotient + 1 by linear_combination cyclotomic]
    ring

/-- The prescribed reduction is primitive, so `factor` is the complete common scalar rather
than a merely chosen divisor. -/
theorem prescribedReset_primitiveIntegralStep
    (prime depth wait : Nat)
    (centerNumerator factor cyclotomicQuotient : ℤ)
    (cyclotomic :
      (prime : ℤ) ^ wait - 1 = factor * cyclotomicQuotient) :
    PrimitiveIntegralStep prime depth centerNumerator
      (prescribedResetDrift prime depth wait centerNumerator factor) 1
      (1, 1)
      (1, prescribedResetTargetDenominator
          prime depth wait cyclotomicQuotient) := by
  refine ⟨isCoprime_one_left, isCoprime_one_left, wait, factor,
    factor *
      prescribedResetTargetDenominator
        prime depth wait cyclotomicQuotient,
    factor, prescribedReset_integralStep prime depth wait centerNumerator
      factor cyclotomicQuotient cyclotomic, by ring, rfl⟩

/-- If the factor does not divide the center offset, it remains coprime to both the base and
the fixed drift support. -/
theorem prescribedReset_factor_isCoprime_fixedSupport
    {prime depth wait : Nat}
    {centerNumerator factor cyclotomicQuotient : ℤ}
    (wait_positive : 0 < wait)
    (center_coprime : IsCoprime factor (centerNumerator - 1))
    (cyclotomic :
      (prime : ℤ) ^ wait - 1 = factor * cyclotomicQuotient) :
    IsCoprime factor
      (prescribedResetDrift prime depth wait centerNumerator factor *
        (prime : ℤ)) := by
  have factor_base :
      IsCoprime factor (prime : ℤ) :=
    divisor_pow_sub_one_isCoprime_base wait_positive
      ⟨cyclotomicQuotient, cyclotomic⟩
  have factor_drift :
      IsCoprime factor
        (prescribedResetDrift
          prime depth wait centerNumerator factor) := by
    rcases center_coprime with ⟨left, right, combination⟩
    refine ⟨left +
        (cyclotomicQuotient +
          (prime : ℤ) ^ (depth * wait)) * right,
        -right, ?_⟩
    simp [prescribedResetDrift] at combination ⊢
    rw [show
      (prime : ℤ) ^ wait =
        factor * cyclotomicQuotient + 1 by linear_combination cyclotomic]
    linear_combination combination
  exact factor_drift.mul_right factor_base

end
end MatrixMortality.ReturnGuard
