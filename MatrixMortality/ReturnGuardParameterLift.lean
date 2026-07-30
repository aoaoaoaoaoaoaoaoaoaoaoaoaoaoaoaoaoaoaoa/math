import MatrixMortality.ReturnGuardTangentBudget

/-!
# Parameter lifting through a primitive collision

Keep the reset fixed while moving the center by `ε`; the drift moves by `-ε`.  One homogeneous
residual transfer then changes in a single rank-one direction.  If the original image contains
a scalar factor `q` and `ε=q·t`, the same factor survives while the reduced exit moves affinely
with the new digit `t`.

Over a field, every observer that sees this direction has exactly one digit placing the exit
in its kernel.  This is the local algebra behind CRT/Hensel synthesis of successive
cyclotomic collisions.
-/

namespace MatrixMortality.ReturnGuard

open scoped Matrix

noncomputable section

/-- Rank-one direction in which a homogeneous residual image moves when the center changes and
the reset remains fixed. -/
def centerDriftTangent
    {R : Type*} [Ring R] (power numerator denominator : R) : Fin 2 → R :=
  ![numerator - denominator, power * (numerator - denominator)]

/-- Moving the center by `ε` and the drift by `-ε` changes one homogeneous transfer only along
the center-drift tangent. -/
theorem integralResidualTransfer_centerDrift_add_mulVec
    {R : Type*} [CommRing R]
    (prime : R) (depth : Nat)
    (center driftNumerator scale perturbation : R) (wait : Nat)
    (numerator denominator : R) :
    integralResidualTransfer prime depth
          (center + perturbation) (driftNumerator - perturbation)
          scale wait *ᵥ ![numerator, denominator] =
      integralResidualTransfer prime depth center driftNumerator
          scale wait *ᵥ ![numerator, denominator] +
        perturbation •
          centerDriftTangent (prime ^ (depth * wait))
            numerator denominator := by
  ext i
  fin_cases i <;>
    simp [integralResidualTransfer, centerDriftTangent,
      Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ, smul_eq_mul]
  all_goals ring

/-- A perturbation divisible by an existing image factor preserves that factor and exposes the
new parameter digit as an affine displacement of the reduced exit. -/
theorem integralResidualTransfer_centerDrift_factor
    {R : Type*} [CommRing R]
    (prime : R) (depth : Nat)
    (center driftNumerator scale common digit : R) (wait : Nat)
    (numerator denominator : R) (target : Fin 2 → R)
    (image :
      integralResidualTransfer prime depth center driftNumerator scale wait *ᵥ
          ![numerator, denominator] =
        common • target) :
    integralResidualTransfer prime depth
          (center + common * digit) (driftNumerator - common * digit)
          scale wait *ᵥ ![numerator, denominator] =
      common •
        (target +
          digit •
            centerDriftTangent (prime ^ (depth * wait))
              numerator denominator) := by
  rw [integralResidualTransfer_centerDrift_add_mulVec, image]
  ext i
  simp [mul_smul]
  ring

/-- An affine line has exactly one parameter whose image lies in a visible linear kernel. -/
theorem existsUnique_incidenceDigit
    {K : Type*} [Field K]
    (observer target direction : Fin 2 → K)
    (visible : observer ⬝ᵥ direction ≠ 0) :
    ∃! digit : K, observer ⬝ᵥ (target + digit • direction) = 0 := by
  let intercept := observer ⬝ᵥ target
  let slope := observer ⬝ᵥ direction
  refine ⟨-intercept / slope, ?_, ?_⟩
  · change
      observer ⬝ᵥ (target + (-intercept / slope) • direction) = 0
    rw [Matrix.dotProduct_add, Matrix.dotProduct_smul]
    change intercept + (-intercept / slope) * slope = 0
    rw [div_mul_cancel₀ _ visible]
    ring
  · intro digit annihilates
    rw [Matrix.dotProduct_add, Matrix.dotProduct_smul] at annihilates
    change intercept + digit * slope = 0 at annihilates
    apply (eq_div_iff visible).2
    linear_combination annihilates

/-- Whenever an observer sees the center-drift tangent, one and only one parameter digit forces
the next moving-kernel incidence. -/
theorem existsUnique_centerDriftDigit
    {K : Type*} [Field K]
    (power numerator denominator : K)
    (observer target : Fin 2 → K)
    (visible :
      observer ⬝ᵥ centerDriftTangent power numerator denominator ≠ 0) :
    ∃! digit : K,
      observer ⬝ᵥ
        (target +
          digit • centerDriftTangent power numerator denominator) = 0 :=
  existsUnique_incidenceDigit observer target
    (centerDriftTangent power numerator denominator) visible

end
end MatrixMortality.ReturnGuard
