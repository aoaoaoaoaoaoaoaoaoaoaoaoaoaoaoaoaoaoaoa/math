import MatrixMortality.IndexedExecution
import MatrixMortality.ReturnGuardTerminalGate

/-!
# Exact-order finite quotients of decoded guard dynamics

Clearing the residual recurrence gives a homogeneous transfer matrix over any commutative
ring.  Modulo a primitive divisor of `p^period - 1`, this transfer depends only on the wait
modulo `period`.  Projectivization therefore yields a finite `ℙ¹` automaton with one additional
state recording annihilation by a singular quotient transfer.

The annihilation state is not a parser artifact: for an actual primitive integral step it is
reached exactly when the quotient prime is swallowed by primitive reduction.  Otherwise the
finite automaton follows the reduced rational orbit exactly.
-/

namespace MatrixMortality.ReturnGuard

open scoped Matrix

noncomputable section

/-- Homogeneous integral form of one decoded residual step. -/
def integralResidualTransfer
    {R : Type*} [CommRing R] (prime : R) (depth : Nat)
    (centerNumerator driftNumerator scale : R) (wait : Nat) :
    Square (Fin 2) R :=
  !![centerNumerator - scale * prime ^ wait, driftNumerator;
     prime ^ (depth * wait) * (centerNumerator - scale),
       prime ^ (depth * wait) * driftNumerator]

/-- The homogeneous transfer evaluates to the two unscaled recurrence coordinates. -/
theorem integralResidualTransfer_mulVec
    {R : Type*} [CommRing R] (prime : R) (depth : Nat)
    (centerNumerator driftNumerator scale : R) (wait : Nat)
    (numerator denominator : R) :
    integralResidualTransfer prime depth centerNumerator driftNumerator scale wait *ᵥ
        ![numerator, denominator] =
      ![
        (centerNumerator - scale * prime ^ wait) * numerator +
          driftNumerator * denominator,
        prime ^ (depth * wait) *
          ((centerNumerator - scale) * numerator +
            driftNumerator * denominator)] := by
  ext i
  fin_cases i <;>
    simp [integralResidualTransfer, Matrix.mulVec, Matrix.dotProduct,
      Fin.sum_univ_succ]
  ring

/-- An integral step is exactly the homogeneous transfer, before primitive reduction. -/
theorem integralResidualTransfer_mulVec_of_integralStep
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {numerator denominator nextNumerator nextDenominator : ℤ}
    (step :
      IntegralStep prime depth centerNumerator driftNumerator scale
        wait numerator denominator nextNumerator nextDenominator) :
    integralResidualTransfer (prime : ℤ) depth centerNumerator
          driftNumerator scale wait *ᵥ ![numerator, denominator] =
      (prime : ℤ) ^ (depth * wait) •
        ![nextNumerator, nextDenominator] := by
  rw [integralResidualTransfer_mulVec]
  ext i
  fin_cases i
  · simpa [integralStepNumerator] using step.1.symm
  · simp [step.2, terminalDefect]

/-- Powers collapse modulo any certified period. -/
theorem pow_eq_pow_mod_of_pow_eq_one
    {M : Type*} [Monoid M] (element : M) {period : Nat}
    (periodic : element ^ period = 1) (exponent : Nat) :
    element ^ exponent = element ^ (exponent % period) :=
  pow_eq_pow_mod exponent periodic

/-- Every entry of the residual transfer depends only on the wait modulo a certified period. -/
theorem integralResidualTransfer_mod
    {R : Type*} [CommRing R] (prime : R) (depth : Nat)
    (centerNumerator driftNumerator scale : R) {period : Nat}
    (periodic : prime ^ period = 1) (wait : Nat) :
    integralResidualTransfer prime depth centerNumerator driftNumerator scale wait =
      integralResidualTransfer prime depth centerNumerator driftNumerator scale
        (wait % period) := by
  have wait_power :
      prime ^ wait = prime ^ (wait % period) :=
    pow_eq_pow_mod_of_pow_eq_one prime periodic wait
  have depth_power :
      prime ^ (depth * wait) =
        prime ^ (depth * (wait % period)) := by
    rw [Nat.mul_comm depth wait, Nat.mul_comm depth (wait % period),
      pow_mul, pow_mul, wait_power]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [integralResidualTransfer, wait_power, depth_power]

/-- A finite quotient state is either a projective point or an annihilated ray. -/
abbrev QuotientState (K : Type*) := Option (ProjectiveLine.Point K)

/-- Total quotient transition.  `none` records a zero homogeneous image and is absorbing. -/
noncomputable def quotientTransition
    {K : Type*} [Field K] (matrix : Square (Fin 2) K) :
    QuotientState K → QuotientState K := by
  classical
  exact fun
    | none => none
    | some point =>
        if matrix *ᵥ ProjectiveLine.ray point = 0 then none
        else some (ProjectiveLine.act matrix point)

@[simp]
theorem quotientTransition_cancelled
    {K : Type*} [Field K] (matrix : Square (Fin 2) K) :
    quotientTransition matrix none = none := rfl

theorem quotientTransition_point_of_image_ne_zero
    {K : Type*} [Field K] (matrix : Square (Fin 2) K)
    (point : ProjectiveLine.Point K)
    (image_ne : matrix *ᵥ ProjectiveLine.ray point ≠ 0) :
    quotientTransition matrix (some point) =
      some (ProjectiveLine.act matrix point) := by
  simp [quotientTransition, image_ne]

theorem quotientTransition_point_of_image_eq_zero
    {K : Type*} [Field K] (matrix : Square (Fin 2) K)
    (point : ProjectiveLine.Point K)
    (image_zero : matrix *ᵥ ProjectiveLine.ray point = 0) :
    quotientTransition matrix (some point) = none := by
  simp [quotientTransition, image_zero]

/-- A rank-one matrix supported on its first column sends every nonzero affine point to that
column's projective ray. -/
theorem quotientTransition_firstColumn
    {K : Type*} [Field K] (top bottom z : K)
    (column_nonzero : ![top, bottom] ≠ 0) (z_ne : z ≠ 0) :
    quotientTransition !![top, 0; bottom, 0] (some (some z)) =
      some (ProjectiveLine.ofPair top bottom) := by
  let matrix : Square (Fin 2) K := !![top, 0; bottom, 0]
  have image_eq :
      matrix *ᵥ ProjectiveLine.ray (some z) =
        z • ![top, bottom] := by
    ext i
    fin_cases i <;>
      simp [matrix, ProjectiveLine.ray, Matrix.mulVec, Matrix.dotProduct,
        Fin.sum_univ_succ]
    all_goals ring
  have image_ne :
      matrix *ᵥ ProjectiveLine.ray (some z) ≠ 0 := by
    rw [image_eq]
    exact smul_ne_zero z_ne column_nonzero
  rw [quotientTransition_point_of_image_ne_zero matrix _ image_ne]
  congr 1
  have source_nonzero : ![z, (1 : K)] ≠ 0 := by
    intro source_zero
    have := congrFun source_zero 1
    simp at this
  have source_point :
      ProjectiveLine.ofPair z (1 : K) = some z := by
    simp [ProjectiveLine.ofPair]
  have pair_image_eq :
      matrix *ᵥ ![z, (1 : K)] = z • ![top, bottom] := by
    simpa [ProjectiveLine.ray] using image_eq
  rw [← source_point, ProjectiveLine.act_ofPair matrix source_nonzero,
    pair_image_eq]
  exact ProjectiveLine.ofPair_smul z z_ne top bottom

/-- Residual transfer reduced modulo one prime. -/
def quotientTransfer
    (factor prime depth : Nat) (centerNumerator driftNumerator scale : ℤ)
    (wait : Nat) : Square (Fin 2) (ZMod factor) :=
  integralResidualTransfer (prime : ZMod factor) depth
    (centerNumerator : ZMod factor) (driftNumerator : ZMod factor)
    (scale : ZMod factor) wait

/-- A primitive divisor makes the quotient transfer periodic with its exact exponent. -/
theorem quotientTransfer_mod_of_primitive
    {factor prime period depth : Nat}
    (primitive : IsPrimitivePrimeDivisor factor prime period)
    (centerNumerator driftNumerator scale : ℤ) (wait : Nat) :
    quotientTransfer factor prime depth centerNumerator driftNumerator scale wait =
      quotientTransfer factor prime depth centerNumerator driftNumerator scale
        (wait % period) := by
  apply integralResidualTransfer_mod
  simpa using
    (ZMod.natCast_eq_natCast_iff (prime ^ period) 1 factor).mpr
      primitive.modEq_one

/-- Primitive integer pairs remain nonzero homogeneous pairs in every prime quotient. -/
theorem zmod_pair_ne_zero_of_isCoprime
    {factor : Nat} [Fact factor.Prime] {numerator denominator : ℤ}
    (primitive : IsCoprime numerator denominator) :
    (![(numerator : ZMod factor), (denominator : ZMod factor)] :
      Fin 2 → ZMod factor) ≠ 0 := by
  intro pair_zero
  have numerator_zero :
      (numerator : ZMod factor) = 0 := by
    simpa using congrFun pair_zero 0
  have denominator_zero :
      (denominator : ZMod factor) = 0 := by
    simpa using congrFun pair_zero 1
  obtain ⟨left, right, bezout⟩ :=
    primitive.map (Int.castRingHom (ZMod factor))
  change
    left * (numerator : ZMod factor) +
        right * (denominator : ZMod factor) = 1 at bezout
  rw [numerator_zero, denominator_zero] at bezout
  simp at bezout

/-- Modulo a prime, one integral step is a scalar multiple of its primitively reduced pair. -/
theorem quotientTransfer_mulVec_of_integralStep
    {factor prime depth : Nat} [Fact factor.Prime]
    {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {numerator denominator nextNumerator nextDenominator
      common reducedNumerator reducedDenominator : ℤ}
    (step :
      IntegralStep prime depth centerNumerator driftNumerator scale
        wait numerator denominator nextNumerator nextDenominator)
    (numerator_reduced : nextNumerator = common * reducedNumerator)
    (denominator_reduced : nextDenominator = common * reducedDenominator) :
    quotientTransfer factor prime depth centerNumerator driftNumerator scale wait *ᵥ
        ![(numerator : ZMod factor), (denominator : ZMod factor)] =
      ((prime : ZMod factor) ^ (depth * wait) * (common : ZMod factor)) •
        ![(reducedNumerator : ZMod factor),
          (reducedDenominator : ZMod factor)] := by
  rw [quotientTransfer, integralResidualTransfer_mulVec]
  ext i
  fin_cases i
  · simp only [Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul]
    have equality :
        (centerNumerator - scale * (prime : ℤ) ^ wait) * numerator +
            driftNumerator * denominator =
          (prime : ℤ) ^ (depth * wait) * common * reducedNumerator := by
      calc
        _ = (prime : ℤ) ^ (depth * wait) * nextNumerator := by
          simpa [integralStepNumerator] using step.1.symm
        _ = _ := by rw [numerator_reduced]; ring
    simpa using congrArg (fun value : ℤ => (value : ZMod factor)) equality
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Pi.smul_apply,
      smul_eq_mul]
    have equality :
        (prime : ℤ) ^ (depth * wait) *
            ((centerNumerator - scale) * numerator +
              driftNumerator * denominator) =
          (prime : ℤ) ^ (depth * wait) * common * reducedDenominator := by
      calc
        _ = (prime : ℤ) ^ (depth * wait) * nextDenominator := by
          rw [step.2]
          rfl
        _ = _ := by rw [denominator_reduced]; ring
    simpa using congrArg (fun value : ℤ => (value : ZMod factor)) equality

/-- Integer pairs viewed as quotient projective points. -/
noncomputable def quotientPoint
    (factor : Nat) [Fact factor.Prime] (numerator denominator : ℤ) :
    ProjectiveLine.Point (ZMod factor) :=
  ProjectiveLine.ofPair (numerator : ZMod factor) (denominator : ZMod factor)

/-- If the quotient prime survives primitive reduction, the finite projective transition
follows the reduced rational state exactly. -/
theorem quotientTransition_integralStep_of_not_dvd_common
    {factor prime depth : Nat} [Fact factor.Prime]
    {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {numerator denominator nextNumerator nextDenominator
      common reducedNumerator reducedDenominator : ℤ}
    (source_primitive : IsCoprime numerator denominator)
    (step :
      IntegralStep prime depth centerNumerator driftNumerator scale
        wait numerator denominator nextNumerator nextDenominator)
    (numerator_reduced : nextNumerator = common * reducedNumerator)
    (denominator_reduced : nextDenominator = common * reducedDenominator)
    (reduced_primitive : IsCoprime reducedNumerator reducedDenominator)
    (factor_not_dvd_prime : ¬(factor : ℤ) ∣ (prime : ℤ))
    (factor_not_dvd_common : ¬(factor : ℤ) ∣ common) :
    quotientTransition
        (quotientTransfer factor prime depth centerNumerator driftNumerator scale wait)
        (some (quotientPoint factor numerator denominator)) =
      some (quotientPoint factor reducedNumerator reducedDenominator) := by
  let matrix :=
    quotientTransfer factor prime depth centerNumerator driftNumerator scale wait
  let source :=
    (![(numerator : ZMod factor), (denominator : ZMod factor)] :
      Fin 2 → ZMod factor)
  let target :=
    (![(reducedNumerator : ZMod factor),
      (reducedDenominator : ZMod factor)] : Fin 2 → ZMod factor)
  let scalar :=
    (prime : ZMod factor) ^ (depth * wait) * (common : ZMod factor)
  have source_nonzero : source ≠ 0 :=
    zmod_pair_ne_zero_of_isCoprime source_primitive
  have target_nonzero : target ≠ 0 :=
    zmod_pair_ne_zero_of_isCoprime reduced_primitive
  have prime_ne : (prime : ZMod factor) ≠ 0 := by
    intro prime_zero
    have divides : factor ∣ prime :=
      (ZMod.natCast_zmod_eq_zero_iff_dvd prime factor).mp prime_zero
    exact factor_not_dvd_prime (by exact_mod_cast divides)
  have common_ne : (common : ZMod factor) ≠ 0 := by
    intro common_zero
    exact factor_not_dvd_common
      ((ZMod.intCast_zmod_eq_zero_iff_dvd common factor).mp common_zero)
  have scalar_ne : scalar ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ prime_ne) common_ne
  have image_eq : matrix *ᵥ source = scalar • target :=
    quotientTransfer_mulVec_of_integralStep step numerator_reduced
      denominator_reduced
  have image_ne : matrix *ᵥ source ≠ 0 := by
    rw [image_eq]
    exact smul_ne_zero scalar_ne target_nonzero
  have ray_image_ne :
      matrix *ᵥ ProjectiveLine.ray
          (ProjectiveLine.ofPair (numerator : ZMod factor)
            (denominator : ZMod factor)) ≠ 0 := by
    intro ray_image_zero
    apply image_ne
    rw [show source =
      ProjectiveLine.pairWeight (numerator : ZMod factor)
          (denominator : ZMod factor) •
        ProjectiveLine.ray
          (ProjectiveLine.ofPair (numerator : ZMod factor)
            (denominator : ZMod factor)) from
      ProjectiveLine.pair_eq_weight_smul_ray _ _,
      Matrix.mulVec_smul, ray_image_zero, smul_zero]
  change
    quotientTransition matrix
        (some (ProjectiveLine.ofPair (numerator : ZMod factor)
          (denominator : ZMod factor))) =
      some (ProjectiveLine.ofPair (reducedNumerator : ZMod factor)
        (reducedDenominator : ZMod factor))
  rw [quotientTransition_point_of_image_ne_zero matrix _ ray_image_ne]
  congr 1
  rw [ProjectiveLine.act_ofPair matrix source_nonzero, image_eq]
  change
    ProjectiveLine.ofPair
        (scalar * (reducedNumerator : ZMod factor))
        (scalar * (reducedDenominator : ZMod factor)) =
      ProjectiveLine.ofPair
        (reducedNumerator : ZMod factor)
        (reducedDenominator : ZMod factor)
  exact ProjectiveLine.ofPair_smul scalar scalar_ne _ _

/-- If the quotient prime is swallowed by primitive reduction, the quotient ray is
annihilated. -/
theorem quotientTransition_integralStep_of_dvd_common
    {factor prime depth : Nat} [Fact factor.Prime]
    {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {numerator denominator nextNumerator nextDenominator
      common reducedNumerator reducedDenominator : ℤ}
    (source_primitive : IsCoprime numerator denominator)
    (step :
      IntegralStep prime depth centerNumerator driftNumerator scale
        wait numerator denominator nextNumerator nextDenominator)
    (numerator_reduced : nextNumerator = common * reducedNumerator)
    (denominator_reduced : nextDenominator = common * reducedDenominator)
    (factor_dvd_common : (factor : ℤ) ∣ common) :
    quotientTransition
        (quotientTransfer factor prime depth centerNumerator driftNumerator scale wait)
        (some (quotientPoint factor numerator denominator)) = none := by
  let matrix :=
    quotientTransfer factor prime depth centerNumerator driftNumerator scale wait
  let source :=
    (![(numerator : ZMod factor), (denominator : ZMod factor)] :
      Fin 2 → ZMod factor)
  let target :=
    (![(reducedNumerator : ZMod factor),
      (reducedDenominator : ZMod factor)] : Fin 2 → ZMod factor)
  let scalar :=
    (prime : ZMod factor) ^ (depth * wait) * (common : ZMod factor)
  have source_nonzero : source ≠ 0 :=
    zmod_pair_ne_zero_of_isCoprime source_primitive
  have common_zero : (common : ZMod factor) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd common factor).mpr factor_dvd_common
  have image_eq : matrix *ᵥ source = scalar • target :=
    quotientTransfer_mulVec_of_integralStep step numerator_reduced
      denominator_reduced
  have image_zero : matrix *ᵥ source = 0 := by
    rw [image_eq]
    simp [scalar, common_zero]
  have source_weight_ne :
      ProjectiveLine.pairWeight (numerator : ZMod factor)
          (denominator : ZMod factor) ≠ 0 :=
    ProjectiveLine.pairWeight_ne_zero source_nonzero
  have ray_image_zero :
      matrix *ᵥ ProjectiveLine.ray
          (ProjectiveLine.ofPair (numerator : ZMod factor)
            (denominator : ZMod factor)) = 0 := by
    have scaled_ray_zero :
        ProjectiveLine.pairWeight (numerator : ZMod factor)
            (denominator : ZMod factor) •
          (matrix *ᵥ ProjectiveLine.ray
            (ProjectiveLine.ofPair (numerator : ZMod factor)
              (denominator : ZMod factor))) = 0 := by
      rw [← Matrix.mulVec_smul, ← ProjectiveLine.pair_eq_weight_smul_ray]
      exact image_zero
    exact (smul_eq_zero.mp scaled_ray_zero).resolve_left source_weight_ne
  change
    quotientTransition matrix
        (some (ProjectiveLine.ofPair (numerator : ZMod factor)
          (denominator : ZMod factor))) = none
  exact quotientTransition_point_of_image_eq_zero matrix _ ray_image_zero

/-- The extra quotient state is exact: it is reached precisely when the prime is swallowed by
the current primitive reduction. -/
theorem quotientTransition_integralStep_eq_cancelled_iff
    {factor prime depth : Nat} [Fact factor.Prime]
    {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {numerator denominator nextNumerator nextDenominator
      common reducedNumerator reducedDenominator : ℤ}
    (source_primitive : IsCoprime numerator denominator)
    (step :
      IntegralStep prime depth centerNumerator driftNumerator scale
        wait numerator denominator nextNumerator nextDenominator)
    (numerator_reduced : nextNumerator = common * reducedNumerator)
    (denominator_reduced : nextDenominator = common * reducedDenominator)
    (reduced_primitive : IsCoprime reducedNumerator reducedDenominator)
    (factor_not_dvd_prime : ¬(factor : ℤ) ∣ (prime : ℤ)) :
    quotientTransition
        (quotientTransfer factor prime depth centerNumerator driftNumerator scale wait)
        (some (quotientPoint factor numerator denominator)) = none ↔
      (factor : ℤ) ∣ common := by
  constructor
  · intro cancelled
    by_contra survives
    have follows :=
      quotientTransition_integralStep_of_not_dvd_common
        source_primitive step numerator_reduced denominator_reduced
        reduced_primitive factor_not_dvd_prime survives
    rw [cancelled] at follows
    exact Option.noConfusion follows
  · exact
      quotientTransition_integralStep_of_dvd_common
        source_primitive step numerator_reduced denominator_reduced

/-- Finite projective transition relation generated by the exact-order residue classes. -/
def QuotientStep
    (factor prime period depth : Nat)
    [Fact factor.Prime]
    (centerNumerator driftNumerator scale : ℤ)
    (source target : QuotientState (ZMod factor)) : Prop :=
  ∃ residue : Fin period,
    quotientTransition
        (quotientTransfer factor prime depth centerNumerator driftNumerator scale residue)
        source = target

/-- One primitive integral step at which `factor` survives reduction. -/
def SurvivingIntegralStep
    (factor prime depth : Nat)
    (centerNumerator driftNumerator scale : ℤ)
    (source target : ℤ × ℤ) : Prop :=
  IsCoprime source.1 source.2 ∧
    IsCoprime target.1 target.2 ∧
      ∃ wait nextNumerator nextDenominator common,
        IntegralStep prime depth centerNumerator driftNumerator scale
            wait source.1 source.2 nextNumerator nextDenominator ∧
          nextNumerator = common * target.1 ∧
          nextDenominator = common * target.2 ∧
          ¬(factor : ℤ) ∣ common

/-- One primitively reduced integral step, without assuming that any quotient prime survives. -/
def PrimitiveIntegralStep
    (prime depth : Nat)
    (centerNumerator driftNumerator scale : ℤ)
    (source target : ℤ × ℤ) : Prop :=
  IsCoprime source.1 source.2 ∧
    IsCoprime target.1 target.2 ∧
      ∃ wait nextNumerator nextDenominator common,
        IntegralStep prime depth centerNumerator driftNumerator scale
            wait source.1 source.2 nextNumerator nextDenominator ∧
          nextNumerator = common * target.1 ∧
          nextDenominator = common * target.2

/-- Projective quotient state represented by one primitive integer pair. -/
noncomputable def quotientPairState
    (factor : Nat) [Fact factor.Prime] (pair : ℤ × ℤ) :
    QuotientState (ZMod factor) :=
  some (quotientPoint factor pair.1 pair.2)

/-- A primitive divisor is coprime to its base, also after coercion to the integers. -/
theorem primitivePrimeDivisor_not_dvd_base_int
    {factor prime period : Nat}
    (primitive : IsPrimitivePrimeDivisor factor prime period) :
    ¬(factor : ℤ) ∣ (prime : ℤ) := by
  intro divides
  have divides_nat : factor ∣ prime := by
    exact_mod_cast divides
  have factor_one :
      factor = 1 :=
    Nat.eq_one_of_dvd_coprimes primitive.base_coprime
      divides_nat (dvd_refl factor)
  exact primitive.prime.ne_one factor_one

/-- Every surviving integral step maps to one edge of the finite exact-order quotient. -/
theorem quotientStep_of_survivingIntegralStep
    {factor prime period depth : Nat} [Fact factor.Prime]
    (primitive : IsPrimitivePrimeDivisor factor prime period)
    (centerNumerator driftNumerator scale : ℤ)
    {source target : ℤ × ℤ}
    (step :
      SurvivingIntegralStep factor prime depth
        centerNumerator driftNumerator scale source target) :
    QuotientStep factor prime period depth
        centerNumerator driftNumerator scale
        (quotientPairState factor source)
        (quotientPairState factor target) := by
  rcases step with
    ⟨source_primitive, target_primitive, wait, nextNumerator,
      nextDenominator, common, integral, numerator_reduced,
      denominator_reduced, common_survives⟩
  let residue : Fin period :=
    ⟨wait % period, Nat.mod_lt wait primitive.exponent_positive⟩
  refine ⟨residue, ?_⟩
  have follows :=
    quotientTransition_integralStep_of_not_dvd_common
      source_primitive integral numerator_reduced denominator_reduced
      target_primitive
      (primitivePrimeDivisor_not_dvd_base_int primitive)
      common_survives
  have periodic :=
    quotientTransfer_mod_of_primitive (depth := depth) primitive
      centerNumerator driftNumerator scale wait
  change
    quotientTransition
        (quotientTransfer factor prime depth centerNumerator driftNumerator scale
          (wait % period))
        (some (quotientPoint factor source.1 source.2)) =
      some (quotientPoint factor target.1 target.2)
  rw [← periodic]
  exact follows

/-- Exact surviving executions descend, step for step, to finite quotient executions. -/
theorem survivingExecution_quotient
    {factor prime period depth steps : Nat} [Fact factor.Prime]
    (primitive : IsPrimitivePrimeDivisor factor prime period)
    (centerNumerator driftNumerator scale : ℤ)
    {source target : ℤ × ℤ}
    (execution :
      Relation.ReachesIn
        (SurvivingIntegralStep factor prime depth
          centerNumerator driftNumerator scale)
        steps source target) :
    Relation.ReachesIn
      (QuotientStep factor prime period depth
        centerNumerator driftNumerator scale)
      steps (quotientPairState factor source)
        (quotientPairState factor target) := by
  exact execution.map (quotientPairState factor)
    (quotientStep_of_survivingIntegralStep primitive
      centerNumerator driftNumerator scale)

/-- Unreachability in the finite quotient certifies that every corresponding rational
execution must swallow the primitive divisor somewhere. -/
theorem no_survivingExecution_of_not_quotientReachable
    {factor prime period depth : Nat} [Fact factor.Prime]
    (primitive : IsPrimitivePrimeDivisor factor prime period)
    (centerNumerator driftNumerator scale : ℤ)
    {source target : ℤ × ℤ}
    (unreachable :
      ¬Relation.ReflTransGen
        (QuotientStep factor prime period depth
          centerNumerator driftNumerator scale)
        (quotientPairState factor source)
        (quotientPairState factor target)) :
    ¬∃ steps,
      Relation.ReachesIn
        (SurvivingIntegralStep factor prime depth
          centerNumerator driftNumerator scale)
        steps source target := by
  rintro ⟨steps, execution⟩
  exact unreachable
    (survivingExecution_quotient primitive centerNumerator driftNumerator
      scale execution).toReflTransGen

/-- A set of quotient states closed under every exact-order residue transition. -/
def QuotientInvariant
    (factor prime period depth : Nat) [Fact factor.Prime]
    (centerNumerator driftNumerator scale : ℤ)
    (states : Set (QuotientState (ZMod factor))) : Prop :=
  ∀ state ∈ states, ∀ residue : Fin period,
    quotientTransition
        (quotientTransfer factor prime depth centerNumerator driftNumerator scale residue)
        state ∈ states

/-- Nonzero affine rays, excluding both the terminal zero ray and quotient annihilation. -/
def AffineSurvivors
    (factor : Nat) [Fact factor.Prime] :
    Set (QuotientState (ZMod factor)) :=
  {state | ∃ value : ZMod factor, value ≠ 0 ∧ state = some (some value)}

/-- If the quotient factor divides the drift numerator, every transfer loses its second
column. -/
theorem quotientTransfer_eq_firstColumn_of_drift_zero
    {factor prime depth : Nat} [Fact factor.Prime]
    {centerNumerator driftNumerator scale : ℤ} (wait : Nat)
    (drift_zero : (driftNumerator : ZMod factor) = 0) :
    quotientTransfer factor prime depth centerNumerator driftNumerator scale wait =
      !![
        (centerNumerator : ZMod factor) -
          (scale : ZMod factor) * (prime : ZMod factor) ^ wait, 0;
        (prime : ZMod factor) ^ (depth * wait) *
          ((centerNumerator : ZMod factor) - (scale : ZMod factor)), 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quotientTransfer, integralResidualTransfer, drift_zero]

/-- A drift-zero transfer with two nonzero first-column entries preserves the nonzero affine
survivor shell. -/
theorem quotientTransition_mem_affineSurvivors_of_drift_zero
    {factor prime depth : Nat} [Fact factor.Prime]
    {centerNumerator driftNumerator scale : ℤ} {wait : Nat}
    (drift_zero : (driftNumerator : ZMod factor) = 0)
    (top_ne :
      (centerNumerator : ZMod factor) -
          (scale : ZMod factor) * (prime : ZMod factor) ^ wait ≠ 0)
    (bottom_ne :
      (prime : ZMod factor) ^ (depth * wait) *
          ((centerNumerator : ZMod factor) - (scale : ZMod factor)) ≠ 0)
    {state : QuotientState (ZMod factor)}
    (state_mem : state ∈ AffineSurvivors factor) :
    quotientTransition
        (quotientTransfer factor prime depth centerNumerator driftNumerator scale wait)
        state ∈ AffineSurvivors factor := by
  obtain ⟨value, value_ne, rfl⟩ := state_mem
  rw [quotientTransfer_eq_firstColumn_of_drift_zero wait drift_zero]
  let top :=
    (centerNumerator : ZMod factor) -
      (scale : ZMod factor) * (prime : ZMod factor) ^ wait
  let bottom :=
    (prime : ZMod factor) ^ (depth * wait) *
      ((centerNumerator : ZMod factor) - (scale : ZMod factor))
  have column_ne : ![top, bottom] ≠ 0 := by
    intro column_zero
    exact top_ne (by simpa [top] using congrFun column_zero 0)
  rw [quotientTransition_firstColumn top bottom value column_ne value_ne]
  refine ⟨top / bottom, div_ne_zero top_ne bottom_ne, ?_⟩
  simp [ProjectiveLine.ofPair, bottom_ne, top, bottom]

/-- A primitive drift divisor gives a closed survivor shell whenever no wait residue hits the
center ratio. -/
theorem affineSurvivors_quotientInvariant
    {factor prime period depth : Nat} [Fact factor.Prime]
    {centerNumerator driftNumerator scale : ℤ}
    (drift_zero : (driftNumerator : ZMod factor) = 0)
    (base_ne : (prime : ZMod factor) ≠ 0)
    (terminal_denominator_ne :
      (centerNumerator : ZMod factor) - (scale : ZMod factor) ≠ 0)
    (residue_avoids_center :
      ∀ residue : Fin period,
        (centerNumerator : ZMod factor) -
            (scale : ZMod factor) *
              (prime : ZMod factor) ^ (residue : Nat) ≠ 0) :
    QuotientInvariant factor prime period depth
      centerNumerator driftNumerator scale (AffineSurvivors factor) := by
  intro state state_mem residue
  exact quotientTransition_mem_affineSurvivors_of_drift_zero
    drift_zero (residue_avoids_center residue)
    (mul_ne_zero (pow_ne_zero _ base_ne) terminal_denominator_ne) state_mem

/-- The canonical reset ray belongs to every affine survivor shell. -/
theorem quotientPairState_one_mem_affineSurvivors
    (factor : Nat) [Fact factor.Prime] :
    quotientPairState factor ((1 : ℤ), (1 : ℤ)) ∈
      AffineSurvivors factor := by
  refine ⟨1, one_ne_zero, ?_⟩
  simp [quotientPairState, quotientPoint, ProjectiveLine.ofPair]

/-- If the drift vanishes but the terminal denominator survives, the terminal residual is the
excluded affine zero ray. -/
theorem quotientPairState_terminal_not_mem_affineSurvivors
    {factor : Nat} [Fact factor.Prime]
    {centerNumerator driftNumerator scale : ℤ}
    (drift_zero : (driftNumerator : ZMod factor) = 0)
    (terminal_denominator_ne :
      (centerNumerator : ZMod factor) - (scale : ZMod factor) ≠ 0) :
    quotientPairState factor
        (-driftNumerator, centerNumerator - scale) ∉
      AffineSurvivors factor := by
  intro terminal_mem
  obtain ⟨value, value_ne, terminal_eq⟩ := terminal_mem
  have terminal_point :
      quotientPoint factor (-driftNumerator) (centerNumerator - scale) =
        some 0 := by
    simp [quotientPoint, ProjectiveLine.ofPair, drift_zero,
      terminal_denominator_ne]
  rw [quotientPairState, terminal_point] at terminal_eq
  exact value_ne (Option.some.inj (Option.some.inj terminal_eq.symm))

/-- One integral step remains in every quotient invariant which excludes annihilation. -/
theorem primitiveIntegralStep_mem_quotientInvariant
    {factor prime period depth : Nat} [Fact factor.Prime]
    (primitive : IsPrimitivePrimeDivisor factor prime period)
    (centerNumerator driftNumerator scale : ℤ)
    {states : Set (QuotientState (ZMod factor))}
    (closed :
      QuotientInvariant factor prime period depth
        centerNumerator driftNumerator scale states)
    (cancelled_absent : none ∉ states)
    {source target : ℤ × ℤ}
    (source_mem : quotientPairState factor source ∈ states)
    (step :
      PrimitiveIntegralStep prime depth
        centerNumerator driftNumerator scale source target) :
    quotientPairState factor target ∈ states := by
  rcases step with
    ⟨source_primitive, target_primitive, wait, nextNumerator,
      nextDenominator, common, integral, numerator_reduced,
      denominator_reduced⟩
  let residue : Fin period :=
    ⟨wait % period, Nat.mod_lt wait primitive.exponent_positive⟩
  have periodic :=
    quotientTransfer_mod_of_primitive (depth := depth) primitive
      centerNumerator driftNumerator scale wait
  have residue_mem :=
    closed (quotientPairState factor source) source_mem residue
  by_cases swallowed : (factor : ℤ) ∣ common
  · have cancelled :=
      quotientTransition_integralStep_of_dvd_common
        source_primitive integral numerator_reduced denominator_reduced swallowed
    have residue_cancelled :
        quotientTransition
            (quotientTransfer factor prime depth centerNumerator driftNumerator scale
              residue)
            (quotientPairState factor source) = none := by
      change
        quotientTransition
            (quotientTransfer factor prime depth centerNumerator driftNumerator scale
              (wait % period))
            (some (quotientPoint factor source.1 source.2)) = none
      rw [← periodic]
      exact cancelled
    rw [residue_cancelled] at residue_mem
    exact (cancelled_absent residue_mem).elim
  · have follows :=
      quotientTransition_integralStep_of_not_dvd_common
        source_primitive integral numerator_reduced denominator_reduced
        target_primitive
        (primitivePrimeDivisor_not_dvd_base_int primitive) swallowed
    have residue_follows :
        quotientTransition
            (quotientTransfer factor prime depth centerNumerator driftNumerator scale
              residue)
            (quotientPairState factor source) =
          quotientPairState factor target := by
      change
        quotientTransition
            (quotientTransfer factor prime depth centerNumerator driftNumerator scale
              (wait % period))
            (some (quotientPoint factor source.1 source.2)) =
          some (quotientPoint factor target.1 target.2)
      rw [← periodic]
      exact follows
    rwa [residue_follows] at residue_mem

/-- Every primitively reduced integral execution remains inside a safe finite quotient
invariant. -/
theorem primitiveExecution_mem_quotientInvariant
    {factor prime period depth steps : Nat} [Fact factor.Prime]
    (primitive : IsPrimitivePrimeDivisor factor prime period)
    (centerNumerator driftNumerator scale : ℤ)
    {states : Set (QuotientState (ZMod factor))}
    (closed :
      QuotientInvariant factor prime period depth
        centerNumerator driftNumerator scale states)
    (cancelled_absent : none ∉ states)
    {source target : ℤ × ℤ}
    (source_mem : quotientPairState factor source ∈ states)
    (execution :
      Relation.ReachesIn
        (PrimitiveIntegralStep prime depth
          centerNumerator driftNumerator scale)
        steps source target) :
    quotientPairState factor target ∈ states := by
  induction execution with
  | refl => exact source_mem
  | head first _ induction =>
      exact induction
        (primitiveIntegralStep_mem_quotientInvariant primitive
          centerNumerator driftNumerator scale closed cancelled_absent
          source_mem first)

/-- A safe quotient invariant excluding the target is a finite certificate against every
primitive integral execution. -/
theorem no_primitiveExecution_of_quotientInvariant
    {factor prime period depth : Nat} [Fact factor.Prime]
    (primitive : IsPrimitivePrimeDivisor factor prime period)
    (centerNumerator driftNumerator scale : ℤ)
    {states : Set (QuotientState (ZMod factor))}
    (closed :
      QuotientInvariant factor prime period depth
        centerNumerator driftNumerator scale states)
    (cancelled_absent : none ∉ states)
    {source target : ℤ × ℤ}
    (source_mem : quotientPairState factor source ∈ states)
    (target_absent : quotientPairState factor target ∉ states) :
    ¬∃ steps,
      Relation.ReachesIn
        (PrimitiveIntegralStep prime depth
          centerNumerator driftNumerator scale)
        steps source target := by
  rintro ⟨steps, execution⟩
  exact target_absent
    (primitiveExecution_mem_quotientInvariant primitive
      centerNumerator driftNumerator scale closed cancelled_absent
      source_mem execution)

/-- A primitive divisor of the drift numerator certifies terminal unreachability whenever the
center ratio avoids the cyclic subgroup generated by the base. -/
theorem no_primitiveExecution_of_drift_divisor
    {factor prime period depth : Nat} [Fact factor.Prime]
    (primitive : IsPrimitivePrimeDivisor factor prime period)
    (centerNumerator driftNumerator scale : ℤ)
    (drift_zero : (driftNumerator : ZMod factor) = 0)
    (terminal_denominator_ne :
      (centerNumerator : ZMod factor) - (scale : ZMod factor) ≠ 0)
    (residue_avoids_center :
      ∀ residue : Fin period,
        (centerNumerator : ZMod factor) -
            (scale : ZMod factor) *
              (prime : ZMod factor) ^ (residue : Nat) ≠ 0) :
    ¬∃ steps,
      Relation.ReachesIn
        (PrimitiveIntegralStep prime depth
          centerNumerator driftNumerator scale)
        steps ((1 : ℤ), (1 : ℤ))
          (-driftNumerator, centerNumerator - scale) := by
  have base_ne : (prime : ZMod factor) ≠ 0 := by
    intro base_zero
    have factor_dvd_prime : factor ∣ prime :=
      (ZMod.natCast_zmod_eq_zero_iff_dvd prime factor).mp base_zero
    exact primitivePrimeDivisor_not_dvd_base_int primitive
      (by exact_mod_cast factor_dvd_prime)
  exact no_primitiveExecution_of_quotientInvariant
    primitive centerNumerator driftNumerator scale
    (affineSurvivors_quotientInvariant drift_zero base_ne
      terminal_denominator_ne residue_avoids_center)
    (by simp [AffineSurvivors])
    (quotientPairState_one_mem_affineSurvivors factor)
    (quotientPairState_terminal_not_mem_affineSurvivors
      drift_zero terminal_denominator_ne)

end
end MatrixMortality.ReturnGuard
