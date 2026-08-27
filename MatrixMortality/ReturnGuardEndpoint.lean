import MatrixMortality.ReturnGuardGap

/-!
# Terminal-centered endpoint transport

The terminal linear defect and the current numerator form a homogeneous coordinate in which
the target is the second coordinate ray.  This is a fixed gauge of the integral residual
transfer, not an additional dynamical state.  Its determinant splits each primitive reduction
into complementary forward and reverse contents.
-/

namespace MatrixMortality.ReturnGuard

open MatrixMortality.PadicValuation
open scoped Matrix

noncomputable section

/-- Fixed change of coordinates from a residual pair to its terminal defect and numerator. -/
def endpointGauge
    {R : Type*} [CommRing R]
    (centerNumerator driftNumerator scale : R) :
    Square (Fin 2) R :=
  !![centerNumerator - scale, driftNumerator; 1, 0]

/-- Terminal-centered homogeneous coordinates of an integral residual pair. -/
def endpointVector
    {R : Type*} [CommRing R]
    (centerNumerator driftNumerator scale : R)
    (numerator denominator : R) : Fin 2 → R :=
  ![
    (centerNumerator - scale) * numerator +
      driftNumerator * denominator,
    numerator]

/-- Affine terminal-centered coordinate represented by a decoded residual. -/
def terminalCoordinate
    (centerNumerator driftNumerator scale : ℤ)
    (residual : ℚ) : ℚ :=
  centerNumerator - scale + driftNumerator / residual

/-- Exact-depth quotient removed by one terminal-coordinate branch. -/
def terminalTail
    (prime depth : Nat) (scale : ℤ) (wait : Nat)
    (coordinate : ℚ) : ℚ :=
  (coordinate - scale * ((prime : ℚ) ^ wait - 1)) /
    prime ^ (depth * wait)

/-- Divisor-Collatz update after the legal wait and exact-depth quotient have been decoded. -/
def terminalStep
    (centerNumerator driftNumerator scale : ℤ)
    (coordinate tail : ℚ) : ℚ :=
  centerNumerator - scale + driftNumerator * coordinate / tail

/-- One terminal-centered branch transfer. -/
def endpointTransfer
    {R : Type*} [CommRing R] (prime : R) (depth : Nat)
    (centerNumerator driftNumerator scale : R) (wait : Nat) :
    Square (Fin 2) R :=
  !![
    centerNumerator - scale +
      driftNumerator * prime ^ (depth * wait),
      -(centerNumerator - scale) * scale * (prime ^ wait - 1);
    1, -scale * (prime ^ wait - 1)]

/-- The endpoint coordinate is exactly the fixed gauge applied to the residual pair. -/
theorem endpointGauge_mulVec
    {R : Type*} [CommRing R]
    (centerNumerator driftNumerator scale numerator denominator : R) :
    endpointGauge centerNumerator driftNumerator scale *ᵥ
        ![numerator, denominator] =
      endpointVector centerNumerator driftNumerator scale
        numerator denominator := by
  ext i
  fin_cases i <;>
    simp [endpointGauge, endpointVector, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

/-- The terminal coordinate is the original guarded state translated by one and scaled by the
integral parameter denominator. -/
theorem terminalCoordinate_eq_scaled_state
    (parameters : Parameters)
    {centerNumerator driftNumerator scale : ℤ}
    (center_eq :
      parameters.center = (centerNumerator : ℚ) / scale)
    (drift_eq :
      drift parameters.center parameters.reset =
        (driftNumerator : ℚ) / scale)
    (scale_ne : scale ≠ 0) (residual : ℚ) :
    terminalCoordinate centerNumerator driftNumerator scale residual =
      scale * (stateOfResidual parameters residual - 1) := by
  have scale_ne_rat : (scale : ℚ) ≠ 0 := by
    exact_mod_cast scale_ne
  by_cases residual_zero : residual = 0
  · subst residual
    simp [terminalCoordinate, stateOfResidual, center_eq]
    field_simp [scale_ne_rat]
  · rw [terminalCoordinate, stateOfResidual, drift_eq, center_eq]
    field_simp [scale_ne_rat, residual_zero]
    ring

/-- The decoded reset is the integral terminal coordinate `A + D - L`. -/
@[simp]
theorem terminalCoordinate_one
    (centerNumerator driftNumerator scale : ℤ) :
    terminalCoordinate centerNumerator driftNumerator scale 1 =
      centerNumerator + driftNumerator - scale := by
  simp [terminalCoordinate]
  ring

/-- The decoded terminal residual is the zero terminal coordinate. -/
theorem terminalCoordinate_terminalResidual
    (parameters : Parameters)
    {centerNumerator driftNumerator scale : ℤ}
    (center_eq :
      parameters.center = (centerNumerator : ℚ) / scale)
    (drift_eq :
      drift parameters.center parameters.reset =
        (driftNumerator : ℚ) / scale)
    (scale_ne : scale ≠ 0) :
    terminalCoordinate centerNumerator driftNumerator scale
        (terminalResidual parameters) = 0 := by
  rw [terminalCoordinate_eq_scaled_state parameters
    center_eq drift_eq scale_ne]
  rw [stateOfResidual_terminalResidual]
  ring

/-- One legal decoded residual step is exactly one divisor-Collatz terminal-coordinate step. -/
theorem terminalCoordinate_residualStep
    (parameters : Parameters)
    {centerNumerator driftNumerator scale : ℤ}
    (center_eq :
      parameters.center = (centerNumerator : ℚ) / scale)
    (drift_eq :
      drift parameters.center parameters.reset =
        (driftNumerator : ℚ) / scale)
    (scale_ne : scale ≠ 0)
    {wait : Nat} {source : ℚ}
    (branch : ResidualBranch parameters wait source) :
    terminalCoordinate centerNumerator driftNumerator scale
        (residualStep parameters wait source) =
      terminalStep centerNumerator driftNumerator scale
        (terminalCoordinate centerNumerator driftNumerator scale source)
        (terminalTail parameters.prime parameters.depth scale wait
          (terminalCoordinate centerNumerator driftNumerator scale source)) := by
  have source_unit :=
    residualBranch_isUnit parameters wait source branch
  have source_ne : source ≠ 0 := source_unit.1
  have center_transform_ne :=
    centerTransform_denominator_isUnit_of_branch parameters wait source branch
  have target_ne :
      residualStep parameters wait source ≠ 0 :=
    (residualStep_isUnit_of_branch parameters wait source branch).1
  have transform_numerator_ne :
      (parameters.center - parameters.prime ^ wait) * source +
          drift parameters.center parameters.reset ≠ 0 := by
    intro numerator_zero
    apply target_ne
    rw [residualStep_eq parameters wait source center_transform_ne.1,
      numerator_zero, zero_div]
  have prime_power_ne :
      (parameters.prime : ℚ) ^ (parameters.depth * wait) ≠ 0 :=
    primePower_ne_zero parameters.prime_prime _
  have scale_ne_rat : (scale : ℚ) ≠ 0 := by
    exact_mod_cast scale_ne
  let raw : ℚ :=
    (centerNumerator - scale * (parameters.prime : ℤ) ^ wait) * source +
      driftNumerator
  let terminal : ℚ :=
    (centerNumerator - scale) * source + driftNumerator
  have raw_ne : raw ≠ 0 := by
    have raw_eq :
        raw =
          scale *
            ((parameters.center - parameters.prime ^ wait) * source +
              drift parameters.center parameters.reset) := by
      dsimp [raw]
      push_cast
      rw [drift_eq, center_eq]
      field_simp [scale_ne_rat]
    rw [raw_eq]
    exact mul_ne_zero scale_ne_rat transform_numerator_ne
  have terminal_ne : terminal ≠ 0 := by
    have terminal_eq :
        terminal =
          scale *
            ((parameters.center - 1) * source +
              drift parameters.center parameters.reset) := by
      dsimp [terminal]
      rw [drift_eq, center_eq]
      field_simp [scale_ne_rat]
    rw [terminal_eq]
    exact mul_ne_zero scale_ne_rat center_transform_ne.1
  have residual_eq :
      residualStep parameters wait source =
        raw /
          ((parameters.prime : ℚ) ^ (parameters.depth * wait) * terminal) := by
    rw [residualStep_eq parameters wait source center_transform_ne.1]
    dsimp [raw, terminal]
    push_cast
    rw [drift_eq, center_eq]
    field_simp [scale_ne_rat, prime_power_ne]
  have coordinate_eq :
      terminalCoordinate centerNumerator driftNumerator scale source =
        centerNumerator - scale + driftNumerator / source := rfl
  have tail_eq :
      terminalTail parameters.prime parameters.depth scale wait
          (terminalCoordinate centerNumerator driftNumerator scale source) =
        raw /
          ((parameters.prime : ℚ) ^ (parameters.depth * wait) * source) := by
    rw [coordinate_eq]
    dsimp [terminalTail, raw]
    push_cast
    field_simp [source_ne, prime_power_ne] ; ring
  rw [residual_eq, tail_eq, coordinate_eq]
  simp only [terminalCoordinate, terminalStep]
  field_simp [source_ne, prime_power_ne, raw_ne, terminal_ne]
  ring

/-- Endpoint transport is conjugate to the integral residual transport before any reduction. -/
theorem endpointTransfer_mul_endpointGauge
    {R : Type*} [CommRing R] (prime : R) (depth : Nat)
    (centerNumerator driftNumerator scale : R) (wait : Nat) :
    endpointTransfer prime depth centerNumerator driftNumerator scale wait *
        endpointGauge centerNumerator driftNumerator scale =
      endpointGauge centerNumerator driftNumerator scale *
        integralResidualTransfer prime depth centerNumerator
          driftNumerator scale wait := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [endpointTransfer, endpointGauge, integralResidualTransfer,
      Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals ring

/-- The branch determinant contains the forced base power and the complete cyclotomic factor. -/
theorem endpointTransfer_det
    {R : Type*} [CommRing R] (prime : R) (depth : Nat)
    (centerNumerator driftNumerator scale : R) (wait : Nat) :
    (endpointTransfer prime depth centerNumerator driftNumerator scale wait).det =
      -driftNumerator * scale * prime ^ (depth * wait) *
        (prime ^ wait - 1) := by
  rw [Matrix.det_fin_two]
  simp [endpointTransfer]
  ring

/-- Explicit adjugate of the endpoint transfer. -/
def endpointAdjugate
    {R : Type*} [CommRing R] (prime : R) (depth : Nat)
    (centerNumerator driftNumerator scale : R) (wait : Nat) :
    Square (Fin 2) R :=
  !![
    -scale * (prime ^ wait - 1),
      (centerNumerator - scale) * scale * (prime ^ wait - 1);
    -1,
      centerNumerator - scale +
        driftNumerator * prime ^ (depth * wait)]

/-- Column-product convention matching chronological branch execution. -/
def endpointProduct
    {R : Type*} [CommRing R] (prime : R) (depth : Nat)
    (centerNumerator driftNumerator scale : R) :
    List Nat → Square (Fin 2) R
  | [] => 1
  | wait :: waits =>
      endpointProduct prime depth centerNumerator driftNumerator scale waits *
        endpointTransfer prime depth centerNumerator driftNumerator scale wait

@[simp]
theorem endpointProduct_nil
    {R : Type*} [CommRing R] (prime : R) (depth : Nat)
    (centerNumerator driftNumerator scale : R) :
    endpointProduct prime depth centerNumerator driftNumerator scale [] = 1 :=
  rfl

@[simp]
theorem endpointProduct_cons
    {R : Type*} [CommRing R] (prime : R) (depth : Nat)
    (centerNumerator driftNumerator scale : R)
    (wait : Nat) (waits : List Nat) :
    endpointProduct prime depth centerNumerator driftNumerator scale
        (wait :: waits) =
      endpointProduct prime depth centerNumerator driftNumerator scale waits *
      endpointTransfer prime depth centerNumerator driftNumerator scale wait :=
  rfl

/-- One endpoint transfer commutes with change of coefficient ring. -/
theorem endpointTransfer_map
    {R S : Type*} [CommRing R] [CommRing S]
    (map : R →+* S) (prime : R) (depth : Nat)
    (centerNumerator driftNumerator scale : R) (wait : Nat) :
    (endpointTransfer prime depth centerNumerator
      driftNumerator scale wait).map map =
        endpointTransfer (map prime) depth (map centerNumerator)
          (map driftNumerator) (map scale) wait := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [endpointTransfer]

/-- Endpoint products commute with change of coefficient ring. -/
theorem endpointProduct_map
    {R S : Type*} [CommRing R] [CommRing S]
    (map : R →+* S) (prime : R) (depth : Nat)
    (centerNumerator driftNumerator scale : R) (waits : List Nat) :
    (endpointProduct prime depth centerNumerator driftNumerator scale waits).map map =
      endpointProduct (map prime) depth (map centerNumerator)
        (map driftNumerator) (map scale) waits := by
  induction waits with
  | nil => simp
  | cons wait waits induction =>
      rw [endpointProduct_cons, endpointProduct_cons, Matrix.map_mul,
        induction, endpointTransfer_map]

/-- The determinant of a whole endpoint word exposes its base-power and cyclotomic products
separately. -/
theorem endpointProduct_det
    {R : Type*} [CommRing R] (prime : R) (depth : Nat)
    (centerNumerator driftNumerator scale : R) (waits : List Nat) :
    (endpointProduct prime depth centerNumerator
        driftNumerator scale waits).det =
      (-1 : R) ^ waits.length *
        (waits.map fun wait => prime ^ (depth * wait)).prod *
        (waits.map fun wait =>
          driftNumerator * scale * (prime ^ wait - 1)).prod := by
  induction waits with
  | nil => simp
  | cons wait waits induction =>
      rw [endpointProduct_cons, Matrix.det_mul, induction,
        endpointTransfer_det]
      simp only [List.length_cons, List.map_cons, List.prod_cons, pow_succ]
      ring

/-- For a two-dimensional transfer sending one affine ray to the terminal ray, its first
coefficient times the image scalar is the determinant. -/
theorem first_mul_scalar_eq_det_of_mulVec_eq_terminal
    {R : Type*} [CommRing R]
    (matrix : Square (Fin 2) R) (source scalar : R)
    (action :
      matrix *ᵥ ![source, 1] = scalar • ![0, 1]) :
    matrix 0 0 * scalar = matrix.det := by
  have first := congrFun action 0
  have second := congrFun action 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    smul_eq_mul] at first second
  rw [Matrix.det_fin_two]
  linear_combination -(matrix 0 0) * second + matrix 1 0 * first

/-- Global endpoint factorization.  If the forward contents and their complementary reverse
contents partition every cyclotomic determinant, then the terminal word's first coefficient
is exactly the signed product of the reverse contents. -/
theorem endpointProduct_first_eq_complementProduct
    {prime depth : Nat}
    {centerNumerator driftNumerator scale : ℤ}
    (prime_ne : prime ≠ 0)
    (waits : List Nat) (forwardContents reverseContents : List ℤ)
    (forward_prod_ne : forwardContents.prod ≠ 0)
    (action :
      endpointProduct (prime : ℤ) depth centerNumerator
          driftNumerator scale waits *ᵥ
        ![centerNumerator + driftNumerator - scale, 1] =
      ((waits.map fun wait =>
          (prime : ℤ) ^ (depth * wait)).prod *
        forwardContents.prod) • ![0, 1])
    (complementary :
      forwardContents.prod * reverseContents.prod =
        (waits.map fun wait =>
          driftNumerator * scale *
            ((prime : ℤ) ^ wait - 1)).prod) :
    endpointProduct (prime : ℤ) depth centerNumerator
        driftNumerator scale waits 0 0 =
      (-1 : ℤ) ^ waits.length * reverseContents.prod := by
  let baseProduct : ℤ :=
    (waits.map fun wait =>
      (prime : ℤ) ^ (depth * wait)).prod
  have all_baseProducts :
      ∀ schedule : List Nat,
        (schedule.map fun wait =>
          (prime : ℤ) ^ (depth * wait)).prod ≠ 0 := by
    intro schedule
    induction schedule with
    | nil => simp
    | cons wait schedule induction =>
        simp only [List.map_cons, List.prod_cons]
        exact mul_ne_zero
          (pow_ne_zero _ (by exact_mod_cast prime_ne))
          induction
  have baseProduct_ne : baseProduct ≠ 0 := by
    dsimp [baseProduct]
    exact all_baseProducts waits
  have scalar_ne : baseProduct * forwardContents.prod ≠ 0 :=
    mul_ne_zero baseProduct_ne forward_prod_ne
  have coefficient_det :=
    first_mul_scalar_eq_det_of_mulVec_eq_terminal
      (endpointProduct (prime : ℤ) depth centerNumerator
        driftNumerator scale waits)
      (centerNumerator + driftNumerator - scale)
      (baseProduct * forwardContents.prod) action
  have determinant :
      (endpointProduct (prime : ℤ) depth centerNumerator
          driftNumerator scale waits).det =
        (-1 : ℤ) ^ waits.length * baseProduct *
          (forwardContents.prod * reverseContents.prod) := by
    rw [endpointProduct_det]
    dsimp [baseProduct]
    rw [complementary]
  apply mul_right_cancel₀ scalar_ne
  calc
    endpointProduct (prime : ℤ) depth centerNumerator
          driftNumerator scale waits 0 0 *
        (baseProduct * forwardContents.prod) =
      (endpointProduct (prime : ℤ) depth centerNumerator
          driftNumerator scale waits).det :=
        coefficient_det
    _ =
      (-1 : ℤ) ^ waits.length * baseProduct *
        (forwardContents.prod * reverseContents.prod) :=
        determinant
    _ =
      ((-1 : ℤ) ^ waits.length * reverseContents.prod) *
        (baseProduct * forwardContents.prod) := by ring

/-- Algebraic endpoint-ray transport once the exact-depth quotient and next value are known. -/
theorem endpointTransfer_mulVec_ray
    {K : Type*} [Field K] (prime : K) (depth : Nat)
    (centerNumerator driftNumerator scale : K) (wait : Nat)
    (coordinate tail next : K)
    (tail_ne : tail ≠ 0)
    (tail_eq :
      tail =
        (coordinate - scale * (prime ^ wait - 1)) /
          prime ^ (depth * wait))
    (next_eq :
      next =
        centerNumerator - scale +
          driftNumerator * coordinate / tail) :
    endpointTransfer prime depth centerNumerator driftNumerator scale wait *ᵥ
        ![coordinate, 1] =
      (coordinate - scale * (prime ^ wait - 1)) • ![next, 1] := by
  have denominator_ne :
      coordinate - scale * (prime ^ wait - 1) ≠ 0 := by
    intro denominator_zero
    apply tail_ne
    rw [tail_eq, denominator_zero, zero_div]
  ext i
  fin_cases i
  · simp [endpointTransfer, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, smul_eq_mul]
    rw [next_eq, tail_eq]
    field_simp [denominator_ne]
    ring
  · simp [endpointTransfer, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, smul_eq_mul]
    ring

/-- A legal residual branch has a nonzero exact-depth quotient in terminal coordinates. -/
theorem terminalTail_ne_of_residualBranch
    (parameters : Parameters)
    {centerNumerator driftNumerator scale : ℤ}
    (center_eq :
      parameters.center = (centerNumerator : ℚ) / scale)
    (drift_eq :
      drift parameters.center parameters.reset =
        (driftNumerator : ℚ) / scale)
    (scale_ne : scale ≠ 0)
    {wait : Nat} {source : ℚ}
    (branch : ResidualBranch parameters wait source) :
    terminalTail parameters.prime parameters.depth scale wait
        (terminalCoordinate centerNumerator driftNumerator scale source) ≠ 0 := by
  have source_ne :
      source ≠ 0 :=
    (residualBranch_isUnit parameters wait source branch).1
  have numerator_ne :
      (parameters.center - parameters.prime ^ wait) * source +
          drift parameters.center parameters.reset ≠ 0 := by
    have denominator :=
      centerTransform_denominator_isUnit_of_branch parameters wait source branch
    have target :=
      residualStep_isUnit_of_branch parameters wait source branch
    intro numerator_zero
    apply target.1
    rw [residualStep_eq parameters wait source denominator.1,
      numerator_zero, zero_div]
  have scale_ne_rat : (scale : ℚ) ≠ 0 := by
    exact_mod_cast scale_ne
  have power_ne :
      (parameters.prime : ℚ) ^ (parameters.depth * wait) ≠ 0 :=
    primePower_ne_zero parameters.prime_prime _
  rw [terminalTail, terminalCoordinate]
  intro tail_zero
  have cleared :
      (centerNumerator - scale * (parameters.prime : ℤ) ^ wait) * source +
          driftNumerator = 0 := by
    field_simp [source_ne, power_ne] at tail_zero
    simp only [Int.cast_natCast] at tail_zero ⊢
    linear_combination tail_zero
  apply numerator_ne
  apply mul_left_cancel₀ scale_ne_rat
  rw [mul_zero]
  rw [drift_eq, center_eq]
  field_simp [scale_ne_rat]
  simpa using cleared

/-- One legal residual branch transports its affine endpoint ray exactly. -/
theorem endpointTransfer_mulVec_terminalCoordinate
    (parameters : Parameters)
    {centerNumerator driftNumerator scale : ℤ}
    (center_eq :
      parameters.center = (centerNumerator : ℚ) / scale)
    (drift_eq :
      drift parameters.center parameters.reset =
        (driftNumerator : ℚ) / scale)
    (scale_ne : scale ≠ 0)
    {wait : Nat} {source : ℚ}
    (branch : ResidualBranch parameters wait source) :
    endpointTransfer (parameters.prime : ℚ) parameters.depth
        centerNumerator driftNumerator scale wait *ᵥ
      ![terminalCoordinate centerNumerator driftNumerator scale source, 1] =
    (terminalCoordinate centerNumerator driftNumerator scale source -
        scale * ((parameters.prime : ℚ) ^ wait - 1)) •
      ![
        terminalCoordinate centerNumerator driftNumerator scale
          (residualStep parameters wait source),
        1] := by
  apply endpointTransfer_mulVec_ray
  · exact terminalTail_ne_of_residualBranch parameters
      center_eq drift_eq scale_ne branch
  · rfl
  · exact terminalCoordinate_residualStep parameters
      center_eq drift_eq scale_ne branch

/-- A legal schedule transports the reset ray to the terminal-coordinate ray up to one scalar. -/
theorem endpointProduct_mulVec_terminalCoordinate
    (parameters : Parameters)
    {centerNumerator driftNumerator scale : ℤ}
    (center_eq :
      parameters.center = (centerNumerator : ℚ) / scale)
    (drift_eq :
      drift parameters.center parameters.reset =
        (driftNumerator : ℚ) / scale)
    (scale_ne : scale ≠ 0)
    (waits : List Nat) (source : ℚ)
    (follows : FollowsResidualSchedule parameters waits source) :
    ∃ scalar : ℚ,
      endpointProduct (parameters.prime : ℚ) parameters.depth
          centerNumerator driftNumerator scale waits *ᵥ
        ![terminalCoordinate centerNumerator driftNumerator scale source, 1] =
      scalar •
        ![
          terminalCoordinate centerNumerator driftNumerator scale
            (residualRun parameters waits source),
          1] := by
  induction waits generalizing source with
  | nil => exact ⟨1, by simp⟩
  | cons wait waits induction =>
      rw [followsResidualSchedule_cons] at follows
      obtain ⟨scalar, tail⟩ :=
        induction (residualStep parameters wait source) follows.2
      refine
        ⟨(terminalCoordinate centerNumerator driftNumerator scale source -
            scale * ((parameters.prime : ℚ) ^ wait - 1)) * scalar, ?_⟩
      rw [endpointProduct_cons, ← Matrix.mulVec_mulVec,
        endpointTransfer_mulVec_terminalCoordinate parameters
          center_eq drift_eq scale_ne follows.1,
        Matrix.mulVec_smul, tail, smul_smul]
      simp only [residualRun_cons]

/-- An integral wait word whose endpoint product sends the reset to the terminal hyperplane. -/
def EndpointTerminalWord
    (prime depth : Nat)
    (centerNumerator driftNumerator scale : ℤ)
    (waits : List Nat) : Prop :=
  (endpointProduct (prime : ℤ) depth centerNumerator
      driftNumerator scale waits *ᵥ
    ![centerNumerator + driftNumerator - scale, 1]) 0 = 0

/-- Every decoded reset-to-terminal schedule yields an integral endpoint terminal word. -/
theorem endpointTerminalWord_of_residualRun_eq_terminal
    (parameters : Parameters)
    {centerNumerator driftNumerator scale : ℤ}
    (center_eq :
      parameters.center = (centerNumerator : ℚ) / scale)
    (drift_eq :
      drift parameters.center parameters.reset =
        (driftNumerator : ℚ) / scale)
    (scale_ne : scale ≠ 0)
    (waits : List Nat)
    (follows : FollowsResidualSchedule parameters waits 1)
    (terminal :
      residualRun parameters waits 1 = terminalResidual parameters) :
    EndpointTerminalWord parameters.prime parameters.depth
      centerNumerator driftNumerator scale waits := by
  obtain ⟨scalar, action⟩ :=
    endpointProduct_mulVec_terminalCoordinate parameters
      center_eq drift_eq scale_ne waits 1 follows
  have rational_zero :
      (endpointProduct (parameters.prime : ℚ) parameters.depth
          centerNumerator driftNumerator scale waits *ᵥ
        ![(centerNumerator + driftNumerator - scale : ℤ), 1]) 0 = 0 := by
    simpa [terminal, terminalCoordinate_terminalResidual parameters
      center_eq drift_eq scale_ne] using congrFun action 0
  let cast : ℤ →+* ℚ := Int.castRingHom ℚ
  have cast_zero :
      cast
        ((endpointProduct (parameters.prime : ℤ) parameters.depth
            centerNumerator driftNumerator scale waits *ᵥ
          ![centerNumerator + driftNumerator - scale, 1]) 0) = 0 := by
    rw [RingHom.map_mulVec]
    rw [endpointProduct_map]
    simpa [cast] using rational_zero
  change
    (((endpointProduct (parameters.prime : ℤ) parameters.depth
        centerNumerator driftNumerator scale waits *ᵥ
      ![centerNumerator + driftNumerator - scale, 1]) 0 : ℤ) : ℚ) = 0
      at cast_zero
  change
    (endpointProduct (parameters.prime : ℤ) parameters.depth
        centerNumerator driftNumerator scale waits *ᵥ
      ![centerNumerator + driftNumerator - scale, 1]) 0 = 0
  exact_mod_cast cast_zero

/-- If the terminal coefficient vanishes in a field while drift and base survive, endpoint
transport preserves a nonzero first coordinate. -/
theorem endpointProduct_first_ne_of_centerDifference_eq_zero
    {K : Type*} [Field K]
    (prime : K) (depth : Nat)
    (centerNumerator driftNumerator scale : K)
    (centerDifference_zero : centerNumerator - scale = 0)
    (drift_ne : driftNumerator ≠ 0)
    (prime_ne : prime ≠ 0)
    (waits : List Nat) (source : Fin 2 → K)
    (source_first_ne : source 0 ≠ 0) :
    (endpointProduct prime depth centerNumerator
      driftNumerator scale waits *ᵥ source) 0 ≠ 0 := by
  induction waits generalizing source with
  | nil => simpa using source_first_ne
  | cons wait waits induction =>
      rw [endpointProduct_cons, ← Matrix.mulVec_mulVec]
      apply induction
      rw [show
        (endpointTransfer prime depth centerNumerator
            driftNumerator scale wait *ᵥ source) 0 =
          (centerNumerator - scale +
                driftNumerator * prime ^ (depth * wait)) * source 0 +
              (-(centerNumerator - scale) * scale *
                (prime ^ wait - 1)) * source 1 by
        simp [endpointTransfer, Matrix.mulVec, dotProduct,
          Fin.sum_univ_succ]]
      rw [centerDifference_zero]
      simp only [zero_add, zero_mul, neg_zero, add_zero]
      exact
        mul_ne_zero
          (mul_ne_zero drift_ne (pow_ne_zero _ prime_ne))
          source_first_ne

/-- On the scale boundary, each branch multiplies the first coordinate independently of the
second. -/
theorem endpointProduct_first_of_scale_eq_zero
    {K : Type*} [CommRing K]
    (prime : K) (depth : Nat)
    (centerNumerator driftNumerator scale : K)
    (scale_zero : scale = 0)
    (waits : List Nat) (source : Fin 2 → K) :
    (endpointProduct prime depth centerNumerator
        driftNumerator scale waits *ᵥ source) 0 =
      source 0 *
        (waits.map fun wait =>
          centerNumerator +
            driftNumerator * prime ^ (depth * wait)).prod := by
  induction waits generalizing source with
  | nil => simp
  | cons wait waits induction =>
      rw [endpointProduct_cons, ← Matrix.mulVec_mulVec, induction]
      simp [endpointTransfer, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ, scale_zero]
      ring

/-- On the drift boundary, the reset ray is a common eigenray of every branch. -/
theorem endpointTransfer_mulVec_driftZero_reset
    {K : Type*} [CommRing K]
    (prime : K) (depth : Nat)
    (centerNumerator driftNumerator scale : K)
    (drift_zero : driftNumerator = 0) (wait : Nat) :
    endpointTransfer prime depth centerNumerator
        driftNumerator scale wait *ᵥ
      ![centerNumerator - scale, 1] =
    (centerNumerator - scale * prime ^ wait) •
      ![centerNumerator - scale, 1] := by
  ext i
  fin_cases i <;>
    simp [endpointTransfer, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, drift_zero, smul_eq_mul]
  all_goals ring

/-- Exact drift-boundary product on the reset ray. -/
theorem endpointProduct_mulVec_driftZero_reset
    {K : Type*} [CommRing K]
    (prime : K) (depth : Nat)
    (centerNumerator driftNumerator scale : K)
    (drift_zero : driftNumerator = 0) (waits : List Nat) :
    endpointProduct prime depth centerNumerator
        driftNumerator scale waits *ᵥ
      ![centerNumerator - scale, 1] =
    (waits.map fun wait =>
      centerNumerator - scale * prime ^ wait).prod •
      ![centerNumerator - scale, 1] := by
  induction waits with
  | nil => simp
  | cons wait waits induction =>
      rw [endpointProduct_cons, ← Matrix.mulVec_mulVec,
        endpointTransfer_mulVec_driftZero_reset
          prime depth centerNumerator driftNumerator scale drift_zero wait,
        Matrix.mulVec_smul, induction, smul_smul, List.map_cons,
        List.prod_cons]

/-- Every terminal word satisfies the scale-boundary coefficient product in any prime
quotient. -/
theorem endpointTerminalWord_scale_boundary
    {factor prime depth : Nat} [Fact factor.Prime]
    {centerNumerator driftNumerator scale : ℤ}
    (scale_zero : (scale : ZMod factor) = 0)
    {waits : List Nat}
    (terminal :
      EndpointTerminalWord prime depth
        centerNumerator driftNumerator scale waits) :
    ((centerNumerator + driftNumerator : ℤ) : ZMod factor) *
        (waits.map fun wait =>
          (centerNumerator : ZMod factor) +
            (driftNumerator : ZMod factor) *
              (prime : ZMod factor) ^ (depth * wait)).prod = 0 := by
  let cast : ℤ →+* ZMod factor := Int.castRingHom (ZMod factor)
  change
    (endpointProduct (prime : ℤ) depth centerNumerator
        driftNumerator scale waits *ᵥ
      ![centerNumerator + driftNumerator - scale, 1]) 0 = 0 at terminal
  have cast_zero := congrArg cast terminal
  rw [RingHom.map_mulVec, endpointProduct_map] at cast_zero
  have vector_eq :
      (cast ∘ ![centerNumerator + driftNumerator - scale, 1]) =
        ![
          ((centerNumerator + driftNumerator - scale : ℤ) : ZMod factor),
          1] := by
    funext i
    fin_cases i <;> simp [cast]
  rw [vector_eq] at cast_zero
  have cast_zero' :
      (endpointProduct (prime : ZMod factor) depth
          (centerNumerator : ZMod factor)
          (driftNumerator : ZMod factor) (scale : ZMod factor) waits *ᵥ
        ![
          ((centerNumerator + driftNumerator - scale : ℤ) : ZMod factor),
          1]) 0 = 0 := by
    simpa [cast] using cast_zero
  rw [
    endpointProduct_first_of_scale_eq_zero
      (prime : ZMod factor) depth
      (centerNumerator : ZMod factor)
      (driftNumerator : ZMod factor) (scale : ZMod factor)
      scale_zero] at cast_zero'
  simpa [scale_zero] using cast_zero'

/-- Every terminal word satisfies the drift-boundary power product in any prime quotient. -/
theorem endpointTerminalWord_drift_boundary
    {factor prime depth : Nat} [Fact factor.Prime]
    {centerNumerator driftNumerator scale : ℤ}
    (drift_zero : (driftNumerator : ZMod factor) = 0)
    {waits : List Nat}
    (terminal :
      EndpointTerminalWord prime depth
        centerNumerator driftNumerator scale waits) :
    ((centerNumerator - scale : ℤ) : ZMod factor) *
        (waits.map fun wait =>
          (centerNumerator : ZMod factor) -
            (scale : ZMod factor) * (prime : ZMod factor) ^ wait).prod = 0 := by
  let cast : ℤ →+* ZMod factor := Int.castRingHom (ZMod factor)
  change
    (endpointProduct (prime : ℤ) depth centerNumerator
        driftNumerator scale waits *ᵥ
      ![centerNumerator + driftNumerator - scale, 1]) 0 = 0 at terminal
  have cast_zero := congrArg cast terminal
  rw [RingHom.map_mulVec, endpointProduct_map] at cast_zero
  have vector_eq :
      (cast ∘ ![centerNumerator + driftNumerator - scale, 1]) =
        ![
          ((centerNumerator - scale : ℤ) : ZMod factor),
          1] := by
    funext i
    fin_cases i <;> simp [cast, drift_zero]
  rw [vector_eq] at cast_zero
  have cast_zero' :
      (endpointProduct (prime : ZMod factor) depth
          (centerNumerator : ZMod factor)
          (driftNumerator : ZMod factor) (scale : ZMod factor) waits *ᵥ
        ![
          ((centerNumerator - scale : ℤ) : ZMod factor),
          1]) 0 = 0 := by
    simpa [cast, drift_zero] using cast_zero
  rw [Int.cast_sub] at cast_zero'
  rw [
    endpointProduct_mulVec_driftZero_reset
      (prime : ZMod factor) depth
      (centerNumerator : ZMod factor)
      (driftNumerator : ZMod factor) (scale : ZMod factor)
      drift_zero] at cast_zero'
  have product_zero :
      (waits.map fun wait =>
        (centerNumerator : ZMod factor) -
          (scale : ZMod factor) * (prime : ZMod factor) ^ wait).prod *
        ((centerNumerator - scale : ℤ) : ZMod factor) = 0 := by
    simpa only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Int.cast_sub] using cast_zero'
  calc
    ((centerNumerator - scale : ℤ) : ZMod factor) *
        (waits.map fun wait =>
          (centerNumerator : ZMod factor) -
            (scale : ZMod factor) * (prime : ZMod factor) ^ wait).prod =
      (waits.map fun wait =>
        (centerNumerator : ZMod factor) -
          (scale : ZMod factor) * (prime : ZMod factor) ^ wait).prod *
        ((centerNumerator - scale : ℤ) : ZMod factor) := mul_comm _ _
    _ = 0 := product_zero

/-- A prime dividing the terminal coefficient but neither drift nor base forbids every
terminal word. -/
theorem not_endpointTerminalWord_of_prime_dvd_centerDifference
    {factor prime depth : Nat} [Fact factor.Prime]
    {centerNumerator driftNumerator scale : ℤ}
    (centerDifference :
      (factor : ℤ) ∣ centerNumerator - scale)
    (drift_survives : ¬(factor : ℤ) ∣ driftNumerator)
    (base_survives : ¬factor ∣ prime)
    (waits : List Nat) :
    ¬EndpointTerminalWord prime depth
      centerNumerator driftNumerator scale waits := by
  intro terminal
  let cast : ℤ →+* ZMod factor := Int.castRingHom (ZMod factor)
  have centerDifference_zero :
      (centerNumerator : ZMod factor) - (scale : ZMod factor) = 0 := by
    rw [← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact centerDifference
  have drift_ne : (driftNumerator : ZMod factor) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact drift_survives
  have prime_ne : (prime : ZMod factor) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact base_survives
  have source_first_ne :
      ((centerNumerator + driftNumerator - scale : ℤ) :
        ZMod factor) ≠ 0 := by
    rw [show
      ((centerNumerator + driftNumerator - scale : ℤ) :
          ZMod factor) =
        (centerNumerator : ZMod factor) - scale + driftNumerator by
      push_cast
      ring, centerDifference_zero, zero_add]
    exact drift_ne
  have nonzero :=
    endpointProduct_first_ne_of_centerDifference_eq_zero
      (prime : ZMod factor) depth
      (centerNumerator : ZMod factor)
      (driftNumerator : ZMod factor) (scale : ZMod factor)
      centerDifference_zero drift_ne prime_ne waits
      ![
        ((centerNumerator + driftNumerator - scale : ℤ) : ZMod factor),
        1]
      source_first_ne
  apply nonzero
  change
    (endpointProduct (prime : ℤ) depth centerNumerator
        driftNumerator scale waits *ᵥ
      ![centerNumerator + driftNumerator - scale, 1]) 0 = 0 at terminal
  have cast_zero :=
    congrArg cast terminal
  rw [RingHom.map_mulVec, endpointProduct_map] at cast_zero
  have vector_eq :
      (cast ∘ ![centerNumerator + driftNumerator - scale, 1]) =
        ![
          ((centerNumerator + driftNumerator - scale : ℤ) : ZMod factor),
          1] := by
    funext i
    fin_cases i <;> simp [cast]
  rw [vector_eq] at cast_zero
  simpa [cast] using cast_zero

/-- The explicit endpoint adjugate multiplies the transfer to its determinant. -/
theorem endpointAdjugate_mul_endpointTransfer
    {R : Type*} [CommRing R] (prime : R) (depth : Nat)
    (centerNumerator driftNumerator scale : R) (wait : Nat) :
    endpointAdjugate prime depth centerNumerator driftNumerator scale wait *
        endpointTransfer prime depth centerNumerator driftNumerator scale wait =
      (-driftNumerator * scale * prime ^ (depth * wait) *
          (prime ^ wait - 1)) • (1 : Square (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [endpointAdjugate, endpointTransfer, Matrix.mul_apply,
      Fin.sum_univ_succ, smul_eq_mul]
  all_goals ring

/-- A primitive residual step transports endpoint coordinates with the same removed scalar. -/
theorem endpointTransfer_mulVec_of_primitiveIntegralStep
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {source target : ℤ × ℤ}
    (step :
      PrimitiveIntegralStep prime depth centerNumerator
        driftNumerator scale source target) :
    ∃ wait common,
      endpointTransfer (prime : ℤ) depth centerNumerator
          driftNumerator scale wait *ᵥ
        endpointVector centerNumerator driftNumerator scale source.1 source.2 =
      ((prime : ℤ) ^ (depth * wait) * common) •
        endpointVector centerNumerator driftNumerator scale target.1 target.2 := by
  rcases step with
    ⟨_, _, wait, nextNumerator, nextDenominator, common,
      integral, numerator_reduced, denominator_reduced⟩
  refine ⟨wait, common, ?_⟩
  rw [← endpointGauge_mulVec, Matrix.mulVec_mulVec,
    endpointTransfer_mul_endpointGauge, ← Matrix.mulVec_mulVec,
    integralResidualTransfer_mulVec_of_integralStep integral]
  rw [numerator_reduced, denominator_reduced]
  ext i
  fin_cases i <;>
    simp [endpointGauge, endpointVector, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
  all_goals ring

/-- The factor removed forward and the factor removed by reverse reconstruction are
complementary parts of the cyclotomic determinant. -/
theorem endpointAdjugate_mulVec_of_complementaryContent
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {source target : ℤ × ℤ} {wait : Nat} {common complement : ℤ}
    (forward :
      endpointTransfer (prime : ℤ) depth centerNumerator
          driftNumerator scale wait *ᵥ
        endpointVector centerNumerator driftNumerator scale source.1 source.2 =
      ((prime : ℤ) ^ (depth * wait) * common) •
        endpointVector centerNumerator driftNumerator scale target.1 target.2)
    (prime_ne : prime ≠ 0)
    (common_ne : common ≠ 0)
    (complementary :
      common * complement =
        driftNumerator * scale * ((prime : ℤ) ^ wait - 1)) :
    endpointAdjugate (prime : ℤ) depth centerNumerator
        driftNumerator scale wait *ᵥ
      endpointVector centerNumerator driftNumerator scale target.1 target.2 =
      -complement •
        endpointVector centerNumerator driftNumerator scale source.1 source.2 := by
  have power_ne :
      (prime : ℤ) ^ (depth * wait) ≠ 0 := by
    exact pow_ne_zero _ (by exact_mod_cast prime_ne)
  have scalar_ne :
      (prime : ℤ) ^ (depth * wait) * common ≠ 0 :=
    mul_ne_zero power_ne common_ne
  have scaled :
      ((prime : ℤ) ^ (depth * wait) * common) •
          (endpointAdjugate (prime : ℤ) depth centerNumerator
            driftNumerator scale wait *ᵥ
            endpointVector centerNumerator driftNumerator scale
              target.1 target.2) =
        ((prime : ℤ) ^ (depth * wait) * common) •
          (-complement •
            endpointVector centerNumerator driftNumerator scale
              source.1 source.2) := by
    rw [← Matrix.mulVec_smul, ← forward, Matrix.mulVec_mulVec,
      endpointAdjugate_mul_endpointTransfer, Matrix.smul_mulVec,
      Matrix.one_mulVec, smul_smul]
    have scalar_eq :
        -driftNumerator * scale * (prime : ℤ) ^ (depth * wait) *
            ((prime : ℤ) ^ wait - 1) =
          ((prime : ℤ) ^ (depth * wait) * common) * -complement := by
      calc
        _ =
            -(prime : ℤ) ^ (depth * wait) *
              (driftNumerator * scale * ((prime : ℤ) ^ wait - 1)) := by
                ring
        _ =
            -(prime : ℤ) ^ (depth * wait) *
              (common * complement) := by rw [complementary]
        _ = _ := by ring
    rw [scalar_eq]
  ext i
  apply mul_left_cancel₀ scalar_ne
  simpa [smul_eq_mul] using congrFun scaled i

end
end MatrixMortality.ReturnGuard
