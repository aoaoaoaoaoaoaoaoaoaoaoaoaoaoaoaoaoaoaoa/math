import MatrixMortality.ReturnGuardAddress
import MatrixMortality.ReturnGuardCumulative

/-!
# Complete endpoint language

Positive endpoint words reach the terminal hyperplane exactly when their inverse address is the
lawful reset-to-terminal execution. The endpoint zero language is therefore singleton-or-empty.
-/

namespace MatrixMortality.ReturnGuard

open MatrixMortality.PadicValuation
open scoped Matrix

noncomputable section

private theorem endpointTransfer_mod_prime
    (parameters : Parameters)
    (centerNumerator driftNumerator scale : ℤ)
    (wait : Nat) (wait_positive : 0 < wait) :
    endpointTransfer (parameters.prime : ZMod parameters.prime) parameters.depth
        centerNumerator driftNumerator scale wait =
      !![
        (centerNumerator : ZMod parameters.prime) - scale,
          ((centerNumerator : ZMod parameters.prime) - scale) * scale;
        1, (scale : ZMod parameters.prime)] := by
  have wait_ne : wait ≠ 0 := Nat.ne_of_gt wait_positive
  have depth_wait_ne : parameters.depth * wait ≠ 0 :=
    Nat.mul_ne_zero (Nat.ne_of_gt parameters.depth_positive) wait_ne
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [endpointTransfer, ZMod.natCast_self, wait_ne, depth_wait_ne]
  all_goals ring

private theorem endpointFlag_sq
    {R : Type*} [CommRing R] (centerNumerator scale : R) :
    !![centerNumerator - scale, (centerNumerator - scale) * scale; 1, scale] *
        !![centerNumerator - scale, (centerNumerator - scale) * scale; 1, scale] =
      centerNumerator •
        !![centerNumerator - scale, (centerNumerator - scale) * scale; 1, scale] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_succ] <;>
    ring

/-- Modulo the distinguished prime, every nonempty positive endpoint product is the scalar
`A^(length - 1)` times one fixed rank-one flag matrix. -/
theorem endpointProduct_mod_prime
    (parameters : Parameters)
    (centerNumerator driftNumerator scale : ℤ)
    (waits : List Nat) (waits_nonempty : waits ≠ [])
    (positive : PositiveAddress waits) :
    endpointProduct (parameters.prime : ZMod parameters.prime) parameters.depth
        centerNumerator driftNumerator scale waits =
      (centerNumerator : ZMod parameters.prime) ^ (waits.length - 1) •
        !![
          (centerNumerator : ZMod parameters.prime) - scale,
            ((centerNumerator : ZMod parameters.prime) - scale) * scale;
          1, (scale : ZMod parameters.prime)] := by
  induction waits with
  | nil => exact (waits_nonempty rfl).elim
  | cons wait waits induction =>
      have wait_positive : 0 < wait := positive wait (by simp)
      cases waits with
      | nil =>
          rw [endpointProduct_cons, endpointProduct_nil, one_mul,
            endpointTransfer_mod_prime parameters centerNumerator driftNumerator scale
              wait wait_positive]
          simp
      | cons next rest =>
          have tail_positive : PositiveAddress (next :: rest) := by
            intro candidate candidate_mem
            exact positive candidate (by simp [candidate_mem])
          rw [endpointProduct_cons,
            induction (by simp) tail_positive,
            endpointTransfer_mod_prime parameters centerNumerator driftNumerator scale
              wait wait_positive,
            Matrix.smul_mul,
            endpointFlag_sq,
            smul_smul]
          simp only [List.length_cons]
          congr 1
          rw [show (rest.length + 1 - 1) = rest.length by omega,
            show (rest.length + 1 + 1 - 1) = rest.length + 1 by omega,
            pow_succ]

/-- In a base-prime-normalized integral presentation, the endpoint product has exactly one
distinguished-prime Smith weight: its determinant valuation is the full schedule weight. -/
theorem endpointProduct_det_hasValue
    (parameters : Parameters)
    (centerNumerator driftNumerator scale : ℤ)
    (driftNumerator_unit :
      IsUnit parameters.prime (driftNumerator : ℚ))
    (scale_unit : IsUnit parameters.prime (scale : ℚ))
    (waits : List Nat) (positive : PositiveAddress waits) :
    HasValue parameters.prime
        (endpointProduct (parameters.prime : ℚ) parameters.depth
          centerNumerator driftNumerator scale waits).det
      (scheduleWeight parameters waits) := by
  induction waits with
  | nil =>
      simp [endpointProduct, scheduleWeight, HasValue]
  | cons wait waits induction =>
      have wait_positive : 0 < wait := positive wait (by simp)
      have tail_positive : PositiveAddress waits := by
        intro candidate candidate_mem
        exact positive candidate (by simp [candidate_mem])
      have cyclotomic_unit :
          IsUnit parameters.prime ((parameters.prime : ℚ) ^ wait - 1) := by
        rw [show (parameters.prime : ℚ) ^ wait - 1 =
          -(1 - parameters.prime ^ wait) by ring]
        exact neg_hasValue
          (one_sub_positive (primePower_positive parameters wait wait_positive))
      have branch_value :
          HasValue parameters.prime
            (-driftNumerator * scale *
              (parameters.prime : ℚ) ^ (parameters.depth * wait) *
                (parameters.prime ^ wait - 1))
            (parameters.depth * wait) := by
        simpa [add_assoc] using
          mul_hasValue
            (mul_hasValue
              (mul_hasValue (neg_hasValue driftNumerator_unit) scale_unit)
              (primePower_hasValue (parameters.depth * wait)))
            cyclotomic_unit
      rw [endpointProduct_cons, Matrix.det_mul,
        endpointTransfer_det]
      have product_value := mul_hasValue (induction tail_positive) branch_value
      convert product_value using 1
      rw [scheduleWeight_cons]
      ring

/-- At the complete forced prime power of a cumulative prefix, the endpoint product's kernel is
exactly the scalar line through the fixed reset pair. This is the integral congruence form of
the fixed reset geodesic: prefix length changes the modulus, never the radial direction. -/
theorem CumulativeEndpointExecution.endpointKernel_eq_resetLine
    (parameters : Parameters)
    {centerNumerator driftNumerator scale : ℤ}
    (centerNumerator_not_dvd :
      ¬(parameters.prime : ℤ) ∣ centerNumerator)
    {waits : List Nat} {target : ℤ × ℤ}
    (execution :
      CumulativeEndpointExecution parameters.prime parameters.depth
        centerNumerator driftNumerator scale waits
        (cumulativeResetPair centerNumerator driftNumerator scale) target)
    (waits_nonempty : waits ≠ [])
    (positive : PositiveAddress waits)
    (point :
      Fin 2 → ZMod (parameters.prime ^ (parameters.depth * waits.sum))) :
    endpointProduct
          (parameters.prime :
            ZMod (parameters.prime ^ (parameters.depth * waits.sum)))
          parameters.depth centerNumerator driftNumerator scale waits *ᵥ point = 0 ↔
      ∃ scalar : ZMod (parameters.prime ^ (parameters.depth * waits.sum)),
        point = scalar •
          ![((centerNumerator + driftNumerator - scale : ℤ) :
              ZMod (parameters.prime ^ (parameters.depth * waits.sum))), 1] := by
  let exponent := parameters.depth * waits.sum
  let modulus := parameters.prime ^ exponent
  let integerMatrix :=
    endpointProduct (parameters.prime : ℤ) parameters.depth
      centerNumerator driftNumerator scale waits
  let matrix :=
    endpointProduct (parameters.prime : ZMod modulus) parameters.depth
      centerNumerator driftNumerator scale waits
  let reset : Fin 2 → ZMod modulus :=
    ![((centerNumerator + driftNumerator - scale : ℤ) : ZMod modulus), 1]
  change matrix *ᵥ point = 0 ↔
    ∃ scalar : ZMod modulus, point = scalar • reset
  let integerBottom := integerMatrix 1 0
  have center_mod_prime_ne :
      (centerNumerator : ZMod parameters.prime) ≠ 0 := by
    exact mt
      (ZMod.intCast_zmod_eq_zero_iff_dvd centerNumerator parameters.prime).mp
      centerNumerator_not_dvd
  have bottom_mod_prime :
      (integerBottom : ZMod parameters.prime) =
        (centerNumerator : ZMod parameters.prime) ^ (waits.length - 1) := by
    calc
      (integerBottom : ZMod parameters.prime) =
          (endpointProduct (parameters.prime : ZMod parameters.prime)
            parameters.depth centerNumerator driftNumerator scale waits) 1 0 := by
        have mapped := congrArg (fun mappedMatrix => mappedMatrix 1 0)
          (endpointProduct_map (Int.castRingHom (ZMod parameters.prime))
            (parameters.prime : ℤ) parameters.depth
            centerNumerator driftNumerator scale waits)
        simpa [integerBottom, integerMatrix] using mapped
      _ = (centerNumerator : ZMod parameters.prime) ^ (waits.length - 1) := by
        rw [endpointProduct_mod_prime parameters centerNumerator driftNumerator scale
          waits waits_nonempty positive]
        simp [Matrix.smul_apply]
  have prime_not_dvd_bottom :
      ¬(parameters.prime : ℤ) ∣ integerBottom := by
    intro divides
    have bottom_zero :
        (integerBottom : ZMod parameters.prime) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd integerBottom parameters.prime).2 divides
    rw [bottom_mod_prime] at bottom_zero
    exact (pow_ne_zero _ center_mod_prime_ne) bottom_zero
  have prime_not_dvd_bottom_abs :
      ¬parameters.prime ∣ integerBottom.natAbs := by
    intro divides
    apply prime_not_dvd_bottom
    apply Int.natAbs_dvd_natAbs.mp
    simpa using divides
  have bottom_coprime_prime :
      integerBottom.natAbs.Coprime parameters.prime :=
    ((parameters.prime_prime.coprime_iff_not_dvd).2
      prime_not_dvd_bottom_abs).symm
  have bottom_abs_unit :
      IsUnit (integerBottom.natAbs : ZMod modulus) := by
    apply (ZMod.isUnit_iff_coprime integerBottom.natAbs modulus).2
    dsimp [modulus]
    exact bottom_coprime_prime.pow_right exponent
  have bottom_integer_unit : IsUnit (integerBottom : ZMod modulus) := by
    rcases Int.natAbs_eq integerBottom with bottom_eq | bottom_eq
    · rw [bottom_eq, Int.cast_natCast]
      exact bottom_abs_unit
    · rw [bottom_eq, Int.cast_neg, Int.cast_natCast]
      exact bottom_abs_unit.neg
  have bottom_eq : (integerBottom : ZMod modulus) = matrix 1 0 := by
    have mapped := congrArg (fun mappedMatrix => mappedMatrix 1 0)
      (endpointProduct_map (Int.castRingHom (ZMod modulus))
        (parameters.prime : ℤ) parameters.depth
        centerNumerator driftNumerator scale waits)
    simpa [integerBottom, integerMatrix, matrix] using mapped
  have bottom_unit : IsUnit (matrix 1 0) := by
    rw [← bottom_eq]
    exact bottom_integer_unit
  let cast : ℤ →+* ZMod modulus := Int.castRingHom (ZMod modulus)
  have primePower_zero :
      cast ((parameters.prime : ℤ) ^ exponent) = 0 := by
    change
      (((parameters.prime : ℤ) ^ exponent : ℤ) : ZMod modulus) = 0
    rw [Int.cast_pow, Int.cast_natCast, ← Nat.cast_pow]
    exact ZMod.natCast_self modulus
  have reset_killed : matrix *ᵥ reset = 0 := by
    have source_cast :
        (cast ∘ pairVector
          (cumulativeResetPair centerNumerator driftNumerator scale)) = reset := by
      funext i
      fin_cases i <;>
        simp [cast, reset, pairVector, cumulativeResetPair]
    funext i
    have transferred := congrFun execution.transfer i
    have casted := congrArg cast transferred
    rw [RingHom.map_mulVec, endpointProduct_map] at casted
    rw [source_cast] at casted
    dsimp [cast] at casted
    have casted' :
        (matrix *ᵥ reset) i =
        (((parameters.prime : ℤ) ^ exponent * pairVector target i : ℤ) :
          ZMod modulus) := by
      simpa only [matrix, exponent, Int.cast_natCast] using casted
    calc
      (matrix *ᵥ reset) i =
          (((parameters.prime : ℤ) ^ exponent * pairVector target i : ℤ) :
            ZMod modulus) := casted'
      _ = 0 := by
        rw [Int.cast_mul, show
          (((parameters.prime : ℤ) ^ exponent : ℤ) : ZMod modulus) = 0 by
            exact primePower_zero,
          zero_mul]
      _ = (0 : Fin 2 → ZMod modulus) i := rfl
  constructor
  · intro annihilated
    have point_equation := congrFun annihilated 1
    have reset_equation := congrFun reset_killed 1
    simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two] at point_equation
    simp [reset, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two] at reset_equation
    have point_first : point 0 = reset 0 * point 1 := by
      dsimp [reset]
      push_cast
      apply bottom_unit.mul_left_cancel
      linear_combination point_equation - point 1 * reset_equation
    refine ⟨point 1, ?_⟩
    funext i
    fin_cases i
    · simp [reset, smul_eq_mul, point_first, mul_comm]
    · simp [reset, smul_eq_mul]
  · rintro ⟨scalar, point_eq⟩
    rw [point_eq, Matrix.mulVec_smul, reset_killed, smul_zero]

private theorem inverseAddress_follows_and_runs
    (parameters : Parameters) (waits : List Nat) (target : ℚ)
    (positive : PositiveAddress waits)
    (target_unit : IsUnit parameters.prime target) :
    FollowsResidualSchedule parameters waits
        (inverseAddress parameters waits target) ∧
      residualRun parameters waits
        (inverseAddress parameters waits target) = target := by
  induction waits with
  | nil => exact ⟨trivial, rfl⟩
  | cons wait waits induction =>
      have wait_positive : 0 < wait := positive wait (by simp)
      have tail_positive : PositiveAddress waits := by
        intro candidate candidate_mem
        exact positive candidate (by simp [candidate_mem])
      have tail_unit :=
        inverseAddress_isUnit parameters waits target tail_positive target_unit
      have branch :=
        inverseResidual_mem_branch parameters wait wait_positive
          (inverseAddress parameters waits target) tail_unit
      have step :=
        residualStep_inverseResidual parameters wait wait_positive
          (inverseAddress parameters waits target) tail_unit
      rw [inverseAddress, followsResidualSchedule_cons, residualRun_cons]
      constructor
      · refine ⟨branch, ?_⟩
        rw [step]
        exact (induction tail_positive).1
      · rw [step]
        exact (induction tail_positive).2

/-- A positive integral endpoint word hits the terminal hyperplane exactly when its inverse
address is the reset residual. Thus endpoint algebra creates no malformed mortality witnesses. -/
theorem endpointTerminalWord_iff_inverseAddress_eq_one
    (parameters : Parameters)
    {centerNumerator driftNumerator scale : ℤ}
    (center_eq :
      parameters.center = (centerNumerator : ℚ) / scale)
    (drift_eq :
      drift parameters.center parameters.reset =
        (driftNumerator : ℚ) / scale)
    (scale_ne : scale ≠ 0)
    (waits : List Nat) (positive : PositiveAddress waits) :
    EndpointTerminalWord parameters.prime parameters.depth
        centerNumerator driftNumerator scale waits ↔
      inverseAddress parameters waits (terminalResidual parameters) = 1 := by
  let matrix :=
    endpointProduct (parameters.prime : ℚ) parameters.depth
      centerNumerator driftNumerator scale waits
  let address :=
    inverseAddress parameters waits (terminalResidual parameters)
  have address_unit : IsUnit parameters.prime address := by
    exact inverseAddress_isUnit parameters waits (terminalResidual parameters)
      positive (terminalResidual_isUnit parameters)
  have address_execution :=
    inverseAddress_follows_and_runs parameters waits
      (terminalResidual parameters) positive (terminalResidual_isUnit parameters)
  have address_first_zero :
      (matrix *ᵥ
        ![terminalCoordinate centerNumerator driftNumerator scale address, 1]) 0 = 0 := by
    obtain ⟨scalar, action⟩ :=
      endpointProduct_mulVec_terminalCoordinate parameters center_eq drift_eq scale_ne
        waits address address_execution.1
    have first := congrFun action 0
    rw [address_execution.2,
      terminalCoordinate_terminalResidual parameters center_eq drift_eq scale_ne] at first
    simpa [matrix, smul_eq_mul] using first
  have scale_ne_rat : (scale : ℚ) ≠ 0 := by
    exact_mod_cast scale_ne
  have driftNumerator_ne_rat : (driftNumerator : ℚ) ≠ 0 := by
    intro driftNumerator_zero
    apply parameters.drift_ne_zero
    rw [drift_eq, driftNumerator_zero, zero_div]
  have matrix_det_ne : matrix.det ≠ 0 := by
    dsimp [matrix]
    rw [endpointProduct_det]
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact pow_ne_zero waits.length (by norm_num)
      · apply List.prod_ne_zero
        intro zero_mem
        obtain ⟨wait, _, power_zero⟩ := List.mem_map.mp zero_mem
        exact pow_ne_zero _ parameters.prime_ne_zero power_zero
    · apply List.prod_ne_zero
      intro zero_mem
      obtain ⟨wait, wait_mem, factor_zero⟩ := List.mem_map.mp zero_mem
      have wait_positive : 0 < wait := positive wait wait_mem
      have primePower_ne_one :
          (parameters.prime : ℚ) ^ wait ≠ 1 := by
        intro power_eq
        have valuation_eq := congrArg (padicValRat parameters.prime) power_eq
        rw [primePower_valuation, padicValRat.one] at valuation_eq
        have wait_zero : wait = 0 := by
          exact_mod_cast valuation_eq
        exact (Nat.ne_of_gt wait_positive) wait_zero
      exact
        (mul_ne_zero
          (mul_ne_zero driftNumerator_ne_rat scale_ne_rat)
          (sub_ne_zero.mpr primePower_ne_one)) factor_zero
  constructor
  · intro terminal
    have terminal_rat :
        (matrix *ᵥ
          ![(centerNumerator : ℚ) + driftNumerator - scale, 1]) 0 = 0 := by
      change
        (endpointProduct (parameters.prime : ℤ) parameters.depth
            centerNumerator driftNumerator scale waits *ᵥ
          ![centerNumerator + driftNumerator - scale, 1]) 0 = 0 at terminal
      let cast : ℤ →+* ℚ := Int.castRingHom ℚ
      have cast_zero := congrArg cast terminal
      rw [RingHom.map_mulVec, endpointProduct_map] at cast_zero
      have vector_eq :
          (cast ∘ ![centerNumerator + driftNumerator - scale, 1]) =
            ![((centerNumerator + driftNumerator - scale : ℤ) : ℚ), 1] := by
        funext i
        fin_cases i <;> simp [cast]
      rw [vector_eq] at cast_zero
      simpa only [matrix, Int.cast_add, Int.cast_sub] using cast_zero
    have reset_first_zero :
        (matrix *ᵥ
          ![terminalCoordinate centerNumerator driftNumerator scale 1, 1]) 0 = 0 := by
      simpa only [terminalCoordinate_one, Int.cast_add, Int.cast_sub] using terminal_rat
    have matrix_first_ne : matrix 0 0 ≠ 0 := by
      intro matrix_first_zero
      have matrix_second_zero : matrix 0 1 = 0 := by
        simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two] at reset_first_zero
        rw [matrix_first_zero, zero_mul, zero_add] at reset_first_zero
        exact reset_first_zero
      apply matrix_det_ne
      rw [Matrix.det_fin_two, matrix_first_zero, matrix_second_zero]
      ring
    have coordinate_eq :
        terminalCoordinate centerNumerator driftNumerator scale address =
          terminalCoordinate centerNumerator driftNumerator scale 1 := by
      have address_equation := address_first_zero
      have reset_equation := reset_first_zero
      simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two] at address_equation reset_equation
      have product_zero :
          matrix 0 0 *
              (terminalCoordinate centerNumerator driftNumerator scale address -
                ((centerNumerator : ℚ) + driftNumerator - scale)) = 0 := by
        linear_combination address_equation - reset_equation
      have address_coordinate_eq :
          terminalCoordinate centerNumerator driftNumerator scale address =
            (centerNumerator : ℚ) + driftNumerator - scale :=
        sub_eq_zero.mp ((mul_eq_zero.mp product_zero).resolve_left matrix_first_ne)
      simpa only [terminalCoordinate_one, Int.cast_add, Int.cast_sub] using
        address_coordinate_eq
    have quotient_eq :
        (driftNumerator : ℚ) / address = driftNumerator := by
      simpa [terminalCoordinate] using coordinate_eq
    have cancelled := (div_eq_iff address_unit.1).mp quotient_eq
    change address = 1
    apply mul_left_cancel₀ driftNumerator_ne_rat
    calc
      (driftNumerator : ℚ) * address = driftNumerator := cancelled.symm
      _ = (driftNumerator : ℚ) * 1 := by ring
  · intro address_eq
    rw [address_eq] at address_execution
    exact endpointTerminalWord_of_residualRun_eq_terminal parameters
      center_eq drift_eq scale_ne waits address_execution.1 address_execution.2

private theorem terminalResidual_no_decodedStep
    (parameters : Parameters) (target : ℚ) :
    ¬DecodedStep parameters (terminalResidual parameters) target := by
  intro step
  have source_live :=
    legalStep_source_live parameters (decodedStep_legalStep parameters step)
  rw [stateOfResidual_terminalResidual] at source_live
  have positive_valuation := source_live.2
  rw [padicValRat.one] at positive_valuation
  exact (lt_irrefl 0) positive_valuation

private theorem inverseAddress_terminal_injective
    (parameters : Parameters) :
    ∀ {left right : List Nat},
      PositiveAddress left →
      PositiveAddress right →
      inverseAddress parameters left (terminalResidual parameters) =
        inverseAddress parameters right (terminalResidual parameters) →
      left = right := by
  intro left
  induction left with
  | nil =>
      intro right _ right_positive addresses_eq
      cases right with
      | nil => rfl
      | cons wait waits =>
          have wait_positive : 0 < wait := right_positive wait (by simp)
          have tail_positive : PositiveAddress waits := by
            intro candidate candidate_mem
            exact right_positive candidate (by simp [candidate_mem])
          have tail_unit :=
            inverseAddress_isUnit parameters waits (terminalResidual parameters)
              tail_positive (terminalResidual_isUnit parameters)
          apply
            (terminalResidual_no_decodedStep parameters
              (inverseAddress parameters waits (terminalResidual parameters))).elim
          exact (decodedStep_iff_inverseResidual parameters).2
            ⟨wait, wait_positive, tail_unit, by
              simpa [inverseAddress] using addresses_eq⟩
  | cons wait waits induction =>
      intro right left_positive right_positive addresses_eq
      cases right with
      | nil =>
          have wait_positive : 0 < wait := left_positive wait (by simp)
          have tail_positive : PositiveAddress waits := by
            intro candidate candidate_mem
            exact left_positive candidate (by simp [candidate_mem])
          have tail_unit :=
            inverseAddress_isUnit parameters waits (terminalResidual parameters)
              tail_positive (terminalResidual_isUnit parameters)
          apply
            (terminalResidual_no_decodedStep parameters
              (inverseAddress parameters waits (terminalResidual parameters))).elim
          exact (decodedStep_iff_inverseResidual parameters).2
            ⟨wait, wait_positive, tail_unit, by
              simpa [inverseAddress] using addresses_eq.symm⟩
      | cons other rest =>
          have wait_positive : 0 < wait := left_positive wait (by simp)
          have other_positive : 0 < other := right_positive other (by simp)
          have tail_positive : PositiveAddress waits := by
            intro candidate candidate_mem
            exact left_positive candidate (by simp [candidate_mem])
          have rest_positive : PositiveAddress rest := by
            intro candidate candidate_mem
            exact right_positive candidate (by simp [candidate_mem])
          have tail_unit :=
            inverseAddress_isUnit parameters waits (terminalResidual parameters)
              tail_positive (terminalResidual_isUnit parameters)
          have rest_unit :=
            inverseAddress_isUnit parameters rest (terminalResidual parameters)
              rest_positive (terminalResidual_isUnit parameters)
          have left_branch :
              ResidualBranch parameters wait
                (inverseAddress parameters (wait :: waits)
                  (terminalResidual parameters)) := by
            simpa [inverseAddress] using
              inverseResidual_mem_branch parameters wait wait_positive
                (inverseAddress parameters waits (terminalResidual parameters)) tail_unit
          have right_branch :
              ResidualBranch parameters other
                (inverseAddress parameters (wait :: waits)
                  (terminalResidual parameters)) := by
            rw [addresses_eq]
            simpa [inverseAddress] using
              inverseResidual_mem_branch parameters other other_positive
                (inverseAddress parameters rest (terminalResidual parameters)) rest_unit
          have waits_eq : wait = other :=
            residualBranch_wait_unique parameters left_branch right_branch
          subst other
          have tails_eq :
              inverseAddress parameters waits (terminalResidual parameters) =
                inverseAddress parameters rest (terminalResidual parameters) := by
            calc
              inverseAddress parameters waits (terminalResidual parameters) =
                  residualStep parameters wait
                    (inverseAddress parameters (wait :: waits)
                      (terminalResidual parameters)) := by
                rw [inverseAddress]
                exact
                  (residualStep_inverseResidual parameters wait wait_positive
                    (inverseAddress parameters waits (terminalResidual parameters))
                    tail_unit).symm
              _ = residualStep parameters wait
                    (inverseAddress parameters (wait :: rest)
                      (terminalResidual parameters)) := by
                rw [addresses_eq]
              _ = inverseAddress parameters rest (terminalResidual parameters) := by
                rw [inverseAddress]
                exact
                  residualStep_inverseResidual parameters wait wait_positive
                    (inverseAddress parameters rest (terminalResidual parameters)) rest_unit
          rw [induction tail_positive rest_positive tails_eq]

/-- Positive endpoint terminal words are unique. The endpoint zero language is therefore
singleton-or-empty, although deciding which alternative holds remains the guard problem. -/
theorem endpointTerminalWord_unique
    (parameters : Parameters)
    {centerNumerator driftNumerator scale : ℤ}
    (center_eq :
      parameters.center = (centerNumerator : ℚ) / scale)
    (drift_eq :
      drift parameters.center parameters.reset =
        (driftNumerator : ℚ) / scale)
    (scale_ne : scale ≠ 0)
    {left right : List Nat}
    (left_positive : PositiveAddress left)
    (right_positive : PositiveAddress right)
    (left_terminal :
      EndpointTerminalWord parameters.prime parameters.depth
        centerNumerator driftNumerator scale left)
    (right_terminal :
      EndpointTerminalWord parameters.prime parameters.depth
        centerNumerator driftNumerator scale right) :
    left = right := by
  apply inverseAddress_terminal_injective parameters left_positive right_positive
  rw [endpointTerminalWord_iff_inverseAddress_eq_one parameters
      center_eq drift_eq scale_ne left left_positive |>.mp left_terminal,
    endpointTerminalWord_iff_inverseAddress_eq_one parameters
      center_eq drift_eq scale_ne right right_positive |>.mp right_terminal]

/-- Physical mortality of the guard is exactly the existence of a nonempty positive endpoint
word with vanishing terminal coefficient; no independent legality predicate remains. -/
theorem physical_isMortal_iff_endpointTerminalWord
    (parameters : Parameters)
    {centerNumerator driftNumerator scale : ℤ}
    (center_eq :
      parameters.center = (centerNumerator : ℚ) / scale)
    (drift_eq :
      drift parameters.center parameters.reset =
        (driftNumerator : ℚ) / scale)
    (scale_ne : scale ≠ 0) :
    IsMortal
        (ReturnFamily.pairGenerator
          (ambient (parameters.prime : ℚ) parameters.depth)
          (cut parameters.center parameters.reset)) ↔
      ∃ waits, waits ≠ [] ∧ PositiveAddress waits ∧
        EndpointTerminalWord parameters.prime parameters.depth
          centerNumerator driftNumerator scale waits := by
  rw [physical_isMortal_iff_inverseAddress]
  constructor
  · rintro ⟨waits, waits_nonempty, positive, address_eq⟩
    refine ⟨waits, waits_nonempty, positive, ?_⟩
    exact
      (endpointTerminalWord_iff_inverseAddress_eq_one parameters
        center_eq drift_eq scale_ne waits positive).2 address_eq.symm
  · rintro ⟨waits, waits_nonempty, positive, terminal⟩
    refine ⟨waits, waits_nonempty, positive, ?_⟩
    exact
      (endpointTerminalWord_iff_inverseAddress_eq_one parameters
        center_eq drift_eq scale_ne waits positive).1 terminal |>.symm

end
end MatrixMortality.ReturnGuard
