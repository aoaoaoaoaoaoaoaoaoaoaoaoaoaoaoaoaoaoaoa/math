import MatrixMortality.ReturnGuardCumulative

/-!
# Universal-boundary valuation wall

At depth two, every positive endpoint branch preserves an explicit prime-adic ball around the
reset when the coefficient valuations fit below its boundary. The physical compiler turns this
local invariant into immortality. In particular, every prime divisor of `p - 1` must divide the
reset resultant of a mortal guard.
-/

namespace MatrixMortality.ReturnGuard

open MatrixMortality.PadicValuation
open scoped Matrix

noncomputable section

private theorem endpointResetDefect
    (parameters : Parameters)
    {centerNumerator driftNumerator scale : ℤ}
    (center_eq :
      parameters.center = (centerNumerator : ℚ) / scale)
    (drift_eq :
      drift parameters.center parameters.reset =
        (driftNumerator : ℚ) / scale)
    (scale_ne : scale ≠ 0)
    (depth_two : parameters.depth = 2)
    {wait : Nat} {source : ℚ}
    (branch : ResidualBranch parameters wait source) :
    (terminalCoordinate centerNumerator driftNumerator scale
          (residualStep parameters wait source) -
        (centerNumerator + driftNumerator - scale)) *
        (terminalCoordinate centerNumerator driftNumerator scale source -
          scale * ((parameters.prime : ℚ) ^ wait - 1)) =
      driftNumerator * ((parameters.prime : ℚ) ^ wait - 1) *
        (((parameters.prime : ℚ) ^ wait + 1) *
            terminalCoordinate centerNumerator driftNumerator scale source +
          scale) := by
  have action := congrFun
    (endpointTransfer_mulVec_terminalCoordinate parameters
      center_eq drift_eq scale_ne branch) 0
  rw [depth_two] at action
  simp [endpointTransfer, Matrix.mulVec, Matrix.dotProduct,
    Fin.sum_univ_succ, smul_eq_mul] at action
  have power_eq :
      (parameters.prime : ℚ) ^ (2 * wait) =
        ((parameters.prime : ℚ) ^ wait) ^ 2 := by
    rw [show 2 * wait = wait * 2 by omega, pow_mul]
  rw [power_eq] at action
  linear_combination -action

/-- A coefficient-prime valuation wall excludes physical mortality in the depth-two guard. -/
theorem not_physical_isMortal_of_resetBall
    (parameters : Parameters)
    {centerNumerator driftNumerator scale : ℤ}
    (center_eq :
      parameters.center = (centerNumerator : ℚ) / scale)
    (drift_eq :
      drift parameters.center parameters.reset =
        (driftNumerator : ℚ) / scale)
    (scale_ne : scale ≠ 0)
    (depth_two : parameters.depth = 2)
    {factor : Nat} [Fact factor.Prime]
    (reset_ne : centerNumerator + driftNumerator - scale ≠ 0)
    (reset_below_boundary :
      (padicValInt factor (centerNumerator + driftNumerator - scale) : ℤ) <
        padicValInt factor scale +
          padicValInt factor ((parameters.prime : ℤ) - 1))
    (reset_twice_below_blade :
      2 * (padicValInt factor
          (centerNumerator + driftNumerator - scale) : ℤ) <
        padicValInt factor driftNumerator +
          padicValInt factor ((parameters.prime : ℤ) - 1) +
            min (padicValInt factor scale : ℤ)
              ((padicValInt factor
                  (centerNumerator + driftNumerator - scale) : ℤ) +
                padicValInt factor 2)) :
    ¬IsMortal
      (ReturnFamily.pairGenerator
        (ambient (parameters.prime : ℚ) parameters.depth)
        (cut parameters.center parameters.reset)) := by
  let resetResultant : ℤ := centerNumerator + driftNumerator - scale
  let rho : ℤ := padicValInt factor resetResultant
  let lam : ℤ := padicValInt factor scale
  let mu : ℤ := padicValInt factor driftNumerator
  let e : ℤ := padicValInt factor ((parameters.prime : ℤ) - 1)
  let epsilon : ℤ := padicValInt factor 2
  have reset_ne' : resetResultant ≠ 0 := by
    simpa only [resetResultant] using reset_ne
  have drift_ne : driftNumerator ≠ 0 := by
    intro drift_zero
    apply parameters.drift_ne_zero
    rw [drift_eq, drift_zero]
    simp
  have reset_value : HasValue factor (resetResultant : ℚ) rho := by
    refine ⟨by exact_mod_cast reset_ne', ?_⟩
    simpa only [rho] using (padicValRat.of_int (p := factor) (z := resetResultant))
  have scale_value : HasValue factor (scale : ℚ) lam := by
    refine ⟨by exact_mod_cast scale_ne, ?_⟩
    simpa only [lam] using (padicValRat.of_int (p := factor) (z := scale))
  have drift_value : HasValue factor (driftNumerator : ℚ) mu := by
    refine ⟨by exact_mod_cast drift_ne, ?_⟩
    simpa only [mu] using
      (padicValRat.of_int (p := factor) (z := driftNumerator))
  have two_value : HasValue factor (2 : ℚ) epsilon := by
    refine ⟨by norm_num, ?_⟩
    simpa only [epsilon] using (padicValRat.of_int (p := factor) (z := (2 : ℤ)))
  have prime_boundary_ne : (parameters.prime : ℤ) - 1 ≠ 0 := by
    have prime_gt_one : (1 : ℤ) < parameters.prime := by
      exact_mod_cast parameters.prime_prime.one_lt
    omega
  have two_dvd_prime_boundary : (2 : ℤ) ∣ (parameters.prime : ℤ) - 1 := by
    obtain ⟨half, prime_eq⟩ := parameters.prime_odd
    refine ⟨half, ?_⟩
    rw [prime_eq]
    norm_num
  have epsilon_le_e : epsilon ≤ e := by
    have raw := padicValInt_le_of_dvd
      (factor := factor) prime_boundary_ne two_dvd_prime_boundary
    exact Int.ofNat_le.mpr raw
  have reset_below_boundary' : rho < lam + e := by
    simpa only [rho, lam, e, resetResultant] using reset_below_boundary
  have reset_twice_below_blade' :
      2 * rho < mu + e + min lam (rho + epsilon) := by
    simpa only [rho, lam, mu, e, epsilon, resetResultant] using
      reset_twice_below_blade
  let inside : Set ℚ :=
    {residual |
      let coordinate :=
        terminalCoordinate centerNumerator driftNumerator scale residual
      coordinate = (resetResultant : ℚ) ∨
        (coordinate - resetResultant ≠ 0 ∧
          rho < padicValRat factor (coordinate - resetResultant))}
  have closed : ∀ {source target : ℚ},
      source ∈ inside → DecodedStep parameters source target → target ∈ inside := by
    intro source target source_inside decoded
    obtain ⟨wait, branch, target_eq⟩ := decoded
    subst target
    let q : ℚ := parameters.prime ^ wait
    let sourceCoordinate : ℚ :=
      terminalCoordinate centerNumerator driftNumerator scale source
    let targetCoordinate : ℚ :=
      terminalCoordinate centerNumerator driftNumerator scale
        (residualStep parameters wait source)
    have source_inside' :
        sourceCoordinate = (resetResultant : ℚ) ∨
          (sourceCoordinate - resetResultant ≠ 0 ∧
            rho < padicValRat factor (sourceCoordinate - resetResultant)) := by
      simpa only [inside, Set.mem_setOf_eq, sourceCoordinate] using source_inside
    have source_value : HasValue factor sourceCoordinate rho := by
      rcases source_inside' with source_reset | source_deep
      · rw [source_reset]
        exact reset_value
      · have error_value :
            HasValue factor
              (sourceCoordinate - (resetResultant : ℚ))
              (padicValRat factor
                (sourceCoordinate - (resetResultant : ℚ))) :=
          ⟨source_deep.1, rfl⟩
        have sum_value :=
          add_hasValue_left reset_value error_value source_deep.2
        convert sum_value using 1; ring
    have power_gt_one : 1 < parameters.prime ^ wait :=
      one_lt_pow parameters.prime_prime.one_lt branch.1.ne'
    have boundary_ne_int :
        (parameters.prime : ℤ) ^ wait - 1 ≠ 0 := by
      have cast_gt : (1 : ℤ) < (parameters.prime : ℤ) ^ wait := by
        exact_mod_cast power_gt_one
      omega
    let b : ℤ :=
      padicValInt factor ((parameters.prime : ℤ) ^ wait - 1)
    have boundary_value : HasValue factor (q - 1) b := by
      have cast_ne :
          (((parameters.prime : ℤ) ^ wait - 1 : ℤ) : ℚ) ≠ 0 := by
        exact_mod_cast boundary_ne_int
      have value :
          HasValue factor
            (((parameters.prime : ℤ) ^ wait - 1 : ℤ) : ℚ) b := by
        refine ⟨cast_ne, ?_⟩
        simpa only [b] using
          (padicValRat.of_int (p := factor)
            (z := (parameters.prime : ℤ) ^ wait - 1))
      simpa only [q, Int.cast_sub, Int.cast_pow, Int.cast_natCast,
        Int.cast_one] using value
    have prime_boundary_dvd :
        (parameters.prime : ℤ) - 1 ∣
          (parameters.prime : ℤ) ^ wait - 1 :=
      sub_one_dvd_pow_sub_one (parameters.prime : ℤ) wait
    have e_le_b : e ≤ b := by
      have raw := padicValInt_le_of_dvd
        (factor := factor) boundary_ne_int prime_boundary_dvd
      exact Int.ofNat_le.mpr raw
    have q_add_one_ne : q + 1 ≠ 0 := by
      have q_positive : 0 < q := by
        exact pow_pos (by exact_mod_cast parameters.prime_prime.pos) _
      positivity
    have epsilon_le_q_add_one : epsilon ≤ padicValRat factor (q + 1) := by
      have sum_ne : q - 1 + 2 ≠ 0 := by
        convert q_add_one_ne using 1; ring
      have lower :=
        padicValRat.min_le_padicValRat_add (p := factor) sum_ne
      rw [boundary_value.2, two_value.2] at lower
      have epsilon_le_b : epsilon ≤ b := epsilon_le_e.trans e_le_b
      have bound :
          epsilon ≤ padicValRat factor (q - 1 + 2) := by
        simpa only [min_eq_right epsilon_le_b] using lower
      convert bound using 1; ring
    have scaled_boundary_value :
        HasValue factor ((scale : ℚ) * (q - 1)) (lam + b) :=
      mul_hasValue scale_value boundary_value
    have rho_lt_lam_add_b : rho < lam + b := by omega
    have denominator_value :
        HasValue factor
          (sourceCoordinate - (scale : ℚ) * (q - 1)) rho := by
      simpa only [sub_eq_add_neg] using
        add_hasValue_left source_value
          (neg_hasValue scaled_boundary_value) rho_lt_lam_add_b
    let blade : ℚ := (q + 1) * sourceCoordinate + scale
    have defect_identity :
        (targetCoordinate - (resetResultant : ℚ)) *
            (sourceCoordinate - scale * (q - 1)) =
          driftNumerator * (q - 1) * blade := by
      simpa only [targetCoordinate, sourceCoordinate, resetResultant, q, blade,
        Int.cast_add, Int.cast_sub] using
        endpointResetDefect parameters center_eq drift_eq scale_ne
          depth_two branch
    by_cases blade_zero : blade = 0
    · have target_reset : targetCoordinate = (resetResultant : ℚ) := by
        apply sub_eq_zero.mp
        apply mul_right_cancel₀ denominator_value.1
        rw [defect_identity, blade_zero]
        ring
      exact Or.inl target_reset
    · have blade_lower :
          min lam (rho + epsilon) ≤ padicValRat factor blade := by
        have q_add_one_value :
            HasValue factor (q + 1) (padicValRat factor (q + 1)) :=
          ⟨q_add_one_ne, rfl⟩
        have product_value := mul_hasValue q_add_one_value source_value
        have sum_lower :=
          padicValRat.min_le_padicValRat_add (p := factor) blade_zero
        rw [product_value.2, scale_value.2] at sum_lower
        calc
          min lam (rho + epsilon) = min (rho + epsilon) lam := min_comm _ _
          _ ≤ min (padicValRat factor (q + 1) + rho) lam := by
            exact min_le_min (by omega) le_rfl
          _ ≤ padicValRat factor blade := by
            simpa only [blade] using sum_lower
      by_cases defect_zero :
          targetCoordinate - (resetResultant : ℚ) = 0
      · exact Or.inl (sub_eq_zero.mp defect_zero)
      · have defect_value :
            HasValue factor
              (targetCoordinate - (resetResultant : ℚ))
              (padicValRat factor
                (targetCoordinate - (resetResultant : ℚ))) :=
          ⟨defect_zero, rfl⟩
        have blade_value :
            HasValue factor blade (padicValRat factor blade) :=
          ⟨blade_zero, rfl⟩
        have left_value := mul_hasValue defect_value denominator_value
        have right_value :=
          mul_hasValue (mul_hasValue drift_value boundary_value) blade_value
        have valuation_identity :
            padicValRat factor
                (targetCoordinate - (resetResultant : ℚ)) + rho =
              mu + b + padicValRat factor blade := by
          have equal := congrArg (padicValRat factor) defect_identity
          rw [left_value.2, right_value.2] at equal
          exact equal
        have defect_deep :
            rho < padicValRat factor
              (targetCoordinate - (resetResultant : ℚ)) := by
          omega
        exact Or.inr ⟨defect_zero, defect_deep⟩
  intro mortal
  have decoded := (physical_isMortal_iff_decodedReachable parameters).mp mortal
  obtain ⟨steps, _, execution⟩ :=
    Relation.transGen_iff_exists_pos_reachesIn.mp decoded
  have reset_inside : (1 : ℚ) ∈ inside := by
    change
      terminalCoordinate centerNumerator driftNumerator scale 1 =
          (resetResultant : ℚ) ∨ _
    exact Or.inl (by
      simpa only [resetResultant, Int.cast_add, Int.cast_sub] using
        terminalCoordinate_one centerNumerator driftNumerator scale)
  have terminal_inside := execution.target_mem closed reset_inside
  have terminal_coordinate_zero :
      terminalCoordinate centerNumerator driftNumerator scale
          (terminalResidual parameters) = 0 :=
    terminalCoordinate_terminalResidual parameters center_eq drift_eq scale_ne
  change
    terminalCoordinate centerNumerator driftNumerator scale
          (terminalResidual parameters) = (resetResultant : ℚ) ∨
      (terminalCoordinate centerNumerator driftNumerator scale
            (terminalResidual parameters) - resetResultant ≠ 0 ∧
        rho < padicValRat factor
          (terminalCoordinate centerNumerator driftNumerator scale
            (terminalResidual parameters) - resetResultant)) at terminal_inside
  rw [terminal_coordinate_zero] at terminal_inside
  rcases terminal_inside with terminal_reset | terminal_deep
  · exact reset_ne' (by exact_mod_cast terminal_reset.symm)
  · have terminal_value :
        padicValRat factor (0 - (resetResultant : ℚ)) = rho := by
      rw [zero_sub, padicValRat.neg, reset_value.2]
    rw [terminal_value] at terminal_deep
    exact (lt_irrefl rho) terminal_deep.2

/-- Every prime divisor of the universal base boundary divides the reset resultant of a mortal
depth-two guard. -/
theorem universalBoundary_dvd_resetResultant_of_physical_isMortal
    (parameters : Parameters)
    {centerNumerator driftNumerator scale : ℤ}
    (center_eq :
      parameters.center = (centerNumerator : ℚ) / scale)
    (drift_eq :
      drift parameters.center parameters.reset =
        (driftNumerator : ℚ) / scale)
    (scale_ne : scale ≠ 0)
    (depth_two : parameters.depth = 2)
    {factor : Nat} [Fact factor.Prime]
    (factor_dvd_boundary :
      (factor : ℤ) ∣ (parameters.prime : ℤ) - 1)
    (mortal :
      IsMortal
        (ReturnFamily.pairGenerator
          (ambient (parameters.prime : ℚ) parameters.depth)
          (cut parameters.center parameters.reset))) :
    (factor : ℤ) ∣ centerNumerator + driftNumerator - scale := by
  by_contra factor_not_dvd_reset
  have reset_ne : centerNumerator + driftNumerator - scale ≠ 0 := by
    intro reset_zero
    apply factor_not_dvd_reset
    rw [reset_zero]
    exact dvd_zero _
  have reset_value_zero :
      padicValInt factor (centerNumerator + driftNumerator - scale) = 0 :=
    padicValInt.eq_zero_of_not_dvd factor_not_dvd_reset
  have boundary_ne : (parameters.prime : ℤ) - 1 ≠ 0 := by
    have prime_gt_one : (1 : ℤ) < parameters.prime := by
      exact_mod_cast parameters.prime_prime.one_lt
    omega
  have boundary_value_positive :
      1 ≤ padicValInt factor ((parameters.prime : ℤ) - 1) := by
    have power_dvd :
        (factor : ℤ) ^ 1 ∣ (parameters.prime : ℤ) - 1 := by
      simpa using factor_dvd_boundary
    exact ((padicValInt_dvd_iff 1
      ((parameters.prime : ℤ) - 1)).mp power_dvd).resolve_left boundary_ne
  have reset_below_boundary :
      (padicValInt factor (centerNumerator + driftNumerator - scale) : ℤ) <
        padicValInt factor scale +
          padicValInt factor ((parameters.prime : ℤ) - 1) := by
    rw [reset_value_zero]
    have scale_nonnegative :
        (0 : ℤ) ≤ padicValInt factor scale := by positivity
    omega
  have reset_twice_below_blade :
      2 * (padicValInt factor
          (centerNumerator + driftNumerator - scale) : ℤ) <
        padicValInt factor driftNumerator +
          padicValInt factor ((parameters.prime : ℤ) - 1) +
            min (padicValInt factor scale : ℤ)
              ((padicValInt factor
                  (centerNumerator + driftNumerator - scale) : ℤ) +
                padicValInt factor 2) := by
    rw [reset_value_zero]
    norm_num
    have drift_nonnegative :
        (0 : ℤ) ≤ padicValInt factor driftNumerator := by positivity
    have minimum_nonnegative :
        (0 : ℤ) ≤
          min (padicValInt factor scale : ℤ) (padicValInt factor 2) := by
      positivity
    omega
  exact (not_physical_isMortal_of_resetBall parameters center_eq drift_eq
    scale_ne depth_two reset_ne reset_below_boundary reset_twice_below_blade) mortal

end
end MatrixMortality.ReturnGuard

