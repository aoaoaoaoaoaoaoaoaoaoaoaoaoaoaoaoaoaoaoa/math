import Mathlib.Tactic.LinearCombination
import MatrixMortality.ReturnGuardGauss

/-!
# Finite addresses in decoded residual dynamics

Distinct positive waits define disjoint residual spheres and incompatible finite fixed points.
Every physical mortality witness is exactly a nonempty positive inverse address from the
terminal residual back to residual one.
-/

namespace MatrixMortality.ReturnGuard

open MatrixMortality.PadicValuation

noncomputable section

/-- The difference of two distinct positive prime powers has the smaller valuation. -/
theorem primePower_sub_hasValue_of_lt
    (parameters : Parameters) {left right : Nat} (left_lt : left < right) :
    HasValue parameters.prime
      ((parameters.prime : ℚ) ^ left - parameters.prime ^ right) left := by
  have value :=
    sub_hasValue_min
      (primePower_ne_zero parameters.prime_prime left)
      (primePower_ne_zero parameters.prime_prime right)
      (by
        rw [primePower_valuation, primePower_valuation]
        exact_mod_cast ne_of_lt left_lt)
  refine ⟨value.1, ?_⟩
  rw [value.2, primePower_valuation, primePower_valuation]
  rw [min_eq_left (by exact_mod_cast left_lt.le)]

/-- Distinct residual branches have no common finite projective fixed point. -/
theorem residualFixed_exclusive
    (parameters : Parameters) {left right : Nat} (left_positive : 0 < left)
    (left_lt_right : left < right) (residual : ℚ) :
    ¬(ResidualFixed parameters left residual ∧
      ResidualFixed parameters right residual) := by
  rintro ⟨left_fixed, right_fixed⟩
  let displacement :=
    (parameters.center - 1) * residual +
      drift parameters.center parameters.reset
  have residual_ne : residual ≠ 0 := by
    intro residual_zero
    have impossible := left_fixed
    simp [ResidualFixed, residual_zero] at impossible
    exact parameters.drift_ne_zero impossible.symm
  have left_scale_lt :
      parameters.depth * left < parameters.depth * right :=
    (Nat.mul_lt_mul_left parameters.depth_positive).2 left_lt_right
  have scale_difference_value :
      HasValue parameters.prime
        ((parameters.prime : ℚ) ^ (parameters.depth * left) -
          parameters.prime ^ (parameters.depth * right))
        (parameters.depth * left) :=
    primePower_sub_hasValue_of_lt parameters left_scale_lt
  have wait_difference_value :
      HasValue parameters.prime
        ((parameters.prime : ℚ) ^ right - parameters.prime ^ left) left := by
    have value :=
      primePower_sub_hasValue_of_lt parameters left_lt_right
    rw [show
      (parameters.prime : ℚ) ^ right - parameters.prime ^ left =
        -((parameters.prime : ℚ) ^ left - parameters.prime ^ right) by ring]
    exact neg_hasValue value
  have cancelled :
      ((parameters.prime : ℚ) ^ (parameters.depth * left) -
          parameters.prime ^ (parameters.depth * right)) *
          displacement =
        parameters.prime ^ right - parameters.prime ^ left := by
    have uncancelled :
        ((parameters.prime : ℚ) ^ (parameters.depth * left) -
            parameters.prime ^ (parameters.depth * right)) *
            residual * displacement =
          (parameters.prime ^ right - parameters.prime ^ left) * residual := by
      dsimp [ResidualFixed] at left_fixed right_fixed
      dsimp [displacement]
      linear_combination left_fixed - right_fixed
    apply mul_right_cancel₀ residual_ne
    simpa [mul_assoc, mul_left_comm, mul_comm] using uncancelled
  have displacement_eq :
      displacement =
        (parameters.prime ^ right - parameters.prime ^ left) /
          (parameters.prime ^ (parameters.depth * left) -
            parameters.prime ^ (parameters.depth * right)) := by
    apply (eq_div_iff scale_difference_value.1).2
    simpa [mul_comm] using cancelled
  have displacement_value :
      HasValue parameters.prime displacement
        (left - parameters.depth * left) := by
    rw [displacement_eq]
    exact div_hasValue wait_difference_value scale_difference_value
  have exponent_negative :
      (left : ℤ) - (parameters.depth * left : Nat) < 0 := by
    have left_lt_scaled : left < parameters.depth * left := by
      nlinarith [parameters.depth_two, left_positive]
    have cast_lt :
        (left : ℤ) < ((parameters.depth * left : Nat) : ℤ) := by
      exact_mod_cast left_lt_scaled
    exact sub_neg.mpr cast_lt
  have residual_value :
      HasValue parameters.prime residual
        (left - parameters.depth * left) := by
    have numerator_value :
        HasValue parameters.prime
          (displacement -
            drift parameters.center parameters.reset)
          (left - parameters.depth * left) := by
      rw [sub_eq_add_neg]
      exact add_hasValue_left displacement_value
        (neg_hasValue parameters.drift_unit) exponent_negative
    have residual_eq :
        residual =
          (displacement -
              drift parameters.center parameters.reset) /
            (parameters.center - 1) := by
      apply (eq_div_iff parameters.center_sub_one_unit.1).2
      dsimp [displacement]
      ring
    rw [residual_eq]
    simpa using
      div_hasValue numerator_value parameters.center_sub_one_unit
  have left_side_value :
      HasValue parameters.prime
        (parameters.prime ^ (parameters.depth * left) * residual *
          displacement)
        (parameters.depth * left +
          (left - parameters.depth * left) +
          (left - parameters.depth * left)) := by
    exact mul_hasValue
      (mul_hasValue (primePower_hasValue (parameters.depth * left))
        residual_value)
      displacement_value
  have coefficient_unit :=
    center_sub_primePower_isUnit parameters left left_positive
  have linear_value :
      HasValue parameters.prime
        ((parameters.center - parameters.prime ^ left) * residual)
        (left - parameters.depth * left) := by
    simpa using mul_hasValue coefficient_unit residual_value
  have right_side_value :
      HasValue parameters.prime
        ((parameters.center - parameters.prime ^ left) * residual +
          drift parameters.center parameters.reset)
        (left - parameters.depth * left) :=
    add_hasValue_left linear_value parameters.drift_unit exponent_negative
  have valuation_eq :=
    congrArg (padicValRat parameters.prime) left_fixed
  rw [left_side_value.2, right_side_value.2] at valuation_eq
  have impossible :
      (parameters.depth * left : ℤ) +
          (left - parameters.depth * left) +
          (left - parameters.depth * left) ≠
        left - parameters.depth * left := by
    omega
  exact impossible valuation_eq

/-- One decoded edge is exactly one positive inverse branch applied to a unit target. -/
theorem decodedStep_iff_inverseResidual
    (parameters : Parameters) {source target : ℚ} :
    DecodedStep parameters source target ↔
      ∃ wait, 0 < wait ∧ IsUnit parameters.prime target ∧
        source = inverseResidual parameters wait target := by
  constructor
  · rintro ⟨wait, branch, image_eq⟩
    have target_unit :
        IsUnit parameters.prime target := by
      rw [← image_eq]
      exact residualStep_isUnit_of_branch parameters wait source branch
    exact ⟨wait, branch.1, target_unit, by
      rw [← image_eq]
      exact inverseResidual_residualStep parameters wait source branch |>.symm⟩
  · rintro ⟨wait, wait_positive, target_unit, rfl⟩
    exact ⟨wait,
      inverseResidual_mem_branch parameters wait wait_positive target target_unit,
      residualStep_inverseResidual parameters wait wait_positive target target_unit⟩

theorem inverseAddress_append
    (parameters : Parameters) (left right : List Nat) (target : ℚ) :
    inverseAddress parameters (left ++ right) target =
      inverseAddress parameters left
        (inverseAddress parameters right target) := by
  induction left with
  | nil => rfl
  | cons wait waits induction =>
      simp [inverseAddress, induction]

/-- Positive inverse addresses preserve the unit shell. -/
theorem inverseAddress_isUnit
    (parameters : Parameters) (waits : List Nat) (target : ℚ)
    (positive : PositiveAddress waits)
    (target_unit : IsUnit parameters.prime target) :
    IsUnit parameters.prime (inverseAddress parameters waits target) := by
  induction waits with
  | nil => exact target_unit
  | cons wait waits induction =>
      have wait_positive : 0 < wait :=
        positive wait (by simp)
      have tail_positive : PositiveAddress waits := by
        intro tail tail_mem
        exact positive tail (by simp [tail_mem])
      exact inverseResidual_isUnit parameters wait wait_positive _ (induction tail_positive)

/-- A nonempty positive inverse address is a decoded path to its endpoint. -/
theorem inverseAddress_transGen
    (parameters : Parameters) (waits : List Nat) (target : ℚ)
    (waits_nonempty : waits ≠ [])
    (positive : PositiveAddress waits)
    (target_unit : IsUnit parameters.prime target) :
    Relation.TransGen (DecodedStep parameters)
      (inverseAddress parameters waits target) target := by
  induction waits with
  | nil => exact (waits_nonempty rfl).elim
  | cons wait waits induction =>
      have wait_positive : 0 < wait :=
        positive wait (by simp)
      have tail_positive : PositiveAddress waits := by
        intro tail tail_mem
        exact positive tail (by simp [tail_mem])
      have tail_unit :=
        inverseAddress_isUnit parameters waits target tail_positive target_unit
      have head_step :
          DecodedStep parameters
            (inverseResidual parameters wait
              (inverseAddress parameters waits target))
            (inverseAddress parameters waits target) :=
        (decodedStep_iff_inverseResidual parameters).2
          ⟨wait, wait_positive, tail_unit, rfl⟩
      cases waits with
      | nil =>
          exact Relation.TransGen.single head_step
      | cons next rest =>
          exact
            (induction (by simp) tail_positive).head head_step

/-- Every decoded path has one finite positive inverse address. -/
theorem transGen_exists_inverseAddress
    (parameters : Parameters) {source target : ℚ}
    (path : Relation.TransGen (DecodedStep parameters) source target) :
    ∃ waits, waits ≠ [] ∧ PositiveAddress waits ∧
      source = inverseAddress parameters waits target := by
  induction path with
  | single step =>
      obtain ⟨wait, wait_positive, _, source_eq⟩ :=
        (decodedStep_iff_inverseResidual parameters).1 step
      exact ⟨[wait], by simp, by
        intro candidate candidate_mem
        simp only [List.mem_singleton] at candidate_mem
        subst candidate
        exact wait_positive,
        source_eq⟩
  | tail _ step induction =>
      obtain ⟨waits, waits_nonempty, waits_positive, source_eq⟩ := induction
      obtain ⟨wait, wait_positive, _, middle_eq⟩ :=
        (decodedStep_iff_inverseResidual parameters).1 step
      refine ⟨waits ++ [wait], by simp [waits_nonempty],
        ?_, ?_⟩
      · intro candidate candidate_mem
        rcases List.mem_append.mp candidate_mem with
          prefix_mem | suffix_mem
        · exact waits_positive candidate prefix_mem
        · simp only [List.mem_singleton] at suffix_mem
          subst candidate
          exact wait_positive
      · rw [inverseAddress_append, source_eq, middle_eq]
        rfl

/-- Mortality is finite inverse-address membership of residual one at the terminal residual. -/
theorem decodedReachable_iff_inverseAddress (parameters : Parameters) :
    DecodedReachable parameters ↔
      ∃ waits, waits ≠ [] ∧ PositiveAddress waits ∧
        1 = inverseAddress parameters waits (terminalResidual parameters) := by
  constructor
  · intro reachable
    exact transGen_exists_inverseAddress parameters reachable
  · rintro ⟨waits, waits_nonempty, positive, address_eq⟩
    have path :=
      inverseAddress_transGen parameters waits (terminalResidual parameters)
        waits_nonempty positive (terminalResidual_isUnit parameters)
    rw [← address_eq] at path
    exact path

theorem physical_isMortal_iff_inverseAddress (parameters : Parameters) :
    IsMortal
        (ReturnFamily.pairGenerator
          (ambient (parameters.prime : ℚ) parameters.depth)
          (cut parameters.center parameters.reset)) ↔
      ∃ waits, waits ≠ [] ∧ PositiveAddress waits ∧
        1 = inverseAddress parameters waits (terminalResidual parameters) := by
  rw [physical_isMortal_iff_decodedReachable,
    decodedReachable_iff_inverseAddress]

end
end MatrixMortality.ReturnGuard
