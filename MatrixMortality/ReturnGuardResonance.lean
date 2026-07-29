import MatrixMortality.ReturnGuardDynamics

/-!
# Resonance localization for the amalgamated valuation guard

The unit tail can support a further legal step only near one distinguished unit.  Away from the
equal-depth shell, its distance from that unit either becomes the strictly smaller next wait or
destroys readiness.  Equal-depth cancellation is the sole source of nondecreasing waits.
-/

namespace MatrixMortality.ReturnGuard

open MatrixMortality.PadicValuation

noncomputable section

/-- Distinguished unit about which every continuing tail must resonate. -/
def resonanceCenter (parameters : Parameters) : ℚ :=
  parameters.center / drift parameters.center parameters.reset

/-- Tail at prescribed distance `p^tailDepth` from the resonance center. -/
def tailAtDepth
    (parameters : Parameters) (tailDepth : Nat) (residual : ℚ) : ℚ :=
  resonanceCenter parameters + parameters.prime ^ tailDepth * residual

/-- One-depth-shallower value exposed by equal-depth resonance. -/
def resonanceValue (parameters : Parameters) (wait : Nat) (residual : ℚ) : ℚ :=
  parameters.center +
    drift parameters.center parameters.reset *
      (parameters.prime ^ ((parameters.depth - 1) * wait) +
        (parameters.prime ^ wait - 1) * residual)

/-- Equal-depth shell in which a wait can be preserved or increased. -/
def ResonantTail (parameters : Parameters) (wait : Nat) (tail : ℚ) : Prop :=
  ∃ residual, IsUnit parameters.prime residual ∧
    tail = tailAtDepth parameters wait residual

/-- Decomposition of one guarded carry depth into its visible and residual parts. -/
theorem depth_mul_eq_wait_add_residualDepth
    (parameters : Parameters) (wait : Nat) :
    parameters.depth * wait =
      wait + (parameters.depth - 1) * wait := by
  have depth_one : 1 ≤ parameters.depth := by
    exact le_trans (by norm_num) parameters.depth_two
  calc
    parameters.depth * wait =
        ((parameters.depth - 1) + 1) * wait := by
          rw [Nat.sub_add_cancel depth_one]
    _ = wait + (parameters.depth - 1) * wait := by
      simp [Nat.add_mul, Nat.add_comm]

/-- The distinguished tail center is a `p`-adic unit. -/
theorem resonanceCenter_isUnit (parameters : Parameters) :
    IsUnit parameters.prime (resonanceCenter parameters) := by
  simpa [resonanceCenter] using
    div_hasValue parameters.center_unit parameters.drift_unit

/-- Prescribing a unit residual at depth `tailDepth` gives exactly that tail valuation. -/
theorem tailAtDepth_sub_center_hasValue
    (parameters : Parameters) (tailDepth : Nat) (residual : ℚ)
    (residual_unit : IsUnit parameters.prime residual) :
    HasValue parameters.prime
      (tailAtDepth parameters tailDepth residual - resonanceCenter parameters)
      tailDepth := by
  rw [show
    tailAtDepth parameters tailDepth residual - resonanceCenter parameters =
      parameters.prime ^ tailDepth * residual by simp [tailAtDepth]]
  simpa using mul_hasValue (primePower_hasValue tailDepth) residual_unit

/-- Expansion separating the wait scale from the tail-center scale. -/
theorem legalValue_tailAtDepth
    (parameters : Parameters) (wait tailDepth : Nat) (residual : ℚ) :
    legalValue parameters wait
        (tailAtDepth parameters tailDepth residual) =
      parameters.center * parameters.prime ^ wait +
        drift parameters.center parameters.reset *
          parameters.prime ^ (parameters.depth * wait) +
        drift parameters.center parameters.reset *
          (parameters.prime ^ wait - 1) *
          parameters.prime ^ tailDepth * residual := by
  have drift_ne := parameters.drift_ne_zero
  simp [legalValue, tailAtDepth, resonanceCenter]
  field_simp [drift_ne]
  ring

/-- Centered form separating the sole potentially cancelling unit from positive-depth terms. -/
theorem legalValue_eq_centeredTail
    (parameters : Parameters) (wait : Nat) (tail : ℚ) :
    legalValue parameters wait tail =
      drift parameters.center parameters.reset *
        ((resonanceCenter parameters - tail) +
          parameters.prime ^ (parameters.depth * wait) +
          parameters.prime ^ wait * tail) := by
  have drift_ne := parameters.drift_ne_zero
  simp [legalValue, resonanceCenter]
  field_simp [drift_ne]
  ring

/-- Equal-depth resonance factors out the current wait and exposes a shallower guard value. -/
theorem legalValue_resonance
    (parameters : Parameters) (wait : Nat) (residual : ℚ) :
    legalValue parameters wait (tailAtDepth parameters wait residual) =
      parameters.prime ^ wait * resonanceValue parameters wait residual := by
  rw [legalValue_tailAtDepth]
  simp [resonanceValue]
  have exponent_split :
      parameters.depth * wait =
        wait + (parameters.depth - 1) * wait :=
    depth_mul_eq_wait_add_residualDepth parameters wait
  rw [exponent_split, pow_add]
  ring

/-- The center term has exactly the current wait valuation. -/
theorem center_scaled_hasValue
    (parameters : Parameters) (wait : Nat) :
    HasValue parameters.prime
      (parameters.center * parameters.prime ^ wait) wait := by
  simpa using
    mul_hasValue parameters.center_unit (primePower_hasValue wait)

/-- The expanding verifier term has valuation `depth * wait`. -/
theorem drift_scaled_hasValue
    (parameters : Parameters) (wait : Nat) :
    HasValue parameters.prime
      (drift parameters.center parameters.reset *
        parameters.prime ^ (parameters.depth * wait))
      (parameters.depth * wait) := by
  simpa using
    mul_hasValue parameters.drift_unit
      (primePower_hasValue (parameters.depth * wait))

/-- The tail perturbation has exactly its prescribed depth. -/
theorem tailPerturbation_hasValue
    (parameters : Parameters) (wait tailDepth : Nat)
    (wait_positive : 0 < wait) (residual : ℚ)
    (residual_unit : IsUnit parameters.prime residual) :
    HasValue parameters.prime
      (drift parameters.center parameters.reset *
        (parameters.prime ^ wait - 1) *
        parameters.prime ^ tailDepth * residual)
      tailDepth := by
  have power_sub_one_unit :
      IsUnit parameters.prime (parameters.prime ^ wait - 1) :=
    positive_sub_one (primePower_positive parameters wait wait_positive)
  have coefficient_unit :
      IsUnit parameters.prime
        (drift parameters.center parameters.reset *
          (parameters.prime ^ wait - 1)) :=
    mul_hasValue parameters.drift_unit power_sub_one_unit
  simpa [add_assoc] using
    mul_hasValue
      (mul_hasValue coefficient_unit (primePower_hasValue tailDepth))
      residual_unit

/-- A legal output can retain positive valuation only if the unit tail equals the resonance
center or differs from it by positive valuation. -/
theorem legalValue_isPositive_forces_tail_resonance
    (parameters : Parameters) (wait : Nat) (wait_positive : 0 < wait)
    (tail : ℚ) (tail_unit : IsUnit parameters.prime tail)
    (output_positive :
      IsPositive parameters.prime (legalValue parameters wait tail)) :
    tail = resonanceCenter parameters ∨
      IsPositive parameters.prime (tail - resonanceCenter parameters) := by
  by_cases centered : tail = resonanceCenter parameters
  · exact Or.inl centered
  · right
    have difference_ne :
        tail - resonanceCenter parameters ≠ 0 :=
      sub_ne_zero.mpr centered
    have difference_nonnegative :
        0 ≤ padicValRat parameters.prime
          (tail - resonanceCenter parameters) := by
      have lower :=
        min_le_sub (prime := parameters.prime) difference_ne
      simpa [tail_unit.2, (resonanceCenter_isUnit parameters).2] using lower
    by_contra difference_not_positive
    have difference_value_zero :
        padicValRat parameters.prime
          (tail - resonanceCenter parameters) = 0 := by
      have nonpositive :
          padicValRat parameters.prime
            (tail - resonanceCenter parameters) ≤ 0 :=
        le_of_not_gt (fun positive =>
          difference_not_positive ⟨difference_ne, positive⟩)
      omega
    have opposite_difference_unit :
        IsUnit parameters.prime
          (resonanceCenter parameters - tail) := by
      rw [show resonanceCenter parameters - tail =
        -(tail - resonanceCenter parameters) by ring]
      exact neg_hasValue ⟨difference_ne, difference_value_zero⟩
    have centered_term_unit :
        IsUnit parameters.prime
          (drift parameters.center parameters.reset *
            (resonanceCenter parameters - tail)) :=
      mul_hasValue parameters.drift_unit opposite_difference_unit
    have wait_lt_scaled : (wait : ℤ) < parameters.depth * wait := by
      exact_mod_cast (show wait < parameters.depth * wait by
        nlinarith [parameters.depth_two])
    have tail_scaled_value :
        HasValue parameters.prime
          (parameters.prime ^ wait * tail) wait :=
      mul_hasValue (primePower_hasValue wait) tail_unit
    have positive_remainder_value :
        HasValue parameters.prime
          (parameters.prime ^ (parameters.depth * wait) +
            parameters.prime ^ wait * tail)
          wait :=
      add_hasValue_right
        (primePower_hasValue (parameters.depth * wait))
        tail_scaled_value wait_lt_scaled
    have scaled_remainder_value :
        HasValue parameters.prime
          (drift parameters.center parameters.reset *
            (parameters.prime ^ (parameters.depth * wait) +
              parameters.prime ^ wait * tail))
          wait :=
      by
        simpa using
          mul_hasValue parameters.drift_unit positive_remainder_value
    have scaled_remainder_positive :
        IsPositive parameters.prime
          (drift parameters.center parameters.reset *
            (parameters.prime ^ (parameters.depth * wait) +
              parameters.prime ^ wait * tail)) :=
      ⟨scaled_remainder_value.1, by
        rw [scaled_remainder_value.2]
        exact_mod_cast wait_positive⟩
    have output_unit :
        IsUnit parameters.prime (legalValue parameters wait tail) := by
      rw [show legalValue parameters wait tail =
        drift parameters.center parameters.reset *
            (resonanceCenter parameters - tail) +
          drift parameters.center parameters.reset *
            (parameters.prime ^ (parameters.depth * wait) +
              parameters.prime ^ wait * tail) by
        rw [legalValue_eq_centeredTail]
        ring]
      exact unit_add_positive centered_term_unit scaled_remainder_positive
    have impossible := output_positive.2
    rw [output_unit.2] at impossible
    exact (lt_irrefl 0 impossible).elim

/-- Every nonzero positive tail displacement has a unique-depth prime-power/unit form. -/
theorem exists_tailAtDepth_of_positive
    (parameters : Parameters) (tail : ℚ)
    (difference_positive :
      IsPositive parameters.prime (tail - resonanceCenter parameters)) :
    ∃ tailDepth : Nat, 0 < tailDepth ∧
      ∃ residual : ℚ, IsUnit parameters.prime residual ∧
        tail = tailAtDepth parameters tailDepth residual := by
  obtain ⟨tailDepth, tailDepth_positive, residual, residual_unit,
      difference_eq⟩ :=
    positive_eq_primePower_mul_unit difference_positive
  exact ⟨tailDepth, tailDepth_positive, residual, residual_unit, by
    rw [tailAtDepth, ← difference_eq]
    ring⟩

/-- Below resonance, the tail depth is the exact valuation of the legal output. -/
theorem legalValue_tailAtDepth_hasValue_of_lt
    (parameters : Parameters) (wait tailDepth : Nat)
    (wait_positive : 0 < wait) (tailDepth_lt : tailDepth < wait)
    (residual : ℚ) (residual_unit : IsUnit parameters.prime residual) :
    HasValue parameters.prime
      (legalValue parameters wait
        (tailAtDepth parameters tailDepth residual))
      tailDepth := by
  have wait_lt_scaled : (wait : ℤ) < parameters.depth * wait := by
    exact_mod_cast (show wait < parameters.depth * wait by
      nlinarith [parameters.depth_two])
  have leading_value :=
    add_hasValue_left
      (center_scaled_hasValue parameters wait)
      (drift_scaled_hasValue parameters wait)
      wait_lt_scaled
  have perturbation_value :=
    tailPerturbation_hasValue parameters wait tailDepth wait_positive
      residual residual_unit
  rw [legalValue_tailAtDepth]
  exact add_hasValue_right leading_value perturbation_value (by
    exact_mod_cast tailDepth_lt)

/-- Above resonance, the center term fixes the output valuation at the current wait. -/
theorem legalValue_tailAtDepth_hasValue_of_gt
    (parameters : Parameters) (wait tailDepth : Nat)
    (wait_positive : 0 < wait) (wait_lt_tailDepth : wait < tailDepth)
    (residual : ℚ) (residual_unit : IsUnit parameters.prime residual) :
    HasValue parameters.prime
      (legalValue parameters wait
        (tailAtDepth parameters tailDepth residual))
      wait := by
  have wait_lt_scaled : (wait : ℤ) < parameters.depth * wait := by
    exact_mod_cast (show wait < parameters.depth * wait by
      nlinarith [parameters.depth_two])
  have leading_value :=
    add_hasValue_left
      (center_scaled_hasValue parameters wait)
      (drift_scaled_hasValue parameters wait)
      wait_lt_scaled
  have perturbation_value :=
    tailPerturbation_hasValue parameters wait tailDepth wait_positive
      residual residual_unit
  rw [legalValue_tailAtDepth]
  exact add_hasValue_left leading_value perturbation_value (by
    exact_mod_cast wait_lt_tailDepth)

/-- Above resonance, the readiness defect still has only the current wait valuation. -/
theorem legalValue_tailAtDepth_defect_hasValue_of_gt
    (parameters : Parameters) (wait tailDepth : Nat)
    (wait_positive : 0 < wait) (wait_lt_tailDepth : wait < tailDepth)
    (residual : ℚ) (residual_unit : IsUnit parameters.prime residual) :
    HasValue parameters.prime
      (legalValue parameters wait
          (tailAtDepth parameters tailDepth residual) -
        parameters.prime ^ wait)
      wait := by
  have center_defect_value :
      HasValue parameters.prime
        ((parameters.center - 1) * parameters.prime ^ wait) wait := by
    simpa using
      mul_hasValue parameters.center_sub_one_unit
        (primePower_hasValue wait)
  have wait_lt_scaled : (wait : ℤ) < parameters.depth * wait := by
    exact_mod_cast (show wait < parameters.depth * wait by
      nlinarith [parameters.depth_two])
  have leading_value :=
    add_hasValue_left center_defect_value
      (drift_scaled_hasValue parameters wait)
      wait_lt_scaled
  have perturbation_value :=
    tailPerturbation_hasValue parameters wait tailDepth wait_positive
      residual residual_unit
  rw [legalValue_tailAtDepth]
  have combined :=
    add_hasValue_left leading_value perturbation_value (by
      exact_mod_cast wait_lt_tailDepth)
  convert combined using 1
  ring

/-- A tail deeper than the selected wait produces a live but non-ready output. -/
theorem legalValue_tailAtDepth_not_ready_of_gt
    (parameters : Parameters) (wait tailDepth : Nat)
    (wait_positive : 0 < wait) (wait_lt_tailDepth : wait < tailDepth)
    (residual : ℚ) (residual_unit : IsUnit parameters.prime residual) :
    ¬Ready parameters wait
      (legalValue parameters wait
        (tailAtDepth parameters tailDepth residual)) := by
  intro ready
  have defect_value :=
    legalValue_tailAtDepth_defect_hasValue_of_gt parameters wait tailDepth
      wait_positive wait_lt_tailDepth residual residual_unit
  have wait_lt_scaled : wait < parameters.depth * wait := by
    nlinarith [parameters.depth_two]
  have impossible : (wait : ℤ) = parameters.depth * wait :=
    defect_value.2.symm.trans ready.2.2
  have impossible_ne : (wait : ℤ) ≠ parameters.depth * wait := by
    exact_mod_cast (ne_of_lt wait_lt_scaled)
  exact impossible_ne impossible

/-- Every subsequent positive wait from an above-resonance output is poisoned. -/
theorem tailDepth_gt_next_step_is_trap
    (parameters : Parameters) (wait tailDepth nextWait : Nat)
    (wait_positive : 0 < wait) (wait_lt_tailDepth : wait < tailDepth)
    (nextWait_positive : 0 < nextWait)
    (residual : ℚ) (residual_unit : IsUnit parameters.prime residual) :
    Trap parameters
      (guardedStep parameters nextWait
        (some
          (legalValue parameters wait
            (tailAtDepth parameters tailDepth residual)))) := by
  let output :=
    legalValue parameters wait
      (tailAtDepth parameters tailDepth residual)
  have output_value :=
    legalValue_tailAtDepth_hasValue_of_gt parameters wait tailDepth
      wait_positive wait_lt_tailDepth residual residual_unit
  have output_positive : IsPositive parameters.prime output :=
    ⟨output_value.1, by
      rw [output_value.2]
      exact_mod_cast wait_positive⟩
  by_cases next_eq : nextWait = wait
  · subst nextWait
    apply depth_mismatch_is_trap parameters wait output output_positive
    intro depth_eq
    have defect_value :=
      legalValue_tailAtDepth_defect_hasValue_of_gt parameters wait tailDepth
        wait_positive wait_lt_tailDepth residual residual_unit
    have impossible : (wait : ℤ) = parameters.depth * wait :=
      defect_value.2.symm.trans depth_eq
    have wait_lt_scaled : wait < parameters.depth * wait := by
      nlinarith [parameters.depth_two]
    have impossible_ne : (wait : ℤ) ≠ parameters.depth * wait := by
      exact_mod_cast (ne_of_lt wait_lt_scaled)
    exact impossible_ne impossible
  · apply wrong_wait_is_trap parameters nextWait nextWait_positive output output_positive
    rw [output_value.2]
    intro wait_eq
    apply next_eq
    exact_mod_cast wait_eq.symm

/-- A ready continuation below resonance must use the smaller tail depth as its next wait. -/
theorem nextReady_wait_eq_tailDepth_of_lt
    (parameters : Parameters) (wait tailDepth nextWait : Nat)
    (wait_positive : 0 < wait) (tailDepth_lt : tailDepth < wait)
    (residual : ℚ) (residual_unit : IsUnit parameters.prime residual)
    (next_ready :
      Ready parameters nextWait
        (legalValue parameters wait
          (tailAtDepth parameters tailDepth residual))) :
    nextWait = tailDepth := by
  have output_value :=
    legalValue_tailAtDepth_hasValue_of_lt parameters wait tailDepth
      wait_positive tailDepth_lt residual residual_unit
  exact_mod_cast next_ready.2.1.symm.trans output_value.2

/-- At the exact tail center, the output contains only the current and expanding scales. -/
theorem legalValue_resonanceCenter
    (parameters : Parameters) (wait : Nat) :
    legalValue parameters wait (resonanceCenter parameters) =
      parameters.center * parameters.prime ^ wait +
        drift parameters.center parameters.reset *
          parameters.prime ^ (parameters.depth * wait) := by
  simpa [tailAtDepth] using
    legalValue_tailAtDepth parameters wait 0 0

/-- The exact tail center leaves the output at the current wait valuation. -/
theorem legalValue_resonanceCenter_hasValue
    (parameters : Parameters) (wait : Nat) (wait_positive : 0 < wait) :
    HasValue parameters.prime
      (legalValue parameters wait (resonanceCenter parameters)) wait := by
  have wait_lt_scaled : (wait : ℤ) < parameters.depth * wait := by
    exact_mod_cast (show wait < parameters.depth * wait by
      nlinarith [parameters.depth_two])
  rw [legalValue_resonanceCenter]
  exact add_hasValue_left
    (center_scaled_hasValue parameters wait)
    (drift_scaled_hasValue parameters wait)
    wait_lt_scaled

/-- The exact tail center also leaves the readiness defect at the current wait valuation. -/
theorem legalValue_resonanceCenter_defect_hasValue
    (parameters : Parameters) (wait : Nat) (wait_positive : 0 < wait) :
    HasValue parameters.prime
      (legalValue parameters wait (resonanceCenter parameters) -
        parameters.prime ^ wait)
      wait := by
  have center_defect_value :
      HasValue parameters.prime
        ((parameters.center - 1) * parameters.prime ^ wait) wait := by
    simpa using
      mul_hasValue parameters.center_sub_one_unit
        (primePower_hasValue wait)
  have wait_lt_scaled : (wait : ℤ) < parameters.depth * wait := by
    exact_mod_cast (show wait < parameters.depth * wait by
      nlinarith [parameters.depth_two])
  rw [legalValue_resonanceCenter]
  convert
    add_hasValue_left center_defect_value
      (drift_scaled_hasValue parameters wait)
      wait_lt_scaled using 1
  ring

/-- The exact center tail cannot produce any next ready state. -/
theorem resonanceCenter_no_ready_output
    (parameters : Parameters) (wait nextWait : Nat) (wait_positive : 0 < wait) :
    ¬Ready parameters nextWait
      (legalValue parameters wait (resonanceCenter parameters)) := by
  intro next_ready
  have output_value :=
    legalValue_resonanceCenter_hasValue parameters wait wait_positive
  have next_eq : nextWait = wait := by
    exact_mod_cast next_ready.2.1.symm.trans output_value.2
  subst nextWait
  have defect_value :=
    legalValue_resonanceCenter_defect_hasValue parameters wait wait_positive
  have impossible : (wait : ℤ) = parameters.depth * wait :=
    defect_value.2.symm.trans next_ready.2.2
  have wait_lt_scaled : wait < parameters.depth * wait := by
    nlinarith [parameters.depth_two]
  have impossible_ne : (wait : ℤ) ≠ parameters.depth * wait := by
    exact_mod_cast (ne_of_lt wait_lt_scaled)
  exact impossible_ne impossible

/-- Every nonresonant ready continuation strictly decreases the positive wait. -/
theorem nonresonant_nextWait_lt
    (parameters : Parameters) (wait nextWait : Nat) (wait_positive : 0 < wait)
    (tail : ℚ) (tail_unit : IsUnit parameters.prime tail)
    (next_ready :
      Ready parameters nextWait (legalValue parameters wait tail))
    (nonresonant : ¬ResonantTail parameters wait tail) :
    nextWait < wait := by
  have output_positive :=
    ready_isPositive parameters nextWait
      (legalValue parameters wait tail) next_ready
  rcases legalValue_isPositive_forces_tail_resonance
      parameters wait wait_positive tail tail_unit output_positive with
    centered | difference_positive
  · subst tail
    exact (resonanceCenter_no_ready_output
      parameters wait nextWait wait_positive next_ready).elim
  · obtain ⟨tailDepth, _, residual, residual_unit, tail_eq⟩ :=
      exists_tailAtDepth_of_positive parameters tail difference_positive
    by_cases below : tailDepth < wait
    · have next_eq :=
        nextReady_wait_eq_tailDepth_of_lt parameters wait tailDepth nextWait
          wait_positive below residual residual_unit (tail_eq ▸ next_ready)
      omega
    have wait_le_depth : wait ≤ tailDepth := le_of_not_gt below
    rcases wait_le_depth.eq_or_lt with equal | above
    · apply (nonresonant ⟨residual, residual_unit, ?_⟩).elim
      simpa [equal] using tail_eq
    · have output_value :=
        legalValue_tailAtDepth_hasValue_of_gt parameters wait tailDepth
          wait_positive above residual residual_unit
      have next_eq : nextWait = wait := by
        exact_mod_cast next_ready.2.1.symm.trans
          (tail_eq ▸ output_value.2)
      subst nextWait
      exfalso
      apply (legalValue_tailAtDepth_not_ready_of_gt
        parameters wait tailDepth wait_positive above residual residual_unit)
      simpa [tail_eq] using next_ready

/-- Every infinite ready-tail chain contains resonances arbitrarily far along the chain. -/
theorem infinite_ready_chain_resonates
    (parameters : Parameters)
    (waits : Nat → Nat) (tails : Nat → ℚ)
    (wait_positive : ∀ index, 0 < waits index)
    (tail_unit : ∀ index, IsUnit parameters.prime (tails index))
    (next_ready :
      ∀ index,
        Ready parameters (waits (index + 1))
          (legalValue parameters (waits index) (tails index))) :
    ∀ start, ∃ index, start ≤ index ∧
      ResonantTail parameters (waits index) (tails index) := by
  intro start
  by_contra no_resonance
  have nonresonant :
      ∀ index, start ≤ index →
        ¬ResonantTail parameters (waits index) (tails index) := by
    intro index start_le resonance
    exact no_resonance ⟨index, start_le, resonance⟩
  have descending :
      ∀ offset, waits (start + offset) + offset ≤ waits start := by
    intro offset
    induction offset with
    | zero => simp
    | succ offset induction =>
        have step_lt :
            waits (start + (offset + 1)) < waits (start + offset) := by
          simpa [Nat.add_assoc] using
            nonresonant_nextWait_lt parameters
              (waits (start + offset)) (waits (start + offset + 1))
              (wait_positive (start + offset))
              (tails (start + offset)) (tail_unit (start + offset))
              (next_ready (start + offset))
              (nonresonant (start + offset) (Nat.le_add_right start offset))
        omega
  have impossible := descending (waits start + 1)
  omega

/-- A prime-power-scaled unit is ready exactly when its normalized defect has depth
`(depth - 1) * wait`. -/
theorem primePower_mul_ready_iff
    (parameters : Parameters) (wait : Nat) (wait_positive : 0 < wait)
    (residual : ℚ) (residual_unit : IsUnit parameters.prime residual) :
    Ready parameters wait (parameters.prime ^ wait * residual) ↔
      padicValRat parameters.prime (residual - 1) =
        (((parameters.depth - 1) * wait : Nat) : ℤ) := by
  have state_value :
      HasValue parameters.prime
        (parameters.prime ^ wait * residual) wait :=
    mul_hasValue (primePower_hasValue wait) residual_unit
  have normalized_depth_positive :
      0 < (parameters.depth - 1) * wait := by
    apply Nat.mul_pos
    · exact Nat.sub_pos_of_lt
        (lt_of_lt_of_le Nat.one_lt_two parameters.depth_two)
    · exact wait_positive
  have depth_split :
      parameters.depth * wait =
        wait + (parameters.depth - 1) * wait :=
    depth_mul_eq_wait_add_residualDepth parameters wait
  have defect_eq :
      parameters.prime ^ wait * residual - parameters.prime ^ wait =
        parameters.prime ^ wait * (residual - 1) := by
    ring
  constructor
  · intro ready
    have residual_sub_one_ne : residual - 1 ≠ 0 := by
      intro residual_eq
      have defect_zero :
          parameters.prime ^ wait * residual - parameters.prime ^ wait = 0 := by
        rw [defect_eq, residual_eq, mul_zero]
      have impossible := ready.2.2
      rw [defect_zero, padicValRat.zero] at impossible
      have scaled_positive : 0 < parameters.depth * wait :=
        Nat.mul_pos parameters.depth_positive wait_positive
      omega
    have defect_value :
        HasValue parameters.prime
          (parameters.prime ^ wait * residual - parameters.prime ^ wait)
          (wait + padicValRat parameters.prime (residual - 1)) := by
      rw [defect_eq]
      exact mul_hasValue (primePower_hasValue wait)
        ⟨residual_sub_one_ne, rfl⟩
    have defect_depth := ready.2.2
    rw [defect_value.2] at defect_depth
    omega
  · intro normalized_depth
    have residual_sub_one_ne : residual - 1 ≠ 0 := by
      intro residual_eq
      have impossible := normalized_depth
      rw [residual_eq, padicValRat.zero] at impossible
      omega
    have defect_value :
        HasValue parameters.prime
          (parameters.prime ^ wait * residual - parameters.prime ^ wait)
          (wait + padicValRat parameters.prime (residual - 1)) := by
      rw [defect_eq]
      exact mul_hasValue (primePower_hasValue wait)
        ⟨residual_sub_one_ne, rfl⟩
    refine ⟨wait_positive, state_value.2, ?_⟩
    rw [defect_value.2, normalized_depth]
    omega

/-- Correct nested-readiness law after an equal-depth resonance. -/
theorem resonance_ready_iff
    (parameters : Parameters) (wait carry : Nat) (wait_positive : 0 < wait)
    (residual normalized : ℚ)
    (normalized_unit : IsUnit parameters.prime normalized)
    (resonance_normalized :
      resonanceValue parameters wait residual =
        parameters.prime ^ carry * normalized) :
    Ready parameters (wait + carry)
        (legalValue parameters wait
          (tailAtDepth parameters wait residual)) ↔
      padicValRat parameters.prime (normalized - 1) =
        (((parameters.depth - 1) * (wait + carry) : Nat) : ℤ) := by
  have wait_sum_positive : 0 < wait + carry := Nat.add_pos_left wait_positive _
  have output_eq :
      legalValue parameters wait
          (tailAtDepth parameters wait residual) =
        parameters.prime ^ (wait + carry) * normalized := by
    rw [legalValue_resonance, resonance_normalized, pow_add]
    ring
  rw [output_eq]
  exact
    primePower_mul_ready_iff parameters (wait + carry) wait_sum_positive
      normalized normalized_unit

end
end MatrixMortality.ReturnGuard
