import MatrixMortality.ReturnGuardAntiHensel

/-!
# A dead parameter-lift cylinder

One arithmetic progression of valid guard parameters has the same legal wait prefix `1, 3`
for every integer parameter digit.  After those two steps, however, the next guarded state is
always a `3`-adic unit.  No positive wait exists, so the decoded orbit is dead.

This is a compact exact witness that parameter sensitivity does not by itself induct a legal
prefix.  Readiness is an annulus, not a Hensel root: satisfying one divisibility constraint can
force the next state outside the live region throughout an entire congruence cylinder.
-/

namespace MatrixMortality.ReturnGuard.Examples

open MatrixMortality.PadicValuation

noncomputable section

private theorem three_not_dvd_three_mul_add_one (value : ℤ) :
    ¬(3 : ℤ) ∣ 3 * value + 1 := by
  rintro ⟨quotient, equality⟩
  omega

private theorem three_not_dvd_three_mul_add_two (value : ℤ) :
    ¬(3 : ℤ) ∣ 3 * value + 2 := by
  rintro ⟨quotient, equality⟩
  omega

private theorem deadLiftResidual_identity
    (digit : ℚ)
    (negative_ne : 40589 - digit * 109350 ≠ 0)
    (positive_ne : -40589 + digit * 109350 ≠ 0) :
    27 +
        (digit * (40589 - digit * 109350)⁻¹ * 2843100 -
          (40589 - digit * 109350)⁻¹ * 1055808) =
      digit * (-40589 + digit * 109350)⁻¹ * 109350 -
        (-40589 + digit * 109350)⁻¹ * 40095 := by
  field_simp [negative_ne, positive_ne]
  ring

private theorem deadLiftTerminal_identity
    (digit : ℚ) (denominator_ne : -55 + digit * 150 ≠ 0) :
    -460 + digit * 729 +
          digit * (-55 + digit * 150)⁻¹ * 61519581 +
          (-(digit ^ 2 * (-55 + digit * 150)⁻¹ * 79716150) -
            (-55 + digit * 150)⁻¹ * 11851988) =
      digit * (-55 + digit * 150)⁻¹ * 61410486 +
        (-(digit ^ 2 * (-55 + digit * 150)⁻¹ * 79606800) -
          (-55 + digit * 150)⁻¹ * 11826688) := by
  field_simp [denominator_ne]
  ring

/-- A full congruence cylinder of centers sharing a legal two-step prefix. -/
def deadLiftParameters (digit : ℤ) : Parameters where
  prime := 3
  prime_prime := by norm_num
  depth := 2
  depth_two := by norm_num
  center := (-460 + 729 * digit : ℤ)
  reset := -168
  center_unit := by
    apply intCast_isUnit_of_not_dvd
    rw [show
      (-460 + 729 * digit : ℤ) =
        3 * (-154 + 243 * digit) + 2 by ring]
    exact three_not_dvd_three_mul_add_two _
  center_sub_one_unit := by
    have center_sub_one :
      ((-460 + 729 * digit : ℤ) : ℚ) - 1 =
        ((-461 + 729 * digit : ℤ) : ℚ) := by
      push_cast
      ring
    rw [center_sub_one]
    apply intCast_isUnit_of_not_dvd
    rw [show
      (-461 + 729 * digit : ℤ) =
        3 * (-154 + 243 * digit) + 1 by ring]
    exact three_not_dvd_three_mul_add_one _
  reset_positive := by
    have reset_value :
        HasValue 3 (-168 : ℚ) 1 := by
      rw [show (-168 : ℚ) =
        (3 : ℚ) ^ 1 * (-56 : ℚ) / (1 : ℚ) by norm_num]
      exact
        primePower_mul_int_div_int_hasValue 1
          (by norm_num) (by norm_num)
    exact ⟨reset_value.1, by rw [reset_value.2]; norm_num⟩

/-- The first legal step has residual `19/169`, independently of the center digit. -/
def deadLiftResidualOne : ℚ :=
  19 / 169

/-- Residual after the forced wait-three step. -/
def deadLiftResidualTwo (digit : ℤ) : ℚ :=
  5 * (30 * digit - 11) / (109350 * digit - 40589)

private theorem deadLift_reset_ready (digit : ℤ) :
    Ready (deadLiftParameters digit) 1 (-168) := by
  have state_value :
      HasValue 3 (-168 : ℚ) 1 := by
    rw [show (-168 : ℚ) =
      (3 : ℚ) ^ 1 * (-56 : ℚ) / (1 : ℚ) by norm_num]
    exact
      primePower_mul_int_div_int_hasValue 1
        (by norm_num) (by norm_num)
  have defect_value :
      HasValue 3 ((-168 : ℚ) - 3) 2 := by
    rw [show (-168 : ℚ) - 3 =
      (3 : ℚ) ^ 2 * (-19 : ℚ) / (1 : ℚ) by norm_num]
    exact
      primePower_mul_int_div_int_hasValue 2
        (by norm_num) (by norm_num)
  exact ⟨by norm_num, state_value.2, defect_value.2⟩

private theorem deadLift_state_one_ready (digit : ℤ) :
    Ready (deadLiftParameters digit) 3
      ((40608 - 109350 * digit : ℤ) / 19) := by
  have unit_numerator :
      IsUnit 3 ((1504 - 4050 * digit : ℤ) : ℚ) := by
    apply intCast_isUnit_of_not_dvd
    rw [show
      (1504 - 4050 * digit : ℤ) =
        3 * (501 - 1350 * digit) + 1 by ring]
    exact three_not_dvd_three_mul_add_one _
  have unit_defect :
      IsUnit 3 ((55 - 150 * digit : ℤ) : ℚ) := by
    apply intCast_isUnit_of_not_dvd
    rw [show
      (55 - 150 * digit : ℤ) =
        3 * (18 - 50 * digit) + 1 by ring]
    exact three_not_dvd_three_mul_add_one _
  have denominator_unit : IsUnit 3 (19 : ℚ) :=
    intCast_isUnit_of_not_dvd (by norm_num)
  have state_value :
      HasValue 3 (((40608 - 109350 * digit : ℤ) : ℚ) / 19) 3 := by
    rw [show
      ((40608 - 109350 * digit : ℤ) : ℚ) / 19 =
        (3 : ℚ) ^ 3 *
          ((1504 - 4050 * digit : ℤ) : ℚ) / 19 by
            push_cast
            ring]
    exact
      div_hasValue
        (mul_hasValue (primePower_hasValue 3) unit_numerator)
        denominator_unit
  have defect_value :
      HasValue 3
        (((40608 - 109350 * digit : ℤ) : ℚ) / 19 - 3 ^ 3) 6 := by
    rw [show
      ((40608 - 109350 * digit : ℤ) : ℚ) / 19 - 3 ^ 3 =
        (3 : ℚ) ^ 6 *
          ((55 - 150 * digit : ℤ) : ℚ) / 19 by
            push_cast
            ring]
    exact
      div_hasValue
        (mul_hasValue (primePower_hasValue 6) unit_defect)
        denominator_unit
  exact ⟨by norm_num, state_value.2, defect_value.2⟩

/-- Every center in the cylinder follows the same legal wait word `1, 3`. -/
theorem deadLift_twoStepPrefix (digit : ℤ) :
    DecodedStep (deadLiftParameters digit) 1 deadLiftResidualOne ∧
      DecodedStep (deadLiftParameters digit)
        deadLiftResidualOne (deadLiftResidualTwo digit) := by
  constructor
  · refine ⟨1, ?_, ?_⟩
    · rw [residualBranch_iff_ready]
      simpa [stateOfResidual_one] using deadLift_reset_ready digit
    · norm_num [deadLiftResidualOne, residualStep, prefixDecode,
        centerTransform, deadLiftParameters, drift]
  · refine ⟨3, ?_, ?_⟩
    · rw [residualBranch_iff_ready]
      convert deadLift_state_one_ready digit using 1
      simp [stateOfResidual, deadLiftResidualOne,
        deadLiftParameters, drift]
      field_simp
      ring
    · have denominator_not_dvd :
          ¬(3 : ℤ) ∣ 109350 * digit - 40589 := by
        rw [show
          (109350 * digit - 40589 : ℤ) =
            3 * (36450 * digit - 13530) + 1 by ring]
        exact three_not_dvd_three_mul_add_one _
      have denominator_ne :
          ((109350 * digit - 40589 : ℤ) : ℚ) ≠ 0 := by
        exact_mod_cast
          (show (109350 * digit - 40589 : ℤ) ≠ 0 by
            intro denominator_zero
            apply denominator_not_dvd
            rw [denominator_zero]
            exact dvd_zero 3)
      have denominator_neg_ne :
          (40589 : ℚ) - (digit : ℚ) * 109350 ≠ 0 := by
        have negated :=
          neg_ne_zero.mpr denominator_ne
        convert negated using 1
        push_cast
        ring
      have denominator_pos_ne :
          (-40589 : ℚ) + (digit : ℚ) * 109350 ≠ 0 := by
        have negated :=
          neg_ne_zero.mpr denominator_neg_ne
        convert negated using 1
        ring
      simp [deadLiftResidualOne, deadLiftResidualTwo, residualStep,
        prefixDecode, centerTransform, deadLiftParameters, drift]
      field_simp [denominator_ne, denominator_neg_ne,
        denominator_pos_ne]
      ring_nf
      exact deadLiftResidual_identity digit
        denominator_neg_ne denominator_pos_ne

private theorem deadLift_terminalState_eq (digit : ℤ) :
    stateOfResidual (deadLiftParameters digit)
        (deadLiftResidualTwo digit) =
      -2 *
          (39803400 * digit ^ 2 - 30705243 * digit + 5913344 : ℤ) /
        (5 * (30 * digit - 11) : ℤ) := by
  have denominator_not_dvd :
      ¬(3 : ℤ) ∣ 30 * digit - 11 := by
    rw [show
      (30 * digit - 11 : ℤ) =
        3 * (10 * digit - 4) + 1 by ring]
    exact three_not_dvd_three_mul_add_one _
  have denominator_ne :
      ((30 * digit - 11 : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast
      (show (30 * digit - 11 : ℤ) ≠ 0 by
        intro denominator_zero
        apply denominator_not_dvd
        rw [denominator_zero]
        exact dvd_zero 3)
  have scaled_denominator_ne :
      (-55 : ℚ) + (digit : ℚ) * 150 ≠ 0 := by
    have product_ne :
        (5 : ℚ) * ((30 * digit - 11 : ℤ) : ℚ) ≠ 0 :=
      mul_ne_zero (by norm_num) denominator_ne
    convert product_ne using 1
    push_cast
    ring
  simp [stateOfResidual, deadLiftResidualTwo, deadLiftParameters, drift]
  field_simp [denominator_ne, scaled_denominator_ne]
  ring_nf
  exact deadLiftTerminal_identity digit scaled_denominator_ne

/-- The state after the shared legal prefix is always a `3`-adic unit. -/
theorem deadLift_terminalState_isUnit (digit : ℤ) :
    IsUnit 3
      (stateOfResidual (deadLiftParameters digit)
        (deadLiftResidualTwo digit)) := by
  let numerator : ℤ :=
    39803400 * digit ^ 2 - 30705243 * digit + 5913344
  have numerator_unit : IsUnit 3 (numerator : ℚ) := by
    apply intCast_isUnit_of_not_dvd
    rw [show
      numerator =
        3 *
            (13267800 * digit ^ 2 - 10235081 * digit + 1971114) +
          2 by
            simp [numerator]
            ring]
    exact three_not_dvd_three_mul_add_two _
  have denominator_unit :
      IsUnit 3 ((5 * (30 * digit - 11) : ℤ) : ℚ) := by
    have five_unit : IsUnit 3 (5 : ℚ) :=
      intCast_isUnit_of_not_dvd (by norm_num)
    have linear_unit : IsUnit 3 (((30 * digit - 11 : ℤ) : ℚ)) := by
      apply intCast_isUnit_of_not_dvd
      rw [show
        (30 * digit - 11 : ℤ) =
          3 * (10 * digit - 4) + 1 by ring]
      exact three_not_dvd_three_mul_add_one _
    simpa only [Int.cast_mul] using mul_hasValue five_unit linear_unit
  rw [deadLift_terminalState_eq]
  exact
    div_hasValue
      (mul_hasValue
        (intCast_isUnit_of_not_dvd (by norm_num) : IsUnit 3 (-2 : ℚ))
        numerator_unit)
      denominator_unit

/-- No third decoded step exists anywhere in the center congruence cylinder. -/
theorem deadLift_noThirdStep (digit : ℤ) :
    ¬∃ target, DecodedStep (deadLiftParameters digit)
      (deadLiftResidualTwo digit) target := by
  rintro ⟨target, wait, branch, _⟩
  have ready :=
    (residualBranch_iff_ready
      (deadLiftParameters digit) wait (deadLiftResidualTwo digit)).mp branch
  have unit := deadLift_terminalState_isUnit digit
  have valuation_eq := ready.2.1
  change
    padicValRat 3
        (stateOfResidual (deadLiftParameters digit)
          (deadLiftResidualTwo digit)) =
      (wait : ℤ) at valuation_eq
  rw [unit.2] at valuation_eq
  have wait_zero : wait = 0 := by
    exact_mod_cast valuation_eq.symm
  exact (Nat.ne_of_gt ready.1) wait_zero

end
end MatrixMortality.ReturnGuard.Examples
