import MatrixMortality.ReturnGuardParameterLattice
import MatrixMortality.ReturnGuardParameterPlaneExamples

/-!
# An anisotropic three-step parameter cylinder

The one-parameter center cylinder at center `998`, reset `-168` dies after waits `1,3`.
Moving reset by `3^8` gives one three-step witness.  The witness is not isolated: every integral
parameter pair

```text
center = 998 + 3^8 c,
reset  = 6393 + 3^11 r
```

has the legal wait prefix `1,3,1`.  The different exponents are the first exact parameter
lattice visible in the guard.  Center and reset refinements do not live at one common precision.
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

/-- Two-dimensional anisotropic refinement of the reset-escape witness. -/
def weightedEscapeParameters (centerDigit resetDigit : ℤ) : Parameters where
  prime := 3
  prime_prime := by norm_num
  depth := 2
  depth_two := by norm_num
  center := (998 + 3 ^ 8 * centerDigit : ℤ)
  reset := (6393 + 3 ^ 11 * resetDigit : ℤ)
  center_unit := by
    apply intCast_isUnit_of_not_dvd
    rw [show
      (998 + 3 ^ 8 * centerDigit : ℤ) =
        3 * (332 + 2187 * centerDigit) + 2 by ring]
    exact three_not_dvd_three_mul_add_two _
  center_sub_one_unit := by
    rw [show
      (((998 + 3 ^ 8 * centerDigit : ℤ) : ℚ) - 1) =
        ((997 + 3 ^ 8 * centerDigit : ℤ) : ℚ) by
          push_cast
          ring]
    apply intCast_isUnit_of_not_dvd
    rw [show
      (997 + 3 ^ 8 * centerDigit : ℤ) =
        3 * (332 + 2187 * centerDigit) + 1 by ring]
    exact three_not_dvd_three_mul_add_one _
  reset_positive := by
    have resetUnit :
        IsUnit 3 (((59049 * resetDigit + 2131 : ℤ) : ℚ)) := by
      apply intCast_isUnit_of_not_dvd
      rw [show
        (59049 * resetDigit + 2131 : ℤ) =
          3 * (19683 * resetDigit + 710) + 1 by ring]
      exact three_not_dvd_three_mul_add_one _
    have resetValue :
        HasValue 3
          ((3 : ℚ) ^ 1 *
            ((59049 * resetDigit + 2131 : ℤ) : ℚ)) 1 := by
      simpa using mul_hasValue (primePower_hasValue 1) resetUnit
    have resetPositive :
        IsPositive 3
          ((3 : ℚ) ^ 1 *
            ((59049 * resetDigit + 2131 : ℤ) : ℚ)) :=
      ⟨resetValue.1, by rw [resetValue.2]; norm_num⟩
    convert resetPositive using 1
    push_cast
    ring

/-- Unit numerator of the first residual throughout the weighted cylinder. -/
def weightedEscapeNumeratorOne (resetDigit : ℤ) : ℤ :=
  19683 * resetDigit + 710

/-- Unit denominator of the first residual throughout the weighted cylinder. -/
def weightedEscapeDenominatorOne (resetDigit : ℤ) : ℤ :=
  177147 * resetDigit + 6392

/-- Residual after the first wait in the weighted cylinder. -/
def weightedEscapeResidualOne (resetDigit : ℤ) : ℚ :=
  weightedEscapeNumeratorOne resetDigit /
    weightedEscapeDenominatorOne resetDigit

/-- Unit numerator of the second residual throughout the weighted cylinder. -/
def weightedEscapeNumeratorTwo
    (centerDigit resetDigit : ℤ) : ℤ :=
  -1417176 * centerDigit * resetDigit -
      51138 * centerDigit +
    43046721 * resetDigit ^ 2 +
      2890458 * resetDigit +
    48250

/-- Unit denominator of the second residual throughout the weighted cylinder. -/
def weightedEscapeDenominatorTwo
    (centerDigit resetDigit : ℤ) : ℤ :=
  -1033121304 * centerDigit * resetDigit -
      37279602 * centerDigit +
    31381059609 * resetDigit ^ 2 +
      2107655640 * resetDigit +
    35192710

/-- Residual after the second wait in the weighted cylinder. -/
def weightedEscapeResidualTwo
    (centerDigit resetDigit : ℤ) : ℚ :=
  weightedEscapeNumeratorTwo centerDigit resetDigit /
    weightedEscapeDenominatorTwo centerDigit resetDigit

/-- Unit numerator of the third residual throughout the weighted cylinder. -/
def weightedEscapeNumeratorThree
    (centerDigit resetDigit : ℤ) : ℤ :=
  752112309312 * centerDigit ^ 2 * resetDigit +
      27139550256 * centerDigit ^ 2 -
    43180338021984 * centerDigit * resetDigit ^ 2 -
      2887603726644 * centerDigit * resetDigit -
    47973015240 * centerDigit +
      617673396283947 * resetDigit ^ 3 +
    60300946859670 * resetDigit ^ 2 +
      1956440131320 * resetDigit +
    21101408800

/-- Unit denominator of the third residual throughout the weighted cylinder. -/
def weightedEscapeDenominatorThree
    (centerDigit resetDigit : ℤ) : ℤ :=
  6769010783808 * centerDigit ^ 2 * resetDigit +
      244255952304 * centerDigit ^ 2 -
    388623042197856 * centerDigit * resetDigit ^ 2 -
      25988436374148 * centerDigit * resetDigit -
    431757239436 * centerDigit +
      5559060566555523 * resetDigit ^ 3 +
    542708607830472 * resetDigit ^ 2 +
      17607966962796 * resetDigit +
    189912775700

/-- Residual after the third wait in the weighted cylinder. -/
def weightedEscapeResidualThree
    (centerDigit resetDigit : ℤ) : ℚ :=
  weightedEscapeNumeratorThree centerDigit resetDigit /
    weightedEscapeDenominatorThree centerDigit resetDigit

private theorem weightedEscapeNumeratorOne_unit (resetDigit : ℤ) :
    IsUnit 3 ((weightedEscapeNumeratorOne resetDigit : ℤ) : ℚ) := by
  apply intCast_isUnit_of_not_dvd
  rw [show
    weightedEscapeNumeratorOne resetDigit =
      3 * (6561 * resetDigit + 236) + 2 by
        simp [weightedEscapeNumeratorOne]
        ring]
  exact three_not_dvd_three_mul_add_two _

private theorem weightedEscapeDenominatorOne_unit (resetDigit : ℤ) :
    IsUnit 3 ((weightedEscapeDenominatorOne resetDigit : ℤ) : ℚ) := by
  apply intCast_isUnit_of_not_dvd
  rw [show
    weightedEscapeDenominatorOne resetDigit =
      3 * (59049 * resetDigit + 2130) + 2 by
        simp [weightedEscapeDenominatorOne]
        ring]
  exact three_not_dvd_three_mul_add_two _

private theorem weightedEscapeNumeratorTwo_unit
    (centerDigit resetDigit : ℤ) :
    IsUnit 3
      ((weightedEscapeNumeratorTwo centerDigit resetDigit : ℤ) : ℚ) := by
  apply intCast_isUnit_of_not_dvd
  rw [show
    weightedEscapeNumeratorTwo centerDigit resetDigit =
      3 *
          (-472392 * centerDigit * resetDigit -
              17046 * centerDigit +
            14348907 * resetDigit ^ 2 +
              963486 * resetDigit +
            16083) +
        1 by
          simp [weightedEscapeNumeratorTwo]
          ring]
  exact three_not_dvd_three_mul_add_one _

private theorem weightedEscapeDenominatorTwo_unit
    (centerDigit resetDigit : ℤ) :
    IsUnit 3
      ((weightedEscapeDenominatorTwo centerDigit resetDigit : ℤ) : ℚ) := by
  apply intCast_isUnit_of_not_dvd
  rw [show
    weightedEscapeDenominatorTwo centerDigit resetDigit =
      3 *
          (-344373768 * centerDigit * resetDigit -
              12426534 * centerDigit +
            10460353203 * resetDigit ^ 2 +
              702551880 * resetDigit +
            11730903) +
        1 by
          simp [weightedEscapeDenominatorTwo]
          ring]
  exact three_not_dvd_three_mul_add_one _

private theorem weightedEscapeNumeratorThree_unit
    (centerDigit resetDigit : ℤ) :
    IsUnit 3
      ((weightedEscapeNumeratorThree centerDigit resetDigit : ℤ) : ℚ) := by
  apply intCast_isUnit_of_not_dvd
  rw [show
    weightedEscapeNumeratorThree centerDigit resetDigit =
      3 *
          (250704103104 * centerDigit ^ 2 * resetDigit +
              9046516752 * centerDigit ^ 2 -
            14393446007328 * centerDigit * resetDigit ^ 2 -
              962534575548 * centerDigit * resetDigit -
            15991005080 * centerDigit +
              205891132094649 * resetDigit ^ 3 +
            20100315619890 * resetDigit ^ 2 +
              652146710440 * resetDigit +
            7033802933) +
        1 by
          simp [weightedEscapeNumeratorThree]
          ring]
  exact three_not_dvd_three_mul_add_one _

private theorem weightedEscapeDenominatorThree_unit
    (centerDigit resetDigit : ℤ) :
    IsUnit 3
      ((weightedEscapeDenominatorThree centerDigit resetDigit : ℤ) : ℚ) := by
  apply intCast_isUnit_of_not_dvd
  rw [show
    weightedEscapeDenominatorThree centerDigit resetDigit =
      3 *
          (2256336927936 * centerDigit ^ 2 * resetDigit +
              81418650768 * centerDigit ^ 2 -
            129541014065952 * centerDigit * resetDigit ^ 2 -
              8662812124716 * centerDigit * resetDigit -
            143919079812 * centerDigit +
              1853020188851841 * resetDigit ^ 3 +
            180902869276824 * resetDigit ^ 2 +
              5869322320932 * resetDigit +
            63304258566) +
        2 by
          simp [weightedEscapeDenominatorThree]
          ring]
  exact three_not_dvd_three_mul_add_two _

private def weightedEscapeStateOneNumerator
    (centerDigit resetDigit : ℤ) : ℤ :=
  -38263752 * centerDigit * resetDigit -
      1380726 * centerDigit +
    1162261467 * resetDigit ^ 2 +
      78062049 * resetDigit +
    1303460

private def weightedEscapeStateTwoNumerator
    (centerDigit resetDigit : ℤ) : ℤ :=
  2256336927936 * centerDigit ^ 2 * resetDigit +
      81418650768 * centerDigit ^ 2 -
    129541014065952 * centerDigit * resetDigit ^ 2 -
      8662812597108 * centerDigit * resetDigit -
    143919096858 * centerDigit +
      1853020188851841 * resetDigit ^ 3 +
    180902883625731 * resetDigit ^ 2 +
      5869323284418 * resetDigit +
    63304274650

private theorem weightedEscapeStateOneNumerator_unit
    (centerDigit resetDigit : ℤ) :
    IsUnit 3
      ((weightedEscapeStateOneNumerator centerDigit resetDigit : ℤ) : ℚ) := by
  apply intCast_isUnit_of_not_dvd
  rw [show
    weightedEscapeStateOneNumerator centerDigit resetDigit =
      3 *
          (-12754584 * centerDigit * resetDigit -
              460242 * centerDigit +
            387420489 * resetDigit ^ 2 +
              26020683 * resetDigit +
            434486) +
        2 by
          simp [weightedEscapeStateOneNumerator]
          ring]
  exact three_not_dvd_three_mul_add_two _

private theorem weightedEscapeStateTwoNumerator_unit
    (centerDigit resetDigit : ℤ) :
    IsUnit 3
      ((weightedEscapeStateTwoNumerator centerDigit resetDigit : ℤ) : ℚ) := by
  apply intCast_isUnit_of_not_dvd
  rw [show
    weightedEscapeStateTwoNumerator centerDigit resetDigit =
      3 *
          (752112309312 * centerDigit ^ 2 * resetDigit +
              27139550256 * centerDigit ^ 2 -
            43180338021984 * centerDigit * resetDigit ^ 2 -
              2887604199036 * centerDigit * resetDigit -
            47973032286 * centerDigit +
              617673396283947 * resetDigit ^ 3 +
            60300961208577 * resetDigit ^ 2 +
              1956441094806 * resetDigit +
            21101424883) +
        1 by
          simp [weightedEscapeStateTwoNumerator]
          ring]
  exact three_not_dvd_three_mul_add_one _

private theorem weightedEscape_reset_ready
    (centerDigit resetDigit : ℤ) :
    Ready (weightedEscapeParameters centerDigit resetDigit) 1
      ((6393 + 3 ^ 11 * resetDigit : ℤ) : ℚ) := by
  have resetUnit :
      IsUnit 3 (((59049 * resetDigit + 2131 : ℤ) : ℚ)) := by
    apply intCast_isUnit_of_not_dvd
    rw [show
      (59049 * resetDigit + 2131 : ℤ) =
        3 * (19683 * resetDigit + 710) + 1 by ring]
    exact three_not_dvd_three_mul_add_one _
  have state_value :
      HasValue 3
        (((6393 + 3 ^ 11 * resetDigit : ℤ) : ℚ)) 1 := by
    rw [show
      (((6393 + 3 ^ 11 * resetDigit : ℤ) : ℚ)) =
        (3 : ℚ) ^ 1 *
          ((59049 * resetDigit + 2131 : ℤ) : ℚ) by
            push_cast
            ring]
    simpa using mul_hasValue (primePower_hasValue 1) resetUnit
  have defect_value :
      HasValue 3
        (((6393 + 3 ^ 11 * resetDigit : ℤ) : ℚ) - 3) 2 := by
    rw [show
      (((6393 + 3 ^ 11 * resetDigit : ℤ) : ℚ) - 3) =
        (3 : ℚ) ^ 2 *
          ((weightedEscapeNumeratorOne resetDigit : ℤ) : ℚ) by
            push_cast
            simp [weightedEscapeNumeratorOne]
            ring]
    simpa using
      mul_hasValue (primePower_hasValue 2)
        (weightedEscapeNumeratorOne_unit resetDigit)
  exact ⟨by norm_num, state_value.2, defect_value.2⟩

private theorem weightedEscape_state_one_eq
    (centerDigit resetDigit : ℤ) :
    stateOfResidual (weightedEscapeParameters centerDigit resetDigit)
        (weightedEscapeResidualOne resetDigit) =
      (3 : ℚ) ^ 3 *
        ((weightedEscapeStateOneNumerator centerDigit resetDigit : ℤ) : ℚ) /
          ((weightedEscapeNumeratorOne resetDigit : ℤ) : ℚ) := by
  have numerator_ne :=
    (weightedEscapeNumeratorOne_unit resetDigit).1
  have denominator_ne :=
    (weightedEscapeDenominatorOne_unit resetDigit).1
  change
    (((998 + 3 ^ 8 * centerDigit : ℤ) : ℚ) +
        ((((6393 + 3 ^ 11 * resetDigit : ℤ) : ℚ) -
            ((998 + 3 ^ 8 * centerDigit : ℤ) : ℚ)) /
          ((((weightedEscapeNumeratorOne resetDigit : ℤ) : ℚ) /
            ((weightedEscapeDenominatorOne resetDigit : ℤ) : ℚ))))) =
      (3 : ℚ) ^ 3 *
        ((weightedEscapeStateOneNumerator centerDigit resetDigit : ℤ) : ℚ) /
          ((weightedEscapeNumeratorOne resetDigit : ℤ) : ℚ)
  field_simp [numerator_ne, denominator_ne]
  simp [weightedEscapeNumeratorOne, weightedEscapeDenominatorOne,
    weightedEscapeStateOneNumerator]
  ring

private theorem weightedEscape_state_one_ready
    (centerDigit resetDigit : ℤ) :
    Ready (weightedEscapeParameters centerDigit resetDigit) 3
      (stateOfResidual (weightedEscapeParameters centerDigit resetDigit)
        (weightedEscapeResidualOne resetDigit)) := by
  rw [weightedEscape_state_one_eq]
  have state_value :
      HasValue 3
        ((3 : ℚ) ^ 3 *
          ((weightedEscapeStateOneNumerator centerDigit resetDigit : ℤ) : ℚ) /
            ((weightedEscapeNumeratorOne resetDigit : ℤ) : ℚ)) 3 := by
    exact
      div_hasValue
        (mul_hasValue (primePower_hasValue 3)
          (weightedEscapeStateOneNumerator_unit centerDigit resetDigit))
        (weightedEscapeNumeratorOne_unit resetDigit)
  have defect_value :
      HasValue 3
        ((3 : ℚ) ^ 3 *
              ((weightedEscapeStateOneNumerator centerDigit resetDigit : ℤ) : ℚ) /
            ((weightedEscapeNumeratorOne resetDigit : ℤ) : ℚ) -
          3 ^ 3) 6 := by
    rw [show
      (3 : ℚ) ^ 3 *
              ((weightedEscapeStateOneNumerator centerDigit resetDigit : ℤ) : ℚ) /
            ((weightedEscapeNumeratorOne resetDigit : ℤ) : ℚ) -
          3 ^ 3 =
        (3 : ℚ) ^ 6 *
          ((weightedEscapeNumeratorTwo centerDigit resetDigit : ℤ) : ℚ) /
            ((weightedEscapeNumeratorOne resetDigit : ℤ) : ℚ) by
              field_simp [(weightedEscapeNumeratorOne_unit resetDigit).1]
              simp [weightedEscapeStateOneNumerator,
                weightedEscapeNumeratorOne, weightedEscapeNumeratorTwo]
              ring]
    exact
      div_hasValue
        (mul_hasValue (primePower_hasValue 6)
          (weightedEscapeNumeratorTwo_unit centerDigit resetDigit))
        (weightedEscapeNumeratorOne_unit resetDigit)
  exact ⟨by norm_num, state_value.2, defect_value.2⟩

private theorem weightedEscape_state_two_eq
    (centerDigit resetDigit : ℤ) :
    stateOfResidual (weightedEscapeParameters centerDigit resetDigit)
        (weightedEscapeResidualTwo centerDigit resetDigit) =
      (3 : ℚ) ^ 1 *
        ((weightedEscapeStateTwoNumerator centerDigit resetDigit : ℤ) : ℚ) /
          ((weightedEscapeNumeratorTwo centerDigit resetDigit : ℤ) : ℚ) := by
  have numerator_ne :=
    (weightedEscapeNumeratorTwo_unit centerDigit resetDigit).1
  have denominator_ne :=
    (weightedEscapeDenominatorTwo_unit centerDigit resetDigit).1
  change
    (((998 + 3 ^ 8 * centerDigit : ℤ) : ℚ) +
        ((((6393 + 3 ^ 11 * resetDigit : ℤ) : ℚ) -
            ((998 + 3 ^ 8 * centerDigit : ℤ) : ℚ)) /
          ((((weightedEscapeNumeratorTwo centerDigit resetDigit : ℤ) : ℚ) /
            ((weightedEscapeDenominatorTwo centerDigit resetDigit : ℤ) : ℚ))))) =
      (3 : ℚ) ^ 1 *
        ((weightedEscapeStateTwoNumerator centerDigit resetDigit : ℤ) : ℚ) /
          ((weightedEscapeNumeratorTwo centerDigit resetDigit : ℤ) : ℚ)
  field_simp [numerator_ne, denominator_ne]
  simp [weightedEscapeNumeratorTwo, weightedEscapeDenominatorTwo,
    weightedEscapeStateTwoNumerator]
  ring

private theorem weightedEscape_state_two_ready
    (centerDigit resetDigit : ℤ) :
    Ready (weightedEscapeParameters centerDigit resetDigit) 1
      (stateOfResidual (weightedEscapeParameters centerDigit resetDigit)
        (weightedEscapeResidualTwo centerDigit resetDigit)) := by
  rw [weightedEscape_state_two_eq]
  have state_value :
      HasValue 3
        ((3 : ℚ) ^ 1 *
          ((weightedEscapeStateTwoNumerator centerDigit resetDigit : ℤ) : ℚ) /
            ((weightedEscapeNumeratorTwo centerDigit resetDigit : ℤ) : ℚ)) 1 :=
    div_hasValue
      (mul_hasValue (primePower_hasValue 1)
        (weightedEscapeStateTwoNumerator_unit centerDigit resetDigit))
      (weightedEscapeNumeratorTwo_unit centerDigit resetDigit)
  have defect_value :
      HasValue 3
        ((3 : ℚ) ^ 1 *
              ((weightedEscapeStateTwoNumerator centerDigit resetDigit : ℤ) : ℚ) /
            ((weightedEscapeNumeratorTwo centerDigit resetDigit : ℤ) : ℚ) -
          3) 2 := by
    rw [show
      (3 : ℚ) ^ 1 *
              ((weightedEscapeStateTwoNumerator centerDigit resetDigit : ℤ) : ℚ) /
            ((weightedEscapeNumeratorTwo centerDigit resetDigit : ℤ) : ℚ) -
          3 =
        (3 : ℚ) ^ 2 *
          ((weightedEscapeNumeratorThree centerDigit resetDigit : ℤ) : ℚ) /
            ((weightedEscapeNumeratorTwo centerDigit resetDigit : ℤ) : ℚ) by
              field_simp [
                (weightedEscapeNumeratorTwo_unit centerDigit resetDigit).1]
              simp [weightedEscapeStateTwoNumerator,
                weightedEscapeNumeratorTwo, weightedEscapeNumeratorThree]
              ring]
    exact
      div_hasValue
        (mul_hasValue (primePower_hasValue 2)
          (weightedEscapeNumeratorThree_unit centerDigit resetDigit))
        (weightedEscapeNumeratorTwo_unit centerDigit resetDigit)
  exact ⟨by norm_num, state_value.2, defect_value.2⟩

private theorem clearedTransformDenominator_ne
    (parameters : Parameters) (numerator denominator : ℚ)
    (denominator_ne : denominator ≠ 0)
    (transform_denominator_ne :
      (parameters.center - 1) * (numerator / denominator) +
        drift parameters.center parameters.reset ≠ 0) :
    (parameters.center - 1) * numerator +
        drift parameters.center parameters.reset * denominator ≠ 0 := by
  rw [show
    (parameters.center - 1) * numerator +
          drift parameters.center parameters.reset * denominator =
        (((parameters.center - 1) * (numerator / denominator) +
            drift parameters.center parameters.reset) * denominator) by
      field_simp [denominator_ne]]
  exact mul_ne_zero transform_denominator_ne denominator_ne

private theorem weightedEscape_step_zero
    (centerDigit resetDigit : ℤ) :
    residualStep (weightedEscapeParameters centerDigit resetDigit) 1 1 =
      weightedEscapeResidualOne resetDigit := by
  have denominatorOne_ne :=
    (weightedEscapeDenominatorOne_unit resetDigit).1
  let parameters := weightedEscapeParameters centerDigit resetDigit
  have branch : ResidualBranch parameters 1 1 := by
    rw [residualBranch_iff_ready]
    simpa [parameters, weightedEscapeParameters, stateOfResidual_one] using
      weightedEscape_reset_ready centerDigit resetDigit
  have transform_denominator_ne :=
    (centerTransform_denominator_isUnit_of_branch parameters 1 1 branch).1
  have reset_sub_one_ne :
      (6393 + 177147 * (resetDigit : ℚ) - 1) ≠ 0 := by
    have reset_sub_one_eq :
        (6393 + 177147 * (resetDigit : ℚ) - 1) =
          ((weightedEscapeDenominatorOne resetDigit : ℤ) : ℚ) := by
      simp [weightedEscapeDenominatorOne]
      ring
    rw [reset_sub_one_eq]
    exact denominatorOne_ne
  rw [residualStep_eq parameters 1 1 transform_denominator_ne]
  unfold weightedEscapeResidualOne
  field_simp [transform_denominator_ne,
    denominatorOne_ne]
  simp [parameters, weightedEscapeParameters, drift,
    weightedEscapeNumeratorOne, weightedEscapeDenominatorOne]
  field_simp [reset_sub_one_ne]
  ring

private theorem weightedEscape_step_one
    (centerDigit resetDigit : ℤ) :
    residualStep (weightedEscapeParameters centerDigit resetDigit) 3
        (weightedEscapeResidualOne resetDigit) =
      weightedEscapeResidualTwo centerDigit resetDigit := by
  have numeratorOne_ne :=
    (weightedEscapeNumeratorOne_unit resetDigit).1
  have denominatorOne_ne :=
    (weightedEscapeDenominatorOne_unit resetDigit).1
  have numeratorTwo_ne :=
    (weightedEscapeNumeratorTwo_unit centerDigit resetDigit).1
  have denominatorTwo_ne :=
    (weightedEscapeDenominatorTwo_unit centerDigit resetDigit).1
  let parameters := weightedEscapeParameters centerDigit resetDigit
  let source := weightedEscapeResidualOne resetDigit
  have branch : ResidualBranch parameters 3 source := by
    rw [residualBranch_iff_ready]
    exact weightedEscape_state_one_ready centerDigit resetDigit
  have transform_denominator_ne :=
    (centerTransform_denominator_isUnit_of_branch parameters 3 source branch).1
  have cleared_denominator_ne :=
    clearedTransformDenominator_ne parameters
      ((weightedEscapeNumeratorOne resetDigit : ℤ) : ℚ)
      ((weightedEscapeDenominatorOne resetDigit : ℤ) : ℚ)
      denominatorOne_ne (by
        simpa [source, weightedEscapeResidualOne] using
          transform_denominator_ne)
  have expanded_denominator_ne :
      ((998 + 6561 * (centerDigit : ℚ) - 1) *
          (19683 * (resetDigit : ℚ) + 710) +
        (6393 + 177147 * (resetDigit : ℚ) -
            (998 + 6561 * (centerDigit : ℚ))) *
          (177147 * (resetDigit : ℚ) + 6392)) ≠ 0 := by
    simpa [parameters, weightedEscapeParameters, drift,
      weightedEscapeNumeratorOne, weightedEscapeDenominatorOne] using
        cleared_denominator_ne
  rw [residualStep_eq parameters 3 source transform_denominator_ne]
  dsimp only [source]
  unfold weightedEscapeResidualOne weightedEscapeResidualTwo
  field_simp [numeratorOne_ne, denominatorOne_ne,
    numeratorTwo_ne, denominatorTwo_ne, transform_denominator_ne]
  simp [parameters, weightedEscapeParameters, drift,
    weightedEscapeNumeratorOne, weightedEscapeDenominatorOne,
    weightedEscapeNumeratorTwo, weightedEscapeDenominatorTwo]
  field_simp [expanded_denominator_ne]
  ring

private theorem weightedEscape_step_two
    (centerDigit resetDigit : ℤ) :
    residualStep (weightedEscapeParameters centerDigit resetDigit) 1
        (weightedEscapeResidualTwo centerDigit resetDigit) =
      weightedEscapeResidualThree centerDigit resetDigit := by
  have numeratorTwo_ne :=
    (weightedEscapeNumeratorTwo_unit centerDigit resetDigit).1
  have denominatorTwo_ne :=
    (weightedEscapeDenominatorTwo_unit centerDigit resetDigit).1
  have numeratorThree_ne :=
    (weightedEscapeNumeratorThree_unit centerDigit resetDigit).1
  have denominatorThree_ne :=
    (weightedEscapeDenominatorThree_unit centerDigit resetDigit).1
  let parameters := weightedEscapeParameters centerDigit resetDigit
  let source := weightedEscapeResidualTwo centerDigit resetDigit
  have branch : ResidualBranch parameters 1 source := by
    rw [residualBranch_iff_ready]
    exact weightedEscape_state_two_ready centerDigit resetDigit
  have transform_denominator_ne :=
    (centerTransform_denominator_isUnit_of_branch parameters 1 source branch).1
  have cleared_denominator_ne :=
    clearedTransformDenominator_ne parameters
      ((weightedEscapeNumeratorTwo centerDigit resetDigit : ℤ) : ℚ)
      ((weightedEscapeDenominatorTwo centerDigit resetDigit : ℤ) : ℚ)
      denominatorTwo_ne (by
        simpa [source, weightedEscapeResidualTwo] using
          transform_denominator_ne)
  have expanded_denominator_ne :
      ((998 + 6561 * (centerDigit : ℚ) - 1) *
          (-(1417176 * (centerDigit : ℚ) * resetDigit) -
              51138 * centerDigit +
            43046721 * (resetDigit : ℚ) ^ 2 +
              2890458 * resetDigit +
            48250) +
        (6393 + 177147 * (resetDigit : ℚ) -
            (998 + 6561 * (centerDigit : ℚ))) *
          (-(1033121304 * (centerDigit : ℚ) * resetDigit) -
              37279602 * centerDigit +
            31381059609 * (resetDigit : ℚ) ^ 2 +
              2107655640 * resetDigit +
            35192710)) ≠ 0 := by
    simpa [parameters, weightedEscapeParameters, drift,
      weightedEscapeNumeratorTwo, weightedEscapeDenominatorTwo] using
        cleared_denominator_ne
  rw [residualStep_eq parameters 1 source transform_denominator_ne]
  dsimp only [source]
  unfold weightedEscapeResidualTwo weightedEscapeResidualThree
  field_simp [numeratorTwo_ne, denominatorTwo_ne,
    numeratorThree_ne, denominatorThree_ne, transform_denominator_ne]
  simp [parameters, weightedEscapeParameters, drift,
    weightedEscapeNumeratorTwo, weightedEscapeDenominatorTwo,
    weightedEscapeNumeratorThree, weightedEscapeDenominatorThree]
  field_simp [expanded_denominator_ne]
  ring

/-- Every integral point in the anisotropic parameter cylinder has wait prefix `1,3,1`. -/
theorem weightedEscape_threeStepPrefix
    (centerDigit resetDigit : ℤ) :
    DecodedStep (weightedEscapeParameters centerDigit resetDigit) 1
        (weightedEscapeResidualOne resetDigit) ∧
      DecodedStep (weightedEscapeParameters centerDigit resetDigit)
        (weightedEscapeResidualOne resetDigit)
        (weightedEscapeResidualTwo centerDigit resetDigit) ∧
      DecodedStep (weightedEscapeParameters centerDigit resetDigit)
        (weightedEscapeResidualTwo centerDigit resetDigit)
        (weightedEscapeResidualThree centerDigit resetDigit) := by
  constructor
  · refine ⟨1, ?_, weightedEscape_step_zero centerDigit resetDigit⟩
    rw [residualBranch_iff_ready]
    simpa [stateOfResidual_one, weightedEscapeParameters] using
      weightedEscape_reset_ready centerDigit resetDigit
  constructor
  · refine ⟨3, ?_, weightedEscape_step_one centerDigit resetDigit⟩
    rw [residualBranch_iff_ready]
    exact weightedEscape_state_one_ready centerDigit resetDigit
  · refine ⟨1, ?_, weightedEscape_step_two centerDigit resetDigit⟩
    rw [residualBranch_iff_ready]
    exact weightedEscape_state_two_ready centerDigit resetDigit

/-- The constant lattice point is the earlier reset-only escape witness. -/
theorem weightedEscape_zero_eq_resetEscape :
    weightedEscapeParameters 0 0 = resetEscapeParameters := by
  rfl

end
end MatrixMortality.ReturnGuard.Examples
