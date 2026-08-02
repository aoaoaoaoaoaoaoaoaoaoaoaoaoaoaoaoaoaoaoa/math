import MatrixMortality.ReturnGuardContinued

/-!
# Bounded-denominator endpoint dynamics

The primitive endpoint recurrence has one remaining elementary stratum: an infinite orbit with
uniformly bounded positive denominators.  This file extracts the exact denominator recurrence
and turns such a bound into explicit local wait and numerator ceilings.  The finite-orbit
consequence lives in `ReturnGuardFiniteOrbit`.
-/

namespace MatrixMortality.ReturnGuard

open MatrixMortality.PadicValuation

noncomputable section

/-- Uniform absolute bound for the divided error term in a denominator-bounded record
transition. -/
def denominatorErrorBound
    (centerNumerator driftNumerator scale : ℤ) (denominatorBound : Nat) : Nat :=
  denominatorBound *
    (centerNumerator.natAbs + (driftNumerator * scale).natAbs)

/-- One explicit base-power ceiling for the earlier wait in every nondecreasing bounded-
denominator transition. -/
def denominatorRecordPowerBound
    (centerNumerator driftNumerator scale : ℤ) (denominatorBound : Nat) : Nat :=
  let error :=
    denominatorErrorBound centerNumerator driftNumerator scale denominatorBound
  max
    (max
      (error * (1 + scale.natAbs * denominatorBound))
      (centerNumerator.natAbs +
        driftNumerator.natAbs * denominatorBound *
          (centerNumerator - scale).natAbs))
    (max error ((driftNumerator - scale).natAbs * denominatorBound))

/-- Uniform forward-content bound once the wait is bounded. -/
def endpointContentBound
    (prime waitBound : Nat) (driftNumerator scale : ℤ) : Nat :=
  (driftNumerator * scale).natAbs * prime ^ waitBound

/-- Uniform numerator bound for a primitive endpoint source with bounded wait and adjacent
denominators. -/
def endpointSourceNumeratorBound
    (prime depth waitBound denominatorBound : Nat)
    (driftNumerator scale : ℤ) : Nat :=
  prime ^ (depth * waitBound) *
      endpointContentBound prime waitBound driftNumerator scale * denominatorBound +
    scale.natAbs * prime ^ waitBound * denominatorBound

/-- Uniform numerator bound for the successor of a source already in the preceding box. -/
def endpointSuccessorNumeratorBound
    (prime depth waitBound denominatorBound : Nat)
    (centerNumerator driftNumerator scale : ℤ) : Nat :=
  driftNumerator.natAbs *
      endpointSourceNumeratorBound prime depth waitBound denominatorBound
        driftNumerator scale +
    (centerNumerator - scale).natAbs *
      endpointContentBound prime waitBound driftNumerator scale * denominatorBound

/-- Explicit ceiling for both waits in a nondecreasing bounded-denominator transition. -/
def denominatorRecordWaitBound
    (prime depth denominatorBound : Nat)
    (centerNumerator driftNumerator scale : ℤ) : Nat :=
  let earlier :=
    Nat.log prime
      (denominatorRecordPowerBound centerNumerator driftNumerator scale denominatorBound)
  max earlier <|
    Nat.log prime
      (endpointSuccessorNumeratorBound prime depth earlier denominatorBound
          centerNumerator driftNumerator scale +
        scale.natAbs * denominatorBound)

private theorem power_sub_one_natAbs_le
    {prime wait : Nat} (prime_positive : 0 < prime) :
    ((prime : ℤ) ^ wait - 1).natAbs ≤ prime ^ wait := by
  have one_le_power : (1 : ℤ) ≤ (prime : ℤ) ^ wait := by
    have power_positive : 0 < prime ^ wait := Nat.pow_pos prime_positive
    exact_mod_cast power_positive
  exact_mod_cast
    (show
      (((prime : ℤ) ^ wait - 1).natAbs : ℤ) ≤ (prime ^ wait : Nat) by
      rw [Int.natAbs_of_nonneg (sub_nonneg.mpr one_le_power)]
      simpa only [Nat.cast_pow] using
        (sub_le_self ((prime : ℤ) ^ wait) (by norm_num : (0 : ℤ) ≤ 1)))

/-- A complementary content cannot exceed its cyclotomic determinant support. -/
theorem complementaryContent_natAbs_le
    {prime wait : Nat} {driftNumerator scale content complement : ℤ}
    (prime_positive : 0 < prime) (content_ne : content ≠ 0)
    (complementary :
      content * complement =
        driftNumerator * scale * ((prime : ℤ) ^ wait - 1)) :
    complement.natAbs ≤
      (driftNumerator * scale).natAbs * prime ^ wait := by
  have content_abs_positive : 0 < content.natAbs := Int.natAbs_pos.mpr content_ne
  have support_abs := congrArg Int.natAbs complementary
  simp only [Int.natAbs_mul] at support_abs
  have complement_le_support :
      complement.natAbs ≤ content.natAbs * complement.natAbs :=
    Nat.le_mul_of_pos_left _ content_abs_positive
  calc
    complement.natAbs ≤ content.natAbs * complement.natAbs := complement_le_support
    _ = (driftNumerator * scale).natAbs *
          ((prime : ℤ) ^ wait - 1).natAbs := by
      simpa only [Int.natAbs_mul, mul_assoc] using support_abs
    _ ≤ (driftNumerator * scale).natAbs * prime ^ wait :=
      Nat.mul_le_mul_left _ (power_sub_one_natAbs_le prime_positive)

/-- Both signed contents obey the same determinant-support bound. -/
theorem forwardContent_natAbs_le
    {prime wait : Nat} {driftNumerator scale content complement : ℤ}
    (prime_gt_one : 1 < prime) (wait_positive : 0 < wait)
    (drift_ne : driftNumerator ≠ 0) (scale_ne : scale ≠ 0)
    (complementary :
      content * complement =
        driftNumerator * scale * ((prime : ℤ) ^ wait - 1)) :
    content.natAbs ≤ (driftNumerator * scale).natAbs * prime ^ wait := by
  have support_ne :
      driftNumerator * scale * ((prime : ℤ) ^ wait - 1) ≠ 0 := by
    have power_gt_one : 1 < prime ^ wait :=
      Nat.one_lt_pow wait_positive.ne' prime_gt_one
    have power_sub_ne : (prime : ℤ) ^ wait - 1 ≠ 0 := by
      have cast_gt : (1 : ℤ) < (prime : ℤ) ^ wait := by exact_mod_cast power_gt_one
      omega
    exact mul_ne_zero (mul_ne_zero drift_ne scale_ne) power_sub_ne
  have complement_ne : complement ≠ 0 := by
    intro complement_zero
    apply support_ne
    rw [← complementary, complement_zero, mul_zero]
  apply complementaryContent_natAbs_le (lt_trans Nat.zero_lt_one prime_gt_one) complement_ne
  simpa only [mul_comm] using complementary

/-- Two consecutive primitive endpoint reductions, with the first determinant split into
forward and reverse contents, obey one exact recurrence on their three denominators. -/
theorem PrimitiveEndpointReduction.denominator_recurrence
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait nextWait : Nat} {source middle target : ℤ × ℤ}
    {content nextContent complement : ℤ}
    (first :
      PrimitiveEndpointReduction prime depth centerNumerator driftNumerator scale
        wait source middle content)
    (second :
      PrimitiveEndpointReduction prime depth centerNumerator driftNumerator scale
        nextWait middle target nextContent)
    (complementary :
      content * complement =
        driftNumerator * scale * ((prime : ℤ) ^ wait - 1)) :
    (prime : ℤ) ^ (depth * nextWait) * nextContent * target.2 =
      (centerNumerator +
          driftNumerator * (prime : ℤ) ^ (depth * wait) -
          scale * (prime : ℤ) ^ nextWait) * middle.2 +
        complement * source.2 := by
  apply mul_left_cancel₀ first.content_ne
  have eliminated := first.twoStep_elimination second
  simp only [Prod.fst, Prod.snd] at eliminated ⊢
  rw [first.source_eq_power_mul_prequotient] at eliminated
  dsimp [endpointPrequotient] at eliminated
  calc
    content *
        ((prime : ℤ) ^ (depth * nextWait) * nextContent * target.2) =
        (prime : ℤ) ^ (depth * nextWait) * content * nextContent * target.2 := by
      ring
    _ = driftNumerator *
          ((prime : ℤ) ^ (depth * wait) * (content * middle.2) +
            scale * ((prime : ℤ) ^ wait - 1) * source.2) +
        (centerNumerator - scale * (prime : ℤ) ^ nextWait) *
          (content * middle.2) := by rw [eliminated]
    _ = content *
          ((centerNumerator +
              driftNumerator * (prime : ℤ) ^ (depth * wait) -
              scale * (prime : ℤ) ^ nextWait) * middle.2 +
            complement * source.2) := by
      calc
        _ = content *
              (centerNumerator +
                driftNumerator * (prime : ℤ) ^ (depth * wait) -
                scale * (prime : ℤ) ^ nextWait) * middle.2 +
            (driftNumerator * scale * ((prime : ℤ) ^ wait - 1)) *
              source.2 := by ring
        _ = content *
              (centerNumerator +
                driftNumerator * (prime : ℤ) ^ (depth * wait) -
                scale * (prime : ℤ) ^ nextWait) * middle.2 +
            (content * complement) * source.2 := by rw [complementary]
        _ = _ := by ring

/-- At a nondecreasing transition, remove the earlier base power from the exact denominator
recurrence.  The remaining two summands expose the gap valuation. -/
theorem PrimitiveEndpointReduction.denominator_growth_factorization
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait gap : Nat} {source middle target : ℤ × ℤ}
    {content nextContent complement : ℤ}
    (first :
      PrimitiveEndpointReduction prime depth centerNumerator driftNumerator scale
        wait source middle content)
    (second :
      PrimitiveEndpointReduction prime depth centerNumerator driftNumerator scale
        (wait + gap) middle target nextContent)
    (depth_positive : 0 < depth)
    (complementary :
      content * complement =
        driftNumerator * scale * ((prime : ℤ) ^ wait - 1)) :
    centerNumerator * middle.2 + complement * source.2 =
      (prime : ℤ) ^ wait *
        (scale * (prime : ℤ) ^ gap * middle.2 +
          (prime : ℤ) ^ ((depth - 1) * wait) *
            ((prime : ℤ) ^ (depth * gap) * nextContent * target.2 -
              driftNumerator * middle.2)) := by
  have recurrence := first.denominator_recurrence second complementary
  simp only [Prod.snd] at recurrence ⊢
  have depth_decomp : depth - 1 + 1 = depth := Nat.sub_add_cancel depth_positive
  have full_exponent :
      depth * (wait + gap) =
        wait + ((depth - 1) * wait + depth * gap) := by
    calc
      depth * (wait + gap) = depth * wait + depth * gap := by ring
      _ = (depth - 1 + 1) * wait + depth * gap := by rw [depth_decomp]
      _ = wait + ((depth - 1) * wait + depth * gap) := by ring
  have wait_exponent : depth * wait = wait + (depth - 1) * wait := by
    calc
      depth * wait = (depth - 1 + 1) * wait := by rw [depth_decomp]
      _ = wait + (depth - 1) * wait := by ring
  rw [full_exponent, pow_add, pow_add, wait_exponent, pow_add, pow_add] at recurrence
  linear_combination -recurrence

/-- Bounded reduced denominators bound the divided error term independently of both waits. -/
theorem PrimitiveEndpointReduction.denominator_growth_error_le
    {prime depth denominatorBound : Nat}
    {centerNumerator driftNumerator scale : ℤ}
    {wait gap : Nat} {source middle target : ℤ × ℤ}
    {content nextContent complement : ℤ}
    (prime_positive : 0 < prime) (depth_positive : 0 < depth)
    (source_denominator_le : source.2.natAbs ≤ denominatorBound)
    (middle_denominator_le : middle.2.natAbs ≤ denominatorBound)
    (first :
      PrimitiveEndpointReduction prime depth centerNumerator driftNumerator scale
        wait source middle content)
    (second :
      PrimitiveEndpointReduction prime depth centerNumerator driftNumerator scale
        (wait + gap) middle target nextContent)
    (complementary :
      content * complement =
        driftNumerator * scale * ((prime : ℤ) ^ wait - 1)) :
    (scale * (prime : ℤ) ^ gap * middle.2 +
        (prime : ℤ) ^ ((depth - 1) * wait) *
          ((prime : ℤ) ^ (depth * gap) * nextContent * target.2 -
            driftNumerator * middle.2)).natAbs ≤
      denominatorErrorBound centerNumerator driftNumerator scale denominatorBound := by
  let power := prime ^ wait
  let error :=
    scale * (prime : ℤ) ^ gap * middle.2 +
      (prime : ℤ) ^ ((depth - 1) * wait) *
        ((prime : ℤ) ^ (depth * gap) * nextContent * target.2 -
          driftNumerator * middle.2)
  have power_positive : 0 < power := Nat.pow_pos prime_positive
  have factorization :=
    first.denominator_growth_factorization second depth_positive complementary
  simp only [Prod.snd] at factorization
  have complement_le :
      complement.natAbs ≤ (driftNumerator * scale).natAbs * power :=
    complementaryContent_natAbs_le prime_positive first.content_ne complementary
  have numerator_le :
      (centerNumerator * middle.2 + complement * source.2).natAbs ≤
        power *
          denominatorErrorBound centerNumerator driftNumerator scale
            denominatorBound := by
    calc
      _ ≤ (centerNumerator * middle.2).natAbs +
          (complement * source.2).natAbs := Int.natAbs_add_le _ _
      _ = centerNumerator.natAbs * middle.2.natAbs +
          complement.natAbs * source.2.natAbs := by
        simp only [Int.natAbs_mul]
      _ ≤ centerNumerator.natAbs * denominatorBound +
          ((driftNumerator * scale).natAbs * power) * denominatorBound :=
        Nat.add_le_add
          (Nat.mul_le_mul_left _ middle_denominator_le)
          (Nat.mul_le_mul complement_le source_denominator_le)
      _ ≤ power * (centerNumerator.natAbs * denominatorBound) +
          power * ((driftNumerator * scale).natAbs * denominatorBound) := by
        apply Nat.add_le_add
        · exact Nat.le_mul_of_pos_left _ power_positive
        · ring_nf
          exact le_rfl
      _ = power *
          denominatorErrorBound centerNumerator driftNumerator scale
            denominatorBound := by
        simp only [denominatorErrorBound]
        ring
  have absolute := congrArg Int.natAbs factorization
  simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_ofNat] at absolute
  change error.natAbs ≤ _
  apply Nat.le_of_mul_le_mul_left _ power_positive
  rw [← absolute]
  exact numerator_le

/-- With bounded positive denominators, the earlier wait in any nondecreasing transition has
an explicit parameter-only ceiling.  This is the arithmetic core of bounded-denominator
periodicity. -/
theorem PrimitiveEndpointReduction.nonDecreasing_wait_le_log_recordBound
    {prime depth denominatorBound : Nat} [Fact prime.Prime]
    {centerNumerator driftNumerator scale : ℤ}
    {wait nextWait : Nat} {source middle target : ℤ × ℤ}
    {content nextContent complement : ℤ}
    (depth_two_le : 2 ≤ depth) (wait_le_next : wait ≤ nextWait)
    (source_denominator_positive : 0 < source.2)
    (middle_denominator_positive : 0 < middle.2)
    (target_denominator_positive : 0 < target.2)
    (source_denominator_le : source.2.natAbs ≤ denominatorBound)
    (middle_denominator_le : middle.2.natAbs ≤ denominatorBound)
    (drift_unit : ¬(prime : ℤ) ∣ driftNumerator)
    (scale_unit : ¬(prime : ℤ) ∣ scale)
    (center_sub_scale_unit : ¬(prime : ℤ) ∣ centerNumerator - scale)
    (middle_denominator_unit : ¬(prime : ℤ) ∣ middle.2)
    (first :
      PrimitiveEndpointReduction prime depth centerNumerator driftNumerator scale
        wait source middle content)
    (second :
      PrimitiveEndpointReduction prime depth centerNumerator driftNumerator scale
        nextWait middle target nextContent)
    (complementary :
      content * complement =
        driftNumerator * scale * ((prime : ℤ) ^ wait - 1)) :
    wait ≤ Nat.log prime
      (denominatorRecordPowerBound centerNumerator driftNumerator scale
        denominatorBound) := by
  obtain ⟨gap, rfl⟩ := Nat.exists_eq_add_of_le wait_le_next
  let errorBound :=
    denominatorErrorBound centerNumerator driftNumerator scale denominatorBound
  let recordBound :=
    denominatorRecordPowerBound centerNumerator driftNumerator scale denominatorBound
  let exponent := (depth - 1) * wait
  let quotient := nextContent * target.2
  let bracket :=
    (prime : ℤ) ^ (depth * gap) * quotient - driftNumerator * middle.2
  let error :=
    scale * (prime : ℤ) ^ gap * middle.2 +
      (prime : ℤ) ^ exponent * bracket
  have prime_gt_one : 1 < prime := (Fact.out : prime.Prime).one_lt
  have prime_positive : 0 < prime := lt_trans Nat.zero_lt_one prime_gt_one
  have depth_positive : 0 < depth := lt_of_lt_of_le (by decide) depth_two_le
  have exponent_wait : wait ≤ exponent := by
    dsimp [exponent]
    apply Nat.le_mul_of_pos_left
    omega
  have quotient_ne : quotient ≠ 0 := by
    exact mul_ne_zero second.content_ne (ne_of_gt target_denominator_positive)
  have scale_middle_unit : ¬(prime : ℤ) ∣ scale * middle.2 := by
    exact
      (Nat.prime_iff_prime_int.mp (Fact.out : prime.Prime)).not_dvd_mul
        scale_unit middle_denominator_unit
  have drift_middle_unit : ¬(prime : ℤ) ∣ driftNumerator * middle.2 := by
    exact
      (Nat.prime_iff_prime_int.mp (Fact.out : prime.Prime)).not_dvd_mul
        drift_unit middle_denominator_unit
  have error_le : error.natAbs ≤ errorBound := by
    simpa only [error, exponent, quotient, bracket, errorBound, mul_assoc] using
      first.denominator_growth_error_le prime_positive depth_positive
        source_denominator_le middle_denominator_le second complementary
  have factorization :=
    first.denominator_growth_factorization second depth_positive complementary
  simp only [Prod.snd] at factorization
  have factorization' :
      centerNumerator * middle.2 + complement * source.2 =
        (prime : ℤ) ^ wait * error := by
    simpa only [error, exponent, quotient, bracket, mul_assoc] using factorization
  by_cases shallow : gap < exponent
  · have exponent_split : exponent = gap + (exponent - gap) := by omega
    let core :=
      scale * middle.2 + (prime : ℤ) ^ (exponent - gap) * bracket
    have error_eq : error = (prime : ℤ) ^ gap * core := by
      have power_split :
          (prime : ℤ) ^ exponent =
            (prime : ℤ) ^ gap * (prime : ℤ) ^ (exponent - gap) := by
        calc
          (prime : ℤ) ^ exponent =
              (prime : ℤ) ^ (gap + (exponent - gap)) :=
            congrArg (fun power : Nat => (prime : ℤ) ^ power) exponent_split
          _ = _ := pow_add _ _ _
      dsimp [error, core]
      rw [power_split]
      ring
    have exponent_remainder_positive : 0 < exponent - gap := by omega
    have prime_dvd_remainder :
        (prime : ℤ) ∣ (prime : ℤ) ^ (exponent - gap) * bracket :=
      dvd_mul_of_dvd_left
        (dvd_pow_self (prime : ℤ) (ne_of_gt exponent_remainder_positive)) _
    have core_unit : ¬(prime : ℤ) ∣ core := by
      intro prime_dvd_core
      have prime_dvd_scale_middle : (prime : ℤ) ∣ scale * middle.2 := by
        have difference := dvd_sub prime_dvd_core prime_dvd_remainder
        convert difference using 1
        all_goals
          dsimp [core]
          ring
      exact scale_middle_unit prime_dvd_scale_middle
    have core_ne : core ≠ 0 := fun core_zero =>
      core_unit (core_zero ▸ dvd_zero (prime : ℤ))
    have error_ne : error ≠ 0 := by
      rw [error_eq]
      exact mul_ne_zero
        (pow_ne_zero _ (by exact_mod_cast (Fact.out : prime.Prime).ne_zero)) core_ne
    have gap_power_dvd : (prime : ℤ) ^ gap ∣ error := by
      rw [error_eq]
      exact dvd_mul_right _ _
    have gap_power_le_error : prime ^ gap ≤ error.natAbs := by
      simpa only [Int.natAbs_pow, Int.natAbs_ofNat] using
        Int.natAbs_le_of_dvd_ne_zero gap_power_dvd error_ne
    have gap_power_le_bound : prime ^ gap ≤ errorBound :=
      gap_power_le_error.trans error_le
    by_cases bracket_zero : bracket = 0
    · have gap_zero : gap = 0 := by
        by_contra gap_ne
        have prime_dvd_left :
            (prime : ℤ) ∣ (prime : ℤ) ^ (depth * gap) * quotient := by
          apply dvd_mul_of_dvd_left
          apply dvd_pow_self
          exact Nat.mul_ne_zero depth_positive.ne' gap_ne
        have bracket_equation :
            (prime : ℤ) ^ (depth * gap) * quotient =
              driftNumerator * middle.2 := by
          dsimp [bracket] at bracket_zero
          linarith
        have prime_dvd_drift_middle :
            (prime : ℤ) ∣ driftNumerator * middle.2 := by
          rw [← bracket_equation]
          exact prime_dvd_left
        exact drift_middle_unit prime_dvd_drift_middle
      subst gap
      have quotient_eq : quotient = driftNumerator * middle.2 := by
        dsimp [bracket] at bracket_zero
        simp only [mul_zero, pow_zero, one_mul] at bracket_zero
        linarith
      have middle_isUnit : IsUnit middle.2 := by
        apply second.prequotient_coprime_denominator.symm.isUnit_of_dvd
        refine ⟨driftNumerator, ?_⟩
        simpa only [quotient, mul_comm] using quotient_eq
      have middle_eq_one : middle.2 = 1 := by
        rcases Int.isUnit_iff.mp middle_isUnit with middle_one | middle_neg_one
        · exact middle_one
        · omega
      have linear_relation :
          scale * (prime : ℤ) ^ wait - centerNumerator =
            complement * source.2 := by
        have zero_error : error = scale * middle.2 := by
          dsimp [error]
          rw [bracket_zero]
          ring
        rw [middle_eq_one] at factorization' zero_error
        simp only [mul_one] at factorization' zero_error
        rw [zero_error] at factorization'
        linarith
      have complement_dvd_support :
          complement ∣
            driftNumerator * scale * ((prime : ℤ) ^ wait - 1) := by
        rw [← complementary]
        exact dvd_mul_left _ _
      have divisor :
          scale * (prime : ℤ) ^ wait - centerNumerator ∣
            driftNumerator * source.2 * (centerNumerator - scale) := by
        obtain ⟨factor, factor_eq⟩ := complement_dvd_support
        refine ⟨factor - driftNumerator * source.2, ?_⟩
        rw [linear_relation]
        linear_combination
          source.2 * factor_eq - driftNumerator * source.2 * linear_relation
      have linear_abs_le :
          (scale * (prime : ℤ) ^ wait - centerNumerator).natAbs ≤
            driftNumerator.natAbs * denominatorBound *
              (centerNumerator - scale).natAbs := by
        calc
          _ ≤ (driftNumerator * source.2 *
                (centerNumerator - scale)).natAbs :=
            Int.natAbs_le_of_dvd_ne_zero divisor
              (mul_ne_zero
                (mul_ne_zero
                  (fun drift_zero => drift_unit
                    (drift_zero ▸ dvd_zero (prime : ℤ)))
                  (ne_of_gt source_denominator_positive))
                (fun difference_zero => center_sub_scale_unit
                  (difference_zero ▸ dvd_zero (prime : ℤ))))
          _ = driftNumerator.natAbs * source.2.natAbs *
                (centerNumerator - scale).natAbs := by
            simp only [Int.natAbs_mul]
          _ ≤ driftNumerator.natAbs * denominatorBound *
                (centerNumerator - scale).natAbs := by gcongr
      have wait_power_le :
          prime ^ wait ≤ centerNumerator.natAbs +
            driftNumerator.natAbs * denominatorBound *
              (centerNumerator - scale).natAbs := by
        have scale_abs_positive : 0 < scale.natAbs :=
          Int.natAbs_pos.mpr fun scale_zero =>
            scale_unit (scale_zero ▸ dvd_zero (prime : ℤ))
        calc
          prime ^ wait ≤ scale.natAbs * prime ^ wait :=
            Nat.le_mul_of_pos_left _ scale_abs_positive
          _ = (scale * (prime : ℤ) ^ wait).natAbs := by
            simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_ofNat]
          _ ≤ (scale * (prime : ℤ) ^ wait - centerNumerator).natAbs +
                centerNumerator.natAbs := by
            have triangle :=
              Int.natAbs_add_le centerNumerator
                (scale * (prime : ℤ) ^ wait - centerNumerator)
            convert triangle using 1 <;> ring
          _ ≤ _ := by
            simpa only [add_comm] using
              Nat.add_le_add_right linear_abs_le centerNumerator.natAbs
      apply Nat.le_log_of_pow_le prime_gt_one
      exact wait_power_le.trans <|
        le_trans (le_max_right _ _)
          (le_max_left _ _)
    · have bracket_abs_positive : 0 < bracket.natAbs :=
        Int.natAbs_pos.mpr bracket_zero
      have powered_bracket_le :
          prime ^ exponent ≤ error.natAbs +
            scale.natAbs * prime ^ gap * middle.2.natAbs := by
        have product_le :
            ((prime : ℤ) ^ exponent * bracket).natAbs ≤
              error.natAbs +
                (scale * (prime : ℤ) ^ gap * middle.2).natAbs := by
          have := Int.natAbs_sub_le error
            (scale * (prime : ℤ) ^ gap * middle.2)
          convert this using 1
          all_goals
            dsimp [error]
            ring
        calc
          prime ^ exponent ≤ prime ^ exponent * bracket.natAbs :=
            Nat.le_mul_of_pos_right _ bracket_abs_positive
          _ = ((prime : ℤ) ^ exponent * bracket).natAbs := by
            simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_ofNat]
          _ ≤ _ := by
            simpa only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_ofNat,
              mul_assoc] using product_le
      have powered_bracket_bound :
          prime ^ exponent ≤ errorBound *
            (1 + scale.natAbs * denominatorBound) := by
        calc
          prime ^ exponent ≤ error.natAbs +
              scale.natAbs * prime ^ gap * middle.2.natAbs :=
            powered_bracket_le
          _ ≤ errorBound +
              scale.natAbs * errorBound * denominatorBound := by
            exact Nat.add_le_add error_le
              (Nat.mul_le_mul
                (Nat.mul_le_mul_left scale.natAbs gap_power_le_bound)
                middle_denominator_le)
          _ = errorBound * (1 + scale.natAbs * denominatorBound) := by ring
      apply Nat.le_log_of_pow_le prime_gt_one
      exact (Nat.pow_le_pow_right prime_positive exponent_wait).trans
        (powered_bracket_bound.trans <|
          le_trans (le_max_left _ _) (le_max_left _ _))
  · have exponent_le_gap : exponent ≤ gap := Nat.le_of_not_gt shallow
    have exponent_split : gap = exponent + (gap - exponent) := by omega
    let core :=
      scale * (prime : ℤ) ^ (gap - exponent) * middle.2 + bracket
    have error_eq : error = (prime : ℤ) ^ exponent * core := by
      have power_split :
          (prime : ℤ) ^ gap =
            (prime : ℤ) ^ exponent * (prime : ℤ) ^ (gap - exponent) := by
        calc
          (prime : ℤ) ^ gap =
              (prime : ℤ) ^ (exponent + (gap - exponent)) :=
            congrArg (fun power : Nat => (prime : ℤ) ^ power) exponent_split
          _ = _ := pow_add _ _ _
      dsimp [error, core]
      rw [power_split]
      ring
    by_cases error_zero : error = 0
    · have core_zero : core = 0 := by
        rw [error_eq] at error_zero
        exact (mul_eq_zero.mp error_zero).resolve_left
          (pow_ne_zero _ (by exact_mod_cast (Fact.out : prime.Prime).ne_zero))
      have gap_eq : gap = exponent := by
        by_contra gap_ne
        have exponent_lt_gap : exponent < gap :=
          lt_of_le_of_ne exponent_le_gap (Ne.symm gap_ne)
        have prime_dvd_scaled :
            (prime : ℤ) ∣
              scale * (prime : ℤ) ^ (gap - exponent) * middle.2 := by
          apply dvd_mul_of_dvd_left
          apply dvd_mul_of_dvd_right
          apply dvd_pow_self
          omega
        have prime_dvd_bracket : (prime : ℤ) ∣ bracket := by
          have bracket_eq :
              bracket =
                -(scale * (prime : ℤ) ^ (gap - exponent) * middle.2) := by
            dsimp [core] at core_zero
            linarith
          rw [bracket_eq]
          exact dvd_neg.mpr prime_dvd_scaled
        have prime_dvd_drift_middle :
            (prime : ℤ) ∣ driftNumerator * middle.2 := by
          have prime_dvd_powered_quotient :
              (prime : ℤ) ∣ (prime : ℤ) ^ (depth * gap) * quotient := by
            apply dvd_mul_of_dvd_left
            apply dvd_pow_self
            have exponent_positive : 0 < exponent :=
              first.wait_positive.trans_le exponent_wait
            exact Nat.mul_ne_zero depth_positive.ne'
              (ne_of_gt (exponent_positive.trans exponent_lt_gap))
          have difference := dvd_sub prime_dvd_powered_quotient prime_dvd_bracket
          convert difference using 1
          all_goals
            dsimp [bracket]
            ring
        exact drift_middle_unit prime_dvd_drift_middle
      have difference_equation :
          (driftNumerator - scale) * middle.2 =
            (prime : ℤ) ^ (depth * gap) * quotient := by
        have expanded := core_zero
        dsimp [core, bracket] at expanded
        rw [gap_eq] at expanded
        simp only [Nat.sub_self, pow_zero, one_mul] at expanded
        rw [gap_eq]
        linear_combination -expanded
      have right_ne :
          (driftNumerator - scale) * middle.2 ≠ 0 := by
        rw [difference_equation]
        exact mul_ne_zero
          (pow_ne_zero _ (by exact_mod_cast (Fact.out : prime.Prime).ne_zero)) quotient_ne
      have power_dvd_difference_product :
          (prime : ℤ) ^ (depth * gap) ∣
            (driftNumerator - scale) * middle.2 := by
        rw [difference_equation]
        exact dvd_mul_right _ _
      have power_le_difference :
          prime ^ (depth * gap) ≤
            (driftNumerator - scale).natAbs * denominatorBound := by
        calc
          prime ^ (depth * gap) ≤
              ((driftNumerator - scale) * middle.2).natAbs := by
            simpa only [Int.natAbs_pow, Int.natAbs_ofNat] using
              Int.natAbs_le_of_dvd_ne_zero power_dvd_difference_product right_ne
          _ = (driftNumerator - scale).natAbs * middle.2.natAbs := by
            simp only [Int.natAbs_mul]
          _ ≤ _ := Nat.mul_le_mul_left _ middle_denominator_le
      apply Nat.le_log_of_pow_le prime_gt_one
      have wait_le_power_exponent : wait ≤ depth * gap :=
        exponent_wait.trans <| gap_eq ▸
          Nat.le_mul_of_pos_left exponent depth_positive
      refine (Nat.pow_le_pow_right prime_positive wait_le_power_exponent).trans ?_
      refine power_le_difference.trans ?_
      dsimp [recordBound, denominatorRecordPowerBound, errorBound]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    · have exponent_power_dvd : (prime : ℤ) ^ exponent ∣ error := by
        rw [error_eq]
        exact dvd_mul_right _ _
      have exponent_power_le : prime ^ exponent ≤ errorBound := by
        calc
          prime ^ exponent ≤ error.natAbs := by
            simpa only [Int.natAbs_pow, Int.natAbs_ofNat] using
              Int.natAbs_le_of_dvd_ne_zero exponent_power_dvd error_zero
          _ ≤ errorBound := error_le
      apply Nat.le_log_of_pow_le prime_gt_one
      refine (Nat.pow_le_pow_right prime_positive exponent_wait).trans ?_
      refine exponent_power_le.trans ?_
      dsimp [recordBound, denominatorRecordPowerBound, errorBound]
      exact le_trans (le_max_left _ _) (le_max_right _ _)

/-- A bounded source pair forces its outgoing wait into a logarithmic interval. -/
theorem PrimitiveEndpointReduction.wait_le_log_sourceBox
    {prime depth numeratorBound denominatorBound : Nat}
    {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {source target : ℤ × ℤ} {content : ℤ}
    (prime_gt_one : 1 < prime) (depth_two_le : 2 ≤ depth)
    (source_numerator_le : source.1.natAbs ≤ numeratorBound)
    (source_denominator_le : source.2.natAbs ≤ denominatorBound)
    (target_denominator_positive : 0 < target.2)
    (reduction :
      PrimitiveEndpointReduction prime depth centerNumerator driftNumerator scale
        wait source target content) :
    wait ≤ Nat.log prime (numeratorBound + scale.natAbs * denominatorBound) := by
  let waitPower := prime ^ wait
  let coefficient := numeratorBound + scale.natAbs * denominatorBound
  have prime_positive : 0 < prime := lt_trans Nat.zero_lt_one prime_gt_one
  have waitPower_positive : 0 < waitPower := Nat.pow_pos prime_positive
  have content_abs_positive : 0 < content.natAbs :=
    Int.natAbs_pos.mpr reduction.content_ne
  have target_abs_positive : 0 < target.2.natAbs :=
    Int.natAbs_pos.mpr (ne_of_gt target_denominator_positive)
  have raw_absolute := congrArg Int.natAbs reduction.step.denominator
  simp only [Prod.snd, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_ofNat] at raw_absolute
  have full_power_le_raw :
      prime ^ (depth * wait) ≤
        (source.1 - scale * ((prime : ℤ) ^ wait - 1) * source.2).natAbs := by
    calc
      prime ^ (depth * wait) ≤
          prime ^ (depth * wait) * (content.natAbs * target.2.natAbs) := by
        have one_le_product : 1 ≤ content.natAbs * target.2.natAbs :=
          Nat.one_le_iff_ne_zero.mpr <|
            mul_ne_zero content_abs_positive.ne' target_abs_positive.ne'
        exact Nat.le_mul_of_pos_right _ one_le_product
      _ = _ := raw_absolute
  have raw_le :
      (source.1 - scale * ((prime : ℤ) ^ wait - 1) * source.2).natAbs ≤
        waitPower * coefficient := by
    calc
      _ ≤ source.1.natAbs +
          (scale * ((prime : ℤ) ^ wait - 1) * source.2).natAbs :=
        Int.natAbs_sub_le _ _
      _ = source.1.natAbs +
          scale.natAbs * ((prime : ℤ) ^ wait - 1).natAbs * source.2.natAbs := by
        simp only [Int.natAbs_mul]
      _ ≤ numeratorBound +
          scale.natAbs * waitPower * denominatorBound :=
        Nat.add_le_add source_numerator_le <|
          Nat.mul_le_mul
            (Nat.mul_le_mul_left scale.natAbs <|
              power_sub_one_natAbs_le prime_positive)
            source_denominator_le
      _ ≤ waitPower * numeratorBound +
          waitPower * (scale.natAbs * denominatorBound) := by
        apply Nat.add_le_add
        · exact Nat.le_mul_of_pos_left _ waitPower_positive
        · ring_nf
          exact le_rfl
      _ = waitPower * coefficient := by
        dsimp [coefficient]
        ring
  have remaining_power_le :
      prime ^ ((depth - 1) * wait) ≤ coefficient := by
    have exponent_decomp :
        depth * wait = wait + (depth - 1) * wait := by
      have depth_positive : 0 < depth := lt_of_lt_of_le (by decide) depth_two_le
      have depth_decomp : depth - 1 + 1 = depth := Nat.sub_add_cancel depth_positive
      calc
        depth * wait = (depth - 1 + 1) * wait := by rw [depth_decomp]
        _ = wait + (depth - 1) * wait := by ring
    apply Nat.le_of_mul_le_mul_left _ waitPower_positive
    rw [← pow_add, ← exponent_decomp]
    exact full_power_le_raw.trans (raw_le)
  apply Nat.le_log_of_pow_le prime_gt_one
  exact (Nat.pow_le_pow_right prime_positive <| by
    apply Nat.le_mul_of_pos_left
    omega).trans remaining_power_le

/-- Bounded wait and adjacent denominators place the primitive source numerator in an explicit
box. -/
theorem PrimitiveEndpointReduction.source_numerator_le_box
    {prime depth waitBound denominatorBound : Nat}
    {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {source target : ℤ × ℤ} {content complement : ℤ}
    (prime_gt_one : 1 < prime) (wait_le : wait ≤ waitBound)
    (source_denominator_le : source.2.natAbs ≤ denominatorBound)
    (target_denominator_le : target.2.natAbs ≤ denominatorBound)
    (drift_ne : driftNumerator ≠ 0) (scale_ne : scale ≠ 0)
    (reduction :
      PrimitiveEndpointReduction prime depth centerNumerator driftNumerator scale
        wait source target content)
    (complementary :
      content * complement =
        driftNumerator * scale * ((prime : ℤ) ^ wait - 1)) :
    source.1.natAbs ≤
      endpointSourceNumeratorBound prime depth waitBound denominatorBound
        driftNumerator scale := by
  have prime_positive : 0 < prime := lt_trans Nat.zero_lt_one prime_gt_one
  have wait_power_le : prime ^ wait ≤ prime ^ waitBound :=
    Nat.pow_le_pow_right prime_positive wait_le
  have depth_wait_le : depth * wait ≤ depth * waitBound :=
    Nat.mul_le_mul_left depth wait_le
  have full_power_le : prime ^ (depth * wait) ≤ prime ^ (depth * waitBound) :=
    Nat.pow_le_pow_right prime_positive depth_wait_le
  have content_le :
      content.natAbs ≤ endpointContentBound prime waitBound driftNumerator scale := by
    refine (forwardContent_natAbs_le prime_gt_one reduction.wait_positive
      drift_ne scale_ne complementary).trans ?_
    dsimp [endpointContentBound]
    exact Nat.mul_le_mul_left _ wait_power_le
  rw [reduction.source_eq_power_mul_prequotient]
  dsimp [endpointPrequotient]
  calc
    ((prime : ℤ) ^ (depth * wait) * (content * target.2) +
          scale * ((prime : ℤ) ^ wait - 1) * source.2).natAbs ≤
        ((prime : ℤ) ^ (depth * wait) * (content * target.2)).natAbs +
          (scale * ((prime : ℤ) ^ wait - 1) * source.2).natAbs :=
      Int.natAbs_add_le _ _
    _ = prime ^ (depth * wait) * content.natAbs * target.2.natAbs +
          scale.natAbs * ((prime : ℤ) ^ wait - 1).natAbs * source.2.natAbs := by
      simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_ofNat, mul_assoc]
    _ ≤ prime ^ (depth * waitBound) *
            endpointContentBound prime waitBound driftNumerator scale *
              denominatorBound +
          scale.natAbs * prime ^ waitBound * denominatorBound := by
      apply Nat.add_le_add
      · exact Nat.mul_le_mul (Nat.mul_le_mul full_power_le content_le)
          target_denominator_le
      · exact Nat.mul_le_mul
          (Nat.mul_le_mul_left scale.natAbs <|
            (power_sub_one_natAbs_le prime_positive).trans wait_power_le)
          source_denominator_le
    _ = endpointSourceNumeratorBound prime depth waitBound denominatorBound
          driftNumerator scale := rfl

/-- The same box controls the successor numerator without dividing by its signed content. -/
theorem PrimitiveEndpointReduction.target_numerator_le_box
    {prime depth waitBound denominatorBound : Nat}
    {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {source target : ℤ × ℤ} {content complement : ℤ}
    (prime_gt_one : 1 < prime) (wait_le : wait ≤ waitBound)
    (source_denominator_le : source.2.natAbs ≤ denominatorBound)
    (target_denominator_le : target.2.natAbs ≤ denominatorBound)
    (drift_ne : driftNumerator ≠ 0) (scale_ne : scale ≠ 0)
    (reduction :
      PrimitiveEndpointReduction prime depth centerNumerator driftNumerator scale
        wait source target content)
    (complementary :
      content * complement =
        driftNumerator * scale * ((prime : ℤ) ^ wait - 1)) :
    target.1.natAbs ≤
      endpointSuccessorNumeratorBound prime depth waitBound denominatorBound
        centerNumerator driftNumerator scale := by
  have source_le := reduction.source_numerator_le_box prime_gt_one wait_le
    source_denominator_le target_denominator_le drift_ne scale_ne complementary
  have content_le :
      content.natAbs ≤ endpointContentBound prime waitBound driftNumerator scale := by
    refine (forwardContent_natAbs_le prime_gt_one reduction.wait_positive
      drift_ne scale_ne complementary).trans ?_
    dsimp [endpointContentBound]
    exact Nat.mul_le_mul_left _ <|
      Nat.pow_le_pow_right (lt_trans Nat.zero_lt_one prime_gt_one) wait_le
  have target_content_absolute := congrArg Int.natAbs reduction.target_eq_drift_add_prequotient
  dsimp [endpointPrequotient] at target_content_absolute
  simp only [Int.natAbs_mul] at target_content_absolute
  have content_abs_positive : 0 < content.natAbs :=
    Int.natAbs_pos.mpr reduction.content_ne
  calc
    target.1.natAbs ≤ content.natAbs * target.1.natAbs :=
      Nat.le_mul_of_pos_left _ content_abs_positive
    _ = (driftNumerator * source.1 +
          (centerNumerator - scale) * (content * target.2)).natAbs :=
      target_content_absolute
    _ ≤ (driftNumerator * source.1).natAbs +
          ((centerNumerator - scale) * (content * target.2)).natAbs :=
      Int.natAbs_add_le _ _
    _ = driftNumerator.natAbs * source.1.natAbs +
          (centerNumerator - scale).natAbs * content.natAbs * target.2.natAbs := by
      simp only [Int.natAbs_mul, mul_assoc]
    _ ≤ driftNumerator.natAbs *
            endpointSourceNumeratorBound prime depth waitBound denominatorBound
              driftNumerator scale +
          (centerNumerator - scale).natAbs *
            endpointContentBound prime waitBound driftNumerator scale * denominatorBound := by
      exact Nat.add_le_add (Nat.mul_le_mul_left _ source_le)
        (Nat.mul_le_mul
          (Nat.mul_le_mul_left (centerNumerator - scale).natAbs content_le)
          target_denominator_le)
    _ = endpointSuccessorNumeratorBound prime depth waitBound denominatorBound
          centerNumerator driftNumerator scale := rfl

/-- Both waits in a nondecreasing transition lie below one explicit computable ceiling. -/
theorem PrimitiveEndpointReduction.nonDecreasing_waits_le
    {prime depth denominatorBound : Nat} [Fact prime.Prime]
    {centerNumerator driftNumerator scale : ℤ}
    {wait nextWait : Nat} {source middle target : ℤ × ℤ}
    {content nextContent complement : ℤ}
    (depth_two_le : 2 ≤ depth) (wait_le_next : wait ≤ nextWait)
    (source_denominator_positive : 0 < source.2)
    (middle_denominator_positive : 0 < middle.2)
    (target_denominator_positive : 0 < target.2)
    (source_denominator_le : source.2.natAbs ≤ denominatorBound)
    (middle_denominator_le : middle.2.natAbs ≤ denominatorBound)
    (drift_unit : ¬(prime : ℤ) ∣ driftNumerator)
    (scale_unit : ¬(prime : ℤ) ∣ scale)
    (center_sub_scale_unit : ¬(prime : ℤ) ∣ centerNumerator - scale)
    (middle_denominator_unit : ¬(prime : ℤ) ∣ middle.2)
    (first :
      PrimitiveEndpointReduction prime depth centerNumerator driftNumerator scale
        wait source middle content)
    (second :
      PrimitiveEndpointReduction prime depth centerNumerator driftNumerator scale
        nextWait middle target nextContent)
    (complementary :
      content * complement =
        driftNumerator * scale * ((prime : ℤ) ^ wait - 1)) :
    wait ≤ denominatorRecordWaitBound prime depth denominatorBound
        centerNumerator driftNumerator scale ∧
      nextWait ≤ denominatorRecordWaitBound prime depth denominatorBound
        centerNumerator driftNumerator scale := by
  let earlier :=
    Nat.log prime
      (denominatorRecordPowerBound centerNumerator driftNumerator scale denominatorBound)
  let successorBound :=
    endpointSuccessorNumeratorBound prime depth earlier denominatorBound
      centerNumerator driftNumerator scale
  have prime_gt_one : 1 < prime := (Fact.out : prime.Prime).one_lt
  have drift_ne : driftNumerator ≠ 0 := fun drift_zero =>
    drift_unit (drift_zero ▸ dvd_zero (prime : ℤ))
  have scale_ne : scale ≠ 0 := fun scale_zero =>
    scale_unit (scale_zero ▸ dvd_zero (prime : ℤ))
  have wait_le_earlier : wait ≤ earlier := by
    simpa only [earlier] using
      first.nonDecreasing_wait_le_log_recordBound depth_two_le wait_le_next
        source_denominator_positive middle_denominator_positive
        target_denominator_positive source_denominator_le middle_denominator_le
        drift_unit scale_unit center_sub_scale_unit middle_denominator_unit second
        complementary
  have middle_numerator_le : middle.1.natAbs ≤ successorBound := by
    simpa only [successorBound] using
      first.target_numerator_le_box prime_gt_one wait_le_earlier
        source_denominator_le middle_denominator_le drift_ne scale_ne complementary
  have next_wait_le :
      nextWait ≤ Nat.log prime (successorBound + scale.natAbs * denominatorBound) :=
    second.wait_le_log_sourceBox prime_gt_one depth_two_le middle_numerator_le
      middle_denominator_le target_denominator_positive
  constructor
  · exact wait_le_earlier.trans <| by
      dsimp [denominatorRecordWaitBound, earlier]
      exact le_max_left _ _
  · exact next_wait_le.trans <| by
      dsimp [denominatorRecordWaitBound, successorBound, earlier]
      exact le_max_right _ _

end
end MatrixMortality.ReturnGuard
