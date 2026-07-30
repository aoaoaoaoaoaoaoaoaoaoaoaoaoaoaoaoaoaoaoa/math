import MatrixMortality.ReturnGuardCancellationJet
import MatrixMortality.ReturnGuardTangent
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Fixed-support localization of the tangent cocycle

The canonical multiplicative normalization of the tangent recurrence is localization away from
the fixed parameter support.  In that localization the tangent transfer is invertible exactly
when its next cyclotomic factor is a unit.

This normalization does not produce a uniform finite core.  The guarded recurrence with
parameters `(p, s, A, D, L) = (5, 2, 29, 1, 1)` realizes every positive `3`-adic cancellation
depth, while localization away from its fixed support `5` retains the entire strict tower of
powers of `3`.
-/

namespace MatrixMortality.ReturnGuard

open scoped Matrix

noncomputable section

/-- A specialization which keeps the inverted element invertible detects nonunits in an away
localization. -/
theorem away_algebraMap_not_isUnit_of_map
    {R S P : Type*} [CommRing R] [CommRing S] [CommRing P]
    [Algebra R S] {inverted detected : R}
    [IsLocalization.Away inverted S]
    (specialization : R →+* P)
    (inverted_unit : IsUnit (specialization inverted))
    (detected_nonunit : ¬IsUnit (specialization detected)) :
    ¬IsUnit (algebraMap R S detected) := by
  intro detected_unit
  apply detected_nonunit
  simpa using
    detected_unit.map
      (IsLocalization.Away.lift (S := S) inverted inverted_unit)

/-- After localizing away from the fixed parameter product, the tangent transfer is invertible
exactly when its next cyclotomic factor is a unit. -/
theorem tangentTransfer_localized_isUnit_iff
    {S : Type*} [CommRing S] [Algebra ℤ S]
    (centerNumerator driftNumerator scale base : ℤ)
    [IsLocalization.Away (driftNumerator * scale * base) S]
    (depth priorWait nextWait : Nat) :
    IsUnit
        (tangentTransfer
          (algebraMap ℤ S centerNumerator)
          (algebraMap ℤ S driftNumerator)
          (algebraMap ℤ S scale)
          ((algebraMap ℤ S base) ^ (depth * priorWait))
          ((algebraMap ℤ S base) ^ nextWait)) ↔
      IsUnit (1 - (algebraMap ℤ S base) ^ nextWait) := by
  have fixed_product_unit :
      IsUnit
        (algebraMap ℤ S driftNumerator *
          algebraMap ℤ S scale * algebraMap ℤ S base) := by
    simpa only [map_mul] using
      (IsLocalization.Away.algebraMap_isUnit
        (S := S) (driftNumerator * scale * base))
  rw [IsUnit.mul_iff, IsUnit.mul_iff] at fixed_product_unit
  exact
    tangentTransfer_isUnit_iff_cyclotomic
      (algebraMap ℤ S centerNumerator)
      (algebraMap ℤ S driftNumerator)
      (algebraMap ℤ S scale)
      ((algebraMap ℤ S base) ^ (depth * priorWait))
      ((algebraMap ℤ S base) ^ nextWait)
      ((fixed_product_unit.1.1.mul fixed_product_unit.1.2).mul
        (fixed_product_unit.2.pow (depth * priorWait)))

/-- Three remains a nonunit after localizing the integers away from five. -/
theorem awayFive_three_not_isUnit :
    ¬IsUnit
      (algebraMap ℤ (Localization.Away (5 : ℤ)) (3 : ℤ)) := by
  let specialization : ℤ →+* ZMod 3 := Int.castRingHom (ZMod 3)
  apply
    away_algebraMap_not_isUnit_of_map
      (S := Localization.Away (5 : ℤ))
      (inverted := (5 : ℤ)) (detected := (3 : ℤ)) specialization
  · have five_unit : IsUnit ((5 : Nat) : ZMod 3) := by
      rw [ZMod.isUnit_iff_coprime]
      norm_num
    simpa [specialization] using five_unit
  · have three_zero : ((3 : Nat) : ZMod 3) = 0 :=
      (ZMod.natCast_zmod_eq_zero_iff_dvd 3 3).mpr (dvd_refl 3)
    rw [show specialization 3 = ((3 : Nat) : ZMod 3) by
      norm_num [specialization], three_zero]
    exact not_isUnit_zero

/-- Every positive power of three remains a nonunit after localizing away from five. -/
theorem awayFive_three_pow_not_isUnit
    (exponent : Nat) (exponent_positive : 0 < exponent) :
    ¬IsUnit
      (algebraMap ℤ (Localization.Away (5 : ℤ)) ((3 : ℤ) ^ exponent)) := by
  intro power_unit
  apply awayFive_three_not_isUnit
  rw [map_pow] at power_unit
  exact
    (isUnit_pow_iff (Nat.ne_of_gt exponent_positive)).mp power_unit

/-- Distinct powers of three remain nonassociated after localization away from five. -/
theorem awayFive_three_pow_not_associated_of_lt
    (lower upper : Nat) (exponent_lt : lower < upper) :
    ¬Associated
      (algebraMap ℤ (Localization.Away (5 : ℤ)) ((3 : ℤ) ^ lower))
      (algebraMap ℤ (Localization.Away (5 : ℤ)) ((3 : ℤ) ^ upper)) := by
  intro associated
  let modulus := 3 ^ (lower + 1)
  let specialization : ℤ →+* ZMod modulus :=
    Int.castRingHom (ZMod modulus)
  have five_unit : IsUnit (specialization 5) := by
    have five_unit' : IsUnit ((5 : Nat) : ZMod modulus) := by
      rw [ZMod.isUnit_iff_coprime]
      exact (by norm_num : Nat.Coprime 5 3).pow_right _
    simpa [specialization] using five_unit'
  let descend :
      Localization.Away (5 : ℤ) →+* ZMod modulus :=
    IsLocalization.Away.lift (5 : ℤ) five_unit
  have descended := associated.map descend
  have descend_three :
      descend
          (algebraMap ℤ (Localization.Away (5 : ℤ)) (3 : ℤ)) =
        ((3 : Nat) : ZMod modulus) := by
    simpa [descend, specialization] using
      (IsLocalization.Away.AwayMap.lift_eq
        (S := Localization.Away (5 : ℤ)) (x := (5 : ℤ))
        five_unit (3 : ℤ))
  have left_nonzero :
      ((3 : Nat) : ZMod modulus) ^ lower ≠ 0 := by
    intro cast_zero
    have power_dvd :
        modulus ∣ 3 ^ lower := by
      apply
        (ZMod.natCast_zmod_eq_zero_iff_dvd
          (3 ^ lower) modulus).mp
      simpa only [Nat.cast_pow] using cast_zero
    change 3 ^ (lower + 1) ∣ 3 ^ lower at power_dvd
    have impossible_le :
        3 ^ (lower + 1) ≤ 3 ^ lower :=
      Nat.le_of_dvd (by positivity) power_dvd
    rw [pow_succ] at impossible_le
    omega
  have right_zero :
      ((3 : Nat) : ZMod modulus) ^ upper = 0 := by
    have modulus_dvd : modulus ∣ 3 ^ upper := by
      exact pow_dvd_pow 3 (Nat.succ_le_iff.mpr exponent_lt)
    simpa only [Nat.cast_pow] using
      (ZMod.natCast_zmod_eq_zero_iff_dvd
        (3 ^ upper) modulus).mpr modulus_dvd
  have impossible :
      Associated
        (((3 : Nat) : ZMod modulus) ^ lower)
        (((3 : Nat) : ZMod modulus) ^ upper) := by
    simpa only [map_pow, descend_three] using descended
  exact left_nonzero (impossible.eq_zero_iff.mpr right_zero)

/-- Consecutive powers of three are the first strict step in the localized tower. -/
theorem awayFive_three_pow_not_associated_succ (exponent : Nat) :
    ¬Associated
      (algebraMap ℤ (Localization.Away (5 : ℤ)) ((3 : ℤ) ^ exponent))
      (algebraMap ℤ (Localization.Away (5 : ℤ)) ((3 : ℤ) ^ (exponent + 1))) :=
  awayFive_three_pow_not_associated_of_lt exponent (exponent + 1) (by omega)

/-- Fixed-support localization retains arbitrary novel cancellation depth in one guarded
recurrence. -/
theorem exists_localized_nonunit_three_cancellationDepth
    (cancellationDepth : Nat) (depth_positive : 0 < cancellationDepth) :
    ∃ wait : Nat,
      ∃ sourceDenominator reducedDenominator displacementUnit : ℤ,
        IntegralStep 5 2 29 1 1 wait 1 sourceDenominator
            ((3 : ℤ) ^ cancellationDepth * 3)
            ((3 : ℤ) ^ cancellationDepth * reducedDenominator) ∧
          IsCoprime (1 : ℤ) sourceDenominator ∧
          IsCoprime (3 : ℤ) reducedDenominator ∧
          1 * (1 - (5 : ℤ) ^ wait) * 1 =
            (3 : ℤ) ^ cancellationDepth * displacementUnit ∧
          ¬(3 : ℤ) ∣ displacementUnit ∧
          ProjectiveLine.ofPair
              ((3 : ℤ) : ZMod 3)
              (reducedDenominator : ZMod 3) =
            some 0 ∧
          ¬IsUnit
            (algebraMap ℤ (Localization.Away (5 : ℤ))
              ((3 : ℤ) ^ cancellationDepth)) := by
  obtain
    ⟨wait, sourceDenominator, reducedDenominator, displacementUnit,
      step, source_primitive, reduced_primitive, displacement,
      displacement_unit, exit⟩ :=
    exists_primitive_integralStep_with_three_cancellationDepth
      cancellationDepth depth_positive
  exact
    ⟨wait, sourceDenominator, reducedDenominator, displacementUnit,
      step, source_primitive, reduced_primitive, displacement,
      displacement_unit, exit,
      awayFive_three_pow_not_isUnit cancellationDepth depth_positive⟩

end
end MatrixMortality.ReturnGuard
