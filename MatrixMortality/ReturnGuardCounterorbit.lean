import MatrixMortality.ReturnGuardExamples

/-!
# Exact death of the order-breaking counterorbit candidate

The ready order-breaking bridge continues deterministically for three further wait-one steps and
then reaches a nonterminal 3-adic unit. Thus the bridge cannot seed an infinite moving-prime
genealogy.
-/

namespace MatrixMortality.ReturnGuard.Examples

open MatrixMortality.PadicValuation

noncomputable section

private theorem val3_scaled_fraction
    (power : Nat) (numerator denominator : ℤ)
    (numerator_ne : numerator ≠ 0) (denominator_ne : denominator ≠ 0)
    (numerator_unit : ¬(3 : ℤ) ∣ numerator)
    (denominator_unit : ¬(3 : ℤ) ∣ denominator) :
    padicValRat 3
        ((3 : ℚ) ^ power * (numerator : ℚ) / (denominator : ℚ)) =
      power := by
  have numerator_has_value : IsUnit 3 (numerator : ℚ) :=
    ⟨by exact_mod_cast numerator_ne, by
      rw [padicValRat.of_int]
      exact_mod_cast padicValInt.eq_zero_of_not_dvd numerator_unit⟩
  have denominator_has_value : IsUnit 3 (denominator : ℚ) :=
    ⟨by exact_mod_cast denominator_ne, by
      rw [padicValRat.of_int]
      exact_mod_cast padicValInt.eq_zero_of_not_dvd denominator_unit⟩
  exact
    (div_hasValue
      (mul_hasValue (primePower_hasValue power) numerator_has_value)
      denominator_has_value).2

private theorem third_step :
    guardedStep orderBreakerParameters 1 (some (67384284465 / 270178)) =
      some (1867323343063569 / 7487052659) := by
  rw [guardedStep_some orderBreakerParameters 1 (67384284465 / 270178)
    (by norm_num [orderBreakerParameters])]
  norm_num [orderBreakerParameters, guardDefect, drift]

private theorem third_target_ready :
    Ready orderBreakerParameters 1 (1867323343063569 / 7487052659) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [show (1867323343063569 / 7487052659 : ℚ) =
      (3 : ℚ) * 622441114354523 / 7487052659 by norm_num]
    exact val3_scaled_fraction 1 622441114354523 7487052659
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num only [orderBreakerParameters, Nat.cast_ofNat, pow_one]
    rw [show (1867300881905592 / 7487052659 : ℚ) =
      (3 : ℚ) ^ 2 * 207477875767288 / 7487052659 by norm_num]
    exact val3_scaled_fraction 2 207477875767288 7487052659
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem fourth_step :
    guardedStep orderBreakerParameters 1
        (some (1867323343063569 / 7487052659)) =
      some (25873217288233051767 / 103738937883644) := by
  rw [guardedStep_some orderBreakerParameters 1
    (1867323343063569 / 7487052659) (by norm_num [orderBreakerParameters])]
  norm_num [orderBreakerParameters, guardDefect, drift]

private theorem fourth_target_ready :
    Ready orderBreakerParameters 1
      (25873217288233051767 / 103738937883644) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [show (25873217288233051767 / 103738937883644 : ℚ) =
      (3 : ℚ) * 8624405762744350589 / 103738937883644 by norm_num]
    exact val3_scaled_fraction 1 8624405762744350589 103738937883644
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num only [orderBreakerParameters, Nat.cast_ofNat, pow_one]
    rw [show (25872906071419400835 / 103738937883644 : ℚ) =
      (3 : ℚ) ^ 2 * 2874767341268822315 / 103738937883644 by norm_num]
    exact val3_scaled_fraction 2 2874767341268822315 103738937883644
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem fifth_step :
    guardedStep orderBreakerParameters 1
        (some (25873217288233051767 / 103738937883644)) =
      some (716987098491311042884493 / 2874767341268822315) := by
  rw [guardedStep_some orderBreakerParameters 1
    (25873217288233051767 / 103738937883644)
    (by norm_num [orderBreakerParameters])]
  norm_num [orderBreakerParameters, guardDefect, drift]

private theorem fifth_target_unit :
    IsUnit 3 (716987098491311042884493 / 2874767341268822315 : ℚ) := by
  refine ⟨by norm_num, ?_⟩
  rw [show (716987098491311042884493 / 2874767341268822315 : ℚ) =
    (3 : ℚ) ^ 0 * 716987098491311042884493 / 2874767341268822315 by norm_num]
  exact val3_scaled_fraction 0 716987098491311042884493 2874767341268822315
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The proposed order-breaking counterorbit has the forced wait prefix `[4,1,1,1,1]` and then
reaches a nonterminal `3`-adic unit. It therefore enters the forward-invariant trap instead of
starting an infinite moving-prime genealogy. -/
theorem orderBreaker_candidate_enters_trap :
    Ready orderBreakerParameters 1 (67384284465 / 270178) ∧
      guardedStep orderBreakerParameters 1 (some (67384284465 / 270178)) =
        some (1867323343063569 / 7487052659) ∧
      Ready orderBreakerParameters 1 (1867323343063569 / 7487052659) ∧
      guardedStep orderBreakerParameters 1
          (some (1867323343063569 / 7487052659)) =
        some (25873217288233051767 / 103738937883644) ∧
      Ready orderBreakerParameters 1
        (25873217288233051767 / 103738937883644) ∧
      guardedStep orderBreakerParameters 1
          (some (25873217288233051767 / 103738937883644)) =
        some (716987098491311042884493 / 2874767341268822315) ∧
      Trap orderBreakerParameters
        (some (716987098491311042884493 / 2874767341268822315)) := by
  refine ⟨orderBreaker_shatters_resetBall.2.2.2.2.1, third_step,
    third_target_ready, fourth_step, fourth_target_ready, fifth_step, ?_⟩
  rw [trap_some_iff]
  exact ⟨by norm_num, fun positive => by
    have valuation :
        0 < padicValRat 3
          (716987098491311042884493 / 2874767341268822315 : ℚ) := by
      simpa only [orderBreakerParameters] using positive.2
    rw [fifth_target_unit.2] at valuation
    omega⟩

end
end MatrixMortality.ReturnGuard.Examples
