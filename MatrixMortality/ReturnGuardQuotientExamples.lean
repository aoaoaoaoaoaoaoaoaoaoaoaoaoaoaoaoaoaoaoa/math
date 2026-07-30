import MatrixMortality.ReturnGuardExamples
import MatrixMortality.ReturnGuardIntegralLift

/-!
# Exact finite quotient certificates for guard examples

The rational period-three guard admits a four-state certificate modulo `11`.  Since `3` has
exact order five modulo `11`, every possible future wait reduces to one of five transitions.
All five transitions send each reachable ray into `{1, 4, 6, 10}`; neither annihilation nor the
terminal ray `0` occurs.
-/

namespace MatrixMortality.ReturnGuard.Examples

noncomputable section

private theorem eleven_prime : Nat.Prime 11 := by norm_num

private instance factPrimeEleven : Fact (Nat.Prime 11) :=
  ⟨eleven_prime⟩

/-- Eleven is a primitive divisor of `3⁵ - 1`. -/
theorem eleven_primitive_three_five :
    IsPrimitivePrimeDivisor 11 3 5 := by
  simp only [IsPrimitivePrimeDivisor]
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  intro earlier earlier_positive earlier_lt
  interval_cases earlier <;> norm_num

/-- Four affine rays contain every finite-quotient continuation of the cycle reset. -/
def cycleElevenInvariant :
    Set (QuotientState (ZMod 11)) :=
  {some (some (1 : ZMod 11)), some (some (4 : ZMod 11)),
    some (some (6 : ZMod 11)), some (some (10 : ZMod 11))}

/-- First-column numerators of the five quotient transfers. -/
def cycleElevenTop : Fin 5 → ZMod 11 :=
  ![8, 5, 7, 2, 9]

/-- First-column denominators of the five quotient transfers. -/
def cycleElevenBottom : Fin 5 → ZMod 11 :=
  ![8, 6, 10, 2, 7]

/-- Projective images of the five quotient transfers. -/
def cycleElevenImage : Fin 5 → ZMod 11 :=
  ![1, 10, 4, 1, 6]

/-- Modulo eleven, every residue transfer has rank one and zero second column. -/
theorem cycleElevenTransfer_eq_firstColumn (residue : Fin 5) :
    quotientTransfer 11 3 2 (-953) 473 2240 residue =
      !![cycleElevenTop residue, 0;
         cycleElevenBottom residue, 0] := by
  fin_cases residue <;> decide

/-- Every quotient first column is nonzero. -/
theorem cycleElevenColumn_ne_zero (residue : Fin 5) :
    ![cycleElevenTop residue, cycleElevenBottom residue] ≠ 0 := by
  fin_cases residue <;> decide

/-- The five first columns represent the displayed invariant rays. -/
theorem cycleElevenColumn_point (residue : Fin 5) :
    ProjectiveLine.ofPair (cycleElevenTop residue) (cycleElevenBottom residue) =
      some (cycleElevenImage residue) := by
  have two_ne : (2 : ZMod 11) ≠ 0 := by decide
  have six_ne : (6 : ZMod 11) ≠ 0 := by decide
  have seven_ne : (7 : ZMod 11) ≠ 0 := by decide
  have eight_ne : (8 : ZMod 11) ≠ 0 := by decide
  have ten_ne : (10 : ZMod 11) ≠ 0 := by decide
  fin_cases residue <;>
    simp [cycleElevenTop, cycleElevenBottom, cycleElevenImage,
      ProjectiveLine.ofPair, two_ne, six_ne, seven_ne, eight_ne, ten_ne] <;>
    field_simp <;>
    decide

/-- The four-ray set is invariant under all five exact-order wait residues. -/
theorem cycleElevenInvariant_closed :
    QuotientInvariant 11 3 5 2 (-953) 473 2240 cycleElevenInvariant := by
  intro state state_mem residue
  simp only [cycleElevenInvariant, Set.mem_insert_iff,
    Set.mem_singleton_iff] at state_mem ⊢
  rcases state_mem with rfl | rfl | rfl | rfl
  all_goals
    rw [cycleElevenTransfer_eq_firstColumn]
    rw [quotientTransition_firstColumn _ _ _
      (cycleElevenColumn_ne_zero residue) (by decide)]
    rw [cycleElevenColumn_point]
    fin_cases residue <;>
      simp [cycleElevenImage]

/-- The annihilation state is absent from the certificate. -/
theorem cycleElevenInvariant_cancelled_absent :
    (none : QuotientState (ZMod 11)) ∉ cycleElevenInvariant := by
  simp [cycleElevenInvariant]

/-- The decoded reset pair represents ray one modulo eleven. -/
theorem cycleElevenInvariant_reset_mem :
    quotientPairState 11 ((1 : ℤ), (1 : ℤ)) ∈ cycleElevenInvariant := by
  simp [quotientPairState, quotientPoint, ProjectiveLine.ofPair,
    cycleElevenInvariant]

/-- The terminal residual pair represents ray zero modulo eleven and is excluded. -/
theorem cycleElevenInvariant_terminal_absent :
    quotientPairState 11 ((-473 : ℤ), (-3193 : ℤ)) ∉
      cycleElevenInvariant := by
  have numerator_zero : ((-473 : ℤ) : ZMod 11) = 0 := by decide
  have denominator_eq : ((-3193 : ℤ) : ZMod 11) = 8 := by decide
  rw [quotientPairState, quotientPoint, numerator_zero, denominator_eq]
  simp [ProjectiveLine.ofPair, cycleElevenInvariant]
  decide

/-- The canonical reduced coordinates of the terminal residual are also excluded. -/
theorem cycleElevenInvariant_canonicalTerminal_absent :
    quotientPairState 11
        (rationalPair (terminalResidual cycleParameters)) ∉
      cycleElevenInvariant := by
  have terminal_point :
      quotientPoint 11
          (rationalPair (terminalResidual cycleParameters)).1
          (rationalPair (terminalResidual cycleParameters)).2 =
        some 0 := by
    rw [quotientPoint_rationalPair_eq_integral
      (value := terminalResidual cycleParameters)
      (numerator := -473) (denominator := -3193)
      (by norm_num)
      (by rw [cycle_terminalResidual]; norm_num)
      (by decide)]
    have numerator_zero : ((-473 : ℤ) : ZMod 11) = 0 := by decide
    have denominator_eq : ((-3193 : ℤ) : ZMod 11) = 8 := by decide
    have eight_ne : (8 : ZMod 11) ≠ 0 := by decide
    rw [numerator_zero, denominator_eq]
    simp [ProjectiveLine.ofPair, eight_ne]
  rw [quotientPairState, terminal_point]
  simp [cycleElevenInvariant]
  decide

/-- The exact-order quotient certificate alone blocks the entire decoded rational orbit. -/
theorem cycle_not_decodedReachable_by_quotient :
    ¬DecodedReachable cycleParameters := by
  apply not_decodedReachable_of_quotientInvariant cycleParameters
    (centerNumerator := -953) (driftNumerator := 473) (scale := 2240)
    (by norm_num [cycleParameters])
    (by norm_num [cycleParameters, drift])
    (by norm_num)
    eleven_primitive_three_five cycleElevenInvariant_closed
    cycleElevenInvariant_cancelled_absent
  · simpa [rationalPair] using cycleElevenInvariant_reset_mem
  · exact cycleElevenInvariant_canonicalTerminal_absent

/-- The finite four-ray quotient is by itself a kernel-checked physical immortality
certificate. -/
theorem cycle_not_physical_isMortal_by_quotient :
    ¬IsMortal
      (ReturnFamily.pairGenerator
        (ambient (cycleParameters.prime : ℚ) cycleParameters.depth)
        (cut cycleParameters.center cycleParameters.reset)) := by
  apply not_physical_isMortal_of_drift_divisor cycleParameters
    (centerNumerator := -953) (driftNumerator := 473) (scale := 2240)
    (by norm_num [cycleParameters])
    (by norm_num [cycleParameters, drift])
    (by norm_num)
    eleven_primitive_three_five (by decide) (by decide)
  intro residue
  fin_cases residue <;> decide

/-- No primitively reduced integral guard execution connects the period-three reset residual
to its terminal residual.  The certificate quantifies over every wait sequence, not only the
displayed three-cycle. -/
theorem cycle_no_primitive_integral_terminal_execution :
    ¬∃ steps,
      Relation.ReachesIn
        (PrimitiveIntegralStep 3 2 (-953) 473 2240)
        steps ((1 : ℤ), (1 : ℤ)) ((-473 : ℤ), (-3193 : ℤ)) :=
  no_primitiveExecution_of_drift_divisor
    eleven_primitive_three_five (-953) 473 2240
    (by decide) (by decide) (by
      intro residue
      fin_cases residue <;> decide)

end
end MatrixMortality.ReturnGuard.Examples
