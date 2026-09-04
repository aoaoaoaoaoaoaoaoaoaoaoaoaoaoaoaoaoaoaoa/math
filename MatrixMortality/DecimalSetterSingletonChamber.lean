import MatrixMortality.DecimalSetterSingletonAncestry

/-!
# Positive singleton-tail chamber

Every physical singleton-pole recurrence has a positive current coefficient. Consequently,
the projective quotient of every lawful older parser history at such a pole is positive.
-/

namespace MatrixMortality.DecimalSetterBridgeRay

open MatrixMortality.DecimalSetterArithmetic
open MatrixMortality.DecimalSetterBridge
open MatrixMortality.DecimalSetterCarry
open MatrixMortality.DecimalSetterDepth
open MatrixMortality.DecimalSetterMatrix
open MatrixMortality.PadicValuation

/-- Either singleton trace dominates twice the calibrated lift times its decimal width. -/
theorem two_mul_tenPow_lift_le_singletonTrace
    {β : Nat} (β_large : 3 ≤ β) (targetLetter : TagLetter) :
    2 * (10 : ℚ) ^ β * lift ((10 : ℚ) ^ β) ≤ singletonTrace β targetLetter := by
  let ρ : ℚ := 10 ^ β
  let G := lift ρ
  have rho_bound : (1000 : ℚ) ≤ ρ := by
    have natural_bound : 10 ^ 3 ≤ 10 ^ β :=
      Nat.pow_le_pow_right (by norm_num) β_large
    norm_num at natural_bound ⊢
    simpa only [ρ] using (show (1000 : ℚ) ≤ (10 : ℚ) ^ β by
      exact_mod_cast natural_bound)
  have rho_pos : 0 < ρ := lt_of_lt_of_le (by norm_num) rho_bound
  have G_pos : 0 < G := by
    dsimp only [G]
    unfold lift
    linarith
  let traceB := 5200 * ρ ^ 2 - 18398 * ρ + 2443
  have traceB_ge_G : G ≤ traceB := by
    have square_growth : 1000 * ρ ≤ ρ ^ 2 := by nlinarith
    dsimp only [traceB, G]
    unfold lift
    nlinarith
  cases targetLetter with
  | c => simpa only [ρ, G] using (singletonCTrace_eq β).ge
  | b =>
      rw [show singletonTrace β .b = 2 * ρ * traceB by
        simpa only [ρ, traceB] using singletonBTrace_eq β]
      exact mul_le_mul_of_nonneg_left traceB_ge_G (by positivity)

/-- The singleton-pole recurrence has a positive current coefficient for every physical
erasure-ended current. This chamber cut is independent of the older parser tail. -/
theorem erasureEnded_singletonCoefficient_pos
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current : List NearyTile}
    (current_ends : EndsInErase current) :
    0 < boundaryTrace β body current * singletonTrace β targetLetter -
      7 * gap ((10 : ℚ) ^ β) * DecimalSetterMatrix.marker β *
        lift ((10 : ℚ) ^ β) * upperScale β current := by
  let ρ : ℚ := 10 ^ β
  let E := gap ρ
  let G := lift ρ
  let μ := DecimalSetterMatrix.marker β
  let P := upperBoundaryCode β current
  let V := lowerBoundaryCode β body current
  let A := upperScale β current
  let T := boundaryTrace β body current
  let S := singletonTrace β targetLetter
  let m := (spell (nearyUpper β) current).length
  have β_pos : 0 < β := by omega
  have rho_bound : (1000 : ℚ) ≤ ρ := by
    have natural_bound : 10 ^ 3 ≤ 10 ^ β :=
      Nat.pow_le_pow_right (by norm_num) β_large
    norm_num at natural_bound ⊢
    simpa only [ρ] using (show (1000 : ℚ) ≤ (10 : ℚ) ^ β by
      exact_mod_cast natural_bound)
  have rho_pos : 0 < ρ := lt_of_lt_of_le (by norm_num) rho_bound
  have E_pos : 0 < E := by
    dsimp only [E]
    unfold gap
    linarith
  have G_pos : 0 < G := by
    dsimp only [G]
    unfold lift
    linarith
  have V_ne : V ≠ 0 := by
    simpa only [V] using
      (lowerBoundaryCode_hasDecimalShell_of_endsInErase β body current_ends).1.1
  have V_nonneg : 0 ≤ V := by simp [V, lowerBoundaryCode]
  have V_pos : 0 < V := lt_of_le_of_ne V_nonneg (Ne.symm V_ne)
  have A_pos : 0 < A := by simp [A, upperScale]
  have S_lower : 2 * ρ * G ≤ S := by
    simpa only [ρ, G, S] using
      two_mul_tenPow_lift_le_singletonTrace β_large targetLetter
  have S_pos : 0 < S := lt_of_lt_of_le (by positivity) S_lower
  let upperWord := spell (nearyUpper β) current ++ nearyMarker β
  have upperWord_ne : upperWord ≠ [] := by simp [upperWord, nearyMarker]
  obtain ⟨first, tail, upperWord_eq⟩ := List.exists_cons_of_ne_nil upperWord_ne
  have upperWord_length : upperWord.length = m + β + 1 := by
    simp [upperWord, m, nearyMarker]
    omega
  have tail_length : tail.length = m + β := by
    simpa [upperWord_eq] using upperWord_length
  have P_lower_nat : 5 * 10 ^ (m + β) ≤ code upperWord := by
    rw [upperWord_eq]
    simpa only [tail_length] using five_mul_pow_length_le_code first tail
  have scale_power : (10 : ℚ) ^ (m + β) = A * ρ := by
    simp only [pow_add, A, upperScale, m, ρ]
  have P_lower : 5 * A * ρ ≤ P := by
    have cast_bound : 5 * 10 ^ (m + β) ≤ code upperWord := P_lower_nat
    have rational_bound :
        (5 * (10 : ℚ) ^ (m + β)) ≤ (code upperWord : ℚ) := by
      exact_mod_cast cast_bound
    rw [scale_power] at rational_bound
    simpa only [P, upperBoundaryCode, upperWord, mul_assoc] using rational_bound
  have marker_bound_nat : code (nearyMarker β) < 10 ^ (β + 1) :=
    code_lt_pow_length (nearyMarker β) |>.trans_eq (by simp [nearyMarker])
  have μ_upper : μ < 10 * ρ := by
    have rational_bound :
        (code (nearyMarker β) : ℚ) < (10 : ℚ) ^ (β + 1) := by
      exact_mod_cast marker_bound_nat
    rw [pow_succ] at rational_bound
    simpa only [μ, DecimalSetterMatrix.marker, ρ, mul_comm] using rational_bound
  have core_growth : 70 * ρ < 10 * ρ ^ 2 := by nlinarith
  have boundary_product : 7 * μ * G * A < P * S := by
    have lower_product : 10 * A * ρ ^ 2 * G ≤ P * S := by
      have P_nonneg : 0 ≤ P :=
        (show (0 : ℚ) ≤ 5 * A * ρ by positivity).trans P_lower
      calc
        10 * A * ρ ^ 2 * G = (5 * A * ρ) * (2 * ρ * G) := by ring
        _ ≤ P * S := mul_le_mul P_lower S_lower (by positivity) P_nonneg
    have upper_product : 7 * μ * G * A < 70 * ρ * G * A := by
      have marker_scaled : 7 * μ < 70 * ρ := by nlinarith
      have lift_scaled := mul_lt_mul_of_pos_right marker_scaled G_pos
      simpa only [mul_assoc] using mul_lt_mul_of_pos_right lift_scaled A_pos
    have growth_scaled : 70 * ρ * G * A < 10 * A * ρ ^ 2 * G := by
      nlinarith
    exact upper_product.trans (growth_scaled.trans_le lower_product)
  have trace_lower : E * P < T := by
    dsimp only [T]
    unfold boundaryTrace
    nlinarith
  have scaled_boundary : 7 * E * μ * G * A < E * P * S := by
    nlinarith
  have trace_scaled : E * P * S < T * S :=
    mul_lt_mul_of_pos_right trace_lower S_pos
  change 0 < T * S - 7 * E * μ * G * A
  linarith

/-- At every lawful singleton pole, the older parser ray lies in the positive-quotient
chamber. This cut applies to an arbitrary nonempty older history. -/
theorem singletonPole_olderRatio_pos
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current next : List NearyTile}
    {rest : List (List NearyTile)} (current_ends : EndsInErase current)
    (tail_law : BlocksLaw (next :: rest))
    (pole : HitsSquarePole β body [.erase targetLetter] (current :: next :: rest)) :
    0 < (parsedRay β body (next :: rest)).2 /
      (parsedRay β body (next :: rest)).1 := by
  have β_pos : 0 < β := by omega
  let ray := parsedRay β body (next :: rest)
  let x := ray.1
  let y := ray.2
  let ρ : ℚ := 10 ^ β
  let E := gap ρ
  let G := lift ρ
  let μ := DecimalSetterMatrix.marker β
  let T := boundaryTrace β body current
  let V := lowerBoundaryCode β body current
  let A := upperScale β current
  let S := singletonTrace β targetLetter
  have G_ne : G ≠ 0 := by
    simpa only [G, ρ] using (lift_tenPow_hasDecimalShell β_pos).1.1
  have V_ne : V ≠ 0 := by
    simpa only [V] using
      (lowerBoundaryCode_hasDecimalShell_of_endsInErase β body current_ends).1.1
  have S_ne : S ≠ 0 := by
    simpa only [S] using (singletonTrace_hasDecimalShell β_pos targetLetter).1.1
  have ray_ne : ray ≠ (0, 0) :=
    parsedRay_ne_zero_of_blocksLaw β_pos body tail_law
  have pole_equation :=
    (hitsSquarePole_singleton_cons_iff_rayRecurrence β_pos body targetLetter
      current next rest).mp pole
  change (T * x - G * V * y) * S = E * μ * G * A * x * 7 at pole_equation
  have x_ne : x ≠ 0 := by
    intro x_zero
    have product_zero : (-(G * V * y)) * S = 0 := by
      simpa only [x_zero, mul_zero, zero_mul, zero_sub] using pole_equation
    have residual_zero : -(G * V * y) = 0 :=
      (mul_eq_zero.mp product_zero).resolve_right S_ne
    have triple_zero : G * V * y = 0 := neg_eq_zero.mp residual_zero
    have y_zero : y = 0 := by
      rcases mul_eq_zero.mp triple_zero with scaled_zero | y_zero
      · rcases mul_eq_zero.mp scaled_zero with lift_zero | lower_zero
        · exact False.elim (G_ne lift_zero)
        · exact False.elim (V_ne lower_zero)
      · exact y_zero
    exact ray_ne (Prod.ext x_zero y_zero)
  have coefficient_pos : 0 < T * S - 7 * E * μ * G * A := by
    simpa only [T, S, E, μ, G, A, ρ] using
      erasureEnded_singletonCoefficient_pos β_large body targetLetter current_ends
  have core_equation :
      x * (T * S - 7 * E * μ * G * A) = G * V * S * y := by
    linear_combination pole_equation
  have quotient_eq : G * V * S * (y / x) = T * S - 7 * E * μ * G * A := by
    calc
      G * V * S * (y / x) = (G * V * S * y) / x := by ring
      _ = (x * (T * S - 7 * E * μ * G * A)) / x := by rw [core_equation]
      _ = T * S - 7 * E * μ * G * A := by field_simp [x_ne]
  have scaled_quotient_pos : 0 < G * V * S * (y / x) := by
    rw [quotient_eq]
    exact coefficient_pos
  have rho_bound : (1000 : ℚ) ≤ ρ := by
    have natural_bound : 10 ^ 3 ≤ 10 ^ β :=
      Nat.pow_le_pow_right (by norm_num) β_large
    norm_num at natural_bound ⊢
    simpa only [ρ] using (show (1000 : ℚ) ≤ (10 : ℚ) ^ β by
      exact_mod_cast natural_bound)
  have rho_pos : 0 < ρ := lt_of_lt_of_le (by norm_num) rho_bound
  have G_pos : 0 < G := by
    dsimp only [G]
    unfold lift
    linarith
  have V_nonneg : 0 ≤ V := by simp [V, lowerBoundaryCode]
  have V_pos : 0 < V := lt_of_le_of_ne V_nonneg (Ne.symm V_ne)
  have S_lower : 2 * ρ * G ≤ S := by
    simpa only [ρ, G, S] using
      two_mul_tenPow_lift_le_singletonTrace β_large targetLetter
  have S_pos : 0 < S := lt_of_lt_of_le (by positivity) S_lower
  have scale_pos : 0 < G * V * S := by positivity
  change 0 < y / x
  rcases (mul_pos_iff.mp scaled_quotient_pos) with ⟨_, quotient_pos⟩ | ⟨scale_neg, _⟩
  · exact quotient_pos
  · exact False.elim (not_lt_of_ge scale_pos.le scale_neg)

end MatrixMortality.DecimalSetterBridgeRay
