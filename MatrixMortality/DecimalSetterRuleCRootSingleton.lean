import MatrixMortality.DecimalSetterRootRay

/-!
# Decimal setter `R_c`-root singleton extinction

The two-block singleton classifier leaves a long multi-role current block over the canonical
`R_c` root. For target `D_c`, the exact root calibration turns its pole equation into

```text
2·10^β(P−V) = 7μ·10^m.
```

When `m≥β+3`, exact decimal suffix exhaustion factors `P−V` at depth
`m−β−1`. The remaining prefix has length `2β+2`, but the pole equation would give it code
`35μ`, strictly below the smallest lawful code of that length. Hence no parser-lawful two-block
source reaches the `D_c` singleton pole.
-/

namespace MatrixMortality.DecimalSetterBridgeRay

open MatrixMortality.DecimalSetterBridge
open MatrixMortality.DecimalSetterCarry
open MatrixMortality.DecimalSetterMatrix

/-- The singleton `D_c` trace is exactly twice the lifted decimal scale times `10^β`. -/
theorem singletonCTrace_eq (β : Nat) :
    singletonTrace β .c =
      2 * (10 : ℚ) ^ β * lift ((10 : ℚ) ^ β) := by
  have marker_eq : DecimalSetterMatrix.marker β =
      (52 * (10 : ℚ) ^ β - 7) / 9 := by
    have relation := DecimalSetterMatrix.marker_relation β
    linarith
  have upper_eq : upperBoundaryCode β [.erase .c] =
      5 * 10 ^ (β + 1) + DecimalSetterMatrix.marker β := by
    rw [upperBoundaryCode_eq]
    norm_num [spell, nearyUpper, tagCode, markerScale, code, digit]
  rw [singletonTrace, upper_eq, marker_eq, pow_succ]
  unfold gap lift
  ring

/-- Over the canonical `R_c` root, the physical `D_c` singleton pole equation is exactly the
upper/lower decimal code discrepancy equation. No parser or block law is needed for this
algebraic equivalence. -/
theorem hitsSquarePole_singletonC_ruleCRoot_iff_codeDiscrepancy
    {β : Nat} (β_pos : 0 < β) (body : List TagLetter)
    (current : List NearyTile) :
    HitsSquarePole β body [.erase .c]
        [current, DecimalSetterMinimumBody.ruleCRoot] ↔
      2 * (10 : ℚ) ^ β *
          (upperBoundaryCode β current - lowerBoundaryCode β body current) =
        7 * DecimalSetterMatrix.marker β * upperScale β current := by
  let ρ : ℚ := 10 ^ β
  let G := lift ρ
  let μ := DecimalSetterMatrix.marker β
  let P := upperBoundaryCode β current
  let V := lowerBoundaryCode β body current
  let A := upperScale β current
  have G_ne : G ≠ 0 := by exact (lift_tenPow_hasDecimalShell β_pos).1.1
  rw [hitsSquarePole_singleton_ruleCRoot_iff_traceDiscrepancy β_pos,
    singletonCTrace_eq]
  change 2 * ρ * G * (P - V) = 7 * μ * G * A ↔
    2 * ρ * (P - V) = 7 * μ * A
  constructor
  · intro equation
    apply mul_right_cancel₀ G_ne
    calc
      (2 * ρ * (P - V)) * G = 2 * ρ * G * (P - V) := by ring
      _ = 7 * μ * G * A := equation
      _ = (7 * μ * A) * G := by ring
  · intro equation
    calc
      2 * ρ * G * (P - V) = G * (2 * ρ * (P - V)) := by ring
      _ = G * (7 * μ * A) := by rw [equation]
      _ = 7 * μ * G * A := by ring

/-- No parser-lawful two-block source reaches the singleton `D_c` pole when `β≥3`.

The two-block classifier first fixes the root as `R_c` and the current upper length `m` at
`m≥β+3`. The resulting discrepancy has exact ten-adic depth `m−β−1`; suffix exhaustion then
forces a lawful prefix of length `2β+2` to have the impossible code `35μ`. -/
theorem singletonC_twoBlockSource_impossible
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    {current root : List NearyTile} (source_law : BlocksLaw [current, root]) :
    ¬HitsSquarePole β body [.erase .c] [current, root] := by
  intro pole
  obtain ⟨root_eq, _, current_long⟩ :=
    singletonPole_twoBlockSource_classifier β_large body .c source_law pole
  subst root
  let upperWord := spell (nearyUpper β) current ++ nearyMarker β
  let lowerWord := spell (nearyLower β body) current
  let m := (spell (nearyUpper β) current).length
  let μ := code (nearyMarker β)
  let P := code upperWord
  let V := code lowerWord
  have rational_equation :=
    (hitsSquarePole_singletonC_ruleCRoot_iff_codeDiscrepancy
      (by omega) body current).mp pole
  have rational_equation' :
      2 * (10 : ℚ) ^ β * ((P : ℚ) - V) =
        7 * (μ : ℚ) * (10 : ℚ) ^ m := by
    simpa only [upperBoundaryCode, lowerBoundaryCode, upperScale,
      upperWord, lowerWord, m, μ, P, V, DecimalSetterMatrix.marker] using rational_equation
  have μ_pos : 0 < μ := by
    exact code_pos_of_ne_nil (by simp [nearyMarker])
  have difference_pos_rat : (0 : ℚ) < (P : ℚ) - V := by
    have right_pos : (0 : ℚ) < 7 * (μ : ℚ) * (10 : ℚ) ^ m := by positivity
    have scale_pos : (0 : ℚ) < 2 * 10 ^ β := by positivity
    nlinarith [rational_equation']
  have difference_pos : V < P := by exact_mod_cast sub_pos.mp difference_pos_rat
  have difference_cast : (((P - V : Nat) : ℚ)) = (P : ℚ) - V := by
    rw [Nat.cast_sub difference_pos.le]
  have natural_equation :
      2 * 10 ^ β * (P - V) = 7 * μ * 10 ^ m := by
    have cast_equation :
        ((2 * 10 ^ β * (P - V) : Nat) : ℚ) =
          ((7 * μ * 10 ^ m : Nat) : ℚ) := by
      push_cast
      rw [difference_cast]
      exact rational_equation'
    exact_mod_cast cast_equation
  let width := m - β - 1
  have m_large : β + 3 ≤ m := by simpa only [m] using current_long
  have width_pos : 0 < width := by omega
  have m_eq : m = β + (width + 1) := by omega
  have difference_eq : P - V = 35 * μ * 10 ^ width := by
    have scaled :
        (2 * 10 ^ β) * (P - V) =
          (2 * 10 ^ β) * (35 * μ * 10 ^ width) := by
      calc
        (2 * 10 ^ β) * (P - V) = 7 * μ * 10 ^ m := natural_equation
        _ = (2 * 10 ^ β) * (35 * μ * 10 ^ width) := by
          rw [m_eq, pow_add, pow_succ]
          ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) scaled
  have ten_power_dvd : 10 ^ width ∣ P - V := by
    rw [difference_eq]
    exact dvd_mul_left _ _
  have μ_odd : μ % 2 = 1 := by
    exact code_odd_of_ne_nil (by simp [nearyMarker])
  have two_power_exact : ¬2 * 10 ^ width ∣ P - V := by
    intro forbidden
    rw [difference_eq] at forbidden
    obtain ⟨quotient, quotient_eq⟩ := forbidden
    have cancelled : 35 * μ = 2 * quotient := by
      apply Nat.mul_right_cancel (m := 10 ^ width) (by positivity)
      calc
        35 * μ * 10 ^ width = 2 * 10 ^ width * quotient := quotient_eq
        _ = 2 * quotient * 10 ^ width := by ring
    have product_mod : (35 * μ) % 2 = 1 := by omega
    rw [cancelled] at product_mod
    omega
  have upper_length : upperWord.length = m + β + 1 := by
    simp [upperWord, m, nearyMarker]
    omega
  have width_lt_upper : width < upperWord.length := by omega
  obtain ⟨_, _, difference_front⟩ :=
    suffix_exhaustion_factorization upperWord lowerWord width width_pos width_lt_upper
      difference_pos ten_power_dvd two_power_exact
  have front_code_eq : code (front width upperWord) = 35 * μ := by
    apply Nat.mul_right_cancel (m := 10 ^ width) (by positivity)
    rw [← difference_front, difference_eq]
  have front_length : (front width upperWord).length = 2 * β + 2 := by
    rw [length_front, upper_length]
    omega
  have front_ne : front width upperWord ≠ [] := by
    intro front_nil
    have length_eq := congrArg List.length front_nil
    simp [front_length] at length_eq
  obtain ⟨frontBit, frontTail, front_eq⟩ := List.exists_cons_of_ne_nil front_ne
  have frontTail_length : frontTail.length = 2 * β + 1 := by
    simpa [front_eq] using front_length
  have front_lower : 5 * 10 ^ (2 * β + 1) ≤ code (front width upperWord) := by
    rw [front_eq]
    simpa only [frontTail_length] using five_mul_pow_length_le_code frontBit frontTail
  have μ_upper : μ < 10 ^ (β + 1) := by
    have bound := code_lt_pow_length (nearyMarker β)
    simpa [μ, nearyMarker] using bound
  have power_lower : 1000 ≤ 10 ^ β := by
    have monotone := Nat.pow_le_pow_right (by norm_num : 0 < 10) β_large
    norm_num at monotone ⊢
    exact monotone
  have coefficient_bound : 35 < 5 * 10 ^ β := by omega
  have marker_bound : 35 * μ < 5 * 10 ^ (2 * β + 1) := by
    calc
      35 * μ < 35 * 10 ^ (β + 1) :=
        Nat.mul_lt_mul_of_pos_left μ_upper (by norm_num)
      _ < (5 * 10 ^ β) * 10 ^ (β + 1) :=
        Nat.mul_lt_mul_of_pos_right coefficient_bound (by positivity)
      _ = 5 * 10 ^ (2 * β + 1) := by
        rw [show 2 * β + 1 = β + (β + 1) by omega, pow_add]
        ring
  rw [front_code_eq] at front_lower
  omega

end MatrixMortality.DecimalSetterBridgeRay
