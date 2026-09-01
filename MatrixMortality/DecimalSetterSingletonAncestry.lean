import MatrixMortality.DecimalSetterTwoBlockSingleton

/-!
# Exact singleton-tail ancestry

Every parser-lawful ray is nonzero. At an actual singleton pole, solving the current-block
recurrence backward shows that a long multi-role current makes the older quotient a decimal
`(1,1)` shell: its trace has shell `(1,1)`, while the pole correction lies strictly deeper.
The intrinsic quotient criterion then supplies decimal-unit peeled coordinates.

Combined with the existing forward length wall, unit peeled ancestry is equivalent to the
physical current shape `length≥2` and `upperLength≥β+3`. It is therefore no longer an
independent hypothesis on the long arbitrary-history singleton branch.
-/

namespace MatrixMortality.DecimalSetterBridgeRay

open MatrixMortality.DecimalSetterArithmetic
open MatrixMortality.DecimalSetterBridge
open MatrixMortality.DecimalSetterCarry
open MatrixMortality.DecimalSetterDepth
open MatrixMortality.DecimalSetterMatrix
open MatrixMortality.PadicValuation

/-- The homogeneous ray of every parser-lawful block history is nonzero.

At a recursive step, a nonzero first coordinate makes the new second coordinate nonzero. If the
first coordinate vanishes, parser law makes the lower code nonzero and the new first coordinate
nonzero instead. -/
theorem parsedRay_ne_zero_of_blocksLaw
    {β : Nat} (β_pos : 0 < β) (body : List TagLetter)
    {blocks : List (List NearyTile)} (law : BlocksLaw blocks) :
    parsedRay β body blocks ≠ (0, 0) := by
  induction blocks with
  | nil => exact False.elim law
  | cons block tail induction =>
      cases tail with
      | nil =>
          have first_ne := (rootRay_fst_hasDecimalShell β_pos block).1.1
          intro ray_zero
          apply first_ne
          simpa only [parsedRay] using congrArg Prod.fst ray_zero
      | cons next rest =>
          have tail_law : BlocksLaw (next :: rest) := law.2
          have tail_ne := induction tail_law
          let ray := parsedRay β body (next :: rest)
          have gap_ne := (gap_tenPow_hasDecimalShell β_pos).1.1
          have marker_ne := (marker_hasDecimalShell β_pos).1.1
          have lift_ne := (lift_tenPow_hasDecimalShell β_pos).1.1
          have lower_ne :=
            (lowerBoundaryCode_hasDecimalShell_of_endsInErase β body law.1).1.1
          by_cases first_zero : ray.1 = 0
          · have second_ne : ray.2 ≠ 0 := by
              intro second_zero
              apply tail_ne
              exact Prod.ext first_zero second_zero
            have new_first_ne : (rayStep β body block ray).1 ≠ 0 := by
              simp only [rayStep, first_zero, mul_zero, zero_sub]
              exact div_ne_zero
                (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero lift_ne lower_ne) second_ne))
                (mul_ne_zero gap_ne marker_ne)
            intro ray_zero
            apply new_first_ne
            simpa only [parsedRay] using congrArg Prod.fst ray_zero
          · have scale_ne : upperScale β block ≠ 0 := by
              simp [upperScale]
            have new_second_ne : (rayStep β body block ray).2 ≠ 0 :=
              mul_ne_zero scale_ne first_zero
            intro ray_zero
            apply new_second_ne
            simpa only [parsedRay] using congrArg Prod.snd ray_zero

/-- A singleton pole above a long multi-role current automatically gives the older tail
decimal-unit peeled ancestry.

After dividing the pole recurrence by the nonzero older numerator, the older quotient is the
difference of the current trace and the pole correction, divided by two decimal units. The trace
has shell `(1,1)`; `m≥β+3` puts the correction strictly deeper at both primes. -/
theorem singletonPole_longMultiTail_admitsUnitPeeledCarrier
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current next : List NearyTile}
    {rest : List (List NearyTile)}
    (current_multi : 2 ≤ current.length) (current_ends : EndsInErase current)
    (tail_law : BlocksLaw (next :: rest))
    (current_long : β + 3 ≤ (spell (nearyUpper β) current).length)
    (pole : HitsSquarePole β body [.erase targetLetter] (current :: next :: rest)) :
    AdmitsUnitPeeledCarrier β (parsedRay β body (next :: rest)) := by
  have β_pos : 0 < β := by omega
  let ray := parsedRay β body (next :: rest)
  let x := ray.1
  let y := ray.2
  let m := (spell (nearyUpper β) current).length
  let E := gap ((10 : ℚ) ^ β)
  let G := lift ((10 : ℚ) ^ β)
  let μ := DecimalSetterMatrix.marker β
  let T := boundaryTrace β body current
  let V := lowerBoundaryCode β body current
  let A := upperScale β current
  let S := singletonTrace β targetLetter
  have E_ne : E ≠ 0 := (gap_tenPow_hasDecimalShell β_pos).1.1
  have G_ne : G ≠ 0 := (lift_tenPow_hasDecimalShell β_pos).1.1
  have μ_ne : μ ≠ 0 := (marker_hasDecimalShell β_pos).1.1
  have V_ne : V ≠ 0 :=
    (lowerBoundaryCode_hasDecimalShell_of_endsInErase β body current_ends).1.1
  have S_ne : S ≠ 0 := (singletonTrace_hasDecimalShell β_pos targetLetter).1.1
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
      · rcases mul_eq_zero.mp scaled_zero with neg_lift_zero | lower_zero
        · exact False.elim (G_ne neg_lift_zero)
        · exact False.elim (V_ne lower_zero)
      · exact y_zero
    exact ray_ne (Prod.ext x_zero y_zero)
  let correction := E * μ * G * A * 7 / S
  have residual_eq : T * x - G * V * y = correction * x := by
    apply mul_right_cancel₀ S_ne
    calc
      (T * x - G * V * y) * S = E * μ * G * A * x * 7 := pole_equation
      _ = (correction * x) * S := by
        dsimp only [correction]
        field_simp [S_ne]
  have quotient_eq : y / x = (T - correction) / (G * V) := by
    field_simp [x_ne, G_ne, V_ne]
    linear_combination -residual_eq
  have trace_shell :=
    DecimalSetterShallow.multiRoleErasureEnded_boundaryTrace_hasDecimalShell
      (show 2 ≤ β by omega) body current_multi current_ends
  have scale_shell : HasDecimalShell A m m := by
    have shell := ten_hasDecimalShell.pow m
    norm_num at shell
    simpa only [A, upperScale, m] using shell
  have seven_unit : HasDecimalShell (7 : ℚ) 0 0 :=
    intCast_hasDecimalShell_of_mod_seven (Int.ModEq.refl 7)
  have numerator_shell : HasDecimalShell (E * μ * G * A * 7) m m := by
    simpa only [E, G, μ, zero_add, add_zero] using
      ((((gap_tenPow_hasDecimalShell β_pos).mul (marker_hasDecimalShell β_pos)).mul
        (lift_tenPow_hasDecimalShell β_pos)).mul scale_shell).mul seven_unit
  have target_shell := singletonTrace_hasDecimalShell β_pos targetLetter
  have correction_shell :
      HasDecimalShell correction ((m : ℤ) - (β + 1)) ((m : ℤ) - β) := by
    dsimp only [correction]
    exact ⟨div_hasValue numerator_shell.1 target_shell.1,
      div_hasValue numerator_shell.2 target_shell.2⟩
  have correction_two_large : (1 : ℤ) < (m : ℤ) - (β + 1) := by
    simpa only [m] using (show (1 : ℤ) <
      ((spell (nearyUpper β) current).length : ℤ) - (β + 1) by omega)
  have correction_five_large : (1 : ℤ) < (m : ℤ) - β := by
    simpa only [m] using (show (1 : ℤ) <
      ((spell (nearyUpper β) current).length : ℤ) - β by omega)
  have residual_shell : HasDecimalShell (T - correction) 1 1 := by
    constructor
    · have shell := sub_hasValue_min trace_shell.1.1 correction_shell.1.1 (by
        rw [trace_shell.1.2, correction_shell.1.2]
        omega)
      rw [trace_shell.1.2, correction_shell.1.2,
        min_eq_left correction_two_large.le] at shell
      exact shell
    · have shell := sub_hasValue_min trace_shell.2.1 correction_shell.2.1 (by
        rw [trace_shell.2.2, correction_shell.2.2]
        omega)
      rw [trace_shell.2.2, correction_shell.2.2,
        min_eq_left correction_five_large.le] at shell
      exact shell
  have denominator_shell : HasDecimalShell (G * V) 0 0 := by
    simpa only [G, V, zero_add] using
      (lift_tenPow_hasDecimalShell β_pos).mul
        (lowerBoundaryCode_hasDecimalShell_of_endsInErase β body current_ends)
  have quotient_shell : HasDecimalShell (y / x) 1 1 := by
    rw [quotient_eq]
    exact ⟨by simpa using div_hasValue residual_shell.1 denominator_shell.1,
      by simpa using div_hasValue residual_shell.2 denominator_shell.2⟩
  apply (admitsUnitPeeledCarrier_iff_ratio_hasDecimalShell β_pos ray).mpr
  exact ⟨x_ne, quotient_shell⟩

/-- For a multi-role current at a genuine singleton pole, older unit ancestry is equivalent
to the sharp current upper-length bound. -/
theorem singletonPole_multiTail_admitsUnitPeeledCarrier_iff_currentLong
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current next : List NearyTile}
    {rest : List (List NearyTile)}
    (current_multi : 2 ≤ current.length) (current_ends : EndsInErase current)
    (tail_law : BlocksLaw (next :: rest))
    (pole : HitsSquarePole β body [.erase targetLetter] (current :: next :: rest)) :
    AdmitsUnitPeeledCarrier β (parsedRay β body (next :: rest)) ↔
      β + 3 ≤ (spell (nearyUpper β) current).length := by
  constructor
  · intro ancestry
    exact singletonPole_of_unitPeeledCarrier_forces_currentUpperLength
      (by omega) body targetLetter rest current_multi current_ends ancestry pole
  · intro current_long
    exact singletonPole_longMultiTail_admitsUnitPeeledCarrier
      β_large body targetLetter current_multi current_ends tail_law current_long pole

/-- Canonical arbitrary-history classifier: at a lawful singleton pole, older unit peeled
ancestry is equivalent to the current block being multi-role and having at least `β+3` upper
digits. -/
theorem singletonPole_tail_admitsUnitPeeledCarrier_iff_currentShape
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current next : List NearyTile}
    {rest : List (List NearyTile)} (current_ends : EndsInErase current)
    (tail_law : BlocksLaw (next :: rest))
    (pole : HitsSquarePole β body [.erase targetLetter] (current :: next :: rest)) :
    AdmitsUnitPeeledCarrier β (parsedRay β body (next :: rest)) ↔
      2 ≤ current.length ∧
        β + 3 ≤ (spell (nearyUpper β) current).length := by
  constructor
  · exact fun ancestry => singletonPole_of_unitPeeledCarrier_currentShape
      β_large body targetLetter rest current_ends ancestry pole
  · rintro ⟨current_multi, current_long⟩
    exact singletonPole_longMultiTail_admitsUnitPeeledCarrier
      β_large body targetLetter current_multi current_ends tail_law current_long pole

/-- Exact complementary grammar: non-unit ancestry at a lawful singleton pole means that the
current block is a singleton or a multi-role block with at most `β+2` upper digits. -/
theorem singletonPole_tail_not_admitsUnitPeeledCarrier_iff_shortCurrent
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current next : List NearyTile}
    {rest : List (List NearyTile)} (current_ends : EndsInErase current)
    (tail_law : BlocksLaw (next :: rest))
    (pole : HitsSquarePole β body [.erase targetLetter] (current :: next :: rest)) :
    ¬AdmitsUnitPeeledCarrier β (parsedRay β body (next :: rest)) ↔
      current.length = 1 ∨
        (2 ≤ current.length ∧
          (spell (nearyUpper β) current).length ≤ β + 2) := by
  have current_pos : 0 < current.length := by
    obtain ⟨front, letter, current_eq⟩ := current_ends
    simp [current_eq]
  rw [singletonPole_tail_admitsUnitPeeledCarrier_iff_currentShape
    β_large body targetLetter current_ends tail_law pole]
  omega

end MatrixMortality.DecimalSetterBridgeRay
