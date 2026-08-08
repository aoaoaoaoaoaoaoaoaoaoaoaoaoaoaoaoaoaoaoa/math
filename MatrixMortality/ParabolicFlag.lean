import MatrixMortality.ParabolicExterior

/-!
# Arbitrary-switching three-adic flag for the parabolic blade

The bridge wall is the first coordinate of `exteriorState`.  This file equips the remaining
three-coordinate dynamics with the exact projective `3`-adic flag preserved by every regular
safe atom.  Zero is treated as having infinite valuation through the relations below rather than
through `padicValRat`, whose library convention assigns zero valuation to zero.
-/

namespace MatrixMortality.ParabolicBlade

open MatrixMortality.PadicValuation
open scoped Matrix

/-- Strict comparison of rational valuations with zero on the right treated as infinity. -/
def ValLt (left right : ℚ) : Prop :=
  left ≠ 0 ∧ (right = 0 ∨ padicValRat 3 left < padicValRat 3 right)

/-- Weak comparison of rational valuations with zero on the right treated as infinity. -/
def ValLe (left right : ℚ) : Prop :=
  left ≠ 0 ∧ (right = 0 ∨ padicValRat 3 left ≤ padicValRat 3 right)

/-- The localization of the integers at three, with zero admitted explicitly. -/
def ThreeIntegral (value : ℚ) : Prop :=
  value = 0 ∨ 0 ≤ padicValRat 3 value

/-- The middle coordinate lies strictly above the minimum exterior valuation. -/
def ExteriorSector0 (state : Fin 3 → ℚ) : Prop :=
  ValLt (state 0) (state 1) ∨ ValLt (state 2) (state 1)

/-- The final coordinate lies strictly above the minimum exterior valuation. -/
def ExteriorSector1 (state : Fin 3 → ℚ) : Prop :=
  ValLt (state 0) (state 2) ∨ ValLt (state 1) (state 2)

/-- The union of the two projective exterior sectors. -/
def ExteriorFlag (state : Fin 3 → ℚ) : Prop :=
  ExteriorSector0 state ∨ ExteriorSector1 state

private theorem valLe_of_not_valLt_right_ne {left right : ℚ}
    (right_ne : right ≠ 0) (not_lt : ¬ValLt left right) : ValLe right left := by
  refine ⟨right_ne, ?_⟩
  by_cases left_zero : left = 0
  · exact Or.inl left_zero
  · refine Or.inr (le_of_not_gt ?_)
    exact fun left_lt => not_lt ⟨left_zero, Or.inr left_lt⟩

private theorem intCast_threeIntegral (value : ℤ) : ThreeIntegral (value : ℚ) := by
  by_cases value_zero : value = 0
  · exact Or.inl (by simp [value_zero])
  · right
    rw [padicValRat.of_int]
    exact Int.ofNat_zero_le _

private theorem valLt_sub {base left right : ℚ}
    (left_high : ValLt base left) (right_high : ValLt base right) :
    ValLt base (left - right) := by
  rcases left_high with ⟨base_ne, left_zero | left_gt⟩
  · rcases right_high with ⟨_, right_zero | right_gt⟩
    · exact ⟨base_ne, Or.inl (by simp [left_zero, right_zero])⟩
    · refine ⟨base_ne, Or.inr ?_⟩
      simpa [left_zero, padicValRat.neg] using right_gt
  · rcases right_high with ⟨_, right_zero | right_gt⟩
    · simpa [right_zero] using ⟨base_ne, Or.inr left_gt⟩
    · by_cases difference_zero : left - right = 0
      · exact ⟨base_ne, Or.inl difference_zero⟩
      · refine ⟨base_ne, Or.inr ?_⟩
        have bound := min_le_sub (prime := 3) difference_zero
        omega

private theorem valLe_sub {base left right : ℚ}
    (left_high : ValLe base left) (right_high : ValLe base right) :
    ValLe base (left - right) := by
  rcases left_high with ⟨base_ne, left_zero | left_bound⟩
  · rcases right_high with ⟨_, right_zero | right_bound⟩
    · exact ⟨base_ne, Or.inl (by simp [left_zero, right_zero])⟩
    · by_cases difference_zero : left - right = 0
      · exact ⟨base_ne, Or.inl difference_zero⟩
      · refine ⟨base_ne, Or.inr ?_⟩
        simpa [left_zero, padicValRat.neg] using right_bound
  · rcases right_high with ⟨_, right_zero | right_bound⟩
    · exact ⟨base_ne, Or.inr (by simpa [right_zero] using left_bound)⟩
    · by_cases difference_zero : left - right = 0
      · exact ⟨base_ne, Or.inl difference_zero⟩
      · refine ⟨base_ne, Or.inr ?_⟩
        have bound := min_le_sub (prime := 3) difference_zero
        omega

private theorem sub_hasValue_of_valLt {left right : ℚ}
    (comparison : ValLt left right) :
    HasValue 3 (left - right) (padicValRat 3 left) := by
  rcases comparison with ⟨left_ne, right_zero | valuation_lt⟩
  · simpa [right_zero] using (show HasValue 3 left (padicValRat 3 left) from ⟨left_ne, rfl⟩)
  · by_cases right_zero : right = 0
    · simpa [right_zero] using (show HasValue 3 left (padicValRat 3 left) from ⟨left_ne, rfl⟩)
    · refine ⟨sub_ne_zero.mpr (ne_of_valuation_ne (prime := 3) (ne_of_lt valuation_lt)), ?_⟩
      exact sub_eq_left_of_lt left_ne right_zero valuation_lt

private theorem add_hasValue_of_valLt {left right : ℚ}
    (comparison : ValLt left right) :
    HasValue 3 (left + right) (padicValRat 3 left) := by
  rcases comparison with ⟨left_ne, right_zero | valuation_lt⟩
  · simpa [right_zero] using (show HasValue 3 left (padicValRat 3 left) from ⟨left_ne, rfl⟩)
  · by_cases right_zero : right = 0
    · simpa [right_zero] using (show HasValue 3 left (padicValRat 3 left) from ⟨left_ne, rfl⟩)
    · exact add_hasValue_left ⟨left_ne, rfl⟩ ⟨right_zero, rfl⟩ valuation_lt

private theorem valLe_addend_of_valLe_sum
    {unit base error : ℚ} (unit_shell : IsUnit 3 unit) (base_ne : base ≠ 0)
    (sum_min : ValLe base (unit * base + error)) :
    ValLe base error := by
  refine ⟨base_ne, ?_⟩
  by_cases error_zero : error = 0
  · exact Or.inl error_zero
  · right
    apply le_of_not_gt
    intro error_lt
    have sum_value :
        HasValue 3 (unit * base + error) (padicValRat 3 error) := by
      apply add_hasValue_right (mul_hasValue unit_shell ⟨base_ne, rfl⟩) ⟨error_zero, rfl⟩
      simpa [unit_shell.2] using error_lt
    have bound : padicValRat 3 base ≤ padicValRat 3 (unit * base + error) :=
      sum_min.2.resolve_left sum_value.1
    rw [sum_value.2] at bound
    omega

private theorem valLt_unit_mul_add_forces_equal
    {unit left right : ℚ} (unit_shell : IsUnit 3 unit)
    (comparison : ValLt left (unit * left + right)) :
    right ≠ 0 ∧ padicValRat 3 right = padicValRat 3 left := by
  rcases comparison with ⟨left_ne, comparison⟩
  by_cases sum_zero : unit * left + right = 0
  · have right_eq : right = -(unit * left) := by linarith
    refine ⟨right_eq ▸ neg_ne_zero.mpr (mul_ne_zero unit_shell.1 left_ne), ?_⟩
    rw [right_eq, padicValRat.neg, padicValRat.mul unit_shell.1 left_ne, unit_shell.2]
    simp
  · have sum_ne : unit * left + right ≠ 0 := by
      exact sum_zero
    have sum_gt : padicValRat 3 left < padicValRat 3 (unit * left + right) :=
      comparison.resolve_left sum_zero
    have right_ne : right ≠ 0 := by
      intro right_zero
      rw [right_zero, add_zero, padicValRat.mul unit_shell.1 left_ne, unit_shell.2] at sum_gt
      simp at sum_gt
    refine ⟨right_ne, ?_⟩
    by_contra valuation_ne
    rcases lt_or_gt_of_ne valuation_ne with right_lt | left_lt
    · have unit_left_ne := mul_ne_zero unit_shell.1 left_ne
      have exact_value := padicValRat.add_eq_of_lt (p := 3)
        (by simpa [add_comm] using sum_ne) right_ne unit_left_ne
        (by simpa [unit_shell.2, padicValRat.mul unit_shell.1 left_ne] using right_lt)
      rw [add_comm] at exact_value
      rw [exact_value] at sum_gt
      omega
    · have exact_value := padicValRat.add_eq_of_lt (p := 3) sum_ne
        (mul_ne_zero unit_shell.1 left_ne) right_ne
        (by simpa [unit_shell.2, padicValRat.mul unit_shell.1 left_ne] using left_lt)
      rw [exact_value, padicValRat.mul unit_shell.1 left_ne, unit_shell.2] at sum_gt
      omega

private theorem flag_forces_first_lt_of_tail_equal
    {first middle last : ℚ} (middle_ne : middle ≠ 0) (last_ne : last ≠ 0)
    (tail_equal : padicValRat 3 last = padicValRat 3 middle)
    (flag : ExteriorFlag ![first, middle, last]) :
    ValLt first middle := by
  change (ValLt first middle ∨ ValLt last middle) ∨
    (ValLt first last ∨ ValLt middle last) at flag
  rcases flag with (first_lt | last_lt) | (first_lt | middle_lt)
  · exact first_lt
  · exact False.elim (by
      rcases last_lt with ⟨_, middle_zero | valuation_lt⟩
      · exact middle_ne middle_zero
      · rw [tail_equal] at valuation_lt
        exact (lt_irrefl _ valuation_lt))
  · rcases first_lt with ⟨first_ne, last_zero | valuation_lt⟩
    · exact False.elim (last_ne last_zero)
    · exact ⟨first_ne, Or.inr (tail_equal ▸ valuation_lt)⟩
  · exact False.elim (by
      rcases middle_lt with ⟨_, last_zero | valuation_lt⟩
      · exact last_ne last_zero
      · rw [tail_equal] at valuation_lt
        exact (lt_irrefl _ valuation_lt))

private theorem flag_forces_tail_unequal_of_last_lt_first
    {first middle last : ℚ} (middle_ne : middle ≠ 0) (last_ne : last ≠ 0)
    (last_lt_first : ValLt last first)
    (flag : ExteriorFlag ![first, middle, last]) :
    padicValRat 3 middle ≠ padicValRat 3 last := by
  intro tail_equal
  change (ValLt first middle ∨ ValLt last middle) ∨
    (ValLt first last ∨ ValLt middle last) at flag
  rcases last_lt_first with ⟨_, first_zero | last_lt⟩
  · rcases flag with (first_lt | last_lt) | (first_lt | middle_lt)
    · exact first_lt.1 first_zero
    · rcases last_lt.2 with middle_zero | valuation_lt
      · exact middle_ne middle_zero
      · rw [tail_equal] at valuation_lt
        exact (lt_irrefl _ valuation_lt)
    · exact first_lt.1 first_zero
    · rcases middle_lt.2 with last_zero | valuation_lt
      · exact last_ne last_zero
      · rw [tail_equal] at valuation_lt
        exact (lt_irrefl _ valuation_lt)
  · rcases flag with (first_lt | last_middle_lt) | (first_last_lt | middle_lt)
    · rcases first_lt.2 with middle_zero | first_lt'
      · exact middle_ne middle_zero
      · rw [tail_equal] at first_lt'
        omega
    · rcases last_middle_lt.2 with middle_zero | valuation_lt
      · exact middle_ne middle_zero
      · rw [tail_equal] at valuation_lt
        exact (lt_irrefl _ valuation_lt)
    · rcases first_last_lt.2 with last_zero | first_lt'
      · exact last_ne last_zero
      · omega
    · rcases middle_lt.2 with last_zero | valuation_lt
      · exact last_ne last_zero
      · rw [tail_equal] at valuation_lt
        exact (lt_irrefl _ valuation_lt)
/-- Every residue-zero `b` action sends the flag into the middle-coordinate sector. -/
theorem safeExteriorAction_b_zero_flag
    (β j : Nat) (L M u v w : ℚ)
    (flag : ExteriorFlag ![u, v, w]) :
    ExteriorSector0
      (safeExteriorAction ((3 : ℚ) ^ β) L M (.b, j, false) *ᵥ ![u, v, w]) := by
  let ρ : ℚ := 3 ^ β
  let A : ℚ := 8 * j + 1
  let B : ℚ := 32 * j * ρ - 8 * j + 2 * ρ - 1
  let C : ℚ := 8 * j - 3 * ρ + 1
  let D : ℚ := (24 * j + 1) / 2
  let E : ℚ := (24 * j + 3 * ρ - 2) / 2
  let first : ℚ := A * u - (3 / 2) * B * v + C * w
  let middle : ℚ := 9 * ρ * A * v
  let last : ℚ := 3 * ρ * (D * v + w)
  have action :
      safeExteriorAction ρ L M (.b, j, false) *ᵥ ![u, v, w] =
        ![first, middle, last] := by
    funext i
    fin_cases i <;>
      norm_num [safeExteriorAction, first, middle, last, A, B, C, D, ρ,
        Matrix.vecHead, Matrix.vecTail, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ] <;>
      ring
  rw [show (3 : ℚ) ^ β = ρ by rfl, action]
  change ValLt first middle ∨ ValLt last middle
  have rho_ne : ρ ≠ 0 := by
    dsimp [ρ]
    positivity
  have A_ne : A ≠ 0 := by
    dsimp [A]
    positivity
  have A_integral : ThreeIntegral A := by
    simpa [A] using intCast_threeIntegral (8 * (j : ℤ) + 1)
  have A_nonnegative : 0 ≤ padicValRat 3 A := A_integral.resolve_left A_ne
  have D_unit : IsUnit 3 D := by
    have numerator : IsUnit 3 ((24 * (j : ℤ) + 1 : ℤ) : ℚ) :=
      intCast_isUnit_of_not_dvd (by
        intro divides
        rcases divides with ⟨quotient, equality⟩
        omega)
    have denominator : IsUnit 3 (2 : ℚ) :=
      intCast_isUnit_of_not_dvd (by norm_num)
    simpa [D] using div_hasValue numerator denominator
  have E_unit : IsUnit 3 E := by
    have numerator : IsUnit 3
        ((24 * (j : ℤ) + 3 * (3 : ℤ) ^ β - 2 : ℤ) : ℚ) :=
      intCast_isUnit_of_not_dvd (by
        intro divides
        rcases divides with ⟨quotient, equality⟩
        omega)
    have denominator : IsUnit 3 (2 : ℚ) :=
      intCast_isUnit_of_not_dvd (by norm_num)
    simpa [E, ρ] using div_hasValue numerator denominator
  by_cases v_zero : v = 0
  · by_cases w_zero : w = 0
    · have u_ne : u ≠ 0 := by
        intro u_zero
        simp [ExteriorFlag, ExteriorSector0, ExteriorSector1, ValLt,
          u_zero, v_zero, w_zero] at flag
      left
      refine ⟨?_, Or.inl ?_⟩
      · dsimp [first]
        simp [v_zero, w_zero]
        exact ⟨A_ne, u_ne⟩
      · simp [middle, v_zero]
    · right
      refine ⟨?_, Or.inl ?_⟩
      · dsimp [last]
        simpa [v_zero] using
          mul_ne_zero (mul_ne_zero (by norm_num : (3 : ℚ) ≠ 0) rho_ne) w_zero
      · simp [middle, v_zero]
  · have middle_ne : middle ≠ 0 := by
      dsimp [middle]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) rho_ne) A_ne) v_zero
    by_contra sector
    have first_min := valLe_of_not_valLt_right_ne middle_ne
      (fun first_lt => sector (Or.inl first_lt))
    have last_min := valLe_of_not_valLt_right_ne middle_ne
      (fun last_lt => sector (Or.inr last_lt))
    have rho_value : HasValue 3 ρ β := by
      simpa [ρ] using (primePower_hasValue (prime := 3) β)
    have middle_value :
        HasValue 3 middle
          (2 + β + padicValRat 3 A + padicValRat 3 v) := by
      have nine_value : HasValue 3 (9 : ℚ) 2 := by
        simpa using (primePower_hasValue (prime := 3) 2)
      dsimp [middle]
      exact mul_hasValue
        (mul_hasValue (mul_hasValue nine_value rho_value) ⟨A_ne, rfl⟩) ⟨v_zero, rfl⟩
    have comparison : ValLt v (D * v + w) := by
      refine ⟨v_zero, ?_⟩
      by_cases sum_zero : D * v + w = 0
      · exact Or.inl sum_zero
      · right
        have last_ne : last ≠ 0 := by
          dsimp [last]
          exact mul_ne_zero (mul_ne_zero (by norm_num) rho_ne) sum_zero
        have last_value :
            HasValue 3 last (1 + β + padicValRat 3 (D * v + w)) := by
          have three_value : HasValue 3 (3 : ℚ) 1 := by
            simpa using (primePower_hasValue (prime := 3) 1)
          dsimp [last]
          exact mul_hasValue (mul_hasValue three_value rho_value) ⟨sum_zero, rfl⟩
        have bound : padicValRat 3 middle ≤ padicValRat 3 last :=
          last_min.2.resolve_left last_ne
        rw [middle_value.2, last_value.2] at bound
        omega
    obtain ⟨w_ne, tail_equal⟩ :=
      valLt_unit_mul_add_forces_equal D_unit comparison
    have u_lt := flag_forces_first_lt_of_tail_equal v_zero w_ne tail_equal flag
    rcases u_lt with ⟨u_ne, u_lt_v⟩
    have u_lt_v' : padicValRat 3 u < padicValRat 3 v :=
      u_lt_v.resolve_left v_zero
    have Ev_ne : E * v ≠ 0 := mul_ne_zero E_unit.1 v_zero
    have difference_value :
        HasValue 3 (u - E * v) (padicValRat 3 u) := by
      refine ⟨sub_ne_zero.mpr (ne_of_valuation_ne (prime := 3) ?_), ?_⟩
      · rw [padicValRat.mul E_unit.1 v_zero, E_unit.2]
        omega
      · exact sub_eq_left_of_lt u_ne Ev_ne (by
          rw [padicValRat.mul E_unit.1 v_zero, E_unit.2]
          omega)
    let blade : ℚ := A * (u - E * v)
    have blade_value :
        HasValue 3 blade (padicValRat 3 A + padicValRat 3 u) := by
      dsimp [blade]
      exact mul_hasValue ⟨A_ne, rfl⟩ difference_value
    have elimination : first - C / (3 * ρ) * last = blade := by
      dsimp [first, last, blade]
      field_simp
      ring
    have blade_lt_first : ValLt blade first := by
      refine ⟨blade_value.1, ?_⟩
      by_cases first_zero : first = 0
      · exact Or.inl first_zero
      · right
        have bound : padicValRat 3 middle ≤ padicValRat 3 first :=
          first_min.2.resolve_left first_zero
        rw [middle_value.2] at bound
        rw [blade_value.2]
        omega
    have C_integral : ThreeIntegral C := by
      have C_eq : C = ((8 * (j : ℤ) - 3 * (3 : ℤ) ^ β + 1 : ℤ) : ℚ) := by
        norm_num [C, ρ]
      rw [C_eq]
      exact intCast_threeIntegral _
    have blade_lt_last_term : ValLt blade (C / (3 * ρ) * last) := by
      refine ⟨blade_value.1, ?_⟩
      by_cases term_zero : C / (3 * ρ) * last = 0
      · exact Or.inl term_zero
      · right
        have C_ne : C ≠ 0 := by
          intro C_zero
          simp [C_zero] at term_zero
        have last_ne : last ≠ 0 := by
          intro last_zero
          simp [last_zero] at term_zero
        have C_nonnegative : 0 ≤ padicValRat 3 C := C_integral.resolve_left C_ne
        have denominator_value : HasValue 3 (3 * ρ) (1 + β) := by
          have three_value : HasValue 3 (3 : ℚ) 1 := by
            simpa using (primePower_hasValue (prime := 3) 1)
          exact mul_hasValue three_value rho_value
        have term_value :
            HasValue 3 (C / (3 * ρ) * last)
              (padicValRat 3 C - (1 + β) + padicValRat 3 last) := by
          exact mul_hasValue
            (div_hasValue ⟨C_ne, rfl⟩ denominator_value) ⟨last_ne, rfl⟩
        have bound : padicValRat 3 middle ≤ padicValRat 3 last :=
          last_min.2.resolve_left last_ne
        rw [middle_value.2] at bound
        rw [blade_value.2, term_value.2]
        omega
    have impossible := valLt_sub blade_lt_first blade_lt_last_term
    rw [elimination] at impossible
    rcases impossible.2 with blade_zero | valuation_lt
    · exact blade_value.1 blade_zero
    · exact (lt_irrefl _ valuation_lt)

private theorem c_zero_formula_flag
    (a B d₀ u v w : ℚ) (a_ne : a ≠ 0) (a_integral : ThreeIntegral a)
    (halfB_unit : IsUnit 3 (B / 2)) (d₀_integral : ThreeIntegral d₀)
    (a_step : a = d₀ + 1)
    (flag : ExteriorFlag ![u, v, w]) :
    ExteriorSector0 ![a * u - B / 2 * v + d₀ * w, 3 * a * v, B / 2 * v + w] := by
  let first := a * u - B / 2 * v + d₀ * w
  let middle := 3 * a * v
  let last := B / 2 * v + w
  change ValLt first middle ∨ ValLt last middle
  have a_nonnegative : 0 ≤ padicValRat 3 a := a_integral.resolve_left a_ne
  by_cases v_zero : v = 0
  · by_cases w_zero : w = 0
    · have u_ne : u ≠ 0 := by
        intro u_zero
        simp [ExteriorFlag, ExteriorSector0, ExteriorSector1, ValLt,
          u_zero, v_zero, w_zero] at flag
      left
      refine ⟨?_, Or.inl ?_⟩
      · dsimp [first]
        simp [v_zero, w_zero]
        exact ⟨a_ne, u_ne⟩
      · simp [middle, v_zero]
    · right
      refine ⟨?_, Or.inl ?_⟩
      · simpa [last, v_zero] using w_zero
      · simp [middle, v_zero]
  · have middle_ne : middle ≠ 0 := by
      dsimp [middle]
      exact mul_ne_zero (mul_ne_zero (by norm_num) a_ne) v_zero
    by_contra sector
    have first_min := valLe_of_not_valLt_right_ne middle_ne
      (fun first_lt => sector (Or.inl first_lt))
    have last_min := valLe_of_not_valLt_right_ne middle_ne
      (fun last_lt => sector (Or.inr last_lt))
    have middle_value :
        HasValue 3 middle (1 + padicValRat 3 a + padicValRat 3 v) := by
      have three_value : HasValue 3 (3 : ℚ) 1 := by
        simpa using (primePower_hasValue (prime := 3) 1)
      dsimp [middle]
      exact mul_hasValue (mul_hasValue three_value ⟨a_ne, rfl⟩) ⟨v_zero, rfl⟩
    have comparison : ValLt v last := by
      refine ⟨v_zero, ?_⟩
      by_cases last_zero : last = 0
      · exact Or.inl last_zero
      · right
        have bound : padicValRat 3 middle ≤ padicValRat 3 last :=
          last_min.2.resolve_left last_zero
        rw [middle_value.2] at bound
        omega
    obtain ⟨w_ne, tail_equal⟩ :=
      valLt_unit_mul_add_forces_equal halfB_unit comparison
    have u_lt := flag_forces_first_lt_of_tail_equal v_zero w_ne tail_equal flag
    rcases u_lt with ⟨u_ne, u_lt_v⟩
    have u_lt_v' : padicValRat 3 u < padicValRat 3 v :=
      u_lt_v.resolve_left v_zero
    have halfBv_ne : B / 2 * v ≠ 0 := mul_ne_zero halfB_unit.1 v_zero
    have difference_value :
        HasValue 3 (u - B / 2 * v) (padicValRat 3 u) := by
      refine ⟨sub_ne_zero.mpr (ne_of_valuation_ne (prime := 3) ?_), ?_⟩
      · rw [padicValRat.mul halfB_unit.1 v_zero, halfB_unit.2]
        omega
      · exact sub_eq_left_of_lt u_ne halfBv_ne (by
          rw [padicValRat.mul halfB_unit.1 v_zero, halfB_unit.2]
          omega)
    let blade := a * (u - B / 2 * v)
    have blade_value :
        HasValue 3 blade (padicValRat 3 a + padicValRat 3 u) := by
      dsimp [blade]
      exact mul_hasValue ⟨a_ne, rfl⟩ difference_value
    have elimination : first - d₀ * last = blade := by
      dsimp [first, last, blade]
      rw [a_step]
      ring
    have blade_lt_first : ValLt blade first := by
      refine ⟨blade_value.1, ?_⟩
      by_cases first_zero : first = 0
      · exact Or.inl first_zero
      · right
        have bound : padicValRat 3 middle ≤ padicValRat 3 first :=
          first_min.2.resolve_left first_zero
        rw [middle_value.2] at bound
        rw [blade_value.2]
        omega
    have blade_lt_last_term : ValLt blade (d₀ * last) := by
      refine ⟨blade_value.1, ?_⟩
      by_cases term_zero : d₀ * last = 0
      · exact Or.inl term_zero
      · right
        have d₀_ne : d₀ ≠ 0 := by
          intro d₀_zero
          simp [d₀_zero] at term_zero
        have last_ne : last ≠ 0 := by
          intro last_zero
          simp [last_zero] at term_zero
        have d₀_nonnegative : 0 ≤ padicValRat 3 d₀ :=
          d₀_integral.resolve_left d₀_ne
        have term_value :
            HasValue 3 (d₀ * last) (padicValRat 3 d₀ + padicValRat 3 last) :=
          mul_hasValue ⟨d₀_ne, rfl⟩ ⟨last_ne, rfl⟩
        have bound : padicValRat 3 middle ≤ padicValRat 3 last :=
          last_min.2.resolve_left last_ne
        rw [middle_value.2] at bound
        rw [blade_value.2, term_value.2]
        omega
    have impossible := valLt_sub blade_lt_first blade_lt_last_term
    rw [elimination] at impossible
    rcases impossible.2 with blade_zero | valuation_lt
    · exact blade_value.1 blade_zero
    · exact (lt_irrefl _ valuation_lt)

/-- Every residue-zero `c` action sends the flag into the middle-coordinate sector. -/
theorem safeExteriorAction_c_zero_flag
    (β j : Nat) (body : List TagLetter) (u v w : ℚ)
    (flag : ExteriorFlag ![u, v, w]) :
    ExteriorSector0
      (safeExteriorAction ((3 : ℚ) ^ β) (nearySideLowerC β body)
        (nearySideLowerCScale β body) (.c, j, false) *ᵥ ![u, v, w]) := by
  let L := nearySideLowerC β body
  let M := nearySideLowerCScale β body
  let a : ℚ := 1 + (M / 3 - 1) * j
  let B : ℚ := (L - 1) * j + 1
  let d₀ : ℚ := (M - 3) * j / 3
  have M_eq : M = 27 * (3 : ℚ) ^ (tagEncode β body).length := by
    dsimp [M]
    rw [nearySideLowerCScale_eq_nine_mul, pow_succ]
    ring
  have L_eq : L = 9 * ternaryCode (true :: tagEncode β body) + 7 := by
    exact nearySideLowerC_eq_nine_mul_add_seven β body
  have a_eq : a =
      ((1 + (9 * (3 : ℤ) ^ (tagEncode β body).length - 1) * j : ℤ) : ℚ) := by
    dsimp [a]
    rw [M_eq]
    push_cast
    ring
  have d₀_eq : d₀ =
      (((9 * (3 : ℤ) ^ (tagEncode β body).length - 1) * j : ℤ) : ℚ) := by
    dsimp [d₀]
    rw [M_eq]
    push_cast
    ring
  have a_ne : a ≠ 0 := by
    rw [a_eq]
    have power_positive : (0 : ℤ) < (3 : ℤ) ^ (tagEncode β body).length := by
      positivity
    have coefficient_nonnegative :
        (0 : ℤ) ≤ 9 * (3 : ℤ) ^ (tagEncode β body).length - 1 := by
      omega
    have product_nonnegative : (0 : ℤ) ≤
        (9 * (3 : ℤ) ^ (tagEncode β body).length - 1) * j :=
      mul_nonneg coefficient_nonnegative (by omega)
    exact_mod_cast (show (1 +
      (9 * (3 : ℤ) ^ (tagEncode β body).length - 1) * j : ℤ) ≠ 0 by omega)
  have a_integral : ThreeIntegral a := by
    rw [a_eq]
    exact intCast_threeIntegral _
  have d₀_integral : ThreeIntegral d₀ := by
    rw [d₀_eq]
    exact intCast_threeIntegral _
  have a_step : a = d₀ + 1 := by
    dsimp [a, d₀]
    ring
  have halfB_unit : IsUnit 3 (B / 2) := by
    have numerator : IsUnit 3
        (((9 * ternaryCode (true :: tagEncode β body) + 6) * j + 1 : ℤ) : ℚ) :=
      intCast_isUnit_of_not_dvd (by
        intro divides
        have base_dvd : (3 : ℤ) ∣
            (9 * ternaryCode (true :: tagEncode β body) + 6) * j := by
          refine ⟨(3 * ternaryCode (true :: tagEncode β body) + 2) * j, ?_⟩
          ring
        have one_dvd : (3 : ℤ) ∣ 1 := by
          convert dvd_sub divides base_dvd using 1
          ring
        norm_num at one_dvd)
    have denominator : IsUnit 3 (2 : ℚ) :=
      intCast_isUnit_of_not_dvd (by norm_num)
    have B_eq : B =
        (((9 * ternaryCode (true :: tagEncode β body) + 6) * j + 1 : ℤ) : ℚ) := by
      dsimp [B]
      rw [L_eq]
      push_cast
      ring
    rw [B_eq]
    exact div_hasValue numerator denominator
  have formula := c_zero_formula_flag a B d₀ u v w a_ne a_integral halfB_unit
    d₀_integral a_step flag
  have action :
      safeExteriorAction ((3 : ℚ) ^ β) L M (.c, j, false) *ᵥ ![u, v, w] =
        ![a * u - B / 2 * v + d₀ * w, 3 * a * v, B / 2 * v + w] := by
    funext i
    fin_cases i
    · norm_num [safeExteriorAction, L, M, a, B, d₀, Matrix.vecHead, Matrix.vecTail,
        Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ]
      ring
    · norm_num [safeExteriorAction, L, M, a, B, d₀, Matrix.vecHead, Matrix.vecTail,
        Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ]
      left
      ring
    · norm_num [safeExteriorAction, L, M, a, B, d₀, Matrix.vecHead, Matrix.vecTail,
        Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ]
  rw [action]
  exact formula

/-- Every regular residue-one `b` action sends the flag into the final-coordinate sector. -/
theorem safeExteriorAction_b_one_flag
    (β j : Nat) (j_positive : 0 < j) (L M u v w : ℚ)
    (flag : ExteriorFlag ![u, v, w]) :
    ExteriorSector1
      (safeExteriorAction ((3 : ℚ) ^ β) L M (.b, j, true) *ᵥ ![u, v, w]) := by
  let ρ : ℚ := 3 ^ β
  let h : ℚ := (8 * j + 3) * u + 8 * j * w
  let F : ℚ := (12 * ρ - 1) * (u + w) + 2 * v
  let first : ℚ := -4 * j * F
  let middle : ℚ := 3 * ρ * (3 * h + 2 * u)
  let last : ℚ := 9 * ρ / 2 * h
  have action :
      safeExteriorAction ρ L M (.b, j, true) *ᵥ ![u, v, w] =
        ![first, middle, last] := by
    funext i
    fin_cases i <;>
      norm_num [safeExteriorAction, h, F, first, middle, last, Matrix.vecHead,
        Matrix.vecTail, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ] <;>
      ring
  rw [show (3 : ℚ) ^ β = ρ by rfl, action]
  change ValLt first last ∨ ValLt middle last
  have rho_ne : ρ ≠ 0 := by
    dsimp [ρ]
    positivity
  have j_ne : (j : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt j_positive)
  by_contra sector
  have h_ne : h ≠ 0 := by
    intro h_zero
    have last_zero : last = 0 := by simp [last, h_zero]
    have first_zero : first = 0 := by
      by_contra first_ne
      exact sector (Or.inl ⟨first_ne, Or.inl last_zero⟩)
    have middle_zero : middle = 0 := by
      by_contra middle_ne
      exact sector (Or.inr ⟨middle_ne, Or.inl last_zero⟩)
    have u_zero : u = 0 := by
      have core_zero : 3 * h + 2 * u = 0 :=
        (mul_eq_zero.mp middle_zero).resolve_left
          (mul_ne_zero (by norm_num) rho_ne)
      rw [h_zero] at core_zero
      linarith
    have w_zero : w = 0 := by
      dsimp [h] at h_zero
      rw [u_zero] at h_zero
      simpa [j_ne] using h_zero
    have v_zero : v = 0 := by
      dsimp [first, F] at first_zero
      rw [u_zero, w_zero] at first_zero
      simpa [j_ne] using first_zero
    simp [ExteriorFlag, ExteriorSector0, ExteriorSector1, ValLt,
      u_zero, v_zero, w_zero] at flag
  have last_ne : last ≠ 0 := by
    dsimp [last]
    exact mul_ne_zero (div_ne_zero (mul_ne_zero (by norm_num) rho_ne) (by norm_num)) h_ne
  have middle_min := valLe_of_not_valLt_right_ne last_ne
    (fun middle_lt => sector (Or.inr middle_lt))
  have rho_value : HasValue 3 ρ β := by
    simpa [ρ] using (primePower_hasValue (prime := 3) β)
  have last_value :
      HasValue 3 last (2 + β + padicValRat 3 h) := by
    have nine_value : HasValue 3 (9 : ℚ) 2 := by
      simpa using (primePower_hasValue (prime := 3) 2)
    have two_unit : IsUnit 3 (2 : ℚ) :=
      intCast_isUnit_of_not_dvd (by norm_num)
    dsimp [last]
    exact mul_hasValue (div_hasValue (mul_hasValue nine_value rho_value) two_unit) ⟨h_ne, rfl⟩
  have middle_identity : middle = 2 * last + 6 * ρ * u := by
    dsimp [middle, last]
    ring
  have error_min : ValLe last (6 * ρ * u) := by
    have two_unit : IsUnit 3 (2 : ℚ) :=
      intCast_isUnit_of_not_dvd (by norm_num)
    apply valLe_addend_of_valLe_sum two_unit last_ne
    rw [← middle_identity]
    exact middle_min
  have h_lt_u : ValLt h u := by
    refine ⟨h_ne, ?_⟩
    by_cases u_zero : u = 0
    · exact Or.inl u_zero
    · right
      have six_value : HasValue 3 (6 : ℚ) 1 := by
        have three_value : HasValue 3 (3 : ℚ) 1 := by
          simpa using (primePower_hasValue (prime := 3) 1)
        have two_unit : IsUnit 3 (2 : ℚ) :=
          intCast_isUnit_of_not_dvd (by norm_num)
        simpa only [show (6 : ℚ) = 3 * 2 by norm_num, two_unit.2, add_zero] using
          mul_hasValue three_value two_unit
      have error_value :
          HasValue 3 (6 * ρ * u) (1 + β + padicValRat 3 u) :=
        mul_hasValue (mul_hasValue six_value rho_value) ⟨u_zero, rfl⟩
      have bound : padicValRat 3 last ≤ padicValRat 3 (6 * ρ * u) :=
        error_min.2.resolve_left error_value.1
      rw [last_value.2, error_value.2] at bound
      omega
  let high : ℚ := (8 * j + 3) * u
  have high_integral : ThreeIntegral (8 * j + 3 : ℚ) := by
    simpa using intCast_threeIntegral (8 * (j : ℤ) + 3)
  have high_coefficient_ne : (8 * j + 3 : ℚ) ≠ 0 := by positivity
  have h_lt_high : ValLt h high := by
    refine ⟨h_ne, ?_⟩
    by_cases u_zero : u = 0
    · exact Or.inl (by simp [high, u_zero])
    · right
      rw [padicValRat.mul high_coefficient_ne u_zero]
      have coefficient_nonnegative := high_integral.resolve_left high_coefficient_ne
      have h_lt_u' := h_lt_u.2.resolve_left u_zero
      omega
  have remainder_value := sub_hasValue_of_valLt h_lt_high
  have remainder_identity : h - high = 8 * j * w := by
    dsimp [h, high]
    ring
  have w_ne : w ≠ 0 := by
    intro w_zero
    rw [remainder_identity, w_zero] at remainder_value
    exact remainder_value.1 (by ring)
  have eight_unit : IsUnit 3 (8 : ℚ) :=
    intCast_isUnit_of_not_dvd (by norm_num)
  have j_value : HasValue 3 (j : ℚ) (padicValRat 3 (j : ℚ)) := ⟨j_ne, rfl⟩
  have remainder_value' :
      HasValue 3 (8 * j * w) (padicValRat 3 (j : ℚ) + padicValRat 3 w) := by
    simpa only [eight_unit.2, zero_add] using
      mul_hasValue (mul_hasValue eight_unit j_value) ⟨w_ne, rfl⟩
  have h_value :
      padicValRat 3 h = padicValRat 3 (j : ℚ) + padicValRat 3 w := by
    have value := remainder_value.2
    rw [remainder_identity, remainder_value'.2] at value
    exact value.symm
  have j_integral : ThreeIntegral (j : ℚ) := by
    simpa using intCast_threeIntegral (j : ℤ)
  have j_nonnegative : 0 ≤ padicValRat 3 (j : ℚ) :=
    j_integral.resolve_left j_ne
  have w_lt_u : ValLt w u := by
    refine ⟨w_ne, ?_⟩
    by_cases u_zero : u = 0
    · exact Or.inl u_zero
    · right
      have h_lt_u' := h_lt_u.2.resolve_left u_zero
      rw [h_value] at h_lt_u'
      omega
  have twelve_rho_sub_one_unit : IsUnit 3 (12 * ρ - 1) := by
    have twelve_value : HasValue 3 (12 : ℚ) 1 := by
      have three_value : HasValue 3 (3 : ℚ) 1 := by
        simpa using (primePower_hasValue (prime := 3) 1)
      have four_unit : IsUnit 3 (4 : ℚ) :=
        intCast_isUnit_of_not_dvd (by norm_num)
      simpa only [show (12 : ℚ) = 3 * 4 by norm_num, four_unit.2, add_zero] using
        mul_hasValue three_value four_unit
    have live_value := mul_hasValue twelve_value rho_value
    exact positive_sub_one ⟨live_value.1, by rw [live_value.2]; omega⟩
  have sum_value : HasValue 3 (u + w) (padicValRat 3 w) := by
    simpa [add_comm] using add_hasValue_of_valLt w_lt_u
  have leading_value :
      HasValue 3 ((12 * ρ - 1) * (u + w)) (padicValRat 3 w) := by
    simpa using mul_hasValue twelve_rho_sub_one_unit sum_value
  have two_unit : IsUnit 3 (2 : ℚ) :=
    intCast_isUnit_of_not_dvd (by norm_num)
  have F_value : HasValue 3 F (padicValRat 3 F) := by
    exact ⟨by
      by_cases v_zero : v = 0
      · dsimp [F]
        simpa [v_zero] using leading_value.1
      · have tail_unequal := flag_forces_tail_unequal_of_last_lt_first
          v_zero w_ne w_lt_u flag
        have error_value := mul_hasValue two_unit
          (show HasValue 3 v (padicValRat 3 v) from ⟨v_zero, rfl⟩)
        dsimp [F]
        by_cases leading_lt : padicValRat 3 w < padicValRat 3 v
        · exact (add_hasValue_left leading_value error_value (by simpa using leading_lt)).1
        · exact (add_hasValue_right leading_value error_value
            (by simpa using lt_of_le_of_ne (le_of_not_gt leading_lt) tail_unequal)).1,
      rfl⟩
  have F_bound : padicValRat 3 F ≤ padicValRat 3 w := by
    by_cases v_zero : v = 0
    · dsimp [F]
      have exact_value :
          padicValRat 3 ((12 * ρ - 1) * (u + w) + 2 * v) = padicValRat 3 w := by
        simpa [v_zero] using leading_value.2
      rw [exact_value]
    · have tail_unequal := flag_forces_tail_unequal_of_last_lt_first
        v_zero w_ne w_lt_u flag
      have error_value := mul_hasValue two_unit
        (show HasValue 3 v (padicValRat 3 v) from ⟨v_zero, rfl⟩)
      dsimp [F]
      by_cases leading_lt : padicValRat 3 w < padicValRat 3 v
      · rw [(add_hasValue_left leading_value error_value (by simpa using leading_lt)).2]
      · rw [(add_hasValue_right leading_value error_value
          (by simpa using lt_of_le_of_ne (le_of_not_gt leading_lt) tail_unequal)).2]
        omega
  have negative_four_unit : IsUnit 3 (-4 : ℚ) :=
    neg_hasValue (intCast_isUnit_of_not_dvd (by norm_num))
  have first_value :
      HasValue 3 first (padicValRat 3 (j : ℚ) + padicValRat 3 F) := by
    dsimp [first]
    simpa only [negative_four_unit.2, zero_add] using
      mul_hasValue (mul_hasValue negative_four_unit j_value) F_value
  have first_lt_last : ValLt first last := by
    refine ⟨first_value.1, Or.inr ?_⟩
    rw [first_value.2, last_value.2, h_value]
    omega
  exact sector (Or.inl first_lt_last)

/-- Two exact eliminations force a residue-one action into the final-coordinate sector. -/
theorem cOneElimination_flag
    (A d e f Δ κ u v w first middle last : ℚ)
    (d_unit : IsUnit 3 d) (e_positive : IsPositive 3 e)
    (f_positive : IsPositive 3 f) (Δ_positive : IsPositive 3 Δ)
    (κ_unit : IsUnit 3 κ) (A_integral : ThreeIntegral A)
    (middle_eq : middle = d * u + e * w)
    (last_elimination : d * last - f * middle = Δ * w)
    (first_elimination : d * first - A * middle = Δ / 3 * (κ * w - d * v))
    (flag : ExteriorFlag ![u, v, w]) :
    ExteriorSector1 ![first, middle, last] := by
  change ValLt first last ∨ ValLt middle last
  by_contra sector
  have last_ne : last ≠ 0 := by
    intro last_zero
    have first_zero : first = 0 := by
      by_contra first_ne
      exact sector (Or.inl ⟨first_ne, Or.inl last_zero⟩)
    have middle_zero : middle = 0 := by
      by_contra middle_ne
      exact sector (Or.inr ⟨middle_ne, Or.inl last_zero⟩)
    have w_zero : w = 0 := by
      rw [last_zero, middle_zero] at last_elimination
      exact (mul_eq_zero.mp (by simpa using last_elimination.symm)).resolve_left Δ_positive.1
    have u_zero : u = 0 := by
      rw [middle_zero, w_zero] at middle_eq
      exact (mul_eq_zero.mp (by simpa using middle_eq.symm)).resolve_left d_unit.1
    have v_zero : v = 0 := by
      rw [first_zero, middle_zero, w_zero] at first_elimination
      norm_num only [mul_zero, sub_zero, zero_sub] at first_elimination
      have core_zero : -(d * v) = 0 :=
        (mul_eq_zero.mp first_elimination.symm).resolve_left
          (div_ne_zero Δ_positive.1 (by norm_num))
      exact (mul_eq_zero.mp (neg_eq_zero.mp core_zero)).resolve_left d_unit.1
    simp [ExteriorFlag, ExteriorSector0, ExteriorSector1, ValLt,
      u_zero, v_zero, w_zero] at flag
  have first_min := valLe_of_not_valLt_right_ne last_ne
    (fun first_lt => sector (Or.inl first_lt))
  have middle_min := valLe_of_not_valLt_right_ne last_ne
    (fun middle_lt => sector (Or.inr middle_lt))
  have dlast_value : HasValue 3 (d * last) (padicValRat 3 last) := by
    simpa using mul_hasValue d_unit
      (show HasValue 3 last (padicValRat 3 last) from ⟨last_ne, rfl⟩)
  have leading_lt_error : ValLt (d * last) (f * middle) := by
    refine ⟨dlast_value.1, ?_⟩
    by_cases middle_zero : middle = 0
    · exact Or.inl (by simp [middle_zero])
    · right
      have f_value : HasValue 3 f (padicValRat 3 f) := ⟨f_positive.1, rfl⟩
      have fmiddle_value := mul_hasValue f_value
        (show HasValue 3 middle (padicValRat 3 middle) from ⟨middle_zero, rfl⟩)
      have middle_bound := middle_min.2.resolve_left middle_zero
      rw [dlast_value.2, fmiddle_value.2]
      have f_value_positive := f_positive.2
      omega
  have wall_value := sub_hasValue_of_valLt leading_lt_error
  rw [last_elimination] at wall_value
  have w_ne : w ≠ 0 := fun w_zero => wall_value.1 (by simp [w_zero])
  have Δ_value : HasValue 3 Δ (padicValRat 3 Δ) := ⟨Δ_positive.1, rfl⟩
  have Δw_value := mul_hasValue Δ_value
    (show HasValue 3 w (padicValRat 3 w) from ⟨w_ne, rfl⟩)
  have last_value :
      padicValRat 3 last = padicValRat 3 Δ + padicValRat 3 w := by
    calc
      padicValRat 3 last = padicValRat 3 (d * last) := dlast_value.2.symm
      _ = padicValRat 3 (Δ * w) := wall_value.2.symm
      _ = padicValRat 3 Δ + padicValRat 3 w := Δw_value.2
  have dfirst_min : ValLe last (d * first) := by
    refine ⟨last_ne, ?_⟩
    by_cases first_zero : first = 0
    · exact Or.inl (by simp [first_zero])
    · right
      have first_bound := first_min.2.resolve_left first_zero
      rw [padicValRat.mul d_unit.1 first_zero, d_unit.2]
      omega
  have Amiddle_min : ValLe last (A * middle) := by
    refine ⟨last_ne, ?_⟩
    by_cases product_zero : A * middle = 0
    · exact Or.inl product_zero
    · right
      have A_ne := (mul_ne_zero_iff.mp product_zero).1
      have middle_ne := (mul_ne_zero_iff.mp product_zero).2
      rw [padicValRat.mul A_ne middle_ne]
      have A_nonnegative := A_integral.resolve_left A_ne
      have middle_bound := middle_min.2.resolve_left middle_ne
      omega
  have wound_min := valLe_sub dfirst_min Amiddle_min
  rw [first_elimination] at wound_min
  have three_value : HasValue 3 (3 : ℚ) 1 := by
    simpa using (primePower_hasValue (prime := 3) 1)
  have Δ_div_three := div_hasValue Δ_value three_value
  have cancellation_sub : ValLt w (κ * w - d * v) := by
    refine ⟨w_ne, ?_⟩
    by_cases core_zero : κ * w - d * v = 0
    · exact Or.inl core_zero
    · right
      have product_value := mul_hasValue Δ_div_three
        (show HasValue 3 (κ * w - d * v)
          (padicValRat 3 (κ * w - d * v)) from ⟨core_zero, rfl⟩)
      have wound_bound := wound_min.2.resolve_left product_value.1
      rw [product_value.2, last_value] at wound_bound
      omega
  have cancellation : ValLt w (κ * w + -(d * v)) := by
    simpa only [sub_eq_add_neg] using cancellation_sub
  obtain ⟨dv_ne, dv_value⟩ :=
    valLt_unit_mul_add_forces_equal κ_unit cancellation
  have v_ne : v ≠ 0 := fun v_zero => dv_ne (by simp [v_zero])
  have v_eq_w : padicValRat 3 v = padicValRat 3 w := by
    rw [padicValRat.neg, padicValRat.mul d_unit.1 v_ne, d_unit.2, zero_add] at dv_value
    exact dv_value
  obtain ⟨u_ne, u_lt_v⟩ :=
    flag_forces_first_lt_of_tail_equal v_ne w_ne v_eq_w.symm flag
  have du_value : HasValue 3 (d * u) (padicValRat 3 u) := by
    simpa using mul_hasValue d_unit
      (show HasValue 3 u (padicValRat 3 u) from ⟨u_ne, rfl⟩)
  have e_value : HasValue 3 e (padicValRat 3 e) := ⟨e_positive.1, rfl⟩
  have ew_value := mul_hasValue e_value
    (show HasValue 3 w (padicValRat 3 w) from ⟨w_ne, rfl⟩)
  have middle_value : HasValue 3 middle (padicValRat 3 u) := by
    rw [middle_eq]
    exact add_hasValue_left du_value ew_value (by
      have u_lt_w : padicValRat 3 u < padicValRat 3 w := v_eq_w ▸ u_lt_v.resolve_left v_ne
      have e_value_positive := e_positive.2
      omega)
  apply sector
  right
  refine ⟨middle_value.1, Or.inr ?_⟩
  rw [middle_value.2, last_value]
  have u_lt_w : padicValRat 3 u < padicValRat 3 w := v_eq_w ▸ u_lt_v.resolve_left v_ne
  have Δ_value_positive := Δ_positive.2
  omega

/-- The empty suffix exterior state lies in the final-coordinate sector. -/
theorem exteriorFlag_seed : ExteriorFlag ![(0 : ℚ), 22, 9] := by
  have middle_unit : IsUnit 3 (22 : ℚ) :=
    intCast_isUnit_of_not_dvd (by norm_num)
  have last_value : HasValue 3 (9 : ℚ) 2 := by
    simpa using (primePower_hasValue (prime := 3) 2)
  right
  right
  refine ⟨by norm_num, Or.inr ?_⟩
  change padicValRat 3 (22 : ℚ) < padicValRat 3 (9 : ℚ)
  rw [middle_unit.2, last_value.2]
  norm_num

end MatrixMortality.ParabolicBlade
