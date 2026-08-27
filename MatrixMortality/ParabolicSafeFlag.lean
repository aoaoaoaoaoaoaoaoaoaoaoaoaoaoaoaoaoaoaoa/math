import MatrixMortality.ParabolicFlag

/-!
# Safe-word exterior flag

The residue-one `c` elimination closes the fourth atom family.  The resulting theorem transports
the two-sector flag through arbitrary regular safe words and leaves only the oriented bridge wall.
-/

namespace MatrixMortality.ParabolicBlade

open MatrixMortality.PadicValuation
open scoped Matrix

private theorem three_mul_int_div_unit_positive
    (value denominator : ℤ) (value_ne : value ≠ 0)
    (denominator_unit : IsUnit 3 (denominator : ℚ)) :
    IsPositive 3 (((3 * value : ℤ) : ℚ) / denominator) := by
  have three_value : HasValue 3 (3 : ℚ) 1 := by
    simpa using (primePower_hasValue (prime := 3) 1)
  have value_shell : HasValue 3 (value : ℚ) (padicValRat 3 (value : ℚ)) := by
    exact ⟨by exact_mod_cast value_ne, rfl⟩
  have quotient := div_hasValue (mul_hasValue three_value value_shell) denominator_unit
  have cast_eq : (((3 * value : ℤ) : ℚ) / denominator) =
      (3 : ℚ) * value / denominator := by
    push_cast
    rfl
  rw [cast_eq]
  refine ⟨quotient.1, ?_⟩
  rw [quotient.2]
  have value_nonnegative : 0 ≤ padicValRat 3 (value : ℚ) := by
    rw [padicValRat.of_int]
    exact Int.natCast_nonneg _
  omega

private theorem safeExteriorAction_c_one_flag
    (β j : Nat) (body : List TagLetter)
    (body_nonempty : body ≠ []) (u v w : ℚ)
    (flag : ExteriorFlag ![u, v, w]) :
    ExteriorSector1
      (safeExteriorAction ((3 : ℚ) ^ β) (nearySideLowerC β body)
        (nearySideLowerCScale β body) (.c, j, true) *ᵥ ![u, v, w]) := by
  let ρ : ℚ := 3 ^ β
  let L := nearySideLowerC β body
  let M := nearySideLowerCScale β body
  let P : ℤ := 3 ^ (tagEncode β body).length
  let K : ℤ := ternaryCode (true :: tagEncode β body)
  let d : ℚ := (M - 3) * j + M / 3 + 2
  let e : ℚ := (M - 3) * j + (27 - M) / 8
  let f : ℚ := (L - 1) * j / 2 + (L + 2) / 6
  let g : ℚ := (L - 1) * j / 2 + (25 - L) / 16
  let Δ : ℚ := (16 * (M - 3) * j + 9 * M - 11 * L + 32) / 16
  let κ : ℚ := -(114 * M * ρ - 11 * M - 342 * ρ + 177) / 48
  let A : ℚ :=
    (-48 * L * j + 114 * L * ρ - 27 * L - 32 * M * j - 38 * M * ρ -
      7 * M + 144 * j - 96) / 96
  let C : ℚ :=
    (-48 * L * j + 114 * L * ρ - 5 * L - 32 * M * j - 114 * M * ρ +
      15 * M + 144 * j + 228 * ρ - 280) / 96
  let first := A * u - Δ / 3 * v + C * w
  let middle := d * u + e * w
  let last := f * u + g * w
  have L_eq : L = ((9 * K + 7 : ℤ) : ℚ) := by
    dsimp [L, K]
    rw [nearySideLowerC_eq_nine_mul_add_seven]
    push_cast
    ring
  have M_eq : M = ((27 * P : ℤ) : ℚ) := by
    dsimp [M, P]
    rw [nearySideLowerCScale_eq_nine_mul, pow_succ]
    push_cast
    ring
  have ρ_eq : ρ = (((3 : ℤ) ^ β : ℤ) : ℚ) := by
    simp [ρ]
  have P_ge_three : 3 ≤ P := by
    have encoded_nonempty : tagEncode β body ≠ [] :=
      (tagEncode_eq_nil_iff β body).not.mpr body_nonempty
    have length_positive := List.length_pos_of_ne_nil encoded_nonempty
    have power_bound : 3 ^ 1 ≤ 3 ^ (tagEncode β body).length :=
      Nat.pow_le_pow_right (by norm_num) length_positive
    dsimp [P]
    exact_mod_cast (by simpa using power_bound)
  let dᵢ : ℤ := 3 * ((9 * P - 1) * j + 3 * P) + 2
  have d_eq : d = (dᵢ : ℚ) := by
    dsimp [d, dᵢ]
    rw [M_eq]
    push_cast
    ring
  have d_unit : IsUnit 3 d := by
    rw [d_eq]
    apply intCast_isUnit_of_not_dvd
    dsimp [dᵢ]
    omega
  let eᵢ : ℤ := 8 * (9 * P - 1) * j + 9 * (1 - P)
  have e_eq : e = ((3 * eᵢ : ℤ) : ℚ) / 8 := by
    dsimp [e, eᵢ]
    rw [M_eq]
    push_cast
    ring
  have eᵢ_ne : eᵢ ≠ 0 := by
    cases j with
    | zero => dsimp [eᵢ]; omega
    | succ j => dsimp [eᵢ]; nlinarith
  have e_positive : IsPositive 3 e := by
    rw [e_eq]
    exact three_mul_int_div_unit_positive eᵢ 8 eᵢ_ne
      (intCast_isUnit_of_not_dvd (by norm_num))
  let fᵢ : ℤ := (3 * K + 2) * j + K + 1
  have f_eq : f = ((3 * fᵢ : ℤ) : ℚ) / 2 := by
    dsimp [f, fᵢ]
    rw [L_eq]
    push_cast
    ring
  have fᵢ_ne : fᵢ ≠ 0 := by
    dsimp [fᵢ]
    positivity
  have f_positive : IsPositive 3 f := by
    rw [f_eq]
    exact three_mul_int_div_unit_positive fᵢ 2 fᵢ_ne
      (intCast_isUnit_of_not_dvd (by norm_num))
  let Δᵢ : ℤ := 16 * (9 * P - 1) * j + 81 * P - 33 * K - 15
  have Δ_eq : Δ = ((3 * Δᵢ : ℤ) : ℚ) / 16 := by
    dsimp [Δ, Δᵢ]
    rw [L_eq, M_eq]
    push_cast
    ring
  have Δᵢ_ne : Δᵢ ≠ 0 := by
    intro Δᵢ_zero
    have Δ_zero : Δ = 0 := by
      rw [Δ_eq, Δᵢ_zero]
      norm_num
    have pencil_zero :
        (16 * (M - 3) * (j : ℚ) + 9 * M - 11 * L + 32) = 0 := by
      dsimp [Δ] at Δ_zero
      linarith
    have determinant_ne :=
      cAtom_det_three_mul_add_one_ne_zero β body body_nonempty j
    rw [cAtom_det_three_mul_add_one] at determinant_ne
    apply determinant_ne
    change (3 / 16 : ℚ) *
      (16 * (j : ℚ) * (M - 3) + 9 * M - 11 * L + 32) = 0
    rw [show 16 * (j : ℚ) * (M - 3) = 16 * (M - 3) * j by ring, pencil_zero]
    norm_num
  have Δ_positive : IsPositive 3 Δ := by
    rw [Δ_eq]
    exact three_mul_int_div_unit_positive Δᵢ 16 Δᵢ_ne
      (intCast_isUnit_of_not_dvd (by norm_num))
  let κᵢ : ℤ := 38 * 27 * P * 3 ^ β - 99 * P - 114 * 3 ^ β + 59
  have κ_eq : κ = -(κᵢ : ℚ) / 16 := by
    dsimp [κ, κᵢ]
    rw [M_eq, ρ_eq]
    push_cast
    ring
  have κ_unit : IsUnit 3 κ := by
    rw [κ_eq]
    have κᵢ_shape : κᵢ =
        3 * (342 * P * 3 ^ β - 33 * P - 38 * 3 ^ β + 19) + 2 := by
      dsimp [κᵢ]
      ring
    exact div_hasValue
      (neg_hasValue (intCast_isUnit_of_not_dvd (by rw [κᵢ_shape]; omega)))
      (intCast_isUnit_of_not_dvd (by norm_num))
  let Aᵢ : ℤ :=
    -16 * (9 * K + 7) * j + 38 * (9 * K + 7) * 3 ^ β - 9 * (9 * K + 7) -
      288 * P * j - 342 * P * 3 ^ β - 63 * P + 48 * j - 32
  have A_eq : A = (Aᵢ : ℚ) / 32 := by
    dsimp [A, Aᵢ]
    rw [L_eq, M_eq, ρ_eq]
    push_cast
    ring
  have A_integral : ThreeIntegral A := by
    rw [A_eq]
    by_cases Aᵢ_zero : Aᵢ = 0
    · exact Or.inl (by simp [Aᵢ_zero])
    · right
      have numerator : HasValue 3 (Aᵢ : ℚ) (padicValRat 3 (Aᵢ : ℚ)) :=
        ⟨by exact_mod_cast Aᵢ_zero, rfl⟩
      have denominator : IsUnit 3 (32 : ℚ) :=
        intCast_isUnit_of_not_dvd (by norm_num)
      have quotient := div_hasValue numerator denominator
      rw [quotient.2]
      simp only [sub_zero]
      rw [padicValRat.of_int]
      exact Int.natCast_nonneg _
  have action :
      safeExteriorAction ρ L M (.c, j, true) *ᵥ ![u, v, w] =
        ![first, middle, last] := by
    funext i
    fin_cases i <;>
      norm_num [safeExteriorAction, first, middle, last, A, C, d, e, f, g, Δ,
        Matrix.vecHead, Matrix.vecTail, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    all_goals ring
  have last_elimination : d * last - f * middle = Δ * w := by
    dsimp [middle, last, d, e, f, g, Δ]
    ring
  have first_elimination :
      d * first - A * middle = Δ / 3 * (κ * w - d * v) := by
    dsimp [first, middle, A, C, d, e, Δ, κ]
    ring
  rw [show (3 : ℚ) ^ β = ρ by rfl, action]
  exact cOneElimination_flag A d e f Δ κ u v w first middle last d_unit e_positive
    f_positive Δ_positive κ_unit A_integral rfl last_elimination first_elimination flag

/-- A safe label is regular unless it is the forbidden zero-wait residue-one `b` atom. -/
def RegularSafeLabel : TagLetter × Nat × Bool → Prop
  | (.b, j, true) => 0 < j
  | _ => True

private theorem valLt_mul_scalar {scalar left right : ℚ} (scalar_ne : scalar ≠ 0) :
    ValLt left right → ValLt (scalar * left) (scalar * right) := by
  rintro ⟨left_ne, right_zero | valuation_lt⟩
  · exact ⟨mul_ne_zero scalar_ne left_ne, Or.inl (by simp [right_zero])⟩
  · by_cases right_zero : right = 0
    · exact ⟨mul_ne_zero scalar_ne left_ne, Or.inl (by simp [right_zero])⟩
    · refine ⟨mul_ne_zero scalar_ne left_ne, Or.inr ?_⟩
      rw [padicValRat.mul scalar_ne left_ne, padicValRat.mul scalar_ne right_zero]
      omega

private theorem exteriorSector0_smul (scalar : ℚ) (scalar_ne : scalar ≠ 0)
    {state : Fin 3 → ℚ} (sector : ExteriorSector0 state) :
    ExteriorSector0 (scalar • state) := by
  rcases sector with first | last
  · left
    simpa only [Pi.smul_apply, smul_eq_mul] using valLt_mul_scalar scalar_ne first
  · right
    simpa only [Pi.smul_apply, smul_eq_mul] using valLt_mul_scalar scalar_ne last

private theorem exteriorSector1_smul (scalar : ℚ) (scalar_ne : scalar ≠ 0)
    {state : Fin 3 → ℚ} (sector : ExteriorSector1 state) :
    ExteriorSector1 (scalar • state) := by
  rcases sector with first | middle
  · left
    simpa only [Pi.smul_apply, smul_eq_mul] using valLt_mul_scalar scalar_ne first
  · right
    simpa only [Pi.smul_apply, smul_eq_mul] using valLt_mul_scalar scalar_ne middle

/-- Every regular normalized safe atom selects the sector indexed by its residue. -/
theorem safeExteriorAction_sector
    (β : Nat) (body : List TagLetter) (body_nonempty : body ≠ [])
    (label : TagLetter × Nat × Bool) (regular : RegularSafeLabel label)
    (state : Fin 3 → ℚ) (flag : ExteriorFlag state) :
    if label.2.2 then
      ExteriorSector1
        (safeExteriorAction ((3 : ℚ) ^ β) (nearySideLowerC β body)
          (nearySideLowerCScale β body) label *ᵥ state)
    else
      ExteriorSector0
        (safeExteriorAction ((3 : ℚ) ^ β) (nearySideLowerC β body)
          (nearySideLowerCScale β body) label *ᵥ state) := by
  have state_eq : state = ![state 0, state 1, state 2] := by
    funext i
    fin_cases i <;> rfl
  rw [state_eq] at flag ⊢
  obtain ⟨letter, j, residueOne⟩ := label
  cases letter <;> cases residueOne
  · simpa using safeExteriorAction_b_zero_flag β j
      (nearySideLowerC β body) (nearySideLowerCScale β body)
      (state 0) (state 1) (state 2) flag
  · exact safeExteriorAction_b_one_flag β j regular
      (nearySideLowerC β body) (nearySideLowerCScale β body)
      (state 0) (state 1) (state 2) flag
  · simpa using safeExteriorAction_c_zero_flag β j body
      (state 0) (state 1) (state 2) flag
  · exact safeExteriorAction_c_one_flag β j body body_nonempty
      (state 0) (state 1) (state 2) flag

/-- Every physical safe atom selects the same sector as its residue. -/
theorem safeExteriorTransition_sector
    (β : Nat) (body : List TagLetter) (body_nonempty : body ≠ [])
    (label : TagLetter × Nat × Bool) (regular : RegularSafeLabel label)
    (state : Fin 3 → ℚ) (flag : ExteriorFlag state) :
    if label.2.2 then
      ExteriorSector1 (exteriorTransition (residueTwoWallGenerator β body label) *ᵥ state)
    else
      ExteriorSector0 (exteriorTransition (residueTwoWallGenerator β body label) *ᵥ state) := by
  have normalized := safeExteriorAction_sector β body body_nonempty label regular state flag
  rw [exteriorTransition_residueTwoWallGenerator, Matrix.smul_mulVec]
  by_cases residueOne : label.2.2
  · simp only [residueOne, if_true] at normalized ⊢
    exact exteriorSector1_smul 3 (by norm_num) normalized
  · simp only [residueOne] at normalized ⊢
    exact exteriorSector0_smul 3 (by norm_num) normalized

/-- Every regular safe word preserves the normalized two-sector exterior flag. -/
theorem exteriorState_safe_word_flag
    (β : Nat) (body : List TagLetter) (body_nonempty : body ≠ [])
    (word : List (TagLetter × Nat × Bool))
    (regular : ∀ label ∈ word, RegularSafeLabel label) :
    ExteriorFlag (exteriorState (wordProduct (residueTwoWallGenerator β body) word)) := by
  induction word with
  | nil => simpa [wordProduct] using exteriorFlag_seed
  | cons head tail induction =>
      have tail_flag := induction (fun label member => regular label (by simp [member]))
      have head_sector := safeExteriorTransition_sector β body body_nonempty head
        (regular head (by simp)) _ tail_flag
      rw [wordProduct_cons, exteriorState_mul]
      split at head_sector
      · exact Or.inr head_sector
      · exact Or.inl head_sector

/-- The leftmost residue orients the exterior state of every nonempty regular safe word. -/
theorem exteriorState_safe_word_cons_sector
    (β : Nat) (body : List TagLetter) (body_nonempty : body ≠ [])
    (head : TagLetter × Nat × Bool) (tail : List (TagLetter × Nat × Bool))
    (regular : ∀ label ∈ head :: tail, RegularSafeLabel label) :
    if head.2.2 then
      ExteriorSector1
        (exteriorState (wordProduct (residueTwoWallGenerator β body) (head :: tail)))
    else
      ExteriorSector0
        (exteriorState (wordProduct (residueTwoWallGenerator β body) (head :: tail))) := by
  have tail_flag := exteriorState_safe_word_flag β body body_nonempty tail
    (fun label member => regular label (by simp [member]))
  rw [wordProduct_cons, exteriorState_mul]
  exact safeExteriorTransition_sector β body body_nonempty head
    (regular head (by simp)) _ tail_flag

/-- On the bridge wall, the leftmost residue fixes the strict orientation of the other two
coordinates. -/
theorem exteriorState_safe_word_wall_orientation
    (β : Nat) (body : List TagLetter) (body_nonempty : body ≠ [])
    (head : TagLetter × Nat × Bool) (tail : List (TagLetter × Nat × Bool))
    (regular : ∀ label ∈ head :: tail, RegularSafeLabel label)
    (wall : exteriorState
      (wordProduct (residueTwoWallGenerator β body) (head :: tail)) 0 = 0) :
    if head.2.2 then
      ValLt
        (exteriorState (wordProduct (residueTwoWallGenerator β body) (head :: tail)) 1)
        (exteriorState (wordProduct (residueTwoWallGenerator β body) (head :: tail)) 2)
    else
      ValLt
        (exteriorState (wordProduct (residueTwoWallGenerator β body) (head :: tail)) 2)
        (exteriorState (wordProduct (residueTwoWallGenerator β body) (head :: tail)) 1) := by
  have sector := exteriorState_safe_word_cons_sector β body body_nonempty head tail regular
  by_cases residueOne : head.2.2
  · simp only [residueOne, if_true] at sector ⊢
    rcases sector with first | middle
    · exact False.elim (first.1 wall)
    · exact middle
  · simp only [residueOne] at sector ⊢
    rcases sector with first | last
    · exact False.elim (first.1 wall)
    · exact last

/-- The first exterior coordinate of a physical residue-one `b` transition is its exact wound
functional. -/
theorem exteriorTransition_b_one_first
    (β j : Nat) (body : List TagLetter) (state : Fin 3 → ℚ) :
    (exteriorTransition (residueTwoWallGenerator β body (.b, j, true)) *ᵥ state) 0 =
      -12 * j * (((12 * (3 : ℚ) ^ β - 1) * (state 0 + state 2)) + 2 * state 1) := by
  rw [exteriorTransition_residueTwoWallGenerator, Matrix.smul_mulVec]
  norm_num [safeExteriorAction, Matrix.vecHead, Matrix.vecTail, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ]
  ring

/-- A regular residue-one `b` transition hits the bridge wall exactly when its wound functional
vanishes. -/
theorem exteriorTransition_b_one_first_eq_zero_iff
    (β j : Nat) (j_positive : 0 < j) (body : List TagLetter) (state : Fin 3 → ℚ) :
    (exteriorTransition (residueTwoWallGenerator β body (.b, j, true)) *ᵥ state) 0 = 0 ↔
      (12 * (3 : ℚ) ^ β - 1) * (state 0 + state 2) + 2 * state 1 = 0 := by
  rw [exteriorTransition_b_one_first]
  have coefficient_ne : (-12 : ℚ) * j ≠ 0 :=
    mul_ne_zero (by norm_num) (by exact_mod_cast Nat.ne_of_gt j_positive)
  constructor
  · exact fun product_zero => (mul_eq_zero.mp product_zero).resolve_left coefficient_ne
  · intro wound_zero
    rw [wound_zero, mul_zero]

end MatrixMortality.ParabolicBlade
