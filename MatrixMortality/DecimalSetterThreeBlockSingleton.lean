import MatrixMortality.DecimalSetterSingletonChamber

/-!
# Three-block decimal singleton frontier

The first resonant parser tail has an exact discrepancy coordinate. Over `R_c`, a physical
block with punctuated upper code `P`, lower code `V`, and upper length `k` produces quotient
`10^k μ / (P - V)`. This module uses that identity and the nonresonant root shells to classify
unit ancestry at depth two.
-/

namespace MatrixMortality.DecimalSetterBridgeRay

open MatrixMortality.DecimalSetterArithmetic
open MatrixMortality.DecimalSetterBridge
open MatrixMortality.DecimalSetterCarry
open MatrixMortality.DecimalSetterDepth
open MatrixMortality.DecimalSetterMatrix
open MatrixMortality.PadicValuation

/-- Exact parser ray of one block above the canonical `R_c` root. -/
theorem parsedRay_pair_ruleCRoot_eq
    {β : Nat} (β_pos : 0 < β) (body : List TagLetter)
    (next : List NearyTile) :
    parsedRay β body [next, DecimalSetterMinimumBody.ruleCRoot] =
      (upperBoundaryCode β DecimalSetterMinimumBody.ruleCRoot *
            (upperBoundaryCode β next - lowerBoundaryCode β body next) /
          DecimalSetterMatrix.marker β ^ 2,
        upperScale β next *
          upperBoundaryCode β DecimalSetterMinimumBody.ruleCRoot /
            DecimalSetterMatrix.marker β) := by
  let E := gap ((10 : ℚ) ^ β)
  let G := lift ((10 : ℚ) ^ β)
  let μ := DecimalSetterMatrix.marker β
  let H := upperBoundaryCode β DecimalSetterMinimumBody.ruleCRoot
  let P := upperBoundaryCode β next
  let V := lowerBoundaryCode β body next
  let A := upperScale β next
  have E_ne : E ≠ 0 := (gap_tenPow_hasDecimalShell β_pos).1.1
  have μ_ne : μ ≠ 0 := (marker_hasDecimalShell β_pos).1.1
  have H_eq : 9 * H = G := by
    simpa only [H, G] using DecimalSetterMinimumBody.ruleCRoot_code_calibration β
  have complement_eq : E = 9 * (10 * μ - H) := by
    have calibration := DecimalSetterMinimumBody.ruleCRoot_complement_calibration β
    have root_complement :
        upperBoundaryComplement β DecimalSetterMinimumBody.ruleCRoot = 10 * μ - H := by
      simp [upperBoundaryComplement, DecimalSetterMinimumBody.ruleCRoot,
        spell, nearyUpper, tagCode, μ, H]
      ring
    rw [root_complement] at calibration
    simpa only [E] using calibration.symm
  apply Prod.ext
  · simp only [parsedRay, rayStep, rootRay]
    change
      ((E * P + G * V) * (H / μ) - G * V * 10) / (E * μ) =
        H * (P - V) / μ ^ 2
    field_simp [E_ne, μ_ne]
    rw [← H_eq, complement_eq]
    ring
  · simp only [parsedRay, rayStep, rootRay]
    change A * (H / μ) = A * H / μ
    ring

/-- The quotient of the `R_c`-rooted two-block ray is the upper scale times the marker divided
by the block discrepancy. -/
theorem parsedRay_pair_ruleCRoot_ratio_eq
    {β : Nat} (β_pos : 0 < β) (body : List TagLetter)
    (next : List NearyTile)
    (discrepancy_ne :
      upperBoundaryCode β next - lowerBoundaryCode β body next ≠ 0) :
    (parsedRay β body [next, DecimalSetterMinimumBody.ruleCRoot]).2 /
        (parsedRay β body [next, DecimalSetterMinimumBody.ruleCRoot]).1 =
      upperScale β next * DecimalSetterMatrix.marker β /
        (upperBoundaryCode β next - lowerBoundaryCode β body next) := by
  rw [parsedRay_pair_ruleCRoot_eq β_pos]
  have root_ne :=
    (upperBoundaryCode_decimalUnit β_pos DecimalSetterMinimumBody.ruleCRoot).1.1
  have marker_ne := (marker_hasDecimalShell β_pos).1.1
  field_simp [root_ne, marker_ne, discrepancy_ne]

/-- Above `R_c`, unit peeled ancestry is exactly an equal-depth discrepancy one decimal place
shallower than the intervening block's upper scale. -/
theorem pair_ruleCRoot_admitsUnitPeeledCarrier_iff_discrepancyShell
    {β : Nat} (β_pos : 0 < β) (body : List TagLetter)
    (next : List NearyTile) :
    AdmitsUnitPeeledCarrier β
        (parsedRay β body [next, DecimalSetterMinimumBody.ruleCRoot]) ↔
      HasDecimalShell
        (upperBoundaryCode β next - lowerBoundaryCode β body next)
        ((spell (nearyUpper β) next).length - 1)
        ((spell (nearyUpper β) next).length - 1) := by
  let k := (spell (nearyUpper β) next).length
  let δ := upperBoundaryCode β next - lowerBoundaryCode β body next
  let numerator := upperScale β next * DecimalSetterMatrix.marker β
  have marker_unit := marker_hasDecimalShell β_pos
  have scale_shell : HasDecimalShell (upperScale β next) k k := by
    have shell := ten_hasDecimalShell.pow k
    norm_num at shell
    simpa only [upperScale, k] using shell
  have numerator_shell : HasDecimalShell numerator k k := by
    simpa only [numerator, add_zero] using scale_shell.mul marker_unit
  rw [admitsUnitPeeledCarrier_iff_ratio_hasDecimalShell β_pos]
  constructor
  · rintro ⟨ray_first_ne, ratio_shell⟩
    change HasDecimalShell δ (k - 1) (k - 1)
    have δ_ne : δ ≠ 0 := by
      intro δ_zero
      apply ray_first_ne
      rw [parsedRay_pair_ruleCRoot_eq β_pos]
      simp [δ_zero, δ]
    have ratio_eq :
        (parsedRay β body [next, DecimalSetterMinimumBody.ruleCRoot]).2 /
            (parsedRay β body [next, DecimalSetterMinimumBody.ruleCRoot]).1 =
          numerator / δ := by
      simpa only [numerator, δ] using
        parsedRay_pair_ruleCRoot_ratio_eq β_pos body next δ_ne
    have δ_eq : δ = numerator /
        ((parsedRay β body [next, DecimalSetterMinimumBody.ruleCRoot]).2 /
          (parsedRay β body [next, DecimalSetterMinimumBody.ruleCRoot]).1) := by
      rw [ratio_eq]
      field_simp [δ_ne, numerator_shell.1.1]
    rw [δ_eq]
    constructor
    · have shell := div_hasValue numerator_shell.1 ratio_shell.1
      simpa only [k, δ] using shell
    · have shell := div_hasValue numerator_shell.2 ratio_shell.2
      simpa only [k, δ] using shell
  · intro δ_shell
    change HasDecimalShell δ (k - 1) (k - 1) at δ_shell
    have δ_ne : δ ≠ 0 := by
      simpa only [δ] using δ_shell.1.1
    have ray_first_ne :
        (parsedRay β body [next, DecimalSetterMinimumBody.ruleCRoot]).1 ≠ 0 := by
      rw [parsedRay_pair_ruleCRoot_eq β_pos]
      exact div_ne_zero
        (mul_ne_zero
          (upperBoundaryCode_decimalUnit β_pos
            DecimalSetterMinimumBody.ruleCRoot).1.1 δ_ne)
        (pow_ne_zero 2 (marker_hasDecimalShell β_pos).1.1)
    refine ⟨ray_first_ne, ?_⟩
    rw [parsedRay_pair_ruleCRoot_ratio_eq β_pos body next δ_ne]
    constructor
    · have shell := div_hasValue numerator_shell.1 δ_shell.1
      norm_num [k] at shell ⊢
      exact shell
    · have shell := div_hasValue numerator_shell.2 δ_shell.2
      norm_num [k] at shell ⊢
      exact shell

/-- Exact three-block singleton equation over the resonant `R_c` root. The entire older tail
enters through the intervening block discrepancy. -/
theorem hitsSquarePole_singleton_pair_ruleCRoot_iff_discrepancyEquation
    {β : Nat} (β_pos : 0 < β) (body : List TagLetter)
    (targetLetter : TagLetter) (current next : List NearyTile) :
    HitsSquarePole β body [.erase targetLetter]
        [current, next, DecimalSetterMinimumBody.ruleCRoot] ↔
      (upperBoundaryCode β next - lowerBoundaryCode β body next) *
          (boundaryTrace β body current * singletonTrace β targetLetter -
            7 * gap ((10 : ℚ) ^ β) * DecimalSetterMatrix.marker β *
              lift ((10 : ℚ) ^ β) * upperScale β current) =
        lift ((10 : ℚ) ^ β) * lowerBoundaryCode β body current *
          upperScale β next * DecimalSetterMatrix.marker β *
            singletonTrace β targetLetter := by
  let E := gap ((10 : ℚ) ^ β)
  let G := lift ((10 : ℚ) ^ β)
  let μ := DecimalSetterMatrix.marker β
  let H := upperBoundaryCode β DecimalSetterMinimumBody.ruleCRoot
  let T := boundaryTrace β body current
  let V := lowerBoundaryCode β body current
  let A := upperScale β current
  let S := singletonTrace β targetLetter
  let δ := upperBoundaryCode β next - lowerBoundaryCode β body next
  let B := upperScale β next
  have H_ne :=
    (upperBoundaryCode_decimalUnit β_pos DecimalSetterMinimumBody.ruleCRoot).1.1
  have μ_ne := (marker_hasDecimalShell β_pos).1.1
  rw [hitsSquarePole_singleton_cons_iff_rayRecurrence β_pos]
  rw [parsedRay_pair_ruleCRoot_eq β_pos]
  change
    (T * (H * δ / μ ^ 2) - G * V * (B * H / μ)) * S =
        E * μ * G * A * (H * δ / μ ^ 2) * 7 ↔
      δ * (T * S - 7 * E * μ * G * A) = G * V * B * μ * S
  have coefficient_ne : H / μ ^ 2 ≠ 0 :=
    div_ne_zero H_ne (pow_ne_zero 2 μ_ne)
  constructor
  · intro equation
    have scaled :
        (H / μ ^ 2) * ((T * δ - μ * G * V * B) * S) =
          (H / μ ^ 2) * (E * μ * G * A * δ * 7) := by
      convert equation using 1 <;> field_simp [μ_ne]
    have core := mul_left_cancel₀ coefficient_ne scaled
    linear_combination core
  · intro equation
    have core :
        (T * δ - μ * G * V * B) * S = E * μ * G * A * δ * 7 := by
      linear_combination equation
    have scaled := congrArg (H / μ ^ 2 * ·) core
    convert scaled using 1 <;> field_simp [μ_ne]

/-- A multi-role erasure block above a root of upper depth at least two has quotient shell
`(k-1,k-1)`, where `k` is the block's upper length. -/
theorem pair_deepRoot_multi_ratio_hasDecimalShell
    {β : Nat} (β_large : 2 ≤ β) (body : List TagLetter)
    {next root : List NearyTile}
    (next_multi : 2 ≤ next.length) (next_ends : EndsInErase next)
    (root_deep : 2 ≤ (spell (nearyUpper β) root).length) :
    HasDecimalShell
      ((parsedRay β body [next, root]).2 / (parsedRay β body [next, root]).1)
      ((spell (nearyUpper β) next).length - 1)
      ((spell (nearyUpper β) next).length - 1) := by
  have β_pos : 0 < β := by omega
  let k := (spell (nearyUpper β) next).length
  let r := (spell (nearyUpper β) root).length
  let ray := rootRay β root
  let T := boundaryTrace β body next
  let V := lowerBoundaryCode β body next
  let E := gap ((10 : ℚ) ^ β)
  let G := lift ((10 : ℚ) ^ β)
  let μ := DecimalSetterMatrix.marker β
  let A := upperScale β next
  have trace_shell : HasDecimalShell T 1 1 := by
    simpa only [T, boundaryTrace] using
      DecimalSetterShallow.multiRoleErasureEnded_boundaryTrace_hasDecimalShell
        β_large body next_multi next_ends
  have lower_unit : HasDecimalShell V 0 0 := by
    simpa only [V] using
      lowerBoundaryCode_hasDecimalShell_of_endsInErase β body next_ends
  have root_first_unit : HasDecimalShell ray.1 0 0 := by
    simpa only [ray] using rootRay_fst_hasDecimalShell β_pos root
  have root_second_shell : HasDecimalShell ray.2 r r := by
    simpa only [ray, r] using rootRay_snd_hasDecimalShell β root
  have trace_term_shell : HasDecimalShell (T * ray.1) 1 1 := by
    simpa only [add_zero] using trace_shell.mul root_first_unit
  have lower_term_shell : HasDecimalShell (G * V * ray.2) r r := by
    simpa only [G, zero_add] using
      ((lift_tenPow_hasDecimalShell β_pos).mul lower_unit).mul root_second_shell
  have residual_shell : HasDecimalShell (T * ray.1 - G * V * ray.2) 1 1 := by
    constructor
    · have shell := sub_hasValue_min trace_term_shell.1.1 lower_term_shell.1.1 (by
        rw [trace_term_shell.1.2, lower_term_shell.1.2]
        omega)
      rw [trace_term_shell.1.2, lower_term_shell.1.2,
        min_eq_left (show (1 : ℤ) ≤ r by omega)] at shell
      exact shell
    · have shell := sub_hasValue_min trace_term_shell.2.1 lower_term_shell.2.1 (by
        rw [trace_term_shell.2.2, lower_term_shell.2.2]
        omega)
      rw [trace_term_shell.2.2, lower_term_shell.2.2,
        min_eq_left (show (1 : ℤ) ≤ r by omega)] at shell
      exact shell
  have denominator_unit : HasDecimalShell (E * μ) 0 0 := by
    simpa only [E, μ, zero_add] using
      (gap_tenPow_hasDecimalShell β_pos).mul (marker_hasDecimalShell β_pos)
  have first_shell :
      HasDecimalShell (rayStep β body next ray).1 1 1 := by
    simp only [rayStep]
    exact ⟨by simpa using div_hasValue residual_shell.1 denominator_unit.1,
      by simpa using div_hasValue residual_shell.2 denominator_unit.2⟩
  have scale_shell : HasDecimalShell A k k := by
    have shell := ten_hasDecimalShell.pow k
    norm_num at shell
    simpa only [A, upperScale, k] using shell
  have second_shell :
      HasDecimalShell (rayStep β body next ray).2 k k := by
    convert scale_shell.mul root_first_unit using 1 <;> simp [rayStep, A]
  have ratio_shell :
      HasDecimalShell
        ((rayStep β body next ray).2 / (rayStep β body next ray).1)
        (k - 1) (k - 1) :=
    ⟨by simpa using div_hasValue second_shell.1 first_shell.1,
      by simpa using div_hasValue second_shell.2 first_shell.2⟩
  simpa only [parsedRay, ray] using ratio_shell

/-- In the nonresonant-root chamber, unit ancestry occurs exactly when the intervening
multi-role block has two upper digits. -/
theorem pair_deepRoot_multi_admitsUnitPeeledCarrier_iff_upperLength_eq_two
    {β : Nat} (β_large : 2 ≤ β) (body : List TagLetter)
    {next root : List NearyTile}
    (next_multi : 2 ≤ next.length) (next_ends : EndsInErase next)
    (root_deep : 2 ≤ (spell (nearyUpper β) root).length) :
    AdmitsUnitPeeledCarrier β (parsedRay β body [next, root]) ↔
      (spell (nearyUpper β) next).length = 2 := by
  have β_pos : 0 < β := by omega
  have ratio_shell := pair_deepRoot_multi_ratio_hasDecimalShell
    β_large body next_multi next_ends root_deep
  rw [admitsUnitPeeledCarrier_iff_ratio_hasDecimalShell β_pos]
  constructor
  · rintro ⟨_, unit_shell⟩
    have cast_length :
        ((spell (nearyUpper β) next).length : ℤ) - 1 = 1 :=
      ratio_shell.1.2.symm.trans unit_shell.1.2
    omega
  · intro upper_length
    have first_ne : (parsedRay β body [next, root]).1 ≠ 0 := by
      intro first_zero
      apply ratio_shell.1.1
      simp [first_zero]
    refine ⟨first_ne, ?_⟩
    norm_num [upper_length] at ratio_shell ⊢
    exact ratio_shell

/-- A multi-role block with two upper digits consists of exactly two `c`-roles. -/
theorem multi_upperLength_two_shape
    {β : Nat} (β_pos : 0 < β) {next : List NearyTile}
    (next_multi : 2 ≤ next.length)
    (upper_length : (spell (nearyUpper β) next).length = 2) :
    next.length = 2 ∧ next.map NearyTile.letter = [.c, .c] := by
  have upper_short : (spell (nearyUpper β) next).length ≤ β + 2 := by omega
  obtain ⟨letters_all_c, next_width⟩ :=
    shortMulti_upperLetters_allC β next_multi upper_short
  have upper_eq_width : (spell (nearyUpper β) next).length = next.length := by
    rw [spell_nearyUpper,
      DecimalSetterAncestry.tagEncode_length_eq_roleLength_add_markerCount,
      letters_all_c]
    simp [List.count_replicate]
  have next_length : next.length = 2 := by omega
  exact ⟨next_length, by simpa [next_length] using letters_all_c⟩

/-- In the nonresonant-root chamber, an actual singleton pole forces the intervening block to
be two `c`-roles and the current multi-role block into the long unit-ancestry corridor. -/
theorem singletonPole_threeBlock_deepRoot_multi_classifier
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current next root : List NearyTile}
    (current_multi : 2 ≤ current.length) (current_ends : EndsInErase current)
    (next_multi : 2 ≤ next.length) (next_ends : EndsInErase next)
    (root_deep : 2 ≤ (spell (nearyUpper β) root).length)
    (pole : HitsSquarePole β body [.erase targetLetter] [current, next, root]) :
    next.length = 2 ∧ next.map NearyTile.letter = [.c, .c] ∧
      β + 3 ≤ (spell (nearyUpper β) current).length := by
  have β_pos : 0 < β := by omega
  let k := (spell (nearyUpper β) next).length
  let m := (spell (nearyUpper β) current).length
  let ray := parsedRay β body [next, root]
  let T := boundaryTrace β body current
  let V := lowerBoundaryCode β body current
  let E := gap ((10 : ℚ) ^ β)
  let G := lift ((10 : ℚ) ^ β)
  let μ := DecimalSetterMatrix.marker β
  let A := upperScale β current
  let S := singletonTrace β targetLetter
  have next_length_le_upper : next.length ≤ k := by
    dsimp only [k]
    rw [spell_nearyUpper]
    simpa using DecimalSetterChamber.length_le_tagEncode β (next.map NearyTile.letter)
  have k_two_le : 2 ≤ k := next_multi.trans next_length_le_upper
  have ratio_shell : HasDecimalShell (ray.2 / ray.1) (k - 1) (k - 1) := by
    simpa only [ray, k] using
      pair_deepRoot_multi_ratio_hasDecimalShell
        (show 2 ≤ β by omega) body next_multi next_ends root_deep
  have root_first_unit := rootRay_fst_hasDecimalShell β_pos root
  have scale_shell : HasDecimalShell (upperScale β next) k k := by
    have shell := ten_hasDecimalShell.pow k
    norm_num at shell
    simpa only [upperScale, k] using shell
  have ray_second_shell : HasDecimalShell ray.2 k k := by
    have shell := scale_shell.mul root_first_unit
    convert shell using 1 <;> simp [ray, parsedRay, rayStep]
  have ray_first_eq : ray.1 = ray.2 / (ray.2 / ray.1) := by
    have first_ne : ray.1 ≠ 0 := by
      intro first_zero
      apply ratio_shell.1.1
      simp [first_zero]
    have second_ne : ray.2 ≠ 0 := ray_second_shell.1.1
    field_simp [first_ne, second_ne]
  have ray_first_shell : HasDecimalShell ray.1 1 1 := by
    rw [ray_first_eq]
    have depth : (k : ℤ) - (k - 1) = 1 := by omega
    constructor
    · have shell := div_hasValue ray_second_shell.1 ratio_shell.1
      simpa only [depth] using shell
    · have shell := div_hasValue ray_second_shell.2 ratio_shell.2
      simpa only [depth] using shell
  have upper_length : k = 2 := by
    by_contra k_ne_two
    have k_three_le : 3 ≤ k := by omega
    have trace_shell : HasDecimalShell T 1 1 := by
      simpa only [T, boundaryTrace] using
        DecimalSetterShallow.multiRoleErasureEnded_boundaryTrace_hasDecimalShell
          (show 2 ≤ β by omega) body current_multi current_ends
    have lower_unit : HasDecimalShell V 0 0 := by
      simpa only [V] using
        lowerBoundaryCode_hasDecimalShell_of_endsInErase β body current_ends
    have trace_term_shell : HasDecimalShell (T * ray.1) 2 2 := by
      exact trace_shell.mul ray_first_shell
    have lower_term_shell : HasDecimalShell (G * V * ray.2) k k := by
      convert ((lift_tenPow_hasDecimalShell β_pos).mul lower_unit).mul ray_second_shell using 1 <;>
        simp
    have residual_shell :
        HasDecimalShell (T * ray.1 - G * V * ray.2) 2 2 := by
      constructor
      · have shell := sub_hasValue_min trace_term_shell.1.1 lower_term_shell.1.1 (by
          rw [trace_term_shell.1.2, lower_term_shell.1.2]
          omega)
        rw [trace_term_shell.1.2, lower_term_shell.1.2,
          min_eq_left (show (2 : ℤ) ≤ k by omega)] at shell
        exact shell
      · have shell := sub_hasValue_min trace_term_shell.2.1 lower_term_shell.2.1 (by
          rw [trace_term_shell.2.2, lower_term_shell.2.2]
          omega)
        rw [trace_term_shell.2.2, lower_term_shell.2.2,
          min_eq_left (show (2 : ℤ) ≤ k by omega)] at shell
        exact shell
    have target_shell : HasDecimalShell S (β + 1) β := by
      simpa only [S] using singletonTrace_hasDecimalShell β_pos targetLetter
    have left_shell :
        HasDecimalShell ((T * ray.1 - G * V * ray.2) * S)
          (β + 3) (β + 2) := by
      convert residual_shell.mul target_shell using 1 <;> omega
    have current_scale_shell : HasDecimalShell A m m := by
      have shell := ten_hasDecimalShell.pow m
      norm_num at shell
      simpa only [A, upperScale, m] using shell
    have seven_unit : HasDecimalShell (7 : ℚ) 0 0 :=
      intCast_hasDecimalShell_of_mod_seven (Int.ModEq.refl 7)
    have right_shell :
        HasDecimalShell (E * μ * G * A * ray.1 * 7) (m + 1) (m + 1) := by
      convert (((((gap_tenPow_hasDecimalShell β_pos).mul
        (marker_hasDecimalShell β_pos)).mul
          (lift_tenPow_hasDecimalShell β_pos)).mul current_scale_shell).mul
            ray_first_shell).mul seven_unit using 1 <;> simp
    have pole_equation :=
      (hitsSquarePole_singleton_cons_iff_rayRecurrence β_pos body targetLetter
        current next [root]).mp pole
    change (T * ray.1 - G * V * ray.2) * S = E * μ * G * A * ray.1 * 7 at pole_equation
    have two_balance := congrArg (padicValRat 2) pole_equation
    have five_balance := congrArg (padicValRat 5) pole_equation
    rw [left_shell.1.2, right_shell.1.2] at two_balance
    rw [left_shell.2.2, right_shell.2.2] at five_balance
    omega
  have ancestry : AdmitsUnitPeeledCarrier β (parsedRay β body [next, root]) :=
    (pair_deepRoot_multi_admitsUnitPeeledCarrier_iff_upperLength_eq_two
      (show 2 ≤ β by omega) body next_multi next_ends root_deep).mpr upper_length
  have current_long :=
    singletonPole_of_unitPeeledCarrier_forces_currentUpperLength
      (show 2 ≤ β by omega) body targetLetter [root] current_multi current_ends ancestry pole
  obtain ⟨next_length, next_letters⟩ :=
    multi_upperLength_two_shape β_pos next_multi upper_length
  exact ⟨next_length, next_letters, current_long⟩

/-- Over `R_c`, a multi-current three-block singleton pole is long exactly when the
intervening punctuated/lower discrepancy has equal depth `k-1`. -/
theorem singletonPole_threeBlock_ruleCRoot_multi_long_iff_discrepancyShell
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current next : List NearyTile}
    (current_multi : 2 ≤ current.length) (current_ends : EndsInErase current)
    (next_ends : EndsInErase next)
    (pole : HitsSquarePole β body [.erase targetLetter]
      [current, next, DecimalSetterMinimumBody.ruleCRoot]) :
    β + 3 ≤ (spell (nearyUpper β) current).length ↔
      HasDecimalShell
        (upperBoundaryCode β next - lowerBoundaryCode β body next)
        ((spell (nearyUpper β) next).length - 1)
        ((spell (nearyUpper β) next).length - 1) := by
  have β_pos : 0 < β := by omega
  have root_ends : EndsInRule DecimalSetterMinimumBody.ruleCRoot :=
    ⟨[], .c, by simp [DecimalSetterMinimumBody.ruleCRoot]⟩
  have tail_law :
      BlocksLaw [next, DecimalSetterMinimumBody.ruleCRoot] :=
    ⟨next_ends, root_ends⟩
  have ancestry_iff_long :=
    singletonPole_multiTail_admitsUnitPeeledCarrier_iff_currentLong
      β_large body targetLetter current_multi current_ends tail_law pole
  have ancestry_iff_discrepancy :=
    pair_ruleCRoot_admitsUnitPeeledCarrier_iff_discrepancyShell β_pos body next
  exact ancestry_iff_long.symm.trans ancestry_iff_discrepancy

/-- Exact A/B classifier for a lawful three-block singleton pole with multi-role current and
intervening blocks. A deep root forces the intervening block to be exactly two `c` roles and
the current into the long corridor. Otherwise the root is `R_c`; its discrepancy shell is
equivalent to the long corridor, while the complementary current is marker-free and all `c`. -/
theorem singletonPole_threeBlock_multi_classifier
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current next root : List NearyTile}
    (source_law : BlocksLaw [current, next, root])
    (current_multi : 2 ≤ current.length) (next_multi : 2 ≤ next.length)
    (pole : HitsSquarePole β body [.erase targetLetter] [current, next, root]) :
    (2 ≤ (spell (nearyUpper β) root).length ∧
      next.length = 2 ∧ next.map NearyTile.letter = [.c, .c] ∧
        β + 3 ≤ (spell (nearyUpper β) current).length) ∨
      (root = DecimalSetterMinimumBody.ruleCRoot ∧
        ((β + 3 ≤ (spell (nearyUpper β) current).length ∧
            HasDecimalShell
              (upperBoundaryCode β next - lowerBoundaryCode β body next)
              ((spell (nearyUpper β) next).length - 1)
              ((spell (nearyUpper β) next).length - 1)) ∨
          (current.length ≤ β + 2 ∧
            current.map NearyTile.letter = List.replicate current.length .c ∧
              ¬HasDecimalShell
                (upperBoundaryCode β next - lowerBoundaryCode β body next)
                ((spell (nearyUpper β) next).length - 1)
                ((spell (nearyUpper β) next).length - 1)))) := by
  have current_ends : EndsInErase current := source_law.1
  have next_ends : EndsInErase next := source_law.2.1
  have root_ends : EndsInRule root := source_law.2.2
  have root_upper_pos : 0 < (spell (nearyUpper β) root).length := by
    obtain ⟨front, letter, root_eq⟩ := root_ends
    have upper_ne : spell (nearyUpper β) root ≠ [] := by
      rw [root_eq, spell_append]
      simp [spell, nearyUpper_ne_nil]
    exact List.length_pos_of_ne_nil upper_ne
  by_cases root_deep : 2 ≤ (spell (nearyUpper β) root).length
  · obtain ⟨next_length, next_letters, current_long⟩ :=
      singletonPole_threeBlock_deepRoot_multi_classifier
        β_large body targetLetter current_multi current_ends next_multi next_ends root_deep pole
    exact Or.inl ⟨root_deep, next_length, next_letters, current_long⟩
  · have root_shallow : (spell (nearyUpper β) root).length = 1 := by omega
    have root_eq := ruleEnded_eq_ruleCRoot_of_upperLength_eq_one root_ends root_shallow
    subst root
    refine Or.inr ⟨rfl, ?_⟩
    let discrepancyShell :=
      HasDecimalShell
        (upperBoundaryCode β next - lowerBoundaryCode β body next)
        ((spell (nearyUpper β) next).length - 1)
        ((spell (nearyUpper β) next).length - 1)
    have long_iff_shell :
        β + 3 ≤ (spell (nearyUpper β) current).length ↔ discrepancyShell := by
      simpa only [discrepancyShell] using
        singletonPole_threeBlock_ruleCRoot_multi_long_iff_discrepancyShell
          β_large body targetLetter current_multi current_ends next_ends pole
    by_cases current_long : β + 3 ≤ (spell (nearyUpper β) current).length
    · exact Or.inl ⟨current_long, long_iff_shell.mp current_long⟩
    · have current_short : (spell (nearyUpper β) current).length ≤ β + 2 := by omega
      obtain ⟨letters_all_c, current_width⟩ :=
        shortMulti_upperLetters_allC β current_multi current_short
      have discrepancy_not_shell : ¬discrepancyShell := by
        intro discrepancy_shell
        exact current_long (long_iff_shell.mpr discrepancy_shell)
      exact Or.inr ⟨current_width, letters_all_c, discrepancy_not_shell⟩

/-- Every `R_c`-rooted three-block singleton pole has positive intervening discrepancy. -/
theorem singletonPole_threeBlock_ruleCRoot_discrepancy_pos
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current next : List NearyTile}
    (current_ends : EndsInErase current)
    (pole : HitsSquarePole β body [.erase targetLetter]
      [current, next, DecimalSetterMinimumBody.ruleCRoot]) :
    lowerBoundaryCode β body next < upperBoundaryCode β next := by
  let ρ : ℚ := 10 ^ β
  let E := gap ρ
  let G := lift ρ
  let μ := DecimalSetterMatrix.marker β
  let V := lowerBoundaryCode β body current
  let A := upperScale β current
  let T := boundaryTrace β body current
  let S := singletonTrace β targetLetter
  let B := upperScale β next
  let δ := upperBoundaryCode β next - lowerBoundaryCode β body next
  have β_pos : 0 < β := by omega
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
  have μ_pos : 0 < μ := by
    simpa only [μ] using DecimalSetterMatrix.marker_pos β
  have V_ne : V ≠ 0 := by
    simpa only [V] using
      (lowerBoundaryCode_hasDecimalShell_of_endsInErase β body current_ends).1.1
  have V_nonneg : 0 ≤ V := by simp [V, lowerBoundaryCode]
  have V_pos : 0 < V := lt_of_le_of_ne V_nonneg (Ne.symm V_ne)
  have B_pos : 0 < B := by simp [B, upperScale]
  have S_lower : 2 * ρ * G ≤ S := by
    simpa only [ρ, G, S] using
      two_mul_tenPow_lift_le_singletonTrace β_large targetLetter
  have S_pos : 0 < S := lt_of_lt_of_le (by positivity) S_lower
  have coefficient_pos : 0 < T * S - 7 * E * μ * G * A := by
    simpa only [T, S, E, μ, G, A, ρ] using
      erasureEnded_singletonCoefficient_pos β_large body targetLetter current_ends
  have exact_equation :=
    (hitsSquarePole_singleton_pair_ruleCRoot_iff_discrepancyEquation
      β_pos body targetLetter current next).mp pole
  change δ * (T * S - 7 * E * μ * G * A) = G * V * B * μ * S at exact_equation
  have discrepancy_pos : 0 < δ := by
    have right_pos : 0 < G * V * B * μ * S := by positivity
    nlinarith
  exact sub_pos.mp (by simpa only [δ] using discrepancy_pos)

/-- In the long `R_c`-resonant branch, the intervening lower word exhausts the entire
`k-1`-digit suffix of its punctuated upper word. The remaining `β+2`-digit head is a decimal
unit. -/
theorem singletonPole_threeBlock_ruleCRoot_long_suffix
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current next : List NearyTile}
    (current_multi : 2 ≤ current.length) (current_ends : EndsInErase current)
    (next_multi : 2 ≤ next.length) (next_ends : EndsInErase next)
    (current_long : β + 3 ≤ (spell (nearyUpper β) current).length)
    (pole : HitsSquarePole β body [.erase targetLetter]
      [current, next, DecimalSetterMinimumBody.ruleCRoot]) :
    let upperWord := spell (nearyUpper β) next ++ nearyMarker β
    let lowerWord := spell (nearyLower β body) next
    let width := (spell (nearyUpper β) next).length - 1
    lowerWord.length = width ∧ back width upperWord = lowerWord ∧
      code upperWord - code lowerWord = code (front width upperWord) * 10 ^ width ∧
        HasDecimalShell (code (front width upperWord) : ℚ) 0 0 := by
  let upperWord := spell (nearyUpper β) next ++ nearyMarker β
  let lowerWord := spell (nearyLower β body) next
  let k := (spell (nearyUpper β) next).length
  let width := k - 1
  let P := code upperWord
  let V := code lowerWord
  have β_pos : 0 < β := by omega
  have next_length_le_upper : next.length ≤ k := by
    dsimp only [k]
    rw [spell_nearyUpper]
    simpa using DecimalSetterChamber.length_le_tagEncode β (next.map NearyTile.letter)
  have k_two_le : 2 ≤ k := next_multi.trans next_length_le_upper
  have width_pos : 0 < width := by omega
  have discrepancy_pos : V < P := by
    have rational := singletonPole_threeBlock_ruleCRoot_discrepancy_pos
      β_large body targetLetter current_ends pole
    change (V : ℚ) < P at rational
    exact_mod_cast rational
  have difference_cast : (((P - V : Nat) : ℚ)) = (P : ℚ) - V := by
    rw [Nat.cast_sub discrepancy_pos.le]
  have discrepancy_shell :
      HasDecimalShell ((P : ℚ) - V) width width := by
    have raw :=
      (singletonPole_threeBlock_ruleCRoot_multi_long_iff_discrepancyShell
        β_large body targetLetter current_multi current_ends next_ends pole).mp current_long
    have width_cast : (width : ℤ) = (k : ℤ) - 1 := by omega
    simpa only [P, V, upperWord, lowerWord, upperBoundaryCode, lowerBoundaryCode,
      k, width, width_cast] using raw
  have difference_two_value : padicValNat 2 (P - V) = width := by
    have valuation := discrepancy_shell.1.2
    rw [← difference_cast, padicValRat.of_nat] at valuation
    exact_mod_cast valuation
  have difference_five_value : padicValNat 5 (P - V) = width := by
    have valuation := discrepancy_shell.2.2
    rw [← difference_cast, padicValRat.of_nat] at valuation
    exact_mod_cast valuation
  have two_power_dvd : 2 ^ width ∣ P - V := by
    apply (padicValNat_dvd_iff (p := 2) width (P - V)).mpr
    exact Or.inr (by rw [difference_two_value])
  have five_power_dvd : 5 ^ width ∣ P - V := by
    apply (padicValNat_dvd_iff (p := 5) width (P - V)).mpr
    exact Or.inr (by rw [difference_five_value])
  have ten_power_dvd : 10 ^ width ∣ P - V := by
    rw [show 10 ^ width = 2 ^ width * 5 ^ width by
      rw [show 10 = 2 * 5 by norm_num, mul_pow]]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
      ((by norm_num : Nat.Coprime 2 5).pow width width) two_power_dvd five_power_dvd
  have next_two_not_dvd : ¬2 ^ (width + 1) ∣ P - V := by
    intro next_dvd
    have valuation_bound :=
      (padicValNat_dvd_iff (p := 2) (width + 1) (P - V)).mp next_dvd
    rcases valuation_bound with difference_zero | valuation_bound
    · omega
    · rw [difference_two_value] at valuation_bound
      omega
  have two_power_exact : ¬2 * 10 ^ width ∣ P - V := by
    intro forbidden
    apply next_two_not_dvd
    apply dvd_trans _ forbidden
    refine ⟨5 ^ width, ?_⟩
    rw [pow_succ, show 10 ^ width = (2 * 5) ^ width by norm_num, mul_pow]
    ring
  have upper_length : upperWord.length = k + β + 1 := by
    simp [upperWord, k, nearyMarker]
    omega
  have width_lt_upper : width < upperWord.length := by omega
  obtain ⟨lower_length, suffix_eq, difference_front⟩ :=
    suffix_exhaustion_factorization upperWord lowerWord width width_pos width_lt_upper
      discrepancy_pos ten_power_dvd two_power_exact
  have difference_front_rat :
      (P : ℚ) - V = code (front width upperWord) * (10 : ℚ) ^ width := by
    rw [← difference_cast, difference_front]
    norm_num
  have scale_shell : HasDecimalShell ((10 : ℚ) ^ width) width width := by
    simpa using ten_hasDecimalShell.pow width
  have head_eq :
      (code (front width upperWord) : ℚ) =
        ((P : ℚ) - V) / (10 : ℚ) ^ width := by
    apply (eq_div_iff (pow_ne_zero width (by norm_num))).2
    simpa only [mul_comm] using difference_front_rat.symm
  have head_unit : HasDecimalShell (code (front width upperWord) : ℚ) 0 0 := by
    rw [head_eq]
    exact ⟨by simpa using div_hasValue discrepancy_shell.1 scale_shell.1,
      by simpa using div_hasValue discrepancy_shell.2 scale_shell.2⟩
  exact ⟨lower_length, suffix_eq, difference_front, head_unit⟩

/-- The unmatched prefix at depth `k-1` is the canonical `β+2`-digit peeled head. -/
theorem front_punctuatedUpper_eq_peeledHeadWord
    (β : Nat) {next : List NearyTile} (next_nonempty : next ≠ []) :
    front ((spell (nearyUpper β) next).length - 1)
        (spell (nearyUpper β) next ++ nearyMarker β) =
      peeledHeadWord β (next.map NearyTile.letter) := by
  have upper_nonempty : spell (nearyUpper β) next ≠ [] := by
    cases next with
    | nil => exact False.elim (next_nonempty rfl)
    | cons role rest => simp [spell, nearyUpper_ne_nil]
  have upper_pos : 0 < (spell (nearyUpper β) next).length := by
    have upper_length_ne : (spell (nearyUpper β) next).length ≠ 0 := by
      intro upper_length_zero
      exact upper_nonempty (List.length_eq_zero_iff.mp upper_length_zero)
    omega
  rw [spell_nearyUpper]
  rw [spell_nearyUpper] at upper_pos
  simp only [front, peeledHeadWord, punctuatedUpper,
    DecimalSetterChamber.markerWord, nearyMarker]
  congr 1
  simp
  omega

/-- The long `R_c` resonance cannot have a leading `b`. Its intervening role letters begin
with `c b` or `c c`, the two surviving peeled-head chambers. -/
theorem singletonPole_threeBlock_ruleCRoot_long_nextHead
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current next : List NearyTile}
    (current_multi : 2 ≤ current.length) (current_ends : EndsInErase current)
    (next_multi : 2 ≤ next.length) (next_ends : EndsInErase next)
    (current_long : β + 3 ≤ (spell (nearyUpper β) current).length)
    (pole : HitsSquarePole β body [.erase targetLetter]
      [current, next, DecimalSetterMinimumBody.ruleCRoot]) :
    (∃ tail, next.map NearyTile.letter = .c :: .b :: tail ∧
        peeledHeadWord β (next.map NearyTile.letter) = terminalHeadWord β) ∨
      ∃ tail fringe,
        next.map NearyTile.letter = .c :: .c :: tail ∧ fringe.length = β ∧
          peeledHeadWord β (next.map NearyTile.letter) = true :: true :: fringe := by
  let upperWord := spell (nearyUpper β) next ++ nearyMarker β
  let width := (spell (nearyUpper β) next).length - 1
  have suffix := singletonPole_threeBlock_ruleCRoot_long_suffix
    β_large body targetLetter current_multi current_ends next_multi next_ends current_long pole
  have head_unit : HasDecimalShell (code (front width upperWord) : ℚ) 0 0 := by
    simpa only [upperWord, width] using suffix.2.2.2
  have next_nonempty : next ≠ [] := by
    intro next_nil
    simp [next_nil] at next_multi
  have front_eq :
      front width upperWord = peeledHeadWord β (next.map NearyTile.letter) := by
    simpa only [upperWord, width] using
      front_punctuatedUpper_eq_peeledHeadWord β next_nonempty
  rw [front_eq] at head_unit
  have encoded_long : 2 ≤ (tagEncode β (next.map NearyTile.letter)).length := by
    rw [← spell_nearyUpper]
    have next_length_le_upper :
        next.length ≤ (spell (nearyUpper β) next).length := by
      rw [spell_nearyUpper]
      simpa using DecimalSetterChamber.length_le_tagEncode β (next.map NearyTile.letter)
    exact next_multi.trans next_length_le_upper
  rcases peeledHead_trichotomy encoded_long with leading_b | cb_or_cc
  · obtain ⟨tail, letters_eq, head_eq⟩ := leading_b
    rw [head_eq] at head_unit
    exact False.elim (bTag_not_decimalUnit β head_unit)
  · exact cb_or_cc

end MatrixMortality.DecimalSetterBridgeRay
