import MatrixMortality.DecimalSetterBridgeRay

/-!
# Decimal setter root rays and two-block singleton frontier

Unit peeled ancestry has a simple intrinsic meaning: the homogeneous parser quotient `y/x` lies
in decimal shell `(1,1)`. A physical root ray has shell `(m,m)`, where `m` is its upper spelling
length, so it enters the unit carrier exactly at `m=1`.

These facts close the first deep singleton slice of the outer parser. A singleton current block
cannot precede a singleton target over any root. If the current block is multi-role, the pole
equation forces the root to have `m=1`, hence parser law identifies it as `R_c`; the current upper
length is then at least `β+3`. The sole two-block survivor is therefore a long multi-role block
over the canonical `R_c` root.
-/

namespace MatrixMortality.DecimalSetterBridgeRay

open MatrixMortality.DecimalSetterArithmetic
open MatrixMortality.DecimalSetterBridge
open MatrixMortality.DecimalSetterCarry
open MatrixMortality.DecimalSetterDepth
open MatrixMortality.DecimalSetterMatrix
open MatrixMortality.PadicValuation

/-- Unit peeled coordinates exist exactly when the ray is numerator-nondegenerate and its
projective quotient has one factor of both two and five. -/
theorem admitsUnitPeeledCarrier_iff_ratio_hasDecimalShell
    {β : Nat} (β_pos : 0 < β) (ray : ℚ × ℚ) :
    AdmitsUnitPeeledCarrier β ray ↔
      ray.1 ≠ 0 ∧ HasDecimalShell (ray.2 / ray.1) 1 1 := by
  have marker_unit := marker_hasDecimalShell β_pos
  constructor
  · rintro ⟨N, D, N_unit, D_unit, ray_numerator_ne, represents⟩
    unfold RepresentsPeeledCarrier at represents
    have ratio_eq : ray.2 / ray.1 =
        (10 * DecimalSetterMatrix.marker β * D) / N := by
      field_simp [ray_numerator_ne, N_unit.1.1]
      linear_combination -represents
    have numerator_shell :
        HasDecimalShell (10 * DecimalSetterMatrix.marker β * D) 1 1 := by
      simpa only [add_zero, zero_add] using
        (ten_hasDecimalShell.mul marker_unit).mul D_unit
    refine ⟨ray_numerator_ne, ?_⟩
    rw [ratio_eq]
    exact ⟨by simpa using div_hasValue numerator_shell.1 N_unit.1,
      by simpa using div_hasValue numerator_shell.2 N_unit.2⟩
  · rintro ⟨ray_numerator_ne, ratio_shell⟩
    let N := 10 * DecimalSetterMatrix.marker β / (ray.2 / ray.1)
    have numerator_shell :
        HasDecimalShell (10 * DecimalSetterMatrix.marker β) 1 1 := by
      simpa only [add_zero] using ten_hasDecimalShell.mul marker_unit
    have N_unit : HasDecimalShell N 0 0 := by
      constructor
      · have shell := div_hasValue numerator_shell.1 ratio_shell.1
        norm_num at shell
        simpa only [N] using shell
      · have shell := div_hasValue numerator_shell.2 ratio_shell.2
        norm_num at shell
        simpa only [N] using shell
    have one_unit : HasDecimalShell (1 : ℚ) 0 0 :=
      ⟨⟨one_ne_zero, padicValRat.one⟩, ⟨one_ne_zero, padicValRat.one⟩⟩
    refine ⟨N, 1, N_unit, one_unit, ray_numerator_ne, ?_⟩
    have ray_denominator_ne : ray.2 ≠ 0 := by
      intro denominator_zero
      apply ratio_shell.1.1
      simp [denominator_zero]
    unfold RepresentsPeeledCarrier
    dsimp only [N]
    field_simp [ray_numerator_ne, ray_denominator_ne]

/-- The numerator coordinate of every physical root ray is a decimal unit. -/
theorem rootRay_fst_hasDecimalShell
    {β : Nat} (β_pos : 0 < β) (roles : List NearyTile) :
    HasDecimalShell (rootRay β roles).1 0 0 := by
  have marker_unit := marker_hasDecimalShell β_pos
  have upper_unit := upperBoundaryCode_decimalUnit β_pos roles
  constructor
  · have shell := div_hasValue upper_unit.1 marker_unit.1
    norm_num at shell
    simpa only [rootRay] using shell
  · have shell := div_hasValue upper_unit.2 marker_unit.2
    norm_num at shell
    simpa only [rootRay] using shell

/-- The denominator coordinate of a root ray has depth equal to its upper spelling length. -/
theorem rootRay_snd_hasDecimalShell
    (β : Nat) (roles : List NearyTile) :
    HasDecimalShell (rootRay β roles).2
      (spell (nearyUpper β) roles).length (spell (nearyUpper β) roles).length := by
  let m := (spell (nearyUpper β) roles).length
  have shell := ten_hasDecimalShell.pow m
  norm_num at shell
  simpa only [rootRay, upperScale, m] using shell

/-- A physical root ray has equal quotient depth given by its upper spelling length. -/
theorem rootRay_ratio_hasDecimalShell
    {β : Nat} (β_pos : 0 < β) (roles : List NearyTile) :
    HasDecimalShell ((rootRay β roles).2 / (rootRay β roles).1)
      (spell (nearyUpper β) roles).length (spell (nearyUpper β) roles).length := by
  have numerator_shell := rootRay_snd_hasDecimalShell β roles
  have denominator_unit := rootRay_fst_hasDecimalShell β_pos roles
  constructor
  · have shell := div_hasValue numerator_shell.1 denominator_unit.1
    norm_num at shell
    exact shell
  · have shell := div_hasValue numerator_shell.2 denominator_unit.2
    norm_num at shell
    exact shell

/-- A root ray admits unit peeled coordinates exactly when its upper spelling has one digit. -/
theorem rootRay_admitsUnitPeeledCarrier_iff_upperLength_eq_one
    {β : Nat} (β_pos : 0 < β) (roles : List NearyTile) :
    AdmitsUnitPeeledCarrier β (rootRay β roles) ↔
      (spell (nearyUpper β) roles).length = 1 := by
  have marker_unit := marker_hasDecimalShell β_pos
  have upper_unit := upperBoundaryCode_decimalUnit β_pos roles
  constructor
  · intro ancestry
    have ratio_shell :=
      (admitsUnitPeeledCarrier_iff_ratio_hasDecimalShell β_pos (rootRay β roles)).mp
        ancestry |>.2
    have root_shell := rootRay_ratio_hasDecimalShell β_pos roles
    have cast_length : ((spell (nearyUpper β) roles).length : ℤ) = 1 :=
      root_shell.1.2.symm.trans ratio_shell.1.2
    exact_mod_cast cast_length
  · intro upper_length
    apply (admitsUnitPeeledCarrier_iff_ratio_hasDecimalShell β_pos (rootRay β roles)).mpr
    refine ⟨?_, ?_⟩
    · simp [rootRay, upper_unit.1.1, marker_unit.1.1]
    · simpa [upper_length] using rootRay_ratio_hasDecimalShell β_pos roles

/-- Exact uncancelled recurrence equation for a singleton target over a current block and older
parser history. Unlike the peeled form, this identity requires no ancestry normalization. -/
theorem hitsSquarePole_singleton_cons_iff_rayRecurrence
    {β : Nat} (β_pos : 0 < β) (body : List TagLetter)
    (targetLetter : TagLetter) (current next : List NearyTile)
    (rest : List (List NearyTile)) :
    HitsSquarePole β body [.erase targetLetter] (current :: next :: rest) ↔
      (boundaryTrace β body current * (parsedRay β body (next :: rest)).1 -
          lift ((10 : ℚ) ^ β) * lowerBoundaryCode β body current *
            (parsedRay β body (next :: rest)).2) * singletonTrace β targetLetter =
        gap ((10 : ℚ) ^ β) * DecimalSetterMatrix.marker β *
          lift ((10 : ℚ) ^ β) * upperScale β current *
            (parsedRay β body (next :: rest)).1 * 7 := by
  have gap_ne := (gap_tenPow_hasDecimalShell β_pos).1.1
  have marker_ne := (marker_hasDecimalShell β_pos).1.1
  rw [hitsSquarePole_singleton_iff_rayEquation β_pos]
  simp only [parsedRay, rayStep]
  field_simp [gap_ne, marker_ne]

/-- Over the canonical `R_c` root, a singleton pole is exactly the target trace times the
current upper/lower code discrepancy. The target letter remains a parameter, and no parser or
block law is needed. -/
theorem hitsSquarePole_singleton_ruleCRoot_iff_traceDiscrepancy
    {β : Nat} (β_pos : 0 < β) (body : List TagLetter)
    (letter : TagLetter) (current : List NearyTile) :
    HitsSquarePole β body [.erase letter]
        [current, DecimalSetterMinimumBody.ruleCRoot] ↔
      singletonTrace β letter *
          (upperBoundaryCode β current - lowerBoundaryCode β body current) =
        7 * DecimalSetterMatrix.marker β * lift ((10 : ℚ) ^ β) *
          upperScale β current := by
  let ρ : ℚ := 10 ^ β
  let E := gap ρ
  let G := lift ρ
  let μ := DecimalSetterMatrix.marker β
  let H := upperBoundaryCode β DecimalSetterMinimumBody.ruleCRoot
  let P := upperBoundaryCode β current
  let V := lowerBoundaryCode β body current
  let A := upperScale β current
  let S := singletonTrace β letter
  have μ_ne : μ ≠ 0 := (marker_hasDecimalShell β_pos).1.1
  have H_ne : H ≠ 0 :=
    (upperBoundaryCode_decimalUnit β_pos DecimalSetterMinimumBody.ruleCRoot).1.1
  have E_ne : E ≠ 0 := (gap_tenPow_hasDecimalShell β_pos).1.1
  have H_eq : H = G / 9 := by
    have calibration := DecimalSetterMinimumBody.ruleCRoot_code_calibration β
    dsimp only [H, G, ρ]
    linarith
  have E_eq : E = 9 * (10 * μ - H) := by
    have calibration := DecimalSetterMinimumBody.ruleCRoot_complement_calibration β
    have complement_eq :
        upperBoundaryComplement β DecimalSetterMinimumBody.ruleCRoot =
          10 * μ - H := by
      simp [upperBoundaryComplement, DecimalSetterMinimumBody.ruleCRoot,
        spell, nearyUpper, tagCode, μ, H]
      ring
    rw [complement_eq] at calibration
    simpa only [E, ρ] using calibration.symm
  have raw := hitsSquarePole_singleton_cons_iff_rayRecurrence β_pos body letter current
    DecimalSetterMinimumBody.ruleCRoot []
  simp only [parsedRay] at raw
  rw [raw]
  dsimp only [rootRay, Prod.fst, Prod.snd]
  have root_scale : upperScale β DecimalSetterMinimumBody.ruleCRoot = 10 := by
    simp [upperScale, DecimalSetterMinimumBody.ruleCRoot, spell, nearyUpper, tagCode]
  rw [root_scale]
  change
    ((E * P + G * V) * (H / μ) - G * V * 10) * S =
        E * μ * G * A * (H / μ) * 7 ↔
      S * (P - V) = 7 * μ * G * A
  have coefficient_ne : E * H / μ ≠ 0 :=
    div_ne_zero (mul_ne_zero E_ne H_ne) μ_ne
  have scaled_identity :
      (((E * P + G * V) * (H / μ) - G * V * 10) * S -
        E * μ * G * A * (H / μ) * 7) =
          (E * H / μ) * (S * (P - V) - 7 * μ * G * A) := by
    field_simp [μ_ne]
    rw [E_eq, H_eq]
    ring
  constructor
  · intro equation
    have scaled_zero :
        (E * H / μ) * (S * (P - V) - 7 * μ * G * A) = 0 := by
      rw [← scaled_identity, equation, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp scaled_zero).resolve_left coefficient_ne)
  · intro equation
    have scaled_zero :
        (E * H / μ) * (S * (P - V) - 7 * μ * G * A) = 0 := by
      rw [sub_eq_zero.mpr equation, mul_zero]
    exact sub_eq_zero.mp (scaled_identity.trans scaled_zero)

/-- A singleton target over one multi-role erasure block and one lawful root forces the root's
upper spelling to have length one. Any other equal-depth root quotient leaves an incompatible
cross-prime shell after the current block. -/
theorem singletonPole_over_multi_root_forces_rootUpperLength_eq_one
    {β : Nat} (β_large : 2 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current root : List NearyTile}
    (current_multi : 2 ≤ current.length) (current_ends : EndsInErase current)
    (root_ends : EndsInRule root)
    (pole : HitsSquarePole β body [.erase targetLetter] [current, root]) :
    (spell (nearyUpper β) root).length = 1 := by
  have β_pos : 0 < β := by omega
  let m := (spell (nearyUpper β) root).length
  let k := (spell (nearyUpper β) current).length
  have m_pos : 0 < m := by
    obtain ⟨front, letter, root_eq⟩ := root_ends
    have upper_ne : spell (nearyUpper β) root ≠ [] := by
      rw [root_eq, spell_append]
      simp [spell, nearyUpper_ne_nil]
    have upper_length_ne : (spell (nearyUpper β) root).length ≠ 0 := by
      intro upper_length_zero
      exact upper_ne (List.length_eq_zero_iff.mp upper_length_zero)
    exact Nat.zero_lt_of_ne_zero upper_length_ne
  by_contra m_ne_one
  have one_lt_m : (1 : ℤ) < m := by omega
  have gap_unit := gap_tenPow_hasDecimalShell β_pos
  have lift_unit := lift_tenPow_hasDecimalShell β_pos
  have marker_unit := marker_hasDecimalShell β_pos
  have root_numerator_unit := rootRay_fst_hasDecimalShell β_pos root
  have root_denominator_shell : HasDecimalShell (rootRay β root).2 m m := by
    simpa only [m] using rootRay_snd_hasDecimalShell β root
  have current_trace_shell :=
    DecimalSetterShallow.multiRoleErasureEnded_boundaryTrace_hasDecimalShell
      β_large body current_multi current_ends
  have current_lower_unit :=
    lowerBoundaryCode_hasDecimalShell_of_endsInErase β body current_ends
  have trace_term_shell :
      HasDecimalShell
        (boundaryTrace β body current * (rootRay β root).1) 1 1 := by
    simpa only [boundaryTrace, add_zero] using current_trace_shell.mul root_numerator_unit
  have lower_term_shell :
      HasDecimalShell
        (lift ((10 : ℚ) ^ β) * lowerBoundaryCode β body current *
          (rootRay β root).2) m m := by
    simpa only [zero_add] using
      (lift_unit.mul current_lower_unit).mul root_denominator_shell
  have residual_shell :
      HasDecimalShell
        (boundaryTrace β body current * (rootRay β root).1 -
          lift ((10 : ℚ) ^ β) * lowerBoundaryCode β body current *
            (rootRay β root).2) 1 1 := by
    constructor
    · have shell := sub_hasValue_min trace_term_shell.1.1 lower_term_shell.1.1 (by
        rw [trace_term_shell.1.2, lower_term_shell.1.2]
        omega)
      rw [trace_term_shell.1.2, lower_term_shell.1.2,
        min_eq_left (le_of_lt one_lt_m)] at shell
      exact shell
    · have shell := sub_hasValue_min trace_term_shell.2.1 lower_term_shell.2.1 (by
        rw [trace_term_shell.2.2, lower_term_shell.2.2]
        omega)
      rw [trace_term_shell.2.2, lower_term_shell.2.2,
        min_eq_left (le_of_lt one_lt_m)] at shell
      exact shell
  have target_shell := singletonTrace_hasDecimalShell β_pos targetLetter
  have left_shell :
      HasDecimalShell
        ((boundaryTrace β body current * (rootRay β root).1 -
          lift ((10 : ℚ) ^ β) * lowerBoundaryCode β body current *
            (rootRay β root).2) * singletonTrace β targetLetter)
        (β + 2) (β + 1) := by
    have shell := residual_shell.mul target_shell
    have two_depth : (1 : ℤ) + (β + 1) = (β + 2 : Nat) := by omega
    have five_depth : (1 : ℤ) + β = (β + 1 : Nat) := by omega
    rw [two_depth, five_depth] at shell
    exact shell
  have scale_shell : HasDecimalShell (upperScale β current) k k := by
    have shell := ten_hasDecimalShell.pow k
    norm_num at shell
    simpa only [upperScale, k] using shell
  have seven_unit : HasDecimalShell (7 : ℚ) 0 0 :=
    intCast_hasDecimalShell_of_mod_seven (Int.ModEq.refl 7)
  have right_shell :
      HasDecimalShell
        (gap ((10 : ℚ) ^ β) * DecimalSetterMatrix.marker β *
          lift ((10 : ℚ) ^ β) * upperScale β current * (rootRay β root).1 * 7)
        k k := by
    simpa only [zero_add, add_zero] using
      ((((gap_unit.mul marker_unit).mul lift_unit).mul scale_shell).mul
        root_numerator_unit).mul seven_unit
  have pole_equation :=
    (hitsSquarePole_singleton_cons_iff_rayRecurrence β_pos body targetLetter current root []).mp
      pole
  simp only [parsedRay] at pole_equation
  have two_balance := congrArg (padicValRat 2) pole_equation
  have five_balance := congrArg (padicValRat 5) pole_equation
  rw [left_shell.1.2, right_shell.1.2] at two_balance
  rw [left_shell.2.2, right_shell.2.2] at five_balance
  omega

/-- The only rule-ended role block with one upper digit is the singleton `R_c` root. -/
theorem ruleEnded_eq_ruleCRoot_of_upperLength_eq_one
    {β : Nat} {root : List NearyTile}
    (root_ends : EndsInRule root)
    (upper_length : (spell (nearyUpper β) root).length = 1) :
    root = DecimalSetterMinimumBody.ruleCRoot := by
  have root_length_upper :
      root.length ≤ (spell (nearyUpper β) root).length := by
    rw [spell_nearyUpper]
    simpa using
      (DecimalSetterChamber.length_le_tagEncode β (root.map NearyTile.letter))
  obtain ⟨front, letter, root_eq⟩ := root_ends
  have front_nil : front = [] := by
    have front_length_le : front.length + 1 ≤ 1 := by
      calc
        front.length + 1 = root.length := by simp [root_eq]
        _ ≤ 1 := by simpa [upper_length] using root_length_upper
    exact List.length_eq_zero_iff.mp (by omega)
  have root_singleton : root = [.rule letter] := by
    simpa [front_nil] using root_eq
  cases letter with
  | b =>
      simp [root_singleton, spell, nearyUpper, tagCode] at upper_length
  | c => simp [root_singleton, DecimalSetterMinimumBody.ruleCRoot]

/-- A two-block singleton pole with multi-role current block has the canonical `R_c` root and
current upper length at least `β+3`. -/
theorem singletonPole_over_multi_root_currentShape
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current root : List NearyTile}
    (current_multi : 2 ≤ current.length) (current_ends : EndsInErase current)
    (root_ends : EndsInRule root)
    (pole : HitsSquarePole β body [.erase targetLetter] [current, root]) :
    root = DecimalSetterMinimumBody.ruleCRoot ∧
      β + 3 ≤ (spell (nearyUpper β) current).length := by
  have β_pos : 0 < β := by omega
  have root_length := singletonPole_over_multi_root_forces_rootUpperLength_eq_one
    (by omega) body targetLetter current_multi current_ends root_ends pole
  have root_eq := ruleEnded_eq_ruleCRoot_of_upperLength_eq_one root_ends root_length
  have ancestry : AdmitsUnitPeeledCarrier β (parsedRay β body [root]) := by
    simp only [parsedRay]
    exact (rootRay_admitsUnitPeeledCarrier_iff_upperLength_eq_one β_pos root).mpr root_length
  exact ⟨root_eq,
    singletonPole_of_unitPeeledCarrier_forces_currentUpperLength
      (by omega) body targetLetter [] current_multi current_ends ancestry pole⟩

/-- No singleton current block can precede a singleton target over any physical root ray. The
three possible comparisons between root depth and `β` are all incompatible with the equal-depth
right side of the pole equation. -/
theorem singletonPole_over_singleton_root_impossible
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter currentLetter : TagLetter) (root : List NearyTile) :
    ¬HitsSquarePole β body [.erase targetLetter] [[.erase currentLetter], root] := by
  intro pole
  have β_pos : 0 < β := by omega
  let m := (spell (nearyUpper β) root).length
  let k := (nearyUpper β (.erase currentLetter)).length
  have root_numerator_unit := rootRay_fst_hasDecimalShell β_pos root
  have root_denominator_shell : HasDecimalShell (rootRay β root).2 m m := by
    simpa only [m] using rootRay_snd_hasDecimalShell β root
  have current_trace_eq :
      boundaryTrace β body [.erase currentLetter] = singletonTrace β currentLetter := by
    simp [boundaryTrace, singletonTrace, lowerBoundaryCode, spell, nearyLower,
      code, digit, mul_comm]
  have current_trace_shell :
      HasDecimalShell (boundaryTrace β body [.erase currentLetter]) (β + 1) β := by
    rw [current_trace_eq]
    exact singletonTrace_hasDecimalShell β_pos currentLetter
  have current_lower_unit :=
    lowerBoundaryCode_hasDecimalShell_of_endsInErase β body
      (roles := [.erase currentLetter]) ⟨[], currentLetter, rfl⟩
  have lift_unit := lift_tenPow_hasDecimalShell β_pos
  have trace_term_shell :
      HasDecimalShell
        (boundaryTrace β body [.erase currentLetter] * (rootRay β root).1)
        (β + 1) β := by
    simpa only [add_zero] using current_trace_shell.mul root_numerator_unit
  have lower_term_shell :
      HasDecimalShell
        (lift ((10 : ℚ) ^ β) * lowerBoundaryCode β body [.erase currentLetter] *
          (rootRay β root).2) m m := by
    simpa only [zero_add] using
      (lift_unit.mul current_lower_unit).mul root_denominator_shell
  have target_shell := singletonTrace_hasDecimalShell β_pos targetLetter
  have gap_unit := gap_tenPow_hasDecimalShell β_pos
  have marker_unit := marker_hasDecimalShell β_pos
  have current_scale_shell : HasDecimalShell (upperScale β [.erase currentLetter]) k k := by
    have shell := ten_hasDecimalShell.pow k
    norm_num at shell
    simpa [upperScale, spell, k] using shell
  have seven_unit : HasDecimalShell (7 : ℚ) 0 0 :=
    intCast_hasDecimalShell_of_mod_seven (Int.ModEq.refl 7)
  have right_shell :
      HasDecimalShell
        (gap ((10 : ℚ) ^ β) * DecimalSetterMatrix.marker β *
          lift ((10 : ℚ) ^ β) * upperScale β [.erase currentLetter] *
            (rootRay β root).1 * 7) k k := by
    simpa only [zero_add, add_zero] using
      ((((gap_unit.mul marker_unit).mul lift_unit).mul current_scale_shell).mul
        root_numerator_unit).mul seven_unit
  have k_le : k ≤ β + 2 := by
    cases currentLetter <;> simp [k, nearyUpper, tagCode]
  have pole_equation :=
    (hitsSquarePole_singleton_cons_iff_rayRecurrence β_pos body targetLetter
      [.erase currentLetter] root []).mp pole
  simp only [parsedRay] at pole_equation
  rcases lt_trichotomy m β with m_lt_beta | m_eq_beta | beta_lt_m
  · have residual_two := sub_hasValue_min trace_term_shell.1.1 lower_term_shell.1.1 (by
      rw [trace_term_shell.1.2, lower_term_shell.1.2]
      omega)
    rw [trace_term_shell.1.2, lower_term_shell.1.2,
      min_eq_right (by omega)] at residual_two
    have residual_five := sub_hasValue_min trace_term_shell.2.1 lower_term_shell.2.1 (by
      rw [trace_term_shell.2.2, lower_term_shell.2.2]
      omega)
    rw [trace_term_shell.2.2, lower_term_shell.2.2,
      min_eq_right (by omega)] at residual_five
    have left_two := mul_hasValue residual_two target_shell.1
    have left_five := mul_hasValue residual_five target_shell.2
    have two_balance := congrArg (padicValRat 2) pole_equation
    have five_balance := congrArg (padicValRat 5) pole_equation
    rw [left_two.2, right_shell.1.2] at two_balance
    rw [left_five.2, right_shell.2.2] at five_balance
    omega
  · subst m
    have residual_two := sub_hasValue_min trace_term_shell.1.1 lower_term_shell.1.1 (by
      rw [trace_term_shell.1.2, lower_term_shell.1.2]
      omega)
    rw [trace_term_shell.1.2, lower_term_shell.1.2,
      min_eq_right (by omega)] at residual_two
    have left_two := mul_hasValue residual_two target_shell.1
    have two_balance := congrArg (padicValRat 2) pole_equation
    rw [left_two.2, right_shell.1.2] at two_balance
    omega
  · have residual_five := sub_hasValue_min trace_term_shell.2.1 lower_term_shell.2.1 (by
      rw [trace_term_shell.2.2, lower_term_shell.2.2]
      omega)
    rw [trace_term_shell.2.2, lower_term_shell.2.2,
      min_eq_left (by omega)] at residual_five
    have left_five := mul_hasValue residual_five target_shell.2
    have five_balance := congrArg (padicValRat 5) pole_equation
    rw [left_five.2, right_shell.2.2] at five_balance
    omega

/-- Complete parser-lawful classification of a singleton target over exactly two source blocks:
the current block is multi-role and long, and the root is exactly `R_c`. -/
theorem singletonPole_twoBlockSource_classifier
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current root : List NearyTile}
    (source_law : BlocksLaw [current, root])
    (pole : HitsSquarePole β body [.erase targetLetter] [current, root]) :
    root = DecimalSetterMinimumBody.ruleCRoot ∧ 2 ≤ current.length ∧
      β + 3 ≤ (spell (nearyUpper β) current).length := by
  have current_ends : EndsInErase current := source_law.1
  have root_ends : EndsInRule root := source_law.2
  have current_positive : 0 < current.length := by
    obtain ⟨front, currentLetter, current_eq⟩ := current_ends
    simp [current_eq]
  have current_length_ne_one : current.length ≠ 1 := by
    intro current_length
    obtain ⟨front, currentLetter, current_eq⟩ := current_ends
    have front_length : front.length = 0 := by
      simpa [current_eq] using current_length
    have front_nil : front = [] := List.length_eq_zero_iff.mp front_length
    have current_singleton : current = [.erase currentLetter] := by
      simpa [front_nil] using current_eq
    exact singletonPole_over_singleton_root_impossible
      β_large body targetLetter currentLetter root
        (by simpa [current_singleton] using pole)
  have current_multi : 2 ≤ current.length := by omega
  obtain ⟨root_eq, current_length⟩ := singletonPole_over_multi_root_currentShape
    β_large body targetLetter current_multi current_ends root_ends pole
  exact ⟨root_eq, current_multi, current_length⟩

end MatrixMortality.DecimalSetterBridgeRay
