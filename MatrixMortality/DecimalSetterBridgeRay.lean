import MatrixMortality.DecimalSetterShallow

/-!
# Decimal setter parser rays and singleton poles

The square-reset bridge recurrence has an exact homogeneous two-coordinate quotient. One role
block acts by a calibrated J-fraction step, and the quotient of `bridgeState` is therefore a
right-to-left parser ray. A singleton target hits exactly when its trace annihilates that ray.

If the older ray has nonzero decimal-unit peeled coordinates `N/(10μD)`, the matrix equation is
literally the recursive carrier equation used by the depth and ancestry modules. This condition
is not automatic: proving it for every relevant parser history is the remaining ancestry seam.
Under it, a deep singleton pole can occur only above a non-singleton current block with at least
`β+3` upper digits. A singleton target over one root block is impossible unconditionally.
-/

namespace MatrixMortality.DecimalSetterBridgeRay

open scoped Matrix

open MatrixMortality.DecimalSetterArithmetic
open MatrixMortality.DecimalSetterBridge
open MatrixMortality.DecimalSetterCarry
open MatrixMortality.DecimalSetterDepth
open MatrixMortality.DecimalSetterMatrix

/-- Projective numerator and denominator carried by a parsed bridge state. -/
def boundaryRay (β : Nat) (state : Fin 3 → ℚ) : ℚ × ℚ :=
  (state 0, state 0 + basisGap β * state 2)

/-- Complete decimal place scale of a role block's upper spelling. -/
def upperScale (β : Nat) (roles : List NearyTile) : ℚ :=
  10 ^ (spell (nearyUpper β) roles).length

/-- Calibrated transfer trace of a physical role block. -/
def boundaryTrace (β : Nat) (body : List TagLetter) (roles : List NearyTile) : ℚ :=
  gap (10 ^ β) * upperBoundaryCode β roles +
    lift (10 ^ β) * lowerBoundaryCode β body roles

/-- Homogeneous J-fraction step of one physical role block. -/
def rayStep (β : Nat) (body : List TagLetter) (roles : List NearyTile)
    (ray : ℚ × ℚ) : ℚ × ℚ :=
  ((boundaryTrace β body roles * ray.1 -
      lift (10 ^ β) * lowerBoundaryCode β body roles * ray.2) /
      (gap (10 ^ β) * DecimalSetterMatrix.marker β),
    upperScale β roles * ray.1)

/-- Boundary ray of one unsquared rightmost role block. -/
def rootRay (β : Nat) (roles : List NearyTile) : ℚ × ℚ :=
  (upperBoundaryCode β roles / DecimalSetterMatrix.marker β, upperScale β roles)

/-- Exact homogeneous J-fraction ray obtained by reading parsed blocks from right to left. -/
def parsedRay (β : Nat) (body : List TagLetter) :
    List (List NearyTile) → ℚ × ℚ
  | [] => (0, 0)
  | [roles] => rootRay β roles
  | roles :: next :: rest =>
      rayStep β body roles (parsedRay β body (next :: rest))

theorem boundaryRay_roleProduct_squareReset
    {β : Nat} (β_pos : 0 < β) (body : List TagLetter)
    (roles : List NearyTile) (state : Fin 3 → ℚ) :
    boundaryRay β
        (roleProduct β body roles *ᵥ squareReset β state) =
      rayStep β body roles (boundaryRay β state) := by
  rw [roleProduct_eq_conjugatedSide β_pos]
  apply Prod.ext
  · simp [boundaryRay, rayStep, boundaryTrace, upperScale,
      squareReset, upperBoundaryCode_eq, lowerBoundaryCode,
      sideBasis, sideBasisInv, sideMatrix, ratio, markerScale,
      Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_succ]
    rw [← basisGap_calibration, ← alpha_calibration]
    field_simp [ne_of_gt (marker_pos β), basisGap_ne_zero β_pos]
    rw [separatorScale]
    field_simp [ne_of_gt (marker_pos β)]
    ring
  · simp [boundaryRay, rayStep, boundaryTrace, upperScale,
      squareReset, upperBoundaryCode_eq, lowerBoundaryCode,
      sideBasis, sideBasisInv, sideMatrix, ratio, markerScale,
      Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_succ]
    field_simp [ne_of_gt (marker_pos β), basisGap_ne_zero β_pos]
    ring

/-- The recursive parsed ray is exactly the projective ray of `bridgeState`. -/
theorem boundaryRay_bridgeState
    {β : Nat} (β_pos : 0 < β) (body : List TagLetter)
    (blocks : List (List NearyTile)) :
    boundaryRay β (bridgeState β body blocks) = parsedRay β body blocks := by
  induction blocks with
  | nil => simp [boundaryRay, bridgeState, parsedRay]
  | cons roles tail induction =>
      cases tail with
      | nil =>
          rw [bridgeState_single_eq β_pos]
          apply Prod.ext
          · simp [boundaryRay, rootRay, parsedRay]
          · simp [boundaryRay, rootRay, parsedRay, upperBoundaryComplement,
              upperScale]
            field_simp [ne_of_gt (marker_pos β), basisGap_ne_zero β_pos]
            ring
      | cons next rest =>
          rw [bridgeState, boundaryRay_roleProduct_squareReset β_pos,
            induction]
          rfl

/-- Any parsed square-pole is exactly the vanishing of the first component after one physical
ray step. -/
theorem hitsSquarePole_iff_rayStep_fst_eq_zero
    {β : Nat} (β_pos : 0 < β) (body : List TagLetter)
    (target : List NearyTile) (source : List (List NearyTile)) :
    HitsSquarePole β body target source ↔
      (rayStep β body target (parsedRay β body source)).1 = 0 := by
  change
    (roleProduct β body target *ᵥ squareReset β (bridgeState β body source)) 0 = 0 ↔ _
  change
    (boundaryRay β
      (roleProduct β body target *ᵥ squareReset β (bridgeState β body source))).1 = 0 ↔ _
  rw [boundaryRay_roleProduct_squareReset β_pos,
    boundaryRay_bridgeState β_pos]

/-- Cross-multiplied parser-ray equation for an arbitrary target and block history. -/
theorem hitsSquarePole_iff_rayEquation
    {β : Nat} (β_pos : 0 < β) (body : List TagLetter)
    (target : List NearyTile) (source : List (List NearyTile)) :
    HitsSquarePole β body target source ↔
      boundaryTrace β body target * (parsedRay β body source).1 =
        lift (10 ^ β) * lowerBoundaryCode β body target *
          (parsedRay β body source).2 := by
  rw [hitsSquarePole_iff_rayStep_fst_eq_zero β_pos]
  have gap_ne : gap ((10 : ℚ) ^ β) ≠ 0 := by
    rw [← basisGap_calibration]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt (marker_pos β)))
      (basisGap_ne_zero β_pos)
  simp [rayStep, gap_ne, ne_of_gt (marker_pos β), sub_eq_zero]

/-- Trace of either physical singleton-erasure target. -/
def singletonTrace (β : Nat) (letter : TagLetter) : ℚ :=
  gap (10 ^ β) * upperBoundaryCode β [.erase letter] + 7 * lift (10 ^ β)

/-- The calibrated gap is a decimal unit at every positive width. -/
theorem gap_tenPow_hasDecimalShell {β : Nat} (β_pos : 0 < β) :
    HasDecimalShell (gap ((10 : ℚ) ^ β)) 0 0 := by
  have width_mod : (10 : ℤ) ^ β ≡ 0 [ZMOD 10] := by
    rw [Int.modEq_zero_iff_dvd]
    exact pow_dvd_pow (10 : ℤ) β_pos
  have gap_mod : decimalGap ((10 : ℤ) ^ β) ≡ 7 [ZMOD 10] := by
    calc
      decimalGap ((10 : ℤ) ^ β) = 18 * (10 : ℤ) ^ β - 63 := by
        simp [decimalGap]
        ring
      _ ≡ 18 * 0 - 63 [ZMOD 10] :=
        (Int.ModEq.refl 18).mul width_mod |>.sub (Int.ModEq.refl 63)
      _ ≡ 7 [ZMOD 10] := by norm_num
  simpa [gap, decimalGap] using intCast_hasDecimalShell_of_mod_seven gap_mod

/-- The calibrated lift is a decimal unit at every positive width. -/
theorem lift_tenPow_hasDecimalShell {β : Nat} (β_pos : 0 < β) :
    HasDecimalShell (lift ((10 : ℚ) ^ β)) 0 0 := by
  have width_mod : (10 : ℤ) ^ β ≡ 0 [ZMOD 10] := by
    rw [Int.modEq_zero_iff_dvd]
    exact pow_dvd_pow (10 : ℤ) β_pos
  have lift_mod : decimalLift ((10 : ℤ) ^ β) ≡ 3 [ZMOD 10] := by
    calc
      decimalLift ((10 : ℤ) ^ β) = 502 * (10 : ℤ) ^ β - 7 := by
        simp [decimalLift]
      _ ≡ 502 * 0 - 7 [ZMOD 10] :=
        (Int.ModEq.refl 502).mul width_mod |>.sub (Int.ModEq.refl 7)
      _ ≡ 3 [ZMOD 10] := by norm_num
  simpa [lift, decimalLift] using intCast_hasDecimalShell_of_mod_three lift_mod

/-- The matrix marker is a decimal unit at every positive width. -/
theorem marker_hasDecimalShell {β : Nat} (β_pos : 0 < β) :
    HasDecimalShell (DecimalSetterMatrix.marker β) 0 0 := by
  simpa [upperBoundaryCode, DecimalSetterMatrix.marker, spell] using
    (upperBoundaryCode_decimalUnit β_pos ([] : List NearyTile))

/-- Every erasure-ended physical block has a decimal-unit complete lower code. -/
theorem lowerBoundaryCode_hasDecimalShell_of_endsInErase
    (β : Nat) (body : List TagLetter) {roles : List NearyTile}
    (roles_ends : EndsInErase roles) :
    HasDecimalShell (lowerBoundaryCode β body roles) 0 0 := by
  obtain ⟨front, letter, rfl⟩ := roles_ends
  unfold lowerBoundaryCode
  rw [spell_append]
  simp only [spell]
  exact code_append_false_hasDecimalShell (spell (nearyLower β body) front)

/-- Either singleton-erasure target has the physical shell `(β+1,β)`. -/
theorem singletonTrace_hasDecimalShell {β : Nat} (β_pos : 0 < β)
    (letter : TagLetter) :
    HasDecimalShell (singletonTrace β letter) (β + 1) β := by
  have marker_eq : DecimalSetterMatrix.marker β =
      (52 * (10 : ℚ) ^ β - 7) / 9 := by
    have relation := DecimalSetterMatrix.marker_relation β
    linarith
  cases letter with
  | b =>
      have upper_eq : upperBoundaryCode β [.erase .b] =
          (10 * DecimalSetterMatrix.marker β + 5) * 10 ^ (β + 1) +
            DecimalSetterMatrix.marker β := by
        rw [upperBoundaryCode_eq]
        rw [show spell (nearyUpper β) [.erase .b] = tagCode β .b by
          simp [spell, nearyUpper]]
        rw [DecimalSetterMinimumBody.tagCodeB_code_eq]
        rfl
      have trace_eq : singletonTrace β .b =
          2 * (10 : ℚ) ^ β *
            (5200 * ((10 : ℚ) ^ β) ^ 2 - 18398 * (10 : ℚ) ^ β + 2443) := by
        rw [singletonTrace, upper_eq, marker_eq, pow_succ]
        unfold gap lift
        ring
      rw [trace_eq]
      simpa using singleBErasure_trace_hasDecimalShell β β_pos
  | c =>
      have upper_eq : upperBoundaryCode β [.erase .c] =
          5 * 10 ^ (β + 1) + DecimalSetterMatrix.marker β := by
        rw [upperBoundaryCode_eq]
        norm_num [spell, nearyUpper, tagCode, markerScale, code, digit]
      have trace_eq : singletonTrace β .c =
          2 * (10 : ℚ) ^ β * (502 * (10 : ℚ) ^ β - 7) := by
        rw [singletonTrace, upper_eq, marker_eq, pow_succ]
        unfold gap lift
        ring
      rw [trace_eq]
      simpa using singleCErasure_trace_hasDecimalShell β β_pos

/-- Exact arbitrary-history singleton criterion. The target letter enters only through its
upper boundary inside `singletonTrace`; every singleton lower code is seven. -/
theorem hitsSquarePole_singleton_iff_rayEquation
    {β : Nat} (β_pos : 0 < β) (body : List TagLetter)
    (letter : TagLetter) (source : List (List NearyTile)) :
    HitsSquarePole β body [.erase letter] source ↔
      singletonTrace β letter * (parsedRay β body source).1 =
        7 * lift (10 ^ β) * (parsedRay β body source).2 := by
  simpa [singletonTrace, boundaryTrace, lowerBoundaryCode, spell, nearyLower,
    code, digit, Nat.ofDigits, mul_assoc, mul_left_comm, mul_comm] using
    hitsSquarePole_iff_rayEquation β_pos body [.erase letter] source

/-- A singleton target cannot hit the square reset of one parser-lawful root block. This closes
the shallow slice of the outer singleton branch without assuming any distinguished raw head. -/
theorem singletonTarget_shallow_impossible
    {β : Nat} (β_pos : 0 < β) (body : List TagLetter)
    (letter : TagLetter) {source : List NearyTile} (source_ends : EndsInRule source) :
    ¬HitsSquarePole β body [.erase letter] [source] := by
  intro pole
  obtain ⟨raw_pole, source_unit, _⟩ :=
    (hitsSquarePole_single_iff_generalizedRawHead_with_units
      β_pos body [.erase letter] source source_ends).mp pole
  have lower_eq : lowerBoundaryCode β body [.erase letter] = 7 := by
    simp [lowerBoundaryCode, spell, nearyLower, code, digit]
  rw [lower_eq] at raw_pole
  let m := (spell (nearyUpper β) source).length
  have pole_equation :
      upperBoundaryCode β source * singletonTrace β letter =
        1 * lift ((10 : ℚ) ^ β) * DecimalSetterMatrix.marker β * 10 ^ m * 7 := by
    rw [upperBoundaryComplement] at raw_pole
    dsimp only [m]
    unfold singletonTrace
    linear_combination raw_pole
  have one_unit : HasDecimalShell (1 : ℚ) 0 0 :=
    ⟨⟨one_ne_zero, padicValRat.one⟩, ⟨one_ne_zero, padicValRat.one⟩⟩
  have seven_unit : HasDecimalShell (7 : ℚ) 0 0 :=
    intCast_hasDecimalShell_of_mod_seven (Int.ModEq.refl 7)
  exact resetZero_singleTarget_impossible source_unit
    (singletonTrace_hasDecimalShell β_pos letter) one_unit
    (lift_tenPow_hasDecimalShell β_pos) (marker_hasDecimalShell β_pos) seven_unit pole_equation

/-- A homogeneous parser ray represents the peeled carrier `N/(10μD)`. -/
def RepresentsPeeledCarrier (β : Nat) (ray : ℚ × ℚ) (N D : ℚ) : Prop :=
  ray.1 * (10 * DecimalSetterMatrix.marker β * D) = ray.2 * N

/-- The exact projective ancestry interface needed by the unit-carrier theorems: the parser ray
has a nonzero numerator and admits decimal-unit peeled coordinates. This predicate does not
assert that such coordinates exist for every parser history. -/
def AdmitsUnitPeeledCarrier (β : Nat) (ray : ℚ × ℚ) : Prop :=
  ∃ N D : ℚ,
    HasDecimalShell N 0 0 ∧ HasDecimalShell D 0 0 ∧ ray.1 ≠ 0 ∧
      RepresentsPeeledCarrier β ray N D

/-- `RepresentsPeeledCarrier` on the recursive parser is exactly the corresponding homogeneous
identity on the physical three-coordinate bridge state. -/
theorem bridgeState_representsPeeledCarrier_iff
    {β : Nat} (β_pos : 0 < β) (body : List TagLetter)
    (blocks : List (List NearyTile)) (N D : ℚ) :
    RepresentsPeeledCarrier β (parsedRay β body blocks) N D ↔
      bridgeState β body blocks 0 * (10 * DecimalSetterMatrix.marker β * D) =
        (bridgeState β body blocks 0 +
          basisGap β * bridgeState β body blocks 2) * N := by
  rw [← boundaryRay_bridgeState β_pos]
  rfl

/-- Exact bridge from the parser ray to the recursive peeled-carrier singleton equation. The
nonzero ray numerator and carrier numerator are precisely the cancellation hypotheses needed
to pass between homogeneous representatives. -/
theorem rayStep_singleton_after_block_iff_peeledEquation
    {β : Nat} (β_pos : 0 < β) (body : List TagLetter)
    (current : List NearyTile) (letter : TagLetter) (ray : ℚ × ℚ)
    {N D : ℚ} (represents : RepresentsPeeledCarrier β ray N D)
    (ray_numerator_ne : ray.1 ≠ 0) (carrier_numerator_ne : N ≠ 0) :
    (rayStep β body [.erase letter]
        (rayStep β body current ray)).1 = 0 ↔
      peeledNumerator N D (DecimalSetterMatrix.marker β) (lift (10 ^ β))
            (boundaryTrace β body current) (lowerBoundaryCode β body current) *
          singletonTrace β letter =
        gap (10 ^ β) * DecimalSetterMatrix.marker β * lift (10 ^ β) *
          upperScale β current * N * 7 := by
  have gap_ne : gap ((10 : ℚ) ^ β) ≠ 0 := by
    rw [← basisGap_calibration]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt (marker_pos β)))
      (basisGap_ne_zero β_pos)
  have marker_ne := ne_of_gt (marker_pos β)
  let n := ray.1
  let d := ray.2
  let μ := DecimalSetterMatrix.marker β
  let E := gap ((10 : ℚ) ^ β)
  let G := lift ((10 : ℚ) ^ β)
  let T := boundaryTrace β body current
  let V := lowerBoundaryCode β body current
  let A := upperScale β current
  let S := singletonTrace β letter
  have representation : n * (10 * μ * D) = d * N := represents
  have scaling_identity :
      N * (S * (T * n - G * V * d) - E * μ * G * 7 * A * n) =
        n * (S * peeledNumerator N D μ G T V - E * μ * G * A * N * 7) := by
    unfold peeledNumerator
    linear_combination S * G * V * representation
  have outer_zero_iff :
      (rayStep β body [.erase letter]
          (rayStep β body current ray)).1 = 0 ↔
        S * (T * n - G * V * d) - E * μ * G * 7 * A * n = 0 := by
    dsimp only [n, d, μ, E, G, T, V, A, S]
    simp only [rayStep]
    rw [show boundaryTrace β body [.erase letter] = singletonTrace β letter by
      simp [boundaryTrace, singletonTrace, lowerBoundaryCode, spell, nearyLower,
        code, digit, mul_comm]]
    simp [lowerBoundaryCode, spell, nearyLower, code, digit,
      gap_ne, marker_ne]
    field_simp [gap_ne, marker_ne]
    ring_nf
  rw [outer_zero_iff]
  constructor
  · intro outer_zero
    have scaled_zero :
        n * (S * peeledNumerator N D μ G T V - E * μ * G * A * N * 7) = 0 := by
      rw [← scaling_identity, outer_zero, mul_zero]
    have peeled_zero :
        S * peeledNumerator N D μ G T V - E * μ * G * A * N * 7 = 0 :=
      (mul_eq_zero.mp scaled_zero).resolve_left ray_numerator_ne
    simpa [n, d, μ, E, G, T, V, A, S, sub_eq_zero,
      mul_assoc, mul_left_comm, mul_comm] using peeled_zero
  · intro peeled_equation
    have peeled_zero :
        S * peeledNumerator N D μ G T V - E * μ * G * A * N * 7 = 0 := by
      simpa [n, d, μ, E, G, T, V, A, S, sub_eq_zero,
        mul_assoc, mul_left_comm, mul_comm] using peeled_equation
    have scaled_zero :
        N * (S * (T * n - G * V * d) - E * μ * G * 7 * A * n) = 0 := by
      rw [scaling_identity, peeled_zero, mul_zero]
    exact (mul_eq_zero.mp scaled_zero).resolve_left carrier_numerator_ne

/-- Parser-facing form of the peeled-carrier adapter. A singleton target over a current block
and a nonempty older history hits the square-reset pole exactly when the recursive singleton
equation holds for any nonzero peeled representative of the older parser ray. -/
theorem hitsSquarePole_singleton_cons_iff_peeledEquation
    {β : Nat} (β_pos : 0 < β) (body : List TagLetter)
    (letter : TagLetter) (current next : List NearyTile)
    (rest : List (List NearyTile)) {N D : ℚ}
    (represents :
      RepresentsPeeledCarrier β (parsedRay β body (next :: rest)) N D)
    (ray_numerator_ne : (parsedRay β body (next :: rest)).1 ≠ 0)
    (carrier_numerator_ne : N ≠ 0) :
    HitsSquarePole β body [.erase letter] (current :: next :: rest) ↔
      peeledNumerator N D (DecimalSetterMatrix.marker β) (lift (10 ^ β))
            (boundaryTrace β body current) (lowerBoundaryCode β body current) *
          singletonTrace β letter =
        gap (10 ^ β) * DecimalSetterMatrix.marker β * lift (10 ^ β) *
          upperScale β current * N * 7 := by
  rw [hitsSquarePole_iff_rayStep_fst_eq_zero β_pos]
  exact rayStep_singleton_after_block_iff_peeledEquation β_pos body current letter
    (parsedRay β body (next :: rest)) represents ray_numerator_ne carrier_numerator_ne

/-- Under unit peeled ancestry, no singleton-erasure block can itself precede a singleton
target in the parser history. -/
theorem singletonPole_of_unitPeeledCarrier_currentSingleton_impossible
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter currentLetter : TagLetter) (next : List NearyTile)
    (rest : List (List NearyTile))
    (ancestry : AdmitsUnitPeeledCarrier β (parsedRay β body (next :: rest))) :
    ¬HitsSquarePole β body [.erase targetLetter]
      ([.erase currentLetter] :: next :: rest) := by
  intro pole
  have β_pos : 0 < β := by omega
  obtain ⟨N, D, N_unit, D_unit, ray_numerator_ne, represents⟩ := ancestry
  have next_pole :=
    (hitsSquarePole_singleton_cons_iff_peeledEquation β_pos body targetLetter
      [.erase currentLetter] next rest represents ray_numerator_ne N_unit.1.1).mp pole
  have gap_unit := gap_tenPow_hasDecimalShell β_pos
  have lift_unit := lift_tenPow_hasDecimalShell β_pos
  have marker_unit := marker_hasDecimalShell β_pos
  have seven_unit : HasDecimalShell (7 : ℚ) 0 0 :=
    intCast_hasDecimalShell_of_mod_seven (Int.ModEq.refl 7)
  exact peeledSingletonToSingleton_impossible currentLetter β_large gap_unit lift_unit
    marker_unit N_unit D_unit seven_unit seven_unit
      (singletonTrace_hasDecimalShell β_pos currentLetter)
      (singletonTrace_hasDecimalShell β_pos targetLetter)
      (by simpa [boundaryTrace, singletonTrace, lowerBoundaryCode, upperScale,
        spell, nearyLower, code, digit, mul_assoc, mul_left_comm, mul_comm] using next_pole)

/-- A parser singleton pole above a non-singleton current block is already subject to the sharp
unit-carrier length wall. The sole additional ancestry hypothesis is that the older parser ray
admits nonzero decimal-unit peeled coordinates. -/
theorem singletonPole_of_unitPeeledCarrier_forces_currentUpperLength
    {β : Nat} (β_large : 2 ≤ β) (body : List TagLetter)
    (letter : TagLetter) {current next : List NearyTile}
    (rest : List (List NearyTile)) (current_multi : 2 ≤ current.length)
    (current_ends : EndsInErase current)
    (ancestry : AdmitsUnitPeeledCarrier β (parsedRay β body (next :: rest)))
    (pole : HitsSquarePole β body [.erase letter] (current :: next :: rest)) :
    β + 3 ≤ (spell (nearyUpper β) current).length := by
  have β_pos : 0 < β := by omega
  obtain ⟨N, D, N_unit, D_unit, ray_numerator_ne, represents⟩ := ancestry
  have next_pole :=
    (hitsSquarePole_singleton_cons_iff_peeledEquation β_pos body letter current next rest
      represents ray_numerator_ne N_unit.1.1).mp pole
  have gap_unit := gap_tenPow_hasDecimalShell β_pos
  have lift_unit := lift_tenPow_hasDecimalShell β_pos
  have marker_unit := marker_hasDecimalShell β_pos
  have current_lower_unit :=
    lowerBoundaryCode_hasDecimalShell_of_endsInErase β body current_ends
  have singleton_lower_unit : HasDecimalShell (7 : ℚ) 0 0 :=
    intCast_hasDecimalShell_of_mod_seven (Int.ModEq.refl 7)
  have current_trace_shell :=
    DecimalSetterShallow.multiRoleErasureEnded_boundaryTrace_hasDecimalShell
      β_large body current_multi current_ends
  have singleton_trace_shell := singletonTrace_hasDecimalShell β_pos letter
  exact peeledMultiToSingleton_beta_add_three_le gap_unit lift_unit marker_unit N_unit D_unit
    current_lower_unit singleton_lower_unit current_trace_shell singleton_trace_shell
      (by simpa [upperScale, boundaryTrace] using next_pole)

/-- Canonical conditional classifier for a deep parser singleton pole. If the intervening block
obeys the parser's erasure boundary law and the older ray admits unit peeled ancestry, then the
intervening block is non-singleton and has at least `β+3` upper digits. -/
theorem singletonPole_of_unitPeeledCarrier_currentShape
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current next : List NearyTile}
    (rest : List (List NearyTile)) (current_ends : EndsInErase current)
    (ancestry : AdmitsUnitPeeledCarrier β (parsedRay β body (next :: rest)))
    (pole : HitsSquarePole β body [.erase targetLetter] (current :: next :: rest)) :
    2 ≤ current.length ∧ β + 3 ≤ (spell (nearyUpper β) current).length := by
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
    exact singletonPole_of_unitPeeledCarrier_currentSingleton_impossible
      β_large body targetLetter currentLetter next rest ancestry
        (by simpa [current_singleton] using pole)
  have current_multi : 2 ≤ current.length := by omega
  exact ⟨current_multi,
    singletonPole_of_unitPeeledCarrier_forces_currentUpperLength
      (by omega) body targetLetter rest current_multi current_ends ancestry pole⟩

end MatrixMortality.DecimalSetterBridgeRay
