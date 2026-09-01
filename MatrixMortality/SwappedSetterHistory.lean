import MatrixMortality.SwappedSetterPhysicalShell

/-!
# Centered histories for the swapped setter

The first physical transfer lands on a special raw-head ray consumed by the local
multi-transfer theorems. A general later transfer does not. This file exposes the complete
homogeneous continuant of an arbitrary block history and proves the exact missing condition:
reusing a completed block as a fresh raw head is lawful precisely when the preceding history
has genuinely returned to the ordinary-reset ray.
-/

namespace MatrixMortality.SwappedSetterHistory

open SwappedSetterMultitransfer

/-- Homogeneous centered carrier. -/
@[ext] structure CenteredState where
  /-- Numerator-side centered coordinate. -/
  x : ℚ
  /-- Denominator-side centered coordinate. -/
  y : ℚ
  deriving DecidableEq

/-- Scalar action on a centered carrier. -/
def scaleState (scalar : ℚ) (state : CenteredState) : CenteredState :=
  ⟨scalar * state.x, scalar * state.y⟩

/-- Ordinary projective reset. -/
def ordinaryReset (width : Nat) : CenteredState :=
  ⟨1, centeredCoefficient width * setterMarker width⟩

/-- Distinguished projective reset. -/
def distinguishedReset (width : Nat) : CenteredState :=
  ⟨3, centeredCoefficient width * terminalDiscrepancy width⟩

/-- Canonical raw-head carrier produced by the first physical transfer. -/
def rawHeadState (width : Nat) (block : List NearyTile) : CenteredState :=
  ⟨3 ^ upperLength width block,
    centeredCoefficient width * swappedUpperCode width block⟩

/-- One physical centered transfer. -/
def blockStep (width : Nat) (body : List TagLetter)
    (block : List NearyTile) (state : CenteredState) : CenteredState :=
  ⟨nextX (3 ^ upperLength width block) state.y,
    nextY (blockCoefficient width body block) (centeredCoupling width)
      (swappedLowerCode width body block) state.x state.y⟩

/-- Left-to-right centered fold of a physical block history. -/
def historyState (width : Nat) (body : List TagLetter)
    (initial : CenteredState) (history : List (List NearyTile)) : CenteredState :=
  history.foldl (fun state block => blockStep width body block state) initial

/-- Four coefficients of the homogeneous linear action of a block history. -/
structure CenteredContinuant where
  /-- Contribution of the incoming `x` coordinate to the outgoing `x`. -/
  xx : ℚ
  /-- Contribution of the incoming `y` coordinate to the outgoing `x`. -/
  xy : ℚ
  /-- Contribution of the incoming `x` coordinate to the outgoing `y`. -/
  yx : ℚ
  /-- Contribution of the incoming `y` coordinate to the outgoing `y`. -/
  yy : ℚ

/-- Identity history continuant. -/
def identityContinuant : CenteredContinuant :=
  ⟨1, 0, 0, 1⟩

/-- Action of a history continuant on a centered carrier. -/
def CenteredContinuant.act (continuant : CenteredContinuant)
    (state : CenteredState) : CenteredState :=
  ⟨continuant.xx * state.x + continuant.xy * state.y,
    continuant.yx * state.x + continuant.yy * state.y⟩

/-- Append one physical block to a history continuant. -/
def CenteredContinuant.advance (width : Nat) (body : List TagLetter)
    (continuant : CenteredContinuant) (block : List NearyTile) : CenteredContinuant :=
  let scale : ℚ := 3 ^ upperLength width block
  let coefficient : ℚ := blockCoefficient width body block
  let transfer : ℚ := centeredCoupling width * swappedLowerCode width body block
  ⟨scale * continuant.yx, scale * continuant.yy,
    transfer * continuant.xx + coefficient * continuant.yx,
    transfer * continuant.xy + coefficient * continuant.yy⟩

/-- Exact continuant of a physical block history. -/
def historyContinuant (width : Nat) (body : List TagLetter)
    (history : List (List NearyTile)) : CenteredContinuant :=
  history.foldl (CenteredContinuant.advance width body) identityContinuant

@[simp] theorem identityContinuant_act (state : CenteredState) :
    identityContinuant.act state = state := by
  ext <;> simp [identityContinuant, CenteredContinuant.act]

theorem CenteredContinuant.advance_act
    (width : Nat) (body : List TagLetter) (continuant : CenteredContinuant)
    (block : List NearyTile) (state : CenteredState) :
    (continuant.advance width body block).act state =
      blockStep width body block (continuant.act state) := by
  ext <;>
    simp [CenteredContinuant.advance, CenteredContinuant.act, blockStep,
      nextX, nextY] <;>
    ring

private theorem historyContinuant_act_aux
    (width : Nat) (body : List TagLetter) (history : List (List NearyTile))
    (continuant : CenteredContinuant) (state : CenteredState) :
    (history.foldl (CenteredContinuant.advance width body) continuant).act state =
      history.foldl (fun live block => blockStep width body block live)
        (continuant.act state) := by
  induction history generalizing continuant with
  | nil => rfl
  | cons block history induction =>
      simp only [List.foldl_cons]
      rw [induction, CenteredContinuant.advance_act]

/-- The continuant is the exact homogeneous action of the complete history. -/
theorem historyContinuant_act
    (width : Nat) (body : List TagLetter) (history : List (List NearyTile))
    (state : CenteredState) :
    (historyContinuant width body history).act state =
      historyState width body state history := by
  rw [historyContinuant, historyState,
    historyContinuant_act_aux width body history identityContinuant state,
    identityContinuant_act]

@[simp] theorem scaleState_x (scalar : ℚ) (state : CenteredState) :
    (scaleState scalar state).x = scalar * state.x := rfl

@[simp] theorem scaleState_y (scalar : ℚ) (state : CenteredState) :
    (scaleState scalar state).y = scalar * state.y := rfl

/-- A centered transfer respects homogeneous rescaling. -/
theorem blockStep_scale (width : Nat) (body : List TagLetter)
    (block : List NearyTile) (scalar : ℚ) (state : CenteredState) :
    blockStep width body block (scaleState scalar state) =
      scaleState scalar (blockStep width body block state) := by
  ext <;> simp [blockStep, scaleState, nextX, nextY] <;> ring

/-- The first physical transfer from the ordinary reset is the canonical raw-head state, up to
its fixed nonzero projective scale. -/
theorem blockStep_ordinaryReset
    (width : Nat) (body : List TagLetter) (block : List NearyTile) :
    blockStep width body block (ordinaryReset width) =
      scaleState (centeredCoefficient width * setterMarker width)
        (rawHeadState width block) := by
  ext <;>
    simp [blockStep, ordinaryReset, rawHeadState, scaleState, nextX, nextY,
      blockCoefficient, centeredCoupling] <;>
    ring

/-- Homogeneous equation cutting out the ordinary-reset ray. -/
def ordinaryDefect (width : Nat) (state : CenteredState) : ℚ :=
  state.y - centeredCoefficient width * setterMarker width * state.x

/-- Homogeneous equation cutting out the canonical raw-head ray of one block. -/
def rawHeadDefect (width : Nat) (block : List NearyTile)
    (state : CenteredState) : ℚ :=
  3 ^ upperLength width block * state.y -
    centeredCoefficient width * swappedUpperCode width block * state.x

/-- A physical step transports its incoming ordinary-reset defect exactly to its outgoing
raw-head defect. This factor is the complete history dependence suppressed by a sliding-window
argument. -/
theorem rawHeadDefect_blockStep
    (width : Nat) (body : List TagLetter) (block : List NearyTile)
    (state : CenteredState) :
    rawHeadDefect width block (blockStep width body block state) =
      -(3 ^ upperLength width block * terminalDiscrepancy width *
          swappedLowerCode width body block) * ordinaryDefect width state := by
  simp [rawHeadDefect, blockStep, ordinaryDefect, nextX, nextY,
    blockCoefficient, centeredCoupling]
  ring

/-- One step sends the ordinary-ray defect through the same affine denominator pencil, with the
upper scale shifted from the punctuated code. -/
theorem ordinaryDefect_blockStep
    (width : Nat) (body : List TagLetter) (block : List NearyTile)
    (state : CenteredState) :
    ordinaryDefect width (blockStep width body block state) =
      centeredCoefficient width *
          (swappedUpperCode width block -
            setterMarker width * (3 : ℚ) ^ upperLength width block) * state.y -
        terminalDiscrepancy width * swappedLowerCode width body block *
          ordinaryDefect width state := by
  simp [ordinaryDefect, blockStep, nextX, nextY, blockCoefficient,
    centeredCoupling]
  ring

private theorem widthScale_ge_nine
    {width : Nat} (width_two : 2 ≤ width) :
    (9 : ℤ) ≤ widthScale width := by
  have power_le : 3 ^ 2 ≤ 3 ^ width :=
    Nat.pow_le_pow_right (by norm_num) width_two
  have nine_le : 9 ≤ 3 ^ width := by
    norm_num at power_le ⊢
    exact power_le
  change (9 : ℤ) ≤ (3 : ℤ) ^ width
  exact_mod_cast nine_le

private theorem centeredCoefficient_ne_zero
    {width : Nat} (width_two : 2 ≤ width) :
    (centeredCoefficient width : ℚ) ≠ 0 := by
  have scale_ge := widthScale_ge_nine width_two
  exact_mod_cast (by simp [centeredCoefficient]; omega : centeredCoefficient width ≠ 0)

private theorem setterMarker_ne_zero
    {width : Nat} (width_two : 2 ≤ width) :
    (setterMarker width : ℚ) ≠ 0 := by
  have scale_ge := widthScale_ge_nine width_two
  exact_mod_cast (by simp [setterMarker]; omega : setterMarker width ≠ 0)

private theorem terminalDiscrepancy_ne_zero
    {width : Nat} (width_two : 2 ≤ width) :
    (terminalDiscrepancy width : ℚ) ≠ 0 := by
  have scale_ge := widthScale_ge_nine width_two
  exact_mod_cast (by simp [terminalDiscrepancy]; omega : terminalDiscrepancy width ≠ 0)

/-- A completed block lies on its canonical raw-head ray exactly when its incoming carrier lies
on the ordinary-reset ray. Thus a later block can be re-used as a fresh first block only after
an actual projective reset return. -/
theorem rawHeadDefect_blockStep_eq_zero_iff
    {width : Nat} (width_two : 2 ≤ width) (body : List TagLetter)
    {block : List NearyTile} (role_block : IsRoleBlock block)
    (state : CenteredState) :
    rawHeadDefect width block (blockStep width body block state) = 0 ↔
      ordinaryDefect width state = 0 := by
  rw [rawHeadDefect_blockStep]
  have scale_ne : (3 : ℚ) ^ upperLength width block ≠ 0 := by positivity
  have terminal_ne := terminalDiscrepancy_ne_zero width_two
  have lower_ne := (roleBlock_lower_isUnit width body role_block).1
  have factor_ne :
      -(3 ^ upperLength width block * terminalDiscrepancy width *
        swappedLowerCode width body block : ℚ) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero scale_ne terminal_ne) lower_ne)
  constructor
  · intro product_zero
    exact (mul_eq_zero.mp product_zero).resolve_left factor_ne
  · intro defect_zero
    rw [defect_zero, mul_zero]

@[simp] theorem ordinaryDefect_ordinaryReset (width : Nat) :
    ordinaryDefect width (ordinaryReset width) = 0 := by
  simp [ordinaryDefect, ordinaryReset]

/-- The distinguished reset misses the ordinary reset ray by the exact square `R²`. -/
theorem ordinaryDefect_distinguishedReset (width : Nat) :
    ordinaryDefect width (distinguishedReset width) =
      (centeredCoefficient width : ℚ) ^ 2 := by
  simp [ordinaryDefect, distinguishedReset, centeredCoefficient,
    terminalDiscrepancy, setterMarker, widthScale]
  ring

/-- Even the distinguished reset does not license sliding-window reinitialization. -/
theorem distinguished_step_rawHeadDefect_ne_zero
    {width : Nat} (width_two : 2 ≤ width) (body : List TagLetter)
    {block : List NearyTile} (role_block : IsRoleBlock block) :
    rawHeadDefect width block
        (blockStep width body block (distinguishedReset width)) ≠ 0 := by
  intro raw_zero
  have ordinary_zero :=
    (rawHeadDefect_blockStep_eq_zero_iff width_two body role_block _).mp raw_zero
  rw [ordinaryDefect_distinguishedReset] at ordinary_zero
  exact pow_ne_zero 2 (centeredCoefficient_ne_zero width_two) ordinary_zero

/-- Denominator residual for a prospective next physical pole. -/
def poleResidual (width : Nat) (body : List TagLetter)
    (target : List NearyTile) (state : CenteredState) : ℚ :=
  blockCoefficient width body target * state.y +
    centeredCoupling width * swappedLowerCode width body target * state.x

/-- The denominator coordinate produced by a block is its pole residual. -/
@[simp] theorem blockStep_y
    (width : Nat) (body : List TagLetter) (block : List NearyTile)
    (state : CenteredState) :
    (blockStep width body block state).y = poleResidual width body block state := rfl

/-- A prospective pole is affine in the incoming ordinary-ray defect. -/
theorem poleResidual_eq_ordinaryDefect
    (width : Nat) (body : List TagLetter) (block : List NearyTile)
    (state : CenteredState) :
    poleResidual width body block state =
      centeredCoefficient width * swappedUpperCode width block * state.y -
        terminalDiscrepancy width * swappedLowerCode width body block *
          ordinaryDefect width state := by
  simp [poleResidual, ordinaryDefect, blockCoefficient, centeredCoupling]
  ring

/-- Ordinary-ray defect normalized by the live denominator coordinate. -/
def defectCoordinate (width : Nat) (state : CenteredState) : ℚ :=
  ordinaryDefect width state / state.y

/-- Exact Möbius recurrence of the normalized history defect away from a pole. -/
theorem defectCoordinate_blockStep
    (width : Nat) (body : List TagLetter) (block : List NearyTile)
    (state : CenteredState) (state_y_ne : state.y ≠ 0) :
    defectCoordinate width (blockStep width body block state) =
      (centeredCoefficient width *
          (swappedUpperCode width block -
            setterMarker width * (3 : ℚ) ^ upperLength width block) -
        terminalDiscrepancy width * swappedLowerCode width body block *
          defectCoordinate width state) /
      (centeredCoefficient width * swappedUpperCode width block -
        terminalDiscrepancy width * swappedLowerCode width body block *
          defectCoordinate width state) := by
  rw [defectCoordinate, ordinaryDefect_blockStep, blockStep_y,
    poleResidual_eq_ordinaryDefect, defectCoordinate]
  field_simp [state_y_ne]

@[simp] theorem defectCoordinate_ordinaryReset (width : Nat) :
    defectCoordinate width (ordinaryReset width) = 0 := by
  simp [defectCoordinate]

/-- The distinguished reset is the fixed center ratio `R/H` in defect coordinates. -/
theorem defectCoordinate_distinguishedReset
    {width : Nat} (width_two : 2 ≤ width) :
    defectCoordinate width (distinguishedReset width) =
      centeredCoefficient width / terminalDiscrepancy width := by
  rw [defectCoordinate, ordinaryDefect_distinguishedReset]
  simp [distinguishedReset]
  field_simp [centeredCoefficient_ne_zero width_two,
    terminalDiscrepancy_ne_zero width_two]

/-- A physical target is a pole exactly when the normalized history defect reaches its target
code ratio, scaled by the fixed center ratio `R/H`. -/
theorem poleResidual_eq_zero_iff_defectCoordinate_eq_target
    {width : Nat} (width_two : 2 ≤ width) (body : List TagLetter)
    {block : List NearyTile} (role_block : IsRoleBlock block)
    (state : CenteredState) (state_y_ne : state.y ≠ 0) :
    poleResidual width body block state = 0 ↔
      defectCoordinate width state =
        centeredCoefficient width * swappedUpperCode width block /
          (terminalDiscrepancy width * swappedLowerCode width body block) := by
  rw [poleResidual_eq_ordinaryDefect, defectCoordinate]
  have terminal_ne := terminalDiscrepancy_ne_zero width_two
  have lower_ne := (roleBlock_lower_isUnit width body role_block).1
  have denominator_ne :
      (terminalDiscrepancy width * swappedLowerCode width body block : ℚ) ≠ 0 :=
    mul_ne_zero terminal_ne lower_ne
  constructor
  · intro pole
    field_simp [state_y_ne, denominator_ne]
    nlinarith [pole]
  · intro coordinate
    field_simp [state_y_ne, denominator_ne] at coordinate
    nlinarith [coordinate]

/-- A physical target threshold equals the distinguished defect coordinate exactly at equality
of its upper and lower swapped codes. -/
theorem targetCoordinate_eq_distinguished_iff_terminal
    {width : Nat} (width_two : 2 ≤ width) (body : List TagLetter)
    {block : List NearyTile} (role_block : IsRoleBlock block) :
    (centeredCoefficient width : ℚ) * swappedUpperCode width block /
          (terminalDiscrepancy width * swappedLowerCode width body block) =
        (centeredCoefficient width : ℚ) / terminalDiscrepancy width ↔
      swappedUpperCode width block = swappedLowerCode width body block := by
  have centered_ne := centeredCoefficient_ne_zero width_two
  have terminal_ne := terminalDiscrepancy_ne_zero width_two
  have lower_ne := (roleBlock_lower_isUnit width body role_block).1
  constructor
  · intro ratio
    field_simp [centered_ne, terminal_ne, lower_ne] at ratio
    exact_mod_cast ratio
  · intro codes
    rw [codes]
    field_simp [centered_ne, terminal_ne, lower_ne]

/-- Hitting the distinguished physical threshold is a genuine terminal Neary match and hence a
halting source computation. -/
theorem tagHaltsFrom_of_targetCoordinate_eq_distinguished
    {width : Nat} (width_two : 2 ≤ width) (body : List TagLetter)
    (body_long : width - 1 ≤ body.length)
    {block : List NearyTile} (role_block : IsRoleBlock block)
    (threshold :
      (centeredCoefficient width : ℚ) * swappedUpperCode width block /
            (terminalDiscrepancy width * swappedLowerCode width body block) =
          (centeredCoefficient width : ℚ) / terminalDiscrepancy width) :
    TagHaltsFrom width (tagOutput body) (body.drop (width - 1) ++ [.b]) := by
  have codes :=
    (targetCoordinate_eq_distinguished_iff_terminal width_two body role_block).mp threshold
  apply tagHaltsFrom_of_swappedTernaryCode_eq width body (by omega) body_long block
  change
    (ternaryCode ((spell (nearyUpper width) block ++ nearyMarker width).map not) : ℤ) =
      (ternaryCode ((spell (nearyLower width body) block).map not) : ℤ) at codes
  exact_mod_cast codes

/-- The singleton `D_c` sends the ordinary reset to the distinguished negative threshold. -/
theorem defectCoordinate_ordinary_singleton_c
    {width : Nat} (width_two : 2 ≤ width) (body : List TagLetter) :
    defectCoordinate width
        (blockStep width body [.erase .c] (ordinaryReset width)) =
      centeredCoefficient width / terminalDiscrepancy width := by
  have centered_ne := centeredCoefficient_ne_zero width_two
  have marker_ne := setterMarker_ne_zero width_two
  have terminal_ne := terminalDiscrepancy_ne_zero width_two
  have ordinary_y_ne : (ordinaryReset width).y ≠ 0 := by
    simp [ordinaryReset, centered_ne, marker_ne]
  rw [defectCoordinate_blockStep width body [.erase .c]
    (ordinaryReset width) ordinary_y_ne, defectCoordinate_ordinaryReset]
  rw [swappedUpperCode_singleton_c, swappedLowerCode_singleton,
    upperLength_singleton_erase_c]
  norm_num
  field_simp [centered_ne, terminal_ne]
  simp [centeredCoefficient, terminalDiscrepancy, setterMarker, widthScale]
  ring

/-- The singleton `D_b` sends the ordinary reset to the positive value `H/P_b`. -/
theorem defectCoordinate_ordinary_singleton_b
    {width : Nat} (width_two : 2 ≤ width) (body : List TagLetter) :
    defectCoordinate width
        (blockStep width body [.erase .b] (ordinaryReset width)) =
      terminalDiscrepancy width / swappedUpperCode width [.erase .b] := by
  have scale_ge := widthScale_ge_nine width_two
  have centered_ne := centeredCoefficient_ne_zero width_two
  have marker_ne := setterMarker_ne_zero width_two
  have punctuated_ne : (swappedUpperCode width [.erase .b] : ℚ) ≠ 0 := by
    rw [swappedUpperCode_singleton_b]
    exact_mod_cast (by
      simp [widthScale] at scale_ge ⊢
      nlinarith : 18 * widthScale width ^ 2 - 4 * widthScale width - 1 ≠ 0)
  have ordinary_y_ne : (ordinaryReset width).y ≠ 0 := by
    simp [ordinaryReset, centered_ne, marker_ne]
  rw [defectCoordinate_blockStep width body [.erase .b]
    (ordinaryReset width) ordinary_y_ne, defectCoordinate_ordinaryReset]
  rw [swappedLowerCode_singleton, upperLength_singleton_erase_b]
  norm_num
  field_simp [centered_ne, punctuated_ne]
  rw [swappedUpperCode_singleton_b]
  simp [terminalDiscrepancy, setterMarker, widthScale, pow_add]
  ring

/-- The two singleton images of the ordinary reset straddle zero. A one-sided sign invariant
therefore cannot contain every physical continuation. -/
theorem ordinary_singletons_straddle_zero
    {width : Nat} (width_two : 2 ≤ width) (body : List TagLetter) :
    defectCoordinate width
          (blockStep width body [.erase .c] (ordinaryReset width)) < 0 ∧
      0 < defectCoordinate width
        (blockStep width body [.erase .b] (ordinaryReset width)) := by
  rw [defectCoordinate_ordinary_singleton_c width_two body,
    defectCoordinate_ordinary_singleton_b width_two body]
  have scale_ge := widthScale_ge_nine width_two
  have centered_neg : (centeredCoefficient width : ℚ) < 0 := by
    exact_mod_cast (by simp [centeredCoefficient]; omega : centeredCoefficient width < 0)
  have terminal_pos : (0 : ℚ) < terminalDiscrepancy width := by
    exact_mod_cast (by simp [terminalDiscrepancy]; omega : 0 < terminalDiscrepancy width)
  have punctuated_pos : (0 : ℚ) < swappedUpperCode width [.erase .b] := by
    rw [swappedUpperCode_singleton_b]
    exact_mod_cast (by
      simp [widthScale] at scale_ge ⊢
      nlinarith : 0 < 18 * widthScale width ^ 2 - 4 * widthScale width - 1)
  exact ⟨div_neg_of_neg_of_pos centered_neg terminal_pos,
    div_pos terminal_pos punctuated_pos⟩

/-- The prospective pole residual respects homogeneous rescaling. -/
theorem poleResidual_scale
    (width : Nat) (body : List TagLetter) (target : List NearyTile)
    (scalar : ℚ) (state : CenteredState) :
    poleResidual width body target (scaleState scalar state) =
      scalar * poleResidual width body target state := by
  simp [poleResidual, scaleState]
  ring

/-- Exact last-two-block continuant. Both coordinates of the incoming history survive in the
prospective pole equation. -/
theorem poleResidual_blockStep
    (width : Nat) (body : List TagLetter) (middle target : List NearyTile)
    (state : CenteredState) :
    poleResidual width body target (blockStep width body middle state) =
      centeredCoupling width * blockCoefficient width body target *
          swappedLowerCode width body middle * state.x +
        (blockCoefficient width body target * blockCoefficient width body middle +
          centeredCoupling width * swappedLowerCode width body target *
            3 ^ upperLength width middle) * state.y := by
  simp [poleResidual, blockStep, nextX, nextY]
  ring

/-- The prospective pole after a middle block splits exactly into its canonical raw-head value
and the incoming history correction. -/
theorem poleResidual_blockStep_rawHeadCorrection
    (width : Nat) (body : List TagLetter) (first middle target : List NearyTile)
    (state : CenteredState) :
    (3 : ℚ) ^ upperLength width first *
        poleResidual width body target (blockStep width body middle state) =
      state.x * poleResidual width body target
          (blockStep width body middle (rawHeadState width first)) +
        (blockCoefficient width body target * blockCoefficient width body middle +
          centeredCoupling width * swappedLowerCode width body target *
            3 ^ upperLength width middle) * rawHeadDefect width first state := by
  simp [poleResidual, blockStep, rawHeadState, rawHeadDefect, nextX, nextY]
  ring

/-- A later pole forces the canonical first-multi residual to equal the sole surviving
history-defect correction. -/
theorem canonicalResidual_eq_historyCorrection_of_pole
    (width : Nat) (body : List TagLetter) (first middle target : List NearyTile)
    (priorState : CenteredState)
    (pole : poleResidual width body target
      (blockStep width body middle (blockStep width body first priorState)) = 0) :
    (blockStep width body first priorState).x *
        poleResidual width body target
          (blockStep width body middle (rawHeadState width first)) =
      (3 : ℚ) ^ upperLength width first * terminalDiscrepancy width *
        swappedLowerCode width body first *
        (blockCoefficient width body target * blockCoefficient width body middle +
          centeredCoupling width * swappedLowerCode width body target *
            3 ^ upperLength width middle) * ordinaryDefect width priorState := by
  have corrected := poleResidual_blockStep_rawHeadCorrection width body first middle target
    (blockStep width body first priorState)
  rw [pole, mul_zero, rawHeadDefect_blockStep] at corrected
  calc
    (blockStep width body first priorState).x *
          poleResidual width body target
            (blockStep width body middle (rawHeadState width first)) =
        -((blockCoefficient width body target * blockCoefficient width body middle +
            centeredCoupling width * swappedLowerCode width body target *
              3 ^ upperLength width middle) *
          (-(3 ^ upperLength width first * terminalDiscrepancy width *
            swappedLowerCode width body first) * ordinaryDefect width priorState)) := by
          linarith only [corrected]
    _ = (3 : ℚ) ^ upperLength width first * terminalDiscrepancy width *
        swappedLowerCode width body first *
        (blockCoefficient width body target * blockCoefficient width body middle +
          centeredCoupling width * swappedLowerCode width body target *
            3 ^ upperLength width middle) * ordinaryDefect width priorState := by ring

/-- Cancelling the nonzero upper power leaves the projectively intrinsic last-resonance
equation. The canonical local residual is balanced by exactly one ordinary-reset defect. -/
theorem canonicalResidual_eq_scaledOrdinaryDefect_of_pole
    (width : Nat) (body : List TagLetter) (first middle target : List NearyTile)
    (priorState : CenteredState)
    (pole : poleResidual width body target
      (blockStep width body middle (blockStep width body first priorState)) = 0) :
    priorState.y * poleResidual width body target
        (blockStep width body middle (rawHeadState width first)) =
      terminalDiscrepancy width * swappedLowerCode width body first *
        (blockCoefficient width body target * blockCoefficient width body middle +
          centeredCoupling width * swappedLowerCode width body target *
            3 ^ upperLength width middle) * ordinaryDefect width priorState := by
  have scaled := canonicalResidual_eq_historyCorrection_of_pole width body first middle target
    priorState pole
  have power_ne : (3 : ℚ) ^ upperLength width first ≠ 0 := by positivity
  apply mul_left_cancel₀ power_ne
  simpa [blockStep, nextX, mul_assoc] using scaled

/-- The exact history term controlling whether the last completed block may be treated as a
fresh raw head. -/
theorem history_rawHeadDefect
    (width : Nat) (body : List TagLetter) (initial : CenteredState)
    (history : List (List NearyTile)) (block : List NearyTile) :
    rawHeadDefect width block
        (historyState width body initial (history ++ [block])) =
      -(3 ^ upperLength width block * terminalDiscrepancy width *
          swappedLowerCode width body block) *
        ordinaryDefect width (historyState width body initial history) := by
  rw [historyState, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  exact rawHeadDefect_blockStep width body block _

/-- Appending a physical block to a history lands on that block's canonical raw-head ray if and
only if the preceding history has returned to the ordinary-reset ray. -/
theorem history_rawHeadDefect_eq_zero_iff
    {width : Nat} (width_two : 2 ≤ width) (body : List TagLetter)
    (initial : CenteredState) (history : List (List NearyTile))
    {block : List NearyTile} (role_block : IsRoleBlock block) :
    rawHeadDefect width block
        (historyState width body initial (history ++ [block])) = 0 ↔
      ordinaryDefect width (historyState width body initial history) = 0 := by
  rw [historyState, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  exact rawHeadDefect_blockStep_eq_zero_iff width_two body role_block _

private theorem state_eq_scale_ordinaryReset
    {width : Nat} {state : CenteredState}
    (return_eq : ordinaryDefect width state = 0) :
    state = scaleState state.x (ordinaryReset width) := by
  ext
  · simp [scaleState, ordinaryReset]
  · simp [ordinaryDefect, scaleState, ordinaryReset] at return_eq ⊢
    linarith

/-- A genuine return of an arbitrary history to the ordinary ray is exactly the missing
constructor needed to reuse the shell-free first-multi theorem. -/
theorem ordinaryReturn_firstMultiTransfer_pole_false
    {width : Nat} (width_large : 6 ≤ width)
    {body : List TagLetter}
    (body_long : width - 1 ≤ body.length)
    (body_head : body.head? = some .b)
    {state : CenteredState} (state_x_ne : state.x ≠ 0)
    (return_eq : ordinaryDefect width state = 0)
    {first middle target : List NearyTile}
    (first_block : IsRoleBlock first)
    (first_ne : first ≠ [.erase .c])
    (middle_block : IsRoleBlock middle)
    (target_block : IsRoleBlock target)
    (pole :
      poleResidual width body target
        (blockStep width body middle (blockStep width body first state)) = 0) : False := by
  have centered_ne := centeredCoefficient_ne_zero (show 2 ≤ width by omega)
  have marker_ne := setterMarker_ne_zero (show 2 ≤ width by omega)
  have scale_ne :
      state.x * (centeredCoefficient width * setterMarker width : ℚ) ≠ 0 :=
    mul_ne_zero state_x_ne (mul_ne_zero centered_ne marker_ne)
  have state_eq := state_eq_scale_ordinaryReset return_eq
  let scale : ℚ := state.x *
    (centeredCoefficient width * setterMarker width : ℚ)
  have after_first_eq :
      blockStep width body first state =
        scaleState scale (rawHeadState width first) := by
    calc
      blockStep width body first state =
          blockStep width body first (scaleState state.x (ordinaryReset width)) := by
            rw [← state_eq]
      _ = scaleState state.x
          (blockStep width body first (ordinaryReset width)) :=
            blockStep_scale width body first state.x _
      _ = scaleState state.x
          (scaleState (centeredCoefficient width * setterMarker width)
            (rawHeadState width first)) := by
              rw [blockStep_ordinaryReset]
      _ = scaleState scale (rawHeadState width first) := by
            ext <;> simp [scaleState, scale] <;> ring
  have after_middle_eq :
      blockStep width body middle (blockStep width body first state) =
        scaleState scale
          (blockStep width body middle (rawHeadState width first)) := by
    rw [after_first_eq, blockStep_scale]
  have scaled_pole :
      scale * poleResidual width body target
        (blockStep width body middle (rawHeadState width first)) = 0 := by
    rw [after_middle_eq, poleResidual_scale] at pole
    exact pole
  have canonical_pole :
      poleResidual width body target
        (blockStep width body middle (rawHeadState width first)) = 0 := by
    exact (mul_eq_zero.mp scaled_pole).resolve_left (by simpa [scale] using scale_ne)
  exact physicalFirstMultiTransfer_pole_false width_large body_long body_head
    first_block first_ne middle_block target_block <| by
      simpa [poleResidual, blockStep, rawHeadState] using canonical_pole

end MatrixMortality.SwappedSetterHistory
