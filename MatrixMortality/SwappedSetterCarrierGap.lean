import MatrixMortality.SwappedSetterThresholdCarry

/-!
# Primitive carrier-gap obstruction for the swapped setter

The exact integer lift of the centered Möbius recurrence exposes its pre-cancellation gap.
Two literal deletion histories from the distinguished reset then give primitive carriers that
respectively violate the proposed marker-scale height bound and its bare modular replacement.
-/

namespace MatrixMortality.SwappedSetterCarrierGap

open SwappedSetterHistory SwappedSetterMultitransfer SwappedSetterThresholdCarry

/-- Unreduced projective numerator after one centered block. -/
def nextCarrierNumerator (width : Nat) (body : List TagLetter)
    (block : List NearyTile) (numerator denominator : ℤ) : ℤ :=
  terminalDiscrepancy width *
    ((swappedUpperCode width block -
        setterMarker width * 3 ^ upperLength width block) * denominator -
      swappedLowerCode width body block * numerator)

/-- Unreduced projective denominator after one centered block. -/
def nextCarrierDenominator (width : Nat) (body : List TagLetter)
    (block : List NearyTile) (numerator denominator : ℤ) : ℤ :=
  centeredCoefficient width *
    (swappedUpperCode width block * denominator -
      swappedLowerCode width body block * numerator)

/-- The integral carrier recurrence represents the exact Möbius defect update. -/
theorem blockStep_represents_nextCarrier
    (width : Nat) (body : List TagLetter) (block : List NearyTile)
    (state : CenteredState) (numerator denominator : ℤ)
    (represented : RepresentsDefectRatio width state numerator denominator) :
    RepresentsDefectRatio width (blockStep width body block state)
      (nextCarrierNumerator width body block numerator denominator)
      (nextCarrierDenominator width body block numerator denominator) := by
  rw [RepresentsDefectRatio] at represented ⊢
  rw [ordinaryDefect_blockStep, blockStep_y, poleResidual_eq_ordinaryDefect]
  simp [nextCarrierNumerator, nextCarrierDenominator]
  linear_combination
    -(3 ^ upperLength width block * terminalDiscrepancy width * setterMarker width *
      centeredCoefficient width * swappedLowerCode width body block) * represented

/-- A common nonzero scaling of integer carrier coordinates can be cancelled. -/
theorem RepresentsDefectRatio.of_common_scale
    {width : Nat} {state : CenteredState} {numerator denominator scale : ℤ}
    (scale_ne : scale ≠ 0)
    (represented : RepresentsDefectRatio width state
      (scale * numerator) (scale * denominator)) :
    RepresentsDefectRatio width state numerator denominator := by
  rw [RepresentsDefectRatio] at represented ⊢
  push_cast at represented
  have scale_ne_rat : (scale : ℚ) ≠ 0 := by exact_mod_cast scale_ne
  apply mul_left_cancel₀ scale_ne_rat
  calc
    (scale : ℚ) *
        (terminalDiscrepancy width * ordinaryDefect width state * denominator) =
      terminalDiscrepancy width * ordinaryDefect width state * (scale * denominator) := by
        ring
    _ = centeredCoefficient width * state.y * (scale * numerator) := represented
    _ = (scale : ℚ) * (centeredCoefficient width * state.y * numerator) := by
      ring

/-- Before gcd cancellation, every carrier gap has the exact common marker factor. -/
theorem nextCarrier_gap (width : Nat) (body : List TagLetter)
    (block : List NearyTile) (numerator denominator : ℤ) :
    nextCarrierDenominator width body block numerator denominator -
        nextCarrierNumerator width body block numerator denominator =
      setterMarker width *
        (terminalDiscrepancy width * 3 ^ upperLength width block * denominator -
          3 * (swappedUpperCode width block * denominator -
            swappedLowerCode width body block * numerator)) := by
  simp [nextCarrierNumerator, nextCarrierDenominator, terminalDiscrepancy,
    centeredCoefficient, setterMarker, widthScale]
  ring

/-- Half of one less than a power of three. -/
def halfScale : Nat → ℤ
  | 0 => 0
  | width + 1 => 3 * halfScale width + 1

theorem widthScale_eq_twice_halfScale_add_one (width : Nat) :
    widthScale width = 2 * halfScale width + 1 := by
  induction width with
  | zero => rfl
  | succ width induction =>
      change (3 : ℤ) ^ width = 2 * halfScale width + 1 at induction
      change (3 : ℤ) ^ width * 3 = 2 * halfScale (width + 1) + 1
      rw [induction]
      simp [halfScale]
      ring

/-- Successor width scale expressed through the preceding half scale. -/
theorem widthScale_succ_eq_six_halfScale_add_three (offset : Nat) :
    widthScale (offset + 1) = 6 * halfScale offset + 3 := by
  rw [widthScale, pow_succ]
  change (3 : ℤ) ^ offset * 3 = _
  rw [show (3 : ℤ) ^ offset = widthScale offset by rfl,
    widthScale_eq_twice_halfScale_add_one]
  ring

private theorem halfScale_nonneg (width : Nat) : 0 ≤ halfScale width := by
  induction width with
  | zero => rfl
  | succ width induction =>
      simp [halfScale]
      omega

/-- Primitive numerator of the distinguished carrier after one literal `D_c`. -/
def distinguishedDeletionCNumerator (offset : Nat) : ℤ :=
  let half := halfScale offset
  (2 * half + 1) * (15 * half + 7)

/-- Primitive denominator of the distinguished carrier after one literal `D_c`. -/
def distinguishedDeletionCDenominator (offset : Nat) : ℤ :=
  let half := halfScale offset
  (6 * half + 1) * (5 * half + 2)

private theorem halfScale_cases (offset : Nat) :
    halfScale offset = 0 ∨ ∃ quotient, halfScale offset = 3 * quotient + 1 := by
  cases offset with
  | zero => exact Or.inl rfl
  | succ offset => exact Or.inr ⟨halfScale offset, rfl⟩

/-- The displayed carrier coordinates have no hidden common factor. -/
theorem distinguishedDeletionC_isCoprime (offset : Nat) :
    IsCoprime (distinguishedDeletionCNumerator offset)
      (distinguishedDeletionCDenominator offset) := by
  let half := halfScale offset
  let source := 2 * half + 1
  let head := 15 * half + 7
  let residual := 6 * half + 1
  let tail := 5 * half + 2
  have source_residual : IsCoprime source residual := by
    refine ⟨1 - 3 * half, half, ?_⟩
    simp [source, residual]
    ring
  have source_tail : IsCoprime source tail := by
    refine ⟨5, -2, ?_⟩
    simp [source, tail]
    ring
  have head_tail : IsCoprime head tail := by
    refine ⟨1, -3, ?_⟩
    simp [head, tail]
    ring
  have head_residual : IsCoprime head residual := by
    rcases halfScale_cases offset with half_zero | ⟨quotient, half_eq⟩
    · refine ⟨0, 1, ?_⟩
      simp [head, residual, half, half_zero]
    · refine ⟨-2 * (8 * quotient + 3), 40 * quotient + 19, ?_⟩
      simp [head, residual, half, half_eq]
      ring
  have source_denominator : IsCoprime source (residual * tail) :=
    source_residual.mul_right source_tail
  have head_denominator : IsCoprime head (residual * tail) :=
    head_residual.mul_right head_tail
  simpa [distinguishedDeletionCNumerator,
    distinguishedDeletionCDenominator, source, head, residual, tail, half] using
      source_denominator.mul_left head_denominator

/-- The primitive carrier gap after distinguished `D_c` is the full setter marker. -/
theorem distinguishedDeletionC_gap (offset : Nat) :
    distinguishedDeletionCNumerator offset -
        distinguishedDeletionCDenominator offset =
      setterMarker (offset + 1) := by
  rw [setterMarker, widthScale, pow_succ,
    show ((3 : ℤ) ^ offset) = widthScale offset by rfl,
    widthScale_eq_twice_halfScale_add_one]
  simp [distinguishedDeletionCNumerator, distinguishedDeletionCDenominator]
  ring

/-- The primitive gap already exceeds the marker modulus after one distinguished `D_c`. -/
theorem widthScale_lt_distinguishedDeletionC_gap_abs (offset : Nat) :
    widthScale (offset + 1) <
      |distinguishedDeletionCDenominator offset -
        distinguishedDeletionCNumerator offset| := by
  rw [abs_sub_comm, distinguishedDeletionC_gap]
  have power_pos : (0 : ℤ) < (3 : ℤ) ^ offset := by positivity
  have scale_ge : (3 : ℤ) ≤ widthScale (offset + 1) := by
    simp [widthScale, pow_succ]
    omega
  have marker_pos : 0 < setterMarker (offset + 1) := by
    simp [setterMarker]
    omega
  rw [abs_of_pos marker_pos]
  simp [setterMarker]
  omega

/-- The displayed primitive pair represents the centered carrier reached from the distinguished
reset by literal `D_c`. -/
theorem distinguishedDeletionC_represents
    (offset : Nat) (body : List TagLetter) :
    RepresentsDefectRatio (offset + 1)
      (blockStep (offset + 1) body [.erase .c]
        (distinguishedReset (offset + 1)))
      (distinguishedDeletionCNumerator offset)
      (distinguishedDeletionCDenominator offset) := by
  rw [RepresentsDefectRatio]
  rw [ordinaryDefect_blockStep, blockStep_y, poleResidual_eq_ordinaryDefect,
    ordinaryDefect_distinguishedReset]
  simp [distinguishedReset, swappedUpperCode_singleton_c,
    swappedLowerCode_singleton, upperLength_singleton_erase_c,
    distinguishedDeletionCNumerator, distinguishedDeletionCDenominator,
    setterMarker, terminalDiscrepancy, centeredCoefficient,
    widthScale_succ_eq_six_halfScale_add_three]
  ring

/-- Primitive numerator after two literal `D_c` blocks from the distinguished reset. -/
def distinguishedDoubleDeletionCNumerator (offset : Nat) : ℤ :=
  let half := halfScale offset
  180 * half ^ 3 + 192 * half ^ 2 + 87 * half + 16

/-- Primitive denominator after two literal `D_c` blocks from the distinguished reset. -/
def distinguishedDoubleDeletionCDenominator (offset : Nat) : ℤ :=
  let half := halfScale offset
  (6 * half + 1) * (30 * half ^ 2 + 15 * half + 1)

/-- The two-deletion coordinates are also primitive. -/
theorem distinguishedDoubleDeletionC_isCoprime (offset : Nat) :
    IsCoprime (distinguishedDoubleDeletionCNumerator offset)
      (distinguishedDoubleDeletionCDenominator offset) := by
  let half := halfScale offset
  let numerator := 180 * half ^ 3 + 192 * half ^ 2 + 87 * half + 16
  let left := 6 * half + 1
  let right := 30 * half ^ 2 + 15 * half + 1
  have numerator_left : IsCoprime numerator left := by
    refine ⟨-half, 1 + half * (30 * half ^ 2 + 27 * half + 10), ?_⟩
    simp [numerator, left]
    ring
  have numerator_right : IsCoprime numerator right := by
    refine ⟨125 * half + 10, -(750 * half ^ 2 + 485 * half + 159), ?_⟩
    simp [numerator, right]
    ring
  simpa [distinguishedDoubleDeletionCNumerator,
    distinguishedDoubleDeletionCDenominator, numerator, left, right, half] using
      numerator_left.mul_right numerator_right

/-- After two distinguished `D_c` blocks the primitive gap is `ρμ`, so it is already a nonzero
multiple of the marker modulus. -/
theorem distinguishedDoubleDeletionC_gap (offset : Nat) :
    distinguishedDoubleDeletionCNumerator offset -
        distinguishedDoubleDeletionCDenominator offset =
      widthScale (offset + 1) * setterMarker (offset + 1) := by
  rw [setterMarker, widthScale_succ_eq_six_halfScale_add_three]
  simp [distinguishedDoubleDeletionCNumerator,
    distinguishedDoubleDeletionCDenominator]
  ring

/-- The nonzero primitive two-deletion gap contains the complete marker modulus. -/
theorem widthScale_dvd_distinguishedDoubleDeletionC_gap (offset : Nat) :
    widthScale (offset + 1) ∣
      distinguishedDoubleDeletionCNumerator offset -
        distinguishedDoubleDeletionCDenominator offset := by
  rw [distinguishedDoubleDeletionC_gap]
  exact dvd_mul_right _ _

/-- The primitive two-deletion gap is genuinely nonzero. -/
theorem distinguishedDoubleDeletionC_gap_pos (offset : Nat) :
    0 < distinguishedDoubleDeletionCNumerator offset -
      distinguishedDoubleDeletionCDenominator offset := by
  rw [distinguishedDoubleDeletionC_gap]
  have scale_pos : 0 < widthScale (offset + 1) := by
    simp [widthScale]
  have marker_pos : 0 < setterMarker (offset + 1) := by
    simp [setterMarker]
    omega
  positivity

/-- The second literal `D_c` realizes the displayed primitive pair. -/
theorem distinguishedDoubleDeletionC_represents
    (offset : Nat) (body : List TagLetter) :
    RepresentsDefectRatio (offset + 1)
      (blockStep (offset + 1) body [.erase .c]
        (blockStep (offset + 1) body [.erase .c]
          (distinguishedReset (offset + 1))))
      (distinguishedDoubleDeletionCNumerator offset)
      (distinguishedDoubleDeletionCDenominator offset) := by
  let half := halfScale offset
  let common := -2 * (15 * half + 7)
  have scale_eq :
      widthScale (offset + 1) = 6 * half + 3 := by
    simpa [half] using widthScale_succ_eq_six_halfScale_add_three offset
  have common_ne : common ≠ 0 := by
    have half_nonneg := halfScale_nonneg offset
    simp [common, half]
    omega
  have first := distinguishedDeletionC_represents offset body
  have raw := blockStep_represents_nextCarrier (offset + 1) body [.erase .c]
    (blockStep (offset + 1) body [.erase .c]
      (distinguishedReset (offset + 1)))
    (distinguishedDeletionCNumerator offset)
    (distinguishedDeletionCDenominator offset) first
  have numerator_eq :
      nextCarrierNumerator (offset + 1) body [.erase .c]
          (distinguishedDeletionCNumerator offset)
          (distinguishedDeletionCDenominator offset) =
        common * distinguishedDoubleDeletionCNumerator offset := by
    simp [nextCarrierNumerator, swappedUpperCode_singleton_c,
      swappedLowerCode_singleton, upperLength_singleton_erase_c,
      distinguishedDeletionCNumerator, distinguishedDeletionCDenominator,
      distinguishedDoubleDeletionCNumerator, terminalDiscrepancy, setterMarker,
      scale_eq, common, half]
    ring
  have denominator_eq :
      nextCarrierDenominator (offset + 1) body [.erase .c]
          (distinguishedDeletionCNumerator offset)
          (distinguishedDeletionCDenominator offset) =
        common * distinguishedDoubleDeletionCDenominator offset := by
    simp [nextCarrierDenominator, swappedUpperCode_singleton_c,
      swappedLowerCode_singleton, distinguishedDeletionCNumerator,
      distinguishedDeletionCDenominator, distinguishedDoubleDeletionCDenominator,
      terminalDiscrepancy, centeredCoefficient, scale_eq, common, half]
    ring
  have scaled :
      RepresentsDefectRatio (offset + 1)
        (blockStep (offset + 1) body [.erase .c]
          (blockStep (offset + 1) body [.erase .c]
            (distinguishedReset (offset + 1))))
        (common * distinguishedDoubleDeletionCNumerator offset)
        (common * distinguishedDoubleDeletionCDenominator offset) := by
    simpa only [numerator_eq, denominator_eq] using raw
  exact RepresentsDefectRatio.of_common_scale common_ne scaled

end MatrixMortality.SwappedSetterCarrierGap
