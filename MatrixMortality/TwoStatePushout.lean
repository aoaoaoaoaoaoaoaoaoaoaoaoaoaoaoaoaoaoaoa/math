import MatrixMortality.PairedCompression
import MatrixMortality.TerminalTile

/-!
# Two-state controlled pushouts

Two side-normal word-pair representations with the same upper word agree on their common
upper-word plane. This file forms their four-dimensional pushout, permits an arbitrary
deterministic transition on the two private lower channels, and proves the resulting suffix
decoder and rank-one mortality compiler for every physical word.
-/

namespace MatrixMortality

open scoped Matrix

/-- A deterministic transition on the rule and erasure copies of the lower-word channel. -/
abbrev TwoStateTransition (α : Type*) := PairPhase → α → PairPhase

/-- One controlled role selected by the suffix state at a physical data letter. -/
abbrev ControlledRole (α : Type*) := PairPhase × α

/-- The side-normal matrix selected by a controlled role. -/
def controlledRoleMatrix (R : Type*) [CommRing R] {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (role : ControlledRole α) : Matrix (Fin 3) (Fin 3) R :=
  sidePcpMatrix R (upper role.2) (lower role.1 role.2)

/-- Matrix form of the phase embedding used by the pushout. -/
def phaseInjection (R : Type*) [CommRing R] : PairPhase → Matrix (Fin 4) (Fin 3) R
  | .rule =>
      !![(1 : R), 0, 0;
         0, 1, 0;
         0, 0, 1;
         0, 0, 0]
  | .erase =>
      !![(1 : R), 0, 0;
         0, 0, 0;
         0, 0, 1;
         0, 1, 0]

/-- Projection from the pushout onto one of its two phase copies. -/
def phaseProjection (R : Type*) [CommRing R] : PairPhase → Matrix (Fin 3) (Fin 4) R
  | .rule =>
      !![(1 : R), 0, 0, 0;
         0, 1, 0, 0;
         0, 0, 1, 0]
  | .erase =>
      !![(1 : R), 0, 0, 0;
         0, 0, 0, 1;
         0, 0, 1, 0]

theorem phaseInjection_mulVec (R : Type*) [CommRing R] (phase : PairPhase)
    (vector : Fin 3 → R) :
    phaseInjection R phase *ᵥ vector = phaseVector R phase vector := by
  funext i
  cases phase <;> fin_cases i <;>
    simp [phaseInjection, phaseVector, Matrix.vecHead, Matrix.vecTail, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_succ]

theorem phaseProjection_mul_phaseInjection (R : Type*) [CommRing R]
    (phase : PairPhase) :
    phaseProjection R phase * phaseInjection R phase = 1 := by
  ext i j
  cases phase <;> fin_cases i <;> fin_cases j <;>
    simp [phaseProjection, phaseInjection, Matrix.vecHead, Matrix.vecTail, Matrix.mul_apply,
      Fin.sum_univ_succ]

theorem phaseProjection_mulVec_phaseVector (R : Type*) [CommRing R]
    (phase : PairPhase) (vector : Fin 3 → R) :
    phaseProjection R phase *ᵥ phaseVector R phase vector = vector := by
  funext i
  cases phase <;> fin_cases i <;>
    simp [phaseProjection, phaseVector, Matrix.vecHead, Matrix.vecTail, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_succ]

/-- Route one private lower-channel scale to its deterministic destination state. -/
def routedScale (R : Type*) [CommRing R] (destination target : PairPhase)
    (scale : R) : R :=
  if destination = target then scale else 0

/-- Four-dimensional pushout of two side-normal role representations.

The first and third coordinates are the shared upper-word plane. Coordinates two and four
are the private rule and erasure lower channels. -/
def twoStateDataMatrix (R : Type*) [CommRing R] {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : TwoStateTransition α) (letter : α) : Matrix (Fin 4) (Fin 4) R :=
  !![(1 : R), ternaryCode (lower .rule letter), ternaryCode (upper letter),
      ternaryCode (lower .erase letter);
     0, routedScale R (δ .rule letter) .rule
          ((3 : R) ^ (lower .rule letter).length),
        0, routedScale R (δ .erase letter) .rule
          ((3 : R) ^ (lower .erase letter).length);
     0, 0, (3 : R) ^ (upper letter).length, 0;
     0, routedScale R (δ .rule letter) .erase
          ((3 : R) ^ (lower .rule letter).length),
        0, routedScale R (δ .erase letter) .erase
          ((3 : R) ^ (lower .erase letter).length)]

/-- The pushout performs the selected role and routes its private coordinate to the next
suffix state. -/
theorem twoStateDataMatrix_mulVec_phaseVector (R : Type*) [CommRing R] {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : TwoStateTransition α) (letter : α) (phase : PairPhase) (vector : Fin 3 → R) :
    twoStateDataMatrix R upper lower δ letter *ᵥ phaseVector R phase vector =
      phaseVector R (δ phase letter)
        (controlledRoleMatrix R upper lower (phase, letter) *ᵥ vector) := by
  cases phase <;>
    cases destination : δ _ letter <;>
      funext i <;>
        fin_cases i <;>
          simp [twoStateDataMatrix, controlledRoleMatrix, routedScale, phaseVector,
            sidePcpMatrix, destination, Matrix.vecHead, Matrix.vecTail, Matrix.mulVec,
            Matrix.dotProduct, Fin.sum_univ_succ]
  all_goals ring

theorem phaseProjection_mul_twoStateDataMatrix_mul_phaseInjection
    (R : Type*) [CommRing R] {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : TwoStateTransition α) (letter : α) (source destination : PairPhase)
    (transition : δ source letter = destination) :
    phaseProjection R destination * twoStateDataMatrix R upper lower δ letter *
        phaseInjection R source =
      controlledRoleMatrix R upper lower (source, letter) := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro vector
  change (phaseProjection R destination * twoStateDataMatrix R upper lower δ letter *
      phaseInjection R source) *ᵥ vector =
    controlledRoleMatrix R upper lower (source, letter) *ᵥ vector
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [phaseInjection_mulVec, twoStateDataMatrix_mulVec_phaseVector, transition,
    phaseProjection_mulVec_phaseVector]

theorem phaseInjection_mul_phaseProjection_mul_twoStateDataMatrix
    (R : Type*) [CommRing R] {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : TwoStateTransition α) (letter : α) (destination : PairPhase)
    (rule_transition : δ .rule letter = destination)
    (erase_transition : δ .erase letter = destination) :
    phaseInjection R destination * phaseProjection R destination *
        twoStateDataMatrix R upper lower δ letter =
      twoStateDataMatrix R upper lower δ letter := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro vector
  change (phaseInjection R destination * phaseProjection R destination *
      twoStateDataMatrix R upper lower δ letter) *ᵥ vector =
    twoStateDataMatrix R upper lower δ letter *ᵥ vector
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  funext i
  cases destination <;> fin_cases i <;>
    simp [phaseProjection, phaseInjection, twoStateDataMatrix, routedScale,
      rule_transition, erase_transition, Matrix.vecHead, Matrix.vecTail, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_succ]

/-- Every side-normal controlled role is nonsingular over the rationals. -/
theorem controlledRoleMatrix_det_rat {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (role : ControlledRole α) :
    (controlledRoleMatrix ℚ upper lower role).det =
      (3 : ℚ) ^ (upper role.2).length * (3 : ℚ) ^ (lower role.1 role.2).length := by
  rw [controlledRoleMatrix, Matrix.det_fin_three]
  norm_num [sidePcpMatrix, Matrix.vecHead, Matrix.vecTail]
  ring

theorem controlledRoleMatrix_rank_rat {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (role : ControlledRole α) :
    (controlledRoleMatrix ℚ upper lower role).rank = 3 := by
  apply Matrix.rank_of_isUnit
  rw [Matrix.isUnit_iff_isUnit_det, controlledRoleMatrix_det_rat]
  exact isUnit_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (by norm_num))
    (pow_ne_zero _ (by norm_num)))

/-- Distinct destinations preserve all four pushout coordinates. -/
theorem twoStateDataMatrix_det_rule_erase (R : Type*) [CommRing R] {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : TwoStateTransition α) (letter : α)
    (rule_destination : δ .rule letter = .rule)
    (erase_destination : δ .erase letter = .erase) :
    (twoStateDataMatrix R upper lower δ letter).det =
      (3 : R) ^ (upper letter).length *
        (3 : R) ^ (lower .rule letter).length *
          (3 : R) ^ (lower .erase letter).length := by
  have phase_ne : (PairPhase.rule : PairPhase) ≠ .erase := by decide
  have erase_ne : (PairPhase.erase : PairPhase) ≠ .rule := by decide
  rw [Matrix.det_succ_column_zero]
  norm_num [Fin.sum_univ_succ, twoStateDataMatrix, routedScale, rule_destination,
    erase_destination, Matrix.submatrix]
  rw [Matrix.det_fin_three]
  norm_num [twoStateDataMatrix, routedScale, rule_destination, erase_destination,
    Matrix.submatrix, phase_ne, erase_ne, Matrix.vecHead, Matrix.vecTail]
  ring

/-- Swapping the two private destinations reverses the determinant sign. -/
theorem twoStateDataMatrix_det_erase_rule (R : Type*) [CommRing R] {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : TwoStateTransition α) (letter : α)
    (rule_destination : δ .rule letter = .erase)
    (erase_destination : δ .erase letter = .rule) :
    (twoStateDataMatrix R upper lower δ letter).det =
      -((3 : R) ^ (upper letter).length *
        (3 : R) ^ (lower .rule letter).length *
          (3 : R) ^ (lower .erase letter).length) := by
  have phase_ne : (PairPhase.rule : PairPhase) ≠ .erase := by decide
  have erase_ne : (PairPhase.erase : PairPhase) ≠ .rule := by decide
  rw [Matrix.det_succ_column_zero]
  norm_num [Fin.sum_univ_succ, twoStateDataMatrix, routedScale, rule_destination,
    erase_destination, Matrix.submatrix]
  rw [Matrix.det_fin_three]
  norm_num [twoStateDataMatrix, routedScale, rule_destination, erase_destination,
    Matrix.submatrix, phase_ne, erase_ne, Matrix.vecHead, Matrix.vecTail]
  ring

/-- A reset of both private channels to the rule state has determinant zero. -/
theorem twoStateDataMatrix_det_rule_rule (R : Type*) [CommRing R] {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : TwoStateTransition α) (letter : α)
    (rule_destination : δ .rule letter = .rule)
    (erase_destination : δ .erase letter = .rule) :
    (twoStateDataMatrix R upper lower δ letter).det = 0 := by
  have phase_ne : (PairPhase.rule : PairPhase) ≠ .erase := by decide
  rw [Matrix.det_succ_column_zero]
  norm_num [Fin.sum_univ_succ, twoStateDataMatrix, routedScale, rule_destination,
    erase_destination, Matrix.submatrix]
  rw [Matrix.det_fin_three]
  norm_num [twoStateDataMatrix, routedScale, rule_destination, erase_destination,
    Matrix.submatrix, phase_ne, Matrix.vecHead, Matrix.vecTail]

/-- A reset of both private channels to the erasure state has determinant zero. -/
theorem twoStateDataMatrix_det_erase_erase (R : Type*) [CommRing R] {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : TwoStateTransition α) (letter : α)
    (rule_destination : δ .rule letter = .erase)
    (erase_destination : δ .erase letter = .erase) :
    (twoStateDataMatrix R upper lower δ letter).det = 0 := by
  have erase_ne : (PairPhase.erase : PairPhase) ≠ .rule := by decide
  rw [Matrix.det_succ_column_zero]
  norm_num [Fin.sum_univ_succ, twoStateDataMatrix, routedScale, rule_destination,
    erase_destination, Matrix.submatrix]
  rw [Matrix.det_fin_three]
  norm_num [twoStateDataMatrix, routedScale, rule_destination, erase_destination,
    Matrix.submatrix, erase_ne, Matrix.vecHead, Matrix.vecTail]

/-- A transition that distinguishes the two source states has full rank. -/
theorem twoStateDataMatrix_rank_eq_four_of_ne {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : TwoStateTransition α) (letter : α)
    (destinations_ne : δ .rule letter ≠ δ .erase letter) :
    (twoStateDataMatrix ℚ upper lower δ letter).rank = 4 := by
  apply Matrix.rank_of_isUnit
  rw [Matrix.isUnit_iff_isUnit_det]
  cases rule_destination : δ .rule letter <;>
    cases erase_destination : δ .erase letter
  · exact (destinations_ne (rule_destination.trans erase_destination.symm)).elim
  · rw [twoStateDataMatrix_det_rule_erase ℚ upper lower δ letter
      rule_destination erase_destination]
    exact isUnit_iff_ne_zero.mpr
      (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)))
        (pow_ne_zero _ (by norm_num)))
  · rw [twoStateDataMatrix_det_erase_rule ℚ upper lower δ letter
      rule_destination erase_destination]
    exact isUnit_iff_ne_zero.mpr
      (neg_ne_zero.mpr
        (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)))
          (pow_ne_zero _ (by norm_num))))
  · exact (destinations_ne (rule_destination.trans erase_destination.symm)).elim

/-- A deterministic reset of both source states has rank exactly three. -/
theorem twoStateDataMatrix_rank_eq_three_of_eq {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : TwoStateTransition α) (letter : α)
    (destinations_eq : δ .rule letter = δ .erase letter) :
    (twoStateDataMatrix ℚ upper lower δ letter).rank = 3 := by
  let destination := δ .rule letter
  have rule_transition : δ .rule letter = destination := rfl
  have erase_transition : δ .erase letter = destination := destinations_eq.symm
  let data := twoStateDataMatrix ℚ upper lower δ letter
  have factor :
      phaseInjection ℚ destination * phaseProjection ℚ destination * data = data :=
    phaseInjection_mul_phaseProjection_mul_twoStateDataMatrix ℚ upper lower δ letter
      destination rule_transition erase_transition
  have factor' :
      phaseInjection ℚ destination * (phaseProjection ℚ destination * data) = data := by
    simpa [Matrix.mul_assoc] using factor
  have rank_le_three : data.rank ≤ 3 := by
    rw [← factor']
    exact (Matrix.rank_mul_le_right (phaseInjection ℚ destination)
      (phaseProjection ℚ destination * data)).trans
        (Matrix.rank_le_height (phaseProjection ℚ destination * data))
  have role_factor :
      phaseProjection ℚ destination * data * phaseInjection ℚ .rule =
        controlledRoleMatrix ℚ upper lower (.rule, letter) :=
    phaseProjection_mul_twoStateDataMatrix_mul_phaseInjection ℚ upper lower δ letter
      .rule destination rule_transition
  have three_le_rank : 3 ≤ data.rank := by
    rw [← controlledRoleMatrix_rank_rat upper lower (.rule, letter), ← role_factor]
    exact (Matrix.rank_mul_le_left
      (phaseProjection ℚ destination * data) (phaseInjection ℚ .rule)).trans
        (Matrix.rank_mul_le_right (phaseProjection ℚ destination) data)
  exact le_antisymm rank_le_three three_le_rank

/-- Right-to-left decoding, retaining the state seen by any further letter on the left. -/
def twoStateSuffixDecode {α : Type*} (δ : TwoStateTransition α) :
    PairPhase → List α → PairPhase × List (ControlledRole α)
  | terminal, [] => (terminal, [])
  | terminal, letter :: word =>
      let decoded := twoStateSuffixDecode δ terminal word
      (δ decoded.1 letter, (decoded.1, letter) :: decoded.2)

/-- The controlled role word assigned to every physical data word. -/
def decodeTwoStateWord {α : Type*} (δ : TwoStateTransition α)
    (terminal : PairPhase) (word : List α) : List (ControlledRole α) :=
  (twoStateSuffixDecode δ terminal word).2

/-- Product of physical two-state pushout matrices. -/
def twoStateProduct (R : Type*) [CommRing R] {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : TwoStateTransition α) (word : List α) : Matrix (Fin 4) (Fin 4) R :=
  wordProduct (twoStateDataMatrix R upper lower δ) word

/-- Product of the decoded side-normal roles. -/
def controlledRoleProduct (R : Type*) [CommRing R] {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (word : List (ControlledRole α)) : Matrix (Fin 3) (Fin 3) R :=
  wordProduct (controlledRoleMatrix R upper lower) word

/-- Every physical word obeys the total suffix decoder. -/
theorem twoStateProduct_mulVec_phaseVector (R : Type*) [CommRing R] {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : TwoStateTransition α) (terminal : PairPhase) (word : List α)
    (vector : Fin 3 → R) :
    twoStateProduct R upper lower δ word *ᵥ phaseVector R terminal vector =
      phaseVector R (twoStateSuffixDecode δ terminal word).1
        (controlledRoleProduct R upper lower (decodeTwoStateWord δ terminal word) *ᵥ vector) := by
  induction word with
  | nil =>
      simp [twoStateProduct, twoStateSuffixDecode, decodeTwoStateWord, controlledRoleProduct]
  | cons letter word induction =>
      simp only [twoStateProduct, wordProduct_cons]
      rw [← Matrix.mulVec_mulVec]
      change twoStateDataMatrix R upper lower δ letter *ᵥ
        (twoStateProduct R upper lower δ word *ᵥ phaseVector R terminal vector) = _
      rw [induction, twoStateDataMatrix_mulVec_phaseVector]
      simp only [twoStateSuffixDecode, decodeTwoStateWord, controlledRoleProduct,
        wordProduct_cons, Matrix.mulVec_mulVec]

/-- The common first-coordinate row of the two-state pushout. -/
def twoStateRow (R : Type*) [CommRing R] : Fin 4 → R := ![1, 0, 0, 0]

/-- Embed a supplied side-normal terminal vector in its terminal control state. -/
def twoStateColumn (R : Type*) [CommRing R] (terminal : PairPhase)
    (column : Fin 3 → R) : Fin 4 → R :=
  phaseVector R terminal column

/-- Scalar coefficient recognized by the physical two-state pushout. -/
def twoStateCoefficient (R : Type*) [CommRing R] {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : TwoStateTransition α) (terminal : PairPhase) (column : Fin 3 → R)
    (word : List α) : R :=
  twoStateRow R ⬝ᵥ
    twoStateProduct R upper lower δ word *ᵥ twoStateColumn R terminal column

/-- The physical coefficient equals the decoded side-normal coefficient for every word. -/
theorem twoStateCoefficient_eq_controlled (R : Type*) [CommRing R] {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : TwoStateTransition α) (terminal : PairPhase) (column : Fin 3 → R)
    (word : List α) :
    twoStateCoefficient R upper lower δ terminal column word =
      (controlledRoleProduct R upper lower (decodeTwoStateWord δ terminal word) *ᵥ column) 0 := by
  rw [twoStateCoefficient, twoStateColumn, twoStateProduct_mulVec_phaseVector]
  exact pairedRow_dot_phaseVector R _ _

/-- The nonzero common first column fixed by every physical data generator. -/
def twoStateAnchor (R : Type*) [CommRing R] : Fin 4 → R := ![1, 0, 0, 0]

theorem twoStateDataMatrix_mulVec_anchor (R : Type*) [CommRing R] {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : TwoStateTransition α) (letter : α) :
    twoStateDataMatrix R upper lower δ letter *ᵥ twoStateAnchor R =
      twoStateAnchor R := by
  funext i
  fin_cases i <;>
    simp [twoStateDataMatrix, twoStateAnchor, Matrix.vecHead, Matrix.vecTail,
      Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ]

@[simp] theorem twoStateRow_dot_anchor (R : Type*) [CommRing R] :
    twoStateRow R ⬝ᵥ twoStateAnchor R = 1 := by
  simp [twoStateRow, twoStateAnchor, Matrix.dotProduct, Fin.sum_univ_succ]

@[simp] theorem twoStateCoefficient_nil (R : Type*) [CommRing R] {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : TwoStateTransition α) (terminal : PairPhase) (column : Fin 3 → R) :
    twoStateCoefficient R upper lower δ terminal column [] = column 0 := by
  cases terminal <;>
    simp [twoStateCoefficient, twoStateProduct, twoStateColumn, twoStateRow, phaseVector,
      Matrix.dotProduct, Fin.sum_univ_succ]

/-- Three physical generators: the data pushout family and its rank-one boundary separator. -/
def twoStateMortalityFamily (R : Type*) [CommRing R] {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : TwoStateTransition α) (terminal : PairPhase) (column : Fin 3 → R) :
    Option α → Matrix (Fin 4) (Fin 4) R :=
  separatedGenerator
    (Matrix.vecMulVec (twoStateColumn R terminal column) (twoStateRow R))
    (twoStateDataMatrix R upper lower δ)

/-- The fixed-anchor separator compiler is exact even when a data letter is singular. -/
theorem twoStateMortalityFamily_mortal_iff_nonempty_zero {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : TwoStateTransition α) (terminal : PairPhase) (column : Fin 3 → ℚ)
    (column_head_nonzero : column 0 ≠ 0) :
    IsMortal (twoStateMortalityFamily ℚ upper lower δ terminal column) ↔
      ∃ word : List α,
        word ≠ [] ∧ twoStateCoefficient ℚ upper lower δ terminal column word = 0 := by
  rw [twoStateMortalityFamily]
  have fixed :
      ∀ letter,
        twoStateDataMatrix ℚ upper lower δ letter *ᵥ twoStateAnchor ℚ =
          twoStateAnchor ℚ :=
    twoStateDataMatrix_mulVec_anchor ℚ upper lower δ
  have row_anchor_nonzero : twoStateRow ℚ ⬝ᵥ twoStateAnchor ℚ ≠ 0 := by
    simp
  rw [fixedAnchor_mortal_adjoin_outer_iff
    (twoStateDataMatrix ℚ upper lower δ)
    (twoStateAnchor ℚ) (twoStateColumn ℚ terminal column) (twoStateRow ℚ)
    fixed row_anchor_nonzero]
  constructor
  · rintro ⟨word, bridge_zero⟩
    refine ⟨word, ?_, ?_⟩
    · intro word_empty
      subst word
      apply column_head_nonzero
      cases terminal <;>
        simpa [bridgeScalar, twoStateCoefficient, twoStateRow, twoStateColumn, phaseVector,
          Matrix.dotProduct, Fin.sum_univ_succ] using bridge_zero
    · simpa [bridgeScalar, twoStateCoefficient]
        using bridge_zero
  · rintro ⟨word, _, coefficient_zero⟩
    exact ⟨word, by simpa [bridgeScalar, twoStateCoefficient] using coefficient_zero⟩

/-! ## Exact integer family -/

theorem castVector_phaseVector (phase : PairPhase) (vector : Fin 3 → ℤ) :
    castVector (phaseVector ℤ phase vector) = phaseVector ℚ phase (castVector vector) := by
  funext i
  cases phase <;> fin_cases i <;> simp [castVector, phaseVector]

theorem castVector_twoStateRow :
    castVector (twoStateRow ℤ) = twoStateRow ℚ := by
  funext i
  fin_cases i <;> simp [castVector, twoStateRow]

theorem castVector_twoStateColumn (terminal : PairPhase) (column : Fin 3 → ℤ) :
    castVector (twoStateColumn ℤ terminal column) =
      twoStateColumn ℚ terminal (castVector column) := by
  exact castVector_phaseVector terminal column

theorem castMatrix_twoStateDataMatrix {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : TwoStateTransition α) (letter : α) :
    castMatrix (twoStateDataMatrix ℤ upper lower δ letter) =
      twoStateDataMatrix ℚ upper lower δ letter := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [castMatrix, twoStateDataMatrix, routedScale, Matrix.vecHead, Matrix.vecTail]

theorem castMatrix_twoStateMortalityFamily {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : TwoStateTransition α) (terminal : PairPhase) (column : Fin 3 → ℤ)
    (label : Option α) :
    castMatrix (twoStateMortalityFamily ℤ upper lower δ terminal column label) =
      twoStateMortalityFamily ℚ upper lower δ terminal (castVector column) label := by
  cases label with
  | none =>
      rw [twoStateMortalityFamily, separatedGenerator, castMatrix_vecMulVec,
        castVector_twoStateColumn, castVector_twoStateRow]
      rfl
  | some letter =>
      exact castMatrix_twoStateDataMatrix upper lower δ letter

/-- The rational compiler theorem transfers back to the displayed integer generators. -/
theorem twoStateMortalityFamily_int_mortal_iff_nonempty_zero {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : TwoStateTransition α) (terminal : PairPhase) (column : Fin 3 → ℤ)
    (column_head_nonzero : column 0 ≠ 0) :
    IsMortal (twoStateMortalityFamily ℤ upper lower δ terminal column) ↔
      ∃ word : List α,
        word ≠ [] ∧
          twoStateCoefficient ℚ upper lower δ terminal (castVector column) word = 0 := by
  have family_cast :
      castMatrix ∘ twoStateMortalityFamily ℤ upper lower δ terminal column =
        twoStateMortalityFamily ℚ upper lower δ terminal (castVector column) := by
    funext label
    exact castMatrix_twoStateMortalityFamily upper lower δ terminal column label
  rw [← isMortal_cast_iff (twoStateMortalityFamily ℤ upper lower δ terminal column),
    family_cast]
  exact twoStateMortalityFamily_mortal_iff_nonempty_zero upper lower δ terminal
    (castVector column) (by simpa [castVector] using column_head_nonzero)

end MatrixMortality
