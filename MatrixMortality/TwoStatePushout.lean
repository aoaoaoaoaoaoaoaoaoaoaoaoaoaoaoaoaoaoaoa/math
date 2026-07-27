import MatrixMortality.ControllerPushout
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

/-- The two roles carried by the paired and two-state compilers. -/
inductive PairPhase where
  | rule
  | erase
  deriving DecidableEq, Fintype, Repr

/-- Toggle the selected member of a rule/erasure pair. -/
def PairPhase.flip : PairPhase → PairPhase
  | .rule => .erase
  | .erase => .rule

/-- Recover the Neary role selected by one phase. -/
def PairPhase.tile : PairPhase → TagLetter → NearyTile
  | .rule, letter => .rule letter
  | .erase, letter => .erase letter

/-- Coordinate order used by the explicit four-state compilers. -/
def pairControllerEquiv : ControllerIndex PairPhase ≃ Fin 4 where
  toFun
    | .inl index => ![(0 : Fin 4), 2] index
    | .inr .rule => 1
    | .inr .erase => 3
  invFun := fun index =>
    ![(Sum.inl 0 : ControllerIndex PairPhase), Sum.inr .rule,
      Sum.inl 1, Sum.inr .erase] index
  left_inv := by
    intro index
    rcases index with index | phase
    · fin_cases index <;> rfl
    · cases phase <;> rfl
  right_inv := by
    intro index
    fin_cases index <;> rfl

@[simp] theorem pairControllerEquiv_symm_zero :
    pairControllerEquiv.symm 0 = Sum.inl 0 := rfl

@[simp] theorem pairControllerEquiv_symm_one :
    pairControllerEquiv.symm 1 = Sum.inr .rule := rfl

@[simp] theorem pairControllerEquiv_symm_two :
    pairControllerEquiv.symm 2 = Sum.inl 1 := rfl

@[simp] theorem pairControllerEquiv_symm_three :
    pairControllerEquiv.symm 3 = Sum.inr .erase := rfl

/-- Embed one side-normal phase vector in the explicit four-coordinate order. -/
def phaseVector (R : Type*) [CommRing R] :
    PairPhase → (Fin 3 → R) → Fin 4 → R :=
  fun phase vector => controllerVector R phase vector ∘ pairControllerEquiv.symm

theorem phaseVector_comp_pairControllerEquiv (R : Type*) [CommRing R]
    (phase : PairPhase) (vector : Fin 3 → R) :
    phaseVector R phase vector ∘ pairControllerEquiv = controllerVector R phase vector := by
  funext index
  simp [phaseVector]

/-- The shared affine coordinate extracts the side-normal head in either phase. -/
theorem phaseHead (R : Type*) [CommRing R] (phase : PairPhase)
    (vector : Fin 3 → R) : phaseVector R phase vector 0 = vector 0 := by
  cases phase <;> simp [phaseVector, controllerVector, pairControllerEquiv]

theorem phaseVector_basis_zero (R : Type*) [CommRing R] (phase : PairPhase) :
    phaseVector R phase ![1, 0, 0] = ![1, 0, 0, 0] := by
  funext index
  cases phase <;> fin_cases index <;>
    simp [phaseVector, controllerVector, pairControllerEquiv]

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
    simp [phaseInjection, phaseVector, controllerVector, pairControllerEquiv,
      Matrix.vecHead, Matrix.vecTail, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ]

theorem phaseProjection_mulVec_phaseVector (R : Type*) [CommRing R]
    (phase : PairPhase) (vector : Fin 3 → R) :
    phaseProjection R phase *ᵥ phaseVector R phase vector = vector := by
  funext i
  cases phase <;> fin_cases i <;>
    simp [phaseProjection, phaseVector, controllerVector, pairControllerEquiv,
      Matrix.vecHead, Matrix.vecTail, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ]

/-- Four-dimensional pushout of two side-normal role representations.

The first and third coordinates are the shared upper-word plane. Coordinates two and four
are the private rule and erasure lower channels. -/
def twoStateDataMatrix (R : Type*) [CommRing R] {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : ControllerTransition PairPhase α) (letter : α) : Matrix (Fin 4) (Fin 4) R :=
  Matrix.reindex pairControllerEquiv pairControllerEquiv
    (controllerMatrix R upper lower δ letter)

/-- The pushout performs the selected role and routes its private coordinate to the next
suffix state. -/
theorem twoStateDataMatrix_mulVec_phaseVector (R : Type*) [CommRing R] {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : ControllerTransition PairPhase α) (letter : α) (phase : PairPhase)
    (vector : Fin 3 → R) :
    twoStateDataMatrix R upper lower δ letter *ᵥ phaseVector R phase vector =
      phaseVector R (δ phase letter)
        (controllerRoleMatrix R upper lower (phase, letter) *ᵥ vector) := by
  rw [twoStateDataMatrix, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
  simp only [Equiv.symm_symm]
  rw [
    phaseVector_comp_pairControllerEquiv,
    controllerMatrix_mulVec_controllerVector]
  rfl

theorem phaseProjection_mul_twoStateDataMatrix_mul_phaseInjection
    (R : Type*) [CommRing R] {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : ControllerTransition PairPhase α) (letter : α) (source destination : PairPhase)
    (transition : δ source letter = destination) :
    phaseProjection R destination * twoStateDataMatrix R upper lower δ letter *
        phaseInjection R source =
      controllerRoleMatrix R upper lower (source, letter) := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro vector
  change (phaseProjection R destination * twoStateDataMatrix R upper lower δ letter *
      phaseInjection R source) *ᵥ vector =
    controllerRoleMatrix R upper lower (source, letter) *ᵥ vector
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [phaseInjection_mulVec, twoStateDataMatrix_mulVec_phaseVector, transition,
    phaseProjection_mulVec_phaseVector]

theorem phaseInjection_mul_phaseProjection_mul_twoStateDataMatrix
    (R : Type*) [CommRing R] {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : ControllerTransition PairPhase α) (letter : α) (destination : PairPhase)
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
    simp [phaseProjection, phaseInjection, twoStateDataMatrix, controllerMatrix,
      pairControllerEquiv, rule_transition, erase_transition, Matrix.vecHead, Matrix.vecTail,
      Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ]

/-- Distinct destinations preserve all four pushout coordinates. -/
theorem twoStateDataMatrix_det_rule_erase (R : Type*) [CommRing R] {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : ControllerTransition PairPhase α) (letter : α)
    (rule_destination : δ .rule letter = .rule)
    (erase_destination : δ .erase letter = .erase) :
    (twoStateDataMatrix R upper lower δ letter).det =
      (3 : R) ^ (upper letter).length *
        (3 : R) ^ (lower .rule letter).length *
          (3 : R) ^ (lower .erase letter).length := by
  have phase_ne : (PairPhase.rule : PairPhase) ≠ .erase := by decide
  have erase_ne : (PairPhase.erase : PairPhase) ≠ .rule := by decide
  rw [Matrix.det_succ_column_zero]
  norm_num [Fin.sum_univ_succ, twoStateDataMatrix, controllerMatrix, pairControllerEquiv,
    rule_destination, erase_destination, Matrix.submatrix]
  rw [Matrix.det_fin_three]
  norm_num [twoStateDataMatrix, controllerMatrix, pairControllerEquiv, rule_destination,
    erase_destination, Matrix.submatrix, phase_ne, erase_ne, Matrix.vecHead, Matrix.vecTail]
  ring

/-- Swapping the two private destinations reverses the determinant sign. -/
theorem twoStateDataMatrix_det_erase_rule (R : Type*) [CommRing R] {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : ControllerTransition PairPhase α) (letter : α)
    (rule_destination : δ .rule letter = .erase)
    (erase_destination : δ .erase letter = .rule) :
    (twoStateDataMatrix R upper lower δ letter).det =
      -((3 : R) ^ (upper letter).length *
        (3 : R) ^ (lower .rule letter).length *
          (3 : R) ^ (lower .erase letter).length) := by
  have phase_ne : (PairPhase.rule : PairPhase) ≠ .erase := by decide
  have erase_ne : (PairPhase.erase : PairPhase) ≠ .rule := by decide
  rw [Matrix.det_succ_column_zero]
  norm_num [Fin.sum_univ_succ, twoStateDataMatrix, controllerMatrix, pairControllerEquiv,
    rule_destination, erase_destination, Matrix.submatrix]
  rw [Matrix.det_fin_three]
  norm_num [twoStateDataMatrix, controllerMatrix, pairControllerEquiv, rule_destination,
    erase_destination, Matrix.submatrix, phase_ne, erase_ne, Matrix.vecHead, Matrix.vecTail]
  ring

/-- A reset of both private channels to the rule state has determinant zero. -/
theorem twoStateDataMatrix_det_rule_rule (R : Type*) [CommRing R] {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : ControllerTransition PairPhase α) (letter : α)
    (rule_destination : δ .rule letter = .rule)
    (erase_destination : δ .erase letter = .rule) :
    (twoStateDataMatrix R upper lower δ letter).det = 0 := by
  have phase_ne : (PairPhase.rule : PairPhase) ≠ .erase := by decide
  rw [Matrix.det_succ_column_zero]
  norm_num [Fin.sum_univ_succ, twoStateDataMatrix, controllerMatrix, pairControllerEquiv,
    rule_destination, erase_destination, Matrix.submatrix]
  rw [Matrix.det_fin_three]
  norm_num [twoStateDataMatrix, controllerMatrix, pairControllerEquiv, rule_destination,
    erase_destination, Matrix.submatrix, phase_ne, Matrix.vecHead, Matrix.vecTail]

/-- A reset of both private channels to the erasure state has determinant zero. -/
theorem twoStateDataMatrix_det_erase_erase (R : Type*) [CommRing R] {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : ControllerTransition PairPhase α) (letter : α)
    (rule_destination : δ .rule letter = .erase)
    (erase_destination : δ .erase letter = .erase) :
    (twoStateDataMatrix R upper lower δ letter).det = 0 := by
  have erase_ne : (PairPhase.erase : PairPhase) ≠ .rule := by decide
  rw [Matrix.det_succ_column_zero]
  norm_num [Fin.sum_univ_succ, twoStateDataMatrix, controllerMatrix, pairControllerEquiv,
    rule_destination, erase_destination, Matrix.submatrix]
  rw [Matrix.det_fin_three]
  norm_num [twoStateDataMatrix, controllerMatrix, pairControllerEquiv, rule_destination,
    erase_destination, Matrix.submatrix, erase_ne, Matrix.vecHead, Matrix.vecTail]

/-- A transition that distinguishes the two source states has full rank. -/
theorem twoStateDataMatrix_rank_eq_four_of_ne {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : ControllerTransition PairPhase α) (letter : α)
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
    (δ : ControllerTransition PairPhase α) (letter : α)
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
        controllerRoleMatrix ℚ upper lower (.rule, letter) :=
    phaseProjection_mul_twoStateDataMatrix_mul_phaseInjection ℚ upper lower δ letter
      .rule destination rule_transition
  have three_le_rank : 3 ≤ data.rank := by
    rw [← controllerRoleMatrix_rank_rat upper lower (.rule, letter), ← role_factor]
    exact (Matrix.rank_mul_le_left
      (phaseProjection ℚ destination * data) (phaseInjection ℚ .rule)).trans
        (Matrix.rank_mul_le_right (phaseProjection ℚ destination) data)
  exact le_antisymm rank_le_three three_le_rank

/-- Product of physical two-state pushout matrices. -/
def twoStateProduct (R : Type*) [CommRing R] {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : ControllerTransition PairPhase α) (word : List α) : Matrix (Fin 4) (Fin 4) R :=
  Matrix.reindex pairControllerEquiv pairControllerEquiv
    (controllerProduct R upper lower δ word)

theorem twoStateProduct_eq_wordProduct (R : Type*) [CommRing R] {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : ControllerTransition PairPhase α) (word : List α) :
    twoStateProduct R upper lower δ word =
      wordProduct (twoStateDataMatrix R upper lower δ) word := by
  simpa [twoStateProduct, controllerProduct, twoStateDataMatrix] using
    (wordProduct_map
      (Matrix.reindexAlgEquiv R R pairControllerEquiv).toAlgHom.toRingHom.toMonoidHom
      (controllerMatrix R upper lower δ) word).symm

/-- Every physical word obeys the total suffix decoder. -/
theorem twoStateProduct_mulVec_phaseVector (R : Type*) [CommRing R] {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : ControllerTransition PairPhase α) (terminal : PairPhase) (word : List α)
    (vector : Fin 3 → R) :
    twoStateProduct R upper lower δ word *ᵥ phaseVector R terminal vector =
      phaseVector R (controllerSuffixDecode δ terminal word).1
        (controllerRoleProduct R upper lower (controllerSuffixRoles δ terminal word) *ᵥ
          vector) := by
  rw [twoStateProduct, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
  simp only [Equiv.symm_symm]
  rw [phaseVector_comp_pairControllerEquiv,
    controllerProduct_mulVec_controllerVector]
  rfl

/-- The common first-coordinate row of the two-state pushout. -/
def twoStateRow (R : Type*) [CommRing R] : Fin 4 → R := ![1, 0, 0, 0]

/-- Embed a supplied side-normal terminal vector in its terminal control state. -/
def twoStateColumn (R : Type*) [CommRing R] (terminal : PairPhase)
    (column : Fin 3 → R) : Fin 4 → R :=
  phaseVector R terminal column

/-- Scalar coefficient recognized by the physical two-state pushout. -/
def twoStateCoefficient (R : Type*) [CommRing R] {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : ControllerTransition PairPhase α) (terminal : PairPhase) (column : Fin 3 → R)
    (word : List α) : R :=
  twoStateRow R ⬝ᵥ
    twoStateProduct R upper lower δ word *ᵥ twoStateColumn R terminal column

/-- The physical coefficient equals the decoded side-normal coefficient for every word. -/
theorem twoStateCoefficient_eq_controlled (R : Type*) [CommRing R] {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : ControllerTransition PairPhase α) (terminal : PairPhase) (column : Fin 3 → R)
    (word : List α) :
    twoStateCoefficient R upper lower δ terminal column word =
      (controllerRoleProduct R upper lower (controllerSuffixRoles δ terminal word) *ᵥ
        column) 0 := by
  rw [twoStateCoefficient, twoStateColumn, twoStateProduct_mulVec_phaseVector]
  simpa [twoStateRow, Matrix.dotProduct, Fin.sum_univ_succ] using
    phaseHead R (controllerSuffixDecode δ terminal word).1
      (controllerRoleProduct R upper lower (controllerSuffixRoles δ terminal word) *ᵥ column)

/-- The nonzero common first column fixed by every physical data generator. -/
def twoStateAnchor (R : Type*) [CommRing R] : Fin 4 → R := ![1, 0, 0, 0]

theorem twoStateDataMatrix_mulVec_anchor (R : Type*) [CommRing R] {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : ControllerTransition PairPhase α) (letter : α) :
    twoStateDataMatrix R upper lower δ letter *ᵥ twoStateAnchor R =
      twoStateAnchor R := by
  funext i
  fin_cases i <;>
    simp [twoStateDataMatrix, controllerMatrix, pairControllerEquiv, twoStateAnchor,
      Matrix.vecHead, Matrix.vecTail, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ]

@[simp] theorem twoStateRow_dot_anchor (R : Type*) [CommRing R] :
    twoStateRow R ⬝ᵥ twoStateAnchor R = 1 := by
  simp [twoStateRow, twoStateAnchor, Matrix.dotProduct, Fin.sum_univ_succ]

@[simp] theorem twoStateCoefficient_nil (R : Type*) [CommRing R] {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : ControllerTransition PairPhase α) (terminal : PairPhase) (column : Fin 3 → R) :
    twoStateCoefficient R upper lower δ terminal column [] = column 0 := by
  rw [twoStateCoefficient_eq_controlled]
  simp [controllerSuffixRoles, controllerSuffixDecode, controllerRoleProduct]

/-- Three physical generators: the data pushout family and its rank-one boundary separator. -/
def twoStateMortalityFamily (R : Type*) [CommRing R] {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : ControllerTransition PairPhase α) (terminal : PairPhase) (column : Fin 3 → R) :
    Option α → Matrix (Fin 4) (Fin 4) R :=
  separatedGenerator
    (Matrix.vecMulVec (twoStateColumn R terminal column) (twoStateRow R))
    (twoStateDataMatrix R upper lower δ)

/-- The fixed-anchor separator compiler is exact even when a data letter is singular. -/
theorem twoStateMortalityFamily_mortal_iff_nonempty_zero {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : ControllerTransition PairPhase α) (terminal : PairPhase) (column : Fin 3 → ℚ)
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
    · simpa [bridgeScalar, twoStateCoefficient, twoStateProduct_eq_wordProduct]
        using bridge_zero
  · rintro ⟨word, _, coefficient_zero⟩
    exact ⟨word, by
      simpa [bridgeScalar, twoStateCoefficient, twoStateProduct_eq_wordProduct] using
        coefficient_zero⟩

/-! ## Exact integer family -/

theorem phaseVector_map {R S : Type*} [CommRing R] [CommRing S]
    (hom : R →+* S) (phase : PairPhase) (vector : Fin 3 → R) :
    hom ∘ phaseVector R phase vector = phaseVector S phase (hom ∘ vector) := by
  funext i
  cases phase <;> fin_cases i <;>
    simp [phaseVector, controllerVector, pairControllerEquiv]

theorem twoStateRow_map {R S : Type*} [CommRing R] [CommRing S]
    (hom : R →+* S) :
    hom ∘ twoStateRow R = twoStateRow S := by
  funext i
  fin_cases i <;> simp [twoStateRow]

theorem twoStateColumn_map {R S : Type*} [CommRing R] [CommRing S]
    (hom : R →+* S) (terminal : PairPhase) (column : Fin 3 → R) :
    hom ∘ twoStateColumn R terminal column =
      twoStateColumn S terminal (hom ∘ column) :=
  phaseVector_map hom terminal column

theorem twoStateDataMatrix_map {R S α : Type*} [CommRing R] [CommRing S]
    (hom : R →+* S)
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : ControllerTransition PairPhase α) (letter : α) :
    (twoStateDataMatrix R upper lower δ letter).map hom =
      twoStateDataMatrix S upper lower δ letter := by
  simpa [twoStateDataMatrix] using congrArg
    (Matrix.reindex pairControllerEquiv pairControllerEquiv)
    (controllerMatrix_map hom upper lower δ letter)

theorem twoStateMortalityFamily_map {R S α : Type*} [CommRing R] [CommRing S]
    (hom : R →+* S)
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : ControllerTransition PairPhase α) (terminal : PairPhase) (column : Fin 3 → R)
    (label : Option α) :
    (twoStateMortalityFamily R upper lower δ terminal column label).map hom =
      twoStateMortalityFamily S upper lower δ terminal (hom ∘ column) label := by
  cases label with
  | none =>
      rw [twoStateMortalityFamily, separatedGenerator, vecMulVec_map,
        twoStateColumn_map, twoStateRow_map]
      rfl
  | some letter =>
      exact twoStateDataMatrix_map hom upper lower δ letter

/-- The rational compiler theorem transfers back to the displayed integer generators. -/
theorem twoStateMortalityFamily_int_mortal_iff_nonempty_zero {α : Type*}
    (upper : α → List Bool) (lower : PairPhase → α → List Bool)
    (δ : ControllerTransition PairPhase α) (terminal : PairPhase) (column : Fin 3 → ℤ)
    (column_head_nonzero : column 0 ≠ 0) :
    IsMortal (twoStateMortalityFamily ℤ upper lower δ terminal column) ↔
      ∃ word : List α,
        word ≠ [] ∧
          twoStateCoefficient ℚ upper lower δ terminal (castVector column) word = 0 := by
  have family_cast :
      castMatrix ∘ twoStateMortalityFamily ℤ upper lower δ terminal column =
        twoStateMortalityFamily ℚ upper lower δ terminal (castVector column) := by
    funext label
    exact twoStateMortalityFamily_map (Int.castRingHom ℚ)
      upper lower δ terminal column label
  rw [← isMortal_cast_iff (twoStateMortalityFamily ℤ upper lower δ terminal column),
    family_cast]
  exact twoStateMortalityFamily_mortal_iff_nonempty_zero upper lower δ terminal
    (castVector column) (by simpa [castVector] using column_head_nonzero)

end MatrixMortality
