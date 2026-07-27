import MatrixMortality.PCPEncoding
import MatrixMortality.TerminalTile
import MatrixMortality.WordMorphism

/-!
# Absorbing a forced terminal PCP tile

This file instantiates the generic rank-one chain theorem with the three-dimensional PCP
encoding.  Its central scalar is proved to vanish exactly for a terminal PCP match.
-/

namespace MatrixMortality

open scoped Matrix

/-- The first standard basis vector `e₁`. -/
def headBasis (R : Type*) [Semiring R] : Fin 3 → R := Pi.single 0 1

/-- The third standard basis vector `e₃`. -/
def tailBasis (R : Type*) [Semiring R] : Fin 3 → R := Pi.single 2 1

theorem headBasis_ne_zero (R : Type*) [Semiring R] [Nontrivial R] : headBasis R ≠ 0 := by
  intro h
  have := congr_fun h 0
  simp [headBasis] at this

theorem tailBasis_ne_zero (R : Type*) [Semiring R] [Nontrivial R] : tailBasis R ≠ 0 := by
  intro h
  have := congr_fun h 2
  simp [tailBasis] at this

theorem pcpMatrix_mulVec_headBasis (R : Type*) [CommRing R] (upper lower : List Bool) :
    pcpMatrix R upper lower *ᵥ headBasis R = headBasis R := by
  funext i
  fin_cases i <;>
    simp [pcpMatrix, headBasis, Matrix.vecHead, Matrix.vecTail, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_succ]

/-- Product of the PCP matrices selected by a tile-index word. -/
def tileProduct {α R : Type*} [CommRing R] (u v : α → List Bool) (word : List α) :
    Matrix (Fin 3) (Fin 3) R :=
  wordProduct (fun i => pcpMatrix R (u i) (v i)) word

theorem tileProduct_eq_pcpMatrix {α R : Type*} [CommRing R]
    (u v : α → List Bool) (word : List α) :
    tileProduct u v word = pcpMatrix R (spell u word) (spell v word) := by
  induction word with
  | nil => simp [tileProduct, spell]
  | cons i word ih =>
      simp only [tileProduct, wordProduct_cons, spell, List.map_cons, List.join_cons]
      change pcpMatrix R (u i) (v i) * tileProduct u v word = _
      rw [ih, ← pcpMatrix_append]
      simp [spell]

/-- The fifth tile after absorbing its matrix into the annihilator's column. -/
def terminalColumn (uₜ vₜ : List Bool) : Fin 3 → ℚ :=
  pcpMatrix ℚ uₜ vₜ *ᵥ tailBasis ℚ

/-- The exceptional rank-one generator `Xₜ e₃ e₁ᵀ`. -/
def terminalGenerator (uₜ vₜ : List Bool) : Matrix (Fin 3) (Fin 3) ℚ :=
  Matrix.vecMulVec (terminalColumn uₜ vₜ) (headBasis ℚ)

theorem terminalGenerator_rank_le_one (uₜ vₜ : List Bool) :
    (terminalGenerator uₜ vₜ).toLin'.rank ≤ 1 := by
  exact Matrix.rank_vecMulVec _ _

theorem terminalColumn_ne_zero (uₜ vₜ : List Bool) : terminalColumn uₜ vₜ ≠ 0 :=
  unit_mulVec_ne_zero (pcpMatrix_isUnit_rat uₜ vₜ) (tailBasis_ne_zero ℚ)

theorem terminalGenerator_ne_zero (uₜ vₜ : List Bool) : terminalGenerator uₜ vₜ ≠ 0 :=
  outer_ne_zero (terminalColumn_ne_zero uₜ vₜ) (headBasis_ne_zero ℚ)

theorem terminalGenerator_rank_eq_one (uₜ vₜ : List Bool) :
    (terminalGenerator uₜ vₜ).toLin'.rank = 1 := by
  apply le_antisymm (terminalGenerator_rank_le_one uₜ vₜ)
  rw [Cardinal.one_le_iff_ne_zero]
  intro hrank
  have hrange : LinearMap.range (Matrix.toLin' (terminalGenerator uₜ vₜ)) = ⊥ := by
    letI : Subsingleton (LinearMap.range (Matrix.toLin' (terminalGenerator uₜ vₜ))) :=
      rank_zero_iff.mp hrank
    exact Submodule.eq_bot_of_subsingleton
  have hlin : Matrix.toLin' (terminalGenerator uₜ vₜ) = 0 := LinearMap.range_eq_bot.mp hrange
  apply terminalGenerator_ne_zero uₜ vₜ
  apply Matrix.toLin'.injective
  simpa using hlin

theorem bridgeScalar_tileProduct {α : Type*} (u v : α → List Bool)
    (uₜ vₜ : List Bool) (word : List α) :
    bridgeScalar (terminalColumn uₜ vₜ) (headBasis ℚ) (tileProduct u v word) = 0 ↔
      spell u word ++ uₜ = spell v word ++ vₜ := by
  rw [bridgeScalar]
  change headBasis ℚ ⬝ᵥ tileProduct u v word *ᵥ
      (pcpMatrix ℚ uₜ vₜ *ᵥ tailBasis ℚ) = 0 ↔ _
  rw [Matrix.mulVec_mulVec]
  change headBasis ℚ ⬝ᵥ
      ((tileProduct u v word * pcpMatrix ℚ uₜ vₜ) *ᵥ tailBasis ℚ) = 0 ↔ _
  rw [tileProduct_eq_pcpMatrix, ← pcpMatrix_append]
  simp only [headBasis, tailBasis, Matrix.single_dotProduct, one_mul,
    Matrix.mulVec_single, mul_one]
  exact pcpMatrix_top_right_eq_zero_iff_rat _ _

/-- The rational family of ordinary PCP matrices and one absorbed terminal separator. -/
def absorbedFamily {α : Type*} (u v : α → List Bool) (uₜ vₜ : List Bool) :
    Option α → Matrix (Fin 3) (Fin 3) ℚ :=
  separatedGenerator (terminalGenerator uₜ vₜ) (fun i => pcpMatrix ℚ (u i) (v i))

theorem absorbedFamily_mortal_iff_terminal_match {α : Type*} (u v : α → List Bool)
    (uₜ vₜ : List Bool) :
    IsMortal (absorbedFamily u v uₜ vₜ) ↔
      ∃ word : List α, spell u word ++ uₜ = spell v word ++ vₜ := by
  let X : α → Matrix (Fin 3) (Fin 3) ℚ := fun i => pcpMatrix ℚ (u i) (v i)
  have fixed : ∀ label, X label *ᵥ headBasis ℚ = headBasis ℚ :=
    fun label => pcpMatrix_mulVec_headBasis ℚ (u label) (v label)
  have anchor_pair : headBasis ℚ ⬝ᵥ headBasis ℚ ≠ 0 := by
    simp [headBasis]
  rw [show absorbedFamily u v uₜ vₜ =
      separatedGenerator
        (Matrix.vecMulVec (terminalColumn uₜ vₜ) (headBasis ℚ)) X by
        rfl]
  rw [fixedAnchor_mortal_adjoin_outer_iff X (headBasis ℚ)
    (terminalColumn uₜ vₜ) (headBasis ℚ) fixed anchor_pair]
  constructor
  · rintro ⟨word, bridge_zero⟩
    exact ⟨word, (bridgeScalar_tileProduct u v uₜ vₜ word).mp
      (by simpa [X, wordProduct, tileProduct] using bridge_zero)⟩
  · rintro ⟨word, terminal_match⟩
    refine ⟨word, ?_⟩
    simpa [X, wordProduct, tileProduct] using
      (bridgeScalar_tileProduct u v uₜ vₜ word).mpr terminal_match

theorem castMatrix_pcpMatrix (x y : List Bool) :
    castMatrix (pcpMatrix ℤ x y) = pcpMatrix ℚ x y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [castMatrix, pcpMatrix, Matrix.vecHead, Matrix.vecTail]

theorem castVector_headBasis : castVector (headBasis ℤ) = headBasis ℚ := by
  funext i
  fin_cases i <;> simp [castVector, headBasis]

theorem castVector_tailBasis : castVector (tailBasis ℤ) = tailBasis ℚ := by
  funext i
  fin_cases i <;> simp [castVector, tailBasis]

/-- The integral absorbed-terminal column `Ψ(uₜ,vₜ)e₃`. -/
def terminalColumnInt (uₜ vₜ : List Bool) : Fin 3 → ℤ :=
  pcpMatrix ℤ uₜ vₜ *ᵥ tailBasis ℤ

/-- The integral rank-one separator `Ψ(uₜ,vₜ)e₃e₁ᵀ`. -/
def terminalGeneratorInt (uₜ vₜ : List Bool) : Matrix (Fin 3) (Fin 3) ℤ :=
  Matrix.vecMulVec (terminalColumnInt uₜ vₜ) (headBasis ℤ)

/-- The exact integral family emitted by the fixed-boundary mortality compiler. -/
def absorbedFamilyInt {α : Type*} (u v : α → List Bool) (uₜ vₜ : List Bool) :
    Option α → Matrix (Fin 3) (Fin 3) ℤ :=
  separatedGenerator (terminalGeneratorInt uₜ vₜ) (fun i => pcpMatrix ℤ (u i) (v i))

theorem castMatrix_terminalGeneratorInt (uₜ vₜ : List Bool) :
    castMatrix (terminalGeneratorInt uₜ vₜ) = terminalGenerator uₜ vₜ := by
  rw [terminalGeneratorInt, castMatrix_vecMulVec, terminalGenerator, terminalColumn,
    terminalColumnInt, castMatrix_mulVec, castMatrix_pcpMatrix, castVector_tailBasis,
    castVector_headBasis]

theorem castMatrix_terminalGeneratorInt_rank_eq_one (uₜ vₜ : List Bool) :
    (castMatrix (terminalGeneratorInt uₜ vₜ)).toLin'.rank = 1 := by
  rw [castMatrix_terminalGeneratorInt]
  exact terminalGenerator_rank_eq_one uₜ vₜ

theorem castMatrix_absorbedFamilyInt {α : Type*} (u v : α → List Bool)
    (uₜ vₜ : List Bool) (letter : Option α) :
    castMatrix (absorbedFamilyInt u v uₜ vₜ letter) = absorbedFamily u v uₜ vₜ letter := by
  cases letter with
  | none => exact castMatrix_terminalGeneratorInt uₜ vₜ
  | some i => exact castMatrix_pcpMatrix (u i) (v i)

theorem terminalGeneratorInt_ne_zero (uₜ vₜ : List Bool) :
    terminalGeneratorInt uₜ vₜ ≠ 0 := by
  intro hzero
  apply terminalGenerator_ne_zero uₜ vₜ
  rw [← castMatrix_terminalGeneratorInt, hzero]
  simp [castMatrix]

theorem absorbedFamilyInt_mortal_iff_terminal_match {α : Type*} (u v : α → List Bool)
    (uₜ vₜ : List Bool) :
    IsMortal (absorbedFamilyInt u v uₜ vₜ) ↔
      ∃ word : List α, spell u word ++ uₜ = spell v word ++ vₜ := by
  rw [← absorbedFamily_mortal_iff_terminal_match]
  have family_cast :
      castMatrix ∘ absorbedFamilyInt u v uₜ vₜ = absorbedFamily u v uₜ vₜ := by
    funext label
    exact castMatrix_absorbedFamilyInt u v uₜ vₜ label
  rw [← family_cast]
  exact (isMortal_cast_iff (absorbedFamilyInt u v uₜ vₜ)).symm

/-- The exact five-generator specialization used for `M₃(5)`: four ordinary tiles and one
absorbed terminal tile, indexed by `Option (Fin 4)`. -/
theorem five_matrix_reduction (u v : Fin 4 → List Bool) (u₅ v₅ : List Bool) :
    IsMortal (absorbedFamilyInt u v u₅ v₅) ↔
      ∃ word : List (Fin 4), spell u word ++ u₅ = spell v word ++ v₅ :=
  absorbedFamilyInt_mortal_iff_terminal_match u v u₅ v₅

end MatrixMortality
