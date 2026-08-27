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

theorem headBasis_map {R S : Type*} [Semiring R] [Semiring S]
    (hom : R →+* S) : hom ∘ headBasis R = headBasis S := by
  funext i
  fin_cases i <;> simp [headBasis]

theorem tailBasis_map {R S : Type*} [Semiring R] [Semiring S]
    (hom : R →+* S) : hom ∘ tailBasis R = tailBasis S := by
  funext i
  fin_cases i <;> simp [tailBasis]

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
    simp [pcpMatrix, headBasis, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

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
      simp only [tileProduct, wordProduct_cons, spell, List.flatMap_cons]
      change pcpMatrix R (u i) (v i) * tileProduct u v word = _
      rw [ih, ← pcpMatrix_append]
      simp [spell]

/-- The fifth tile after absorbing its matrix into the annihilator's column. -/
def terminalColumn (R : Type*) [CommRing R] (uₜ vₜ : List Bool) : Fin 3 → R :=
  pcpMatrix R uₜ vₜ *ᵥ tailBasis R

/-- The exceptional rank-one generator `Xₜ e₃ e₁ᵀ`. -/
def terminalGenerator (R : Type*) [CommRing R] (uₜ vₜ : List Bool) :
    Matrix (Fin 3) (Fin 3) R :=
  Matrix.vecMulVec (terminalColumn R uₜ vₜ) (headBasis R)

theorem terminalGenerator_rank_le_one (uₜ vₜ : List Bool) :
    (terminalGenerator ℚ uₜ vₜ).toLin'.rank ≤ 1 := by
  exact Matrix.rank_vecMulVec _ _

theorem terminalColumn_ne_zero (uₜ vₜ : List Bool) : terminalColumn ℚ uₜ vₜ ≠ 0 :=
  unit_mulVec_ne_zero (pcpMatrix_isUnit_rat uₜ vₜ) (tailBasis_ne_zero ℚ)

theorem terminalGenerator_ne_zero (uₜ vₜ : List Bool) :
    terminalGenerator ℚ uₜ vₜ ≠ 0 :=
  outer_ne_zero (terminalColumn_ne_zero uₜ vₜ) (headBasis_ne_zero ℚ)

theorem terminalGenerator_rank_eq_one (uₜ vₜ : List Bool) :
    (terminalGenerator ℚ uₜ vₜ).toLin'.rank = 1 := by
  apply le_antisymm (terminalGenerator_rank_le_one uₜ vₜ)
  rw [Cardinal.one_le_iff_ne_zero]
  intro hrank
  have hrange : LinearMap.range (Matrix.toLin' (terminalGenerator ℚ uₜ vₜ)) = ⊥ := by
    let _ : Subsingleton (LinearMap.range (Matrix.toLin' (terminalGenerator ℚ uₜ vₜ))) :=
      rank_zero_iff.mp hrank
    exact Submodule.eq_bot_of_subsingleton
  have hlin : Matrix.toLin' (terminalGenerator ℚ uₜ vₜ) = 0 :=
    LinearMap.range_eq_bot.mp hrange
  apply terminalGenerator_ne_zero uₜ vₜ
  apply Matrix.toLin'.injective
  simpa using hlin

theorem bridgeScalar_tileProduct {α : Type*} (u v : α → List Bool)
    (uₜ vₜ : List Bool) (word : List α) :
    bridgeScalar (terminalColumn ℚ uₜ vₜ) (headBasis ℚ) (tileProduct u v word) = 0 ↔
      spell u word ++ uₜ = spell v word ++ vₜ := by
  rw [bridgeScalar]
  change headBasis ℚ ⬝ᵥ tileProduct u v word *ᵥ
      (pcpMatrix ℚ uₜ vₜ *ᵥ tailBasis ℚ) = 0 ↔ _
  rw [Matrix.mulVec_mulVec]
  change headBasis ℚ ⬝ᵥ
      ((tileProduct u v word * pcpMatrix ℚ uₜ vₜ) *ᵥ tailBasis ℚ) = 0 ↔ _
  rw [tileProduct_eq_pcpMatrix, ← pcpMatrix_append]
  simp only [headBasis, tailBasis, Matrix.mulVec_single_one, single_one_dotProduct]
  exact pcpMatrix_top_right_eq_zero_iff_rat _ _

/-- The rational family of ordinary PCP matrices and one absorbed terminal separator. -/
def absorbedFamily (R : Type*) [CommRing R] {α : Type*}
    (u v : α → List Bool) (uₜ vₜ : List Bool) :
    Option α → Matrix (Fin 3) (Fin 3) R :=
  separatedGenerator (terminalGenerator R uₜ vₜ) (fun i => pcpMatrix R (u i) (v i))

theorem absorbedFamily_mortal_iff_terminal_match {α : Type*} (u v : α → List Bool)
    (uₜ vₜ : List Bool) :
    IsMortal (absorbedFamily ℚ u v uₜ vₜ) ↔
      ∃ word : List α, spell u word ++ uₜ = spell v word ++ vₜ := by
  let X : α → Matrix (Fin 3) (Fin 3) ℚ := fun i => pcpMatrix ℚ (u i) (v i)
  have fixed : ∀ label, X label *ᵥ headBasis ℚ = headBasis ℚ :=
    fun label => pcpMatrix_mulVec_headBasis ℚ (u label) (v label)
  have anchor_pair : headBasis ℚ ⬝ᵥ headBasis ℚ ≠ 0 := by
    simp [headBasis]
  rw [show absorbedFamily ℚ u v uₜ vₜ =
      separatedGenerator
        (Matrix.vecMulVec (terminalColumn ℚ uₜ vₜ) (headBasis ℚ)) X by
        rfl]
  rw [fixedAnchor_mortal_adjoin_outer_iff X (headBasis ℚ)
    (terminalColumn ℚ uₜ vₜ) (headBasis ℚ) fixed anchor_pair]
  constructor
  · rintro ⟨word, bridge_zero⟩
    exact ⟨word, (bridgeScalar_tileProduct u v uₜ vₜ word).mp
      (by simpa [X, wordProduct, tileProduct] using bridge_zero)⟩
  · rintro ⟨word, terminal_match⟩
    refine ⟨word, ?_⟩
    simpa [X, wordProduct, tileProduct] using
      (bridgeScalar_tileProduct u v uₜ vₜ word).mpr terminal_match

theorem terminalColumn_map {R S : Type*} [CommRing R] [CommRing S]
    (hom : R →+* S) (uₜ vₜ : List Bool) :
    hom ∘ terminalColumn R uₜ vₜ = terminalColumn S uₜ vₜ := by
  funext i
  change hom ((pcpMatrix R uₜ vₜ *ᵥ tailBasis R) i) = _
  rw [RingHom.map_mulVec, pcpMatrix_map, tailBasis_map]
  rfl

theorem terminalGenerator_map {R S : Type*} [CommRing R] [CommRing S]
    (hom : R →+* S) (uₜ vₜ : List Bool) :
    (terminalGenerator R uₜ vₜ).map hom = terminalGenerator S uₜ vₜ := by
  rw [terminalGenerator, vecMulVec_map, terminalColumn_map, headBasis_map]
  rfl

theorem absorbedFamily_map {R S α : Type*} [CommRing R] [CommRing S]
    (hom : R →+* S) (u v : α → List Bool) (uₜ vₜ : List Bool)
    (letter : Option α) :
    (absorbedFamily R u v uₜ vₜ letter).map hom =
      absorbedFamily S u v uₜ vₜ letter := by
  cases letter with
  | none => exact terminalGenerator_map hom uₜ vₜ
  | some i => exact pcpMatrix_map hom (u i) (v i)

theorem terminalGenerator_int_entry_primrec {Input : Type*} [Primcodable Input]
    {uₜ vₜ : Input → List Bool} (uₜRec : Primrec uₜ) (vₜRec : Primrec vₜ)
    (row column : Fin 3) :
    Primrec fun input => terminalGenerator ℤ (uₜ input) (vₜ input) row column := by
  have terminalColumnRec :=
    pcpMatrixInt_entry_primrec uₜRec vₜRec row (2 : Fin 3)
  have zeroRec : Primrec fun _ : Input => (0 : ℤ) := Primrec.const 0
  fin_cases column
  · simpa [terminalGenerator, terminalColumn, Matrix.vecMulVec, Matrix.mulVec,
      dotProduct, headBasis, tailBasis, Fin.sum_univ_succ] using terminalColumnRec
  · simpa [terminalGenerator, Matrix.vecMulVec, headBasis] using zeroRec
  · simpa [terminalGenerator, Matrix.vecMulVec, headBasis] using zeroRec

theorem absorbedFamily_int_entry_primrec {Input Label : Type*} [Primcodable Input]
    (u v : Input → Label → List Bool) (uₜ vₜ : Input → List Bool)
    (uRec : ∀ label, Primrec fun input => u input label)
    (vRec : ∀ label, Primrec fun input => v input label)
    (uₜRec : Primrec uₜ) (vₜRec : Primrec vₜ)
    (label : Option Label) (row column : Fin 3) :
    Primrec fun input => absorbedFamily ℤ (u input) (v input)
      (uₜ input) (vₜ input) label row column := by
  cases label with
  | none =>
      simpa [absorbedFamily, separatedGenerator] using
        terminalGenerator_int_entry_primrec uₜRec vₜRec row column
  | some ordinary =>
      simpa [absorbedFamily, separatedGenerator] using
        pcpMatrixInt_entry_primrec (uRec ordinary) (vRec ordinary) row column

theorem terminalGenerator_int_cast_rank_eq_one (uₜ vₜ : List Bool) :
    (castMatrix (terminalGenerator ℤ uₜ vₜ)).toLin'.rank = 1 := by
  change (Matrix.toLin'
    ((terminalGenerator ℤ uₜ vₜ).map (Int.castRingHom ℚ))).rank = 1
  rw [terminalGenerator_map]
  exact terminalGenerator_rank_eq_one uₜ vₜ

theorem terminalGenerator_int_ne_zero (uₜ vₜ : List Bool) :
    terminalGenerator ℤ uₜ vₜ ≠ 0 := by
  intro hzero
  apply terminalGenerator_ne_zero uₜ vₜ
  rw [← terminalGenerator_map (Int.castRingHom ℚ), hzero]
  simp

theorem absorbedFamily_int_mortal_iff_terminal_match {α : Type*} (u v : α → List Bool)
    (uₜ vₜ : List Bool) :
    IsMortal (absorbedFamily ℤ u v uₜ vₜ) ↔
      ∃ word : List α, spell u word ++ uₜ = spell v word ++ vₜ := by
  rw [← absorbedFamily_mortal_iff_terminal_match]
  have family_cast :
      castMatrix ∘ absorbedFamily ℤ u v uₜ vₜ = absorbedFamily ℚ u v uₜ vₜ := by
    funext label
    exact absorbedFamily_map (Int.castRingHom ℚ) u v uₜ vₜ label
  rw [← family_cast]
  exact (isMortal_cast_iff (absorbedFamily ℤ u v uₜ vₜ)).symm

/-- The exact five-generator specialization used for `M₃(5)`: four ordinary tiles and one
absorbed terminal tile, indexed by `Option (Fin 4)`. -/
theorem five_matrix_reduction (u v : Fin 4 → List Bool) (u₅ v₅ : List Bool) :
    IsMortal (absorbedFamily ℤ u v u₅ v₅) ↔
      ∃ word : List (Fin 4), spell u word ++ u₅ = spell v word ++ v₅ :=
  absorbedFamily_int_mortal_iff_terminal_match u v u₅ v₅

end MatrixMortality
