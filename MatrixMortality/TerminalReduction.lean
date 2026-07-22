import MatrixMortality.PCPEncoding
import MatrixMortality.TerminalTile

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

/-- Concatenate the words selected by a tile-index word. -/
def spell {α β : Type*} (side : α → List β) (word : List α) : List β :=
  (word.map side).join

/-- Product of the PCP matrices selected by a tile-index word. -/
def tileProduct {α R : Type*} [CommRing R] (u v : α → List Bool) (word : List α) :
    Matrix (Fin 3) (Fin 3) R :=
  (word.map fun i => pcpMatrix R (u i) (v i)).prod

theorem tileProduct_eq_pcpMatrix {α R : Type*} [CommRing R]
    (u v : α → List Bool) (word : List α) :
    tileProduct u v word = pcpMatrix R (spell u word) (spell v word) := by
  induction word with
  | nil => simp [tileProduct, spell]
  | cons i word ih =>
      simp only [tileProduct, spell, List.map_cons, List.prod_cons, List.join_cons]
      rw [show (word.map fun j => pcpMatrix R (u j) (v j)).prod =
          tileProduct u v word from rfl]
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

/-- A labelled family is mortal when a nonempty generator word multiplies to zero. -/
def IsMortal {α M : Type*} [MonoidWithZero M] (generators : α → M) : Prop :=
  ∃ word : List α, word ≠ [] ∧ (word.map generators).prod = 0

/-- The rational family of ordinary PCP matrices and one absorbed terminal separator. -/
def absorbedFamily {α : Type*} (u v : α → List Bool) (uₜ vₜ : List Bool) :
    Option α → Matrix (Fin 3) (Fin 3) ℚ :=
  separatedGenerator (terminalGenerator uₜ vₜ) (fun i => pcpMatrix ℚ (u i) (v i))

theorem absorbedFamily_mortal_iff_terminal_match {α : Type*} (u v : α → List Bool)
    (uₜ vₜ : List Bool) :
    IsMortal (absorbedFamily u v uₜ vₜ) ↔
      ∃ word : List α, spell u word ++ uₜ = spell v word ++ vₜ := by
  let c := terminalColumn uₜ vₜ
  let r := headBasis ℚ
  let A := terminalGenerator uₜ vₜ
  let X : α → Matrix (Fin 3) (Fin 3) ℚ := fun i => pcpMatrix ℚ (u i) (v i)
  have hc : c ≠ 0 := terminalColumn_ne_zero uₜ vₜ
  have hr : r ≠ 0 := headBasis_ne_zero ℚ
  have hX : ∀ i, IsUnit (X i) := fun i => pcpMatrix_isUnit_rat (u i) (v i)
  constructor
  · rintro ⟨raw, _, hzero⟩
    have hproduct : generatorProduct A X raw = 0 := by
      simpa [IsMortal, absorbedFamily, generatorProduct, A, X] using hzero
    have hnone : none ∈ raw := by
      by_contra hnone
      exact (generatorProduct_isUnit_of_none_not_mem A hX hnone).ne_zero hproduct
    rw [generatorProduct_eq_rankOneChain] at hproduct
    have hlength := fracture_length_two_le_of_none_mem hnone
    have hfracture := fracture_ne_nil raw
    rcases List.exists_cons_of_ne_nil hfracture with ⟨first, rest, hfirst⟩
    have hrest : rest ≠ [] := by
      intro hnil
      rw [hfirst, hnil] at hlength
      simp at hlength
    let last := rest.getLast hrest
    let middle := rest.dropLast
    have hdecomp : fracture raw = first :: middle ++ [last] := by
      rw [hfirst]
      congr 1
      exact (List.dropLast_append_getLast hrest).symm
    have hmapped : (fracture raw).map (blockProduct X) =
        blockProduct X first :: (middle.map (blockProduct X)) ++ [blockProduct X last] := by
      simp [hdecomp]
    rw [hmapped] at hproduct
    have hbridge := (rankOneChain_eq_zero_iff c r (blockProduct X first)
      (blockProduct X last) (middle.map (blockProduct X)) hc hr
      (blockProduct_isUnit hX first) (blockProduct_isUnit hX last)).mp hproduct
    rcases hbridge with ⟨P, hP, hPzero⟩
    rcases List.mem_map.mp hP with ⟨word, _, rfl⟩
    refine ⟨word, (bridgeScalar_tileProduct u v uₜ vₜ word).mp ?_⟩
    simpa [c, r, X, blockProduct, tileProduct] using hPzero
  · rintro ⟨word, hmatch⟩
    have hbridge : bridgeScalar c r (tileProduct u v word) = 0 :=
      (bridgeScalar_tileProduct u v uₜ vₜ word).mpr hmatch
    have hchain : rankOneChain A
        (1 :: [tileProduct u v word] ++ [1]) = 0 := by
      apply (rankOneChain_eq_zero_iff c r 1 1 [tileProduct u v word] hc hr
        (isUnit_one) (isUnit_one)).mpr
      exact ⟨tileProduct u v word, by simp, hbridge⟩
    refine ⟨none :: word.map some ++ [none], by simp, ?_⟩
    have hfracture : fracture (none :: word.map some ++ [none]) = [[], word, []] := by
      simp [fracture, fracture_map_some_append_none]
    change generatorProduct A X (none :: word.map some ++ [none]) = 0
    rw [generatorProduct_eq_rankOneChain, hfracture]
    simpa [blockProduct, tileProduct, A, X] using hchain

/-- Entrywise inclusion of an integer matrix into the rationals. -/
def castMatrix (M : Matrix (Fin 3) (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℚ :=
  M.map (Int.castRingHom ℚ)

/-- Entrywise inclusion of an integer vector into the rationals. -/
def castVector (v : Fin 3 → ℤ) : Fin 3 → ℚ := fun i => v i

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

theorem castMatrix_mulVec (M : Matrix (Fin 3) (Fin 3) ℤ) (v : Fin 3 → ℤ) :
    castVector (M *ᵥ v) = castMatrix M *ᵥ castVector v := by
  funext i
  simp [castVector, castMatrix, Matrix.mulVec, Matrix.dotProduct]

theorem castMatrix_vecMulVec (c r : Fin 3 → ℤ) :
    castMatrix (Matrix.vecMulVec c r) =
      Matrix.vecMulVec (castVector c) (castVector r) := by
  ext i j
  simp [castMatrix, castVector, Matrix.vecMulVec]

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

theorem castMatrix_eq_zero_iff (M : Matrix (Fin 3) (Fin 3) ℤ) :
    castMatrix M = 0 ↔ M = 0 := by
  constructor
  · intro h
    ext i j
    have hij := congr_fun (congr_fun h i) j
    simpa [castMatrix] using hij
  · rintro rfl
    simp [castMatrix]

theorem castMatrix_absorbedProduct {α : Type*} (u v : α → List Bool)
    (uₜ vₜ : List Bool) (word : List (Option α)) :
    castMatrix ((word.map (absorbedFamilyInt u v uₜ vₜ)).prod) =
      (word.map (absorbedFamily u v uₜ vₜ)).prod := by
  induction word with
  | nil => simp [castMatrix]
  | cons letter word ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [show castMatrix
          (absorbedFamilyInt u v uₜ vₜ letter *
            (word.map (absorbedFamilyInt u v uₜ vₜ)).prod) =
          castMatrix (absorbedFamilyInt u v uₜ vₜ letter) *
            castMatrix ((word.map (absorbedFamilyInt u v uₜ vₜ)).prod) by
        ext i j
        simp [castMatrix, Matrix.mul_apply]]
      rw [castMatrix_absorbedFamilyInt, ih]

theorem absorbedFamilyInt_mortal_iff_terminal_match {α : Type*} (u v : α → List Bool)
    (uₜ vₜ : List Bool) :
    IsMortal (absorbedFamilyInt u v uₜ vₜ) ↔
      ∃ word : List α, spell u word ++ uₜ = spell v word ++ vₜ := by
  rw [← absorbedFamily_mortal_iff_terminal_match]
  constructor
  · rintro ⟨word, hword, hzero⟩
    refine ⟨word, hword, ?_⟩
    rw [← castMatrix_absorbedProduct]
    exact (castMatrix_eq_zero_iff _).mpr hzero
  · rintro ⟨word, hword, hzero⟩
    refine ⟨word, hword, ?_⟩
    apply (castMatrix_eq_zero_iff _).mp
    rw [castMatrix_absorbedProduct]
    exact hzero

/-- The exact five-generator specialization used for `M₃(5)`: four ordinary tiles and one
absorbed terminal tile, indexed by `Option (Fin 4)`. -/
theorem five_matrix_reduction (u v : Fin 4 → List Bool) (u₅ v₅ : List Bool) :
    IsMortal (absorbedFamilyInt u v u₅ v₅) ↔
      ∃ word : List (Fin 4), spell u word ++ u₅ = spell v word ++ v₅ :=
  absorbedFamilyInt_mortal_iff_terminal_match u v u₅ v₅

end MatrixMortality
