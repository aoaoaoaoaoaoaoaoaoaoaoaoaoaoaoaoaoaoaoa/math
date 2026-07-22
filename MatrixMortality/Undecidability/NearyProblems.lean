import MatrixMortality.Undecidability.Problems

/-!
# Concrete four- and five-label Neary instances

The existing source compiler uses semantic label types.  Computability theory requires fixed,
canonically encoded carriers, so this file transports the four ordinary labels to `Fin 4` and the
four ordinary labels plus terminal separator to `Fin 5`.
-/

namespace MatrixMortality
namespace Undecidability

/-- Canonical enumeration of the four ordinary Neary labels. -/
def nearyTileOfFin : Fin 4 → NearyTile
  | ⟨0, _⟩ => .rule .b
  | ⟨1, _⟩ => .rule .c
  | ⟨2, _⟩ => .erase .b
  | ⟨3, _⟩ => .erase .c

/-- Inverse of `nearyTileOfFin`. -/
def finOfNearyTile : NearyTile → Fin 4
  | .rule .b => 0
  | .rule .c => 1
  | .erase .b => 2
  | .erase .c => 3

theorem nearyTileOfFin_finOfNearyTile (tile : NearyTile) :
    nearyTileOfFin (finOfNearyTile tile) = tile := by
  cases tile with
  | rule letter | erase letter => cases letter <;> rfl

theorem finOfNearyTile_nearyTileOfFin (label : Fin 4) :
    finOfNearyTile (nearyTileOfFin label) = label := by
  fin_cases label <;> rfl

/-- The fixed computable equivalence used at the four-generator boundary. -/
def nearyTileEquivFin : NearyTile ≃ Fin 4 where
  toFun := finOfNearyTile
  invFun := nearyTileOfFin
  left_inv := nearyTileOfFin_finOfNearyTile
  right_inv := finOfNearyTile_nearyTileOfFin

/-- Canonical enumeration of the terminal label and four ordinary labels. -/
def nearyGeneratorOfFin : Fin 5 → Option NearyTile
  | ⟨0, _⟩ => some (.rule .b)
  | ⟨1, _⟩ => some (.rule .c)
  | ⟨2, _⟩ => some (.erase .b)
  | ⟨3, _⟩ => some (.erase .c)
  | ⟨4, _⟩ => none

/-- Inverse of `nearyGeneratorOfFin`. -/
def finOfNearyGenerator : Option NearyTile → Fin 5
  | some tile => Fin.castLE (by omega) (finOfNearyTile tile)
  | none => 4

theorem nearyGeneratorOfFin_finOfNearyGenerator (label : Option NearyTile) :
    nearyGeneratorOfFin (finOfNearyGenerator label) = label := by
  cases label with
  | none => rfl
  | some tile =>
      cases tile with
      | rule letter | erase letter => cases letter <;> rfl

theorem finOfNearyGenerator_nearyGeneratorOfFin (label : Fin 5) :
    finOfNearyGenerator (nearyGeneratorOfFin label) = label := by
  fin_cases label <;> rfl

/-- The fixed computable equivalence used at the five-generator boundary. -/
def nearyGeneratorEquivFin : Option NearyTile ≃ Fin 5 where
  toFun := finOfNearyGenerator
  invFun := nearyGeneratorOfFin
  left_inv := nearyGeneratorOfFin_finOfNearyGenerator
  right_inv := finOfNearyGenerator_nearyGeneratorOfFin

private theorem spell_comp_map {a b c : Type*} (side : b → List c) (f : a → b)
    (word : List a) :
    spell (side ∘ f) word = spell side (word.map f) := by
  simp [spell, Function.comp_def]

private theorem isMortal_comp_equiv {a b M : Type*} [MonoidWithZero M]
    (generators : b → M) (equivalence : a ≃ b) :
    IsMortal (generators ∘ equivalence) ↔ IsMortal generators := by
  constructor
  · rintro ⟨word, word_ne, product_zero⟩
    refine ⟨word.map equivalence, ?_, ?_⟩
    · simpa using word_ne
    · simpa [List.map_map, Function.comp_def] using product_zero
  · rintro ⟨word, word_ne, product_zero⟩
    refine ⟨word.map equivalence.symm, ?_, ?_⟩
    · simpa using word_ne
    · simpa [List.map_map, Function.comp_def] using product_zero

/-- The four-generator binary GPCP problem emitted by one restricted tag source. -/
def nearyGPCP4 (beta : Nat) (body : List TagLetter) : BinaryGPCP4 where
  upper := nearyUpper beta ∘ nearyTileOfFin
  lower := nearyLower beta body ∘ nearyTileOfFin
  upperLeft := []
  upperRight := nearyMarker beta
  lowerLeft := []
  lowerRight := []

theorem nearyGPCP4_solvable_iff_tagHaltsFrom (beta : Nat) (body : List TagLetter)
    (beta_large : 2 < beta) (body_long : beta - 1 ≤ body.length)
    (body_divisible : beta - 1 ∣ body.length) :
    (nearyGPCP4 beta body).Solvable ↔
      TagHaltsFrom beta (tagOutput body) (body.drop (beta - 1) ++ [.b]) := by
  rw [← nearyGPCP_solvable_iff_tagHaltsFrom beta body beta_large body_long body_divisible]
  constructor
  · rintro ⟨word, solution⟩
    refine ⟨word.map nearyTileOfFin, ?_⟩
    simpa [BinaryGPCP4.Solvable, IsGPCPSolution, nearyGPCP4, spell_comp_map] using solution
  · rintro ⟨word, solution⟩
    refine ⟨word.map finOfNearyTile, ?_⟩
    simp only [nearyGPCP4, List.nil_append, List.append_nil]
    rw [spell_comp_map, spell_comp_map]
    simpa [IsGPCPSolution, List.map_map, Function.comp_def,
      nearyTileOfFin_finOfNearyTile] using solution

/-- The five `3 × 3` integer matrices emitted by one restricted tag source. -/
def nearyMortality35 (beta : Nat) (body : List TagLetter) : Mortality35 :=
  fun label row column =>
    nearyMortalityFamilyInt beta body (nearyGeneratorOfFin label) row column

theorem nearyMortality35_mortal_iff_tagHaltsFrom (beta : Nat) (body : List TagLetter)
    (beta_large : 2 < beta) (body_long : beta - 1 ≤ body.length)
    (body_divisible : beta - 1 ∣ body.length) :
    (nearyMortality35 beta body).Mortal ↔
      TagHaltsFrom beta (tagOutput body) (body.drop (beta - 1) ++ [.b]) := by
  rw [← nearyMortalityFamilyInt_mortal_iff_tagHaltsFrom beta body beta_large body_long
    body_divisible]
  exact isMortal_comp_equiv (nearyMortalityFamilyInt beta body) nearyGeneratorEquivFin.symm

end Undecidability
end MatrixMortality
