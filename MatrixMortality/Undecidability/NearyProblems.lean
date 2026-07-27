import MatrixMortality.NearyEncoding
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

/-- The four-generator binary GPCP problem emitted by one restricted tag source. -/
def nearyGPCP4 (beta : Nat) (body : List TagLetter) : BinaryGPCP4 where
  upper := nearyUpper beta ∘ nearyTileOfFin
  lower := nearyLower beta body ∘ nearyTileOfFin
  upperLeft := []
  upperRight := nearyMarker beta
  lowerLeft := []
  lowerRight := []

/-- Each semantic lower word is primitive recursive in the variable Neary body. -/
theorem nearyLower_primrec (beta : Nat) (tile : NearyTile) :
    Primrec fun body => nearyLower beta body tile := by
  cases tile with
  | rule letter =>
      cases letter with
      | b => exact Primrec.const _
      | c =>
          exact
            (Primrec.list_append.comp (Primrec.const [true])
              (Primrec.list_append.comp (tagEncode_primrec beta)
                (Primrec.const [true, false]))).of_eq fun body => by
                  rfl
  | erase letter =>
      cases letter <;> exact Primrec.const _

/-- The four-generator GPCP compiler is primitive recursive in its variable body. -/
theorem nearyGPCP4_primrec (beta : Nat) :
    Primrec (nearyGPCP4 beta) := by
  have upperRec :
      Primrec fun _ : List TagLetter =>
        nearyUpper beta ∘ nearyTileOfFin :=
    Primrec.const _
  have lowerRec :
      Primrec fun body : List TagLetter =>
        nearyLower beta body ∘ nearyTileOfFin := by
    apply MatrixMortality.Primrec.fin_function
    intro label
    exact nearyLower_primrec beta (nearyTileOfFin label)
  exact
    BinaryGPCP4.primrec_mk
      (fun _ => nearyUpper beta ∘ nearyTileOfFin)
      (fun body => nearyLower beta body ∘ nearyTileOfFin)
      (fun _ => []) (fun _ => nearyMarker beta)
      (fun _ => []) (fun _ => [])
      upperRec lowerRec
      (Primrec.const []) (Primrec.const (nearyMarker beta))
      (Primrec.const []) (Primrec.const [])

theorem nearyGPCP4_solvable_iff_tagHaltsFrom (beta : Nat) (body : List TagLetter)
    (beta_large : 2 < beta) (body_long : beta - 1 ≤ body.length)
    (body_divisible : beta - 1 ∣ body.length) :
    (nearyGPCP4 beta body).Solvable ↔
      TagHaltsFrom beta (tagOutput body) (body.drop (beta - 1) ++ [.b]) := by
  rw [← nearyGPCP_solvable_iff_tagHaltsFrom beta body beta_large body_long body_divisible]
  simpa [BinaryGPCP4.Solvable, nearyGPCP4, IsGPCPSolution] using
    gpcpSolvable_relabel_equiv (nearyUpper beta) (nearyLower beta body)
      [] (nearyMarker beta) [] [] nearyTileEquivFin.symm

/-- The five `3 × 3` integer matrices emitted by one restricted tag source. -/
def nearyMortality35 (beta : Nat) (body : List TagLetter) : Mortality35 :=
  fun label row column =>
    nearyMortalityFamilyInt beta body (nearyGeneratorOfFin label) row column

/-- The five-matrix mortality compiler is primitive recursive in its variable body. -/
theorem nearyMortality35_primrec (beta : Nat) :
    Primrec (nearyMortality35 beta) := by
  apply MatrixMortality.Primrec.fin_function
  intro label
  apply MatrixMortality.Primrec.fin_function
  intro row
  apply MatrixMortality.Primrec.fin_function
  intro column
  exact absorbedFamily_int_entry_primrec
    (fun _ tile => nearyUpper beta tile)
    (fun body tile => nearyLower beta body tile)
    (fun _ => nearyMarker beta) (fun _ => [])
    (fun tile => Primrec.const (nearyUpper beta tile))
    (nearyLower_primrec beta)
    (Primrec.const (nearyMarker beta)) (Primrec.const [])
    (nearyGeneratorOfFin label) row column

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
