import MatrixMortality.PairedBinary
import MatrixMortality.Undecidability.NearyProblems

/-!
# Canonical two-matrix scalar-zero instances

This file transports the semantic bit alphabet to `Fin 2` and transposes the six-state compiler.
The resulting matrices share first column `e₁`; word reversal preserves the represented zero
language.
-/

namespace MatrixMortality
namespace Undecidability

open scoped Matrix

/-- The structured two-matrix, six-state scalar-zero problem emitted by one restricted tag
source. -/
def nearyScalarZero62 (β : Nat) (body : List TagLetter) : ScalarZero62 where
  matrix label := (pairedBinaryGenerator ℤ β body (finTwoEquiv label))ᵀ
  row := pairedBinaryBoundaryColumn ℤ
  column := pairedBinaryBoundaryRow ℤ β

private theorem vecCons_val_three {α : Type*} {n : Nat}
    (head : α) (tail : Fin (n + 3) → α) :
    Matrix.vecCons head tail (3 : Fin (n + 4)) = tail 2 := rfl

private theorem vecCons_val_four {α : Type*} {n : Nat}
    (head : α) (tail : Fin (n + 4) → α) :
    Matrix.vecCons head tail (4 : Fin (n + 5)) = tail 3 := rfl

private theorem vecCons_val_five {α : Type*} {n : Nat}
    (head : α) (tail : Fin (n + 5) → α) :
    Matrix.vecCons head tail (5 : Fin (n + 6)) = tail 4 := rfl

attribute [local simp] vecCons_val_three vecCons_val_four vecCons_val_five

private theorem pairedBinaryGenerator_int_entry_primrec (β : Nat) (bit : Bool)
    (row column : Fin 6) :
    Primrec fun body : List TagLetter =>
      pairedBinaryGenerator ℤ β body bit row column := by
  cases bit with
  | false =>
      exact Primrec.const
        (pairedBinaryGenerator ℤ β ([] : List TagLetter) false row column)
  | true =>
      have ruleWord := nearyLower_primrec β (.rule .c)
      have eraseWord := nearyLower_primrec β (.erase .c)
      have ruleCode := ternaryCode_int_primrec.comp ruleWord
      have eraseCode := ternaryCode_int_primrec.comp eraseWord
      have ruleScale := ternaryScale_int_primrec.comp ruleWord
      fin_cases row <;> fin_cases column <;>
        simp [pairedBinaryGenerator, Matrix.vecHead, Matrix.vecTail]
      all_goals first | exact Primrec.const _ | exact ruleCode | exact eraseCode |
        exact ruleScale

/-- The two-matrix scalar-zero compiler is primitive recursive in its variable body. -/
theorem nearyScalarZero62_primrec (β : Nat) :
    Primrec (nearyScalarZero62 β) := by
  apply ScalarZeroProblem.primrec_mk
  · intro label row column
    fin_cases label
    · simpa [nearyScalarZero62] using
        pairedBinaryGenerator_int_entry_primrec β false column row
    · simpa [nearyScalarZero62] using
        pairedBinaryGenerator_int_entry_primrec β true column row
  · intro coordinate
    exact Primrec.const _
  · intro coordinate
    exact Primrec.const _

theorem nearyScalarZero62_coefficient (β : Nat) (body : List TagLetter)
    (word : List (Fin 2)) :
    (nearyScalarZero62 β body).coefficient word =
      pairedBinaryCoefficient ℤ β body ((word.map finTwoEquiv).reverse) := by
  change
    pairedBinaryBoundaryColumn ℤ ⬝ᵥ
        wordProduct
            (fun label : Fin 2 =>
              (pairedBinaryGenerator ℤ β body (finTwoEquiv label))ᵀ)
            word *ᵥ
          pairedBinaryBoundaryRow ℤ β =
      pairedBinaryCoefficient ℤ β body ((word.map finTwoEquiv).reverse)
  have product_relabel :
      wordProduct
          (fun label : Fin 2 =>
            (pairedBinaryGenerator ℤ β body (finTwoEquiv label))ᵀ)
          word =
        wordProduct (Matrix.transpose ∘ pairedBinaryGenerator ℤ β body)
          (word.map finTwoEquiv) := by
    simp [wordProduct, List.map_map, Function.comp_def]
  rw [product_relabel, scalarCoefficient_transpose]
  rfl

theorem nearyScalarZero62_hasZero_iff_pairedBinaryZero (β : Nat)
    (body : List TagLetter) :
    (nearyScalarZero62 β body).HasZero ↔
      WordSeries.HasNonemptyZero (pairedBinaryCoefficient ℤ β body) := by
  constructor
  · rintro ⟨word, word_nonempty, coefficient_zero⟩
    refine ⟨(word.map finTwoEquiv).reverse, by simpa using word_nonempty, ?_⟩
    rw [← nearyScalarZero62_coefficient]
    exact coefficient_zero
  · rintro ⟨bits, bits_nonempty, coefficient_zero⟩
    let word := bits.reverse.map finTwoEquiv.symm
    have word_nonempty : word ≠ [] := by
      simpa [word] using bits_nonempty
    refine ⟨word, word_nonempty, ?_⟩
    rw [nearyScalarZero62_coefficient]
    simpa [word, List.map_map, Function.comp_def] using coefficient_zero

theorem nearyScalarZero62_empty_coefficient_ne_zero (β : Nat) (body : List TagLetter) :
    (nearyScalarZero62 β body).coefficient [] ≠ 0 := by
  rw [nearyScalarZero62_coefficient]
  exact pairedBinaryCoefficient_nil_ne_zero β body

theorem nearyScalarZero62_hasZero_iff_hasZeroStar (β : Nat) (body : List TagLetter) :
    (nearyScalarZero62 β body).HasZero ↔ (nearyScalarZero62 β body).HasZeroStar :=
  ScalarZeroProblem.hasZero_iff_hasZeroStar_of_empty_ne _
    (nearyScalarZero62_empty_coefficient_ne_zero β body)

theorem nearyScalarZero62_hasZero_iff_tagHaltsFrom (β : Nat) (body : List TagLetter)
    (β_large : 2 < β) (body_long : β - 1 ≤ body.length)
    (body_divisible : β - 1 ∣ body.length) :
    (nearyScalarZero62 β body).HasZero ↔
      TagHaltsFrom β (tagOutput body) (body.drop (β - 1) ++ [.b]) := by
  rw [nearyScalarZero62_hasZero_iff_pairedBinaryZero]
  exact pairedBinary_zero_iff_tagHaltsFrom β body β_large body_long body_divisible

theorem nearyScalarZero62_hasZeroStar_iff_tagHaltsFrom (β : Nat)
    (body : List TagLetter) (β_large : 2 < β) (body_long : β - 1 ≤ body.length)
    (body_divisible : β - 1 ∣ body.length) :
    (nearyScalarZero62 β body).HasZeroStar ↔
      TagHaltsFrom β (tagOutput body) (body.drop (β - 1) ++ [.b]) := by
  rw [← nearyScalarZero62_hasZero_iff_hasZeroStar]
  exact nearyScalarZero62_hasZero_iff_tagHaltsFrom β body β_large body_long body_divisible

/-- Both matrices in the canonical family share first column `e₁`. -/
theorem nearyScalarZero62_fixes_anchor (β : Nat) (body : List TagLetter)
    (label : Fin 2) :
    (nearyScalarZero62 β body).matrix label *ᵥ pairedBinaryBoundaryColumn ℤ =
      pairedBinaryBoundaryColumn ℤ := by
  exact pairedBinaryGenerator_transpose_fixes_boundaryColumn ℤ β body
    (finTwoEquiv label)

end Undecidability

namespace NearyArithmeticEnvelope

/-- The exact structured scalar-zero instance emitted by an arithmetic-envelope source. -/
def scalarZero62 (source : NearyArithmeticEnvelope) : Undecidability.ScalarZero62 :=
  Undecidability.nearyScalarZero62 source.β source.body

theorem scalarZero62_iff_halts (source : NearyArithmeticEnvelope) :
    source.scalarZero62.HasZero ↔
      TagHaltsFrom source.β (tagOutput source.body) source.initial := by
  exact Undecidability.nearyScalarZero62_hasZero_iff_tagHaltsFrom source.β source.body
    source.beta_large source.body_long source.body_divisible

end NearyArithmeticEnvelope
end MatrixMortality
