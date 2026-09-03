import MatrixMortality.ReturnFamily

/-!
# Return compression with a singular ambient generator

Sandwiching an entire physical zero word by the output and input retains both exterior ambient
runs as additional returns. Thus return compression needs no exterior cancellation: the sole
extra obligation beyond the invertible case is that no pure ambient power vanishes.
-/

namespace MatrixMortality

open scoped Matrix

namespace ReturnFamily

variable {R Large Small : Type*} [CommSemiring R]
  [Fintype Large] [DecidableEq Large] [Fintype Small] [DecidableEq Small]

/-- Relabelling along a map with an explicit right inverse preserves mortality. -/
theorem isMortal_comp_rightInverse_iff
    {α β M : Type*} [MonoidWithZero M]
    (generators : β → M) (relabel : α → β) (lift : β → α)
    (right_inverse : Function.RightInverse lift relabel) :
    IsMortal (generators ∘ relabel) ↔ IsMortal generators := by
  constructor
  · rintro ⟨word, word_nonempty, product_zero⟩
    refine ⟨word.map relabel, by simpa using word_nonempty, ?_⟩
    rw [← wordProduct_comp]
    exact product_zero
  · rintro ⟨word, word_nonempty, product_zero⟩
    refine ⟨word.map lift, by simpa using word_nonempty, ?_⟩
    rw [wordProduct_comp]
    have relabel_lift : (word.map lift).map relabel = word := by
      have comp_eq : relabel ∘ lift = id := by
        funext label
        exact right_inverse label
      rw [List.map_map, comp_eq, List.map_id]
    rw [relabel_lift]
    exact product_zero

/-- Sandwiching a nonempty intercalation gives the product of every return, including both
exterior waits. -/
theorem sandwichedIntercalatedPowers_eq_returnProduct
    (ambient : Square Large R) (input : Matrix Large Small R)
    (output : Matrix Small Large R) (first : Nat) (rest : List Nat) :
    output *
          intercalatedProduct (input * output)
            ((first :: rest).map (ambient ^ ·)) *
        input =
      wordProduct (returnMatrix ambient input output) (first :: rest) := by
  induction rest generalizing first with
  | nil =>
      simp [intercalatedProduct, returnMatrix]
  | cons next rest induction =>
      rw [wordProduct_cons]
      simp only [List.map_cons, intercalatedProduct, returnMatrix]
      rw [← induction next]
      simp only [Matrix.mul_assoc]
      rfl

/-- A possibly singular ambient generator loses no zero words under return compression when no
pure ambient power vanishes. Interface compression absorbs both exterior ambient runs as bridge
loops; no splitting hypothesis is needed. -/
theorem pairGenerator_isMortal_iff_returnFamily
    (ambient : Square Large R) (input : Matrix Large Small R)
    (output : Matrix Small Large R)
    (ambient_powers_ne_zero : ∀ n, ambient ^ n ≠ 0) :
    IsMortal (pairGenerator ambient (input * output)) ↔
      IsMortal (returnMatrix ambient input output) := by
  rw [pairGenerator_isMortal_iff_ambient_or_returnFamily]
  apply or_iff_right
  rintro ⟨word, _, product_zero⟩
  rw [wordProduct_const] at product_zero
  exact ambient_powers_ne_zero word.length product_zero

end ReturnFamily

end MatrixMortality
