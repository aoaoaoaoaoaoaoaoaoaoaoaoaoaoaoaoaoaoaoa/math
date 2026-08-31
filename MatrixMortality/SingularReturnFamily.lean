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
pure ambient power vanishes. -/
theorem pairGenerator_isMortal_iff_returnFamily
    (ambient : Square Large R) (input : Matrix Large Small R)
    (output : Matrix Small Large R)
    (ambient_powers_ne_zero : ∀ n, ambient ^ n ≠ 0) :
    IsMortal (pairGenerator ambient (input * output)) ↔
      IsMortal (returnMatrix ambient input output) := by
  constructor
  · rintro ⟨word, word_nonempty, product_zero⟩
    by_cases cut_mem : none ∈ word
    · let waits := (fracture word).map List.length
      have waits_nonempty : waits ≠ [] := by
        simpa [waits] using fracture_ne_nil word
      refine ⟨waits, waits_nonempty, ?_⟩
      obtain ⟨first, rest, waits_eq⟩ := List.exists_cons_of_ne_nil waits_nonempty
      have physical_eq :
          wordProduct (pairGenerator ambient (input * output)) word =
            intercalatedProduct (input * output)
              (waits.map (ambient ^ ·)) := by
        rw [pairGenerator, wordProduct_separatedGenerator_eq_intercalatedProduct]
        congr 1
        change
          (fracture word).map (wordProduct fun _ : Unit => ambient) =
            ((fracture word).map List.length).map (ambient ^ ·)
        rw [List.map_map]
        apply List.map_congr_left
        intro block _
        exact wordProduct_const ambient block
      rw [waits_eq, ← sandwichedIntercalatedPowers_eq_returnProduct]
      rw [← waits_eq, ← physical_eq, product_zero]
      simp
    · change
        wordProduct
            (separatedGenerator (input * output) (fun _ : Unit => ambient)) word = 0
          at product_zero
      obtain ⟨ordinary, rfl⟩ := exists_eq_map_some_of_none_not_mem word cut_mem
      rw [wordProduct_separatedGenerator_map_some, wordProduct_const] at product_zero
      exact (ambient_powers_ne_zero ordinary.length product_zero).elim
  · rintro ⟨waits, _, returns_zero⟩
    change returnProduct ambient input output waits = 0 at returns_zero
    refine ⟨blockedWord waits, ?_, ?_⟩
    · cases waits <;> simp [blockedWord]
    · rw [wordProduct_blockedWord, blockedProduct_eq_sandwich, returns_zero]
      simp

end ReturnFamily

end MatrixMortality
