import MatrixMortality.ReturnFamily

/-!
# Split edge compression

A family of finite-rank generators `Uᵢ * Vᵢ` compresses every nonempty word to the product of
the interface edges `Vᵢ * Uⱼ` along its adjacent labels. Explicit splittings of every `Uᵢ` and
`Vᵢ` make this compression reflect zero exactly.
-/

namespace MatrixMortality

open scoped Matrix

namespace EdgeCompression

variable {R Label Large Small : Type*} [CommSemiring R]
  [Fintype Large] [DecidableEq Large] [Fintype Small] [DecidableEq Small]

/-- Last vertex of a nonempty path represented by its first vertex and remaining vertices. -/
def terminal : Label → List Label → Label
  | start, [] => start
  | _, next :: tail => terminal next tail

/-- Product of a prescribed square edge family along a nonempty labelled path. -/
def pathProduct (edge : Label → Label → Square Small R) : Label → List Label → Square Small R
  | _, [] => 1
  | start, next :: tail => edge start next * pathProduct edge next tail

/-- Concatenating two path tails composes their edge products at the intermediate vertex. -/
theorem pathProduct_append (edge : Label → Label → Square Small R)
    (start : Label) (left right : List Label) :
    pathProduct edge start (left ++ right) =
      pathProduct edge start left * pathProduct edge (terminal start left) right := by
  induction left generalizing start with
  | nil => simp [pathProduct, terminal]
  | cons next tail induction =>
      rw [List.cons_append, pathProduct, induction, pathProduct, terminal, Matrix.mul_assoc]

/-- Product of the interface edges traversed by a nonempty labelled path. -/
def edgeProduct (input : Label → Matrix Large Small R)
    (output : Label → Matrix Small Large R) : Label → List Label → Square Small R
  := pathProduct fun target source => output target * input source

/-- Ambient generator split through the small interface. -/
def generator (input : Label → Matrix Large Small R)
    (output : Label → Matrix Small Large R) (label : Label) : Square Large R :=
  input label * output label

/-- Every nonempty ambient word is its edge product between the first input and final output. -/
theorem wordProduct_cons_eq_sandwich
    (input : Label → Matrix Large Small R)
    (output : Label → Matrix Small Large R)
    (start : Label) (tail : List Label) :
    wordProduct (generator input output) (start :: tail) =
      input start * edgeProduct input output start tail * output (terminal start tail) := by
  induction tail generalizing start with
  | nil =>
      simp [generator, edgeProduct, pathProduct, terminal]
  | cons next tail induction =>
      rw [wordProduct_cons, induction]
      simp only [generator, edgeProduct, pathProduct, terminal, Matrix.mul_assoc]

/-- Split interfaces reduce every nonempty ambient zero exactly to its adjacent-edge zero. -/
theorem wordProduct_cons_eq_zero_iff
    (input : Label → Matrix Large Small R)
    (output : Label → Matrix Small Large R)
    (inputLeftInverse : Label → Matrix Small Large R)
    (outputRightInverse : Label → Matrix Large Small R)
    (left_inverse : ∀ label, inputLeftInverse label * input label = 1)
    (right_inverse : ∀ label, output label * outputRightInverse label = 1)
    (start : Label) (tail : List Label) :
    wordProduct (generator input output) (start :: tail) = 0 ↔
      edgeProduct input output start tail = 0 := by
  rw [wordProduct_cons_eq_sandwich]
  exact ReturnFamily.split_sandwich_eq_zero_iff
    (input start) (output (terminal start tail))
    (inputLeftInverse start) (outputRightInverse (terminal start tail))
    (left_inverse start) (right_inverse (terminal start tail)) _

/-- Mortality of a split finite-rank family is exactly mortality along one nonempty edge path. -/
theorem isMortal_iff_exists_edgeProduct_eq_zero
    (input : Label → Matrix Large Small R)
    (output : Label → Matrix Small Large R)
    (inputLeftInverse : Label → Matrix Small Large R)
    (outputRightInverse : Label → Matrix Large Small R)
    (left_inverse : ∀ label, inputLeftInverse label * input label = 1)
    (right_inverse : ∀ label, output label * outputRightInverse label = 1) :
    IsMortal (generator input output) ↔
      ∃ start tail, edgeProduct input output start tail = 0 := by
  constructor
  · rintro ⟨word, word_nonempty, word_zero⟩
    obtain ⟨start, tail, rfl⟩ := List.exists_cons_of_ne_nil word_nonempty
    exact ⟨start, tail,
      (wordProduct_cons_eq_zero_iff input output inputLeftInverse outputRightInverse
        left_inverse right_inverse start tail).mp word_zero⟩
  · rintro ⟨start, tail, edges_zero⟩
    refine ⟨start :: tail, List.cons_ne_nil _ _, ?_⟩
    exact (wordProduct_cons_eq_zero_iff input output inputLeftInverse outputRightInverse
      left_inverse right_inverse start tail).mpr edges_zero

end EdgeCompression

end MatrixMortality
