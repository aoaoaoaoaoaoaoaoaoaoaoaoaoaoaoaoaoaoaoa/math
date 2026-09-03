import MatrixMortality.ReturnFamily

/-!
# Edge compression

A family of factored generators `Uᵢ * Vᵢ` compresses mortality to products of the interface
edges `Vᵢ * Uⱼ`. Loop-closing the exterior factors makes this exact without splitting. A fixed
physical word still needs split interfaces to reflect zero through its two exterior factors.
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

private def edgeLabelEquiv : Label ≃ Empty ⊕ Label where
  toFun label := .inr label
  invFun
    | .inl impossible => nomatch impossible
    | .inr label => label
  left_inv _ := rfl
  right_inv label := by rcases label with (impossible | label) <;> first | contradiction | rfl

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

/-- Split interfaces reduce one prescribed nonempty ambient word exactly to its adjacent-edge
product. The splits cancel the fixed word's exterior input and output; mortality below instead
loop-closes those factors and needs no cancellation hypothesis. -/
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

private theorem interfacePathProduct_eq_edgeProduct
    (input : Label → Matrix Large Small R) (output : Label → Matrix Small Large R)
    (start : Label) (steps : List (InterfaceCompression.Step Empty Label)) :
    InterfaceCompression.pathProduct (fun label : Empty => nomatch label) input output
        start steps =
      edgeProduct input output start (steps.map Prod.snd) := by
  induction steps generalizing start with
  | nil => simp [InterfaceCompression.pathProduct, edgeProduct, pathProduct]
  | cons step steps induction =>
      obtain ⟨word, target⟩ := step
      have word_eq : word = [] := Subsingleton.elim word []
      rw [InterfaceCompression.pathProduct, List.map_cons, edgeProduct, pathProduct,
        induction]
      simp [InterfaceCompression.bridge, edgeProduct, word_eq]

/-- Mortality of an arbitrary factored family is exactly mortality along one edge path. -/
theorem isMortal_iff_exists_edgeProduct_eq_zero
    (input : Label → Matrix Large Small R)
    (output : Label → Matrix Small Large R) :
    IsMortal (generator input output) ↔
      ∃ start tail, edgeProduct input output start tail = 0 := by
  have generator_eq :
      InterfaceCompression.generator (fun label : Empty => nomatch label) input output ∘
          edgeLabelEquiv =
        generator input output := by
    funext label
    rfl
  rw [← generator_eq, isMortal_comp_equiv, InterfaceCompression.isMortal_iff]
  have empty_immortal :
      ¬IsMortal (fun label : Empty => (nomatch label : Square Large R)) := by
    rintro ⟨word, word_nonempty, _⟩
    exact word_nonempty (Subsingleton.elim word [])
  rw [or_iff_right empty_immortal]
  constructor
  · rintro ⟨start, steps, _, path_zero⟩
    refine ⟨start, steps.map Prod.snd, ?_⟩
    rw [← interfacePathProduct_eq_edgeProduct input output start steps]
    exact path_zero
  · rintro ⟨start, tail, edges_zero⟩
    by_cases tail_nonempty : tail ≠ []
    · let steps : List (InterfaceCompression.Step Empty Label) :=
        tail.map fun target => ([], target)
      refine ⟨start, steps, by simpa [steps] using tail_nonempty, ?_⟩
      rw [interfacePathProduct_eq_edgeProduct input output start steps]
      simpa [steps, Function.comp_def] using edges_zero
    · have tail_eq : tail = [] := not_ne_iff.mp tail_nonempty
      rw [tail_eq] at edges_zero
      have one_eq_zero : (1 : Square Small R) = 0 := by
        simpa [edgeProduct, pathProduct] using edges_zero
      have bridge_zero : output start * input start = 0 := by
        calc
          output start * input start = (output start * input start) * 1 :=
            (Matrix.mul_one _).symm
          _ = (output start * input start) * 0 :=
            congrArg ((output start * input start) * ·) one_eq_zero
          _ = 0 := Matrix.mul_zero _
      refine ⟨start, [([], start)], List.cons_ne_nil _ _, ?_⟩
      simp [InterfaceCompression.pathProduct, InterfaceCompression.bridge, bridge_zero]

end EdgeCompression

end MatrixMortality
