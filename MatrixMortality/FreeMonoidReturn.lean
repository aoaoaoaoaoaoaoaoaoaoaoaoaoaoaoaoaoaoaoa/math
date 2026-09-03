import MatrixMortality.InterfaceCompression
import MatrixMortality.TerminalTile

/-!
# Free-monoid returns with a rank-one empty return

Two arbitrary transition matrices and one rank-two cut compress to a matrix-valued return
family indexed by the transition free monoid. If its empty return is rank one, adjoining that
return to the nonempty returns reduces mortality to one scalar bridge. The nonempty returns may
be singular; unit transitions are needed only to exclude a zero word containing no cut.
-/

namespace MatrixMortality.FreeMonoidReturn

open scoped Matrix

variable {α Large Small K : Type*} [Field K]
  [Fintype Large] [DecidableEq Large] [Fintype Small] [DecidableEq Small]

/-- Canonical spelling of a nonempty word by its head and tail. -/
def positiveWord (word : α × List α) : List α :=
  word.1 :: word.2

/-- The return across an arbitrary transition word. -/
def returnMatrix (transitions : α → Square Large K) (input : Matrix Large Small K)
    (output : Matrix Small Large K) (word : List α) : Square Small K :=
  output * wordProduct transitions word * input

/-- The return across a nonempty transition word. -/
def positiveReturn (transitions : α → Square Large K) (input : Matrix Large Small K)
    (output : Matrix Small Large K) (word : α × List α) : Square Small K :=
  returnMatrix transitions input output (positiveWord word)

/-- The empty word and the head-tail spellings partition the transition free monoid. -/
def optionPositiveWordEquiv : Option (α × List α) ≃ List α where
  toFun
    | none => []
    | some word => positiveWord word
  invFun
    | [] => none
    | head :: tail => some (head, tail)
  left_inv word := by cases word <;> rfl
  right_inv word := by cases word <;> rfl

theorem pathProduct_eq_wordProduct
    (transitions : α → Square Large K) (input : Matrix Large Small K)
    (output : Matrix Small Large K) (steps : List (List α × Unit)) :
    InterfaceCompression.pathProduct transitions (fun _ : Unit => input)
        (fun _ : Unit => output) () steps =
      wordProduct (returnMatrix transitions input output) (steps.map Prod.fst) := by
  induction steps with
  | nil => rfl
  | cons step steps induction =>
      obtain ⟨word, target⟩ := step
      cases target
      simp only [InterfaceCompression.pathProduct, List.map_cons, wordProduct_cons]
      rw [induction]
      rfl

/-- One cut compresses exactly to the complete return family. No splitting hypothesis is
needed; transition-only mortality remains as an explicit disjunct. -/
theorem physical_isMortal_iff_returnFamily
    (transitions : α → Square Large K) (input : Matrix Large Small K)
    (output : Matrix Small Large K) :
    IsMortal
        (InterfaceCompression.generator transitions (fun _ : Unit => input)
          (fun _ : Unit => output)) ↔
      IsMortal transitions ∨ IsMortal (returnMatrix transitions input output) := by
  rw [InterfaceCompression.isMortal_iff]
  apply or_congr_right
  constructor
  · rintro ⟨start, steps, steps_nonempty, product_zero⟩
    cases start
    refine ⟨steps.map Prod.fst, by simpa using steps_nonempty, ?_⟩
    rw [← pathProduct_eq_wordProduct]
    exact product_zero
  · rintro ⟨words, words_nonempty, product_zero⟩
    let steps : List (List α × Unit) := words.map (·, ())
    refine ⟨(), steps, by simpa [steps] using words_nonempty, ?_⟩
    rw [pathProduct_eq_wordProduct]
    have step_words : steps.map Prod.fst = words := by
      change (words.map fun word => (word, ())).map Prod.fst = words
      rw [List.map_map]
      change words.map id = words
      simp
    rw [step_words]
    exact product_zero

theorem returnFamily_isMortal_iff_rankOneEmptyReturn
    (transitions : α → Square Large K) (input : Matrix Large Small K)
    (output : Matrix Small Large K) (column row : Small → K)
    (empty_return : output * input = Matrix.vecMulVec column row) :
    IsMortal (returnMatrix transitions input output) ↔
      ∃ words : List (α × List α),
        bridgeScalar column row
          (wordProduct (positiveReturn transitions input output) words) = 0 := by
  have separated_returns :
      returnMatrix transitions input output ∘ optionPositiveWordEquiv =
        separatedGenerator (Matrix.vecMulVec column row)
          (positiveReturn transitions input output) := by
    funext word
    cases word with
    | none =>
        change returnMatrix transitions input output [] = Matrix.vecMulVec column row
        simpa [returnMatrix] using empty_return
    | some word => rfl
  rw [← isMortal_comp_equiv
    (returnMatrix transitions input output) optionPositiveWordEquiv]
  rw [separated_returns]
  exact mortal_adjoin_outer_iff (positiveReturn transitions input output) column row

/-- Free-monoid rank-one-empty-return reduction. It remains exact when any nonempty return is
singular or zero; such a return already supplies a scalar-zero bridge. -/
theorem physical_isMortal_iff_rankOneEmptyReturn
    (transitions : α → Square Large K) (input : Matrix Large Small K)
    (output : Matrix Small Large K) (column row : Small → K)
    (empty_return : output * input = Matrix.vecMulVec column row) :
    IsMortal
        (InterfaceCompression.generator transitions (fun _ : Unit => input)
          (fun _ : Unit => output)) ↔
      IsMortal transitions ∨
        ∃ words : List (α × List α),
          bridgeScalar column row
            (wordProduct (positiveReturn transitions input output) words) = 0 := by
  exact (physical_isMortal_iff_returnFamily transitions input output).trans
    (or_congr Iff.rfl
      (returnFamily_isMortal_iff_rankOneEmptyReturn transitions input output column row
        empty_return))

/-- For unit transitions, physical mortality is exactly scalar incidence under a finite list of
nonempty word-indexed returns. No unit hypothesis on those returns is required. -/
theorem physical_isMortal_iff_rankOneEmptyReturn_of_transitionUnits
    [Nonempty Large]
    (transitions : α → Square Large K) (input : Matrix Large Small K)
    (output : Matrix Small Large K) (column row : Small → K)
    (transition_unit : ∀ label, IsUnit (transitions label))
    (empty_return : output * input = Matrix.vecMulVec column row) :
    IsMortal
        (InterfaceCompression.generator transitions (fun _ : Unit => input)
          (fun _ : Unit => output)) ↔
      ∃ words : List (α × List α),
        bridgeScalar column row
          (wordProduct (positiveReturn transitions input output) words) = 0 := by
  rw [physical_isMortal_iff_rankOneEmptyReturn transitions input output column row
    empty_return]
  exact or_iff_right (not_isMortal_of_forall_isUnit transitions transition_unit)

end MatrixMortality.FreeMonoidReturn
