import MatrixMortality.MatrixSemigroup

/-!
# Interface compression

A labelled matrix family splits into *transitions*, which are arbitrary, and *cuts*, each of
which factors through one interface space as `input cut * output cut`. Every physical word is
one transition word followed by cut-headed blocks. Sandwiching a physical zero between the
output of its first cut and the input of its last cut retains both exterior transition words
as loops, so the family is mortal exactly when the transitions alone are mortal or one nonempty
path of interface bridges `output source * transitions(word) * input target` vanishes.

No splitting, rank, field, or nonvanishing hypothesis is used. The rank-one separator, the
split return normal form, singular return compression, and split edge compression are the
instances `Small = Unit` with one cut, `α = Unit` with one cut, and `α = Empty`.
-/

namespace MatrixMortality

open scoped Matrix

namespace InterfaceCompression

variable {R α J Large Small : Type*} [CommSemiring R]
  [Fintype Large] [DecidableEq Large] [Fintype Small] [DecidableEq Small]

/-- Transitions act directly; each cut is its interface input followed by its output. -/
def generator (transitions : α → Square Large R) (input : J → Matrix Large Small R)
    (output : J → Matrix Small Large R) : α ⊕ J → Square Large R
  | .inl label => transitions label
  | .inr cut => input cut * output cut

/-- The interface bridge from `source` to `target` across one transition word. -/
def bridge (transitions : α → Square Large R) (input : J → Matrix Large Small R)
    (output : J → Matrix Small Large R) (source : J) (word : List α) (target : J) :
    Square Small R :=
  output source * wordProduct transitions word * input target

/-- One step of a bridge path: the transition word crossed and the cut reached. -/
abbrev Step (α J : Type*) := List α × J

/-- Product of the bridges along a path starting at `source`. -/
def pathProduct (transitions : α → Square Large R) (input : J → Matrix Large Small R)
    (output : J → Matrix Small Large R) : J → List (Step α J) → Square Small R
  | _, [] => 1
  | source, (word, target) :: steps =>
      bridge transitions input output source word target *
        pathProduct transitions input output target steps

/-- Final cut of a path. -/
def terminal : J → List (Step α J) → J
  | source, [] => source
  | _, (_, target) :: steps => terminal target steps

/-- Physical spelling of the steps after the initial cut. -/
def physicalTail : List (Step α J) → List (α ⊕ J)
  | [] => []
  | (word, target) :: steps => word.map Sum.inl ++ Sum.inr target :: physicalTail steps

/-- Physical word beginning with cut `start` and crossing the listed steps. -/
def physicalWord (start : J) (steps : List (Step α J)) : List (α ⊕ J) :=
  Sum.inr start :: physicalTail steps

/-- Leading transition word of a physical word, followed by its cut-headed blocks. -/
def blocks : List (α ⊕ J) → List α × List (J × List α)
  | [] => ([], [])
  | .inl label :: word => (label :: (blocks word).1, (blocks word).2)
  | .inr cut :: word => ([], (cut, (blocks word).1) :: (blocks word).2)

/-- Product of cut-headed blocks. -/
def blockProduct (transitions : α → Square Large R) (input : J → Matrix Large Small R)
    (output : J → Matrix Small Large R) : List (J × List α) → Square Large R
  | [] => 1
  | (cut, word) :: rest =>
      input cut * output cut * wordProduct transitions word *
        blockProduct transitions input output rest

/-- Bridge path traversing the blocks after `cut`, closed by a loop carrying the final word. -/
def loopSteps : J → List α → List (J × List α) → List (Step α J)
  | cut, word, [] => [(word, cut)]
  | _, word, (next, nextWord) :: rest => (word, next) :: loopSteps next nextWord rest

/-- Cut heading the last block, or `cut` when there is none. -/
def lastCut : J → List (J × List α) → J
  | cut, [] => cut
  | _, (next, _) :: rest => lastCut next rest

omit [DecidableEq Small] in
theorem wordProduct_map_inl (transitions : α → Square Large R)
    (input : J → Matrix Large Small R) (output : J → Matrix Small Large R) (word : List α) :
    wordProduct (generator transitions input output) (word.map Sum.inl) =
      wordProduct transitions word := by
  have relabel : generator transitions input output ∘ Sum.inl = transitions := by
    funext label
    rfl
  rw [← wordProduct_comp, relabel]

/-- A physical word spelt from a path is its path product inside the boundary cuts. -/
theorem wordProduct_physicalWord (transitions : α → Square Large R)
    (input : J → Matrix Large Small R) (output : J → Matrix Small Large R)
    (start : J) (steps : List (Step α J)) :
    wordProduct (generator transitions input output) (physicalWord start steps) =
      input start * pathProduct transitions input output start steps *
        output (terminal start steps) := by
  induction steps generalizing start with
  | nil =>
      simp [physicalWord, physicalTail, pathProduct, terminal, wordProduct, generator]
  | cons step steps induction =>
      obtain ⟨word, target⟩ := step
      have tail_eq :
          wordProduct (generator transitions input output)
              (physicalTail ((word, target) :: steps)) =
            wordProduct transitions word *
              (input target * pathProduct transitions input output target steps *
                output (terminal target steps)) := by
        rw [physicalTail, wordProduct_append, wordProduct_map_inl]
        exact congrArg _ (induction target)
      rw [physicalWord, wordProduct_cons, tail_eq]
      simp only [generator, pathProduct, terminal, bridge, Matrix.mul_assoc]

omit [DecidableEq Small] in
/-- Every physical word is its leading transition word times its cut-headed blocks. -/
theorem wordProduct_eq_blocks (transitions : α → Square Large R)
    (input : J → Matrix Large Small R) (output : J → Matrix Small Large R)
    (word : List (α ⊕ J)) :
    wordProduct (generator transitions input output) word =
      wordProduct transitions (blocks word).1 *
        blockProduct transitions input output (blocks word).2 := by
  induction word with
  | nil => simp [blocks, blockProduct, wordProduct]
  | cons head word induction =>
      cases head with
      | inl label =>
          rw [wordProduct_cons, induction]
          simp only [generator, blocks, wordProduct_cons, Matrix.mul_assoc]
      | inr cut =>
          rw [wordProduct_cons, induction]
          simp only [generator, blocks, blockProduct, wordProduct_nil, Matrix.one_mul,
            Matrix.mul_assoc]

/-- A physical word without cuts is the spelling of its leading transition word. -/
theorem eq_map_inl_of_blocks_snd_nil (word : List (α ⊕ J)) (no_cut : (blocks word).2 = []) :
    word = (blocks word).1.map Sum.inl := by
  induction word with
  | nil => rfl
  | cons head word induction =>
      cases head with
      | inl label =>
          have tail_no_cut : (blocks word).2 = [] := no_cut
          have tail_eq := induction tail_no_cut
          simp only [blocks, List.map_cons]
          exact congrArg (Sum.inl label :: ·) tail_eq
      | inr cut =>
          exact absurd no_cut (by simp [blocks])

theorem loopSteps_ne_nil (cut : J) (word : List α) (rest : List (J × List α)) :
    loopSteps cut word rest ≠ [] := by
  cases rest with
  | nil => simp [loopSteps]
  | cons step rest =>
      obtain ⟨next, nextWord⟩ := step
      simp [loopSteps]

/-- Sandwiching the transitions after a cut between that cut's output and the last cut's input
gives the loop-closed path product. -/
theorem sandwich (transitions : α → Square Large R)
    (input : J → Matrix Large Small R) (output : J → Matrix Small Large R)
    (cut : J) (word : List α) (rest : List (J × List α)) :
    output cut * (wordProduct transitions word * blockProduct transitions input output rest) *
        input (lastCut cut rest) =
      pathProduct transitions input output cut (loopSteps cut word rest) := by
  induction rest generalizing cut word with
  | nil =>
      simp only [blockProduct, lastCut, loopSteps, pathProduct, bridge, Matrix.mul_one]
  | cons step rest induction =>
      obtain ⟨next, nextWord⟩ := step
      simp only [lastCut, loopSteps, pathProduct, bridge]
      rw [← induction next nextWord]
      simp only [blockProduct, Matrix.mul_assoc]

/-- Interface compression: a family of arbitrary transitions and factored cuts is mortal exactly
when the transitions alone are mortal or one nonempty path of interface bridges vanishes. -/
theorem isMortal_iff (transitions : α → Square Large R)
    (input : J → Matrix Large Small R) (output : J → Matrix Small Large R) :
    IsMortal (generator transitions input output) ↔
      IsMortal transitions ∨
        ∃ start steps, steps ≠ [] ∧ pathProduct transitions input output start steps = 0 := by
  constructor
  · rintro ⟨word, word_nonempty, product_zero⟩
    have blocks_zero :
        wordProduct transitions (blocks word).1 *
          blockProduct transitions input output (blocks word).2 = 0 := by
      rw [← wordProduct_eq_blocks]
      exact product_zero
    rcases rest_cases : (blocks word).2 with _ | ⟨⟨cut, cutWord⟩, rest⟩
    · left
      have word_eq := eq_map_inl_of_blocks_snd_nil word rest_cases
      refine ⟨(blocks word).1, ?_, ?_⟩
      · intro lead_nil
        apply word_nonempty
        rw [word_eq, lead_nil]
        rfl
      · have rest_product : blockProduct transitions input output (blocks word).2 = 1 := by
          rw [rest_cases]
          rfl
        rw [← Matrix.mul_one (wordProduct transitions (blocks word).1), ← rest_product]
        exact blocks_zero
    · right
      refine ⟨cut, loopSteps cut (blocks word).1 ((cut, cutWord) :: rest),
        loopSteps_ne_nil cut (blocks word).1 ((cut, cutWord) :: rest), ?_⟩
      rw [← sandwich, ← rest_cases, blocks_zero]
      simp
  · rintro (⟨word, word_nonempty, product_zero⟩ | ⟨start, steps, _, path_zero⟩)
    · refine ⟨word.map Sum.inl, by simpa using word_nonempty, ?_⟩
      rw [wordProduct_map_inl]
      exact product_zero
    · refine ⟨physicalWord start steps, List.cons_ne_nil _ _, ?_⟩
      rw [wordProduct_physicalWord, path_zero]
      simp

section RankOne

variable {K : Type*} [Field K]

/-- Transitions together with rank-one cuts given by column and row vectors. -/
def rankOneGenerator (transitions : α → Square Large K) (column row : J → Large → K) :
    α ⊕ J → Square Large K
  | .inl label => transitions label
  | .inr cut => Matrix.vecMulVec (column cut) (row cut)

omit [Fintype Large] [DecidableEq Large] in
theorem rankOneGenerator_eq (transitions : α → Square Large K) (column row : J → Large → K) :
    rankOneGenerator transitions column row =
      generator transitions (fun cut => Matrix.replicateCol Unit (column cut))
        (fun cut => Matrix.replicateRow Unit (row cut)) := by
  funext label
  cases label with
  | inl label => rfl
  | inr cut => exact Matrix.vecMulVec_eq Unit (column cut) (row cut)

/-- A rank-one bridge is the scalar seen by its row and column around the transition word. -/
theorem bridge_rankOne_apply (transitions : α → Square Large K) (column row : J → Large → K)
    (source : J) (word : List α) (target : J) :
    bridge transitions (fun cut => Matrix.replicateCol Unit (column cut))
        (fun cut => Matrix.replicateRow Unit (row cut)) source word target () () =
      row source ⬝ᵥ wordProduct transitions word *ᵥ column target := by
  rw [bridge, ← Matrix.replicateRow_vecMul, Matrix.replicateRow_mul_replicateCol_apply,
    Matrix.dotProduct_mulVec]

theorem exists_bridge_eq_zero_of_pathProduct_eq_zero (transitions : α → Square Large K)
    (input : J → Matrix Large Unit K) (output : J → Matrix Unit Large K) :
    ∀ (source : J) (steps : List (Step α J)),
      pathProduct transitions input output source steps = 0 →
        ∃ left word right, bridge transitions input output left word right = 0
  | _, [], zero => absurd zero one_ne_zero
  | source, (word, target) :: steps, zero => by
      have factor_zero :
          bridge transitions input output source word target = 0 ∨
            pathProduct transitions input output target steps = 0 := by
        have entry_zero :
            bridge transitions input output source word target () () *
              pathProduct transitions input output target steps () () = 0 := by
          have product_entry := congrFun (congrFun zero ()) ()
          simpa [pathProduct, Matrix.mul_apply] using product_entry
        rw [unitSquare_eq_zero_iff, unitSquare_eq_zero_iff]
        exact mul_eq_zero.mp entry_zero
      rcases factor_zero with bridge_zero | tail_zero
      · exact ⟨source, word, target, bridge_zero⟩
      · exact exists_bridge_eq_zero_of_pathProduct_eq_zero transitions input output
          target steps tail_zero

/-- With rank-one cuts, interface compression is scalar: the family is mortal exactly when the
transitions alone are mortal or one row sees zero through some transition word at some column.
One cut is the unconditional rank-one separator; several cuts give several endpoint pairs. -/
theorem isMortal_rankOne_iff (transitions : α → Square Large K) (column row : J → Large → K) :
    IsMortal (rankOneGenerator transitions column row) ↔
      IsMortal transitions ∨
        ∃ source word target, row source ⬝ᵥ wordProduct transitions word *ᵥ column target = 0 := by
  rw [rankOneGenerator_eq, isMortal_iff]
  apply or_congr_right
  constructor
  · rintro ⟨start, steps, _, path_zero⟩
    obtain ⟨source, word, target, bridge_zero⟩ :=
      exists_bridge_eq_zero_of_pathProduct_eq_zero transitions _ _ start steps path_zero
    refine ⟨source, word, target, ?_⟩
    rw [← bridge_rankOne_apply, bridge_zero]
    rfl
  · rintro ⟨source, word, target, scalar_zero⟩
    refine ⟨source, [(word, target)], List.cons_ne_nil _ _, ?_⟩
    rw [pathProduct, pathProduct, Matrix.mul_one, unitSquare_eq_zero_iff,
      bridge_rankOne_apply]
    exact scalar_zero

end RankOne

end InterfaceCompression

end MatrixMortality
