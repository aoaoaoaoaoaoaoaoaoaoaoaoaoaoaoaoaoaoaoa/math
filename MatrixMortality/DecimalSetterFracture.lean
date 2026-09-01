import MatrixMortality.DecimalSetterMatrix
import MatrixMortality.TerminalTile
import Mathlib.Tactic

/-!
# Arbitrary-word fracture for the decimal setter

Runs of at least three delimiters stabilize at the rank-one delimiter cube.  Greedily consuming
three delimiters therefore fractures every arbitrary physical word into exact scalar bridges.
This module proves the list normal form independently of projective avoidance inside one bridge.
-/

namespace MatrixMortality.DecimalSetterFracture

open scoped Matrix

open MatrixMortality.DecimalSetterMatrix

/-- Greedily split a physical word at disjoint delimiter triples. -/
def fractureTriple {α : Type*} : List (Option α) → List (List (Option α))
  | [] => [[]]
  | none :: none :: none :: word => [] :: fractureTriple word
  | head :: word => (fractureTriple word).modifyHead (head :: ·)

/-- A physical word begins with a delimiter triple. -/
def StartsWithTriple {α : Type*} (word : List (Option α)) : Prop :=
  ∃ tail, word = none :: none :: none :: tail

private theorem fractureTriple_cons_of_not_startsWithTriple {α : Type*}
    (head : Option α) (word : List (Option α))
    (not_triple : ¬StartsWithTriple (head :: word)) :
    fractureTriple (head :: word) =
      (fractureTriple word).modifyHead (head :: ·) := by
  cases head with
  | some label => rfl
  | none =>
      cases word with
      | nil => rfl
      | cons second rest =>
          cases second with
          | some label => rfl
          | none =>
              cases rest with
              | nil => rfl
              | cons third tail =>
                  cases third with
                  | some label => rfl
                  | none => exact (not_triple ⟨tail, rfl⟩).elim

theorem fractureTriple_ne_nil {α : Type*} :
    ∀ word : List (Option α), fractureTriple word ≠ []
  | [] => by simp [fractureTriple]
  | head :: word => by
      by_cases starts : StartsWithTriple (head :: word)
      · obtain ⟨tail, word_eq⟩ := starts
        rw [word_eq]
        simp [fractureTriple]
      · rw [fractureTriple_cons_of_not_startsWithTriple head word starts]
        have tail_nonempty := fractureTriple_ne_nil word
        obtain ⟨block, blocks, fracture_eq⟩ :=
          List.exists_cons_of_ne_nil tail_nonempty
        simp [fracture_eq]

private theorem intercalatedProduct_one_cons {M : Type*} [Monoid M]
    (separator : M) {blocks : List M} (blocks_nonempty : blocks ≠ []) :
    intercalatedProduct separator (1 :: blocks) =
      separator * intercalatedProduct separator blocks := by
  obtain ⟨block, blocks, rfl⟩ := List.exists_cons_of_ne_nil blocks_nonempty
  cases blocks <;> simp [intercalatedProduct]

private theorem intercalatedProduct_modifyHead {M : Type*} [Monoid M]
    (separator left : M) {blocks : List M} (blocks_nonempty : blocks ≠ []) :
    intercalatedProduct separator (blocks.modifyHead (left * ·)) =
      left * intercalatedProduct separator blocks := by
  obtain ⟨block, blocks, rfl⟩ := List.exists_cons_of_ne_nil blocks_nonempty
  cases blocks <;> simp [intercalatedProduct, mul_assoc]

/-- Exact word-product reconstruction from the delimiter-triple fracture. -/
theorem wordProduct_eq_fractureTriple {α M : Type*} [Monoid M]
    (delimiter : M) (data : α → M) :
    ∀ word : List (Option α),
      wordProduct (separatedGenerator delimiter data) word =
        intercalatedProduct (delimiter ^ 3)
          ((fractureTriple word).map (wordProduct (separatedGenerator delimiter data)))
  | [] => by simp [fractureTriple, intercalatedProduct]
  | head :: word => by
      by_cases starts : StartsWithTriple (head :: word)
      · obtain ⟨tail, word_eq⟩ := starts
        have head_eq : head = none := (List.cons.inj word_eq).1
        have word_eq' : word = none :: none :: tail := (List.cons.inj word_eq).2
        subst head
        subst word
        have induction := wordProduct_eq_fractureTriple delimiter data tail
        have tail_nonempty :
            (fractureTriple tail).map
                (wordProduct (separatedGenerator delimiter data)) ≠ [] := by
          simpa using fractureTriple_ne_nil tail
        rw [show wordProduct (separatedGenerator delimiter data)
                (none :: none :: none :: tail) =
              delimiter ^ 3 * wordProduct (separatedGenerator delimiter data) tail by
            simp [separatedGenerator, pow_succ, mul_assoc],
          show fractureTriple (none :: none :: none :: tail) =
            [] :: fractureTriple tail by rfl,
          List.map_cons, wordProduct_nil,
          intercalatedProduct_one_cons _ tail_nonempty, induction]
      · rw [wordProduct_cons, wordProduct_eq_fractureTriple,
          fractureTriple_cons_of_not_startsWithTriple head word starts]
        have fractured_nonempty := fractureTriple_ne_nil word
        obtain ⟨block, blocks, fracture_eq⟩ :=
          List.exists_cons_of_ne_nil fractured_nonempty
        rw [fracture_eq]
        simp only [List.modifyHead, List.map_cons, wordProduct_cons]
        exact (intercalatedProduct_modifyHead (delimiter ^ 3)
          (separatedGenerator delimiter data head)
          (List.cons_ne_nil (wordProduct (separatedGenerator delimiter data) block)
            (blocks.map (wordProduct (separatedGenerator delimiter data))))).symm
termination_by word => word.length
decreasing_by
  · rw [word_eq']
    simp
    omega
  · simp

private theorem generator_eq_separated (β : Nat) (body : List TagLetter) :
    generator β body = separatedGenerator (delimiter β) (data β body) := by
  funext label
  cases label <;> rfl

/-- One scalar bridge between two delimiter cubes. -/
def bridgeScalar (β : Nat) (body : List TagLetter)
    (word : List (Option TagLetter)) : ℚ :=
  terminalRow ⬝ᵥ wordProduct (generator β body) word *ᵥ firstAxis

/-- Fracturing at delimiter triples exposes a product of scalar bridges between two exterior
vectors. -/
theorem fractureTriple_rankOne_formula (β : Nat) (body : List TagLetter)
    (first last : List (Option TagLetter))
    (middle : List (List (Option TagLetter))) :
    intercalatedProduct (delimiter β ^ 3)
        (wordProduct (generator β body) first ::
          middle.map (wordProduct (generator β body)) ++
            [wordProduct (generator β body) last]) =
      (middle.map (bridgeScalar β body)).prod •
        Matrix.vecMulVec
          (wordProduct (generator β body) first *ᵥ firstAxis)
          (terminalRow ᵥ* wordProduct (generator β body) last) := by
  rw [delimiter_cube]
  have scalar_map :
      middle.map (bridgeScalar β body) =
        (middle.map (wordProduct (generator β body))).map
          (MatrixMortality.bridgeScalar firstAxis terminalRow) := by
    induction middle with
    | nil => rfl
    | cons word middle induction =>
        simp only [List.map_cons, induction, List.cons.injEq, and_true]
        rfl
  rw [scalar_map]
  exact rankOneIntercalatedProduct_formula firstAxis terminalRow
    (wordProduct (generator β body) first)
    (wordProduct (generator β body) last)
    (middle.map (wordProduct (generator β body)))

/-- Complete arbitrary-product normal form after at least one delimiter triple. -/
theorem wordProduct_eq_scalarBridges
    (β : Nat) (body : List TagLetter) (word : List (Option TagLetter))
    (triple_present : 2 ≤ (fractureTriple word).length) :
    ∃ (first last : List (Option TagLetter))
        (middle : List (List (Option TagLetter))),
      fractureTriple word = first :: middle ++ [last] ∧
      wordProduct (generator β body) word =
        (middle.map (bridgeScalar β body)).prod •
          Matrix.vecMulVec
            (wordProduct (generator β body) first *ᵥ firstAxis)
            (terminalRow ᵥ* wordProduct (generator β body) last) := by
  have fractured_nonempty := fractureTriple_ne_nil word
  obtain ⟨first, rest, fracture_eq⟩ := List.exists_cons_of_ne_nil fractured_nonempty
  have rest_nonempty : rest ≠ [] := by
    intro rest_nil
    rw [fracture_eq, rest_nil] at triple_present
    simp at triple_present
  let last := rest.getLast rest_nonempty
  let middle := rest.dropLast
  have decomposition : fractureTriple word = first :: middle ++ [last] := by
    rw [fracture_eq]
    congr 1
    exact (List.dropLast_append_getLast rest_nonempty).symm
  refine ⟨first, last, middle, decomposition, ?_⟩
  have reconstruction :=
    wordProduct_eq_fractureTriple (delimiter β) (data β body) word
  have reconstruction' :
      wordProduct (generator β body) word =
        intercalatedProduct (delimiter β ^ 3)
          ((fractureTriple word).map (wordProduct (generator β body))) := by
    rw [generator_eq_separated]
    exact reconstruction
  rw [reconstruction', decomposition]
  simp only [List.map_cons, List.map_append]
  exact fractureTriple_rankOne_formula β body first last middle

end MatrixMortality.DecimalSetterFracture
