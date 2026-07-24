import MatrixMortality.MatrixSemigroup

/-!
# Deterministic matrix transducers

A deterministic transition emits a square matrix. The construction below realizes the transducer
as one block matrix per input letter and proves the unique nonzero-block normal form for every
input word.
-/

namespace MatrixMortality

open scoped Matrix

/-- A deterministic finite-state transducer whose transitions emit square matrices. -/
structure WeightedTransducer (State Letter Index R : Type*) where
  /-- Deterministic control transition. -/
  next : State → Letter → State
  /-- Matrix emitted by the transition. -/
  output : State → Letter → Square Index R

namespace WeightedTransducer

variable {State Letter Index R : Type*} [Fintype State] [DecidableEq State]
  [Fintype Index] [DecidableEq Index] [CommSemiring R]

/-- Final state and emitted product of one transducer run. -/
def run (machine : WeightedTransducer State Letter Index R) :
    State → List Letter → State × Square Index R
  | state, [] => (state, 1)
  | state, letter :: word =>
      let tail := machine.run (machine.next state letter) word
      (tail.1, machine.output state letter * tail.2)

omit [Fintype State] [DecidableEq State] in
@[simp] theorem run_nil (machine : WeightedTransducer State Letter Index R) (state : State) :
    machine.run state [] = (state, 1) := rfl

omit [Fintype State] [DecidableEq State] in
@[simp] theorem run_cons (machine : WeightedTransducer State Letter Index R) (state : State)
    (letter : Letter) (word : List Letter) :
    machine.run state (letter :: word) =
      let tail := machine.run (machine.next state letter) word
      (tail.1, machine.output state letter * tail.2) := rfl

/-- Block generator carrying each state row to its unique successor state. -/
def generator (machine : WeightedTransducer State Letter Index R) (letter : Letter) :
    Square (State × Index) R :=
  fun row column =>
    if machine.next row.1 letter = column.1
    then machine.output row.1 letter row.2 column.2
    else 0

theorem wordProduct_apply (machine : WeightedTransducer State Letter Index R)
    (word : List Letter) (start finish : State) (row column : Index) :
    wordProduct machine.generator word (start, row) (finish, column) =
      if (machine.run start word).1 = finish
      then (machine.run start word).2 row column
      else 0 := by
  induction word generalizing start row with
  | nil =>
      by_cases state_eq : start = finish
      · subst finish
        simp [wordProduct, Matrix.one_apply]
      · simp [wordProduct, Matrix.one_apply, state_eq]
  | cons letter word induction =>
      rw [wordProduct_cons, Matrix.mul_apply]
      rw [Fintype.sum_prod_type]
      by_cases final_eq : (machine.run (machine.next start letter) word).1 = finish
      · simp only [generator, if_pos final_eq, run_cons]
        rw [Finset.sum_eq_single (machine.next start letter)]
        · simp only [if_pos, Matrix.mul_apply]
          apply Finset.sum_congr rfl
          intro index _
          rw [induction]
          simp [final_eq]
        · intro state _ state_ne
          simp [Ne.symm state_ne]
        · intro state_absent
          exact (state_absent (Finset.mem_univ _)).elim
      · simp only [generator, if_neg final_eq, run_cons]
        rw [Finset.sum_eq_single (machine.next start letter)]
        · apply Finset.sum_eq_zero
          intro index _
          rw [induction]
          simp [final_eq]
        · intro state _ state_ne
          simp [Ne.symm state_ne]
        · intro state_absent
          exact (state_absent (Finset.mem_univ _)).elim

end WeightedTransducer
end MatrixMortality
