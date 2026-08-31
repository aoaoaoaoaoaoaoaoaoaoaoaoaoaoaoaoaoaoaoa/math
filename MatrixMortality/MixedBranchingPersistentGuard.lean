import MatrixMortality.MixedBranchingRecognizer

/-!
# Persistent-guard escape from the common-kernel architecture

The exact `bcbcbb` recognizer remains exact after giving its data-`b` control an arbitrary even
persistent guard multiplier. Every `b`-headed guard is then odd, while data `c` retains the
original accepting-carry test. For nonzero memory the data-`b` matrix has full rational rank, so
the all-word recognizer no longer has two singular data maps or a common data kernel.
-/

namespace MatrixMortality
namespace MixedBranchingPersistentGuard

open scoped Matrix
open MixedBranchingRecognizer

/-- Data controls obtained by retaining the exact data-`c` reset and adding persistent memory to
the guard coordinate of data `b`. -/
def data (memory : ℤ) : TagLetter → Matrix (Fin 3) (Fin 3) ℤ
  | .b =>
      !![memory, 2, 1;
         0, 5, 3703455;
         0, 0, 1]
  | .c => recognizerData .c

/-- The persistent data controls together with the original affine involution. -/
def generator (memory : ℤ) : PairedControl → Matrix (Fin 3) (Fin 3) ℤ
  | .data letter => data memory letter
  | .toggle => recognizerGenerator .toggle

/-- Guard recurrence of the persistent-memory representation. Data `c` retains the original
refresh law; data `b` keeps `memory` times the incoming guard. -/
def guard (memory : ℤ) : List PairedControl → ℤ
  | [] => 1
  | .data .b :: word => memory * guard memory word + 2 * recognizerCarry word + 1
  | .data .c :: word => recognizerGuard (.data .c :: word)
  | .toggle :: word => guard memory word

/-- The original boundary row selecting the guard coordinate. -/
def row : Fin 3 → ℤ := recognizerRow

/-- The original homogeneous pre-boundary state. -/
def delta : Fin 3 → ℤ := recognizerDelta

/-- The original toggled boundary column. -/
def column : Fin 3 → ℤ := recognizerColumn

@[simp] theorem recognizerCarry_data_b (word : List PairedControl) :
    recognizerCarry (.data .b :: word) = 5 * recognizerCarry word + 3703455 := by
  rfl

/-- Exact state recurrence for every raw control word. -/
theorem wordProduct_mulVec_delta (memory : ℤ) (word : List PairedControl) :
    wordProduct (generator memory) word *ᵥ delta =
      ![guard memory word, recognizerCarry word, 1] := by
  induction word with
  | nil =>
      ext coordinate
      fin_cases coordinate <;>
        simp [wordProduct, delta, recognizerDelta, AffineRecognizer.delta, guard,
          recognizerCarry]
  | cons control word induction =>
      rw [wordProduct_cons, ← Matrix.mulVec_mulVec, induction]
      cases control with
      | toggle =>
          ext coordinate
          fin_cases coordinate
          · simp [generator, guard, recognizerGenerator, recognizerCarry,
              AffineRecognizer.Parameters.generator, AffineRecognizer.Parameters.carry,
              Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
          · simp [generator, guard, recognizerGenerator, recognizerCarry,
              AffineRecognizer.Parameters.generator, AffineRecognizer.Parameters.carry,
              Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
            ring
          · simp [generator, guard, recognizerGenerator, recognizerCarry,
              AffineRecognizer.Parameters.generator, AffineRecognizer.Parameters.carry,
              Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      | data letter =>
          cases letter with
          | b =>
              ext coordinate
              fin_cases coordinate
              · simp [generator, data, guard, Matrix.mulVec, dotProduct,
                  Fin.sum_univ_succ]
                ring
              · simp [generator, data, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
              · simp [generator, data, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
          | c =>
              ext coordinate
              fin_cases coordinate <;>
                simp [generator, data, guard, recognizerData, recognizerGuard,
                  recognizerCarry, AffineRecognizer.Parameters.data,
                  AffineRecognizer.Parameters.guard, AffineRecognizer.Parameters.carry,
                  Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem column_eq_toggle_delta (memory : ℤ) :
    column = generator memory .toggle *ᵥ delta := by
  simpa [column, generator, delta] using recognizerColumn_eq_toggle_delta

/-- Scalar coefficient of the persistent-memory representation. -/
def coefficient (memory : ℤ) (word : List PairedControl) : ℤ :=
  linearCoefficient (generator memory) row column word

/-- The scalar coefficient is the persistent guard after the boundary toggle. -/
theorem coefficient_eq_guard (memory : ℤ) (word : List PairedControl) :
    coefficient memory word = guard memory (word ++ [.toggle]) := by
  have state :
      wordProduct (generator memory) word *ᵥ column =
        ![guard memory (word ++ [.toggle]), recognizerCarry (word ++ [.toggle]), 1] := by
    calc
      wordProduct (generator memory) word *ᵥ column =
          wordProduct (generator memory) word *ᵥ
            (generator memory .toggle *ᵥ delta) := by
              rw [← column_eq_toggle_delta]
      _ = (wordProduct (generator memory) word * generator memory .toggle) *ᵥ
          delta := by rw [Matrix.mulVec_mulVec]
      _ = wordProduct (generator memory) (word ++ [.toggle]) *ᵥ delta := by
        rw [wordProduct_append]
        simp [wordProduct]
      _ = _ := wordProduct_mulVec_delta memory (word ++ [.toggle])
  rw [coefficient, linearCoefficient, state]
  simp [row, recognizerRow, AffineRecognizer.row, dotProduct, Fin.sum_univ_succ]

/-- Even persistent memory preserves exactly the zero set of the original refreshed guard. -/
theorem guard_eq_zero_iff_recognizerGuard
    {memory : ℤ} (memory_even : Even memory) (word : List PairedControl) :
    guard memory word = 0 ↔ recognizerGuard word = 0 := by
  obtain ⟨half, rfl⟩ := memory_even
  induction word with
  | nil => simp [guard, recognizerGuard]
  | cons control word induction =>
      cases control with
      | toggle => simpa [guard, recognizerGuard] using induction
      | data letter =>
          cases letter with
          | b =>
              constructor
              · intro persistent_zero
                have persistent_formula :
                    guard (half + half) (.data .b :: word) =
                      2 * (half * guard (half + half) word + recognizerCarry word) + 1 := by
                  simp [guard]
                  ring
                rw [persistent_formula] at persistent_zero
                omega
              · intro refreshed_zero
                have refreshed_formula :
                    recognizerGuard (.data .b :: word) = 2 * recognizerCarry word + 1 := rfl
                rw [refreshed_formula] at refreshed_zero
                omega
          | c => simp [guard]

/-- Every even-memory member has the complete `bcbcbb` paired zero language on the free raw
control monoid. -/
theorem coefficient_eq_zero_iff_paired
    {memory : ℤ} (memory_even : Even memory) (word : List PairedControl) :
    coefficient memory word = 0 ↔ pairedCoefficient ℚ 3 mixedBody word = 0 := by
  calc
    coefficient memory word = 0 ↔ guard memory (word ++ [.toggle]) = 0 := by
      rw [coefficient_eq_guard]
    _ ↔ recognizerGuard (word ++ [.toggle]) = 0 :=
      guard_eq_zero_iff_recognizerGuard memory_even _
    _ ↔ recognizerCoefficient word = 0 := by rw [recognizerCoefficient_eq_guard]
    _ ↔ pairedCoefficient ℚ 3 mixedBody word = 0 :=
      recognizerCoefficient_eq_zero_iff_paired word

/-- Determinant of the persistent data-`b` control. -/
theorem data_b_det (memory : ℤ) : (data memory .b).det = 5 * memory := by
  rw [Matrix.det_fin_three]
  simp [data]
  ring

/-- Nonzero persistent memory makes data `b` nonsingular over the integers. -/
theorem data_b_det_ne_zero {memory : ℤ} (memory_ne : memory ≠ 0) :
    (data memory .b).det ≠ 0 := by
  rw [data_b_det]
  exact mul_ne_zero (by norm_num) memory_ne

/-- After scalar extension, nonzero persistent memory makes data `b` a full-rank rational
matrix. -/
theorem data_b_rank_rat {memory : ℤ} (memory_ne : memory ≠ 0) :
    ((data memory .b).map (Int.castRingHom ℚ)).rank = 3 := by
  apply Matrix.rank_of_isUnit
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  have determinant :
      ((data memory .b).map (Int.castRingHom ℚ)).det = 5 * (memory : ℚ) := by
    rw [Matrix.det_fin_three]
    simp [data]
    ring
  rw [determinant]
  exact mul_ne_zero (by norm_num) (Int.cast_ne_zero.mpr memory_ne)

/-- The unchanged data-`c` control still kills the old guard axis. -/
theorem data_c_kills_guardAxis (memory : ℤ) : data memory .c *ᵥ ![1, 0, 0] = 0 := by
  simpa [data] using recognizerData_kills_guardAxis .c

/-- Nonzero memory makes the data-`b` control visible on the old guard axis. -/
theorem data_b_guardAxis_ne_zero {memory : ℤ} (memory_ne : memory ≠ 0) :
    data memory .b *ᵥ ![1, 0, 0] ≠ 0 := by
  intro image_zero
  have first := congrFun image_zero 0
  simp [data, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at first
  exact memory_ne first

end MixedBranchingPersistentGuard
end MatrixMortality
