import MatrixMortality.PriorityAffineResidual

/-!
# Priority-triangular residual transfers

A destructive transfer drains one natural counter and deposits fixed nonnegative multiples of
its old value only into later counters. This file proves that one nested-prefix exit test forces
the exact number of drain-loop iterations, and that the resulting transfer class strictly
exceeds every finite union of fixed translations.
-/

namespace MatrixMortality

namespace PriorityTriangularResidual

open PriorityAffineResidual

/-- A fanout vector deposits mass strictly after one pivot in the fixed counter priority. -/
def StrictlyLater {dimension : Nat} (pivot : Fin dimension)
    (fanout : Fin dimension → Nat) : Prop :=
  ∀ coordinate, coordinate.val ≤ pivot.val → fanout coordinate = 0

/-- The ordinary VASS shift which removes one pivot token and emits its fixed fanout. -/
def drainShift {dimension : Nat} (pivot : Fin dimension)
    (fanout : Fin dimension → Nat) : Fin dimension → ℤ :=
  fun coordinate =>
    (fanout coordinate : ℤ) - if coordinate = pivot then 1 else 0

/-- Net arithmetic of iterating the ordinary drain loop `steps` times. Natural source and target
states enforce that the pivot cannot be overdrawn. -/
def DrainIteration {dimension : Nat} (pivot : Fin dimension)
    (fanout : Fin dimension → Nat) (steps : Nat)
    (source target : Fin dimension → Nat) : Prop :=
  IntegerStep (fun coordinate => (steps : ℤ) * drainShift pivot fanout coordinate)
    source target

/-- The logical destructive transfer: zero the pivot and add its old value times the fanout to
every other coordinate. -/
def DrainTransfer {dimension : Nat} (pivot : Fin dimension)
    (fanout source target : Fin dimension → Nat) : Prop :=
  ∀ coordinate,
    target coordinate =
      if coordinate = pivot then 0
      else source coordinate + source pivot * fanout coordinate

@[simp] theorem drainShift_pivot {dimension : Nat} (pivot : Fin dimension)
    (fanout : Fin dimension → Nat) (later : StrictlyLater pivot fanout) :
    drainShift pivot fanout pivot = -1 := by
  simp [drainShift, later pivot (by rfl)]

theorem drainIteration_pivot {dimension : Nat} (pivot : Fin dimension)
    (fanout : Fin dimension → Nat) (later : StrictlyLater pivot fanout)
    (steps : Nat) (source target : Fin dimension → Nat)
    (iteration : DrainIteration pivot fanout steps source target) :
    (target pivot : ℤ) = (source pivot : ℤ) - steps := by
  have pivotEquation := iteration pivot
  simp [DrainIteration, IntegerStep, drainShift, later pivot (by rfl)] at pivotEquation
  omega

/-- Natural-state semantics forbids more drain iterations than the pivot initially contains. -/
theorem drainIteration_steps_le {dimension : Nat} (pivot : Fin dimension)
    (fanout : Fin dimension → Nat) (later : StrictlyLater pivot fanout)
    (steps : Nat) (source target : Fin dimension → Nat)
    (iteration : DrainIteration pivot fanout steps source target) :
    steps ≤ source pivot := by
  have pivotEquation := drainIteration_pivot pivot fanout later steps source target iteration
  omega

/-- The nested exit test forces the loop to run exactly once per old pivot token. -/
theorem drainIteration_exit_steps {dimension : Nat} (pivot : Fin dimension)
    (fanout : Fin dimension → Nat) (later : StrictlyLater pivot fanout)
    (steps : Nat) (source target : Fin dimension → Nat)
    (iteration : DrainIteration pivot fanout steps source target)
    (exitZero : NestedZero (pivot.val + 1) target) :
    steps = source pivot := by
  have targetZero : target pivot = 0 := exitZero pivot (by omega)
  have pivotEquation := drainIteration_pivot pivot fanout later steps source target iteration
  rw [targetZero] at pivotEquation
  simp at pivotEquation
  omega

/-- One priority-aligned destructive transfer is exactly an ordinary drain loop followed by the
next nested-prefix zero test. This equivalence excludes premature exits and overdrains. -/
theorem drainTransfer_iff_exitIteration {dimension : Nat} (pivot : Fin dimension)
    (fanout source target : Fin dimension → Nat) (later : StrictlyLater pivot fanout) :
    NestedZero pivot.val source ∧ DrainTransfer pivot fanout source target ↔
      ∃ steps,
        DrainIteration pivot fanout steps source target ∧
          NestedZero (pivot.val + 1) target := by
  constructor
  · rintro ⟨sourceZero, transfer⟩
    refine ⟨source pivot, ?_, ?_⟩
    · intro coordinate
      have transferEquation := transfer coordinate
      by_cases atPivot : coordinate = pivot
      · subst coordinate
        simp [DrainIteration, IntegerStep, drainShift,
          later pivot (by rfl)] at transferEquation ⊢
        omega
      · simp [DrainIteration, IntegerStep, drainShift, atPivot] at transferEquation ⊢
        omega
    · intro coordinate coordinate_lt
      have coordinate_le : coordinate.val ≤ pivot.val := by omega
      by_cases atPivot : coordinate = pivot
      · subst coordinate
        simpa [DrainTransfer] using transfer pivot
      · have earlier : coordinate.val < pivot.val := by
          have distinctValues : coordinate.val ≠ pivot.val := by
            intro equalValues
            exact atPivot (Fin.ext equalValues)
          omega
        have sourceCoordinate := sourceZero coordinate earlier
        have noFanout := later coordinate coordinate_le
        simpa [DrainTransfer, atPivot, sourceCoordinate, noFanout] using transfer coordinate
  · rintro ⟨steps, iteration, exitZero⟩
    have steps_eq := drainIteration_exit_steps pivot fanout later steps source target
      iteration exitZero
    constructor
    · intro coordinate coordinate_lt
      have targetZero := exitZero coordinate (by omega)
      have iterationEquation := iteration coordinate
      have notPivot : coordinate ≠ pivot := by
        intro equality
        subst coordinate
        omega
      have noFanout := later coordinate (by omega)
      simp [DrainIteration, IntegerStep, drainShift, notPivot, noFanout,
        targetZero] at iterationEquation
      omega
    · intro coordinate
      have iterationEquation := iteration coordinate
      by_cases atPivot : coordinate = pivot
      · subst coordinate
        have targetZero := exitZero pivot (by omega)
        simp [DrainTransfer, targetZero]
      · simp [DrainIteration, IntegerStep, drainShift, atPivot, steps_eq] at iterationEquation
        simp [DrainTransfer, atPivot]
        omega

/-- A finite list of fixed translations cannot realize the reset graph `n ↦ 0` on all natural
inputs. Thus priority-triangular transfer strictly exceeds the old affine-translation atlas. -/
theorem reset_not_finite_translation_union (shifts : List ℤ) :
    ¬∀ source : Nat,
      ∃ shift ∈ shifts, (0 : ℤ) = (source : ℤ) + shift := by
  intro covered
  let bound : Nat := (shifts.map Int.natAbs).sum
  obtain ⟨shift, shift_mem, reset⟩ := covered (bound + 1)
  have abs_mem : shift.natAbs ∈ shifts.map Int.natAbs :=
    List.mem_map_of_mem Int.natAbs shift_mem
  have abs_le : shift.natAbs ≤ bound := by
    exact List.single_le_sum (by simp) _ abs_mem
  have shift_eq : shift = -((bound + 1 : Nat) : ℤ) := by omega
  have abs_eq : shift.natAbs = bound + 1 := by
    rw [shift_eq, Int.natAbs_neg]
    exact Int.natAbs_ofNat (bound + 1)
  omega

end PriorityTriangularResidual

end MatrixMortality
