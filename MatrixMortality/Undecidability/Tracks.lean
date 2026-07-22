import Mathlib.Data.List.OfFn

/-!
# Finite tracks

Neary's compiler defines one long tag word by prescribing every fixed-stride track through it.
The representation below makes that prescription literal: a `period × columns` grid is serialized
column by column, so phase `r` is recovered at indices `r + period * j`.
-/

namespace MatrixMortality.Undecidability

/-- Serialize a phase-by-column grid in column-major order. -/
def weave {α : Type*} (period columns : Nat) (period_pos : 0 < period)
    (grid : Fin period → Fin columns → α) : List α :=
  List.ofFn fun index : Fin (period * columns) =>
    grid
      ⟨index % period, Nat.mod_lt _ period_pos⟩
      ⟨index / period, by
        rw [Nat.div_lt_iff_lt_mul period_pos]
        exact lt_of_lt_of_le index.isLt (Nat.le_of_eq (Nat.mul_comm period columns))⟩

@[simp]
theorem weave_length {α : Type*} (period columns : Nat) (period_pos : 0 < period)
    (grid : Fin period → Fin columns → α) :
    (weave period columns period_pos grid).length = period * columns := by
  simp [weave]

/-- The linear position occupied by one phase in one column. -/
def trackIndex {period columns : Nat} (phase : Fin period) (column : Fin columns) :
    Fin (period * columns) :=
  ⟨phase + period * column, by
    calc
      phase.val + period * column.val < period + period * column.val :=
        Nat.add_lt_add_right phase.isLt _
      _ = period * (column.val + 1) := by simp [Nat.mul_succ, Nat.add_comm]
      _ ≤ period * columns :=
        Nat.mul_le_mul_left period (Nat.succ_le_of_lt column.isLt)⟩

/-- Reading a woven word at fixed phase and period recovers the prescribed track. -/
theorem weave_get_track {α : Type*} {period columns : Nat} (period_pos : 0 < period)
    (grid : Fin period → Fin columns → α) (phase : Fin period) (column : Fin columns) :
    (weave period columns period_pos grid).get
        (Fin.cast (weave_length period columns period_pos grid).symm
          (trackIndex phase column)) =
      grid phase column := by
  simp [weave, trackIndex, Fin.cast, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left, Nat.mod_eq_of_lt phase.isLt, Nat.div_eq_of_lt phase.isLt,
    period_pos]

/-- Materialize one prescribed track as a list. -/
def gridTrack {α : Type*} {period columns : Nat}
    (grid : Fin period → Fin columns → α) (phase : Fin period) : List α :=
  List.ofFn (grid phase)

@[simp]
theorem gridTrack_length {α : Type*} {period columns : Nat}
    (grid : Fin period → Fin columns → α) (phase : Fin period) :
    (gridTrack grid phase).length = columns := by
  simp [gridTrack]

end MatrixMortality.Undecidability
