import MatrixMortality.Computability
import Mathlib.Data.List.OfFn

/-!
# Finite tracks

Neary's compiler defines one long tag word by prescribing every fixed-stride track through it.
The representation below makes that prescription literal: a `period × columns` grid is serialized
column by column, so phase `r` is recovered at indices `r + period * j`.
-/

namespace MatrixMortality.Undecidability

/-- Pad a prefix on the right to an exact target length. -/
def padRight {α : Type*} (width : Nat) (filler : α) (stem : List α) : List α :=
  stem ++ List.replicate (width - stem.length) filler

theorem padRight_length {α : Type*} {width : Nat} (filler : α) (stem : List α)
    (stem_fits : stem.length ≤ width) :
    (padRight width filler stem).length = width := by
  simp [padRight]
  omega

/-- Place padding between a fixed prefix and suffix. -/
def padBetween {α : Type*} (width : Nat) (filler : α) (stem ending : List α) : List α :=
  stem ++ List.replicate (width - stem.length - ending.length) filler ++ ending

theorem padBetween_length {α : Type*} {width : Nat} (filler : α)
    (stem ending : List α) (fixed_fits : stem.length + ending.length ≤ width) :
    (padBetween width filler stem ending).length = width := by
  simp [padBetween]
  omega

end MatrixMortality.Undecidability

namespace MatrixMortality.Primrec

theorem padRight {Input α : Type*} [Primcodable Input] [Primcodable α]
    {width : Input → Nat} {filler : Input → α} {stem : Input → List α}
    (width_rec : Primrec width) (filler_rec : Primrec filler) (stem_rec : Primrec stem) :
    Primrec fun input =>
      Undecidability.padRight (width input) (filler input) (stem input) := by
  have padding_length :
      Primrec fun input => width input - (stem input).length :=
    Primrec.nat_sub.comp width_rec (Primrec.list_length.comp stem_rec)
  exact
    Primrec.list_append.comp stem_rec <|
      list_replicate.comp padding_length filler_rec

theorem padBetween {Input α : Type*} [Primcodable Input] [Primcodable α]
    {width : Input → Nat} {filler : Input → α} {stem ending : Input → List α}
    (width_rec : Primrec width) (filler_rec : Primrec filler) (stem_rec : Primrec stem)
    (ending_rec : Primrec ending) :
    Primrec fun input =>
      Undecidability.padBetween (width input) (filler input) (stem input) (ending input) := by
  have padding_length :
      Primrec fun input => width input - (stem input).length - (ending input).length :=
    Primrec.nat_sub.comp
      (Primrec.nat_sub.comp width_rec (Primrec.list_length.comp stem_rec))
      (Primrec.list_length.comp ending_rec)
  have padding :
      Primrec fun input =>
        List.replicate (width input - (stem input).length - (ending input).length)
          (filler input) :=
    list_replicate.comp padding_length filler_rec
  exact Primrec.list_append.comp (Primrec.list_append.comp stem_rec padding) ending_rec

end MatrixMortality.Primrec

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

/-- Column-major serialization of a finite family of materialized tracks. -/
def weaveTracks {α : Type*} [Inhabited α] (period columns : Nat)
    (tracks : Fin period → List α) : List α :=
  (List.range (period * columns)).map fun index =>
    (List.ofFn fun phase : Fin period => (tracks phase).getI (index / period)).getI
      (index % period)

theorem weaveTracks_eq_weave {α : Type*} [Inhabited α] {period columns : Nat}
    (period_pos : 0 < period) (tracks : Fin period → Mathlib.Vector α columns) :
    weaveTracks period columns (fun phase => (tracks phase).val) =
      weave period columns period_pos fun phase column => (tracks phase).get column := by
  apply List.ext_getElem
  · simp [weaveTracks, weave]
  · intro index tracks_bound weave_bound
    have index_bound : index < period * columns := by
      simpa [weaveTracks] using tracks_bound
    have phase_bound : index % period < period := Nat.mod_lt _ period_pos
    have column_bound : index / period < columns := by
      rw [Nat.div_lt_iff_lt_mul period_pos]
      simpa [Nat.mul_comm] using index_bound
    simp only [weaveTracks, weave, List.getElem_map, List.getElem_range]
    have phase_list_bound :
        index % period <
          (List.ofFn fun phase : Fin period =>
            (tracks phase).val.getI (index / period)).length := by
      simpa using phase_bound
    rw [List.getI_eq_getElem _ phase_list_bound, List.getElem_ofFn]
    have track_bound :
        index / period <
          (tracks ⟨index % period, phase_bound⟩).val.length := by
      simpa using column_bound
    rw [List.getI_eq_getElem _ track_bound, List.getElem_ofFn]
    rfl

end MatrixMortality.Undecidability

namespace MatrixMortality.Primrec

theorem weaveTracks {Input α : Type*} [Primcodable Input] [Primcodable α]
    [Inhabited α] {period : Nat} {columns : Input → Nat}
    {tracks : Input → Fin period → List α}
    (columns_rec : Primrec columns) (tracks_rec : Primrec₂ tracks) :
    Primrec fun input =>
      Undecidability.weaveTracks period (columns input) (tracks input) := by
  have total_rec : Primrec fun input => period * columns input :=
    Primrec.nat_mul.comp (Primrec.const period) columns_rec
  have range_rec : Primrec fun input => List.range (period * columns input) :=
    Primrec.list_range.comp total_rec
  have track_rec (phase : Fin period) : Primrec fun input => tracks input phase :=
    tracks_rec.comp Primrec.id (Primrec.const phase)
  have column_rec : Primrec fun pair : Input × Nat => pair.2 / period :=
    Primrec.nat_div.comp Primrec.snd (Primrec.const period)
  have phase_value_rec (phase : Fin period) :
      Primrec fun pair : Input × Nat => (tracks pair.1 phase).getI (pair.2 / period) :=
    Primrec.list_getI.comp ((track_rec phase).comp Primrec.fst) column_rec
  have column_values_rec :
      Primrec fun pair : Input × Nat =>
        List.ofFn fun phase : Fin period => (tracks pair.1 phase).getI (pair.2 / period) :=
    Primrec.list_ofFn phase_value_rec
  have phase_rec : Primrec fun pair : Input × Nat => pair.2 % period :=
    Primrec.nat_mod.comp Primrec.snd (Primrec.const period)
  have grid_value_rec :
      Primrec₂ fun input index =>
        (List.ofFn fun phase : Fin period => (tracks input phase).getI (index / period)).getI
          (index % period) :=
    (Primrec.list_getI.comp column_values_rec phase_rec).to₂
  exact Primrec.list_map range_rec grid_value_rec

end MatrixMortality.Primrec
