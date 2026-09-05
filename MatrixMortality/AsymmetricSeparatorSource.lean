import MatrixMortality.Undecidability.NearyCompiler

/-!
# Compiler prefix for asymmetric separation

The first three Table 2 tracks are constant `b`, `c`, and `b`. Their first entries survive
deletion of the final appendant letter. This is the source restriction used to reject the
asymmetric separator's unwanted phase.
-/

namespace MatrixMortality.Undecidability.NearyCompiler

/-- Every emitted body has the three-letter prefix needed by asymmetric separation. -/
theorem body_take_three {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) :
    (body system input haltPhase period_pos).take 3 = [.b, .c, .b] := by
  have width_large : 3 < deletionWidth period := by
    simp only [deletionWidth]
    omega
  have columns_pos := trackWidth_pos system input
  have whole_large : 3 < (wholeAppendant system input haltPhase period_pos).length := by
    rw [wholeAppendant_length]
    exact lt_of_lt_of_le width_large (Nat.le_mul_of_pos_right _ columns_pos)
  have body_large : 3 ≤ (body system input haltPhase period_pos).length := by
    simp only [body, List.length_dropLast]
    omega
  refine List.ext_getElem ?_ ?_
  · simp [List.length_take, Nat.min_eq_left body_large]
  · intro index left_bound right_bound
    have index_lt : index < 3 := by simpa using right_bound
    have not_last : index ≠ deletionWidth period - 1 := by omega
    have index_lt_width : index < deletionWidth period := by omega
    have at_index := weave_get_track (deletionWidth_pos period_pos)
      (fun phase column => (tableTrack system input haltPhase period_pos phase).get column)
      ⟨index, index_lt_width⟩ ⟨0, columns_pos⟩
    have entry : (wholeAppendant system input haltPhase period_pos)[index]'(by omega) =
        (tableTrack system input haltPhase period_pos ⟨index, index_lt_width⟩).get
          ⟨0, columns_pos⟩ := by
      simpa [wholeAppendant, trackIndex, List.get_eq_getElem] using at_index
    simp only [List.getElem_take, body, List.getElem_dropLast]
    rw [entry]
    have track_length :
        (tableTrackVal system input haltPhase period_pos ⟨index, index_lt_width⟩).length =
          trackWidth system input :=
      (tableTrack system input haltPhase period_pos ⟨index, index_lt_width⟩).property
    change (tableTrackVal system input haltPhase period_pos ⟨index, index_lt_width⟩)[0]'(by
      rw [track_length]
      exact columns_pos) =
      [TagLetter.b, TagLetter.c, TagLetter.b][index]
    simp only [tableTrackVal, if_neg not_last]
    interval_cases index <;> simp

end MatrixMortality.Undecidability.NearyCompiler
