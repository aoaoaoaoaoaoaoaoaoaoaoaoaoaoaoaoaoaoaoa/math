import MatrixMortality.Undecidability.Problems

/-!
# Primitive-recursive dimension padding

Adjoining a zero block preserves every nonempty zero product. The entrywise padding map
is primitive recursive, so a certified reduction transports to each larger dimension.
-/

namespace MatrixMortality.Undecidability.MortalityProblem

/-- Append an identically zero block and reindex to the canonical finite coordinates. -/
def pad {d k : Nat} (extra : Nat) (problem : MortalityProblem d k) :
    MortalityProblem (d + extra) k :=
  fun label => Matrix.reindex finSumFinEquiv finSumFinEquiv
    (zeroPad (κ := Fin extra) (problem label))

theorem pad_primrec (d k extra : Nat) :
    Primrec (pad (d := d) (k := k) extra) := by
  refine MortalityProblem.primrec _ (fun label row column => ?_)
  obtain ⟨sumRow, rfl⟩ := finSumFinEquiv.surjective row
  obtain ⟨sumColumn, rfl⟩ := finSumFinEquiv.surjective column
  cases sumRow with
  | inl sourceRow =>
      cases sumColumn with
      | inl sourceColumn =>
          exact (entry_primrec label sourceRow sourceColumn).of_eq fun problem => by
            simp [pad, zeroPad]
      | inr _ => exact (Primrec.const 0).of_eq fun problem => by simp [pad, zeroPad]
  | inr _ =>
      cases sumColumn with
      | inl _ => exact (Primrec.const 0).of_eq fun problem => by simp [pad, zeroPad]
      | inr _ => exact (Primrec.const 0).of_eq fun problem => by simp [pad, zeroPad]

/-- Padding is an exact reduction of the nonempty-product mortality predicate. -/
theorem pad_mortal_iff {d k : Nat} (extra : Nat) (problem : MortalityProblem d k) :
    (pad extra problem).Mortal ↔ problem.Mortal := by
  change IsMortal (Matrix.reindex finSumFinEquiv finSumFinEquiv ∘
    (zeroPad (κ := Fin extra) ∘ problem.matrix)) ↔ _
  rw [isMortal_reindex_iff, isMortal_zeroPad_iff]
  rfl

end MatrixMortality.Undecidability.MortalityProblem
