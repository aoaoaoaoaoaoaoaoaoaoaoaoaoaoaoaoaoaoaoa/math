import MatrixMortality.PrefixAlgebraRank

/-!
# Full algebra of the restricted prefix pair

The physical word `000` is rank one.  Powers of `1` make its column reachable in every
direction, and ten short binary contexts make its row observable in every direction.  Their
one hundred physical sandwiches span the full ten-dimensional matrix algebra.
-/

namespace MatrixMortality

/-- Every rational ten-by-ten matrix is a linear combination of physical products of the
restricted binary prefix pair throughout the arithmetic source envelope. -/
theorem prefixAlgebra_wordProductSpan_eq_top
    (β : Nat) (body : List TagLetter) (three_le : 3 ≤ β)
    (body_long : β - 1 ≤ body.length) :
    wordProductSpan (prefixAlgebraGenerator β body) = ⊤ := by
  have body_nonempty : body ≠ [] := by
    intro body_empty
    rw [body_empty] at body_long
    simp only [List.length_nil] at body_long
    omega
  apply wordProductSpan_eq_top_of_rankOne_contexts
    (prefixAlgebraGenerator β body)
    (prefixAlgebraColumn β body) (prefixAlgebraRow β)
    [false, false, false] (prefixAlgebra_zero_cube β body)
    prefixAlgebraLeftWords prefixAlgebraRightWords
  · exact prefixAlgebraReachable_isUnit β body three_le body_nonempty
  · exact prefixAlgebraObservable_isUnit β body three_le

end MatrixMortality
