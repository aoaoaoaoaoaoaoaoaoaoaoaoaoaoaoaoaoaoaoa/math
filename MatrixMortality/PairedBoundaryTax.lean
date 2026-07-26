import MatrixMortality.BoundaryTax
import MatrixMortality.PairedRank

/-!
# Exact diagonal punctuation cannot compress the paired series

The paired scalar series exposes four states.  Any exact diagonal two-channel bridge for that
series needs two further coordinates, so it cannot fit in dimension five.
-/

namespace MatrixMortality

open scoped Matrix

/--
Every exact diagonal two-channel realization of the paired coefficient series has at least six
states.  The inactive boundary column and row need only be nonzero; full rank-two boundary
matrices are stronger than necessary.
-/
theorem paired_exact_diagonal_twoChannel_state_lower_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : Nat) (body : List TagLetter) (three_le : 3 ≤ β)
    (generators : PairedControl → Matrix ι ι ℚ)
    (inactiveColumn activeColumn inactiveRow activeRow : ι → ℚ)
    (inactive_column_zero :
      ∀ word, activeRow ⬝ᵥ wordProduct generators word *ᵥ inactiveColumn = 0)
    (inactive_row_active_zero :
      ∀ word, inactiveRow ⬝ᵥ wordProduct generators word *ᵥ activeColumn = 0)
    (inactive_diagonal_zero :
      ∀ word, inactiveRow ⬝ᵥ wordProduct generators word *ᵥ inactiveColumn = 0)
    (column_ne_zero : inactiveColumn ≠ 0)
    (row_ne_zero : inactiveRow ≠ 0)
    (active_exact :
      RepresentsSeries (pairedCoefficient ℚ β body)
        generators activeRow activeColumn) :
    6 ≤ Fintype.card ι := by
  have section_eq :
      finiteHankel (linearCoefficient generators activeRow activeColumn)
          pairedRankPrefixes pairedRankSuffixes =
        pairedRankHankelRat β body := by
    ext pidx sidx
    simpa [finiteHankel, pairedRankHankelRat] using
      active_exact (pairedRankPrefixes pidx ++ pairedRankSuffixes sidx)
  have section_det_ne_zero :
      (finiteHankel (linearCoefficient generators activeRow activeColumn)
        pairedRankPrefixes pairedRankSuffixes).det ≠ 0 := by
    rw [section_eq]
    exact pairedRankHankelRat_det_ne_zero β body three_le
  have bound := exactDiagonalTwoChannel_card_lower_bound
    generators inactiveColumn activeColumn inactiveRow activeRow
    pairedRankPrefixes pairedRankSuffixes inactive_column_zero
    inactive_row_active_zero inactive_diagonal_zero column_ne_zero row_ne_zero
    section_det_ne_zero
  simpa using bound

end MatrixMortality
