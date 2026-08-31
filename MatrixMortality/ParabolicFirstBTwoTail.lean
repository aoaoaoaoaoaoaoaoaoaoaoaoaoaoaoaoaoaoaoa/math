import MatrixMortality.ParabolicFirstBTwoTailBefore
import MatrixMortality.ParabolicFirstBTwoTailLower
import MatrixMortality.ParabolicFirstBTwoTailUpper

/-!
# Tail certificate for the second-first-`b` cylinder

The second-first-`b` root envelope leaves seventy-seven integral outer-wait pairs. This
module combines their exact tail-density certificates and isolates the sole integral
inner-wait candidate, on the tail prefix `ccb`.
-/

namespace MatrixMortality.ParabolicBlade

/-- A candidate tail root is the explicit `(213, 465, 38)` point on the `ccb` cylinder. -/
theorem firstBTwoTail_root_eq_exception
    (tail : List TagLetter) (contains_b : .b ∈ tail) (x y z : Nat)
    (candidate : FirstBTwoRootCandidate x y)
    (root_eq :
      firstBTwoTailZDenominator (firstBTwoTailA tail y) (firstBTwoTailD tail) x y * z =
        firstBTwoTailZNumerator (firstBTwoTailA tail y) (firstBTwoTailD tail) x y) :
    x = 213 ∧ y = 465 ∧ z = 38 ∧ ∃ rest, tail = [.c, .c, .b] ++ rest := by
  obtain ⟨j, rest, tail_eq⟩ := firstBTwoTail_first_b_decomposition tail contains_b
  subst tail
  by_cases x_eq : x = 213
  · subst x
    have y_lower : 465 ≤ y := by
      unfold FirstBTwoRootCandidate at candidate
      omega
    have y_upper : y ≤ 520 := by
      unfold FirstBTwoRootCandidate at candidate
      omega
    by_cases y_le : y ≤ 492
    · obtain ⟨j_eq, y_eq, z_eq⟩ :=
        firstBTwoTail_root_213_lower_exception j rest y z y_lower y_le root_eq
      refine ⟨rfl, y_eq, z_eq, rest, ?_⟩
      simp [j_eq]
    · have y_ge : 493 ≤ y := by omega
      exact (firstBTwoTail_root_213_upper_ne j rest y z y_ge y_upper root_eq).elim
  · have x_lt : x < 213 := by
      unfold FirstBTwoRootCandidate at candidate
      omega
    exact (firstBTwoTail_root_before_213_ne j rest x y z candidate x_lt root_eq).elim

end MatrixMortality.ParabolicBlade
