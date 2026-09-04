import MatrixMortality.RunLengthHankel
import MatrixMortality.NearySideNormal
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-!
# Periodic Fourier-component rank screen

Two local rank strata drive the periodic-transition obstruction. A paired Fourier component
containing both the toggle and separator directions has rank at least three. A Neary component
containing the terminal direction and any ordinary direction has rank at least two.
-/

namespace MatrixMortality.PeriodicRankScreen

open scoped Matrix

variable {K : Type*} [Field K] [CharZero K]

/-- The paired benchmark separator direction over an arbitrary characteristic-zero field. -/
def pairedSeparator (q : K) : Square (Fin 4) K :=
  !![67, 67 * q, 67 * q, 67 * q;
     0, 0, 0, 0;
     81, 81 * q, 81 * q, 81 * q;
     -1, -q, -q, -q]

/-- One Fourier component in the span of the four paired benchmark roles. -/
def pairedComponent (t b c p q : K) : Square (Fin 4) K :=
  t • !![1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0] +
    b • !![1, 25, 203, 1; 0, 0, 0, 0; 0, 0, 243, 0; 0, 27, 0, 3] +
    c • !![1, 1508677, 2, 1; 0, 0, 0, 0; 0, 0, 3, 0; 0, 1594323, 0, 3] +
    p • pairedSeparator q

private def pairedRows : Fin 3 → Fin 4 := ![1, 2, 3]
private def pairedLeftColumns : Fin 3 → Fin 4 := ![0, 1, 3]
private def pairedRightColumns : Fin 3 → Fin 4 := ![0, 2, 3]
private def pairedTailRows : Fin 3 → Fin 4 := ![0, 1, 2]
private def pairedTailColumns : Fin 3 → Fin 4 := ![1, 2, 3]

omit [CharZero K] in
private theorem pairedLeftMinor_det (t b c p q : K) :
    ((pairedComponent t b c p q).submatrix pairedRows pairedLeftColumns).det =
      81 * p * t * (27 * b + 1594323 * c + t) := by
  have minor_eq :
      (pairedComponent t b c p q).submatrix pairedRows pairedLeftColumns =
      (!![0, 0, t;
        81 * p, 81 * p * q, 81 * p * q;
        -p, t + 27 * b + 1594323 * c - p * q, 3 * b + 3 * c - p * q] :
        Square (Fin 3) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pairedComponent, pairedSeparator, pairedRows, pairedLeftColumns] <;> ring
  rw [minor_eq]
  simp [Matrix.det_fin_three]
  ring

omit [CharZero K] in
private theorem pairedRightMinor_det (t b c p q : K) :
    ((pairedComponent t b c p q).submatrix pairedRows pairedRightColumns).det =
      p * t * (243 * b + 3 * c + t) := by
  have minor_eq :
      (pairedComponent t b c p q).submatrix pairedRows pairedRightColumns =
      (!![0, 0, t;
        81 * p, t + 243 * b + 3 * c + 81 * p * q, 81 * p * q;
        -p, -p * q, 3 * b + 3 * c - p * q] : Square (Fin 3) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pairedComponent, pairedSeparator, pairedRows, pairedRightColumns] <;> ring
  rw [minor_eq]
  simp [Matrix.det_fin_three]
  ring

private theorem pairedTailMinor_scaled_det (t b c p q : K)
    (left_zero : 27 * b + 1594323 * c + t = 0)
    (right_zero : 243 * b + 3 * c + t = 0) :
    597871 * ((pairedComponent t b c p q).submatrix pairedTailRows pairedTailColumns).det =
      5260605 * p * q * t ^ 2 := by
  have minor_eq :
      (pairedComponent t b c p q).submatrix pairedTailRows pairedTailColumns =
      (!![25 * b + 1508677 * c + 67 * p * q, 203 * b + 2 * c + 67 * p * q,
          b + c + 67 * p * q;
        0, 0, t;
        81 * p * q, t + 243 * b + 3 * c + 81 * p * q, 81 * p * q] :
        Square (Fin 3) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pairedComponent, pairedSeparator, pairedTailRows, pairedTailColumns] <;> ring
  rw [minor_eq]
  simp [Matrix.det_fin_three]
  have hb : 16142517 * b + 66430 * t = 0 := by
    linear_combination (-1 / 8 : K) * left_zero + (531441 / 8 : K) * right_zero
  have hc : 1793613 * c + t = 0 := by
    linear_combination (9 / 8 : K) * left_zero - (1 / 8 : K) * right_zero
  linear_combination
    (-t * (3632066325 * b + 219184641920406 * c + 1113833673 * p * q + 25 * t) /
      16142517) * hb +
    (-t * (24353844120009 * c + 657554001092964 * p * q - 1660750 * t) /
      16142517) * hc

omit [CharZero K] in
private theorem three_le_rank_of_minor
    (matrix : Square (Fin 4) K) (rows columns : Fin 3 → Fin 4)
    (det_ne_zero : (matrix.submatrix rows columns).det ≠ 0) :
    3 ≤ matrix.rank := by
  have minor_rank : (matrix.submatrix rows columns).rank = 3 := by
    have det_unit : IsUnit (matrix.submatrix rows columns).det :=
      isUnit_iff_ne_zero.mpr det_ne_zero
    have rank_eq := Matrix.rank_mul_eq_right_of_isUnit_det
      (matrix.submatrix rows columns) (1 : Square (Fin 3) K) det_unit
    simpa using rank_eq
  rw [← minor_rank]
  exact Matrix.rank_submatrix_le matrix rows columns

/-- Every paired Fourier component with nonzero toggle and separator coefficients has rank at
least three; the separator-row parameter only needs to be nonzero. -/
theorem pairedComponent_three_le_rank (t b c p q : K)
    (t_ne_zero : t ≠ 0) (p_ne_zero : p ≠ 0) (q_ne_zero : q ≠ 0) :
    3 ≤ (pairedComponent t b c p q).rank := by
  by_cases left_zero : 27 * b + 1594323 * c + t = 0
  · by_cases right_zero : 243 * b + 3 * c + t = 0
    · apply three_le_rank_of_minor _ pairedTailRows pairedTailColumns
      intro det_zero
      have scaled := pairedTailMinor_scaled_det t b c p q left_zero right_zero
      have right_ne_zero : 5260605 * p * q * t ^ 2 ≠ 0 :=
        mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) p_ne_zero) q_ne_zero)
          (pow_ne_zero 2 t_ne_zero)
      exact right_ne_zero (by simpa [det_zero] using scaled.symm)
    · apply three_le_rank_of_minor _ pairedRows pairedRightColumns
      rw [pairedRightMinor_det]
      exact mul_ne_zero (mul_ne_zero p_ne_zero t_ne_zero) right_zero
  · apply three_le_rank_of_minor _ pairedRows pairedLeftColumns
    rw [pairedLeftMinor_det]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) p_ne_zero) t_ne_zero) left_zero

/-- The five coefficient directions of the width-three, body-`bb` Neary family. -/
def nearyComponent (ruleB ruleC eraseB eraseC terminal : K) : Square (Fin 3) K :=
  ruleB • !![1, 25, 203; 0, 27, 0; 0, 0, 243] +
    ruleC • !![1, 1508677, 2; 0, 1594323, 0; 0, 0, 3] +
    eraseB • !![1, 1, 203; 0, 3, 0; 0, 0, 243] +
    eraseC • !![1, 1, 2; 0, 3, 0; 0, 0, 3] +
    terminal • !![67, 0, 0; -1, 0, 0; 81, 0, 0]

private def nearyUpperRows : Fin 2 → Fin 3 := ![0, 1]
private def nearyMiddleRows : Fin 2 → Fin 3 := ![0, 2]
private def nearyLowerRows : Fin 2 → Fin 3 := ![1, 2]
private def nearyLeftColumns : Fin 2 → Fin 3 := ![0, 1]
private def nearyRightColumns : Fin 2 → Fin 3 := ![0, 2]

omit [CharZero K] in
private theorem nearyUpperLeftMinor_det (a d e f g : K) :
    ((nearyComponent a d e f g).submatrix nearyMiddleRows nearyLeftColumns).det =
      -81 * g * (25 * a + 1508677 * d + e + f) := by
  have minor_eq :
      (nearyComponent a d e f g).submatrix nearyMiddleRows nearyLeftColumns =
      (!![a + d + e + f + 67 * g, 25 * a + 1508677 * d + e + f;
        81 * g, 0] : Square (Fin 2) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [nearyComponent, nearyMiddleRows, nearyLeftColumns] <;> ring
  rw [minor_eq]
  simp [Matrix.det_fin_two]
  ring

omit [CharZero K] in
private theorem nearyUpperRightMinor_det (a d e f g : K) :
    ((nearyComponent a d e f g).submatrix nearyUpperRows nearyRightColumns).det =
      g * (203 * a + 2 * d + 203 * e + 2 * f) := by
  have minor_eq :
      (nearyComponent a d e f g).submatrix nearyUpperRows nearyRightColumns =
      (!![a + d + e + f + 67 * g, 203 * a + 2 * d + 203 * e + 2 * f;
        -g, 0] : Square (Fin 2) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [nearyComponent, nearyUpperRows, nearyRightColumns] <;> ring
  rw [minor_eq]
  simp [Matrix.det_fin_two]
  ring

omit [CharZero K] in
private theorem nearyLowerLeftMinor_det (a d e f g : K) :
    ((nearyComponent a d e f g).submatrix nearyLowerRows nearyLeftColumns).det =
      -243 * g * (9 * a + 531441 * d + e + f) := by
  have minor_eq :
      (nearyComponent a d e f g).submatrix nearyLowerRows nearyLeftColumns =
      (!![-g, 27 * a + 1594323 * d + 3 * e + 3 * f;
        81 * g, 0] : Square (Fin 2) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [nearyComponent, nearyLowerRows, nearyLeftColumns] <;> ring
  rw [minor_eq]
  simp [Matrix.det_fin_two]
  ring

omit [CharZero K] in
private theorem nearyLowerRightMinor_det (a d e f g : K) :
    ((nearyComponent a d e f g).submatrix nearyLowerRows nearyRightColumns).det =
      -3 * g * (81 * a + d + 81 * e + f) := by
  have minor_eq :
      (nearyComponent a d e f g).submatrix nearyLowerRows nearyRightColumns =
      (!![-g, 0;
        81 * g, 243 * a + 3 * d + 243 * e + 3 * f] : Square (Fin 2) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [nearyComponent, nearyLowerRows, nearyRightColumns] <;> ring
  rw [minor_eq]
  simp [Matrix.det_fin_two]
  ring

omit [CharZero K] in
private theorem two_le_rank_of_minor
    (matrix : Square (Fin 3) K) (rows columns : Fin 2 → Fin 3)
    (det_ne_zero : (matrix.submatrix rows columns).det ≠ 0) :
    2 ≤ matrix.rank := by
  have minor_rank : (matrix.submatrix rows columns).rank = 2 := by
    have det_unit : IsUnit (matrix.submatrix rows columns).det :=
      isUnit_iff_ne_zero.mpr det_ne_zero
    have rank_eq := Matrix.rank_mul_eq_right_of_isUnit_det
      (matrix.submatrix rows columns) (1 : Square (Fin 2) K) det_unit
    simpa using rank_eq
  rw [← minor_rank]
  exact Matrix.rank_submatrix_le matrix rows columns

/-- A Neary Fourier component containing the terminal direction and any nonzero ordinary
coefficient has rank at least two. -/
theorem nearyComponent_two_le_rank (a d e f g : K) (g_ne_zero : g ≠ 0)
    (ordinary_ne_zero : a ≠ 0 ∨ d ≠ 0 ∨ e ≠ 0 ∨ f ≠ 0) :
    2 ≤ (nearyComponent a d e f g).rank := by
  by_cases upper_left_zero : 25 * a + 1508677 * d + e + f = 0
  · by_cases upper_right_zero : 203 * a + 2 * d + 203 * e + 2 * f = 0
    · by_cases lower_left_zero : 9 * a + 531441 * d + e + f = 0
      · by_cases lower_right_zero : 81 * a + d + 81 * e + f = 0
        · have a_zero : a = 0 := by
            linear_combination
              (2555 / 3294 : K) * upper_left_zero -
                (187930 / 67527 : K) * upper_right_zero -
                (9671 / 4392 : K) * lower_left_zero +
                (1259131 / 180072 : K) * lower_right_zero
          have d_zero : d = 0 := by
            linear_combination
              (-1 / 85644 : K) * upper_left_zero +
                (40 / 877851 : K) * upper_right_zero +
                (1 / 28548 : K) * lower_left_zero -
                (67 / 585234 : K) * lower_right_zero
          have e_zero : e = 0 := by
            linear_combination
              (-2555 / 3294 : K) * upper_left_zero +
                (189577 / 67527 : K) * upper_right_zero +
                (9671 / 4392 : K) * lower_left_zero -
                (1267915 / 180072 : K) * lower_right_zero
          have f_zero : f = 0 := by
            linear_combination
              (1 / 85644 : K) * upper_left_zero -
                (1734331 / 877851 : K) * upper_right_zero -
                (1 / 28548 : K) * lower_left_zero +
                (2897689 / 585234 : K) * lower_right_zero
          rcases ordinary_ne_zero with a_ne | d_ne | e_ne | f_ne
          · exact (a_ne a_zero).elim
          · exact (d_ne d_zero).elim
          · exact (e_ne e_zero).elim
          · exact (f_ne f_zero).elim
        · apply two_le_rank_of_minor _ nearyLowerRows nearyRightColumns
          rw [nearyLowerRightMinor_det]
          exact mul_ne_zero (mul_ne_zero (by norm_num) g_ne_zero) lower_right_zero
      · apply two_le_rank_of_minor _ nearyLowerRows nearyLeftColumns
        rw [nearyLowerLeftMinor_det]
        exact mul_ne_zero (mul_ne_zero (by norm_num) g_ne_zero) lower_left_zero
    · apply two_le_rank_of_minor _ nearyUpperRows nearyRightColumns
      rw [nearyUpperRightMinor_det]
      exact mul_ne_zero g_ne_zero upper_right_zero
  · apply two_le_rank_of_minor _ nearyMiddleRows nearyLeftColumns
    rw [nearyUpperLeftMinor_det]
    exact mul_ne_zero (mul_ne_zero (by norm_num) g_ne_zero) upper_left_zero

end MatrixMortality.PeriodicRankScreen
