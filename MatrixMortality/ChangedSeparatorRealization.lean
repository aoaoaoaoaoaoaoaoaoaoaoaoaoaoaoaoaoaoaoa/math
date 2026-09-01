import MatrixMortality.ChangedSeparatorTail
import MatrixMortality.EffectiveRational
import MatrixMortality.RationalClearing
import MatrixMortality.ReturnFamily

/-!
# Rank-nine changed-separator realization

The `3+3+2+1` chain realizes the paired toggle and data roles at return times zero, one, and two.
Its surviving eigenline carries the changed rank-one separator at every later return.
-/

namespace MatrixMortality

open scoped Matrix

namespace ChangedSeparatorRealization

/-- Positional radix used by the Neary body encoding. -/
def widthScale (β : Nat) : ℚ := 3 ^ β

/-- Common denominator polynomial of the exact three-parameter chain chart. -/
def chainDenominator {R : Type*} [FractionArithmetic R] (ρ V K : R) : R :=
  9 * K ^ 2 * ρ ^ 2 + 2 * K ^ 2 * ρ - K ^ 2 -
    18 * K * V * ρ ^ 2 + 2 * K * V - 9 * K * ρ ^ 2 -
    6 * K * ρ - 47 * K + 48 * V + 96

/-- Nonzero denominator of the geometric tail specialization. -/
def denominator (β : Nat) (body : List TagLetter) : ℚ :=
  chainDenominator (widthScale β) (ChangedSeparatorTail.lowerCCode β body)
    (ChangedSeparatorTail.lowerCScale β body)

theorem denominator_eq_transferDenominator (β : Nat) (body : List TagLetter) :
    denominator β body = ChangedSeparatorTail.transferDenominator β body := by
  rfl

theorem widthScale_pos (β : Nat) : 0 < widthScale β := by
  simp [widthScale]

theorem denominator_lt_zero (β : Nat) (body : List TagLetter) :
    denominator β body < 0 :=
  denominator_eq_transferDenominator β body ▸
    ChangedSeparatorTail.transferDenominator_lt_zero β body

theorem denominator_ne_zero (β : Nat) (body : List TagLetter) :
    denominator β body ≠ 0 :=
  ne_of_lt (denominator_lt_zero β body)

/-- Eigenvalue of the exact chart's one-dimensional geometric tail. -/
def chainTailEigenvalue {R : Type*} [FractionArithmetic R] (ρ V K : R) : R :=
  K * (3 * ρ - 1) * (K - 2 * V - 1) / chainDenominator ρ V K

/-- Eigenvalue carried by the realization's specialized geometric tail. -/
def tailEigenvalue (β : Nat) (body : List TagLetter) : ℚ :=
  chainTailEigenvalue (widthScale β) (ChangedSeparatorTail.lowerCCode β body)
    (ChangedSeparatorTail.lowerCScale β body)

theorem tailEigenvalue_ne_zero (β : Nat) (body : List TagLetter) :
    tailEigenvalue β body ≠ 0 := by
  have lowerScale_ne_zero : ChangedSeparatorTail.lowerCScale β body ≠ 0 := by
    linarith [ChangedSeparatorTail.lowerCScale_gt_three β body]
  have widthFactor_ne_zero : 3 * widthScale β - 1 ≠ 0 := by
    have width_one_le : 1 ≤ widthScale β := by
      exact one_le_pow₀ (by norm_num)
    linarith
  have tailGap_ne_zero :
      ChangedSeparatorTail.lowerCScale β body -
          2 * ChangedSeparatorTail.lowerCCode β body - 1 ≠ 0 := by
    linarith [ChangedSeparatorTail.lowerCScale_sub_two_mul_lowerCCode_sub_one_lt_zero β body]
  unfold tailEigenvalue chainTailEigenvalue
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero lowerScale_ne_zero widthFactor_ne_zero) tailGap_ne_zero)
    (denominator_ne_zero β body)

/-- Nonvanishing locus of the exact rational chain chart. -/
structure RegularChart (ρ V K : ℚ) : Prop where
  width_ne_zero : ρ ≠ 0
  lowerScale_ne_zero : K ≠ 0
  denominator_ne_zero : chainDenominator ρ V K ≠ 0
  widthFactor_ne_zero : 3 * ρ - 1 ≠ 0
  tailGap_ne_zero : K - 2 * V - 1 ≠ 0
  sumGap_ne_zero : K + 3 * V - 6 ≠ 0
  chartGap_ne_zero : K - V - 2 ≠ 0

namespace RegularChart

/-- The output chart's tail factor is the negative of the input chart's factor. -/
theorem negTailGap_eq (V K : ℚ) :
    -K + 2 * V + 1 = -(K - 2 * V - 1) := by
  ring

/-- Normalized subtraction form of the output chart's tail factor. -/
theorem subNegTailGap_eq (V K : ℚ) :
    1 - (K - 2 * V) = -(K - 2 * V - 1) := by
  ring

/-- Odd powers preserve the normalized tail factor's sign reversal. -/
theorem subNegTailGap_cube_eq (V K : ℚ) :
    (1 - (K - 2 * V)) ^ 3 = -(K - 2 * V - 1) ^ 3 := by
  rw [subNegTailGap_eq]
  ring

/-- The output chart's body gap is the negative of the input chart's gap. -/
theorem negChartGap_eq (V K : ℚ) :
    -K + V + 2 = -(K - V - 2) := by
  ring

/-- Parenthesized normalized subtraction form of the output chart's body gap. -/
theorem subNegChartGap_eq (V K : ℚ) :
    2 - (K - V) = -(K - V - 2) := by
  ring

/-- The output chart's sum factor is the negative of the input chart's factor. -/
theorem negSumGap_eq (V K : ℚ) :
    -K - 3 * V + 6 = -(K + 3 * V - 6) := by
  ring

/-- Normalized subtraction form of the output chart's sum factor. -/
theorem normalizedNegSumGap_eq (V K : ℚ) :
    6 - (K + 3 * V) = -(K + 3 * V - 6) := by
  ring

/-- The apparently mixed denominator is the product of the three chart gaps. -/
theorem mixedDenominator_eq (ρ V K : ℚ) :
    3 * K ^ 2 * ρ - K ^ 2 - 9 * K * V * ρ + 3 * K * V -
        9 * K * ρ + 3 * K + 6 * V ^ 2 * ρ - 2 * V ^ 2 +
        15 * V * ρ - 5 * V + 6 * ρ - 2 =
      (3 * ρ - 1) * (K - 2 * V - 1) * (K - V - 2) := by
  ring

/-- The shorter mixed denominator is the product of the width and tail gaps. -/
theorem widthTailDenominator_eq (ρ V K : ℚ) :
    3 * K * ρ - K - 6 * V * ρ + 2 * V - 3 * ρ + 1 =
      (3 * ρ - 1) * (K - 2 * V - 1) := by
  ring

theorem negTailGap_ne_zero {ρ V K : ℚ} (regular : RegularChart ρ V K) :
    -K + 2 * V + 1 ≠ 0 := by
  rw [negTailGap_eq]
  exact neg_ne_zero.mpr regular.tailGap_ne_zero

theorem negChartGap_ne_zero {ρ V K : ℚ} (regular : RegularChart ρ V K) :
    -K + V + 2 ≠ 0 := by
  rw [negChartGap_eq]
  exact neg_ne_zero.mpr regular.chartGap_ne_zero

theorem factoredGap_ne_zero {ρ V K : ℚ} (regular : RegularChart ρ V K) :
    3 * K ^ 2 * ρ - K ^ 2 - 9 * K * V * ρ + 3 * K * V -
        9 * K * ρ + 3 * K + 6 * V ^ 2 * ρ - 2 * V ^ 2 +
        15 * V * ρ - 5 * V + 6 * ρ - 2 ≠ 0 := by
  rw [mixedDenominator_eq]
  exact mul_ne_zero
    (mul_ne_zero regular.widthFactor_ne_zero regular.tailGap_ne_zero)
    regular.chartGap_ne_zero

end RegularChart

/-- Every positive-width encoded body containing `b` lies in the regular chart. -/
theorem regularChart (β : Nat) (β_pos : 0 < β) (body : List TagLetter)
    (b_mem : .b ∈ body) :
    RegularChart (widthScale β) (ChangedSeparatorTail.lowerCCode β body)
      (ChangedSeparatorTail.lowerCScale β body) where
  width_ne_zero := (widthScale_pos β).ne'
  lowerScale_ne_zero := by
    linarith [ChangedSeparatorTail.lowerCScale_gt_three β body]
  denominator_ne_zero := denominator_ne_zero β body
  widthFactor_ne_zero := by
    have width_one_le : 1 ≤ widthScale β := one_le_pow₀ (by norm_num)
    linarith
  tailGap_ne_zero := by
    linarith [ChangedSeparatorTail.lowerCScale_sub_two_mul_lowerCCode_sub_one_lt_zero β body]
  sumGap_ne_zero := by
    linarith [ChangedSeparatorTail.lowerCScale_add_three_mul_lowerCCode_sub_six_pos β body]
  chartGap_ne_zero := by
    linarith [ChangedSeparatorTail.lowerCCode_add_two_lt_lowerCScale_of_b_mem
      β β_pos body b_mem]

/-- Two length-three nilpotent chains, one length-two chain, and the geometric tail line. -/
def chainTransition {R : Type*} [FractionArithmetic R] (ρ V K : R) : Square (Fin 9) R :=
  let s := chainTailEigenvalue ρ V K
  !![0, 0, 0, 0, 0, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, s]

/-- The chain transition specialized to one encoded Neary instance. -/
def transition (β : Nat) (body : List TagLetter) : Square (Fin 9) ℚ :=
  chainTransition (widthScale β) (ChangedSeparatorTail.lowerCCode β body)
    (ChangedSeparatorTail.lowerCScale β body)

/-- The paired `b` data role in chart coordinates. -/
def chainDataB (ρ : ℚ) : Square (Fin 4) ℚ :=
  !![1, 25, (15 * ρ + 1) / 2, 1;
     0, 0, 0, 0;
     0, 0, 9 * ρ, 0;
     0, 27, 0, 3]

/-- The paired `c` data role in chart coordinates. -/
def chainDataC (V K : ℚ) : Square (Fin 4) ℚ :=
  !![1, V, 2, 1;
     0, 0, 0, 0;
     0, 0, 3, 0;
     0, K, 0, 3]

/-- Observable column of the surviving geometric tail. -/
def chainTailColumn (ρ : ℚ) : Fin 4 → ℚ :=
  ![(5 * ρ - 1) / 2, 0, 3 * ρ, -1]

/-- Body-dependent row of the surviving geometric tail. -/
def chainTailRow (ρ V K : ℚ) : Fin 4 → ℚ :=
  ![2 * K * (K - 3) / chainDenominator ρ V K,
    2 * K * (K - 3 * V) / chainDenominator ρ V K,
    2 * K * (K - 3 * V) / chainDenominator ρ V K,
    2 * K * (K - 3 * V) / chainDenominator ρ V K]

/-- Rank-one matrix carried by the realization after the nilpotent chains die. -/
def chainTailSeparator (ρ V K : ℚ) : Square (Fin 4) ℚ :=
  Matrix.vecMulVec (chainTailColumn ρ) (chainTailRow ρ V K)

/-- Four interface columns in the exact three-parameter chain chart. -/
def chainInput {R : Type*} [FractionArithmetic R]
    (ρ V K : R) : Matrix (Fin 9) (Fin 4) R :=
  !![
    1,
    0,
    (-K*ρ + K - 2*V)/(2*K*ρ),
    (K - 3*V)/K;
    0,
    0,
    5/2 - 1/(2*ρ) - 3*V/K + V/(K*ρ) - 25/(K*ρ) + 27*V/(K ^ 2*ρ),
    3*(35*K ^ 2*ρ - 12*K ^ 2 - 108*K*V*ρ + 36*K*V + 30*K*ρ + 24*K + 81*V ^ 2*ρ - 24*V ^ 2 - 162*V*ρ
      - 48*V)/(K ^ 2*ρ*(K + 3*V - 6));
    0,
    0,
    (135*K ^ 4*ρ ^ 4 + 3*K ^ 4*ρ ^ 3 - 9*K ^ 4*ρ ^ 2 - K ^ 4*ρ - 270*K ^ 3*V*ρ ^ 4 + 108*K ^ 3*V*ρ ^
      3 + 2*K ^ 3*V*ρ - 135*K ^ 3*ρ ^ 4 - 63*K ^ 3*ρ ^ 3 - 249*K ^ 3*ρ ^ 2 - 147*K ^ 3*ρ + 50*K ^ 3
      - 108*K ^ 2*V ^ 2*ρ ^ 3 + 36*K ^ 2*V ^ 2*ρ ^ 2 - 54*K ^ 2*V*ρ ^ 3 - 684*K ^ 2*V*ρ ^ 2 + 450*K
      ^ 2*V*ρ - 152*K ^ 2*V + 1800*K ^ 2*ρ ^ 2 - 3890*K ^ 2*ρ + 1198*K ^ 2 + 972*K*V ^ 2*ρ ^ 2 -
      312*K*V ^ 2*ρ + 104*K*V ^ 2 - 1944*K*V*ρ ^ 2 + 12288*K*V*ρ - 3692*K*V - 3240*K*ρ - 2592*K -
      8748*V ^ 2*ρ + 2592*V ^ 2 + 17496*V*ρ + 5184*V)/(4*K ^ 3*ρ ^ 2*(K + 3*V - 6)),
    0;
    0,
    1,
    1/(K*ρ),
    3/K;
    0,
    0,
    3/K - 27/(K ^ 2*ρ),
    3*((K - 27)*(K*ρ + 3*V*ρ - V - 6*ρ + 1) + (K - 3)*(V - 25))/(K ^ 2*ρ*(K + 3*V - 6));
    0,
    0,
    (-27*K ^ 3*ρ ^ 3 - 6*K ^ 3*ρ ^ 2 - K ^ 3*ρ + 54*K ^ 2*V*ρ ^ 3 + 27*K ^ 2*ρ ^ 3 - 144*K ^ 2*ρ ^ 2
      + K ^ 2*ρ + 50*K ^ 2 - 486*K*V*ρ ^ 2 - 6*K*V*ρ - 52*K*V + 972*K*ρ ^ 2 + 1470*K*ρ + 1198*K +
      4374*V*ρ - 1296*V - 8748*ρ - 2592)/(2*K ^ 3*ρ ^ 2*(K + 3*V - 6)),
    0;
    0,
    0,
    0,
    216*(K - V - 2)/(K*(K + 3*V - 6));
    0,
    0,
    (81*K ^ 3*ρ ^ 3 + 18*K ^ 3*ρ ^ 2 + 5*K ^ 3*ρ - 162*K ^ 2*V*ρ ^ 3 + 6*K ^ 2*V*ρ - 81*K ^ 2*ρ ^ 3
      - 54*K ^ 2*ρ ^ 2 - 21*K ^ 2*ρ - 150*K ^ 2 + 156*K*V - 3594*K + 3888*V + 7776)/(2*K ^ 2*ρ*(K +
      3*V - 6)),
    0;
    2*(K - 3)*(9*K ^ 2*ρ ^ 2 + 2*K ^ 2*ρ - K ^ 2 - 18*K*V*ρ ^ 2 + 2*K*V - 9*K*ρ ^ 2 - 6*K*ρ - 47*K +
      48*V + 96) ^ 2/(K ^ 2*(3*ρ - 1) ^ 3*(K - 2*V - 1) ^ 3),
    2*(K - 3*V)*(9*K ^ 2*ρ ^ 2 + 2*K ^ 2*ρ - K ^ 2 - 18*K*V*ρ ^ 2 + 2*K*V - 9*K*ρ ^ 2 - 6*K*ρ - 47*K
      + 48*V + 96) ^ 2/(K ^ 2*(3*ρ - 1) ^ 3*(K - 2*V - 1) ^ 3),
    2*(K - 3*V)*(9*K ^ 2*ρ ^ 2 + 2*K ^ 2*ρ - K ^ 2 - 18*K*V*ρ ^ 2 + 2*K*V - 9*K*ρ ^ 2 - 6*K*ρ - 47*K
      + 48*V + 96) ^ 2/(K ^ 2*(3*ρ - 1) ^ 3*(K - 2*V - 1) ^ 3),
    2*(K - 3*V)*(9*K ^ 2*ρ ^ 2 + 2*K ^ 2*ρ - K ^ 2 - 18*K*V*ρ ^ 2 + 2*K*V - 9*K*ρ ^ 2 - 6*K*ρ - 47*K
      + 48*V + 96) ^ 2/(K ^ 2*(3*ρ - 1) ^ 3*(K - 2*V - 1) ^ 3)]

/- The exact generated chart is expensive to elaborate but contains no proof search. -/
set_option maxHeartbeats 800000 in
/-- Four interface rows in the exact three-parameter chain chart. -/
def chainOutput {R : Type*} [FractionArithmetic R]
    (ρ V K : R) : Matrix (Fin 4) (Fin 9) R :=
  !![
    (K ^ 2*(3*ρ - 1) ^ 3*(-K + 2*V + 1) ^ 3 + (K - 3)*(5*ρ - 1)*(9*K ^ 2*ρ ^ 2 + 2*K ^ 2*ρ - K ^ 2 -
      18*K*V*ρ ^ 2 + 2*K*V - 9*K*ρ ^ 2 - 6*K*ρ - 47*K + 48*V + 96) ^ 2)/(K ^ 2*(3*ρ - 1) ^ 3*(-K +
      2*V + 1) ^ 3),
    (K*(3*ρ - 1) ^ 2*(-K + 2*V + 1) ^ 2 - (K - 3)*(5*ρ - 1)*(9*K ^ 2*ρ ^ 2 + 2*K ^ 2*ρ - K ^ 2 -
      18*K*V*ρ ^ 2 + 2*K*V - 9*K*ρ ^ 2 - 6*K*ρ - 47*K + 48*V + 96))/(K*(3*ρ - 1) ^ 2*(-K + 2*V + 1)
      ^ 2),
    ((K - 3)*(5*ρ - 1) + (3*ρ - 1)*(-K + 2*V + 1))/((3*ρ - 1)*(-K + 2*V + 1)),
    (K - 3*V)*(5*ρ - 1)*(9*K ^ 2*ρ ^ 2 + 2*K ^ 2*ρ - K ^ 2 - 18*K*V*ρ ^ 2 + 2*K*V - 9*K*ρ ^ 2 -
      6*K*ρ - 47*K + 48*V + 96) ^ 2/(K ^ 2*(3*ρ - 1) ^ 3*(-K + 2*V + 1) ^ 3),
    (25*K*(3*ρ - 1) ^ 2*(-K + 2*V + 1) ^ 2 - (K - 3*V)*(5*ρ - 1)*(9*K ^ 2*ρ ^ 2 + 2*K ^ 2*ρ - K ^ 2
      - 18*K*V*ρ ^ 2 + 2*K*V - 9*K*ρ ^ 2 - 6*K*ρ - 47*K + 48*V + 96))/(K*(3*ρ - 1) ^ 2*(-K + 2*V +
      1) ^ 2),
    (V*(3*ρ - 1)*(-K + 2*V + 1) + (K - 3*V)*(5*ρ - 1))/((3*ρ - 1)*(-K + 2*V + 1)),
    (-3*K ^ 4*ρ ^ 2 + K ^ 4*ρ + 6*K ^ 3*V*ρ ^ 2 - 2*K ^ 3*V*ρ + 1620*K ^ 3*ρ ^ 3 - 483*K ^ 3*ρ ^ 2 +
      29*K ^ 3*ρ + 27*K ^ 2*V ^ 2*ρ ^ 2 - 9*K ^ 2*V ^ 2*ρ - 4860*K ^ 2*V*ρ ^ 3 + 1899*K ^ 2*V*ρ ^ 2
      - 357*K ^ 2*V*ρ + 72*K ^ 2*V - 4860*K ^ 2*ρ ^ 3 + 6849*K ^ 2*ρ ^ 2 - 5223*K ^ 2*ρ - 72*K ^ 2 -
      54*K*V ^ 3*ρ ^ 2 + 18*K*V ^ 3*ρ + 3240*K*V ^ 2*ρ ^ 3 - 1890*K*V ^ 2*ρ ^ 2 + 918*K*V ^ 2*ρ -
      216*K*V ^ 2 + 8100*K*V*ρ ^ 3 + 4590*K*V*ρ ^ 2 - 558*K*V*ρ + 1728*K*V + 3240*K*ρ ^ 3 -
      42093*K*ρ ^ 2 + 32319*K*ρ - 1512*K + 1458*V ^ 3*ρ ^ 2 - 918*V ^ 3*ρ + 144*V ^ 3 - 38637*V ^
      2*ρ ^ 2 + 13959*V ^ 2*ρ - 1512*V ^ 2 + 53217*V*ρ ^ 2 - 25731*V*ρ - 1944*V + 36450*ρ ^ 2 -
      35910*ρ + 3312)/(216*K*ρ*(3*K ^ 2*ρ - K ^ 2 - 9*K*V*ρ + 3*K*V - 9*K*ρ + 3*K + 6*V ^ 2*ρ - 2*V
      ^ 2 + 15*V*ρ - 5*V + 6*ρ - 2)),
    0,
    5*ρ/2 - 1/2;
    0,
    0,
    0,
    0,
    0,
    0,
    K*(-K - 3*V + 6)/(216*(-K + V + 2)),
    0,
    0;
    6*ρ*(K - 3)*(9*K ^ 2*ρ ^ 2 + 2*K ^ 2*ρ - K ^ 2 - 18*K*V*ρ ^ 2 + 2*K*V - 9*K*ρ ^ 2 - 6*K*ρ - 47*K
      + 48*V + 96) ^ 2/(K ^ 2*(3*ρ - 1) ^ 3*(-K + 2*V + 1) ^ 3),
    -6*ρ*(K - 3)*(9*K ^ 2*ρ ^ 2 + 2*K ^ 2*ρ - K ^ 2 - 18*K*V*ρ ^ 2 + 2*K*V - 9*K*ρ ^ 2 - 6*K*ρ -
      47*K + 48*V + 96)/(K*(3*ρ - 1) ^ 2*(-K + 2*V + 1) ^ 2),
    6*ρ*(K - 3)/((3*ρ - 1)*(-K + 2*V + 1)),
    6*ρ*(K - 3*V)*(9*K ^ 2*ρ ^ 2 + 2*K ^ 2*ρ - K ^ 2 - 18*K*V*ρ ^ 2 + 2*K*V - 9*K*ρ ^ 2 - 6*K*ρ -
      47*K + 48*V + 96) ^ 2/(K ^ 2*(3*ρ - 1) ^ 3*(-K + 2*V + 1) ^ 3),
    -6*ρ*(K - 3*V)*(9*K ^ 2*ρ ^ 2 + 2*K ^ 2*ρ - K ^ 2 - 18*K*V*ρ ^ 2 + 2*K*V - 9*K*ρ ^ 2 - 6*K*ρ -
      47*K + 48*V + 96)/(K*(3*ρ - 1) ^ 2*(-K + 2*V + 1) ^ 2),
    6*ρ*(K - 3*V)/((3*ρ - 1)*(-K + 2*V + 1)),
    (9*K ^ 2*ρ ^ 2 + 2*K ^ 2*ρ - K ^ 2 - 18*K*V*ρ ^ 2 + 2*K*V - 9*K*ρ ^ 2 - 6*K*ρ - 47*K + 48*V +
      96)/(K*(3*K*ρ - K - 6*V*ρ + 2*V - 3*ρ + 1)),
    1,
    3*ρ;
    2*(3 - K)*(9*K ^ 2*ρ ^ 2 + 2*K ^ 2*ρ - K ^ 2 - 18*K*V*ρ ^ 2 + 2*K*V - 9*K*ρ ^ 2 - 6*K*ρ - 47*K +
      48*V + 96) ^ 2/(K ^ 2*(3*ρ - 1) ^ 3*(-K + 2*V + 1) ^ 3),
    2*(K - 3)*(9*K ^ 2*ρ ^ 2 + 2*K ^ 2*ρ - K ^ 2 - 18*K*V*ρ ^ 2 + 2*K*V - 9*K*ρ ^ 2 - 6*K*ρ - 47*K +
      48*V + 96)/(K*(3*ρ - 1) ^ 2*(-K + 2*V + 1) ^ 2),
    2*(3 - K)/((3*ρ - 1)*(-K + 2*V + 1)),
    (K ^ 2*(3*ρ - 1) ^ 3*(-K + 2*V + 1) ^ 3 + 2*(-K + 3*V)*(9*K ^ 2*ρ ^ 2 + 2*K ^ 2*ρ - K ^ 2 -
      18*K*V*ρ ^ 2 + 2*K*V - 9*K*ρ ^ 2 - 6*K*ρ - 47*K + 48*V + 96) ^ 2)/(K ^ 2*(3*ρ - 1) ^ 3*(-K +
      2*V + 1) ^ 3),
    (27*K*(3*ρ - 1) ^ 2*(-K + 2*V + 1) ^ 2 + 2*(K - 3*V)*(9*K ^ 2*ρ ^ 2 + 2*K ^ 2*ρ - K ^ 2 -
      18*K*V*ρ ^ 2 + 2*K*V - 9*K*ρ ^ 2 - 6*K*ρ - 47*K + 48*V + 96))/(K*(3*ρ - 1) ^ 2*(-K + 2*V + 1)
      ^ 2),
    (K*(3*ρ - 1)*(-K + 2*V + 1) - 2*K + 6*V)/((3*ρ - 1)*(-K + 2*V + 1)),
    (-300*K ^ 3*ρ ^ 2 - 20*K ^ 3*ρ + 24*K ^ 3 + 564*K ^ 2*V*ρ ^ 2 + 76*K ^ 2*V*ρ - 72*K ^ 2*V +
      3423*K ^ 2*ρ ^ 2 + 1259*K ^ 2*ρ + 432*K ^ 2 + 72*K*V ^ 2*ρ ^ 2 - 168*K*V ^ 2*ρ + 48*K*V ^ 2 +
      351*K*V*ρ ^ 2 - 6453*K*V*ρ - 240*K*V - 16245*K*ρ ^ 2 - 849*K*ρ - 2616*K - 13122*V ^ 2*ρ ^ 2 +
      8262*V ^ 2*ρ - 144*V ^ 2 + 19683*V*ρ ^ 2 + 3159*V*ρ + 1368*V + 13122*ρ ^ 2 - 486*ρ +
      3312)/(72*K*ρ*(3*K ^ 2*ρ - K ^ 2 - 9*K*V*ρ + 3*K*V - 9*K*ρ + 3*K + 6*V ^ 2*ρ - 2*V ^ 2 +
      15*V*ρ - 5*V + 6*ρ - 2)),
    0,
    -1]

/-- Four interface columns specialized to the encoded Neary instance. -/
def input (β : Nat) (body : List TagLetter) : Matrix (Fin 9) (Fin 4) ℚ :=
  chainInput (widthScale β) (ChangedSeparatorTail.lowerCCode β body)
    (ChangedSeparatorTail.lowerCScale β body)

/-- Four interface rows specialized to the encoded Neary instance. -/
def output (β : Nat) (body : List TagLetter) : Matrix (Fin 4) (Fin 9) ℚ :=
  chainOutput (widthScale β) (ChangedSeparatorTail.lowerCCode β body)
    (ChangedSeparatorTail.lowerCScale β body)

/-- The rank-four physical cut. -/
def cut (β : Nat) (body : List TagLetter) : Square (Fin 9) ℚ :=
  input β body * output β body

/-- The rational two-generator candidate. -/
def generator (β : Nat) (body : List TagLetter) : Option Unit → Square (Fin 9) ℚ :=
  ReturnFamily.pairGenerator (transition β body) (cut β body)

/-- Canonical integer numerator pair. -/
def integralGenerator (β : Nat) (body : List TagLetter) : Option Unit → Square (Fin 9) ℤ :=
  clearRationalFamily (generator β body)

end ChangedSeparatorRealization

end MatrixMortality
