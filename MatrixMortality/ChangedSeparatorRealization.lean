import MatrixMortality.ChangedSeparatorTail
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

/-- Ternary width scale of the changed-separator chart. -/
def widthScale (β : Nat) : ℚ := 3 ^ β

/-- Common denominator of the changed-separator input/output chart. -/
def denominator (β : Nat) (body : List TagLetter) : ℚ :=
  ChangedSeparatorTail.transferDenominator β body

theorem widthScale_pos (β : Nat) : 0 < widthScale β := by
  simp [widthScale]

theorem denominator_lt_zero (β : Nat) (body : List TagLetter) :
    denominator β body < 0 :=
  ChangedSeparatorTail.transferDenominator_lt_zero β body

theorem denominator_ne_zero (β : Nat) (body : List TagLetter) :
    denominator β body ≠ 0 :=
  ne_of_lt (denominator_lt_zero β body)

/-- Eigenvalue carried by the one-dimensional safe tail. -/
def tailEigenvalue (β : Nat) (body : List TagLetter) : ℚ :=
  let ρ := widthScale β
  let V := ChangedSeparatorTail.lowerCCode β body
  let K := ChangedSeparatorTail.lowerCScale β body
  K * (3 * ρ - 1) * (K - 2 * V - 1) / denominator β body

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
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero lowerScale_ne_zero widthFactor_ne_zero) tailGap_ne_zero)
    (denominator_ne_zero β body)

/-- Two length-three nilpotent chains, one length-two chain, and the geometric tail line. -/
def transition (β : Nat) (body : List TagLetter) : Square (Fin 9) ℚ :=
  let s := tailEigenvalue β body
  !![0, 0, 0, 0, 0, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, s]

/-- Four interface columns in the exact three-parameter chain chart. -/
def chainInput (ρ V K : ℚ) : Matrix (Fin 9) (Fin 4) ℚ :=
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
def chainOutput (ρ V K : ℚ) : Matrix (Fin 4) (Fin 9) ℚ :=
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
