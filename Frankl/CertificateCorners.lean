import Frankl.CertificateObjective

namespace Frankl

open Finset Real Set

namespace CertificateCorner

private noncomputable def betaMaximum : ℝ := 2 * abundanceTarget

private noncomputable def betaMinimum : ℝ :=
  2 * (abundanceTarget - 1 / 1000) / (1 - 1 / 1000)

private noncomputable def lowWeightMinimum : ℝ := 1 - betaMaximum

private noncomputable def lowWeightMaximum : ℝ := 1 - betaMinimum

private noncomputable def meanEntropyCoefficient : ℝ :=
  lowWeightMinimum *
    ((9 / 5 - 1) * ((1 - dependentShare) * lowWeightMinimum + dependentShare) -
      entropySlack)

private noncomputable def endpointEntropyCoefficient : ℝ :=
  betaMinimum / 2 *
    ((1 - dependentShare) *
      (2 * lowWeightMinimum + 9 / 5 * betaMinimum / 2) - (1 + entropySlack))

private noncomputable def ternaryEntropyError : ℝ :=
  (1 - dependentShare) * betaMaximum * lowWeightMaximum

/-- A lower logarithm bound used only at the entropy-zero corners. -/
theorem log_thousand_gt : (69 : ℝ) / 10 < log 1000 := by
  have hratio := one_sub_inv_le_log_of_pos (x := (125 : ℝ) / 128) (by norm_num)
  have htwo : (6931471803 : ℝ) / 10000000000 < log 2 := by
    rw [show (6931471803 : ℝ) / 10000000000 = 0.6931471803 by norm_num]
    exact log_two_gt_d9
  have hidentity : log 1000 = 10 * log 2 + log ((125 : ℝ) / 128) := by
    rw [show (1000 : ℝ) = 2 ^ 10 * ((125 : ℝ) / 128) by norm_num,
      log_mul (pow_ne_zero 10 (by norm_num)) (by norm_num), log_pow]
    norm_num
  rw [hidentity]
  norm_num at hratio
  nlinarith

/-- A coarse upper logarithm bound used in the three-state entropy estimate. -/
theorem log_three_lt : log 3 < (11 : ℝ) / 10 := by
  rw [log_lt_iff_lt_exp (by norm_num)]
  have htenth := quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 / 10 by norm_num)
  have hone : (27182818283 : ℝ) / 10000000000 < exp 1 := by
    rw [show (27182818283 : ℝ) / 10000000000 = 2.7182818283 by norm_num]
    exact exp_one_gt_d9
  calc
    (3 : ℝ) < (27182818283 / 10000000000) * (1 + 1 / 10 + (1 / 10) ^ 2 / 2) :=
      by norm_num
    _ < exp 1 * (1 + 1 / 10 + (1 / 10) ^ 2 / 2) := by
      gcongr
    _ ≤ exp 1 * exp (1 / 10) := by
      gcongr
    _ = exp (11 / 10) := by rw [← exp_add]; congr 1; norm_num

theorem log_two_lt_seven_tenths : log 2 < (7 : ℝ) / 10 := by
  have htwo : log 2 < (6931471808 : ℝ) / 10000000000 := by
    rw [show (6931471808 : ℝ) / 10000000000 = 0.6931471808 by norm_num]
    exact log_two_lt_d9
  norm_num at htwo ⊢
  linarith

/-- The complement contribution to binary entropy is at most its missing mass. -/
theorem binEntropy_le_log_envelope {x : ℝ} (hx₁ : x < 1) :
    binEntropy x ≤ x * (log x⁻¹ + 1) := by
  have hcomplementPos : 0 < 1 - x := sub_pos.2 hx₁
  have hlog := log_le_sub_one_of_pos (inv_pos.2 hcomplementPos)
  have hscaled := mul_le_mul_of_nonneg_left hlog hcomplementPos.le
  rw [binEntropy]
  calc
    x * log x⁻¹ + (1 - x) * log (1 - x)⁻¹ ≤
        x * log x⁻¹ + (1 - x) * ((1 - x)⁻¹ - 1) := by gcongr
    _ = x * (log x⁻¹ + 1) := by
      rw [mul_sub, mul_inv_cancel₀ hcomplementPos.ne']
      ring

/-- The complement contribution to binary entropy dominates its quadratic chord. -/
theorem log_envelope_le_binEntropy {x : ℝ} (hx₁ : x < 1) :
    x * (log x⁻¹ + 1 - x) ≤ binEntropy x := by
  have hcomplementPos : 0 < 1 - x := sub_pos.2 hx₁
  have hlog := one_sub_inv_le_log_of_pos (inv_pos.2 hcomplementPos)
  have hlog' : x ≤ log (1 - x)⁻¹ := by simpa using hlog
  rw [binEntropy]
  calc
    x * (log x⁻¹ + 1 - x) =
        x * log x⁻¹ + (1 - x) * x := by ring
    _ ≤ x * log x⁻¹ + (1 - x) * log (1 - x)⁻¹ := by
      gcongr

/-- Binary entropy dominates the linear-log term throughout the corner interval. -/
theorem corner_linear_entropy_lower {x : ℝ} (hx₀ : 0 ≤ x) (hxδ : x ≤ 1 / 1000) :
    (69 : ℝ) / 10 * x ≤ binEntropy x := by
  rcases hx₀.eq_or_lt with rfl | hxPos
  · simp
  have hinverse : (1000 : ℝ) ≤ x⁻¹ := by
    have := one_div_le_one_div_of_le hxPos hxδ
    norm_num at this ⊢
    exact this
  have hlog := log_le_log (by norm_num : (0 : ℝ) < 1000) hinverse
  have hlogLower : (69 : ℝ) / 10 < log x⁻¹ := log_thousand_gt.trans_le hlog
  have hcomplement : 0 ≤ negMulLog (1 - x) := by
    apply negMulLog_nonneg
    · linarith
    · linarith
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub, negMulLog]
  have hleft : (69 : ℝ) / 10 * x ≤ -x * log x := by
    rw [show log x = -log x⁻¹ by rw [log_inv, neg_neg]]
    nlinarith
  linarith

private theorem endpointWeight_zero_corner_bounds {a q : ℝ}
    (ha₀ : 0 ≤ a) (haδ : a ≤ 1 / 1000) (hq₀ : 0 ≤ q) (hqδ : q ≤ 1 / 1000) :
    0 ≤ endpointCertificateWeight a q ∧
      betaMinimum ≤ endpointCertificateWeight a q ∧
      endpointCertificateWeight a q ≤ betaMaximum := by
  have hdenominator : 0 < 1 + q - 2 * a := by nlinarith
  unfold endpointCertificateWeight
  constructor
  · exact div_nonneg (by norm_num [abundanceTarget]; linarith) hdenominator.le
  constructor
  · apply (le_div_iff₀ hdenominator).2
    norm_num [betaMinimum, abundanceTarget]
    nlinarith
  · apply (div_le_iff₀ hdenominator).2
    norm_num [betaMaximum, abundanceTarget]
    nlinarith

private theorem zero_corner_coefficient_bounds {beta lowWeight : ℝ}
    (hbeta₀ : 0 ≤ beta) (hbetaMinimum : betaMinimum ≤ beta)
    (hbetaMaximum : beta ≤ betaMaximum) (hlowWeight : lowWeight = 1 - beta) :
    meanEntropyCoefficient ≤
        lowWeight *
          ((9 / 5 - 1) * ((1 - dependentShare) * lowWeight + dependentShare) -
            entropySlack) ∧
      endpointEntropyCoefficient ≤
        beta / 2 *
          ((1 - dependentShare) * (2 * lowWeight + 9 / 5 * beta / 2) -
            (1 + entropySlack)) ∧
      (1 - dependentShare) * lowWeight * beta ≤ ternaryEntropyError := by
  have hlowMinimum₀ : 0 ≤ lowWeightMinimum := by
    norm_num [lowWeightMinimum, betaMaximum, abundanceTarget]
  have hlowMaximum₀ : 0 ≤ lowWeightMaximum := by
    norm_num [lowWeightMaximum, betaMinimum, abundanceTarget]
  have hlowBounds : lowWeightMinimum ≤ lowWeight ∧ lowWeight ≤ lowWeightMaximum := by
    subst lowWeight
    constructor <;> dsimp [lowWeightMinimum, lowWeightMaximum] <;> linarith
  have hlowWeight₀ : 0 ≤ lowWeight := hlowMinimum₀.trans hlowBounds.1
  have hmeanInner :
      (9 / 5 - 1) *
          ((1 - dependentShare) * lowWeightMinimum + dependentShare) - entropySlack ≤
        (9 / 5 - 1) *
          ((1 - dependentShare) * lowWeight + dependentShare) - entropySlack := by
    have hshare : (0 : ℝ) ≤ 1 - dependentShare := by norm_num [dependentShare]
    nlinarith
  have hmeanInner₀ :
      0 ≤ (9 / 5 - 1) *
          ((1 - dependentShare) * lowWeightMinimum + dependentShare) - entropySlack := by
    norm_num [dependentShare, entropySlack, lowWeightMinimum, betaMaximum,
      abundanceTarget]
  have hmean : meanEntropyCoefficient ≤
      lowWeight *
        ((9 / 5 - 1) * ((1 - dependentShare) * lowWeight + dependentShare) -
          entropySlack) := by
    dsimp [meanEntropyCoefficient]
    exact mul_le_mul hlowBounds.1 hmeanInner hmeanInner₀ hlowWeight₀
  have hendpointInner :
      (1 - dependentShare) *
          (2 * lowWeightMinimum + 9 / 5 * betaMinimum / 2) -
            (1 + entropySlack) ≤
        (1 - dependentShare) * (2 * lowWeight + 9 / 5 * beta / 2) -
          (1 + entropySlack) := by
    have hshare : (0 : ℝ) ≤ 1 - dependentShare := by norm_num [dependentShare]
    nlinarith
  have hendpointInner₀ :
      0 ≤ (1 - dependentShare) *
          (2 * lowWeightMinimum + 9 / 5 * betaMinimum / 2) -
            (1 + entropySlack) := by
    norm_num [dependentShare, entropySlack, lowWeightMinimum, betaMaximum, betaMinimum,
      abundanceTarget]
  have hendpoint : endpointEntropyCoefficient ≤
      beta / 2 *
        ((1 - dependentShare) * (2 * lowWeight + 9 / 5 * beta / 2) -
          (1 + entropySlack)) := by
    dsimp [endpointEntropyCoefficient]
    exact mul_le_mul (by linarith) hendpointInner hendpointInner₀ (by positivity)
  have hweightProduct : lowWeight * beta ≤ lowWeightMaximum * betaMaximum :=
    mul_le_mul hlowBounds.2 hbetaMaximum hbeta₀ hlowMaximum₀
  have herror :
      (1 - dependentShare) * lowWeight * beta ≤ ternaryEntropyError := by
    dsimp [ternaryEntropyError]
    have hshare : (0 : ℝ) ≤ 1 - dependentShare := by norm_num [dependentShare]
    nlinarith
  exact ⟨hmean, hendpoint, herror⟩

private theorem log_inv_add_one_lower {x : ℝ} (hx₀ : 0 < x) (hxδ : x ≤ 1 / 1000) :
    (79 : ℝ) / 10 < log x⁻¹ + 1 := by
  have hinverse : (1000 : ℝ) ≤ x⁻¹ := by
    have := one_div_le_one_div_of_le hx₀ hxδ
    norm_num at this ⊢
    exact this
  have hlog := log_le_log (by norm_num : (0 : ℝ) < 1000) hinverse
  nlinarith [log_thousand_gt]

/-- On the corner interval, any near-doubling amplifies binary entropy by `9/5`. -/
theorem binEntropy_near_double {x y : ℝ} (hx₀ : 0 ≤ x) (hxδ : x ≤ 1 / 1000)
    (hyLower : (1999 : ℝ) / 1000 * x ≤ y) (hyUpper : y ≤ 2 * x) :
    (9 : ℝ) / 5 * binEntropy x ≤ binEntropy y := by
  rcases hx₀.eq_or_lt with rfl | hxPos
  · have hy : y = 0 := by linarith
    simp [hy]
  have hyPos : 0 < y := lt_of_lt_of_le (mul_pos (by norm_num) hxPos) hyLower
  have hxOne : x < 1 := hxδ.trans_lt (by norm_num)
  have hyOne : y < 1 := hyUpper.trans_lt (by nlinarith)
  have hxEnvelope := binEntropy_le_log_envelope hxOne
  have hyEnvelope := log_envelope_le_binEntropy hyOne
  have hinverse : (2 * x)⁻¹ ≤ y⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hyPos hyUpper
  have hlogInverse := log_le_log (inv_pos.2 (mul_pos (by norm_num) hxPos)) hinverse
  have hlogProduct : log x⁻¹ - log 2 ≤ log y⁻¹ := by
    have hidentity : log (2 * x)⁻¹ = log x⁻¹ - log 2 := by
      have htwoInverse : log (2 : ℝ)⁻¹ = -log 2 := log_inv 2
      rw [mul_inv_rev, log_mul (inv_ne_zero hxPos.ne') (by norm_num), htwoInverse]
      ring
    rw [← hidentity]
    exact hlogInverse
  have hlogScaled := mul_le_mul_of_nonneg_left hlogProduct hyPos.le
  have hleading :
      (1999 / 1000 * x) * (log x⁻¹ + 1) ≤ y * (log x⁻¹ + 1) := by
    have hnonnegative : 0 ≤ log x⁻¹ + 1 := by
      linarith [log_inv_add_one_lower hxPos hxδ]
    exact mul_le_mul_of_nonneg_right hyLower hnonnegative
  have hlogTwoNonnegative : 0 ≤ log 2 := log_nonneg (by norm_num)
  have hlogTwoScaled : y * log 2 ≤ (7 : ℝ) / 5 * x := by
    calc
      y * log 2 ≤ (2 * x) * log 2 :=
        mul_le_mul_of_nonneg_right hyUpper hlogTwoNonnegative
      _ ≤ (2 * x) * (7 / 10) := by
        gcongr
        exact log_two_lt_seven_tenths.le
      _ = (7 : ℝ) / 5 * x := by ring
  have hySquare : y ^ 2 ≤ 4 * x ^ 2 := by nlinarith
  have hxSquare : x ^ 2 ≤ x / 1000 := by nlinarith
  have hmargin := log_inv_add_one_lower hxPos hxδ
  nlinarith

theorem binEntropy_two_mul {x : ℝ} (hx₀ : 0 ≤ x) (hxδ : x ≤ 1 / 1000) :
    (9 : ℝ) / 5 * binEntropy x ≤ binEntropy (2 * x) := by
  apply binEntropy_near_double hx₀ hxδ
  · nlinarith
  · rfl

theorem binEntropy_self_union {x : ℝ} (hx₀ : 0 ≤ x) (hxδ : x ≤ 1 / 1000) :
    (9 : ℝ) / 5 * binEntropy x ≤ binEntropy (2 * x - x ^ 2) := by
  apply binEntropy_near_double hx₀ hxδ
  · nlinarith [mul_nonneg hx₀ hx₀]
  · nlinarith [mul_nonneg hx₀ hx₀]

/-- Entropy of three nonnegative masses is maximized by their equalization. -/
private theorem three_negMulLog_le {p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    negMulLog p + negMulLog q + negMulLog r ≤
      3 * negMulLog ((p + q + r) / 3) := by
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hthird : (0 : ℝ) ≤ 1 / 3 := by norm_num
  have htwoThirds : (0 : ℝ) ≤ 2 / 3 := by norm_num
  have hpair := concaveOn_negMulLog.2 hp hq hhalf hhalf (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hmidNonnegative : 0 ≤ (p + q) / 2 := by positivity
  have htriple := concaveOn_negMulLog.2 hmidNonnegative hr htwoThirds hthird
    (by norm_num : (2 / 3 : ℝ) + 1 / 3 = 1)
  dsimp only [smul_eq_mul] at hpair htriple
  have hmid : (1 / 2 : ℝ) * p + 1 / 2 * q = (p + q) / 2 := by ring
  rw [hmid] at hpair
  have hmean : (2 / 3 : ℝ) * ((p + q) / 2) + 1 / 3 * r =
      (p + q + r) / 3 := by ring
  rw [hmean] at htriple
  linarith

private theorem three_negMulLog_mean_identity (u : ℝ) :
    3 * negMulLog (u / 3) = negMulLog u + u * log 3 := by
  rw [show u / 3 = u * (1 / 3 : ℝ) by ring, negMulLog_mul]
  have hlogThird : log (1 / 3 : ℝ) = -log 3 := by
    rw [one_div, log_inv]
  simp only [negMulLog]
  rw [hlogThird]
  ring

/-- The entropy of an independent Bernoulli OR loses at most one ternary symbol on its
nonzero fiber. -/
theorem binEntropy_join_lower {a q : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1)
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    binEntropy a + binEntropy q - join a q * log 3 ≤ binEntropy (join a q) := by
  let left := a * (1 - q)
  let right := (1 - a) * q
  let both := a * q
  let occupied := join a q
  have hleft : 0 ≤ left := mul_nonneg ha₀ (sub_nonneg.2 hq₁)
  have hright : 0 ≤ right := mul_nonneg (sub_nonneg.2 ha₁) hq₀
  have hboth : 0 ≤ both := mul_nonneg ha₀ hq₀
  have hsum : left + right + both = occupied := by
    dsimp [left, right, both, occupied, join]
    ring
  have hthree := three_negMulLog_le hleft hright hboth
  rw [hsum, three_negMulLog_mean_identity] at hthree
  have hindependent :
      binEntropy a + binEntropy q =
        negMulLog ((1 - a) * (1 - q)) + negMulLog left +
          negMulLog right + negMulLog both := by
    rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub,
      binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    rw [negMulLog_mul, negMulLog_mul, negMulLog_mul, negMulLog_mul]
    ring
  have hcomplement : (1 - a) * (1 - q) = 1 - occupied := by
    dsimp [occupied, join]
    ring
  rw [hindependent, hcomplement]
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  dsimp only [occupied]
  linarith

/-- Concavity along the chord from zero. -/
theorem one_sub_mul_binEntropy_le {a r : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1)
    (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    (1 - a) * binEntropy r ≤ binEntropy (r * (1 - a)) := by
  have hzero : (0 : ℝ) ∈ Set.Icc 0 1 := by norm_num
  have hr : r ∈ Set.Icc (0 : ℝ) 1 := ⟨hr₀, hr₁⟩
  have hweight₀ : 0 ≤ a := ha₀
  have hweight₁ : 0 ≤ 1 - a := sub_nonneg.2 ha₁
  have hsum : a + (1 - a) = (1 : ℝ) := by ring
  have hconcave := strictConcave_binEntropy.concaveOn.2 hzero hr hweight₀ hweight₁ hsum
  dsimp only [smul_eq_mul] at hconcave
  rw [show a * 0 + (1 - a) * r = r * (1 - a) by ring, binEntropy_zero,
    mul_zero, zero_add] at hconcave
  exact hconcave

private theorem diagonalEndpointObjective_zero_corner {a q beta lowWeight : ℝ}
    (ha₀ : 0 ≤ a) (haδ : a ≤ 1 / 1000) (hq₀ : 0 ≤ q) (hqδ : q ≤ 1 / 1000)
    (hbeta₀ : 0 ≤ beta) (hbetaMinimum : betaMinimum ≤ beta)
    (hbetaMaximum : beta ≤ betaMaximum) (hlowWeight : lowWeight = 1 - beta) :
    0 ≤ diagonalEndpointObjective lowWeight beta a q := by
  have ha₁ : a ≤ 1 := haδ.trans (by norm_num)
  have hq₁ : q ≤ 1 := hqδ.trans (by norm_num)
  have hlowMinimum₀ : 0 ≤ lowWeightMinimum := by
    norm_num [lowWeightMinimum, betaMaximum, abundanceTarget]
  have hlowWeightLower : lowWeightMinimum ≤ lowWeight := by
    subst lowWeight
    dsimp [lowWeightMinimum]
    linarith
  have hlowWeight₀ : 0 ≤ lowWeight := hlowMinimum₀.trans hlowWeightLower
  have haEntropy : 0 ≤ binEntropy a := binEntropy_nonneg ha₀ ha₁
  have hqEntropy : 0 ≤ binEntropy q := binEntropy_nonneg hq₀ hq₁
  have hselfA : (9 : ℝ) / 5 * binEntropy a ≤ binEntropy (join a a) := by
    convert binEntropy_self_union ha₀ haδ using 1
    dsimp [join]
    ring
  have hselfQ : (9 : ℝ) / 5 * binEntropy q ≤ binEntropy (join q q) := by
    convert binEntropy_self_union hq₀ hqδ using 1
    dsimp [join]
    ring
  have hdependent : dependentCost a a = binEntropy (2 * a) := by
    rw [dependentCost_self_eq_cappedEntropy (by linarith : a ≤ (1 : ℝ) / 2)]
    rw [min_eq_left (by linarith : 2 * a ≤ (1 : ℝ) / 2)]
  have hdependentLower :
      (9 : ℝ) / 5 * binEntropy a ≤ dependentCost a a := by
    rw [hdependent]
    exact binEntropy_two_mul ha₀ haδ
  have hjoinRaw := binEntropy_join_lower ha₀ ha₁ hq₀ hq₁
  have hjoinUpper : join a q ≤ a + q := by
    dsimp [join]
    nlinarith [mul_nonneg ha₀ hq₀]
  have hlogThree₀ : 0 ≤ log 3 := log_nonneg (by norm_num)
  have hjoinError : join a q * log 3 ≤ (a + q) * log 3 :=
    mul_le_mul_of_nonneg_right hjoinUpper hlogThree₀
  have hjoin :
      binEntropy a + binEntropy q - (a + q) * log 3 ≤ binEntropy (join a q) := by
    linarith
  have hfirstCoefficient : 0 ≤ lowWeight ^ 2 := sq_nonneg lowWeight
  have hcrossCoefficient : 0 ≤ lowWeight * beta := mul_nonneg hlowWeight₀ hbeta₀
  have hlastCoefficient : 0 ≤ beta ^ 2 / 4 := by positivity
  have hfirst := mul_le_mul_of_nonneg_left hselfA hfirstCoefficient
  have hcross := mul_le_mul_of_nonneg_left hjoin hcrossCoefficient
  have hlast := mul_le_mul_of_nonneg_left hselfQ hlastCoefficient
  have hindependent :
      lowWeight ^ 2 * ((9 : ℝ) / 5 * binEntropy a) +
          lowWeight * beta *
            (binEntropy a + binEntropy q - (a + q) * log 3) +
          beta ^ 2 / 4 * ((9 : ℝ) / 5 * binEntropy q) ≤
        lowWeight ^ 2 * binEntropy (join a a) +
          lowWeight * beta * binEntropy (join a q) +
          beta ^ 2 / 4 * binEntropy (join q q) := by
    linarith
  have hdependentScaled := mul_le_mul_of_nonneg_left hdependentLower hlowWeight₀
  have hindependentShare : 0 ≤ 1 - dependentShare := by norm_num [dependentShare]
  have hdependentShare : 0 ≤ dependentShare := by norm_num [dependentShare]
  have hindependentScaled :=
    mul_le_mul_of_nonneg_left hindependent hindependentShare
  have hdependentShareScaled :=
    mul_le_mul_of_nonneg_left hdependentScaled hdependentShare
  let reducedGap :=
    (1 - dependentShare) *
        (lowWeight ^ 2 * ((9 : ℝ) / 5 * binEntropy a) +
          lowWeight * beta *
            (binEntropy a + binEntropy q - (a + q) * log 3) +
          beta ^ 2 / 4 * ((9 : ℝ) / 5 * binEntropy q)) +
      dependentShare * (lowWeight * ((9 : ℝ) / 5 * binEntropy a)) -
      (1 + entropySlack) *
        (lowWeight * binEntropy a + beta / 2 * binEntropy q)
  have hgap : reducedGap ≤ diagonalEndpointObjective lowWeight beta a q := by
    unfold diagonalEndpointObjective yuGap
    dsimp only [reducedGap]
    linarith
  let meanCoefficient :=
    lowWeight *
      ((9 / 5 - 1) * ((1 - dependentShare) * lowWeight + dependentShare) -
        entropySlack)
  let endpointCoefficient :=
    beta / 2 *
      ((1 - dependentShare) * (2 * lowWeight + 9 / 5 * beta / 2) -
        (1 + entropySlack))
  let errorCoefficient := (1 - dependentShare) * lowWeight * beta
  have hreducedIdentity :
      reducedGap = meanCoefficient * binEntropy a + endpointCoefficient * binEntropy q -
        errorCoefficient * (a + q) * log 3 := by
    dsimp only [reducedGap, meanCoefficient, endpointCoefficient, errorCoefficient]
    rw [hlowWeight]
    ring
  have hcoefficients := zero_corner_coefficient_bounds hbeta₀ hbetaMinimum hbetaMaximum
    hlowWeight
  have hmeanCoefficient : meanEntropyCoefficient ≤ meanCoefficient := by
    exact hcoefficients.1
  have hendpointCoefficient : endpointEntropyCoefficient ≤ endpointCoefficient := by
    exact hcoefficients.2.1
  have herrorCoefficient : errorCoefficient ≤ ternaryEntropyError := by
    exact hcoefficients.2.2
  have hmean₀ : 0 ≤ meanEntropyCoefficient := by
    norm_num [meanEntropyCoefficient, lowWeightMinimum, betaMaximum, dependentShare,
      entropySlack, abundanceTarget]
  have hendpoint₀ : 0 ≤ endpointEntropyCoefficient := by
    norm_num [endpointEntropyCoefficient, betaMinimum, lowWeightMinimum, betaMaximum,
      dependentShare, entropySlack, abundanceTarget]
  have herror₀ : 0 ≤ ternaryEntropyError := by
    norm_num [ternaryEntropyError, betaMaximum, lowWeightMaximum, betaMinimum,
      dependentShare, abundanceTarget]
  have hmeanEntropy := mul_le_mul_of_nonneg_right hmeanCoefficient haEntropy
  have hendpointEntropy := mul_le_mul_of_nonneg_right hendpointCoefficient hqEntropy
  have herrorArgument₀ : 0 ≤ (a + q) * log 3 := mul_nonneg (by linarith) hlogThree₀
  have herrorEntropy := mul_le_mul_of_nonneg_right herrorCoefficient herrorArgument₀
  have hcoefficientReduction :
      meanEntropyCoefficient * binEntropy a + endpointEntropyCoefficient * binEntropy q -
          ternaryEntropyError * (a + q) * log 3 ≤
        meanCoefficient * binEntropy a + endpointCoefficient * binEntropy q -
          errorCoefficient * (a + q) * log 3 := by
    have hpositiveTerms := add_le_add hmeanEntropy hendpointEntropy
    calc
      meanEntropyCoefficient * binEntropy a + endpointEntropyCoefficient * binEntropy q -
          ternaryEntropyError * (a + q) * log 3 =
        (meanEntropyCoefficient * binEntropy a +
            endpointEntropyCoefficient * binEntropy q) -
          ternaryEntropyError * ((a + q) * log 3) := by ring
      _ ≤ (meanCoefficient * binEntropy a + endpointCoefficient * binEntropy q) -
          ternaryEntropyError * ((a + q) * log 3) :=
        sub_le_sub_right hpositiveTerms _
      _ ≤ (meanCoefficient * binEntropy a + endpointCoefficient * binEntropy q) -
          errorCoefficient * ((a + q) * log 3) :=
        sub_le_sub_left herrorEntropy _
      _ = meanCoefficient * binEntropy a + endpointCoefficient * binEntropy q -
          errorCoefficient * (a + q) * log 3 := by ring
  have haLinear := corner_linear_entropy_lower ha₀ haδ
  have hqLinear := corner_linear_entropy_lower hq₀ hqδ
  have hmeanLinear := mul_le_mul_of_nonneg_left haLinear hmean₀
  have hendpointLinear := mul_le_mul_of_nonneg_left hqLinear hendpoint₀
  have hlogError :
      ternaryEntropyError * (a + q) * log 3 ≤
        ternaryEntropyError * (a + q) * ((11 : ℝ) / 10) := by
    gcongr
    exact log_three_lt.le
  have hmeanMargin :
      (11 : ℝ) / 10 * ternaryEntropyError <
        (69 : ℝ) / 10 * meanEntropyCoefficient := by
    norm_num [ternaryEntropyError, betaMaximum, lowWeightMaximum, betaMinimum,
      meanEntropyCoefficient, lowWeightMinimum, dependentShare, entropySlack,
      abundanceTarget]
  have hendpointMargin :
      (11 : ℝ) / 10 * ternaryEntropyError <
        (69 : ℝ) / 10 * endpointEntropyCoefficient := by
    norm_num [ternaryEntropyError, betaMaximum, lowWeightMaximum, betaMinimum,
      endpointEntropyCoefficient, lowWeightMinimum, dependentShare, entropySlack,
      abundanceTarget]
  have hmeanMarginScaled := mul_le_mul_of_nonneg_right hmeanMargin.le ha₀
  have hendpointMarginScaled := mul_le_mul_of_nonneg_right hendpointMargin.le hq₀
  have hlinearMargin :
      ternaryEntropyError * (a + q) * ((11 : ℝ) / 10) ≤
        meanEntropyCoefficient * ((69 : ℝ) / 10 * a) +
          endpointEntropyCoefficient * ((69 : ℝ) / 10 * q) := by
    calc
      ternaryEntropyError * (a + q) * ((11 : ℝ) / 10) =
          ((11 : ℝ) / 10 * ternaryEntropyError) * a +
            ((11 : ℝ) / 10 * ternaryEntropyError) * q := by ring
      _ ≤ ((69 : ℝ) / 10 * meanEntropyCoefficient) * a +
          ((69 : ℝ) / 10 * endpointEntropyCoefficient) * q :=
        add_le_add hmeanMarginScaled hendpointMarginScaled
      _ = meanEntropyCoefficient * ((69 : ℝ) / 10 * a) +
          endpointEntropyCoefficient * ((69 : ℝ) / 10 * q) := by ring
  have hentropyMargin :
      ternaryEntropyError * (a + q) * log 3 ≤
        meanEntropyCoefficient * binEntropy a +
          endpointEntropyCoefficient * binEntropy q :=
    hlogError.trans (hlinearMargin.trans (add_le_add hmeanLinear hendpointLinear))
  have hpositive : 0 ≤
      meanEntropyCoefficient * binEntropy a + endpointEntropyCoefficient * binEntropy q -
        ternaryEntropyError * (a + q) * log 3 := by
    rw [sub_nonneg]
    exact hentropyMargin
  rw [hreducedIdentity] at hgap
  exact hpositive.trans (hcoefficientReduction.trans hgap)

theorem endpointCertificateObjective_zero_corner {a q : ℝ}
    (ha₀ : 0 ≤ a) (haδ : a ≤ 1 / 1000) (hq₀ : 0 ≤ q) (hqδ : q ≤ 1 / 1000) :
    0 ≤ endpointCertificateObjective a q := by
  have hbounds := endpointWeight_zero_corner_bounds ha₀ haδ hq₀ hqδ
  rw [endpointCertificateObjective]
  exact diagonalEndpointObjective_zero_corner ha₀ haδ hq₀ hqδ
    hbounds.1 hbounds.2.1 hbounds.2.2 rfl

private theorem diagonalEndpointObjective_one_corner {a r beta lowWeight : ℝ}
    (ha₀ : 0 ≤ a) (haδ : a ≤ 1 / 1000) (hr₀ : 0 ≤ r) (hrδ : r ≤ 1 / 1000)
    (hbeta₀ : 0 ≤ beta) (hbetaUpper : beta < 2 / 5)
    (hlowWeight : lowWeight = 1 - beta) :
    0 ≤ diagonalEndpointObjective lowWeight beta a (1 - r) := by
  have ha₁ : a ≤ 1 := haδ.trans (by norm_num)
  have hr₁ : r ≤ 1 := hrδ.trans (by norm_num)
  have hq₀ : 0 ≤ 1 - r := sub_nonneg.2 hr₁
  have hq₁ : 1 - r ≤ 1 := by linarith
  have hlowWeightLower : (3 : ℝ) / 5 < lowWeight := by
    rw [hlowWeight]
    linarith
  have hlowWeight₀ : 0 ≤ lowWeight := hlowWeightLower.le.trans' (by norm_num)
  have haEntropy : 0 ≤ binEntropy a := binEntropy_nonneg ha₀ ha₁
  have hrEntropy : 0 ≤ binEntropy r := binEntropy_nonneg hr₀ hr₁
  have hselfA : (9 : ℝ) / 5 * binEntropy a ≤ binEntropy (join a a) := by
    convert binEntropy_self_union ha₀ haδ using 1
    dsimp [join]
    ring
  have hjoinIdentity :
      binEntropy (join a (1 - r)) = binEntropy (r * (1 - a)) := by
    rw [show join a (1 - r) = 1 - r * (1 - a) by
      dsimp [join]
      ring, binEntropy_one_sub]
  have hjoin :
      (1 - a) * binEntropy r ≤ binEntropy (join a (1 - r)) := by
    rw [hjoinIdentity]
    exact one_sub_mul_binEntropy_le ha₀ ha₁ hr₀ hr₁
  have hselfQNonnegative : 0 ≤ binEntropy (join (1 - r) (1 - r)) := by
    have hjoinMem := join_mem_Icc ⟨hq₀, hq₁⟩ ⟨hq₀, hq₁⟩
    exact binEntropy_nonneg hjoinMem.1 hjoinMem.2
  have hdependent : dependentCost a a = binEntropy (2 * a) := by
    rw [dependentCost_self_eq_cappedEntropy (by linarith : a ≤ (1 : ℝ) / 2)]
    rw [min_eq_left (by linarith : 2 * a ≤ (1 : ℝ) / 2)]
  have hdependentLower :
      (9 : ℝ) / 5 * binEntropy a ≤ dependentCost a a := by
    rw [hdependent]
    exact binEntropy_two_mul ha₀ haδ
  have hfirst := mul_le_mul_of_nonneg_left hselfA (sq_nonneg lowWeight)
  have hcross := mul_le_mul_of_nonneg_left hjoin (mul_nonneg hlowWeight₀ hbeta₀)
  have hlast : 0 ≤ beta ^ 2 / 4 * binEntropy (join (1 - r) (1 - r)) :=
    mul_nonneg (by positivity) hselfQNonnegative
  have hindependent :
      lowWeight ^ 2 * ((9 : ℝ) / 5 * binEntropy a) +
          lowWeight * beta * ((1 - a) * binEntropy r) ≤
        lowWeight ^ 2 * binEntropy (join a a) +
          lowWeight * beta * binEntropy (join a (1 - r)) +
          beta ^ 2 / 4 * binEntropy (join (1 - r) (1 - r)) := by
    linarith
  have hdependentScaled := mul_le_mul_of_nonneg_left hdependentLower hlowWeight₀
  have hindependentScaled := mul_le_mul_of_nonneg_left hindependent
    (by norm_num [dependentShare] : 0 ≤ 1 - dependentShare)
  have hdependentShareScaled := mul_le_mul_of_nonneg_left hdependentScaled
    (by norm_num [dependentShare] : 0 ≤ dependentShare)
  have hqEntropy : binEntropy (1 - r) = binEntropy r := binEntropy_one_sub r
  let reducedGap :=
    (1 - dependentShare) *
        (lowWeight ^ 2 * ((9 : ℝ) / 5 * binEntropy a) +
          lowWeight * beta * ((1 - a) * binEntropy r)) +
      dependentShare * (lowWeight * ((9 : ℝ) / 5 * binEntropy a)) -
      (1 + entropySlack) *
        (lowWeight * binEntropy a + beta / 2 * binEntropy r)
  have hgap : reducedGap ≤ diagonalEndpointObjective lowWeight beta a (1 - r) := by
    unfold diagonalEndpointObjective yuGap
    rw [hqEntropy]
    dsimp only [reducedGap]
    linarith
  let meanCoefficient := lowWeight *
    ((1 - dependentShare) * (9 / 5 * lowWeight) + dependentShare * (9 / 5) -
      (1 + entropySlack))
  let endpointCoefficient := beta *
    ((1 - dependentShare) * lowWeight * (1 - a) - (1 + entropySlack) / 2)
  have hreducedIdentity :
      reducedGap = meanCoefficient * binEntropy a + endpointCoefficient * binEntropy r := by
    dsimp only [reducedGap, meanCoefficient, endpointCoefficient]
    ring
  have hmeanInner : 0 <
      (1 - dependentShare) * (9 / 5 * lowWeight) + dependentShare * (9 / 5) -
        (1 + entropySlack) := by
    norm_num [dependentShare, entropySlack] at hlowWeightLower ⊢
    nlinarith
  have hmeanCoefficient₀ : 0 ≤ meanCoefficient := by
    dsimp only [meanCoefficient]
    exact mul_nonneg hlowWeight₀ hmeanInner.le
  have hweightProduct : (3 : ℝ) / 5 * (1 - 1 / 1000) < lowWeight * (1 - a) := by
    calc
      (3 : ℝ) / 5 * (1 - 1 / 1000) < lowWeight * (1 - 1 / 1000) := by
        gcongr
      _ ≤ lowWeight * (1 - a) := by
        exact mul_le_mul_of_nonneg_left (by linarith) hlowWeight₀
  have hendpointInner : 0 <
      (1 - dependentShare) * lowWeight * (1 - a) - (1 + entropySlack) / 2 := by
    norm_num [dependentShare, entropySlack] at hweightProduct ⊢
    linarith
  have hendpointCoefficient₀ : 0 ≤ endpointCoefficient := by
    dsimp only [endpointCoefficient]
    exact mul_nonneg hbeta₀ hendpointInner.le
  rw [hreducedIdentity] at hgap
  have hreduced₀ : 0 ≤
      meanCoefficient * binEntropy a + endpointCoefficient * binEntropy r :=
    add_nonneg (mul_nonneg hmeanCoefficient₀ haEntropy)
      (mul_nonneg hendpointCoefficient₀ hrEntropy)
  exact hreduced₀.trans hgap

private theorem endpointWeight_one_corner_bounds {a q : ℝ}
    (ha₀ : 0 ≤ a) (haδ : a ≤ 1 / 1000)
    (hqLower : 1 - 1 / 1000 ≤ q) :
    0 ≤ endpointCertificateWeight a q ∧ endpointCertificateWeight a q < 2 / 5 := by
  have hdenominator : 0 < 1 + q - 2 * a := by nlinarith
  unfold endpointCertificateWeight
  constructor
  · exact div_nonneg (by norm_num [abundanceTarget]; linarith) hdenominator.le
  · apply (div_lt_iff hdenominator).2
    norm_num [abundanceTarget]
    nlinarith

theorem endpointCertificateObjective_one_corner {a q : ℝ}
    (ha₀ : 0 ≤ a) (haδ : a ≤ 1 / 1000)
    (hqLower : 1 - 1 / 1000 ≤ q) (hq₁ : q ≤ 1) :
    0 ≤ endpointCertificateObjective a q := by
  let r := 1 - q
  have hr₀ : 0 ≤ r := by dsimp [r]; linarith
  have hrδ : r ≤ 1 / 1000 := by dsimp [r]; linarith
  have hbounds := endpointWeight_one_corner_bounds ha₀ haδ hqLower
  have hqIdentity : q = 1 - r := by dsimp [r]; ring
  rw [hqIdentity] at hbounds ⊢
  rw [endpointCertificateObjective]
  exact diagonalEndpointObjective_one_corner ha₀ haδ hr₀ hrδ
    hbounds.1 hbounds.2 rfl

/-- Analytic discharge of the lower entropy-zero endpoint square. -/
theorem endpointExpression_zero_corner {a q : ℝ}
    (ha₀ : 0 ≤ a) (haCorner : a ≤ cornerWidth)
    (hq₀ : 0 ≤ q) (hqCorner : q ≤ cornerWidth) :
    0 ≤ CertificateObjective.endpointExpression.eval a q := by
  have haδ : a ≤ (1 : ℝ) / 1000 := by
    simpa [cornerWidth] using haCorner
  have hqδ : q ≤ (1 : ℝ) / 1000 := by
    simpa [cornerWidth] using hqCorner
  rw [CertificateObjective.endpointExpression_eval (by linarith : a ≤ (1 : ℝ) / 2)]
  exact endpointCertificateObjective_zero_corner ha₀ haδ hq₀ hqδ

/-- Analytic discharge of the upper entropy-zero endpoint square. -/
theorem endpointExpression_one_corner {a q : ℝ}
    (ha₀ : 0 ≤ a) (haCorner : a ≤ cornerWidth)
    (hqCorner : 1 - cornerWidth ≤ q) (hq₁ : q ≤ 1) :
    0 ≤ CertificateObjective.endpointExpression.eval a q := by
  have haδ : a ≤ (1 : ℝ) / 1000 := by
    simpa [cornerWidth] using haCorner
  have hqLower : (1 : ℝ) - 1 / 1000 ≤ q := by
    simpa [cornerWidth] using hqCorner
  rw [CertificateObjective.endpointExpression_eval (by linarith : a ≤ (1 : ℝ) / 2)]
  exact endpointCertificateObjective_one_corner ha₀ haδ hqLower hq₁

end CertificateCorner

end Frankl
