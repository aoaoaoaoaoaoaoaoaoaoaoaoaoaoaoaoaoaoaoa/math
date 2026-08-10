import Frankl.CanonicalObjective
import Frankl.CertificateTree

namespace Frankl

open Real Set

namespace CertificateObjective

/-- Exact expression for Yu's strict affine entropy gap. -/
def yuGap (independent marginal dependent : EntropyExpr) : EntropyExpr :=
  .sub
    (.add
      (.mul (.constant (193 / 200)) independent)
      (.mul (.constant (7 / 200)) dependent))
    (.mul (.constant (10000001 / 10000000)) marginal)

/-- Exact independent entropy of two diagonal atoms. -/
def diagonalIndependent
    (lowerWeight upperWeight lowerMean upperMean : EntropyExpr) : EntropyExpr :=
  .add
    (.add
      (.mul (.mul lowerWeight lowerWeight) (.entropy (.selfJoin lowerMean)))
      (.mul
        (.mul (.mul (.constant 2) upperWeight) lowerWeight)
        (.entropy (.join lowerMean upperMean))))
    (.mul (.mul upperWeight upperWeight) (.entropy (.selfJoin upperMean)))

/-- Exact marginal entropy of two diagonal atoms. -/
def diagonalMarginal
    (lowerWeight upperWeight lowerMean upperMean : EntropyExpr) : EntropyExpr :=
  .add
    (.mul lowerWeight (.entropy lowerMean))
    (.mul upperWeight (.entropy upperMean))

/-- Exact dependent entropy of two diagonal atoms below one half. -/
def diagonalDependent
    (lowerWeight upperWeight lowerMean upperMean : EntropyExpr) : EntropyExpr :=
  .add
    (.mul lowerWeight (.cappedEntropy lowerMean))
    (.mul upperWeight (.cappedEntropy upperMean))

/-- Exact Yu objective for two diagonal atoms below one half. -/
def diagonal
    (lowerWeight upperWeight lowerMean upperMean : EntropyExpr) : EntropyExpr :=
  yuGap
    (diagonalIndependent lowerWeight upperWeight lowerMean upperMean)
    (diagonalMarginal lowerWeight upperWeight lowerMean upperMean)
    (diagonalDependent lowerWeight upperWeight lowerMean upperMean)

/-- Exact independent entropy of a diagonal atom and the endpoint orbit `(q,1)`. -/
def endpointIndependent
    (lowerWeight upperWeight lowerMean q : EntropyExpr) : EntropyExpr :=
  .add
    (.add
      (.mul (.mul lowerWeight lowerWeight) (.entropy (.selfJoin lowerMean)))
      (.mul
        (.mul lowerWeight upperWeight)
        (.entropy (.join lowerMean q))))
    (.mul
      (.div (.mul upperWeight upperWeight) (.constant 4))
      (.entropy (.selfJoin q)))

/-- Exact marginal entropy of a diagonal atom and the endpoint orbit `(q,1)`. -/
def endpointMarginal
    (lowerWeight upperWeight lowerMean q : EntropyExpr) : EntropyExpr :=
  .add
    (.mul lowerWeight (.entropy lowerMean))
    (.mul (.div upperWeight (.constant 2)) (.entropy q))

/-- Exact Yu objective for a diagonal atom and an endpoint orbit. -/
def endpoint
    (lowerWeight upperWeight lowerMean q : EntropyExpr) : EntropyExpr :=
  yuGap
    (endpointIndependent lowerWeight upperWeight lowerMean q)
    (endpointMarginal lowerWeight upperWeight lowerMean q)
    (.mul lowerWeight (.cappedEntropy lowerMean))

/-- Endpoint-orbit mass in certificate coordinates. -/
def endpointUpperWeight : EntropyExpr :=
  .div
    (.mul (.constant 2) (.sub (.constant (76469 / 200000)) .horizontal))
    (.sub
      (.add (.constant 1) .vertical)
      (.mul (.constant 2) .horizontal))

/-- Reflected endpoint objective on coordinates `(a,q)`. -/
def endpointExpression : EntropyExpr :=
  endpoint (.sub (.constant 1) endpointUpperWeight) endpointUpperWeight
    .horizontal .vertical

/-- Lower diagonal mean on the region `w ≤ 2t`. -/
def lowerRegionLowerMeanExpression : EntropyExpr :=
  .sub
    (.constant (76469 / 200000))
    (.mul .horizontal
      (.div
        (.mul .vertical (.sub (.constant (1 / 2)) (.constant (76469 / 200000))))
        (.sub (.constant 1) .horizontal)))

/-- Upper diagonal mean on the region `w ≤ 2t`. -/
def lowerRegionUpperMeanExpression : EntropyExpr :=
  .add
    (.constant (76469 / 200000))
    (.mul .vertical (.sub (.constant (1 / 2)) (.constant (76469 / 200000))))

/-- Reflected diagonal objective on the region `w ≤ 2t`. -/
def lowerRegionExpression : EntropyExpr :=
  diagonal (.sub (.constant 1) .horizontal) .horizontal
    lowerRegionLowerMeanExpression lowerRegionUpperMeanExpression

/-- Lower diagonal mean on the region `2t ≤ w`. -/
def upperRegionLowerMeanExpression : EntropyExpr :=
  .mul (.constant (76469 / 200000)) (.sub (.constant 1) .vertical)

/-- Upper diagonal mean on the region `2t ≤ w`. -/
def upperRegionUpperMeanExpression : EntropyExpr :=
  .add
    (.constant (76469 / 200000))
    (.mul
      (.sub (.constant 1) .horizontal)
      (.div
        (.mul .vertical (.constant (76469 / 200000)))
        .horizontal))

/-- Reflected diagonal objective on the region `2t ≤ w`. -/
def upperRegionExpression : EntropyExpr :=
  diagonal (.sub (.constant 1) .horizontal) .horizontal
    upperRegionLowerMeanExpression upperRegionUpperMeanExpression

/-- The saturated centered endpoint objective after multiplication by the square of the
conditional complement. -/
def centeredCurveExpression : EntropyExpr :=
  yuGap
    (.mul
      (.constant ((123531 / 200000) ^ 2))
      (.entropy (.mul .horizontal .horizontal)))
    (.mul
      (.mul (.constant (123531 / 200000)) .horizontal)
      (.entropy .horizontal))
    (.mul
      (.sub
        (.mul (.constant (123531 / 100000)) .horizontal)
        (.mul .horizontal .horizontal))
      (.entropy (.constant (1 / 2))))

theorem constant_domain (value : ℚ) (x y : ℝ) :
    (EntropyExpr.constant value).DomainAt x y := by
  trivial

theorem add_domain {left right : EntropyExpr} {x y : ℝ}
    (hleft : left.DomainAt x y) (hright : right.DomainAt x y) :
    (EntropyExpr.add left right).DomainAt x y :=
  ⟨hleft, hright⟩

theorem neg_domain {body : EntropyExpr} {x y : ℝ}
    (hbody : body.DomainAt x y) :
    (EntropyExpr.neg body).DomainAt x y :=
  hbody

theorem mul_domain {left right : EntropyExpr} {x y : ℝ}
    (hleft : left.DomainAt x y) (hright : right.DomainAt x y) :
    (EntropyExpr.mul left right).DomainAt x y :=
  ⟨hleft, hright⟩

theorem inv_domain {body : EntropyExpr} {x y : ℝ}
    (hbody : body.DomainAt x y) (hpositive : 0 < body.eval x y) :
    (EntropyExpr.inv body).DomainAt x y :=
  ⟨hbody, hpositive⟩

theorem sub_domain {left right : EntropyExpr} {x y : ℝ}
    (hleft : left.DomainAt x y) (hright : right.DomainAt x y) :
    (left.sub right).DomainAt x y :=
  add_domain hleft (neg_domain hright)

theorem div_domain {left right : EntropyExpr} {x y : ℝ}
    (hleft : left.DomainAt x y) (hright : right.DomainAt x y)
    (hpositive : 0 < right.eval x y) :
    (left.div right).DomainAt x y :=
  mul_domain hleft (inv_domain hright hpositive)

theorem join_domain {left right : EntropyExpr} {x y : ℝ}
    (hleft : left.DomainAt x y) (hright : right.DomainAt x y) :
    (left.join right).DomainAt x y := by
  unfold EntropyExpr.join
  exact sub_domain (constant_domain 1 x y)
    (mul_domain (sub_domain (constant_domain 1 x y) hleft)
      (sub_domain (constant_domain 1 x y) hright))

theorem join_eval (left right : EntropyExpr) (x y : ℝ) :
    (left.join right).eval x y = Frankl.join (left.eval x y) (right.eval x y) := by
  simp [EntropyExpr.join, EntropyExpr.sub, EntropyExpr.eval, Frankl.join]
  ring

theorem selfJoin_domain {body : EntropyExpr} {x y : ℝ}
    (hbody : body.DomainAt x y) (hvalue : body.eval x y ∈ Icc (0 : ℝ) 1) :
    body.selfJoin.DomainAt x y :=
  ⟨hbody, hvalue⟩

theorem selfJoin_eval (body : EntropyExpr) (x y : ℝ) :
    body.selfJoin.eval x y = Frankl.join (body.eval x y) (body.eval x y) :=
  rfl

theorem entropy_domain {body : EntropyExpr} {x y : ℝ}
    (hbody : body.DomainAt x y) (hvalue : body.eval x y ∈ Icc (0 : ℝ) 1) :
    (EntropyExpr.entropy body).DomainAt x y :=
  ⟨hbody, hvalue⟩

theorem cappedEntropy_domain {body : EntropyExpr} {x y : ℝ}
    (hbody : body.DomainAt x y) (hvalue : body.eval x y ∈ Icc (0 : ℝ) (1 / 2)) :
    (EntropyExpr.cappedEntropy body).DomainAt x y :=
  ⟨hbody, hvalue⟩

theorem horizontal_domain (x y : ℝ) :
    EntropyExpr.horizontal.DomainAt x y := by
  trivial

theorem vertical_domain (x y : ℝ) :
    EntropyExpr.vertical.DomainAt x y := by
  trivial

theorem diagonal_domain {lowerWeight upperWeight lowerMean upperMean : EntropyExpr}
    {x y : ℝ}
    (hlowerWeight : lowerWeight.DomainAt x y)
    (hupperWeight : upperWeight.DomainAt x y)
    (hlowerMean : lowerMean.DomainAt x y)
    (hupperMean : upperMean.DomainAt x y)
    (hlowerValue : lowerMean.eval x y ∈ Icc (0 : ℝ) (1 / 2))
    (hupperValue : upperMean.eval x y ∈ Icc (0 : ℝ) (1 / 2)) :
    (diagonal lowerWeight upperWeight lowerMean upperMean).DomainAt x y := by
  have hlowerUnit : lowerMean.eval x y ∈ Icc (0 : ℝ) 1 :=
    ⟨hlowerValue.1, hlowerValue.2.trans (by norm_num)⟩
  have hupperUnit : upperMean.eval x y ∈ Icc (0 : ℝ) 1 :=
    ⟨hupperValue.1, hupperValue.2.trans (by norm_num)⟩
  have hjoinLower := Frankl.join_mem_Icc hlowerUnit hlowerUnit
  have hjoinCross := Frankl.join_mem_Icc hlowerUnit hupperUnit
  have hjoinUpper := Frankl.join_mem_Icc hupperUnit hupperUnit
  have hselfLower := entropy_domain (selfJoin_domain hlowerMean hlowerUnit)
    (selfJoin_eval lowerMean x y ▸ hjoinLower)
  have hcross := entropy_domain (join_domain hlowerMean hupperMean)
    (join_eval lowerMean upperMean x y ▸ hjoinCross)
  have hselfUpper := entropy_domain (selfJoin_domain hupperMean hupperUnit)
    (selfJoin_eval upperMean x y ▸ hjoinUpper)
  have hlowerEntropy := entropy_domain hlowerMean hlowerUnit
  have hupperEntropy := entropy_domain hupperMean hupperUnit
  have hlowerCapped := cappedEntropy_domain hlowerMean hlowerValue
  have hupperCapped := cappedEntropy_domain hupperMean hupperValue
  have hindependent :
      (diagonalIndependent lowerWeight upperWeight lowerMean upperMean).DomainAt x y :=
    add_domain
      (add_domain
        (mul_domain (mul_domain hlowerWeight hlowerWeight) hselfLower)
        (mul_domain
          (mul_domain (mul_domain (constant_domain 2 x y) hupperWeight) hlowerWeight)
          hcross))
      (mul_domain (mul_domain hupperWeight hupperWeight) hselfUpper)
  have hmarginal :
      (diagonalMarginal lowerWeight upperWeight lowerMean upperMean).DomainAt x y :=
    add_domain (mul_domain hlowerWeight hlowerEntropy)
      (mul_domain hupperWeight hupperEntropy)
  have hdependent :
      (diagonalDependent lowerWeight upperWeight lowerMean upperMean).DomainAt x y :=
    add_domain (mul_domain hlowerWeight hlowerCapped)
      (mul_domain hupperWeight hupperCapped)
  exact sub_domain
    (add_domain
      (mul_domain (constant_domain (193 / 200) x y) hindependent)
      (mul_domain (constant_domain (7 / 200) x y) hdependent))
    (mul_domain (constant_domain (10000001 / 10000000) x y) hmarginal)

theorem endpoint_domain {lowerWeight upperWeight lowerMean q : EntropyExpr}
    {x y : ℝ}
    (hlowerWeight : lowerWeight.DomainAt x y)
    (hupperWeight : upperWeight.DomainAt x y)
    (hlowerMean : lowerMean.DomainAt x y)
    (hq : q.DomainAt x y)
    (hlowerValue : lowerMean.eval x y ∈ Icc (0 : ℝ) (1 / 2))
    (hqValue : q.eval x y ∈ Icc (0 : ℝ) 1) :
    (endpoint lowerWeight upperWeight lowerMean q).DomainAt x y := by
  have hlowerUnit : lowerMean.eval x y ∈ Icc (0 : ℝ) 1 :=
    ⟨hlowerValue.1, hlowerValue.2.trans (by norm_num)⟩
  have hjoinLower := Frankl.join_mem_Icc hlowerUnit hlowerUnit
  have hjoinCross := Frankl.join_mem_Icc hlowerUnit hqValue
  have hjoinQ := Frankl.join_mem_Icc hqValue hqValue
  have hselfLower := entropy_domain (selfJoin_domain hlowerMean hlowerUnit)
    (selfJoin_eval lowerMean x y ▸ hjoinLower)
  have hcross := entropy_domain (join_domain hlowerMean hq)
    (join_eval lowerMean q x y ▸ hjoinCross)
  have hselfQ := entropy_domain (selfJoin_domain hq hqValue)
    (selfJoin_eval q x y ▸ hjoinQ)
  have hlowerEntropy := entropy_domain hlowerMean hlowerUnit
  have hqEntropy := entropy_domain hq hqValue
  have hlowerCapped := cappedEntropy_domain hlowerMean hlowerValue
  have hquarter : (EntropyExpr.constant 4).DomainAt x y :=
    constant_domain 4 x y
  have hquarterPositive : 0 < (EntropyExpr.constant 4).eval x y := by
    norm_num [EntropyExpr.eval]
  have hhalf : (EntropyExpr.constant 2).DomainAt x y :=
    constant_domain 2 x y
  have hhalfPositive : 0 < (EntropyExpr.constant 2).eval x y := by
    norm_num [EntropyExpr.eval]
  have hindependent :
      (endpointIndependent lowerWeight upperWeight lowerMean q).DomainAt x y :=
    add_domain
      (add_domain
        (mul_domain (mul_domain hlowerWeight hlowerWeight) hselfLower)
        (mul_domain (mul_domain hlowerWeight hupperWeight) hcross))
      (mul_domain
        (div_domain (mul_domain hupperWeight hupperWeight) hquarter hquarterPositive)
        hselfQ)
  have hmarginal :
      (endpointMarginal lowerWeight upperWeight lowerMean q).DomainAt x y :=
    add_domain (mul_domain hlowerWeight hlowerEntropy)
      (mul_domain (div_domain hupperWeight hhalf hhalfPositive) hqEntropy)
  have hdependent := mul_domain hlowerWeight hlowerCapped
  exact sub_domain
    (add_domain
      (mul_domain (constant_domain (193 / 200) x y) hindependent)
      (mul_domain (constant_domain (7 / 200) x y) hdependent))
    (mul_domain (constant_domain (10000001 / 10000000) x y) hmarginal)

theorem endpointUpperWeight_domain {a q : ℝ}
    (haUpper : a ≤ abundanceTarget) (hqLower : 0 ≤ q) :
    endpointUpperWeight.DomainAt a q := by
  have hdenominator : 0 < 1 + q - 2 * a := by
    have htargetHalf := abundanceTarget_lt_half
    linarith
  simpa [endpointUpperWeight, EntropyExpr.DomainAt, EntropyExpr.eval, EntropyExpr.sub,
    EntropyExpr.div] using hdenominator

theorem endpointExpression_domain {a q : ℝ}
    (haLower : 0 ≤ a) (haUpper : a ≤ abundanceTarget)
    (hqLower : 0 ≤ q) (hqUpper : q ≤ 1) :
    endpointExpression.DomainAt a q := by
  have hweight := endpointUpperWeight_domain haUpper hqLower
  have haHalf : a ≤ (1 : ℝ) / 2 := haUpper.trans abundanceTarget_lt_half.le
  exact endpoint_domain
    (sub_domain (constant_domain 1 a q) hweight)
    hweight
    (horizontal_domain a q)
    (vertical_domain a q)
    ⟨haLower, haHalf⟩
    ⟨hqLower, hqUpper⟩

theorem lowerRegionLowerMeanExpression_eval (upperWeight displacement : ℝ) :
    lowerRegionLowerMeanExpression.eval upperWeight displacement =
      lowerRegionLowerMean upperWeight displacement := by
  simp [lowerRegionLowerMeanExpression, lowerRegionLowerMean, EntropyExpr.eval,
    EntropyExpr.sub, EntropyExpr.div, abundanceTarget]
  ring

theorem lowerRegionUpperMeanExpression_eval (upperWeight displacement : ℝ) :
    lowerRegionUpperMeanExpression.eval upperWeight displacement =
      lowerRegionUpperMean displacement := by
  norm_num [lowerRegionUpperMeanExpression, lowerRegionUpperMean, EntropyExpr.eval,
    EntropyExpr.sub, abundanceTarget]

theorem lowerRegion_means_mem {upperWeight displacement : ℝ}
    (hweightLower : 0 ≤ upperWeight)
    (hweightUpper : upperWeight ≤ 2 * abundanceTarget)
    (hdisplacementLower : 0 ≤ displacement) (hdisplacementUpper : displacement ≤ 1) :
    lowerRegionLowerMean upperWeight displacement ∈ Icc (0 : ℝ) (1 / 2) ∧
      lowerRegionUpperMean displacement ∈ Icc (0 : ℝ) (1 / 2) := by
  have hdeltaLower : 0 ≤ (1 : ℝ) / 2 - abundanceTarget :=
    sub_nonneg.2 abundanceTarget_lt_half.le
  have hweightOne : upperWeight < 1 := by
    nlinarith [abundanceTarget_lt_half]
  have hdenominator : 0 < 1 - upperWeight := sub_pos.2 hweightOne
  have hproduct : 0 ≤ upperWeight * (1 - displacement) :=
    mul_nonneg hweightLower (sub_nonneg.2 hdisplacementUpper)
  have hweightedDisplacement : upperWeight * displacement ≤ upperWeight := by
    nlinarith
  have hscaled :
      upperWeight * displacement * (1 / 2 - abundanceTarget) ≤
        upperWeight * (1 / 2 - abundanceTarget) :=
    mul_le_mul_of_nonneg_right hweightedDisplacement hdeltaLower
  have hbudget :
      upperWeight * (1 / 2 - abundanceTarget) ≤
        abundanceTarget * (1 - upperWeight) := by
    nlinarith
  have hquotientLower :
      0 ≤ upperWeight * (displacement * (1 / 2 - abundanceTarget) /
        (1 - upperWeight)) :=
    mul_nonneg hweightLower (div_nonneg
      (mul_nonneg hdisplacementLower hdeltaLower) hdenominator.le)
  have hquotientUpper :
      upperWeight * (displacement * (1 / 2 - abundanceTarget) /
          (1 - upperWeight)) ≤ abundanceTarget := by
    rw [show upperWeight * (displacement * (1 / 2 - abundanceTarget) /
        (1 - upperWeight)) =
      (upperWeight * displacement * (1 / 2 - abundanceTarget)) /
        (1 - upperWeight) by ring]
    exact (div_le_iff₀ hdenominator).2 (hscaled.trans hbudget)
  constructor
  · dsimp [lowerRegionLowerMean]
    constructor <;> nlinarith [abundanceTarget_lt_half]
  · dsimp [lowerRegionUpperMean]
    constructor <;> nlinarith

theorem lowerRegionExpression_domain {upperWeight displacement : ℝ}
    (hweightLower : 0 ≤ upperWeight)
    (hweightUpper : upperWeight ≤ 2 * abundanceTarget)
    (hdisplacementLower : 0 ≤ displacement) (hdisplacementUpper : displacement ≤ 1) :
    lowerRegionExpression.DomainAt upperWeight displacement := by
  have hmeans := lowerRegion_means_mem hweightLower hweightUpper
    hdisplacementLower hdisplacementUpper
  have hweightOne : upperWeight < 1 := by
    nlinarith [abundanceTarget_lt_half]
  have hlowerMeanDomain :
      lowerRegionLowerMeanExpression.DomainAt upperWeight displacement := by
    simp [lowerRegionLowerMeanExpression, EntropyExpr.DomainAt, EntropyExpr.eval,
      EntropyExpr.sub, EntropyExpr.div]
    linarith
  have hupperMeanDomain :
      lowerRegionUpperMeanExpression.DomainAt upperWeight displacement := by
    simp [lowerRegionUpperMeanExpression, EntropyExpr.DomainAt, EntropyExpr.sub]
  apply diagonal_domain
    (sub_domain (constant_domain 1 upperWeight displacement)
      (horizontal_domain upperWeight displacement))
    (horizontal_domain upperWeight displacement)
    hlowerMeanDomain hupperMeanDomain
  · rw [lowerRegionLowerMeanExpression_eval]
    exact hmeans.1
  · rw [lowerRegionUpperMeanExpression_eval]
    exact hmeans.2

theorem upperRegionLowerMeanExpression_eval (upperWeight displacement : ℝ) :
    upperRegionLowerMeanExpression.eval upperWeight displacement =
      upperRegionLowerMean displacement := by
  simp [upperRegionLowerMeanExpression, upperRegionLowerMean, EntropyExpr.eval,
    EntropyExpr.sub, abundanceTarget]
  ring

theorem upperRegionUpperMeanExpression_eval (upperWeight displacement : ℝ) :
    upperRegionUpperMeanExpression.eval upperWeight displacement =
      upperRegionUpperMean upperWeight displacement := by
  simp [upperRegionUpperMeanExpression, upperRegionUpperMean, EntropyExpr.eval,
    EntropyExpr.sub, EntropyExpr.div, abundanceTarget]
  ring

theorem upperRegion_means_mem {upperWeight displacement : ℝ}
    (hweightLower : 2 * abundanceTarget ≤ upperWeight)
    (hweightUpper : upperWeight ≤ 1)
    (hdisplacementLower : 0 ≤ displacement) (hdisplacementUpper : displacement ≤ 1) :
    upperRegionLowerMean displacement ∈ Icc (0 : ℝ) (1 / 2) ∧
      upperRegionUpperMean upperWeight displacement ∈ Icc (0 : ℝ) (1 / 2) := by
  have htargetPositive : 0 < abundanceTarget := by
    norm_num [abundanceTarget]
  have hweightPositive : 0 < upperWeight := by
    nlinarith
  have honeMinusWeight : 0 ≤ 1 - upperWeight := sub_nonneg.2 hweightUpper
  have honeMinusDisplacement : 0 ≤ 1 - displacement :=
    sub_nonneg.2 hdisplacementUpper
  have hextraLower :
      0 ≤ (1 - upperWeight) *
        (displacement * abundanceTarget / upperWeight) :=
    mul_nonneg honeMinusWeight
      (div_nonneg (mul_nonneg hdisplacementLower htargetPositive.le) hweightPositive.le)
  have hproduct : 0 ≤ (1 - upperWeight) * (1 - displacement) :=
    mul_nonneg honeMinusWeight honeMinusDisplacement
  have hweightedDisplacement :
      (1 - upperWeight) * displacement ≤ 1 - upperWeight := by
    nlinarith
  have hbudget :
      (1 - upperWeight) * displacement * abundanceTarget ≤
        (1 / 2 - abundanceTarget) * upperWeight := by
    have hfirst :
        (1 - upperWeight) * displacement * abundanceTarget ≤
          (1 - upperWeight) * abundanceTarget :=
      mul_le_mul_of_nonneg_right hweightedDisplacement htargetPositive.le
    nlinarith
  have hextraUpper :
      (1 - upperWeight) *
          (displacement * abundanceTarget / upperWeight) ≤
        1 / 2 - abundanceTarget := by
    rw [show (1 - upperWeight) *
        (displacement * abundanceTarget / upperWeight) =
      ((1 - upperWeight) * displacement * abundanceTarget) / upperWeight by ring]
    exact (div_le_iff₀ hweightPositive).2 hbudget
  constructor
  · dsimp [upperRegionLowerMean]
    constructor
    · exact mul_nonneg htargetPositive.le honeMinusDisplacement
    · nlinarith [abundanceTarget_lt_half]
  · dsimp [upperRegionUpperMean]
    constructor <;> nlinarith

theorem upperRegionExpression_domain {upperWeight displacement : ℝ}
    (hweightLower : 2 * abundanceTarget ≤ upperWeight)
    (hweightUpper : upperWeight ≤ 1)
    (hdisplacementLower : 0 ≤ displacement) (hdisplacementUpper : displacement ≤ 1) :
    upperRegionExpression.DomainAt upperWeight displacement := by
  have hmeans := upperRegion_means_mem hweightLower hweightUpper
    hdisplacementLower hdisplacementUpper
  have hweightPositive : 0 < upperWeight := by
    have htargetPositive : 0 < abundanceTarget := by
      norm_num [abundanceTarget]
    nlinarith
  have hlowerMeanDomain :
      upperRegionLowerMeanExpression.DomainAt upperWeight displacement := by
    simp [upperRegionLowerMeanExpression, EntropyExpr.DomainAt, EntropyExpr.sub]
  have hupperMeanDomain :
      upperRegionUpperMeanExpression.DomainAt upperWeight displacement := by
    simp [upperRegionUpperMeanExpression, EntropyExpr.DomainAt, EntropyExpr.eval,
      EntropyExpr.sub, EntropyExpr.div]
    exact hweightPositive
  apply diagonal_domain
    (sub_domain (constant_domain 1 upperWeight displacement)
      (horizontal_domain upperWeight displacement))
    (horizontal_domain upperWeight displacement)
    hlowerMeanDomain hupperMeanDomain
  · rw [upperRegionLowerMeanExpression_eval]
    exact hmeans.1
  · rw [upperRegionUpperMeanExpression_eval]
    exact hmeans.2

theorem centeredCurveExpression_domain {y auxiliary : ℝ}
    (hy₀ : 0 < y) (hy₁ : y < 1) :
    centeredCurveExpression.DomainAt y auxiliary := by
  have hyDomain := horizontal_domain y auxiliary
  have hyMem : (EntropyExpr.horizontal.eval y auxiliary) ∈ Icc (0 : ℝ) 1 := by
    simpa only [EntropyExpr.eval] using And.intro hy₀.le hy₁.le
  have hySquareMem :
      (EntropyExpr.mul .horizontal .horizontal).eval y auxiliary ∈ Icc (0 : ℝ) 1 := by
    simp only [EntropyExpr.eval]
    constructor
    · positivity
    · nlinarith [mul_nonneg hy₀.le (sub_nonneg.2 hy₁.le)]
  have hySquareEntropy := entropy_domain (mul_domain hyDomain hyDomain) hySquareMem
  have hyEntropy := entropy_domain hyDomain hyMem
  have hhalfEntropy :
      (EntropyExpr.entropy (.constant (1 / 2))).DomainAt y auxiliary := by
    apply entropy_domain (constant_domain (1 / 2) y auxiliary)
    norm_num [EntropyExpr.eval]
  have hindependent := mul_domain
    (constant_domain ((123531 / 200000) ^ 2) y auxiliary) hySquareEntropy
  have hmarginal := mul_domain
    (mul_domain (constant_domain (123531 / 200000) y auxiliary) hyDomain) hyEntropy
  have hdependent := mul_domain
    (sub_domain
      (mul_domain (constant_domain (123531 / 100000) y auxiliary) hyDomain)
      (mul_domain hyDomain hyDomain))
    hhalfEntropy
  exact sub_domain
    (add_domain
      (mul_domain (constant_domain (193 / 200) y auxiliary) hindependent)
      (mul_domain (constant_domain (7 / 200) y auxiliary) hdependent))
    (mul_domain (constant_domain (10000001 / 10000000) y auxiliary) hmarginal)

theorem centeredCurveExpression_eval (y auxiliary : ℝ) :
    centeredCurveExpression.eval y auxiliary =
      (1 - dependentShare) * targetComplement ^ 2 * binEntropy (y ^ 2) +
        dependentShare * (2 * targetComplement * y - y ^ 2) * log 2 -
        (1 + entropySlack) * targetComplement * y * binEntropy y := by
  simp [centeredCurveExpression, yuGap, EntropyExpr.eval, EntropyExpr.sub,
    dependentShare, entropySlack, targetComplement, abundanceTarget]
  ring

theorem endpointExpression_eval {a q : ℝ} (haHalf : a ≤ 1 / 2) :
    endpointExpression.eval a q = endpointCertificateObjective a q := by
  rw [endpointCertificateObjective, diagonalEndpointObjective,
    dependentCost_self_eq_cappedEntropy haHalf]
  simp [endpointExpression, endpoint, endpointIndependent, endpointMarginal,
    endpointUpperWeight, yuGap, EntropyExpr.eval, EntropyExpr.sub, EntropyExpr.div,
    EntropyExpr.join, EntropyExpr.selfJoin, endpointCertificateWeight, Frankl.yuGap,
    Frankl.join, abundanceTarget, dependentShare, entropySlack]
  ring

theorem lowerRegionExpression_eval {upperWeight displacement : ℝ}
    (hlowerHalf : lowerRegionLowerMean upperWeight displacement ≤ 1 / 2)
    (hupperHalf : lowerRegionUpperMean displacement ≤ 1 / 2) :
    lowerRegionExpression.eval upperWeight displacement =
      lowerRegionDiagonalObjective upperWeight displacement := by
  rw [lowerRegionDiagonalObjective, diagonalPairObjective,
    dependentCost_self_eq_cappedEntropy hlowerHalf,
    dependentCost_self_eq_cappedEntropy hupperHalf]
  simp [lowerRegionExpression, diagonal, diagonalIndependent, diagonalMarginal,
    diagonalDependent, lowerRegionLowerMeanExpression, lowerRegionUpperMeanExpression,
    lowerRegionLowerMean, lowerRegionUpperMean, yuGap, EntropyExpr.eval, EntropyExpr.sub,
    EntropyExpr.div, EntropyExpr.join, EntropyExpr.selfJoin, Frankl.yuGap, Frankl.join,
    abundanceTarget, dependentShare, entropySlack]
  ring

theorem upperRegionExpression_eval {upperWeight displacement : ℝ}
    (hlowerHalf : upperRegionLowerMean displacement ≤ 1 / 2)
    (hupperHalf : upperRegionUpperMean upperWeight displacement ≤ 1 / 2) :
    upperRegionExpression.eval upperWeight displacement =
      upperRegionDiagonalObjective upperWeight displacement := by
  rw [upperRegionDiagonalObjective, diagonalPairObjective,
    dependentCost_self_eq_cappedEntropy hlowerHalf,
    dependentCost_self_eq_cappedEntropy hupperHalf]
  simp [upperRegionExpression, diagonal, diagonalIndependent, diagonalMarginal,
    diagonalDependent, upperRegionLowerMeanExpression, upperRegionUpperMeanExpression,
    upperRegionLowerMean, upperRegionUpperMean, yuGap, EntropyExpr.eval, EntropyExpr.sub,
    EntropyExpr.div, EntropyExpr.join, EntropyExpr.selfJoin, Frankl.yuGap, Frankl.join,
    abundanceTarget, dependentShare, entropySlack]
  ring

end CertificateObjective

end Frankl
