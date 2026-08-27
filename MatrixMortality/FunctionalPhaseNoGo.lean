import Mathlib
import MatrixMortality.EndpointPrefixCompiler

/-!
# Functional phase-transfer obstruction

A positive phase quotient lifts phase weights to strictly positive symbol weights.  For three
loopless functional transfers, two of the three drifts can always be killed exactly; the last
drift then fixes a common sign.  The forked two-cycle is the sharp three-rule topology outside
that argument.
-/

namespace MatrixMortality

namespace FunctionalPhaseNoGo

/-! ## Positive quotient arithmetic -/

/-- Lift phase weights through a nonnegative phase-by-symbol quotient. -/
def liftWeight {Phase Symbol : Type*} [Fintype Phase]
    (quotient : Phase → Symbol → ℚ) (phaseWeight : Phase → ℚ) : Symbol → ℚ :=
  fun symbol => ∑ phase, phaseWeight phase * quotient phase symbol

/-- Evaluate a symbol displacement against one symbol weighting. -/
def symbolDrift {Symbol : Type*} [Fintype Symbol]
    (weight displacement : Symbol → ℚ) : ℚ :=
  ∑ symbol, weight symbol * displacement symbol

/-- Project one symbol displacement into phase charge. -/
def quotientDrift {Phase Symbol : Type*} [Fintype Symbol]
    (quotient : Phase → Symbol → ℚ) (displacement : Symbol → ℚ) : Phase → ℚ :=
  fun phase => ∑ symbol, quotient phase symbol * displacement symbol

/-- Removing `consume` units at `source` and emitting `produce` units at `target`. -/
def transferCharge {Phase : Type*} [DecidableEq Phase]
    (source target : Phase) (consume produce : ℚ) : Phase → ℚ :=
  fun phase =>
    (if phase = target then produce else 0) -
      if phase = source then consume else 0

/-- Nonnegative quotient columns with positive support turn positive phase weights into a
strictly positive symbol weighting. -/
theorem liftWeight_pos {Phase Symbol : Type*} [Fintype Phase]
    (quotient : Phase → Symbol → ℚ) (phaseWeight : Phase → ℚ)
    (quotient_nonnegative : ∀ phase symbol, 0 ≤ quotient phase symbol)
    (column_positive : ∀ symbol, ∃ phase, 0 < quotient phase symbol)
    (phaseWeight_positive : ∀ phase, 0 < phaseWeight phase) (symbol : Symbol) :
    0 < liftWeight quotient phaseWeight symbol := by
  apply Finset.sum_pos'
  · intro phase _
    exact mul_nonneg (phaseWeight_positive phase).le
      (quotient_nonnegative phase symbol)
  · obtain ⟨phase, positive⟩ := column_positive symbol
    exact ⟨phase, Finset.mem_univ phase,
      mul_pos (phaseWeight_positive phase) positive⟩

/-- Lifting a weighting and projecting a displacement are adjoint finite sums. -/
theorem symbolDrift_liftWeight {Phase Symbol : Type*}
    [Fintype Phase] [Fintype Symbol] (quotient : Phase → Symbol → ℚ)
    (phaseWeight : Phase → ℚ) (displacement : Symbol → ℚ) :
    symbolDrift (liftWeight quotient phaseWeight) displacement =
      ∑ phase, phaseWeight phase * quotientDrift quotient displacement phase := by
  simp only [symbolDrift, liftWeight, quotientDrift, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro phase _
  apply Finset.sum_congr rfl
  intro symbol _
  ring

/-- An exact source-to-target phase transfer has the expected scalar drift after lifting. -/
theorem symbolDrift_liftWeight_of_transfer {Phase Symbol : Type*}
    [Fintype Phase] [Fintype Symbol] [DecidableEq Phase]
    (quotient : Phase → Symbol → ℚ) (phaseWeight : Phase → ℚ)
    (displacement : Symbol → ℚ) (source target : Phase) (consume produce : ℚ)
    (transfer : quotientDrift quotient displacement =
      transferCharge source target consume produce) :
    symbolDrift (liftWeight quotient phaseWeight) displacement =
      produce * phaseWeight target - consume * phaseWeight source := by
  rw [symbolDrift_liftWeight, transfer]
  simp only [transferCharge, mul_sub, Finset.sum_sub_distrib]
  simp
  ring

/-! ## Three functional phases -/

/-- The phase graph has three vertices, one for each production. -/
abbrev Phase := Fin 3

/-- The eight loopless functional graphs on three labeled phases. -/
inductive RouteShape
  | cycle012
  | cycle021
  | cycle01Feed0
  | cycle01Feed1
  | cycle02Feed0
  | cycle02Feed2
  | cycle12Feed1
  | cycle12Feed2
  deriving DecidableEq

/-- The unique outgoing route represented by a three-phase graph shape. -/
def RouteShape.next : RouteShape → Phase → Phase
  | .cycle012 => ![1, 2, 0]
  | .cycle021 => ![2, 0, 1]
  | .cycle01Feed0 => ![1, 0, 0]
  | .cycle01Feed1 => ![1, 0, 1]
  | .cycle02Feed0 => ![2, 0, 0]
  | .cycle02Feed2 => ![2, 2, 0]
  | .cycle12Feed1 => ![1, 2, 1]
  | .cycle12Feed2 => ![2, 2, 1]

@[simp] theorem RouteShape.next_ne_self (shape : RouteShape) (phase : Phase) :
    shape.next phase ≠ phase := by
  cases shape <;> fin_cases phase <;> decide

/-- Every loopless functional graph on three vertices is one three-cycle or a two-cycle with a
single feeder. -/
theorem exists_routeShape (next : Phase → Phase) (loopless : ∀ phase, next phase ≠ phase) :
    ∃ shape : RouteShape, next = RouteShape.next shape := by
  have next_zero : next 0 = 1 ∨ next 0 = 2 := by
    have range := (next 0).isLt
    have distinct : (next 0).val ≠ 0 := by
      intro equality
      exact loopless 0 (Fin.ext equality)
    have alternatives : (next 0).val = 1 ∨ (next 0).val = 2 := by omega
    exact alternatives.imp Fin.ext Fin.ext
  have next_one : next 1 = 0 ∨ next 1 = 2 := by
    have range := (next 1).isLt
    have distinct : (next 1).val ≠ 1 := by
      intro equality
      exact loopless 1 (Fin.ext equality)
    have alternatives : (next 1).val = 0 ∨ (next 1).val = 2 := by omega
    exact alternatives.imp Fin.ext Fin.ext
  have next_two : next 2 = 0 ∨ next 2 = 1 := by
    have range := (next 2).isLt
    have distinct : (next 2).val ≠ 2 := by
      intro equality
      exact loopless 2 (Fin.ext equality)
    have alternatives : (next 2).val = 0 ∨ (next 2).val = 1 := by omega
    exact alternatives.imp Fin.ext Fin.ext
  rcases next_zero with zero_to_one | zero_to_two <;>
    rcases next_one with one_to_zero | one_to_two <;>
      rcases next_two with two_to_zero | two_to_one
  · exact ⟨.cycle01Feed0, by
      funext phase
      fin_cases phase <;> simp [RouteShape.next, zero_to_one, one_to_zero, two_to_zero]⟩
  · exact ⟨.cycle01Feed1, by
      funext phase
      fin_cases phase <;> simp [RouteShape.next, zero_to_one, one_to_zero, two_to_one]⟩
  · exact ⟨.cycle012, by
      funext phase
      fin_cases phase <;> simp [RouteShape.next, zero_to_one, one_to_two, two_to_zero]⟩
  · exact ⟨.cycle12Feed1, by
      funext phase
      fin_cases phase <;> simp [RouteShape.next, zero_to_one, one_to_two, two_to_one]⟩
  · exact ⟨.cycle02Feed0, by
      funext phase
      fin_cases phase <;> simp [RouteShape.next, zero_to_two, one_to_zero, two_to_zero]⟩
  · exact ⟨.cycle021, by
      funext phase
      fin_cases phase <;> simp [RouteShape.next, zero_to_two, one_to_zero, two_to_one]⟩
  · exact ⟨.cycle02Feed2, by
      funext phase
      fin_cases phase <;> simp [RouteShape.next, zero_to_two, one_to_two, two_to_zero]⟩
  · exact ⟨.cycle12Feed2, by
      funext phase
      fin_cases phase <;> simp [RouteShape.next, zero_to_two, one_to_two, two_to_one]⟩

/-- Drift of one functional phase transfer under a phase weighting. -/
def phaseDrift (next : Phase → Phase) (consume produce weight : Phase → ℚ)
    (rule : Phase) : ℚ :=
  produce rule * weight (next rule) - consume rule * weight rule

/-- All drifts point weakly in one direction. -/
def OneSidedDrift (drift : Phase → ℚ) : Prop :=
  (∀ rule, 0 ≤ drift rule) ∨ ∀ rule, drift rule ≤ 0

private theorem oneSidedDrift_of_zero_off (drift : Phase → ℚ) (live : Phase)
    (zero_off : ∀ rule, rule ≠ live → drift rule = 0) :
    OneSidedDrift drift := by
  rcases le_total 0 (drift live) with nonnegative | nonpositive
  · left
    intro rule
    by_cases equality : rule = live
    · simpa [equality] using nonnegative
    · simp [zero_off rule equality]
  · right
    intro rule
    by_cases equality : rule = live
    · simpa [equality] using nonpositive
    · simp [zero_off rule equality]

/-- Every positive loopless functional three-phase transporter admits positive phase weights
whose three drifts have one common weak sign. -/
theorem exists_positive_weight_oneSided (next : Phase → Phase)
    (consume produce : Phase → ℚ) (loopless : ∀ phase, next phase ≠ phase)
    (consume_positive : ∀ phase, 0 < consume phase)
    (produce_positive : ∀ phase, 0 < produce phase) :
    ∃ weight : Phase → ℚ,
      (∀ phase, 0 < weight phase) ∧
        OneSidedDrift (phaseDrift next consume produce weight) := by
  have consume_zero_positive := consume_positive 0
  have consume_one_positive := consume_positive 1
  have consume_two_positive := consume_positive 2
  have produce_zero_positive := produce_positive 0
  have produce_one_positive := produce_positive 1
  have produce_two_positive := produce_positive 2
  obtain ⟨shape, rfl⟩ := exists_routeShape next loopless
  cases shape with
  | cycle012 =>
      let weight : Phase → ℚ :=
        ![produce 0 * produce 1, consume 0 * produce 1, consume 0 * consume 1]
      refine ⟨weight, ?_, oneSidedDrift_of_zero_off _ 2 ?_⟩
      · intro phase
        fin_cases phase <;> simp [weight] <;> positivity
      · intro rule not_live
        fin_cases rule <;> simp_all [phaseDrift, RouteShape.next, weight] <;> ring
  | cycle021 =>
      let weight : Phase → ℚ :=
        ![produce 0 * produce 2, consume 0 * consume 2, consume 0 * produce 2]
      refine ⟨weight, ?_, oneSidedDrift_of_zero_off _ 1 ?_⟩
      · intro phase
        fin_cases phase <;> simp [weight] <;> positivity
      · intro rule not_live
        fin_cases rule <;> simp_all [phaseDrift, RouteShape.next, weight] <;> ring
  | cycle01Feed0 =>
      let weight : Phase → ℚ :=
        ![produce 0 * consume 2, consume 0 * consume 2, produce 2 * produce 0]
      refine ⟨weight, ?_, oneSidedDrift_of_zero_off _ 1 ?_⟩
      · intro phase
        fin_cases phase <;> simp [weight] <;> positivity
      · intro rule not_live
        fin_cases rule <;> simp_all [phaseDrift, RouteShape.next, weight] <;> ring
  | cycle01Feed1 =>
      let weight : Phase → ℚ :=
        ![produce 0 * consume 2, consume 0 * consume 2, produce 2 * consume 0]
      refine ⟨weight, ?_, oneSidedDrift_of_zero_off _ 1 ?_⟩
      · intro phase
        fin_cases phase <;> simp [weight] <;> positivity
      · intro rule not_live
        fin_cases rule <;> simp_all [phaseDrift, RouteShape.next, weight] <;> ring
  | cycle02Feed0 =>
      let weight : Phase → ℚ :=
        ![produce 0 * consume 1, produce 1 * produce 0, consume 0 * consume 1]
      refine ⟨weight, ?_, oneSidedDrift_of_zero_off _ 2 ?_⟩
      · intro phase
        fin_cases phase <;> simp [weight] <;> positivity
      · intro rule not_live
        fin_cases rule <;> simp_all [phaseDrift, RouteShape.next, weight] <;> ring
  | cycle02Feed2 =>
      let weight : Phase → ℚ :=
        ![produce 0 * consume 1, produce 1 * consume 0, consume 0 * consume 1]
      refine ⟨weight, ?_, oneSidedDrift_of_zero_off _ 2 ?_⟩
      · intro phase
        fin_cases phase <;> simp [weight] <;> positivity
      · intro rule not_live
        fin_cases rule <;> simp_all [phaseDrift, RouteShape.next, weight] <;> ring
  | cycle12Feed1 =>
      let weight : Phase → ℚ :=
        ![produce 0 * produce 1, produce 1 * consume 0, consume 1 * consume 0]
      refine ⟨weight, ?_, oneSidedDrift_of_zero_off _ 2 ?_⟩
      · intro phase
        fin_cases phase <;> simp [weight] <;> positivity
      · intro rule not_live
        fin_cases rule <;> simp_all [phaseDrift, RouteShape.next, weight] <;> ring
  | cycle12Feed2 =>
      let weight : Phase → ℚ :=
        ![produce 0 * consume 1, produce 1 * consume 0, consume 1 * consume 0]
      refine ⟨weight, ?_, oneSidedDrift_of_zero_off _ 2 ?_⟩
      · intro phase
        fin_cases phase <;> simp [weight] <;> positivity
      · intro rule not_live
        fin_cases rule <;> simp_all [phaseDrift, RouteShape.next, weight] <;> ring

/-- A positive functional quotient therefore yields a strictly positive symbol weighting with
one-sided drift. -/
theorem exists_positive_symbolWeight_oneSided {Symbol : Type*} [Fintype Symbol]
    (quotient : Phase → Symbol → ℚ) (displacement : Phase → Symbol → ℚ)
    (next : Phase → Phase) (consume produce : Phase → ℚ)
    (quotient_nonnegative : ∀ phase symbol, 0 ≤ quotient phase symbol)
    (column_positive : ∀ symbol, ∃ phase, 0 < quotient phase symbol)
    (loopless : ∀ phase, next phase ≠ phase)
    (consume_positive : ∀ phase, 0 < consume phase)
    (produce_positive : ∀ phase, 0 < produce phase)
    (transfer : ∀ rule,
      quotientDrift quotient (displacement rule) =
        transferCharge rule (next rule) (consume rule) (produce rule)) :
    ∃ weight : Symbol → ℚ,
      (∀ symbol, 0 < weight symbol) ∧
        OneSidedDrift (fun rule => symbolDrift weight (displacement rule)) := by
  obtain ⟨phaseWeight, phaseWeight_positive, oneSided⟩ :=
    exists_positive_weight_oneSided next consume produce loopless
      consume_positive produce_positive
  refine ⟨liftWeight quotient phaseWeight,
    liftWeight_pos quotient phaseWeight quotient_nonnegative column_positive
      phaseWeight_positive, ?_⟩
  have drift_eq (rule : Phase) :
      symbolDrift (liftWeight quotient phaseWeight) (displacement rule) =
        phaseDrift next consume produce phaseWeight rule := by
    rw [symbolDrift_liftWeight_of_transfer quotient phaseWeight (displacement rule)
      rule (next rule) (consume rule) (produce rule) (transfer rule)]
    rfl
  rcases oneSided with nonnegative | nonpositive
  · left
    intro rule
    change 0 ≤ symbolDrift (liftWeight quotient phaseWeight) (displacement rule)
    rw [drift_eq]
    exact nonnegative rule
  · right
    intro rule
    change symbolDrift (liftWeight quotient phaseWeight) (displacement rule) ≤ 0
    rw [drift_eq]
    exact nonpositive rule

/-! ## Cycle products and the sharp fork -/

/-- Multiplying local inequalities around a positive two-cycle cancels the phase weights. -/
theorem twoCycle_product_le {consume₀ consume₁ produce₀ produce₁ weight₀ weight₁ : ℚ}
    (consume₁_nonnegative : 0 ≤ consume₁) (produce₀_nonnegative : 0 ≤ produce₀)
    (weight₀_positive : 0 < weight₀) (weight₁_positive : 0 < weight₁)
    (first : consume₀ * weight₀ ≤ produce₀ * weight₁)
    (second : consume₁ * weight₁ ≤ produce₁ * weight₀) :
    consume₀ * consume₁ ≤ produce₀ * produce₁ := by
  have multiplied := mul_le_mul first second
    (mul_nonneg consume₁_nonnegative weight₁_positive.le)
    (mul_nonneg produce₀_nonnegative weight₁_positive.le)
  have weightProduct_positive : 0 < weight₀ * weight₁ :=
    mul_pos weight₀_positive weight₁_positive
  apply (mul_le_mul_iff_of_pos_left weightProduct_positive).mp
  convert multiplied using 1 <;> ring

/-- Reversing both inequalities reverses the two-cycle product comparison. -/
theorem twoCycle_product_ge {consume₀ consume₁ produce₀ produce₁ weight₀ weight₁ : ℚ}
    (produce₁_nonnegative : 0 ≤ produce₁) (consume₀_nonnegative : 0 ≤ consume₀)
    (weight₀_positive : 0 < weight₀) (weight₁_positive : 0 < weight₁)
    (first : produce₀ * weight₁ ≤ consume₀ * weight₀)
    (second : produce₁ * weight₀ ≤ consume₁ * weight₁) :
    produce₀ * produce₁ ≤ consume₀ * consume₁ := by
  simpa [mul_comm] using
    twoCycle_product_le produce₁_nonnegative consume₀_nonnegative
      weight₁_positive weight₀_positive first second

/-- Multiplying local inequalities around a positive three-cycle cancels all phase weights. -/
theorem threeCycle_product_le
    {consume₀ consume₁ consume₂ produce₀ produce₁ produce₂ : ℚ}
    {weight₀ weight₁ weight₂ : ℚ}
    (consume₁_nonnegative : 0 ≤ consume₁) (consume₂_nonnegative : 0 ≤ consume₂)
    (produce₀_nonnegative : 0 ≤ produce₀) (produce₁_nonnegative : 0 ≤ produce₁)
    (weight₀_positive : 0 < weight₀) (weight₁_positive : 0 < weight₁)
    (weight₂_positive : 0 < weight₂)
    (first : consume₀ * weight₀ ≤ produce₀ * weight₁)
    (second : consume₁ * weight₁ ≤ produce₁ * weight₂)
    (third : consume₂ * weight₂ ≤ produce₂ * weight₀) :
    consume₀ * consume₁ * consume₂ ≤ produce₀ * produce₁ * produce₂ := by
  have firstSecond := mul_le_mul first second
    (mul_nonneg consume₁_nonnegative weight₁_positive.le)
    (mul_nonneg produce₀_nonnegative weight₁_positive.le)
  have multiplied := mul_le_mul firstSecond third
    (mul_nonneg consume₂_nonnegative weight₂_positive.le)
    (mul_nonneg
      (mul_nonneg produce₀_nonnegative weight₁_positive.le)
      (mul_nonneg produce₁_nonnegative weight₂_positive.le))
  have weightProduct_positive : 0 < weight₀ * weight₁ * weight₂ :=
    mul_pos (mul_pos weight₀_positive weight₁_positive) weight₂_positive
  apply (mul_le_mul_iff_of_pos_left weightProduct_positive).mp
  convert multiplied using 1 <;> ring

/-- Reversing all three local inequalities reverses the three-cycle product comparison. -/
theorem threeCycle_product_ge
    {consume₀ consume₁ consume₂ produce₀ produce₁ produce₂ : ℚ}
    {weight₀ weight₁ weight₂ : ℚ}
    (produce₂_nonnegative : 0 ≤ produce₂) (produce₁_nonnegative : 0 ≤ produce₁)
    (consume₀_nonnegative : 0 ≤ consume₀) (consume₂_nonnegative : 0 ≤ consume₂)
    (weight₀_positive : 0 < weight₀) (weight₁_positive : 0 < weight₁)
    (weight₂_positive : 0 < weight₂)
    (first : produce₀ * weight₁ ≤ consume₀ * weight₀)
    (second : produce₁ * weight₂ ≤ consume₁ * weight₁)
    (third : produce₂ * weight₀ ≤ consume₂ * weight₂) :
    produce₀ * produce₁ * produce₂ ≤ consume₀ * consume₁ * consume₂ := by
  have reversed :=
    threeCycle_product_le produce₂_nonnegative produce₁_nonnegative
      consume₀_nonnegative consume₂_nonnegative weight₁_positive
      weight₀_positive weight₂_positive first third second
  convert reversed using 1 <;> ring

/-- The three rules in the sharp forked two-cycle. -/
inductive ForkRule
  | contract
  | expand
  | return
  deriving DecidableEq

/-- Parikh drift of `ppX ⟶ Xq`, `pX ⟶ Xqq`, and `qX ⟶ Xp`. -/
def forkDrift (pWeight qWeight : ℚ) : ForkRule → ℚ
  | .contract => qWeight - 2 * pWeight
  | .expand => 2 * qWeight - pWeight
  | .return => pWeight - qWeight

/-- Every positive weighting gives the forked two-cycle both a strict expansion and a strict
contraction.  Thus head separation is compatible with the mixed-drift condition once functional
one-target transport is abandoned. -/
theorem forkDrift_mixed (pWeight qWeight : ℚ)
    (pWeight_positive : 0 < pWeight) (qWeight_positive : 0 < qWeight) :
    (∃ rule, forkDrift pWeight qWeight rule < 0) ∧
      ∃ rule, 0 < forkDrift pWeight qWeight rule := by
  constructor
  · by_cases q_lt_twice_p : qWeight < 2 * pWeight
    · exact ⟨.contract, by simpa [forkDrift] using q_lt_twice_p⟩
    · refine ⟨.return, ?_⟩
      simp only [forkDrift]
      push Not at q_lt_twice_p
      linarith
  · by_cases q_le_half_p : qWeight ≤ pWeight / 2
    · refine ⟨.return, ?_⟩
      simp only [forkDrift]
      linarith
    · refine ⟨.expand, ?_⟩
      simp only [forkDrift]
      push Not at q_le_half_p
      linarith

/-- The sharp fork admits no positive one-sided weighting. -/
theorem forkDrift_not_oneSided (pWeight qWeight : ℚ)
    (pWeight_positive : 0 < pWeight) (qWeight_positive : 0 < qWeight) :
    ¬((∀ rule, 0 ≤ forkDrift pWeight qWeight rule) ∨
      ∀ rule, forkDrift pWeight qWeight rule ≤ 0) := by
  obtain ⟨⟨negativeRule, negative⟩, positiveRule, positive⟩ :=
    forkDrift_mixed pWeight qWeight pWeight_positive qWeight_positive
  rintro (nonnegative | nonpositive)
  · exact (not_le_of_gt negative) (nonnegative negativeRule)
  · exact (not_le_of_gt positive) (nonpositive positiveRule)

/-- An empty-consume transfer is strictly expanding under every positive phase weighting. -/
theorem emptyConsume_drift_pos (produce sourceWeight targetWeight : ℚ)
    (produce_positive : 0 < produce) (targetWeight_positive : 0 < targetWeight) :
    0 < produce * targetWeight - 0 * sourceWeight := by
  simpa using mul_pos produce_positive targetWeight_positive

end FunctionalPhaseNoGo

end MatrixMortality
