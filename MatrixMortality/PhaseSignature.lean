import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FinCases

/-!
# Two-private-state phase obstruction

An exact phase compiler with at most two private quotient states cannot distinguish two data
letters at one cyclic phase while making them agree at every other phase. Two consecutive
agreement phases either span the quotient, forcing global agreement, or lie on one line. In
the latter case the cyclic transition preserves that line and carries it back to the
distinguished phase, again forcing agreement there.
-/

namespace MatrixMortality

/-- Two linear controls that agree on two consecutive private phase vectors also agree on the
distinguished phase reached by cycling the second vector, provided the private quotient has
dimension at most two. -/
theorem twoPrivateState_agree_at_rulePhase
    {K Q : Type*} [Field K] [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q]
    (left right clock : Q →ₗ[K] Q)
    (rulePhase firstDeletion secondDeletion : Q)
    (firstDeletion_ne : firstDeletion ≠ 0)
    (clockScale returnScale : K)
    (returnScale_ne : returnScale ≠ 0)
    (returnSteps : Nat)
    (dimension_le : Module.finrank K Q ≤ 2)
    (clock_first :
      clock firstDeletion = clockScale • secondDeletion)
    (clock_return :
      (clock : Q → Q)^[returnSteps] secondDeletion = returnScale • rulePhase)
    (agree_first : left firstDeletion = right firstDeletion)
    (agree_second : left secondDeletion = right secondDeletion) :
    left rulePhase = right rulePhase := by
  let difference := left - right
  have first_mem_ker : firstDeletion ∈ LinearMap.ker difference := by
    simp only [LinearMap.mem_ker, difference, LinearMap.sub_apply, sub_eq_zero]
    exact agree_first
  have second_mem_ker : secondDeletion ∈ LinearMap.ker difference := by
    simp only [LinearMap.mem_ker, difference, LinearMap.sub_apply, sub_eq_zero]
    exact agree_second
  by_cases dependent :
      secondDeletion ∈ Submodule.span K ({firstDeletion} : Set Q)
  · let line := Submodule.span K ({firstDeletion} : Set Q)
    have clock_preserves_line :
        ∀ vector ∈ line, clock vector ∈ line := by
      intro vector vector_mem
      obtain ⟨coefficient, rfl⟩ :=
        Submodule.mem_span_singleton.mp vector_mem
      rw [LinearMap.map_smul, clock_first]
      simpa only [smul_smul] using
        line.smul_mem (coefficient * clockScale) dependent
    have iterate_mem :
        ∀ steps, (clock : Q → Q)^[steps] secondDeletion ∈ line := by
      intro steps
      induction steps with
      | zero => exact dependent
      | succ steps induction =>
          rw [Function.iterate_succ_apply']
          exact clock_preserves_line _ induction
    have scaled_rule_mem : returnScale • rulePhase ∈ line := by
      rw [← clock_return]
      exact iterate_mem returnSteps
    have rule_mem_line : rulePhase ∈ line := by
      have inverse_scaled := line.smul_mem returnScale⁻¹ scaled_rule_mem
      simpa only [inv_smul_smul₀ returnScale_ne] using inverse_scaled
    have line_le_ker : line ≤ LinearMap.ker difference :=
      (Submodule.span_singleton_le_iff_mem firstDeletion
        (LinearMap.ker difference)).mpr first_mem_ker
    have rule_mem_ker := line_le_ker rule_mem_line
    simpa only [LinearMap.mem_ker, difference, LinearMap.sub_apply, sub_eq_zero] using
      rule_mem_ker
  · have independent :
        LinearIndependent K ![firstDeletion, secondDeletion] := by
      rw [LinearIndependent.pair_iff' firstDeletion_ne]
      intro coefficient equality
      exact dependent (Submodule.mem_span_singleton.mpr ⟨coefficient, equality⟩)
    have two_le_dimension :
        2 ≤ Module.finrank K Q := by
      simpa using independent.fintype_card_le_finrank
    have dimension_eq : Module.finrank K Q = 2 :=
      Nat.le_antisymm dimension_le two_le_dimension
    have span_eq_top :
        Submodule.span K (Set.range ![firstDeletion, secondDeletion]) = ⊤ :=
      independent.span_eq_top_of_card_eq_finrank' (by simpa using dimension_eq.symm)
    have span_le_ker :
        Submodule.span K (Set.range ![firstDeletion, secondDeletion]) ≤
          LinearMap.ker difference := by
      rw [Submodule.span_le]
      intro vector vector_mem
      obtain ⟨index, rfl⟩ := vector_mem
      fin_cases index
      · exact first_mem_ker
      · exact second_mem_ker
    have rule_mem_ker : rulePhase ∈ LinearMap.ker difference := by
      apply span_le_ker
      rw [span_eq_top]
      exact Submodule.mem_top
    simpa only [LinearMap.mem_ker, difference, LinearMap.sub_apply, sub_eq_zero] using
      rule_mem_ker

/-- In a two-private-state cyclic compiler, equality at two consecutive deletion phases
contradicts unequal nonzero scale factors at the distinguished rule phase. -/
theorem twoPrivateState_ruleScale_eq
    {K Q : Type*} [Field K] [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q]
    (left right clock : Q →ₗ[K] Q)
    (rulePhase firstDeletion secondDeletion nextPhase : Q)
    (firstDeletion_ne : firstDeletion ≠ 0)
    (nextPhase_ne : nextPhase ≠ 0)
    (clockScale returnScale leftScale rightScale : K)
    (returnScale_ne : returnScale ≠ 0)
    (returnSteps : Nat)
    (dimension_le : Module.finrank K Q ≤ 2)
    (clock_first :
      clock firstDeletion = clockScale • secondDeletion)
    (clock_return :
      (clock : Q → Q)^[returnSteps] secondDeletion = returnScale • rulePhase)
    (agree_first : left firstDeletion = right firstDeletion)
    (agree_second : left secondDeletion = right secondDeletion)
    (left_rule : left rulePhase = leftScale • nextPhase)
    (right_rule : right rulePhase = rightScale • nextPhase) :
    leftScale = rightScale := by
  have rule_agreement :=
    twoPrivateState_agree_at_rulePhase left right clock rulePhase
      firstDeletion secondDeletion firstDeletion_ne clockScale returnScale
      returnScale_ne returnSteps dimension_le clock_first clock_return agree_first
      agree_second
  rw [left_rule, right_rule] at rule_agreement
  exact smul_left_injective K nextPhase_ne rule_agreement

end MatrixMortality
