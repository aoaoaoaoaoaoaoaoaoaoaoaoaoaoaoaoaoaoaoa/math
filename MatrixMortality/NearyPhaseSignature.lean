import MatrixMortality.NearyEncoding
import MatrixMortality.PhaseSignature

/-!
# Neary phase-signature obstruction

The Neary lower channel agrees at every deletion phase but has unequal rule scales, contradicting
the generic two-private-state phase law.
-/

namespace MatrixMortality

/-- The lower-channel scale of one Neary role over the rational side representation. -/
def nearyLowerScale (β : Nat) (body : List TagLetter) (tile : NearyTile) : ℚ :=
  3 ^ (nearyLower β body tile).length

@[simp] theorem nearyLowerScale_erase_eq
    (β : Nat) (body : List TagLetter) :
    nearyLowerScale β body (.erase .b) =
      nearyLowerScale β body (.erase .c) := by
  rfl

theorem nearyLowerScale_rule_ne
    (β : Nat) (body : List TagLetter) (body_ne : body ≠ []) :
    nearyLowerScale β body (.rule .b) ≠
      nearyLowerScale β body (.rule .c) := by
  have encoded_nonempty : tagEncode β body ≠ [] :=
    (tagEncode_eq_nil_iff β body).not.mpr body_ne
  have lower_length :
      3 < (nearyLower β body (.rule .c)).length := by
    simp only [nearyLower, List.length_append, List.length_cons, List.length_nil]
    have encoded_length := List.length_pos_of_ne_nil encoded_nonempty
    omega
  have scale_lt :
      (3 : ℚ) ^ 3 <
        3 ^ (nearyLower β body (.rule .c)).length :=
    pow_lt_pow_right₀ (a := (3 : ℚ)) (by norm_num) lower_length
  exact ne_of_lt (by
    simpa only [nearyLowerScale, nearyLower, List.length_cons, List.length_nil] using
      scale_lt)

/-- The Neary lower-channel signature cannot occur in a cyclic exact compiler with at most
two private quotient states. -/
theorem neary_twoPrivateState_phaseCompiler_impossible
    {Q : Type*} [AddCommGroup Q] [Module ℚ Q] [FiniteDimensional ℚ Q]
    (β : Nat) (body : List TagLetter) (body_ne : body ≠ [])
    (left right clock : Q →ₗ[ℚ] Q)
    (rulePhase firstDeletion secondDeletion nextPhase : Q)
    (firstDeletion_ne : firstDeletion ≠ 0)
    (nextPhase_ne : nextPhase ≠ 0)
    (clockScale returnScale : ℚ)
    (returnScale_ne : returnScale ≠ 0)
    (returnSteps : Nat)
    (dimension_le : Module.finrank ℚ Q ≤ 2)
    (clock_first :
      clock firstDeletion = clockScale • secondDeletion)
    (clock_return :
      (clock : Q → Q)^[returnSteps] secondDeletion = returnScale • rulePhase)
    (agree_first : left firstDeletion = right firstDeletion)
    (agree_second : left secondDeletion = right secondDeletion)
    (left_rule :
      left rulePhase =
        nearyLowerScale β body (.rule .b) • nextPhase)
    (right_rule :
      right rulePhase =
        nearyLowerScale β body (.rule .c) • nextPhase) :
    False := by
  exact nearyLowerScale_rule_ne β body body_ne <|
    twoPrivateState_ruleScale_eq left right clock rulePhase firstDeletion
      secondDeletion nextPhase firstDeletion_ne nextPhase_ne clockScale
      returnScale (nearyLowerScale β body (.rule .b))
      (nearyLowerScale β body (.rule .c)) returnScale_ne returnSteps dimension_le
      clock_first clock_return agree_first agree_second left_rule right_rule

end MatrixMortality
