import MatrixMortality.NearySideNormal

/-!
# Deletion-first binary scheduling obstruction

The shared deletion channel does not by itself merge the three lower-channel fibres of the
two-bit Neary decoder. If one bit operator carries the boundary fibre to the rule fibre and both
rule and deletion fibres return through the same carrier, exact transition
compatibility forces the two rule scales to agree. Neary's `b`- and `c`-rule scales are unequal.
-/

namespace MatrixMortality

/-- A deletion-first scheduler sharing one exact lower-channel fibre forces the two rule scales
to coincide. The statement includes arbitrary ambient dimension; injectivity is needed only for
the bit operator on the displayed fibre. -/
theorem ruleScale_eq_of_deletionFirst_fibre
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (bBit cBit : V →ₗ[ℚ] V) (boundary rule deletion : V)
    (ruleBScale ruleCScale deletionScale : ℚ)
    (bBit_injective : Function.Injective bBit)
    (boundary_ne : boundary ≠ 0) (deletionScale_ne : deletionScale ≠ 0)
    (bBit_rule : bBit rule = ruleBScale • boundary)
    (bBit_deletion : bBit deletion = deletionScale • boundary)
    (cBit_rule : cBit rule = ruleCScale • boundary)
    (cBit_deletion : cBit deletion = deletionScale • boundary) :
    ruleBScale = ruleCScale := by
  have fibre_eq : ruleBScale • deletion = deletionScale • rule := by
    apply bBit_injective
    rw [map_smul, map_smul, bBit_deletion, bBit_rule]
    simp only [smul_smul]
    congr 1
    ring
  have scaled_rule_eq := congrArg cBit fibre_eq
  rw [map_smul, map_smul, cBit_deletion, cBit_rule] at scaled_rule_eq
  simp only [smul_smul] at scaled_rule_eq
  have scalar_eq : ruleBScale * deletionScale = deletionScale * ruleCScale :=
    smul_left_injective ℚ boundary_ne scaled_rule_eq
  exact (mul_left_cancel₀ deletionScale_ne <| by
    simpa [mul_comm] using scalar_eq.symm).symm

/-- The body-dependent Neary `c`-rule scale is strictly larger than the fixed `b`-rule scale. -/
theorem nearySideLowerCScale_gt_twentySeven
    (β : Nat) (body : List TagLetter) (body_nonempty : body ≠ []) :
    (27 : ℚ) < nearySideLowerCScale β body := by
  have encoded_nonempty : tagEncode β body ≠ [] :=
    (tagEncode_eq_nil_iff β body).not.mpr body_nonempty
  have four_le : 4 ≤ (nearyLower β body (.rule .c)).length := by
    simp only [nearyLower, List.length_append, List.length_cons, List.length_nil]
    have encoded_length := List.length_pos_of_ne_nil encoded_nonempty
    omega
  have power_lt : 27 < 3 ^ (nearyLower β body (.rule .c)).length := by
    have power_le := Nat.pow_le_pow_right (by norm_num : 0 < 3) four_le
    norm_num at power_le ⊢
    omega
  simp only [nearySideLowerCScale]
  exact_mod_cast power_lt

/-- The exact deletion-first fibre equations cannot hold for the two Neary rule scales. -/
theorem no_neary_deletionFirst_fibre
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (β : Nat) (body : List TagLetter) (body_nonempty : body ≠ [])
    (bBit cBit : V →ₗ[ℚ] V) (boundary rule deletion : V)
    (bBit_injective : Function.Injective bBit) (boundary_ne : boundary ≠ 0)
    (bBit_rule : bBit rule = (27 : ℚ) • boundary)
    (bBit_deletion : bBit deletion = (3 : ℚ) • boundary)
    (cBit_rule : cBit rule = nearySideLowerCScale β body • boundary)
    (cBit_deletion : cBit deletion = (3 : ℚ) • boundary) : False := by
  have scale_eq : (27 : ℚ) = nearySideLowerCScale β body :=
    ruleScale_eq_of_deletionFirst_fibre bBit cBit boundary rule deletion
      27 (nearySideLowerCScale β body) 3 bBit_injective boundary_ne (by norm_num)
      bBit_rule bBit_deletion cBit_rule cBit_deletion
  have scale_gt := nearySideLowerCScale_gt_twentySeven β body body_nonempty
  linarith

end MatrixMortality
