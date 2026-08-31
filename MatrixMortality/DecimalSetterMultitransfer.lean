import MatrixMortality.DecimalSetterDepth

/-!
# Decimal extinction of the first multi-transfer frontier

The swapped ternary carry leaves three possible first multi-transfer shapes. The decimal
specialization admits the same role words, but its joint two- and five-adic shells kill all
three: a two-digit multi-role block is impossible, a `(β+1)`-digit multi-role block is too
short to reach a singleton, and a current singleton cannot reach another singleton.
-/

namespace MatrixMortality.DecimalSetterDepth

open MatrixMortality.DecimalSetterArithmetic
open MatrixMortality.DecimalSetterCarry

/-- The three role shapes surviving the swapped ternary first-multi-transfer gate are all empty
in the decimal specialization. The third branch is stated without the ternary gate's preceding
two-`c` hypothesis: a current `D_b` cannot reach a singleton from any decimal-unit carrier. -/
theorem firstMultiTransfer_threeShapeFrontier_impossible
    {E G μ N D T₂ T₃ V₂ V₃ : ℚ} {m β : Nat}
    (β_large : 3 ≤ β)
    (E_unit : HasDecimalShell E 0 0)
    (G_unit : HasDecimalShell G 0 0)
    (μ_unit : HasDecimalShell μ 0 0)
    (N_unit : HasDecimalShell N 0 0)
    (D_unit : HasDecimalShell D 0 0)
    (V₂_unit : HasDecimalShell V₂ 0 0)
    (V₃_unit : HasDecimalShell V₃ 0 0)
    (shape :
      (m = 2 ∧ HasDecimalShell T₂ 1 1 ∧ HasDecimalShell T₃ 1 1) ∨
      (m = β + 1 ∧ HasDecimalShell T₂ 1 1 ∧ HasDecimalShell T₃ (β + 1) β) ∨
      (m = (nearyUpper β (.erase .b)).length ∧
        HasDecimalShell T₂ (β + 1) β ∧ HasDecimalShell T₃ (β + 1) β))
    (next_pole :
      peeledNumerator N D μ G T₂ V₂ * T₃ =
        E * μ * G * 10 ^ m * N * V₃) :
    False := by
  rcases shape with twoC_to_multi | longC_to_singleton | bSingleton_to_singleton
  · obtain ⟨m_eq, T₂_shell, T₃_shell⟩ := twoC_to_multi
    have m_ne := peeledMultiPole_length_ne_two E_unit G_unit μ_unit N_unit D_unit
      V₂_unit V₃_unit T₂_shell T₃_shell next_pole
    exact m_ne m_eq
  · obtain ⟨m_eq, T₂_shell, T₃_shell⟩ := longC_to_singleton
    have length_lower := peeledMultiToSingleton_beta_add_three_le E_unit G_unit μ_unit
      N_unit D_unit V₂_unit V₃_unit T₂_shell T₃_shell next_pole
    omega
  · obtain ⟨m_eq, T₂_shell, T₃_shell⟩ := bSingleton_to_singleton
    have b_pole :
        peeledNumerator N D μ G T₂ V₂ * T₃ =
          E * μ * G * 10 ^ (nearyUpper β (.erase .b)).length * N * V₃ := by
      simpa only [m_eq] using next_pole
    exact peeledSingletonToSingleton_impossible .b β_large E_unit G_unit μ_unit
      N_unit D_unit V₂_unit V₃_unit T₂_shell T₃_shell b_pole

end MatrixMortality.DecimalSetterDepth
