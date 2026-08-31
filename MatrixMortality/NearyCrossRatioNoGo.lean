import MatrixMortality.NearySideNormal

/-!
# Projective cross-ratio obstruction for binary face factorizations

Four invertible payloads on one binary cube face inherit proportional right cross ratios from
every scalar-weighted edge factorization.  None of the three pairings of the four ordinary
Neary roles has this property when the tag body is nonempty.
-/

namespace MatrixMortality

open scoped Matrix

namespace NearyCrossRatioNoGo

/-- A scalar-weighted factorization of a four-element face through two common right factors
produces proportional right cross ratios.  Only a right inverse of the first factor is needed. -/
theorem factorizedFace_has_proportional_rightQuotients
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [Field R]
    (P Q X₀ X₁ X₀Inv : Square ι R) (a b c d : R)
    (a_ne : a ≠ 0) (b_ne : b ≠ 0) (c_ne : c ≠ 0) (d_ne : d ≠ 0)
    (X₀Inv_right : X₀ * X₀Inv = 1) :
    ∃ U V : Square ι R, ∃ κ : R,
      (a • (P * X₀)) * U = b • (P * X₁) ∧
      (c • (Q * X₀)) * V = d • (Q * X₁) ∧
      U = κ • V := by
  refine ⟨(b / a) • (X₀Inv * X₁), (d / c) • (X₀Inv * X₁),
    (b * c) / (a * d), ?_, ?_, ?_⟩
  · calc
      (a • (P * X₀)) * ((b / a) • (X₀Inv * X₁)) =
          (a * (b / a)) • ((P * X₀) * (X₀Inv * X₁)) := by
            rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      _ = b • (P * X₁) := by
        have scalar_cancel : a * (b / a) = b := by
          field_simp [a_ne]
        rw [scalar_cancel, Matrix.mul_assoc, ← Matrix.mul_assoc X₀ X₀Inv X₁,
          X₀Inv_right, Matrix.one_mul]
  · calc
      (c • (Q * X₀)) * ((d / c) • (X₀Inv * X₁)) =
          (c * (d / c)) • ((Q * X₀) * (X₀Inv * X₁)) := by
            rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      _ = d • (Q * X₁) := by
        have scalar_cancel : c * (d / c) = d := by
          field_simp [c_ne]
        rw [scalar_cancel, Matrix.mul_assoc, ← Matrix.mul_assoc X₀ X₀Inv X₁,
          X₀Inv_right, Matrix.one_mul]
  · have scalar_eq :
        b / a = ((b * c) / (a * d)) * (d / c) := by
      field_simp [a_ne, b_ne, c_ne, d_ne]
    rw [smul_smul, scalar_eq]

/-- A nonempty tag body makes the private rule-`c` scale exceed the rule-`b` scale. -/
theorem twentySeven_lt_lowerCScale (β : Nat) (body : List TagLetter)
    (body_nonempty : body ≠ []) :
    27 < nearySideLowerCScale β body := by
  have encoded_nonempty : tagEncode β body ≠ [] :=
    (tagEncode_eq_nil_iff β body).not.mpr body_nonempty
  have encoded_length_pos : 0 < (tagEncode β body).length :=
    List.length_pos_of_ne_nil encoded_nonempty
  have power_gt_one :
      (1 : ℚ) < 3 ^ (tagEncode β body).length :=
    one_lt_pow₀ (by norm_num) encoded_length_pos.ne'
  rw [nearySideLowerCScale_eq_nine_mul, pow_succ]
  nlinarith

/-- The rule/erase pairing by tag letter has no proportional pair of right cross ratios. -/
theorem ruleErase_rightQuotients_not_proportional
    (β : Nat) (body : List TagLetter) (body_nonempty : body ≠ [])
    (U V : Square (Fin 3) ℚ) (κ : ℚ)
    (c_quotient :
      nearySideNativeRole β body (.rule .c) * U =
        nearySideNativeRole β body (.erase .c))
    (b_quotient :
      nearySideNativeRole β body (.rule .b) * V =
        nearySideNativeRole β body (.erase .b))
    (proportional : U = κ • V) : False := by
  have hU22 := congrFun (congrFun c_quotient (2 : Fin 3)) (2 : Fin 3)
  have hV22 := congrFun (congrFun b_quotient (2 : Fin 3)) (2 : Fin 3)
  have hU11 := congrFun (congrFun c_quotient (1 : Fin 3)) (1 : Fin 3)
  have hV11 := congrFun (congrFun b_quotient (1 : Fin 3)) (1 : Fin 3)
  have hProportional22 := congrFun (congrFun proportional (2 : Fin 3)) (2 : Fin 3)
  have hProportional11 := congrFun (congrFun proportional (1 : Fin 3)) (1 : Fin 3)
  simp [nearySideNativeRole, Matrix.mul_apply, Fin.sum_univ_succ] at hU22
  simp [nearySideNativeRole, Matrix.mul_apply, Fin.sum_univ_succ] at hV22
  simp [nearySideNativeRole, Matrix.mul_apply, Fin.sum_univ_succ] at hU11
  simp [nearySideNativeRole, Matrix.mul_apply, Fin.sum_univ_succ] at hV11
  simp [smul_eq_mul] at hProportional22 hProportional11
  have upper_scale_ne : nearySideUpperBScale β ≠ 0 := by
    simp [nearySideUpperBScale]
  field_simp [upper_scale_ne] at hV22
  have κ_eq : κ = 1 := by nlinarith
  have lower_scale_gt := twentySeven_lt_lowerCScale β body body_nonempty
  rw [κ_eq] at hProportional11
  nlinarith

/-- Pairing the two rules against the two erasers has no proportional right cross ratios. -/
theorem rulesErasers_rightQuotients_not_proportional
    (β : Nat) (body : List TagLetter) (body_nonempty : body ≠ [])
    (U V : Square (Fin 3) ℚ) (κ : ℚ)
    (rules_quotient :
      nearySideNativeRole β body (.rule .c) * U =
        nearySideNativeRole β body (.rule .b))
    (erasers_quotient :
      nearySideNativeRole β body (.erase .c) * V =
        nearySideNativeRole β body (.erase .b))
    (proportional : U = κ • V) : False := by
  have hU22 := congrFun (congrFun rules_quotient (2 : Fin 3)) (2 : Fin 3)
  have hV22 := congrFun (congrFun erasers_quotient (2 : Fin 3)) (2 : Fin 3)
  have hU11 := congrFun (congrFun rules_quotient (1 : Fin 3)) (1 : Fin 3)
  have hV11 := congrFun (congrFun erasers_quotient (1 : Fin 3)) (1 : Fin 3)
  have hProportional22 := congrFun (congrFun proportional (2 : Fin 3)) (2 : Fin 3)
  have hProportional11 := congrFun (congrFun proportional (1 : Fin 3)) (1 : Fin 3)
  simp [nearySideNativeRole, Matrix.mul_apply, Fin.sum_univ_succ] at hU22
  simp [nearySideNativeRole, Matrix.mul_apply, Fin.sum_univ_succ] at hV22
  simp [nearySideNativeRole, Matrix.mul_apply, Fin.sum_univ_succ] at hU11
  simp [nearySideNativeRole, Matrix.mul_apply, Fin.sum_univ_succ] at hV11
  simp [smul_eq_mul] at hProportional22 hProportional11
  have upper_scale_ne : nearySideUpperBScale β ≠ 0 := by
    simp [nearySideUpperBScale]
  have κ_eq : κ = 1 := by
    have U22_eq_V22 : U 2 2 = V 2 2 := by linarith
    have V22_ne : V 2 2 ≠ 0 := by
      intro V22_zero
      rw [V22_zero] at hV22
      norm_num at hV22
      exact upper_scale_ne hV22.symm
    have scaled_eq : V 2 2 * 1 = V 2 2 * κ := by
      calc
        V 2 2 * 1 = V 2 2 := mul_one _
        _ = U 2 2 := U22_eq_V22.symm
        _ = κ * V 2 2 := hProportional22
        _ = V 2 2 * κ := mul_comm _ _
    exact (mul_left_cancel₀ V22_ne scaled_eq).symm
  have lower_scale_gt := twentySeven_lt_lowerCScale β body body_nonempty
  rw [κ_eq] at hProportional11
  nlinarith

/-- The crossed rule/erase pairing has no proportional pair of right cross ratios. -/
theorem crossed_rightQuotients_not_proportional
    (β : Nat) (body : List TagLetter) (body_nonempty : body ≠ [])
    (U V : Square (Fin 3) ℚ) (κ : ℚ)
    (left_quotient :
      nearySideNativeRole β body (.rule .c) * U =
        nearySideNativeRole β body (.erase .b))
    (right_quotient :
      nearySideNativeRole β body (.erase .c) * V =
        nearySideNativeRole β body (.rule .b))
    (proportional : U = κ • V) : False := by
  have hU22 := congrFun (congrFun left_quotient (2 : Fin 3)) (2 : Fin 3)
  have hV22 := congrFun (congrFun right_quotient (2 : Fin 3)) (2 : Fin 3)
  have hU11 := congrFun (congrFun left_quotient (1 : Fin 3)) (1 : Fin 3)
  have hV11 := congrFun (congrFun right_quotient (1 : Fin 3)) (1 : Fin 3)
  have hProportional22 := congrFun (congrFun proportional (2 : Fin 3)) (2 : Fin 3)
  have hProportional11 := congrFun (congrFun proportional (1 : Fin 3)) (1 : Fin 3)
  simp [nearySideNativeRole, Matrix.mul_apply, Fin.sum_univ_succ] at hU22
  simp [nearySideNativeRole, Matrix.mul_apply, Fin.sum_univ_succ] at hV22
  simp [nearySideNativeRole, Matrix.mul_apply, Fin.sum_univ_succ] at hU11
  simp [nearySideNativeRole, Matrix.mul_apply, Fin.sum_univ_succ] at hV11
  simp [smul_eq_mul] at hProportional22 hProportional11
  have upper_scale_ne : nearySideUpperBScale β ≠ 0 := by
    simp [nearySideUpperBScale]
  have κ_eq : κ = 1 := by
    have U22_eq_V22 : U 2 2 = V 2 2 := by linarith
    have V22_ne : V 2 2 ≠ 0 := by
      intro V22_zero
      rw [V22_zero] at hV22
      norm_num at hV22
      exact upper_scale_ne hV22.symm
    have scaled_eq : V 2 2 * 1 = V 2 2 * κ := by
      calc
        V 2 2 * 1 = V 2 2 := mul_one _
        _ = U 2 2 := U22_eq_V22.symm
        _ = κ * V 2 2 := hProportional22
        _ = V 2 2 * κ := mul_comm _ _
    exact (mul_left_cancel₀ V22_ne scaled_eq).symm
  have lower_scale_gt := twentySeven_lt_lowerCScale β body body_nonempty
  rw [κ_eq] at hProportional11
  nlinarith

end NearyCrossRatioNoGo

end MatrixMortality
