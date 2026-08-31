import MatrixMortality.MatrixSemigroup

/-!
# Rational affine group orbits

This file isolates the algebra behind the affine branch of projective group incidence.  The
translation kernel corrects every orbit hit modulo that kernel to an exact hit.  When the kernel
is trivial, one nontranslation element forces a common rational fixed point.
-/

namespace MatrixMortality.AffineGroupOrbit

/-- An invertible rational affine map `x ↦ multiplier * x + offset`. -/
@[ext]
structure RationalAffineUnit where
  /-- The nonzero rational linear coefficient. -/
  multiplier : ℚˣ
  /-- The rational translation coefficient. -/
  offset : ℚ

namespace RationalAffineUnit

instance : One RationalAffineUnit := ⟨⟨1, 0⟩⟩

instance : Mul RationalAffineUnit where
  mul left right :=
    ⟨left.multiplier * right.multiplier,
      left.multiplier.1 * right.offset + left.offset⟩

instance : Inv RationalAffineUnit where
  inv affine :=
    ⟨affine.multiplier⁻¹, -affine.multiplier⁻¹.1 * affine.offset⟩

@[simp]
theorem multiplier_one : (1 : RationalAffineUnit).multiplier = 1 := rfl

@[simp]
theorem offset_one : (1 : RationalAffineUnit).offset = 0 := rfl

@[simp]
theorem multiplier_mul (left right : RationalAffineUnit) :
    (left * right).multiplier = left.multiplier * right.multiplier := rfl

@[simp]
theorem offset_mul (left right : RationalAffineUnit) :
    (left * right).offset = left.multiplier.1 * right.offset + left.offset := rfl

@[simp]
theorem multiplier_inv (affine : RationalAffineUnit) :
    affine⁻¹.multiplier = affine.multiplier⁻¹ := rfl

@[simp]
theorem offset_inv (affine : RationalAffineUnit) :
    affine⁻¹.offset = -affine.multiplier⁻¹.1 * affine.offset := rfl

instance : Group RationalAffineUnit where
  mul_assoc left middle right := by
    ext <;> simp <;> ring
  one_mul affine := by
    ext <;> simp
  mul_one affine := by
    ext <;> simp
  inv_mul_cancel affine := by
    ext
    · simp
    · simp

/-- Evaluation of an affine group element. -/
def act (affine : RationalAffineUnit) (point : ℚ) : ℚ :=
  affine.multiplier.1 * point + affine.offset

@[simp]
theorem act_one (point : ℚ) : act 1 point = point := by
  simp [act]

@[simp]
theorem act_mul (left right : RationalAffineUnit) (point : ℚ) :
    act (left * right) point = act left (act right point) := by
  simp [act]
  ring

/-- Translation by a rational displacement. -/
def translation (displacement : ℚ) : RationalAffineUnit :=
  ⟨1, displacement⟩

@[simp]
theorem multiplier_translation (displacement : ℚ) :
    (translation displacement).multiplier = 1 := rfl

@[simp]
theorem offset_translation (displacement : ℚ) :
    (translation displacement).offset = displacement := rfl

@[simp]
theorem act_translation (displacement point : ℚ) :
    act (translation displacement) point = point + displacement := by
  simp [act, translation, add_comm]

@[simp]
theorem translation_mul (left right : ℚ) :
    translation left * translation right = translation (left + right) := by
  ext <;> simp [translation, add_comm]

@[simp]
theorem translation_zero : translation 0 = 1 := rfl

@[simp]
theorem translation_inv (displacement : ℚ) :
    (translation displacement)⁻¹ = translation (-displacement) := by
  ext <;> simp [translation]

/-- Conjugating a translation multiplies its displacement by the affine multiplier. -/
theorem conjugate_translation (affine : RationalAffineUnit) (displacement : ℚ) :
    affine * translation displacement * affine⁻¹ =
      translation (affine.multiplier.1 * displacement) := by
  ext <;> simp [translation]

/-- An affine map with unit multiplier is its translation by the stored offset. -/
theorem eq_translation_of_multiplier_eq_one
    {affine : RationalAffineUnit} (multiplier_one : affine.multiplier = 1) :
    affine = translation affine.offset := by
  ext
  · simp [multiplier_one, translation]
  · rfl

end RationalAffineUnit

open RationalAffineUnit

/-- Rational translations contained in an affine subgroup. -/
def translationKernel (group : Subgroup RationalAffineUnit) : AddSubgroup ℚ where
  carrier := {displacement | translation displacement ∈ group}
  zero_mem' := by simp
  add_mem' {left right} left_mem right_mem := by
    change translation (left + right) ∈ group
    rw [← translation_mul]
    exact group.mul_mem left_mem right_mem
  neg_mem' {displacement} displacement_mem := by
    change translation (-displacement) ∈ group
    rw [← translation_inv]
    exact group.inv_mem displacement_mem

@[simp]
theorem mem_translationKernel_iff
    (group : Subgroup RationalAffineUnit) (displacement : ℚ) :
    displacement ∈ translationKernel group ↔ translation displacement ∈ group :=
  Iff.rfl

/-- The translation kernel is stable under every multiplier in the affine subgroup. -/
theorem multiplier_mul_mem_translationKernel
    (group : Subgroup RationalAffineUnit) {affine : RationalAffineUnit}
    (affine_mem : affine ∈ group) {displacement : ℚ}
    (displacement_mem : displacement ∈ translationKernel group) :
    affine.multiplier.1 * displacement ∈ translationKernel group := by
  rw [mem_translationKernel_iff, ← conjugate_translation]
  exact group.mul_mem (group.mul_mem affine_mem displacement_mem) (group.inv_mem affine_mem)

/-- A hit modulo the translation kernel corrects inside the group to an exact affine-orbit hit. -/
theorem exists_exact_hit_iff_exists_hit_mod_translationKernel
    (group : Subgroup RationalAffineUnit) (source target : ℚ) :
    (∃ affine ∈ group, act affine source = target) ↔
      ∃ affine ∈ group, target - act affine source ∈ translationKernel group := by
  constructor
  · rintro ⟨affine, affine_mem, hit⟩
    exact ⟨affine, affine_mem, by simp [hit]⟩
  · rintro ⟨affine, affine_mem, defect_mem⟩
    let correction := translation (target - act affine source)
    refine ⟨correction * affine,
      group.mul_mem (show correction ∈ group from defect_mem) affine_mem, ?_⟩
    simp [correction, act_mul]

private theorem eq_of_multiplier_eq_of_trivial_translationKernel
    (group : Subgroup RationalAffineUnit)
    (kernel_trivial : translationKernel group = ⊥)
    {left right : RationalAffineUnit} (left_mem : left ∈ group) (right_mem : right ∈ group)
    (same_multiplier : left.multiplier = right.multiplier) :
    left = right := by
  let quotient := left * right⁻¹
  have quotient_mem : quotient ∈ group := group.mul_mem left_mem (group.inv_mem right_mem)
  have quotient_multiplier : quotient.multiplier = 1 := by
    simp [quotient, same_multiplier]
  have offset_mem : quotient.offset ∈ translationKernel group := by
    rw [mem_translationKernel_iff, ← eq_translation_of_multiplier_eq_one quotient_multiplier]
    exact quotient_mem
  have offset_zero : quotient.offset = 0 := by
    rw [kernel_trivial] at offset_mem
    simpa using offset_mem
  have quotient_one : quotient = 1 := by
    ext
    · change quotient.multiplier.1 = (1 : ℚˣ).1
      exact congrArg Units.val quotient_multiplier
    · simpa using offset_zero
  exact mul_inv_eq_one.mp quotient_one

/-- A trivial translation kernel makes the affine subgroup abelian. -/
theorem commute_of_translationKernel_eq_bot
    (group : Subgroup RationalAffineUnit)
    (kernel_trivial : translationKernel group = ⊥)
    {left right : RationalAffineUnit} (left_mem : left ∈ group) (right_mem : right ∈ group) :
    Commute left right := by
  apply eq_of_multiplier_eq_of_trivial_translationKernel group kernel_trivial
    (group.mul_mem left_mem right_mem) (group.mul_mem right_mem left_mem)
  simp [mul_comm]

/-- The rational fixed point of a nontranslation affine map. -/
def fixedPoint (affine : RationalAffineUnit) : ℚ :=
  affine.offset / (1 - affine.multiplier.1)

theorem act_fixedPoint
    (affine : RationalAffineUnit) (nontranslation : affine.multiplier ≠ 1) :
    act affine (fixedPoint affine) = fixedPoint affine := by
  have denominator_ne : 1 - affine.multiplier.1 ≠ 0 := by
    intro denominator_zero
    apply nontranslation
    exact Units.ext (sub_eq_zero.mp denominator_zero).symm
  simp only [act, fixedPoint]
  field_simp
  ring

/-- A nontranslation rational affine map has exactly one fixed point. -/
theorem eq_fixedPoint_of_act_eq
    (affine : RationalAffineUnit) (nontranslation : affine.multiplier ≠ 1)
    {point : ℚ} (point_fixed : act affine point = point) :
    point = fixedPoint affine := by
  have denominator_ne : 1 - affine.multiplier.1 ≠ 0 := by
    intro denominator_zero
    apply nontranslation
    exact Units.ext (sub_eq_zero.mp denominator_zero).symm
  rw [fixedPoint, eq_div_iff denominator_ne]
  dsimp [act] at point_fixed
  linarith

/-- If the translation kernel is trivial, the fixed point of one nontranslation element is
fixed by the entire affine subgroup. -/
theorem act_fixedPoint_of_translationKernel_eq_bot
    (group : Subgroup RationalAffineUnit)
    (kernel_trivial : translationKernel group = ⊥)
    {witness : RationalAffineUnit} (witness_mem : witness ∈ group)
    (nontranslation : witness.multiplier ≠ 1)
    {affine : RationalAffineUnit} (affine_mem : affine ∈ group) :
    act affine (fixedPoint witness) = fixedPoint witness := by
  have commute := commute_of_translationKernel_eq_bot group kernel_trivial
    witness_mem affine_mem
  have witness_fixed := act_fixedPoint witness nontranslation
  apply eq_fixedPoint_of_act_eq witness nontranslation
  calc
    act witness (act affine (fixedPoint witness)) =
        act (witness * affine) (fixedPoint witness) := by rw [act_mul]
    _ = act (affine * witness) (fixedPoint witness) := by rw [commute.eq]
    _ = act affine (act witness (fixedPoint witness)) := act_mul _ _ _
    _ = act affine (fixedPoint witness) := by rw [witness_fixed]

end MatrixMortality.AffineGroupOrbit
