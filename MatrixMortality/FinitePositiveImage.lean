import Mathlib.GroupTheory.OrderOfElement

/-!
# Positive generation in finite group images

A multiplicatively closed subset of a finite group contains inverses. Hence a set which
generates a finite group also generates it without inverse letters.
-/

namespace MatrixMortality.FinitePositiveImage

variable {G : Type*} [Group G] [Finite G]

/-- Every submonoid of a finite group contains the inverse of each of its elements. -/
theorem Submonoid.inv_mem_of_finite (S : Submonoid G) {element : G}
    (member : element ∈ S) :
    element⁻¹ ∈ S := by
  have inverse_power : element⁻¹ ∈ Submonoid.powers element := by
    apply mem_powers_iff_mem_zpowers.mpr
    exact Subgroup.mem_zpowers_iff.mpr ⟨-1, by simp⟩
  obtain ⟨exponent, power_eq⟩ :=
    (Submonoid.mem_powers_iff element⁻¹ element).mp inverse_power
  rw [← power_eq]
  exact S.pow_mem member exponent

/-- A group-generating set in a finite group already generates the whole positive monoid. -/
theorem mclosure_eq_top_of_group_closure_eq_top
    {generators : Set G} (generates : Subgroup.closure generators = ⊤) :
    Submonoid.closure generators = ⊤ := by
  rw [← Subgroup.closure_toSubmonoid_of_finite, generates]
  rfl

end MatrixMortality.FinitePositiveImage
