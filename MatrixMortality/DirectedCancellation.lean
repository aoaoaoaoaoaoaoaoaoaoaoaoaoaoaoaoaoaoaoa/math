import MatrixMortality.PositiveFreeCancellation

/-!
# Directed cancellation in finite-dimensional scalar carriers

A finite-dimensional algebra cannot faithfully absorb the oriented relation `push * pop = 1`:
direct finiteness forces the reverse relation. Even zero-language absorption collapses when the
relevant two-sided zero contexts separate carrier elements projectively.
-/

namespace MatrixMortality

namespace DirectedCancellation

/-- Exact scalar values in all two-sided algebra contexts distinguish carrier elements. This is
the defining separation property of the syntactic algebra of a rational series. -/
def ScalarContextFaithful
    {K A : Type*} [Field K] [Ring A] [Algebra K A]
    (observe : A →ₗ[K] K) : Prop :=
  ∀ left right : A,
    (∀ before after : A,
      observe (before * left * after) = observe (before * right * after)) →
      left = right

/-- Every finite-dimensional algebra over a field is directly finite: a one-sided inverse is
automatically two-sided. -/
theorem mul_eq_one_reverse_of_finiteDimensional
    {K A : Type*} [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    {left right : A} (forward : left * right = 1) :
    right * left = 1 := by
  have left_surjective : Function.Surjective (LinearMap.mulLeft K left) := by
    intro value
    refine ⟨right * value, ?_⟩
    simp only [LinearMap.mulLeft_apply, ← mul_assoc, forward, one_mul]
  have left_injective : Function.Injective (LinearMap.mulLeft K left) :=
    LinearMap.injective_iff_surjective.mpr left_surjective
  apply left_injective
  change left * (right * left) = left * 1
  rw [← mul_assoc, forward, one_mul, mul_one]

/-- A finite-dimensional context-faithful scalar carrier which absorbs one oriented
cancellation in every context must absorb the reverse cancellation too. -/
theorem reverse_value_context_cancellation_of_forward
    {K A : Type*} [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (observe : A →ₗ[K] K) (push pop : A)
    (faithful : ScalarContextFaithful observe)
    (forward : ∀ before after : A,
      observe (before * (push * pop) * after) = observe (before * after)) :
    ∀ before after : A,
      observe (before * (pop * push) * after) = observe (before * after) := by
  have cancel : push * pop = 1 := by
    apply faithful
    intro before after
    simpa only [mul_one, mul_assoc] using forward before after
  have reverse : pop * push = 1 :=
    mul_eq_one_reverse_of_finiteDimensional (K := K) cancel
  intro before after
  rw [reverse, mul_one]

/-- Two carrier elements have the same zero status in every selected two-sided context. The
context set can be the complete word monoid or a restricted stable source domain. -/
def ZeroContextEquivalent
    {K A : Type*} [Field K] [Ring A] [Algebra K A]
    (observe : A →ₗ[K] K) (contexts : Set A) (left right : A) : Prop :=
  ∀ before ∈ contexts, ∀ after ∈ contexts,
    observe (before * left * after) = 0 ↔
      observe (before * right * after) = 0

/-- The selected zero contexts distinguish carrier elements up to a nonzero scalar. -/
def ZeroContextsProjectivelyFaithful
    {K A : Type*} [Field K] [Ring A] [Algebra K A]
    (observe : A →ₗ[K] K) (contexts : Set A) : Prop :=
  ∀ left right : A,
    ZeroContextEquivalent observe contexts left right →
      ∃ scale : K, scale ≠ 0 ∧ left = scale • right

/-- Even preservation of zeros alone forces reverse cancellation when the relevant zero
contexts separate carrier elements projectively. -/
theorem reverse_zero_context_cancellation_of_forward
    {K A : Type*} [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (observe : A →ₗ[K] K) (contexts : Set A) (push pop : A)
    (faithful : ZeroContextsProjectivelyFaithful observe contexts)
    (forward : ZeroContextEquivalent observe contexts (push * pop) 1) :
    ZeroContextEquivalent observe contexts (pop * push) 1 := by
  obtain ⟨scale, scale_ne, cancel⟩ := faithful (push * pop) 1 forward
  have scaled_forward : (scale⁻¹ • push) * pop = 1 := by
    rw [smul_mul_assoc, cancel]
    simp [scale_ne]
  have scaled_reverse : pop * (scale⁻¹ • push) = 1 :=
    mul_eq_one_reverse_of_finiteDimensional (K := K) scaled_forward
  have reverse : pop * push = scale • (1 : A) := by
    calc
      pop * push = scale • (pop * (scale⁻¹ • push)) := by
        simp [scale_ne]
      _ = scale • (1 : A) := by rw [scaled_reverse]
  intro before _ after _
  rw [reverse]
  simp [scale_ne]

/-- If one ordered product is a nonzero scalar identity, finite dimension forces the reverse
product to have the same scalar value and hence the same zero contexts as the identity. -/
theorem reverse_zero_context_cancellation_of_smul_one
    {K A : Type*} [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (observe : A →ₗ[K] K) (contexts : Set A) (push pop : A) (scale : K)
    (scale_ne : scale ≠ 0) (forward : push * pop = scale • (1 : A)) :
    ZeroContextEquivalent observe contexts (pop * push) 1 := by
  have scaled_forward : (scale⁻¹ • push) * pop = 1 := by
    rw [smul_mul_assoc, forward]
    simp [scale_ne]
  have scaled_reverse : pop * (scale⁻¹ • push) = 1 :=
    mul_eq_one_reverse_of_finiteDimensional (K := K) scaled_forward
  have reverse : pop * push = scale • (1 : A) := by
    calc
      pop * push = scale • (pop * (scale⁻¹ • push)) := by
        simp [scale_ne]
      _ = scale • (1 : A) := by rw [scaled_reverse]
  intro before _ after _
  rw [reverse]
  simp [scale_ne]

/-- Any context family which distinguishes the reverse ordered product from the identity also
forces the forward ordered product away from every nonzero scalar identity. -/
theorem asymmetric_zero_context_cancellation_not_smul_one
    {K A : Type*} [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (observe : A →ₗ[K] K) (contexts : Set A) (push pop : A)
    (reverse_separated :
      ¬ZeroContextEquivalent observe contexts (pop * push) 1) :
    ∀ scale : K, scale ≠ 0 → push * pop ≠ scale • (1 : A) := by
  intro scale scale_ne forward
  exact reverse_separated
    (reverse_zero_context_cancellation_of_smul_one
      observe contexts push pop scale scale_ne forward)

/-- An oriented zero-language cancellation which really distinguishes the reverse word must use
nonprojective blindness in its relevant context family. -/
theorem asymmetric_zero_context_cancellation_forces_projective_blindness
    {K A : Type*} [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (observe : A →ₗ[K] K) (contexts : Set A) (push pop : A)
    (forward : ZeroContextEquivalent observe contexts (push * pop) 1)
    (reverse_separated :
      ¬ZeroContextEquivalent observe contexts (pop * push) 1) :
    ¬ZeroContextsProjectivelyFaithful observe contexts := by
  intro faithful
  exact reverse_separated
    (reverse_zero_context_cancellation_of_forward observe contexts push pop faithful forward)

end DirectedCancellation

end MatrixMortality
