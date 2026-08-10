import MatrixMortality.LinearRepresentation

/-!
# Positive reset dimension tax

A residual-local reverse queue cannot use two full positive prepend cylinders and faithfully
distinguish the rule output from the empty queue.  Cylinder fullness forces both data maps to be
invertible; the single legal state `qb` then makes the two rule equations collide.
-/

namespace MatrixMortality

open scoped Matrix

namespace PositiveResetNoGo

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- Equality of nonzero projective scalings, stated without quotienting the ambient vector space. -/
def SameRay (left right : V) : Prop :=
  ∃ scalar : ℚ, scalar ≠ 0 ∧ left = scalar • right

theorem sameRay_refl (vector : V) : SameRay vector vector := by
  exact ⟨1, one_ne_zero, (one_smul ℚ vector).symm⟩

theorem sameRay_symm {left right : V} (same : SameRay left right) :
    SameRay right left := by
  obtain ⟨scalar, scalar_ne, rfl⟩ := same
  refine ⟨scalar⁻¹, inv_ne_zero scalar_ne, ?_⟩
  simp [scalar_ne]

theorem sameRay_trans {first second third : V}
    (first_second : SameRay first second) (second_third : SameRay second third) :
    SameRay first third := by
  obtain ⟨firstScalar, firstScalar_ne, first_eq⟩ := first_second
  obtain ⟨secondScalar, secondScalar_ne, second_eq⟩ := second_third
  refine ⟨firstScalar * secondScalar, mul_ne_zero firstScalar_ne secondScalar_ne, ?_⟩
  rw [first_eq, second_eq, smul_smul]

theorem sameRay_cancel (map : V →ₗ[ℚ] V) (injective : Function.Injective map)
    {left right : V} (same : SameRay (map left) (map right)) :
    SameRay left right := by
  obtain ⟨scalar, scalar_ne, equal⟩ := same
  refine ⟨scalar, scalar_ne, injective ?_⟩
  simpa using equal

theorem sameRay_right_mem_range (map : V →ₗ[ℚ] V) {left right : V}
    (same : SameRay (map left) right) : right ∈ LinearMap.range map := by
  obtain ⟨scalar, scalar_ne, equal⟩ := same
  refine ⟨scalar⁻¹ • left, ?_⟩
  rw [map.map_smul, equal, smul_smul]
  simp [scalar_ne]

/-- If one legal prepend cylinder spans the finite-dimensional state space, its data map is
invertible on that space. -/
theorem injective_of_cylinder_span [FiniteDimensional ℚ V]
    (map : V →ₗ[ℚ] V) (state : List Bool → V) (letter : Bool)
    (prepend : ∀ word, SameRay (map (state word)) (state (letter :: word)))
    (full : Submodule.span ℚ (Set.range fun word => state (letter :: word)) = ⊤) :
    Function.Injective map := by
  apply LinearMap.injective_iff_surjective.mpr
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← full]
  apply Submodule.span_le.mpr
  intro vector member
  obtain ⟨word, rfl⟩ := member
  exact sameRay_right_mem_range map (prepend word)

/-- Full positive prepend cylinders force the `b`-rule and `c`-rule views of the legal queue
`qb` to identify the persistent states of `q` and `ε`.  `false` is `b` and `true` is `c`. -/
theorem positiveReset_collision [FiniteDimensional ℚ V]
    (q : List Bool) (state : List Bool → V)
    (dataB dataC toggle : V →ₗ[ℚ] V)
    (eraseB : ∀ word, SameRay (dataB (state word)) (state (false :: word)))
    (eraseC : ∀ word, SameRay (dataC (state word)) (state (true :: word)))
    (ruleB : ∀ word,
      SameRay (dataB (toggle (state (word ++ [false])))) (state (false :: word)))
    (ruleC : ∀ word,
      SameRay
        (dataC (toggle (state (word ++ q ++ [false]))))
        (state (true :: word)))
    (fullB : Submodule.span ℚ (Set.range fun word => state (false :: word)) = ⊤)
    (fullC : Submodule.span ℚ (Set.range fun word => state (true :: word)) = ⊤) :
    SameRay (state q) (state []) := by
  have dataB_injective :=
    injective_of_cylinder_span dataB state false eraseB fullB
  have dataC_injective :=
    injective_of_cylinder_span dataC state true eraseC fullC
  let critical := state (q ++ [false])
  have ruleB_at_critical :
      SameRay (dataB (toggle critical)) (state (false :: q)) := by
    simpa [critical] using ruleB q
  have eraseB_at_q : SameRay (dataB (state q)) (state (false :: q)) := eraseB q
  have toggle_to_q : SameRay (toggle critical) (state q) :=
    sameRay_cancel dataB dataB_injective
      (sameRay_trans ruleB_at_critical (sameRay_symm eraseB_at_q))
  have ruleC_at_critical :
      SameRay (dataC (toggle critical)) (state [true]) := by
    simpa [critical] using ruleC []
  have eraseC_at_empty : SameRay (dataC (state [])) (state [true]) := eraseC []
  have toggle_to_empty : SameRay (toggle critical) (state []) :=
    sameRay_cancel dataC dataC_injective
      (sameRay_trans ruleC_at_critical (sameRay_symm eraseC_at_empty))
  exact sameRay_trans (sameRay_symm toggle_to_q) toggle_to_empty

/-! ## Rank-two kernel bifurcation -/

/-- A route difference confined to a common data kernel survives toggles only until the next data
action. -/
theorem commonKernel_route_erased
    (kernel : Submodule ℚ V) (dataB dataC toggle : V →ₗ[ℚ] V)
    (toggle_stable : ∀ vector ∈ kernel, toggle vector ∈ kernel)
    (kernel_le_dataB : kernel ≤ LinearMap.ker dataB)
    (kernel_le_dataC : kernel ≤ LinearMap.ker dataC)
    (difference : V) (difference_mem : difference ∈ kernel) (toggles : Nat) :
    dataB ((toggle : V → V)^[toggles] difference) = 0 ∧
      dataC ((toggle : V → V)^[toggles] difference) = 0 := by
  have iterate_mem : (toggle : V → V)^[toggles] difference ∈ kernel := by
    induction toggles with
    | zero => exact difference_mem
    | succ toggles induction =>
        rw [Function.iterate_succ_apply']
        exact toggle_stable _ induction
  exact ⟨LinearMap.mem_ker.mp (kernel_le_dataB iterate_mem),
    LinearMap.mem_ker.mp (kernel_le_dataC iterate_mem)⟩

/-- Quotient by the first coordinate axis. -/
def leftKernelQuotient (point : Fin 3 → ℚ) : Fin 2 → ℚ :=
  ![point 1, point 2]

/-- Quotient by the second coordinate axis. -/
def rightKernelQuotient (point : Fin 3 → ℚ) : Fin 2 → ℚ :=
  ![point 0, point 2]

/-- Bilinear intersection of the two transverse rank-two projective fibres. -/
def bilinearFibrePoint (u v r s : ℚ) : Fin 3 → ℚ :=
  ![r * v, u * s, v * s]

/-- Two transverse rank-two quotient targets determine one projective point. The nonzero final
coordinates exclude the exceptional lines through the two kernel points. -/
theorem sameRay_bilinearFibrePoint
    (point : Fin 3 → ℚ) (u v r s : ℚ) (s_ne : s ≠ 0)
    (left_same : SameRay (leftKernelQuotient point) ![u, v])
    (right_same : SameRay (rightKernelQuotient point) ![r, s]) :
    SameRay point (bilinearFibrePoint u v r s) := by
  obtain ⟨leftScale, leftScale_ne, left_eq⟩ := left_same
  obtain ⟨rightScale, _, right_eq⟩ := right_same
  have point_one : point 1 = leftScale * u := by
    simpa [leftKernelQuotient] using congrFun left_eq 0
  have point_two_left : point 2 = leftScale * v := by
    simpa [leftKernelQuotient] using congrFun left_eq 1
  have point_zero : point 0 = rightScale * r := by
    simpa [rightKernelQuotient] using congrFun right_eq 0
  have point_two_right : point 2 = rightScale * s := by
    simpa [rightKernelQuotient] using congrFun right_eq 1
  have scale_relation : rightScale * s = leftScale * v := by
    exact point_two_right.symm.trans point_two_left
  have rightScale_eq : rightScale = leftScale * v / s := by
    exact (eq_div_iff s_ne).2 scale_relation
  refine ⟨leftScale / s, div_ne_zero leftScale_ne s_ne, ?_⟩
  funext coordinate
  fin_cases coordinate
  · change point 0 = leftScale / s * (r * v)
    rw [point_zero, rightScale_eq]
    field_simp
    ring
  · change point 1 = leftScale / s * (u * s)
    rw [point_one]
    field_simp
    ring
  · change point 2 = leftScale / s * (v * s)
    rw [point_two_left]
    field_simp
    ring

/-! ## Fullness of the standard homogeneous radix cylinder -/

/-- Three states in one prepend cylinder of a homogeneous radix queue code. -/
def radixCylinder (K : Type*) [CommRing K] (base digitB digitC digitA : K) :
    Square (Fin 3) K :=
  !![digitA, digitA + base * digitB, digitA + base * digitC;
     base, base ^ 2, base ^ 2;
     1, 1, 1]

/-- Exact cylinder determinant. -/
theorem radixCylinder_det (K : Type*) [CommRing K] (base digitB digitC digitA : K) :
    (radixCylinder K base digitB digitC digitA).det =
      base ^ 2 * (base - 1) * (digitB - digitC) := by
  rw [Matrix.det_fin_three]
  simp [radixCylinder, Matrix.vecHead, Matrix.vecTail]
  ring

/-- Every ordinary nondegenerate radix prepend cylinder spans three vector dimensions. -/
theorem radixCylinder_det_ne_zero (base digitB digitC digitA : ℚ)
    (base_ne_zero : base ≠ 0) (base_ne_one : base ≠ 1)
    (digits_ne : digitB ≠ digitC) :
    (radixCylinder ℚ base digitB digitC digitA).det ≠ 0 := by
  rw [radixCylinder_det]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 base_ne_zero) (sub_ne_zero.mpr base_ne_one))
    (sub_ne_zero.mpr digits_ne)

end PositiveResetNoGo

end MatrixMortality
