import MatrixMortality.ParabolicEvenBody

/-!
# Trailing arithmetic for the phase-zero right-c bridge

An exact trailing run of `c` letters exposes the 3-adic content of the complement coordinate.
The same coordinates split the residual core into two affine `z` pencils whose cross-resultant
factors completely.
-/

namespace MatrixMortality.ParabolicBlade

/-- Appending a last `b` and then `h` copies of `c` exposes the exact power of three in the
complement coordinate. -/
theorem tagComplementCode_append_b_c_run (stem : List TagLetter) (h : Nat) :
    tagComplementCode (stem ++ .b :: List.replicate h .c) =
      3 ^ (h + 1) * (81 * tagComplementCode stem + 13) := by
  rw [show stem ++ .b :: List.replicate h .c =
    (stem ++ [.b]) ++ List.replicate h .c by simp]
  induction h with
  | zero =>
      rw [List.replicate_zero, List.append_nil, tagComplementCode_append_b]
      norm_num
      ring
  | succ h induction =>
      rw [List.replicate_succ', ← List.append_assoc, tagComplementCode_append_c, induction,
        pow_succ]
      ring

/-- The cofactor left after removing the exact trailing power of three is prime to three. -/
theorem tagComplementCode_b_cofactor_mod_three (stem : List TagLetter) :
    (81 * tagComplementCode stem + 13) % 3 = 1 := by omega

/-- The complement correction is twelve times this primitive affine `z` pencil. -/
def bZeroBDefectCOneComplementPencil {R : Type*} [CommRing R] (x y z : R) : R :=
  (52633465128 * x + 51726485736 * y + 35202967090) * z +
    4920673878 * x + 4833755406 * y + 3153182195

/-- The coefficient of `z` in the all-`c` root pencil. -/
def bZeroBDefectCOneRootSlope {R : Type*} [CommRing R] (x : R) : R :=
  119911680 * x - 25766986436

/-- The constant coefficient in the all-`c` root pencil. -/
def bZeroBDefectCOneRootConstant {R : Type*} [CommRing R] (x : R) : R :=
  11209824 * x - 2408152393

/-- The coefficient of `z` in the primitive complement pencil. -/
def bZeroBDefectCOneComplementSlope {R : Type*} [CommRing R] (x y : R) : R :=
  52633465128 * x + 51726485736 * y + 35202967090

/-- The constant coefficient in the primitive complement pencil. -/
def bZeroBDefectCOneComplementConstantPencil {R : Type*} [CommRing R] (x y : R) : R :=
  4920673878 * x + 4833755406 * y + 3153182195

/-- The coefficient-positive complement core has a common factor of twelve. -/
theorem bZeroBDefectCOneComplementCore_eq_twelve_pencil
    {R : Type*} [CommRing R] (x y z : R) :
    bZeroBDefectCOneComplementCore x y z =
      12 * bZeroBDefectCOneComplementPencil x y z := by
  unfold bZeroBDefectCOneComplementCore bZeroBDefectCOneComplementPencil
  ring

/-- The all-`c` root pencil is affine in `z` with the displayed coefficients. -/
theorem bZeroBDefectCOneRootPencil_collect
    {R : Type*} [CommRing R] (x z : R) :
    bZeroBDefectCOneRootPencil x z =
      bZeroBDefectCOneRootSlope x * z + bZeroBDefectCOneRootConstant x := by
  unfold bZeroBDefectCOneRootPencil bZeroBDefectCOneRootSlope
    bZeroBDefectCOneRootConstant
  ring

/-- The primitive complement pencil is affine in `z` with the displayed coefficients. -/
theorem bZeroBDefectCOneComplementPencil_collect
    {R : Type*} [CommRing R] (x y z : R) :
    bZeroBDefectCOneComplementPencil x y z =
      bZeroBDefectCOneComplementSlope x y * z +
        bZeroBDefectCOneComplementConstantPencil x y := by
  unfold bZeroBDefectCOneComplementPencil bZeroBDefectCOneComplementSlope
    bZeroBDefectCOneComplementConstantPencil
  ring

/-- Cross-resultant of the two trailing affine pencils. -/
theorem bZeroBDefectCOneTrailing_resultant (x y : ℤ) :
    bZeroBDefectCOneRootSlope x * bZeroBDefectCOneComplementConstantPencil x y -
        bZeroBDefectCOneComplementSlope x y * bZeroBDefectCOneRootConstant x =
      2 * 3 ^ 12 * (48 * x - 3029) *
        (674088 * x - 4333144 * y - 1095244575) := by
  unfold bZeroBDefectCOneRootSlope bZeroBDefectCOneComplementConstantPencil
    bZeroBDefectCOneComplementSlope bZeroBDefectCOneRootConstant
  ring

/-- Scaling both code coordinates by a trailing power isolates the sole unscaled wait term. -/
theorem bZeroBDefectCOneCodeCore_trailing_decomposition
    {R : Type*} [CommRing R] (r S D x y z : R) :
    bZeroBDefectCOneCodeCore (r * S) (r * S - 1 - r * D) x y z =
      r * ((72 * y - 9) * bZeroBDefectCOneRootPencil x z * S +
        12 * bZeroBDefectCOneComplementPencil x y z * D) -
        (8 * y - 9) * bZeroBDefectCOneRootPencil x z := by
  rw [bZeroBDefectCOneCodeCore_thin_decomposition,
    bZeroBDefectCOneComplementCore_eq_twelve_pencil]
  unfold bZeroBDefectCOneWaitFactor
  ring

end MatrixMortality.ParabolicBlade
