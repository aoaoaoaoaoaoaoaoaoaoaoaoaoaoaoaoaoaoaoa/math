import MatrixMortality.PhaseFracture
import MatrixMortality.NearySideNormal

/-!
# Algebraic certificates for phase rigidity

This file isolates the finite algebra in the phase-plane obstruction.  In particular, the
line-image branch reduces to a two-dimensional pencil of affine forms.  Invariance under one
constant and one radial translation forces that pencil to forget the accumulator coordinate.
-/

namespace MatrixMortality

open scoped Matrix

namespace PhaseRigidity

/-- Affine forms `a + bt + cr`, stored in the coordinate order `(a,b,c)`. -/
abbrev AffineForm := Fin 3 → ℚ

/-- The coefficient of the accumulator coordinate `t`. -/
def tCoefficient : AffineForm →ₗ[ℚ] ℚ where
  toFun form := form 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Pullback of affine forms along `(t,r) ↦ (t+s,r)`. -/
def constantTranslation (s : ℚ) (form : AffineForm) : AffineForm :=
  ![form 0 + s * form 1, form 1, form 2]

/-- Pullback of affine forms along `(t,r) ↦ (t+cr,r)`. -/
def radialTranslation (c : ℚ) (form : AffineForm) : AffineForm :=
  ![form 0, form 1, form 2 + c * form 1]

/-- A two-dimensional affine pencil invariant under a nonzero constant translation and a
nonzero radial translation contains no `t` term.

This is the linear-fractional core of the two-translation rigidity argument.  It avoids a choice
of numerator and denominator: a target Möbius action is exactly preservation of their pencil.
-/
theorem invariant_affine_pencil_forgets_t
    (pencil : Submodule ℚ AffineForm)
    (pencil_rank : Module.finrank ℚ pencil = 2)
    (s c : ℚ) (s_ne : s ≠ 0) (c_ne : c ≠ 0)
    (constant_invariant : ∀ form ∈ pencil, constantTranslation s form ∈ pencil)
    (radial_invariant : ∀ form ∈ pencil, radialTranslation c form ∈ pencil) :
    pencil ≤ LinearMap.ker tCoefficient := by
  intro form form_mem
  by_contra t_ne
  have constant_difference :
      constantTranslation s form - form =
        (s * form 1) • (![1, 0, 0] : AffineForm) := by
    ext coordinate
    fin_cases coordinate <;> simp [constantTranslation]
  have radial_difference :
      radialTranslation c form - form =
        (c * form 1) • (![0, 0, 1] : AffineForm) := by
    ext coordinate
    fin_cases coordinate <;> simp [radialTranslation]
  have constant_mem : (![1, 0, 0] : AffineForm) ∈ pencil := by
    have difference_mem := pencil.sub_mem (constant_invariant form form_mem) form_mem
    rw [constant_difference] at difference_mem
    have scale_ne : s * form 1 ≠ 0 := mul_ne_zero s_ne t_ne
    have scaled := pencil.smul_mem (s * form 1)⁻¹ difference_mem
    rw [smul_smul, inv_mul_cancel₀ scale_ne, one_smul] at scaled
    exact scaled
  have radial_mem : (![0, 0, 1] : AffineForm) ∈ pencil := by
    have difference_mem := pencil.sub_mem (radial_invariant form form_mem) form_mem
    rw [radial_difference] at difference_mem
    have scale_ne : c * form 1 ≠ 0 := mul_ne_zero c_ne t_ne
    have scaled := pencil.smul_mem (c * form 1)⁻¹ difference_mem
    rw [smul_smul, inv_mul_cancel₀ scale_ne, one_smul] at scaled
    exact scaled
  have kernel_le : LinearMap.ker tCoefficient ≤ pencil := by
    intro candidate candidate_mem
    have t_zero : candidate 1 = 0 := candidate_mem
    have decomposition :
        candidate = candidate 0 • (![1, 0, 0] : AffineForm) +
          candidate 2 • (![0, 0, 1] : AffineForm) := by
      ext coordinate
      fin_cases coordinate <;> simp [t_zero]
    rw [decomposition]
    exact pencil.add_mem (pencil.smul_mem _ constant_mem) (pencil.smul_mem _ radial_mem)
  have coefficient_ne : tCoefficient ≠ 0 := by
    intro coefficient_zero
    have at_t := LinearMap.congr_fun coefficient_zero (![0, 1, 0] : AffineForm)
    norm_num [tCoefficient] at at_t
  have kernel_rank : Module.finrank ℚ (LinearMap.ker tCoefficient) = 2 := by
    have rank_nullity := Module.Dual.finrank_ker_add_one_of_ne_zero coefficient_ne
    rw [Module.finrank_fin_fun] at rank_nullity
    omega
  have kernel_eq : LinearMap.ker tCoefficient = pencil :=
    Submodule.eq_of_le_of_finrank_eq kernel_le (by rw [kernel_rank, pencil_rank])
  have : form ∈ LinearMap.ker tCoefficient := by rw [kernel_eq]; exact form_mem
  exact t_ne this

/-! ## Checked phase matrices -/

/-- Swap the private lower coordinate with the shared upper scale coordinate. -/
def payloadSwap : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

/-- A Neary role in the local coordinate order `(z,x,h)`. -/
def localRole (β : Nat) (body : List TagLetter) (tile : NearyTile) :
    Matrix (Fin 3) (Fin 3) ℚ :=
  payloadSwap * nearySideRole β body tile * payloadSwap

/-- The four local roles are exactly the matrices used by the phase-rigidity calculation. -/
theorem localRole_eq (β : Nat) (body : List TagLetter) :
    localRole β body (.erase .b) =
        !![1, nearySideUpperB β, 1;
           0, nearySideUpperBScale β, 0;
           0, 0, 3] ∧
      localRole β body (.rule .b) =
        !![1, nearySideUpperB β, 25;
           0, nearySideUpperBScale β, 0;
           0, 0, 27] ∧
      localRole β body (.erase .c) =
        !![1, 2, 1;
           0, 3, 0;
           0, 0, 3] ∧
      localRole β body (.rule .c) =
        !![1, 2, nearySideLowerC β body;
           0, 3, 0;
           0, 0, nearySideLowerCScale β body] := by
  repeat' apply And.intro
  all_goals
    rw [localRole, nearySideRole_eq_native]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [payloadSwap, nearySideNativeRole, Matrix.mul_apply, Matrix.vecHead,
        Fin.sum_univ_succ]

/-- The affine chart vector with coordinates
`r=h/x` and `t=(z-x-h/2)/x`, normalized by `x=1`. -/
def chartVector (t r : ℚ) : Fin 3 → ℚ := ![t + 1 + r / 2, 1, r]

/-- Closed scale of the erase-`b` action. -/
def eraseBScale (β : Nat) : ℚ := nearySideUpperBScale β

/-- Translation defect in the erase-`b` action. -/
def eraseBDefect (β : Nat) : ℚ :=
  nearySideUpperB β + 1 - eraseBScale β

/-- Erase-`c` divides `t` by three and fixes `r` projectively. -/
theorem localRole_erase_c_chart (β : Nat) (body : List TagLetter) (t r : ℚ) :
    localRole β body (.erase .c) *ᵥ chartVector t r =
      3 • chartVector (t / 3) r := by
  rw [(localRole_eq β body).2.2.1]
  ext coordinate
  fin_cases coordinate <;>
    simp [chartVector, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- Erase-`b` acts by `(t,r) ↦ ((t+d)/a,(3/a)r)` projectively. -/
theorem localRole_erase_b_chart (β : Nat) (body : List TagLetter) (t r : ℚ) :
    localRole β body (.erase .b) *ᵥ chartVector t r =
      eraseBScale β •
        chartVector ((t + eraseBDefect β) / eraseBScale β)
          ((3 / eraseBScale β) * r) := by
  rw [(localRole_eq β body).1]
  have scale_ne : eraseBScale β ≠ 0 := by
    simp [eraseBScale, nearySideUpperBScale]
  have native_scale_ne : nearySideUpperBScale β ≠ 0 := by
    simpa [eraseBScale] using scale_ne
  ext coordinate
  fin_cases coordinate
  · simp [chartVector, eraseBDefect, eraseBScale, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
    field_simp [native_scale_ne]
    ring
  · simp [chartVector, eraseBScale, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
  · simp [chartVector, eraseBScale, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
    field_simp [native_scale_ne]

/-- The fixed-width relation reduces the erase-`b` defect to `(3-q)/2`. -/
theorem eraseBDefect_eq (β : Nat) :
    eraseBDefect β = (3 - nearySideMarkerScale β) / 2 := by
  rw [eraseBDefect, eraseBScale, nearySideUpperBScale_relation]
  nlinarith [nearySideUpperB_relation β]

/-- The erase-`b` translation is nonzero at every admissible width. -/
theorem eraseBDefect_ne_zero (β : Nat) (three_le : 3 ≤ β) : eraseBDefect β ≠ 0 := by
  rw [eraseBDefect_eq]
  have scale_gt_three : (3 : ℚ) < nearySideMarkerScale β := by
    rw [nearySideMarkerScale_eq]
    have power_bound : (27 : ℕ) ≤ 3 ^ β := by
      change 3 ^ 3 ≤ 3 ^ β
      exact Nat.pow_le_pow_right (by norm_num) three_le
    exact_mod_cast (show 3 < 3 * 3 ^ β by omega)
  exact div_ne_zero (sub_ne_zero.mpr (ne_of_lt scale_gt_three)) (by norm_num)

/-! ## The two exact commutators -/

/-- Erase-`c` in affine coordinates. -/
def eraseCPoint (point : ℚ × ℚ) : ℚ × ℚ := (point.1 / 3, point.2)

/-- Inverse erase-`c` action. -/
def eraseCPointInv (point : ℚ × ℚ) : ℚ × ℚ := (3 * point.1, point.2)

/-- Erase-`b` in affine coordinates, parameterized by its scale and defect. -/
def eraseBPoint (a d : ℚ) (point : ℚ × ℚ) : ℚ × ℚ :=
  ((point.1 + d) / a, (3 / a) * point.2)

/-- Inverse erase-`b` action. -/
def eraseBPointInv (a d : ℚ) (point : ℚ × ℚ) : ℚ × ℚ :=
  (a * point.1 - d, (a / 3) * point.2)

/-- Rule/erase discrepancy for the letter `b`. -/
def discrepancyBPoint (point : ℚ × ℚ) : ℚ × ℚ :=
  (point.1 + 12 * point.2, 9 * point.2)

/-- Inverse rule/erase discrepancy for the letter `b`. -/
def discrepancyBPointInv (point : ℚ × ℚ) : ℚ × ℚ :=
  (point.1 - (4 / 3) * point.2, point.2 / 9)

/-- The erase commutator is a nonzero constant translation in `t`. -/
theorem erase_commutator (a d : ℚ) (a_ne : a ≠ 0) (point : ℚ × ℚ) :
    eraseCPoint
        (eraseBPoint a d (eraseCPointInv (eraseBPointInv a d point))) =
      (point.1 - 2 * d / (3 * a), point.2) := by
  rcases point with ⟨t, r⟩
  ext <;>
    simp [eraseCPoint, eraseBPoint, eraseCPointInv, eraseBPointInv]
  all_goals
    field_simp [a_ne]
  ring

/-- The discrepancy commutator is the radial translation `t ↦ t-(8/9)r`. -/
theorem discrepancy_commutator (point : ℚ × ℚ) :
    eraseCPoint
        (discrepancyBPoint (eraseCPointInv (discrepancyBPointInv point))) =
      (point.1 - (8 / 9) * point.2, point.2) := by
  rcases point with ⟨t, r⟩
  ext <;>
    norm_num [eraseCPoint, discrepancyBPoint, eraseCPointInv, discrepancyBPointInv]
  all_goals ring

/-! ## Rule/erase discrepancy -/

/-- Explicit inverse of erase-`b` in local homogeneous coordinates. -/
def eraseBInverse (β : Nat) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, -nearySideUpperB β / eraseBScale β, -(1 / 3);
     0, 1 / eraseBScale β, 0;
     0, 0, 1 / 3]

/-- Explicit inverse of erase-`c` in local homogeneous coordinates. -/
def eraseCInverse : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, -(2 / 3), -(1 / 3);
     0, 1 / 3, 0;
     0, 0, 1 / 3]

/-- Body-dependent expansion in the rule-`c` private coordinate. -/
def ruleCRho (β : Nat) (body : List TagLetter) : ℚ :=
  nearySideLowerCScale β body / 3

/-- Both displayed matrices really are inverses of their erase roles. -/
theorem erase_inverses (β : Nat) (body : List TagLetter) :
    eraseBInverse β * localRole β body (.erase .b) = 1 ∧
      eraseCInverse * localRole β body (.erase .c) = 1 := by
  constructor
  · rw [(localRole_eq β body).1]
    have scale_ne : eraseBScale β ≠ 0 := by
      simp [eraseBScale, nearySideUpperBScale]
    have native_scale_ne : nearySideUpperBScale β ≠ 0 := by
      simpa [eraseBScale] using scale_ne
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [eraseBInverse, eraseBScale, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals field_simp [native_scale_ne]
    all_goals ring
  · rw [(localRole_eq β body).2.2.1]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [eraseCInverse, Matrix.mul_apply, Matrix.vecHead,
        Fin.sum_univ_succ, Fin.ext_iff]

/-- The two rule/erase discrepancies are diagonal shears. -/
theorem phase_discrepancies (β : Nat) (body : List TagLetter) :
    eraseBInverse β * localRole β body (.rule .b) =
        !![1, 0, 16;
           0, 1, 0;
           0, 0, 9] ∧
      eraseCInverse * localRole β body (.rule .c) =
        !![1, 0, nearySideLowerC β body - ruleCRho β body;
           0, 1, 0;
           0, 0, ruleCRho β body] := by
  constructor
  · rw [(localRole_eq β body).2.1]
    have scale_ne : eraseBScale β ≠ 0 := by
      simp [eraseBScale, nearySideUpperBScale]
    have native_scale_ne : nearySideUpperBScale β ≠ 0 := by
      simpa [eraseBScale] using scale_ne
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [eraseBInverse, eraseBScale, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals field_simp [native_scale_ne]
    all_goals ring
  · rw [(localRole_eq β body).2.2.2]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [eraseCInverse, ruleCRho, Matrix.mul_apply, Matrix.vecTail,
        Fin.sum_univ_succ]
    all_goals ring

/-- Inverse of the fixed `b` discrepancy. -/
def discrepancyBInverse : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 0, -(16 / 9);
     0, 1, 0;
     0, 0, 1 / 9]

/-- Comparing the two discrepancies produces one shear followed by one private scaling. -/
theorem discrepancy_quotient (β : Nat) (body : List TagLetter) :
    (eraseCInverse * localRole β body (.rule .c)) * discrepancyBInverse =
      !![1, 0, (nearySideLowerC β body - ruleCRho β body - 16) / 9;
         0, 1, 0;
         0, 0, ruleCRho β body / 9] := by
  rw [(phase_discrepancies β body).2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [discrepancyBInverse, Matrix.mul_apply, Matrix.vecTail,
      Fin.sum_univ_succ]
  all_goals ring

/-- The body scale is `9·3ᴺ`, where `N` is the encoded body length. -/
theorem ruleCRho_eq (β : Nat) (body : List TagLetter) :
    ruleCRho β body = 9 * (3 : ℚ) ^ (tagEncode β body).length := by
  rw [ruleCRho, nearySideLowerCScale_eq_nine_mul, pow_succ]
  ring

/-- A nonempty body makes the private discrepancy genuinely nontrivial. -/
theorem ruleCRho_div_nine_ne_one (β : Nat) (body : List TagLetter)
    (body_nonempty : body ≠ []) : ruleCRho β body / 9 ≠ 1 := by
  rw [ruleCRho_eq]
  have encoded_nonempty : tagEncode β body ≠ [] :=
    (tagEncode_eq_nil_iff β body).not.mpr body_nonempty
  have encoded_length_pos : 0 < (tagEncode β body).length :=
    List.length_pos_of_ne_nil encoded_nonempty
  have power_gt_one : (1 : ℚ) < 3 ^ (tagEncode β body).length := by
    exact one_lt_pow₀ (by norm_num) encoded_length_pos.ne'
  norm_num
  exact ne_of_gt power_gt_one

/-- Closed value of the body-dependent rule-`c` translation. -/
theorem nearySideLowerC_eq_encoded (β : Nat) (body : List TagLetter) :
    nearySideLowerC β body =
      18 * (3 : ℚ) ^ (tagEncode β body).length +
        9 * ternaryCode (tagEncode β body) + 7 := by
  rw [nearySideLowerC_eq_nine_mul_add_seven]
  simp [ternaryCode_cons, ternaryDigit]
  ring

/-- Coefficient by which erase-`c` mixes the discrepancy-invariant coordinate with the private
coordinate. -/
def ruleCMixing (β : Nat) (body : List TagLetter) : ℚ :=
  (3 * ruleCRho β body + 23 - 2 * nearySideLowerC β body) /
    (ruleCRho β body - 9)

/-- The mixing numerator has a strictly signed base-three normal form. -/
theorem ruleCMixing_numerator_eq (β : Nat) (body : List TagLetter) :
    3 * ruleCRho β body + 23 - 2 * nearySideLowerC β body =
      9 * (1 - (3 : ℚ) ^ (tagEncode β body).length -
        2 * ternaryCode (tagEncode β body)) := by
  rw [ruleCRho_eq, nearySideLowerC_eq_encoded]
  ring

/-- The non-line branch has genuine private-coordinate mixing for every nonempty body. -/
theorem ruleCMixing_ne_zero (β : Nat) (body : List TagLetter)
    (body_nonempty : body ≠ []) : ruleCMixing β body ≠ 0 := by
  have encoded_nonempty : tagEncode β body ≠ [] :=
    (tagEncode_eq_nil_iff β body).not.mpr body_nonempty
  have encoded_length_pos : 0 < (tagEncode β body).length :=
    List.length_pos_of_ne_nil encoded_nonempty
  have power_gt_one : (1 : ℚ) < 3 ^ (tagEncode β body).length :=
    one_lt_pow₀ (by norm_num) encoded_length_pos.ne'
  have signed :
      9 * (1 - (3 : ℚ) ^ (tagEncode β body).length -
        2 * ternaryCode (tagEncode β body)) < 0 := by
    nlinarith
  have numerator_ne :
      3 * ruleCRho β body + 23 - 2 * nearySideLowerC β body ≠ 0 := by
    rw [ruleCMixing_numerator_eq]
    exact ne_of_lt signed
  have denominator_ne : ruleCRho β body - 9 ≠ 0 := by
    rw [ruleCRho_eq]
    nlinarith
  exact div_ne_zero numerator_ne denominator_ne

/-- The two checked Neary commutators force every invariant two-dimensional affine pencil to
forget `t`. -/
theorem neary_commutator_pencil_forgets_t
    (β : Nat) (three_le : 3 ≤ β)
    (pencil : Submodule ℚ AffineForm) (pencil_rank : Module.finrank ℚ pencil = 2)
    (constant_invariant :
      ∀ form ∈ pencil,
        constantTranslation
          (-2 * eraseBDefect β / (3 * eraseBScale β)) form ∈ pencil)
    (radial_invariant :
      ∀ form ∈ pencil, radialTranslation (-(8 / 9)) form ∈ pencil) :
    pencil ≤ LinearMap.ker tCoefficient := by
  have scale_ne : eraseBScale β ≠ 0 := by
    simp [eraseBScale, nearySideUpperBScale]
  have defect_ne := eraseBDefect_ne_zero β three_le
  have constant_ne : -2 * eraseBDefect β / (3 * eraseBScale β) ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) defect_ne)
      (mul_ne_zero (by norm_num) scale_ne)
  have radial_ne : -(8 / 9 : ℚ) ≠ 0 := by norm_num
  exact invariant_affine_pencil_forgets_t pencil pencil_rank _ _ constant_ne radial_ne
    constant_invariant radial_invariant

end PhaseRigidity

end MatrixMortality
