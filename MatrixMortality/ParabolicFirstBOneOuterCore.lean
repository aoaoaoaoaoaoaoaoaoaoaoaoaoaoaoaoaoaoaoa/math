import MatrixMortality.ParabolicFirstBOneInnerCore
import MatrixMortality.ParabolicFirstBTwo
import MatrixMortality.ParabolicFirstBTwoTailCore

/-!
# Outer-wait reduction for the first-`b`-after-one-`c` cylinder

Complement normalization traps every physical `cb` zero in an exact rational outer-root
window. Its integral points form 22 compressed ranges containing 113 `(x,y)` pairs below
outer wait 211. The generated tail certificate refines those ranges to five suffix chambers.
-/

namespace MatrixMortality.ParabolicBlade

/-- Encoded scale of the tail following the initial `cb`. -/
def firstBOneOuterTailScale (tail : List TagLetter) : ℚ :=
  3 ^ (tagEncode 3 tail).length

/-- Complement coordinate of the tail following the initial `cb`. -/
def firstBOneOuterTailComplement (tail : List TagLetter) : ℚ :=
  tagComplementCode tail

/-- Normalized all-`c` coefficient of a physical `cb` tail. -/
def firstBOneOuterA (tail : List TagLetter) (y : Nat) : ℚ :=
  729 * (72 * y - 9) + (9 - 8 * y) / firstBOneOuterTailScale tail

/-- Normalized complement coefficient of a physical `cb` tail. -/
def firstBOneOuterD (tail : List TagLetter) : ℚ :=
  39 + firstBOneOuterTailComplement tail / firstBOneOuterTailScale tail

/-- Lower all-`c` endpoint on the exact first-`b` position-`j` rectangle. -/
def firstBOneOuterALower (j y : Nat) : ℚ :=
  729 * (72 * y - 9) + (9 - 8 * y) / 3 ^ (j + 5)

/-- Upper all-`c` endpoint on every first-`b` tail rectangle. -/
def firstBOneOuterAUpper (y : Nat) : ℚ :=
  729 * (72 * y - 9)

private theorem firstBOneOuter_cb_scale (tail : List TagLetter) :
    3 ^ (tagEncode 3 ([.c, .b] ++ tail)).length =
      729 * 3 ^ (tagEncode 3 tail).length := by
  rw [tagEncode_append, List.length_append, pow_add]
  norm_num [tagEncode, spell, tagCode]

private theorem firstBOneOuter_cb_complement (tail : List TagLetter) :
    tagComplementCode ([.c, .b] ++ tail) =
      39 * 3 ^ (tagEncode 3 tail).length + tagComplementCode tail := by
  rw [tagComplementCode_append]
  have prefix_complement : tagComplementCode [.c, .b] = 39 := by decide
  rw [prefix_complement]

private theorem firstBOneOuter_normalized_root_of_core_zero
    (T E x y z : Nat) (scale_positive : 0 < T)
    (core_zero :
      bZeroBDefectCOneCodeCore (729 * (T : ℚ))
        (729 * T - 1 - (39 * T + E)) x y z = 0) :
    let a : ℚ := 729 * (72 * y - 9) + (9 - 8 * y) / T
    let d : ℚ := 39 + E / T
    parabolicOuterRootDenominator a d z * x =
      parabolicOuterRootNumerator a d y z := by
  have scale_nonzero : (T : ℚ) ≠ 0 := by exact_mod_cast scale_positive.ne'
  rw [bZeroBDefectCOneCodeCore_thin_decomposition] at core_zero
  unfold bZeroBDefectCOneWaitFactor bZeroBDefectCOneRootPencil
    bZeroBDefectCOneComplementCore at core_zero
  dsimp only
  unfold parabolicOuterRootDenominator parabolicOuterRootNumerator
  field_simp [scale_nonzero]
  linear_combination core_zero

private theorem firstBOneOuter_physical_parameters
    (tail : List TagLetter) (contains_b : .b ∈ tail) (y : Nat) :
    let T : Nat := 3 ^ (tagEncode 3 tail).length
    let E : Nat := tagComplementCode tail
    let a : ℚ := 729 * (72 * y - 9) + (9 - 8 * y) / T
    let d : ℚ := 39 + E / T
    243 ≤ T ∧ 39 ≤ d ∧ d ≤ 9477 / 242 ∧
      (2 ≤ y →
        729 * (72 * y - 9) + (9 - 8 * y) / 243 ≤ a ∧
          a ≤ 729 * (72 * y - 9)) ∧
      (y = 1 → 45927 ≤ a ∧ a ≤ 45927 + 1 / 243) := by
  let T : Nat := 3 ^ (tagEncode 3 tail).length
  let E : Nat := tagComplementCode tail
  let a : ℚ := 729 * (72 * y - 9) + (9 - 8 * y) / T
  let d : ℚ := 39 + E / T
  have encoded_length : 5 ≤ (tagEncode 3 tail).length :=
    tagEncode_length_five_le_of_mem_b tail contains_b
  have scale_bound : 243 ≤ T := by
    dsimp [T]
    calc
      243 = 3 ^ 5 := by norm_num
      _ ≤ 3 ^ (tagEncode 3 tail).length :=
        Nat.pow_le_pow_right (by norm_num) encoded_length
  have scale_positive_nat : 0 < T := lt_of_lt_of_le (by norm_num) scale_bound
  have scale_positive : (0 : ℚ) < T := by exact_mod_cast scale_positive_nat
  have complement_bound_nat : 242 * E ≤ 39 * T := by
    have sharp := tagComplementCode_global_bound tail
    dsimp [T, E] at sharp ⊢
    have scale_one : 1 ≤ 3 ^ (tagEncode 3 tail).length := one_le_pow₀ (by norm_num)
    omega
  have complement_bound : (E : ℚ) / T ≤ 39 / 242 := by
    rw [div_le_div_iff₀ scale_positive (by norm_num)]
    have complement_bound_rat : (242 : ℚ) * E ≤ 39 * T := by
      exact_mod_cast complement_bound_nat
    simpa only [mul_comm] using complement_bound_rat
  have d_lower : (39 : ℚ) ≤ d := by
    dsimp [d]
    have quotient_nonnegative : (0 : ℚ) ≤ (E : ℚ) / T := by positivity
    linarith
  have d_upper : d ≤ (9477 / 242 : ℚ) := by
    dsimp [d]
    norm_num
    linarith
  refine ⟨scale_bound, d_lower, d_upper, ?_, ?_⟩
  · intro two_le_y
    have y_large : (2 : ℚ) ≤ y := by exact_mod_cast two_le_y
    have numerator_nonpositive : (9 : ℚ) - 8 * y ≤ 0 := by linarith
    have scale_bound_rat : (243 : ℚ) ≤ T := by exact_mod_cast scale_bound
    have scaled_numerator :
        ((9 : ℚ) - 8 * y) * T ≤ ((9 : ℚ) - 8 * y) * 243 :=
      mul_le_mul_of_nonpos_left scale_bound_rat numerator_nonpositive
    have fraction_lower : ((9 : ℚ) - 8 * y) / 243 ≤ (9 - 8 * y) / T := by
      rw [div_le_div_iff₀ (by norm_num) scale_positive]
      simpa only [mul_comm] using scaled_numerator
    constructor
    · linarith
    · have fraction_nonpositive : ((9 : ℚ) - 8 * y) / T ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg numerator_nonpositive scale_positive.le
      linarith
  · intro y_one
    subst y
    have reciprocal_bound : (1 : ℚ) / T ≤ 1 / 243 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast scale_bound)
    constructor
    · dsimp [a]
      have reciprocal_nonnegative : (0 : ℚ) ≤ 1 / T := by positivity
      linarith
    · dsimp [a]
      norm_num only [Nat.cast_one]
      linarith

private theorem firstBOneOuter_core_zero_in_complement_coordinates
    (tail : List TagLetter) (x y z : Nat)
    (core_zero :
      bZeroBDefectCOneCodeCore
        ((3 : ℚ) ^ (tagEncode 3 ([.c, .b] ++ tail)).length)
        (ternaryCode (tagEncode 3 ([.c, .b] ++ tail))) x y z = 0) :
    let T : Nat := 3 ^ (tagEncode 3 tail).length
    let E : Nat := tagComplementCode tail
    bZeroBDefectCOneCodeCore (729 * (T : ℚ))
      (729 * T - 1 - (39 * T + E)) x y z = 0 := by
  let body := [.c, .b] ++ tail
  let T : Nat := 3 ^ (tagEncode 3 tail).length
  let E : Nat := tagComplementCode tail
  let S : Nat := 3 ^ (tagEncode 3 body).length
  let C : Nat := ternaryCode (tagEncode 3 body)
  let D : Nat := tagComplementCode body
  have scale_eq : S = 729 * T := by
    dsimp [S, T, body]
    exact firstBOneOuter_cb_scale tail
  have complement_eq : D = 39 * T + E := by
    dsimp [D, T, E, body]
    exact firstBOneOuter_cb_complement tail
  have code_lt : C < S := by
    dsimp [C, S, body]
    exact ternaryCode_lt_pow_length (tagEncode 3 ([.c, .b] ++ tail))
  have complement_nat : D = S - C - 1 := rfl
  have coordinate_sum : C + D + 1 = S := by omega
  have code_eq : (C : ℚ) = (S : ℚ) - 1 - D := by
    have coordinate_sum_rat : (C : ℚ) + D + 1 = S := by exact_mod_cast coordinate_sum
    linarith
  have scale_cast :
      (S : ℚ) = (3 : ℚ) ^ (tagEncode 3 ([.c, .b] ++ tail)).length := by
    dsimp [S, body]
    norm_num
  rw [← scale_cast] at core_zero
  change bZeroBDefectCOneCodeCore (S : ℚ) (C : ℚ) x y z = 0 at core_zero
  rw [code_eq, scale_eq, complement_eq] at core_zero
  dsimp only
  push_cast at core_zero
  exact core_zero

/-- A physical `cb` core zero supplies the normalized inner-wait root equation. -/
theorem firstBOneOuter_z_equation_of_core_zero
    (tail : List TagLetter) (x y z : Nat)
    (core_zero :
      bZeroBDefectCOneCodeCore
        ((3 : ℚ) ^ (tagEncode 3 ([.c, .b] ++ tail)).length)
        (ternaryCode (tagEncode 3 ([.c, .b] ++ tail))) x y z = 0) :
    let a := firstBOneOuterA tail y
    let d := firstBOneOuterD tail
    firstBTwoTailZDenominator a d x y * z =
      firstBTwoTailZNumerator a d x y := by
  let T : Nat := 3 ^ (tagEncode 3 tail).length
  let E : Nat := tagComplementCode tail
  let a : ℚ := 729 * (72 * y - 9) + (9 - 8 * y) / T
  let d : ℚ := 39 + E / T
  have scale_positive : 0 < T := by dsimp [T]; positivity
  have complement_core_zero :=
    firstBOneOuter_core_zero_in_complement_coordinates tail x y z core_zero
  dsimp only at complement_core_zero
  have root_eq :=
    firstBOneOuter_normalized_root_of_core_zero
      T E x y z scale_positive complement_core_zero
  dsimp [a, d, T, E] at root_eq
  simp only [firstBOneOuterA, firstBOneOuterD, firstBOneOuterTailScale,
    firstBOneOuterTailComplement]
  unfold parabolicOuterRootDenominator parabolicOuterRootNumerator at root_eq
  unfold firstBTwoTailZDenominator firstBTwoTailZNumerator
  norm_num only [Nat.cast_pow, Nat.cast_ofNat, inv_pow] at root_eq ⊢
  linear_combination -root_eq

/-- Exact affine rectangle for a tail whose first `b` occurs at position `j`. -/
theorem firstBOneOuter_exact_rectangle
    (j : Nat) (rest : List TagLetter) (y : Nat) (two_le_y : 2 ≤ y) :
    let tail := List.replicate j .c ++ .b :: rest
    FirstBTwoTailRectangle
      (firstBOneOuterALower j y) (firstBOneOuterAUpper y)
      (firstBTwoTailDLower j) (firstBTwoTailDUpper j)
      (firstBOneOuterA tail y) (firstBOneOuterD tail) := by
  let tail := List.replicate j .c ++ .b :: rest
  let T := firstBTwoTailScale tail
  let E := firstBTwoTailComplement tail
  have scale_positive : (0 : ℚ) < T := by dsimp [T, firstBTwoTailScale]; positivity
  have threshold_positive : (0 : ℚ) < 3 ^ (j + 5) := by positivity
  have scale_lower := firstBTwoTail_scale_lower j rest
  have density := firstBTwoTail_density_bounds j rest
  dsimp only [tail, T, E] at density scale_lower
  have correction_nonpositive : (9 : ℚ) - 8 * y ≤ 0 := by
    have y_lower : (2 : ℚ) ≤ y := by exact_mod_cast two_le_y
    linarith
  have correction_lower :
      ((9 : ℚ) - 8 * y) / 3 ^ (j + 5) ≤ (9 - 8 * y) / T := by
    rw [div_le_div_iff₀ threshold_positive scale_positive]
    nlinarith
  have correction_upper : (9 - 8 * (y : ℚ)) / T ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg correction_nonpositive scale_positive.le
  have density_lower : (13 : ℚ) / (81 * 3 ^ j) ≤ E / T := by
    have denominator_positive : (0 : ℚ) < 81 * 3 ^ j := by positivity
    rw [div_le_div_iff₀ denominator_positive scale_positive]
    nlinarith [density.1]
  have density_upper : E / T ≤ (39 : ℚ) / (242 * 3 ^ j) := by
    have denominator_positive : (0 : ℚ) < 242 * 3 ^ j := by positivity
    rw [div_le_div_iff₀ scale_positive denominator_positive]
    nlinarith [density.2]
  constructor
  · simpa [firstBOneOuterALower, firstBOneOuterA, firstBOneOuterTailScale,
      firstBTwoTailScale, tail, T] using
      add_le_add_left correction_lower (729 * (72 * (y : ℚ) - 9))
  · simpa [firstBOneOuterAUpper, firstBOneOuterA, firstBOneOuterTailScale,
      firstBTwoTailScale, tail, T] using
      add_le_add_left correction_upper (729 * (72 * (y : ℚ) - 9))
  · simpa [firstBTwoTailDLower, firstBOneOuterD, firstBOneOuterTailComplement,
      firstBOneOuterTailScale, firstBTwoTailComplement, firstBTwoTailScale,
      tail, T, E] using
      add_le_add_left density_lower 39
  · simpa [firstBTwoTailDUpper, firstBOneOuterD, firstBOneOuterTailComplement,
      firstBOneOuterTailScale, firstBTwoTailComplement, firstBTwoTailScale,
      tail, T, E] using
      add_le_add_left density_upper 39

/-- Closed rectangle containing every tail whose first `b` occurs no earlier than `k`. -/
theorem firstBOneOuter_envelope_rectangle
    (k j : Nat) (rest : List TagLetter) (y : Nat)
    (k_le_j : k ≤ j) (two_le_y : 2 ≤ y) :
    let tail := List.replicate j .c ++ .b :: rest
    FirstBTwoTailRectangle
      (firstBOneOuterALower k y) (firstBOneOuterAUpper y)
      39 (firstBTwoTailDUpper k)
      (firstBOneOuterA tail y) (firstBOneOuterD tail) := by
  let tail := List.replicate j .c ++ .b :: rest
  let T := firstBTwoTailScale tail
  let E := firstBTwoTailComplement tail
  have scale_positive : (0 : ℚ) < T := by dsimp [T, firstBTwoTailScale]; positivity
  have threshold_positive : (0 : ℚ) < 3 ^ (k + 5) := by positivity
  have scale_lower := firstBTwoTail_scale_lower j rest
  have threshold_power_order : (3 : Nat) ^ (k + 5) ≤ 3 ^ (j + 5) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have threshold_lower : (3 : ℚ) ^ (k + 5) ≤ T :=
    le_trans (by exact_mod_cast threshold_power_order) scale_lower
  have density := firstBTwoTail_density_bounds j rest
  dsimp only [tail, T, E] at density
  have power_order : (3 : Nat) ^ k ≤ 3 ^ j :=
    Nat.pow_le_pow_right (by norm_num) k_le_j
  have density_at_k : (242 : ℚ) * 3 ^ k * E ≤ 39 * T := by
    have complement_nonnegative : (0 : ℚ) ≤ E := by
      dsimp [E, firstBTwoTailComplement]
      positivity
    have power_order_rat : (3 : ℚ) ^ k ≤ 3 ^ j := by exact_mod_cast power_order
    have scaled_power_order : (242 : ℚ) * 3 ^ k * E ≤ 242 * 3 ^ j * E := by
      have scaled := mul_le_mul_of_nonneg_left power_order_rat
        (by norm_num : (0 : ℚ) ≤ 242)
      exact mul_le_mul_of_nonneg_right scaled complement_nonnegative
    exact scaled_power_order.trans density.2
  have correction_nonpositive : (9 : ℚ) - 8 * y ≤ 0 := by
    have y_lower : (2 : ℚ) ≤ y := by exact_mod_cast two_le_y
    linarith
  have correction_lower :
      ((9 : ℚ) - 8 * y) / 3 ^ (k + 5) ≤ (9 - 8 * y) / T := by
    rw [div_le_div_iff₀ threshold_positive scale_positive]
    nlinarith
  have correction_upper : (9 - 8 * (y : ℚ)) / T ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg correction_nonpositive scale_positive.le
  have density_nonnegative : (0 : ℚ) ≤ E / T := by
    exact div_nonneg (by dsimp [E, firstBTwoTailComplement]; positivity) scale_positive.le
  have density_upper : E / T ≤ (39 : ℚ) / (242 * 3 ^ k) := by
    have denominator_positive : (0 : ℚ) < 242 * 3 ^ k := by positivity
    rw [div_le_div_iff₀ scale_positive denominator_positive]
    nlinarith [density_at_k]
  constructor
  · simpa [firstBOneOuterALower, firstBOneOuterA, firstBOneOuterTailScale,
      firstBTwoTailScale, tail, T] using
      add_le_add_left correction_lower (729 * (72 * (y : ℚ) - 9))
  · simpa [firstBOneOuterAUpper, firstBOneOuterA, firstBOneOuterTailScale,
      firstBTwoTailScale, tail, T] using
      add_le_add_left correction_upper (729 * (72 * (y : ℚ) - 9))
  · simpa [firstBOneOuterD, firstBOneOuterTailComplement, firstBOneOuterTailScale,
      firstBTwoTailComplement, firstBTwoTailScale, tail, T, E] using
      add_le_add_left density_nonnegative 39
  · simpa [firstBTwoTailDUpper, firstBOneOuterD, firstBOneOuterTailComplement,
      firstBOneOuterTailScale, firstBTwoTailComplement, firstBTwoTailScale,
      tail, T, E] using
      add_le_add_left density_upper 39

/-- Rational lower outer-root graph for a physical `cb` tail. -/
def firstBOneOuterRootLower (y : Nat) : ℚ :=
  (912430059418355833 * y - 127032616940179878) /
    (4325040702677376 * y + 16457183626531023)

/-- Rational upper outer-root graph for a physical `cb` tail. -/
def firstBOneOuterRootUpper (y : Nat) : ℚ :=
  (36895821909120 * y - 5153671850131) /
    (174831229440 * y + 662381142984)

/-- Integral outer waits lie in this normalized root window. -/
def FirstBOneOuterRootWindow (x y : Nat) : Prop :=
  firstBOneOuterRootLower y ≤ x ∧ x ≤ firstBOneOuterRootUpper y

/-- The 22 compressed integral ranges in the outer-root window below wait 211. -/
def FirstBOneOuterRootCandidate (x y : Nat) : Prop :=
  (x = 134 ∧ y = 7) ∨
    (x = 146 ∧ y = 9) ∨
    (x = 169 ∧ y = 16) ∨
    (x = 171 ∧ y = 17) ∨
    (x = 180 ∧ y = 23) ∨
    (x = 184 ∧ y = 27) ∨
    (x = 189 ∧ y = 34) ∨
    (x = 192 ∧ y = 40) ∨
    (x = 194 ∧ y = 45) ∨
    (x = 195 ∧ y = 48) ∨
    (x = 198 ∧ y = 60) ∨
    (x = 200 ∧ y = 72) ∨
    (x = 201 ∧ y = 79) ∨
    (x = 202 ∧ 88 ≤ y ∧ y ≤ 89) ∨
    (x = 203 ∧ y = 100) ∨
    (x = 204 ∧ y = 115) ∨
    (x = 205 ∧ 134 ≤ y ∧ y ≤ 135) ∨
    (x = 206 ∧ 161 ≤ y ∧ y ≤ 163) ∨
    (x = 207 ∧ 202 ≤ y ∧ y ≤ 206) ∨
    (x = 208 ∧ 270 ≤ y ∧ y ≤ 276) ∨
    (x = 209 ∧ 404 ≤ y ∧ y ≤ 419) ∨
    (x = 210 ∧ 796 ≤ y ∧ y ≤ 858)

private def firstBOneOuterRootLowerNumerator (y : Nat) : ℤ :=
  912430059418355833 * y - 127032616940179878

private def firstBOneOuterRootLowerDenominator (y : Nat) : ℤ :=
  4325040702677376 * y + 16457183626531023

private def firstBOneOuterRootUpperNumerator (y : Nat) : ℤ :=
  36895821909120 * y - 5153671850131

private def firstBOneOuterRootUpperDenominator (y : Nat) : ℤ :=
  174831229440 * y + 662381142984

private theorem firstBOneOuter_root_between_envelopes
    (a d : ℚ) (x y z : Nat) (two_le_y : 2 ≤ y)
    (a_lower : 729 * (72 * y - 9) + (9 - 8 * y) / 243 ≤ a)
    (a_upper : a ≤ 729 * (72 * y - 9))
    (d_lower : 39 ≤ d) (d_upper : d ≤ 9477 / 242)
    (root_eq : parabolicOuterRootDenominator a d z * x =
      parabolicOuterRootNumerator a d y z) :
    firstBOneOuterRootLower y ≤ x ∧ (x : ℚ) < firstBOneOuterRootUpper y := by
  let a₀ : ℚ := 729 * (72 * y - 9) + (9 - 8 * y) / 243
  let a₁ : ℚ := 729 * (72 * y - 9)
  let d₀ : ℚ := 39
  let d₁ : ℚ := 9477 / 242
  have y_nonnegative : (0 : ℚ) ≤ y := by positivity
  have y_large : (2 : ℚ) ≤ y := by exact_mod_cast two_le_y
  have a₀_positive : 0 < a₀ := by dsimp [a₀]; linarith
  have a_positive : 0 < a := lt_of_lt_of_le a₀_positive a_lower
  have a₁_positive : 0 < a₁ := by dsimp [a₁]; nlinarith
  have d₀_positive : 0 < d₀ := by norm_num [d₀]
  have d_positive : 0 < d := lt_of_lt_of_le d₀_positive d_lower
  have d₁_positive : 0 < d₁ := by norm_num [d₁]
  have worst_margin : d₁ * (1296 * (y : ℚ) + 84099) < 38 * a₀ := by
    dsimp [a₀, d₁]
    norm_num
    linarith
  have factor_nonnegative : (0 : ℚ) ≤ 1296 * y + 84099 := by positivity
  have scaled_d : d * (1296 * (y : ℚ) + 84099) ≤
      d₁ * (1296 * y + 84099) :=
    mul_le_mul_of_nonneg_right d_upper factor_nonnegative
  have margin : d * (1296 * (y : ℚ) + 84099) < 38 * a := by nlinarith
  have z_nonnegative : (0 : ℚ) ≤ z := by positivity
  have root_value :=
    parabolicOuterRoot_eq a d y z x a_positive d_positive z_nonnegative root_eq
  have lower_value :
      firstBOneOuterRootLower y =
        parabolicOuterRootNumerator a₀ d₁ y 0 /
          parabolicOuterRootDenominator a₀ d₁ 0 := by
    unfold firstBOneOuterRootLower
    have left_denominator_positive :
        (0 : ℚ) < 4325040702677376 * y + 16457183626531023 := by positivity
    have right_denominator_positive :=
      parabolicOuterRootDenominator_pos a₀ d₁ 0 a₀_positive d₁_positive (by norm_num)
    field_simp [left_denominator_positive.ne', right_denominator_positive.ne']
    dsimp [a₀, d₁]
    norm_num [firstBOneOuterRootLower, parabolicOuterRootNumerator,
      parabolicOuterRootDenominator]
    ring
  have upper_value :
      parabolicOuterAsymptoteNumerator a₁ d₀ y /
          parabolicOuterAsymptoteDenominator a₁ d₀ =
        firstBOneOuterRootUpper y := by
    unfold firstBOneOuterRootUpper
    have left_denominator_positive :=
      parabolicOuterAsymptoteDenominator_pos a₁ d₀ a₁_positive d₀_positive
    have right_denominator_positive :
        (0 : ℚ) < 174831229440 * y + 662381142984 := by positivity
    field_simp [left_denominator_positive.ne', right_denominator_positive.ne']
    dsimp [a₁, d₀]
    norm_num [firstBOneOuterRootUpper, parabolicOuterAsymptoteNumerator,
      parabolicOuterAsymptoteDenominator]
    ring
  constructor
  · rw [lower_value]
    calc
      _ ≤ parabolicOuterRootNumerator a₀ d y 0 /
          parabolicOuterRootDenominator a₀ d 0 :=
        parabolicOuterRoot_decreases_d a₀ d d₁ y 0 d_upper a₀_positive d_positive
          y_nonnegative (by norm_num)
      _ ≤ parabolicOuterRootNumerator a d y 0 /
          parabolicOuterRootDenominator a d 0 :=
        parabolicOuterRoot_increases_a a₀ a d y 0 a_lower a₀_positive d_positive
          y_nonnegative (by norm_num)
      _ ≤ parabolicOuterRootNumerator a d y z /
          parabolicOuterRootDenominator a d z :=
        parabolicOuterRoot_increases_z a d y 0 z (by positivity) a_positive d_positive
          (by norm_num) margin
      _ = x := root_value
  · rw [← upper_value, ← root_value]
    calc
      _ < parabolicOuterAsymptoteNumerator a d y /
          parabolicOuterAsymptoteDenominator a d :=
        parabolicOuterRoot_lt_asymptote a d y z a_positive d_positive z_nonnegative margin
      _ ≤ parabolicOuterAsymptoteNumerator a₁ d y /
          parabolicOuterAsymptoteDenominator a₁ d :=
        parabolicOuterAsymptote_increases_a a a₁ d y a_upper a_positive d_positive
          y_nonnegative
      _ ≤ parabolicOuterAsymptoteNumerator a₁ d₀ y /
          parabolicOuterAsymptoteDenominator a₁ d₀ :=
        parabolicOuterAsymptote_decreases_d a₁ d₀ d y d_lower a₁_positive d₀_positive
          y_nonnegative

private theorem firstBOneOuter_no_root_at_y_one
    (a d : ℚ) (x z : Nat)
    (a_lower : 45927 ≤ a) (a_upper : a ≤ 45927 + 1 / 243)
    (d_lower : 39 ≤ d) (d_upper : d ≤ 9477 / 242)
    (root_eq : parabolicOuterRootDenominator a d z * x =
      parabolicOuterRootNumerator a d 1 z) : False := by
  have a_positive : 0 < a := lt_of_lt_of_le (by norm_num) a_lower
  have d_positive : 0 < d := lt_of_lt_of_le (by norm_num) d_lower
  have z_nonnegative : (0 : ℚ) ≤ z := by positivity
  have denominator_positive :=
    parabolicOuterRootDenominator_pos a d z a_positive d_positive z_nonnegative
  have lower_slope :
      0 < (21330254276 : ℚ) * a - 24412411950744 * d := by
    have a_scaled := mul_le_mul_of_nonneg_left a_lower (by norm_num : (0 : ℚ) ≤ 21330254276)
    have d_scaled := mul_le_mul_of_nonneg_left d_upper (by norm_num : (0 : ℚ) ≤ 24412411950744)
    norm_num at a_scaled d_scaled
    linarith
  have lower_constant :
      0 < (1993388905 : ℚ) * a - 2280622453044 * d := by
    have a_scaled := mul_le_mul_of_nonneg_left a_lower (by norm_num : (0 : ℚ) ≤ 1993388905)
    have d_scaled := mul_le_mul_of_nonneg_left d_upper (by norm_num : (0 : ℚ) ≤ 2280622453044)
    norm_num at a_scaled d_scaled
    linarith
  have lower_gap :
      37 * parabolicOuterRootDenominator a d z <
        parabolicOuterRootNumerator a d 1 z := by
    unfold parabolicOuterRootDenominator parabolicOuterRootNumerator
    nlinarith [mul_nonneg lower_slope.le z_nonnegative]
  have upper_slope :
      0 < -(21210342596 : ℚ) * a + 25044013532280 * d := by
    have a_scaled := mul_le_mul_of_nonneg_left a_upper (by norm_num : (0 : ℚ) ≤ 21210342596)
    have d_scaled := mul_le_mul_of_nonneg_left d_lower (by norm_num : (0 : ℚ) ≤ 25044013532280)
    norm_num at a_scaled d_scaled
    linarith
  have upper_constant :
      0 < -(1982179081 : ℚ) * a + 2339670539580 * d := by
    have a_scaled := mul_le_mul_of_nonneg_left a_upper (by norm_num : (0 : ℚ) ≤ 1982179081)
    have d_scaled := mul_le_mul_of_nonneg_left d_lower (by norm_num : (0 : ℚ) ≤ 2339670539580)
    norm_num at a_scaled d_scaled
    linarith
  have upper_gap :
      parabolicOuterRootNumerator a d 1 z <
        38 * parabolicOuterRootDenominator a d z := by
    unfold parabolicOuterRootDenominator parabolicOuterRootNumerator
    nlinarith [mul_nonneg upper_slope.le z_nonnegative]
  have lower_rat : (37 : ℚ) < x := by
    rw [← root_eq] at lower_gap
    nlinarith
  have upper_rat : (x : ℚ) < 38 := by
    rw [← root_eq] at upper_gap
    nlinarith
  have lower_nat : 37 < x := by exact_mod_cast lower_rat
  have upper_nat : x < 38 := by exact_mod_cast upper_rat
  omega

/-- Every physical `cb` zero has middle wait at least two. -/
theorem firstBOneOuter_wait_two_le_of_core_zero
    (tail : List TagLetter) (contains_b : .b ∈ tail) (x y z : Nat)
    (core_zero :
      bZeroBDefectCOneCodeCore
        ((3 : ℚ) ^ (tagEncode 3 ([.c, .b] ++ tail)).length)
        (ternaryCode (tagEncode 3 ([.c, .b] ++ tail))) x y z = 0) :
    2 ≤ y := by
  by_contra wait_not_two
  have wait_cases : y = 0 ∨ y = 1 := by omega
  rcases wait_cases with rfl | rfl
  · let T : Nat := 3 ^ (tagEncode 3 tail).length
    let E : Nat := tagComplementCode tail
    have T_positive : 0 < T := by dsimp [T]; positivity
    have core_complement_zero :=
      firstBOneOuter_core_zero_in_complement_coordinates tail x 0 z core_zero
    dsimp only at core_complement_zero
    have scale_large : (1 : ℚ) < 729 * T := by
      have T_one : (1 : ℚ) ≤ T := by exact_mod_cast one_le_pow₀ (by norm_num : 0 < 3)
      nlinarith
    have complement_positive : (0 : ℚ) < 39 * T + E := by
      have T_positive_rat : (0 : ℚ) < T := by exact_mod_cast T_positive
      positivity
    have complement_large : (729 : ℚ) * T - 1 ≤ 585 * (39 * T + E) := by
      have T_one : (1 : ℚ) ≤ T := by exact_mod_cast one_le_pow₀ (by norm_num : 0 < 3)
      have E_nonnegative : (0 : ℚ) ≤ E := by positivity
      nlinarith
    have core_positive :=
      bZeroBDefectCOneCodeCore_pos_of_zero_wait_large_complement
        (729 * T) (39 * T + E) scale_large complement_positive complement_large x z
    exact (ne_of_gt core_positive) core_complement_zero
  · let T : Nat := 3 ^ (tagEncode 3 tail).length
    let E : Nat := tagComplementCode tail
    let a : ℚ := 729 * (72 * 1 - 9) + (9 - 8 * 1) / T
    let d : ℚ := 39 + E / T
    have parameters := firstBOneOuter_physical_parameters tail contains_b 1
    dsimp only at parameters
    have scale_positive : 0 < T := lt_of_lt_of_le (by norm_num) parameters.1
    have complement_core_zero :=
      firstBOneOuter_core_zero_in_complement_coordinates tail x 1 z core_zero
    dsimp only at complement_core_zero
    have root_eq :=
      firstBOneOuter_normalized_root_of_core_zero
        T E x 1 z scale_positive complement_core_zero
    exact firstBOneOuter_no_root_at_y_one a d x z
      (parameters.2.2.2.2 rfl).1 (parameters.2.2.2.2 rfl).2
      parameters.2.1 parameters.2.2.1 root_eq

private theorem firstBOneOuterRootLower_integer_form (y : Nat) :
    firstBOneOuterRootLower y =
      firstBOneOuterRootLowerNumerator y / firstBOneOuterRootLowerDenominator y := by
  norm_num [firstBOneOuterRootLower, firstBOneOuterRootLowerNumerator,
    firstBOneOuterRootLowerDenominator]

private theorem firstBOneOuterRootUpper_integer_form (y : Nat) :
    firstBOneOuterRootUpper y =
      firstBOneOuterRootUpperNumerator y / firstBOneOuterRootUpperDenominator y := by
  norm_num [firstBOneOuterRootUpper, firstBOneOuterRootUpperNumerator,
    firstBOneOuterRootUpperDenominator]

private theorem firstBOneOuterRootWindow_cross
    (x y : Nat) (window : FirstBOneOuterRootWindow x y) :
    firstBOneOuterRootLowerNumerator y ≤
        (x : ℤ) * firstBOneOuterRootLowerDenominator y ∧
      (x : ℤ) * firstBOneOuterRootUpperDenominator y ≤
        firstBOneOuterRootUpperNumerator y := by
  rcases window with ⟨lower, upper⟩
  rw [firstBOneOuterRootLower_integer_form] at lower
  rw [firstBOneOuterRootUpper_integer_form] at upper
  have lower_denominator_positive :
      (0 : ℚ) < firstBOneOuterRootLowerDenominator y := by
    unfold firstBOneOuterRootLowerDenominator
    positivity
  have upper_denominator_positive :
      (0 : ℚ) < firstBOneOuterRootUpperDenominator y := by
    unfold firstBOneOuterRootUpperDenominator
    positivity
  have lower_cross := (div_le_iff₀ lower_denominator_positive).mp lower
  have upper_cross := (le_div_iff₀ upper_denominator_positive).mp upper
  constructor
  · apply (Int.cast_le (R := ℚ)).mp
    simpa only [Int.cast_mul, Int.cast_natCast] using lower_cross
  · apply (Int.cast_le (R := ℚ)).mp
    simpa only [Int.cast_mul, Int.cast_natCast] using upper_cross

private theorem firstBOneOuterRootWindow_coarse
    (x y : Nat) (y_lower : 7 ≤ y) (x_upper : x ≤ 210)
    (window : FirstBOneOuterRootWindow x y) :
    134 ≤ x ∧ y ≤ 858 := by
  rcases firstBOneOuterRootWindow_cross x y window with ⟨lower, upper⟩
  have x_lower : 134 ≤ x := by
    by_contra x_small
    have x_le : x ≤ 133 := by omega
    have scaled := Int.mul_le_mul_of_nonneg_right
      (show (x : ℤ) ≤ 133 by exact_mod_cast x_le)
      (show (0 : ℤ) ≤ firstBOneOuterRootLowerDenominator y by
        unfold firstBOneOuterRootLowerDenominator
        positivity)
    unfold firstBOneOuterRootLowerNumerator firstBOneOuterRootLowerDenominator at lower scaled
    omega
  have y_upper : y ≤ 858 := by
    have scaled := Int.mul_le_mul_of_nonneg_right
      (show (x : ℤ) ≤ 210 by exact_mod_cast x_upper)
      (show (0 : ℤ) ≤ firstBOneOuterRootLowerDenominator y by
        unfold firstBOneOuterRootLowerDenominator
        positivity)
    unfold firstBOneOuterRootLowerNumerator firstBOneOuterRootLowerDenominator at lower scaled
    omega
  exact ⟨x_lower, y_upper⟩

/-- Every integral outer-root window below 211 belongs to one of 22 compressed ranges. -/
theorem firstBOneOuterRootWindow_candidates
    (x y : Nat) (two_le_y : 2 ≤ y) (x_upper : x ≤ 210)
    (window : FirstBOneOuterRootWindow x y) :
    FirstBOneOuterRootCandidate x y := by
  rcases firstBOneOuterRootWindow_cross x y window with ⟨lower, upper⟩
  have y_lower : 7 ≤ y := by
    by_contra y_small
    have y_upper_small : y ≤ 6 := by omega
    interval_cases y <;>
      norm_num [firstBOneOuterRootLowerNumerator, firstBOneOuterRootLowerDenominator,
        firstBOneOuterRootUpperNumerator, firstBOneOuterRootUpperDenominator] at lower upper <;>
      omega
  rcases firstBOneOuterRootWindow_coarse x y y_lower x_upper window with
    ⟨x_lower, y_upper⟩
  unfold FirstBOneOuterRootCandidate
  interval_cases x <;>
    norm_num [firstBOneOuterRootLowerNumerator, firstBOneOuterRootLowerDenominator,
      firstBOneOuterRootUpperNumerator, firstBOneOuterRootUpperDenominator] at lower upper ⊢ <;>
    omega

/-- A physical `cb` zero below outer wait 211 lies in the 113-pair root window. -/
theorem firstBOneOuterRootCandidate_of_core_zero
    (tail : List TagLetter) (contains_b : .b ∈ tail) (x y z : Nat)
    (x_upper : x ≤ 210)
    (core_zero :
      bZeroBDefectCOneCodeCore
        ((3 : ℚ) ^ (tagEncode 3 ([.c, .b] ++ tail)).length)
        (ternaryCode (tagEncode 3 ([.c, .b] ++ tail))) x y z = 0) :
    FirstBOneOuterRootCandidate x y := by
  have two_le_y :=
    firstBOneOuter_wait_two_le_of_core_zero tail contains_b x y z core_zero
  let T : Nat := 3 ^ (tagEncode 3 tail).length
  let E : Nat := tagComplementCode tail
  let a : ℚ := 729 * (72 * y - 9) + (9 - 8 * y) / T
  let d : ℚ := 39 + E / T
  have parameters := firstBOneOuter_physical_parameters tail contains_b y
  dsimp only at parameters
  have scale_positive : 0 < T := lt_of_lt_of_le (by norm_num) parameters.1
  have complement_core_zero :=
    firstBOneOuter_core_zero_in_complement_coordinates tail x y z core_zero
  dsimp only at complement_core_zero
  have root_eq :=
    firstBOneOuter_normalized_root_of_core_zero
      T E x y z scale_positive complement_core_zero
  have bounds := firstBOneOuter_root_between_envelopes a d x y z two_le_y
    (parameters.2.2.2.1 two_le_y).1 (parameters.2.2.2.1 two_le_y).2
    parameters.2.1 parameters.2.2.1 root_eq
  exact firstBOneOuterRootWindow_candidates x y two_le_y x_upper ⟨bounds.1, bounds.2.le⟩

end MatrixMortality.ParabolicBlade
