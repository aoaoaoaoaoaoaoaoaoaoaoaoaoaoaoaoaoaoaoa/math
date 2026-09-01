import MatrixMortality.ParabolicFirstBTwo
import MatrixMortality.ParabolicFirstBTwoTailCore

/-!
# Later first-`b` cylinders

The bodies whose first `b` follows three through eleven leading `c` letters share one
normalized root equation. This module exposes that equation, its exact outer-root window,
and the affine rectangle calculus used by the finite suffix certificate.
-/

namespace MatrixMortality.ParabolicBlade

/-- Code-scale multiplier contributed by `c^k b`. -/
def firstBLatePrefixScale (k : Nat) : Nat :=
  243 * 3 ^ k

/-- Cleared numerator of the weak lower outer-root envelope. -/
def firstBLateRootLowerNumerator (k y : Nat) : ℤ :=
  let r : ℤ := firstBLatePrefixScale k
  242 * (243 * r * (72 * (y : ℤ) - 9) + 9 - 8 * y) * 2408152393 -
    9477 * 243 * (58005064872 * y + 37838186340)

/-- Positive cleared denominator of the weak lower outer-root envelope. -/
def firstBLateRootLowerDenominator (k y : Nat) : ℤ :=
  let r : ℤ := firstBLatePrefixScale k
  242 * (243 * r * (72 * (y : ℤ) - 9) + 9 - 8 * y) * 11209824 +
    9477 * 243 * 59048086536

/-- Cleared numerator of the strict upper outer-root envelope. -/
def firstBLateRootUpperNumerator (k y : Nat) : ℤ :=
  let r : ℤ := firstBLatePrefixScale k
  r * (72 * (y : ℤ) - 9) * 25766986436 -
    39 * (620717828832 * y + 422435605080)

/-- Positive cleared denominator of the strict upper outer-root envelope. -/
def firstBLateRootUpperDenominator (k y : Nat) : ℤ :=
  let r : ℤ := firstBLatePrefixScale k
  r * (72 * (y : ℤ) - 9) * 119911680 + 39 * 631601581536

/-- Cleared exact outer-root window for a later first-`b` position. -/
def FirstBLateRootWindow (k x y : Nat) : Prop :=
  firstBLateRootLowerNumerator k y ≤
      (x : ℤ) * firstBLateRootLowerDenominator k y ∧
    (x : ℤ) * firstBLateRootUpperDenominator k y <
      firstBLateRootUpperNumerator k y

private theorem firstBLate_replicate_c_length (k : Nat) :
    (tagEncode 3 (List.replicate k .c)).length = k := by
  induction k with
  | zero => rfl
  | succ k induction =>
      rw [List.replicate_succ, tagEncode_cons, List.length_append]
      simp only [tagCode, List.length_singleton, induction]
      omega

theorem firstBLate_scale (k : Nat) (tail : List TagLetter) :
    3 ^ (tagEncode 3 (List.replicate k .c ++ .b :: tail)).length =
      firstBLatePrefixScale k * 3 ^ (tagEncode 3 tail).length := by
  rw [tagEncode_append, List.length_append, firstBLate_replicate_c_length,
    tagEncode_cons, List.length_append, pow_add, pow_add]
  norm_num [firstBLatePrefixScale, tagCode]
  ring

theorem firstBLate_complement (k : Nat) (tail : List TagLetter) :
    tagComplementCode (List.replicate k .c ++ .b :: tail) =
      39 * 3 ^ (tagEncode 3 tail).length + tagComplementCode tail := by
  rw [tagComplementCode_replicate_c_append, tagComplementCode_cons_b]

private theorem firstBLate_normalized_root_of_core_zero
    (r T E x y z : Nat) (scale_positive : 0 < T)
    (core_zero :
      bZeroBDefectCOneCodeCore ((r * T : Nat) : ℚ)
        ((r * T : Nat) - 1 - (39 * T + E)) x y z = 0) :
    let a : ℚ := r * (72 * y - 9) + (9 - 8 * y) / T
    let d : ℚ := 39 + E / T
    parabolicOuterRootDenominator a d z * x =
      parabolicOuterRootNumerator a d y z := by
  have scale_nonzero : (T : ℚ) ≠ 0 := by exact_mod_cast scale_positive.ne'
  rw [bZeroBDefectCOneCodeCore_thin_decomposition] at core_zero
  unfold bZeroBDefectCOneWaitFactor bZeroBDefectCOneRootPencil
    bZeroBDefectCOneComplementCore at core_zero
  push_cast at core_zero
  dsimp only
  unfold parabolicOuterRootDenominator parabolicOuterRootNumerator
  field_simp [scale_nonzero]
  linear_combination core_zero

private theorem firstBLate_core_zero_in_complement_coordinates
    (k : Nat) (tail : List TagLetter) (x y z : Nat)
    (core_zero :
      bZeroBDefectCOneCodeCore
        ((3 : ℚ) ^
          (tagEncode 3 (List.replicate k .c ++ .b :: tail)).length)
        (ternaryCode (tagEncode 3 (List.replicate k .c ++ .b :: tail))) x y z = 0) :
    let r := firstBLatePrefixScale k
    let T : Nat := 3 ^ (tagEncode 3 tail).length
    let E := tagComplementCode tail
    bZeroBDefectCOneCodeCore ((r * T : Nat) : ℚ)
      ((r * T : Nat) - 1 - (39 * T + E)) x y z = 0 := by
  let body := List.replicate k .c ++ .b :: tail
  let r := firstBLatePrefixScale k
  let T : Nat := 3 ^ (tagEncode 3 tail).length
  let E := tagComplementCode tail
  let S : Nat := 3 ^ (tagEncode 3 body).length
  let C := ternaryCode (tagEncode 3 body)
  let D := tagComplementCode body
  have scale_eq : S = r * T := by
    dsimp [S, r, T, body]
    exact firstBLate_scale k tail
  have complement_eq : D = 39 * T + E := by
    dsimp [D, T, E, body]
    exact firstBLate_complement k tail
  have code_lt : C < S := by
    dsimp [C, S, body]
    exact ternaryCode_lt_pow_length
      (tagEncode 3 (List.replicate k .c ++ .b :: tail))
  have complement_nat : D = S - C - 1 := rfl
  have coordinate_sum : C + D + 1 = S := by omega
  have code_eq : (C : ℚ) = (S : ℚ) - 1 - D := by
    have coordinate_sum_rat : (C : ℚ) + D + 1 = S := by
      exact_mod_cast coordinate_sum
    linarith
  have scale_cast :
      (S : ℚ) =
        (3 : ℚ) ^ (tagEncode 3 (List.replicate k .c ++ .b :: tail)).length := by
    dsimp [S, body]
    norm_num
  rw [← scale_cast] at core_zero
  change bZeroBDefectCOneCodeCore (S : ℚ) (C : ℚ) x y z = 0 at core_zero
  rw [code_eq, scale_eq, complement_eq] at core_zero
  dsimp only
  push_cast at core_zero
  push_cast
  simpa only [r, T, E, Nat.cast_pow, Nat.cast_ofNat] using core_zero

private theorem firstBLate_physical_parameters
    (k : Nat) (tail : List TagLetter) (contains_b : .b ∈ tail) (y : Nat) :
    let r : Nat := firstBLatePrefixScale k
    let T : Nat := 3 ^ (tagEncode 3 tail).length
    let E := tagComplementCode tail
    let a : ℚ := r * (72 * y - 9) + (9 - 8 * y) / T
    let d : ℚ := 39 + E / T
    243 ≤ T ∧ 39 ≤ d ∧ d ≤ 9477 / 242 ∧
      (2 ≤ y →
        r * (72 * y - 9) + (9 - 8 * y) / 243 ≤ a ∧
          a ≤ r * (72 * y - 9)) := by
  let r : Nat := firstBLatePrefixScale k
  let T : Nat := 3 ^ (tagEncode 3 tail).length
  let E := tagComplementCode tail
  let a : ℚ := r * (72 * y - 9) + (9 - 8 * y) / T
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
    have bound_rat : (242 : ℚ) * E ≤ 39 * T := by
      exact_mod_cast complement_bound_nat
    simpa only [mul_comm] using bound_rat
  have d_lower : (39 : ℚ) ≤ d := by
    dsimp [d]
    have quotient_nonnegative : (0 : ℚ) ≤ (E : ℚ) / T := by positivity
    linarith
  have d_upper : d ≤ (9477 / 242 : ℚ) := by
    dsimp [d]
    norm_num
    linarith
  refine ⟨scale_bound, d_lower, d_upper, ?_⟩
  intro two_le_y
  have y_large : (2 : ℚ) ≤ y := by exact_mod_cast two_le_y
  have numerator_nonpositive : (9 : ℚ) - 8 * y ≤ 0 := by linarith
  have scale_bound_rat : (243 : ℚ) ≤ T := by exact_mod_cast scale_bound
  have scaled_numerator :
      ((9 : ℚ) - 8 * y) * T ≤ ((9 : ℚ) - 8 * y) * 243 :=
    mul_le_mul_of_nonpos_left scale_bound_rat numerator_nonpositive
  have fraction_lower : ((9 : ℚ) - 8 * y) / 243 ≤ (9 - 8 * y) / T := by
    rw [div_le_div_iff₀ (by norm_num) scale_positive]
    simpa only [mul_comm] using scaled_numerator
  have fraction_upper : ((9 : ℚ) - 8 * y) / T ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg numerator_nonpositive scale_positive.le
  constructor <;> linarith

theorem firstBLate_lower_denominator_positive
    (k y : Nat) (three_le_k : 3 ≤ k) (k_le : k ≤ 11) (two_le_y : 2 ≤ y) :
    0 < firstBLateRootLowerDenominator k y := by
  interval_cases k <;>
    norm_num [firstBLateRootLowerDenominator, firstBLatePrefixScale] <;>
    omega

theorem firstBLate_upper_denominator_positive
    (k y : Nat) (three_le_k : 3 ≤ k) (k_le : k ≤ 11) (two_le_y : 2 ≤ y) :
    0 < firstBLateRootUpperDenominator k y := by
  interval_cases k <;>
    norm_num [firstBLateRootUpperDenominator, firstBLatePrefixScale] <;>
    omega

/-- A physical later-position zero satisfies the common normalized outer-root equation. -/
theorem firstBLate_normalized_root_eq_of_core_zero
    (k : Nat) (tail : List TagLetter) (x y z : Nat)
    (core_zero :
      bZeroBDefectCOneCodeCore
        ((3 : ℚ) ^
          (tagEncode 3 (List.replicate k .c ++ .b :: tail)).length)
        (ternaryCode (tagEncode 3 (List.replicate k .c ++ .b :: tail))) x y z = 0) :
    let T : Nat := 3 ^ (tagEncode 3 tail).length
    let E := tagComplementCode tail
    let a : ℚ := firstBLatePrefixScale k * (72 * y - 9) + (9 - 8 * y) / T
    let d : ℚ := 39 + E / T
    parabolicOuterRootDenominator a d z * x =
      parabolicOuterRootNumerator a d y z := by
  let r := firstBLatePrefixScale k
  let T : Nat := 3 ^ (tagEncode 3 tail).length
  let E := tagComplementCode tail
  have scale_positive : 0 < T := by
    dsimp [T]
    positivity
  have complement_core_zero :=
    firstBLate_core_zero_in_complement_coordinates k tail x y z core_zero
  dsimp only at complement_core_zero
  simpa only [r] using
    firstBLate_normalized_root_of_core_zero r T E x y z scale_positive
      complement_core_zero

/-- The same normalized equation solved for the inner wait. -/
theorem firstBLate_z_equation_of_core_zero
    (k : Nat) (tail : List TagLetter) (x y z : Nat)
    (core_zero :
      bZeroBDefectCOneCodeCore
        ((3 : ℚ) ^
          (tagEncode 3 (List.replicate k .c ++ .b :: tail)).length)
        (ternaryCode (tagEncode 3 (List.replicate k .c ++ .b :: tail))) x y z = 0) :
    let T : Nat := 3 ^ (tagEncode 3 tail).length
    let E := tagComplementCode tail
    let a : ℚ := firstBLatePrefixScale k * (72 * y - 9) + (9 - 8 * y) / T
    let d : ℚ := 39 + E / T
    firstBTwoTailZDenominator a d x y * z =
      firstBTwoTailZNumerator a d x y := by
  have root_eq := firstBLate_normalized_root_eq_of_core_zero k tail x y z core_zero
  dsimp only at root_eq ⊢
  unfold parabolicOuterRootDenominator parabolicOuterRootNumerator at root_eq
  unfold firstBTwoTailZDenominator firstBTwoTailZNumerator
  linear_combination -root_eq

/-- A physical zero at first-`b` position `k ∈ [3,11]` and middle wait at least two lies
inside the exact cleared outer-root window. -/
theorem firstBLateRootWindow_of_core_zero
    (k : Nat) (tail : List TagLetter) (contains_b : .b ∈ tail)
    (x y z : Nat) (three_le_k : 3 ≤ k) (k_le : k ≤ 11) (two_le_y : 2 ≤ y)
    (core_zero :
      bZeroBDefectCOneCodeCore
        ((3 : ℚ) ^
          (tagEncode 3 (List.replicate k .c ++ .b :: tail)).length)
        (ternaryCode (tagEncode 3 (List.replicate k .c ++ .b :: tail))) x y z = 0) :
    FirstBLateRootWindow k x y := by
  let r : Nat := firstBLatePrefixScale k
  let T : Nat := 3 ^ (tagEncode 3 tail).length
  let E := tagComplementCode tail
  let a : ℚ := r * (72 * y - 9) + (9 - 8 * y) / T
  let d : ℚ := 39 + E / T
  let a₀ : ℚ := r * (72 * y - 9) + (9 - 8 * y) / 243
  let a₁ : ℚ := r * (72 * y - 9)
  let d₀ : ℚ := 39
  let d₁ : ℚ := 9477 / 242
  have parameters := firstBLate_physical_parameters k tail contains_b y
  dsimp only at parameters
  have scale_positive : 0 < T := lt_of_lt_of_le (by norm_num) parameters.1
  have a_bounds := parameters.2.2.2 two_le_y
  have a_lower : a₀ ≤ a := by
    simpa only [a₀, a, r] using a_bounds.1
  have a_upper : a ≤ a₁ := by
    simpa only [a₁, a, r] using a_bounds.2
  have a₀_positive : 0 < a₀ := by
    dsimp [a₀, r]
    have y_large : (2 : ℚ) ≤ y := by exact_mod_cast two_le_y
    interval_cases k <;> norm_num [firstBLatePrefixScale] <;> nlinarith
  have a_positive : 0 < a := lt_of_lt_of_le a₀_positive a_lower
  have a₁_positive : 0 < a₁ := by
    have factor_positive : (0 : ℚ) < 72 * y - 9 := by
      have y_large : (2 : ℚ) ≤ y := by exact_mod_cast two_le_y
      linarith
    have r_positive : (0 : ℚ) < r := by
      dsimp [r, firstBLatePrefixScale]
      positivity
    dsimp only [a₁]
    exact mul_pos r_positive factor_positive
  have d₀_positive : 0 < d₀ := by norm_num [d₀]
  have d_positive : 0 < d := lt_of_lt_of_le d₀_positive parameters.2.1
  have d₁_positive : 0 < d₁ := by norm_num [d₁]
  have worst_margin : d₁ * (1296 * (y : ℚ) + 84099) < 38 * a₀ := by
    dsimp [a₀, d₁, r]
    have y_large : (2 : ℚ) ≤ y := by exact_mod_cast two_le_y
    interval_cases k <;> norm_num [firstBLatePrefixScale] <;> nlinarith
  have factor_nonnegative : (0 : ℚ) ≤ 1296 * y + 84099 := by positivity
  have scaled_d : d * (1296 * (y : ℚ) + 84099) ≤
      d₁ * (1296 * y + 84099) :=
    mul_le_mul_of_nonneg_right parameters.2.2.1 factor_nonnegative
  have margin : d * (1296 * (y : ℚ) + 84099) < 38 * a := by
    have below_a₀ := scaled_d.trans_lt worst_margin
    have scaled_a := mul_le_mul_of_nonneg_left a_lower (by norm_num : (0 : ℚ) ≤ 38)
    exact below_a₀.trans_le scaled_a
  have complement_core_zero :=
    firstBLate_core_zero_in_complement_coordinates k tail x y z core_zero
  dsimp only at complement_core_zero
  have root_eq : parabolicOuterRootDenominator a d z * x =
      parabolicOuterRootNumerator a d y z := by
    simpa only [a, d, r] using
      firstBLate_normalized_root_of_core_zero r T E x y z scale_positive
        complement_core_zero
  have root_value :
      parabolicOuterRootNumerator a d y z / parabolicOuterRootDenominator a d z = x :=
    parabolicOuterRoot_eq a d y z x a_positive d_positive (by positivity) root_eq
  have lower_bound :
      parabolicOuterRootNumerator a₀ d₁ y 0 /
          parabolicOuterRootDenominator a₀ d₁ 0 ≤ (x : ℚ) := by
    calc
      _ ≤ parabolicOuterRootNumerator a₀ d y 0 /
          parabolicOuterRootDenominator a₀ d 0 :=
        parabolicOuterRoot_decreases_d a₀ d d₁ y 0 parameters.2.2.1
          a₀_positive d_positive (by positivity) (by positivity)
      _ ≤ parabolicOuterRootNumerator a d y 0 /
          parabolicOuterRootDenominator a d 0 :=
        parabolicOuterRoot_increases_a a₀ a d y 0 a_lower a₀_positive
          d_positive (by positivity) (by positivity)
      _ ≤ parabolicOuterRootNumerator a d y z /
          parabolicOuterRootDenominator a d z :=
        parabolicOuterRoot_increases_z a d y 0 z (by positivity) a_positive d_positive
          (by positivity) margin
      _ = x := root_value
  have upper_bound :
      (x : ℚ) < parabolicOuterAsymptoteNumerator a₁ d₀ y /
        parabolicOuterAsymptoteDenominator a₁ d₀ := by
    rw [← root_value]
    calc
      _ < parabolicOuterAsymptoteNumerator a d y /
          parabolicOuterAsymptoteDenominator a d :=
        parabolicOuterRoot_lt_asymptote a d y z a_positive d_positive (by positivity) margin
      _ ≤ parabolicOuterAsymptoteNumerator a₁ d y /
          parabolicOuterAsymptoteDenominator a₁ d :=
        parabolicOuterAsymptote_increases_a a a₁ d y a_upper a_positive d_positive
          (by positivity)
      _ ≤ parabolicOuterAsymptoteNumerator a₁ d₀ y /
          parabolicOuterAsymptoteDenominator a₁ d₀ :=
        parabolicOuterAsymptote_decreases_d a₁ d₀ d y parameters.2.1
          a₁_positive d₀_positive (by positivity)
  have lower_identity :
      ((firstBLateRootLowerNumerator k y : ℤ) : ℚ) /
          firstBLateRootLowerDenominator k y =
        parabolicOuterRootNumerator a₀ d₁ y 0 /
          parabolicOuterRootDenominator a₀ d₁ 0 := by
    have numerator_identity :
        ((firstBLateRootLowerNumerator k y : ℤ) : ℚ) =
          243 * 242 * parabolicOuterRootNumerator a₀ d₁ y 0 := by
      dsimp [a₀, d₁, r]
      unfold firstBLateRootLowerNumerator firstBLatePrefixScale
        parabolicOuterRootNumerator
      push_cast
      ring
    have denominator_identity :
        ((firstBLateRootLowerDenominator k y : ℤ) : ℚ) =
          243 * 242 * parabolicOuterRootDenominator a₀ d₁ 0 := by
      dsimp [a₀, d₁, r]
      unfold firstBLateRootLowerDenominator firstBLatePrefixScale
        parabolicOuterRootDenominator
      push_cast
      ring
    rw [numerator_identity, denominator_identity]
    ring
  have upper_identity :
      ((firstBLateRootUpperNumerator k y : ℤ) : ℚ) /
          firstBLateRootUpperDenominator k y =
        parabolicOuterAsymptoteNumerator a₁ d₀ y /
          parabolicOuterAsymptoteDenominator a₁ d₀ := by
    have numerator_identity :
        ((firstBLateRootUpperNumerator k y : ℤ) : ℚ) =
          parabolicOuterAsymptoteNumerator a₁ d₀ y := by
      dsimp [a₁, d₀, r]
      unfold firstBLateRootUpperNumerator firstBLatePrefixScale
        parabolicOuterAsymptoteNumerator
      push_cast
      ring
    have denominator_identity :
        ((firstBLateRootUpperDenominator k y : ℤ) : ℚ) =
          parabolicOuterAsymptoteDenominator a₁ d₀ := by
      dsimp [a₁, d₀, r]
      unfold firstBLateRootUpperDenominator firstBLatePrefixScale
        parabolicOuterAsymptoteDenominator
      push_cast
      ring
    rw [numerator_identity, denominator_identity]
  have lower_denominator_positive :=
    firstBLate_lower_denominator_positive k y three_le_k k_le two_le_y
  have upper_denominator_positive :=
    firstBLate_upper_denominator_positive k y three_le_k k_le two_le_y
  unfold FirstBLateRootWindow
  constructor
  · rw [← lower_identity] at lower_bound
    have denominator_rat : (0 : ℚ) < firstBLateRootLowerDenominator k y := by
      exact_mod_cast lower_denominator_positive
    have crossed := (div_le_iff₀ denominator_rat).mp lower_bound
    exact_mod_cast crossed
  · rw [← upper_identity] at upper_bound
    have denominator_rat : (0 : ℚ) < firstBLateRootUpperDenominator k y := by
      exact_mod_cast upper_denominator_positive
    have crossed := (lt_div_iff₀ denominator_rat).mp upper_bound
    exact_mod_cast crossed

end MatrixMortality.ParabolicBlade
