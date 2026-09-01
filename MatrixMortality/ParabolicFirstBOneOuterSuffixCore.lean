import MatrixMortality.ParabolicFirstBOneInnerCore
import MatrixMortality.ParabolicFirstBOneOuterCore

/-!
# Exact suffix balance below outer wait 211

The normalized `cb` balance is uniform in the outer wait. Removing the tail's first `b`
turns it into the same parameter-free suffix grammar used at outer wait 211. This module
separates that analytic reduction from the generated terminal certificate.
-/

namespace MatrixMortality.ParabolicBlade

/-- Positive all-`c` pencil on the retained outer-wait range. -/
def firstBOneOuterQ (x z : Nat) : ℤ :=
  (25766986436 - 119911680 * (x : ℤ)) * z +
    (2408152393 - 11209824 * (x : ℤ))

/-- Complement coefficient in the normalized `cb` balance. -/
def firstBOneOuterJ (x y z : Nat) : ℤ :=
  631601581536 * (x : ℤ) * z + 59048086536 * x +
    620717828832 * y * z + 58005064872 * y +
    422435605080 * z + 37838186340

/-- Scale coefficient in the normalized `cb` balance. -/
def firstBOneOuterScaleCoefficient (x y z : Nat) : ℤ :=
  729 * (72 * y - 9) * firstBOneOuterQ x z

/-- Finite-scale correction in the normalized `cb` balance. -/
def firstBOneOuterCorrection (x y z : Nat) : ℤ :=
  (8 * y - 9) * firstBOneOuterQ x z

/-- The parameter-free suffix grammar, exposed under its uniform outer-wait name. -/
abbrev FirstBOneOuterSuffixCore := FirstBOneX211SuffixCore

/-- Removing a leading `c` triples the suffix coefficient. -/
theorem firstBOneOuterSuffixCore_cons_c
    (body : List TagLetter) (H J B : ℤ)
    (core : FirstBOneOuterSuffixCore (.c :: body) H J B) :
    FirstBOneOuterSuffixCore body (3 * H) J B :=
  firstBOneX211SuffixCore_cons_c body H J B core

/-- Removing a leading `b` applies the exact affine suffix transition. -/
theorem firstBOneOuterSuffixCore_cons_b
    (body : List TagLetter) (H J B : ℤ)
    (core : FirstBOneOuterSuffixCore (.b :: body) H J B) :
    FirstBOneOuterSuffixCore body (243 * H - 39 * J) J B :=
  firstBOneX211SuffixCore_cons_b body H J B core

/-- A nonpositive suffix coefficient cannot balance a positive correction. -/
theorem firstBOneOuterSuffixCore_false_of_nonpositive
    (body : List TagLetter) (H J B : ℤ) (J_positive : 0 < J)
    (B_positive : 0 < B) (H_nonpositive : H ≤ 0)
    (core : FirstBOneOuterSuffixCore body H J B) : False :=
  firstBOneX211SuffixCore_false_of_nonpositive
    body H J B J_positive B_positive H_nonpositive core

/-- The global complement wall excludes a suffix coefficient above its density ceiling. -/
theorem firstBOneOuterSuffixCore_false_of_global
    (body : List TagLetter) (H J B : ℤ) (J_positive : 0 < J)
    (B_positive : 0 < B)
    (coefficient_large : 242 * H - 39 * J > 242 * B)
    (core : FirstBOneOuterSuffixCore body H J B) : False :=
  firstBOneX211SuffixCore_false_of_global
    body H J B J_positive B_positive coefficient_large core

/-- Either side of the first-`b` separator contradicts the displayed strict gap. -/
theorem firstBOneOuterSuffixCore_false_of_gap
    (k : Nat) (body : List TagLetter) (H J B : ℤ) (J_positive : 0 < J)
    (B_positive : 0 < B)
    (low_impossible : 242 * (3 : ℤ) ^ (k + 1) * H - 39 * J >
      242 * (3 : ℤ) ^ (k + 1) * B)
    (high_impossible : 81 * (3 : ℤ) ^ k * H - 13 * J < 0)
    (core : FirstBOneOuterSuffixCore body H J B) : False :=
  firstBOneX211SuffixCore_false_of_gap k body H J B J_positive B_positive
    low_impossible high_impossible core

/-- The empty suffix is impossible when its coefficient differs from the correction. -/
theorem firstBOneOuterSuffixCore_false_of_nil
    (H J B : ℤ) (different : H ≠ B)
    (core : FirstBOneOuterSuffixCore [] H J B) : False :=
  firstBOneX211SuffixCore_false_of_nil H J B different core

private theorem firstBOneOuter_replicate_c_length (j : Nat) :
    (tagEncode 3 (List.replicate j .c)).length = j := by
  induction j with
  | zero => rfl
  | succ j induction =>
      rw [List.replicate_succ, tagEncode_cons, List.length_append]
      simp only [tagCode, List.length_singleton, induction]
      omega

/-- Exact suffix coefficient after `j` leading `c` letters and the first tail `b`. -/
def firstBOneOuterSuffixH (j x y z : Nat) : ℤ :=
  243 * (3 : ℤ) ^ j *
      (firstBOneOuterScaleCoefficient x y z - 39 * firstBOneOuterJ x y z) -
    39 * firstBOneOuterJ x y z

/-- A physical `cb` zero satisfies the exact tail-complement balance. -/
theorem firstBOneOuter_core_balance
    (tail : List TagLetter) (x y z : Nat)
    (core_zero :
      bZeroBDefectCOneCodeCore
        ((3 : ℚ) ^ (tagEncode 3 ([.c, .b] ++ tail)).length)
        (ternaryCode (tagEncode 3 ([.c, .b] ++ tail))) x y z = 0) :
    let T : Nat := 3 ^ (tagEncode 3 tail).length
    let E : Nat := tagComplementCode tail
    ((39 * T + E : Nat) : ℤ) * firstBOneOuterJ x y z =
      (T : ℤ) * firstBOneOuterScaleCoefficient x y z -
        firstBOneOuterCorrection x y z := by
  let body := [.c, .b] ++ tail
  let T : Nat := 3 ^ (tagEncode 3 tail).length
  let E : Nat := tagComplementCode tail
  let S : Nat := 3 ^ (tagEncode 3 body).length
  let C : Nat := ternaryCode (tagEncode 3 body)
  let D : Nat := tagComplementCode body
  have scale_eq : S = 729 * T := by
    dsimp [S, T, body]
    simp only [List.length_append, tagCode, List.length_singleton, pow_add]
    norm_num
    ring
  have complement_eq : D = 39 * T + E := by
    dsimp [D, T, E, body]
    rw [tagComplementCode_cons_c, tagComplementCode_cons_b]
  have code_lt : C < S := by
    dsimp [C, S, body]
    exact ternaryCode_lt_pow_length (tagEncode 3 ([.c, .b] ++ tail))
  have complement_nat : D = S - C - 1 := rfl
  have coordinate_sum : C + D + 1 = S := by omega
  have code_eq_int : (C : ℤ) = 729 * T - 1 - (39 * T + E) := by
    have coordinate_sum_int : (C : ℤ) + D + 1 = S := by
      exact_mod_cast coordinate_sum
    have scale_eq_int : (S : ℤ) = 729 * T := by exact_mod_cast scale_eq
    have complement_eq_int : (D : ℤ) = 39 * T + E := by
      exact_mod_cast complement_eq
    omega
  have scale_cast :
      (S : ℚ) = (3 : ℚ) ^ (tagEncode 3 ([.c, .b] ++ tail)).length := by
    dsimp [S, body]
    norm_num
  rw [← scale_cast] at core_zero
  change bZeroBDefectCOneCodeCore (S : ℚ) (C : ℚ) x y z = 0 at core_zero
  have core_zero_int :
      bZeroBDefectCOneCodeCore (S : ℤ) (C : ℤ) x y z = 0 := by
    unfold bZeroBDefectCOneCodeCore at core_zero ⊢
    exact_mod_cast core_zero
  rw [scale_eq, code_eq_int] at core_zero_int
  change ((39 * T + E : Nat) : ℤ) * firstBOneOuterJ x y z =
    (T : ℤ) * firstBOneOuterScaleCoefficient x y z -
      firstBOneOuterCorrection x y z
  push_cast at core_zero_int ⊢
  unfold bZeroBDefectCOneCodeCore at core_zero_int
  unfold firstBOneOuterJ firstBOneOuterScaleCoefficient
    firstBOneOuterCorrection firstBOneOuterQ
  linear_combination core_zero_int

/-- Removing the tail's first `b` turns a physical zero into the uniform suffix grammar. -/
theorem firstBOneOuterSuffixCore_of_core_zero
    (j : Nat) (tail rest : List TagLetter) (x y z : Nat)
    (first_b : tail = List.replicate j .c ++ .b :: rest)
    (core_zero :
      bZeroBDefectCOneCodeCore
        ((3 : ℚ) ^ (tagEncode 3 ([.c, .b] ++ tail)).length)
        (ternaryCode (tagEncode 3 ([.c, .b] ++ tail))) x y z = 0) :
    FirstBOneOuterSuffixCore rest (firstBOneOuterSuffixH j x y z)
      (firstBOneOuterJ x y z) (firstBOneOuterCorrection x y z) := by
  let R : Nat := 3 ^ (tagEncode 3 rest).length
  let G : Nat := tagComplementCode rest
  let T : Nat := 3 ^ (tagEncode 3 tail).length
  let E : Nat := tagComplementCode tail
  have scale_eq : T = 3 ^ j * 243 * R := by
    dsimp [T, R]
    rw [first_b, tagEncode_append, List.length_append,
      firstBOneOuter_replicate_c_length, tagEncode_cons, List.length_append,
      pow_add, pow_add]
    norm_num [tagCode]
    ring
  have complement_eq : E = 39 * R + G := by
    dsimp [E, R, G]
    rw [first_b, tagComplementCode_replicate_c_append, tagComplementCode_cons_b]
  have balance := firstBOneOuter_core_balance tail x y z core_zero
  change ((39 * T + E : Nat) : ℤ) * firstBOneOuterJ x y z =
    (T : ℤ) * firstBOneOuterScaleCoefficient x y z -
      firstBOneOuterCorrection x y z at balance
  rw [scale_eq, complement_eq] at balance
  dsimp [R, G] at balance
  unfold FirstBOneOuterSuffixCore FirstBOneX211SuffixCore firstBOneOuterSuffixH
  linear_combination balance

/-- The sole lower-range ray left by the outer-root certificate stops before inner wait
`1448`. -/
theorem firstBOneOuterRay_z_lt_1448
    (body : List TagLetter) (z : Nat)
    (core : FirstBOneOuterSuffixCore body (firstBOneOuterSuffixH 1 210 801 z)
      (firstBOneOuterJ 210 801 z) (firstBOneOuterCorrection 210 801 z)) :
    z < 1448 := by
  by_contra z_not_small
  have z_large : 1448 ≤ z := by omega
  apply firstBOneOuterSuffixCore_false_of_gap 0 body
    (firstBOneOuterSuffixH 1 210 801 z)
    (firstBOneOuterJ 210 801 z) (firstBOneOuterCorrection 210 801 z)
  · unfold firstBOneOuterJ
    positivity
  · unfold firstBOneOuterCorrection firstBOneOuterQ
    positivity
  · norm_num [firstBOneOuterSuffixH, firstBOneOuterScaleCoefficient,
      firstBOneOuterCorrection, firstBOneOuterQ, firstBOneOuterJ]
    nlinarith
  · norm_num [firstBOneOuterSuffixH, firstBOneOuterScaleCoefficient,
      firstBOneOuterCorrection, firstBOneOuterQ, firstBOneOuterJ]
    nlinarith
  · exact core

end MatrixMortality.ParabolicBlade
