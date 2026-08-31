import MatrixMortality.SwappedSetterFringeLanguage
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Swapped-setter fringe classification

This file classifies the regular-language fringes left by a positive depth-one transfer in the
swapped ternary setter.
-/

namespace MatrixMortality.SwappedSetterFringe

theorem swappedCode_append (left right : List Bool) :
    swappedCode (left ++ right) =
      3 ^ right.length * swappedCode left + swappedCode right := by
  simp [swappedCode, ternaryCode_append]

theorem swappedCode_cons (head : Bool) (tail : List Bool) :
    swappedCode (head :: tail) =
      3 ^ tail.length * ternaryDigit (!head) + swappedCode tail := by
  simp [swappedCode, ternaryCode_cons]

@[simp] theorem swappedCode_nil : swappedCode [] = 0 := by
  rfl

@[simp] theorem swappedCode_false : swappedCode [false] = 2 := by
  decide

@[simp] theorem swappedCode_true : swappedCode [true] = 1 := by
  decide

theorem swappedCode_replicate_false (length : Nat) :
    swappedCode (List.replicate length false) + 1 = 3 ^ length := by
  induction length with
  | zero => simp
  | succ length induction =>
      rw [List.replicate_succ, swappedCode_cons]
      simp only [List.length_replicate, Bool.not_false, ternaryDigit]
      rw [pow_succ]
      omega

theorem swappedCode_replicate_true (length : Nat) :
    2 * swappedCode (List.replicate length true) + 1 = 3 ^ length := by
  induction length with
  | zero => simp
  | succ length induction =>
      rw [List.replicate_succ, swappedCode_cons]
      simp only [List.length_replicate, Bool.not_true, ternaryDigit]
      rw [pow_succ]
      omega

theorem swappedCode_true_false_run (ones zeros : Nat) :
    2 * swappedCode
        (List.replicate ones true ++ List.replicate zeros false) + 2 =
      3 ^ (ones + zeros) + 3 ^ zeros := by
  rw [swappedCode_append, List.length_replicate,
    ]
  have false_code := swappedCode_replicate_false zeros
  have true_code := swappedCode_replicate_true ones
  rw [pow_add]
  nlinarith

theorem swappedCode_pair_zero_tail (front : List Bool) (zeros : Nat) :
    swappedCode (front ++ [true, true] ++ List.replicate zeros false) + 1 =
      3 ^ zeros * (9 * swappedCode front + 5) := by
  rw [swappedCode_append, swappedCode_append,
    List.length_replicate]
  have pair_code : swappedCode [true, true] = 4 := by decide
  rw [pair_code]
  norm_num
  have false_code := swappedCode_replicate_false zeros
  nlinarith

theorem swappedCode_lt_pow_length (word : List Bool) :
    swappedCode word < 3 ^ word.length := by
  simpa [swappedCode] using ternaryCode_lt_pow_length (word.map Bool.not)

private theorem swappedCode_append_singleton_mod_three (front : List Bool) (bit : Bool) :
    swappedCode (front ++ [bit]) % 3 = if bit then 1 else 2 := by
  rw [swappedCode_append]
  cases bit <;> norm_num [swappedCode, ternaryCode, ternaryDigit]

theorem swappedCode_modEq_zero_iff (word : List Bool) :
    swappedCode word ≡ 0 [MOD 3] ↔ word = [] := by
  induction word using List.reverseRecOn with
  | nil => decide
  | append_singleton front bit =>
      rw [Nat.ModEq, swappedCode_append_singleton_mod_three]
      cases bit <;> norm_num

theorem swappedCode_modEq_two_iff_getLast?_false (word : List Bool) :
    swappedCode word ≡ 2 [MOD 3] ↔ word.getLast? = some false := by
  induction word using List.reverseRecOn with
  | nil => decide
  | append_singleton front bit =>
      rw [Nat.ModEq, swappedCode_append_singleton_mod_three]
      cases bit <;> norm_num

theorem swappedCode_modEq_one_iff_getLast?_true (word : List Bool) :
    swappedCode word ≡ 1 [MOD 3] ↔ word.getLast? = some true := by
  induction word using List.reverseRecOn with
  | nil => decide
  | append_singleton front bit =>
      rw [Nat.ModEq, swappedCode_append_singleton_mod_three]
      cases bit <;> norm_num

private theorem getLast?_replicate_of_pos (bit : Bool) {length : Nat}
    (length_pos : 0 < length) :
    (List.replicate length bit).getLast? = some bit := by
  obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : length ≠ 0)
  rw [List.replicate_succ']
  simp

theorem swappedCode_append_false_false_modEq (front : List Bool) :
    swappedCode (front ++ [false, false]) ≡ 8 [MOD 9] := by
  rw [swappedCode_append]
  have pair_code : swappedCode [false, false] = 8 := by decide
  rw [pair_code]
  exact Nat.ModEq.modulus_mul_add

private theorem replicate_false_suffix_two {length : Nat} (two_le : 2 ≤ length) :
    ∃ front, List.replicate length false = front ++ [false, false] := by
  refine ⟨List.replicate (length - 2) false, ?_⟩
  change List.replicate length false =
    List.replicate (length - 2) false ++ List.replicate 2 false
  rw [← List.replicate_add]
  congr 1
  omega

theorem targetFringe_ends_double_false {width : Nat} (width_large : 3 ≤ width)
    {word : List Bool} (target : TargetFringe width word) :
    ∃ front, word = front ++ [false, false] := by
  rcases target with ⟨_, zero_run | pair_run | cut⟩
  · obtain ⟨zeros, two_le, rfl⟩ := zero_run
    exact replicate_false_suffix_two two_le
  · obtain ⟨front, zeros, two_le, rfl⟩ := pair_run
    obtain ⟨tail, tail_eq⟩ := replicate_false_suffix_two two_le
    refine ⟨front ++ [true, true] ++ tail, ?_⟩
    simp [tail_eq, List.append_assoc]
  · obtain ⟨_, rfl⟩ := cut
    obtain ⟨tail, tail_eq⟩ := replicate_false_suffix_two (show 2 ≤ width - 1 by omega)
    refine ⟨true :: tail, ?_⟩
    simp [tail_eq]

theorem targetFringe_code_modEq_eight {width : Nat} (width_large : 3 ≤ width)
    {word : List Bool} (target : TargetFringe width word) :
    swappedCode word ≡ 8 [MOD 9] := by
  obtain ⟨front, rfl⟩ := targetFringe_ends_double_false width_large target
  exact swappedCode_append_false_false_modEq front

/-- The body-independent congruence left by a positive depth-one pole. -/
def PoleCongruence (β : Nat) (upper source target : List Bool) : Prop :=
  let δ : ℤ := swappedCode upper - swappedCode source
  δ * ((3 : ℤ) ^ β - 2) ≡
    (6 * (3 : ℤ) ^ β - 3 - δ) * swappedCode target
      [ZMOD 9 * (3 : ℤ) ^ β]

private theorem pole_delta_modEq_neg_one
    {β : Nat} {δ σ : ℤ} (β_large : 2 ≤ β)
    (target_mod : σ ≡ -1 [ZMOD 9])
    (pole :
      δ * ((3 : ℤ) ^ β - 2) ≡
        (6 * (3 : ℤ) ^ β - 3 - δ) * σ [ZMOD 9 * (3 : ℤ) ^ β]) :
    δ ≡ -1 [ZMOD 3] := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le β_large
  have rho_zero : (3 : ℤ) ^ (2 + extra) ≡ 0 [ZMOD 9] := by
    apply Dvd.dvd.modEq_zero_int
    refine ⟨(3 : ℤ) ^ extra, ?_⟩
    rw [pow_add]
    norm_num
  have pole_nine := pole.of_dvd (show (9 : ℤ) ∣ 9 * 3 ^ (2 + extra) by simp)
  have difference_mod :
      (3 : ℤ) * ((-1) - δ) ≡ 0 [ZMOD 9] := by
    have reduced :
        δ * (-2) ≡ (-3 - δ) * (-1) [ZMOD 9] :=
      calc
        δ * (-2) ≡ δ * ((3 : ℤ) ^ (2 + extra) - 2) [ZMOD 9] :=
          (Int.ModEq.refl δ).mul
            (rho_zero.sub (Int.ModEq.refl 2)).symm
        _ ≡ (6 * (3 : ℤ) ^ (2 + extra) - 3 - δ) * σ [ZMOD 9] := pole_nine
        _ ≡ (-3 - δ) * (-1) [ZMOD 9] :=
          by
            simpa using (((rho_zero.mul_left 6).sub (Int.ModEq.refl 3)).sub
              (Int.ModEq.refl δ)).mul target_mod
    rw [Int.modEq_iff_dvd] at reduced ⊢
    convert reduced using 1
    ring
  have factored :
      (3 : ℤ) * ((-1) - δ) ≡ 3 * 0 [ZMOD 9] := by
    simpa using difference_mod
  have divided := factored.cancel_left_div_gcd (by norm_num : (0 : ℤ) < 9)
  norm_num at divided
  rw [Int.modEq_iff_dvd] at divided ⊢
  have positive : (3 : ℤ) ∣ 1 + δ := by
    convert divided using 1
    ring
  have negated : (3 : ℤ) ∣ -(1 + δ) := Int.dvd_neg.mpr positive
  convert negated using 1
  ring

theorem poleCongruence_delta_modEq_neg_one {β : Nat} (β_large : 2 ≤ β)
    {upper source target : List Bool} (target_fringe : TargetFringe (β + 2) target)
    (pole : PoleCongruence β upper source target) :
    (swappedCode upper : ℤ) - swappedCode source ≡ -1 [ZMOD 3] := by
  have target_nat := targetFringe_code_modEq_eight (show 3 ≤ β + 2 by omega) target_fringe
  have target_int : (swappedCode target : ℤ) ≡ 8 [ZMOD 9] := by
    exact Int.natCast_modEq_iff.mpr target_nat
  have eight_neg_one : (8 : ℤ) ≡ -1 [ZMOD 9] := by decide
  exact pole_delta_modEq_neg_one β_large (target_int.trans eight_neg_one) pole

private theorem source_eq_nil_of_upper_getLast?_false {upper source : List Bool}
    (upper_last : upper.getLast? = some false)
    (delta_mod :
      (swappedCode upper : ℤ) - swappedCode source ≡ -1 [ZMOD 3]) :
    source = [] := by
  have upper_nat := (swappedCode_modEq_two_iff_getLast?_false upper).mpr upper_last
  have upper_int : (swappedCode upper : ℤ) ≡ 2 [ZMOD 3] :=
    Int.natCast_modEq_iff.mpr upper_nat
  have source_int : (swappedCode source : ℤ) ≡ 0 [ZMOD 3] :=
    calc
      (swappedCode source : ℤ) =
          swappedCode upper - ((swappedCode upper : ℤ) - swappedCode source) := by ring
      _ ≡ 2 - (-1) [ZMOD 3] := upper_int.sub delta_mod
      _ ≡ 0 [ZMOD 3] := by decide
  have source_nat : swappedCode source ≡ 0 [MOD 3] :=
    Int.natCast_modEq_iff.mp source_int
  exact (swappedCode_modEq_zero_iff source).mp source_nat

private theorem source_getLast?_false_of_upper_getLast?_true {upper source : List Bool}
    (upper_last : upper.getLast? = some true)
    (delta_mod :
      (swappedCode upper : ℤ) - swappedCode source ≡ -1 [ZMOD 3]) :
    source.getLast? = some false := by
  have upper_nat := (swappedCode_modEq_one_iff_getLast?_true upper).mpr upper_last
  have upper_int : (swappedCode upper : ℤ) ≡ 1 [ZMOD 3] :=
    Int.natCast_modEq_iff.mpr upper_nat
  have source_int : (swappedCode source : ℤ) ≡ 2 [ZMOD 3] :=
    calc
      (swappedCode source : ℤ) =
          swappedCode upper - ((swappedCode upper : ℤ) - swappedCode source) := by ring
      _ ≡ 1 - (-1) [ZMOD 3] := upper_int.sub delta_mod
      _ ≡ 2 [ZMOD 3] := by decide
  have source_nat : swappedCode source ≡ 2 [MOD 3] :=
    Int.natCast_modEq_iff.mp source_int
  exact (swappedCode_modEq_two_iff_getLast?_false source).mp source_nat

/-- The mod-nine pole sieve separates positive-zero runs from the two upper fringes ending in
one.  A positive-zero run has no lower fringe; the tag and all-one fringes have a complete
zero-ending lower spelling. -/
theorem upperFringe_source_sieve {β : Nat} (β_large : 2 ≤ β)
    {upper source target : List Bool} (upper_fringe : UpperFringe β upper)
    (target_fringe : TargetFringe (β + 2) target)
    (pole : PoleCongruence β upper source target) :
    (∃ ones,
        2 ≤ ones ∧
          ones ≤ β + 1 ∧
            upper = List.replicate ones true ++
              List.replicate (β + 2 - ones) false ∧
              source = []) ∨
      (upper = tagCode β .b ∧ source.getLast? = some false) ∨
      (upper = List.replicate (β + 2) true ∧ source.getLast? = some false) := by
  have delta_mod := poleCongruence_delta_modEq_neg_one β_large target_fringe pole
  rcases upper_fringe with tag | ⟨ones, two_le, ones_le, run⟩
  · right
    left
    refine ⟨tag, source_getLast?_false_of_upper_getLast?_true ?_ delta_mod⟩
    rw [tag]
    change (true :: List.replicate β false ++ [true]).getLast? = some true
    rw [List.getLast?_append_of_ne_nil]
    · simp
    · simp
  · by_cases all_ones : ones = β + 2
    · right
      right
      subst ones
      have upper_eq : upper = List.replicate (β + 2) true := by
        simpa using run
      refine ⟨upper_eq, source_getLast?_false_of_upper_getLast?_true ?_ delta_mod⟩
      rw [upper_eq]
      exact getLast?_replicate_of_pos true (by omega)
    · left
      have ones_short : ones ≤ β + 1 := by omega
      refine ⟨ones, two_le, ones_short, run, ?_⟩
      apply source_eq_nil_of_upper_getLast?_false _ delta_mod
      rw [run, List.getLast?_append_of_ne_nil]
      · exact getLast?_replicate_of_pos false (by omega)
      · simp
        omega

theorem swappedCode_tag_b_add_two (β : Nat) :
    swappedCode (tagCode β .b) + 2 = 6 * 3 ^ β := by
  rw [tagCode]
  simp only [List.cons_append, List.nil_append]
  rw [swappedCode_cons]
  simp only [List.length_append, List.length_replicate, List.length_singleton,
    Bool.not_true, ternaryDigit, pow_succ]
  rw [swappedCode_append]
  norm_num
  have false_code := swappedCode_replicate_false β
  nlinarith

theorem swappedCode_tag_b (β : Nat) :
    swappedCode (tagCode β .b) = 6 * 3 ^ β - 2 := by
  have code := swappedCode_tag_b_add_two β
  have power_pos : 0 < 3 ^ β := pow_pos (by norm_num) β
  omega

end MatrixMortality.SwappedSetterFringe
