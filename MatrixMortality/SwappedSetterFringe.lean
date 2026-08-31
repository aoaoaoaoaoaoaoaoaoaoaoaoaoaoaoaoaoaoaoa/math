import MatrixMortality.SwappedSetterBoundaryInverse
import MatrixMortality.SwappedSetterFringeArithmetic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
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

theorem swappedCode_lower_bound (word : List Bool) (word_nonempty : word ≠ []) :
    3 ^ (word.length - 1) ≤ swappedCode word := by
  have mapped_nonempty : word.map Bool.not ≠ [] := by
    simpa using word_nonempty
  simpa [swappedCode] using ternaryCode_lower_bound (word.map Bool.not) mapped_nonempty

private theorem source_length_le_upper_length {upper source : List Bool}
    (source_nonempty : source ≠ []) (code_lt : swappedCode source < swappedCode upper) :
    source.length ≤ upper.length := by
  by_contra length_not_le
  have exponent_le : upper.length ≤ source.length - 1 := by omega
  have power_le : 3 ^ upper.length ≤ 3 ^ (source.length - 1) :=
    Nat.pow_le_pow_right (by norm_num) exponent_le
  have source_lower := swappedCode_lower_bound source source_nonempty
  have upper_upper := swappedCode_lt_pow_length upper
  omega

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

/-- Exact ternary factor exposed by the final zero run of a target fringe. -/
theorem targetFringe_codeFactor {width : Nat} {word : List Bool}
    (target : TargetFringe width word) :
    (∃ zeros,
        2 ≤ zeros ∧
          word.length ≤ width ∧
            swappedCode word + 1 = 3 ^ zeros) ∨
      (∃ front zeros,
        2 ≤ zeros ∧
          word.length ≤ width ∧
            swappedCode word + 1 = 3 ^ zeros * (9 * swappedCode front + 5)) ∨
      (word.length = width ∧
        swappedCode word + 1 = 2 * 3 ^ (width - 1)) := by
  rcases target with ⟨length_bound, zero_run | pair_run | cut⟩
  · obtain ⟨zeros, two_le, rfl⟩ := zero_run
    exact Or.inl ⟨zeros, two_le, length_bound, swappedCode_replicate_false zeros⟩
  · obtain ⟨front, zeros, two_le, rfl⟩ := pair_run
    exact Or.inr <| Or.inl ⟨front, zeros, two_le, length_bound,
      swappedCode_pair_zero_tail front zeros⟩
  · right
    right
    obtain ⟨length_eq, rfl⟩ := cut
    refine ⟨length_eq, ?_⟩
    have code := swappedCode_true_false_run 1 (width - 1)
    simp only [List.replicate_one, List.cons_append, List.nil_append] at code
    have width_pos : 0 < width := by
      by_contra width_zero
      have : width = 0 := by omega
      subst width
      simp at length_eq
    have sum_eq : 1 + (width - 1) = width := by omega
    rw [sum_eq] at code
    have power_eq : 3 ^ width = 3 * 3 ^ (width - 1) := by
      calc
        3 ^ width = 3 ^ ((width - 1) + 1) := by
          congr 1
          omega
        _ = 3 ^ (width - 1) * 3 := pow_succ _ _
        _ = 3 * 3 ^ (width - 1) := by ring
    nlinarith

private theorem powerFactor_of_modEq_next
    {value exponent factor power : Nat} (value_ne : value ≠ 0)
    (relation : value ≡ 3 ^ power [MOD 3 ^ (power + 1)])
    (factorization : value = 3 ^ exponent * factor)
    (factor_unit : ¬3 ∣ factor) :
    exponent = power ∧ factor ≡ 1 [MOD 3] := by
  have lower_divisor : 3 ^ power ∣ value := by
    exact (relation.dvd_iff (Nat.pow_dvd_pow 3 (by omega))).mpr (dvd_refl _)
  have upper_not_divisor : ¬3 ^ (power + 1) ∣ value := by
    intro divides_value
    have divides_smaller :=
      (relation.dvd_iff (dvd_refl (3 ^ (power + 1)))).mp divides_value
    rw [Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)] at divides_smaller
    omega
  have valuation_lower : power ≤ padicValNat 3 value :=
    (padicValNat_dvd_iff_le value_ne).mp lower_divisor
  have valuation_upper : padicValNat 3 value < power + 1 := by
    rw [← not_le]
    intro upper_le
    exact upper_not_divisor ((padicValNat_dvd_iff_le value_ne).mpr upper_le)
  have factor_ne : factor ≠ 0 := by
    intro factor_zero
    subst factor
    exact factor_unit (dvd_zero 3)
  have factor_value : padicValNat 3 factor = 0 :=
    padicValNat.eq_zero_of_not_dvd factor_unit
  have value_valuation : padicValNat 3 value = exponent := by
    rw [factorization, padicValNat_base_pow_mul (by norm_num) factor_ne, factor_value]
    omega
  have exponent_eq : exponent = power := by omega
  have cancellable : 3 ^ power ≠ 0 := pow_ne_zero _ (by norm_num)
  have rewritten := relation
  rw [factorization, exponent_eq] at rewritten
  have normalized_relation :
      3 ^ power * factor ≡ 3 ^ power * 1 [MOD 3 ^ power * 3] := by
    simpa only [pow_succ, mul_one] using rewritten
  exact ⟨exponent_eq, normalized_relation.mul_left_cancel' cancellable⟩

private theorem powerFactor_of_modEq_twoMore
    {value exponent factor power quotient : Nat} (value_ne : value ≠ 0)
    (relation : value ≡ 3 ^ power * quotient [MOD 3 ^ (power + 2)])
    (factorization : value = 3 ^ exponent * factor)
    (factor_unit : ¬3 ∣ factor) (quotient_unit : ¬3 ∣ quotient) :
    exponent = power ∧ factor ≡ quotient [MOD 9] := by
  have power_dvd_modulus : 3 ^ power ∣ 3 ^ (power + 2) :=
    Nat.pow_dvd_pow 3 (by omega)
  have lower_divisor : 3 ^ power ∣ value := by
    exact (relation.dvd_iff power_dvd_modulus).mpr (dvd_mul_right _ _)
  have next_dvd_modulus : 3 ^ (power + 1) ∣ 3 ^ (power + 2) :=
    Nat.pow_dvd_pow 3 (by omega)
  have upper_not_divisor : ¬3 ^ (power + 1) ∣ value := by
    intro divides_value
    have divides_right := (relation.dvd_iff next_dvd_modulus).mp divides_value
    have normalized : 3 ^ power * 3 ∣ 3 ^ power * quotient := by
      simpa only [pow_succ] using divides_right
    have divides_quotient : 3 ∣ quotient :=
      Nat.dvd_of_mul_dvd_mul_left (pow_pos (by norm_num) power) normalized
    exact quotient_unit divides_quotient
  have valuation_lower : power ≤ padicValNat 3 value :=
    (padicValNat_dvd_iff_le value_ne).mp lower_divisor
  have valuation_upper : padicValNat 3 value < power + 1 := by
    rw [← not_le]
    intro upper_le
    exact upper_not_divisor ((padicValNat_dvd_iff_le value_ne).mpr upper_le)
  have factor_ne : factor ≠ 0 := by
    intro factor_zero
    subst factor
    exact factor_unit (dvd_zero 3)
  have factor_value : padicValNat 3 factor = 0 :=
    padicValNat.eq_zero_of_not_dvd factor_unit
  have value_valuation : padicValNat 3 value = exponent := by
    rw [factorization, padicValNat_base_pow_mul (by norm_num) factor_ne, factor_value]
    omega
  have exponent_eq : exponent = power := by omega
  have rewritten := relation
  rw [factorization, exponent_eq] at rewritten
  have cancellable : 3 ^ power ≠ 0 := pow_ne_zero _ (by norm_num)
  have normalized_relation :
      3 ^ power * factor ≡ 3 ^ power * quotient [MOD 3 ^ power * 9] := by
    simpa [pow_add, pow_two] using rewritten
  exact ⟨exponent_eq, normalized_relation.mul_left_cancel' cancellable⟩

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

private theorem runPole_target_factor_congruence
    {β zeros : Nat} (zeros_inside : zeros + 2 ≤ β)
    {upper target : List Bool}
    (upper_code :
      2 * swappedCode upper + 2 = 9 * 3 ^ β + 3 ^ zeros)
    (pole : PoleCongruence β upper [] target) :
    (3 ^ zeros + 4) * (swappedCode target + 1) ≡ 3 * 3 ^ zeros
      [MOD 3 ^ (zeros + 2)] := by
  have power_dvd_nat : 3 ^ (zeros + 2) ∣ 3 ^ β := Nat.pow_dvd_pow 3 zeros_inside
  have power_dvd_int : (3 : ℤ) ^ (zeros + 2) ∣ (3 : ℤ) ^ β := by
    exact_mod_cast power_dvd_nat
  have modulus_dvd : (3 : ℤ) ^ (zeros + 2) ∣ 9 * (3 : ℤ) ^ β :=
    power_dvd_int.trans (dvd_mul_left ((3 : ℤ) ^ β) 9)
  have rho_zero : (3 : ℤ) ^ β ≡ 0 [ZMOD (3 : ℤ) ^ (zeros + 2)] :=
    power_dvd_int.modEq_zero_int
  have upper_code_int :
      2 * (swappedCode upper : ℤ) + 2 =
        9 * (3 : ℤ) ^ β + (3 : ℤ) ^ zeros := by
    exact_mod_cast upper_code
  have twice_upper :
      2 * (swappedCode upper : ℤ) ≡ (3 : ℤ) ^ zeros - 2
        [ZMOD (3 : ℤ) ^ (zeros + 2)] := by
    calc
      2 * (swappedCode upper : ℤ) =
          9 * (3 : ℤ) ^ β + (3 : ℤ) ^ zeros - 2 := by linarith
      _ ≡ 9 * 0 + (3 : ℤ) ^ zeros - 2 [ZMOD (3 : ℤ) ^ (zeros + 2)] :=
        ((rho_zero.mul_left 9).add (Int.ModEq.refl ((3 : ℤ) ^ zeros))).sub
          (Int.ModEq.refl 2)
      _ = (3 : ℤ) ^ zeros - 2 := by ring
  have doubled := pole.mul_left 2
  have reduced := doubled.of_dvd modulus_dvd
  have core :
      ((3 : ℤ) ^ zeros - 2) * (-2) ≡
        (-(3 : ℤ) ^ zeros - 4) * swappedCode target
          [ZMOD (3 : ℤ) ^ (zeros + 2)] := by
    calc
      ((3 : ℤ) ^ zeros - 2) * (-2) ≡
          (2 * swappedCode upper) * ((3 : ℤ) ^ β - 2)
            [ZMOD (3 : ℤ) ^ (zeros + 2)] :=
        twice_upper.symm.mul (rho_zero.sub (Int.ModEq.refl 2)).symm
      _ = 2 *
          ((swappedCode upper : ℤ) * ((3 : ℤ) ^ β - 2)) := by ring
      _ ≡ 2 *
          ((6 * (3 : ℤ) ^ β - 3 - swappedCode upper) * swappedCode target)
            [ZMOD (3 : ℤ) ^ (zeros + 2)] := by
        simpa [PoleCongruence] using reduced
      _ = (12 * (3 : ℤ) ^ β - 6 - 2 * swappedCode upper) *
          swappedCode target := by ring
      _ ≡ (12 * 0 - 6 - ((3 : ℤ) ^ zeros - 2)) * swappedCode target
            [ZMOD (3 : ℤ) ^ (zeros + 2)] :=
        (((rho_zero.mul_left 12).sub (Int.ModEq.refl 6)).sub twice_upper).mul
          (Int.ModEq.refl (swappedCode target))
      _ = (-(3 : ℤ) ^ zeros - 4) * swappedCode target := by ring
  have factored :
      ((3 : ℤ) ^ zeros + 4) * (swappedCode target + 1) ≡
        3 * (3 : ℤ) ^ zeros [ZMOD (3 : ℤ) ^ (zeros + 2)] := by
    rw [Int.modEq_iff_dvd] at core ⊢
    convert core using 1
    ring
  have modulus_eq : (3 : ℤ) ^ (zeros + 2) = (3 ^ (zeros + 2) : Nat) := by
    norm_num
  rw [modulus_eq] at factored
  exact Int.natCast_modEq_iff.mp (by simpa using factored)

private theorem runPole_target_code_congruence
    {β zeros : Nat} (zeros_pos : 1 ≤ zeros) (zeros_inside : zeros + 2 ≤ β)
    {upper target : List Bool}
    (upper_code :
      2 * swappedCode upper + 2 = 9 * 3 ^ β + 3 ^ zeros)
    (pole : PoleCongruence β upper [] target) :
    swappedCode target + 1 ≡ 3 * 3 ^ zeros [MOD 3 ^ (zeros + 2)] := by
  have factor_relation :=
    runPole_target_factor_congruence zeros_inside upper_code pole
  have three_dvd_power : 3 ∣ 3 ^ zeros := by
    exact Nat.pow_dvd_pow 3 zeros_pos
  have factor_unit : ¬3 ∣ 3 ^ zeros + 4 := by
    intro divides_sum
    have divides_four : 3 ∣ 4 :=
      (Nat.dvd_add_iff_left three_dvd_power).mpr (by
        simpa [Nat.add_comm] using divides_sum)
    norm_num at divides_four
  have factor_coprime : Nat.Coprime (3 ^ zeros + 4) (3 ^ (zeros + 2)) :=
    Nat.prime_three.coprime_pow_of_not_dvd factor_unit
  obtain ⟨unit, power_eq⟩ := three_dvd_power
  have modulus_eq : 3 ^ (zeros + 2) = 9 * 3 ^ zeros := by
    rw [pow_add]
    norm_num
    ring
  have candidate_relation :
      (3 ^ zeros + 4) * (3 * 3 ^ zeros) ≡ 3 * 3 ^ zeros
        [MOD 3 ^ (zeros + 2)] := by
    rw [show (3 ^ zeros + 4) * (3 * 3 ^ zeros) =
        3 ^ (zeros + 2) * (unit + 1) + 3 * 3 ^ zeros by
      rw [modulus_eq, power_eq]
      ring]
    exact Nat.ModEq.modulus_mul_add
  apply Nat.ModEq.cancel_left_of_coprime factor_coprime.symm.gcd_eq_one
  exact factor_relation.trans candidate_relation.symm

private theorem runMimic_lowPower_not_dvd {zeros : Nat} (zeros_pos : 1 ≤ zeros) :
    ¬3 ^ (zeros + 3) ∣ 3 * 3 ^ zeros * (3 ^ zeros + 3) := by
  obtain ⟨previous, rfl⟩ := Nat.exists_eq_add_of_le zeros_pos
  have unit_not_dvd : ¬3 ∣ 3 ^ previous + 1 := by
    cases previous with
    | zero => norm_num
    | succ previous =>
        intro divides_sum
        have divides_power : 3 ∣ 3 ^ (previous + 1) := by
          refine ⟨3 ^ previous, ?_⟩
          rw [pow_succ]
          ring
        have divides_one : 3 ∣ 1 :=
          (Nat.dvd_add_iff_left divides_power).mpr (by
            simpa [Nat.add_comm] using divides_sum)
        norm_num at divides_one
  intro divisibility
  have normalized :
      3 ^ (previous + 1 + 3) = 3 ^ (previous + 1 + 2) * 3 := by
    rw [show previous + 1 + 3 = (previous + 1 + 2) + 1 by omega, pow_succ]
  have product_eq :
      3 * 3 ^ (previous + 1) * (3 ^ (previous + 1) + 3) =
        3 ^ (previous + 1 + 2) * (3 ^ previous + 1) := by
    rw [pow_succ, show previous + 1 + 2 = previous + 3 by omega, pow_add]
    norm_num
    ring
  have divisibility' :
      3 ^ (previous + 1 + 3) ∣
        3 * 3 ^ (previous + 1) * (3 ^ (previous + 1) + 3) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using divisibility
  rw [normalized, product_eq] at divisibility'
  have divides_unit : 3 ∣ 3 ^ previous + 1 :=
    Nat.dvd_of_mul_dvd_mul_left (pow_pos (by norm_num) (previous + 1 + 2)) divisibility'
  exact unit_not_dvd divides_unit

private theorem runMimic_residual_not_dvd {β zeros : Nat}
    (β_large : 5 ≤ β) (zeros_pos : 1 ≤ zeros) (zeros_inside : zeros + 2 ≤ β) :
    ¬(9 * (3 : ℤ) ^ β) ∣
      9 * ((3 : ℤ) ^ β) ^ 2 -
        8 * (3 : ℤ) ^ β * (3 : ℤ) ^ zeros -
        17 * (3 : ℤ) ^ β +
        3 * ((3 : ℤ) ^ zeros) ^ 2 +
        9 * (3 : ℤ) ^ zeros := by
  intro divisibility
  by_cases deeply_inside : zeros + 3 ≤ β
  · have rho_dvd_modulus : (3 : ℤ) ^ β ∣ 9 * (3 : ℤ) ^ β :=
      dvd_mul_left _ _
    have rho_dvd_residual := rho_dvd_modulus.trans divisibility
    have rho_dvd_bulk :
        (3 : ℤ) ^ β ∣
          (3 : ℤ) ^ β *
            (9 * (3 : ℤ) ^ β - 8 * (3 : ℤ) ^ zeros - 17) :=
      dvd_mul_right _ _
    have rho_dvd_small :
        (3 : ℤ) ^ β ∣
          3 * (3 : ℤ) ^ zeros * ((3 : ℤ) ^ zeros + 3) := by
      have difference := Int.dvd_sub rho_dvd_residual rho_dvd_bulk
      convert difference using 1
      ring
    have rho_dvd_small_nat :
        3 ^ β ∣ 3 * 3 ^ zeros * (3 ^ zeros + 3) := by
      exact_mod_cast rho_dvd_small
    have lower_power : 3 ^ (zeros + 3) ∣ 3 ^ β :=
      Nat.pow_dvd_pow 3 deeply_inside
    exact runMimic_lowPower_not_dvd zeros_pos (lower_power.trans rho_dvd_small_nat)
  · have β_eq : β = zeros + 2 := by omega
    subst β
    have zeros_large : 3 ≤ zeros := by omega
    have residual_factorization :
        9 * ((3 : ℤ) ^ (zeros + 2)) ^ 2 -
              8 * (3 : ℤ) ^ (zeros + 2) * (3 : ℤ) ^ zeros -
              17 * (3 : ℤ) ^ (zeros + 2) +
              3 * ((3 : ℤ) ^ zeros) ^ 2 +
              9 * (3 : ℤ) ^ zeros =
          (3 : ℤ) ^ zeros * (660 * (3 : ℤ) ^ zeros - 144) := by
      rw [pow_add]
      norm_num
      ring
    have modulus_factorization :
        9 * (3 : ℤ) ^ (zeros + 2) = (3 : ℤ) ^ zeros * 81 := by
      rw [pow_add]
      norm_num
      ring
    rw [residual_factorization, modulus_factorization] at divisibility
    have power_ne : (3 : ℤ) ^ zeros ≠ 0 := pow_ne_zero _ (by norm_num)
    have quotient_dvd : (81 : ℤ) ∣ 660 * (3 : ℤ) ^ zeros - 144 :=
      Int.dvd_of_mul_dvd_mul_left power_ne divisibility
    have twenty_seven_dvd_nat : 27 ∣ 3 ^ zeros := by
      exact Nat.pow_dvd_pow 3 zeros_large
    have twenty_seven_dvd : (27 : ℤ) ∣ (3 : ℤ) ^ zeros := by
      exact_mod_cast twenty_seven_dvd_nat
    obtain ⟨scale, power_eq⟩ := twenty_seven_dvd
    have eighty_one_dvd_scaled : (81 : ℤ) ∣ 660 * (3 : ℤ) ^ zeros := by
      refine ⟨220 * scale, ?_⟩
      rw [power_eq]
      ring
    have eighty_one_dvd_144 : (81 : ℤ) ∣ 144 := by
      have difference := Int.dvd_sub eighty_one_dvd_scaled quotient_dvd
      convert difference using 1
      ring
    norm_num at eighty_one_dvd_144

private theorem runPole_zeroTarget_false
    {β zeros : Nat} (β_large : 5 ≤ β) (zeros_pos : 1 ≤ zeros)
    (zeros_inside : zeros + 2 ≤ β) {upper target : List Bool}
    (upper_code :
      2 * swappedCode upper + 2 = 9 * 3 ^ β + 3 ^ zeros)
    (target_code : swappedCode target + 1 = 3 ^ (zeros + 1))
    (pole : PoleCongruence β upper [] target) : False := by
  have upper_code_int :
      2 * (swappedCode upper : ℤ) =
        9 * (3 : ℤ) ^ β + (3 : ℤ) ^ zeros - 2 := by
    have upper_add_int :
        2 * (swappedCode upper : ℤ) + 2 =
          9 * (3 : ℤ) ^ β + (3 : ℤ) ^ zeros := by
      exact_mod_cast upper_code
    linarith
  have target_code_int :
      (swappedCode target : ℤ) = 3 * (3 : ℤ) ^ zeros - 1 := by
    have target_add_int :
        (swappedCode target : ℤ) + 1 = (3 : ℤ) ^ (zeros + 1) := by
      exact_mod_cast target_code
    rw [pow_succ] at target_add_int
    linarith
  have raw_divisibility := (pole.mul_left 2).dvd
  have residual_divisibility :
      (9 * (3 : ℤ) ^ β) ∣
        9 * ((3 : ℤ) ^ β) ^ 2 -
          8 * (3 : ℤ) ^ β * (3 : ℤ) ^ zeros -
          17 * (3 : ℤ) ^ β +
          3 * ((3 : ℤ) ^ zeros) ^ 2 +
          9 * (3 : ℤ) ^ zeros := by
    have negated := Int.dvd_neg.mpr raw_divisibility
    convert negated using 1
    simp only [swappedCode_nil, Nat.cast_zero, sub_zero]
    calc
      9 * ((3 : ℤ) ^ β) ^ 2 -
            8 * (3 : ℤ) ^ β * (3 : ℤ) ^ zeros -
            17 * (3 : ℤ) ^ β +
            3 * ((3 : ℤ) ^ zeros) ^ 2 +
            9 * (3 : ℤ) ^ zeros =
          (2 * (swappedCode upper : ℤ)) * ((3 : ℤ) ^ β - 2) -
            (12 * (3 : ℤ) ^ β - 6 - 2 * swappedCode upper) *
              swappedCode target := by
        rw [upper_code_int, target_code_int]
        ring
      _ = -(2 *
            ((6 * (3 : ℤ) ^ β - 3 - swappedCode upper) * swappedCode target) -
          2 * (swappedCode upper * ((3 : ℤ) ^ β - 2))) := by ring
  exact runMimic_residual_not_dvd β_large zeros_pos zeros_inside residual_divisibility

private theorem three_not_dvd_nine_mul_add_five (value : Nat) :
    ¬3 ∣ 9 * value + 5 := by
  intro divides_sum
  have divides_scaled : 3 ∣ 9 * value := by
    exact dvd_mul_of_dvd_left (by norm_num) value
  have divides_five : 3 ∣ 5 :=
    (Nat.dvd_add_iff_left divides_scaled).mpr (by
      simpa [Nat.add_comm] using divides_sum)
  norm_num at divides_five

private theorem nine_mul_add_five_modEq_two (value : Nat) :
    9 * value + 5 ≡ 2 [MOD 3] := by
  rw [show 9 * value + 5 = 3 * (3 * value + 1) + 2 by ring]
  exact Nat.ModEq.modulus_mul_add

private theorem swappedCode_complete_modNine_cases (phases : List Bool) :
    swappedCode (spell fringeBlock phases) = 0 ∨
      swappedCode (spell fringeBlock phases) = 2 ∨
      swappedCode (spell fringeBlock phases) ≡ 5 [MOD 9] ∨
      swappedCode (spell fringeBlock phases) ≡ 8 [MOD 9] := by
  induction phases using List.reverseRecOn with
  | nil => exact Or.inl rfl
  | append_singleton phases phase =>
      rw [spell_append]
      cases phase with
      | true =>
          right
          right
          left
          rw [show spell fringeBlock [true] = [true, true, false] by rfl,
            swappedCode_append]
          have block_code : swappedCode [true, true, false] = 14 := by decide
          rw [block_code]
          change 27 * swappedCode (spell fringeBlock phases) + 14 ≡ 5 [MOD 9]
          rw [show 27 * swappedCode (spell fringeBlock phases) + 14 =
              9 * (3 * swappedCode (spell fringeBlock phases) + 1) + 5 by ring]
          exact Nat.ModEq.modulus_mul_add
      | false =>
          rw [show spell fringeBlock [false] = [false] by rfl, swappedCode_append]
          rcases swappedCode_spell_fringeBlock_zero_or_modEq_two phases with zero | residue
          · right
            left
            rw [zero]
            decide
          · right
            right
            right
            have scaled := residue.mul_left' 3
            have shifted := scaled.add (Nat.ModEq.refl 2)
            simpa using shifted

private theorem runPole_inside_false
    {β zeros : Nat} (β_large : 5 ≤ β) (zeros_pos : 1 ≤ zeros)
    (zeros_inside : zeros + 2 ≤ β) {upper target : List Bool}
    (upper_code :
      2 * swappedCode upper + 2 = 9 * 3 ^ β + 3 ^ zeros)
    (target_fringe : TargetFringe (β + 2) target)
    (pole : PoleCongruence β upper [] target) : False := by
  have raw_relation :=
    runPole_target_code_congruence zeros_pos zeros_inside upper_code pole
  have relation :
      swappedCode target + 1 ≡ 3 ^ (zeros + 1) [MOD 3 ^ ((zeros + 1) + 1)] := by
    simpa [pow_succ, Nat.mul_comm, Nat.add_assoc] using raw_relation
  have value_ne : swappedCode target + 1 ≠ 0 := by omega
  rcases targetFringe_codeFactor target_fringe with zero_factor | pair_factor | cut_factor
  · obtain ⟨target_zeros, _, _, factorization⟩ := zero_factor
    have normalized_factorization :
        swappedCode target + 1 = 3 ^ target_zeros * 1 := by
      simpa using factorization
    have unique := powerFactor_of_modEq_next value_ne relation normalized_factorization (by
      norm_num)
    have target_zeros_eq : target_zeros = zeros + 1 := unique.1
    subst target_zeros
    exact runPole_zeroTarget_false β_large zeros_pos zeros_inside upper_code factorization pole
  · obtain ⟨front, target_zeros, _, _, factorization⟩ := pair_factor
    have unique := powerFactor_of_modEq_next value_ne relation factorization
      (three_not_dvd_nine_mul_add_five (swappedCode front))
    have impossible := unique.2.symm.trans
      (nine_mul_add_five_modEq_two (swappedCode front))
    norm_num [Nat.ModEq] at impossible
  · obtain ⟨_, factorization⟩ := cut_factor
    have normalized_factorization :
        swappedCode target + 1 = 3 ^ ((β + 2) - 1) * 2 := by
      rw [factorization]
      ring
    have unique := powerFactor_of_modEq_next value_ne relation normalized_factorization (by
      norm_num)
    have exponent_eq := unique.1
    omega

private theorem allOnesPole_relation
    {β : Nat} {upper source target : List Bool}
    (source_code_lower : 2 ≤ swappedCode source)
    (upper_code : 2 * swappedCode upper + 1 = 9 * 3 ^ β)
    (pole : PoleCongruence β upper source target) :
    (3 * 3 ^ β + 2 * swappedCode source - 5) * (swappedCode target + 1) ≡
      3 * (2 * swappedCode source - 1) [MOD 3 ^ β] := by
  have upper_code_int :
      2 * (swappedCode upper : ℤ) + 1 = 9 * (3 : ℤ) ^ β := by
    exact_mod_cast upper_code
  have modulus_dvd : (3 : ℤ) ^ β ∣ 9 * (3 : ℤ) ^ β := dvd_mul_left _ _
  have rho_zero : (3 : ℤ) ^ β ≡ 0 [ZMOD (3 : ℤ) ^ β] :=
    Int.modulus_modEq_zero
  have doubled := pole.mul_left 2
  have reduced := doubled.of_dvd modulus_dvd
  have core :
      (9 * (3 : ℤ) ^ β - 1 - 2 * swappedCode source) *
          ((3 : ℤ) ^ β - 2) ≡
        (3 * (3 : ℤ) ^ β - 5 + 2 * swappedCode source) * swappedCode target
          [ZMOD (3 : ℤ) ^ β] := by
    calc
      (9 * (3 : ℤ) ^ β - 1 - 2 * swappedCode source) *
          ((3 : ℤ) ^ β - 2) =
        2 * (((swappedCode upper : ℤ) - swappedCode source) *
          ((3 : ℤ) ^ β - 2)) := by
            rw [← upper_code_int]
            ring
      _ ≡ 2 *
          ((6 * (3 : ℤ) ^ β - 3 -
            ((swappedCode upper : ℤ) - swappedCode source)) * swappedCode target)
            [ZMOD (3 : ℤ) ^ β] := by
              simpa [PoleCongruence] using reduced
      _ = (12 * (3 : ℤ) ^ β - 6 - 2 * swappedCode upper +
            2 * swappedCode source) * swappedCode target := by ring
      _ = (3 * (3 : ℤ) ^ β - 5 + 2 * swappedCode source) *
          swappedCode target := by
            have twice_upper :
                2 * (swappedCode upper : ℤ) = 9 * (3 : ℤ) ^ β - 1 := by
              linarith
            rw [twice_upper]
            ring
  have shifted :
      (3 * (3 : ℤ) ^ β - 5 + 2 * swappedCode source) *
          (swappedCode target + 1) ≡
        3 * (2 * (swappedCode source : ℤ) - 1) [ZMOD (3 : ℤ) ^ β] := by
    calc
      (3 * (3 : ℤ) ^ β - 5 + 2 * swappedCode source) *
          (swappedCode target + 1) =
        (3 * (3 : ℤ) ^ β - 5 + 2 * swappedCode source) *
            swappedCode target +
          (3 * (3 : ℤ) ^ β - 5 + 2 * swappedCode source) := by ring
      _ ≡ (9 * (3 : ℤ) ^ β - 1 - 2 * swappedCode source) *
            ((3 : ℤ) ^ β - 2) +
          (3 * (3 : ℤ) ^ β - 5 + 2 * swappedCode source)
            [ZMOD (3 : ℤ) ^ β] := core.symm.add (Int.ModEq.refl _)
      _ ≡ (9 * 0 - 1 - 2 * swappedCode source) * (0 - 2) +
          (3 * 0 - 5 + 2 * swappedCode source) [ZMOD (3 : ℤ) ^ β] :=
        (((rho_zero.mul_left 9).sub (Int.ModEq.refl 1)).sub
          (Int.ModEq.refl (2 * (swappedCode source : ℤ)))).mul
            (rho_zero.sub (Int.ModEq.refl 2)) |>.add
          (((rho_zero.mul_left 3).sub (Int.ModEq.refl 5)).add
            (Int.ModEq.refl (2 * (swappedCode source : ℤ))))
      _ = 3 * (2 * (swappedCode source : ℤ) - 1) := by ring
  have left_bound : 5 ≤ 3 * 3 ^ β + 2 * swappedCode source := by
    have power_pos : 0 < 3 ^ β := pow_pos (by norm_num) β
    omega
  have right_bound : 1 ≤ 2 * swappedCode source := by omega
  have reordered :
      (3 * (3 : ℤ) ^ β + 2 * swappedCode source - 5) *
          (swappedCode target + 1) ≡
        3 * (2 * (swappedCode source : ℤ) - 1) [ZMOD (3 : ℤ) ^ β] := by
    convert shifted using 1
    ring
  apply Int.natCast_modEq_iff.mp
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_add, Nat.cast_one, Nat.cast_sub left_bound,
    Nat.cast_sub right_bound] using reordered

private theorem coprime_eightyOne_of_modEq_two {value : Nat}
    (residue : value ≡ 2 [MOD 3]) : Nat.Coprime value 81 := by
  have not_divisible : ¬3 ∣ value := by
    intro divisibility
    have zero := Nat.modEq_zero_iff_dvd.mpr divisibility
    have impossible := residue.symm.trans zero
    norm_num [Nat.ModEq] at impossible
  have coprime := Nat.prime_three.coprime_pow_of_not_dvd (m := 4) not_divisible
  norm_num at coprime ⊢
  exact coprime

private theorem targetFactor_false_of_quotient
    {width quotient : Nat} {word : List Bool}
    (target_fringe : TargetFringe width word)
    (relation : swappedCode word + 1 ≡ 9 * quotient [MOD 81])
    (quotient_unit : ¬3 ∣ quotient)
    (quotient_ne_one : ¬quotient ≡ 1 [MOD 9])
    (quotient_ne_five : ¬quotient ≡ 5 [MOD 9])
    (quotient_ne_two : ¬quotient ≡ 2 [MOD 9]) : False := by
  have normalized_relation :
      swappedCode word + 1 ≡ 3 ^ 2 * quotient [MOD 3 ^ (2 + 2)] := by
    norm_num at relation ⊢
    exact relation
  have value_ne : swappedCode word + 1 ≠ 0 := by omega
  rcases targetFringe_codeFactor target_fringe with zero_factor | pair_factor | cut_factor
  · obtain ⟨zeros, _, _, factorization⟩ := zero_factor
    have normalized_factorization :
        swappedCode word + 1 = 3 ^ zeros * 1 := by simpa using factorization
    have unique := powerFactor_of_modEq_twoMore value_ne normalized_relation
      normalized_factorization (by norm_num) quotient_unit
    exact quotient_ne_one unique.2.symm
  · obtain ⟨front, zeros, _, _, factorization⟩ := pair_factor
    have unique := powerFactor_of_modEq_twoMore value_ne normalized_relation factorization
      (three_not_dvd_nine_mul_add_five (swappedCode front)) quotient_unit
    have factor_mod_five : 9 * swappedCode front + 5 ≡ 5 [MOD 9] := by
      exact Nat.ModEq.modulus_mul_add
    exact quotient_ne_five (unique.2.symm.trans factor_mod_five)
  · obtain ⟨_, factorization⟩ := cut_factor
    have normalized_factorization :
        swappedCode word + 1 = 3 ^ (width - 1) * 2 := by
      rw [factorization]
      ring
    have unique := powerFactor_of_modEq_twoMore value_ne normalized_relation
      normalized_factorization (by norm_num) quotient_unit
    have factor_two : (2 : Nat) ≡ 2 [MOD 9] := Nat.ModEq.refl 2
    exact quotient_ne_two (unique.2.symm.trans factor_two)

private theorem targetFactor_eq_power_of_quotient_one
    {width power : Nat} {word : List Bool} (target_fringe : TargetFringe width word)
    (relation : swappedCode word + 1 ≡ 3 ^ power [MOD 3 ^ (power + 2)]) :
    swappedCode word + 1 = 3 ^ power := by
  have normalized_relation :
      swappedCode word + 1 ≡ 3 ^ power * 1 [MOD 3 ^ (power + 2)] := by
    simpa using relation
  have value_ne : swappedCode word + 1 ≠ 0 := by omega
  rcases targetFringe_codeFactor target_fringe with zero_factor | pair_factor | cut_factor
  · obtain ⟨zeros, _, _, factorization⟩ := zero_factor
    have normalized_factorization :
        swappedCode word + 1 = 3 ^ zeros * 1 := by simpa using factorization
    have unique := powerFactor_of_modEq_twoMore value_ne normalized_relation
      normalized_factorization (by norm_num) (by norm_num)
    rw [factorization, unique.1]
  · obtain ⟨front, zeros, _, _, factorization⟩ := pair_factor
    have unique := powerFactor_of_modEq_twoMore value_ne normalized_relation factorization
      (three_not_dvd_nine_mul_add_five (swappedCode front)) (by norm_num)
    have factor_mod_five : 9 * swappedCode front + 5 ≡ 5 [MOD 9] :=
      Nat.ModEq.modulus_mul_add
    have impossible := unique.2.symm.trans factor_mod_five
    norm_num [Nat.ModEq] at impossible
  · obtain ⟨_, factorization⟩ := cut_factor
    have normalized_factorization :
        swappedCode word + 1 = 3 ^ (width - 1) * 2 := by
      rw [factorization]
      ring
    have unique := powerFactor_of_modEq_twoMore value_ne normalized_relation
      normalized_factorization (by norm_num) (by norm_num)
    have impossible := unique.2.symm.trans (Nat.ModEq.refl 2 : (2 : Nat) ≡ 2 [MOD 9])
    norm_num [Nat.ModEq] at impossible

private theorem cancel_eightyOne_factor {factor left right residue : Nat}
    (factor_mod : factor ≡ 2 [MOD 3])
    (left_relation : factor * left ≡ residue [MOD 81])
    (right_relation : factor * right ≡ residue [MOD 81]) :
    left ≡ right [MOD 81] := by
  apply Nat.ModEq.cancel_left_of_coprime
    (coprime_eightyOne_of_modEq_two factor_mod).symm.gcd_eq_one
  exact left_relation.trans right_relation.symm

private theorem allOnes_zeroSource_false
    {β zeros : Nat} (β_large : 4 ≤ β) (zeros_pos : 1 ≤ zeros)
    {upper source target : List Bool}
    (source_eq : source = List.replicate zeros false)
    (upper_code : 2 * swappedCode upper + 1 = 9 * 3 ^ β)
    (target_fringe : TargetFringe (β + 2) target)
    (pole : PoleCongruence β upper source target) : False := by
  have source_code_add := swappedCode_replicate_false zeros
  have source_code : swappedCode source = 3 ^ zeros - 1 := by
    rw [source_eq]
    omega
  have source_lower : 2 ≤ swappedCode source := by
    have power_lower : 3 ≤ 3 ^ zeros := by
      exact Nat.pow_le_pow_right (n := 3) (by norm_num) zeros_pos
    omega
  have base_relation := allOnesPole_relation source_lower upper_code pole
  have eightyOne_dvd : 81 ∣ 3 ^ β := by
    exact Nat.pow_dvd_pow 3 (show 4 ≤ β by omega)
  have three_dvd_rho : 3 ∣ 3 ^ β := by
    exact Nat.pow_dvd_pow 3 (show 1 ≤ β by omega)
  obtain ⟨rhoUnit, rho_eq⟩ := three_dvd_rho
  have rhoUnit_pos : 0 < rhoUnit := by
    have rho_pos : 0 < 3 ^ β := pow_pos (by norm_num) β
    omega
  rcases zeros with _ | zeros
  · omega
  · cases zeros with
    | zero =>
        have source_code_eq : swappedCode source = 2 := by
          norm_num at source_code ⊢
          exact source_code
        have relation :
            (3 * 3 ^ β - 1) * (swappedCode target + 1) ≡ 9 [MOD 3 ^ β] := by
          simpa [source_code_eq] using base_relation
        have relation_eightyOne := relation.of_dvd eightyOne_dvd
        have factor_mod : 3 * 3 ^ β - 1 ≡ 2 [MOD 3] := by
          rw [rho_eq, show 3 * (3 * rhoUnit) - 1 =
              3 * (3 * rhoUnit - 1) + 2 by omega]
          exact Nat.ModEq.modulus_mul_add
        have candidate : (3 * 3 ^ β - 1) * 72 ≡ 9 [MOD 81] := by
          rw [rho_eq, show (3 * (3 * rhoUnit) - 1) * 72 =
              81 * (8 * rhoUnit - 1) + 9 by omega]
          exact Nat.ModEq.modulus_mul_add
        have target_relation := cancel_eightyOne_factor factor_mod
          relation_eightyOne candidate
        exact targetFactor_false_of_quotient (quotient := 8) target_fringe target_relation
          (by norm_num)
          (by norm_num [Nat.ModEq]) (by norm_num [Nat.ModEq]) (by norm_num [Nat.ModEq])
    | succ zeros =>
        cases zeros with
        | zero =>
            have source_code_eq : swappedCode source = 8 := by
              norm_num at source_code ⊢
              exact source_code
            have relation :
                (3 * 3 ^ β + 11) * (swappedCode target + 1) ≡ 45 [MOD 3 ^ β] := by
              simpa [source_code_eq] using base_relation
            have relation_eightyOne := relation.of_dvd eightyOne_dvd
            have factor_mod : 3 * 3 ^ β + 11 ≡ 2 [MOD 3] := by
              rw [rho_eq, show 3 * (3 * rhoUnit) + 11 =
                  3 * (3 * rhoUnit + 3) + 2 by ring]
              exact Nat.ModEq.modulus_mul_add
            have candidate : (3 * 3 ^ β + 11) * 63 ≡ 45 [MOD 81] := by
              rw [rho_eq, show (3 * (3 * rhoUnit) + 11) * 63 =
                  81 * (7 * rhoUnit + 8) + 45 by ring]
              exact Nat.ModEq.modulus_mul_add
            have target_relation := cancel_eightyOne_factor factor_mod
              relation_eightyOne candidate
            exact targetFactor_false_of_quotient (quotient := 7) target_fringe target_relation
              (by norm_num)
              (by norm_num [Nat.ModEq]) (by norm_num [Nat.ModEq])
              (by norm_num [Nat.ModEq])
        | succ zeros =>
            have original_zeros_large : 3 ≤ Nat.succ (Nat.succ (Nat.succ zeros)) := by omega
            have twentySeven_dvd : 27 ∣ 3 ^ Nat.succ (Nat.succ (Nat.succ zeros)) := by
              exact Nat.pow_dvd_pow 3 original_zeros_large
            obtain ⟨powerUnit, power_eq⟩ := twentySeven_dvd
            have powerUnit_pos : 0 < powerUnit := by
              have power_pos : 0 < 3 ^ Nat.succ (Nat.succ (Nat.succ zeros)) :=
                pow_pos (by norm_num) _
              omega
            have source_code_eq :
                swappedCode source = 27 * powerUnit - 1 := by
              rw [source_code, power_eq]
            have relation :
                (3 * 3 ^ β + 54 * powerUnit - 7) * (swappedCode target + 1) ≡
                  3 * (54 * powerUnit - 3) [MOD 3 ^ β] := by
              rw [source_code_eq] at base_relation
              have coefficient_eq :
                  3 * 3 ^ β + 2 * (27 * powerUnit - 1) - 5 =
                    3 * 3 ^ β + 54 * powerUnit - 7 := by omega
              have residue_eq :
                  3 * (2 * (27 * powerUnit - 1) - 1) =
                    3 * (54 * powerUnit - 3) := by omega
              rw [coefficient_eq, residue_eq] at base_relation
              exact base_relation
            have relation_eightyOne := relation.of_dvd eightyOne_dvd
            have factor_mod : 3 * 3 ^ β + 54 * powerUnit - 7 ≡ 2 [MOD 3] := by
              rw [rho_eq, show 3 * (3 * rhoUnit) + 54 * powerUnit - 7 =
                  3 * (3 * rhoUnit + 18 * powerUnit - 3) + 2 by omega]
              exact Nat.ModEq.modulus_mul_add
            have candidate :
                (3 * 3 ^ β + 54 * powerUnit - 7) * 36 ≡
                  3 * (54 * powerUnit - 3) [MOD 81] := by
              rw [rho_eq, show
                  (3 * (3 * rhoUnit) + 54 * powerUnit - 7) * 36 =
                    81 * (4 * rhoUnit + 22 * powerUnit - 3) +
                      3 * (54 * powerUnit - 3) by omega]
              exact Nat.ModEq.modulus_mul_add
            have target_relation := cancel_eightyOne_factor factor_mod
              relation_eightyOne candidate
            exact targetFactor_false_of_quotient (quotient := 4) target_fringe target_relation
              (by norm_num)
              (by norm_num [Nat.ModEq]) (by norm_num [Nat.ModEq])
              (by norm_num [Nat.ModEq])

private theorem allOnes_patternSource_highTail_false
    {β zeros : Nat} (β_large : 6 ≤ β) (zeros_large : 2 ≤ zeros)
    {upper source target front : List Bool} (front_phases : List Bool)
    (front_eq : front = spell fringeBlock front_phases)
    (source_eq : source = front ++ [true, true] ++ List.replicate zeros false)
    (upper_code : 2 * swappedCode upper + 1 = 9 * 3 ^ β)
    (target_fringe : TargetFringe (β + 2) target)
    (pole : PoleCongruence β upper source target) : False := by
  let middle := 9 * swappedCode front + 5
  have middle_lower : 5 ≤ middle := by simp [middle]
  have source_code_add := swappedCode_pair_zero_tail front zeros
  have source_code : swappedCode source = 3 ^ zeros * middle - 1 := by
    rw [source_eq]
    dsimp only [middle]
    omega
  have source_lower : 2 ≤ swappedCode source := by
    have power_lower : 9 ≤ 3 ^ zeros :=
      Nat.pow_le_pow_right (n := 3) (by norm_num) zeros_large
    have product_lower : 45 ≤ 3 ^ zeros * middle :=
      Nat.mul_le_mul power_lower middle_lower
    omega
  have base_relation := allOnesPole_relation source_lower upper_code pole
  have eightyOne_dvd : 81 ∣ 3 ^ β := Nat.pow_dvd_pow 3 (show 4 ≤ β by omega)
  have three_dvd_rho : 3 ∣ 3 ^ β := Nat.pow_dvd_pow 3 (show 1 ≤ β by omega)
  obtain ⟨rhoUnit, rho_eq⟩ := three_dvd_rho
  have rhoUnit_pos : 0 < rhoUnit := by
    have rho_pos : 0 < 3 ^ β := pow_pos (by norm_num) β
    omega
  by_cases exactly_two : zeros = 2
  · subst zeros
    have source_code_eq : swappedCode source = 9 * middle - 1 := by
      norm_num at source_code ⊢
      exact source_code
    have relation :
        (3 * 3 ^ β + 18 * middle - 7) * (swappedCode target + 1) ≡
          3 * (18 * middle - 3) [MOD 3 ^ β] := by
      rw [source_code_eq] at base_relation
      have coefficient_eq :
          3 * 3 ^ β + 2 * (9 * middle - 1) - 5 =
            3 * 3 ^ β + 18 * middle - 7 := by omega
      have residue_eq :
          3 * (2 * (9 * middle - 1) - 1) = 3 * (18 * middle - 3) := by omega
      rw [coefficient_eq, residue_eq] at base_relation
      exact base_relation
    have relation_eightyOne := relation.of_dvd eightyOne_dvd
    have factor_mod : 3 * 3 ^ β + 18 * middle - 7 ≡ 2 [MOD 3] := by
      rw [rho_eq, show 3 * (3 * rhoUnit) + 18 * middle - 7 =
          3 * (3 * rhoUnit + 6 * middle - 3) + 2 by omega]
      exact Nat.ModEq.modulus_mul_add
    have candidate :
        (3 * 3 ^ β + 18 * middle - 7) * 9 ≡
          3 * (18 * middle - 3) [MOD 81] := by
      rw [rho_eq, show (3 * (3 * rhoUnit) + 18 * middle - 7) * 9 =
          81 * (rhoUnit + 12 * swappedCode front + 6) +
            3 * (18 * middle - 3) by
              dsimp [middle]
              omega]
      exact Nat.ModEq.modulus_mul_add
    have target_relation := cancel_eightyOne_factor factor_mod
      relation_eightyOne candidate
    have normalized_target_relation :
        swappedCode target + 1 ≡ 3 ^ 2 [MOD 3 ^ (2 + 2)] := by
      norm_num at target_relation ⊢
      exact target_relation
    have target_code :=
      targetFactor_eq_power_of_quotient_one target_fringe normalized_target_relation
    have coefficient_bound : 7 ≤ 3 * 3 ^ β + 18 * middle := by omega
    have residue_bound : 3 ≤ 18 * middle := by omega
    have relation_int_cast := Int.natCast_modEq_iff.mpr relation
    have relation_int :
        (3 * (3 : ℤ) ^ β + 18 * middle - 7) * (swappedCode target + 1) ≡
          3 * (18 * middle - 3) [ZMOD (3 : ℤ) ^ β] := by
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat,
        Nat.cast_one, Nat.cast_sub coefficient_bound, Nat.cast_sub residue_bound]
        using relation_int_cast
    have difference_dvd := Int.dvd_neg.mpr relation_int.dvd
    have rho_dvd_whole :
        ((3 : ℤ) ^ β) ∣ 27 * (3 : ℤ) ^ β +
          486 * (2 * (swappedCode front : ℤ) + 1) := by
      convert difference_dvd using 1
      have target_code_int : (swappedCode target : ℤ) + 1 = 9 := by
        exact_mod_cast target_code
      rw [target_code_int]
      dsimp [middle]
      ring
    have rho_dvd_bulk : ((3 : ℤ) ^ β) ∣ 27 * (3 : ℤ) ^ β := dvd_mul_left _ _
    have rho_dvd_unit :
        ((3 : ℤ) ^ β) ∣ 486 * (2 * (swappedCode front : ℤ) + 1) := by
      simpa using Int.dvd_sub rho_dvd_whole rho_dvd_bulk
    have rho_dvd_unit_nat :
        3 ^ β ∣ 486 * (2 * swappedCode front + 1) := by
      exact_mod_cast rho_dvd_unit
    have unit :=
      three_not_dvd_twice_swappedCode_spell_fringeBlock_add_one front_phases
    rw [← front_eq] at unit
    exact pow_three_not_dvd_486_mul_of_unit (by omega) unit rho_dvd_unit_nat
  · have zeros_at_least_three : 3 ≤ zeros := by omega
    have twentySeven_dvd : 27 ∣ 3 ^ zeros :=
      Nat.pow_dvd_pow 3 zeros_at_least_three
    obtain ⟨powerUnit, power_eq⟩ := twentySeven_dvd
    have powerUnit_pos : 0 < powerUnit := by
      have power_pos : 0 < 3 ^ zeros := pow_pos (by norm_num) zeros
      omega
    let product := powerUnit * middle
    have product_pos : 0 < product := mul_pos powerUnit_pos (by omega)
    have source_code_eq : swappedCode source = 27 * product - 1 := by
      rw [source_code, power_eq]
      simp only [product, mul_assoc]
    have relation :
        (3 * 3 ^ β + 54 * product - 7) * (swappedCode target + 1) ≡
          3 * (54 * product - 3) [MOD 3 ^ β] := by
      rw [source_code_eq] at base_relation
      have coefficient_eq :
          3 * 3 ^ β + 2 * (27 * product - 1) - 5 =
            3 * 3 ^ β + 54 * product - 7 := by omega
      have residue_eq :
          3 * (2 * (27 * product - 1) - 1) = 3 * (54 * product - 3) := by omega
      rw [coefficient_eq, residue_eq] at base_relation
      exact base_relation
    have relation_eightyOne := relation.of_dvd eightyOne_dvd
    have factor_mod : 3 * 3 ^ β + 54 * product - 7 ≡ 2 [MOD 3] := by
      rw [rho_eq, show 3 * (3 * rhoUnit) + 54 * product - 7 =
          3 * (3 * rhoUnit + 18 * product - 3) + 2 by omega]
      exact Nat.ModEq.modulus_mul_add
    have candidate :
        (3 * 3 ^ β + 54 * product - 7) * 36 ≡
          3 * (54 * product - 3) [MOD 81] := by
      rw [rho_eq, show
          (3 * (3 * rhoUnit) + 54 * product - 7) * 36 =
            81 * (4 * rhoUnit + 22 * product - 3) +
              3 * (54 * product - 3) by omega]
      exact Nat.ModEq.modulus_mul_add
    have target_relation := cancel_eightyOne_factor factor_mod
      relation_eightyOne candidate
    exact targetFactor_false_of_quotient (quotient := 4) target_fringe target_relation
      (by norm_num) (by norm_num [Nat.ModEq]) (by norm_num [Nat.ModEq])
      (by norm_num [Nat.ModEq])

private theorem coprime_sevenTwentyNine_of_modEq_two {value : Nat}
    (residue : value ≡ 2 [MOD 3]) : Nat.Coprime value 729 := by
  have not_divisible : ¬3 ∣ value := by
    intro divisibility
    have zero := Nat.modEq_zero_iff_dvd.mpr divisibility
    have impossible := residue.symm.trans zero
    norm_num [Nat.ModEq] at impossible
  have coprime := Nat.prime_three.coprime_pow_of_not_dvd (m := 6) not_divisible
  norm_num at coprime ⊢
  exact coprime

private theorem targetFactor_eq_power_of_quotient_modEq_one
    {width power quotient : Nat} {word : List Bool}
    (target_fringe : TargetFringe width word)
    (relation : swappedCode word + 1 ≡ 3 ^ power * quotient [MOD 3 ^ (power + 2)])
    (quotient_unit : ¬3 ∣ quotient) (quotient_one : quotient ≡ 1 [MOD 9]) :
    swappedCode word + 1 = 3 ^ power := by
  have value_ne : swappedCode word + 1 ≠ 0 := by omega
  rcases targetFringe_codeFactor target_fringe with zero_factor | pair_factor | cut_factor
  · obtain ⟨zeros, _, _, factorization⟩ := zero_factor
    have normalized_factorization :
        swappedCode word + 1 = 3 ^ zeros * 1 := by simpa using factorization
    have unique := powerFactor_of_modEq_twoMore value_ne relation normalized_factorization
      (by norm_num) quotient_unit
    rw [factorization, unique.1]
  · obtain ⟨front, zeros, _, _, factorization⟩ := pair_factor
    have unique := powerFactor_of_modEq_twoMore value_ne relation factorization
      (three_not_dvd_nine_mul_add_five (swappedCode front)) quotient_unit
    have factor_mod_five : 9 * swappedCode front + 5 ≡ 5 [MOD 9] :=
      Nat.ModEq.modulus_mul_add
    have impossible := quotient_one.symm.trans (unique.2.symm.trans factor_mod_five)
    norm_num [Nat.ModEq] at impossible
  · obtain ⟨_, factorization⟩ := cut_factor
    have normalized_factorization :
        swappedCode word + 1 = 3 ^ (width - 1) * 2 := by
      rw [factorization]
      ring
    have unique := powerFactor_of_modEq_twoMore value_ne relation
      normalized_factorization (by norm_num) quotient_unit
    have factor_two : (2 : Nat) ≡ 2 [MOD 9] := Nat.ModEq.refl 2
    have impossible := quotient_one.symm.trans (unique.2.symm.trans factor_two)
    norm_num [Nat.ModEq] at impossible

private theorem targetFactor_false_of_quotient_two_below_cut
    {width power : Nat} {word : List Bool} (power_succ_lt_width : power + 1 < width)
    (target_fringe : TargetFringe width word)
    (relation : swappedCode word + 1 ≡ 3 ^ power * 2 [MOD 3 ^ (power + 2)]) : False := by
  have value_ne : swappedCode word + 1 ≠ 0 := by omega
  rcases targetFringe_codeFactor target_fringe with zero_factor | pair_factor | cut_factor
  · obtain ⟨zeros, _, _, factorization⟩ := zero_factor
    have normalized_factorization :
        swappedCode word + 1 = 3 ^ zeros * 1 := by simpa using factorization
    have unique := powerFactor_of_modEq_twoMore value_ne relation normalized_factorization
      (by norm_num) (by norm_num)
    have impossible := unique.2
    norm_num [Nat.ModEq] at impossible
  · obtain ⟨front, zeros, _, _, factorization⟩ := pair_factor
    have unique := powerFactor_of_modEq_twoMore value_ne relation factorization
      (three_not_dvd_nine_mul_add_five (swappedCode front)) (by norm_num)
    have factor_mod_five : 9 * swappedCode front + 5 ≡ 5 [MOD 9] :=
      Nat.ModEq.modulus_mul_add
    have impossible := unique.2.symm.trans factor_mod_five
    norm_num [Nat.ModEq] at impossible
  · obtain ⟨_, factorization⟩ := cut_factor
    have normalized_factorization :
        swappedCode word + 1 = 3 ^ (width - 1) * 2 := by
      rw [factorization]
      ring
    have unique := powerFactor_of_modEq_twoMore value_ne relation
      normalized_factorization (by norm_num) (by norm_num)
    omega

private theorem targetFactor_false_of_power_quotient
    {width power quotient : Nat} {word : List Bool}
    (target_fringe : TargetFringe width word)
    (relation : swappedCode word + 1 ≡ 3 ^ power * quotient [MOD 3 ^ (power + 2)])
    (quotient_unit : ¬3 ∣ quotient)
    (quotient_ne_one : ¬quotient ≡ 1 [MOD 9])
    (quotient_ne_five : ¬quotient ≡ 5 [MOD 9])
    (quotient_ne_two : ¬quotient ≡ 2 [MOD 9]) : False := by
  have value_ne : swappedCode word + 1 ≠ 0 := by omega
  rcases targetFringe_codeFactor target_fringe with zero_factor | pair_factor | cut_factor
  · obtain ⟨zeros, _, _, factorization⟩ := zero_factor
    have normalized_factorization :
        swappedCode word + 1 = 3 ^ zeros * 1 := by simpa using factorization
    have unique := powerFactor_of_modEq_twoMore value_ne relation normalized_factorization
      (by norm_num) quotient_unit
    exact quotient_ne_one unique.2.symm
  · obtain ⟨front, zeros, _, _, factorization⟩ := pair_factor
    have unique := powerFactor_of_modEq_twoMore value_ne relation factorization
      (three_not_dvd_nine_mul_add_five (swappedCode front)) quotient_unit
    have factor_mod_five : 9 * swappedCode front + 5 ≡ 5 [MOD 9] :=
      Nat.ModEq.modulus_mul_add
    exact quotient_ne_five (unique.2.symm.trans factor_mod_five)
  · obtain ⟨_, factorization⟩ := cut_factor
    have normalized_factorization :
        swappedCode word + 1 = 3 ^ (width - 1) * 2 := by
      rw [factorization]
      ring
    have unique := powerFactor_of_modEq_twoMore value_ne relation
      normalized_factorization (by norm_num) quotient_unit
    have factor_two : (2 : Nat) ≡ 2 [MOD 9] := Nat.ModEq.refl 2
    exact quotient_ne_two (unique.2.symm.trans factor_two)

private theorem allOnes_patternSource_oneTail_false
    {β : Nat} (β_large : 7 ≤ β) {upper source target front : List Bool}
    (front_phases : List Bool) (front_eq : front = spell fringeBlock front_phases)
    (source_eq : source = front ++ [true, true] ++ List.replicate 1 false)
    (upper_code : 2 * swappedCode upper + 1 = 9 * 3 ^ β)
    (target_fringe : TargetFringe (β + 2) target)
    (pole : PoleCongruence β upper source target) : False := by
  have source_code_add := swappedCode_pair_zero_tail front 1
  have source_code : swappedCode source = 27 * swappedCode front + 14 := by
    rw [source_eq]
    norm_num at source_code_add ⊢
    omega
  have source_lower : 2 ≤ swappedCode source := by omega
  have base_relation := allOnesPole_relation source_lower upper_code pole
  have relation :
      (3 * 3 ^ β + 54 * swappedCode front + 23) * (swappedCode target + 1) ≡
        3 * (54 * swappedCode front + 27) [MOD 3 ^ β] := by
    rw [source_code] at base_relation
    have coefficient_eq :
        3 * 3 ^ β + 2 * (27 * swappedCode front + 14) - 5 =
          3 * 3 ^ β + 54 * swappedCode front + 23 := by omega
    have residue_eq :
        3 * (2 * (27 * swappedCode front + 14) - 1) =
          3 * (54 * swappedCode front + 27) := by omega
    rw [coefficient_eq, residue_eq] at base_relation
    exact base_relation
  have sevenTwentyNine_dvd : 729 ∣ 3 ^ β :=
    Nat.pow_dvd_pow 3 (show 6 ≤ β by omega)
  have relation_sevenTwentyNine := relation.of_dvd sevenTwentyNine_dvd
  have three_dvd_rho : 3 ∣ 3 ^ β := Nat.pow_dvd_pow 3 (show 1 ≤ β by omega)
  obtain ⟨rhoUnit, rho_eq⟩ := three_dvd_rho
  have factor_mod : 3 * 3 ^ β + 54 * swappedCode front + 23 ≡ 2 [MOD 3] := by
    rw [rho_eq, show
        3 * (3 * rhoUnit) + 54 * swappedCode front + 23 =
          3 * (3 * rhoUnit + 18 * swappedCode front + 7) + 2 by ring]
    exact Nat.ModEq.modulus_mul_add
  have candidate :
      (3 * 3 ^ β + 54 * swappedCode front + 23) *
          (81 * (4 * swappedCode front + 2)) ≡
        3 * (54 * swappedCode front + 27) [MOD 729] := by
    rw [rho_eq, show
        (3 * (3 * rhoUnit) + 54 * swappedCode front + 23) *
            (81 * (4 * swappedCode front + 2)) =
          729 * (rhoUnit * (4 * swappedCode front + 2) +
            24 * swappedCode front * swappedCode front +
            22 * swappedCode front + 5) +
            3 * (54 * swappedCode front + 27) by ring]
    exact Nat.ModEq.modulus_mul_add
  have target_relation :
      swappedCode target + 1 ≡ 81 * (4 * swappedCode front + 2) [MOD 729] := by
    apply Nat.ModEq.cancel_left_of_coprime
      (coprime_sevenTwentyNine_of_modEq_two factor_mod).symm.gcd_eq_one
    exact relation_sevenTwentyNine.trans candidate.symm
  have front_cases := swappedCode_complete_modNine_cases front_phases
  rw [← front_eq] at front_cases
  rcases front_cases with front_zero | front_two | front_five | front_eight
  · have specialized_target := target_relation
    rw [front_zero] at specialized_target
    have normalized_target :
        swappedCode target + 1 ≡ 3 ^ 4 * 2 [MOD 3 ^ (4 + 2)] := by
      norm_num at specialized_target ⊢
      exact specialized_target
    exact targetFactor_false_of_quotient_two_below_cut (by omega) target_fringe
      normalized_target
  · have specialized_target := target_relation
    rw [front_two] at specialized_target
    have normalized_target :
        swappedCode target + 1 ≡ 3 ^ 4 * 10 [MOD 3 ^ (4 + 2)] := by
      norm_num at specialized_target ⊢
      exact specialized_target
    have target_code := targetFactor_eq_power_of_quotient_modEq_one target_fringe
      normalized_target (by norm_num) (by norm_num [Nat.ModEq])
    have specialized_relation := relation
    rw [front_two] at specialized_relation
    have relation_int :
        ((3 * 3 ^ β + 131) * (swappedCode target + 1) : ℤ) ≡
          405 [ZMOD (3 : ℤ) ^ β] := by
      exact Int.natCast_modEq_iff.mpr specialized_relation
    have difference_dvd := Int.dvd_neg.mpr relation_int.dvd
    have target_code_int : (swappedCode target : ℤ) + 1 = 81 := by
      exact_mod_cast target_code
    have rho_dvd_whole :
        ((3 : ℤ) ^ β) ∣ 243 * (3 : ℤ) ^ β + 10206 := by
      convert difference_dvd using 1
      rw [target_code_int]
      norm_num
      ring
    have rho_dvd_bulk : ((3 : ℤ) ^ β) ∣ 243 * (3 : ℤ) ^ β := dvd_mul_left _ _
    have rho_dvd_fixed : ((3 : ℤ) ^ β) ∣ 10206 := by
      convert Int.dvd_sub rho_dvd_whole rho_dvd_bulk using 1
      ring
    have rho_dvd_fixed_nat : 3 ^ β ∣ 10206 := by
      exact_mod_cast rho_dvd_fixed
    exact pow_three_not_dvd_10206 (by omega) rho_dvd_fixed_nat
  · have scaled := front_five.mul_left 4
    have shifted := scaled.add (Nat.ModEq.refl 2)
    have quotient_residue : 4 * swappedCode front + 2 ≡ 4 [MOD 9] := by
      norm_num at shifted ⊢
      exact shifted
    have quotient_unit : ¬3 ∣ 4 * swappedCode front + 2 := by
      intro divisibility
      have zero := Nat.modEq_zero_iff_dvd.mpr divisibility
      have residue_mod_three := quotient_residue.of_dvd (by norm_num : 3 ∣ 9)
      have impossible := residue_mod_three.symm.trans zero
      norm_num [Nat.ModEq] at impossible
    have quotient_ne_one : ¬4 * swappedCode front + 2 ≡ 1 [MOD 9] := by
      intro residue_one
      have impossible := quotient_residue.symm.trans residue_one
      norm_num [Nat.ModEq] at impossible
    have quotient_ne_five : ¬4 * swappedCode front + 2 ≡ 5 [MOD 9] := by
      intro residue_five
      have impossible := quotient_residue.symm.trans residue_five
      norm_num [Nat.ModEq] at impossible
    have quotient_ne_two : ¬4 * swappedCode front + 2 ≡ 2 [MOD 9] := by
      intro residue_two
      have impossible := quotient_residue.symm.trans residue_two
      norm_num [Nat.ModEq] at impossible
    have normalized_target :
        swappedCode target + 1 ≡
          3 ^ 4 * (4 * swappedCode front + 2) [MOD 3 ^ (4 + 2)] := by
      norm_num at target_relation ⊢
      exact target_relation
    exact targetFactor_false_of_power_quotient target_fringe normalized_target quotient_unit
      quotient_ne_one quotient_ne_five quotient_ne_two
  · have scaled := front_eight.mul_left 4
    have shifted := scaled.add (Nat.ModEq.refl 2)
    have quotient_residue : 4 * swappedCode front + 2 ≡ 7 [MOD 9] := by
      norm_num at shifted ⊢
      exact shifted
    have quotient_unit : ¬3 ∣ 4 * swappedCode front + 2 := by
      intro divisibility
      have zero := Nat.modEq_zero_iff_dvd.mpr divisibility
      have residue_mod_three := quotient_residue.of_dvd (by norm_num : 3 ∣ 9)
      have impossible := residue_mod_three.symm.trans zero
      norm_num [Nat.ModEq] at impossible
    have quotient_ne_one : ¬4 * swappedCode front + 2 ≡ 1 [MOD 9] := by
      intro residue_one
      have impossible := quotient_residue.symm.trans residue_one
      norm_num [Nat.ModEq] at impossible
    have quotient_ne_five : ¬4 * swappedCode front + 2 ≡ 5 [MOD 9] := by
      intro residue_five
      have impossible := quotient_residue.symm.trans residue_five
      norm_num [Nat.ModEq] at impossible
    have quotient_ne_two : ¬4 * swappedCode front + 2 ≡ 2 [MOD 9] := by
      intro residue_two
      have impossible := quotient_residue.symm.trans residue_two
      norm_num [Nat.ModEq] at impossible
    have normalized_target :
        swappedCode target + 1 ≡
          3 ^ 4 * (4 * swappedCode front + 2) [MOD 3 ^ (4 + 2)] := by
      norm_num at target_relation ⊢
      exact target_relation
    exact targetFactor_false_of_power_quotient target_fringe normalized_target quotient_unit
      quotient_ne_one quotient_ne_five quotient_ne_two

private theorem allOnes_sourceFringe_false
    {β : Nat} (β_large : 7 ≤ β) {upper source target : List Bool}
    (source_fringe : SourceFringe source) (source_last : source.getLast? = some false)
    (upper_code : 2 * swappedCode upper + 1 = 9 * 3 ^ β)
    (target_fringe : TargetFringe (β + 2) target)
    (pole : PoleCongruence β upper source target) : False := by
  rcases sourceFringe_lastTrue_normal source_fringe source_last with zero_run | pair_run
  · obtain ⟨zeros, zeros_pos, source_eq⟩ := zero_run
    exact allOnes_zeroSource_false (by omega) zeros_pos source_eq upper_code target_fringe pole
  · obtain ⟨front, phases, zeros, zeros_pos, front_eq, source_eq⟩ := pair_run
    by_cases one_tail : zeros = 1
    · subst zeros
      exact allOnes_patternSource_oneTail_false β_large phases front_eq source_eq upper_code
        target_fringe pole
    · exact allOnes_patternSource_highTail_false (by omega) (by omega) phases front_eq source_eq
        upper_code target_fringe pole

private theorem runPole_terminal_shapes
    {β ones : Nat} (β_large : 5 ≤ β) (ones_lower : 2 ≤ ones)
    (ones_upper : ones ≤ β + 1) {upper source target : List Bool}
    (upper_eq :
      upper = List.replicate ones true ++ List.replicate (β + 2 - ones) false)
    (source_eq : source = []) (target_fringe : TargetFringe (β + 2) target)
    (pole : PoleCongruence β upper source target) :
    (upper = List.replicate 3 true ++ List.replicate (β - 1) false ∧ source = []) ∨
      (upper = List.replicate 2 true ++ List.replicate β false ∧ source = []) := by
  let zeros := β + 2 - ones
  have zeros_pos : 1 ≤ zeros := by
    dsimp [zeros]
    omega
  have sum_eq : ones + zeros = β + 2 := by
    dsimp [zeros]
    omega
  have upper_code_raw := swappedCode_true_false_run ones zeros
  have upper_code : 2 * swappedCode upper + 2 = 9 * 3 ^ β + 3 ^ zeros := by
    rw [upper_eq]
    rw [sum_eq] at upper_code_raw
    simpa [pow_add, Nat.mul_comm] using upper_code_raw
  have zeros_lower : β - 1 ≤ zeros := by
    by_contra lower_failure
    have zeros_inside : zeros + 2 ≤ β := by omega
    subst source
    exact runPole_inside_false β_large zeros_pos zeros_inside upper_code target_fringe pole
  have zeros_upper : zeros ≤ β := by omega
  rcases (show zeros = β - 1 ∨ zeros = β by omega) with zeros_eq | zeros_eq
  · left
    refine ⟨?_, source_eq⟩
    have ones_eq : ones = 3 := by omega
    rw [upper_eq, ones_eq]
    congr 1
  · right
    refine ⟨?_, source_eq⟩
    have ones_eq : ones = 2 := by omega
    rw [upper_eq, ones_eq]
    congr 1

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
