import MatrixMortality.SwappedSetterFringe
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Tag-upper fringe classification

The shifted swapped codes of complete source and target fringes expose a three-adic unit after
their final zero run.  The pole congruence leaves two and only two terminal tag pairs.
-/

namespace MatrixMortality.SwappedSetterFringe

private theorem exponent_eq_of_unit_relation
    {value exponent factor power unit : Nat} (value_ne : value ≠ 0)
    (relation : value ≡ 3 ^ power * unit [MOD 3 ^ (power + 1)])
    (factorization : value = 3 ^ exponent * factor)
    (factor_unit : ¬3 ∣ factor) (right_unit : ¬3 ∣ unit) :
    exponent = power := by
  have power_dvd_modulus : 3 ^ power ∣ 3 ^ (power + 1) :=
    Nat.pow_dvd_pow 3 (by omega)
  have lower_divisor : 3 ^ power ∣ value :=
    (relation.dvd_iff power_dvd_modulus).mpr (dvd_mul_right _ _)
  have upper_not_divisor : ¬3 ^ (power + 1) ∣ value := by
    intro divides_value
    have divides_right :=
      (relation.dvd_iff (dvd_refl (3 ^ (power + 1)))).mp divides_value
    have normalized : 3 ^ power * 3 ∣ 3 ^ power * unit := by
      simpa only [pow_succ] using divides_right
    have divides_unit : 3 ∣ unit :=
      Nat.dvd_of_mul_dvd_mul_left (pow_pos (by norm_num) power) normalized
    exact right_unit divides_unit
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
  omega

private theorem tagFactor_source_bounds {b e u : Nat} (e_pos : 1 ≤ e)
    (u_unit : ¬3 ∣ u) (factorization : b + 1 = 3 ^ e * u) :
    2 ≤ b ∧ b - 1 = 3 ^ e * u - 2 ∧ ¬3 ∣ b - 1 := by
  have u_pos : 0 < u := by
    by_contra u_zero
    have u_eq : u = 0 := by omega
    subst u
    exact u_unit (dvd_zero 3)
  have power_lower : 3 ≤ 3 ^ e :=
    Nat.pow_le_pow_right (n := 3) (by norm_num) e_pos
  have product_lower : 3 ≤ 3 ^ e * u := by
    calc
      3 ≤ 3 ^ e := power_lower
      _ ≤ 3 ^ e * u := Nat.le_mul_of_pos_right _ u_pos
  have b_lower : 2 ≤ b := by omega
  have shifted : b - 1 = 3 ^ e * u - 2 := by omega
  have three_dvd_b_add : 3 ∣ b + 1 := by
    rw [factorization]
    exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow 3 e_pos) u
  have b_unit : ¬3 ∣ b - 1 := by
    intro three_dvd_b_sub
    obtain ⟨left, left_eq⟩ := three_dvd_b_add
    obtain ⟨right, right_eq⟩ := three_dvd_b_sub
    omega
  exact ⟨b_lower, shifted, b_unit⟩

private theorem tagFactor_lowZone {β b t e u z v : Nat}
    (e_pos : 1 ≤ e) (zone : e + 3 ≤ β)
    (source_factor : b + 1 = 3 ^ e * u) (source_unit : ¬3 ∣ u)
    (target_factor : t = 3 ^ z * v) (target_unit : ¬3 ∣ v)
    (relation :
      (b - 1) * t + (b + 14) * 3 ^ β ≡ 3 * (b + 1) [MOD 9 * 3 ^ β]) :
    z = e + 1 ∧ (3 ^ e * u - 2) * v ≡ u [MOD 9] := by
  obtain ⟨b_lower, b_shift, b_unit⟩ :=
    tagFactor_source_bounds e_pos source_unit source_factor
  have modulus_eq : 9 * 3 ^ β = 3 ^ (β + 2) := by
    rw [pow_add]
    norm_num
    ring
  have small_dvd : 3 ^ (e + 2) ∣ 9 * 3 ^ β := by
    rw [modulus_eq]
    exact Nat.pow_dvd_pow 3 (by omega)
  have small_relation := relation.of_dvd small_dvd
  have rho_dvd_small : 3 ^ (e + 2) ∣ (b + 14) * 3 ^ β := by
    exact dvd_mul_of_dvd_right (Nat.pow_dvd_pow 3 (by omega)) _
  have rho_zero := Dvd.dvd.modEq_zero_nat rho_dvd_small
  have core_relation :
      (b - 1) * t ≡ 3 * (b + 1) [MOD 3 ^ (e + 2)] := by
    exact rho_zero.add_right_cancel (by simpa using small_relation)
  have factor_unit : ¬3 ∣ (b - 1) * v := by
    intro divides
    rcases Nat.prime_three.dvd_mul.mp divides with left | right
    · exact b_unit left
    · exact target_unit right
  have value_ne : (b - 1) * t ≠ 0 := by
    have b_sub_pos : 0 < b - 1 := by omega
    have v_pos : 0 < v := by
      by_contra v_zero
      have v_eq : v = 0 := by omega
      subst v
      exact target_unit (dvd_zero 3)
    rw [target_factor]
    positivity
  have value_factorization :
      (b - 1) * t = 3 ^ z * ((b - 1) * v) := by
    rw [target_factor]
    ring
  have normalized_core :
      (b - 1) * t ≡ 3 ^ (e + 1) * u [MOD 3 ^ ((e + 1) + 1)] := by
    rw [source_factor] at core_relation
    simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using core_relation
  have exponent_eq := exponent_eq_of_unit_relation value_ne normalized_core
    value_factorization factor_unit source_unit
  have residue_dvd : 3 ^ (e + 3) ∣ 9 * 3 ^ β := by
    rw [modulus_eq]
    exact Nat.pow_dvd_pow 3 (by omega)
  have residue_relation := relation.of_dvd residue_dvd
  have correction_dvd : 3 ^ (e + 3) ∣ (b + 14) * 3 ^ β := by
    exact dvd_mul_of_dvd_right (Nat.pow_dvd_pow 3 zone) _
  have correction_zero := Dvd.dvd.modEq_zero_nat correction_dvd
  have residue_core :
      (b - 1) * t ≡ 3 * (b + 1) [MOD 3 ^ (e + 3)] := by
    exact correction_zero.add_right_cancel (by simpa using residue_relation)
  have cancelled :
      3 ^ (e + 1) * ((3 ^ e * u - 2) * v) ≡
        3 ^ (e + 1) * u [MOD 3 ^ (e + 1) * 9] := by
    rw [target_factor, exponent_eq, source_factor, b_shift] at residue_core
    have small_modulus_eq : 3 ^ (e + 3) = 3 ^ (e + 1) * 9 := by
      rw [show e + 3 = (e + 1) + 2 by omega, pow_add]
      norm_num
    rw [small_modulus_eq] at residue_core
    simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using residue_core
  have power_ne : 3 ^ (e + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact ⟨exponent_eq, cancelled.mul_left_cancel' power_ne⟩

private theorem tagFactor_coefficient_mod_of_exponent_one {u residue : Nat}
    (u_pos : 1 ≤ u) (residue_pos : 1 ≤ residue)
    (unit_mod : u ≡ residue [MOD 9]) :
    3 ^ 1 * u - 2 ≡ 3 * residue - 2 [MOD 9] := by
  have scaled := unit_mod.mul_left 3
  simpa using Nat.ModEq.sub (by omega) (by omega) scaled (Nat.ModEq.refl 2)

private theorem tagFactor_coefficient_mod_of_exponent_large {e u : Nat}
    (e_large : 2 ≤ e) (u_pos : 1 ≤ u) :
    3 ^ e * u - 2 ≡ 7 [MOD 9] := by
  have nine_dvd_power : 9 ∣ 3 ^ e := by
    exact Nat.pow_dvd_pow 3 e_large
  obtain ⟨quotient, quotient_eq⟩ := dvd_mul_of_dvd_left nine_dvd_power u
  have product_lower : 9 ≤ 3 ^ e * u := by
    have power_lower : 9 ≤ 3 ^ e := by
      change 3 ^ 2 ≤ 3 ^ e
      exact Nat.pow_le_pow_right (by norm_num) e_large
    exact power_lower.trans (Nat.le_mul_of_pos_right _ u_pos)
  have quotient_pos : 1 ≤ quotient := by omega
  rw [quotient_eq, show 9 * quotient - 2 = 9 * (quotient - 1) + 7 by omega]
  exact Nat.ModEq.modulus_mul_add

private theorem tagFactor_lowZone_false {β b t e u z v : Nat}
    (e_pos : 1 ≤ e) (zone : e + 3 ≤ β)
    (source_factor : b + 1 = 3 ^ e * u) (source_unit : ¬3 ∣ u)
    (source_kind : u = 1 ∨ u ≡ 5 [MOD 9])
    (target_factor : t = 3 ^ z * v) (target_unit : ¬3 ∣ v)
    (target_kind : v = 1 ∨ v ≡ 5 [MOD 9] ∨ (v = 2 ∧ z = β + 1))
    (relation :
      (b - 1) * t + (b + 14) * 3 ^ β ≡ 3 * (b + 1) [MOD 9 * 3 ^ β]) :
    False := by
  obtain ⟨exponent_eq, residue_relation⟩ := tagFactor_lowZone e_pos zone
    source_factor source_unit target_factor target_unit relation
  have u_pos : 1 ≤ u := by
    by_contra u_zero
    have u_eq : u = 0 := by omega
    subst u
    exact source_unit (dvd_zero 3)
  have v_pos : 1 ≤ v := by
    by_contra v_zero
    have v_eq : v = 0 := by omega
    subst v
    exact target_unit (dvd_zero 3)
  rcases source_kind with rfl | source_five
  · rcases target_kind with rfl | target_nonzero
    · by_cases exponent_one : e = 1
      · subst e
        have b_eq : b = 2 := by norm_num at source_factor ⊢; omega
        have z_eq : z = 2 := by omega
        subst b
        subst z
        have t_eq : t = 9 := by norm_num at target_factor ⊢; exact target_factor
        subst t
        have rho_pos : 0 < 3 ^ β := pow_pos (by norm_num) β
        have reduced : 9 * 3 ^ β ∣ 16 * 3 ^ β := by
          rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' (by omega)] at relation
          norm_num at relation ⊢
          simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using relation
        have nine_dvd_sixteen : 9 ∣ 16 := by
          exact Nat.dvd_of_mul_dvd_mul_right rho_pos (by
            simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using reduced)
        norm_num at nine_dvd_sixteen
      · have e_large : 2 ≤ e := by omega
        have coefficient_mod :=
          tagFactor_coefficient_mod_of_exponent_large e_large (by norm_num : 1 ≤ 1)
        have left_mod := coefficient_mod.mul (Nat.ModEq.refl 1)
        have impossible := left_mod.symm.trans residue_relation
        norm_num [Nat.ModEq] at impossible
    · rcases target_nonzero with target_five | ⟨rfl, cut_exponent⟩
      · by_cases exponent_one : e = 1
        · subst e
          have coefficient_mod := tagFactor_coefficient_mod_of_exponent_one
            (by norm_num : 1 ≤ 1) (by norm_num : 1 ≤ 1) (Nat.ModEq.refl 1)
          have left_mod := coefficient_mod.mul target_five
          have impossible := left_mod.symm.trans residue_relation
          norm_num [Nat.ModEq] at impossible
        · have coefficient_mod := tagFactor_coefficient_mod_of_exponent_large
            (show 2 ≤ e by omega) (by norm_num : 1 ≤ 1)
          have left_mod := coefficient_mod.mul target_five
          have impossible := left_mod.symm.trans residue_relation
          norm_num [Nat.ModEq] at impossible
      · rcases show e = 1 ∨ 2 ≤ e by omega with exponent_one | exponent_large
        · subst e
          have coefficient_mod := tagFactor_coefficient_mod_of_exponent_one
            (by norm_num : 1 ≤ 1) (by norm_num : 1 ≤ 1) (Nat.ModEq.refl 1)
          have left_mod := coefficient_mod.mul (Nat.ModEq.refl 2)
          have impossible := left_mod.symm.trans residue_relation
          norm_num [Nat.ModEq] at impossible
        · have coefficient_mod := tagFactor_coefficient_mod_of_exponent_large
            exponent_large (by norm_num : 1 ≤ 1)
          have left_mod := coefficient_mod.mul (Nat.ModEq.refl 2)
          have impossible := left_mod.symm.trans residue_relation
          norm_num [Nat.ModEq] at impossible
  · rcases target_kind with rfl | target_nonzero
    · rcases show e = 1 ∨ 2 ≤ e by omega with rfl | exponent_large
      · have coefficient_mod := tagFactor_coefficient_mod_of_exponent_one
          u_pos (by norm_num : 1 ≤ 5) source_five
        have left_mod := coefficient_mod.mul (Nat.ModEq.refl 1)
        have impossible := (left_mod.symm.trans residue_relation).trans source_five
        norm_num [Nat.ModEq] at impossible
      · have coefficient_mod :=
          tagFactor_coefficient_mod_of_exponent_large exponent_large u_pos
        have left_mod := coefficient_mod.mul (Nat.ModEq.refl 1)
        have impossible := (left_mod.symm.trans residue_relation).trans source_five
        norm_num [Nat.ModEq] at impossible
    · rcases target_nonzero with target_five | ⟨rfl, cut_exponent⟩
      · rcases show e = 1 ∨ 2 ≤ e by omega with rfl | exponent_large
        · have coefficient_mod := tagFactor_coefficient_mod_of_exponent_one
            u_pos (by norm_num : 1 ≤ 5) source_five
          have left_mod := coefficient_mod.mul target_five
          have impossible := (left_mod.symm.trans residue_relation).trans source_five
          norm_num [Nat.ModEq] at impossible
        · have coefficient_mod :=
            tagFactor_coefficient_mod_of_exponent_large exponent_large u_pos
          have left_mod := coefficient_mod.mul target_five
          have impossible := (left_mod.symm.trans residue_relation).trans source_five
          norm_num [Nat.ModEq] at impossible
      · rcases show e = 1 ∨ 2 ≤ e by omega with rfl | exponent_large
        · have coefficient_mod := tagFactor_coefficient_mod_of_exponent_one
            u_pos (by norm_num : 1 ≤ 5) source_five
          have left_mod := coefficient_mod.mul (Nat.ModEq.refl 2)
          have impossible := (left_mod.symm.trans residue_relation).trans source_five
          norm_num [Nat.ModEq] at impossible
        · omega

private theorem tagFactor_midZone {β b t u z v : Nat}
    (β_large : 5 ≤ β)
    (source_factor : b + 1 = 3 ^ (β - 2) * u) (source_unit : ¬3 ∣ u)
    (target_factor : t = 3 ^ z * v) (target_unit : ¬3 ∣ v)
    (relation :
      (b - 1) * t + (b + 14) * 3 ^ β ≡ 3 * (b + 1) [MOD 9 * 3 ^ β]) :
    z = β - 1 ∧
      (3 ^ (β - 2) * u - 2) * v + 3 * (3 ^ (β - 2) * u + 13) ≡
        u [MOD 27] := by
  have exponent_pos : 1 ≤ β - 2 := by omega
  obtain ⟨b_lower, b_shift, b_unit⟩ :=
    tagFactor_source_bounds exponent_pos source_unit source_factor
  have rho_dvd_modulus : 3 ^ β ∣ 9 * 3 ^ β := dvd_mul_left _ _
  have reduced := relation.of_dvd rho_dvd_modulus
  have correction_zero : (b + 14) * 3 ^ β ≡ 0 [MOD 3 ^ β] := by
    exact Dvd.dvd.modEq_zero_nat (dvd_mul_left _ _)
  have core_relation : (b - 1) * t ≡ 3 * (b + 1) [MOD 3 ^ β] := by
    exact correction_zero.add_right_cancel (by simpa using reduced)
  have factor_unit : ¬3 ∣ (b - 1) * v := by
    intro divides
    rcases Nat.prime_three.dvd_mul.mp divides with left | right
    · exact b_unit left
    · exact target_unit right
  have value_ne : (b - 1) * t ≠ 0 := by
    have b_sub_pos : 0 < b - 1 := by omega
    have v_pos : 0 < v := by
      by_contra v_zero
      have v_eq : v = 0 := by omega
      subst v
      exact target_unit (dvd_zero 3)
    rw [target_factor]
    positivity
  have value_factorization :
      (b - 1) * t = 3 ^ z * ((b - 1) * v) := by
    rw [target_factor]
    ring
  have normalized_core :
      (b - 1) * t ≡ 3 ^ (β - 1) * u [MOD 3 ^ ((β - 1) + 1)] := by
    rw [source_factor] at core_relation
    have rhs_eq : 3 * (3 ^ (β - 2) * u) = 3 ^ (β - 1) * u := by
      rw [show β - 1 = (β - 2) + 1 by omega, pow_succ]
      ring
    rw [rhs_eq] at core_relation
    have modulus_eq : 3 ^ β = 3 ^ ((β - 1) + 1) := by
      congr 1
      omega
    rw [← modulus_eq]
    exact core_relation
  have target_exponent := exponent_eq_of_unit_relation value_ne normalized_core
    value_factorization factor_unit source_unit
  have exponent_eq : z = β - 1 := by simpa using target_exponent
  have source_product_lower : 3 ≤ 3 ^ (β - 2) * u := by
    have u_pos : 1 ≤ u := by
      by_contra u_zero
      have u_eq : u = 0 := by omega
      subst u
      exact source_unit (dvd_zero 3)
    have power_lower : 3 ≤ 3 ^ (β - 2) :=
      Nat.pow_le_pow_right (n := 3) (by norm_num) exponent_pos
    exact power_lower.trans (Nat.le_mul_of_pos_right _ u_pos)
  have source_plus : b + 14 = 3 ^ (β - 2) * u + 13 := by omega
  have rho_eq : 3 ^ β = 3 ^ (β - 1) * 3 := by
    calc
      3 ^ β = 3 ^ ((β - 1) + 1) := by
        apply congrArg (fun exponent : Nat => 3 ^ exponent)
        omega
      _ = 3 ^ (β - 1) * 3 := pow_succ _ _
  have rhs_eq : 3 * (3 ^ (β - 2) * u) = 3 ^ (β - 1) * u := by
    have exponent_eq' : β - 1 = (β - 2) + 1 := by omega
    rw [exponent_eq', pow_succ]
    ring
  rw [b_shift, source_plus, source_factor, target_factor, exponent_eq,
    rho_eq, rhs_eq] at relation
  have modulus_eq : 9 * (3 ^ (β - 1) * 3) = 3 ^ (β - 1) * 27 := by ring
  rw [modulus_eq] at relation
  have factored :
      3 ^ (β - 1) *
          ((3 ^ (β - 2) * u - 2) * v + 3 * (3 ^ (β - 2) * u + 13)) ≡
        3 ^ (β - 1) * u [MOD 3 ^ (β - 1) * 27] := by
    have left_eq :
        3 ^ (β - 1) *
            ((3 ^ (β - 2) * u - 2) * v + 3 * (3 ^ (β - 2) * u + 13)) =
          (3 ^ (β - 2) * u - 2) * (3 ^ (β - 1) * v) +
            (3 ^ (β - 2) * u + 13) * (3 ^ (β - 1) * 3) := by ring
    rw [left_eq]
    exact relation
  exact ⟨exponent_eq, factored.mul_left_cancel' (pow_ne_zero _ (by norm_num))⟩

private theorem tagFactor_coefficient_mod_twentySeven {e u : Nat}
    (e_large : 3 ≤ e) (u_pos : 1 ≤ u) :
    3 ^ e * u - 2 ≡ 25 [MOD 27] ∧ 3 ^ e * u + 13 ≡ 13 [MOD 27] := by
  have power_dvd : 27 ∣ 3 ^ e := Nat.pow_dvd_pow 3 e_large
  have product_dvd : 27 ∣ 3 ^ e * u := dvd_mul_of_dvd_left power_dvd u
  have product_zero : 3 ^ e * u ≡ 0 [MOD 27] := Dvd.dvd.modEq_zero_nat product_dvd
  obtain ⟨quotient, quotient_eq⟩ := product_dvd
  have product_lower : 27 ≤ 3 ^ e * u := by
    have power_lower : 27 ≤ 3 ^ e := by
      change 3 ^ 3 ≤ 3 ^ e
      exact Nat.pow_le_pow_right (by norm_num) e_large
    exact power_lower.trans (Nat.le_mul_of_pos_right _ u_pos)
  have quotient_pos : 1 ≤ quotient := by omega
  constructor
  · rw [quotient_eq, show 27 * quotient - 2 = 27 * (quotient - 1) + 25 by omega]
    exact Nat.ModEq.modulus_mul_add
  · exact product_zero.add (Nat.ModEq.refl 13)

private theorem tagFactor_midZone_false {β b t u z v : Nat}
    (β_large : 5 ≤ β)
    (source_factor : b + 1 = 3 ^ (β - 2) * u) (source_unit : ¬3 ∣ u)
    (source_kind : u = 1 ∨ u ≡ 5 [MOD 9])
    (target_factor : t = 3 ^ z * v) (target_unit : ¬3 ∣ v)
    (target_kind : v = 1 ∨ v ≡ 5 [MOD 9] ∨ (v = 2 ∧ z = β + 1))
    (relation :
      (b - 1) * t + (b + 14) * 3 ^ β ≡ 3 * (b + 1) [MOD 9 * 3 ^ β]) :
    False := by
  obtain ⟨exponent_eq, quotient_relation⟩ := tagFactor_midZone β_large
    source_factor source_unit target_factor target_unit relation
  have u_pos : 1 ≤ u := by
    by_contra u_zero
    have u_eq : u = 0 := by omega
    subst u
    exact source_unit (dvd_zero 3)
  obtain ⟨coefficient_mod, correction_mod⟩ :=
    tagFactor_coefficient_mod_twentySeven (show 3 ≤ β - 2 by omega) u_pos
  rcases source_kind with rfl | source_five
  · rcases target_kind with rfl | target_nonzero
    · have left_mod := (coefficient_mod.mul (Nat.ModEq.refl 1)).add
        (correction_mod.mul_left 3)
      have impossible := left_mod.symm.trans quotient_relation
      norm_num [Nat.ModEq] at impossible
    · rcases target_nonzero with target_five | ⟨rfl, cut_exponent⟩
      · have coefficient_nine := coefficient_mod.of_dvd (by norm_num : 9 ∣ 27)
        have correction_nine := correction_mod.of_dvd (by norm_num : 9 ∣ 27)
        have relation_nine := quotient_relation.of_dvd (by norm_num : 9 ∣ 27)
        have left_mod := (coefficient_nine.mul target_five).add
          (correction_nine.mul_left 3)
        have impossible := left_mod.symm.trans relation_nine
        norm_num [Nat.ModEq] at impossible
      · omega
  · rcases target_kind with rfl | target_nonzero
    · have left_mod := (coefficient_mod.mul (Nat.ModEq.refl 1)).add
        (correction_mod.mul_left 3)
      have impossible := ((left_mod.of_dvd (by norm_num : 9 ∣ 27)).symm.trans
        (quotient_relation.of_dvd (by norm_num : 9 ∣ 27))).trans source_five
      norm_num [Nat.ModEq] at impossible
    · rcases target_nonzero with target_five | ⟨rfl, cut_exponent⟩
      · have coefficient_nine := coefficient_mod.of_dvd (by norm_num : 9 ∣ 27)
        have correction_nine := correction_mod.of_dvd (by norm_num : 9 ∣ 27)
        have relation_nine := quotient_relation.of_dvd (by norm_num : 9 ∣ 27)
        have left_mod := (coefficient_nine.mul target_five).add
          (correction_nine.mul_left 3)
        have impossible := (left_mod.symm.trans relation_nine).trans source_five
        norm_num [Nat.ModEq] at impossible
      · omega

private theorem tagFactor_highZone {β e b t u q : Nat}
    (β_large : 2 ≤ β) (tail_terminal : β - 1 ≤ e)
    (u_pos : 1 ≤ u)
    (source_factor : b + 1 = 3 ^ e * u)
    (target_factor : t = 3 ^ β * q)
    (relation :
      (b - 1) * t + (b + 14) * 3 ^ β ≡ 3 * (b + 1) [MOD 9 * 3 ^ β]) :
    (3 ^ e * u - 2) * q + (3 ^ e * u + 13) ≡
      3 ^ (e + 1 - β) * u [MOD 9] := by
  have exponent_pos : 1 ≤ e := by omega
  have source_product_lower : 3 ≤ 3 ^ e * u := by
    have power_lower : 3 ≤ 3 ^ e :=
      Nat.pow_le_pow_right (n := 3) (by norm_num) exponent_pos
    exact power_lower.trans (Nat.le_mul_of_pos_right _ u_pos)
  have source_minus : b - 1 = 3 ^ e * u - 2 := by omega
  have source_plus : b + 14 = 3 ^ e * u + 13 := by omega
  have high_power : 3 ^ (e + 1) = 3 ^ β * 3 ^ (e + 1 - β) := by
    calc
      3 ^ (e + 1) = 3 ^ (β + (e + 1 - β)) := by
        apply congrArg (fun exponent : Nat => 3 ^ exponent)
        omega
      _ = 3 ^ β * 3 ^ (e + 1 - β) := pow_add _ _ _
  have rhs_eq : 3 * (3 ^ e * u) = 3 ^ β * (3 ^ (e + 1 - β) * u) := by
    calc
      3 * (3 ^ e * u) = 3 ^ (e + 1) * u := by rw [pow_succ]; ring
      _ = 3 ^ β * (3 ^ (e + 1 - β) * u) := by rw [high_power]; ring
  rw [source_minus, source_plus, source_factor, target_factor, rhs_eq] at relation
  have modulus_eq : 9 * 3 ^ β = 3 ^ β * 9 := by ring
  rw [modulus_eq] at relation
  have factored :
      3 ^ β * ((3 ^ e * u - 2) * q + (3 ^ e * u + 13)) ≡
        3 ^ β * (3 ^ (e + 1 - β) * u) [MOD 3 ^ β * 9] := by
    have left_eq :
        3 ^ β * ((3 ^ e * u - 2) * q + (3 ^ e * u + 13)) =
          (3 ^ e * u - 2) * (3 ^ β * q) + (3 ^ e * u + 13) * 3 ^ β := by ring
    rw [left_eq]
    exact relation
  exact factored.mul_left_cancel' (pow_ne_zero _ (by norm_num))

private theorem tagFactor_highZone_target_dvd {β e b t u : Nat}
    (β_large : 2 ≤ β) (tail_terminal : β - 1 ≤ e)
    (source_factor : b + 1 = 3 ^ e * u) (source_unit : ¬3 ∣ u)
    (relation :
      (b - 1) * t + (b + 14) * 3 ^ β ≡ 3 * (b + 1) [MOD 9 * 3 ^ β]) :
    3 ^ β ∣ t := by
  have exponent_pos : 1 ≤ e := by omega
  obtain ⟨_, _, b_unit⟩ :=
    tagFactor_source_bounds exponent_pos source_unit source_factor
  have reduced := relation.of_dvd (show 3 ^ β ∣ 9 * 3 ^ β by exact dvd_mul_left _ _)
  have rhs_dvd : 3 ^ β ∣ 3 * (b + 1) := by
    rw [source_factor]
    have rhs_eq : 3 * (3 ^ e * u) = 3 ^ (e + 1) * u := by
      rw [pow_succ]
      ring
    rw [rhs_eq]
    exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow 3 (by omega)) u
  have sum_dvd : 3 ^ β ∣ (b - 1) * t + (b + 14) * 3 ^ β :=
    (reduced.dvd_iff (dvd_refl _)).mpr rhs_dvd
  have correction_dvd : 3 ^ β ∣ (b + 14) * 3 ^ β := dvd_mul_left _ _
  have product_dvd : 3 ^ β ∣ (b - 1) * t :=
    (Nat.dvd_add_iff_left correction_dvd).mpr sum_dvd
  have coprime : Nat.Coprime (b - 1) (3 ^ β) :=
    Nat.prime_three.coprime_pow_of_not_dvd b_unit
  exact coprime.symm.dvd_of_dvd_mul_left product_dvd

private theorem tagFactor_highZone_classify {β e b t u q : Nat}
    (β_large : 5 ≤ β) (tail_terminal : β - 1 ≤ e)
    (source_factor : b + 1 = 3 ^ e * u) (source_unit : ¬3 ∣ u)
    (source_kind : u = 1 ∨ u ≡ 5 [MOD 9])
    (target_factor : t = 3 ^ β * q)
    (target_kind : q = 1 ∨ q = 3 ∨ q = 9 ∨ q = 5 ∨ q = 6)
    (relation :
      (b - 1) * t + (b + 14) * 3 ^ β ≡ 3 * (b + 1) [MOD 9 * 3 ^ β]) :
    (e = β - 1 ∧ u = 1 ∧ q = 6) ∨ (e = β ∧ u = 1 ∧ q = 5) := by
  have u_pos : 1 ≤ u := by
    by_contra u_zero
    have u_eq : u = 0 := by omega
    subst u
    exact source_unit (dvd_zero 3)
  have high_relation := tagFactor_highZone (show 2 ≤ β by omega) tail_terminal
    u_pos source_factor target_factor relation
  have coefficient_mod := tagFactor_coefficient_mod_of_exponent_large
    (show 2 ≤ e by omega) u_pos
  have nine_dvd_power : 9 ∣ 3 ^ e := Nat.pow_dvd_pow 3 (show 2 ≤ e by omega)
  have correction_mod : 3 ^ e * u + 13 ≡ 13 [MOD 9] :=
    (Dvd.dvd.modEq_zero_nat (dvd_mul_of_dvd_left nine_dvd_power u)).add
      (Nat.ModEq.refl 13)
  have left_mod :
      (3 ^ e * u - 2) * q + (3 ^ e * u + 13) ≡ 7 * q + 13 [MOD 9] :=
    (coefficient_mod.mul (Nat.ModEq.refl q)).add correction_mod
  have numerical_relation : 7 * q + 13 ≡ 3 ^ (e + 1 - β) * u [MOD 9] :=
    left_mod.symm.trans high_relation
  rcases show e = β - 1 ∨ e = β ∨ β + 1 ≤ e by omega with
      penultimate | terminal | beyond
  · left
    refine ⟨penultimate, ?_⟩
    have exponent_zero : e + 1 - β = 0 := by omega
    rw [exponent_zero] at numerical_relation
    norm_num only [pow_zero, one_mul] at numerical_relation
    rcases source_kind with rfl | source_five
    · refine ⟨rfl, ?_⟩
      rcases target_kind with rfl | rfl | rfl | rfl | rfl
      · norm_num [Nat.ModEq] at numerical_relation
      · norm_num [Nat.ModEq] at numerical_relation
      · norm_num [Nat.ModEq] at numerical_relation
      · norm_num [Nat.ModEq] at numerical_relation
      · rfl
    · rcases target_kind with rfl | rfl | rfl | rfl | rfl
      · have impossible := numerical_relation.trans source_five
        norm_num [Nat.ModEq] at impossible
      · have impossible := numerical_relation.trans source_five
        norm_num [Nat.ModEq] at impossible
      · have impossible := numerical_relation.trans source_five
        norm_num [Nat.ModEq] at impossible
      · have impossible := numerical_relation.trans source_five
        norm_num [Nat.ModEq] at impossible
      · have impossible := numerical_relation.trans source_five
        norm_num [Nat.ModEq] at impossible
  · right
    refine ⟨terminal, ?_⟩
    have exponent_one : e + 1 - β = 1 := by omega
    rw [exponent_one] at numerical_relation
    norm_num only [pow_one] at numerical_relation
    rcases source_kind with rfl | source_five
    · refine ⟨rfl, ?_⟩
      rcases target_kind with rfl | rfl | rfl | rfl | rfl
      · norm_num [Nat.ModEq] at numerical_relation
      · norm_num [Nat.ModEq] at numerical_relation
      · norm_num [Nat.ModEq] at numerical_relation
      · rfl
      · norm_num [Nat.ModEq] at numerical_relation
    · have right_mod := source_five.mul_left 3
      rcases target_kind with rfl | rfl | rfl | rfl | rfl
      · have impossible := numerical_relation.trans right_mod
        norm_num [Nat.ModEq] at impossible
      · have impossible := numerical_relation.trans right_mod
        norm_num [Nat.ModEq] at impossible
      · have impossible := numerical_relation.trans right_mod
        norm_num [Nat.ModEq] at impossible
      · have impossible := numerical_relation.trans right_mod
        norm_num [Nat.ModEq] at impossible
      · have impossible := numerical_relation.trans right_mod
        norm_num [Nat.ModEq] at impossible
  · have exponent_large : 2 ≤ e + 1 - β := by omega
    have rhs_dvd : 9 ∣ 3 ^ (e + 1 - β) * u :=
      dvd_mul_of_dvd_left (Nat.pow_dvd_pow 3 exponent_large) u
    have rhs_zero := Nat.modEq_zero_iff_dvd.mpr rhs_dvd
    have impossible_base := numerical_relation.trans rhs_zero
    rcases target_kind with rfl | rfl | rfl | rfl | rfl <;>
      norm_num [Nat.ModEq] at impossible_base

private theorem tagPole_factor_relation {β : Nat} (β_pos : 1 ≤ β)
    {source target : List Bool} (source_code_lower : 2 ≤ swappedCode source)
    (pole : PoleCongruence β (tagCode β .b) source target) :
    (swappedCode source - 1) * (swappedCode target + 1) +
        (swappedCode source + 14) * 3 ^ β ≡
      3 * (swappedCode source + 1) [MOD 9 * 3 ^ β] := by
  have upper_code_int :
      (swappedCode (tagCode β .b) : ℤ) = 6 * (3 : ℤ) ^ β - 2 := by
    have upper_add_two :
        (swappedCode (tagCode β .b) : ℤ) + 2 = 6 * (3 : ℤ) ^ β := by
      exact_mod_cast swappedCode_tag_b_add_two β
    linarith
  have pole_expanded :
      ((6 * (3 : ℤ) ^ β - 2) - swappedCode source) * ((3 : ℤ) ^ β - 2) ≡
        (6 * (3 : ℤ) ^ β - 3 -
            ((6 * (3 : ℤ) ^ β - 2) - swappedCode source)) * swappedCode target
          [ZMOD 9 * (3 : ℤ) ^ β] := by
    simpa only [PoleCongruence, upper_code_int] using pole
  have bulk_dvd : 9 * (3 : ℤ) ^ β ∣ 6 * ((3 : ℤ) ^ β) ^ 2 := by
    obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le β_pos
    refine ⟨2 * (3 : ℤ) ^ extra, ?_⟩
    rw [pow_succ]
    ring
  have factor_relation_int :
      ((swappedCode source : ℤ) - 1) * (swappedCode target + 1) +
          ((swappedCode source : ℤ) + 14) * (3 : ℤ) ^ β ≡
        3 * ((swappedCode source : ℤ) + 1) [ZMOD 9 * (3 : ℤ) ^ β] := by
    rw [Int.modEq_iff_dvd] at pole_expanded ⊢
    have combined := Int.dvd_add (Int.dvd_neg.mpr pole_expanded)
      (dvd_neg.mpr bulk_dvd)
    convert combined using 1
    ring
  apply Int.natCast_modEq_iff.mp
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add,
    Nat.cast_one, Nat.cast_sub (show 1 ≤ swappedCode source by omega)] using
    factor_relation_int

private theorem tagSource_codeFactor {source : List Bool}
    (source_fringe : SourceFringe source) (source_last : source.getLast? = some false) :
    (∃ zeros,
        1 ≤ zeros ∧ source = List.replicate zeros false ∧
          swappedCode source + 1 = 3 ^ zeros) ∨
      ∃ front phases zeros,
        1 ≤ zeros ∧ front = spell fringeBlock phases ∧
          source = front ++ [true, true] ++ List.replicate zeros false ∧
            swappedCode source + 1 = 3 ^ zeros * (9 * swappedCode front + 5) := by
  rcases sourceFringe_lastTrue_normal source_fringe source_last with zero | pair
  · left
    obtain ⟨zeros, zeros_pos, source_eq⟩ := zero
    refine ⟨zeros, zeros_pos, source_eq, ?_⟩
    rw [source_eq]
    exact swappedCode_replicate_false zeros
  · right
    obtain ⟨front, phases, zeros, zeros_pos, front_eq, source_eq⟩ := pair
    refine ⟨front, phases, zeros, zeros_pos, front_eq, source_eq, ?_⟩
    rw [source_eq]
    exact swappedCode_pair_zero_tail front zeros

private theorem tagTarget_codeFactor {β : Nat} {target : List Bool}
    (target_fringe : TargetFringe (β + 2) target) :
    (∃ zeros,
        2 ≤ zeros ∧ zeros ≤ β + 2 ∧ target = List.replicate zeros false ∧
          swappedCode target + 1 = 3 ^ zeros) ∨
      (∃ front zeros,
        2 ≤ zeros ∧ front.length + 2 + zeros ≤ β + 2 ∧
          target = front ++ [true, true] ++ List.replicate zeros false ∧
            swappedCode target + 1 = 3 ^ zeros * (9 * swappedCode front + 5)) ∨
      (target = true :: List.replicate (β + 1) false ∧
        swappedCode target + 1 = 2 * 3 ^ (β + 1)) := by
  rcases target_fringe with ⟨length_bound, zero | pair | cut⟩
  · left
    obtain ⟨zeros, zeros_large, target_eq⟩ := zero
    refine ⟨zeros, zeros_large, ?_, target_eq, ?_⟩
    · rw [target_eq, List.length_replicate] at length_bound
      exact length_bound
    · rw [target_eq]
      exact swappedCode_replicate_false zeros
  · right
    left
    obtain ⟨front, zeros, zeros_large, target_eq⟩ := pair
    refine ⟨front, zeros, zeros_large, ?_, target_eq, ?_⟩
    · rw [target_eq] at length_bound
      simp only [List.length_append, List.length_cons, List.length_nil,
        List.length_replicate] at length_bound
      omega
    · rw [target_eq]
      exact swappedCode_pair_zero_tail front zeros
  · right
    right
    obtain ⟨_, target_eq⟩ := cut
    refine ⟨by simpa using target_eq, ?_⟩
    rw [target_eq]
    have code := swappedCode_true_false_run 1 ((β + 2) - 1)
    simp only [List.replicate_one, List.cons_append, List.nil_append] at code
    have sum_eq : 1 + ((β + 2) - 1) = β + 2 := by omega
    rw [sum_eq] at code
    have power_eq : 3 ^ (β + 2) = 3 * 3 ^ (β + 1) := by
      rw [show β + 2 = (β + 1) + 1 by omega, pow_succ]
      ring
    have tail_eq : (β + 2) - 1 = β + 1 := by omega
    rw [tail_eq] at code ⊢
    nlinarith

private theorem fringeUnit_modEq_five (front : List Bool) :
    9 * swappedCode front + 5 ≡ 5 [MOD 9] := Nat.ModEq.modulus_mul_add

private theorem three_not_dvd_fringeUnit (front : List Bool) :
    ¬3 ∣ 9 * swappedCode front + 5 := by
  rintro ⟨quotient, quotient_eq⟩
  omega

private theorem tagFactor_classifyTarget {β b t e u : Nat} {target : List Bool}
    (β_large : 5 ≤ β) (e_pos : 1 ≤ e)
    (source_factor : b + 1 = 3 ^ e * u) (source_unit : ¬3 ∣ u)
    (source_kind : u = 1 ∨ u ≡ 5 [MOD 9])
    (target_factors :
      (∃ zeros,
          2 ≤ zeros ∧ zeros ≤ β + 2 ∧ target = List.replicate zeros false ∧
            t = 3 ^ zeros) ∨
        (∃ front zeros,
          2 ≤ zeros ∧ front.length + 2 + zeros ≤ β + 2 ∧
            target = front ++ [true, true] ++ List.replicate zeros false ∧
              t = 3 ^ zeros * (9 * swappedCode front + 5)) ∨
        (target = true :: List.replicate (β + 1) false ∧
          t = 2 * 3 ^ (β + 1)))
    (relation : (b - 1) * t + (b + 14) * 3 ^ β ≡
      3 * (b + 1) [MOD 9 * 3 ^ β]) :
    (e = β - 1 ∧ u = 1 ∧ target = true :: List.replicate (β + 1) false) ∨
      (e = β ∧ u = 1 ∧ target = [true, true] ++ List.replicate β false) := by
  by_cases low_zone : e + 3 ≤ β
  · rcases target_factors with zero | pair | cut
    · obtain ⟨zeros, _, _, _, target_factor⟩ := zero
      exact False.elim <| tagFactor_lowZone_false e_pos low_zone source_factor source_unit
        source_kind (by simpa using target_factor) (by norm_num)
        (Or.inl rfl) relation
    · obtain ⟨front, zeros, _, _, _, target_factor⟩ := pair
      exact False.elim <| tagFactor_lowZone_false e_pos low_zone source_factor source_unit
        source_kind target_factor (three_not_dvd_fringeUnit front)
        (Or.inr <| Or.inl <| fringeUnit_modEq_five front) relation
    · obtain ⟨_, target_factor⟩ := cut
      have normalized_target : t = 3 ^ (β + 1) * 2 := by
        rw [target_factor]
        ring
      exact False.elim <| tagFactor_lowZone_false e_pos low_zone source_factor source_unit
        source_kind normalized_target (by norm_num)
        (Or.inr <| Or.inr ⟨rfl, rfl⟩) relation
  · by_cases mid_zone : e = β - 2
    · rcases target_factors with zero | pair | cut
      · obtain ⟨zeros, _, _, _, target_factor⟩ := zero
        rw [mid_zone] at source_factor
        exact False.elim <| tagFactor_midZone_false (show 5 ≤ β by omega)
          source_factor source_unit source_kind (by simpa using target_factor) (by norm_num)
          (Or.inl rfl) relation
      · obtain ⟨front, zeros, _, _, _, target_factor⟩ := pair
        rw [mid_zone] at source_factor
        exact False.elim <| tagFactor_midZone_false (show 5 ≤ β by omega)
          source_factor source_unit source_kind target_factor
          (three_not_dvd_fringeUnit front)
          (Or.inr <| Or.inl <| fringeUnit_modEq_five front) relation
      · obtain ⟨_, target_factor⟩ := cut
        rw [mid_zone] at source_factor
        have normalized_target : t = 3 ^ (β + 1) * 2 := by
          rw [target_factor]
          ring
        exact False.elim <| tagFactor_midZone_false (show 5 ≤ β by omega)
          source_factor source_unit source_kind normalized_target (by norm_num)
          (Or.inr <| Or.inr ⟨rfl, rfl⟩) relation
    · have high_zone : β - 1 ≤ e := by omega
      rcases target_factors with zero | pair | cut
      · obtain ⟨zeros, _, zeros_le, _, target_factor⟩ := zero
        have target_dvd := tagFactor_highZone_target_dvd (show 2 ≤ β by omega)
          high_zone source_factor source_unit relation
        rw [target_factor] at target_dvd
        have beta_le_zeros : β ≤ zeros := by
          rw [Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)] at target_dvd
          exact target_dvd
        rcases show zeros = β ∨ zeros = β + 1 ∨ zeros = β + 2 by omega with
            zeros_eq | zeros_eq | zeros_eq
        · have normalized_target : t = 3 ^ β * 1 := by simpa [zeros_eq] using target_factor
          have shapes := tagFactor_highZone_classify (show 5 ≤ β by omega) high_zone
            source_factor source_unit source_kind normalized_target (Or.inl rfl) relation
          rcases shapes with ⟨_, _, quotient_eq⟩ | ⟨_, _, quotient_eq⟩ <;> omega
        · have normalized_target : t = 3 ^ β * 3 := by
            rw [target_factor, zeros_eq, pow_succ]
          have shapes := tagFactor_highZone_classify (show 5 ≤ β by omega) high_zone
            source_factor source_unit source_kind normalized_target
            (Or.inr <| Or.inl rfl) relation
          rcases shapes with ⟨_, _, quotient_eq⟩ | ⟨_, _, quotient_eq⟩ <;> omega
        · have normalized_target : t = 3 ^ β * 9 := by
            rw [target_factor, zeros_eq, show β + 2 = β + 2 by rfl, pow_add]
            norm_num
          have shapes := tagFactor_highZone_classify (show 5 ≤ β by omega) high_zone
            source_factor source_unit source_kind normalized_target
            (Or.inr <| Or.inr <| Or.inl rfl) relation
          rcases shapes with ⟨_, _, quotient_eq⟩ | ⟨_, _, quotient_eq⟩ <;> omega
      · obtain ⟨front, zeros, _, length_bound, target_eq, target_factor⟩ := pair
        have target_dvd := tagFactor_highZone_target_dvd (show 2 ≤ β by omega)
          high_zone source_factor source_unit relation
        rw [target_factor] at target_dvd
        have unit_coprime : Nat.Coprime (9 * swappedCode front + 5) (3 ^ β) :=
          Nat.prime_three.coprime_pow_of_not_dvd (three_not_dvd_fringeUnit front)
        have power_dvd : 3 ^ β ∣ 3 ^ zeros :=
          unit_coprime.symm.dvd_of_dvd_mul_right target_dvd
        have beta_le_zeros : β ≤ zeros := by
          rw [Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)] at power_dvd
          exact power_dvd
        have zeros_eq : zeros = β := by omega
        have front_empty : front = [] := List.length_eq_zero_iff.mp (by omega)
        subst front
        subst zeros
        have normalized_target : t = 3 ^ β * 5 := by simpa using target_factor
        have shapes := tagFactor_highZone_classify (show 5 ≤ β by omega) high_zone
          source_factor source_unit source_kind normalized_target
          (Or.inr <| Or.inr <| Or.inr <| Or.inl rfl) relation
        rcases shapes with ⟨_, _, quotient_eq⟩ | ⟨exponent_eq, unit_eq, _⟩
        · omega
        · right
          exact ⟨exponent_eq, unit_eq, by simpa using target_eq⟩
      · obtain ⟨target_eq, target_factor⟩ := cut
        have normalized_target : t = 3 ^ β * 6 := by
          rw [target_factor, pow_succ]
          ring
        have shapes := tagFactor_highZone_classify (show 5 ≤ β by omega) high_zone
          source_factor source_unit source_kind normalized_target
          (Or.inr <| Or.inr <| Or.inr <| Or.inr rfl) relation
        rcases shapes with ⟨exponent_eq, unit_eq, _⟩ | ⟨_, _, quotient_eq⟩
        · left
          exact ⟨exponent_eq, unit_eq, target_eq⟩
        · omega

/-- A tag upper fringe satisfying the pole congruence is one of the two terminal pairs. -/
theorem tagPole_classify {β : Nat} (β_large : 5 ≤ β)
    {source target : List Bool} (source_fringe : SourceFringe source)
    (source_last : source.getLast? = some false)
    (target_fringe : TargetFringe (β + 2) target)
    (pole : PoleCongruence β (tagCode β .b) source target) :
    (source = List.replicate (β - 1) false ∧
        target = true :: List.replicate (β + 1) false) ∨
      (source = List.replicate β false ∧
        target = [true, true] ++ List.replicate β false) := by
  have source_code_lower : 2 ≤ swappedCode source := by
    have source_mod := (swappedCode_modEq_two_iff_getLast?_false source).mpr source_last
    rw [Nat.ModEq] at source_mod
    omega
  have relation := tagPole_factor_relation (show 1 ≤ β by omega)
    source_code_lower pole
  have target_factors := tagTarget_codeFactor target_fringe
  rcases tagSource_codeFactor source_fringe source_last with zero | pair
  · obtain ⟨zeros, zeros_pos, source_eq, source_factor⟩ := zero
    have normalized_source : swappedCode source + 1 = 3 ^ zeros * 1 := by
      simpa using source_factor
    have shapes := tagFactor_classifyTarget β_large zeros_pos normalized_source (by norm_num)
      (Or.inl rfl) target_factors relation
    rcases shapes with ⟨exponent_eq, _, target_eq⟩ | ⟨exponent_eq, _, target_eq⟩
    · left
      rw [exponent_eq] at source_eq
      exact ⟨source_eq, target_eq⟩
    · right
      rw [exponent_eq] at source_eq
      exact ⟨source_eq, target_eq⟩
  · obtain ⟨front, _, zeros, zeros_pos, _, _, source_factor⟩ := pair
    let unit := 9 * swappedCode front + 5
    have unit_factor : swappedCode source + 1 = 3 ^ zeros * unit := by
      exact source_factor
    have unit_not_one : unit ≠ 1 := by simp [unit]
    have shapes := tagFactor_classifyTarget β_large zeros_pos unit_factor
      (three_not_dvd_fringeUnit front) (Or.inr <| fringeUnit_modEq_five front)
      target_factors relation
    rcases shapes with ⟨_, unit_eq, _⟩ | ⟨_, unit_eq, _⟩
    · exact False.elim (unit_not_one unit_eq)
    · exact False.elim (unit_not_one unit_eq)

end MatrixMortality.SwappedSetterFringe
