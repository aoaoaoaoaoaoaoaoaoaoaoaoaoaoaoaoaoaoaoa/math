import MatrixMortality.DecimalSetterFiveDepth
import Mathlib.NumberTheory.PowModTotient
import Mathlib.RingTheory.Radical.Basic
import Mathlib.Tactic

/-!
# Decimal setter denominator ancestry

The recursive carrier denominator retains the preceding numerator through `D=EN₋`. Reducing
the recurrence by factors of the primitive gap `q=2·10^β−7` shows exactly how prime support
enters and persists. Every factor coprime to the current numerator also imposes two successive
code congruences on a transition into a singleton. This factorwise law remains informative when
`q` is composite and the numerator is not coprime to the full gap. Exact upper-suffix depth
excludes full-gap all-erasure entry blocks whose first or second role is `D_b`.
-/

namespace MatrixMortality.DecimalSetterAncestry

open MatrixMortality.DecimalSetterArithmetic
open MatrixMortality.DecimalSetterCarry
open MatrixMortality.DecimalSetterChamber
open MatrixMortality.DecimalSetterDepth

/-- The primitive factor left after removing the fixed factor nine from the decimal gap. -/
def gapFactor (β : Nat) : ℤ :=
  2 * 10 ^ β - 7

/-- The primitive gap is positive at every physical deletion width. -/
theorem gapFactor_pos {β : Nat} (β_positive : 0 < β) : 0 < gapFactor β := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt β_positive)
  have power_pos : (0 : ℤ) < 10 ^ k := pow_pos (by norm_num) k
  simp only [gapFactor, pow_succ]
  nlinarith

/-- The full primitive gap cannot already divide the distinguished two-`c` raw head. Its code
lies strictly between the consecutive multiples `27q` and `28q`. -/
theorem gapFactor_not_dvd_twoCHead {β : Nat} (β_large : 3 ≤ β) (fringe : List Bool)
    (fringe_length : fringe.length = β) :
    ¬gapFactor β ∣ (code (true :: true :: fringe) : ℤ) := by
  let ρ : ℤ := 10 ^ β
  let H : ℤ := code (true :: true :: fringe)
  have rho_bound_nat : 1000 ≤ 10 ^ β := by
    have power_bound : 10 ^ 3 ≤ 10 ^ β :=
      Nat.pow_le_pow_right (by norm_num) β_large
    norm_num at power_bound ⊢
    exact power_bound
  have rho_bound : (1000 : ℤ) ≤ ρ := by
    dsimp [ρ]
    exact_mod_cast rho_bound_nat
  have head_lower_nat : 55 * 10 ^ β ≤ code (true :: true :: fringe) := by
    simp only [code_cons, digit_true, List.length_cons, fringe_length, pow_succ]
    omega
  have head_lower : 55 * ρ ≤ H := by
    dsimp [ρ, H]
    exact_mod_cast head_lower_nat
  have head_upper_nat := leadingTrueTrue_code_bound fringe
  rw [fringe_length] at head_upper_nat
  have head_upper : 9 * H + 7 ≤ 502 * ρ := by
    dsimp [ρ, H]
    exact_mod_cast head_upper_nat
  intro head_dvd
  obtain ⟨k, H_eq⟩ := head_dvd
  have k_lower : (27 : ℤ) < k := by
    dsimp [H] at H_eq head_lower
    rw [H_eq] at head_lower
    simp only [gapFactor] at head_lower
    dsimp [ρ] at rho_bound head_lower
    nlinarith
  have k_upper : k < (28 : ℤ) := by
    dsimp [H] at H_eq head_upper
    rw [H_eq] at head_upper
    simp only [gapFactor] at head_upper
    dsimp [ρ] at rho_bound head_upper
    nlinarith
  omega

private theorem gapFactor_coprime_seven (β : Nat) :
    IsCoprime (gapFactor β) (7 : ℤ) := by
  have ten_coprime : IsCoprime ((10 : ℤ) ^ β) 7 :=
    (by norm_num : IsCoprime (10 : ℤ) 7).pow_left
  have twice_coprime : IsCoprime (2 * (10 : ℤ) ^ β) 7 :=
    (by norm_num : IsCoprime (2 : ℤ) 7).mul_left ten_coprime
  have shifted := twice_coprime.add_mul_left_left (-1)
  rw [show gapFactor β = 2 * (10 : ℤ) ^ β + 7 * (-1) by simp [gapFactor]; ring]
  exact shifted

private theorem gapFactor_coprime_two (β : Nat) :
    IsCoprime (gapFactor β) (2 : ℤ) := by
  have shifted := (isCoprime_one_left : IsCoprime (1 : ℤ) 2).add_mul_left_left
    ((10 : ℤ) ^ β - 4)
  rw [show gapFactor β = 1 + 2 * ((10 : ℤ) ^ β - 4) by simp [gapFactor]; ring]
  exact shifted

private theorem gapFactor_coprime_five {β : Nat} (β_positive : 0 < β) :
    IsCoprime (gapFactor β) (5 : ℤ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt β_positive)
  have shifted := (by norm_num : IsCoprime (3 : ℤ) 5).add_mul_left_left
    (4 * (10 : ℤ) ^ k - 2)
  rw [show gapFactor (k + 1) = 3 + 5 * (4 * (10 : ℤ) ^ k - 2) by
    simp [gapFactor, pow_succ]; ring]
  exact shifted

/-- The primitive gap is coprime to the decimal radix. -/
theorem gapFactor_coprime_ten {β : Nat} (β_positive : 0 < β) :
    IsCoprime (gapFactor β) (10 : ℤ) := by
  simpa using (gapFactor_coprime_two β).mul_right
    (gapFactor_coprime_five β_positive)

private theorem gapFactor_coprime_1750 {β : Nat} (β_positive : 0 < β) :
    IsCoprime (gapFactor β) (1750 : ℤ) := by
  have two := gapFactor_coprime_two β
  have five := (gapFactor_coprime_five β_positive).pow_right (n := 3)
  have seven := gapFactor_coprime_seven β
  simpa using (two.mul_right five).mul_right seven

private theorem gapFactor_coprime_decimalLift {β : Nat} (β_positive : 0 < β) :
    IsCoprime (gapFactor β) (decimalLift (10 ^ β)) := by
  have shifted := (gapFactor_coprime_1750 β_positive).add_mul_left_right (251 : ℤ)
  rw [show decimalLift (10 ^ β) = 1750 + gapFactor β * 251 by
    simp [gapFactor, decimalLift]; ring]
  exact shifted

private theorem nine_dvd_decimalLift_ten_pow (β : Nat) :
    (9 : ℤ) ∣ decimalLift (10 ^ β) := by
  have rho_mod : ((10 : ℤ) ^ β) ≡ 1 [ZMOD 9] := by
    simpa using (by norm_num : (10 : ℤ) ≡ 1 [ZMOD 9]).pow β
  have lift_mod : decimalLift (10 ^ β) ≡ 0 [ZMOD 9] := by
    simp only [decimalLift]
    calc
      502 * (10 : ℤ) ^ β - 7 ≡ 502 * 1 - 7 [ZMOD 9] :=
        (Int.ModEq.refl 502).mul rho_mod |>.sub (Int.ModEq.refl 7)
      _ ≡ 0 [ZMOD 9] := by norm_num
  exact Int.modEq_zero_iff_dvd.mp lift_mod

/-- Every divisor of the primitive decimal gap is coprime to the factor nine removed from the
full gap. -/
theorem gapFactorDivisor_coprime_nine
    {β : Nat} {r : ℤ}
    (β_positive : 0 < β)
    (r_dvd_q : r ∣ gapFactor β) :
    IsCoprime r (9 : ℤ) := by
  have qG_coprime : IsCoprime (gapFactor β) (decimalLift (10 ^ β)) :=
    gapFactor_coprime_decimalLift β_positive
  have nine_dvd_G : (9 : ℤ) ∣ decimalLift (10 ^ β) :=
    nine_dvd_decimalLift_ten_pow β
  have q9_coprime : IsCoprime (gapFactor β) (9 : ℤ) :=
    IsCoprime.of_isCoprime_of_dvd_right qG_coprime nine_dvd_G
  exact IsCoprime.of_isCoprime_of_dvd_left q9_coprime r_dvd_q

/-- The exact mixed-prime identity for a unit two-`c` raw head reduces every gap-factor test to
its final run length. This consumes the raw-head identity supplied by the suffix grammar. -/
theorem rawHead_factor_iff
    {β s : Nat} {r H : ℤ}
    (β_positive : 0 < β)
    (r_dvd_q : r ∣ gapFactor β)
    (head_eq : 9 * H = 5 * 10 ^ (β + 2) + 2 * 10 ^ s - 7) :
    r ∣ H ↔ r ∣ 2 * 10 ^ s + 1743 := by
  let q := gapFactor β
  have r9_coprime : IsCoprime r (9 : ℤ) :=
    gapFactorDivisor_coprime_nine β_positive r_dvd_q
  have decomposition : 9 * H = 250 * q + (2 * 10 ^ s + 1743) := by
    calc
      9 * H = 5 * 10 ^ (β + 2) + 2 * 10 ^ s - 7 := head_eq
      _ = 250 * q + (2 * 10 ^ s + 1743) := by
        simp [q, gapFactor, pow_add]
        ring
  have q_zero : q ≡ 0 [ZMOD r] := by
    simpa [q] using r_dvd_q.modEq_zero_int
  have head_mod : 9 * H ≡ 2 * 10 ^ s + 1743 [ZMOD r] := by
    calc
      9 * H = 250 * q + (2 * 10 ^ s + 1743) := decomposition
      _ ≡ 250 * 0 + (2 * 10 ^ s + 1743) [ZMOD r] :=
        ((Int.ModEq.refl 250).mul q_zero).add (Int.ModEq.refl _)
      _ = 2 * 10 ^ s + 1743 := by ring
  constructor
  · intro r_dvd_H
    have left_zero : 9 * H ≡ 0 [ZMOD r] :=
      (r_dvd_H.mul_left 9).modEq_zero_int
    exact Int.modEq_zero_iff_dvd.mp (head_mod.symm.trans left_zero)
  · intro r_dvd_boundary
    have left_dvd : r ∣ 9 * H :=
      Int.modEq_zero_iff_dvd.mp (head_mod.trans r_dvd_boundary.modEq_zero_int)
    exact r9_coprime.dvd_of_dvd_mul_left left_dvd

/-- Divisibility by any factor of the primitive gap propagates through a recursive multi-shell
step exactly by multiplication with the current lower code. Thus prime contamination is
absorbing, and a new prime can enter only through an emitted lower word. -/
theorem carrierFactor_dvd_next_iff
    {β depth : Nat} {r μ N D Nprev P V T Nnext : ℤ}
    (β_positive : 0 < β)
    (r_dvd_q : r ∣ gapFactor β)
    (D_eq : D = decimalGap (10 ^ β) * Nprev)
    (T_eq : T = decimalGap (10 ^ β) * P + decimalLift (10 ^ β) * V)
    (factor :
      peeledNumerator N D μ (decimalLift (10 ^ β)) T V = 10 ^ depth * Nnext) :
    r ∣ Nnext ↔ r ∣ N * V := by
  let G := decimalLift (10 ^ β)
  have qG_coprime : IsCoprime (gapFactor β) G := by
    simpa [G] using gapFactor_coprime_decimalLift β_positive
  have rG_coprime : IsCoprime r G :=
    IsCoprime.of_isCoprime_of_dvd_left qG_coprime r_dvd_q
  have q10_coprime : IsCoprime (gapFactor β) (10 : ℤ) := by
    exact gapFactor_coprime_ten β_positive
  have r10_coprime : IsCoprime r (10 : ℤ) :=
    IsCoprime.of_isCoprime_of_dvd_left q10_coprime r_dvd_q
  have r10pow_coprime : IsCoprime r ((10 : ℤ) ^ depth) :=
    r10_coprime.pow_right
  have q_dvd_E : gapFactor β ∣ decimalGap (10 ^ β) := by
    refine ⟨9, ?_⟩
    simp [decimalGap, gapFactor]
    ring
  have r_dvd_E : r ∣ decimalGap (10 ^ β) := r_dvd_q.trans q_dvd_E
  have E_zero : decimalGap (10 ^ β) ≡ 0 [ZMOD r] := r_dvd_E.modEq_zero_int
  have D_zero : D ≡ 0 [ZMOD r] := by
    rw [D_eq]
    simpa using E_zero.mul (Int.ModEq.refl Nprev)
  have T_mod : T ≡ G * V [ZMOD r] := by
    rw [T_eq]
    simpa [G] using
      (E_zero.mul (Int.ModEq.refl P)).add
        ((Int.ModEq.refl G).mul (Int.ModEq.refl V))
  have residual_mod :
      peeledNumerator N D μ G T V ≡ N * G * V [ZMOD r] := by
    unfold peeledNumerator
    have left_mod := (Int.ModEq.refl N).mul T_mod
    have right_mod : 10 * μ * G * V * D ≡ 0 [ZMOD r] := by
      simpa using
        (((((Int.ModEq.refl (10 : ℤ)).mul (Int.ModEq.refl μ)).mul
          (Int.ModEq.refl G)).mul (Int.ModEq.refl V)).mul D_zero)
    simpa [mul_assoc] using left_mod.sub right_mod
  have step_mod : 10 ^ depth * Nnext ≡ N * G * V [ZMOD r] := by
    rw [← factor]
    exact residual_mod
  constructor
  · intro next_dvd
    have left_zero : 10 ^ depth * Nnext ≡ 0 [ZMOD r] :=
      (next_dvd.mul_left (10 ^ depth)).modEq_zero_int
    have product_dvd : r ∣ N * G * V :=
      Int.modEq_zero_iff_dvd.mp (step_mod.symm.trans left_zero)
    apply rG_coprime.dvd_of_dvd_mul_right
    simpa [mul_assoc, mul_comm, mul_left_comm] using product_dvd
  · intro product_dvd
    have right_dvd : r ∣ N * G * V := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using product_dvd.mul_right G
    have left_dvd : r ∣ 10 ^ depth * Nnext :=
      Int.modEq_zero_iff_dvd.mp (step_mod.trans right_dvd.modEq_zero_int)
    exact r10pow_coprime.dvd_of_dvd_mul_left left_dvd

/-- Prime support has no hidden source: a gap prime divides the next carrier numerator exactly
when it already divides the current numerator or divides the current lower code. -/
theorem primeFactor_dvd_next_iff
    {β depth : Nat} {p μ N D Nprev P V T Nnext : ℤ}
    (β_positive : 0 < β)
    (p_prime : Prime p)
    (p_dvd_q : p ∣ gapFactor β)
    (D_eq : D = decimalGap (10 ^ β) * Nprev)
    (T_eq : T = decimalGap (10 ^ β) * P + decimalLift (10 ^ β) * V)
    (factor :
      peeledNumerator N D μ (decimalLift (10 ^ β)) T V = 10 ^ depth * Nnext) :
    p ∣ Nnext ↔ p ∣ N ∨ p ∣ V :=
  (carrierFactor_dvd_next_iff β_positive p_dvd_q D_eq T_eq factor).trans p_prime.dvd_mul

/-- One exact recursive carrier transition, retaining precisely the denominator ancestry and
trace equations needed by the gap-support law. -/
def GapCarrierStep (β : Nat) (source lower target : ℤ) : Prop :=
  ∃ depth : Nat, ∃ μ D previous upper trace : ℤ,
    D = decimalGap (10 ^ β) * previous ∧
      trace = decimalGap (10 ^ β) * upper + decimalLift (10 ^ β) * lower ∧
        peeledNumerator source D μ (decimalLift (10 ^ β)) trace lower =
          10 ^ depth * target

/-- A finite exact carrier history indexed by its emitted lower codes. -/
inductive GapCarrierHistory (β : Nat) : ℤ → List ℤ → ℤ → Prop
  | nil (carrier : ℤ) : GapCarrierHistory β carrier [] carrier
  | cons {source lower next final : ℤ} {tail : List ℤ}
      (step : GapCarrierStep β source lower next)
      (history : GapCarrierHistory β next tail final) :
      GapCarrierHistory β source (lower :: tail) final

/-- A certified carrier step has the same exact prime-support transition as its expanded
arithmetic witness. -/
theorem GapCarrierStep.prime_dvd_target_iff
    {β : Nat} {p source lower target : ℤ}
    (step : GapCarrierStep β source lower target)
    (β_positive : 0 < β)
    (p_prime : Prime p)
    (p_dvd_q : p ∣ gapFactor β) :
    p ∣ target ↔ p ∣ source ∨ p ∣ lower := by
  obtain ⟨depth, μ, D, previous, upper, trace, D_eq, trace_eq, factor⟩ := step
  exact primeFactor_dvd_next_iff β_positive p_prime p_dvd_q D_eq trace_eq factor

/-- Across an arbitrary exact carrier history, a gap prime divides the final numerator exactly
when it divided the initial numerator or one of the emitted lower codes. -/
theorem GapCarrierHistory.prime_dvd_final_iff
    {β : Nat} {p source final : ℤ} {lowerCodes : List ℤ}
    (history : GapCarrierHistory β source lowerCodes final)
    (β_positive : 0 < β)
    (p_prime : Prime p)
    (p_dvd_q : p ∣ gapFactor β) :
    p ∣ final ↔ p ∣ source ∨ ∃ lower ∈ lowerCodes, p ∣ lower := by
  induction history with
  | nil => simp
  | @cons source lower next final tail step history induction =>
      rw [induction, step.prime_dvd_target_iff β_positive p_prime p_dvd_q]
      simp only [List.mem_cons]
      constructor
      · rintro ((source_dvd | lower_dvd) | ⟨candidate, candidate_mem, candidate_dvd⟩)
        · exact Or.inl source_dvd
        · exact Or.inr ⟨lower, Or.inl rfl, lower_dvd⟩
        · exact Or.inr ⟨candidate, Or.inr candidate_mem, candidate_dvd⟩
      · rintro (source_dvd | ⟨candidate, (rfl | candidate_mem), candidate_dvd⟩)
        · exact Or.inl (Or.inl source_dvd)
        · exact Or.inl (Or.inr candidate_dvd)
        · exact Or.inr ⟨candidate, candidate_mem, candidate_dvd⟩

/-- If a gap prime was absent initially, it enters an exact carrier history if and only if it
divides one of that history's emitted lower codes. -/
theorem GapCarrierHistory.absent_prime_dvd_final_iff_lowerCode
    {β : Nat} {p source final : ℤ} {lowerCodes : List ℤ}
    (history : GapCarrierHistory β source lowerCodes final)
    (β_positive : 0 < β)
    (p_prime : Prime p)
    (p_dvd_q : p ∣ gapFactor β)
    (p_absent : ¬p ∣ source) :
    p ∣ final ↔ ∃ lower ∈ lowerCodes, p ∣ lower := by
  rw [history.prime_dvd_final_iff β_positive p_prime p_dvd_q]
  simp only [p_absent, false_or]

/-- Saturation of the gap support means divisibility by the squarefree radical of the primitive
gap, rather than by the generally non-squarefree gap itself. -/
def gapSupportSaturated (β : Nat) (carrier : ℤ) : Prop :=
  UniqueFactorizationMonoid.radical (gapFactor β) ∣ carrier

/-- Radical saturation is equivalent to divisibility by every prime factor of the primitive
gap. -/
theorem gapSupportSaturated_iff
    {β : Nat} (β_positive : 0 < β) (carrier : ℤ) :
    gapSupportSaturated β carrier ↔
      ∀ p : ℤ, Prime p → p ∣ gapFactor β → p ∣ carrier := by
  constructor
  · intro saturated p p_prime p_dvd_q
    have p_dvd_radical : p ∣ UniqueFactorizationMonoid.radical (gapFactor β) :=
      (UniqueFactorizationMonoid.dvd_radical_iff_of_irreducible
        p_prime.irreducible (gapFactor_pos β_positive).ne').mpr p_dvd_q
    exact p_dvd_radical.trans saturated
  · intro support
    by_cases carrier_zero : carrier = 0
    · rw [carrier_zero]
      exact dvd_zero _
    · rw [gapSupportSaturated,
        UniqueFactorizationMonoid.radical_dvd_iff_primeFactors_subset carrier_zero]
      intro p p_mem_q
      rw [UniqueFactorizationMonoid.mem_primeFactors] at p_mem_q ⊢
      rw [UniqueFactorizationMonoid.mem_normalizedFactors_iff'
        (gapFactor_pos β_positive).ne'] at p_mem_q
      rw [UniqueFactorizationMonoid.mem_normalizedFactors_iff' carrier_zero]
      exact ⟨p_mem_q.1, p_mem_q.2.1,
        support p p_mem_q.1.prime p_mem_q.2.2⟩

/-- A finite carrier history ends with saturated gap support exactly when every gap prime was
present initially or entered through one of its emitted lower codes. -/
theorem GapCarrierHistory.gapSupportSaturated_iff
    {β : Nat} {source final : ℤ} {lowerCodes : List ℤ}
    (history : GapCarrierHistory β source lowerCodes final)
    (β_positive : 0 < β) :
    gapSupportSaturated β final ↔
      ∀ p : ℤ, Prime p → p ∣ gapFactor β →
        p ∣ source ∨ ∃ lower ∈ lowerCodes, p ∣ lower := by
  rw [MatrixMortality.DecimalSetterAncestry.gapSupportSaturated_iff β_positive]
  constructor
  · intro final_support p p_prime p_dvd_q
    exact (history.prime_dvd_final_iff β_positive p_prime p_dvd_q).mp
      (final_support p p_prime p_dvd_q)
  · intro installed p p_prime p_dvd_q
    exact (history.prime_dvd_final_iff β_positive p_prime p_dvd_q).mpr
      (installed p p_prime p_dvd_q)

/-- Radical saturation at the end of a history requires every initially absent gap prime to
have entered through an emitted lower code. -/
theorem GapCarrierHistory.lowerCode_of_gapSupportSaturated
    {β : Nat} {p source final : ℤ} {lowerCodes : List ℤ}
    (history : GapCarrierHistory β source lowerCodes final)
    (β_positive : 0 < β)
    (saturated : gapSupportSaturated β final)
    (p_prime : Prime p)
    (p_dvd_q : p ∣ gapFactor β)
    (p_absent : ¬p ∣ source) :
    ∃ lower ∈ lowerCodes, p ∣ lower := by
  have p_dvd_radical : p ∣ UniqueFactorizationMonoid.radical (gapFactor β) :=
    (UniqueFactorizationMonoid.dvd_radical_iff_of_irreducible
      p_prime.irreducible (gapFactor_pos β_positive).ne').mpr p_dvd_q
  have p_dvd_final : p ∣ final := p_dvd_radical.trans saturated
  exact (history.absent_prime_dvd_final_iff_lowerCode
    β_positive p_prime p_dvd_q p_absent).mp p_dvd_final

/-- A physical block of erasure tiles whose lower side is a pure zero word. -/
def allEraseBlock (width : Nat) : List NearyTile :=
  List.replicate width (.erase .c)

/-- Decimal lower code emitted by a physical all-erasure block. -/
def allEraseLowerCode (β : Nat) (body : List TagLetter) (width : Nat) : ℤ :=
  code (spell (nearyLower β body) (allEraseBlock width))

@[simp] theorem spell_allEraseBlock (β : Nat) (body : List TagLetter) (width : Nat) :
    spell (nearyLower β body) (allEraseBlock width) = List.replicate width false := by
  induction width with
  | zero => rfl
  | succ width induction =>
      change false :: spell (nearyLower β body) (List.replicate width (.erase .c)) =
        false :: List.replicate width false
      exact congrArg (false :: ·) (by simpa only [allEraseBlock] using induction)

/-- The Euler-totient saturation block is nonempty at every physical width. -/
theorem allEraseSaturationWidth_pos {β : Nat} (β_positive : 0 < β) :
    0 < Nat.totient (gapFactor β).natAbs := by
  rw [Nat.totient_pos, Int.natAbs_pos]
  exact (gapFactor_pos β_positive).ne'

/-- At Euler's totient width, the physical all-erasure lower code contains the entire primitive
gap. Thus no prime factor of the gap is permanently absent from the emitted lower-code
language. -/
theorem gapFactor_dvd_allEraseLowerCode
    {β : Nat} (β_positive : 0 < β) (body : List TagLetter) :
    gapFactor β ∣
      allEraseLowerCode β body (Nat.totient (gapFactor β).natAbs) := by
  let q := gapFactor β
  let width := Nat.totient q.natAbs
  have q_pos : 0 < q := by simpa only [q] using gapFactor_pos β_positive
  have ten_coprime_q : Nat.Coprime 10 q.natAbs := by
    have int_coprime : IsCoprime q (10 : ℤ) := by
      simpa only [q] using gapFactor_coprime_ten β_positive
    have abs_coprime : Nat.Coprime q.natAbs (10 : ℤ).natAbs :=
      Int.isCoprime_iff_nat_coprime.mp int_coprime
    simpa using abs_coprime.symm
  have euler : 10 ^ width ≡ 1 [MOD q.natAbs] := by
    simpa only [width] using Nat.ModEq.pow_totient ten_coprime_q
  have q_dvd_one_sub : q ∣ (1 : ℤ) - (10 : ℤ) ^ width := by
    have euler_dvd := euler.dvd
    norm_num at euler_dvd
    exact euler_dvd
  have q_dvd_pow_sub_one : q ∣ (10 : ℤ) ^ width - 1 := by
    simpa only [neg_sub] using dvd_neg.mpr q_dvd_one_sub
  have code_identity := replicateFalse_code_identity width
  have code_identity_int :
      9 * (code (List.replicate width false) : ℤ) =
        7 * ((10 : ℤ) ^ width - 1) := by
    have cast_identity := congrArg (fun value : Nat => (value : ℤ)) code_identity
    norm_num at cast_identity
    nlinarith
  have q_dvd_scaled_code : q ∣ 9 * (code (List.replicate width false) : ℤ) := by
    rw [code_identity_int]
    exact q_dvd_pow_sub_one.mul_left 7
  have q_coprime_nine : IsCoprime q (9 : ℤ) := by
    apply gapFactorDivisor_coprime_nine β_positive
    exact dvd_rfl
  have q_dvd_code : q ∣ (code (List.replicate width false) : ℤ) :=
    q_coprime_nine.dvd_of_dvd_mul_left q_dvd_scaled_code
  simpa only [q, width, allEraseLowerCode, spell_allEraseBlock] using q_dvd_code

/-- The same exact all-erasure lower code contains the radical of the primitive gap. -/
theorem radical_gapFactor_dvd_allEraseLowerCode
    {β : Nat} (β_positive : 0 < β) (body : List TagLetter) :
    UniqueFactorizationMonoid.radical (gapFactor β) ∣
      allEraseLowerCode β body (Nat.totient (gapFactor β).natAbs) :=
  UniqueFactorizationMonoid.radical_dvd_self.trans
    (gapFactor_dvd_allEraseLowerCode β_positive body)

/-- A support-saturating erasure width forced into the initial raw-head extinction range. -/
def entrySaturationWidth (β : Nat) : Nat :=
  3 * Nat.totient (gapFactor β).natAbs

/-- The entry saturation width is at least three at every physical deletion width. -/
theorem entrySaturationWidth_three_le {β : Nat} (β_positive : 0 < β) :
    3 ≤ entrySaturationWidth β := by
  have width_positive := allEraseSaturationWidth_pos β_positive
  simp only [entrySaturationWidth]
  omega

/-- Exact decimal-code identity for every physical all-erasure lower word. -/
theorem allEraseLowerCode_identity (β : Nat) (body : List TagLetter) (width : Nat) :
    9 * allEraseLowerCode β body width + 7 = 7 * (10 : ℤ) ^ width := by
  have identity := replicateFalse_code_identity width
  have cast_identity := congrArg (fun value : Nat => (value : ℤ)) identity
  norm_num at cast_identity
  simpa only [allEraseLowerCode, spell_allEraseBlock] using cast_identity

/-- The physical entry-width all-erasure lower code contains the full primitive gap. -/
theorem gapFactor_dvd_entrySaturationLowerCode
    {β : Nat} (β_positive : 0 < β) (body : List TagLetter) :
    gapFactor β ∣ allEraseLowerCode β body (entrySaturationWidth β) := by
  let width := Nat.totient (gapFactor β).natAbs
  let zeros := List.replicate width false
  have base : gapFactor β ∣ (code zeros : ℤ) := by
    simpa only [width, zeros, allEraseLowerCode, spell_allEraseBlock] using
      gapFactor_dvd_allEraseLowerCode β_positive body
  have double : gapFactor β ∣ (code (zeros ++ zeros) : ℤ) := by
    rw [code_append]
    push_cast
    exact dvd_add (base.mul_right (10 ^ zeros.length)) base
  have triple : gapFactor β ∣ (code ((zeros ++ zeros) ++ zeros) : ℤ) := by
    rw [code_append]
    push_cast
    exact dvd_add (double.mul_right (10 ^ zeros.length)) base
  have spelling :
      List.replicate (entrySaturationWidth β) false =
        (zeros ++ zeros) ++ zeros := by
    simp only [entrySaturationWidth, zeros, width]
    rw [show 3 * Nat.totient (gapFactor β).natAbs =
      (Nat.totient (gapFactor β).natAbs + Nat.totient (gapFactor β).natAbs) +
        Nat.totient (gapFactor β).natAbs by omega]
    simp only [List.replicate_add]
  simpa only [allEraseLowerCode, spell_allEraseBlock, spelling] using triple

/-- The universal all-erasure support saturator cannot be the first transition from a lawful
two-`c` raw head to another multi-role pole. -/
theorem entrySaturator_rawHead_shell_impossible
    {β : Nat} (body tail : List TagLetter) {μ E G P T R : ℤ}
    (β_large : 2 ≤ β)
    (head_unit :
      HasDecimalShell (code (peeledHeadWord β (.c :: .c :: tail)) : ℚ) 0 0)
    (mu_eq : 9 * μ = 52 * 10 ^ β - 7)
    (gap_eq : E = 18 * 10 ^ β - 63)
    (lift_eq : G = 502 * 10 ^ β - 7)
    (upper_eq :
      9 * P = 50 * 10 ^ β * 10 ^ entrySaturationWidth β + 2 * 10 ^ β - 7)
    (trace_eq :
      T = E * P + G * allEraseLowerCode β body (entrySaturationWidth β))
    (residual_eq :
      R = (code (peeledHeadWord β (.c :: .c :: tail)) : ℤ) * T -
        10 * μ * G * allEraseLowerCode β body (entrySaturationWidth β))
    (shell : HasDecimalShell (R : ℚ)
      ((entrySaturationWidth β - 1 : Nat) : ℤ)
      ((entrySaturationWidth β - 1 : Nat) : ℤ)) :
    False := by
  apply allCDeletion_peeledDoubleCHead_shell_impossible tail β_large
    (entrySaturationWidth_three_le (by omega)) head_unit mu_eq gap_eq lift_eq upper_eq
  · have identity := allEraseLowerCode_identity β body (entrySaturationWidth β)
    linear_combination identity
  · exact trace_eq
  · exact residual_eq
  · exact shell

/-- A leading-`D_b` erasure block followed by `tailWidth` copies of `D_c`. -/
def leadingBEraseBlock (tailWidth : Nat) : List NearyTile :=
  .erase .b :: List.replicate tailWidth (.erase .c)

/-- Every lower side in a leading-`D_b` erasure block is the same one-digit zero word. -/
@[simp] theorem spell_leadingBEraseBlock_lower
    (β : Nat) (body : List TagLetter) (tailWidth : Nat) :
    spell (nearyLower β body) (leadingBEraseBlock tailWidth) =
      List.replicate (tailWidth + 1) false := by
  change false :: spell (nearyLower β body) (List.replicate tailWidth (.erase .c)) =
    false :: List.replicate tailWidth false
  exact congrArg (false :: ·) (by
    simpa only [allEraseBlock] using (spell_allEraseBlock β body tailWidth))

@[simp] private theorem tagEncode_replicate_c (β width : Nat) :
    tagEncode β (List.replicate width .c) = List.replicate width true := by
  induction width with
  | zero => rfl
  | succ width induction =>
      rw [List.replicate_succ, tagEncode_cons, tagCode, induction,
        List.replicate_succ]
      rfl

/-- Replacing the leading `D_c` of an all-`D_c` word by `D_b` prefixes its punctuated upper
word by exactly one marker word. -/
theorem leadingB_punctuatedUpper_eq (β tailWidth : Nat) :
    punctuatedUpper β (.b :: List.replicate tailWidth .c) =
      markerWord β ++ punctuatedUpper β (List.replicate (tailWidth + 1) .c) := by
  simp [punctuatedUpper, tagEncode_cons, tagCode, markerWord, List.replicate_succ,
    List.append_assoc]

private theorem allC_punctuatedUpper_length (β width : Nat) :
    (punctuatedUpper β (List.replicate width .c)).length = width + β + 1 := by
  simp [punctuatedUpper, markerWord, Nat.add_assoc]

/-- The leading-`D_b` upper code differs from the same-width all-`D_c` code by one marker
shifted past the entire punctuated all-`D_c` word. -/
theorem leadingB_punctuatedUpper_code_eq (β tailWidth : Nat) :
    code (punctuatedUpper β (.b :: List.replicate tailWidth .c)) =
      code (punctuatedUpper β (List.replicate (tailWidth + 1) .c)) +
        code (markerWord β) * 10 ^ (tailWidth + 1 + β + 1) := by
  rw [leadingB_punctuatedUpper_eq, code_append,
    allC_punctuatedUpper_length]
  ring

private theorem replicateTrue_code_identity (width : Nat) :
    9 * code (List.replicate width true) + 5 = 5 * 10 ^ width := by
  induction width with
  | zero => norm_num
  | succ width induction =>
      rw [List.replicate_succ, code_cons, digit_true, List.length_replicate,
        pow_succ]
      omega

/-- Exact upper-code formula for an all-`D_c` word followed by the marker. -/
theorem allC_punctuatedUpper_code_identity (β width : Nat) :
    9 * (code (punctuatedUpper β (List.replicate width .c)) : ℤ) =
      50 * 10 ^ β * 10 ^ width + 2 * 10 ^ β - 7 := by
  have upper_spelling :
      punctuatedUpper β (List.replicate width .c) =
        List.replicate width true ++ markerWord β := by
    simp only [punctuatedUpper, tagEncode_replicate_c]
  have true_identity :
      9 * (code (List.replicate width true) : ℤ) + 5 = 5 * 10 ^ width := by
    exact_mod_cast replicateTrue_code_identity width
  have marker_identity :
      9 * (code (markerWord β) : ℤ) + 7 = 52 * 10 ^ β := by
    exact_mod_cast markerWord_code_identity β
  rw [upper_spelling, code_append]
  push_cast
  rw [show (markerWord β).length = β + 1 by simp [markerWord]]
  rw [pow_succ]
  linear_combination 10 * 10 ^ β * true_identity + marker_identity

/-- Decimal lower code emitted by a leading-`D_b` erasure block. -/
def leadingBEraseLowerCode
    (β : Nat) (body : List TagLetter) (tailWidth : Nat) : ℤ :=
  code (spell (nearyLower β body) (leadingBEraseBlock tailWidth))

/-- A leading-`D_b` erasure block has the same lower code as the same-width all-`D_c` block. -/
theorem leadingBEraseLowerCode_eq_allEraseLowerCode
    (β : Nat) (body : List TagLetter) (tailWidth : Nat) :
    leadingBEraseLowerCode β body tailWidth =
      allEraseLowerCode β body (tailWidth + 1) := by
  simp only [leadingBEraseLowerCode, allEraseLowerCode,
    spell_leadingBEraseBlock_lower, spell_allEraseBlock]

/-- At the entry saturation width, the physical leading-`D_b` erasure lower code contains the
full primitive gap. -/
theorem gapFactor_dvd_entryLeadingBEraseLowerCode
    {β : Nat} (β_positive : 0 < β) (body : List TagLetter) :
    gapFactor β ∣ leadingBEraseLowerCode β body (entrySaturationWidth β - 1) := by
  rw [leadingBEraseLowerCode_eq_allEraseLowerCode,
    Nat.sub_add_cancel (show 1 ≤ entrySaturationWidth β by
      exact (entrySaturationWidth_three_le β_positive).trans' (by norm_num))]
  exact gapFactor_dvd_entrySaturationLowerCode β_positive body

/-- Under the exact marker equation, the leading-`D_b` upper perturbation is
`μ·10^(width+β+1)`. -/
theorem leadingB_punctuatedUpper_code_perturbation
    {β : Nat} {μ : ℤ} (tailWidth : Nat)
    (mu_eq : 9 * μ = 52 * 10 ^ β - 7) :
    (code (punctuatedUpper β (.b :: List.replicate tailWidth .c)) : ℤ) =
      code (punctuatedUpper β (List.replicate (tailWidth + 1) .c)) +
        μ * 10 ^ (tailWidth + 1 + β + 1) := by
  have marker_identity :
      9 * (code (markerWord β) : ℤ) = 52 * 10 ^ β - 7 := by
    have identity :
        9 * (code (markerWord β) : ℤ) + 7 = 52 * 10 ^ β := by
      exact_mod_cast markerWord_code_identity β
    linear_combination identity
  have marker_eq : (code (markerWord β) : ℤ) = μ := by
    have scaled : 9 * (code (markerWord β) : ℤ) = 9 * μ :=
      marker_identity.trans mu_eq.symm
    exact mul_left_cancel₀ (show (9 : ℤ) ≠ 0 by norm_num) scaled
  have code_eq := leadingB_punctuatedUpper_code_eq β tailWidth
  have code_eq_int :
      (code (punctuatedUpper β (.b :: List.replicate tailWidth .c)) : ℤ) =
        code (punctuatedUpper β (List.replicate (tailWidth + 1) .c)) +
          code (markerWord β) * 10 ^ (tailWidth + 1 + β + 1) := by
    exact_mod_cast code_eq
  simpa only [marker_eq] using code_eq_int

/-- The entry-width leading-`D_b` upper perturbation occurs exactly at decimal depth
`entrySaturationWidth β+β+1`. -/
theorem entryLeadingB_punctuatedUpper_code_perturbation
    {β : Nat} {μ : ℤ} (β_positive : 0 < β)
    (mu_eq : 9 * μ = 52 * 10 ^ β - 7) :
    (code (punctuatedUpper β
      (.b :: List.replicate (entrySaturationWidth β - 1) .c)) : ℤ) =
        code (punctuatedUpper β
          (List.replicate (entrySaturationWidth β) .c)) +
            μ * 10 ^ (entrySaturationWidth β + β + 1) := by
  have width_restore : entrySaturationWidth β - 1 + 1 = entrySaturationWidth β :=
    Nat.sub_add_cancel (show 1 ≤ entrySaturationWidth β by
      exact (entrySaturationWidth_three_le β_positive).trans' (by norm_num))
  simpa only [width_restore] using
    (leadingB_punctuatedUpper_code_perturbation
      (entrySaturationWidth β - 1) mu_eq)

/-- The support-saturating leading-`D_b` erasure block cannot be the first transition from a
lawful two-`c` raw head to another multi-role pole. -/
theorem entryLeadingBErase_rawHead_shell_impossible
    {β : Nat} (body tail : List TagLetter) {μ E G : ℤ}
    (β_large : 2 ≤ β)
    (head_unit :
      HasDecimalShell (code (peeledHeadWord β (.c :: .c :: tail)) : ℚ) 0 0)
    (mu_eq : 9 * μ = 52 * 10 ^ β - 7)
    (gap_eq : E = 18 * 10 ^ β - 63)
    (lift_eq : G = 502 * 10 ^ β - 7)
    (shell :
      HasDecimalShell
        (((code (peeledHeadWord β (.c :: .c :: tail)) : ℤ) *
          (E * code (punctuatedUpper β
              (.b :: List.replicate (entrySaturationWidth β - 1) .c)) +
            G * leadingBEraseLowerCode β body (entrySaturationWidth β - 1)) -
          10 * μ * G *
            leadingBEraseLowerCode β body (entrySaturationWidth β - 1) : ℤ) : ℚ)
        ((entrySaturationWidth β + β : Nat) : ℤ)
        ((entrySaturationWidth β + β : Nat) : ℤ)) :
    False := by
  let n := entrySaturationWidth β
  let H : ℤ := code (peeledHeadWord β (.c :: .c :: tail))
  let PAll : ℤ := code (punctuatedUpper β (List.replicate n .c))
  let PB : ℤ := code (punctuatedUpper β
    (.b :: List.replicate (n - 1) .c))
  let V := leadingBEraseLowerCode β body (n - 1)
  let RAll := H * (E * PAll + G * V) - 10 * μ * G * V
  let RB := H * (E * PB + G * V) - 10 * μ * G * V
  have β_positive : 0 < β := by omega
  have n_positive : 1 ≤ n := by
    exact (entrySaturationWidth_three_le β_positive).trans' (by norm_num)
  have allC_upper_eq : 9 * PAll =
      50 * 10 ^ β * 10 ^ n + 2 * 10 ^ β - 7 := by
    exact allC_punctuatedUpper_code_identity β n
  have V_eq : V = allEraseLowerCode β body n := by
    dsimp only [V]
    rw [leadingBEraseLowerCode_eq_allEraseLowerCode,
      Nat.sub_add_cancel n_positive]
  have lower_eq : 9 * V = 7 * 10 ^ n - 7 := by
    have identity := allEraseLowerCode_identity β body n
    rw [V_eq]
    linear_combination identity
  have leadingB_upper_eq : PB = PAll + μ * 10 ^ (n + β + 1) := by
    dsimp only [PB, PAll]
    exact entryLeadingB_punctuatedUpper_code_perturbation β_positive mu_eq
  refine leadingBDeletion_peeledDoubleCHead_shell_impossible
    (RAll := RAll) (RB := RB) tail β_large n_positive head_unit mu_eq gap_eq lift_eq
      allC_upper_eq lower_eq ?_ leadingB_upper_eq ?_ ?_
  · rfl
  · rfl
  · simpa only [n, H, PB, V, RB, Nat.cast_add] using shell

/-- An all-erasure word whose second tile is `D_b`. -/
def secondBEraseBlock (tailWidth : Nat) : List NearyTile :=
  .erase .c :: .erase .b :: List.replicate tailWidth (.erase .c)

/-- Every lower side in a second-position `D_b` erasure block is the one-digit zero word. -/
@[simp] theorem spell_secondBEraseBlock_lower
    (β : Nat) (body : List TagLetter) (tailWidth : Nat) :
    spell (nearyLower β body) (secondBEraseBlock tailWidth) =
      List.replicate (tailWidth + 2) false := by
  change false :: false ::
      spell (nearyLower β body) (List.replicate tailWidth (.erase .c)) =
    false :: false :: List.replicate tailWidth false
  exact congrArg (false :: false :: ·) (by
    simpa only [allEraseBlock] using spell_allEraseBlock β body tailWidth)

private theorem secondB_punctuatedUpper_eq_append (β tailWidth : Nat) :
    punctuatedUpper β (.c :: .b :: List.replicate tailWidth .c) =
      ([true] ++ markerWord β) ++
        (List.replicate (tailWidth + 1) true ++ markerWord β) := by
  simp [punctuatedUpper, tagEncode_cons, tagCode, markerWord, List.replicate_succ,
    List.append_assoc]

private theorem sameWidthAllC_punctuatedUpper_eq_append (β tailWidth : Nat) :
  punctuatedUpper β (List.replicate (tailWidth + 2) .c) =
      [true] ++ (List.replicate (tailWidth + 1) true ++ markerWord β) := by
  simp [punctuatedUpper, tagEncode_cons, tagCode, markerWord, List.replicate_succ]

/-- Replacing the second `D_c` by `D_b` changes the punctuated upper code only above the
common suffix of decimal length `tailWidth+β+2`. -/
theorem tenPower_dvd_secondB_punctuatedUpper_code_sub (β tailWidth : Nat) :
    (10 : ℤ) ^ (tailWidth + β + 2) ∣
      (code (punctuatedUpper β (.c :: .b :: List.replicate tailWidth .c)) : ℤ) -
        code (punctuatedUpper β (List.replicate (tailWidth + 2) .c)) := by
  let suffix := List.replicate (tailWidth + 1) true ++ markerWord β
  have suffix_length : suffix.length = tailWidth + β + 2 := by
    simp [suffix, markerWord]
    omega
  rw [secondB_punctuatedUpper_eq_append,
    sameWidthAllC_punctuatedUpper_eq_append]
  change (10 : ℤ) ^ (tailWidth + β + 2) ∣
    (code (([true] ++ markerWord β) ++ suffix) : ℤ) -
      code ([true] ++ suffix)
  have secondB_code := code_append ([true] ++ markerWord β) suffix
  have allC_code := code_append [true] suffix
  rw [secondB_code, allC_code]
  push_cast
  rw [suffix_length]
  refine ⟨(code ([true] ++ markerWord β) : ℤ) - code [true], ?_⟩
  ring

/-- The second-position upper perturbation is five-adically invisible at exactly the full
multi-role target depth. -/
theorem fivePower_dvd_secondB_punctuatedUpper_code_sub (β tailWidth : Nat) :
    (5 : ℤ) ^ (tailWidth + 2 + β) ∣
      (code (punctuatedUpper β (.c :: .b :: List.replicate tailWidth .c)) : ℤ) -
        code (punctuatedUpper β (List.replicate (tailWidth + 2) .c)) := by
  have five_dvd_ten : (5 : ℤ) ∣ 10 := by norm_num
  have power_dvd : (5 : ℤ) ^ (tailWidth + 2 + β) ∣
      10 ^ (tailWidth + 2 + β) := pow_dvd_pow_of_dvd five_dvd_ten _
  have code_dvd := tenPower_dvd_secondB_punctuatedUpper_code_sub β tailWidth
  have code_dvd' : (10 : ℤ) ^ (tailWidth + 2 + β) ∣
      (code (punctuatedUpper β (.c :: .b :: List.replicate tailWidth .c)) : ℤ) -
        code (punctuatedUpper β (List.replicate (tailWidth + 2) .c)) := by
    simpa only [show tailWidth + 2 + β = tailWidth + β + 2 by omega] using code_dvd
  exact power_dvd.trans code_dvd'

/-- Decimal lower code emitted by a second-position `D_b` erasure block. -/
def secondBEraseLowerCode
    (β : Nat) (body : List TagLetter) (tailWidth : Nat) : ℤ :=
  code (spell (nearyLower β body) (secondBEraseBlock tailWidth))

/-- A second-position `D_b` erasure block has the same lower code as the same-width all-`D_c`
block. -/
theorem secondBEraseLowerCode_eq_allEraseLowerCode
    (β : Nat) (body : List TagLetter) (tailWidth : Nat) :
    secondBEraseLowerCode β body tailWidth =
      allEraseLowerCode β body (tailWidth + 2) := by
  simp only [secondBEraseLowerCode, allEraseLowerCode,
    spell_secondBEraseBlock_lower, spell_allEraseBlock]

/-- At the entry saturation width, the physical second-position `D_b` erasure lower code
contains the full primitive gap. -/
theorem gapFactor_dvd_entrySecondBEraseLowerCode
    {β : Nat} (β_positive : 0 < β) (body : List TagLetter) :
    gapFactor β ∣ secondBEraseLowerCode β body (entrySaturationWidth β - 2) := by
  rw [secondBEraseLowerCode_eq_allEraseLowerCode,
    Nat.sub_add_cancel (show 2 ≤ entrySaturationWidth β by
      exact (entrySaturationWidth_three_le β_positive).trans' (by norm_num))]
  exact gapFactor_dvd_entrySaturationLowerCode β_positive body

/-- No second-position `D_b` all-erasure block can be the first transition from a lawful
two-`c` raw head to another multi-role pole. -/
theorem secondBErase_rawHead_shell_impossible
    {β tailWidth : Nat} (body headTail : List TagLetter) {μ E G : ℤ}
    (β_large : 2 ≤ β)
    (head_unit :
      HasDecimalShell (code (peeledHeadWord β (.c :: .c :: headTail)) : ℚ) 0 0)
    (mu_eq : 9 * μ = 52 * 10 ^ β - 7)
    (gap_eq : E = 18 * 10 ^ β - 63)
    (lift_eq : G = 502 * 10 ^ β - 7)
    (shell :
      HasDecimalShell
        (((code (peeledHeadWord β (.c :: .c :: headTail)) : ℤ) *
          (E * code (punctuatedUpper β
              (.c :: .b :: List.replicate tailWidth .c)) +
            G * secondBEraseLowerCode β body tailWidth) -
          10 * μ * G * secondBEraseLowerCode β body tailWidth : ℤ) : ℚ)
        ((tailWidth + 2 + β : Nat) : ℤ)
        ((tailWidth + 2 + β : Nat) : ℤ)) :
    False := by
  let n := tailWidth + 2
  let H : ℤ := code (peeledHeadWord β (.c :: .c :: headTail))
  let PAll : ℤ := code (punctuatedUpper β (List.replicate n .c))
  let P : ℤ := code (punctuatedUpper β (.c :: .b :: List.replicate tailWidth .c))
  let V := secondBEraseLowerCode β body tailWidth
  let RAll := H * (E * PAll + G * V) - 10 * μ * G * V
  let R := H * (E * P + G * V) - 10 * μ * G * V
  have n_positive : 1 ≤ n := by omega
  have allC_upper_eq : 9 * PAll =
      50 * 10 ^ β * 10 ^ n + 2 * 10 ^ β - 7 := by
    exact allC_punctuatedUpper_code_identity β n
  have V_eq : V = allEraseLowerCode β body n := by
    dsimp only [V, n]
    exact secondBEraseLowerCode_eq_allEraseLowerCode β body tailWidth
  have lower_eq : 9 * V = 7 * 10 ^ n - 7 := by
    have identity := allEraseLowerCode_identity β body n
    rw [V_eq]
    linear_combination identity
  refine fiveDeepUpperPerturbation_peeledDoubleCHead_shell_impossible
    (PAll := PAll) (P := P) (RAll := RAll) (R := R) headTail β_large n_positive
      head_unit mu_eq gap_eq lift_eq allC_upper_eq lower_eq ?_ ?_ ?_ ?_
  · rfl
  · dsimp only [P, PAll, n]
    exact fivePower_dvd_secondB_punctuatedUpper_code_sub β tailWidth
  · rfl
  · simpa only [n, H, P, V, R, Nat.cast_add] using shell

private theorem gapFactor_dvd_carrierProduct
    {q E G μ N D Nprev P₂ P₃ V₂ V₃ T₂ T₃ : ℤ} {m : Nat}
    (E_multiple : q ∣ E)
    (D_eq : D = E * Nprev)
    (T2_eq : T₂ = E * P₂ + G * V₂)
    (T3_eq : T₃ = E * P₃ + G * V₃)
    (next_pole :
      peeledNumerator N D μ G T₂ V₂ * T₃ =
        E * μ * G * 10 ^ m * N * V₃) :
    q ∣ N * G ^ 2 * V₂ * V₃ := by
  have E_zero : E ≡ 0 [ZMOD q] := E_multiple.modEq_zero_int
  have D_zero : D ≡ 0 [ZMOD q] := by
    rw [D_eq]
    simpa using E_zero.mul (Int.ModEq.refl Nprev)
  have T2_mod : T₂ ≡ G * V₂ [ZMOD q] := by
    rw [T2_eq]
    simpa using
      (E_zero.mul (Int.ModEq.refl P₂)).add
        ((Int.ModEq.refl G).mul (Int.ModEq.refl V₂))
  have T3_mod : T₃ ≡ G * V₃ [ZMOD q] := by
    rw [T3_eq]
    simpa using
      (E_zero.mul (Int.ModEq.refl P₃)).add
        ((Int.ModEq.refl G).mul (Int.ModEq.refl V₃))
  have residual_mod :
      peeledNumerator N D μ G T₂ V₂ ≡ N * G * V₂ [ZMOD q] := by
    unfold peeledNumerator
    have left_mod := (Int.ModEq.refl N).mul T2_mod
    have right_mod : 10 * μ * G * V₂ * D ≡ 0 [ZMOD q] := by
      simpa using
        (((((Int.ModEq.refl (10 : ℤ)).mul (Int.ModEq.refl μ)).mul
          (Int.ModEq.refl G)).mul (Int.ModEq.refl V₂)).mul D_zero)
    simpa [mul_assoc] using left_mod.sub right_mod
  have right_dvd : q ∣ E * μ * G * 10 ^ m * N * V₃ := by
    simpa [mul_assoc] using
      dvd_mul_of_dvd_left E_multiple (μ * G * 10 ^ m * N * V₃)
  have left_zero : peeledNumerator N D μ G T₂ V₂ * T₃ ≡ 0 [ZMOD q] := by
    rw [next_pole]
    exact right_dvd.modEq_zero_int
  have product_zero : N * G ^ 2 * V₂ * V₃ ≡ 0 [ZMOD q] := by
    calc
      N * G ^ 2 * V₂ * V₃ = (N * G * V₂) * (G * V₃) := by ring
      _ ≡ peeledNumerator N D μ G T₂ V₂ * T₃ [ZMOD q] :=
        (residual_mod.mul T3_mod).symm
      _ ≡ 0 [ZMOD q] := left_zero
  exact Int.modEq_zero_iff_dvd.mp product_zero

private theorem carrierFactor_quotientCongruence
    {r s q g E G μ N D Nprev P₂ P₃ V₂ V₃ T₂ T₃ W : ℤ} {m : Nat}
    (r_ne : r ≠ 0)
    (q_eq : q = r * s)
    (E_eq : E = 9 * q)
    (G_eq : G = 9 * g)
    (D_eq : D = E * Nprev)
    (T2_eq : T₂ = E * P₂ + G * V₂)
    (T3_eq : T₃ = E * P₃ + G * V₃)
    (V2_eq : V₂ = r * W)
    (coprime : IsCoprime r (N * g * V₃))
    (next_pole :
      peeledNumerator N D μ G T₂ V₂ * T₃ =
        E * μ * G * 10 ^ m * N * V₃) :
    r ∣ s * (P₂ - μ * 10 ^ m) + g * W := by
  have factored :
      (81 * r) *
          ((N * (s * P₂ + g * W) - 90 * μ * g * (r * s) * W * Nprev) *
            (r * s * P₃ + g * V₃)) =
        (81 * r) * (s * μ * g * 10 ^ m * N * V₃) := by
    rw [E_eq] at D_eq
    rw [E_eq, G_eq] at T2_eq T3_eq next_pole
    rw [q_eq] at D_eq T2_eq T3_eq next_pole
    rw [D_eq, T2_eq, T3_eq, V2_eq] at next_pole
    unfold peeledNumerator at next_pole
    linear_combination next_pole
  have coefficient_ne : 81 * r ≠ 0 := mul_ne_zero (by norm_num) r_ne
  have cancelled :
      (N * (s * P₂ + g * W) - 90 * μ * g * (r * s) * W * Nprev) *
          (r * s * P₃ + g * V₃) =
        s * μ * g * 10 ^ m * N * V₃ :=
    mul_left_cancel₀ coefficient_ne factored
  have product_dvd :
      r ∣ N * g * V₃ * (s * (P₂ - μ * 10 ^ m) + g * W) := by
    refine ⟨s * (-(N * (s * P₂ + g * W) * P₃) +
      90 * μ * g * W * Nprev * (r * s * P₃ + g * V₃)), ?_⟩
    linear_combination cancelled
  exact coprime.dvd_of_dvd_mul_left product_dvd

/-- Every factor of the primitive gap that is coprime to the carrier numerator imposes its own
two-stage code gate. This remains informative when the full gap and numerator share factors. -/
theorem carrierFactor_multiToSingleton_quotientGate
    {β m : Nat} {r s μ N D Nprev P₂ P₃ V₂ T₂ T₃ : ℤ}
    (β_positive : 0 < β)
    (q_factor : gapFactor β = r * s)
    (N_coprime : IsCoprime r N)
    (D_eq : D = decimalGap (10 ^ β) * Nprev)
    (T2_eq : T₂ = decimalGap (10 ^ β) * P₂ + decimalLift (10 ^ β) * V₂)
    (T3_eq : T₃ = decimalGap (10 ^ β) * P₃ + decimalLift (10 ^ β) * 7)
    (next_pole :
      peeledNumerator N D μ (decimalLift (10 ^ β)) T₂ V₂ * T₃ =
        decimalGap (10 ^ β) * μ * decimalLift (10 ^ β) * 10 ^ m * N * 7) :
    ∃ g W : ℤ,
      decimalLift (10 ^ β) = 9 * g ∧
        V₂ = r * W ∧
          r ∣ s * (P₂ - μ * 10 ^ m) + g * W := by
  let q := gapFactor β
  let G := decimalLift (10 ^ β)
  have q_ne : q ≠ 0 := by
    exact (gapFactor_pos β_positive).ne'
  have q_eq : q = r * s := by simpa only [q] using q_factor
  have r_ne : r ≠ 0 := by
    intro r_zero
    rw [r_zero, zero_mul] at q_eq
    exact q_ne q_eq
  have E_eq : decimalGap (10 ^ β) = 9 * q := by
    simp [decimalGap, q, gapFactor]
  obtain ⟨g, G_eq⟩ := nine_dvd_decimalLift_ten_pow β
  have qG_coprime : IsCoprime q G := by
    simpa [q, G] using gapFactor_coprime_decimalLift β_positive
  have q7_coprime : IsCoprime q (7 : ℤ) := by
    simpa [q] using gapFactor_coprime_seven β
  have r_dvd_q : r ∣ q := ⟨s, q_eq⟩
  have rG_coprime : IsCoprime r G :=
    IsCoprime.of_isCoprime_of_dvd_left qG_coprime r_dvd_q
  have r7_coprime : IsCoprime r (7 : ℤ) :=
    IsCoprime.of_isCoprime_of_dvd_left q7_coprime r_dvd_q
  have r_dvd_E : r ∣ decimalGap (10 ^ β) := by
    refine ⟨9 * s, ?_⟩
    rw [E_eq, q_eq]
    ring
  have product_dvd : r ∣ N * G ^ 2 * V₂ * 7 := by
    apply gapFactor_dvd_carrierProduct r_dvd_E D_eq T2_eq T3_eq
    simpa only [G] using next_pole
  have coefficient_coprime : IsCoprime r (N * G ^ 2 * 7) := by
    simpa [pow_two, mul_assoc] using
      ((N_coprime.mul_right rG_coprime).mul_right rG_coprime).mul_right r7_coprime
  have V2_dvd : r ∣ V₂ := by
    apply coefficient_coprime.dvd_of_dvd_mul_left
    simpa [mul_assoc, mul_left_comm, mul_comm] using product_dvd
  obtain ⟨W, V2_eq⟩ := V2_dvd
  have g_dvd_G : g ∣ G := by
    refine ⟨9, ?_⟩
    dsimp [G]
    rw [G_eq]
    ring
  have rg_coprime : IsCoprime r g :=
    IsCoprime.of_isCoprime_of_dvd_right rG_coprime g_dvd_G
  have quotient_coprime : IsCoprime r (N * g * 7) :=
    (N_coprime.mul_right rg_coprime).mul_right r7_coprime
  refine ⟨g, W, G_eq, V2_eq, ?_⟩
  apply carrierFactor_quotientCongruence r_ne q_eq E_eq G_eq D_eq T2_eq T3_eq V2_eq
    quotient_coprime
  simpa only [G] using next_pole

/-- A denominator-descended carrier can hit a physical singleton target only through two
successive gap-factor gates. If its numerator is coprime to the primitive gap factor, then the
current lower code contains that factor; after division, the upper code and scale obey the
displayed second congruence. -/
theorem gapClean_multiToSingleton_quotientGate
    {β m : Nat} {μ N D Nprev P₂ P₃ V₂ T₂ T₃ : ℤ}
    (β_positive : 0 < β)
    (N_coprime : IsCoprime (gapFactor β) N)
    (D_eq : D = decimalGap (10 ^ β) * Nprev)
    (T2_eq : T₂ = decimalGap (10 ^ β) * P₂ + decimalLift (10 ^ β) * V₂)
    (T3_eq : T₃ = decimalGap (10 ^ β) * P₃ + decimalLift (10 ^ β) * 7)
    (next_pole :
      peeledNumerator N D μ (decimalLift (10 ^ β)) T₂ V₂ * T₃ =
        decimalGap (10 ^ β) * μ * decimalLift (10 ^ β) * 10 ^ m * N * 7) :
    ∃ g W : ℤ,
      decimalLift (10 ^ β) = 9 * g ∧
        V₂ = gapFactor β * W ∧
          gapFactor β ∣ P₂ + g * W - μ * 10 ^ m := by
  obtain ⟨g, W, G_eq, V2_eq, gate⟩ :=
    carrierFactor_multiToSingleton_quotientGate
      (r := gapFactor β) (s := 1) β_positive (by ring) N_coprime
      D_eq T2_eq T3_eq next_pole
  refine ⟨g, W, G_eq, V2_eq, ?_⟩
  simpa only [one_mul, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using gate

end MatrixMortality.DecimalSetterAncestry
