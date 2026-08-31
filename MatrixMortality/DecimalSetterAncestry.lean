import MatrixMortality.DecimalSetterDepth
import Mathlib.Tactic

/-!
# Decimal setter denominator ancestry

The recursive carrier denominator retains the preceding numerator through `D=EN₋`. Reducing
the recurrence by factors of the primitive gap `q=2·10^β−7` shows exactly how prime support
enters and persists. Every factor coprime to the current numerator also imposes two successive
code congruences on a transition into a singleton. This factorwise law remains informative when
`q` is composite and the numerator is not coprime to the full gap.
-/

namespace MatrixMortality.DecimalSetterAncestry

open MatrixMortality.DecimalSetterArithmetic
open MatrixMortality.DecimalSetterCarry
open MatrixMortality.DecimalSetterChamber
open MatrixMortality.DecimalSetterDepth

/-- The primitive factor left after removing the fixed factor nine from the decimal gap. -/
def gapFactor (β : Nat) : ℤ :=
  2 * 10 ^ β - 7

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
    simpa using (gapFactor_coprime_two β).mul_right
      (gapFactor_coprime_five β_positive)
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
    simp only [q, gapFactor]
    have ten_pos : (0 : ℤ) < 10 ^ β := pow_pos (by norm_num) β
    omega
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
