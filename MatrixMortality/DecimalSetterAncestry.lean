import MatrixMortality.DecimalSetterDepth
import Mathlib.Tactic

/-!
# Decimal setter denominator ancestry

The recursive carrier denominator retains the preceding numerator through `D=EN₋`. Reducing
the next-pole equation by the primitive gap factor `q=2·10^β−7` therefore exposes a constraint
invisible to decimal valuations: a carrier numerator coprime to `q` can reach a singleton only
when the current lower code contains `q`, and its quotient then satisfies a second congruence.
-/

namespace MatrixMortality.DecimalSetterAncestry

open MatrixMortality.DecimalSetterArithmetic
open MatrixMortality.DecimalSetterDepth

/-- The primitive factor left after removing the fixed factor nine from the decimal gap. -/
def gapFactor (β : Nat) : ℤ :=
  2 * 10 ^ β - 7

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

private theorem gapFactor_quotientCongruence
    {q g E G μ N D Nprev P₂ P₃ V₂ V₃ T₂ T₃ W : ℤ} {m : Nat}
    (q_ne : q ≠ 0)
    (E_eq : E = 9 * q)
    (G_eq : G = 9 * g)
    (D_eq : D = E * Nprev)
    (T2_eq : T₂ = E * P₂ + G * V₂)
    (T3_eq : T₃ = E * P₃ + G * V₃)
    (V2_eq : V₂ = q * W)
    (coprime : IsCoprime q (N * g * V₃))
    (next_pole :
      peeledNumerator N D μ G T₂ V₂ * T₃ =
        E * μ * G * 10 ^ m * N * V₃) :
    q ∣ P₂ + g * W - μ * 10 ^ m := by
  have factored :
      (81 * q) *
          ((N * (P₂ + g * W) - 90 * μ * g * q * W * Nprev) *
            (q * P₃ + g * V₃)) =
        (81 * q) * (μ * g * 10 ^ m * N * V₃) := by
    rw [E_eq] at D_eq
    rw [E_eq, G_eq] at T2_eq T3_eq next_pole
    rw [D_eq, T2_eq, T3_eq, V2_eq] at next_pole
    unfold peeledNumerator at next_pole
    linear_combination next_pole
  have coefficient_ne : 81 * q ≠ 0 := mul_ne_zero (by norm_num) q_ne
  have cancelled :
      (N * (P₂ + g * W) - 90 * μ * g * q * W * Nprev) *
          (q * P₃ + g * V₃) =
        μ * g * 10 ^ m * N * V₃ :=
    mul_left_cancel₀ coefficient_ne factored
  have product_dvd : q ∣ N * g * V₃ * (P₂ + g * W - μ * 10 ^ m) := by
    refine ⟨-(N * (P₂ + g * W) * P₃) +
      90 * μ * g * W * Nprev * (q * P₃ + g * V₃), ?_⟩
    linear_combination cancelled
  exact coprime.dvd_of_dvd_mul_left product_dvd

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
  let q := gapFactor β
  let G := decimalLift (10 ^ β)
  have q_ne : q ≠ 0 := by
    simp only [q, gapFactor]
    have ten_pos : (0 : ℤ) < 10 ^ β := pow_pos (by norm_num) β
    omega
  have E_eq : decimalGap (10 ^ β) = 9 * q := by
    simp [decimalGap, q, gapFactor]
  obtain ⟨g, G_eq⟩ := nine_dvd_decimalLift_ten_pow β
  have qG_coprime : IsCoprime q G := by
    simpa [q, G] using gapFactor_coprime_decimalLift β_positive
  have q7_coprime : IsCoprime q (7 : ℤ) := by
    simpa [q] using gapFactor_coprime_seven β
  have q_dvd_E : q ∣ decimalGap (10 ^ β) := by
    refine ⟨9, ?_⟩
    rw [E_eq]
    ring
  have product_dvd : q ∣ N * G ^ 2 * V₂ * 7 := by
    apply gapFactor_dvd_carrierProduct q_dvd_E D_eq T2_eq T3_eq
    simpa only [G] using next_pole
  have coefficient_coprime : IsCoprime q (N * G ^ 2 * 7) := by
    simpa [pow_two, mul_assoc] using
      ((N_coprime.mul_right qG_coprime).mul_right qG_coprime).mul_right q7_coprime
  have V2_dvd : q ∣ V₂ := by
    apply coefficient_coprime.dvd_of_dvd_mul_left
    simpa [mul_assoc, mul_left_comm, mul_comm] using product_dvd
  obtain ⟨W, V2_eq⟩ := V2_dvd
  have g_dvd_G : g ∣ G := by
    refine ⟨9, ?_⟩
    dsimp [G]
    rw [G_eq]
    ring
  have qg_coprime : IsCoprime q g :=
    IsCoprime.of_isCoprime_of_dvd_right qG_coprime g_dvd_G
  have quotient_coprime : IsCoprime q (N * g * 7) :=
    (N_coprime.mul_right qg_coprime).mul_right q7_coprime
  refine ⟨g, W, G_eq, V2_eq, ?_⟩
  apply gapFactor_quotientCongruence q_ne E_eq G_eq D_eq T2_eq T3_eq V2_eq
    quotient_coprime
  simpa only [G] using next_pole

end MatrixMortality.DecimalSetterAncestry
