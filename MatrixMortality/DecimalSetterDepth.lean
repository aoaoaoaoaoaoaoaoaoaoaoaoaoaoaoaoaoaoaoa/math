import MatrixMortality.DecimalSetterChamber
import Mathlib.Tactic

/-!
# Recursive decimal setter carrier

An A-shell pole chain admits an exact peeled carrier `t=N/(10μD)`. One transfer replaces its
numerator by `NT−10μGVD`; a following multi-role pole forces exactly `m−1` factors of both two
and five in that residual. Removing them gives the next carrier `(N', EN)`.

The initial carrier comes from a raw encoded-word suffix peel and has a three-way head grammar.
Later numerators are generalized product residuals, not raw encoded heads. A `2`-adic resonance
law excludes upper length two, so every surviving transition enters the compatible final-digit
two-cycle.
-/

namespace MatrixMortality.DecimalSetterDepth

open MatrixMortality.DecimalSetterArithmetic
open MatrixMortality.DecimalSetterCarry
open MatrixMortality.DecimalSetterChamber
open MatrixMortality.PadicValuation

/-- Numerator left after applying one J-fraction block to a peeled state. -/
def peeledNumerator {R : Type*} [Ring R]
    (N D μ G T V : R) : R :=
  N * T - 10 * μ * G * V * D

theorem jStep_peeled
    {E G μ P V N D : ℚ} {m : Nat}
    (E_ne : E ≠ 0) (mu_ne : μ ≠ 0) (N_ne : N ≠ 0) :
    jStep (P / (μ * 10 ^ m)) (G * V / (E * μ * 10 ^ m))
        (N / (10 * μ * D)) =
      peeledNumerator N D μ G (transferTrace E G P V) V /
        (E * μ * 10 ^ m * N) := by
  unfold jStep peeledNumerator transferTrace
  field_simp [E_ne, mu_ne, N_ne]

theorem peeled_pole_iff
    {G μ N D T V : ℚ}
    (mu_ne : μ ≠ 0) (D_ne : D ≠ 0) (T_ne : T ≠ 0) :
    N / (10 * μ * D) = G * V / T ↔
      peeledNumerator N D μ G T V = 0 := by
  unfold peeledNumerator
  rw [div_eq_div_iff]
  · constructor <;> intro equality <;> linear_combination equality
  · exact mul_ne_zero (mul_ne_zero (by norm_num) mu_ne) D_ne
  · exact T_ne

theorem peeledNumerator_multi_shell
    {E G μ N D T₂ T₃ V₂ V₃ : ℚ} {m : Nat}
    (E_unit : HasDecimalShell E 0 0)
    (G_unit : HasDecimalShell G 0 0)
    (mu_unit : HasDecimalShell μ 0 0)
    (N_unit : HasDecimalShell N 0 0)
    (V3_unit : HasDecimalShell V₃ 0 0)
    (T3_shell : HasDecimalShell T₃ 1 1)
    (next_pole :
      peeledNumerator N D μ G T₂ V₂ * T₃ =
        E * μ * G * 10 ^ m * N * V₃) :
    HasDecimalShell (peeledNumerator N D μ G T₂ V₂)
      ((m : ℤ) - 1) ((m : ℤ) - 1) := by
  have residual_ne : peeledNumerator N D μ G T₂ V₂ ≠ 0 := by
    intro residual_zero
    have right_zero : E * μ * G * 10 ^ m * N * V₃ = 0 := by
      rw [← next_pole, residual_zero, zero_mul]
    exact (mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero
            (mul_ne_zero E_unit.1.1 mu_unit.1.1) G_unit.1.1)
            (pow_ne_zero m (by norm_num)))
          N_unit.1.1)
        V3_unit.1.1) right_zero
  let rTwo := padicValRat 2 (peeledNumerator N D μ G T₂ V₂)
  let rFive := padicValRat 5 (peeledNumerator N D μ G T₂ V₂)
  have residual_shell :
      HasDecimalShell (peeledNumerator N D μ G T₂ V₂) rTwo rFive :=
    ⟨⟨residual_ne, rfl⟩, ⟨residual_ne, rfl⟩⟩
  have balances := poleEquation_shellBalance residual_shell T3_shell
    E_unit G_unit mu_unit (N_unit.mul V3_unit) (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using next_pole)
  have two_depth : rTwo = (m : ℤ) - 1 := by omega
  have five_depth : rFive = (m : ℤ) - 1 := by omega
  rw [two_depth, five_depth] at residual_shell
  exact residual_shell

theorem peeledDenominator_decimalUnit {E N : ℚ}
    (E_unit : HasDecimalShell E 0 0)
    (N_unit : HasDecimalShell N 0 0) :
    HasDecimalShell (E * N) 0 0 := by
  simpa only [zero_add] using E_unit.mul N_unit

private theorem two_unit_sub_unit_not_unit
    {left right : ℚ}
    (left_unit : HasValue 2 left 0)
    (right_unit : HasValue 2 right 0) :
    ¬HasValue 2 (left - right) 0 := by
  intro difference_unit
  have ratio_unit : HasValue 2 (left / right) 0 := by
    simpa using div_hasValue left_unit right_unit
  have predecessor_unit : HasValue 2 (left / right - 1) 0 := by
    have divided_difference : HasValue 2 ((left - right) / right) 0 := by
      simpa using div_hasValue difference_unit right_unit
    rw [show left / right - 1 = (left - right) / right by
      field_simp [right_unit.1]]
    exact divided_difference
  have two_odd := odd_prime_of_adjacent_units ratio_unit predecessor_unit
  norm_num at two_odd

/-- Two summands in the same `2`-adic shell of depth one cancel more deeply. In particular,
the residual of a multi-role trace cannot itself remain at depth one when the carrier and all
coefficients are decimal units. -/
theorem peeledNumerator_twoAdic_deepens
    {N D μ G T V : ℚ}
    (N_unit : HasValue 2 N 0)
    (D_unit : HasValue 2 D 0)
    (mu_unit : HasValue 2 μ 0)
    (G_unit : HasValue 2 G 0)
    (T_shell : HasValue 2 T 1)
    (V_unit : HasValue 2 V 0) :
    ¬HasValue 2 (peeledNumerator N D μ G T V) 1 := by
  intro residual_shell
  have ten_shell : HasValue 2 (10 : ℚ) 1 := ten_hasDecimalShell.1
  have trace_quotient_unit : HasValue 2 (T / 10) 0 := by
    simpa using div_hasValue T_shell ten_shell
  have left_unit : HasValue 2 (N * (T / 10)) 0 := by
    simpa using mul_hasValue N_unit trace_quotient_unit
  have right_unit : HasValue 2 (μ * G * V * D) 0 := by
    simpa using
      mul_hasValue (mul_hasValue (mul_hasValue mu_unit G_unit) V_unit) D_unit
  have normalized_residual_unit :
      HasValue 2 (N * (T / 10) - μ * G * V * D) 0 := by
    have quotient_unit : HasValue 2 (peeledNumerator N D μ G T V / 10) 0 := by
      simpa using div_hasValue residual_shell ten_shell
    rw [show peeledNumerator N D μ G T V / 10 =
        N * (T / 10) - μ * G * V * D by
      unfold peeledNumerator
      ring] at quotient_unit
    exact quotient_unit
  exact two_unit_sub_unit_not_unit left_unit right_unit normalized_residual_unit

/-- A consecutive multi-role pole transition from a decimal-unit carrier cannot use an upper
block of length two. The prospective pole forces residual depth `m-1`, while at `m=2` the two
depth-one summands cancel more deeply at two. -/
theorem peeledMultiPole_length_ne_two
    {E G μ N D T₂ T₃ V₂ V₃ : ℚ} {m : Nat}
    (E_unit : HasDecimalShell E 0 0)
    (G_unit : HasDecimalShell G 0 0)
    (mu_unit : HasDecimalShell μ 0 0)
    (N_unit : HasDecimalShell N 0 0)
    (D_unit : HasDecimalShell D 0 0)
    (V2_unit : HasDecimalShell V₂ 0 0)
    (V3_unit : HasDecimalShell V₃ 0 0)
    (T2_shell : HasDecimalShell T₂ 1 1)
    (T3_shell : HasDecimalShell T₃ 1 1)
    (next_pole :
      peeledNumerator N D μ G T₂ V₂ * T₃ =
        E * μ * G * 10 ^ m * N * V₃) :
    m ≠ 2 := by
  intro length_two
  subst m
  have residual_shell := peeledNumerator_multi_shell E_unit G_unit mu_unit N_unit V3_unit
    T3_shell next_pole
  have residual_two_shell : HasValue 2 (peeledNumerator N D μ G T₂ V₂) 1 := by
    norm_num at residual_shell ⊢
    exact residual_shell.1
  exact peeledNumerator_twoAdic_deepens N_unit.1 D_unit.1 mu_unit.1 G_unit.1 T2_shell.1
    V2_unit.1 residual_two_shell

/-- Every non-singleton consecutive multi-role transition from the recursive carrier has upper
length at least three. Thus all surviving transitions lie inside the higher-suffix regime. -/
theorem peeledMultiPole_three_le_length
    {E G μ N D T₂ T₃ V₂ V₃ : ℚ} {m : Nat}
    (length_two_le : 2 ≤ m)
    (E_unit : HasDecimalShell E 0 0)
    (G_unit : HasDecimalShell G 0 0)
    (mu_unit : HasDecimalShell μ 0 0)
    (N_unit : HasDecimalShell N 0 0)
    (D_unit : HasDecimalShell D 0 0)
    (V2_unit : HasDecimalShell V₂ 0 0)
    (V3_unit : HasDecimalShell V₃ 0 0)
    (T2_shell : HasDecimalShell T₂ 1 1)
    (T3_shell : HasDecimalShell T₃ 1 1)
    (next_pole :
      peeledNumerator N D μ G T₂ V₂ * T₃ =
        E * μ * G * 10 ^ m * N * V₃) :
    3 ≤ m := by
  have length_ne := peeledMultiPole_length_ne_two E_unit G_unit mu_unit N_unit D_unit V2_unit
    V3_unit T2_shell T3_shell next_pole
  omega

theorem peeledStep_factor
    {E G μ P V N D N' : ℚ} {depth : Nat}
    (E_ne : E ≠ 0) (mu_ne : μ ≠ 0) (N_ne : N ≠ 0)
    (factor :
      peeledNumerator N D μ G (transferTrace E G P V) V =
        10 ^ depth * N') :
    jStep (P / (μ * 10 ^ (depth + 1)))
        (G * V / (E * μ * 10 ^ (depth + 1)))
        (N / (10 * μ * D)) =
      N' / (10 * μ * (E * N)) := by
  rw [jStep_peeled E_ne mu_ne N_ne, factor, pow_succ]
  field_simp [E_ne, mu_ne, N_ne]

theorem cancelledDepthTwo_to_peeled
    {E G μ H T₂ T₃ V₂ V₃ : ℚ} {m : Nat}
    (identity :
      twoTransferTrace E G μ (10 ^ m) T₂ T₃ V₃ * H =
        10 * μ * G * V₂ * T₃) :
    peeledNumerator H 1 μ G T₂ V₂ * T₃ =
      H * E * μ * G * 10 ^ m * V₃ := by
  unfold peeledNumerator
  unfold twoTransferTrace at identity
  linear_combination identity

theorem cancel_decimalSuffix
    {K H μ G V T : ℚ} {depth : Nat}
    (identity :
      K * (10 ^ depth * H) =
        μ * G * V * 10 ^ (depth + 1) * T) :
    K * H = 10 * μ * G * V * T := by
  have scale_ne : (10 : ℚ) ^ depth ≠ 0 := pow_ne_zero depth (by norm_num)
  have factored :
      10 ^ depth * (K * H) =
        10 ^ depth * (10 * μ * G * V * T) := by
    rw [pow_succ] at identity
    linear_combination identity
  exact mul_left_cancel₀ scale_ne factored

theorem depthTwo_suffix_to_peeled
    {E G μ H T₂ T₃ V₂ V₃ : ℚ} {firstDepth middleLength : Nat}
    (identity :
      twoTransferTrace E G μ (10 ^ middleLength) T₂ T₃ V₃ *
          (10 ^ firstDepth * H) =
        μ * G * V₂ * 10 ^ (firstDepth + 1) * T₃) :
    peeledNumerator H 1 μ G T₂ V₂ * T₃ =
      H * E * μ * G * 10 ^ middleLength * V₃ := by
  apply cancelledDepthTwo_to_peeled
  exact cancel_decimalSuffix identity

theorem decimalUnit_of_factoredShell
    {H : ℚ} {depth : Nat}
    (factored_shell :
      HasDecimalShell (10 ^ depth * H) depth depth) :
    HasDecimalShell H 0 0 := by
  have scale_shell : HasDecimalShell ((10 : ℚ) ^ depth) depth depth := by
    simpa using ten_hasDecimalShell.pow depth
  constructor
  · have quotient := div_hasValue factored_shell.1 scale_shell.1
    simpa [show (10 : ℚ) ^ depth * H / 10 ^ depth = H by
      field_simp] using quotient
  · have quotient := div_hasValue factored_shell.2 scale_shell.2
    simpa [show (10 : ℚ) ^ depth * H / 10 ^ depth = H by
      field_simp] using quotient

theorem bTag_code_divisible_five (β : Nat) : 5 ∣ code (bTag β) := by
  rw [bTag_code]
  omega

theorem bTag_not_decimalUnit (β : Nat) :
    ¬HasDecimalShell (code (bTag β) : ℚ) 0 0 := by
  intro shell
  have code_ne : code (bTag β) ≠ 0 := by
    exact Nat.ne_of_gt (code_pos_of_ne_nil (by simp [bTag]))
  have valuation_pos : 0 < padicValNat 5 (code (bTag β)) :=
    one_le_padicValNat_of_dvd code_ne (bTag_code_divisible_five β)
  have valuation_zero : padicValNat 5 (code (bTag β)) = 0 := by
    exact_mod_cast shell.2.2
  omega

theorem bTag_cannot_head_equalDepth (β depth : Nat) :
    ¬HasDecimalShell
      ((10 : ℚ) ^ depth * code (bTag β)) depth depth := by
  intro shell
  exact bTag_not_decimalUnit β (decimalUnit_of_factoredShell shell)

theorem peeledNumerator_traceFactor
    {N D μ G T V τ : ℤ} (trace_factor : T = 10 * τ) :
    peeledNumerator N D μ G T V =
      10 * (N * τ - μ * G * V * D) := by
  simp [peeledNumerator, trace_factor]
  ring

theorem peeledNumerator_hundred_dvd_forces_unitCongruence
    {N D μ G T V τ : ℤ} (trace_factor : T = 10 * τ)
    (hundred_dvd : (100 : ℤ) ∣ peeledNumerator N D μ G T V) :
    N * τ ≡ μ * G * V * D [ZMOD 10] := by
  rw [Int.modEq_iff_dvd]
  obtain ⟨carry, carry_eq⟩ := hundred_dvd
  have factored := peeledNumerator_traceFactor
    (N := N) (D := D) (μ := μ) (G := G) (V := V) trace_factor
  have equation :
      10 * (N * τ - μ * G * V * D) = 100 * carry := by
    rw [← factored, carry_eq]
  have cancelled : N * τ - μ * G * V * D = 10 * carry := by
    apply mul_left_cancel₀ (show (10 : ℤ) ≠ 0 by norm_num)
    convert equation using 1
    all_goals ring
  have divides : (10 : ℤ) ∣ N * τ - μ * G * V * D := ⟨carry, cancelled⟩
  rw [show μ * G * V * D - N * τ = -(N * τ - μ * G * V * D) by ring]
  exact dvd_neg.mpr divides

theorem peeledNumerator_forces_lastDigit
    {N D μ G T V τ : ℤ} (trace_factor : T = 10 * τ)
    (hundred_dvd : (100 : ℤ) ∣ peeledNumerator N D μ G T V)
    (trace_unit : τ ≡ 1 [ZMOD 10])
    (mu_unit : μ ≡ 7 [ZMOD 10])
    (G_unit : G ≡ 3 [ZMOD 10])
    (V_unit : V ≡ 7 [ZMOD 10]) :
    N ≡ 7 * D [ZMOD 10] := by
  have forced := peeledNumerator_hundred_dvd_forces_unitCongruence
    trace_factor hundred_dvd
  calc
    N ≡ N * τ [ZMOD 10] := by
      simpa using ((Int.ModEq.refl N).mul trace_unit).symm
    _ ≡ μ * G * V * D [ZMOD 10] := forced
    _ ≡ 7 * 3 * 7 * D [ZMOD 10] :=
      (((mu_unit.mul G_unit).mul V_unit).mul (Int.ModEq.refl D))
    _ ≡ 7 * D [ZMOD 10] := by
      rw [Int.modEq_iff_dvd]
      refine ⟨-14 * D, by ring⟩

theorem peeledLastDigit_advances
    {N D N' D' E : ℤ}
    (current : N ≡ 7 * D [ZMOD 10])
    (gap_unit : E ≡ 7 [ZMOD 10])
    (denominator_step : D' = E * N)
    (next : N' ≡ 7 * D' [ZMOD 10]) :
    D' ≡ 9 * D [ZMOD 10] ∧ N' ≡ 3 * D [ZMOD 10] := by
  subst D'
  have denominator_residue : E * N ≡ 9 * D [ZMOD 10] := by
    calc
      E * N ≡ 7 * (7 * D) [ZMOD 10] := gap_unit.mul current
      _ ≡ 9 * D [ZMOD 10] := by
        rw [Int.modEq_iff_dvd]
        refine ⟨-4 * D, by ring⟩
  constructor
  · exact denominator_residue
  · calc
      N' ≡ 7 * (E * N) [ZMOD 10] := next
      _ ≡ 7 * (9 * D) [ZMOD 10] := (Int.ModEq.refl 7).mul denominator_residue
      _ ≡ 3 * D [ZMOD 10] := by
        rw [Int.modEq_iff_dvd]
        refine ⟨-6 * D, by ring⟩

theorem peeledLastDigit_twoStep
    {N₀ D₀ N₁ D₁ N₂ D₂ E : ℤ}
    (initial : N₀ ≡ 7 * D₀ [ZMOD 10])
    (gap_unit : E ≡ 7 [ZMOD 10])
    (first_denominator : D₁ = E * N₀)
    (first_next : N₁ ≡ 7 * D₁ [ZMOD 10])
    (second_denominator : D₂ = E * N₁)
    (second_next : N₂ ≡ 7 * D₂ [ZMOD 10]) :
    D₂ ≡ D₀ [ZMOD 10] ∧ N₂ ≡ 7 * D₀ [ZMOD 10] := by
  have first := peeledLastDigit_advances initial gap_unit first_denominator first_next
  have second := peeledLastDigit_advances first_next gap_unit second_denominator second_next
  constructor
  · calc
      D₂ ≡ 9 * D₁ [ZMOD 10] := second.1
      _ ≡ 9 * (9 * D₀) [ZMOD 10] := (Int.ModEq.refl 9).mul first.1
      _ ≡ D₀ [ZMOD 10] := by
        rw [Int.modEq_iff_dvd]
        refine ⟨-8 * D₀, by ring⟩
  · calc
      N₂ ≡ 3 * D₁ [ZMOD 10] := second.2
      _ ≡ 3 * (9 * D₀) [ZMOD 10] := (Int.ModEq.refl 3).mul first.1
      _ ≡ 7 * D₀ [ZMOD 10] := by
        rw [Int.modEq_iff_dvd]
        refine ⟨-2 * D₀, by ring⟩

/-- Punctuated upper spelling of a role-letter word. -/
def punctuatedUpper (β : Nat) (letters : List TagLetter) : List Bool :=
  tagEncode β letters ++ markerWord β

/-- The `β+2`-digit head left by an A-shell suffix peel. -/
def peeledHeadWord (β : Nat) (letters : List TagLetter) : List Bool :=
  (punctuatedUpper β letters).take (β + 2)

/-- Exact head produced by the role prefix `c b`. -/
def terminalHeadWord (β : Nat) : List Bool :=
  true :: true :: List.replicate β false

theorem terminalHeadWord_code_eq (β : Nat) :
    (code (terminalHeadWord β) : ℚ) = terminalPrefix ((10 : ℚ) ^ β) := by
  rw [show terminalHeadWord β = true :: markerWord β by rfl, code_cons]
  push_cast
  rw [markerWord_code_eq_marker]
  simp [markerWord, terminalPrefix_eq]
  ring

theorem peeledHead_trichotomy {β : Nat} {letters : List TagLetter}
    (encoded_long : 2 ≤ (tagEncode β letters).length) :
    (∃ tail, letters = .b :: tail ∧ peeledHeadWord β letters = bTag β) ∨
      (∃ tail, letters = .c :: .b :: tail ∧
        peeledHeadWord β letters = terminalHeadWord β) ∨
      ∃ tail fringe, letters = .c :: .c :: tail ∧ fringe.length = β ∧
        peeledHeadWord β letters = true :: true :: fringe := by
  cases letters with
  | nil => simp at encoded_long
  | cons first rest =>
      cases first with
      | b =>
          exact Or.inl ⟨rest, rfl, by
            change
              (bTag β ++ tagEncode β rest ++ markerWord β).take (β + 2) = bTag β
            have tag_length : (bTag β).length = β + 2 := by
              simp [bTag, markerWord]
            rw [← tag_length]
            simp⟩
      | c =>
          cases rest with
          | nil => simp [tagEncode_cons, tagCode] at encoded_long
          | cons second tail =>
              cases second with
              | b =>
                  exact Or.inr <| Or.inl ⟨tail, rfl, by
                    simp [peeledHeadWord, punctuatedUpper, terminalHeadWord,
                      tagEncode_cons, tagCode, markerWord]⟩
              | c =>
                  let fringe :=
                    (tagEncode β tail ++ markerWord β).take β
                  refine Or.inr <| Or.inr ⟨tail, fringe, rfl, ?_, ?_⟩
                  · have continuation_long :
                        β ≤ (tagEncode β tail ++ markerWord β).length := by
                      simp [markerWord]
                      omega
                    simp only [fringe, List.length_take]
                    exact min_eq_left continuation_long
                  · simp [peeledHeadWord, punctuatedUpper, tagEncode_cons, tagCode,
                      fringe]

end MatrixMortality.DecimalSetterDepth
