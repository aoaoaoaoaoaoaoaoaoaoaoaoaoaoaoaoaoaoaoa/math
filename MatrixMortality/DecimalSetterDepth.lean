import MatrixMortality.DecimalSetterChamber
import Mathlib.Tactic

/-!
# Recursive decimal setter carrier

An A-shell pole chain admits an exact peeled carrier `t=N/(10μD)`. One transfer replaces its
numerator by `NT−10μGVD`; a following multi-role pole forces exactly `m−1` factors of both two
and five in that residual. Removing them gives the next carrier `(N', EN)`.

The initial carrier comes from a raw encoded-word suffix peel and has a three-way head grammar.
Later numerators are generalized product residuals, not raw encoded heads. The final-digit law
therefore enters a compatible two-cycle rather than closing the induction. The exceptional
upper length two forces only one decimal factor and lies outside that law.
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
  have coefficient_unit :
      HasDecimalShell (E * μ * N) 0 0 := by
    simpa only [zero_add] using (E_unit.mul mu_unit).mul N_unit
  have depths := distinguishedMulti_forces_equal_depth residual_shell coefficient_unit
    G_unit V3_unit T3_shell (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using next_pole)
  rw [depths.1, depths.2] at residual_shell
  exact residual_shell

theorem peeledDenominator_decimalUnit {E N : ℚ}
    (E_unit : HasDecimalShell E 0 0)
    (N_unit : HasDecimalShell N 0 0) :
    HasDecimalShell (E * N) 0 0 := by
  simpa only [zero_add] using E_unit.mul N_unit

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
