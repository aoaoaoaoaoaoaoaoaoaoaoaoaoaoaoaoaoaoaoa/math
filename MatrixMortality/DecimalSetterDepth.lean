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
two-cycle. At the initial raw two-`c` head, an exact mixed-prime suffix split excludes every
all-`D_c` block of upper length at least three; this cut does not recur for generalized carriers.
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

theorem tagPrefix_shape (β width : Nat) (letters : List TagLetter)
    (width_pos : 1 ≤ width) (width_le : width ≤ β) :
    ∃ ones, 1 ≤ ones ∧ ones ≤ width ∧
      (tagEncode β letters ++ markerWord β).take width =
        List.replicate ones true ++ List.replicate (width - ones) false := by
  induction width generalizing letters with
  | zero => omega
  | succ width ih =>
      cases width with
      | zero =>
          refine ⟨1, by omega, by omega, ?_⟩
          cases letters with
          | nil => simp [markerWord]
          | cons letter tail => cases letter <;> simp [tagEncode_cons, tagCode]
      | succ width =>
          cases letters with
          | nil =>
              refine ⟨1, by omega, by omega, ?_⟩
              simp [markerWord]
              omega
          | cons letter tail =>
              cases letter with
              | b =>
                  refine ⟨1, by omega, by omega, ?_⟩
                  simp [tagEncode_cons, tagCode]
                  have remaining_le : width + 1 ≤ β := by omega
                  rw [List.take_append_of_le_length (by simpa using remaining_le)]
                  simp
                  omega
              | c =>
                  obtain ⟨ones, ones_pos, ones_le, prefix_eq⟩ :=
                    ih tail (by omega) (by omega)
                  refine ⟨ones + 1, by omega, by omega, ?_⟩
                  simp only [tagEncode_cons, tagCode,
                    List.cons_append, List.take_succ_cons, List.replicate_succ,
                    List.cons.injEq, true_and]
                  change List.take (width + 1) (tagEncode β tail ++ markerWord β) = _
                  rw [prefix_eq]
                  rw [show width + 1 + 1 - (ones + 1) = width + 1 - ones by omega]

theorem peeledDoubleCHead_shape {β : Nat} (tail : List TagLetter) (β_pos : 1 ≤ β) :
    ∃ ones, 1 ≤ ones ∧ ones ≤ β ∧
      peeledHeadWord β (.c :: .c :: tail) =
        List.replicate (ones + 2) true ++ List.replicate (β - ones) false := by
  obtain ⟨ones, ones_pos, ones_le, prefix_eq⟩ :=
    tagPrefix_shape β β tail β_pos le_rfl
  refine ⟨ones, ones_pos, ones_le, ?_⟩
  change (true :: true :: (tagEncode β tail ++ markerWord β)).take (β + 2) = _
  change true :: true :: (tagEncode β tail ++ markerWord β).take β = _
  rw [prefix_eq]
  rw [show ones + 2 = 2 + ones by omega, List.replicate_add]
  rfl

private theorem repeatedTrue_code_identity (width : Nat) :
    9 * code (List.replicate width true) + 5 = 5 * 10 ^ width := by
  induction width with
  | zero => norm_num
  | succ width induction =>
      rw [List.replicate_succ, code_cons, digit_true, List.length_replicate,
        pow_succ]
      omega

private theorem repeatedTrue_code_divisible_five (width : Nat) :
    5 ∣ code (List.replicate width true) := by
  induction width with
  | zero => simp
  | succ width induction =>
      rw [List.replicate_succ, code_cons, digit_true, List.length_replicate]
      exact dvd_add (dvd_mul_right 5 _) induction

private theorem repeatedTrue_not_decimalUnit {width : Nat} (width_pos : 1 ≤ width) :
    ¬HasDecimalShell (code (List.replicate width true) : ℚ) 0 0 := by
  intro shell
  have code_ne : code (List.replicate width true) ≠ 0 := by
    apply Nat.ne_of_gt
    exact code_pos_of_ne_nil (by simp; omega)
  have valuation_pos : 0 < padicValNat 5 (code (List.replicate width true)) :=
    one_le_padicValNat_of_dvd code_ne (repeatedTrue_code_divisible_five width)
  have valuation_zero : padicValNat 5 (code (List.replicate width true)) = 0 := by
    exact_mod_cast shell.2.2
  omega

private theorem rawHead_code_identity (ones suffix : Nat) :
    9 * (code
        (List.replicate (ones + 2) true ++ List.replicate suffix false) : ℤ) =
      5 * 10 ^ (ones + 2 + suffix) + 2 * 10 ^ suffix - 7 := by
  have true_identity :
      9 * (code (List.replicate (ones + 2) true) : ℤ) + 5 =
        5 * 10 ^ (ones + 2) := by
    exact_mod_cast repeatedTrue_code_identity (ones + 2)
  have false_identity :
      9 * (code (List.replicate suffix false) : ℤ) + 7 =
        7 * 10 ^ suffix := by
    exact_mod_cast replicateFalse_code_identity suffix
  rw [code_append, List.length_replicate]
  push_cast
  rw [show ones + 2 + suffix = (ones + 2) + suffix by rfl, pow_add]
  linear_combination (10 : ℤ) ^ suffix * true_identity + false_identity

/-- Every decimal-unit two-`c` raw head has a nonempty final run of sevens. -/
theorem peeledDoubleCHead_unit_shape {β : Nat} (tail : List TagLetter)
    (β_pos : 1 ≤ β)
    (head_unit :
      HasDecimalShell (code (peeledHeadWord β (.c :: .c :: tail)) : ℚ) 0 0) :
    ∃ suffix, 1 ≤ suffix ∧ suffix ≤ β - 1 ∧
      peeledHeadWord β (.c :: .c :: tail) =
        List.replicate (β + 2 - suffix) true ++ List.replicate suffix false ∧
      9 * (code (peeledHeadWord β (.c :: .c :: tail)) : ℤ) =
        5 * 10 ^ (β + 2) + 2 * 10 ^ suffix - 7 := by
  obtain ⟨ones, ones_pos, ones_le, head_shape⟩ :=
    peeledDoubleCHead_shape tail β_pos
  let suffix := β - ones
  have suffix_le : suffix ≤ β - 1 := by
    dsimp [suffix]
    omega
  have first_length : β + 2 - suffix = ones + 2 := by
    dsimp [suffix]
    omega
  have total_length : ones + 2 + suffix = β + 2 := by
    dsimp [suffix]
    omega
  have suffix_pos : 1 ≤ suffix := by
    by_contra suffix_not_pos
    have suffix_zero : suffix = 0 := by omega
    have ones_eq : ones = β := by
      dsimp [suffix] at suffix_zero
      omega
    have all_true :
        peeledHeadWord β (.c :: .c :: tail) =
          List.replicate (β + 2) true := by
      rw [head_shape, ones_eq]
      simp
    rw [all_true] at head_unit
    exact repeatedTrue_not_decimalUnit (by omega) head_unit
  refine ⟨suffix, suffix_pos, suffix_le, ?_, ?_⟩
  · simpa [first_length] using head_shape
  · rw [head_shape]
    rw [show β - ones = suffix by rfl]
    simpa [total_length] using rawHead_code_identity ones suffix

private theorem primePower_dvd_int_of_hasValue
    {prime : Nat} [Fact prime.Prime] {value : ℤ} {depth : Nat}
  (shell : HasValue prime (value : ℚ) depth) :
    (prime : ℤ) ^ depth ∣ value := by
  have valuation_eq : padicValInt prime value = depth := by
    have valuation_rat := shell.2
    rw [padicValRat.of_int] at valuation_rat
    exact_mod_cast valuation_rat
  exact (padicValInt_dvd_iff depth value).mpr (Or.inr (by omega))

private theorem nextPrimePower_not_dvd_int_of_hasValue
    {prime : Nat} [Fact prime.Prime] {value : ℤ} {depth : Nat}
    (shell : HasValue prime (value : ℚ) depth) :
    ¬(prime : ℤ) ^ (depth + 1) ∣ value := by
  intro divides
  have valuation_eq : padicValInt prime value = depth := by
    have valuation_rat := shell.2
    rw [padicValRat.of_int] at valuation_rat
    exact_mod_cast valuation_rat
  have bound := (padicValInt_dvd_iff (depth + 1) value).mp divides
  have value_ne : value ≠ 0 := by exact_mod_cast shell.1
  have depth_bound := bound.resolve_left value_ne
  omega

theorem rawHead_linear_factor
    {β s : Nat} {H : ℤ} (suffix_bound : s ≤ β + 2)
    (head_eq : 9 * H = 5 * 10 ^ (β + 2) + 2 * 10 ^ s - 7) :
    441 * H + 343 =
      10 ^ s * (245 * 10 ^ (β + 2 - s) + 98) := by
  have exponent_eq : β + 2 = s + (β + 2 - s) := by omega
  rw [exponent_eq, pow_add] at head_eq
  linear_combination 49 * head_eq

theorem allCDeletion_residual_decomposition
    {ρ q H μ E G P V T R : ℤ}
    (mu_eq : 9 * μ = 52 * ρ - 7)
    (gap_eq : E = 18 * ρ - 63)
    (lift_eq : G = 502 * ρ - 7)
    (upper_eq : 9 * P = 50 * ρ * q + 2 * ρ - 7)
    (lower_eq : 9 * V = 7 * q - 7)
    (trace_eq : T = E * P + G * V)
    (residual_eq : R = H * T - 10 * μ * G * V) :
    81 * R = 10 * (441 * H + 343) +
      q * (8100 * H * ρ ^ 2 + 3276 * H * ρ - 441 * H -
        1827280 * ρ ^ 2 + 271460 * ρ - 3430) +
      ρ * (324 * H * ρ - 33894 * H + 1827280 * ρ - 271460) := by
  rw [residual_eq, trace_eq]
  calc
    81 * (H * (E * P + G * V) - 10 * μ * G * V) =
        9 * H * (E * (9 * P) + G * (9 * V)) -
          10 * (9 * μ) * G * (9 * V) := by ring
    _ = _ := by rw [mu_eq, gap_eq, lift_eq, upper_eq, lower_eq]; ring

private theorem primePower_dvd_tenPower
    {prime exponent power : Nat} (prime_dvd_ten : (prime : ℤ) ∣ 10)
    (exponent_le : exponent ≤ power) :
    (prime : ℤ) ^ exponent ∣ 10 ^ power :=
  (pow_dvd_pow (prime : ℤ) exponent_le).trans
    (pow_dvd_pow_of_dvd prime_dvd_ten power)

theorem regularHead_decimalShell_impossible
    {β s n : Nat} {R A B K : ℤ}
    (n_pos : 1 ≤ n) (suffix_below : s + 2 ≤ β)
    (K_even : (2 : ℤ) ∣ K) (K_five_unit : ¬(5 : ℤ) ∣ K)
    (decomposition :
      81 * R = 10 ^ (s + 1) * K + 10 ^ n * A + 10 ^ β * B)
    (shell : HasDecimalShell (R : ℚ)
      ((n - 1 : Nat) : ℤ) ((n - 1 : Nat) : ℤ)) :
    False := by
  have two_not : ¬(2 : ℤ) ^ n ∣ R := by
    have exact := nextPrimePower_not_dvd_int_of_hasValue shell.1
    simpa [Nat.sub_add_cancel n_pos] using exact
  have five_dvd : (5 : ℤ) ^ (n - 1) ∣ R :=
    primePower_dvd_int_of_hasValue shell.2
  rcases (show n ≤ s + 1 ∨ n = s + 2 ∨ s + 3 ≤ n by omega) with
    shallow | boundary | deep
  · apply two_not
    have first_dvd : (2 : ℤ) ^ n ∣ 10 ^ (s + 1) * K :=
      dvd_mul_of_dvd_left
        (primePower_dvd_tenPower (prime := 2) (by norm_num) shallow) K
    have second_dvd : (2 : ℤ) ^ n ∣ 10 ^ n * A :=
      dvd_mul_of_dvd_left
        (primePower_dvd_tenPower (prime := 2) (by norm_num) le_rfl) A
    have third_dvd : (2 : ℤ) ^ n ∣ 10 ^ β * B :=
      dvd_mul_of_dvd_left
        (primePower_dvd_tenPower (prime := 2) (by norm_num) (by omega)) B
    have product_dvd : (2 : ℤ) ^ n ∣ 81 * R := by
      rw [decomposition]
      exact dvd_add (dvd_add first_dvd second_dvd) third_dvd
    have coprime : IsCoprime ((2 : ℤ) ^ n) 81 :=
      (by norm_num : IsCoprime (2 : ℤ) 81).pow_left
    exact coprime.dvd_of_dvd_mul_left product_dvd
  · subst n
    apply two_not
    have first_power : (2 : ℤ) ^ (s + 2) ∣ 10 ^ (s + 1) * 2 := by
      rw [show s + 2 = (s + 1) + 1 by omega, pow_add]
      exact mul_dvd_mul
        (primePower_dvd_tenPower (prime := 2) (by norm_num) le_rfl)
        (dvd_refl 2)
    have first_dvd : (2 : ℤ) ^ (s + 2) ∣ 10 ^ (s + 1) * K := by
      obtain ⟨quotient, quotient_eq⟩ := K_even
      rw [quotient_eq, ← mul_assoc]
      exact dvd_mul_of_dvd_left first_power quotient
    have second_dvd : (2 : ℤ) ^ (s + 2) ∣ 10 ^ (s + 2) * A :=
      dvd_mul_of_dvd_left
        (primePower_dvd_tenPower (prime := 2) (by norm_num) le_rfl) A
    have third_dvd : (2 : ℤ) ^ (s + 2) ∣ 10 ^ β * B :=
      dvd_mul_of_dvd_left
        (primePower_dvd_tenPower (prime := 2) (by norm_num) suffix_below) B
    have product_dvd : (2 : ℤ) ^ (s + 2) ∣ 81 * R := by
      rw [decomposition]
      exact dvd_add (dvd_add first_dvd second_dvd) third_dvd
    have coprime : IsCoprime ((2 : ℤ) ^ (s + 2)) 81 :=
      (by norm_num : IsCoprime (2 : ℤ) 81).pow_left
    exact coprime.dvd_of_dvd_mul_left product_dvd
  · have required_dvd : (5 : ℤ) ^ (s + 2) ∣ R := by
      exact (pow_dvd_pow (5 : ℤ) (by omega)).trans five_dvd
    have product_dvd : (5 : ℤ) ^ (s + 2) ∣ 81 * R :=
      dvd_mul_of_dvd_right required_dvd 81
    have second_dvd : (5 : ℤ) ^ (s + 2) ∣ 10 ^ n * A :=
      dvd_mul_of_dvd_left
        (primePower_dvd_tenPower (prime := 5) (by norm_num) (by omega)) A
    have third_dvd : (5 : ℤ) ^ (s + 2) ∣ 10 ^ β * B :=
      dvd_mul_of_dvd_left
        (primePower_dvd_tenPower (prime := 5) (by norm_num) suffix_below) B
    have first_dvd : (5 : ℤ) ^ (s + 2) ∣ 10 ^ (s + 1) * K := by
      have error_dvd : (5 : ℤ) ^ (s + 2) ∣ 10 ^ n * A + 10 ^ β * B :=
        dvd_add second_dvd third_dvd
      rw [decomposition] at product_dvd
      simpa [add_assoc] using dvd_sub product_dvd error_dvd
    have cancelled : (5 : ℤ) ∣ K := by
      have ten_power : (10 : ℤ) ^ (s + 1) =
          (5 : ℤ) ^ (s + 1) * (2 : ℤ) ^ (s + 1) := by
        rw [show (10 : ℤ) = 5 * 2 by norm_num, mul_pow]
      rw [ten_power, pow_succ, mul_assoc] at first_dvd
      have rearranged : (5 : ℤ) ^ (s + 1) * 5 ∣
          (5 : ℤ) ^ (s + 1) * ((2 : ℤ) ^ (s + 1) * K) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using first_dvd
      have power_ne : (5 : ℤ) ^ (s + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
      have five_dvd_scaled : (5 : ℤ) ∣ (2 : ℤ) ^ (s + 1) * K :=
        (mul_dvd_mul_iff_left power_ne).mp rearranged
      have coprime : IsCoprime (5 : ℤ) ((2 : ℤ) ^ (s + 1)) :=
        (by norm_num : IsCoprime (5 : ℤ) 2).pow_right
      exact coprime.dvd_of_dvd_mul_left five_dvd_scaled
    exact K_five_unit cancelled

theorem allCDeletion_regularRawHead_shell_impossible
    {β s n : Nat} {H μ E G P V T R : ℤ}
    (n_large : 3 ≤ n) (suffix_below : s + 2 ≤ β)
    (head_eq : 9 * H = 5 * 10 ^ (β + 2) + 2 * 10 ^ s - 7)
    (mu_eq : 9 * μ = 52 * 10 ^ β - 7)
    (gap_eq : E = 18 * 10 ^ β - 63)
    (lift_eq : G = 502 * 10 ^ β - 7)
    (upper_eq : 9 * P = 50 * 10 ^ β * 10 ^ n + 2 * 10 ^ β - 7)
    (lower_eq : 9 * V = 7 * 10 ^ n - 7)
    (trace_eq : T = E * P + G * V)
    (residual_eq : R = H * T - 10 * μ * G * V)
    (shell : HasDecimalShell (R : ℚ)
      ((n - 1 : Nat) : ℤ) ((n - 1 : Nat) : ℤ)) :
    False := by
  let K : ℤ := 245 * 10 ^ (β + 2 - s) + 98
  let A : ℤ :=
    8100 * H * (10 : ℤ) ^ (β + β) + 3276 * H * 10 ^ β - 441 * H -
      1827280 * 10 ^ (β + β) + 271460 * 10 ^ β - 3430
  let B : ℤ :=
    324 * H * 10 ^ β - 33894 * H + 1827280 * 10 ^ β - 271460
  have suffix_bound : s ≤ β + 2 := by omega
  have head_factor := rawHead_linear_factor suffix_bound head_eq
  have decomposition := allCDeletion_residual_decomposition
    (ρ := (10 : ℤ) ^ β) (q := (10 : ℤ) ^ n)
    mu_eq gap_eq lift_eq upper_eq lower_eq trace_eq residual_eq
  have decomposition' :
      81 * R = 10 ^ (s + 1) * K + 10 ^ n * A + 10 ^ β * B := by
    rw [head_factor] at decomposition
    dsimp [K, A, B]
    rw [pow_two, ← pow_add] at decomposition
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using decomposition
  have exponent_pos : 1 ≤ β + 2 - s := by omega
  have K_even : (2 : ℤ) ∣ K := by
    have power_even : (2 : ℤ) ∣ 10 ^ (β + 2 - s) :=
      primePower_dvd_tenPower (prime := 2) (by norm_num) exponent_pos
    have first_even : (2 : ℤ) ∣ 245 * 10 ^ (β + 2 - s) :=
      dvd_mul_of_dvd_right power_even 245
    have last_even : (2 : ℤ) ∣ 98 := by norm_num
    exact dvd_add first_even last_even
  have K_five_unit : ¬(5 : ℤ) ∣ K := by
    intro K_five
    have first_five : (5 : ℤ) ∣ 245 * 10 ^ (β + 2 - s) :=
      dvd_mul_of_dvd_left (by norm_num) _
    have impossible : (5 : ℤ) ∣ 98 := by
      dsimp [K] at K_five
      simpa using dvd_sub K_five first_five
    norm_num at impossible
  exact regularHead_decimalShell_impossible (by omega) suffix_below
    K_even K_five_unit decomposition' shell

theorem exceptionalHead_decimalShell_impossible
    {β n : Nat} {R A B : ℤ}
    (n_pos : 1 ≤ n) (B_five_unit : ¬(5 : ℤ) ∣ B)
    (decomposition :
      45 * R = 10 ^ n * A + 10 ^ (2 * β) * B)
    (shell : HasDecimalShell (R : ℚ)
      ((n - 1 : Nat) : ℤ) ((n - 1 : Nat) : ℤ)) :
    False := by
  have two_not : ¬(2 : ℤ) ^ n ∣ R := by
    have exact := nextPrimePower_not_dvd_int_of_hasValue shell.1
    simpa [Nat.sub_add_cancel n_pos] using exact
  have five_dvd : (5 : ℤ) ^ (n - 1) ∣ R :=
    primePower_dvd_int_of_hasValue shell.2
  by_cases shallow : n ≤ 2 * β
  · apply two_not
    have first_dvd : (2 : ℤ) ^ n ∣ 10 ^ n * A :=
      dvd_mul_of_dvd_left
        (primePower_dvd_tenPower (prime := 2) (by norm_num) le_rfl) A
    have second_dvd : (2 : ℤ) ^ n ∣ 10 ^ (2 * β) * B :=
      dvd_mul_of_dvd_left
        (primePower_dvd_tenPower (prime := 2) (by norm_num) shallow) B
    have product_dvd : (2 : ℤ) ^ n ∣ 45 * R := by
      rw [decomposition]
      exact dvd_add first_dvd second_dvd
    have coprime : IsCoprime ((2 : ℤ) ^ n) 45 :=
      (by norm_num : IsCoprime (2 : ℤ) 45).pow_left
    exact coprime.dvd_of_dvd_mul_left product_dvd
  · have exponent_le : 2 * β ≤ n - 1 := by omega
    have required_dvd : (5 : ℤ) ^ (2 * β) ∣ R :=
      (pow_dvd_pow (5 : ℤ) exponent_le).trans five_dvd
    have product_dvd : (5 : ℤ) ^ (2 * β + 1) ∣ 45 * R := by
      rw [show 45 = (5 : ℤ) * 9 by norm_num, show 2 * β + 1 = 1 + 2 * β by omega,
        pow_add]
      have raw := dvd_mul_of_dvd_left (mul_dvd_mul (dvd_refl 5) required_dvd) 9
      simpa [mul_assoc, mul_left_comm, mul_comm] using raw
    have first_dvd : (5 : ℤ) ^ (2 * β + 1) ∣ 10 ^ n * A :=
      dvd_mul_of_dvd_left
        (primePower_dvd_tenPower (prime := 5) (by norm_num) (by omega)) A
    have second_dvd : (5 : ℤ) ^ (2 * β + 1) ∣ 10 ^ (2 * β) * B := by
      rw [decomposition] at product_dvd
      simpa using dvd_sub product_dvd first_dvd
    have ten_power : (10 : ℤ) ^ (2 * β) =
        (5 : ℤ) ^ (2 * β) * (2 : ℤ) ^ (2 * β) := by
      rw [show (10 : ℤ) = 5 * 2 by norm_num, mul_pow]
    rw [ten_power, pow_succ, mul_assoc] at second_dvd
    have rearranged : (5 : ℤ) ^ (2 * β) * 5 ∣
        (5 : ℤ) ^ (2 * β) * ((2 : ℤ) ^ (2 * β) * B) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using second_dvd
    have power_ne : (5 : ℤ) ^ (2 * β) ≠ 0 := pow_ne_zero _ (by norm_num)
    have five_dvd_scaled : (5 : ℤ) ∣ (2 : ℤ) ^ (2 * β) * B :=
      (mul_dvd_mul_iff_left power_ne).mp rearranged
    have coprime : IsCoprime (5 : ℤ) ((2 : ℤ) ^ (2 * β)) :=
      (by norm_num : IsCoprime (5 : ℤ) 2).pow_right
    exact B_five_unit (coprime.dvd_of_dvd_mul_left five_dvd_scaled)

theorem allCDeletion_firstRawHead_residual_decomposition
    {ρ q a H μ E G P V T R : ℤ}
    (rho_eq : ρ = 10 * a)
    (head_eq : 9 * H = 500 * ρ + 2 * a - 7)
    (mu_eq : 9 * μ = 52 * ρ - 7)
    (gap_eq : E = 18 * ρ - 63)
    (lift_eq : G = 502 * ρ - 7)
    (upper_eq : 9 * P = 50 * ρ * q + 2 * ρ - 7)
    (lower_eq : 9 * V = 7 * q - 7)
    (trace_eq : T = E * P + G * V)
    (residual_eq : R = H * T - 10 * μ * G * V) :
    45 * R =
      q * (250100 * ρ ^ 3 - 917504 * ρ ^ 2 + 135779 * ρ - 1715) +
      ρ ^ 2 * (10004 * ρ - 31514) := by
  have decomposition := allCDeletion_residual_decomposition
    mu_eq gap_eq lift_eq upper_eq lower_eq trace_eq residual_eq
  subst ρ
  have head_zero : 9 * H - 5002 * a + 7 = 0 := by
    linear_combination head_eq
  have scaled :
      9 * (q *
          (250100 * (10 * a) ^ 3 - 917504 * (10 * a) ^ 2 +
            135779 * (10 * a) - 1715) +
        (10 * a) ^ 2 * (10004 * (10 * a) - 31514)) =
        5 * (81 * R) := by
    let C : ℤ :=
      90000 * a ^ 2 * q + 3600 * a ^ 2 + 3640 * a * q -
        37660 * a - 49 * q + 490
    have difference_zero :
      9 * (q *
          (250100 * (10 * a) ^ 3 - 917504 * (10 * a) ^ 2 +
            135779 * (10 * a) - 1715) +
        (10 * a) ^ 2 * (10004 * (10 * a) - 31514)) -
          5 * (81 * R) = 0 := by
      calc
        9 * (q *
            (250100 * (10 * a) ^ 3 - 917504 * (10 * a) ^ 2 +
              135779 * (10 * a) - 1715) +
          (10 * a) ^ 2 * (10004 * (10 * a) - 31514)) -
            5 * (81 * R) = -5 * C * (9 * H - 5002 * a + 7) := by
            rw [decomposition]
            dsimp [C]
            ring
        _ = 0 := by rw [head_zero]; ring
    exact sub_eq_zero.mp difference_zero
  have cancelled : 45 * R =
      q * (250100 * (10 * a) ^ 3 - 917504 * (10 * a) ^ 2 +
        135779 * (10 * a) - 1715) +
      (10 * a) ^ 2 * (10004 * (10 * a) - 31514) := by
    apply mul_left_cancel₀ (show (9 : ℤ) ≠ 0 by norm_num)
    calc
      9 * (45 * R) = 5 * (81 * R) := by ring
      _ = _ := scaled.symm
  exact cancelled

theorem allCDeletion_firstRawHead_shell_impossible
    {β n : Nat} {H μ E G P V T R : ℤ}
    (β_large : 2 ≤ β) (n_large : 3 ≤ n)
    (head_eq :
      9 * H = 5 * 10 ^ (β + 2) + 2 * 10 ^ (β - 1) - 7)
    (mu_eq : 9 * μ = 52 * 10 ^ β - 7)
    (gap_eq : E = 18 * 10 ^ β - 63)
    (lift_eq : G = 502 * 10 ^ β - 7)
    (upper_eq : 9 * P = 50 * 10 ^ β * 10 ^ n + 2 * 10 ^ β - 7)
    (lower_eq : 9 * V = 7 * 10 ^ n - 7)
    (trace_eq : T = E * P + G * V)
    (residual_eq : R = H * T - 10 * μ * G * V)
    (shell : HasDecimalShell (R : ℚ)
      ((n - 1 : Nat) : ℤ) ((n - 1 : Nat) : ℤ)) :
    False := by
  let ρ : ℤ := 10 ^ β
  let a : ℤ := 10 ^ (β - 1)
  let A : ℤ := 250100 * ρ ^ 3 - 917504 * ρ ^ 2 + 135779 * ρ - 1715
  let B : ℤ := 10004 * ρ - 31514
  have exponent_eq : β = (β - 1) + 1 := by omega
  have rho_eq : ρ = 10 * a := by
    dsimp [ρ, a]
    calc
      (10 : ℤ) ^ β = 10 ^ ((β - 1) + 1) := congrArg _ exponent_eq
      _ = 10 ^ (β - 1) * 10 := pow_succ _ _
      _ = 10 * 10 ^ (β - 1) := mul_comm _ _
  have head_eq' : 9 * H = 500 * ρ + 2 * a - 7 := by
    calc
      9 * H = 5 * 10 ^ (β + 2) + 2 * 10 ^ (β - 1) - 7 := head_eq
      _ = 500 * ρ + 2 * a - 7 := by
        dsimp [ρ, a]
        rw [pow_add]
        norm_num
        ring
  have decomposition := allCDeletion_firstRawHead_residual_decomposition
    rho_eq head_eq' mu_eq gap_eq lift_eq upper_eq lower_eq trace_eq residual_eq
  have decomposition' : 45 * R = 10 ^ n * A + 10 ^ (2 * β) * B := by
    have scale_eq : (10 : ℤ) ^ (2 * β) = ρ ^ 2 := by
      dsimp [ρ]
      rw [two_mul, pow_add, pow_two]
    rw [scale_eq]
    simpa [A, B, mul_assoc, mul_left_comm, mul_comm] using decomposition
  have B_five_unit : ¬(5 : ℤ) ∣ B := by
    intro B_five
    have first_five : (5 : ℤ) ∣ 10004 * ρ := by
      apply dvd_mul_of_dvd_right
      dsimp [ρ]
      exact primePower_dvd_tenPower (prime := 5) (exponent := 1) (power := β)
        (by norm_num) (by omega)
    have impossible : (5 : ℤ) ∣ 31514 := by
      dsimp [B] at B_five
      simpa using dvd_sub first_five B_five
    norm_num at impossible
  exact exceptionalHead_decimalShell_impossible (by omega)
    B_five_unit decomposition' shell

/-- No all-`D_c` block of length at least three can follow a lawful decimal-unit two-`c`
raw head and land on another multi-role pole. -/
theorem allCDeletion_peeledDoubleCHead_shell_impossible
    {β n : Nat} (tail : List TagLetter) {μ E G P V T R : ℤ}
    (β_large : 2 ≤ β) (n_large : 3 ≤ n)
    (head_unit :
      HasDecimalShell (code (peeledHeadWord β (.c :: .c :: tail)) : ℚ) 0 0)
    (mu_eq : 9 * μ = 52 * 10 ^ β - 7)
    (gap_eq : E = 18 * 10 ^ β - 63)
    (lift_eq : G = 502 * 10 ^ β - 7)
    (upper_eq : 9 * P = 50 * 10 ^ β * 10 ^ n + 2 * 10 ^ β - 7)
    (lower_eq : 9 * V = 7 * 10 ^ n - 7)
    (trace_eq : T = E * P + G * V)
    (residual_eq :
      R = (code (peeledHeadWord β (.c :: .c :: tail)) : ℤ) * T -
        10 * μ * G * V)
    (shell : HasDecimalShell (R : ℚ)
      ((n - 1 : Nat) : ℤ) ((n - 1 : Nat) : ℤ)) :
    False := by
  obtain ⟨suffix, suffix_pos, suffix_le, _, head_eq⟩ :=
    peeledDoubleCHead_unit_shape tail (by omega) head_unit
  rcases lt_or_eq_of_le suffix_le with suffix_below | first_head
  · exact allCDeletion_regularRawHead_shell_impossible n_large (by omega) head_eq
      mu_eq gap_eq lift_eq upper_eq lower_eq trace_eq residual_eq shell
  · rw [first_head] at head_eq
    exact allCDeletion_firstRawHead_shell_impossible β_large n_large head_eq
      mu_eq gap_eq lift_eq upper_eq lower_eq trace_eq residual_eq shell

end MatrixMortality.DecimalSetterDepth
