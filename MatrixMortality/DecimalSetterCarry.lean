import MatrixMortality.DecimalSetterArithmetic
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic

/-!
# Decimal setter carry

The decimal setter embeds a binary word with digits `1 ↦ 5` and `0 ↦ 7`.
This file isolates the arithmetic used to peel the first malformed transfer from either
projective reset.  The decisive fact is joint rather than separately `2`- or `5`-adic: if a
difference of two encoded words contains exactly `k` factors of two and at least `k` factors
of five, the shorter word must be the complete common suffix. Eliminating one intermediate
denominator further reduces the ordinary depth-two carry to four exact A/B shell gates.
-/

namespace MatrixMortality.DecimalSetterCarry

open MatrixMortality.DecimalSetterArithmetic
open MatrixMortality.PadicValuation

/-! ## Pole-shell balances -/

/-- If the output from the ordinary centered reset is the next block's pole, the source upper
code absorbs the target trace. -/
theorem resetZero_successivePole_identity
    {K : Type*} [Field K] {E G μ A sourceP targetP targetV : K}
    (E_ne : E ≠ 0)
    (next_pole :
      E * targetP * (E * sourceP) =
        G * targetV * (E * (μ * A - sourceP))) :
    sourceP * transferTrace E G targetP targetV = G * μ * A * targetV := by
  apply (mul_left_cancel₀ E_ne)
  unfold transferTrace
  linear_combination next_pole

/-- If the output from the distinguished centered reset is the next block's pole, the source
upper/lower discrepancy absorbs the target trace. -/
theorem resetOne_successivePole_identity
    {K : Type*} [Field K] {E G μ A sourceP sourceV targetP targetV : K}
    (E_ne : E ≠ 0) (G_ne : G ≠ 0)
    (next_pole :
      E * targetP * (E * G * (sourceP - sourceV)) =
        G * targetV * (E * G * (μ * A - sourceP + sourceV))) :
    (sourceP - sourceV) * transferTrace E G targetP targetV =
      G * μ * A * targetV := by
  apply (mul_left_cancel₀ (mul_ne_zero E_ne G_ne))
  unfold transferTrace
  linear_combination next_pole

/-- A pole equation transfers the two decimal valuations from its target trace to the source
factor. The other coefficients are units, so the upper-word length is the entire right-hand
valuation. -/
theorem poleEquation_shellBalance
    {left target E G μ V : ℚ} {m : Nat}
    {leftTwo leftFive targetTwo targetFive : ℤ}
    (left_shell : HasDecimalShell left leftTwo leftFive)
    (target_shell : HasDecimalShell target targetTwo targetFive)
    (E_unit : HasDecimalShell E 0 0)
    (G_unit : HasDecimalShell G 0 0)
    (μ_unit : HasDecimalShell μ 0 0)
    (V_unit : HasDecimalShell V 0 0)
    (pole_equation : left * target = E * G * μ * 10 ^ m * V) :
    leftTwo + targetTwo = m ∧ leftFive + targetFive = m := by
  have scale_shell : HasDecimalShell ((10 : ℚ) ^ m) m m := by
    simpa using ten_hasDecimalShell.pow m
  have left_product_shell := left_shell.mul target_shell
  have right_product_shell :
      HasDecimalShell (E * G * μ * 10 ^ m * V) m m := by
    simpa only [zero_add, add_zero] using
      (((E_unit.mul G_unit).mul μ_unit).mul scale_shell).mul V_unit
  constructor
  · calc
      leftTwo + targetTwo = padicValRat 2 (left * target) :=
        left_product_shell.1.2.symm
      _ = padicValRat 2 (E * G * μ * 10 ^ m * V) := congrArg _ pole_equation
      _ = m := right_product_shell.1.2
  · calc
      leftFive + targetFive = padicValRat 5 (left * target) :=
        left_product_shell.2.2.symm
      _ = padicValRat 5 (E * G * μ * 10 ^ m * V) := congrArg _ pole_equation
      _ = m := right_product_shell.2.2

/-- From the ordinary reset, a multi-role target forces a one-digit source block. -/
theorem resetZero_multiTarget_length
    {source target E G μ V : ℚ} {m : Nat}
    (source_unit : HasDecimalShell source 0 0)
    (target_shell : HasDecimalShell target 1 1)
    (E_unit : HasDecimalShell E 0 0)
    (G_unit : HasDecimalShell G 0 0)
    (μ_unit : HasDecimalShell μ 0 0)
    (V_unit : HasDecimalShell V 0 0)
    (pole_equation : source * target = E * G * μ * 10 ^ m * V) :
    m = 1 := by
  obtain ⟨two_balance, _⟩ :=
    poleEquation_shellBalance source_unit target_shell E_unit G_unit μ_unit V_unit
      pole_equation
  omega

/-- From the ordinary reset, a singleton-erasure target would force two incompatible source
lengths. -/
theorem resetZero_singleTarget_impossible
    {source target E G μ V : ℚ} {β m : Nat}
    (source_unit : HasDecimalShell source 0 0)
    (target_shell : HasDecimalShell target (β + 1) β)
    (E_unit : HasDecimalShell E 0 0)
    (G_unit : HasDecimalShell G 0 0)
    (μ_unit : HasDecimalShell μ 0 0)
    (V_unit : HasDecimalShell V 0 0)
    (pole_equation : source * target = E * G * μ * 10 ^ m * V) :
    False := by
  obtain ⟨two_balance, five_balance⟩ :=
    poleEquation_shellBalance source_unit target_shell E_unit G_unit μ_unit V_unit
      pole_equation
  omega

/-- At the distinguished reset, a multi-role target forces equal `2`- and `5`-depth in the
source discrepancy. -/
theorem resetOne_multiTarget_equalDepth
    {difference target E G μ V : ℚ} {m : Nat} {twoDepth fiveDepth : ℤ}
    (difference_shell : HasDecimalShell difference twoDepth fiveDepth)
    (target_shell : HasDecimalShell target 1 1)
    (E_unit : HasDecimalShell E 0 0)
    (G_unit : HasDecimalShell G 0 0)
    (μ_unit : HasDecimalShell μ 0 0)
    (V_unit : HasDecimalShell V 0 0)
    (pole_equation : difference * target = E * G * μ * 10 ^ m * V) :
    twoDepth = fiveDepth ∧ twoDepth + 1 = m := by
  obtain ⟨two_balance, five_balance⟩ :=
    poleEquation_shellBalance difference_shell target_shell E_unit G_unit μ_unit V_unit
      pole_equation
  omega

/-- At the distinguished reset, a singleton-erasure target forces one additional factor of
five in the source discrepancy. -/
theorem resetOne_singleTarget_depthGap
    {difference target E G μ V : ℚ} {β m : Nat} {twoDepth fiveDepth : ℤ}
    (difference_shell : HasDecimalShell difference twoDepth fiveDepth)
    (target_shell : HasDecimalShell target (β + 1) β)
    (E_unit : HasDecimalShell E 0 0)
    (G_unit : HasDecimalShell G 0 0)
    (μ_unit : HasDecimalShell μ 0 0)
    (V_unit : HasDecimalShell V 0 0)
    (pole_equation : difference * target = E * G * μ * 10 ^ m * V) :
    fiveDepth = twoDepth + 1 ∧ twoDepth + (β + 1) = m := by
  obtain ⟨two_balance, five_balance⟩ :=
    poleEquation_shellBalance difference_shell target_shell E_unit G_unit μ_unit V_unit
      pole_equation
  omega

/-! ## Two-transfer gates -/

private theorem decimalShell_unique
    {value : ℚ} {leftTwo leftFive rightTwo rightFive : ℤ}
    (left : HasDecimalShell value leftTwo leftFive)
    (right : HasDecimalShell value rightTwo rightFive) :
    leftTwo = rightTwo ∧ leftFive = rightFive :=
  ⟨left.1.2.symm.trans right.1.2, left.2.2.symm.trans right.2.2⟩

/-- Backward trace left after eliminating the intermediate projective denominator from two
successive transfers. -/
def twoTransferTrace {R : Type*} [CommRing R]
    (E G μ A₂ T₂ T₃ V₃ : R) : R :=
  T₂ * T₃ - E * μ * G * A₂ * V₃

/-- Exact depth-two elimination. Here `R₁=P₁-V₁Z₀` and
`R₂=P₂-V₂Z₁`; the second hypothesis says that the third block is the next pole. -/
theorem twoTransferTrace_identity
    {R : Type*} [CommRing R]
    {E G μ A₁ A₂ T₂ T₃ V₂ V₃ R₁ R₂ : R}
    (transfer_step :
      E * R₁ * R₂ = T₂ * R₁ - μ * G * V₂ * A₁)
    (next_pole : T₃ * R₂ = G * μ * V₃ * A₂) :
    twoTransferTrace E G μ A₂ T₂ T₃ V₃ * R₁ =
      μ * G * V₂ * A₁ * T₃ := by
  unfold twoTransferTrace
  linear_combination -T₃ * transfer_step + E * R₁ * next_pole

/-- Coordinatewise unequal shells survive the subtraction defining the depth-two backward
trace. -/
theorem twoTransferTrace_shell_of_nonresonant
    {E G μ V₃ T₂ T₃ : ℚ} {m : Nat}
    {T2Two T2Five T3Two T3Five : ℤ}
    (E_unit : HasDecimalShell E 0 0)
    (G_unit : HasDecimalShell G 0 0)
    (mu_unit : HasDecimalShell μ 0 0)
    (V3_unit : HasDecimalShell V₃ 0 0)
    (T2_shell : HasDecimalShell T₂ T2Two T2Five)
    (T3_shell : HasDecimalShell T₃ T3Two T3Five)
    (two_nonresonant : T2Two + T3Two ≠ (m : ℤ))
    (five_nonresonant : T2Five + T3Five ≠ (m : ℤ)) :
    HasDecimalShell
      (twoTransferTrace E G μ (10 ^ m) T₂ T₃ V₃)
      (min (T2Two + T3Two) (m : ℤ))
      (min (T2Five + T3Five) (m : ℤ)) := by
  have trace_product :
      HasDecimalShell (T₂ * T₃) (T2Two + T3Two) (T2Five + T3Five) :=
    T2_shell.mul T3_shell
  have scale_shell : HasDecimalShell ((10 : ℚ) ^ m) m m := by
    simpa using ten_hasDecimalShell.pow m
  have scaled_product :
      HasDecimalShell (E * μ * G * 10 ^ m * V₃) m m := by
    simpa using (((E_unit.mul mu_unit).mul G_unit).mul scale_shell).mul V3_unit
  have two_shell := sub_hasValue_min trace_product.1.1 scaled_product.1.1 (by
    rw [trace_product.1.2, scaled_product.1.2]
    exact two_nonresonant)
  have five_shell := sub_hasValue_min trace_product.2.1 scaled_product.2.1 (by
    rw [trace_product.2.2, scaled_product.2.2]
    exact five_nonresonant)
  rw [trace_product.1.2, scaled_product.1.2] at two_shell
  rw [trace_product.2.2, scaled_product.2.2] at five_shell
  exact ⟨by simpa [twoTransferTrace] using two_shell,
    by simpa [twoTransferTrace] using five_shell⟩

/-- Away from the unique length-two resonance, two consecutive multi-role traces leave a
joint shell equal to the smaller of depths two and `m`. -/
theorem twoTransferTrace_multi_shell
    {E G μ V₃ T₂ T₃ : ℚ} {m : Nat}
    (E_unit : HasDecimalShell E 0 0)
    (G_unit : HasDecimalShell G 0 0)
    (mu_unit : HasDecimalShell μ 0 0)
    (V3_unit : HasDecimalShell V₃ 0 0)
    (T2_shell : HasDecimalShell T₂ 1 1)
    (T3_shell : HasDecimalShell T₃ 1 1)
    (nonresonant : m ≠ 2) :
    HasDecimalShell
      (twoTransferTrace E G μ (10 ^ m) T₂ T₃ V₃)
      (min 2 (m : ℤ)) (min 2 (m : ℤ)) := by
  have valuation_ne : (1 : ℤ) + 1 ≠ (m : ℤ) := by
    exact_mod_cast Ne.symm nonresonant
  simpa using twoTransferTrace_shell_of_nonresonant E_unit G_unit mu_unit V3_unit
    T2_shell T3_shell valuation_ne valuation_ne

/-- At the ordinary reset, a known backward-trace shell must equal the source scale plus the
prospective target shell. -/
theorem ordinaryTwo_shellBalance
    {K μ G V₂ T₃ R₁ : ℚ} {m₁ : Nat}
    {backwardTwo backwardFive targetTwo targetFive : ℤ}
    (K_shell : HasDecimalShell K backwardTwo backwardFive)
    (R1_unit : HasDecimalShell R₁ 0 0)
    (mu_unit : HasDecimalShell μ 0 0)
    (G_unit : HasDecimalShell G 0 0)
    (V2_unit : HasDecimalShell V₂ 0 0)
    (T3_shell : HasDecimalShell T₃ targetTwo targetFive)
    (depth_two_identity : K * R₁ = μ * G * V₂ * 10 ^ m₁ * T₃) :
    backwardTwo = (m₁ : ℤ) + targetTwo ∧
      backwardFive = (m₁ : ℤ) + targetFive := by
  have left_shell : HasDecimalShell (K * R₁) backwardTwo backwardFive := by
    simpa using K_shell.mul R1_unit
  have scale_shell : HasDecimalShell ((10 : ℚ) ^ m₁) m₁ m₁ := by
    simpa using ten_hasDecimalShell.pow m₁
  have right_shell :
      HasDecimalShell (μ * G * V₂ * 10 ^ m₁ * T₃)
        (m₁ + targetTwo) (m₁ + targetFive) := by
    simpa [add_assoc] using
      ((((mu_unit.mul G_unit).mul V2_unit).mul scale_shell).mul T3_shell)
  have transported :
      HasDecimalShell (μ * G * V₂ * 10 ^ m₁ * T₃)
        backwardTwo backwardFive := by
    simpa only [depth_two_identity] using left_shell
  exact decimalShell_unique transported right_shell

/-- From the ordinary reset, a two-transfer multi-shell pole either crosses the unique
length-two resonance in the middle block or begins with the one-digit distinguished block. -/
theorem ordinaryTwoMulti_gate
    {E G μ V₂ V₃ T₂ T₃ R₁ : ℚ} {m₁ m₂ : Nat}
    (E_unit : HasDecimalShell E 0 0)
    (G_unit : HasDecimalShell G 0 0)
    (mu_unit : HasDecimalShell μ 0 0)
    (V2_unit : HasDecimalShell V₂ 0 0)
    (V3_unit : HasDecimalShell V₃ 0 0)
    (R1_unit : HasDecimalShell R₁ 0 0)
    (T2_shell : HasDecimalShell T₂ 1 1)
    (T3_shell : HasDecimalShell T₃ 1 1)
    (middle_length : 2 ≤ m₂)
    (depth_two_identity :
      twoTransferTrace E G μ (10 ^ m₂) T₂ T₃ V₃ * R₁ =
        μ * G * V₂ * 10 ^ m₁ * T₃) :
    m₂ = 2 ∨ m₁ = 1 := by
  by_cases resonant : m₂ = 2
  · exact Or.inl resonant
  · have backward_shell :
        HasDecimalShell
          (twoTransferTrace E G μ (10 ^ m₂) T₂ T₃ V₃) 2 2 := by
      have shell := twoTransferTrace_multi_shell E_unit G_unit mu_unit V3_unit
        T2_shell T3_shell resonant
      simpa [min_eq_left (show (2 : ℤ) ≤ m₂ by exact_mod_cast middle_length)] using shell
    have balance := ordinaryTwo_shellBalance backward_shell R1_unit mu_unit G_unit
      V2_unit T3_shell depth_two_identity
    exact Or.inr (by omega)

/-- An ordinary multi-to-singleton depth-two pole is confined to the prior one-digit reset or
one of the two adjacent singleton-shell resonances. -/
theorem ordinaryTwoMultiToSingleton_gate
    {E G μ V₂ V₃ T₂ T₃ R₁ : ℚ} {m₁ m₂ β : Nat}
    (beta_bound : 3 ≤ β)
    (first_length : 1 ≤ m₁)
    (middle_length : 2 ≤ m₂)
    (E_unit : HasDecimalShell E 0 0)
    (G_unit : HasDecimalShell G 0 0)
    (mu_unit : HasDecimalShell μ 0 0)
    (V2_unit : HasDecimalShell V₂ 0 0)
    (V3_unit : HasDecimalShell V₃ 0 0)
    (R1_unit : HasDecimalShell R₁ 0 0)
    (T2_shell : HasDecimalShell T₂ 1 1)
    (T3_shell : HasDecimalShell T₃ (β + 1) β)
    (depth_two_identity :
      twoTransferTrace E G μ (10 ^ m₂) T₂ T₃ V₃ * R₁ =
        μ * G * V₂ * 10 ^ m₁ * T₃) :
    m₁ = 1 ∨ m₂ = β + 1 ∨ m₂ = β + 2 := by
  have beta_bound_int : (3 : ℤ) ≤ β := by exact_mod_cast beta_bound
  have middle_length_int : (2 : ℤ) ≤ m₂ := by exact_mod_cast middle_length
  by_cases five_resonant : m₂ = β + 1
  · exact Or.inr (Or.inl five_resonant)
  · by_cases two_resonant : m₂ = β + 2
    · exact Or.inr (Or.inr two_resonant)
    · have backward_shell := twoTransferTrace_shell_of_nonresonant (m := m₂) E_unit G_unit
        mu_unit V3_unit T2_shell T3_shell (by omega) (by omega)
      have balance := ordinaryTwo_shellBalance backward_shell R1_unit mu_unit G_unit
        V2_unit T3_shell depth_two_identity
      rcases (show m₂ ≤ β ∨ β + 3 ≤ m₂ by omega) with small | large
      · simp [min_eq_right (show (m₂ : ℤ) ≤ 1 + (β + 1) by omega),
          min_eq_right (show (m₂ : ℤ) ≤ 1 + β by omega)] at balance
        exact False.elim (by omega)
      · simp [min_eq_left (show (1 : ℤ) + (β + 1) ≤ m₂ by omega),
          min_eq_left (show (1 : ℤ) + β ≤ m₂ by omega)] at balance
        exact Or.inl (by omega)

/-- The `5`-adic component of a backward trace remains exact even when its `2`-adic component
is resonant. -/
theorem twoTransferTrace_five_shell_of_nonresonant
    {E G μ V₃ T₂ T₃ : ℚ} {m : Nat}
    {T2Two T2Five T3Two T3Five : ℤ}
    (E_unit : HasDecimalShell E 0 0)
    (G_unit : HasDecimalShell G 0 0)
    (mu_unit : HasDecimalShell μ 0 0)
    (V3_unit : HasDecimalShell V₃ 0 0)
    (T2_shell : HasDecimalShell T₂ T2Two T2Five)
    (T3_shell : HasDecimalShell T₃ T3Two T3Five)
    (five_nonresonant : T2Five + T3Five ≠ (m : ℤ)) :
    HasValue 5
      (twoTransferTrace E G μ (10 ^ m) T₂ T₃ V₃)
      (min (T2Five + T3Five) (m : ℤ)) := by
  have trace_product : HasValue 5 (T₂ * T₃) (T2Five + T3Five) :=
    mul_hasValue T2_shell.2 T3_shell.2
  have scale_shell : HasDecimalShell ((10 : ℚ) ^ m) m m := by
    simpa using ten_hasDecimalShell.pow m
  have scaled_product :
      HasDecimalShell (E * μ * G * 10 ^ m * V₃) m m := by
    simpa using (((E_unit.mul mu_unit).mul G_unit).mul scale_shell).mul V3_unit
  have five_shell := sub_hasValue_min trace_product.1 scaled_product.2.1 (by
    rw [trace_product.2, scaled_product.2.2]
    exact five_nonresonant)
  rw [trace_product.2, scaled_product.2.2] at five_shell
  simpa [twoTransferTrace] using five_shell

/-- If the middle block is a singleton and the target is multi-role, the ordinary branch kills
`D_c` and forces first length `β` for `D_b`. -/
theorem ordinaryTwoSingletonToMulti_gate
    {E G μ V₂ V₃ T₂ T₃ R₁ : ℚ} {m₁ m₂ β : Nat}
    (beta_bound : 3 ≤ β)
    (first_length : 1 ≤ m₁)
    (middle_singleton : m₂ = 1 ∨ m₂ = β + 2)
    (E_unit : HasDecimalShell E 0 0)
    (G_unit : HasDecimalShell G 0 0)
    (mu_unit : HasDecimalShell μ 0 0)
    (V2_unit : HasDecimalShell V₂ 0 0)
    (V3_unit : HasDecimalShell V₃ 0 0)
    (R1_unit : HasDecimalShell R₁ 0 0)
    (T2_shell : HasDecimalShell T₂ (β + 1) β)
    (T3_shell : HasDecimalShell T₃ 1 1)
    (depth_two_identity :
      twoTransferTrace E G μ (10 ^ m₂) T₂ T₃ V₃ * R₁ =
        μ * G * V₂ * 10 ^ m₁ * T₃) :
    m₂ = β + 2 ∧ m₁ = β := by
  rcases middle_singleton with dc | db
  · subst m₂
    have backward_shell :
        HasDecimalShell (twoTransferTrace E G μ 10 T₂ T₃ V₃) 1 1 := by
      have shell := twoTransferTrace_shell_of_nonresonant (m := 1) E_unit G_unit mu_unit
        V3_unit T2_shell T3_shell (by omega) (by omega)
      simpa [min_eq_right (show (1 : ℤ) ≤ (β + 1) + 1 by omega)] using shell
    have balance := ordinaryTwo_shellBalance backward_shell R1_unit mu_unit G_unit
      V2_unit T3_shell depth_two_identity
    exact False.elim (by omega)
  · subst m₂
    have backward_five :
        HasValue 5
          (twoTransferTrace E G μ (10 ^ (β + 2)) T₂ T₃ V₃) (β + 1) := by
      have shell := twoTransferTrace_five_shell_of_nonresonant (m := β + 2)
        E_unit G_unit mu_unit V3_unit T2_shell T3_shell (by omega)
      simpa [min_eq_left (show (β + 1 : ℤ) ≤ β + 2 by omega)] using shell
    have left_five :
        HasValue 5
          (twoTransferTrace E G μ (10 ^ (β + 2)) T₂ T₃ V₃ * R₁)
          (β + 1) := by
      simpa using mul_hasValue backward_five R1_unit.2
    have scale_shell : HasDecimalShell ((10 : ℚ) ^ m₁) m₁ m₁ := by
      simpa using ten_hasDecimalShell.pow m₁
    have right_five :
        HasValue 5 (μ * G * V₂ * 10 ^ m₁ * T₃) (m₁ + 1) := by
      simpa [add_assoc] using
        ((((mu_unit.mul G_unit).mul V2_unit).mul scale_shell).mul T3_shell).2
    have transported :
        HasValue 5 (μ * G * V₂ * 10 ^ m₁ * T₃) (β + 1) := by
      simpa only [depth_two_identity] using left_five
    have balance : (β + 1 : ℤ) = m₁ + 1 :=
      transported.2.symm.trans right_five.2
    exact ⟨rfl, by omega⟩

/-- Two successive singleton shells cannot form an ordinary depth-two pole. -/
theorem ordinaryTwoSingletonToSingleton_impossible
    {E G μ V₂ V₃ T₂ T₃ R₁ : ℚ} {m₁ m₂ β : Nat}
    (beta_bound : 3 ≤ β)
    (first_length : 1 ≤ m₁)
    (middle_singleton : m₂ = 1 ∨ m₂ = β + 2)
    (E_unit : HasDecimalShell E 0 0)
    (G_unit : HasDecimalShell G 0 0)
    (mu_unit : HasDecimalShell μ 0 0)
    (V2_unit : HasDecimalShell V₂ 0 0)
    (V3_unit : HasDecimalShell V₃ 0 0)
    (R1_unit : HasDecimalShell R₁ 0 0)
    (T2_shell : HasDecimalShell T₂ (β + 1) β)
    (T3_shell : HasDecimalShell T₃ (β + 1) β)
    (depth_two_identity :
      twoTransferTrace E G μ (10 ^ m₂) T₂ T₃ V₃ * R₁ =
        μ * G * V₂ * 10 ^ m₁ * T₃) :
    False := by
  rcases middle_singleton with dc | db
  · subst m₂
    have backward_shell :
        HasDecimalShell (twoTransferTrace E G μ 10 T₂ T₃ V₃) 1 1 := by
      have shell := twoTransferTrace_shell_of_nonresonant (m := 1) E_unit G_unit mu_unit
        V3_unit T2_shell T3_shell (by omega) (by omega)
      simpa [min_eq_right (show (1 : ℤ) ≤ (β + 1) + (β + 1) by omega),
        min_eq_right (show (1 : ℤ) ≤ β + β by omega)] using shell
    have balance := ordinaryTwo_shellBalance backward_shell R1_unit mu_unit G_unit
      V2_unit T3_shell depth_two_identity
    omega
  · subst m₂
    have backward_shell :
        HasDecimalShell
          (twoTransferTrace E G μ (10 ^ (β + 2)) T₂ T₃ V₃)
          (β + 2) (β + 2) := by
      have shell := twoTransferTrace_shell_of_nonresonant (m := β + 2)
        E_unit G_unit mu_unit V3_unit T2_shell T3_shell (by omega) (by omega)
      simpa [min_eq_right (show (β + 2 : ℤ) ≤ (β + 1) + (β + 1) by omega),
        min_eq_right (show (β + 2 : ℤ) ≤ β + β by omega)] using shell
    have balance := ordinaryTwo_shellBalance backward_shell R1_unit mu_unit G_unit
      V2_unit T3_shell depth_two_identity
    omega

/-- Decimal digit used for the positive radix-ten binary embedding. -/
def digit : Bool → ℕ
  | false => 7
  | true => 5

/-- Big-endian radix-ten value of a binary word under `1 ↦ 5`, `0 ↦ 7`. -/
def code (word : List Bool) : ℕ :=
  Nat.ofDigits 10 (word.reverse.map digit)

@[simp] theorem digit_false : digit false = 7 := rfl

@[simp] theorem digit_true : digit true = 5 := rfl

private theorem digit_lt_ten (bit : Bool) : digit bit < 10 := by
  cases bit <;> norm_num [digit]

private theorem map_digit_length (word : List Bool) :
    (word.reverse.map digit).length = word.length := by
  simp

@[simp] theorem code_nil : code [] = 0 := rfl

@[simp] theorem code_singleton (bit : Bool) : code [bit] = digit bit := by
  cases bit <;> norm_num [code, digit, Nat.ofDigits]

theorem code_append (head tail : List Bool) :
    code (head ++ tail) = code head * 10 ^ tail.length + code tail := by
  simp only [code, List.reverse_append, List.map_append, Nat.ofDigits_append,
    List.length_map, List.length_reverse]
  ring

theorem code_cons (bit : Bool) (tail : List Bool) :
    code (bit :: tail) = digit bit * 10 ^ tail.length + code tail := by
  simpa only [List.singleton_append, code_singleton] using code_append [bit] tail

theorem code_lt_pow_length (word : List Bool) : code word < 10 ^ word.length := by
  unfold code
  rw [← map_digit_length]
  exact Nat.ofDigits_lt_base_pow_length (by norm_num) fun value member => by
    rw [List.mem_map] at member
    obtain ⟨bit, _, rfl⟩ := member
    exact digit_lt_ten bit

theorem five_mul_pow_length_le_code (bit : Bool) (tail : List Bool) :
    5 * 10 ^ tail.length ≤ code (bit :: tail) := by
  rw [code_cons]
  have digit_lower : 5 ≤ digit bit := by cases bit <;> norm_num [digit]
  exact le_add_right (Nat.mul_le_mul_right (10 ^ tail.length) digit_lower)

theorem code_pos_of_ne_nil {word : List Bool} (word_ne : word ≠ []) : 0 < code word := by
  obtain ⟨bit, tail, rfl⟩ := List.exists_cons_of_ne_nil word_ne
  exact lt_of_lt_of_le (by positivity) (five_mul_pow_length_le_code bit tail)

theorem code_odd_of_ne_nil {word : List Bool} (word_ne : word ≠ []) :
    code word % 2 = 1 := by
  induction word using List.reverseRecOn with
  | nil => exact False.elim (word_ne rfl)
  | append_singleton head bit _ =>
      rw [code_append]
      cases bit <;> simp [digit, Nat.add_mod, Nat.mul_mod]

theorem code_injective : Function.Injective code := by
  intro left right equal
  have digits_roundtrip (word : List Bool) :
      Nat.digits 10 (code word) = word.reverse.map digit := by
    exact Nat.digits_ofDigits 10 (by norm_num) _
      (fun value member => by
        rw [List.mem_map] at member
        obtain ⟨bit, _, rfl⟩ := member
        exact digit_lt_ten bit)
      (fun word_ne => by
        have last_mem := List.getLast_mem word_ne
        rw [List.mem_map] at last_mem
        obtain ⟨bit, _, bit_eq⟩ := last_mem
        rw [← bit_eq]
        cases bit <;> norm_num [digit])
  have reversed_digits_equal :
      left.reverse.map digit = right.reverse.map digit := by
    calc
      left.reverse.map digit = Nat.digits 10 (code left) := (digits_roundtrip left).symm
      _ = Nat.digits 10 (code right) := by rw [equal]
      _ = right.reverse.map digit := digits_roundtrip right
  have reversed_equal : left.reverse = right.reverse := by
    exact (List.map_injective_iff.mpr (by
      intro x y
      cases x <;> cases y <;> simp [digit])) reversed_digits_equal
  simpa using congrArg List.reverse reversed_equal

/-- Prefix left after cutting the last `width` symbols. -/
def front (width : Nat) (word : List Bool) : List Bool :=
  word.take (word.length - width)

/-- Last `width` symbols, or the whole word when it is shorter. -/
def back (width : Nat) (word : List Bool) : List Bool :=
  word.drop (word.length - width)

theorem front_append_back (width : Nat) (word : List Bool) :
    front width word ++ back width word = word := by
  exact List.take_append_drop (word.length - width) word

theorem length_back {width : Nat} {word : List Bool} (width_le : width ≤ word.length) :
    (back width word).length = width := by
  simp [back]
  omega

theorem length_front {width : Nat} {word : List Bool} :
    (front width word).length = word.length - width := by
  simp [front]

private theorem code_mod_pow_back {width : Nat} {word : List Bool}
    (width_le : width ≤ word.length) :
    code word % 10 ^ width = code (back width word) := by
  have decomposition := front_append_back width word
  conv_lhs => rw [← decomposition, code_append, length_back width_le]
  have back_bound : code (back width word) < 10 ^ width := by
    simpa [length_back width_le] using code_lt_pow_length (back width word)
  simp [Nat.add_mod, Nat.mod_eq_of_lt back_bound]

/-- Exact `2`-depth at a shared decimal suffix forces the shorter encoded word to end there.

The `10^width` divisibility supplies a shared suffix.  If both words continued to its left,
their next encoded digits would both be odd, so the remaining difference would be even and
would supply one additional factor of two. -/
theorem suffix_exhaustion
    (punctuated lower : List Bool) (width : Nat)
    (width_pos : 0 < width)
    (punctuated_long : width < punctuated.length)
    (difference_pos : code lower < code punctuated)
    (ten_power_dvd : 10 ^ width ∣ code punctuated - code lower)
    (two_power_exact : ¬2 * 10 ^ width ∣ code punctuated - code lower) :
    lower.length = width ∧ back width punctuated = lower := by
  have lower_width : width ≤ lower.length := by
    by_contra lower_short
    have lower_lt : lower.length < width := by omega
    have modulus_equal : code lower ≡ code punctuated [MOD 10 ^ width] :=
      Nat.modEq_of_dvd' difference_pos.le ten_power_dvd
    change code lower % 10 ^ width = code punctuated % 10 ^ width at modulus_equal
    have lower_bound : code lower < 10 ^ (width - 1) :=
      (code_lt_pow_length lower).trans_le <|
        Nat.pow_le_pow_right (by norm_num : 0 < 10) (by omega)
    have punctuated_back_ne : back width punctuated ≠ [] := by
      have back_length := length_back punctuated_long.le
      exact fun back_nil => by simp [back_nil] at back_length; omega
    obtain ⟨bit, tail, back_eq⟩ := List.exists_cons_of_ne_nil punctuated_back_ne
    have punctuated_lower : 5 * 10 ^ (width - 1) ≤ code (back width punctuated) := by
      rw [back_eq]
      have tail_length : tail.length = width - 1 := by
        have back_length := length_back punctuated_long.le
        simp [back_eq] at back_length
        omega
      simpa [tail_length] using five_mul_pow_length_le_code bit tail
    have lower_mod : code lower % 10 ^ width = code lower := by
      exact Nat.mod_eq_of_lt ((code_lt_pow_length lower).trans_le <|
        Nat.pow_le_pow_right (by norm_num : 0 < 10) lower_lt.le)
    have punctuated_mod := code_mod_pow_back punctuated_long.le
    rw [lower_mod, punctuated_mod] at modulus_equal
    omega
  have suffix_equal : back width punctuated = back width lower := by
    apply code_injective
    have modulus_equal : code lower ≡ code punctuated [MOD 10 ^ width] :=
      Nat.modEq_of_dvd' difference_pos.le ten_power_dvd
    change code lower % 10 ^ width = code punctuated % 10 ^ width at modulus_equal
    simpa [code_mod_pow_back punctuated_long.le, code_mod_pow_back lower_width] using
      modulus_equal.symm
  have lower_not_long : ¬width < lower.length := by
    intro lower_long
    have punctuated_front_ne : front width punctuated ≠ [] := by
      have front_length := length_front (width := width) (word := punctuated)
      exact fun front_nil => by simp [front_nil] at front_length; omega
    have lower_front_ne : front width lower ≠ [] := by
      have front_length := length_front (width := width) (word := lower)
      exact fun front_nil => by simp [front_nil] at front_length; omega
    have punctuated_decomposition := front_append_back width punctuated
    have lower_decomposition := front_append_back width lower
    have punctuated_code :
        code punctuated =
          code (front width punctuated) * 10 ^ width + code (back width punctuated) := by
      conv_lhs => rw [← punctuated_decomposition, code_append, length_back punctuated_long.le]
    have lower_code :
        code lower = code (front width lower) * 10 ^ width + code (back width lower) := by
      conv_lhs => rw [← lower_decomposition, code_append, length_back lower_long.le]
    have front_order : code (front width lower) < code (front width punctuated) := by
      by_contra order_not
      have reverse_order :
          code (front width punctuated) ≤ code (front width lower) := by omega
      have scaled_order := Nat.mul_le_mul_right (10 ^ width) reverse_order
      rw [suffix_equal] at punctuated_code
      omega
    have front_mod :
        code (front width lower) ≡ code (front width punctuated) [MOD 2] := by
      rw [Nat.ModEq, code_odd_of_ne_nil lower_front_ne,
        code_odd_of_ne_nil punctuated_front_ne]
    have two_dvd_front :
        2 ∣ code (front width punctuated) - code (front width lower) :=
      front_mod.dvd'
    have difference_factor :
        code punctuated - code lower =
          10 ^ width *
            (code (front width punctuated) - code (front width lower)) := by
      calc
        code punctuated - code lower =
            (code (front width punctuated) * 10 ^ width + code (back width lower)) -
              (code (front width lower) * 10 ^ width + code (back width lower)) := by
                rw [punctuated_code, lower_code, suffix_equal]
        _ = code (front width punctuated) * 10 ^ width -
              code (front width lower) * 10 ^ width := Nat.add_sub_add_right _ _ _
        _ = (code (front width punctuated) - code (front width lower)) *
              10 ^ width := by rw [Nat.sub_mul]
        _ = 10 ^ width *
              (code (front width punctuated) - code (front width lower)) := mul_comm _ _
    have forbidden_divides :
        2 * 10 ^ width ∣ code punctuated - code lower := by
      obtain ⟨quotient, quotient_eq⟩ := two_dvd_front
      refine ⟨quotient, ?_⟩
      rw [difference_factor, quotient_eq]
      ring
    exact two_power_exact forbidden_divides
  have lower_length : lower.length = width := by omega
  have lower_back : back width lower = lower := by
    simp [back, lower_length]
  exact ⟨lower_length, by simpa [lower_back] using suffix_equal⟩

/-- The exhausted suffix factors the entire positive discrepancy by the corresponding decimal
power, leaving exactly the unmatched punctuated prefix. -/
theorem suffix_exhaustion_factorization
    (punctuated lower : List Bool) (width : Nat)
    (width_pos : 0 < width)
    (punctuated_long : width < punctuated.length)
    (difference_pos : code lower < code punctuated)
    (ten_power_dvd : 10 ^ width ∣ code punctuated - code lower)
    (two_power_exact : ¬2 * 10 ^ width ∣ code punctuated - code lower) :
    lower.length = width ∧
      back width punctuated = lower ∧
      code punctuated - code lower = code (front width punctuated) * 10 ^ width := by
  obtain ⟨lower_length, suffix_equal⟩ :=
    suffix_exhaustion punctuated lower width width_pos punctuated_long difference_pos
      ten_power_dvd two_power_exact
  have decomposition := front_append_back width punctuated
  have punctuated_code :
      code punctuated =
        code (front width punctuated) * 10 ^ width + code lower := by
    conv_lhs => rw [← decomposition, code_append, length_back punctuated_long.le]
    rw [suffix_equal]
  refine ⟨lower_length, suffix_equal, ?_⟩
  rw [punctuated_code]
  exact Nat.add_sub_cancel_right _ _

/-! ## Prefix intervals -/

/-- Decimal marker value `(52ρ-7)/9`. -/
def marker (ρ : ℚ) : ℚ := (52 * ρ - 7) / 9

/-- Integral denominator of the decimal setter's projective shift. -/
def gap (ρ : ℚ) : ℚ := 9 * (2 * ρ - 7)

/-- Integral numerator of the decimal setter's projective shift. -/
def lift (ρ : ℚ) : ℚ := 502 * ρ - 7

/-- Pole forced by a suffix-exhausted upper prefix `head`. -/
def forcedPole (ρ head : ℚ) : ℚ :=
  lift ρ * (10 * marker ρ - head) / (gap ρ * head)

/-- Prefix `11 0^β`, the exact boundary between terminal and false targets. -/
def terminalPrefix (ρ : ℚ) : ℚ := lift ρ / 9

/-- Largest prefix beginning with at least two `c` letters. -/
def doubleCPrefix (ρ : ℚ) : ℚ := (2501 * ρ - 35) / 45

theorem lift_add_gap (ρ : ℚ) : lift ρ + gap ρ = 90 * marker ρ := by
  simp [lift, gap, marker]
  ring

theorem terminalPrefix_eq (ρ : ℚ) :
    terminalPrefix ρ = marker ρ + 50 * ρ := by
  simp [terminalPrefix, marker, lift]
  ring

theorem forcedPole_terminalPrefix {ρ : ℚ}
    (gap_ne : gap ρ ≠ 0) (lift_ne : lift ρ ≠ 0) :
    forcedPole ρ (terminalPrefix ρ) = 1 := by
  unfold forcedPole terminalPrefix marker
  field_simp [gap_ne, lift_ne]
  simp [lift, gap]
  ring

private theorem decimal_constants_bounds {ρ : ℚ} (rho_bound : 1000 ≤ ρ) :
    0 < gap ρ ∧ 0 < lift ρ ∧
      27 < lift ρ / gap ρ ∧ lift ρ / gap ρ < 30 ∧
      5 * ρ < marker ρ ∧ marker ρ < 6 * ρ := by
  have gap_pos : 0 < gap ρ := by
    simp [gap]
    linarith
  have lift_pos : 0 < lift ρ := by
    simp [lift]
    linarith
  have ratio_lower : 27 < lift ρ / gap ρ := by
    rw [lt_div_iff₀ gap_pos]
    simp [lift, gap]
    linarith
  have ratio_upper : lift ρ / gap ρ < 30 := by
    rw [div_lt_iff₀ gap_pos]
    simp [lift, gap]
    linarith
  have marker_lower : 5 * ρ < marker ρ := by
    simp [marker]
    linarith
  have marker_upper : marker ρ < 6 * ρ := by
    simp [marker]
    linarith
  exact ⟨gap_pos, lift_pos, ratio_lower, ratio_upper, marker_lower, marker_upper⟩

theorem forcedPole_doubleC_lower {ρ head : ℚ}
    (rho_bound : 1000 ≤ ρ)
    (head_pos : 0 < head)
    (head_upper : head ≤ doubleCPrefix ρ) :
    58 / 55 < forcedPole ρ head := by
  obtain ⟨gap_pos, lift_pos, ratio_lower, _, _, _⟩ :=
    decimal_constants_bounds rho_bound
  have double_pos : 0 < doubleCPrefix ρ := by
    simp [doubleCPrefix]
    linarith
  have boundary_gap : 0 < 10 * marker ρ - doubleCPrefix ρ := by
    simp [marker, doubleCPrefix]
    linarith
  have quotient_mono :
      (10 * marker ρ - doubleCPrefix ρ) / doubleCPrefix ρ ≤
        (10 * marker ρ - head) / head := by
    rw [div_le_div_iff₀ double_pos head_pos]
    nlinarith
  have exact_corner :
      58 / 55 <
        (lift ρ / gap ρ) *
          ((10 * marker ρ - doubleCPrefix ρ) / doubleCPrefix ρ) := by
    rw [show lift ρ / gap ρ *
          ((10 * marker ρ - doubleCPrefix ρ) / doubleCPrefix ρ) =
        lift ρ * (10 * marker ρ - doubleCPrefix ρ) /
          (gap ρ * doubleCPrefix ρ) by ring]
    rw [lt_div_iff₀ (mul_pos gap_pos double_pos)]
    simp [lift, gap, marker, doubleCPrefix]
    nlinarith
  have ratio_nonneg : 0 ≤ lift ρ / gap ρ := (div_pos lift_pos gap_pos).le
  have monotone_product := mul_le_mul_of_nonneg_left quotient_mono ratio_nonneg
  unfold forcedPole
  rw [show lift ρ * (10 * marker ρ - head) / (gap ρ * head) =
    (lift ρ / gap ρ) * ((10 * marker ρ - head) / head) by ring]
  exact exact_corner.trans_le monotone_product

theorem forcedPole_upper {ρ head : ℚ}
    (rho_bound : 1000 ≤ ρ)
    (head_lower : 50 * ρ ≤ head)
    (head_upper : head < 10 * marker ρ) :
    forcedPole ρ head < 6 := by
  obtain ⟨gap_pos, lift_pos, _, ratio_upper, _, marker_upper⟩ :=
    decimal_constants_bounds rho_bound
  have rho_pos : 0 < ρ := lt_of_lt_of_le (by norm_num) rho_bound
  have head_pos : 0 < head := lt_of_lt_of_le (mul_pos (by norm_num) rho_pos) head_lower
  have boundary_pos : 0 < 10 * marker ρ - head := sub_pos.mpr head_upper
  have gap_ratio :
      (10 * marker ρ - head) / head < 1 / 5 := by
    rw [div_lt_iff₀ head_pos]
    nlinarith
  have ratio_pos : 0 < lift ρ / gap ρ := div_pos lift_pos gap_pos
  unfold forcedPole
  rw [show lift ρ * (10 * marker ρ - head) / (gap ρ * head) =
    (lift ρ / gap ρ) * ((10 * marker ρ - head) / head) by ring]
  nlinarith [mul_lt_mul_of_pos_left gap_ratio ratio_pos,
    mul_lt_mul_of_pos_right ratio_upper (by norm_num : 0 < (1 / 5 : ℚ))]

/-- Equal-length decimal words with target prefixes `57/55` have ratio below `58/55`. -/
theorem targetPrefix_ratio_lt
    {P V scale : ℚ}
    (scale_pos : 0 < scale)
    (P_upper : P < 58 * scale)
    (V_lower : 55 * scale ≤ V) :
    P / V < 58 / 55 := by
  have V_pos : 0 < V := lt_of_lt_of_le (mul_pos (by norm_num) scale_pos) V_lower
  rw [div_lt_iff₀ V_pos]
  nlinarith

/-- Every singleton erasure pole lies above six throughout the emitted range. -/
theorem singletonPole_gt_six {ρ P : ℚ}
    (rho_bound : 1000 ≤ ρ)
    (P_lower : terminalPrefix ρ ≤ P) :
    6 < P / 7 := by
  rw [lt_div_iff₀ (by norm_num : (0 : ℚ) < 7)]
  have lift_lower : 378 < lift ρ := by
    simp [lift]
    linarith
  have terminal_lower : 42 < terminalPrefix ρ := by
    simp [terminalPrefix]
    linarith
  linarith

/-- A prefix in the double-`c` chamber cannot induce an equal-length `5/7` target pole. -/
theorem forcedPole_ne_prefixTarget
    {ρ head P V scale : ℚ}
    (rho_bound : 1000 ≤ ρ)
    (head_pos : 0 < head)
    (head_upper : head ≤ doubleCPrefix ρ)
    (scale_pos : 0 < scale)
    (P_upper : P < 58 * scale)
    (V_lower : 55 * scale ≤ V) :
    forcedPole ρ head ≠ P / V := by
  have forced_lower := forcedPole_doubleC_lower rho_bound head_pos head_upper
  have target_upper := targetPrefix_ratio_lt scale_pos P_upper V_lower
  exact ne_of_gt (target_upper.trans forced_lower)

/-- A rescaled unmatched prefix in the emitted interval cannot induce either singleton-erasure
pole. -/
theorem forcedPole_ne_singletonTarget
    {ρ head P : ℚ}
    (rho_bound : 1000 ≤ ρ)
    (head_lower : 50 * ρ ≤ head)
    (head_upper : head < 10 * marker ρ)
    (P_lower : terminalPrefix ρ ≤ P) :
    forcedPole ρ head ≠ P / 7 := by
  have forced_upper := forcedPole_upper rho_bound head_lower head_upper
  have target_lower := singletonPole_gt_six rho_bound P_lower
  exact ne_of_lt (forced_upper.trans_le target_lower.le)

end MatrixMortality.DecimalSetterCarry
