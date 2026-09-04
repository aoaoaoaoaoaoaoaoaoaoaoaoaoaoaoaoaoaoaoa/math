import MatrixMortality.GuardedMixedPrimeReducedKernel

/-!
# Mixed-prime fork crossing transport

The five-factor affine fork equality says exactly that the toggle action transports the crossing
of `X Y X` with `Y X Y` to the crossing of `X` with `Y`. For physical contractions, these two
crossings lie strictly between the fixed point of the more contracting data action and the toggle
fixed point. This strengthens the three-fixed-point exterior order to a five-point chain.
-/

namespace MatrixMortality.GuardedMixedPrimeFork

open MixedPrimeKernel GuardedMixedPrimeBridge
open BranchingHistory BranchingRecognizer PeriodicHistory TransverseSeparatedForkNoGo

/-- Number of consecutive translations before the first dilation. -/
def leadingTranslateRun : List Letter → ℕ
  | .translate :: tail => (leadingTranslateRun tail).succ
  | _ => 0

/-- Cassaigne's left relation word after a common translation prefix. -/
def prefixedCassaigneLeft (depth : ℕ) : List Letter :=
  List.replicate depth .translate ++ cassaigneLeft

/-- Cassaigne's right relation word after a common translation prefix. -/
def prefixedCassaigneRight (depth : ℕ) : List Letter :=
  List.replicate depth .translate ++ cassaigneRight

theorem leadingTranslateRun_replicate_translate_dilate
    (depth : ℕ) (tail : List Letter) :
    leadingTranslateRun (List.replicate depth .translate ++ .dilate :: tail) = depth := by
  induction depth with
  | zero => rfl
  | succ depth induction => simp [List.replicate_succ, leadingTranslateRun, induction]
@[simp]
theorem leadingTranslateRun_replicate_translate_append
    (depth : ℕ) (word : List Letter) :
    leadingTranslateRun (List.replicate depth .translate ++ word) =
      depth + leadingTranslateRun word := by
  induction depth with
  | zero => simp
  | succ depth induction =>
      simp [List.replicate_succ, leadingTranslateRun, induction]
      omega

/-- The prefixed Cassaigne relation realizes the two-run ambiguity at every translate depth. -/
theorem prefixedCassaigne_leadingTranslateRun (depth : ℕ) :
    leadingTranslateRun (prefixedCassaigneLeft depth) = depth ∧
      leadingTranslateRun (prefixedCassaigneRight depth) = depth + 2 := by
  constructor
  · simp [prefixedCassaigneLeft, cassaigneLeft, leadingTranslateRun]
  · simp [prefixedCassaigneRight, cassaigneRight, leadingTranslateRun]

/-- The prefixed Cassaigne words remain literally distinct. -/
theorem prefixedCassaigne_ne (depth : ℕ) :
    prefixedCassaigneLeft depth ≠ prefixedCassaigneRight depth := by
  intro words_eq
  apply cassaigne_ne
  unfold prefixedCassaigneLeft prefixedCassaigneRight at words_eq
  exact (List.append_right_inj (List.replicate depth .translate)).mp words_eq

/-- At every translation depth, one affine action has physical spellings whose leading
translation runs differ by two. -/
theorem wordAction_prefixedCassaigne (depth : ℕ) (state : ℚ) :
    wordAction (prefixedCassaigneLeft depth) state =
      wordAction (prefixedCassaigneRight depth) state := by
  simp only [prefixedCassaigneLeft, prefixedCassaigneRight, wordAction_append]
  rw [wordAction_cassaigne]

/-- Left endpoint of the fixed-point cylinder selected by a leading translation run. -/
def leadingTranslateFloor (depth : ℕ) : ℚ :=
  5 / 2 * (1 - (3 / 5 : ℚ) ^ depth)

/-- Scale of a translation run followed by the first dilation. -/
def leadingTranslateScale (depth : ℕ) : ℚ :=
  2 / 3 * (3 / 5 : ℚ) ^ depth

theorem wordAction_translateDilatePrefix (depth : ℕ) (state : ℚ) :
    wordAction (List.replicate depth .translate ++ [.dilate]) state =
      leadingTranslateScale depth * state + leadingTranslateFloor depth := by
  induction depth with
  | zero => norm_num [wordAction, action, leadingTranslateScale, leadingTranslateFloor]
  | succ depth induction =>
      rw [List.replicate_succ, List.cons_append]
      simp only [wordAction]
      rw [induction]
      simp only [action, leadingTranslateScale, leadingTranslateFloor, pow_succ]
      ring

theorem wordScale_translateDilatePrefix (depth : ℕ) :
    wordScale (List.replicate depth .translate ++ [.dilate]) =
      leadingTranslateScale depth := by
  simp [wordScale, actionScale, leadingTranslateScale]
  ring

/-- A physical word beginning with `T^depth D` has its fixed point in the corresponding
slope-conditioned cylinder. -/
theorem wordFixedPoint_mem_leadingTranslateCylinder (depth : ℕ) (tail : List Letter) :
    leadingTranslateFloor depth /
          (1 - wordScale (List.replicate depth .translate ++ (.dilate :: tail))) ≤
        wordFixedPoint (List.replicate depth .translate ++ (.dilate :: tail)) ∧
      wordFixedPoint (List.replicate depth .translate ++ (.dilate :: tail)) ≤
        (leadingTranslateFloor depth +
          (5 / 2 : ℚ) * (leadingTranslateScale depth -
            wordScale (List.replicate depth .translate ++ (.dilate :: tail)))) /
          (1 - wordScale (List.replicate depth .translate ++ (.dilate :: tail))) := by
  let headWord : List Letter := List.replicate depth .translate ++ [.dilate]
  let word : List Letter := List.replicate depth .translate ++ (.dilate :: tail)
  change leadingTranslateFloor depth / (1 - wordScale word) ≤ wordFixedPoint word ∧
    wordFixedPoint word ≤
      (leadingTranslateFloor depth +
        (5 / 2 : ℚ) * (leadingTranslateScale depth - wordScale word)) /
          (1 - wordScale word)
  have word_eq : word = headWord ++ tail := by
    simp [word, headWord, List.append_assoc]
  have word_ne : word ≠ [] := by simp [word]
  have scale_lt := wordScale_lt_one_of_ne_nil word word_ne
  have denominator_pos : 0 < 1 - wordScale word := sub_pos.mpr scale_lt
  have fixed := wordAction_wordFixedPoint_of_ne_nil word word_ne
  have tail_zero_bounds :=
    wordAction_mem_fixedPointInterval tail (state := 0) (by norm_num) (by norm_num)
  have tail_top_bounds :=
    wordAction_mem_fixedPointInterval tail (state := 5 / 2) (by norm_num) (by norm_num)
  have zero_lower : leadingTranslateFloor depth ≤ wordAction word 0 := by
    rw [word_eq, wordAction_append, wordAction_translateDilatePrefix]
    have scale_nonneg : 0 ≤ leadingTranslateScale depth := by
      simp only [leadingTranslateScale]
      positivity
    nlinarith
  have top_upper :
      wordAction word (5 / 2) ≤
        leadingTranslateFloor depth + leadingTranslateScale depth * (5 / 2) := by
    rw [word_eq, wordAction_append, wordAction_translateDilatePrefix]
    have scale_nonneg : 0 ≤ leadingTranslateScale depth := by
      simp only [leadingTranslateScale]
      positivity
    nlinarith
  have at_zero := wordAction_sub word (wordFixedPoint word) 0
  have at_top := wordAction_sub word (5 / 2) (wordFixedPoint word)
  rw [fixed] at at_zero at_top
  constructor
  · apply (div_le_iff₀ denominator_pos).2
    norm_num at at_zero
    nlinarith
  · apply (le_div_iff₀ denominator_pos).2
    norm_num at at_top
    nlinarith

/-- Crossing point of the two data actions. -/
def forkCrossingTarget (a b p q : ℚ) : ℚ :=
  ((1 - a) * p - (1 - b) * q) / (b - a)

/-- Crossing point of the palindromic actions `X Y X` and `Y X Y`. -/
def forkCrossingSource (a b p q : ℚ) : ℚ :=
  ((1 - a) * p * (a * b ^ 2 - a * b + b) +
      (1 - b) * q * (-a ^ 2 * b + a * b - a)) / (b - a)

theorem fixedAffineFork_difference_eq_crossing
    (a b c p q r state : ℚ) (scales_ne : a ≠ b) :
    fixedAffine b q
          (fixedAffine c r
            (fixedAffine a p (fixedAffine b q (fixedAffine a p state)))) -
        fixedAffine a p
          (fixedAffine c r
            (fixedAffine b q (fixedAffine a p (fixedAffine b q state)))) =
      (b - a) *
        (fixedAffine c r (forkCrossingSource a b p q) -
          forkCrossingTarget a b p q) := by
  simp only [fixedAffine, forkCrossingSource, forkCrossingTarget]
  field_simp [sub_ne_zero.mpr scales_ne]
  ring

theorem fixedAffineFork_crossing
    (a b c p q r : ℚ) (scales_ne : a ≠ b)
    (actions_eq : ∀ state,
      fixedAffine b q
          (fixedAffine c r
            (fixedAffine a p (fixedAffine b q (fixedAffine a p state)))) =
        fixedAffine a p
          (fixedAffine c r
            (fixedAffine b q (fixedAffine a p (fixedAffine b q state))))) :
    fixedAffine c r (forkCrossingSource a b p q) =
      forkCrossingTarget a b p q := by
  have difference_zero :
      fixedAffine b q
            (fixedAffine c r
              (fixedAffine a p (fixedAffine b q (fixedAffine a p 0)))) -
          fixedAffine a p
            (fixedAffine c r
              (fixedAffine b q (fixedAffine a p (fixedAffine b q 0)))) = 0 := by
    rw [actions_eq 0]
    ring
  rw [fixedAffineFork_difference_eq_crossing _ _ _ _ _ _ _ scales_ne] at difference_zero
  have factor_ne : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm scales_ne)
  exact sub_eq_zero.mp ((mul_eq_zero.mp difference_zero).resolve_left factor_ne)

/-- For unequal data slopes, the five-factor affine fork equality is exactly one crossing
transport equation. -/
theorem fixedAffineFork_eq_iff_crossing
    (a b c p q r : ℚ) (scales_ne : a ≠ b) :
    (∀ state,
      fixedAffine b q
          (fixedAffine c r
            (fixedAffine a p (fixedAffine b q (fixedAffine a p state)))) =
        fixedAffine a p
          (fixedAffine c r
            (fixedAffine b q (fixedAffine a p (fixedAffine b q state))))) ↔
      fixedAffine c r (forkCrossingSource a b p q) =
        forkCrossingTarget a b p q := by
  constructor
  · exact fixedAffineFork_crossing a b c p q r scales_ne
  · intro crossing state
    have difference :=
      fixedAffineFork_difference_eq_crossing a b c p q r state scales_ne
    rw [crossing, sub_self, mul_zero] at difference
    exact sub_eq_zero.mp difference

/-- The toggle word transports the inner crossing to the outer crossing in every word-action
solution of the fork equation. -/
theorem forkActions_crossing
    (x y z : List Letter) (scales_ne : wordScale x ≠ wordScale y)
    (actions_eq : ∀ state,
      wordAction (y ++ z ++ x ++ y ++ x) state =
        wordAction (x ++ z ++ y ++ x ++ y) state) :
    fixedAffine (wordScale z) (wordFixedPoint z)
        (forkCrossingSource (wordScale x) (wordScale y)
          (wordFixedPoint x) (wordFixedPoint y)) =
      forkCrossingTarget (wordScale x) (wordScale y)
        (wordFixedPoint x) (wordFixedPoint y) := by
  apply fixedAffineFork_crossing
    (wordScale x) (wordScale y) (wordScale z)
    (wordFixedPoint x) (wordFixedPoint y) (wordFixedPoint z) scales_ne
  intro state
  have equality := actions_eq state
  simp only [wordAction_append] at equality
  simpa only [wordAction_eq_fixedAffine] using equality

/-- Every exact `bcbc` endpoint code makes its toggle macro transport the palindromic data
crossing to the original data crossing. -/
theorem bcbc_macro_crossing_transport
    (code : PairedControl → List Letter) (source target : ℚ)
    (endpoint_exact : ∀ word,
      wordAction (encodedWord code word) source = target ↔
        pairedCoefficient ℚ 3 bcbcBody (.data .c :: word) = 0) :
    fixedAffine (wordScale (code .toggle)) (wordFixedPoint (code .toggle))
        (forkCrossingSource
          (wordScale (code (.data .b))) (wordScale (code (.data .c)))
          (wordFixedPoint (code (.data .b))) (wordFixedPoint (code (.data .c)))) =
      forkCrossingTarget
        (wordScale (code (.data .b))) (wordScale (code (.data .c)))
        (wordFixedPoint (code (.data .b))) (wordFixedPoint (code (.data .c))) := by
  apply forkActions_crossing
    (code (.data .b)) (code (.data .c)) (code .toggle)
    (bcbc_data_macro_scales_ne code source target endpoint_exact)
  intro state
  simpa [flatForkKernelWord, nestedForkKernelWord] using
    bcbc_reducedFork_actions_eq code source target endpoint_exact state

theorem forkCrossingSource_sub_target
    (a b p q : ℚ) (scales_ne : a ≠ b) :
    forkCrossingSource a b p q - forkCrossingTarget a b p q =
      (1 - a) * (1 - b) * (1 + a * b) * (p - q) / (a - b) := by
  simp only [forkCrossingSource, forkCrossingTarget]
  field_simp [sub_ne_zero.mpr scales_ne]
  ring

theorem forkCrossingTarget_sub_rightFixed
    (a b p q : ℚ) (scales_ne : a ≠ b) :
    forkCrossingTarget a b p q - q =
      (a - 1) * (p - q) / (a - b) := by
  simp only [forkCrossingTarget]
  field_simp [sub_ne_zero.mpr scales_ne]
  ring

theorem forkCrossingTarget_sub_leftFixed
    (a b p q : ℚ) (scales_ne : a ≠ b) :
    forkCrossingTarget a b p q - p =
      (b - 1) * (p - q) / (a - b) := by
  simp only [forkCrossingTarget]
  field_simp [sub_ne_zero.mpr scales_ne]
  ring

theorem forkCrossingSource_between_rightFixed_target
    (a b p q : ℚ) (a_pos : 0 < a) (a_lt : a < 1)
    (b_pos : 0 < b) (b_lt : b < 1) (b_lt_a : b < a) (p_lt_q : p < q) :
    q < forkCrossingSource a b p q ∧
      forkCrossingSource a b p q < forkCrossingTarget a b p q := by
  have scales_ne : a ≠ b := ne_of_gt b_lt_a
  have target_difference := forkCrossingTarget_sub_rightFixed a b p q scales_ne
  have source_difference := forkCrossingSource_sub_target a b p q scales_ne
  have target_gt : q < forkCrossingTarget a b p q := by
    have quotient_pos : 0 < (a - 1) * (p - q) / (a - b) := by
      exact div_pos (mul_pos_of_neg_of_neg (by linarith) (by linarith)) (by linarith)
    linarith
  have coefficient_pos : 0 < (1 - b) * (1 + a * b) := by positivity
  have coefficient_lt : (1 - b) * (1 + a * b) < 1 := by
    nlinarith [mul_pos b_pos (sub_pos.mpr (by nlinarith : 0 < 1 - a + a * b))]
  have source_eq :
      forkCrossingSource a b p q =
        forkCrossingTarget a b p q -
          (1 - b) * (1 + a * b) *
            (forkCrossingTarget a b p q - q) := by
    simp only [forkCrossingSource, forkCrossingTarget]
    field_simp [sub_ne_zero.mpr scales_ne]
    ring
  constructor <;> rw [source_eq] <;> nlinarith

theorem fixedAffine_crossing_forces_fixed_beyond
    (c r source target : ℚ) (c_pos : 0 < c) (c_lt : c < 1)
    (maps : fixedAffine c r source = target) (source_lt_target : source < target) :
    target < r := by
  simp only [fixedAffine] at maps
  nlinarith

theorem fixedAffineFork_chain_of_right_more_contracting
    (a b c p q r : ℚ) (a_pos : 0 < a) (a_lt : a < 1)
    (b_pos : 0 < b) (b_lt : b < 1) (c_pos : 0 < c) (c_lt : c < 1)
    (b_lt_a : b < a) (p_lt_q : p < q)
    (crossing : fixedAffine c r (forkCrossingSource a b p q) =
      forkCrossingTarget a b p q) :
    p < q ∧ q < forkCrossingSource a b p q ∧
      forkCrossingSource a b p q < forkCrossingTarget a b p q ∧
        forkCrossingTarget a b p q < r := by
  have between := forkCrossingSource_between_rightFixed_target
    a b p q a_pos a_lt b_pos b_lt b_lt_a p_lt_q
  have beyond := fixedAffine_crossing_forces_fixed_beyond c r
    (forkCrossingSource a b p q) (forkCrossingTarget a b p q)
    c_pos c_lt crossing between.2
  exact ⟨p_lt_q, between.1, between.2, beyond⟩

theorem forkCrossingTarget_swap (a b p q : ℚ) (scales_ne : a ≠ b) :
    forkCrossingTarget b a q p = forkCrossingTarget a b p q := by
  simp only [forkCrossingTarget]
  field_simp [sub_ne_zero.mpr scales_ne]
  ring

theorem forkCrossingSource_swap (a b p q : ℚ) (scales_ne : a ≠ b) :
    forkCrossingSource b a q p = forkCrossingSource a b p q := by
  simp only [forkCrossingSource]
  field_simp [sub_ne_zero.mpr scales_ne]
  ring

theorem forkCrossingSource_between_target_rightFixed
    (a b p q : ℚ) (a_pos : 0 < a) (a_lt : a < 1)
    (b_pos : 0 < b) (b_lt : b < 1) (b_lt_a : b < a) (q_lt_p : q < p) :
    forkCrossingTarget a b p q < forkCrossingSource a b p q ∧
      forkCrossingSource a b p q < q := by
  have scales_ne : a ≠ b := ne_of_gt b_lt_a
  have target_difference := forkCrossingTarget_sub_rightFixed a b p q scales_ne
  have target_lt : forkCrossingTarget a b p q < q := by
    have quotient_neg : (a - 1) * (p - q) / (a - b) < 0 :=
      div_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos (by linarith) (by linarith)) (by linarith)
    linarith
  have coefficient_pos : 0 < (1 - b) * (1 + a * b) := by positivity
  have coefficient_lt : (1 - b) * (1 + a * b) < 1 := by
    nlinarith [mul_pos b_pos (sub_pos.mpr (by nlinarith : 0 < 1 - a + a * b))]
  have source_eq :
      forkCrossingSource a b p q =
        forkCrossingTarget a b p q -
          (1 - b) * (1 + a * b) *
            (forkCrossingTarget a b p q - q) := by
    simp only [forkCrossingSource, forkCrossingTarget]
    field_simp [sub_ne_zero.mpr scales_ne]
    ring
  constructor <;> rw [source_eq] <;> nlinarith

theorem fixedAffine_crossing_forces_fixed_before
    (c r source target : ℚ) (c_pos : 0 < c) (c_lt : c < 1)
    (maps : fixedAffine c r source = target) (target_lt_source : target < source) :
    r < target := by
  simp only [fixedAffine] at maps
  nlinarith

theorem fixedAffineFork_chain_of_right_more_contracting_reverse
    (a b c p q r : ℚ) (a_pos : 0 < a) (a_lt : a < 1)
    (b_pos : 0 < b) (b_lt : b < 1) (c_pos : 0 < c) (c_lt : c < 1)
    (b_lt_a : b < a) (q_lt_p : q < p)
    (crossing : fixedAffine c r (forkCrossingSource a b p q) =
      forkCrossingTarget a b p q) :
    r < forkCrossingTarget a b p q ∧
      forkCrossingTarget a b p q < forkCrossingSource a b p q ∧
        forkCrossingSource a b p q < q ∧ q < p := by
  have between := forkCrossingSource_between_target_rightFixed
    a b p q a_pos a_lt b_pos b_lt b_lt_a q_lt_p
  have before := fixedAffine_crossing_forces_fixed_before c r
    (forkCrossingSource a b p q) (forkCrossingTarget a b p q)
    c_pos c_lt crossing between.1
  exact ⟨before, between.1, between.2, q_lt_p⟩

/-- Complete order classification of the two data fixed points, the inner and outer crossings,
and the toggle fixed point. -/
theorem fixedAffineFork_crossing_chain
    (a b c p q r : ℚ) (a_pos : 0 < a) (a_lt : a < 1)
    (b_pos : 0 < b) (b_lt : b < 1) (c_pos : 0 < c) (c_lt : c < 1)
    (scales_ne : a ≠ b) (fixed_ne : p ≠ q)
    (crossing : fixedAffine c r (forkCrossingSource a b p q) =
      forkCrossingTarget a b p q) :
    (b < a ∧ p < q ∧ q < forkCrossingSource a b p q ∧
        forkCrossingSource a b p q < forkCrossingTarget a b p q ∧
          forkCrossingTarget a b p q < r) ∨
      (b < a ∧ q < p ∧ r < forkCrossingTarget a b p q ∧
        forkCrossingTarget a b p q < forkCrossingSource a b p q ∧
          forkCrossingSource a b p q < q) ∨
      (a < b ∧ q < p ∧ p < forkCrossingSource a b p q ∧
        forkCrossingSource a b p q < forkCrossingTarget a b p q ∧
          forkCrossingTarget a b p q < r) ∨
      (a < b ∧ p < q ∧ r < forkCrossingTarget a b p q ∧
        forkCrossingTarget a b p q < forkCrossingSource a b p q ∧
          forkCrossingSource a b p q < p) := by
  rcases lt_or_gt_of_ne scales_ne with a_lt_b | b_lt_a
  · have target_swap := forkCrossingTarget_swap a b p q scales_ne
    have source_swap := forkCrossingSource_swap a b p q scales_ne
    have crossing_swap :
        fixedAffine c r (forkCrossingSource b a q p) =
          forkCrossingTarget b a q p := by
      rw [source_swap, target_swap]
      exact crossing
    rcases lt_or_gt_of_ne fixed_ne with p_lt_q | q_lt_p
    · have chain := fixedAffineFork_chain_of_right_more_contracting_reverse
        b a c q p r b_pos b_lt a_pos a_lt c_pos c_lt a_lt_b p_lt_q crossing_swap
      rw [target_swap, source_swap] at chain
      exact Or.inr (Or.inr (Or.inr
        ⟨a_lt_b, p_lt_q, chain.1, chain.2.1, chain.2.2.1⟩))
    · have chain := fixedAffineFork_chain_of_right_more_contracting
        b a c q p r b_pos b_lt a_pos a_lt c_pos c_lt a_lt_b q_lt_p crossing_swap
      rw [source_swap, target_swap] at chain
      exact Or.inr (Or.inr (Or.inl
        ⟨a_lt_b, q_lt_p, chain.2.1, chain.2.2.1, chain.2.2.2⟩))
  · rcases lt_or_gt_of_ne fixed_ne with p_lt_q | q_lt_p
    · have chain := fixedAffineFork_chain_of_right_more_contracting
        a b c p q r a_pos a_lt b_pos b_lt c_pos c_lt b_lt_a p_lt_q crossing
      exact Or.inl ⟨b_lt_a, p_lt_q, chain.2.1, chain.2.2.1, chain.2.2.2⟩
    · have chain := fixedAffineFork_chain_of_right_more_contracting_reverse
        a b c p q r a_pos a_lt b_pos b_lt c_pos c_lt b_lt_a q_lt_p crossing
      exact Or.inr (Or.inl
        ⟨b_lt_a, q_lt_p, chain.1, chain.2.1, chain.2.2.1⟩)

end MatrixMortality.GuardedMixedPrimeFork
