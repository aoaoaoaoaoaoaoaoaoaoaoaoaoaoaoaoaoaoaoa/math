import MatrixMortality.GuardedMixedPrimeLiteralNoGo

/-!
# Reduced mixed-prime fork kernel

Every raw mixed-prime word acts bijectively on `ℚ`. The common macro prefix and suffix surrounding
the flat/nested fork collision can therefore be cancelled at the action level. Exact `bcbc`
endpoint semantics forces the reduced words `y z x y x` and `x z y x y` to be distinct while
inducing one affine map. Their exact raw length is `2|x|+2|y|+|z|`.
-/

namespace MatrixMortality.GuardedMixedPrimeFork

open MixedPrimeKernel GuardedMixedPrimeBridge
open BranchingHistory BranchingRecognizer PeriodicHistory TransverseSeparatedForkNoGo

theorem action_surjective (letter : Letter) : Function.Surjective (action letter) := by
  intro target
  cases letter with
  | dilate =>
      refine ⟨3 / 2 * target, ?_⟩
      norm_num [action]
      ring
  | translate =>
      refine ⟨5 / 3 * (target - 1), ?_⟩
      norm_num [action]
      ring

theorem wordAction_surjective (word : List Letter) : Function.Surjective (wordAction word) := by
  induction word with
  | nil => exact Function.surjective_id
  | cons letter word induction =>
      intro target
      obtain ⟨middle, middle_eq⟩ := action_surjective letter target
      obtain ⟨source, source_eq⟩ := induction middle
      exact ⟨source, by simp only [wordAction, source_eq, middle_eq]⟩

/-- Equality of two mixed-prime actions in one fixed two-sided context implies equality before
the context is attached. -/
theorem wordAction_cancel_context
    (before left right after : List Letter)
    (context_eq : ∀ state,
      wordAction (before ++ left ++ after) state =
        wordAction (before ++ right ++ after) state) :
    ∀ state, wordAction left state = wordAction right state := by
  intro state
  obtain ⟨source, source_eq⟩ := wordAction_surjective after state
  apply wordAction_injective before
  have contextual := context_eq source
  simpa only [wordAction_append, source_eq] using contextual

/-- Reduced flat-fork word after cancelling the common macro context. -/
def flatForkKernelWord (code : PairedControl → List Letter) : List Letter :=
  code (.data .c) ++ code .toggle ++ code (.data .b) ++
    code (.data .c) ++ code (.data .b)

/-- Reduced nested-fork word after cancelling the common macro context. -/
def nestedForkKernelWord (code : PairedControl → List Letter) : List Letter :=
  code (.data .b) ++ code .toggle ++ code (.data .c) ++
    code (.data .b) ++ code (.data .c)

private def forkContextPrefix (code : PairedControl → List Letter) : List Letter :=
  code (.data .b) ++ code .toggle ++ code (.data .b) ++ code (.data .b)

private def forkContextSuffix (code : PairedControl → List Letter) : List Letter :=
  code .toggle ++ code (.data .b) ++ code (.data .b) ++ code (.data .c) ++
    code .toggle ++ code (.data .b) ++ code (.data .c)

private theorem encodedWord_flatForkControl_eq_context
    (code : PairedControl → List Letter) :
    encodedWord code flatForkControl =
      forkContextPrefix code ++ flatForkKernelWord code ++ forkContextSuffix code := by
  simp [encodedWord, flatForkControl, forkContextPrefix, flatForkKernelWord, forkContextSuffix,
    historyControl, strokeControl, flatBlock, strokeBBB, strokeCBC, stroke₃,
    List.append_assoc]

private theorem encodedWord_nestedForkControl_eq_context
    (code : PairedControl → List Letter) :
    encodedWord code nestedForkControl =
      forkContextPrefix code ++ nestedForkKernelWord code ++ forkContextSuffix code := by
  simp [encodedWord, nestedForkControl, forkContextPrefix, nestedForkKernelWord, forkContextSuffix,
    historyControl, strokeControl, nestedBlock, strokeBBB, strokeBCB, strokeCBB, strokeCBC,
    stroke₃, List.append_assoc]

/-- Exact endpoint semantics identifies the two reduced fork actions after cancelling their
common bijective macro context. -/
theorem bcbc_reducedFork_actions_eq
    (code : PairedControl → List Letter) (source target : ℚ)
    (endpoint_exact : ∀ word,
      wordAction (encodedWord code word) source = target ↔
        pairedCoefficient ℚ 3 bcbcBody (.data .c :: word) = 0) :
    ∀ state,
      wordAction (flatForkKernelWord code) state =
        wordAction (nestedForkKernelWord code) state := by
  apply wordAction_cancel_context
    (forkContextPrefix code) (flatForkKernelWord code) (nestedForkKernelWord code)
      (forkContextSuffix code)
  intro state
  rw [← encodedWord_flatForkControl_eq_context,
    ← encodedWord_nestedForkControl_eq_context]
  exact bcbc_fork_macro_actions_eq code source target endpoint_exact state

/-- Exact endpoint semantics makes the reduced fork words literally distinct. -/
theorem bcbc_reducedFork_words_ne
    (code : PairedControl → List Letter) (source target : ℚ)
    (endpoint_exact : ∀ word,
      wordAction (encodedWord code word) source = target ↔
        pairedCoefficient ℚ 3 bcbcBody (.data .c :: word) = 0) :
    flatForkKernelWord code ≠ nestedForkKernelWord code := by
  intro reduced_eq
  apply no_bcbc_literal_fork_words code source target endpoint_exact
  rw [encodedWord_flatForkControl_eq_context, encodedWord_nestedForkControl_eq_context,
    reduced_eq]

/-- Both reduced fork words have raw length `2|κ(b)|+2|κ(c)|+|κ(toggle)|`. -/
theorem bcbc_reducedFork_length (code : PairedControl → List Letter) :
    (flatForkKernelWord code).length =
        2 * (code (.data .b)).length + 2 * (code (.data .c)).length +
          (code .toggle).length ∧
      (nestedForkKernelWord code).length =
        2 * (code (.data .b)).length + 2 * (code (.data .c)).length +
          (code .toggle).length := by
  simp [flatForkKernelWord, nestedForkKernelWord]
  omega

/-- Every exact endpoint code supplies a genuine reduced mixed-prime kernel pair. -/
theorem bcbc_reducedFork_genuine_kernel
    (code : PairedControl → List Letter) (source target : ℚ)
    (endpoint_exact : ∀ word,
      wordAction (encodedWord code word) source = target ↔
        pairedCoefficient ℚ 3 bcbcBody (.data .c :: word) = 0) :
    flatForkKernelWord code ≠ nestedForkKernelWord code ∧
      ∀ state,
        wordAction (flatForkKernelWord code) state =
          wordAction (nestedForkKernelWord code) state :=
  ⟨bcbc_reducedFork_words_ne code source target endpoint_exact,
    bcbc_reducedFork_actions_eq code source target endpoint_exact⟩

/-- Affine map written by its slope and fixed point. -/
def fixedAffine (slope fixed state : ℚ) : ℚ :=
  slope * state + (1 - slope) * fixed

theorem wordAction_eq_fixedAffine (word : List Letter) (state : ℚ) :
    wordAction word state = fixedAffine (wordScale word) (wordFixedPoint word) state := by
  by_cases word_ne : word ≠ []
  · have fixed := wordAction_wordFixedPoint_of_ne_nil word word_ne
    have difference := wordAction_sub word state (wordFixedPoint word)
    rw [fixed] at difference
    simp only [fixedAffine]
    linarith
  · have word_eq : word = [] := not_ne_iff.mp word_ne
    simp [word_eq, wordAction, wordScale, wordFixedPoint, fixedAffine]

/-- Every mixed-prime word preserves the closed interval between the generator fixed points. -/
theorem wordAction_mem_fixedPointInterval (word : List Letter) {state : ℚ}
    (state_nonneg : 0 ≤ state) (state_le : state ≤ 5 / 2) :
    0 ≤ wordAction word state ∧ wordAction word state ≤ 5 / 2 := by
  induction word generalizing state with
  | nil => exact ⟨state_nonneg, state_le⟩
  | cons letter word induction =>
      have tail_bounds := induction state_nonneg state_le
      cases letter <;> norm_num [wordAction, action] <;> constructor <;> nlinarith

/-- The fixed point of every nonempty mixed-prime word lies in `[0,5/2]`. -/
theorem wordFixedPoint_mem_interval (word : List Letter) (word_ne : word ≠ []) :
    0 ≤ wordFixedPoint word ∧ wordFixedPoint word ≤ 5 / 2 := by
  have scale_lt := wordScale_lt_one_of_ne_nil word word_ne
  have denominator_pos : 0 < 1 - wordScale word := sub_pos.mpr scale_lt
  have zero_bounds :=
    wordAction_mem_fixedPointInterval word (state := 0) (by norm_num) (by norm_num)
  have top_bounds :=
    wordAction_mem_fixedPointInterval word (state := 5 / 2) (by norm_num) (by norm_num)
  have difference := wordAction_sub word (5 / 2) 0
  constructor
  · rw [wordFixedPoint]
    exact div_nonneg zero_bounds.1 denominator_pos.le
  · rw [wordFixedPoint]
    apply (div_le_iff₀ denominator_pos).2
    norm_num at difference
    nlinarith

/-- Coefficient of the data-fixed-point difference in the affine fork equation. -/
def forkFixedCoefficient (a b c : ℚ) : ℚ :=
  (1 - a) * (a * b ^ 2 * c - a * b * c + b * c - 1)

/-- Weight of the data-`b` fixed point in the balanced fork equation. -/
def forkLeftWeight (a b c : ℚ) : ℚ :=
  (1 - a) * (1 - b * c * (1 - a * (1 - b)))

/-- Weight of the data-`c` fixed point in the balanced fork equation. -/
def forkRightWeight (a b c : ℚ) : ℚ :=
  (1 - b) * (1 - a * c * (1 - b * (1 - a)))

theorem forkRightWeight_sub_leftWeight (a b c : ℚ) :
    forkRightWeight a b c - forkLeftWeight a b c = (a - b) * (1 - c) := by
  simp only [forkLeftWeight, forkRightWeight]
  ring

/-- Exact scalar difference between the two five-factor affine fork composites. -/
theorem fixedAffineFork_difference
    (a b c p q r state : ℚ) :
    fixedAffine b q
          (fixedAffine c r
            (fixedAffine a p (fixedAffine b q (fixedAffine a p state)))) -
        fixedAffine a p
          (fixedAffine c r
            (fixedAffine b q (fixedAffine a p (fixedAffine b q state)))) =
      forkFixedCoefficient a b c * (p - q) +
        (a - b) * (c - 1) * (r - q) := by
  simp only [fixedAffine, forkFixedCoefficient]
  ring

/-- Macro actions satisfying the reduced fork equation obey one exact fixed-point relation. -/
theorem forkActions_fixedPoint_equation
    (x y z : List Letter) (actions_eq : ∀ state,
      wordAction (y ++ z ++ x ++ y ++ x) state =
        wordAction (x ++ z ++ y ++ x ++ y) state) :
    forkFixedCoefficient (wordScale x) (wordScale y) (wordScale z) *
          (wordFixedPoint x - wordFixedPoint y) +
        (wordScale x - wordScale y) * (wordScale z - 1) *
          (wordFixedPoint z - wordFixedPoint y) = 0 := by
  have equality := actions_eq 0
  simp only [wordAction_append] at equality
  simp_rw [wordAction_eq_fixedAffine x, wordAction_eq_fixedAffine y,
    wordAction_eq_fixedAffine z] at equality
  calc
    forkFixedCoefficient (wordScale x) (wordScale y) (wordScale z) *
          (wordFixedPoint x - wordFixedPoint y) +
        (wordScale x - wordScale y) * (wordScale z - 1) *
          (wordFixedPoint z - wordFixedPoint y) =
        fixedAffine (wordScale y) (wordFixedPoint y)
              (fixedAffine (wordScale z) (wordFixedPoint z)
                (fixedAffine (wordScale x) (wordFixedPoint x)
                  (fixedAffine (wordScale y) (wordFixedPoint y)
                    (fixedAffine (wordScale x) (wordFixedPoint x) 0)))) -
          fixedAffine (wordScale x) (wordFixedPoint x)
              (fixedAffine (wordScale z) (wordFixedPoint z)
                (fixedAffine (wordScale y) (wordFixedPoint y)
                  (fixedAffine (wordScale x) (wordFixedPoint x)
                    (fixedAffine (wordScale y) (wordFixedPoint y) 0)))) := by
          rw [fixedAffineFork_difference]
    _ = 0 := sub_eq_zero.mpr equality

/-- Symmetric balance form of the exact fixed-point equation. -/
theorem forkActions_fixedPoint_balance
    (x y z : List Letter) (actions_eq : ∀ state,
      wordAction (y ++ z ++ x ++ y ++ x) state =
        wordAction (x ++ z ++ y ++ x ++ y) state) :
    forkLeftWeight (wordScale x) (wordScale y) (wordScale z) *
        (wordFixedPoint x - wordFixedPoint z) =
      forkRightWeight (wordScale x) (wordScale y) (wordScale z) *
        (wordFixedPoint y - wordFixedPoint z) := by
  have equation := forkActions_fixedPoint_equation x y z actions_eq
  simp only [forkFixedCoefficient, forkLeftWeight, forkRightWeight] at equation ⊢
  nlinarith

theorem forkFixedCoefficient_neg
    {a b c : ℚ} (a_pos : 0 < a) (a_lt : a < 1)
    (b_pos : 0 < b) (b_lt : b < 1) (c_pos : 0 < c) (c_le : c ≤ 1) :
    forkFixedCoefficient a b c < 0 := by
  have abc_pos : 0 < a * b * c := mul_pos (mul_pos a_pos b_pos) c_pos
  have first_neg : a * b * c * (b - 1) < 0 :=
    mul_neg_of_pos_of_neg abc_pos (sub_neg.mpr b_lt)
  have bc_lt : b * c < 1 := by
    calc
      b * c < 1 * c := mul_lt_mul_of_pos_right b_lt c_pos
      _ = c := one_mul c
      _ ≤ 1 := c_le
  have inner_neg : a * b ^ 2 * c - a * b * c + b * c - 1 < 0 := by
    calc
      a * b ^ 2 * c - a * b * c + b * c - 1 =
          a * b * c * (b - 1) + (b * c - 1) := by ring
      _ < 0 := add_neg first_neg (sub_neg.mpr bc_lt)
  exact mul_neg_of_pos_of_neg (sub_pos.mpr a_lt) inner_neg

private theorem forkInnerLeft_pos
    {a b c : ℚ} (a_pos : 0 < a) (a_lt : a < 1)
    (b_pos : 0 < b) (b_lt : b < 1) (c_pos : 0 < c) (c_lt : c < 1) :
    0 < 1 - b * c * (1 - a * (1 - b)) := by
  have one_sub_b_pos : 0 < 1 - b := sub_pos.mpr b_lt
  have a_one_sub_b_pos : 0 < a * (1 - b) := mul_pos a_pos one_sub_b_pos
  have a_one_sub_b_lt : a * (1 - b) < 1 := by nlinarith
  have factor_pos : 0 < 1 - a * (1 - b) := sub_pos.mpr a_one_sub_b_lt
  have factor_lt : 1 - a * (1 - b) < 1 := by linarith
  have bc_lt : b * c < 1 := by
    calc
      b * c < 1 * c := mul_lt_mul_of_pos_right b_lt c_pos
      _ < 1 := by simpa using c_lt
  have product_lt : b * c * (1 - a * (1 - b)) < 1 := by
    calc
      b * c * (1 - a * (1 - b)) < b * c * 1 :=
        mul_lt_mul_of_pos_left factor_lt (mul_pos b_pos c_pos)
      _ < 1 := by simpa using bc_lt
  exact sub_pos.mpr product_lt

private theorem forkInnerRight_pos
    {a b c : ℚ} (a_pos : 0 < a) (a_lt : a < 1)
    (b_pos : 0 < b) (b_lt : b < 1) (c_pos : 0 < c) (c_lt : c < 1) :
    0 < 1 - a * c * (1 - b * (1 - a)) :=
  forkInnerLeft_pos b_pos b_lt a_pos a_lt c_pos c_lt

private theorem forkLeftWeight_pos
    {a b c : ℚ} (a_pos : 0 < a) (a_lt : a < 1)
    (b_pos : 0 < b) (b_lt : b < 1) (c_pos : 0 < c) (c_lt : c < 1) :
    0 < forkLeftWeight a b c :=
  mul_pos (sub_pos.mpr a_lt) (forkInnerLeft_pos a_pos a_lt b_pos b_lt c_pos c_lt)

private theorem forkRightWeight_pos
    {a b c : ℚ} (a_pos : 0 < a) (a_lt : a < 1)
    (b_pos : 0 < b) (b_lt : b < 1) (c_pos : 0 < c) (c_lt : c < 1) :
    0 < forkRightWeight a b c :=
  mul_pos (sub_pos.mpr b_lt) (forkInnerRight_pos a_pos a_lt b_pos b_lt c_pos c_lt)

/-- Distinct nonempty data-macro actions solving the fork equation have unequal slopes. -/
theorem forkActions_scale_ne
    (x y z : List Letter) (x_ne : x ≠ []) (y_ne : y ≠ [])
    (actions_eq : ∀ state,
      wordAction (y ++ z ++ x ++ y ++ x) state =
        wordAction (x ++ z ++ y ++ x ++ y) state)
    (actions_ne : ¬ ∀ state, wordAction x state = wordAction y state) :
    wordScale x ≠ wordScale y := by
  intro scale_eq
  have equation := forkActions_fixedPoint_equation x y z actions_eq
  have coefficient_neg := forkFixedCoefficient_neg
    (wordScale_pos x) (wordScale_lt_one_of_ne_nil x x_ne)
    (wordScale_pos y) (wordScale_lt_one_of_ne_nil y y_ne)
    (wordScale_pos z) (wordScale_le_one z)
  have fixed_difference_zero :
      forkFixedCoefficient (wordScale x) (wordScale y) (wordScale z) *
        (wordFixedPoint x - wordFixedPoint y) = 0 := by
    rw [scale_eq]
    rw [scale_eq] at equation
    simpa using equation
  have fixed_eq : wordFixedPoint x = wordFixedPoint y := by
    apply sub_eq_zero.mp
    exact (mul_eq_zero.mp fixed_difference_zero).resolve_left coefficient_neg.ne
  apply actions_ne
  exact wordAction_eq_of_common_fixedPoint_of_scale_eq x y (wordFixedPoint x)
    (wordAction_wordFixedPoint_of_ne_nil x x_ne)
    (by rw [fixed_eq]; exact wordAction_wordFixedPoint_of_ne_nil y y_ne) scale_eq

/-- Without a common fixed point, the two data actions in a nonempty fork solution have
different fixed points. -/
theorem forkActions_fixedPoint_ne_of_no_common
    (x y z : List Letter) (x_ne : x ≠ []) (y_ne : y ≠ []) (z_ne : z ≠ [])
    (actions_eq : ∀ state,
      wordAction (y ++ z ++ x ++ y ++ x) state =
        wordAction (x ++ z ++ y ++ x ++ y) state)
    (actions_ne : ¬ ∀ state, wordAction x state = wordAction y state)
    (no_common : ¬ ∃ fixed,
      wordAction x fixed = fixed ∧ wordAction y fixed = fixed ∧
        wordAction z fixed = fixed) :
    wordFixedPoint x ≠ wordFixedPoint y := by
  intro fixed_eq
  have scales_ne := forkActions_scale_ne x y z x_ne y_ne actions_eq actions_ne
  have z_scale_lt := wordScale_lt_one_of_ne_nil z z_ne
  have balance := forkActions_fixedPoint_balance x y z actions_eq
  rw [fixed_eq] at balance
  have weight_difference := forkRightWeight_sub_leftWeight
    (wordScale x) (wordScale y) (wordScale z)
  have difference_ne :
      forkRightWeight (wordScale x) (wordScale y) (wordScale z) -
          forkLeftWeight (wordScale x) (wordScale y) (wordScale z) ≠ 0 := by
    rw [weight_difference]
    exact mul_ne_zero (sub_ne_zero.mpr scales_ne) (sub_ne_zero.mpr z_scale_lt.ne')
  have z_fixed_eq : wordFixedPoint z = wordFixedPoint y := by
    have product_zero :
        (forkRightWeight (wordScale x) (wordScale y) (wordScale z) -
            forkLeftWeight (wordScale x) (wordScale y) (wordScale z)) *
          (wordFixedPoint y - wordFixedPoint z) = 0 := by
      nlinarith
    have second_zero := (mul_eq_zero.mp product_zero).resolve_left difference_ne
    exact (sub_eq_zero.mp second_zero).symm
  apply no_common
  refine ⟨wordFixedPoint y, ?_, wordAction_wordFixedPoint_of_ne_nil y y_ne, ?_⟩
  · simpa [fixed_eq] using wordAction_wordFixedPoint_of_ne_nil x x_ne
  · simpa [z_fixed_eq] using wordAction_wordFixedPoint_of_ne_nil z z_ne

/-- In a nonempty fork solution, the fixed point of the more contracting data action lies
strictly between the other data fixed point and the toggle fixed point. -/
theorem forkActions_fixedPoint_exterior
    (x y z : List Letter) (x_ne : x ≠ []) (y_ne : y ≠ []) (z_ne : z ≠ [])
    (actions_eq : ∀ state,
      wordAction (y ++ z ++ x ++ y ++ x) state =
        wordAction (x ++ z ++ y ++ x ++ y) state) :
    (wordScale y < wordScale x →
      (wordFixedPoint x < wordFixedPoint y →
          wordFixedPoint y < wordFixedPoint z) ∧
        (wordFixedPoint y < wordFixedPoint x →
          wordFixedPoint z < wordFixedPoint y)) ∧
      (wordScale x < wordScale y →
        (wordFixedPoint y < wordFixedPoint x →
            wordFixedPoint x < wordFixedPoint z) ∧
          (wordFixedPoint x < wordFixedPoint y →
            wordFixedPoint z < wordFixedPoint x)) := by
  have x_scale_pos := wordScale_pos x
  have x_scale_lt := wordScale_lt_one_of_ne_nil x x_ne
  have y_scale_pos := wordScale_pos y
  have y_scale_lt := wordScale_lt_one_of_ne_nil y y_ne
  have z_scale_pos := wordScale_pos z
  have z_scale_lt := wordScale_lt_one_of_ne_nil z z_ne
  have left_weight_pos := forkLeftWeight_pos x_scale_pos x_scale_lt
    y_scale_pos y_scale_lt z_scale_pos z_scale_lt
  have right_weight_pos := forkRightWeight_pos x_scale_pos x_scale_lt
    y_scale_pos y_scale_lt z_scale_pos z_scale_lt
  have balance := forkActions_fixedPoint_balance x y z actions_eq
  have weight_difference := forkRightWeight_sub_leftWeight
    (wordScale x) (wordScale y) (wordScale z)
  constructor
  · intro scales_lt
    have gap_pos :
        0 < forkRightWeight (wordScale x) (wordScale y) (wordScale z) -
          forkLeftWeight (wordScale x) (wordScale y) (wordScale z) := by
      rw [weight_difference]
      exact mul_pos (sub_pos.mpr scales_lt) (sub_pos.mpr z_scale_lt)
    have exterior_identity :
        (forkRightWeight (wordScale x) (wordScale y) (wordScale z) -
            forkLeftWeight (wordScale x) (wordScale y) (wordScale z)) *
            (wordFixedPoint z - wordFixedPoint y) =
          forkLeftWeight (wordScale x) (wordScale y) (wordScale z) *
            (wordFixedPoint y - wordFixedPoint x) := by
      nlinarith
    constructor
    · intro fixed_lt
      have product_pos :
          0 < (forkRightWeight (wordScale x) (wordScale y) (wordScale z) -
              forkLeftWeight (wordScale x) (wordScale y) (wordScale z)) *
              (wordFixedPoint z - wordFixedPoint y) := by
        rw [exterior_identity]
        exact mul_pos left_weight_pos (sub_pos.mpr fixed_lt)
      nlinarith
    · intro fixed_lt
      have product_neg :
          (forkRightWeight (wordScale x) (wordScale y) (wordScale z) -
              forkLeftWeight (wordScale x) (wordScale y) (wordScale z)) *
              (wordFixedPoint z - wordFixedPoint y) < 0 := by
        rw [exterior_identity]
        exact mul_neg_of_pos_of_neg left_weight_pos (sub_neg.mpr fixed_lt)
      nlinarith
  · intro scales_lt
    have gap_pos :
        0 < forkLeftWeight (wordScale x) (wordScale y) (wordScale z) -
          forkRightWeight (wordScale x) (wordScale y) (wordScale z) := by
      rw [sub_pos, ← sub_neg, weight_difference]
      exact mul_neg_of_neg_of_pos (sub_neg.mpr scales_lt) (sub_pos.mpr z_scale_lt)
    have exterior_identity :
        (forkLeftWeight (wordScale x) (wordScale y) (wordScale z) -
            forkRightWeight (wordScale x) (wordScale y) (wordScale z)) *
            (wordFixedPoint z - wordFixedPoint x) =
          forkRightWeight (wordScale x) (wordScale y) (wordScale z) *
            (wordFixedPoint x - wordFixedPoint y) := by
      nlinarith
    constructor
    · intro fixed_lt
      have product_pos :
          0 < (forkLeftWeight (wordScale x) (wordScale y) (wordScale z) -
              forkRightWeight (wordScale x) (wordScale y) (wordScale z)) *
              (wordFixedPoint z - wordFixedPoint x) := by
        rw [exterior_identity]
        exact mul_pos right_weight_pos (sub_pos.mpr fixed_lt)
      nlinarith
    · intro fixed_lt
      have product_neg :
          (forkLeftWeight (wordScale x) (wordScale y) (wordScale z) -
              forkRightWeight (wordScale x) (wordScale y) (wordScale z)) *
              (wordFixedPoint z - wordFixedPoint x) < 0 := by
        rw [exterior_identity]
        exact mul_neg_of_pos_of_neg right_weight_pos (sub_neg.mpr fixed_lt)
      nlinarith

/-- The reduced `bcbc` kernel equation determines the macro fixed-point coordinates by one exact
scalar relation. -/
theorem bcbc_macro_fixedPoint_equation
    (code : PairedControl → List Letter) (source target : ℚ)
    (endpoint_exact : ∀ word,
      wordAction (encodedWord code word) source = target ↔
        pairedCoefficient ℚ 3 bcbcBody (.data .c :: word) = 0) :
    forkFixedCoefficient (wordScale (code (.data .b)))
          (wordScale (code (.data .c))) (wordScale (code .toggle)) *
          (wordFixedPoint (code (.data .b)) - wordFixedPoint (code (.data .c))) +
        (wordScale (code (.data .b)) - wordScale (code (.data .c))) *
          (wordScale (code .toggle) - 1) *
          (wordFixedPoint (code .toggle) - wordFixedPoint (code (.data .c))) = 0 := by
  apply forkActions_fixedPoint_equation
    (code (.data .b)) (code (.data .c)) (code .toggle)
  intro state
  simpa [flatForkKernelWord, nestedForkKernelWord] using
    bcbc_reducedFork_actions_eq code source target endpoint_exact state

/-- Nonempty data macros in an exact endpoint code have different affine slopes. -/
theorem bcbc_data_macro_scales_ne_of_nonempty
    (code : PairedControl → List Letter) (source target : ℚ)
    (data_b_ne : code (.data .b) ≠ []) (data_c_ne : code (.data .c) ≠ [])
    (endpoint_exact : ∀ word,
      wordAction (encodedWord code word) source = target ↔
        pairedCoefficient ℚ 3 bcbcBody (.data .c :: word) = 0) :
    wordScale (code (.data .b)) ≠ wordScale (code (.data .c)) := by
  apply forkActions_scale_ne
    (code (.data .b)) (code (.data .c)) (code .toggle)
    data_b_ne data_c_ne
  · intro state
    simpa [flatForkKernelWord, nestedForkKernelWord] using
      bcbc_reducedFork_actions_eq code source target endpoint_exact state
  · exact (bcbc_macro_actions_pairwise_ne code source target endpoint_exact).1

/-- An action commuting with one nonempty mixed-prime word fixes that word's unique rational
fixed point. -/
theorem wordAction_wordFixedPoint_of_actions_commute
    (anchor word : List Letter) (anchor_ne : anchor ≠ [])
    (commute : ∀ state,
      wordAction anchor (wordAction word state) =
        wordAction word (wordAction anchor state)) :
    wordAction word (wordFixedPoint anchor) = wordFixedPoint anchor := by
  have anchor_fixed := wordAction_wordFixedPoint_of_ne_nil anchor anchor_ne
  apply wordAction_fixedPoint_unique_of_ne_nil anchor anchor_ne
  · calc
      wordAction anchor (wordAction word (wordFixedPoint anchor)) =
          wordAction word (wordAction anchor (wordFixedPoint anchor)) :=
        commute (wordFixedPoint anchor)
      _ = wordAction word (wordFixedPoint anchor) := by rw [anchor_fixed]
  · exact anchor_fixed

/-- The data-`b` macro of an exact endpoint code is nonempty. -/
theorem bcbc_data_b_macro_ne
    (code : PairedControl → List Letter) (source target : ℚ)
    (endpoint_exact : ∀ word,
      wordAction (encodedWord code word) source = target ↔
        pairedCoefficient ℚ 3 bcbcBody (.data .c :: word) = 0) :
    code (.data .b) ≠ [] := by
  intro data_b_empty
  have macro_actions_ne := bcbc_macro_actions_pairwise_ne code source target endpoint_exact
  have data_c_ne : code (.data .c) ≠ [] := by
    intro data_c_empty
    apply macro_actions_ne.1
    intro state
    simp [data_b_empty, data_c_empty, wordAction]
  have reduced_actions := bcbc_reducedFork_actions_eq code source target endpoint_exact
  have commute_actions : ∀ state,
      wordAction (code (.data .c)) (wordAction (code .toggle) state) =
        wordAction (code .toggle) (wordAction (code (.data .c)) state) := by
    have cancelled := wordAction_cancel_context []
      (code (.data .c) ++ code .toggle) (code .toggle ++ code (.data .c))
      (code (.data .c))
    have context_eq : ∀ state,
        wordAction ([] ++ (code (.data .c) ++ code .toggle) ++ code (.data .c)) state =
          wordAction ([] ++ (code .toggle ++ code (.data .c)) ++ code (.data .c)) state := by
      intro state
      simpa [flatForkKernelWord, nestedForkKernelWord, data_b_empty, List.append_assoc] using
        reduced_actions state
    have words_commute := cancelled context_eq
    intro state
    simpa only [wordAction_append] using words_commute state
  let fixed := wordFixedPoint (code (.data .c))
  have data_c_fixed : wordAction (code (.data .c)) fixed = fixed :=
    wordAction_wordFixedPoint_of_ne_nil (code (.data .c)) data_c_ne
  have toggle_fixed : wordAction (code .toggle) fixed = fixed :=
    wordAction_wordFixedPoint_of_actions_commute
      (code (.data .c)) (code .toggle) data_c_ne commute_actions
  have macro_fixed : ∀ control, wordAction (code control) fixed = fixed := by
    intro control
    cases control with
    | toggle => exact toggle_fixed
    | data letter =>
        cases letter with
        | b => simp [data_b_empty, wordAction]
        | c => exact data_c_fixed
  exact no_bcbc_endpoint_of_common_macro_fixedPoint
    code source target fixed macro_fixed endpoint_exact

/-- The data-`c` macro of an exact endpoint code is nonempty. -/
theorem bcbc_data_c_macro_ne
    (code : PairedControl → List Letter) (source target : ℚ)
    (endpoint_exact : ∀ word,
      wordAction (encodedWord code word) source = target ↔
        pairedCoefficient ℚ 3 bcbcBody (.data .c :: word) = 0) :
    code (.data .c) ≠ [] := by
  intro data_c_empty
  have macro_actions_ne := bcbc_macro_actions_pairwise_ne code source target endpoint_exact
  have data_b_ne : code (.data .b) ≠ [] := by
    intro data_b_empty
    apply macro_actions_ne.1
    intro state
    simp [data_b_empty, data_c_empty, wordAction]
  have reduced_actions := bcbc_reducedFork_actions_eq code source target endpoint_exact
  have commute_actions : ∀ state,
      wordAction (code (.data .b)) (wordAction (code .toggle) state) =
        wordAction (code .toggle) (wordAction (code (.data .b)) state) := by
    have cancelled := wordAction_cancel_context []
      (code .toggle ++ code (.data .b)) (code (.data .b) ++ code .toggle)
      (code (.data .b))
    have context_eq : ∀ state,
        wordAction ([] ++ (code .toggle ++ code (.data .b)) ++ code (.data .b)) state =
          wordAction ([] ++ (code (.data .b) ++ code .toggle) ++ code (.data .b)) state := by
      intro state
      simpa [flatForkKernelWord, nestedForkKernelWord, data_c_empty, List.append_assoc] using
        reduced_actions state
    have words_commute := cancelled context_eq
    intro state
    simpa only [wordAction_append] using (words_commute state).symm
  let fixed := wordFixedPoint (code (.data .b))
  have data_b_fixed : wordAction (code (.data .b)) fixed = fixed :=
    wordAction_wordFixedPoint_of_ne_nil (code (.data .b)) data_b_ne
  have toggle_fixed : wordAction (code .toggle) fixed = fixed :=
    wordAction_wordFixedPoint_of_actions_commute
      (code (.data .b)) (code .toggle) data_b_ne commute_actions
  have macro_fixed : ∀ control, wordAction (code control) fixed = fixed := by
    intro control
    cases control with
    | toggle => exact toggle_fixed
    | data letter =>
        cases letter with
        | b => exact data_b_fixed
        | c => simp [data_c_empty, wordAction]
  exact no_bcbc_endpoint_of_common_macro_fixedPoint
    code source target fixed macro_fixed endpoint_exact

/-- The toggle macro of an exact endpoint code is nonempty. -/
theorem bcbc_toggle_macro_ne
    (code : PairedControl → List Letter) (source target : ℚ)
    (endpoint_exact : ∀ word,
      wordAction (encodedWord code word) source = target ↔
        pairedCoefficient ℚ 3 bcbcBody (.data .c :: word) = 0) :
    code .toggle ≠ [] := by
  intro toggle_empty
  have data_b_ne := bcbc_data_b_macro_ne code source target endpoint_exact
  have data_c_ne := bcbc_data_c_macro_ne code source target endpoint_exact
  have equation := bcbc_macro_fixedPoint_equation code source target endpoint_exact
  have coefficient_neg := forkFixedCoefficient_neg (c := 1)
    (wordScale_pos (code (.data .b)))
    (wordScale_lt_one_of_ne_nil (code (.data .b)) data_b_ne)
    (wordScale_pos (code (.data .c)))
    (wordScale_lt_one_of_ne_nil (code (.data .c)) data_c_ne)
    (by norm_num) (by norm_num)
  have fixed_difference_zero :
      forkFixedCoefficient (wordScale (code (.data .b)))
          (wordScale (code (.data .c))) 1 *
        (wordFixedPoint (code (.data .b)) - wordFixedPoint (code (.data .c))) = 0 := by
    simpa [toggle_empty, wordScale] using equation
  have fixed_eq :
      wordFixedPoint (code (.data .b)) = wordFixedPoint (code (.data .c)) := by
    apply sub_eq_zero.mp
    exact (mul_eq_zero.mp fixed_difference_zero).resolve_left coefficient_neg.ne
  let fixed := wordFixedPoint (code (.data .b))
  have data_b_fixed : wordAction (code (.data .b)) fixed = fixed :=
    wordAction_wordFixedPoint_of_ne_nil (code (.data .b)) data_b_ne
  have data_c_fixed : wordAction (code (.data .c)) fixed = fixed := by
    dsimp only [fixed]
    rw [fixed_eq]
    exact wordAction_wordFixedPoint_of_ne_nil (code (.data .c)) data_c_ne
  have macro_fixed : ∀ control, wordAction (code control) fixed = fixed := by
    intro control
    cases control with
    | toggle => simp [toggle_empty, wordAction]
    | data letter =>
        cases letter with
        | b => exact data_b_fixed
        | c => exact data_c_fixed
  exact no_bcbc_endpoint_of_common_macro_fixedPoint
    code source target fixed macro_fixed endpoint_exact

/-- All three control macros of an exact endpoint code are nonempty. -/
theorem bcbc_macro_words_ne_nil
    (code : PairedControl → List Letter) (source target : ℚ)
    (endpoint_exact : ∀ word,
      wordAction (encodedWord code word) source = target ↔
        pairedCoefficient ℚ 3 bcbcBody (.data .c :: word) = 0) :
    code (.data .b) ≠ [] ∧ code (.data .c) ≠ [] ∧ code .toggle ≠ [] :=
  ⟨bcbc_data_b_macro_ne code source target endpoint_exact,
    bcbc_data_c_macro_ne code source target endpoint_exact,
    bcbc_toggle_macro_ne code source target endpoint_exact⟩

/-- Exact endpoint semantics forces the two data macros to have unequal slopes. -/
theorem bcbc_data_macro_scales_ne
    (code : PairedControl → List Letter) (source target : ℚ)
    (endpoint_exact : ∀ word,
      wordAction (encodedWord code word) source = target ↔
        pairedCoefficient ℚ 3 bcbcBody (.data .c :: word) = 0) :
    wordScale (code (.data .b)) ≠ wordScale (code (.data .c)) :=
  bcbc_data_macro_scales_ne_of_nonempty code source target
    (bcbc_data_b_macro_ne code source target endpoint_exact)
    (bcbc_data_c_macro_ne code source target endpoint_exact) endpoint_exact

/-- Exact endpoint semantics forces the two data macros to have different rational fixed
points. -/
theorem bcbc_data_macro_fixedPoints_ne
    (code : PairedControl → List Letter) (source target : ℚ)
    (endpoint_exact : ∀ word,
      wordAction (encodedWord code word) source = target ↔
        pairedCoefficient ℚ 3 bcbcBody (.data .c :: word) = 0) :
    wordFixedPoint (code (.data .b)) ≠ wordFixedPoint (code (.data .c)) := by
  have macro_words_ne := bcbc_macro_words_ne_nil code source target endpoint_exact
  apply forkActions_fixedPoint_ne_of_no_common
    (code (.data .b)) (code (.data .c)) (code .toggle)
    macro_words_ne.1 macro_words_ne.2.1 macro_words_ne.2.2
  · intro state
    simpa [flatForkKernelWord, nestedForkKernelWord] using
      bcbc_reducedFork_actions_eq code source target endpoint_exact state
  · exact (bcbc_macro_actions_pairwise_ne code source target endpoint_exact).1
  · rintro ⟨fixed, data_b_fixed, data_c_fixed, toggle_fixed⟩
    have macro_fixed : ∀ control, wordAction (code control) fixed = fixed := by
      intro control
      cases control with
      | toggle => exact toggle_fixed
      | data letter =>
          cases letter with
          | b => exact data_b_fixed
          | c => exact data_c_fixed
    exact no_bcbc_endpoint_of_common_macro_fixedPoint
      code source target fixed macro_fixed endpoint_exact

/-- Every exact `bcbc` code places the toggle fixed point strictly beyond the fixed point of the
more contracting data macro, on the side away from the other data fixed point. -/
theorem bcbc_toggle_fixedPoint_exterior
    (code : PairedControl → List Letter) (source target : ℚ)
    (endpoint_exact : ∀ word,
      wordAction (encodedWord code word) source = target ↔
        pairedCoefficient ℚ 3 bcbcBody (.data .c :: word) = 0) :
    (wordScale (code (.data .c)) < wordScale (code (.data .b)) ∧
        ((wordFixedPoint (code (.data .b)) < wordFixedPoint (code (.data .c)) ∧
            wordFixedPoint (code (.data .c)) < wordFixedPoint (code .toggle)) ∨
          (wordFixedPoint (code .toggle) < wordFixedPoint (code (.data .c)) ∧
            wordFixedPoint (code (.data .c)) < wordFixedPoint (code (.data .b))))) ∨
      (wordScale (code (.data .b)) < wordScale (code (.data .c)) ∧
        ((wordFixedPoint (code (.data .c)) < wordFixedPoint (code (.data .b)) ∧
            wordFixedPoint (code (.data .b)) < wordFixedPoint (code .toggle)) ∨
          (wordFixedPoint (code .toggle) < wordFixedPoint (code (.data .b)) ∧
            wordFixedPoint (code (.data .b)) < wordFixedPoint (code (.data .c))))) := by
  have macro_words_ne := bcbc_macro_words_ne_nil code source target endpoint_exact
  have actions_eq : ∀ state,
      wordAction
          (code (.data .c) ++ code .toggle ++ code (.data .b) ++
            code (.data .c) ++ code (.data .b)) state =
        wordAction
          (code (.data .b) ++ code .toggle ++ code (.data .c) ++
            code (.data .b) ++ code (.data .c)) state := by
    intro state
    simpa [flatForkKernelWord, nestedForkKernelWord] using
      bcbc_reducedFork_actions_eq code source target endpoint_exact state
  have exterior := forkActions_fixedPoint_exterior
    (code (.data .b)) (code (.data .c)) (code .toggle)
    macro_words_ne.1 macro_words_ne.2.1 macro_words_ne.2.2 actions_eq
  have scales_ne := bcbc_data_macro_scales_ne code source target endpoint_exact
  have fixed_points_ne := bcbc_data_macro_fixedPoints_ne code source target endpoint_exact
  rcases lt_or_gt_of_ne scales_ne with scales_lt | scales_lt
  · refine Or.inr ⟨scales_lt, ?_⟩
    rcases lt_or_gt_of_ne fixed_points_ne with fixed_lt | fixed_lt
    · exact Or.inr ⟨(exterior.2 scales_lt).2 fixed_lt, fixed_lt⟩
    · exact Or.inl ⟨fixed_lt, (exterior.2 scales_lt).1 fixed_lt⟩
  · refine Or.inl ⟨scales_lt, ?_⟩
    rcases lt_or_gt_of_ne fixed_points_ne with fixed_lt | fixed_lt
    · exact Or.inl ⟨fixed_lt, (exterior.1 scales_lt).1 fixed_lt⟩
    · exact Or.inr ⟨(exterior.1 scales_lt).2 fixed_lt, fixed_lt⟩

/-- The fixed point of the more contracting data macro lies strictly inside the common invariant
interval `[0,5/2]`. -/
theorem bcbc_moreContracting_fixedPoint_interior
    (code : PairedControl → List Letter) (source target : ℚ)
    (endpoint_exact : ∀ word,
      wordAction (encodedWord code word) source = target ↔
        pairedCoefficient ℚ 3 bcbcBody (.data .c :: word) = 0) :
    (wordScale (code (.data .c)) < wordScale (code (.data .b)) ∧
        0 < wordFixedPoint (code (.data .c)) ∧
          wordFixedPoint (code (.data .c)) < 5 / 2) ∨
      (wordScale (code (.data .b)) < wordScale (code (.data .c)) ∧
        0 < wordFixedPoint (code (.data .b)) ∧
          wordFixedPoint (code (.data .b)) < 5 / 2) := by
  have macro_words_ne := bcbc_macro_words_ne_nil code source target endpoint_exact
  have data_b_bounds := wordFixedPoint_mem_interval (code (.data .b)) macro_words_ne.1
  have data_c_bounds := wordFixedPoint_mem_interval (code (.data .c)) macro_words_ne.2.1
  have toggle_bounds := wordFixedPoint_mem_interval (code .toggle) macro_words_ne.2.2
  rcases bcbc_toggle_fixedPoint_exterior code source target endpoint_exact with
    ⟨scales_lt, fixed_order | fixed_order⟩ | ⟨scales_lt, fixed_order | fixed_order⟩
  · exact Or.inl ⟨scales_lt, by linarith, by linarith⟩
  · exact Or.inl ⟨scales_lt, by linarith, by linarith⟩
  · exact Or.inr ⟨scales_lt, by linarith, by linarith⟩
  · exact Or.inr ⟨scales_lt, by linarith, by linarith⟩

end MatrixMortality.GuardedMixedPrimeFork
