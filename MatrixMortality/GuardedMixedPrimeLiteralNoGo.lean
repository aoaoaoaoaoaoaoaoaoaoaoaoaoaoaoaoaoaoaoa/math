import MatrixMortality.GuardedMixedPrimeFork

/-!
# Literal mixed-prime fork extinction

The literal branch left by `bcbc_fork_macro_word_or_kernel` cannot occur. After cancelling the
common macro prefix and suffix, equality of the flat and nested fork words becomes
`y z x y x = x z y x y`. Equal-length splitting forces both `y z x = x z y` and
`y x = x y`. Distinct mixed-prime actions satisfying those equations have one common rational
fixed point, contradicting the exact `bcbc` endpoint language. Thus every exact code must supply
a genuine nontrivial relation in the mixed-prime affine monoid.
-/

namespace MatrixMortality.GuardedMixedPrimeFork

open MixedPrimeKernel
open GuardedMixedPrimeBridge
open BranchingHistory BranchingRecognizer PeriodicHistory
open TransverseSeparatedForkNoGo

/-- Equal-length splitting of the substituted flat/nested fork equation. -/
theorem forkEquation_split {α : Type*} (x y z : List α)
    (fork_eq : y ++ z ++ x ++ y ++ x = x ++ z ++ y ++ x ++ y) :
    y ++ z ++ x = x ++ z ++ y ∧ y ++ x = x ++ y := by
  apply List.append_inj (s₁ := y ++ z ++ x) (s₂ := x ++ z ++ y)
  · simpa [List.append_assoc] using fork_eq
  · simp only [List.length_append]
    omega

/-- The rational fixed point of one nonempty mixed-prime word. -/
def wordFixedPoint (word : List Letter) : ℚ :=
  wordAction word 0 / (1 - wordScale word)

theorem wordAction_wordFixedPoint_of_ne_nil (word : List Letter) (word_ne : word ≠ []) :
    wordAction word (wordFixedPoint word) = wordFixedPoint word := by
  have scale_lt : wordScale word < 1 := wordScale_lt_one_of_ne_nil word word_ne
  have denominator_ne : 1 - wordScale word ≠ 0 := by linarith
  have difference := wordAction_sub word (wordFixedPoint word) 0
  simp only [sub_zero] at difference
  rw [wordFixedPoint]
  rw [wordFixedPoint] at difference
  field_simp [denominator_ne] at difference ⊢
  linarith

/-- A word commuting with a nonempty mixed-prime word fixes its unique rational fixed point. -/
theorem wordAction_wordFixedPoint_of_commute
    (anchor word : List Letter) (anchor_ne : anchor ≠ [])
    (commute : anchor ++ word = word ++ anchor) :
    wordAction word (wordFixedPoint anchor) = wordFixedPoint anchor := by
  have anchor_fixed := wordAction_wordFixedPoint_of_ne_nil anchor anchor_ne
  apply wordAction_fixedPoint_unique_of_ne_nil anchor anchor_ne
  · calc
      wordAction anchor (wordAction word (wordFixedPoint anchor)) =
          wordAction (anchor ++ word) (wordFixedPoint anchor) := by
            rw [wordAction_append]
      _ = wordAction (word ++ anchor) (wordFixedPoint anchor) := by rw [commute]
      _ = wordAction word (wordAction anchor (wordFixedPoint anchor)) := by
            rw [wordAction_append]
      _ = wordAction word (wordFixedPoint anchor) := by rw [anchor_fixed]
  · exact anchor_fixed

/-- Two mixed-prime affine words agreeing at two distinct rational points agree everywhere. -/
theorem wordAction_eq_of_eq_at_two_points
    (left right : List Letter) {first second : ℚ}
    (at_first : wordAction left first = wordAction right first)
    (at_second : wordAction left second = wordAction right second)
    (points_ne : first ≠ second) :
    ∀ state, wordAction left state = wordAction right state := by
  have left_difference := wordAction_sub left second first
  have right_difference := wordAction_sub right second first
  have scale_product_zero :
      (wordScale left - wordScale right) * (second - first) = 0 := by
    rw [at_second, at_first] at left_difference
    linarith
  have point_difference_ne : second - first ≠ 0 := sub_ne_zero.mpr points_ne.symm
  have scale_eq : wordScale left = wordScale right := by
    exact sub_eq_zero.mp ((mul_eq_zero.mp scale_product_zero).resolve_right point_difference_ne)
  intro state
  calc
    wordAction left state =
        wordAction left first + wordScale left * (state - first) := by
      linarith [wordAction_sub left state first]
    _ = wordAction right first + wordScale right * (state - first) := by
      rw [at_first, scale_eq]
    _ = wordAction right state := by
      linarith [wordAction_sub right state first]

/-- Off the diagonal `x = y` action, the substituted fork equation forces all three
mixed-prime macro actions to share a rational fixed point. -/
theorem forkEquation_common_fixedPoint_of_actions_ne
    (x y z : List Letter)
    (fork_eq : y ++ z ++ x ++ y ++ x = x ++ z ++ y ++ x ++ y)
    (actions_ne : ¬ ∀ state, wordAction x state = wordAction y state) :
    ∃ fixed,
      wordAction x fixed = fixed ∧ wordAction y fixed = fixed ∧
        wordAction z fixed = fixed := by
  obtain ⟨triple_eq, commute⟩ := forkEquation_split x y z fork_eq
  have one_nonempty : x ≠ [] ∨ y ≠ [] := by
    by_cases x_ne : x ≠ []
    · exact Or.inl x_ne
    · apply Or.inr
      intro y_empty
      have x_empty : x = [] := not_ne_iff.mp x_ne
      apply actions_ne
      intro state
      simp [x_empty, y_empty, wordAction]
  rcases one_nonempty with x_ne | y_ne
  · let fixed := wordFixedPoint x
    have x_fixed : wordAction x fixed = fixed :=
      wordAction_wordFixedPoint_of_ne_nil x x_ne
    have y_fixed : wordAction y fixed = fixed :=
      wordAction_wordFixedPoint_of_commute x y x_ne commute.symm
    have at_image :
        wordAction x (wordAction z fixed) = wordAction y (wordAction z fixed) := by
      calc
        wordAction x (wordAction z fixed) =
            wordAction x (wordAction z (wordAction y fixed)) := by rw [y_fixed]
        _ = wordAction (x ++ z ++ y) fixed := by
          simp only [wordAction_append]
        _ = wordAction (y ++ z ++ x) fixed := by rw [triple_eq]
        _ = wordAction y (wordAction z (wordAction x fixed)) := by
          simp only [wordAction_append]
        _ = wordAction y (wordAction z fixed) := by rw [x_fixed]
    have z_fixed : wordAction z fixed = fixed := by
      by_contra image_ne
      apply actions_ne
      exact wordAction_eq_of_eq_at_two_points x y
        (by rw [x_fixed, y_fixed]) at_image (Ne.symm image_ne)
    exact ⟨fixed, x_fixed, y_fixed, z_fixed⟩
  · let fixed := wordFixedPoint y
    have y_fixed : wordAction y fixed = fixed :=
      wordAction_wordFixedPoint_of_ne_nil y y_ne
    have x_fixed : wordAction x fixed = fixed :=
      wordAction_wordFixedPoint_of_commute y x y_ne commute
    have at_image :
        wordAction x (wordAction z fixed) = wordAction y (wordAction z fixed) := by
      calc
        wordAction x (wordAction z fixed) =
            wordAction x (wordAction z (wordAction y fixed)) := by rw [y_fixed]
        _ = wordAction (x ++ z ++ y) fixed := by
          simp only [wordAction_append]
        _ = wordAction (y ++ z ++ x) fixed := by rw [triple_eq]
        _ = wordAction y (wordAction z (wordAction x fixed)) := by
          simp only [wordAction_append]
        _ = wordAction y (wordAction z fixed) := by rw [x_fixed]
    have z_fixed : wordAction z fixed = fixed := by
      by_contra image_ne
      apply actions_ne
      exact wordAction_eq_of_eq_at_two_points x y
        (by rw [x_fixed, y_fixed]) at_image (Ne.symm image_ne)
    exact ⟨fixed, x_fixed, y_fixed, z_fixed⟩

/-- Cancelling the common prefix and suffix of literal flat/nested macro equality leaves the
five-factor fork equation. -/
theorem bcbc_literal_macro_equation
    (code : PairedControl → List Letter)
    (words_eq : encodedWord code flatForkControl = encodedWord code nestedForkControl) :
    code (.data .c) ++ code .toggle ++ code (.data .b) ++ code (.data .c) ++
        code (.data .b) =
      code (.data .b) ++ code .toggle ++ code (.data .c) ++ code (.data .b) ++
        code (.data .c) := by
  apply List.append_cancel_right
    (bs := code .toggle ++ code (.data .b) ++ code (.data .b) ++
      code (.data .c) ++ code .toggle ++ code (.data .b) ++ code (.data .c))
  simpa [List.append_assoc, encodedWord, flatForkControl, nestedForkControl, historyControl,
    strokeControl, flatBlock, nestedBlock, strokeBBB, strokeBCB, strokeCBC, strokeCBB,
    stroke₃] using words_eq

/-- Both expanded fork words have raw length `4(2|κ(b)|+|κ(c)|+|κ(toggle)|)`. -/
theorem bcbc_encodedFork_length (code : PairedControl → List Letter) :
    (encodedWord code flatForkControl).length =
        4 * (2 * (code (.data .b)).length + (code (.data .c)).length +
          (code .toggle).length) ∧
      (encodedWord code nestedForkControl).length =
        4 * (2 * (code (.data .b)).length + (code (.data .c)).length +
          (code .toggle).length) := by
  simp [encodedWord, flatForkControl, nestedForkControl, historyControl, strokeControl,
    flatBlock, nestedBlock, strokeBBB, strokeBCB, strokeCBC, strokeCBB, stroke₃]
  omega

/-- Exact endpoint recognition excludes literal equality of the flat and nested fork words. -/
theorem no_bcbc_literal_fork_words
    (code : PairedControl → List Letter) (source target : ℚ)
    (endpoint_exact : ∀ word,
      wordAction (encodedWord code word) source = target ↔
        pairedCoefficient ℚ 3 bcbcBody (.data .c :: word) = 0) :
    encodedWord code flatForkControl ≠ encodedWord code nestedForkControl := by
  intro words_eq
  have macro_actions_ne := bcbc_macro_actions_pairwise_ne code source target endpoint_exact
  obtain ⟨fixed, data_b_fixed, data_c_fixed, toggle_fixed⟩ :=
    forkEquation_common_fixedPoint_of_actions_ne
      (code (.data .b)) (code (.data .c)) (code .toggle)
      (bcbc_literal_macro_equation code words_eq) macro_actions_ne.1
  have all_macro_fixed : ∀ control, wordAction (code control) fixed = fixed := by
    intro control
    cases control with
    | toggle => exact toggle_fixed
    | data letter =>
        cases letter with
        | b => exact data_b_fixed
        | c => exact data_c_fixed
  exact no_bcbc_endpoint_of_common_macro_fixedPoint
    code source target fixed all_macro_fixed endpoint_exact

/-- Every exact endpoint code realizes a genuine nontrivial relation in the mixed-prime affine
action; the literal branch of `bcbc_fork_macro_word_or_kernel` is impossible. -/
theorem bcbc_fork_macro_kernel
    (code : PairedControl → List Letter) (source target : ℚ)
    (endpoint_exact : ∀ word,
      wordAction (encodedWord code word) source = target ↔
        pairedCoefficient ℚ 3 bcbcBody (.data .c :: word) = 0) :
    encodedWord code flatForkControl ≠ encodedWord code nestedForkControl ∧
      ∀ state,
        wordAction (encodedWord code flatForkControl) state =
          wordAction (encodedWord code nestedForkControl) state :=
  ⟨no_bcbc_literal_fork_words code source target endpoint_exact,
    bcbc_fork_macro_actions_eq code source target endpoint_exact⟩

end MatrixMortality.GuardedMixedPrimeFork
