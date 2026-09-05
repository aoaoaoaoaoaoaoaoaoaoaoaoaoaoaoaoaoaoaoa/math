import Mathlib.Tactic.NormNum.Prime
import MatrixMortality.PadicValuation
import MatrixMortality.ProjectiveIncidence

/-!
# Shortcut-Collatz projective incidence

The two inverse branches of shortcut Collatz act by fixed rational projectivities. A malformed
odd branch creates a factor three in the reduced denominator which no later branch can remove.
Consequently pointwise shortcut-Collatz reachability reduces exactly to normalized generic
two-generator projective incidence.
-/

namespace MatrixMortality.ProjectiveCollatz

open PadicValuation
open scoped Matrix

/-- Least set containing one and closed under the two integral inverse branches of shortcut
Collatz. -/
inductive ReachesOne : ℤ → Prop
  | one : ReachesOne 1
  | even {target : ℤ} : ReachesOne target → ReachesOne (2 * target)
  | odd {target source : ℤ} :
      ReachesOne target →
      2 * target - 1 = 3 * source →
      ReachesOne source

/-- One conventional shortcut-Collatz step: halve an even source, or apply `(3n+1)/2` to an
odd source. -/
def ShortcutStep (source target : ℤ) : Prop :=
  (Even source ∧ source = 2 * target) ∨
    (Odd source ∧ 3 * source + 1 = 2 * target)

/-- The inverse-branch closure is exactly finite conventional shortcut-Collatz reachability. -/
theorem reachesOne_iff_shortcutCollatz (value : ℤ) :
    ReachesOne value ↔
      Relation.ReflTransGen ShortcutStep value 1 := by
  constructor
  · intro reaches
    induction reaches with
    | one =>
        exact .refl
    | @even target _ induction =>
        exact .head (Or.inl ⟨⟨target, by ring⟩, rfl⟩) induction
    | @odd target source _ source_eq induction =>
        have target_odd : Odd (2 * target - 1) :=
          (show Even (2 * target) from ⟨target, by ring⟩).sub_odd ⟨0, by ring⟩
        have product_odd : Odd (3 * source) := source_eq ▸ target_odd
        have source_odd : Odd source := (Int.odd_mul.mp product_odd).2
        have step : ShortcutStep source target :=
          Or.inr ⟨source_odd, by omega⟩
        exact Relation.ReflTransGen.head step induction
  · intro reaches
    induction reaches using Relation.ReflTransGen.head_induction_on with
    | refl =>
        exact .one
    | @head source target step _ induction =>
        rcases step with ⟨_, source_eq⟩ | ⟨_, source_eq⟩
        · rw [source_eq]
          exact .even induction
        · exact .odd induction (by omega)

/-- The fixed even and odd inverse branches, indexed as the incidence generators `H` and `G`. -/
def predecessor : Bool → ℚ → ℚ
  | false, value => (2 * value - 1) / 3
  | true, value => 2 * value

/-- Apply a projective word from right to left, matching matrix multiplication. -/
def predecessorState (word : List Bool) : ℚ :=
  word.foldr predecessor 1

@[simp]
theorem predecessorState_nil :
    predecessorState [] = 1 := rfl

@[simp]
theorem predecessorState_cons (label : Bool) (word : List Bool) :
    predecessorState (label :: word) =
      predecessor label (predecessorState word) := rfl

private theorem double_negative {value : ℚ}
    (negative : IsNegative 3 value) :
    IsNegative 3 (2 * value) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have two_unit : HasValue 3 (2 : ℚ) 0 :=
    intCast_isUnit_of_not_dvd (by norm_num)
  have value_exact : HasValue 3 value (padicValRat 3 value) :=
    ⟨negative.1, rfl⟩
  have product := mul_hasValue two_unit value_exact
  refine ⟨product.1, ?_⟩
  rw [product.2]
  simpa using negative.2

private theorem odd_predecessor_negative {value : ℚ}
    (negative : IsNegative 3 value) :
    IsNegative 3 ((2 * value - 1) / 3) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have numerator_negative : IsNegative 3 (2 * value - 1) := by
    have minus_one_unit : IsUnit 3 (-1 : ℚ) :=
      neg_hasValue (intCast_isUnit_of_not_dvd (by norm_num))
    simpa only [sub_eq_add_neg] using
      negative_add_unit (double_negative negative) minus_one_unit
  have numerator_exact :
      HasValue 3 (2 * value - 1) (padicValRat 3 (2 * value - 1)) :=
    ⟨numerator_negative.1, rfl⟩
  have three_value : HasValue 3 (3 : ℚ) 1 := by
    simpa using (primePower_hasValue (prime := 3) 1)
  have quotient := div_hasValue numerator_exact three_value
  refine ⟨quotient.1, ?_⟩
  rw [quotient.2]
  have numerator_lt := numerator_negative.2
  omega

private theorem odd_integer_predecessor_negative
    (target : ℤ) (illegal : ¬(3 : ℤ) ∣ 2 * target - 1) :
    IsNegative 3 ((((2 * target - 1 : ℤ) : ℚ)) / 3) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have numerator_unit :
      HasValue 3 ((2 * target - 1 : ℤ) : ℚ) 0 :=
    intCast_isUnit_of_not_dvd illegal
  have three_value : HasValue 3 (3 : ℚ) 1 := by
    simpa using (primePower_hasValue (prime := 3) 1)
  have quotient := div_hasValue numerator_unit three_value
  refine ⟨quotient.1, ?_⟩
  rw [quotient.2]
  norm_num

/-- Every inverse-branch word either remains an integral shortcut-Collatz predecessor path or
has permanently negative 3-adic valuation. -/
theorem predecessorState_reaches_or_negative (word : List Bool) :
    (∃ value : ℤ,
      predecessorState word = value ∧ ReachesOne value) ∨
      IsNegative 3 (predecessorState word) := by
  induction word with
  | nil =>
      exact Or.inl ⟨1, by norm_num, .one⟩
  | cons label word induction =>
      rw [predecessorState_cons]
      rcases induction with ⟨value, state_eq, reaches⟩ | negative
      · rw [state_eq]
        cases label
        · by_cases legal : (3 : ℤ) ∣ 2 * value - 1
          · obtain ⟨source, source_eq⟩ := legal
            apply Or.inl
            refine ⟨source, ?_, .odd reaches source_eq⟩
            change (2 * (value : ℚ) - 1) / 3 = (source : ℚ)
            apply (div_eq_iff (by norm_num : (3 : ℚ) ≠ 0)).2
            simpa [mul_comm] using (show
              (2 * value - 1 : ℚ) = 3 * source by exact_mod_cast source_eq)
          · apply Or.inr
            simpa [predecessor] using
              odd_integer_predecessor_negative value legal
        · exact Or.inl ⟨2 * value, by
            simp only [predecessor]
            exact_mod_cast rfl, .even reaches⟩
      · cases label
        · exact Or.inr (odd_predecessor_negative negative)
        · exact Or.inr (double_negative negative)

private theorem integer_not_negative (value : ℤ) :
    ¬IsNegative 3 (value : ℚ) := by
  intro negative
  change (value : ℚ) ≠ 0 ∧ padicValRat 3 (value : ℚ) < 0 at negative
  have valuation_negative := negative.2
  rw [padicValRat.of_int] at valuation_negative
  exact (not_lt_of_ge (Int.natCast_nonneg _)) valuation_negative

private theorem exists_predecessorState_eq_of_reaches
    {value : ℤ} (reaches : ReachesOne value) :
    ∃ word : List Bool, predecessorState word = value := by
  induction reaches with
  | one =>
      exact ⟨[], by norm_num⟩
  | @even target _ induction =>
      obtain ⟨word, state_eq⟩ := induction
      refine ⟨true :: word, ?_⟩
      simp [predecessor, state_eq]
  | @odd target source _ source_eq induction =>
      obtain ⟨word, state_eq⟩ := induction
      refine ⟨false :: word, ?_⟩
      rw [predecessorState_cons, state_eq]
      change (2 * (target : ℚ) - 1) / 3 = (source : ℚ)
      apply (div_eq_iff (by norm_num : (3 : ℚ) ≠ 0)).2
      simpa [mul_comm] using (show
        (2 * target - 1 : ℚ) = 3 * source by exact_mod_cast source_eq)

/-- A rational inverse-branch word reaches an integer exactly when that integer reaches one
under shortcut Collatz. -/
theorem exists_predecessorState_eq_iff (value : ℤ) :
    (∃ word : List Bool, predecessorState word = value) ↔
      ReachesOne value := by
  constructor
  · rintro ⟨word, state_eq⟩
    rcases predecessorState_reaches_or_negative word with
      ⟨reached, reached_eq, reaches⟩ | negative
    · have reached_cast : (reached : ℚ) = (value : ℚ) := reached_eq.symm.trans state_eq
      have reached_eq_value : reached = value := by exact_mod_cast reached_cast
      exact reached_eq_value ▸ reaches
    · exact ((integer_not_negative value) (state_eq ▸ negative)).elim
  · exact exists_predecessorState_eq_of_reaches

/-- Raw projective matrix for the even inverse branch. -/
def evenMatrix : Square (Fin 2) ℚ :=
  !![2, 0; 0, 1]

/-- Raw projective matrix for the odd inverse branch. -/
def oddMatrix : Square (Fin 2) ℚ :=
  !![2, -1; 0, 3]

/-- Raw Collatz predecessor generator in the `G,H` incidence order. -/
def rawGenerator : Bool → Square (Fin 2) ℚ
  | false => oddMatrix
  | true => evenMatrix

/-- Homogeneous scale introduced by one raw predecessor letter. -/
def branchScale : Bool → ℚ
  | false => 3
  | true => 1

/-- Homogeneous scale introduced by a complete raw predecessor word. -/
def wordScale : List Bool → ℚ
  | [] => 1
  | label :: word => branchScale label * wordScale word

private theorem rawGenerator_mulVec (label : Bool) (value : ℚ) :
    rawGenerator label *ᵥ ![value, 1] =
      branchScale label • ![predecessor label value, 1] := by
  cases label <;>
    ext i <;>
    fin_cases i <;>
    simp [rawGenerator, oddMatrix, evenMatrix, branchScale, predecessor,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- Raw matrix multiplication realizes the inverse-branch word exactly. -/
theorem rawProduct_mulVec (word : List Bool) :
    wordProduct rawGenerator word *ᵥ ![(1 : ℚ), 1] =
      wordScale word • ![predecessorState word, 1] := by
  induction word with
  | nil =>
      simp [wordScale]
  | cons label word induction =>
      rw [wordProduct_cons, ← Matrix.mulVec_mulVec, induction,
        Matrix.mulVec_smul, rawGenerator_mulVec, smul_smul]
      simp only [wordScale, predecessorState_cons]
      rw [mul_comm]

/-- Incidence row selecting one integral target. -/
def targetRow (value : ℤ) : Fin 2 → ℚ :=
  ![1, -value]

/-- Fixed projective source representing one. -/
def sourceColumn : Fin 2 → ℚ :=
  ![1, 1]

private theorem wordScale_ne_zero (word : List Bool) :
    wordScale word ≠ 0 := by
  induction word with
  | nil => norm_num [wordScale]
  | cons label word induction =>
      cases label <;> simp [wordScale, branchScale, induction]

/-- Raw projective incidence is the scaled difference between the word state and its target. -/
theorem rawIncidence_eq (value : ℤ) (word : List Bool) :
    ReverseEdge.incidence oddMatrix evenMatrix (targetRow value) sourceColumn word =
      wordScale word * (predecessorState word - value) := by
  rw [ReverseEdge.incidence]
  change targetRow value ⬝ᵥ wordProduct rawGenerator word *ᵥ sourceColumn = _
  rw [show sourceColumn = ![(1 : ℚ), 1] by rfl, rawProduct_mulVec]
  simp [targetRow, dotProduct, Fin.sum_univ_succ]
  ring

/-- Raw projective incidence reaches an integral target exactly when shortcut Collatz reaches
one from that target. -/
theorem exists_rawIncidence_zero_iff (value : ℤ) :
    (∃ word : List Bool,
      ReverseEdge.incidence oddMatrix evenMatrix
        (targetRow value) sourceColumn word = 0) ↔
      ReachesOne value := by
  rw [← exists_predecessorState_eq_iff]
  apply exists_congr
  intro word
  rw [rawIncidence_eq]
  constructor
  · intro product_zero
    have difference_zero :=
      (mul_eq_zero.mp product_zero).resolve_left (wordScale_ne_zero word)
    exact sub_eq_zero.mp difference_zero
  · intro state_eq
    rw [state_eq, sub_self, mul_zero]

/-- First scalar used to normalize the Collatz incidence instance. -/
def lambda (value : ℤ) : ℚ :=
  1 / 2 - value

/-- Second raw exceptional scalar. -/
def mu (value : ℤ) : ℚ :=
  -3 * value

/-- Normalized even predecessor generator. -/
def H (value : ℤ) : Square (Fin 2) ℚ :=
  lambda value • evenMatrix

/-- Normalized odd predecessor generator. -/
def G (value : ℤ) : Square (Fin 2) ℚ :=
  (lambda value ^ 2 / mu value) • oddMatrix

private theorem lambda_ne_zero (value : ℤ) :
    lambda value ≠ 0 := by
  intro lambda_zero
  have rational_eq : (1 : ℚ) = 2 * value := by
    rw [lambda] at lambda_zero
    linarith
  have integer_eq : (1 : ℤ) = 2 * value := by
    exact_mod_cast rational_eq
  omega

private theorem mu_ne_zero {value : ℤ} (value_ne : value ≠ 0) :
    mu value ≠ 0 := by
  intro mu_zero
  have value_zero : value = 0 := by
    have rational_zero : (value : ℚ) = 0 := by
      rw [mu] at mu_zero
      linarith
    exact_mod_cast rational_zero
  exact value_ne value_zero

/-- Both normalized Collatz generators are units away from the nongeneric zero target. -/
theorem generators_isUnit {value : ℤ} (value_ne : value ≠ 0) :
    IsUnit (G value) ∧ IsUnit (H value) := by
  constructor
  · rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    simp [G, oddMatrix, Matrix.det_fin_two, lambda_ne_zero value,
      mu_ne_zero value_ne]
  · rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    simp [H, evenMatrix, Matrix.det_fin_two, lambda_ne_zero value]

/-- The fixed Collatz family lies in the exact `α=β=1` normalized GPI₂ chart. -/
theorem normalizedScalars {value : ℤ} (value_ne : value ≠ 0) :
    ReverseEdge.alpha (H value) (targetRow value) sourceColumn = 1 ∧
      ReverseEdge.beta (G value) (H value) (targetRow value) sourceColumn = 1 := by
  let pulled : Fin 2 → ℚ :=
    (lambda value)⁻¹ • ![(1 / 2 : ℚ), 1]
  have H_unit : IsUnit (H value) := (generators_isUnit value_ne).2
  have pulled_action : H value *ᵥ pulled = sourceColumn := by
    ext i
    fin_cases i <;>
      simp [H, evenMatrix, pulled, sourceColumn, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ, lambda_ne_zero value]
    all_goals field_simp [lambda_ne_zero value]
  have pulled_eq :
      ReverseEdge.pulledColumn (H value) sourceColumn = pulled :=
    nonsingInv_mulVec_eq_of_mulVec_eq H_unit pulled_action
  let first : Fin 2 → ℚ :=
    ![0, 3 / mu value]
  have first_action :
      H value *ᵥ first = G value *ᵥ pulled := by
    ext i
    fin_cases i <;>
      simp [H, G, oddMatrix, evenMatrix, pulled, first, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ]
    all_goals field_simp [lambda_ne_zero value, mu_ne_zero value_ne]
    all_goals ring
  have first_eq :
      ReverseEdge.firstVector (G value) (H value) sourceColumn = first := by
    rw [ReverseEdge.firstVector, pulled_eq]
    exact nonsingInv_mulVec_eq_of_mulVec_eq H_unit first_action
  constructor
  · rw [ReverseEdge.alpha, pulled_eq]
    calc
      targetRow value ⬝ᵥ pulled =
          (lambda value)⁻¹ * (1 / 2 - value) := by
        simp [targetRow, pulled, dotProduct, Fin.sum_univ_succ]
        ring
      _ = 1 := by
        rw [← lambda]
        exact inv_mul_cancel₀ (lambda_ne_zero value)
  · rw [ReverseEdge.beta, first_eq]
    calc
      targetRow value ⬝ᵥ first =
          -(value : ℚ) * (3 / mu value) := by
        simp [targetRow, first, dotProduct, Fin.sum_univ_succ]
      _ = 1 := by
        rw [mu]
        field_simp [mu_ne_zero value_ne]

/-- Nonzero scalar relating each normalized letter to its raw projective map. -/
def normalizedScale (value : ℤ) : Bool → ℚ
  | false => lambda value ^ 2 / mu value
  | true => lambda value

private theorem normalizedGenerator_eq (value : ℤ) :
    ReverseEdge.incidenceGenerator (G value) (H value) =
      fun label => normalizedScale value label • rawGenerator label := by
  funext label
  cases label <;> rfl

private theorem normalizedScale_ne_zero
    {value : ℤ} (value_ne : value ≠ 0) :
    ∀ label, normalizedScale value label ≠ 0 := by
  intro label
  cases label
  · exact div_ne_zero (pow_ne_zero _ (lambda_ne_zero value))
      (mu_ne_zero value_ne)
  · exact lambda_ne_zero value

/-- Normalization preserves the complete Collatz incidence zero language. -/
theorem normalizedIncidence_zero_iff
    {value : ℤ} (value_ne : value ≠ 0) (word : List Bool) :
    ReverseEdge.incidence (G value) (H value)
        (targetRow value) sourceColumn word = 0 ↔
      ReverseEdge.incidence oddMatrix evenMatrix
        (targetRow value) sourceColumn word = 0 := by
  have scaled_eq :
      ReverseEdge.incidence (G value) (H value)
          (targetRow value) sourceColumn word =
        (word.map (normalizedScale value)).prod *
          ReverseEdge.incidence oddMatrix evenMatrix
            (targetRow value) sourceColumn word := by
    rw [ReverseEdge.incidence, ReverseEdge.incidence, normalizedGenerator_eq,
      wordProduct_smulMatrix, Matrix.smul_mulVec, dotProduct_smul]
    rfl
  rw [scaled_eq]
  have product_ne :
      (word.map (normalizedScale value)).prod ≠ 0 := by
    apply List.prod_ne_zero
    intro zero_mem
    obtain ⟨label, _, scale_zero⟩ := List.mem_map.mp zero_mem
    exact normalizedScale_ne_zero value_ne label scale_zero
  constructor
  · intro scaled_zero
    exact (mul_eq_zero.mp scaled_zero).resolve_left product_ne
  · intro raw_zero
    rw [raw_zero, mul_zero]

/-- Exact reduction from pointwise shortcut-Collatz reachability to normalized GPI₂. -/
theorem exists_normalizedIncidence_zero_iff
    {value : ℤ} (value_ne : value ≠ 0) :
    (∃ word : List Bool,
      ReverseEdge.incidence (G value) (H value)
        (targetRow value) sourceColumn word = 0) ↔
      ReachesOne value := by
  rw [← exists_rawIncidence_zero_iff]
  apply exists_congr
  exact normalizedIncidence_zero_iff value_ne

end MatrixMortality.ProjectiveCollatz
