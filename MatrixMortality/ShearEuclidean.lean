import MatrixMortality.CongruenceBlindOrbit

/-!
# Euclidean height for the step-three shear orbit

A reduced alternating word in the upper and lower step-three shears grows the
Archimedean height of `[1:1]` by at least a factor of two per syllable. Every
signed syllable exponent is also bounded by the endpoint height.
Determinant-one coprimality removes projective scaling, giving a finite search
envelope for every nonidentity orbit witness.
-/

set_option autoImplicit false

namespace MatrixMortality.ShearEuclidean

open scoped Matrix

private theorem upper_abs_growth
    (m n exponent : ℤ)
    (dominance : |m| ≤ |n|)
    (exponent_ne : exponent ≠ 0) :
    2 * |n| ≤ |m + 3 * exponent * n| := by
  have exponent_abs : (1 : ℤ) ≤ |exponent| := Int.one_le_abs exponent_ne
  have scaled : |n| ≤ |exponent| * |n| := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right exponent_abs (abs_nonneg n)
  have product_lower : 3 * |n| ≤ |3 * exponent * n| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℤ) ≤ 3)]
    nlinarith
  have reverse_triangle :
      |3 * exponent * n| - |m| ≤ |m + 3 * exponent * n| := by
    simpa only [abs_neg, sub_neg_eq_add, add_comm] using
      abs_sub_abs_le_abs_sub (3 * exponent * n) (-m)
  linarith

private theorem upper_natAbs_growth
    (m n exponent : ℤ)
    (dominance : m.natAbs ≤ n.natAbs)
    (exponent_ne : exponent ≠ 0) :
    2 * n.natAbs ≤ (m + 3 * exponent * n).natAbs := by
  have dominance_cast : (m.natAbs : ℤ) ≤ (n.natAbs : ℤ) := by
    exact_mod_cast dominance
  have dominance_abs : |m| ≤ |n| := by
    simpa only [Int.natCast_natAbs] using dominance_cast
  have growth := upper_abs_growth m n exponent dominance_abs exponent_ne
  rw [← Int.natCast_natAbs n,
    ← Int.natCast_natAbs (m + 3 * exponent * n)] at growth
  exact_mod_cast growth

private theorem upper_exponent_natAbs_le
    (m n exponent : ℤ)
    (dominance : m.natAbs ≤ n.natAbs)
    (exponent_ne : exponent ≠ 0)
    (n_ne : n ≠ 0) :
    exponent.natAbs ≤ (m + 3 * exponent * n).natAbs := by
  have dominance_cast : (m.natAbs : ℤ) ≤ (n.natAbs : ℤ) := by
    exact_mod_cast dominance
  have dominance_abs : |m| ≤ |n| := by
    simpa only [Int.natCast_natAbs] using dominance_cast
  have exponent_abs : (1 : ℤ) ≤ |exponent| := Int.one_le_abs exponent_ne
  have n_abs : (1 : ℤ) ≤ |n| := Int.one_le_abs n_ne
  have exponent_scaled : |exponent| ≤ |exponent| * |n| := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left n_abs (abs_nonneg exponent)
  have n_scaled : |n| ≤ |exponent| * |n| := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right exponent_abs (abs_nonneg n)
  have product_abs : |3 * exponent * n| = 3 * (|exponent| * |n|) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℤ) ≤ 3)]
    ring
  have reverse_triangle :
      |3 * exponent * n| - |m| ≤ |m + 3 * exponent * n| := by
    simpa only [abs_neg, sub_neg_eq_add, add_comm] using
      abs_sub_abs_le_abs_sub (3 * exponent * n) (-m)
  rw [product_abs] at reverse_triangle
  have exponent_le_abs : |exponent| ≤ |m + 3 * exponent * n| := by
    linarith
  have exponent_cast : (exponent.natAbs : ℤ) ≤
      ((m + 3 * exponent * n).natAbs : ℤ) := by
    simpa only [Int.natCast_natAbs] using exponent_le_abs
  exact_mod_cast exponent_cast

private theorem lower_natAbs_growth
    (m n exponent : ℤ)
    (dominance : n.natAbs ≤ m.natAbs)
    (exponent_ne : exponent ≠ 0) :
    2 * m.natAbs ≤ (n + 3 * exponent * m).natAbs :=
  upper_natAbs_growth n m exponent dominance exponent_ne

private theorem lower_exponent_natAbs_le
    (m n exponent : ℤ)
    (dominance : n.natAbs ≤ m.natAbs)
    (exponent_ne : exponent ≠ 0)
    (m_ne : m ≠ 0) :
    exponent.natAbs ≤ (n + 3 * exponent * m).natAbs :=
  upper_exponent_natAbs_le n m exponent dominance exponent_ne m_ne

/-- An integral homogeneous projective pair. -/
abbrev IntegralPair := ℤ × ℤ

/-- Archimedean height of an integral projective pair. -/
def pairHeight (pair : IntegralPair) : ℕ :=
  max pair.1.natAbs pair.2.natAbs

/-- The action of one signed step-three shear syllable on an integral pair. -/
def shearPair (index : Bool) (exponent : ℤ) (pair : IntegralPair) : IntegralPair :=
  if index then (pair.1, pair.2 + 3 * exponent * pair.1)
  else (pair.1 + 3 * exponent * pair.2, pair.2)

/-- Coordinate dominance required before applying a shear from one factor. -/
def AcceptsShear (index : Bool) (pair : IntegralPair) : Prop :=
  if index then pair.2.natAbs ≤ pair.1.natAbs
  else pair.1.natAbs ≤ pair.2.natAbs

/-- Strict coordinate dominance owned after applying a nonzero shear syllable. -/
def OwnsShearChamber (index : Bool) (pair : IntegralPair) : Prop :=
  if index then pair.1.natAbs < pair.2.natAbs
  else pair.2.natAbs < pair.1.natAbs

/-- A nonzero shear applied across the opposite dominance chamber at least doubles height and
lands strictly in its own chamber. -/
theorem shearPair_doubles_height
    (index : Bool) (exponent : ℤ) (pair : IntegralPair)
    (exponent_ne : exponent ≠ 0)
    (accepts : AcceptsShear index pair)
    (height_pos : 0 < pairHeight pair) :
    OwnsShearChamber index (shearPair index exponent pair) ∧
      2 * pairHeight pair ≤ pairHeight (shearPair index exponent pair) := by
  rcases pair with ⟨first, second⟩
  cases index
  · change first.natAbs ≤ second.natAbs at accepts
    change 0 < max first.natAbs second.natAbs at height_pos
    have coordinate_growth :=
      upper_natAbs_growth first second exponent accepts exponent_ne
    have second_pos : 0 < second.natAbs := by
      rw [Nat.max_eq_right accepts] at height_pos
      exact height_pos
    have strict_growth :
        second.natAbs < (first + 3 * exponent * second).natAbs := by
      omega
    constructor
    · exact strict_growth
    · change 2 * max first.natAbs second.natAbs ≤
        max (first + 3 * exponent * second).natAbs second.natAbs
      rw [Nat.max_eq_right accepts, Nat.max_eq_left strict_growth.le]
      exact coordinate_growth
  · change second.natAbs ≤ first.natAbs at accepts
    change 0 < max first.natAbs second.natAbs at height_pos
    have coordinate_growth :=
      lower_natAbs_growth first second exponent accepts exponent_ne
    have first_pos : 0 < first.natAbs := by
      rw [Nat.max_eq_left accepts] at height_pos
      exact height_pos
    have strict_growth :
        first.natAbs < (second + 3 * exponent * first).natAbs := by
      omega
    constructor
    · exact strict_growth
    · change 2 * max first.natAbs second.natAbs ≤
        max first.natAbs (second + 3 * exponent * first).natAbs
      rw [Nat.max_eq_left accepts, Nat.max_eq_right strict_growth.le]
      exact coordinate_growth

/-- The exponent of a nonzero shear across the opposite chamber is bounded by the output height. -/
theorem shearPair_exponent_natAbs_le_height
    (index : Bool) (exponent : ℤ) (pair : IntegralPair)
    (exponent_ne : exponent ≠ 0)
    (accepts : AcceptsShear index pair)
    (height_pos : 0 < pairHeight pair) :
    exponent.natAbs ≤ pairHeight (shearPair index exponent pair) := by
  rcases pair with ⟨first, second⟩
  cases index
  · change first.natAbs ≤ second.natAbs at accepts
    change 0 < max first.natAbs second.natAbs at height_pos
    have second_ne : second ≠ 0 := by
      rw [Nat.max_eq_right accepts] at height_pos
      exact Int.natAbs_ne_zero.mp height_pos.ne'
    have exponent_bound := upper_exponent_natAbs_le
      first second exponent accepts exponent_ne second_ne
    exact exponent_bound.trans (Nat.le_max_left _ _)
  · change second.natAbs ≤ first.natAbs at accepts
    change 0 < max first.natAbs second.natAbs at height_pos
    have first_ne : first ≠ 0 := by
      rw [Nat.max_eq_left accepts] at height_pos
      exact Int.natAbs_ne_zero.mp height_pos.ne'
    have exponent_bound := lower_exponent_natAbs_le
      first second exponent accepts exponent_ne first_ne
    exact exponent_bound.trans (Nat.le_max_right _ _)

private theorem accepts_of_opposite_owns
    {accepted owned : Bool} {pair : IntegralPair}
    (different : accepted ≠ owned)
    (owns : OwnsShearChamber owned pair) :
    AcceptsShear accepted pair := by
  cases accepted
  · cases owned
    · exact (different rfl).elim
    · change pair.1.natAbs < pair.2.natAbs at owns
      exact owns.le
  · cases owned
    · change pair.2.natAbs < pair.1.natAbs at owns
      exact owns.le
    · exact (different rfl).elim

/-- Evaluate a canonical nonempty reduced shear word on an integral pair. -/
def reducedPairAction {first last : Bool}
    (word : Monoid.CoprodI.NeWord (fun _ : Bool => Multiplicative ℤ) first last)
    (pair : IntegralPair) : IntegralPair :=
  word.toList.foldr
    (fun syllable tail => shearPair syllable.1 (Multiplicative.toAdd syllable.2) tail)
    pair

/-- Number of nonzero alternating cyclic syllables in a reduced shear word. -/
def reducedSyllableCount {first last : Bool}
    (word : Monoid.CoprodI.NeWord (fun _ : Bool => Multiplicative ℤ) first last) : ℕ :=
  word.toList.length

/-- Every signed exponent in a reduced word fits under one common numerical bound. -/
def ReducedExponentsBounded {first last : Bool}
    (word : Monoid.CoprodI.NeWord (fun _ : Bool => Multiplicative ℤ) first last)
    (bound : ℕ) : Prop :=
  ∀ syllable ∈ word.toList, (Multiplicative.toAdd syllable.2).natAbs ≤ bound

/-- Column-vector realization of an integral pair. -/
def pairVector (pair : IntegralPair) : Fin 2 → ℤ :=
  ![pair.1, pair.2]

theorem pairVector_injective : Function.Injective pairVector := by
  intro left right vectors_eq
  apply Prod.ext
  · exact congrFun vectors_eq 0
  · exact congrFun vectors_eq 1

private def reducedSyllableMatrix
    (syllable : Sigma fun _ : Bool => Multiplicative ℤ) :
    CongruenceBlindOrbit.Square₂ ℤ :=
  CongruenceBlindOrbit.modularShearPower
    (syllable.1, Multiplicative.toAdd syllable.2)

/-- Literal integral matrix product represented by a reduced shear word. -/
def reducedMatrixProduct {first last : Bool}
    (word : Monoid.CoprodI.NeWord (fun _ : Bool => Multiplicative ℤ) first last) :
    CongruenceBlindOrbit.Square₂ ℤ :=
  wordProduct reducedSyllableMatrix word.toList

private theorem reducedSyllableMatrix_det
    (syllable : Sigma fun _ : Bool => Multiplicative ℤ) :
    (reducedSyllableMatrix syllable).det = 1 := by
  rcases syllable with ⟨index, exponent⟩
  cases index <;>
    simp [reducedSyllableMatrix, CongruenceBlindOrbit.modularShearPower,
      CongruenceBlindOrbit.upperShear, CongruenceBlindOrbit.lowerShear,
      Matrix.det_fin_two]

private theorem reducedWordProduct_det
    (word : List (Sigma fun _ : Bool => Multiplicative ℤ)) :
    (wordProduct reducedSyllableMatrix word).det = 1 := by
  induction word with
  | nil => simp [wordProduct]
  | cons syllable tail induction =>
      rw [wordProduct_cons, Matrix.det_mul, reducedSyllableMatrix_det,
        induction, one_mul]

/-- Every reduced shear product is an integral determinant-one matrix. -/
theorem reducedMatrixProduct_det
    {first last : Bool}
    (word : Monoid.CoprodI.NeWord (fun _ : Bool => Multiplicative ℤ) first last) :
    (reducedMatrixProduct word).det = 1 :=
  reducedWordProduct_det word.toList

/-- The determinant-one matrix represented by a reduced shear word. -/
def reducedSLProduct
    {first last : Bool}
    (word : Monoid.CoprodI.NeWord (fun _ : Bool => Multiplicative ℤ) first last) :
    Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨reducedMatrixProduct word, reducedMatrixProduct_det word⟩

@[simp]
theorem reducedPairAction_singleton
    (index : Bool) (power : Multiplicative ℤ) (power_ne : power ≠ 1)
    (pair : IntegralPair) :
    reducedPairAction (Monoid.CoprodI.NeWord.singleton (i := index) power power_ne) pair =
      shearPair index (Multiplicative.toAdd power) pair := rfl

@[simp]
theorem reducedPairAction_append
    {first middle next last : Bool}
    (left : Monoid.CoprodI.NeWord (fun _ : Bool => Multiplicative ℤ) first middle)
    (different : middle ≠ next)
    (right : Monoid.CoprodI.NeWord (fun _ : Bool => Multiplicative ℤ) next last)
    (pair : IntegralPair) :
    reducedPairAction (Monoid.CoprodI.NeWord.append left different right) pair =
      reducedPairAction left (reducedPairAction right pair) := by
  simp [reducedPairAction, List.foldr_append]

@[simp]
theorem reducedMatrixProduct_singleton
    (index : Bool) (power : Multiplicative ℤ) (power_ne : power ≠ 1) :
    reducedMatrixProduct (Monoid.CoprodI.NeWord.singleton (i := index) power power_ne) =
      CongruenceBlindOrbit.modularShearPower
        (R := ℤ) (index, Multiplicative.toAdd power) := by
  simp [reducedMatrixProduct, reducedSyllableMatrix, wordProduct]

@[simp]
theorem reducedMatrixProduct_append
    {first middle next last : Bool}
    (left : Monoid.CoprodI.NeWord (fun _ : Bool => Multiplicative ℤ) first middle)
    (different : middle ≠ next)
    (right : Monoid.CoprodI.NeWord (fun _ : Bool => Multiplicative ℤ) next last) :
    reducedMatrixProduct (Monoid.CoprodI.NeWord.append left different right) =
      reducedMatrixProduct left * reducedMatrixProduct right := by
  simp [reducedMatrixProduct, wordProduct_append]

/-- The recursive pair evaluation is exactly multiplication by the represented integral matrix. -/
theorem reducedMatrixProduct_mulVec_pairVector
    {first last : Bool}
    (word : Monoid.CoprodI.NeWord (fun _ : Bool => Multiplicative ℤ) first last)
    (pair : IntegralPair) :
    reducedMatrixProduct word *ᵥ pairVector pair =
      pairVector (reducedPairAction word pair) := by
  induction word generalizing pair with
  | @singleton index power power_ne =>
      rw [reducedMatrixProduct_singleton, reducedPairAction_singleton]
      cases index
      · ext coordinate
        fin_cases coordinate
        · simp [CongruenceBlindOrbit.modularShearPower,
            CongruenceBlindOrbit.upperShear, shearPair, pairVector,
            Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
        · simp [CongruenceBlindOrbit.modularShearPower,
            CongruenceBlindOrbit.upperShear, shearPair, pairVector,
            Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      · ext coordinate
        fin_cases coordinate
        · simp [CongruenceBlindOrbit.modularShearPower,
            CongruenceBlindOrbit.lowerShear, shearPair, pairVector,
            Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
        · simp [CongruenceBlindOrbit.modularShearPower,
            CongruenceBlindOrbit.lowerShear, shearPair, pairVector,
            Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
          ring
  | @append first middle next last left different right left_induction right_induction =>
      rw [reducedMatrixProduct_append, reducedPairAction_append,
        ← Matrix.mulVec_mulVec, right_induction, left_induction]

/-- A reduced determinant-one shear product preserves coprimality of integral coordinates. -/
theorem reducedPairAction_isCoprime
    {first last : Bool}
    (word : Monoid.CoprodI.NeWord (fun _ : Bool => Multiplicative ℤ) first last)
    (pair : IntegralPair)
    (coprime : IsCoprime pair.1 pair.2) :
    IsCoprime (reducedPairAction word pair).1 (reducedPairAction word pair).2 := by
  have pair_coprime : IsCoprime (pairVector pair 0) (pairVector pair 1) := by
    simpa [pairVector] using coprime
  have image_coprime := pair_coprime.mulVecSL (reducedSLProduct word)
  change IsCoprime
      (Matrix.mulVec (reducedMatrixProduct word) (pairVector pair) 0)
      (Matrix.mulVec (reducedMatrixProduct word) (pairVector pair) 1) at image_coprime
  rw [reducedMatrixProduct_mulVec_pairVector] at image_coprime
  simpa [pairVector] using image_coprime

/-- Two coprime integral pairs on the same projective ray differ by sign only. -/
theorem coprime_pairs_eq_or_neg_of_cross_eq
    (left right : IntegralPair)
    (left_coprime : IsCoprime left.1 left.2)
    (right_coprime : IsCoprime right.1 right.2)
    (cross_eq : left.1 * right.2 = right.1 * left.2) :
    left = right ∨ left = (-right.1, -right.2) := by
  obtain ⟨u, v, bezout⟩ := right_coprime
  let scale := u * left.1 + v * left.2
  have first_eq : left.1 = scale * right.1 := by
    dsimp only [scale]
    calc
      left.1 = left.1 * (u * right.1 + v * right.2) := by rw [bezout, mul_one]
      _ = (u * left.1 + v * left.2) * right.1 := by
        rw [mul_add]
        linear_combination v * cross_eq
  have second_eq : left.2 = scale * right.2 := by
    dsimp only [scale]
    calc
      left.2 = left.2 * (u * right.1 + v * right.2) := by rw [bezout, mul_one]
      _ = (u * left.1 + v * left.2) * right.2 := by
        rw [mul_add]
        linear_combination -u * cross_eq
  have scale_dvd_first : scale ∣ left.1 := ⟨right.1, first_eq⟩
  have scale_dvd_second : scale ∣ left.2 := ⟨right.2, second_eq⟩
  have scale_unit : IsUnit scale :=
    left_coprime.isUnit_of_dvd' scale_dvd_first scale_dvd_second
  rcases Int.isUnit_iff.mp scale_unit with scale_one | scale_neg_one
  · left
    apply Prod.ext
    · simpa [scale_one] using first_eq
    · simpa [scale_one] using second_eq
  · right
    apply Prod.ext
    · simpa [scale_neg_one] using first_eq
    · simpa [scale_neg_one] using second_eq

/-- A reduced word applied across the chamber opposite its last factor grows by at least two per
syllable and lands in the chamber of its first factor. -/
theorem reducedPairAction_power_le_height
    {first last : Bool}
    (word : Monoid.CoprodI.NeWord (fun _ : Bool => Multiplicative ℤ) first last)
    (pair : IntegralPair)
    (accepts : AcceptsShear last pair)
    (height_pos : 0 < pairHeight pair) :
    OwnsShearChamber first (reducedPairAction word pair) ∧
      2 ^ reducedSyllableCount word * pairHeight pair ≤
        pairHeight (reducedPairAction word pair) := by
  induction word generalizing pair with
  | @singleton index power power_ne =>
      have exponent_ne : Multiplicative.toAdd power ≠ 0 := by
        simpa using power_ne
      have growth := shearPair_doubles_height index
        (Multiplicative.toAdd power) pair exponent_ne accepts height_pos
      simpa [reducedSyllableCount] using growth
  | @append first middle next last left different right left_induction right_induction =>
      have right_growth := right_induction pair accepts height_pos
      have left_accepts :
          AcceptsShear middle (reducedPairAction right pair) :=
        accepts_of_opposite_owns different right_growth.1
      have pair_le_right :
          pairHeight pair ≤ pairHeight (reducedPairAction right pair) := by
        calc
          pairHeight pair = 1 * pairHeight pair := by simp
          _ ≤ 2 ^ reducedSyllableCount right * pairHeight pair := by
            exact Nat.mul_le_mul_right _ (Nat.one_le_two_pow)
          _ ≤ pairHeight (reducedPairAction right pair) := right_growth.2
      have right_height_pos :
          0 < pairHeight (reducedPairAction right pair) :=
        height_pos.trans_le pair_le_right
      have left_growth := left_induction
        (reducedPairAction right pair) left_accepts right_height_pos
      constructor
      · simpa using left_growth.1
      · rw [reducedPairAction_append]
        calc
          2 ^ reducedSyllableCount (Monoid.CoprodI.NeWord.append left different right) *
                pairHeight pair =
              2 ^ reducedSyllableCount left *
                (2 ^ reducedSyllableCount right * pairHeight pair) := by
            simp [reducedSyllableCount, pow_add, mul_assoc]
          _ ≤ 2 ^ reducedSyllableCount left *
                pairHeight (reducedPairAction right pair) :=
            Nat.mul_le_mul_left _ right_growth.2
          _ ≤ pairHeight (reducedPairAction left
                (reducedPairAction right pair)) := left_growth.2

/-- Every exponent in a reduced word is bounded by the height of its endpoint. -/
theorem reducedPairAction_exponents_le_height
    {first last : Bool}
    (word : Monoid.CoprodI.NeWord (fun _ : Bool => Multiplicative ℤ) first last)
    (pair : IntegralPair)
    (accepts : AcceptsShear last pair)
    (height_pos : 0 < pairHeight pair) :
    ReducedExponentsBounded word (pairHeight (reducedPairAction word pair)) := by
  induction word generalizing pair with
  | @singleton index power power_ne =>
      have exponent_ne : Multiplicative.toAdd power ≠ 0 := by
        simpa using power_ne
      have exponent_bound := shearPair_exponent_natAbs_le_height index
        (Multiplicative.toAdd power) pair exponent_ne accepts height_pos
      intro syllable membership
      simp only [Monoid.CoprodI.NeWord.toList, List.mem_singleton] at membership
      subst syllable
      exact exponent_bound
  | @append first middle next last left different right left_induction right_induction =>
      have right_growth :=
        reducedPairAction_power_le_height right pair accepts height_pos
      have left_accepts :
          AcceptsShear middle (reducedPairAction right pair) :=
        accepts_of_opposite_owns different right_growth.1
      have pair_le_right :
          pairHeight pair ≤ pairHeight (reducedPairAction right pair) := by
        calc
          pairHeight pair = 1 * pairHeight pair := by simp
          _ ≤ 2 ^ reducedSyllableCount right * pairHeight pair := by
            exact Nat.mul_le_mul_right _ Nat.one_le_two_pow
          _ ≤ pairHeight (reducedPairAction right pair) := right_growth.2
      have right_height_pos :
          0 < pairHeight (reducedPairAction right pair) :=
        height_pos.trans_le pair_le_right
      have left_growth := reducedPairAction_power_le_height left
        (reducedPairAction right pair) left_accepts right_height_pos
      have right_le_final :
          pairHeight (reducedPairAction right pair) ≤
            pairHeight (reducedPairAction left (reducedPairAction right pair)) := by
        calc
          pairHeight (reducedPairAction right pair) =
              1 * pairHeight (reducedPairAction right pair) := by simp
          _ ≤ 2 ^ reducedSyllableCount left *
                pairHeight (reducedPairAction right pair) := by
            exact Nat.mul_le_mul_right _ Nat.one_le_two_pow
          _ ≤ pairHeight (reducedPairAction left
                (reducedPairAction right pair)) := left_growth.2
      have left_bounds := left_induction
        (reducedPairAction right pair) left_accepts right_height_pos
      have right_bounds := right_induction pair accepts height_pos
      intro syllable membership
      simp only [Monoid.CoprodI.NeWord.toList, List.mem_append] at membership
      rw [reducedPairAction_append]
      cases membership with
      | inl in_left => exact left_bounds syllable in_left
      | inr in_right => exact (right_bounds syllable in_right).trans right_le_final

/-- The primitive source pair `[1:1]`. -/
def sourcePair : IntegralPair := (1, 1)

theorem sourcePair_accepts (index : Bool) : AcceptsShear index sourcePair := by
  cases index <;> norm_num [AcceptsShear, sourcePair]

@[simp]
theorem sourcePair_height : pairHeight sourcePair = 1 := by
  norm_num [pairHeight, sourcePair]

/-- Every nonempty reduced step-three shear word has endpoint height at least exponential in its
syllable count. -/
theorem reducedPairAction_source_power_le_height
    {first last : Bool}
    (word : Monoid.CoprodI.NeWord (fun _ : Bool => Multiplicative ℤ) first last) :
    2 ^ reducedSyllableCount word ≤ pairHeight (reducedPairAction word sourcePair) := by
  have growth := reducedPairAction_power_le_height word sourcePair
    (sourcePair_accepts last) (by norm_num)
  simpa using growth.2

/-- Every exponent in a reduced word from `[1:1]` is bounded by its endpoint height. -/
theorem reducedPairAction_source_exponents_le_height
    {first last : Bool}
    (word : Monoid.CoprodI.NeWord (fun _ : Bool => Multiplicative ℤ) first last) :
    ReducedExponentsBounded word (pairHeight (reducedPairAction word sourcePair)) :=
  reducedPairAction_exponents_le_height word sourcePair
    (sourcePair_accepts last) (by norm_num)

/-- A projective hit on a coprime target pair obeys finite height bounds on its reduced syntax.
The cross-product equation is the homogeneous projective equality; coprimality removes every
scale except sign. -/
theorem finite_search_bounds_of_projective_hit
    {first last : Bool}
    (word : Monoid.CoprodI.NeWord (fun _ : Bool => Multiplicative ℤ) first last)
    (target : IntegralPair)
    (target_coprime : IsCoprime target.1 target.2)
    (cross_eq :
      (reducedPairAction word sourcePair).1 * target.2 =
        target.1 * (reducedPairAction word sourcePair).2) :
    2 ^ reducedSyllableCount word ≤ pairHeight target ∧
      ReducedExponentsBounded word (pairHeight target) := by
  have source_coprime : IsCoprime sourcePair.1 sourcePair.2 := by
    norm_num [sourcePair]
  have image_coprime :=
    reducedPairAction_isCoprime word sourcePair source_coprime
  have image_eq := coprime_pairs_eq_or_neg_of_cross_eq
    (reducedPairAction word sourcePair) target image_coprime target_coprime cross_eq
  have height_eq : pairHeight (reducedPairAction word sourcePair) = pairHeight target := by
    rcases image_eq with image_eq | image_eq
    · rw [image_eq]
    · rw [image_eq]
      simp [pairHeight]
  constructor
  · rw [← height_eq]
    exact reducedPairAction_source_power_le_height word
  · rw [← height_eq]
    exact reducedPairAction_source_exponents_le_height word

/-- Any nonidentity matrix-word witness from `[1:1]` obeys finite height bounds on both its
syllable count and every signed exponent. -/
theorem finite_search_bounds_of_matrix_hit
    {first last : Bool}
    (word : Monoid.CoprodI.NeWord (fun _ : Bool => Multiplicative ℤ) first last)
    (target : IntegralPair)
    (hit : reducedMatrixProduct word *ᵥ pairVector sourcePair = pairVector target) :
    2 ^ reducedSyllableCount word ≤ pairHeight target ∧
      ReducedExponentsBounded word (pairHeight target) := by
  have pair_eq : reducedPairAction word sourcePair = target := by
    apply pairVector_injective
    rw [← reducedMatrixProduct_mulVec_pairVector]
    exact hit
  subst target
  exact ⟨reducedPairAction_source_power_le_height word,
    reducedPairAction_source_exponents_le_height word⟩

end MatrixMortality.ShearEuclidean
