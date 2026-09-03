import MatrixMortality.InterfaceCompression
import MatrixMortality.LinearRepresentation
import MatrixMortality.TerminalTile

/-!
# Split return families

A finite-rank generator `U * V` cuts every intervening power of an ambient generator down to
the interface return `V * A ^ n * U`. Explicit splittings of `U` and `V` make this compression
reflect zero exactly. No dimension, field, or rank calculation is intrinsic to the argument.
-/

namespace MatrixMortality

open scoped Matrix

namespace ReturnFamily

variable {R Large Small : Type*} [CommSemiring R]
  [Fintype Large] [DecidableEq Large] [Fintype Small] [DecidableEq Small]

/-- The interface action induced by waiting `n` ambient steps between two finite-rank cuts. -/
def returnMatrix (ambient : Square Large R) (input : Matrix Large Small R)
    (output : Matrix Small Large R) (n : Nat) : Square Small R :=
  output * ambient ^ n * input

/-- Product of an arbitrary list of interface returns. -/
def returnProduct (ambient : Square Large R) (input : Matrix Large Small R)
    (output : Matrix Small Large R) (waits : List Nat) : Square Small R :=
  wordProduct (returnMatrix ambient input output) waits

/-- Ambient product beginning and ending with the finite-rank cut `input * output`. -/
def blockedProduct (ambient cut : Square Large R) : List Nat → Square Large R
  | [] => cut
  | wait :: waits => cut * ambient ^ wait * blockedProduct ambient cut waits

/-- Two-generator family whose ordinary letter is `ambient` and whose `none` letter is the cut. -/
def pairGenerator (ambient cut : Square Large R) : Option Unit → Square Large R :=
  separatedGenerator cut (fun _ => ambient)

private def pairLabelEquiv : Option Unit ≃ Unit ⊕ Unit where
  toFun
    | none => .inr ()
    | some _ => .inl ()
  invFun
    | .inl _ => some ()
    | .inr _ => none
  left_inv label := by cases label <;> rfl
  right_inv label := by rcases label with (_ | _) <;> rfl

omit [CommSemiring R] [Fintype Large] [DecidableEq Large] in
@[simp]
theorem pairGenerator_none (ambient cut : Square Large R) :
    pairGenerator ambient cut none = cut := rfl

omit [CommSemiring R] [Fintype Large] [DecidableEq Large] in
@[simp]
theorem pairGenerator_some (ambient cut : Square Large R) (point : Unit) :
    pairGenerator ambient cut (some point) = ambient := rfl

/-- Physical word beginning and ending with a cut and realizing the listed ambient waits. -/
def blockedWord : List Nat → List (Option Unit)
  | [] => [none]
  | wait :: waits => none :: (List.replicate wait (some ()) ++ blockedWord waits)

/-! ## Finite block-Hankel witnesses -/

/-- A coefficient Hankel section may choose return times and interface coordinates
independently in each row and column. -/
def finiteCoefficientHankel {P : Type*} (series : Nat → Square Small R)
    (left right : P → Nat × Small) : Square P R :=
  fun i j => series ((left i).1 + (right j).1) (left i).2 (right j).2

/-- Observable coefficient rows selected independently by time and interface coordinate. -/
def coefficientPrefixRows {P : Type*} (ambient : Square Large R)
    (output : Matrix Small Large R) (index : P → Nat × Small) :
    Matrix P Large R :=
  fun row state => (output * ambient ^ (index row).1) (index row).2 state

/-- Reachable coefficient columns selected independently by time and interface coordinate. -/
def coefficientSuffixColumns {P : Type*} (ambient : Square Large R)
    (input : Matrix Large Small R) (index : P → Nat × Small) :
    Matrix Large P R :=
  fun state column => (ambient ^ (index column).1 * input) state (index column).2

omit [Fintype Small] [DecidableEq Small] in
/-- Every finite coefficient Hankel section factors through the ambient state space. -/
theorem finiteCoefficientHankel_factor {P : Type*}
    (ambient : Square Large R) (input : Matrix Large Small R)
    (output : Matrix Small Large R) (left right : P → Nat × Small) :
    finiteCoefficientHankel (returnMatrix ambient input output) left right =
      coefficientPrefixRows ambient output left *
        coefficientSuffixColumns ambient input right := by
  ext i j
  change
    (output * ambient ^ ((left i).1 + (right j).1) * input)
        (left i).2 (right j).2 =
      ((output * ambient ^ (left i).1) *
        (ambient ^ (right j).1 * input)) (left i).2 (right j).2
  rw [pow_add]
  simp only [Matrix.mul_assoc]

/-- A nonsingular coefficient Hankel section lower-bounds every exact ambient realization. -/
theorem coefficientHankel_card_le
    {K P Big Interface : Type*} [Field K]
    [Fintype P] [DecidableEq P]
    [Fintype Big] [DecidableEq Big]
    (ambient : Square Big K) (input : Matrix Big Interface K)
    (output : Matrix Interface Big K) (left right : P → Nat × Interface)
    (det_ne_zero :
      (finiteCoefficientHankel (returnMatrix ambient input output) left right).det ≠ 0) :
    Fintype.card P ≤ Fintype.card Big := by
  apply card_le_of_det_rectangular_product_ne_zero
    (coefficientPrefixRows ambient output left)
    (coefficientSuffixColumns ambient input right)
  rw [← finiteCoefficientHankel_factor]
  exact det_ne_zero

/-- Finite block-Hankel section of a square matrix sequence. -/
def finiteReturnHankel {P : Type*} (series : Nat → Square Small R)
    (leftTimes rightTimes : P → Nat) : Square (P × Small) R :=
  fun left right => series (leftTimes left.1 + rightTimes right.1) left.2 right.2

/-- Reachable block rows selected by return times. -/
def returnPrefixRows {P : Type*} (ambient : Square Large R)
    (output : Matrix Small Large R) (times : P → Nat) :
    Matrix (P × Small) Large R :=
  fun row state => (output * ambient ^ times row.1) row.2 state

/-- Observable block columns selected by return times. -/
def returnSuffixColumns {P : Type*} (ambient : Square Large R)
    (input : Matrix Large Small R) (times : P → Nat) :
    Matrix Large (P × Small) R :=
  fun state column => (ambient ^ times column.1 * input) state column.2

omit [Fintype Small] [DecidableEq Small] in
/-- Every finite block-Hankel section of a return sequence factors through the ambient state
space. -/
theorem finiteReturnHankel_factor {P : Type*}
    (ambient : Square Large R) (input : Matrix Large Small R)
    (output : Matrix Small Large R) (leftTimes rightTimes : P → Nat) :
    finiteReturnHankel (returnMatrix ambient input output) leftTimes rightTimes =
      returnPrefixRows ambient output leftTimes *
        returnSuffixColumns ambient input rightTimes := by
  ext left right
  change
    (output * ambient ^ (leftTimes left.1 + rightTimes right.1) * input) left.2 right.2 =
      ((output * ambient ^ leftTimes left.1) *
        (ambient ^ rightTimes right.1 * input)) left.2 right.2
  rw [pow_add]
  simp only [Matrix.mul_assoc]

/-- A nonsingular finite block-Hankel section lower-bounds every exact ambient realization of a
return sequence. -/
theorem returnHankel_card_le
    {K P Big Interface : Type*} [Field K]
    [Fintype P] [DecidableEq P]
    [Fintype Big] [DecidableEq Big]
    [Fintype Interface] [DecidableEq Interface]
    (ambient : Square Big K) (input : Matrix Big Interface K)
    (output : Matrix Interface Big K) (leftTimes rightTimes : P → Nat)
    (det_ne_zero :
      (finiteReturnHankel (returnMatrix ambient input output)
        leftTimes rightTimes).det ≠ 0) :
    Fintype.card (P × Interface) ≤ Fintype.card Big := by
  apply card_le_of_det_rectangular_product_ne_zero
    (returnPrefixRows ambient output leftTimes)
    (returnSuffixColumns ambient input rightTimes)
  rw [← finiteReturnHankel_factor]
  exact det_ne_zero

omit [DecidableEq Large] in
/-- A split input and split output reflect zero through every interface matrix. -/
theorem split_sandwich_eq_zero_iff
    (input : Matrix Large Small R) (output : Matrix Small Large R)
    (inputLeftInverse : Matrix Small Large R)
    (outputRightInverse : Matrix Large Small R)
    (left_inverse : inputLeftInverse * input = 1)
    (right_inverse : output * outputRightInverse = 1)
    (matrix : Square Small R) :
    input * matrix * output = 0 ↔ matrix = 0 := by
  constructor
  · intro sandwich_zero
    calc
      matrix = 1 * matrix * 1 := by simp
      _ = (inputLeftInverse * input) * matrix * (output * outputRightInverse) := by
        rw [left_inverse, right_inverse]
      _ = inputLeftInverse * (input * matrix * output) * outputRightInverse := by
        simp only [Matrix.mul_assoc]
      _ = 0 := by rw [sandwich_zero]; simp
  · rintro rfl
    simp

/-- Intercalating a cut between ambient powers is the blocked return product with exterior
ambient powers restored. -/
theorem intercalatedPowers_eq
    (ambient cut : Square Large R) (left right : Nat) :
    ∀ waits : List Nat,
      intercalatedProduct cut
          (ambient ^ left :: waits.map (ambient ^ ·) ++ [ambient ^ right]) =
        ambient ^ left * blockedProduct ambient cut waits * ambient ^ right
  | [] => by
      simp [intercalatedProduct, blockedProduct]
  | wait :: waits => by
      change
        ambient ^ left * cut *
            intercalatedProduct cut
              (ambient ^ wait :: waits.map (ambient ^ ·) ++ [ambient ^ right]) =
          ambient ^ left * blockedProduct ambient cut (wait :: waits) * ambient ^ right
      rw [intercalatedPowers_eq ambient cut wait right waits]
      simp [blockedProduct, Matrix.mul_assoc]

/-- `blockedWord` has exactly the blocked ambient product as its physical value. -/
theorem wordProduct_blockedWord
    (ambient cut : Square Large R) (waits : List Nat) :
    wordProduct (pairGenerator ambient cut) (blockedWord waits) =
      blockedProduct ambient cut waits := by
  induction waits with
  | nil =>
      simp [blockedWord, blockedProduct, pairGenerator, separatedGenerator]
  | cons wait waits induction =>
      rw [blockedWord]
      rw [wordProduct_cons (pairGenerator ambient cut) none
        (List.replicate wait (some ()) ++ blockedWord waits)]
      rw [pairGenerator_none]
      rw [wordProduct_append, induction]
      simp [wordProduct, List.map_replicate, blockedProduct, Matrix.mul_assoc]

/-- Every blocked ambient product is the corresponding return product inside the same cut. -/
theorem blockedProduct_eq_sandwich
    (ambient : Square Large R) (input : Matrix Large Small R)
    (output : Matrix Small Large R) (waits : List Nat) :
    blockedProduct ambient (input * output) waits =
      input * returnProduct ambient input output waits * output := by
  induction waits with
  | nil =>
      simp [blockedProduct, returnProduct]
  | cons wait waits induction =>
      rw [blockedProduct, induction]
      simp only [returnProduct, wordProduct_cons]
      simp [returnMatrix, Matrix.mul_assoc]

/-- Split finite-rank cuts reduce a blocked ambient zero exactly to an interface zero. -/
theorem blockedProduct_eq_zero_iff
    (ambient : Square Large R) (input : Matrix Large Small R)
    (output : Matrix Small Large R)
    (inputLeftInverse : Matrix Small Large R)
    (outputRightInverse : Matrix Large Small R)
    (left_inverse : inputLeftInverse * input = 1)
    (right_inverse : output * outputRightInverse = 1)
    (waits : List Nat) :
    blockedProduct ambient (input * output) waits = 0 ↔
      returnProduct ambient input output waits = 0 := by
  rw [blockedProduct_eq_sandwich]
  exact split_sandwich_eq_zero_iff input output inputLeftInverse outputRightInverse
    left_inverse right_inverse _

private theorem interfacePathProduct_eq_returnProduct
    (ambient : Square Large R) (input : Matrix Large Small R)
    (output : Matrix Small Large R) (steps : List (InterfaceCompression.Step Unit Unit)) :
    InterfaceCompression.pathProduct (fun _ : Unit => ambient) (fun _ => input)
        (fun _ => output) () steps =
      returnProduct ambient input output (steps.map fun step => step.1.length) := by
  induction steps with
  | nil => simp [InterfaceCompression.pathProduct, returnProduct]
  | cons step steps induction =>
      obtain ⟨word, target⟩ := step
      cases target
      rw [InterfaceCompression.pathProduct, List.map_cons, returnProduct, wordProduct_cons,
        induction]
      simp [InterfaceCompression.bridge, returnMatrix, returnProduct, wordProduct_const]

/-- A physical return pair is mortal exactly when either its ambient transition family or its
interface return family is mortal. This is the one-transition, one-cut interface-compression
theorem; no splitting or rank hypothesis is involved. -/
theorem pairGenerator_isMortal_iff_ambient_or_returnFamily
    (ambient : Square Large R) (input : Matrix Large Small R)
    (output : Matrix Small Large R) :
    IsMortal (pairGenerator ambient (input * output)) ↔
      IsMortal (fun _ : Unit => ambient) ∨ IsMortal (returnMatrix ambient input output) := by
  have generator_eq :
      InterfaceCompression.generator (fun _ : Unit => ambient) (fun _ : Unit => input)
          (fun _ : Unit => output) ∘ pairLabelEquiv =
        pairGenerator ambient (input * output) := by
    funext label
    cases label <;> rfl
  rw [← generator_eq, isMortal_comp_equiv, InterfaceCompression.isMortal_iff]
  apply or_congr_right
  constructor
  · rintro ⟨start, steps, steps_nonempty, path_zero⟩
    cases start
    let waits := steps.map fun step => step.1.length
    refine ⟨waits, by simpa [waits] using steps_nonempty, ?_⟩
    change returnProduct ambient input output waits = 0
    rw [← interfacePathProduct_eq_returnProduct ambient input output steps]
    exact path_zero
  · rintro ⟨waits, waits_nonempty, returns_zero⟩
    let steps : List (InterfaceCompression.Step Unit Unit) :=
      waits.map fun wait => (List.replicate wait (), ())
    refine ⟨(), steps, by simpa [steps] using waits_nonempty, ?_⟩
    rw [interfacePathProduct_eq_returnProduct ambient input output steps]
    have encoded_waits : steps.map (fun step => step.1.length) = waits := by
      simp [steps, Function.comp_def]
    rw [encoded_waits]
    exact returns_zero

/-- An invertible ambient generator and an arbitrary factored cut are mortal exactly when one
finite product of interface returns vanishes. -/
theorem pairGenerator_isMortal_iff
    [Nontrivial R] [Nonempty Large]
    (ambient : Square Large R) (input : Matrix Large Small R)
    (output : Matrix Small Large R)
    (ambient_unit : IsUnit ambient) :
    IsMortal (pairGenerator ambient (input * output)) ↔
      ∃ waits, returnProduct ambient input output waits = 0 := by
  rw [pairGenerator_isMortal_iff_ambient_or_returnFamily]
  have ambient_immortal : ¬IsMortal (fun _ : Unit => ambient) :=
    not_isMortal_of_forall_isUnit (fun _ : Unit => ambient) fun _ => ambient_unit
  rw [or_iff_right ambient_immortal]
  constructor
  · rintro ⟨waits, _, returns_zero⟩
    exact ⟨waits, returns_zero⟩
  · rintro ⟨waits, returns_zero⟩
    by_cases waits_nonempty : waits ≠ []
    · exact ⟨waits, waits_nonempty, returns_zero⟩
    · have waits_eq : waits = [] := not_ne_iff.mp waits_nonempty
      rw [waits_eq] at returns_zero
      have one_eq_zero : (1 : Square Small R) = 0 := by
        simpa [returnProduct] using returns_zero
      have return_zero : returnMatrix ambient input output 0 = 0 := by
        calc
          returnMatrix ambient input output 0 =
              returnMatrix ambient input output 0 * 1 := (Matrix.mul_one _).symm
          _ = returnMatrix ambient input output 0 * 0 :=
            congrArg (returnMatrix ambient input output 0 * ·) one_eq_zero
          _ = 0 := Matrix.mul_zero _
      exact ⟨[0], List.cons_ne_nil _ _, by simpa [returnProduct] using return_zero⟩

/-- A physical return pair whose zero-wait return is an outer product is mortal exactly
when one positive-return bridge vanishes. The positive returns may be singular or zero. -/
theorem pairGenerator_isMortal_iff_positiveBridge
    {K Big Interface : Type*} [Field K]
    [Fintype Big] [DecidableEq Big] [Nonempty Big]
    [Fintype Interface] [DecidableEq Interface] [Nonempty Interface]
    (ambient : Square Big K) (input : Matrix Big Interface K)
    (output : Matrix Interface Big K)
    (column row : Interface → K)
    (ambient_unit : IsUnit ambient)
    (zero_return :
      returnMatrix ambient input output 0 = Matrix.vecMulVec column row) :
    IsMortal (pairGenerator ambient (input * output)) ↔
      ∃ waits : List Nat,
        bridgeScalar column row
          (wordProduct (fun wait => returnMatrix ambient input output (wait + 1)) waits) = 0 := by
  rw [pairGenerator_isMortal_iff ambient input output ambient_unit]
  change
    (∃ waits, wordProduct (returnMatrix ambient input output) waits = 0) ↔ _
  rw [← isMortal_iff_exists_wordProduct_eq_zero]
  have separated_returns :
      separatedGenerator (Matrix.vecMulVec column row)
          (fun wait => returnMatrix ambient input output (wait + 1)) ∘
        natEquivOption =
          returnMatrix ambient input output := by
    funext wait
    cases wait with
    | zero => simpa [separatedGenerator] using zero_return.symm
    | succ wait => simp [separatedGenerator]
  rw [← separated_returns, isMortal_comp_equiv]
  exact mortal_adjoin_outer_iff
    (fun wait => returnMatrix ambient input output (wait + 1)) column row

section RankOne

variable {K Ambient : Type*} [Field K]
  [Fintype Ambient] [DecidableEq Ambient]

/-- A rank-one cut beside an invertible ambient generator is mortal exactly when one scalar
return vanishes. -/
theorem rankOnePair_isMortal_iff
    [Nonempty Ambient]
    (ambient : Square Ambient K) (input : Matrix Ambient Unit K)
    (output : Matrix Unit Ambient K)
    (ambient_unit : IsUnit ambient) :
    IsMortal (pairGenerator ambient (input * output)) ↔
      ∃ wait, returnMatrix ambient input output wait = 0 := by
  rw [pairGenerator_isMortal_iff ambient input output ambient_unit]
  constructor
  · rintro ⟨waits, product_zero⟩
    have factor_zero :
        ∃ wait ∈ waits, returnMatrix ambient input output wait = 0 :=
      (wordProduct_unitSquare_eq_zero_iff
        (returnMatrix ambient input output) waits).mp (by
          simpa [returnProduct] using product_zero)
    exact ⟨factor_zero.choose, factor_zero.choose_spec.2⟩
  · rintro ⟨wait, return_zero⟩
    refine ⟨[wait], ?_⟩
    simp [returnProduct, return_zero]

end RankOne

end ReturnFamily

end MatrixMortality
