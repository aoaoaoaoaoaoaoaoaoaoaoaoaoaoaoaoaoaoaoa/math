import MatrixMortality.NearySideNormal
import MatrixMortality.LinearRepresentation
import MatrixMortality.TerminalTile

/-!
# Square-root punctuation

A distinguished matrix whose square is an outer product turns every adjacent pair of its
letters into exact rank-one punctuation. This file proves the complete free-monoid converse:
an arbitrary zero product exists exactly when the boundary coefficient vanishes on a word with
no adjacent punctuation letters. It then instantiates the construction by an explicit rational
rank-two square root of the side-normal Neary boundary.
-/

namespace MatrixMortality

open scoped Matrix

namespace SquareRootPunctuation

/-! ## The square-free residual language -/

/-- A physical word is punctuation-square-free when it has no factor `none, none`. -/
def IsSquareFree {α : Type*} (word : List (Option α)) : Prop :=
  ¬∃ left right : List (Option α), word = left ++ none :: none :: right

theorem isSquareFree_iff {α : Type*} (word : List (Option α)) :
    IsSquareFree word ↔
      ∀ left right : List (Option α), word ≠ left ++ none :: none :: right := by
  simp [IsSquareFree]

/-! ## Exact fracture at a punctuation square -/

section Fracture

variable {α ι K : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- The scalar seen between the boundary row and column by a physical word. -/
def coefficient (squareRoot : Square ι K) (generators : α → Square ι K)
    (column row : ι → K) (word : List (Option α)) : K :=
  bridgeScalar column row
    (wordProduct (separatedGenerator squareRoot generators) word)

theorem coefficient_append_square
    (squareRoot : Square ι K) (generators : α → Square ι K)
    (column row : ι → K)
    (square : squareRoot * squareRoot = Matrix.vecMulVec column row)
    (left right : List (Option α)) :
    coefficient squareRoot generators column row
        (left ++ none :: none :: right) =
      coefficient squareRoot generators column row left *
        coefficient squareRoot generators column row right := by
  let family := separatedGenerator squareRoot generators
  let leftProduct := wordProduct family left
  let rightProduct := wordProduct family right
  have product_eq :
      wordProduct family (left ++ none :: none :: right) =
        leftProduct * Matrix.vecMulVec column row * rightProduct := by
    simp only [wordProduct_append, wordProduct_cons, family, separatedGenerator,
      wordProduct_nil, Matrix.mul_one]
    rw [← Matrix.mul_assoc squareRoot squareRoot rightProduct, square]
    simp [leftProduct, rightProduct, Matrix.mul_assoc]
  have core_eq :
      leftProduct * Matrix.vecMulVec column row * rightProduct =
        Matrix.vecMulVec (leftProduct *ᵥ column) (row ᵥ* rightProduct) := by
    rw [mul_outer, outer_mul]
  rw [coefficient, product_eq, core_eq]
  simp only [coefficient, bridgeScalar, Matrix.dotProduct_mulVec,
    leftProduct, rightProduct, family]
  rw [vecMul_outer]
  simp only [Matrix.smul_dotProduct, Matrix.dotProduct_mulVec, smul_eq_mul]

/-- Every scalar-zero physical word contains a punctuation-square-free scalar-zero residual.
The residual may be empty; this is necessary when the two boundary vectors are orthogonal. -/
theorem exists_squareFree_zero_of_zero
    (squareRoot : Square ι K) (generators : α → Square ι K)
    (column row : ι → K)
    (square : squareRoot * squareRoot = Matrix.vecMulVec column row)
    (word : List (Option α))
    (zero : coefficient squareRoot generators column row word = 0) :
    ∃ residual : List (Option α),
      IsSquareFree residual ∧
        coefficient squareRoot generators column row residual = 0 := by
  have descend : ∀ n, ∀ candidate : List (Option α), candidate.length = n →
      coefficient squareRoot generators column row candidate = 0 →
      ∃ residual : List (Option α),
        IsSquareFree residual ∧
          coefficient squareRoot generators column row residual = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n induction =>
        intro candidate candidate_length candidate_zero
        by_cases squareFree : IsSquareFree candidate
        · exact ⟨candidate, squareFree, candidate_zero⟩
        · simp only [IsSquareFree, not_not] at squareFree
          obtain ⟨left, right, candidate_eq⟩ := squareFree
          have factor_zero :
              coefficient squareRoot generators column row left *
                  coefficient squareRoot generators column row right = 0 := by
            rw [← coefficient_append_square squareRoot generators column row square left right]
            simpa [candidate_eq] using candidate_zero
          rcases mul_eq_zero.mp factor_zero with left_zero | right_zero
          · apply induction left.length
            · rw [← candidate_length, candidate_eq]
              simp
            · exact rfl
            · exact left_zero
          · apply induction right.length
            · rw [← candidate_length, candidate_eq]
              simp
              omega
            · exact rfl
            · exact right_zero
  exact descend word.length word rfl zero

/-- A square-root punctuation family is mortal exactly when its boundary coefficient vanishes
on one punctuation-square-free word. This quantifies over the complete physical free monoid;
singular ordinary controls and malformed isolated punctuation remain inside the residual
language rather than being discarded. -/
theorem isMortal_iff_exists_squareFree_zero
    (squareRoot : Square ι K) (generators : α → Square ι K)
    (column row : ι → K)
    (square : squareRoot * squareRoot = Matrix.vecMulVec column row) :
    IsMortal (separatedGenerator squareRoot generators) ↔
      ∃ word : List (Option α),
        IsSquareFree word ∧ coefficient squareRoot generators column row word = 0 := by
  constructor
  · rintro ⟨word, _, product_zero⟩
    apply exists_squareFree_zero_of_zero squareRoot generators column row square word
    simp [coefficient, bridgeScalar, product_zero]
  · rintro ⟨word, _, coefficient_zero⟩
    refine ⟨none :: none :: word ++ [none, none], by simp, ?_⟩
    let family := separatedGenerator squareRoot generators
    have square_word_square :
        wordProduct family (none :: none :: word ++ [none, none]) =
          Matrix.vecMulVec column row * wordProduct family word *
            Matrix.vecMulVec column row := by
      change wordProduct family (([none, none] ++ word) ++ [none, none]) = _
      rw [wordProduct_append, wordProduct_append]
      simp [wordProduct, family, separatedGenerator, square]
    rw [square_word_square]
    rw [outer_mul, outer_mul_outer]
    have scalar_zero :
        row ᵥ* wordProduct family word ⬝ᵥ column = 0 := by
      rw [← Matrix.dotProduct_mulVec]
      simpa [coefficient, bridgeScalar, family] using coefficient_zero
    rw [scalar_zero, zero_smul]

end Fracture

/-! ## Boundary saturation forced by every nondegenerate square root -/

section BoundarySaturation

variable {α ι K : Type*} [Field K] [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
private theorem smul_vector_cancel {vector : ι → K} (vector_ne : vector ≠ 0)
    {first second : K} (equal : first • vector = second • vector) :
    first = second := by
  by_contra scalars_ne
  apply vector_ne
  funext i
  have coordinate := congr_fun equal i
  simp only [Pi.smul_apply, smul_eq_mul] at coordinate
  by_contra coordinate_ne
  exact scalars_ne (mul_right_cancel₀ coordinate_ne coordinate)

omit [Fintype ι] [DecidableEq ι] in
private theorem outer_left_cancel {column : ι → K} (column_ne : column ≠ 0)
    {first second : ι → K}
    (equal : Matrix.vecMulVec column first = Matrix.vecMulVec column second) :
    first = second := by
  by_contra rows_ne
  obtain ⟨j, coordinate_ne⟩ := Function.ne_iff.mp rows_ne
  apply column_ne
  funext i
  have entry := congr_fun (congr_fun equal i) j
  simp only [Matrix.vecMulVec_apply] at entry
  by_contra column_ne
  exact coordinate_ne (mul_left_cancel₀ column_ne entry)

omit [DecidableEq ι] in
private theorem outer_mulVec (column row active : ι → K) :
    Matrix.vecMulVec column row *ᵥ active = (row ⬝ᵥ active) • column := by
  ext i
  simp only [Matrix.mulVec, Matrix.vecMulVec_apply, Matrix.dotProduct,
    Pi.smul_apply, smul_eq_mul]
  simp only [mul_assoc]
  rw [← Finset.mul_sum]
  ring

omit [DecidableEq ι] in
/-- Every square root of a nondegenerate rank-one separator scales both boundary vectors by the
same nonzero scalar. The conclusion is independent of dimension and of the square root's rank. -/
theorem squareRoot_boundary_eigenvectors
    (squareRoot : Square ι K) (column row : ι → K)
    (square : squareRoot * squareRoot = Matrix.vecMulVec column row)
    (pairing_ne : row ⬝ᵥ column ≠ 0) :
    ∃ scalar : K,
      scalar ≠ 0 ∧
        scalar ^ 2 = row ⬝ᵥ column ∧
        squareRoot *ᵥ column = scalar • column ∧
        row ᵥ* squareRoot = scalar • row := by
  let pairing := row ⬝ᵥ column
  have column_ne : column ≠ 0 := by
    intro column_zero
    apply pairing_ne
    simp [column_zero]
  have commutes :
      squareRoot * Matrix.vecMulVec column row =
        Matrix.vecMulVec column row * squareRoot := by
    rw [← square]
    simp [Matrix.mul_assoc]
  have proportional :
      pairing • (squareRoot *ᵥ column) =
        (row ⬝ᵥ squareRoot *ᵥ column) • column := by
    have applied := congrArg (fun matrix => matrix *ᵥ column) commutes
    rw [mul_outer, outer_mul] at applied
    change
      Matrix.vecMulVec (squareRoot *ᵥ column) row *ᵥ column =
        Matrix.vecMulVec column (row ᵥ* squareRoot) *ᵥ column at applied
    rw [outer_mulVec, outer_mulVec] at applied
    simpa [pairing, Matrix.dotProduct_mulVec] using applied
  let scalar := pairing⁻¹ * (row ⬝ᵥ squareRoot *ᵥ column)
  have column_eigen : squareRoot *ᵥ column = scalar • column := by
    calc
      squareRoot *ᵥ column = pairing⁻¹ • (pairing • (squareRoot *ᵥ column)) := by
        simp [pairing, pairing_ne]
      _ = pairing⁻¹ • ((row ⬝ᵥ squareRoot *ᵥ column) • column) := by
        rw [proportional]
      _ = scalar • column := by
        simp [scalar, smul_smul]
  have square_eigen : (scalar ^ 2) • column = pairing • column := by
    calc
      (scalar ^ 2) • column =
          squareRoot *ᵥ (squareRoot *ᵥ column) := by
            rw [column_eigen, Matrix.mulVec_smul, column_eigen]
            simp [pow_two, smul_smul]
      _ = pairing • column := by
        calc
          squareRoot *ᵥ (squareRoot *ᵥ column) =
              (squareRoot * squareRoot) *ᵥ column := by
            rw [Matrix.mulVec_mulVec]
          _ = Matrix.vecMulVec column row *ᵥ column := by rw [square]
          _ = pairing • column := by rw [outer_mulVec]
  have scalar_square : scalar ^ 2 = pairing :=
    smul_vector_cancel column_ne square_eigen
  have scalar_ne : scalar ≠ 0 := by
    intro scalar_zero
    apply pairing_ne
    change pairing = 0
    rw [← scalar_square, scalar_zero]
    simp
  have row_eigen : row ᵥ* squareRoot = scalar • row := by
    apply outer_left_cancel column_ne
    calc
      Matrix.vecMulVec column (row ᵥ* squareRoot) =
          Matrix.vecMulVec column row * squareRoot := by
            rw [outer_mul]
      _ = squareRoot * Matrix.vecMulVec column row := commutes.symm
      _ = Matrix.vecMulVec (squareRoot *ᵥ column) row := by
        rw [mul_outer]
      _ = Matrix.vecMulVec column (scalar • row) := by
        rw [column_eigen]
        ext i j
        simp [Matrix.vecMulVec_apply]
        ring
  exact ⟨scalar, scalar_ne, scalar_square, column_eigen, row_eigen⟩

/-- Prefixing one isolated square-root letter preserves scalar vanishing for every surrounding
word and every choice of ordinary generators. -/
theorem squareRoot_coefficient_cons_zero_iff
    (squareRoot : Square ι K) (generators : α → Square ι K)
    (column row : ι → K)
    (square : squareRoot * squareRoot = Matrix.vecMulVec column row)
    (pairing_ne : row ⬝ᵥ column ≠ 0) (word : List (Option α)) :
    coefficient squareRoot generators column row (none :: word) = 0 ↔
      coefficient squareRoot generators column row word = 0 := by
  obtain ⟨scalar, scalar_ne, _, _, row_eigen⟩ :=
    squareRoot_boundary_eigenvectors squareRoot column row square pairing_ne
  have scaled :
      coefficient squareRoot generators column row (none :: word) =
        scalar * coefficient squareRoot generators column row word := by
    simp only [coefficient, bridgeScalar, wordProduct_cons, separatedGenerator]
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, row_eigen]
    simp [Matrix.smul_dotProduct, smul_eq_mul]
  rw [scaled, mul_eq_zero]
  simp [scalar_ne]

/-- Suffixing one isolated square-root letter preserves scalar vanishing for every surrounding
word and every choice of ordinary generators. -/
theorem squareRoot_coefficient_append_zero_iff
    (squareRoot : Square ι K) (generators : α → Square ι K)
    (column row : ι → K)
    (square : squareRoot * squareRoot = Matrix.vecMulVec column row)
    (pairing_ne : row ⬝ᵥ column ≠ 0) (word : List (Option α)) :
    coefficient squareRoot generators column row (word ++ [none]) = 0 ↔
      coefficient squareRoot generators column row word = 0 := by
  obtain ⟨scalar, scalar_ne, _, column_eigen, _⟩ :=
    squareRoot_boundary_eigenvectors squareRoot column row square pairing_ne
  have scaled :
      coefficient squareRoot generators column row (word ++ [none]) =
        scalar * coefficient squareRoot generators column row word := by
    simp only [coefficient, bridgeScalar, wordProduct_append, wordProduct_cons,
      wordProduct_nil, Matrix.mul_one, separatedGenerator]
    rw [← Matrix.mulVec_mulVec, column_eigen, Matrix.mulVec_smul]
    simp [Matrix.dotProduct_smul, smul_eq_mul, mul_comm]
  rw [scaled, mul_eq_zero]
  simp [scalar_ne]

end BoundarySaturation

/-! ## Explicit side-normal square root -/

/-- The side-normal marker value is nonzero over `ℚ`. -/
theorem nearySideMarkerValue_ne_zero (β : Nat) : nearySideMarkerValue β ≠ 0 := by
  change (ternaryCode (nearyMarker β) : ℚ) ≠ 0
  exact_mod_cast ternaryCode_nearyMarker_ne_zero β

/-- The normalized side boundary column `γ / (λγ)`. -/
def normalizedNearyColumn (β : Nat) : Fin 3 → ℚ :=
  (nearySideMarkerValue β)⁻¹ • nearySideColumn β

/-- A rational rank-two matrix whose square is the normalized side separator. -/
def nearySquareRoot (β : Nat) : Square (Fin 3) ℚ :=
  let marker := nearySideMarkerValue β
  let scale := nearySideMarkerScale β
  !![1, 0, 0;
     -marker⁻¹, 0, 0;
     scale * marker⁻¹ + 1, marker, 0]

theorem normalizedNearyColumn_eq (β : Nat) :
    normalizedNearyColumn β =
      ![1, -(nearySideMarkerValue β)⁻¹,
        nearySideMarkerScale β * (nearySideMarkerValue β)⁻¹] := by
  rw [normalizedNearyColumn, nearySideColumn_eq_native]
  ext coordinate
  fin_cases coordinate <;>
    simp [nearySideNativeColumn, nearySideMarkerValue_ne_zero]
  ring

/-- Directly checked square-root identity for the source-uniform rational punctuation matrix. -/
theorem nearySquareRoot_sq (β : Nat) :
    nearySquareRoot β * nearySquareRoot β =
      Matrix.vecMulVec (normalizedNearyColumn β) nearySideRow := by
  rw [normalizedNearyColumn_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nearySquareRoot, nearySideRow, Matrix.mul_apply, Matrix.vecMulVec_apply,
      Fin.sum_univ_succ, nearySideMarkerValue_ne_zero]

/-- Two-column input factor of the explicit square root. -/
def nearySquareRootInput (β : Nat) : Matrix (Fin 3) (Fin 2) ℚ :=
  let marker := nearySideMarkerValue β
  let scale := nearySideMarkerScale β
  !![1, 0;
     -marker⁻¹, 0;
     scale * marker⁻¹ + 1, marker]

/-- Coordinate projection forming the output factor of the explicit square root. -/
def nearySquareRootOutput : Matrix (Fin 2) (Fin 3) ℚ :=
  !![1, 0, 0;
     0, 1, 0]

/-- A checked left inverse for the two-column input factor. -/
def nearySquareRootLeftInverse (β : Nat) : Matrix (Fin 2) (Fin 3) ℚ :=
  let marker := nearySideMarkerValue β
  let scale := nearySideMarkerScale β
  !![1, 0, 0;
     -(scale * marker⁻¹ + 1) * marker⁻¹, 0, marker⁻¹]

/-- A checked right inverse for the output projection. -/
def nearySquareRootRightInverse : Matrix (Fin 3) (Fin 2) ℚ :=
  !![1, 0;
     0, 1;
     0, 0]

theorem nearySquareRoot_factor (β : Nat) :
    nearySquareRoot β = nearySquareRootInput β * nearySquareRootOutput := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nearySquareRoot, nearySquareRootInput, nearySquareRootOutput,
      Matrix.vecHead, Matrix.vecTail, Matrix.mul_apply, Fin.sum_univ_succ]

theorem nearySquareRootLeftInverse_mul_input (β : Nat) :
    nearySquareRootLeftInverse β * nearySquareRootInput β = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nearySquareRootLeftInverse, nearySquareRootInput, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_succ, nearySideMarkerValue_ne_zero]
  all_goals ring

theorem nearySquareRootOutput_mul_rightInverse :
    nearySquareRootOutput * nearySquareRootRightInverse = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nearySquareRootOutput, nearySquareRootRightInverse, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_succ]

/-- The source-uniform square root has rank exactly two. -/
theorem nearySquareRoot_rank (β : Nat) : (nearySquareRoot β).rank = 2 := by
  apply le_antisymm
  · rw [nearySquareRoot_factor]
    exact (Matrix.rank_mul_le_left
      (nearySquareRootInput β) nearySquareRootOutput).trans
        (Matrix.rank_le_width (nearySquareRootInput β))
  · have split :
        nearySquareRootLeftInverse β * nearySquareRoot β *
            nearySquareRootRightInverse = 1 := by
      rw [nearySquareRoot_factor, ← Matrix.mul_assoc,
        nearySquareRootLeftInverse_mul_input]
      simp [nearySquareRootOutput_mul_rightInverse]
    have outerBound := Matrix.rank_mul_le_left
      (nearySquareRootLeftInverse β * nearySquareRoot β)
      nearySquareRootRightInverse
    rw [split, Matrix.rank_one] at outerBound
    have innerBound := Matrix.rank_mul_le_right
      (nearySquareRootLeftInverse β) (nearySquareRoot β)
    norm_num at outerBound ⊢
    exact outerBound.trans innerBound

/-- The explicit square root is singular. -/
theorem nearySquareRoot_det (β : Nat) : (nearySquareRoot β).det = 0 := by
  rw [Matrix.det_fin_three]
  simp [nearySquareRoot]

/-- Every role word prefixed by the b-rule has nonzero native coefficient. The statement uses
the complete arbitrary-word terminal converse, including malformed role orders. -/
theorem nearySide_ruleB_cons_ne_zero (β : Nat) (body : List TagLetter)
    (β_pos : 0 < β) (word : List NearyTile) :
    sideCoefficient ℚ β body (.rule .b :: word) ≠ 0 := by
  intro prefixed_zero
  have prefixed_terminal :=
    (sideCoefficient_eq_zero_iff_terminal_match_rat β body (.rule .b :: word)).mp
      prefixed_zero
  obtain ⟨tail, starts⟩ :=
    terminalMatch_starts_rule_c β body β_pos (.rule .b :: word) prefixed_terminal
  have heads_equal := (List.cons.inj starts).1
  cases heads_equal

/-- Boundary saturation contradicts any proposed same-zero compiler as soon as one native zero
word and its physical b-rule prefix both lie in the square-free domain. -/
theorem no_ruleB_squareRoot_sameZero_on_boundary_pair
    {α : Type*} (β : Nat) (body : List TagLetter) (β_pos : 0 < β)
    (generators : α → Square (Fin 3) ℚ) (decode : Option α → NearyTile)
    (decode_squareRoot : decode none = .rule .b) (word : List (Option α))
    (word_squareFree : IsSquareFree word)
    (prefixed_squareFree : IsSquareFree (none :: word))
    (native_zero : sideCoefficient ℚ β body (word.map decode) = 0)
    (sameZero : ∀ physical, IsSquareFree physical →
      (coefficient (nearySquareRoot β) generators
          (normalizedNearyColumn β) nearySideRow physical = 0 ↔
        sideCoefficient ℚ β body (physical.map decode) = 0)) :
    False := by
  have pairing_ne : nearySideRow ⬝ᵥ normalizedNearyColumn β ≠ 0 := by
    rw [normalizedNearyColumn_eq]
    norm_num [nearySideRow, Matrix.dotProduct, Fin.sum_univ_succ]
  have physical_zero := (sameZero word word_squareFree).mpr native_zero
  have prefixed_zero :=
    (squareRoot_coefficient_cons_zero_iff
      (nearySquareRoot β) generators (normalizedNearyColumn β) nearySideRow
      (nearySquareRoot_sq β) pairing_ne word).mpr physical_zero
  have impossible_native :=
    (sameZero (none :: word) prefixed_squareFree).mp prefixed_zero
  simp only [List.map_cons, decode_squareRoot] at impossible_native
  exact nearySide_ruleB_cons_ne_zero β body β_pos _ impossible_native

/-! ## Exact-series rigidity on the square-free subshift -/

/-- Three prefixes exposing the side-normal state space without using the distinguished rule. -/
def rigidityPrefixes : Fin 3 → List NearyTile :=
  ![[], [.erase .c], [.erase .b]]

/-- Three suffixes exposing the side-normal state space without using the distinguished rule. -/
def rigiditySuffixes : Fin 3 → List NearyTile :=
  ![[], [.erase .c], [.erase .b]]

/-- Finite coefficient section with one prescribed letter between every prefix and suffix. -/
def finiteInsertedSection {α ι K : Type*} [Semiring K] [Fintype ι] [DecidableEq ι]
    {P S : Type*} (generators : α → Square ι K) (row column : ι → K)
    (prefixes : P → List α) (middle : α) (suffixes : S → List α) : Matrix P S K :=
  fun p s => linearCoefficient generators row column
    (prefixes p ++ middle :: suffixes s)

theorem finiteInsertedSection_factor
    {α ι K : Type*} [CommSemiring K] [Fintype ι] [DecidableEq ι]
    {P S : Type*} (generators : α → Square ι K) (row column : ι → K)
    (prefixes : P → List α) (middle : α) (suffixes : S → List α) :
    finiteInsertedSection generators row column prefixes middle suffixes =
      finitePrefixStates generators row prefixes * generators middle *
        finiteSuffixStates generators column suffixes := by
  ext p s
  calc
    finiteInsertedSection generators row column prefixes middle suffixes p s =
        (row ᵥ* wordProduct generators (prefixes p)) ⬝ᵥ
          generators middle *ᵥ wordProduct generators (suffixes s) *ᵥ column := by
      rw [finiteInsertedSection, linearCoefficient, wordProduct_append,
        wordProduct_cons, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        ← Matrix.mulVec_mulVec]
    _ = (finitePrefixStates generators row prefixes * generators middle *
          finiteSuffixStates generators column suffixes) p s := by
      rw [Matrix.mul_assoc]
      simp [finitePrefixStates, finiteSuffixStates, Matrix.mul_apply,
        Matrix.mulVec, Matrix.dotProduct]

/-- The three native reachable rows used by the rigidity certificate. -/
def rigidityReachable (β : Nat) : Square (Fin 3) ℚ :=
  !![1, 0, 0;
     1, 1, 2;
     1, 1, nearySideUpperB β]

/-- The three native observable columns used by the rigidity certificate. -/
def rigidityObservable (β : Nat) : Square (Fin 3) ℚ :=
  let marker := nearySideMarkerValue β
  let scale := nearySideMarkerScale β
  let upperB := nearySideUpperB β
  !![marker, marker - 1 + 2 * scale, marker - 1 + upperB * scale;
     -1, -3, -3;
     scale, 3 * scale, 3 * scale ^ 2]

theorem rigidityReachable_native (β : Nat) (body : List TagLetter) :
    finitePrefixStates (nearySideRole β body) nearySideRow rigidityPrefixes =
      rigidityReachable β := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [finitePrefixStates, rigidityPrefixes, rigidityReachable, nearySideRole,
      nearySideRow, sidePcpMatrix, sideTileProduct, nearyUpper, nearyLower,
      wordProduct, Matrix.vecHead, Matrix.vecTail, Matrix.vecMul, Matrix.dotProduct,
      Fin.sum_univ_succ, ternaryDigit, nearySideUpperB]

theorem rigidityObservable_native (β : Nat) (body : List TagLetter) :
    finiteSuffixStates (nearySideRole β body) (nearySideColumn β) rigiditySuffixes =
      rigidityObservable β := by
  rw [nearySideColumn_eq_native]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [finiteSuffixStates, rigiditySuffixes, rigidityObservable, nearySideRole,
      nearySideNativeColumn, sidePcpMatrix, wordProduct, nearyUpper, nearyLower,
      nearySideMarkerValue, nearySideMarkerScale, nearySideUpperB,
      nearySideUpperBScale, Matrix.vecHead, Matrix.vecTail, Matrix.mulVec,
      Matrix.dotProduct, Matrix.one_apply, Fin.sum_univ_succ, ternaryDigit]
  all_goals norm_num [tagCode, ternaryCode, ternaryDigit, Nat.ofDigits]
  all_goals ring

theorem rigidityReachable_det (β : Nat) :
    (rigidityReachable β).det = nearySideUpperB β - 2 := by
  rw [Matrix.det_fin_three]
  simp [rigidityReachable, Matrix.vecHead, Matrix.vecTail]

theorem rigidityObservable_det (β : Nat) :
    (rigidityObservable β).det =
      nearySideMarkerScale β ^ 2 * (nearySideMarkerScale β - 1) := by
  rw [Matrix.det_fin_three]
  simp [rigidityObservable, Matrix.vecHead, Matrix.vecTail]
  rw [nearySideMarkerValue_eq, nearySideMarkerScale_eq]
  ring

theorem nearySideRuleB_det (β : Nat) (body : List TagLetter) :
    (nearySideRole β body (.rule .b)).det = 81 * nearySideMarkerScale β := by
  rw [nearySideRole_eq_native, Matrix.det_fin_three]
  simp [nearySideNativeRole, nearySideUpperBScale_relation,
    Matrix.vecHead, Matrix.vecTail]
  ring

theorem rigidityReachable_det_ne_zero (β : Nat) (three_le : 3 ≤ β) :
    (rigidityReachable β).det ≠ 0 := by
  rw [rigidityReachable_det]
  have upper_gt : (2 : ℚ) < nearySideUpperB β := by
    have bound := ternaryCode_tagCode_b_gt_fifty β three_le
    change (2 : ℚ) < (ternaryCode (tagCode β .b) : ℚ)
    exact_mod_cast (show 2 < ternaryCode (tagCode β .b) by omega)
  exact sub_ne_zero.mpr (ne_of_gt upper_gt)

theorem rigidityObservable_det_ne_zero (β : Nat) (three_le : 3 ≤ β) :
    (rigidityObservable β).det ≠ 0 := by
  rw [rigidityObservable_det]
  have scale_gt : (1 : ℚ) < nearySideMarkerScale β :=
    (by have := nearySideMarkerScale_gt_twenty_five β three_le; linarith)
  exact mul_ne_zero (pow_ne_zero 2 (ne_of_gt (by linarith : (0 : ℚ) <
    nearySideMarkerScale β))) (sub_ne_zero.mpr (ne_of_gt scale_gt))

theorem nearySideRuleB_det_ne_zero (β : Nat) (body : List TagLetter)
    (three_le : 3 ≤ β) :
    (nearySideRole β body (.rule .b)).det ≠ 0 := by
  rw [nearySideRuleB_det]
  exact mul_ne_zero (by norm_num)
    (ne_of_gt (by have := nearySideMarkerScale_gt_twenty_five β three_le; linarith))

/-- A Neary role word has no adjacent occurrences of the distinguished rule-`b` letter. -/
def IsRuleBSquareFree : List NearyTile → Prop
  | [] | [_] => True
  | first :: second :: tail =>
      (first ≠ .rule .b ∨ second ≠ .rule .b) ∧
        IsRuleBSquareFree (second :: tail)

theorem rigidityWord_ruleB_squareFree (p s : Fin 3) :
    IsRuleBSquareFree
      (rigidityPrefixes p ++ .rule .b :: rigiditySuffixes s) := by
  fin_cases p <;> fin_cases s <;>
    simp [IsRuleBSquareFree, rigidityPrefixes, rigiditySuffixes]

/-- Exact preservation of the old coefficient series on the square-free subshift forces the
distinguished letter matrix to be nonsingular. Hence a square-root completion must preserve only
the zero set and must change nonzero coefficients in a genuinely word-dependent way. -/
theorem ruleB_isUnit_of_exact_on_squareFree
    (β : Nat) (body : List TagLetter) (three_le : 3 ≤ β)
    (generators : NearyTile → Square (Fin 3) ℚ) (row column : Fin 3 → ℚ)
    (exact : ∀ word, IsRuleBSquareFree word →
      linearCoefficient generators row column word =
        linearCoefficient (nearySideRole β body) nearySideRow
          (nearySideColumn β) word) :
    IsUnit (generators (.rule .b)) := by
  have sections_equal :
      finiteInsertedSection generators row column rigidityPrefixes (.rule .b)
          rigiditySuffixes =
        finiteInsertedSection (nearySideRole β body) nearySideRow
          (nearySideColumn β) rigidityPrefixes (.rule .b) rigiditySuffixes := by
    ext p s
    simpa [finiteInsertedSection] using
      exact _ (rigidityWord_ruleB_squareFree p s)
  rw [finiteInsertedSection_factor, finiteInsertedSection_factor,
    rigidityReachable_native, rigidityObservable_native] at sections_equal
  have target_det_ne_zero :
      (rigidityReachable β * nearySideRole β body (.rule .b) *
        rigidityObservable β).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_mul]
    exact mul_ne_zero
      (mul_ne_zero (rigidityReachable_det_ne_zero β three_le)
        (nearySideRuleB_det_ne_zero β body three_le))
      (rigidityObservable_det_ne_zero β three_le)
  have source_det_ne_zero :
      (finitePrefixStates generators row rigidityPrefixes * generators (.rule .b) *
        finiteSuffixStates generators column rigiditySuffixes).det ≠ 0 := by
    rw [sections_equal]
    exact target_det_ne_zero
  apply (generators (.rule .b)).isUnit_iff_isUnit_det.mpr
  apply isUnit_iff_ne_zero.mpr
  intro middle_det_zero
  apply source_det_ne_zero
  rw [Matrix.det_mul, Matrix.det_mul, middle_det_zero]
  simp

theorem linearCoefficient_smulMatrix
    {α ι K : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (scales : α → K) (generators : α → Square ι K) (row column : ι → K)
    (word : List α) :
    linearCoefficient (fun letter => scales letter • generators letter) row column word =
      (word.map scales).prod * linearCoefficient generators row column word := by
  rw [linearCoefficient, wordProduct_smulMatrix, Matrix.smul_mulVec_assoc,
    Matrix.dotProduct_smul]
  rfl

/-- Multiplicative nonzero letter weights do not rescue exact coefficient preservation on the
square-free subshift. -/
theorem ruleB_isUnit_of_weighted_exact_on_squareFree
    (β : Nat) (body : List TagLetter) (three_le : 3 ≤ β)
    (generators : NearyTile → Square (Fin 3) ℚ) (row column : Fin 3 → ℚ)
    (weights : NearyTile → ℚ) (weights_ne_zero : ∀ letter, weights letter ≠ 0)
    (exact : ∀ word, IsRuleBSquareFree word →
      linearCoefficient generators row column word =
        (word.map weights).prod *
          linearCoefficient (nearySideRole β body) nearySideRow
            (nearySideColumn β) word) :
    IsUnit (generators (.rule .b)) := by
  let inverseWeights : NearyTile → ℚ := fun letter => (weights letter)⁻¹
  let scaled : NearyTile → Square (Fin 3) ℚ :=
    fun letter => inverseWeights letter • generators letter
  have inverse_product (word : List NearyTile) :
      (word.map inverseWeights).prod = ((word.map weights).prod)⁻¹ := by
    induction word with
    | nil => simp
    | cons letter tail induction =>
        simp only [List.map_cons, List.prod_cons, inverseWeights, induction]
        simp [mul_comm]
  have product_ne_zero (word : List NearyTile) : (word.map weights).prod ≠ 0 := by
    apply List.prod_ne_zero
    intro zero_mem
    obtain ⟨letter, _, weight_zero⟩ := List.mem_map.mp zero_mem
    exact weights_ne_zero letter weight_zero
  have scaled_exact : ∀ word, IsRuleBSquareFree word →
      linearCoefficient scaled row column word =
        linearCoefficient (nearySideRole β body) nearySideRow
          (nearySideColumn β) word := by
    intro word squareFree
    change linearCoefficient
        (fun letter => inverseWeights letter • generators letter) row column word = _
    rw [linearCoefficient_smulMatrix, inverse_product, exact word squareFree]
    simp [product_ne_zero word]
  have scaled_unit := ruleB_isUnit_of_exact_on_squareFree β body three_le
    scaled row column scaled_exact
  have scaled_det_ne_zero : (scaled (.rule .b)).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((scaled (.rule .b)).isUnit_iff_isUnit_det.mp scaled_unit)
  apply (generators (.rule .b)).isUnit_iff_isUnit_det.mpr
  apply isUnit_iff_ne_zero.mpr
  intro original_det_zero
  apply scaled_det_ne_zero
  change ((inverseWeights (.rule .b) • generators (.rule .b)).det) = 0
  rw [Matrix.det_smul, original_det_zero]
  simp

/-- Square-root punctuation reduces mortality to same-zero recognition on the complete
punctuation-square-free subshift of the four Neary roles. -/
theorem nearySquareRoot_mortal_iff (β : Nat)
    (generators : NearyTile → Square (Fin 3) ℚ) :
    IsMortal (separatedGenerator (nearySquareRoot β) generators) ↔
      ∃ word : List (Option NearyTile),
        IsSquareFree word ∧
          coefficient (nearySquareRoot β) generators
            (normalizedNearyColumn β) nearySideRow word = 0 := by
  exact isMortal_iff_exists_squareFree_zero
    (nearySquareRoot β) generators (normalizedNearyColumn β) nearySideRow
      (nearySquareRoot_sq β)

end SquareRootPunctuation

end MatrixMortality
