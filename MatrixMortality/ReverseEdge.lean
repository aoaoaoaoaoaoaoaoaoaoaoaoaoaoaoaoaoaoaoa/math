import MatrixMortality.TerminalTile
import MatrixMortality.TwoPlaneEdges

/-!
# Generic reverse edge compiler

A nondegenerate two-dimensional projective-incidence instance embeds into the constrained edge
square of two rank-two three-dimensional generators. One rank-one loop tests the incidence
scalar; the other three edges are units. This file owns the basis adaptation and the complete
all-path converse.
-/

namespace MatrixMortality.ReverseEdge

open scoped Matrix

/-- Two-dimensional projective interface. -/
abbrev Interface := Fin 2

/-- The two ordinary incidence generators. -/
def incidenceGenerator {K : Type*} (G H : Square Interface K) : Bool → Square Interface K
  | false => G
  | true => H

/-- Projective-incidence coefficient of one ordinary word. -/
def incidence {K : Type*} [CommSemiring K]
    (G H : Square Interface K) (row column : Interface → K) (word : List Bool) : K :=
  row ⬝ᵥ wordProduct (incidenceGenerator G H) word *ᵥ column

/-- Right boundary pulled back through `H`. -/
noncomputable def pulledColumn {K : Type*} [Field K]
    (H : Square Interface K) (column : Interface → K) : Interface → K :=
  H⁻¹ *ᵥ column

/-- Compatibility vector in the first source plane. -/
noncomputable def firstVector {K : Type*} [Field K]
    (G H : Square Interface K) (column : Interface → K) : Interface → K :=
  H⁻¹ *ᵥ (G *ᵥ pulledColumn H column)

/-- Self-incidence of the rank-one test loop. -/
noncomputable def alpha {K : Type*} [Field K]
    (H : Square Interface K) (row column : Interface → K) : K :=
  row ⬝ᵥ pulledColumn H column

/-- Normalizing incidence which makes the test loop map the first compatibility vector to the
second. -/
noncomputable def beta {K : Type*} [Field K]
    (G H : Square Interface K) (row column : Interface → K) : K :=
  row ⬝ᵥ firstVector G H column

/-- Rank-one test loop. -/
noncomputable def testLoop {K : Type*} [Field K]
    (G H : Square Interface K) (row column : Interface → K) : Square Interface K :=
  (beta G H row column)⁻¹ •
    Matrix.vecMulVec (pulledColumn H column) row

/-- Raw edge square before adapting its two source compatibility vectors to the shared first
coordinate. Indices are `target, source`. -/
noncomputable def rawEdge {K : Type*} [Field K]
    (G H : Square Interface K) (row column : Interface → K) :
    Bool → Bool → Square Interface K
  | false, false => testLoop G H row column
  | false, true => 1
  | true, false => H
  | true, true => G

/-- Compatibility vector in each source plane. -/
noncomputable def sourceVector {K : Type*} [Field K]
    (G H : Square Interface K) (column : Interface → K) :
    Bool → Interface → K
  | false => firstVector G H column
  | true => pulledColumn H column

theorem mulVec_pulledColumn
    {K : Type*} [Field K]
    (H : Square Interface K) (column : Interface → K)
    (H_unit : IsUnit H) :
    H *ᵥ pulledColumn H column = column := by
  rw [pulledColumn, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv H (H.isUnit_iff_isUnit_det.mp H_unit), Matrix.one_mulVec]

theorem mulVec_firstVector
    {K : Type*} [Field K]
    (G H : Square Interface K) (column : Interface → K)
    (H_unit : IsUnit H) :
    H *ᵥ firstVector G H column = G *ᵥ pulledColumn H column := by
  rw [firstVector, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv H (H.isUnit_iff_isUnit_det.mp H_unit), Matrix.one_mulVec]

theorem testLoop_mulVec_firstVector
    {K : Type*} [Field K]
    (G H : Square Interface K) (row column : Interface → K)
    (beta_nonzero : beta G H row column ≠ 0) :
    testLoop G H row column *ᵥ firstVector G H column =
      pulledColumn H column := by
  have expanded_beta :
      row 0 * firstVector G H column 0 +
          row 1 * firstVector G H column 1 ≠ 0 := by
    simpa [beta, Matrix.dotProduct, Fin.sum_univ_succ] using beta_nonzero
  ext i
  fin_cases i <;>
    simp [testLoop, beta, Matrix.mulVec, Matrix.dotProduct, Matrix.vecMulVec_apply,
      Fin.sum_univ_succ, beta_nonzero]
  all_goals field_simp [expanded_beta]
  all_goals ring

theorem rawEdge_agrees
    {K : Type*} [Field K]
    (G H : Square Interface K) (row column : Interface → K)
    (H_unit : IsUnit H) (beta_nonzero : beta G H row column ≠ 0) :
    ∀ target,
      (rawEdge G H row column target false) *ᵥ
          sourceVector G H column false =
        (rawEdge G H row column target true) *ᵥ
          sourceVector G H column true := by
  intro target
  cases target
  · simpa [rawEdge, sourceVector] using
      testLoop_mulVec_firstVector G H row column beta_nonzero
  · simpa [rawEdge, sourceVector] using
      mulVec_firstVector G H column H_unit

/-- A rational two-vector completed by its quarter-turn. -/
def frame (vector : Interface → ℚ) : Square Interface ℚ :=
  !![vector 0, -vector 1;
     vector 1, vector 0]

theorem frame_mulVec_first (vector : Interface → ℚ) :
    frame vector *ᵥ ![1, 0] = vector := by
  ext i
  fin_cases i <;>
    simp [frame, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ]

theorem frame_det (vector : Interface → ℚ) :
    (frame vector).det = vector 0 ^ 2 + vector 1 ^ 2 := by
  rw [Matrix.det_fin_two]
  simp [frame]
  ring

theorem frame_isUnit (vector : Interface → ℚ) (vector_nonzero : vector ≠ 0) :
    IsUnit (frame vector) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, frame_det]
  intro sum_zero
  have first_zero : vector 0 = 0 := by
    nlinarith [sq_nonneg (vector 0), sq_nonneg (vector 1)]
  have second_zero : vector 1 = 0 := by
    nlinarith [sq_nonneg (vector 0), sq_nonneg (vector 1)]
  apply vector_nonzero
  funext i
  fin_cases i
  · exact first_zero
  · exact second_zero

/-- Adapted edge square satisfying the canonical shared-first-column condition. -/
noncomputable def adaptedEdge
    (G H : Square Interface ℚ) (row column : Interface → ℚ) :
    Bool → Bool → Square Interface ℚ :=
  TwoPlaneEdges.transport (rawEdge G H row column)
    (frame ∘ sourceVector G H column)
    (fun source => (frame (sourceVector G H column source))⁻¹)

theorem adaptedEdge_compatible
    (G H : Square Interface ℚ) (row column : Interface → ℚ)
    (H_unit : IsUnit H) (beta_nonzero : beta G H row column ≠ 0) :
    TwoPlaneEdges.Compatible (adaptedEdge G H row column) := by
  apply TwoPlaneEdges.transport_compatible
    (rawEdge G H row column)
    (frame ∘ sourceVector G H column)
    (fun source => (frame (sourceVector G H column source))⁻¹)
    (sourceVector G H column)
  · intro source
    exact frame_mulVec_first (sourceVector G H column source)
  · exact rawEdge_agrees G H row column H_unit beta_nonzero

theorem sourceVector_ne_zero
    (G H : Square Interface ℚ) (row column : Interface → ℚ)
    (alpha_nonzero : alpha H row column ≠ 0)
    (beta_nonzero : beta G H row column ≠ 0) :
    ∀ source, sourceVector G H column source ≠ 0 := by
  intro source
  cases source
  · intro vector_zero
    apply beta_nonzero
    have first_zero : firstVector G H column = 0 := by
      simpa [sourceVector] using vector_zero
    simp [beta, first_zero]
  · intro vector_zero
    apply alpha_nonzero
    have pulled_zero : pulledColumn H column = 0 := by
      simpa [sourceVector] using vector_zero
    simp [alpha, pulled_zero]

theorem sourceFrame_isUnit
    (G H : Square Interface ℚ) (row column : Interface → ℚ)
    (alpha_nonzero : alpha H row column ≠ 0)
    (beta_nonzero : beta G H row column ≠ 0) :
    ∀ source, IsUnit (frame (sourceVector G H column source)) :=
  fun source => frame_isUnit _ <|
    sourceVector_ne_zero G H row column alpha_nonzero beta_nonzero source

/-- Basis adaptation preserves every constrained path zero. -/
theorem adaptedEdge_pathProduct_eq_zero_iff
    (G H : Square Interface ℚ) (row column : Interface → ℚ)
    (alpha_nonzero : alpha H row column ≠ 0)
    (beta_nonzero : beta G H row column ≠ 0)
    (start : Bool) (tail : List Bool) :
    EdgeCompression.pathProduct (adaptedEdge G H row column) start tail = 0 ↔
      EdgeCompression.pathProduct (rawEdge G H row column) start tail = 0 := by
  let change := frame ∘ sourceVector G H column
  let inverse := fun source => (change source)⁻¹
  have change_unit : ∀ source, IsUnit (change source) := by
    intro source
    exact sourceFrame_isUnit G H row column alpha_nonzero beta_nonzero source
  apply TwoPlaneEdges.transport_edgeProduct_eq_zero_iff
    (rawEdge G H row column) change inverse
  · exact fun source => mul_nonsingInv_of_isUnit _ (change_unit source)
  · exact fun source => nonsingInv_mul_of_isUnit _ (change_unit source)
  · exact change_unit
  · exact fun source => nonsingInv_isUnit _ (change_unit source)

/-- Each target uses the nonsingular edge entering from the opposite source plane. -/
def splitSource : Bool → Bool
  | false => true
  | true => false

theorem rawEdge_split_isUnit
    (G H : Square Interface ℚ) (row column : Interface → ℚ)
    (H_unit : IsUnit H) :
    ∀ target, IsUnit (rawEdge G H row column target (splitSource target)) := by
  intro target
  cases target
  · simp [rawEdge, splitSource]
  · simpa [rawEdge, splitSource] using H_unit

theorem adaptedEdge_split_isUnit
    (G H : Square Interface ℚ) (row column : Interface → ℚ)
    (H_unit : IsUnit H)
    (alpha_nonzero : alpha H row column ≠ 0)
    (beta_nonzero : beta G H row column ≠ 0) :
    ∀ target, IsUnit (adaptedEdge G H row column target (splitSource target)) := by
  intro target
  let change := frame ∘ sourceVector G H column
  have change_unit : ∀ source, IsUnit (change source) := by
    intro source
    exact sourceFrame_isUnit G H row column alpha_nonzero beta_nonzero source
  simpa [adaptedEdge, TwoPlaneEdges.transport, change, Function.comp_def,
    Matrix.mul_assoc] using
      (nonsingInv_isUnit _ (change_unit target)).mul
        ((rawEdge_split_isUnit G H row column H_unit target).mul
          (change_unit (splitSource target)))

/-- Nonsingular inverse of the split incoming adapted edge. -/
noncomputable def adaptedRightInverse
    (G H : Square Interface ℚ) (row column : Interface → ℚ) (target : Bool) :
    Square Interface ℚ :=
  (adaptedEdge G H row column target (splitSource target))⁻¹

theorem adaptedEdge_split
    (G H : Square Interface ℚ) (row column : Interface → ℚ)
    (H_unit : IsUnit H)
    (alpha_nonzero : alpha H row column ≠ 0)
    (beta_nonzero : beta G H row column ≠ 0) :
    ∀ target,
      adaptedEdge G H row column target (splitSource target) *
          adaptedRightInverse G H row column target =
        1 := by
  intro target
  exact mul_nonsingInv_of_isUnit _ <|
    adaptedEdge_split_isUnit G H row column H_unit alpha_nonzero beta_nonzero target

/-! ## Raw path normal form -/

/-- The three nonsingular physical edges: an invisible plane change, `G`, and `H`. -/
inductive UnitEdge
  | skip
  | g
  | h
  deriving DecidableEq

/-- Matrix carried by one nonsingular edge symbol. -/
def unitEdgeMatrix {K : Type*} [CommSemiring K]
    (G H : Square Interface K) : UnitEdge → Square Interface K
  | .skip => 1
  | .g => G
  | .h => H

/-- Split a constrained vertex path at every test loop, retaining all possibly empty blocks of
nonsingular edges. -/
def pathBlocks : Bool → List Bool → List (List UnitEdge)
  | _, [] => [[]]
  | false, false :: tail => [] :: pathBlocks false tail
  | false, true :: tail => (pathBlocks true tail).modifyHead (.skip :: ·)
  | true, false :: tail => (pathBlocks false tail).modifyHead (.h :: ·)
  | true, true :: tail => (pathBlocks true tail).modifyHead (.g :: ·)

theorem pathBlocks_ne_nil (start : Bool) (tail : List Bool) :
    pathBlocks start tail ≠ [] := by
  induction tail generalizing start with
  | nil => simp [pathBlocks]
  | cons next tail induction =>
      cases start <;> cases next
      · simp [pathBlocks]
      · obtain ⟨block, blocks, blocks_eq⟩ :=
          List.exists_cons_of_ne_nil (induction true)
        simp [pathBlocks, blocks_eq]
      · obtain ⟨block, blocks, blocks_eq⟩ :=
          List.exists_cons_of_ne_nil (induction false)
        simp [pathBlocks, blocks_eq]
      · obtain ⟨block, blocks, blocks_eq⟩ :=
          List.exists_cons_of_ne_nil (induction true)
        simp [pathBlocks, blocks_eq]

private theorem map_wordProduct_modifyHead
    {K : Type*} [CommSemiring K]
    (G H : Square Interface K) (edge : UnitEdge)
    (blocks : List (List UnitEdge)) :
    (blocks.modifyHead (edge :: ·)).map (wordProduct (unitEdgeMatrix G H)) =
      (blocks.map (wordProduct (unitEdgeMatrix G H))).modifyHead
        (unitEdgeMatrix G H edge * ·) := by
  cases blocks <;> simp [wordProduct]

/-- The raw constrained path is exactly the rank-one test loop intercalated between its
nonsingular edge blocks. -/
theorem rawEdge_pathProduct
    (G H : Square Interface ℚ) (row column : Interface → ℚ)
    (start : Bool) (tail : List Bool) :
    EdgeCompression.pathProduct (rawEdge G H row column) start tail =
      intercalatedProduct (testLoop G H row column)
        ((pathBlocks start tail).map (wordProduct (unitEdgeMatrix G H))) := by
  induction tail generalizing start with
  | nil => simp [EdgeCompression.pathProduct, pathBlocks, intercalatedProduct]
  | cons next tail induction =>
      cases start <;> cases next
      · rw [EdgeCompression.pathProduct]
        simp only [rawEdge, pathBlocks, List.map_cons, wordProduct_nil]
        rw [intercalatedProduct_one_cons _ (by
          simpa using pathBlocks_ne_nil false tail), induction]
      · rw [EdgeCompression.pathProduct, rawEdge, pathBlocks,
          map_wordProduct_modifyHead]
        rw [intercalatedProduct_modifyHead _ _ (by
          simpa using pathBlocks_ne_nil true tail), induction]
        simp [unitEdgeMatrix]
      · rw [EdgeCompression.pathProduct, rawEdge, pathBlocks,
          map_wordProduct_modifyHead]
        rw [intercalatedProduct_modifyHead _ _ (by
          simpa using pathBlocks_ne_nil false tail), induction]
        simp [unitEdgeMatrix]
      · rw [EdgeCompression.pathProduct, rawEdge, pathBlocks,
          map_wordProduct_modifyHead]
        rw [intercalatedProduct_modifyHead _ _ (by
          simpa using pathBlocks_ne_nil true tail), induction]
        simp [unitEdgeMatrix]

/-- A completed nonsingular block ends in the return edge `H`. -/
def EndsH (block : List UnitEdge) : Prop :=
  ∃ front, block = front ++ [.h]

/-- Empty blocks are adjacent test loops; nonempty completed blocks end in `H`. -/
def ClosedBlock (block : List UnitEdge) : Prop :=
  block = [] ∨ EndsH block

/-- Every block except the unfinished final block satisfies `ClosedBlock`. -/
def ClosedPrefix : List (List UnitEdge) → Prop
  | [] => True
  | [_] => True
  | block :: next :: blocks =>
      ClosedBlock block ∧ ClosedPrefix (next :: blocks)

/-- A path starting at vertex `true` cannot meet a test loop before traversing `H`. -/
def FirstEndsH : List (List UnitEdge) → Prop
  | [] => True
  | [_] => True
  | block :: _ :: _ => EndsH block

theorem endsH_cons (edge : UnitEdge) {block : List UnitEdge}
    (ends_h : EndsH block) :
    EndsH (edge :: block) := by
  obtain ⟨front, rfl⟩ := ends_h
  exact ⟨edge :: front, rfl⟩

theorem endsH_h_cons {block : List UnitEdge} (closed : ClosedBlock block) :
    EndsH (.h :: block) := by
  rcases closed with rfl | ends_h
  · exact ⟨[], rfl⟩
  · exact endsH_cons .h ends_h

/-- The path grammar needed by the arbitrary-path converse. -/
theorem pathBlocks_closed (start : Bool) (tail : List Bool) :
    ClosedPrefix (pathBlocks start tail) ∧
      (start = true → FirstEndsH (pathBlocks start tail)) := by
  induction tail generalizing start with
  | nil =>
      simp [pathBlocks, ClosedPrefix, FirstEndsH]
  | cons next tail induction =>
      cases start <;> cases next
      · have recursively_closed := induction false
        obtain ⟨block, blocks, blocks_eq⟩ :=
          List.exists_cons_of_ne_nil (pathBlocks_ne_nil false tail)
        cases blocks with
        | nil =>
            simp [pathBlocks, blocks_eq, ClosedPrefix, ClosedBlock]
        | cons next blocks =>
            simpa [pathBlocks, blocks_eq, ClosedPrefix, ClosedBlock] using
              recursively_closed.1
      · have recursively_closed := induction true
        obtain ⟨block, blocks, blocks_eq⟩ :=
          List.exists_cons_of_ne_nil (pathBlocks_ne_nil true tail)
        cases blocks with
        | nil =>
            simp [pathBlocks, blocks_eq, ClosedPrefix, FirstEndsH]
        | cons next blocks =>
            have head_ends : EndsH block := by
              simpa [blocks_eq, FirstEndsH] using recursively_closed.2 rfl
            have recursive_parts :
                ClosedBlock block ∧ ClosedPrefix (next :: blocks) := by
              simpa [blocks_eq, ClosedPrefix] using recursively_closed.1
            constructor
            · simpa [pathBlocks, blocks_eq, ClosedPrefix] using
                And.intro (Or.inr (endsH_cons .skip head_ends))
                  recursive_parts.2
            · simp
      · have recursively_closed := induction false
        obtain ⟨block, blocks, blocks_eq⟩ :=
          List.exists_cons_of_ne_nil (pathBlocks_ne_nil false tail)
        cases blocks with
        | nil =>
            simp [pathBlocks, blocks_eq, ClosedPrefix, FirstEndsH]
        | cons next blocks =>
            have recursive_parts :
                ClosedBlock block ∧ ClosedPrefix (next :: blocks) := by
              simpa [blocks_eq, ClosedPrefix] using recursively_closed.1
            have head_ends := endsH_h_cons recursive_parts.1
            constructor
            · simpa [pathBlocks, blocks_eq, ClosedPrefix] using
                And.intro (Or.inr head_ends) recursive_parts.2
            · simpa [pathBlocks, blocks_eq, FirstEndsH] using head_ends
      · have recursively_closed := induction true
        obtain ⟨block, blocks, blocks_eq⟩ :=
          List.exists_cons_of_ne_nil (pathBlocks_ne_nil true tail)
        cases blocks with
        | nil =>
            simp [pathBlocks, blocks_eq, ClosedPrefix, FirstEndsH]
        | cons next blocks =>
            have head_ends : EndsH block := by
              simpa [blocks_eq, FirstEndsH] using recursively_closed.2 rfl
            have prefixed_ends := endsH_cons .g head_ends
            have recursive_parts :
                ClosedBlock block ∧ ClosedPrefix (next :: blocks) := by
              simpa [blocks_eq, ClosedPrefix] using recursively_closed.1
            constructor
            · simpa [pathBlocks, blocks_eq, ClosedPrefix] using
                And.intro (Or.inr prefixed_ends) recursive_parts.2
            · simpa [pathBlocks, blocks_eq, FirstEndsH] using prefixed_ends

/-- Delete invisible source-plane changes and retain the `G/H` word. -/
def eraseUnitEdge : UnitEdge → Option Bool
  | .skip => none
  | .g => some false
  | .h => some true

/-- Ordinary incidence word obtained by deleting invisible plane changes. -/
def eraseSkips (block : List UnitEdge) : List Bool :=
  block.filterMap eraseUnitEdge

theorem wordProduct_unitEdgeMatrix
    {K : Type*} [CommSemiring K]
    (G H : Square Interface K) (block : List UnitEdge) :
    wordProduct (unitEdgeMatrix G H) block =
      wordProduct (incidenceGenerator G H) (eraseSkips block) := by
  induction block with
  | nil => rfl
  | cons edge block induction =>
      cases edge
      · simpa [wordProduct, unitEdgeMatrix, eraseSkips, eraseUnitEdge] using induction
      · simp only [wordProduct_cons, unitEdgeMatrix, eraseSkips, List.filterMap_cons,
          eraseUnitEdge, Option.toList_some, List.cons_append, incidenceGenerator]
        rw [induction]
        simp [eraseSkips]
      · simp only [wordProduct_cons, unitEdgeMatrix, eraseSkips, List.filterMap_cons,
          eraseUnitEdge, Option.toList_some, List.cons_append, incidenceGenerator]
        rw [induction]
        simp [eraseSkips]

theorem eraseSkips_endsH {block : List UnitEdge} (ends_h : EndsH block) :
    ∃ word, eraseSkips block = word ++ [true] := by
  obtain ⟨front, rfl⟩ := ends_h
  exact ⟨eraseSkips front, by
    unfold eraseSkips
    rw [List.filterMap_append]
    rfl⟩

theorem closedPrefix_mem_dropLast
    (blocks : List (List UnitEdge)) (closed : ClosedPrefix blocks)
    (block : List UnitEdge) (member : block ∈ blocks.dropLast) :
    ClosedBlock block := by
  induction blocks with
  | nil => simp at member
  | cons first rest induction =>
      cases rest with
      | nil => simp at member
      | cons next rest =>
          rw [List.dropLast_cons₂] at member
          rcases List.mem_cons.mp member with rfl | member
          · exact closed.1
          · exact induction closed.2 member

/-- Column of the normalized rank-one test loop. -/
noncomputable def testColumn
    (G H : Square Interface ℚ) (row column : Interface → ℚ) : Interface → ℚ :=
  (beta G H row column)⁻¹ • pulledColumn H column

theorem testLoop_eq_outer
    (G H : Square Interface ℚ) (row column : Interface → ℚ) :
    testLoop G H row column = Matrix.vecMulVec (testColumn G H row column) row := by
  ext i j
  simp [testLoop, testColumn, Matrix.vecMulVec_apply]
  ring

theorem alpha_eq_dotProduct
    (H : Square Interface ℚ) (row column : Interface → ℚ) :
    alpha H row column = row ⬝ᵥ pulledColumn H column := rfl

theorem testColumn_ne_zero
    (G H : Square Interface ℚ) (row column : Interface → ℚ)
    (alpha_nonzero : alpha H row column ≠ 0)
    (beta_nonzero : beta G H row column ≠ 0) :
    testColumn G H row column ≠ 0 := by
  have pulled_nonzero : pulledColumn H column ≠ 0 := by
    intro pulled_zero
    apply alpha_nonzero
    simp [alpha, pulled_zero]
  exact smul_ne_zero (inv_ne_zero beta_nonzero) pulled_nonzero

theorem row_ne_zero
    (H : Square Interface ℚ) (row column : Interface → ℚ)
    (alpha_nonzero : alpha H row column ≠ 0) :
    row ≠ 0 := by
  intro row_zero
  apply alpha_nonzero
  simp [alpha, row_zero]

theorem unitEdgeMatrix_isUnit
    (G H : Square Interface ℚ) (G_unit : IsUnit G) (H_unit : IsUnit H) :
    ∀ edge, IsUnit (unitEdgeMatrix G H edge)
  | .skip => by simp [unitEdgeMatrix]
  | .g => G_unit
  | .h => H_unit

/-- Every completed nonsingular block has a nonzero test scalar unless it encodes a genuine
incidence zero. -/
theorem closedBlock_bridge_ne_zero
    (G H : Square Interface ℚ) (row column : Interface → ℚ)
    (H_unit : IsUnit H)
    (alpha_nonzero : alpha H row column ≠ 0)
    (beta_nonzero : beta G H row column ≠ 0)
    (incidence_nonzero : ∀ word, incidence G H row column word ≠ 0)
    (block : List UnitEdge) (closed : ClosedBlock block) :
    bridgeScalar (testColumn G H row column) row
      (wordProduct (unitEdgeMatrix G H) block) ≠ 0 := by
  rcases closed with rfl | ends_h
  · simp only [wordProduct_nil]
    rw [bridgeScalar, Matrix.one_mulVec]
    change row ⬝ᵥ ((beta G H row column)⁻¹ • pulledColumn H column) ≠ 0
    rw [Matrix.dotProduct_smul]
    exact mul_ne_zero (inv_ne_zero beta_nonzero) alpha_nonzero
  · obtain ⟨word, erased_eq⟩ := eraseSkips_endsH ends_h
    rw [wordProduct_unitEdgeMatrix, erased_eq, wordProduct_append, wordProduct_cons,
      wordProduct_nil, mul_one, bridgeScalar, ← Matrix.mulVec_mulVec]
    rw [show incidenceGenerator G H true = H by rfl, testColumn, Matrix.mulVec_smul,
      mulVec_pulledColumn H column H_unit]
    change row ⬝ᵥ
      wordProduct (incidenceGenerator G H) word *ᵥ
        ((beta G H row column)⁻¹ • column) ≠ 0
    rw [Matrix.mulVec_smul, Matrix.dotProduct_smul]
    exact mul_ne_zero (inv_ne_zero beta_nonzero) (incidence_nonzero word)

/-- Under the generic nondegeneracy hypotheses, no constrained raw edge path can vanish unless
the original projective-incidence series vanishes. -/
theorem rawEdge_pathProduct_ne_zero
    (G H : Square Interface ℚ) (row column : Interface → ℚ)
    (G_unit : IsUnit G) (H_unit : IsUnit H)
    (alpha_nonzero : alpha H row column ≠ 0)
    (beta_nonzero : beta G H row column ≠ 0)
    (incidence_nonzero : ∀ word, incidence G H row column word ≠ 0)
    (start : Bool) (tail : List Bool) :
    EdgeCompression.pathProduct (rawEdge G H row column) start tail ≠ 0 := by
  rw [rawEdge_pathProduct]
  let blocks := pathBlocks start tail
  change intercalatedProduct (testLoop G H row column)
    (blocks.map (wordProduct (unitEdgeMatrix G H))) ≠ 0
  have blocks_nonempty : blocks ≠ [] := pathBlocks_ne_nil start tail
  obtain ⟨first, rest, blocks_eq⟩ := List.exists_cons_of_ne_nil blocks_nonempty
  cases rest with
  | nil =>
      rw [blocks_eq]
      simp only [List.map_singleton, intercalatedProduct]
      exact (wordProduct_isUnit (unitEdgeMatrix G H)
        (unitEdgeMatrix_isUnit G H G_unit H_unit) first).ne_zero
  | cons next rest =>
      let remaining := next :: rest
      have remaining_nonempty : remaining ≠ [] := by simp [remaining]
      let last := remaining.getLast remaining_nonempty
      let middle := remaining.dropLast
      have blocks_decomposition : blocks = first :: middle ++ [last] := by
        rw [blocks_eq]
        congr 1
        exact (List.dropLast_append_getLast remaining_nonempty).symm
      rw [blocks_decomposition]
      simp only [List.map_cons, List.map_append, List.map_singleton, List.map_nil]
      rw [testLoop_eq_outer, rankOneIntercalatedProduct_formula]
      apply smul_ne_zero
      · apply List.prod_ne_zero
        intro zero_mem
        obtain ⟨matrix, matrix_mem, bridge_zero⟩ := List.mem_map.mp zero_mem
        obtain ⟨block, block_mem, matrix_eq⟩ := List.mem_map.mp matrix_mem
        subst matrix
        have block_closed : ClosedBlock block := by
          apply closedPrefix_mem_dropLast blocks (pathBlocks_closed start tail).1 block
          rw [blocks_decomposition]
          change block ∈ ((first :: middle) ++ [last]).dropLast
          rw [List.dropLast_append_cons, List.dropLast_single, List.append_nil]
          exact List.mem_cons_of_mem first block_mem
        exact closedBlock_bridge_ne_zero G H row column H_unit alpha_nonzero
          beta_nonzero incidence_nonzero block block_closed bridge_zero
      · apply outer_ne_zero
        · exact unit_mulVec_ne_zero
            (wordProduct_isUnit (unitEdgeMatrix G H)
              (unitEdgeMatrix_isUnit G H G_unit H_unit) first)
            (testColumn_ne_zero G H row column alpha_nonzero beta_nonzero)
        · exact vecMul_unit_ne_zero
            (row_ne_zero H row column alpha_nonzero)
            (wordProduct_isUnit (unitEdgeMatrix G H)
              (unitEdgeMatrix_isUnit G H G_unit H_unit) last)

/-- Destination vertex after emitting one ordinary incidence letter. -/
def letterDestination : Bool → Bool
  | false => true
  | true => false

/-- Realize an arbitrary `G/H` word as a test-loop-free constrained path, inserting invisible
`false → true` edges whenever the previous `H` returned to vertex `false`. -/
def realizeTail : Bool → List Bool → List Bool
  | _, [] => []
  | state, letter :: word =>
      (if state then [] else [true]) ++
        letterDestination letter ::
          realizeTail (letterDestination letter) word

theorem realizeTail_terminal (start : Bool) (word : List Bool) :
    EdgeCompression.terminal start (realizeTail start word) =
      word.foldl (fun _ letter => letterDestination letter) start := by
  induction word generalizing start with
  | nil => rfl
  | cons letter word induction =>
      cases start <;> cases letter <;>
        simp [realizeTail, EdgeCompression.terminal, letterDestination, induction]

theorem realizeTail_pathProduct
    (G H : Square Interface ℚ) (row column : Interface → ℚ)
    (start : Bool) (word : List Bool) :
    EdgeCompression.pathProduct (rawEdge G H row column) start
        (realizeTail start word) =
      wordProduct (incidenceGenerator G H) word := by
  induction word generalizing start with
  | nil => rfl
  | cons letter word induction =>
      cases start <;> cases letter <;>
        simp [realizeTail, EdgeCompression.pathProduct, rawEdge, letterDestination,
          incidenceGenerator, wordProduct, induction, Matrix.mul_assoc]

theorem realizeTail_append_h_terminal (start : Bool) (word : List Bool) :
    EdgeCompression.terminal start (realizeTail start (word ++ [true])) = false := by
  rw [realizeTail_terminal]
  simp [List.foldl_append, letterDestination]

/-- Every projective-incidence zero yields a zero constrained raw edge path. -/
theorem exists_rawEdge_pathProduct_eq_zero_of_incidence
    (G H : Square Interface ℚ) (row column : Interface → ℚ)
    (H_unit : IsUnit H)
    {word : List Bool} (incidence_zero : incidence G H row column word = 0) :
    ∃ start tail,
      EdgeCompression.pathProduct (rawEdge G H row column) start tail = 0 := by
  let letters := word ++ [true]
  let excursion := realizeTail false letters
  refine ⟨false, false :: excursion ++ [false], ?_⟩
  change testLoop G H row column *
      EdgeCompression.pathProduct (rawEdge G H row column) false
        (excursion ++ [false]) = 0
  rw [EdgeCompression.pathProduct_append, show
      EdgeCompression.terminal false excursion = false by
        simpa [excursion, letters] using realizeTail_append_h_terminal false word,
    EdgeCompression.pathProduct, EdgeCompression.pathProduct]
  rw [show EdgeCompression.pathProduct (rawEdge G H row column) false excursion =
      wordProduct (incidenceGenerator G H) letters by
        simpa [excursion, letters] using
          realizeTail_pathProduct G H row column false letters]
  rw [show wordProduct (incidenceGenerator G H) letters =
      wordProduct (incidenceGenerator G H) word * H by
        simp [letters, wordProduct_append, incidenceGenerator]]
  rw [testLoop_eq_outer]
  have bridge_zero :
      bridgeScalar (testColumn G H row column) row
          (wordProduct (incidenceGenerator G H) word * H) = 0 := by
    rw [bridgeScalar, ← Matrix.mulVec_mulVec, testColumn, Matrix.mulVec_smul]
    change row ⬝ᵥ
      wordProduct (incidenceGenerator G H) word *ᵥ
        ((beta G H row column)⁻¹ • (H *ᵥ pulledColumn H column)) = 0
    rw [mulVec_pulledColumn H column H_unit, Matrix.mulVec_smul,
      Matrix.dotProduct_smul]
    change (beta G H row column)⁻¹ * incidence G H row column word = 0
    rw [incidence_zero, mul_zero]
  simp only [rawEdge, EdgeCompression.pathProduct, Matrix.mul_one]
  rw [testLoop_eq_outer, ← Matrix.mul_assoc, outer_mul, outer_mul_outer]
  rw [← Matrix.dotProduct_mulVec]
  change bridgeScalar (testColumn G H row column) row
      (wordProduct (incidenceGenerator G H) word * H) •
        Matrix.vecMulVec (testColumn G H row column) row = 0
  rw [bridge_zero, zero_smul]

/-- The adapted pushout generators have rank exactly two. -/
theorem adaptedGenerator_rank
    (G H : Square Interface ℚ) (row column : Interface → ℚ)
    (H_unit : IsUnit H)
    (alpha_nonzero : alpha H row column ≠ 0)
    (beta_nonzero : beta G H row column ≠ 0)
    (target : Bool) :
    (TwoPlaneEdges.generator (adaptedEdge G H row column) target).rank = 2 :=
  TwoPlaneEdges.generator_rank
    (adaptedEdge G H row column)
    (adaptedEdge_compatible G H row column H_unit beta_nonzero)
    target (splitSource target)
    (adaptedRightInverse G H row column target)
    (adaptedEdge_split G H row column H_unit alpha_nonzero beta_nonzero target)

/-- Generic projective incidence compiles, without a new generator, to mortality of two
rank-two `3 × 3` matrices. -/
theorem isMortal_adaptedGenerator_iff
    (G H : Square Interface ℚ) (row column : Interface → ℚ)
    (G_unit : IsUnit G) (H_unit : IsUnit H)
    (alpha_nonzero : alpha H row column ≠ 0)
    (beta_nonzero : beta G H row column ≠ 0) :
    IsMortal (TwoPlaneEdges.generator (adaptedEdge G H row column)) ↔
      ∃ word, incidence G H row column word = 0 := by
  let edge := adaptedEdge G H row column
  have compatible : TwoPlaneEdges.Compatible edge :=
    adaptedEdge_compatible G H row column H_unit beta_nonzero
  have split :
      ∀ target,
        edge target (splitSource target) *
            adaptedRightInverse G H row column target =
          1 :=
    adaptedEdge_split G H row column H_unit alpha_nonzero beta_nonzero
  rw [TwoPlaneEdges.isMortal_iff_exists_edgeProduct_eq_zero
    edge compatible splitSource (adaptedRightInverse G H row column) split]
  constructor
  · rintro ⟨start, tail, edge_zero⟩
    have adapted_zero :
        EdgeCompression.pathProduct edge start tail = 0 := by
      rwa [TwoPlaneEdges.edgeProduct_eq_pathProduct edge compatible] at edge_zero
    have raw_zero :
        EdgeCompression.pathProduct (rawEdge G H row column) start tail = 0 :=
      (adaptedEdge_pathProduct_eq_zero_iff G H row column alpha_nonzero beta_nonzero
        start tail).mp adapted_zero
    by_contra no_incidence
    have incidence_nonzero : ∀ word, incidence G H row column word ≠ 0 := by
      intro word word_zero
      exact no_incidence ⟨word, word_zero⟩
    exact rawEdge_pathProduct_ne_zero G H row column G_unit H_unit alpha_nonzero
      beta_nonzero incidence_nonzero start tail raw_zero
  · rintro ⟨word, incidence_zero⟩
    obtain ⟨start, tail, raw_zero⟩ :=
      exists_rawEdge_pathProduct_eq_zero_of_incidence G H row column H_unit incidence_zero
    refine ⟨start, tail, ?_⟩
    rw [TwoPlaneEdges.edgeProduct_eq_pathProduct edge compatible]
    exact (adaptedEdge_pathProduct_eq_zero_iff G H row column alpha_nonzero beta_nonzero
      start tail).mpr raw_zero

end MatrixMortality.ReverseEdge
