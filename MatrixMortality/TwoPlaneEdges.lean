import MatrixMortality.EdgeCompression

/-!
# Two-plane edge realizations

Two planes in a three-dimensional space share one line. Four two-dimensional edge maps whose
actions agree on that line therefore assemble into two ambient generators, one with each plane
as image. This file is the exact algebraic seam between rank-`(2,2)` binary mortality and a
two-vertex graph of `2 × 2` edge products.
-/

namespace MatrixMortality.TwoPlaneEdges

open scoped Matrix

/-- Embed a two-dimensional interface into one of two coordinate planes sharing `e₀`. -/
def input {R : Type*} [CommSemiring R] (plane : Bool) : Matrix (Fin 3) (Fin 2) R :=
  if plane then
    !![1, 0;
       0, 0;
       0, 1]
  else
    !![1, 0;
       0, 1;
       0, 0]

/-- Coordinate projection splitting `input`. -/
def inputLeftInverse {R : Type*} [CommSemiring R]
    (plane : Bool) : Matrix (Fin 2) (Fin 3) R :=
  if plane then
    !![1, 0, 0;
       0, 0, 1]
  else
    !![1, 0, 0;
       0, 1, 0]

/-- Assemble all edges entering one target plane. The common column comes from source `false`;
compatibility below makes the choice immaterial. -/
def output {R : Type*}
    (edge : Bool → Bool → Square (Fin 2) R) (target : Bool) :
    Matrix (Fin 2) (Fin 3) R :=
  !![edge target false 0 0, edge target false 0 1, edge target true 0 1;
     edge target false 1 0, edge target false 1 1, edge target true 1 1]

/-- Both edges entering a target plane agree on the shared source line. -/
def Compatible {R : Type*}
    (edge : Bool → Bool → Square (Fin 2) R) : Prop :=
  ∀ target row, edge target false row 0 = edge target true row 0

/-- Change coordinates independently in the two interface planes. -/
def transport {R : Type*} [CommSemiring R]
    (edge : Bool → Bool → Square (Fin 2) R)
    (change inverse : Bool → Square (Fin 2) R) (target source : Bool) :
    Square (Fin 2) R :=
  inverse target * edge target source * change source

/-- Ambient generator whose image is the selected target plane. -/
def generator {R : Type*} [CommSemiring R]
    (edge : Bool → Bool → Square (Fin 2) R) (target : Bool) :
    Square (Fin 3) R :=
  input target * output edge target

/-- Each plane embedding is split. -/
theorem inputLeftInverse_mul_input {R : Type*} [CommSemiring R] (plane : Bool) :
    (inputLeftInverse plane : Matrix (Fin 2) (Fin 3) R) *
        (input plane : Matrix (Fin 3) (Fin 2) R) =
      (1 : Square (Fin 2) R) := by
  cases plane <;>
    ext i j <;>
    fin_cases i <;>
    fin_cases j <;>
    norm_num [inputLeftInverse, input, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_succ]

/-- Compression along adjacent planes recovers the prescribed edge exactly. -/
theorem output_mul_input {R : Type*} [CommSemiring R]
    (edge : Bool → Bool → Square (Fin 2) R) (compatible : Compatible edge)
    (target source : Bool) :
    output edge target * input source = edge target source := by
  ext row column
  cases source
  · fin_cases row <;> fin_cases column <;>
      norm_num [output, input, Matrix.mul_apply, Fin.sum_univ_succ]
  · fin_cases row <;> fin_cases column
    · norm_num [output, input, Matrix.mul_apply, Fin.sum_univ_succ]
      exact compatible target 0
    · norm_num [output, input, Matrix.mul_apply, Fin.sum_univ_succ]
    · norm_num [output, input, Matrix.mul_apply, Fin.sum_univ_succ]
      exact compatible target 1
    · norm_num [output, input, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The generic compression path product is the prescribed compatible edge product. -/
theorem edgeProduct_eq_pathProduct {R : Type*} [CommSemiring R]
    (edge : Bool → Bool → Square (Fin 2) R) (compatible : Compatible edge)
    (start : Bool) (tail : List Bool) :
    EdgeCompression.edgeProduct
        (input (R := R)) (output edge) start tail =
      EdgeCompression.pathProduct edge start tail := by
  change EdgeCompression.pathProduct
      (fun target source => output edge target * input source) start tail =
    EdgeCompression.pathProduct edge start tail
  induction tail generalizing start with
  | nil => rfl
  | cons next tail induction =>
      rw [EdgeCompression.pathProduct, output_mul_input edge compatible, induction,
        EdgeCompression.pathProduct]

/-- Independent source-plane coordinates turn agreement on arbitrary nonzero source vectors
into the canonical shared-first-column compatibility condition. -/
theorem transport_compatible {R : Type*} [CommSemiring R]
    (edge : Bool → Bool → Square (Fin 2) R)
    (change inverse : Bool → Square (Fin 2) R)
    (vector : Bool → Fin 2 → R)
    (change_first :
      ∀ source, Matrix.mulVec (change source) ![1, 0] = vector source)
    (agrees :
      ∀ target,
        Matrix.mulVec (edge target false) (vector false) =
          Matrix.mulVec (edge target true) (vector true)) :
    Compatible (transport edge change inverse) := by
  intro target row
  have transported :
      Matrix.mulVec (transport edge change inverse target false) ![1, 0] =
        Matrix.mulVec (transport edge change inverse target true) ![1, 0] := by
    simp only [transport, ← Matrix.mulVec_mulVec, change_first, agrees]
  simpa [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ] using congrFun transported row

/-- Coordinate changes telescope along every constrained edge path. -/
theorem transport_edgeProduct {R : Type*} [CommSemiring R]
    (edge : Bool → Bool → Square (Fin 2) R)
    (change inverse : Bool → Square (Fin 2) R)
    (change_inverse : ∀ plane, change plane * inverse plane = 1)
    (inverse_change : ∀ plane, inverse plane * change plane = 1)
    (start : Bool) (tail : List Bool) :
    EdgeCompression.pathProduct (transport edge change inverse) start tail =
      inverse start * EdgeCompression.pathProduct edge start tail *
          change (EdgeCompression.terminal start tail) := by
  induction tail generalizing start with
  | nil =>
      simp [EdgeCompression.pathProduct, EdgeCompression.terminal, inverse_change]
  | cons next tail induction =>
      rw [EdgeCompression.pathProduct, induction]
      simp only [transport, EdgeCompression.terminal, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (change next) (inverse next)
        (EdgeCompression.pathProduct edge next tail *
          change (EdgeCompression.terminal next tail)),
        change_inverse, Matrix.one_mul, EdgeCompression.pathProduct]
      simp only [Matrix.mul_assoc]

/-- Invertible independent coordinate changes preserve every constrained edge zero. -/
theorem transport_edgeProduct_eq_zero_iff
    {K : Type*} [Field K]
    (edge : Bool → Bool → Square (Fin 2) K)
    (change inverse : Bool → Square (Fin 2) K)
    (change_inverse : ∀ plane, change plane * inverse plane = 1)
    (inverse_change : ∀ plane, inverse plane * change plane = 1)
    (change_unit : ∀ plane, IsUnit (change plane))
    (inverse_unit : ∀ plane, IsUnit (inverse plane))
    (start : Bool) (tail : List Bool) :
    EdgeCompression.pathProduct (transport edge change inverse) start tail = 0 ↔
      EdgeCompression.pathProduct edge start tail = 0 := by
  rw [transport_edgeProduct edge change inverse change_inverse inverse_change]
  exact unit_sandwich_eq_zero_iff (inverse_unit start)
    (change_unit (EdgeCompression.terminal start tail))

/-- A split edge supplies a right inverse for its target output. -/
theorem output_mul_rightInverse {R : Type*} [CommSemiring R]
    (edge : Bool → Bool → Square (Fin 2) R) (compatible : Compatible edge)
    (target source : Bool) (edgeRightInverse : Square (Fin 2) R)
    (edge_split : edge target source * edgeRightInverse = 1) :
    output edge target *
        ((input source : Matrix (Fin 3) (Fin 2) R) * edgeRightInverse) =
      (1 : Square (Fin 2) R) := by
  rw [← Matrix.mul_assoc, output_mul_input edge compatible, edge_split]

/-- A split incoming edge forces the corresponding ambient generator to have rank exactly two. -/
theorem generator_rank
    {K : Type*} [Field K]
    (edge : Bool → Bool → Square (Fin 2) K) (compatible : Compatible edge)
    (target source : Bool) (edgeRightInverse : Square (Fin 2) K)
    (edge_split : edge target source * edgeRightInverse = 1) :
    (generator edge target).rank = 2 := by
  apply le_antisymm
  · calc
      (generator edge target).rank ≤
          (input target : Matrix (Fin 3) (Fin 2) K).rank := by
        exact Matrix.rank_mul_le_left (input target) (output edge target)
      _ ≤ Fintype.card (Fin 2) := Matrix.rank_le_width (input target)
      _ = 2 := by norm_num
  · have full_split :
        (inputLeftInverse target : Matrix (Fin 2) (Fin 3) K) *
              generator edge target *
            ((input source : Matrix (Fin 3) (Fin 2) K) * edgeRightInverse) =
          1 := by
      rw [generator]
      rw [← Matrix.mul_assoc
        (inputLeftInverse target : Matrix (Fin 2) (Fin 3) K)
        (input target : Matrix (Fin 3) (Fin 2) K) (output edge target)]
      rw [inputLeftInverse_mul_input]
      simpa only [Matrix.one_mul] using
        output_mul_rightInverse edge compatible target source edgeRightInverse edge_split
    have outer_bound :=
      Matrix.rank_mul_le_left
        ((inputLeftInverse target : Matrix (Fin 2) (Fin 3) K) * generator edge target)
        ((input source : Matrix (Fin 3) (Fin 2) K) * edgeRightInverse)
    rw [full_split, Matrix.rank_one] at outer_bound
    have inner_bound :=
      Matrix.rank_mul_le_right
        (inputLeftInverse target : Matrix (Fin 2) (Fin 3) K) (generator edge target)
    norm_num at outer_bound ⊢
    exact outer_bound.trans inner_bound

/-- The ambient family is exactly the generic edge-compression family. -/
theorem generator_eq_edgeCompression {R : Type*} [CommSemiring R]
    (edge : Bool → Bool → Square (Fin 2) R) :
    generator edge = EdgeCompression.generator input (output edge) := rfl

/-- A compatible edge square with one split incoming edge per target has exactly the same
mortality problem as its two-vertex constrained edge paths. -/
theorem isMortal_iff_exists_edgeProduct_eq_zero
    {R : Type*} [CommSemiring R]
    (edge : Bool → Bool → Square (Fin 2) R) (compatible : Compatible edge)
    (source : Bool → Bool)
    (edgeRightInverse : Bool → Square (Fin 2) R)
    (edge_split :
      ∀ target, edge target (source target) * edgeRightInverse target = 1) :
    IsMortal (generator edge) ↔
      ∃ start tail,
        EdgeCompression.edgeProduct input (output edge) start tail = 0 := by
  rw [generator_eq_edgeCompression]
  exact EdgeCompression.isMortal_iff_exists_edgeProduct_eq_zero
    (input (R := R)) (output edge) (inputLeftInverse (R := R))
    (fun target => (input (R := R) (source target)) * edgeRightInverse target)
    (inputLeftInverse_mul_input (R := R))
    (fun target => output_mul_rightInverse edge compatible target (source target)
      (edgeRightInverse target) (edge_split target))

end MatrixMortality.TwoPlaneEdges
