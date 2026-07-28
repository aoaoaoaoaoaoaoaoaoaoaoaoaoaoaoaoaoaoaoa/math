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
