import MatrixMortality.LinearRepresentation
import MatrixMortality.PairedCompression

/-!
# Singular affine recognizers

One transient guard coordinate and one persistent affine carry give a common three-state
realization for the branching recognizers. Data controls refresh the guard and update the carry;
the toggle fixes the guard and reflects the carry about one center.
-/

namespace MatrixMortality

open scoped Matrix

namespace AffineRecognizer

/-- Parameters of a three-state affine carry recognizer. The carry ring may be smaller than the
matrix scalar ring; `cast` is its sole scalar-extension boundary. -/
structure Parameters (Carry Scalar : Type*) [CommRing Carry] [CommRing Scalar] where
  /-- Scalar extension from the carry ring into the matrix ring. -/
  cast : Carry →+* Scalar
  /-- Multiplicative carry coefficient of each data letter. -/
  carryScale : TagLetter → Carry
  /-- Additive carry coefficient of each data letter. -/
  carryShift : TagLetter → Carry
  /-- Carry coefficient read into the transient guard. -/
  guardScale : TagLetter → Scalar
  /-- Constant coefficient read into the transient guard. -/
  guardShift : TagLetter → Scalar
  /-- Center sum of the affine carry reflection. -/
  toggleCenter : Carry

variable {Carry Scalar : Type*} [CommRing Carry] [CommRing Scalar]

/-- Singular data matrix refreshing the guard and advancing the affine carry. -/
def Parameters.data (parameters : Parameters Carry Scalar) (letter : TagLetter) :
    Square (Fin 3) Scalar :=
  !![0, parameters.guardScale letter, parameters.guardShift letter;
     0, parameters.cast (parameters.carryScale letter),
       parameters.cast (parameters.carryShift letter);
     0, 0, 1]

/-- Data matrices together with the affine carry reflection. -/
def Parameters.generator (parameters : Parameters Carry Scalar) :
    PairedControl → Square (Fin 3) Scalar
  | .data letter => parameters.data letter
  | .toggle =>
      !![1, 0, 0;
         0, -1, parameters.cast parameters.toggleCenter;
         0, 0, 1]

/-- Persistent carry driven from the right end of a control word. -/
def Parameters.carry (parameters : Parameters Carry Scalar) : List PairedControl → Carry
  | [] => 0
  | .data letter :: word =>
      parameters.carryScale letter * parameters.carry word + parameters.carryShift letter
  | .toggle :: word => parameters.toggleCenter - parameters.carry word

@[simp] theorem Parameters.carry_nil (parameters : Parameters Carry Scalar) :
    parameters.carry [] = 0 := rfl

@[simp] theorem Parameters.carry_data
    (parameters : Parameters Carry Scalar) (letter : TagLetter) (word : List PairedControl) :
    parameters.carry (.data letter :: word) =
      parameters.carryScale letter * parameters.carry word + parameters.carryShift letter := rfl

@[simp] theorem Parameters.carry_toggle
    (parameters : Parameters Carry Scalar) (word : List PairedControl) :
    parameters.carry (.toggle :: word) =
      parameters.toggleCenter - parameters.carry word := rfl

/-- Transient guard refreshed by data and preserved by the toggle. -/
def Parameters.guard (parameters : Parameters Carry Scalar) : List PairedControl → Scalar
  | [] => 1
  | .data letter :: word =>
      parameters.guardScale letter * parameters.cast (parameters.carry word) +
        parameters.guardShift letter
  | .toggle :: word => parameters.guard word

@[simp] theorem Parameters.guard_nil (parameters : Parameters Carry Scalar) :
    parameters.guard [] = 1 := rfl

@[simp] theorem Parameters.guard_data
    (parameters : Parameters Carry Scalar) (letter : TagLetter) (word : List PairedControl) :
    parameters.guard (.data letter :: word) =
      parameters.guardScale letter * parameters.cast (parameters.carry word) +
        parameters.guardShift letter := rfl

@[simp] theorem Parameters.guard_toggle
    (parameters : Parameters Carry Scalar) (word : List PairedControl) :
    parameters.guard (.toggle :: word) = parameters.guard word := rfl

/-- Boundary row selecting the transient guard. -/
def row : Fin 3 → Scalar := ![1, 0, 0]

/-- Homogeneous state before the boundary toggle. -/
def delta : Fin 3 → Scalar := ![1, 0, 1]

/-- Boundary column obtained by toggling `delta`. -/
def Parameters.column (parameters : Parameters Carry Scalar) : Fin 3 → Scalar :=
  ![1, parameters.cast parameters.toggleCenter, 1]

/-- Scalar coefficient of the affine recognizer. -/
def Parameters.coefficient (parameters : Parameters Carry Scalar)
    (word : List PairedControl) : Scalar :=
  linearCoefficient parameters.generator row parameters.column word

/-- Exact affine state of every raw control word. -/
theorem Parameters.wordProduct_mulVec_delta
    (parameters : Parameters Carry Scalar) (word : List PairedControl) :
    wordProduct parameters.generator word *ᵥ delta =
      ![parameters.guard word, parameters.cast (parameters.carry word), 1] := by
  induction word with
  | nil =>
      ext coordinate
      fin_cases coordinate <;> simp [wordProduct, delta, Parameters.guard, Parameters.carry]
  | cons control word induction =>
      rw [wordProduct_cons, ← Matrix.mulVec_mulVec, induction]
      cases control with
      | toggle =>
          ext coordinate
          fin_cases coordinate <;>
            simp [Parameters.generator, Parameters.guard, Parameters.carry, Matrix.mulVec,
              dotProduct, Fin.sum_univ_succ]
          all_goals ring
      | data letter =>
          ext coordinate
          fin_cases coordinate <;>
            simp [Parameters.generator, Parameters.data, Parameters.guard, Parameters.carry,
              Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem Parameters.column_eq_toggle_delta (parameters : Parameters Carry Scalar) :
    parameters.column = parameters.generator .toggle *ᵥ delta := by
  ext coordinate
  fin_cases coordinate <;>
    simp [Parameters.column, Parameters.generator, delta, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

theorem Parameters.coefficient_eq_guard
    (parameters : Parameters Carry Scalar) (word : List PairedControl) :
    parameters.coefficient word = parameters.guard (word ++ [.toggle]) := by
  have state :
      wordProduct parameters.generator word *ᵥ parameters.column =
        ![parameters.guard (word ++ [.toggle]),
          parameters.cast (parameters.carry (word ++ [.toggle])), 1] := by
    calc
      wordProduct parameters.generator word *ᵥ parameters.column =
          wordProduct parameters.generator word *ᵥ
            (parameters.generator .toggle *ᵥ delta) := by
              rw [← parameters.column_eq_toggle_delta]
      _ = (wordProduct parameters.generator word * parameters.generator .toggle) *ᵥ
          delta := by rw [Matrix.mulVec_mulVec]
      _ = wordProduct parameters.generator (word ++ [.toggle]) *ᵥ delta := by
        rw [wordProduct_append]
        simp [wordProduct]
      _ = _ := parameters.wordProduct_mulVec_delta (word ++ [.toggle])
  rw [Parameters.coefficient, linearCoefficient, state]
  simp [row, dotProduct, Fin.sum_univ_succ]

@[simp] theorem Parameters.data_det
    (parameters : Parameters Carry Scalar) (letter : TagLetter) :
    (parameters.data letter).det = 0 := by
  rw [Matrix.det_fin_three]
  simp [Parameters.data]

@[simp] theorem Parameters.toggle_det (parameters : Parameters Carry Scalar) :
    (parameters.generator .toggle).det = -1 := by
  rw [Matrix.det_fin_three]
  simp [Parameters.generator]

theorem Parameters.toggle_involutive (parameters : Parameters Carry Scalar) :
    parameters.generator .toggle * parameters.generator .toggle = 1 := by
  ext matrixRow column
  fin_cases matrixRow <;> fin_cases column <;>
    simp [Parameters.generator, Matrix.mul_apply, Fin.sum_univ_succ]

end AffineRecognizer

end MatrixMortality
