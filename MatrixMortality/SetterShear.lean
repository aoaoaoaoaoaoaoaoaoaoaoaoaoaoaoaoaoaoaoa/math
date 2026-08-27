import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic

/-!
# Boundary-correct shears of the five-state setter

The distinguished side vector admits a one-parameter family of coordinate splittings.  This
file proves that the parameter disappears once the delimiter cube carries the physical terminal
row.  Thus this shear cannot alter the setter's projective transfer.
-/

namespace MatrixMortality

open scoped Matrix

namespace SetterShear

/-- Coefficient of the third basis vector in the physical terminal row. -/
def hook {R : Type*} [CommRing R] (r upper distinguished alpha : R) : R :=
  1 + r * upper - alpha

/-- The denominator left after resolving the distinguished side vector. -/
def gap {R : Type*} [CommRing R] (r upper distinguished scale : R) : R :=
  scale - 1 - r * upper

/-- Side basis whose columns are `f`, `p`, and `R_c f - alpha f`. -/
def sideBasis {R : Type*} [CommRing R]
    (r upper distinguishedScale alpha : R) : Matrix (Fin 3) (Fin 3) R :=
  !![1, 0, hook r upper distinguishedScale alpha;
     0, -1, 0;
     r, 0, r * (distinguishedScale - alpha)]

/-- The side-basis determinant is independent of the shear parameter. -/
theorem sideBasis_det {R : Type*} [CommRing R]
    (r upper distinguishedScale alpha : R) :
    (sideBasis r upper distinguishedScale alpha).det =
      -r * gap r upper distinguishedScale := by
  rw [Matrix.det_fin_three]
  simp [sideBasis, hook, gap]
  ring

/-- Boundary-correct delimiter attached to a sheared side basis. -/
def delimiter {R : Type*} [CommRing R] (q lambda : R) : Matrix (Fin 5) (Fin 5) R :=
  !![1, 0, 0, 0, q;
     0, 1, 0, -1, lambda;
     0, 0, 1, 0, -1;
     0, 1, 0, -1, lambda;
     0, 0, 1, 0, -1]

/-- Physical terminal row in sheared coordinates. -/
def terminalRow {R : Type*} [CommRing R] (q : R) : Fin 5 → R :=
  ![1, 0, q, 0, 0]

/-- First coordinate axis in the five-state space. -/
def firstAxis {R : Type*} [CommRing R] : Fin 5 → R :=
  ![1, 0, 0, 0, 0]

/-- The delimiter cube is the first-axis column times the physical terminal row. -/
theorem delimiter_cube {R : Type*} [CommRing R] (q lambda : R) :
    delimiter q lambda ^ 3 = Matrix.vecMulVec firstAxis (terminalRow q) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [delimiter, firstAxis, terminalRow, pow_succ, Matrix.mul_apply,
      Matrix.dotProduct, Fin.sum_univ_succ]
  all_goals ring

/-- Coordinates of `R_c f` in the sheared side basis. -/
def distinguishedColumn {R : Type*} [CommRing R] (alpha : R) : Fin 5 → R :=
  ![alpha, 0, 1, 0, 0]

/-- Column of the internal rank-one separator. -/
def separatorColumn {R : Type*} [CommRing R] (marker : R) : Fin 5 → R :=
  ![marker, 1, 0, 1, 0]

/-- Repairing the terminal row also repairs the mixed separator, independently of the shear. -/
theorem delimiter_square_distinguishedColumn
    {R : Type*} [CommRing R]
    (r upper distinguishedScale alpha lambda marker : R)
    (calibrated : lambda * marker = 1 + r * upper) :
    delimiter (hook r upper distinguishedScale alpha) lambda ^ 2 *ᵥ
        distinguishedColumn alpha =
      lambda • separatorColumn marker := by
  ext coordinate
  fin_cases coordinate <;>
    simp [delimiter, hook, distinguishedColumn, separatorColumn, pow_succ,
      Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ]
  all_goals linear_combination calibrated

/-- Resolving a side product in a sheared basis yields the original transfer tail. -/
theorem transfer_tail
    {R : Type*} [CommRing R]
    (a x resolvedHead resolvedTail r upper distinguishedUpper alpha value scale : R)
    (headEquation :
      resolvedHead + hook r distinguishedUpper scale alpha * resolvedTail =
        (1 + r * upper) * a - value * x)
    (scaleEquation :
      resolvedHead + (scale - alpha) * resolvedTail = distinguishedUpper * a) :
    gap r distinguishedUpper scale * resolvedTail =
      (distinguishedUpper - 1 - r * upper) * a + value * x := by
  calc
    gap r distinguishedUpper scale * resolvedTail =
        ((scale - alpha) - hook r distinguishedUpper scale alpha) * resolvedTail := by
      simp [gap, hook]
      ring
    _ = (resolvedHead + (scale - alpha) * resolvedTail) -
        (resolvedHead + hook r distinguishedUpper scale alpha * resolvedTail) := by
      ring
    _ = distinguishedUpper * a - ((1 + r * upper) * a - value * x) := by
      rw [scaleEquation, headEquation]
    _ = (distinguishedUpper - 1 - r * upper) * a + value * x := by
      ring

end SetterShear

end MatrixMortality
