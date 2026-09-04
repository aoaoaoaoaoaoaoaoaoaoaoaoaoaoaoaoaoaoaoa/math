import MatrixMortality.MatrixSemigroup

/-!
# Two-register projective-plane obstruction

The empty return of an `x`-reader and that of its mirrored `y`-reader cannot coincide. In
homogeneous coordinates `[x : y : z]`, a genuine finite pole in the `x`-reader has a nonzero
`(z,x)` coefficient, whereas the `y`-reader block forces that coefficient to vanish. This
contradiction is independent of the ambient modes and their number.

Multiplying both positive-wait families by exponential scales which vanish at wait zero does
not repair a mortality construction: the resulting empty return is zero, so the physical cut
squares to zero.
-/

namespace MatrixMortality.TwoRegisterPlaneNoGo

open scoped Matrix

/-- An `x`-reader embedded in the projective plane, with `y` as the spectator coordinate. -/
def xReader {R : Type*} [CommRing R]
    (numeratorX numeratorZ denominatorX denominatorZ spectator : R) : Square (Fin 3) R :=
  !![numeratorX, 0, numeratorZ;
     0, spectator, 0;
     denominatorX, 0, denominatorZ]

/-- A `y`-reader embedded in the projective plane, with `x` as the spectator coordinate. -/
def yReader {R : Type*} [CommRing R]
    (numeratorY numeratorZ denominatorY denominatorZ spectator : R) : Square (Fin 3) R :=
  !![spectator, 0, 0;
     0, numeratorY, numeratorZ;
     0, denominatorY, denominatorZ]

/-- A nonconstant affine denominator vanishing at one has a genuine finite pole there. -/
def DenominatorHasPoleAtOne (linear constant : ℚ) : Prop :=
  linear ≠ 0 ∧ linear + constant = 0

/-- No matrix is simultaneously a nonzero-scaled `x`-reader with a finite pole at one and a
scaled mirrored `y`-reader. The obstruction is the `(z,x)` entry. -/
theorem no_common_scaled_xReader_yReader_of_xPoleAtOne
    (xNumeratorX xNumeratorZ xDenominatorX xDenominatorZ xSpectator
      yNumeratorY yNumeratorZ yDenominatorY yDenominatorZ ySpectator
      xScale yScale : ℚ)
    (xScale_ne_zero : xScale ≠ 0)
    (xPole : DenominatorHasPoleAtOne xDenominatorX xDenominatorZ) :
    xScale • xReader xNumeratorX xNumeratorZ xDenominatorX xDenominatorZ xSpectator ≠
      yScale • yReader yNumeratorY yNumeratorZ yDenominatorY yDenominatorZ ySpectator := by
  intro common
  have zx := congrArg (fun matrix : Square (Fin 3) ℚ => matrix 2 0) common
  simp [xReader, yReader, Matrix.smul_apply] at zx
  exact zx.elim xScale_ne_zero xPole.1

/-- A zero empty return makes the corresponding physical cut square to zero. -/
theorem cut_sq_eq_zero_of_emptyReturn_eq_zero
    {R Large Small : Type*} [CommSemiring R]
    [Fintype Large] [DecidableEq Large] [Fintype Small]
    (input : Matrix Large Small R) (output : Matrix Small Large R)
    (emptyReturn : output * input = 0) :
    (input * output) ^ 2 = 0 := by
  calc
    (input * output) ^ 2 = input * (output * input) * output := by
      simp [pow_two, Matrix.mul_assoc]
    _ = 0 := by rw [emptyReturn]; simp

/-- The zero-scale repair is already a mortal one-generator matrix family. -/
theorem zero_emptyReturn_forces_mortal_cut
    {R Large Small : Type*} [CommSemiring R]
    [Fintype Large] [DecidableEq Large] [Fintype Small]
    (input : Matrix Large Small R) (output : Matrix Small Large R)
    (emptyReturn : output * input = 0) :
    IsMortal (fun _ : Unit => input * output) := by
  refine ⟨[(), ()], by simp, ?_⟩
  simpa [wordProduct, pow_two] using
    cut_sq_eq_zero_of_emptyReturn_eq_zero input output emptyReturn

end MatrixMortality.TwoRegisterPlaneNoGo
