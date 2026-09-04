import MatrixMortality.ProjectiveLine

/-!
# Mixed-radix tape obstruction

An additive tape boundary stores its independently variable left and right tails on opposite
radices. Moving the boundary rescales those tails by unequal factors. A single projectivity
cannot perform that operation: three variations of one tail and one variation of the other
already force every coefficient of its matrix to vanish.
-/

namespace MatrixMortality.MixedRadixTape

open scoped Matrix

/-- Cross-multiplied affine-chart action of a two-dimensional matrix. -/
def Realizes (matrix : Square (Fin 2) ℚ) (source target : ℚ) : Prop :=
  matrix 0 0 * source + matrix 0 1 =
    target * (matrix 1 0 * source + matrix 1 1)

private theorem unequal_scaling_normalized
    (a b c d x y leftScale rightScale : ℚ)
    (x_ne : x ≠ 0) (y_ne : y ≠ 0) (leftScale_ne : leftScale ≠ 0)
    (scales_ne : leftScale ≠ rightScale)
    (origin : a * 0 + b = 0 * (c * 0 + d))
    (leftOne : a * x + b = (leftScale * x) * (c * x + d))
    (leftTwo : a * (2 * x) + b =
      (leftScale * (2 * x)) * (c * (2 * x) + d))
    (rightOne : a * y + b = (rightScale * y) * (c * y + d)) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have b_zero : b = 0 := by
    simpa using origin
  have leftOne_normalized : a = leftScale * (c * x + d) := by
    have leftOne_zero : x * (a - leftScale * (c * x + d)) = 0 := by
      linear_combination leftOne - origin
    have difference_zero : a - leftScale * (c * x + d) = 0 :=
      (mul_eq_zero.mp leftOne_zero).resolve_left x_ne
    exact sub_eq_zero.mp difference_zero
  have leftTwo_normalized : a = leftScale * (c * (2 * x) + d) := by
    have two_x_ne : (2 : ℚ) * x ≠ 0 := mul_ne_zero (by norm_num) x_ne
    have leftTwo_zero :
        (2 * x) * (a - leftScale * (c * (2 * x) + d)) = 0 := by
      linear_combination leftTwo - origin
    have difference_zero : a - leftScale * (c * (2 * x) + d) = 0 :=
      (mul_eq_zero.mp leftTwo_zero).resolve_left two_x_ne
    exact sub_eq_zero.mp difference_zero
  have c_zero : c = 0 := by
    have product_zero : c * (leftScale * x) = 0 := by
      linear_combination leftOne_normalized - leftTwo_normalized
    exact (mul_eq_zero.mp product_zero).resolve_right
      (mul_ne_zero leftScale_ne x_ne)
  have a_eq : a = leftScale * d := by
    simpa [c_zero] using leftOne_normalized
  have rightOne_normalized : a = rightScale * d := by
    have rightOne_zero : y * (a - rightScale * d) = 0 := by
      linear_combination rightOne - origin + rightScale * y ^ 2 * c_zero
    have difference_zero : a - rightScale * d = 0 :=
      (mul_eq_zero.mp rightOne_zero).resolve_left y_ne
    exact sub_eq_zero.mp difference_zero
  have d_zero : d = 0 := by
    have product_zero : (leftScale - rightScale) * d = 0 := by
      rw [sub_mul, sub_eq_zero]
      exact a_eq.symm.trans rightOne_normalized
    exact (mul_eq_zero.mp product_zero).resolve_left (sub_ne_zero.mpr scales_ne)
  exact ⟨by simpa [d_zero] using a_eq, b_zero, c_zero, d_zero⟩

/-- A Möbius letter cannot rescale two independently variable tails by unequal factors.
Three variations of the left tail and one of the right tail already force its matrix to zero. -/
theorem unequalTailScaling_matrix_eq_zero
    (matrix : Square (Fin 2) ℚ)
    (sourceMarker targetMarker leftTail rightTail leftScale rightScale : ℚ)
    (leftTail_ne : leftTail ≠ 0) (rightTail_ne : rightTail ≠ 0)
    (leftScale_ne : leftScale ≠ 0) (scales_ne : leftScale ≠ rightScale)
    (origin : Realizes matrix sourceMarker targetMarker)
    (leftOne : Realizes matrix (sourceMarker + leftTail)
      (targetMarker + leftScale * leftTail))
    (leftTwo : Realizes matrix (sourceMarker + 2 * leftTail)
      (targetMarker + leftScale * (2 * leftTail)))
    (rightOne : Realizes matrix (sourceMarker + rightTail)
      (targetMarker + rightScale * rightTail)) :
    matrix = 0 := by
  let a := matrix 0 0 - targetMarker * matrix 1 0
  let b := matrix 0 0 * sourceMarker + matrix 0 1 -
    targetMarker * (matrix 1 0 * sourceMarker + matrix 1 1)
  let c := matrix 1 0
  let d := matrix 1 0 * sourceMarker + matrix 1 1
  have normalizedOrigin : a * 0 + b = 0 * (c * 0 + d) := by
    dsimp [a, b, c, d]
    have origin_eq := origin
    dsimp [Realizes] at origin_eq
    linear_combination origin_eq
  have normalizedLeftOne :
      a * leftTail + b =
        (leftScale * leftTail) * (c * leftTail + d) := by
    dsimp [a, b, c, d]
    have leftOne_eq := leftOne
    dsimp [Realizes] at leftOne_eq
    linear_combination leftOne_eq
  have normalizedLeftTwo :
      a * (2 * leftTail) + b =
        (leftScale * (2 * leftTail)) * (c * (2 * leftTail) + d) := by
    dsimp [a, b, c, d]
    have leftTwo_eq := leftTwo
    dsimp [Realizes] at leftTwo_eq
    linear_combination leftTwo_eq
  have normalizedRightOne :
      a * rightTail + b =
        (rightScale * rightTail) * (c * rightTail + d) := by
    dsimp [a, b, c, d]
    have rightOne_eq := rightOne
    dsimp [Realizes] at rightOne_eq
    linear_combination rightOne_eq
  obtain ⟨a_zero, b_zero, c_zero, d_zero⟩ :=
    unequal_scaling_normalized a b c d leftTail rightTail leftScale rightScale
      leftTail_ne rightTail_ne leftScale_ne scales_ne normalizedOrigin
      normalizedLeftOne normalizedLeftTwo normalizedRightOne
  have m10_zero : matrix 1 0 = 0 := c_zero
  have m11_zero : matrix 1 1 = 0 := by
    simpa [d, m10_zero] using d_zero
  have m00_zero : matrix 0 0 = 0 := by
    simpa [a, m10_zero] using a_zero
  have m01_zero : matrix 0 1 = 0 := by
    simpa [b, m00_zero, m10_zero, m11_zero] using b_zero
  ext i j
  fin_cases i <;> fin_cases j
  · exact m00_zero
  · exact m01_zero
  · exact m10_zero
  · exact m11_zero

end MatrixMortality.MixedRadixTape
