import MatrixMortality.Computability
import MatrixMortality.TernaryEncoding

/-!
# The three-dimensional PCP matrix morphism

The definition is polymorphic over a commutative ring.  At `ℤ` it is the computable integer
matrix emitted by the reduction; at `ℚ` it is the same matrix viewed in the field where its
nonsingularity is expressed by `IsUnit`.
-/

namespace MatrixMortality

open scoped Matrix

/-- Cassaigne–Halava–Harju–Nicolas's three-dimensional encoding of a pair of words. -/
def pcpMatrix (R : Type*) [CommRing R] (x y : List Bool) : Matrix (Fin 3) (Fin 3) R :=
  !![(1 : R), ternaryCode y, ternaryCode x - ternaryCode y;
     0, (3 : R) ^ y.length, (3 : R) ^ x.length - (3 : R) ^ y.length;
     0, 0, (3 : R) ^ x.length]

/-- Every entry of the integral PCP matrix is primitive recursive in two primitive-recursive word
families. -/
theorem pcpMatrixInt_entry_primrec {α : Type*} [Primcodable α] {x y : α → List Bool}
    (xRec : Primrec x) (yRec : Primrec y) (row column : Fin 3) :
    Primrec fun input => pcpMatrix ℤ (x input) (y input) row column := by
  have xCodeRec : Primrec fun input => ternaryCode (x input) :=
    ternaryCode_primrec.comp xRec
  have yCodeRec : Primrec fun input => ternaryCode (y input) :=
    ternaryCode_primrec.comp yRec
  have xPowerRec : Primrec fun input => 3 ^ (x input).length :=
    MatrixMortality.Primrec.nat_pow.comp (Primrec.const 3)
      (Primrec.list_length.comp xRec)
  have yPowerRec : Primrec fun input => 3 ^ (y input).length :=
    MatrixMortality.Primrec.nat_pow.comp (Primrec.const 3)
      (Primrec.list_length.comp yRec)
  have yCodeIntRec : Primrec fun input => Int.ofNat (ternaryCode (y input)) :=
    MatrixMortality.Primrec.int_ofNat.comp yCodeRec
  have xPowerIntRec : Primrec fun input => Int.ofNat (3 ^ (x input).length) :=
    MatrixMortality.Primrec.int_ofNat.comp xPowerRec
  have yPowerIntRec : Primrec fun input => Int.ofNat (3 ^ (y input).length) :=
    MatrixMortality.Primrec.int_ofNat.comp yPowerRec
  fin_cases row <;> fin_cases column
  · exact Primrec.const 1
  · simpa [pcpMatrix, Matrix.vecHead, Matrix.vecTail] using yCodeIntRec
  · simpa [pcpMatrix, Matrix.vecHead, Matrix.vecTail] using
      MatrixMortality.Primrec.int_subNat.comp xCodeRec yCodeRec
  · exact Primrec.const 0
  · simpa [pcpMatrix, Matrix.vecHead, Matrix.vecTail] using yPowerIntRec
  · simpa [pcpMatrix, Matrix.vecHead, Matrix.vecTail] using
      MatrixMortality.Primrec.int_subNat.comp xPowerRec yPowerRec
  · exact Primrec.const 0
  · exact Primrec.const 0
  · simpa [pcpMatrix, Matrix.vecHead, Matrix.vecTail] using xPowerIntRec

@[simp] theorem pcpMatrix_nil (R : Type*) [CommRing R] : pcpMatrix R [] [] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pcpMatrix, Matrix.vecHead, Matrix.vecTail]

theorem pcpMatrix_append (R : Type*) [CommRing R] (x y x' y' : List Bool) :
    pcpMatrix R (x ++ x') (y ++ y') = pcpMatrix R x y * pcpMatrix R x' y' := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pcpMatrix, Matrix.vecHead, Matrix.vecTail, Matrix.mul_apply, Fin.sum_univ_succ,
      ternaryCode_append] <;> ring

@[simp] theorem pcpMatrix_top_right (R : Type*) [CommRing R] (x y : List Bool) :
    pcpMatrix R x y 0 2 = (ternaryCode x : R) - ternaryCode y := by
  simp [pcpMatrix]

theorem pcpMatrix_top_right_eq_zero_iff (x y : List Bool) :
    pcpMatrix ℤ x y 0 2 = 0 ↔ x = y := by
  rw [pcpMatrix_top_right, sub_eq_zero, Int.ofNat_inj]
  exact ternaryCode_injective.eq_iff

theorem pcpMatrix_top_right_eq_zero_iff_rat (x y : List Bool) :
    pcpMatrix ℚ x y 0 2 = 0 ↔ x = y := by
  rw [pcpMatrix_top_right, sub_eq_zero, Nat.cast_inj]
  exact ternaryCode_injective.eq_iff

theorem pcpMatrix_det (R : Type*) [CommRing R] (x y : List Bool) :
    (pcpMatrix R x y).det = (3 : R) ^ (x.length + y.length) := by
  rw [Matrix.det_fin_three]
  simp [pcpMatrix, Matrix.vecHead, Matrix.vecTail, pow_add, mul_comm]

theorem pcpMatrix_upperTriangular (R : Type*) [CommRing R] (x y : List Bool) :
    (pcpMatrix R x y).BlockTriangular id := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp [pcpMatrix, Matrix.vecHead, Matrix.vecTail] at h ⊢

theorem pcpMatrix_det_ne_zero_int (x y : List Bool) : (pcpMatrix ℤ x y).det ≠ 0 := by
  rw [pcpMatrix_det]
  positivity

theorem pcpMatrix_isUnit_rat (x y : List Bool) : IsUnit (pcpMatrix ℚ x y) := by
  rw [Matrix.isUnit_iff_isUnit_det, pcpMatrix_det, isUnit_iff_ne_zero]
  positivity

end MatrixMortality
