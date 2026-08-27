import MatrixMortality.NearyEncoding
import MatrixMortality.MatrixSemigroup
import MatrixMortality.PCPEncoding

/-!
# Side-normal correspondence matrices

The side-normal basis separates the upper and lower word channels of the ternary
correspondence representation.  The shared upper channel is the plane on which rule and
erasure roles agree.
-/

namespace MatrixMortality

open scoped Matrix

/-- The PCP representation after separating its lower- and upper-word channels. -/
def sidePcpMatrix (R : Type*) [CommRing R] (x y : List Bool) : Matrix (Fin 3) (Fin 3) R :=
  !![(1 : R), ternaryCode y, ternaryCode x;
     0, (3 : R) ^ y.length, 0;
     0, 0, (3 : R) ^ x.length]

theorem sidePcpMatrix_map {R S : Type*} [CommRing R] [CommRing S]
    (hom : R →+* S) (x y : List Bool) :
    (sidePcpMatrix R x y).map hom = sidePcpMatrix S x y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sidePcpMatrix]
  all_goals
    congr 1
    exact map_ofNat hom 3

/-- The unimodular change of basis separating the two word channels. -/
def sideChange (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  !![(1 : R), 0, 0;
     0, 1, 1;
     0, 0, 1]

/-- The inverse of `sideChange`. -/
def sideChangeInv (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  !![(1 : R), 0, 0;
     0, 1, -1;
     0, 0, 1]

theorem sideChangeInv_mul_sideChange (R : Type*) [CommRing R] :
    sideChangeInv R * sideChange R = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sideChangeInv, sideChange, Matrix.mul_apply,
      Fin.sum_univ_succ]

theorem sideChange_mul_sideChangeInv (R : Type*) [CommRing R] :
    sideChange R * sideChangeInv R = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sideChangeInv, sideChange, Matrix.mul_apply,
      Fin.sum_univ_succ]

theorem sidePcpMatrix_eq_conjugate (R : Type*) [CommRing R] (x y : List Bool) :
    sidePcpMatrix R x y = sideChangeInv R * pcpMatrix R x y * sideChange R := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sidePcpMatrix, sideChangeInv, sideChange, pcpMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ]
  all_goals ring

@[simp] theorem sidePcpMatrix_nil (R : Type*) [CommRing R] :
    sidePcpMatrix R [] [] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sidePcpMatrix]

theorem sidePcpMatrix_append (R : Type*) [CommRing R] (x y x' y' : List Bool) :
    sidePcpMatrix R (x ++ x') (y ++ y') =
      sidePcpMatrix R x y * sidePcpMatrix R x' y' := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sidePcpMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ, ternaryCode_append]
  all_goals ring

/-- The transformed right selector `P⁻¹e₃`. -/
def sideTailBasis (R : Type*) [CommRing R] : Fin 3 → R := ![0, -1, 1]

theorem sideTailBasis_map {R S : Type*} [CommRing R] [CommRing S]
    (hom : R →+* S) :
    hom ∘ sideTailBasis R = sideTailBasis S := by
  funext i
  fin_cases i <;> simp [sideTailBasis]

/-- The transformed fixed-boundary column. -/
def sideTerminalColumn (R : Type*) [CommRing R] (marker : List Bool) : Fin 3 → R :=
  sidePcpMatrix R marker [] *ᵥ sideTailBasis R

theorem sideTerminalColumn_map {R S : Type*} [CommRing R] [CommRing S]
    (hom : R →+* S) (marker : List Bool) :
    hom ∘ sideTerminalColumn R marker = sideTerminalColumn S marker := by
  funext i
  change hom ((sidePcpMatrix R marker [] *ᵥ sideTailBasis R) i) = _
  rw [RingHom.map_mulVec, sidePcpMatrix_map, sideTailBasis_map]
  rfl

@[simp] theorem sideTerminalColumn_zero (R : Type*) [CommRing R] (marker : List Bool) :
    sideTerminalColumn R marker 0 = (ternaryCode marker : R) := by
  simp [sideTerminalColumn, sidePcpMatrix, sideTailBasis, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]

/-- Product of the side-normal matrices named by a Neary role word. -/
def sideTileProduct (R : Type*) [CommRing R] (β : Nat) (body : List TagLetter)
    (word : List NearyTile) : Matrix (Fin 3) (Fin 3) R :=
  wordProduct
    (fun tile => sidePcpMatrix R (nearyUpper β tile) (nearyLower β body tile)) word

theorem sideTileProduct_map {R S : Type*} [CommRing R] [CommRing S]
    (hom : R →+* S) (β : Nat) (body : List TagLetter) (word : List NearyTile) :
    (sideTileProduct R β body word).map hom = sideTileProduct S β body word := by
  rw [sideTileProduct, wordProduct_mapMatrix]
  congr 1
  funext tile
  exact sidePcpMatrix_map hom (nearyUpper β tile) (nearyLower β body tile)

theorem sideTileProduct_append (R : Type*) [CommRing R] (β : Nat)
    (body : List TagLetter) (left right : List NearyTile) :
    sideTileProduct R β body (left ++ right) =
      sideTileProduct R β body left * sideTileProduct R β body right :=
  wordProduct_append _ left right

theorem sideTileProduct_eq_sidePcpMatrix (R : Type*) [CommRing R] (β : Nat)
    (body : List TagLetter) (word : List NearyTile) :
    sideTileProduct R β body word =
      sidePcpMatrix R (spell (nearyUpper β) word) (spell (nearyLower β body) word) := by
  induction word with
  | nil => simp [sideTileProduct, spell]
  | cons tile word ih =>
      simp only [sideTileProduct, wordProduct_cons, spell]
      change sidePcpMatrix R (nearyUpper β tile) (nearyLower β body tile) *
          sideTileProduct R β body word = _
      rw [ih, ← sidePcpMatrix_append]
      rfl

/-- The upper-word plane in side-normal coordinates. -/
def UpperSide {R : Type*} [CommRing R] (vector : Fin 3 → R) : Prop := vector 1 = 0

/-- A rule and its erasure role agree on the complete two-dimensional upper-word plane. -/
theorem rule_erase_agree_on_upperSide (R : Type*) [CommRing R] (β : Nat)
    (body : List TagLetter) (letter : TagLetter) (vector : Fin 3 → R)
    (upperSide : UpperSide vector) :
    sidePcpMatrix R (nearyUpper β (.rule letter)) (nearyLower β body (.rule letter)) *ᵥ
        vector =
      sidePcpMatrix R (nearyUpper β (.erase letter)) (nearyLower β body (.erase letter)) *ᵥ
        vector := by
  change vector 1 = 0 at upperSide
  funext i
  fin_cases i <;>
    simp [sidePcpMatrix, nearyUpper, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      upperSide]

/-- The coefficient of one side-normal role word. -/
def sideCoefficient (R : Type*) [CommRing R] (β : Nat) (body : List TagLetter)
    (word : List NearyTile) : R :=
  (sideTileProduct R β body word *ᵥ sideTerminalColumn R (nearyMarker β)) 0

theorem sideCoefficient_map {R S : Type*} [CommRing R] [CommRing S]
    (hom : R →+* S) (β : Nat) (body : List TagLetter) (word : List NearyTile) :
    hom (sideCoefficient R β body word) = sideCoefficient S β body word := by
  change hom ((sideTileProduct R β body word *ᵥ
    sideTerminalColumn R (nearyMarker β)) 0) = _
  rw [RingHom.map_mulVec, sideTileProduct_map, sideTerminalColumn_map]
  rfl

@[simp] theorem sideCoefficient_nil (R : Type*) [CommRing R] (β : Nat)
    (body : List TagLetter) :
    sideCoefficient R β body [] = (ternaryCode (nearyMarker β) : R) := by
  simp [sideCoefficient, sideTileProduct]

theorem sidePcpMatrix_mulVec_sideTailBasis_head (R : Type*) [CommRing R]
    (x y : List Bool) :
    (sidePcpMatrix R x y *ᵥ sideTailBasis R) 0 =
      (ternaryCode x : R) - ternaryCode y := by
  simp [sidePcpMatrix, sideTailBasis, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

theorem sidePcpMatrix_mulVec_sideTailBasis_head_rat (x y : List Bool) :
    (sidePcpMatrix ℚ x y *ᵥ sideTailBasis ℚ) 0 =
      (ternaryCode x : ℚ) - ternaryCode y :=
  sidePcpMatrix_mulVec_sideTailBasis_head ℚ x y

/-- Closed arithmetic form of the side-normal coefficient. -/
theorem sideCoefficient_eq_ternaryCode_sub (R : Type*) [CommRing R]
    (β : Nat) (body : List TagLetter) (word : List NearyTile) :
    sideCoefficient R β body word =
      (ternaryCode (spell (nearyUpper β) word ++ nearyMarker β) : R) -
        ternaryCode (spell (nearyLower β body) word) := by
  rw [sideCoefficient, sideTerminalColumn, Matrix.mulVec_mulVec,
    sideTileProduct_eq_sidePcpMatrix, ← sidePcpMatrix_append,
    sidePcpMatrix_mulVec_sideTailBasis_head R]
  simp

theorem sideCoefficient_eq_zero_iff_terminal_match (β : Nat) (body : List TagLetter)
    (word : List NearyTile) :
    sideCoefficient ℤ β body word = 0 ↔
      spell (nearyUpper β) word ++ nearyMarker β = spell (nearyLower β body) word := by
  rw [sideCoefficient, sideTerminalColumn, Matrix.mulVec_mulVec,
    sideTileProduct_eq_sidePcpMatrix, ← sidePcpMatrix_append]
  rw [sidePcpMatrix_mulVec_sideTailBasis_head ℤ, sub_eq_zero, Int.ofNat_inj]
  simpa using ternaryCode_injective.eq_iff

theorem sideCoefficient_eq_zero_iff_terminal_match_rat (β : Nat) (body : List TagLetter)
    (word : List NearyTile) :
    sideCoefficient ℚ β body word = 0 ↔
      spell (nearyUpper β) word ++ nearyMarker β = spell (nearyLower β body) word := by
  rw [sideCoefficient, sideTerminalColumn, Matrix.mulVec_mulVec,
    sideTileProduct_eq_sidePcpMatrix, ← sidePcpMatrix_append]
  rw [sidePcpMatrix_mulVec_sideTailBasis_head_rat, sub_eq_zero, Nat.cast_inj]
  simpa using ternaryCode_injective.eq_iff

end MatrixMortality
