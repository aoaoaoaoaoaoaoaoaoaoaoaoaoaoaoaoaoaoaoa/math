import MatrixMortality.FullMatrixAlgebra
import MatrixMortality.NearySideNormal
import MatrixMortality.PrefixMortality

/-!
# Algebra of the restricted prefix pair

The ten-state binary prefix decoder has an internal rank-one word.  This file exposes the
restricted generators in closed rational coordinates and records that word as an outer
product.  Later files prove that physical contexts around it span the full matrix algebra.
-/

namespace MatrixMortality

open scoped Matrix

namespace PrefixAlgebra.Certificate

theorem vecCons_val_three {α : Type*} {n : Nat}
    (head : α) (tail : Fin (n + 3) → α) :
    Matrix.vecCons head tail (3 : Fin (n + 4)) = tail 2 := rfl

theorem vecCons_val_four {α : Type*} {n : Nat}
    (head : α) (tail : Fin (n + 4) → α) :
    Matrix.vecCons head tail (4 : Fin (n + 5)) = tail 3 := rfl

theorem vecCons_val_five {α : Type*} {n : Nat}
    (head : α) (tail : Fin (n + 5) → α) :
    Matrix.vecCons head tail (5 : Fin (n + 6)) = tail 4 := rfl

theorem vecCons_val_six {α : Type*} {n : Nat}
    (head : α) (tail : Fin (n + 6) → α) :
    Matrix.vecCons head tail (6 : Fin (n + 7)) = tail 5 := rfl

theorem vecCons_val_seven {α : Type*} {n : Nat}
    (head : α) (tail : Fin (n + 7) → α) :
    Matrix.vecCons head tail (7 : Fin (n + 8)) = tail 6 := rfl

theorem vecCons_val_eight {α : Type*} {n : Nat}
    (head : α) (tail : Fin (n + 8) → α) :
    Matrix.vecCons head tail (8 : Fin (n + 9)) = tail 7 := rfl

theorem vecCons_val_nine {α : Type*} {n : Nat}
    (head : α) (tail : Fin (n + 9) → α) :
    Matrix.vecCons head tail (9 : Fin (n + 10)) = tail 8 := rfl

theorem fin_succ_two_eq_three {n : Nat} :
    Fin.succ (2 : Fin (n + 3)) = (3 : Fin (n + 4)) := by
  apply Fin.ext
  rfl

theorem fin_succ_three_eq_four {n : Nat} :
    Fin.succ (3 : Fin (n + 4)) = (4 : Fin (n + 5)) := by
  apply Fin.ext
  rfl

theorem fin_succ_four_eq_five {n : Nat} :
    Fin.succ (4 : Fin (n + 5)) = (5 : Fin (n + 6)) := by
  apply Fin.ext
  rfl

theorem fin_succ_five_eq_six {n : Nat} :
    Fin.succ (5 : Fin (n + 6)) = (6 : Fin (n + 7)) := by
  apply Fin.ext
  rfl

theorem fin_succ_six_eq_seven {n : Nat} :
    Fin.succ (6 : Fin (n + 7)) = (7 : Fin (n + 8)) := by
  apply Fin.ext
  rfl

theorem fin_succ_seven_eq_eight {n : Nat} :
    Fin.succ (7 : Fin (n + 8)) = (8 : Fin (n + 9)) := by
  apply Fin.ext
  rfl

theorem fin_succ_eight_eq_nine {n : Nat} :
    Fin.succ (8 : Fin (n + 9)) = (9 : Fin (n + 10)) := by
  apply Fin.ext
  rfl

end PrefixAlgebra.Certificate

open PrefixAlgebra.Certificate

attribute [local simp]
  vecCons_val_three vecCons_val_four vecCons_val_five vecCons_val_six
  vecCons_val_seven vecCons_val_eight vecCons_val_nine
  fin_succ_two_eq_three fin_succ_three_eq_four fin_succ_four_eq_five
  fin_succ_five_eq_six fin_succ_six_eq_seven fin_succ_seven_eq_eight
  fin_succ_eight_eq_nine

/-- Rational form of the restricted ten-state prefix generators. -/
def prefixAlgebraGenerator (β : Nat) (body : List TagLetter) (bit : Bool) :
    Square (Fin 10) ℚ :=
  castMatrix (restrictedPrefixGenerator β body bit)

namespace PrefixAlgebra.Certificate

/-- Entry formula after the one-hot restriction and deterministic prefix transition have been
eliminated. -/
private theorem restrictedPrefixGenerator_apply (β : Nat) (body : List TagLetter)
    (bit : Bool) (row column : Fin 10) :
    restrictedPrefixGenerator β body bit row column =
      ∑ payloadColumn : Fin 3,
        if prefixCoordinate
            (prefixNext (prefixRepresentative row).1 bit) payloadColumn = column
        then prefixOutput β body (prefixRepresentative row).1 bit
          (prefixRepresentative row).2 payloadColumn
        else 0 := by
  rw [restrictedPrefixGenerator, Matrix.mul_assoc, Matrix.mul_apply]
  rw [Finset.sum_eq_single (prefixRepresentative row)]
  · simp only [prefixRetract, if_pos, one_mul]
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single
      (prefixNext (prefixRepresentative row).1 bit)]
    · apply Finset.sum_congr rfl
      intro payloadColumn _
      simp [prefixMachine, WeightedTransducer.generator, prefixEmbed]
    · intro state _ state_ne
      apply Finset.sum_eq_zero
      intro payloadColumn _
      simp [prefixMachine, WeightedTransducer.generator, Ne.symm state_ne]
    · intro state_absent
      exact (state_absent (Finset.mem_univ _)).elim
  · intro large _ large_ne
    simp [prefixRetract, Ne.symm large_ne]
  · intro representative_absent
    exact (representative_absent (Finset.mem_univ _)).elim

/-- Closed three-state payload emitted on one prefix transition. -/
private def prefixAlgebraOutputClosed (β : Nat) (body : List TagLetter)
    (state : PrefixState) (bit : Bool) : Square (Fin 3) ℚ :=
  let ρ := (3 : ℚ) ^ β
  let m := (5 * ρ - 1) / 2
  let u := (15 * ρ + 1) / 2
  match state, bit with
  | .root, false =>
      !![m, -1, 3 * ρ;
         0, 0, 0;
         0, 0, 0]
  | .root, true | .one, false | .one, true => 1
  | .ten, false =>
      !![1, 0, 0;
         nearySideLowerC β body, nearySideLowerCScale β body, 0;
         2, 0, 3]
  | .ten, true =>
      !![1, 0, 0;
         25, 27, 0;
         u, 0, 9 * ρ]
  | .eleven, false =>
      !![1, 0, 0;
         1, 3, 0;
         2, 0, 3]
  | .eleven, true =>
      !![1, 0, 0;
         1, 3, 0;
         u, 0, 9 * ρ]

private theorem cast_normalizedNearyFamily_none (β : Nat) (body : List TagLetter) :
    castMatrix (normalizedNearyFamily β body none) =
      let ρ := (3 : ℚ) ^ β
      let m := (5 * ρ - 1) / 2
      !![m, -1, 3 * ρ;
         0, 0, 0;
         0, 0, 0] := by
  have marker_value :
      (ternaryCode (nearyMarker β) : ℚ) = (5 * (3 : ℚ) ^ β - 1) / 2 := by
    simpa [nearySideMarkerValue] using nearySideMarkerValue_eq β
  have marker_scale :
      ((3 : ℚ) ^ (nearyMarker β).length) = 3 * (3 : ℚ) ^ β := by
    simpa [nearySideMarkerScale] using nearySideMarkerScale_eq β
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [normalizedNearyFamily, nearyMortalityFamilyInt, absorbedFamilyInt,
      separatedGenerator, terminalGeneratorInt, terminalColumnInt, sideChange,
      sideChangeInv, pcpMatrix, castMatrix, Matrix.transpose_apply,
      Matrix.vecMulVec, Matrix.mul_apply, Matrix.mulVec, Matrix.dotProduct,
      Matrix.vecHead, Matrix.vecTail, headBasis, tailBasis, Fin.sum_univ_succ,
      marker_value, marker_scale] <;>
    ring

private theorem cast_normalizedNearyFamily_some
    (β : Nat) (body : List TagLetter) (tile : NearyTile) :
    castMatrix (normalizedNearyFamily β body (some tile)) =
      (sidePcpMatrix ℚ (nearyUpper β tile) (nearyLower β body tile))ᵀ := by
  rw [normalizedNearyFamily_some]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [castMatrix, sidePcpMatrix, Matrix.transpose_apply, Matrix.vecHead,
      Matrix.vecTail]

private theorem cast_prefixOutput_eq_closed (β : Nat) (body : List TagLetter)
    (state : PrefixState) (bit : Bool) :
    castMatrix (prefixOutput β body state bit) =
      prefixAlgebraOutputClosed β body state bit := by
  have upper_b :
      (ternaryCode (tagCode β .b) : ℚ) = (15 * (3 : ℚ) ^ β + 1) / 2 := by
    simpa [nearySideUpperB] using nearySideUpperB_eq β
  have rule_b_value : (ternaryCode [true, true, false] : ℚ) = 25 := by
    norm_num [ternaryCode, ternaryDigit, Nat.ofDigits]
  have erase_value : ternaryDigit false = 1 := rfl
  cases state <;> cases bit
  · simp only [prefixOutput, prefixEmission]
    rw [cast_normalizedNearyFamily_none]
    rfl
  · ext row column
    fin_cases row <;> fin_cases column <;>
      simp [prefixOutput, prefixEmission, prefixAlgebraOutputClosed, castMatrix,
        Matrix.one_apply]
  · ext row column
    fin_cases row <;> fin_cases column <;>
      simp [prefixOutput, prefixEmission, prefixAlgebraOutputClosed, castMatrix,
        Matrix.one_apply]
  · ext row column
    fin_cases row <;> fin_cases column <;>
      simp [prefixOutput, prefixEmission, prefixAlgebraOutputClosed, castMatrix,
        Matrix.one_apply]
  · rw [prefixOutput, prefixEmission, cast_normalizedNearyFamily_some]
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [prefixAlgebraOutputClosed, sidePcpMatrix, nearyUpper, nearyLower,
        Matrix.transpose_apply, Matrix.vecHead, Matrix.vecTail,
        nearySideLowerC, nearySideLowerCScale, ternaryCode, ternaryDigit,
        tagCode, pow_add]
  · rw [prefixOutput, prefixEmission, cast_normalizedNearyFamily_some]
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [prefixAlgebraOutputClosed, sidePcpMatrix, nearyUpper, nearyLower,
        Matrix.transpose_apply, Matrix.vecHead, Matrix.vecTail, upper_b,
        rule_b_value]
    all_goals norm_num
    all_goals ring
  · rw [prefixOutput, prefixEmission, cast_normalizedNearyFamily_some]
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [prefixAlgebraOutputClosed, sidePcpMatrix, nearyUpper, nearyLower,
        Matrix.transpose_apply, Matrix.vecHead, Matrix.vecTail, ternaryCode,
        ternaryDigit, tagCode, pow_add]
  · rw [prefixOutput, prefixEmission, cast_normalizedNearyFamily_some]
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [prefixAlgebraOutputClosed, sidePcpMatrix, nearyUpper, nearyLower,
        Matrix.transpose_apply, Matrix.vecHead, Matrix.vecTail, upper_b,
        erase_value, pow_add]
    all_goals ring

/-- Rational entry formula for the restricted generator. -/
private theorem prefixAlgebraGenerator_apply (β : Nat) (body : List TagLetter)
    (bit : Bool) (row column : Fin 10) :
    prefixAlgebraGenerator β body bit row column =
      ∑ payloadColumn : Fin 3,
        if prefixCoordinate
            (prefixNext (prefixRepresentative row).1 bit) payloadColumn = column
        then prefixAlgebraOutputClosed β body (prefixRepresentative row).1 bit
          (prefixRepresentative row).2 payloadColumn
        else 0 := by
  change
    ((restrictedPrefixGenerator β body bit row column : ℤ) : ℚ) =
      ∑ payloadColumn : Fin 3,
        if prefixCoordinate
            (prefixNext (prefixRepresentative row).1 bit) payloadColumn = column
        then prefixAlgebraOutputClosed β body (prefixRepresentative row).1 bit
          (prefixRepresentative row).2 payloadColumn
        else 0
  rw [restrictedPrefixGenerator_apply]
  push_cast
  apply Finset.sum_congr rfl
  intro payloadColumn _
  split
  · change
      castMatrix
          (prefixOutput β body (prefixRepresentative row).1 bit)
          (prefixRepresentative row).2 payloadColumn =
        prefixAlgebraOutputClosed β body (prefixRepresentative row).1 bit
          (prefixRepresentative row).2 payloadColumn
    rw [cast_prefixOutput_eq_closed]
  · rfl

/-- Closed coordinate form of the restricted ten-state prefix generators. -/
def prefixAlgebraGeneratorClosed (β : Nat) (body : List TagLetter) :
    Bool → Square (Fin 10) ℚ
  | false =>
      let ρ := (3 : ℚ) ^ β
      let m := (5 * ρ - 1) / 2
      let V := nearySideLowerC β body
      let B := nearySideLowerCScale β body
      !![m, -1, 3 * ρ, 0, 0, 0, 0, 0, 0, 0;
         0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
         0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
         0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
         0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
         0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
         1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
         V, B, 0, 0, 0, 0, 0, 0, 0, 0;
         2, 0, 3, 0, 0, 0, 0, 0, 0, 0;
         1, 3, 0, 0, 0, 0, 0, 0, 0, 0]
  | true =>
      let ρ := (3 : ℚ) ^ β
      let u := (15 * ρ + 1) / 2
      !![0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
         0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
         0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
         0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
         0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
         0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
         1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
         25, 27, 0, 0, 0, 0, 0, 0, 0, 0;
         u, 0, 9 * ρ, 0, 0, 0, 0, 0, 0, 0;
         1, 3, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Column action of the closed zero generator. -/
theorem prefixAlgebraGeneratorClosed_false_mulVec
    (β : Nat) (body : List TagLetter) (vector : Fin 10 → ℚ) :
    prefixAlgebraGeneratorClosed β body false *ᵥ vector =
      let ρ := (3 : ℚ) ^ β
      let m := (5 * ρ - 1) / 2
      ![m * vector 0 - vector 1 + 3 * ρ * vector 2,
        0,
        0,
        vector 6,
        vector 7,
        vector 8,
        vector 0,
        nearySideLowerC β body * vector 0 +
          nearySideLowerCScale β body * vector 1,
        2 * vector 0 + 3 * vector 2,
        vector 0 + 3 * vector 1] := by
  ext coordinate
  fin_cases coordinate <;>
    simp [prefixAlgebraGeneratorClosed, Matrix.mulVec, Matrix.dotProduct,
      Fin.sum_univ_succ]
  all_goals ring

/-- Column action of the closed one generator. -/
theorem prefixAlgebraGeneratorClosed_true_mulVec
    (β : Nat) (body : List TagLetter) (vector : Fin 10 → ℚ) :
    prefixAlgebraGeneratorClosed β body true *ᵥ vector =
      let ρ := (3 : ℚ) ^ β
      let u := (15 * ρ + 1) / 2
      ![vector 3,
        vector 4,
        vector 5,
        vector 6,
        vector 9,
        vector 8,
        vector 0,
        25 * vector 0 + 27 * vector 1,
        u * vector 0 + 9 * ρ * vector 2,
        vector 0 + 3 * vector 1] := by
  ext coordinate
  fin_cases coordinate <;>
    simp [prefixAlgebraGeneratorClosed, Matrix.mulVec, Matrix.dotProduct,
      Fin.sum_univ_succ]

/-- Row action on the closed zero generator. -/
theorem prefixAlgebraGeneratorClosed_vecMul_false
    (β : Nat) (body : List TagLetter) (vector : Fin 10 → ℚ) :
    vector ᵥ* prefixAlgebraGeneratorClosed β body false =
      let ρ := (3 : ℚ) ^ β
      let m := (5 * ρ - 1) / 2
      ![m * vector 0 + vector 6 + nearySideLowerC β body * vector 7 +
          2 * vector 8 + vector 9,
        -vector 0 + nearySideLowerCScale β body * vector 7 + 3 * vector 9,
        3 * ρ * vector 0 + 3 * vector 8,
        0,
        0,
        0,
        vector 3,
        vector 4,
        vector 5,
        0] := by
  ext coordinate
  fin_cases coordinate <;>
    simp [prefixAlgebraGeneratorClosed, Matrix.vecMul, Matrix.dotProduct,
      Fin.sum_univ_succ]
  all_goals ring

/-- Row action on the closed one generator. -/
theorem prefixAlgebraGeneratorClosed_vecMul_true
    (β : Nat) (body : List TagLetter) (vector : Fin 10 → ℚ) :
    vector ᵥ* prefixAlgebraGeneratorClosed β body true =
      let ρ := (3 : ℚ) ^ β
      let u := (15 * ρ + 1) / 2
      ![vector 6 + 25 * vector 7 + u * vector 8 + vector 9,
        27 * vector 7 + 3 * vector 9,
        9 * ρ * vector 8,
        vector 0,
        vector 1,
        vector 2,
        vector 3,
        0,
        vector 5,
        vector 4] := by
  ext coordinate
  fin_cases coordinate <;>
    simp [prefixAlgebraGeneratorClosed, Matrix.vecMul, Matrix.dotProduct,
      Fin.sum_univ_succ]
  all_goals ring

private theorem prefixAlgebraGenerator_mulVec_eq_closed
    (β : Nat) (body : List TagLetter) (bit : Bool) (vector : Fin 10 → ℚ) :
    prefixAlgebraGenerator β body bit *ᵥ vector =
      prefixAlgebraGeneratorClosed β body bit *ᵥ vector := by
  cases bit
  · rw [prefixAlgebraGeneratorClosed_false_mulVec]
    ext coordinate
    fin_cases coordinate <;>
      simp [Matrix.mulVec, prefixAlgebraGenerator_apply, prefixAlgebraOutputClosed,
        prefixRepresentative, prefixCoordinate, prefixNext, Matrix.dotProduct,
        Matrix.vecHead, Matrix.vecTail, Matrix.one_apply, Fin.sum_univ_succ]
    all_goals ring
  · rw [prefixAlgebraGeneratorClosed_true_mulVec]
    ext coordinate
    fin_cases coordinate <;>
      simp [Matrix.mulVec, prefixAlgebraGenerator_apply, prefixAlgebraOutputClosed,
        prefixRepresentative, prefixCoordinate, prefixNext, Matrix.dotProduct,
        Matrix.vecHead, Matrix.vecTail, Matrix.one_apply, Fin.sum_univ_succ]

theorem prefixAlgebraGenerator_eq_closed (β : Nat) (body : List TagLetter)
    (bit : Bool) :
    prefixAlgebraGenerator β body bit =
      prefixAlgebraGeneratorClosed β body bit := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro vector
  exact prefixAlgebraGenerator_mulVec_eq_closed β body bit vector

private theorem prefixAlgebraGenerator_eq_closed_fun (β : Nat) (body : List TagLetter) :
    prefixAlgebraGenerator β body =
      prefixAlgebraGeneratorClosed β body := by
  funext bit
  exact prefixAlgebraGenerator_eq_closed β body bit

end PrefixAlgebra.Certificate

/-- Column of the internal rank-one word `000`. -/
def prefixAlgebraColumn (β : Nat) (body : List TagLetter) : Fin 10 → ℚ :=
  let ρ := (3 : ℚ) ^ β
  let m := (5 * ρ - 1) / 2
  let V := nearySideLowerC β body
  ![m ^ 2, 0, 0, 1, V, 2, m, m * V, 2 * m, m]

/-- Row of the internal rank-one word `000`. -/
def prefixAlgebraRow (β : Nat) : Fin 10 → ℚ :=
  let ρ := (3 : ℚ) ^ β
  let m := (5 * ρ - 1) / 2
  ![m, -1, 3 * ρ, 0, 0, 0, 0, 0, 0, 0]

/-- The physical word `000` is the displayed nonzero rank-one outer product. -/
theorem prefixAlgebra_zero_cube (β : Nat) (body : List TagLetter) :
    wordProduct (prefixAlgebraGenerator β body) [false, false, false] =
      Matrix.vecMulVec (prefixAlgebraColumn β body) (prefixAlgebraRow β) := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro vector
  simp only [Matrix.toLin'_apply', Matrix.mulVecLin_apply]
  rw [prefixAlgebraGenerator_eq_closed_fun]
  change
    ((1 * prefixAlgebraGeneratorClosed β body false *
          prefixAlgebraGeneratorClosed β body false) *
        prefixAlgebraGeneratorClosed β body false) *ᵥ vector =
      Matrix.vecMulVec (prefixAlgebraColumn β body) (prefixAlgebraRow β) *ᵥ vector
  simp only [one_mul]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  change
    prefixAlgebraGeneratorClosed β body false *ᵥ
        (prefixAlgebraGeneratorClosed β body false *ᵥ
          (prefixAlgebraGeneratorClosed β body false *ᵥ vector)) =
      Matrix.vecMulVec (prefixAlgebraColumn β body) (prefixAlgebraRow β) *ᵥ vector
  rw [prefixAlgebraGeneratorClosed_false_mulVec,
    prefixAlgebraGeneratorClosed_false_mulVec,
    prefixAlgebraGeneratorClosed_false_mulVec]
  ext coordinate
  fin_cases coordinate <;>
    simp [prefixAlgebraColumn, prefixAlgebraRow, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_succ] <;>
    ring

end MatrixMortality
