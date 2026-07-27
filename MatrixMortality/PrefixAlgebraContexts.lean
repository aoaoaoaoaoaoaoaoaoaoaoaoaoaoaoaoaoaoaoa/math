import MatrixMortality.PrefixAlgebra

/-!
# Ten-state prefix-algebra contexts

The internal word `000` supplies a rank-one boundary.  Ten powers of the one-generator give
reachable columns; ten short physical words give observable rows.  A monic Krylov basis change
exposes the reachable matrix as a `3+3+3+1` block filtration.
-/

namespace MatrixMortality

open scoped Matrix

attribute [local simp]
  vecCons_val_three vecCons_val_four vecCons_val_five vecCons_val_six
  vecCons_val_seven vecCons_val_eight vecCons_val_nine
  fin_succ_two_eq_three fin_succ_three_eq_four fin_succ_four_eq_five
  fin_succ_five_eq_six fin_succ_six_eq_seven fin_succ_seven_eq_eight
  fin_succ_eight_eq_nine

private theorem mulVec_const_mul {ι : Type*} [Fintype ι]
    (matrix : Matrix ι ι ℚ) (scalar : ℚ) (vector : ι → ℚ) :
    matrix *ᵥ ((fun _ => scalar) * vector) =
      (fun _ => scalar) * (matrix *ᵥ vector) := by
  change matrix *ᵥ (scalar • vector) = scalar • (matrix *ᵥ vector)
  exact Matrix.mulVec_smul matrix scalar vector

private theorem mulVec_mul_const {ι : Type*} [Fintype ι]
    (matrix : Matrix ι ι ℚ) (scalar : ℚ) (vector : ι → ℚ) :
    matrix *ᵥ (vector * fun _ => scalar) =
      (matrix *ᵥ vector) * fun _ => scalar := by
  have vector_mul : vector * (fun _ => scalar) = scalar • vector := by
    funext index
    simp [mul_comm]
  rw [vector_mul, Matrix.mulVec_smul]
  funext index
  simp [mul_comm]

private theorem mulVec_nine_mul {ι : Type*} [Fintype ι]
    (matrix : Matrix ι ι ℚ) (vector : ι → ℚ) :
    matrix *ᵥ ((9 : ι → ℚ) * vector) =
      (9 : ι → ℚ) * (matrix *ᵥ vector) := by
  change matrix *ᵥ ((fun _ => (9 : ℚ)) * vector) =
    (fun _ => (9 : ℚ)) * (matrix *ᵥ vector)
  change matrix *ᵥ ((9 : ℚ) • vector) = (9 : ℚ) • (matrix *ᵥ vector)
  exact Matrix.mulVec_smul matrix 9 vector

/-- Physical one-generator powers selecting ten reachable columns. -/
def prefixAlgebraLeftWords : Fin 10 → List Bool :=
  ![[],
    [true],
    [true, true],
    [true, true, true],
    [true, true, true, true],
    [true, true, true, true, true],
    [true, true, true, true, true, true],
    [true, true, true, true, true, true, true],
    [true, true, true, true, true, true, true, true],
    [true, true, true, true, true, true, true, true, true]]

/-- Physical words selecting ten observable rows. -/
def prefixAlgebraRightWords : Fin 10 → List Bool :=
  ![[],
    [true],
    [true, false],
    [true, true],
    [true, false, true],
    [true, true, false],
    [true, false, true, true],
    [true, true, false, true],
    [true, false, true, true, false],
    [true, true, false, true, false]]

/-- Reachable Krylov matrix around the internal rank-one word. -/
def prefixAlgebraReachable (β : Nat) (body : List TagLetter) :
    Square (Fin 10) ℚ :=
  contextColumns (prefixAlgebraGenerator β body)
    (prefixAlgebraColumn β body) prefixAlgebraLeftWords

/-- Observable context matrix around the internal rank-one word. -/
def prefixAlgebraObservable (β : Nat) (body : List TagLetter) :
    Square (Fin 10) ℚ :=
  contextRows (prefixAlgebraGenerator β body)
    (prefixAlgebraRow β) prefixAlgebraRightWords

/-- The body-dependent lower-code displacement from the fixed rule-`b` value. -/
def prefixAlgebraLowerGap (β : Nat) (body : List TagLetter) : ℚ :=
  chhnNearyLowerC β body - 25

/-- Monic polynomial change from the ordinary Krylov columns to the adapted filtration. -/
def prefixAlgebraReachabilityChange (β : Nat) : Square (Fin 10) ℚ :=
  let ρ := (3 : ℚ) ^ β
  !![1, 0, 0, -1, 0, 0, 9 * ρ, 0, 0, -27 * ρ;
     0, 1, 0, 0, -1, 0, 0, 9 * ρ, 0, 0;
     0, 0, 1, 0, 0, -1, 0, 0, 9 * ρ, 0;
     0, 0, 0, 1, 0, 0, -(1 + 9 * ρ), 0, 0, 3 + 36 * ρ;
     0, 0, 0, 0, 1, 0, 0, -(1 + 9 * ρ), 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0, -(1 + 9 * ρ), 0;
     0, 0, 0, 0, 0, 0, 1, 0, 0, -(4 + 9 * ρ);
     0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

/-- First annihilating-polynomial difference `(T³-I)u`. -/
def prefixAlgebraSeedA (β : Nat) (body : List TagLetter) : Fin 10 → ℚ :=
  let T := prefixAlgebraGenerator β body true
  let u := prefixAlgebraColumn β body
  T *ᵥ (T *ᵥ (T *ᵥ u)) - u

/-- Second annihilating-polynomial difference `(T³-9ρI)(T³-I)u`. -/
def prefixAlgebraSeedC (β : Nat) (body : List TagLetter) : Fin 10 → ℚ :=
  let ρ := (3 : ℚ) ^ β
  let T := prefixAlgebraGenerator β body true
  let seed := prefixAlgebraSeedA β body
  T *ᵥ (T *ᵥ (T *ᵥ seed)) - 9 * ρ • seed

/-- Final annihilating-polynomial difference, supported on one coordinate. -/
def prefixAlgebraSeedB (β : Nat) (body : List TagLetter) : Fin 10 → ℚ :=
  let T := prefixAlgebraGenerator β body true
  let seed := prefixAlgebraSeedC β body
  T *ᵥ (T *ᵥ (T *ᵥ seed)) - 3 • seed

/-- Adapted reachable columns grouped by the cubic factors of the one-generator dynamics. -/
def prefixAlgebraAdapted (β : Nat) (body : List TagLetter) :
    Square (Fin 10) ℚ :=
  let T := prefixAlgebraGenerator β body true
  let u := prefixAlgebraColumn β body
  let a := prefixAlgebraSeedA β body
  let c := prefixAlgebraSeedC β body
  let b := prefixAlgebraSeedB β body
  fun row index =>
    ![u, T *ᵥ u, T *ᵥ (T *ᵥ u),
      a, T *ᵥ a, T *ᵥ (T *ᵥ a),
      c, T *ᵥ c, T *ᵥ (T *ᵥ c), b] index row

/-- Closed form of the adapted reachable matrix. -/
def prefixAlgebraAdaptedClosed (β : Nat) (body : List TagLetter) :
    Square (Fin 10) ℚ :=
  let ρ := (3 : ℚ) ^ β
  let m := (5 * ρ - 1) / 2
  let u := (15 * ρ + 1) / 2
  let V := chhnNearyLowerC β body
  let x := prefixAlgebraLowerGap β body
  !![m ^ 2, 1, m, 0, 0, 0, 0, 0, 0, 0;
     0, V, m, m ^ 2, 2 * V + 1, 3 * m,
       -3 * (3 * ρ - 1) * m ^ 2,
       -3 * (3 * ρ - 1) * (2 * V + 1),
       -9 * (3 * ρ - 1) * m, 0;
     0, 2, 2 * m, m ^ 2 * u, 3 * (17 * ρ - 1) / 2,
       3 * m * (17 * ρ - 1) / 2, 0, 0, 0, 0;
     1, m, m ^ 2, 0, 0, 0, 0, 0, 0, 0;
     V, m, m ^ 2, 2 * V + 1, 3 * m, 3 * m ^ 2,
       -3 * (3 * ρ - 1) * (2 * V + 1),
       -9 * (3 * ρ - 1) * m,
       -9 * (3 * ρ - 1) * m ^ 2, 0;
     2, 2 * m, m ^ 2 * u, 3 * (17 * ρ - 1) / 2,
       3 * m * (17 * ρ - 1) / 2, 9 * ρ * m ^ 2 * u, 0, 0, 0, 0;
     m, m ^ 2, 1, 0, 0, 0, 0, 0, 0, 0;
     m * V, 25 * m ^ 2, 27 * x + 700, -m * (x - 27), 27 * m ^ 2,
       27 * (2 * V + 1), 9 * m * (ρ * x - 27 * ρ + 9),
       -81 * (3 * ρ - 1) * m ^ 2,
       -81 * (3 * ρ - 1) * (2 * V + 1), -27 * ρ * x * m;
     2 * m, m ^ 2 * u, (51 * ρ + 1) / 2,
       3 * m * (17 * ρ - 1) / 2, 9 * ρ * m ^ 2 * u,
       27 * ρ * (17 * ρ - 1) / 2, 0, 0, 0, 0;
     m, m ^ 2, 3 * x + 76, 3 * m, 3 * m ^ 2, 3 * (2 * V + 1),
       -9 * (3 * ρ - 1) * m,
       -9 * (3 * ρ - 1) * m ^ 2,
       -9 * (3 * ρ - 1) * (2 * V + 1), 0]

/-- One row of the closed sparse observable context matrix. -/
def prefixAlgebraObservableClosedRow
    (β : Nat) (row : Fin 10) : Fin 10 → ℚ :=
  let ρ := (3 : ℚ) ^ β
  let m := (5 * ρ - 1) / 2
  let large := (45 * ρ ^ 2 + 8 * ρ - 51) / 2
  let small := (17 * ρ - 3) / 2
  ![![m, -1, 3 * ρ, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, m, -1, 3 * ρ, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, m, -1, 3 * ρ, 0],
    ![0, 0, 0, 0, 0, 0, m, 0, 3 * ρ, -1],
    ![large, -27, 27 * ρ ^ 2, 0, 0, 0, 0, 0, 0, 0],
    ![small, -3, 9 * ρ, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, large, -27, 27 * ρ ^ 2, 0, 0, 0, 0],
    ![0, 0, 0, small, -3, 9 * ρ, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, large, -27, 27 * ρ ^ 2, 0],
    ![0, 0, 0, 0, 0, 0, small, -3, 9 * ρ, 0]] row

/-- Closed sparse form of the observable context matrix. -/
def prefixAlgebraObservableClosed (β : Nat) : Square (Fin 10) ℚ :=
  prefixAlgebraObservableClosedRow β

private def prefixAlgebraAdaptedClosedColumn
    (β : Nat) (body : List TagLetter) (column : Fin 10) : Fin 10 → ℚ :=
  fun row => prefixAlgebraAdaptedClosed β body row column

@[simp]
private theorem prefixAlgebraAdaptedClosedColumn_apply
    (β : Nat) (body : List TagLetter) (column row : Fin 10) :
    prefixAlgebraAdaptedClosedColumn β body column row =
      prefixAlgebraAdaptedClosed β body row column :=
  rfl

private theorem prefixAlgebraAdaptedClosedColumn_zero
    (β : Nat) (body : List TagLetter) :
    prefixAlgebraColumn β body =
      prefixAlgebraAdaptedClosedColumn β body 0 := by
  ext row
  fin_cases row <;>
    simp [prefixAlgebraColumn, prefixAlgebraAdaptedClosedColumn,
      prefixAlgebraAdaptedClosed]

private theorem prefixAlgebraAdaptedClosedColumn_step_zero
    (β : Nat) (body : List TagLetter) :
    prefixAlgebraGenerator β body true *ᵥ
        prefixAlgebraAdaptedClosedColumn β body 0 =
      prefixAlgebraAdaptedClosedColumn β body 1 := by
  rw [prefixAlgebraGenerator_eq_closed,
    prefixAlgebraGeneratorClosed_true_mulVec]
  ext row
  fin_cases row <;>
    (simp [prefixAlgebraAdaptedClosedColumn, prefixAlgebraAdaptedClosed,
      prefixAlgebraLowerGap, Matrix.vecHead, Matrix.vecTail] <;> ring)

private theorem prefixAlgebraAdaptedClosedColumn_step_one
    (β : Nat) (body : List TagLetter) :
    prefixAlgebraGenerator β body true *ᵥ
        prefixAlgebraAdaptedClosedColumn β body 1 =
      prefixAlgebraAdaptedClosedColumn β body 2 := by
  rw [prefixAlgebraGenerator_eq_closed,
    prefixAlgebraGeneratorClosed_true_mulVec]
  ext row
  fin_cases row <;>
    (simp [prefixAlgebraAdaptedClosedColumn, prefixAlgebraAdaptedClosed,
      prefixAlgebraLowerGap, Matrix.vecHead, Matrix.vecTail] <;> ring)

private theorem prefixAlgebraAdaptedClosedColumn_cut_a
    (β : Nat) (body : List TagLetter) :
    prefixAlgebraGenerator β body true *ᵥ
          prefixAlgebraAdaptedClosedColumn β body 2 -
        prefixAlgebraAdaptedClosedColumn β body 0 =
      prefixAlgebraAdaptedClosedColumn β body 3 := by
  rw [prefixAlgebraGenerator_eq_closed,
    prefixAlgebraGeneratorClosed_true_mulVec]
  ext row
  fin_cases row <;>
    (simp [prefixAlgebraAdaptedClosedColumn, prefixAlgebraAdaptedClosed,
      prefixAlgebraLowerGap, Matrix.vecHead, Matrix.vecTail] <;> ring)

private theorem prefixAlgebraAdaptedClosedColumn_step_three
    (β : Nat) (body : List TagLetter) :
    prefixAlgebraGenerator β body true *ᵥ
        prefixAlgebraAdaptedClosedColumn β body 3 =
      prefixAlgebraAdaptedClosedColumn β body 4 := by
  rw [prefixAlgebraGenerator_eq_closed,
    prefixAlgebraGeneratorClosed_true_mulVec]
  ext row
  fin_cases row <;>
    (simp [prefixAlgebraAdaptedClosedColumn, prefixAlgebraAdaptedClosed,
      prefixAlgebraLowerGap, Matrix.vecHead, Matrix.vecTail] <;> ring)

private theorem prefixAlgebraAdaptedClosedColumn_step_four
    (β : Nat) (body : List TagLetter) :
    prefixAlgebraGenerator β body true *ᵥ
        prefixAlgebraAdaptedClosedColumn β body 4 =
      prefixAlgebraAdaptedClosedColumn β body 5 := by
  rw [prefixAlgebraGenerator_eq_closed,
    prefixAlgebraGeneratorClosed_true_mulVec]
  ext row
  fin_cases row <;>
    (simp [prefixAlgebraAdaptedClosedColumn, prefixAlgebraAdaptedClosed,
      prefixAlgebraLowerGap, Matrix.vecHead, Matrix.vecTail] <;> ring)

private theorem prefixAlgebraAdaptedClosedColumn_cut_c
    (β : Nat) (body : List TagLetter) :
    prefixAlgebraGenerator β body true *ᵥ
          prefixAlgebraAdaptedClosedColumn β body 5 -
        9 * (3 : ℚ) ^ β • prefixAlgebraAdaptedClosedColumn β body 3 =
      prefixAlgebraAdaptedClosedColumn β body 6 := by
  rw [prefixAlgebraGenerator_eq_closed,
    prefixAlgebraGeneratorClosed_true_mulVec]
  ext row
  fin_cases row <;>
    (simp [prefixAlgebraAdaptedClosedColumn, prefixAlgebraAdaptedClosed,
      prefixAlgebraLowerGap, Matrix.vecHead, Matrix.vecTail] <;> ring)

private theorem prefixAlgebraAdaptedClosedColumn_step_six
    (β : Nat) (body : List TagLetter) :
    prefixAlgebraGenerator β body true *ᵥ
        prefixAlgebraAdaptedClosedColumn β body 6 =
      prefixAlgebraAdaptedClosedColumn β body 7 := by
  rw [prefixAlgebraGenerator_eq_closed,
    prefixAlgebraGeneratorClosed_true_mulVec]
  ext row
  fin_cases row <;>
    (simp [prefixAlgebraAdaptedClosedColumn, prefixAlgebraAdaptedClosed,
      prefixAlgebraLowerGap, Matrix.vecHead, Matrix.vecTail] <;> ring)

private theorem prefixAlgebraAdaptedClosedColumn_step_seven
    (β : Nat) (body : List TagLetter) :
    prefixAlgebraGenerator β body true *ᵥ
        prefixAlgebraAdaptedClosedColumn β body 7 =
      prefixAlgebraAdaptedClosedColumn β body 8 := by
  rw [prefixAlgebraGenerator_eq_closed,
    prefixAlgebraGeneratorClosed_true_mulVec]
  ext row
  fin_cases row <;>
    (simp [prefixAlgebraAdaptedClosedColumn, prefixAlgebraAdaptedClosed,
      prefixAlgebraLowerGap, Matrix.vecHead, Matrix.vecTail] <;> ring)

private theorem prefixAlgebraAdaptedClosedColumn_cut_b
    (β : Nat) (body : List TagLetter) :
    prefixAlgebraGenerator β body true *ᵥ
          prefixAlgebraAdaptedClosedColumn β body 8 -
        3 • prefixAlgebraAdaptedClosedColumn β body 6 =
      prefixAlgebraAdaptedClosedColumn β body 9 := by
  rw [prefixAlgebraGenerator_eq_closed,
    prefixAlgebraGeneratorClosed_true_mulVec]
  ext row
  fin_cases row <;>
    (simp [prefixAlgebraAdaptedClosedColumn, prefixAlgebraAdaptedClosed,
      prefixAlgebraLowerGap, Matrix.vecHead, Matrix.vecTail] <;> ring)

private theorem prefixAlgebraSeedA_eq_closed
    (β : Nat) (body : List TagLetter) :
    prefixAlgebraSeedA β body =
      prefixAlgebraAdaptedClosedColumn β body 3 := by
  rw [prefixAlgebraSeedA, prefixAlgebraAdaptedClosedColumn_zero,
    prefixAlgebraAdaptedClosedColumn_step_zero,
    prefixAlgebraAdaptedClosedColumn_step_one,
    prefixAlgebraAdaptedClosedColumn_cut_a]

private theorem prefixAlgebraSeedC_eq_closed
    (β : Nat) (body : List TagLetter) :
    prefixAlgebraSeedC β body =
      prefixAlgebraAdaptedClosedColumn β body 6 := by
  rw [prefixAlgebraSeedC, prefixAlgebraSeedA_eq_closed,
    prefixAlgebraAdaptedClosedColumn_step_three,
    prefixAlgebraAdaptedClosedColumn_step_four,
    prefixAlgebraAdaptedClosedColumn_cut_c]

private theorem prefixAlgebraSeedB_eq_closed
    (β : Nat) (body : List TagLetter) :
    prefixAlgebraSeedB β body =
      prefixAlgebraAdaptedClosedColumn β body 9 := by
  rw [prefixAlgebraSeedB, prefixAlgebraSeedC_eq_closed,
    prefixAlgebraAdaptedClosedColumn_step_six,
    prefixAlgebraAdaptedClosedColumn_step_seven,
    prefixAlgebraAdaptedClosedColumn_cut_b]

private theorem prefixAlgebraObservableClosedRow_zero (β : Nat) :
    prefixAlgebraRow β = prefixAlgebraObservableClosedRow β 0 := by
  ext column
  fin_cases column <;>
    simp [prefixAlgebraRow, prefixAlgebraObservableClosedRow,
      prefixAlgebraObservableClosed]

private theorem prefixAlgebraObservableClosedRow_step_zero (β : Nat)
    (body : List TagLetter) :
    prefixAlgebraObservableClosedRow β 0 ᵥ*
        prefixAlgebraGenerator β body true =
      prefixAlgebraObservableClosedRow β 1 := by
  rw [prefixAlgebraGenerator_eq_closed,
    prefixAlgebraGeneratorClosed_vecMul_true]
  ext column
  fin_cases column <;>
    simp [prefixAlgebraObservableClosedRow, prefixAlgebraObservableClosed,
      Matrix.vecHead, Matrix.vecTail]

private theorem prefixAlgebraObservableClosedRow_step_one_zero (β : Nat)
    (body : List TagLetter) :
    prefixAlgebraObservableClosedRow β 1 ᵥ*
        prefixAlgebraGenerator β body false =
      prefixAlgebraObservableClosedRow β 2 := by
  rw [prefixAlgebraGenerator_eq_closed,
    prefixAlgebraGeneratorClosed_vecMul_false]
  ext column
  fin_cases column <;>
    simp [prefixAlgebraObservableClosedRow, prefixAlgebraObservableClosed,
      Matrix.vecHead, Matrix.vecTail]

private theorem prefixAlgebraObservableClosedRow_step_one_one (β : Nat)
    (body : List TagLetter) :
    prefixAlgebraObservableClosedRow β 1 ᵥ*
        prefixAlgebraGenerator β body true =
      prefixAlgebraObservableClosedRow β 3 := by
  rw [prefixAlgebraGenerator_eq_closed,
    prefixAlgebraGeneratorClosed_vecMul_true]
  ext column
  fin_cases column <;>
    simp [prefixAlgebraObservableClosedRow, prefixAlgebraObservableClosed,
      Matrix.vecHead, Matrix.vecTail]

private theorem prefixAlgebraObservableClosedRow_step_two (β : Nat)
    (body : List TagLetter) :
    prefixAlgebraObservableClosedRow β 2 ᵥ*
        prefixAlgebraGenerator β body true =
      prefixAlgebraObservableClosedRow β 4 := by
  rw [prefixAlgebraGenerator_eq_closed,
    prefixAlgebraGeneratorClosed_vecMul_true]
  ext column
  fin_cases column <;>
    (simp [prefixAlgebraObservableClosedRow, prefixAlgebraObservableClosed,
      Matrix.vecHead, Matrix.vecTail] <;> ring)

private theorem prefixAlgebraObservableClosedRow_step_three (β : Nat)
    (body : List TagLetter) :
    prefixAlgebraObservableClosedRow β 3 ᵥ*
        prefixAlgebraGenerator β body false =
      prefixAlgebraObservableClosedRow β 5 := by
  rw [prefixAlgebraGenerator_eq_closed,
    prefixAlgebraGeneratorClosed_vecMul_false]
  ext column
  fin_cases column <;>
    (simp [prefixAlgebraObservableClosedRow, prefixAlgebraObservableClosed,
      Matrix.vecHead, Matrix.vecTail] <;> ring)

private theorem prefixAlgebraObservableClosedRow_step_four (β : Nat)
    (body : List TagLetter) :
    prefixAlgebraObservableClosedRow β 4 ᵥ*
        prefixAlgebraGenerator β body true =
      prefixAlgebraObservableClosedRow β 6 := by
  rw [prefixAlgebraGenerator_eq_closed,
    prefixAlgebraGeneratorClosed_vecMul_true]
  ext column
  fin_cases column <;>
    simp [prefixAlgebraObservableClosedRow, prefixAlgebraObservableClosed,
      Matrix.vecHead, Matrix.vecTail]

private theorem prefixAlgebraObservableClosedRow_step_five (β : Nat)
    (body : List TagLetter) :
    prefixAlgebraObservableClosedRow β 5 ᵥ*
        prefixAlgebraGenerator β body true =
      prefixAlgebraObservableClosedRow β 7 := by
  rw [prefixAlgebraGenerator_eq_closed,
    prefixAlgebraGeneratorClosed_vecMul_true]
  ext column
  fin_cases column <;>
    simp [prefixAlgebraObservableClosedRow, prefixAlgebraObservableClosed,
      Matrix.vecHead, Matrix.vecTail]

private theorem prefixAlgebraObservableClosedRow_step_six (β : Nat)
    (body : List TagLetter) :
    prefixAlgebraObservableClosedRow β 6 ᵥ*
        prefixAlgebraGenerator β body false =
      prefixAlgebraObservableClosedRow β 8 := by
  rw [prefixAlgebraGenerator_eq_closed,
    prefixAlgebraGeneratorClosed_vecMul_false]
  ext column
  fin_cases column <;>
    simp [prefixAlgebraObservableClosedRow, prefixAlgebraObservableClosed,
      Matrix.vecHead, Matrix.vecTail]

private theorem prefixAlgebraObservableClosedRow_step_seven (β : Nat)
    (body : List TagLetter) :
    prefixAlgebraObservableClosedRow β 7 ᵥ*
        prefixAlgebraGenerator β body false =
      prefixAlgebraObservableClosedRow β 9 := by
  rw [prefixAlgebraGenerator_eq_closed,
    prefixAlgebraGeneratorClosed_vecMul_false]
  ext column
  fin_cases column <;>
    simp [prefixAlgebraObservableClosedRow, prefixAlgebraObservableClosed,
      Matrix.vecHead, Matrix.vecTail]

theorem prefixAlgebraReachable_mul_change (β : Nat) (body : List TagLetter) :
    prefixAlgebraReachable β body * prefixAlgebraReachabilityChange β =
      prefixAlgebraAdapted β body := by
  ext row column
  fin_cases column <;>
    simp [prefixAlgebraReachable, prefixAlgebraReachabilityChange,
      prefixAlgebraAdapted, prefixAlgebraSeedA, prefixAlgebraSeedB,
      prefixAlgebraSeedC, contextColumns, prefixAlgebraLeftWords,
      wordProduct, Matrix.mul_apply, Matrix.mulVec_sub, Matrix.mulVec_smul,
      mulVec_const_mul, mulVec_mul_const, mulVec_nine_mul,
      Fin.sum_univ_succ] <;>
    (repeat' rw [← Matrix.mulVec_mulVec]
     ring)

theorem prefixAlgebraAdapted_eq_closed (β : Nat) (body : List TagLetter) :
    prefixAlgebraAdapted β body =
      prefixAlgebraAdaptedClosed β body := by
  ext row column
  fin_cases column
  · change prefixAlgebraColumn β body row =
      prefixAlgebraAdaptedClosedColumn β body 0 row
    rw [prefixAlgebraAdaptedClosedColumn_zero]
  · change
      (prefixAlgebraGenerator β body true *ᵥ
        prefixAlgebraColumn β body) row =
      prefixAlgebraAdaptedClosedColumn β body 1 row
    rw [prefixAlgebraAdaptedClosedColumn_zero,
      prefixAlgebraAdaptedClosedColumn_step_zero]
  · change
      (prefixAlgebraGenerator β body true *ᵥ
        (prefixAlgebraGenerator β body true *ᵥ
          prefixAlgebraColumn β body)) row =
      prefixAlgebraAdaptedClosedColumn β body 2 row
    rw [prefixAlgebraAdaptedClosedColumn_zero,
      prefixAlgebraAdaptedClosedColumn_step_zero,
      prefixAlgebraAdaptedClosedColumn_step_one]
  · change prefixAlgebraSeedA β body row =
      prefixAlgebraAdaptedClosedColumn β body 3 row
    rw [prefixAlgebraSeedA_eq_closed]
  · change
      (prefixAlgebraGenerator β body true *ᵥ
        prefixAlgebraSeedA β body) row =
      prefixAlgebraAdaptedClosedColumn β body 4 row
    rw [prefixAlgebraSeedA_eq_closed,
      prefixAlgebraAdaptedClosedColumn_step_three]
  · change
      (prefixAlgebraGenerator β body true *ᵥ
        (prefixAlgebraGenerator β body true *ᵥ
          prefixAlgebraSeedA β body)) row =
      prefixAlgebraAdaptedClosedColumn β body 5 row
    rw [prefixAlgebraSeedA_eq_closed,
      prefixAlgebraAdaptedClosedColumn_step_three,
      prefixAlgebraAdaptedClosedColumn_step_four]
  · change prefixAlgebraSeedC β body row =
      prefixAlgebraAdaptedClosedColumn β body 6 row
    rw [prefixAlgebraSeedC_eq_closed]
  · change
      (prefixAlgebraGenerator β body true *ᵥ
        prefixAlgebraSeedC β body) row =
      prefixAlgebraAdaptedClosedColumn β body 7 row
    rw [prefixAlgebraSeedC_eq_closed,
      prefixAlgebraAdaptedClosedColumn_step_six]
  · change
      (prefixAlgebraGenerator β body true *ᵥ
        (prefixAlgebraGenerator β body true *ᵥ
          prefixAlgebraSeedC β body)) row =
      prefixAlgebraAdaptedClosedColumn β body 8 row
    rw [prefixAlgebraSeedC_eq_closed,
      prefixAlgebraAdaptedClosedColumn_step_six,
      prefixAlgebraAdaptedClosedColumn_step_seven]
  · change prefixAlgebraSeedB β body row =
      prefixAlgebraAdaptedClosedColumn β body 9 row
    rw [prefixAlgebraSeedB_eq_closed]

theorem prefixAlgebraObservable_eq_closed (β : Nat) (body : List TagLetter) :
    prefixAlgebraObservable β body =
      prefixAlgebraObservableClosed β := by
  rw [prefixAlgebraObservable, prefixAlgebraObservableClosed]
  ext row column
  fin_cases row <;>
    simp [contextRows, prefixAlgebraRightWords]
  · rw [prefixAlgebraObservableClosedRow_zero]
  · rw [prefixAlgebraObservableClosedRow_zero,
      prefixAlgebraObservableClosedRow_step_zero]
  · rw [← Matrix.vecMul_vecMul, prefixAlgebraObservableClosedRow_zero,
      prefixAlgebraObservableClosedRow_step_zero,
      prefixAlgebraObservableClosedRow_step_one_zero]
  · rw [← Matrix.vecMul_vecMul, prefixAlgebraObservableClosedRow_zero,
      prefixAlgebraObservableClosedRow_step_zero,
      prefixAlgebraObservableClosedRow_step_one_one]
  · rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul,
      prefixAlgebraObservableClosedRow_zero,
      prefixAlgebraObservableClosedRow_step_zero,
      prefixAlgebraObservableClosedRow_step_one_zero,
      prefixAlgebraObservableClosedRow_step_two]
  · rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul,
      prefixAlgebraObservableClosedRow_zero,
      prefixAlgebraObservableClosedRow_step_zero,
      prefixAlgebraObservableClosedRow_step_one_one,
      prefixAlgebraObservableClosedRow_step_three]
  · rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul,
      ← Matrix.vecMul_vecMul, prefixAlgebraObservableClosedRow_zero,
      prefixAlgebraObservableClosedRow_step_zero,
      prefixAlgebraObservableClosedRow_step_one_zero,
      prefixAlgebraObservableClosedRow_step_two,
      prefixAlgebraObservableClosedRow_step_four]
  · rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul,
      ← Matrix.vecMul_vecMul, prefixAlgebraObservableClosedRow_zero,
      prefixAlgebraObservableClosedRow_step_zero,
      prefixAlgebraObservableClosedRow_step_one_one,
      prefixAlgebraObservableClosedRow_step_three,
      prefixAlgebraObservableClosedRow_step_five]
  · rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul,
      ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul,
      prefixAlgebraObservableClosedRow_zero,
      prefixAlgebraObservableClosedRow_step_zero,
      prefixAlgebraObservableClosedRow_step_one_zero,
      prefixAlgebraObservableClosedRow_step_two,
      prefixAlgebraObservableClosedRow_step_four,
      prefixAlgebraObservableClosedRow_step_six]
  · rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul,
      ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul,
      prefixAlgebraObservableClosedRow_zero,
      prefixAlgebraObservableClosedRow_step_zero,
      prefixAlgebraObservableClosedRow_step_one_one,
      prefixAlgebraObservableClosedRow_step_three,
      prefixAlgebraObservableClosedRow_step_five,
      prefixAlgebraObservableClosedRow_step_seven]

end MatrixMortality
