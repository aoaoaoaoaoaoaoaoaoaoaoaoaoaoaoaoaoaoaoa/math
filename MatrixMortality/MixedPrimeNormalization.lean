import MatrixMortality.MatrixSemigroup
import MatrixMortality.MixedPrimeKernel

/-!
# Normalized mixed-prime kernel

The mixed-prime affine kernel is not an artefact of projective representatives. Its odd family
has equal letter content, so every relation remains an exact homogeneous-matrix equality after
independent scaling of the two generators. The first two members also force the whole family in
every group-valued interpretation by cancellation; this finite pump preserves length and gives
no bounded reachability normal form.
-/

namespace MatrixMortality.MixedPrimeNormalization

open MixedPrimeKernel
open scoped Matrix

/-- An exact matrix relation between words with the same letter multiset survives independent
scaling of every generator. -/
theorem wordProduct_smulMatrix_eq_of_perm
    {α ι K : Type*} [CommSemiring K] [Fintype ι] [DecidableEq ι]
    (scales : α → K) (generators : α → Square ι K)
    {left right : List α} (permutation : left.Perm right)
    (relation : wordProduct generators left = wordProduct generators right) :
    wordProduct (fun label => scales label • generators label) left =
      wordProduct (fun label => scales label • generators label) right := by
  rw [wordProduct_smulMatrix, wordProduct_smulMatrix, relation]
  exact congrArg (· • wordProduct generators right)
    (permutation.map scales).prod_eq

/-- Two consecutive instances force an entire conjugacy pump in any group. The conclusion has
no shortening content: every member retains the same exponent `power` on both sides. -/
theorem groupPump_eq_of_zero_one
    {G : Type*} [Group G] (left right bridge pump tail : G)
    (zero : left * bridge = right * bridge * tail)
    (one : left * pump * bridge = right * pump * bridge * tail)
    (power : ℕ) :
    left * pump ^ power * bridge =
      right * pump ^ power * bridge * tail := by
  let conjugate := bridge * tail * bridge⁻¹
  have left_eq : left = right * conjugate := by
    dsimp [conjugate]
    calc
      left = left * bridge * bridge⁻¹ := by group
      _ = right * bridge * tail * bridge⁻¹ := by rw [zero]
      _ = right * (bridge * tail * bridge⁻¹) := by group
  have commutes : Commute conjugate pump := by
    rw [Commute]
    calc
      conjugate * pump = right⁻¹ * (left * pump * bridge) * bridge⁻¹ := by
        rw [left_eq]
        dsimp [conjugate]
        group
      _ = right⁻¹ * (right * pump * bridge * tail) * bridge⁻¹ := by
        rw [one]
      _ = pump * conjugate := by
        dsimp [conjugate]
        group
  rw [left_eq]
  calc
    right * conjugate * pump ^ power * bridge =
        right * (conjugate * pump ^ power) * bridge := by group
    _ = right * (pump ^ power * conjugate) * bridge := by
      rw [(commutes.pow_right power).eq]
    _ = right * pump ^ power * conjugate * bridge := by group
    _ = right * pump ^ power * bridge * tail := by
      dsimp [conjugate]
      group

@[simp]
private theorem pumpWord_count_dilate (pump : ℕ) :
    (pumpWord pump).count .dilate = pump := by
  induction pump with
  | zero => rfl
  | succ pump induction => simp [pumpWord, induction]

@[simp]
private theorem pumpWord_count_translate (pump : ℕ) :
    (pumpWord pump).count .translate = pump := by
  induction pump with
  | zero => rfl
  | succ pump induction => simp [pumpWord, induction]

/-- Exact Parikh vector of both words in the odd family. -/
theorem kernelOddFamily_count (pump : ℕ) :
    (kernelOddFamilyLeft pump).count .dilate = 16 + pump ∧
      (kernelOddFamilyLeft pump).count .translate = 13 + pump ∧
      (kernelOddFamilyRight pump).count .dilate = 16 + pump ∧
      (kernelOddFamilyRight pump).count .translate = 13 + pump := by
  simp [kernelOddFamilyLeft, kernelOddFamilyRight]
  omega

/-- The two sides of every odd-family relation have the same letter multiset. In particular,
the relation is invisible to abelianization and survives independent generator scaling. -/
theorem kernelOddFamily_perm (pump : ℕ) :
    (kernelOddFamilyLeft pump).Perm (kernelOddFamilyRight pump) := by
  rw [List.perm_iff_count]
  intro letter
  have counts := kernelOddFamily_count pump
  cases letter
  · exact counts.1.trans counts.2.2.1.symm
  · exact counts.2.1.trans counts.2.2.2.symm

/-- Normalized homogeneous matrices realizing the mixed-prime affine action on `[z,1]`. -/
def affineGenerator : Letter → Square (Fin 2) ℚ
  | .dilate => !![2 / 3, 0; 0, 1]
  | .translate => !![3 / 5, 1; 0, 1]

/-- Both normalized affine generators are invertible. -/
theorem affineGenerator_isUnit (letter : Letter) : IsUnit (affineGenerator letter) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  cases letter <;>
    norm_num [affineGenerator, Matrix.det_fin_two]

/-- Nonzero independent scaling keeps both normalized affine generators invertible. -/
theorem scaledAffineGenerator_isUnit
    (scales : Letter → ℚ) (scale_ne : ∀ letter, scales letter ≠ 0)
    (letter : Letter) :
    IsUnit (scales letter • affineGenerator letter) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_smul, isUnit_iff_ne_zero]
  exact mul_ne_zero (pow_ne_zero _ (scale_ne letter))
    ((Matrix.isUnit_iff_isUnit_det (affineGenerator letter)).mp
      (affineGenerator_isUnit letter)).ne_zero

private theorem affineGenerator_mulVec (letter : Letter) (state : ℚ) :
    affineGenerator letter *ᵥ ![state, 1] = ![action letter state, 1] := by
  cases letter <;>
    ext i <;>
    fin_cases i <;>
    norm_num [affineGenerator, action, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Homogeneous matrix multiplication and the raw affine action agree on the affine chart. -/
theorem wordProduct_affineGenerator_mulVec (word : List Letter) (state : ℚ) :
    wordProduct affineGenerator word *ᵥ ![state, 1] =
      ![wordAction word state, 1] := by
  induction word with
  | nil => simp [wordAction]
  | cons letter word induction =>
      rw [wordProduct_cons, ← Matrix.mulVec_mulVec, induction,
        affineGenerator_mulVec]
      rfl

private theorem matrix_eq_of_affineChart_eq
    {left right : Square (Fin 2) ℚ}
    (agreement : ∀ state : ℚ, left *ᵥ ![state, 1] = right *ᵥ ![state, 1]) :
    left = right := by
  ext i j
  fin_cases j
  · have at_zero := congrFun (agreement 0) i
    have at_one := congrFun (agreement 1) i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at at_zero at_one
    change left i 0 = right i 0
    linarith
  · have at_zero := congrFun (agreement 0) i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using at_zero

/-- Every odd-family affine collision is an exact relation between its normalized homogeneous
matrix products, rather than equality only after projectivization. -/
theorem wordProduct_affineGenerator_kernelOddFamily (pump : ℕ) :
    wordProduct affineGenerator (kernelOddFamilyLeft pump) =
      wordProduct affineGenerator (kernelOddFamilyRight pump) := by
  apply matrix_eq_of_affineChart_eq
  intro state
  rw [wordProduct_affineGenerator_mulVec, wordProduct_affineGenerator_mulVec,
    wordAction_kernelOddFamily]

/-- Every independent rescaling of the two affine generators retains the exact odd-family
matrix relation. This includes the nonzero rescalings used by unit normalization. -/
theorem wordProduct_scaledAffineGenerator_kernelOddFamily
    (scales : Letter → ℚ) (pump : ℕ) :
    wordProduct (fun letter => scales letter • affineGenerator letter)
        (kernelOddFamilyLeft pump) =
      wordProduct (fun letter => scales letter • affineGenerator letter)
        (kernelOddFamilyRight pump) :=
  wordProduct_smulMatrix_eq_of_perm scales affineGenerator
    (kernelOddFamily_perm pump)
    (wordProduct_affineGenerator_kernelOddFamily pump)

/-- Independent generator scaling cannot restore freeness to the mixed-prime affine pair. -/
theorem scaledAffineGenerator_not_injective (scales : Letter → ℚ) :
    ¬Function.Injective
      (wordProduct (fun letter => scales letter • affineGenerator letter)) := by
  intro injective
  exact kernelOddFamily_ne 0
    (injective (wordProduct_scaledAffineGenerator_kernelOddFamily scales 0))

/-- A group-valued interpretation sends the repeated raw `D T` pump to the corresponding
element power. -/
theorem wordProduct_pumpWord
    {G : Type*} [Monoid G] (generators : Letter → G) (power : ℕ) :
    wordProduct generators (pumpWord power) =
      (generators .dilate * generators .translate) ^ power := by
  induction power with
  | zero => simp [pumpWord]
  | succ power induction =>
      simp [pumpWord, induction, pow_succ', mul_assoc]

private def oddLeftHead : List Letter :=
  [.dilate] ++ List.replicate 10 .translate ++ List.replicate 2 .dilate ++
    [.translate] ++ List.replicate 2 .dilate ++ [.translate] ++
    List.replicate 9 .dilate ++ [.translate]

private def oddRightHead : List Letter :=
  List.replicate 2 .translate ++ List.replicate 6 .dilate ++
    List.replicate 2 .translate ++ List.replicate 2 .dilate ++
    [.translate, .dilate, .translate, .dilate, .translate] ++
    List.replicate 2 .dilate ++ List.replicate 2 .translate ++
    List.replicate 2 .dilate ++ List.replicate 2 .translate

private def oddBridge : List Letter :=
  List.replicate 2 .dilate

private def oddTail : List Letter :=
  List.replicate 2 .translate

private theorem wordProduct_kernelOddFamilyLeft
    {G : Type*} [Monoid G] (generators : Letter → G) (power : ℕ) :
    wordProduct generators (kernelOddFamilyLeft power) =
      wordProduct generators oddLeftHead *
        (generators .dilate * generators .translate) ^ power *
          wordProduct generators oddBridge := by
  simp [kernelOddFamilyLeft, oddLeftHead, oddBridge, wordProduct_append,
    wordProduct_pumpWord, mul_assoc]

private theorem wordProduct_kernelOddFamilyRight
    {G : Type*} [Monoid G] (generators : Letter → G) (power : ℕ) :
    wordProduct generators (kernelOddFamilyRight power) =
      wordProduct generators oddRightHead *
        (generators .dilate * generators .translate) ^ power *
          wordProduct generators oddBridge * wordProduct generators oddTail := by
  simp [kernelOddFamilyRight, oddRightHead, oddBridge, oddTail, wordProduct_append,
    wordProduct_pumpWord, mul_assoc]

/-- In every group-valued interpretation, the first two odd-family equalities force every later
member. Cancellation turns the base equality into one conjugate and the next equality into its
commutation with `D T`; no infinite independent group relation remains. -/
theorem wordProduct_kernelOddFamily_of_zero_one
    {G : Type*} [Group G] (generators : Letter → G)
    (zero :
      wordProduct generators (kernelOddFamilyLeft 0) =
        wordProduct generators (kernelOddFamilyRight 0))
    (one :
      wordProduct generators (kernelOddFamilyLeft 1) =
        wordProduct generators (kernelOddFamilyRight 1))
    (power : ℕ) :
    wordProduct generators (kernelOddFamilyLeft power) =
      wordProduct generators (kernelOddFamilyRight power) := by
  rw [wordProduct_kernelOddFamilyLeft, wordProduct_kernelOddFamilyRight]
  apply groupPump_eq_of_zero_one
  · simpa [wordProduct_kernelOddFamilyLeft, wordProduct_kernelOddFamilyRight] using zero
  · simpa [wordProduct_kernelOddFamilyLeft, wordProduct_kernelOddFamilyRight] using one

end MatrixMortality.MixedPrimeNormalization
