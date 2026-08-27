import MatrixMortality.MatrixSemigroup
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Affine matrix pencils

The constant and highest possible coefficients of a word over affine matrix pencils are the
corresponding products of the constant and slope matrices. This is the coefficient support
needed by rational-root arguments for parameterized return families.
-/

namespace MatrixMortality

open scoped Matrix Polynomial

namespace PolynomialPencil

noncomputable section

/-- Entrywise affine pencil `constant + X · slope`. -/
def affine {ι R : Type*} [CommSemiring R]
    (constant slope : Square ι R) : Square ι R[X] :=
  fun i j => Polynomial.C (constant i j) + Polynomial.X * Polynomial.C (slope i j)

@[simp]
theorem affine_coeff_zero {ι R : Type*} [CommSemiring R]
    (constant slope : Square ι R) (i j : ι) :
    (affine constant slope i j).coeff 0 = constant i j := by
  simp [affine]

@[simp]
theorem affine_coeff_one {ι R : Type*} [CommSemiring R]
    (constant slope : Square ι R) (i j : ι) :
    (affine constant slope i j).coeff 1 = slope i j := by
  simp [affine]

theorem affine_natDegree_le_one {ι R : Type*} [CommSemiring R]
    (constant slope : Square ι R) (i j : ι) :
    (affine constant slope i j).natDegree ≤ 1 := by
  rw [affine]
  refine (Polynomial.natDegree_add_le _ _).trans ?_
  rw [max_le_iff]
  constructor
  · simp
  · rw [Polynomial.X_mul]
    simpa using Polynomial.natDegree_C_mul_X_pow_le (slope i j) 1

/-- Word product of a family of affine pencils. -/
def product {α ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]
    (constant slope : α → Square ι R) (word : List α) : Square ι R[X] :=
  wordProduct (fun label => affine (constant label) (slope label)) word

@[simp]
theorem product_nil
    {α ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]
    (constant slope : α → Square ι R) :
    product constant slope [] = 1 :=
  by simp [product]

@[simp]
theorem product_cons
    {α ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]
    (constant slope : α → Square ι R) (label : α) (tail : List α) :
    product constant slope (label :: tail) =
      affine (constant label) (slope label) * product constant slope tail :=
  by simp [product, wordProduct]

/-- Every entry of an affine-pencil word has degree at most the word length. -/
theorem product_natDegree_le_length
    {α ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]
    (constant slope : α → Square ι R) (word : List α) (i j : ι) :
    (product constant slope word i j).natDegree ≤ word.length := by
  induction word generalizing i j with
  | nil =>
      simp only [product_nil, List.length_nil, le_zero_iff]
      rw [Matrix.one_apply]
      split_ifs <;> simp
  | cons label tail induction =>
      rw [product_cons, Matrix.mul_apply]
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro k _
      simpa [Nat.add_comm] using
        Polynomial.natDegree_mul_le_of_le (m := 1) (n := tail.length)
          (affine_natDegree_le_one (constant label) (slope label) i k)
          (induction k j)

/-- The constant coefficient of an affine-pencil word is the word product of its constants. -/
theorem product_coeff_zero
    {α ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]
    (constant slope : α → Square ι R) (word : List α) :
    (fun i j => (product constant slope word i j).coeff 0) =
      wordProduct constant word := by
  induction word with
  | nil =>
      ext i j
      rw [product_nil, wordProduct]
      by_cases indices : i = j <;> simp [Matrix.one_apply, indices]
  | cons label tail induction =>
      ext i j
      rw [product_cons, Matrix.mul_apply,
        Polynomial.finsetSum_coeff, wordProduct_cons, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro k _
      rw [Polynomial.coeff_mul]
      simp
      rw [congrFun (congrFun induction k) j]

/-- The coefficient at the maximal possible degree is the word product of the slope matrices. -/
theorem product_coeff_length
    {α ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]
    (constant slope : α → Square ι R) (word : List α) :
    (fun i j => (product constant slope word i j).coeff word.length) =
      wordProduct slope word := by
  induction word with
  | nil =>
      ext i j
      rw [product_nil, wordProduct]
      by_cases indices : i = j <;> simp [Matrix.one_apply, indices]
  | cons label tail induction =>
      ext i j
      rw [product_cons, Matrix.mul_apply,
        Polynomial.finsetSum_coeff, wordProduct_cons, Matrix.mul_apply]
      simp only [List.length_cons]
      apply Finset.sum_congr rfl
      intro k _
      rw [show tail.length + 1 = 1 + tail.length by omega]
      rw [Polynomial.coeff_mul_add_eq_of_natDegree_le
        (affine_natDegree_le_one (constant label) (slope label) i k)
        (product_natDegree_le_length constant slope tail k j)]
      rw [affine_coeff_one]
      congr 1
      exact congrFun (congrFun induction k) j

/-- Evaluation after a coefficient homomorphism evaluates each affine-pencil letter before
multiplication. -/
theorem eval₂_product
    {α ι R S : Type*} [Fintype ι] [DecidableEq ι]
    [CommSemiring R] [CommSemiring S]
    (map : R →+* S) (constant slope : α → Square ι R) (word : List α) (x : S) :
    (product constant slope word).map (Polynomial.eval₂RingHom map x) =
      wordProduct
        (fun label => (constant label).map map + x • (slope label).map map)
        word := by
  induction word with
  | nil =>
      ext i j
      rw [product_nil, wordProduct]
      by_cases indices : i = j <;> simp [indices]
  | cons label tail induction =>
      rw [product_cons, Matrix.map_mul, induction, wordProduct_cons]
      congr 1
      ext i j
      change Polynomial.eval₂ map x
          (Polynomial.C (constant label i j) +
            Polynomial.X * Polynomial.C (slope label i j)) =
        map (constant label i j) + x * map (slope label i j)
      simp
      rw [mul_comm]

/-- Evaluating an affine-pencil word evaluates each letter before multiplication. -/
theorem eval_product
    {α ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]
    (constant slope : α → Square ι R) (word : List α) (x : R) :
    (product constant slope word).map (Polynomial.evalRingHom x) =
      wordProduct (fun label => constant label + x • slope label) word := by
  change (product constant slope word).map
      (Polynomial.eval₂RingHom (RingHom.id R) x) =
    wordProduct (fun label => constant label + x • slope label) word
  simpa using eval₂_product (RingHom.id R) constant slope word x

end
end PolynomialPencil

end MatrixMortality
