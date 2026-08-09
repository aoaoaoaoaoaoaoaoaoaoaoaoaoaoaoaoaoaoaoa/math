import MatrixMortality.ParabolicSafeFlag

/-!
# Arbitrary residue-two defect grammar

The modulo-three protected plane admits a complete run calculus.  Safe residues are rank-one
outer products; the residue-two action has fourth power minus the identity.  Consequently an
arbitrary safe/defect skeleton vanishes exactly at one local run incidence.  The same file
records the source-independent rank-one bridge factorization consumed by the rational grammar.
-/

namespace MatrixMortality.ParabolicBlade

open scoped Matrix

/-! ## Complete protected-plane skeleton -/

/-- Protected-plane column selected by a safe residue. -/
def skeletonColumn : Bool → Fin 2 → ZMod 3
  | false => ![1, 0]
  | true => ![0, 1]

/-- Protected-plane row selected by a safe residue. -/
def skeletonRow : Bool → Fin 2 → ZMod 3
  | false => ![1, 2]
  | true => ![2, 2]

/-- Rank-one protected-plane action of one safe residue. -/
def skeletonSafe : Bool → Matrix (Fin 2) (Fin 2) (ZMod 3)
  | false => !![1, 2; 0, 0]
  | true => !![0, 0; 2, 2]

/-- Uniform protected-plane action of one residue-two defect. -/
def skeletonDefect : Matrix (Fin 2) (Fin 2) (ZMod 3) :=
  !![1, 1; 2, 1]

theorem skeletonSafe_eq_outer (residue : Bool) :
    skeletonSafe residue =
      Matrix.vecMulVec (skeletonColumn residue) (skeletonRow residue) := by
  cases residue <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [skeletonSafe, skeletonColumn, skeletonRow, Matrix.vecMulVec_apply]

theorem skeletonColumn_ne_zero (residue : Bool) : skeletonColumn residue ≠ 0 := by
  cases residue
  · intro zero
    have entry := congr_fun zero 0
    norm_num [skeletonColumn] at entry
  · intro zero
    have entry := congr_fun zero 1
    norm_num [skeletonColumn] at entry

theorem skeletonRow_ne_zero (residue : Bool) : skeletonRow residue ≠ 0 := by
  cases residue
  · intro zero
    have entry := congr_fun zero 0
    norm_num [skeletonRow] at entry
  · intro zero
    have entry := congr_fun zero 0
    norm_num [skeletonRow] at entry
    exact (show (2 : ZMod 3) ≠ 0 by decide) entry

/-- Four consecutive defects act as the nonzero scalar minus one. -/
theorem skeletonDefect_pow_four :
    skeletonDefect ^ 4 = (2 : ZMod 3) • (1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [skeletonDefect, pow_succ, Matrix.one_apply, Matrix.mul_apply,
      Fin.sum_univ_succ]
  all_goals decide

/-- Scalar coupling across a maximal internal run of defects. -/
def skeletonIncidence (left : Bool) (count : Nat) (right : Bool) : ZMod 3 :=
  skeletonRow left ⬝ᵥ (skeletonDefect ^ count *ᵥ skeletonColumn right)

theorem skeletonIncidence_add_four (left right : Bool) (count : Nat) :
    skeletonIncidence left (count + 4) right =
      2 * skeletonIncidence left count right := by
  rw [skeletonIncidence, pow_add, skeletonDefect_pow_four]
  simp [skeletonIncidence, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mulVec_assoc, Matrix.dotProduct, Matrix.mulVec,
    Finset.mul_sum]
  ring

/-- Exact four-periodic zero table for one maximal defect run. -/
theorem skeletonIncidence_eq_zero_iff (left right : Bool) (count : Nat) :
    skeletonIncidence left count right = 0 ↔
      (count % 4 = 1 ∧ left ≠ right) ∨
        (count % 4 = 3 ∧ left = right) := by
  induction count using Nat.strong_induction_on with
  | h count induction =>
      by_cases small : count < 4
      · interval_cases count <;> cases left <;> cases right <;>
          norm_num [skeletonIncidence, skeletonDefect, skeletonColumn, skeletonRow,
            pow_succ, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ] <;>
          decide
      · let prior := count - 4
        have prior_lt : prior < count := by
          dsimp [prior]
          omega
        have count_eq : count = prior + 4 := by
          dsimp [prior]
          omega
        rw [count_eq, skeletonIncidence_add_four, mul_eq_zero]
        have two_ne : (2 : ZMod 3) ≠ 0 := by decide
        simp only [two_ne, false_or, induction prior prior_lt]
        simp [Nat.add_mod]

/-- Exact rank-one factorization of a safe/defect/safe block. -/
theorem skeleton_run_factor (left right : Bool) (count : Nat) :
    skeletonSafe left * skeletonDefect ^ count * skeletonSafe right =
      skeletonIncidence left count right •
        Matrix.vecMulVec (skeletonColumn left) (skeletonRow right) := by
  rw [skeletonSafe_eq_outer, skeletonSafe_eq_outer, outer_mul, outer_mul_outer,
    skeletonIncidence, Matrix.dotProduct_mulVec]

/-- A maximal internal defect run vanishes precisely in the two four-periodic phase patterns. -/
theorem skeleton_run_eq_zero_iff (left right : Bool) (count : Nat) :
    skeletonSafe left * skeletonDefect ^ count * skeletonSafe right = 0 ↔
      (count % 4 = 1 ∧ left ≠ right) ∨
        (count % 4 = 3 ∧ left = right) := by
  rw [skeleton_run_factor, smul_eq_zero, skeletonIncidence_eq_zero_iff]
  have outer_ne :
      Matrix.vecMulVec (skeletonColumn left) (skeletonRow right) ≠ 0 :=
    outer_ne_zero (skeletonColumn_ne_zero left) (skeletonRow_ne_zero right)
  simp [outer_ne]

/-- A residue skeleton beginning in one safe phase and listing each following defect run and
safe phase. -/
def skeletonChain : Bool → List (Nat × Bool) → Matrix (Fin 2) (Fin 2) (ZMod 3)
  | first, [] => skeletonSafe first
  | first, (count, next) :: tail =>
      skeletonSafe first * skeletonDefect ^ count * skeletonChain next tail

/-- Local incidence scalars encountered by a residue skeleton. -/
def skeletonIncidences : Bool → List (Nat × Bool) → List (ZMod 3)
  | _, [] => []
  | first, (count, next) :: tail =>
      skeletonIncidence first count next :: skeletonIncidences next tail

/-- Final safe phase of a residue skeleton. -/
def skeletonLast : Bool → List (Nat × Bool) → Bool
  | first, [] => first
  | _, (_, next) :: tail => skeletonLast next tail

/-- A residue skeleton is bad when one internal run has one of the exact zero patterns. -/
def BadSkeleton : Bool → List (Nat × Bool) → Prop
  | _, [] => False
  | first, (count, next) :: tail =>
      ((count % 4 = 1 ∧ first ≠ next) ∨
        (count % 4 = 3 ∧ first = next)) ∨
      BadSkeleton next tail

/-- Every residue skeleton is one outer product times the product of its local incidences. -/
theorem skeletonChain_factor (first : Bool) (tail : List (Nat × Bool)) :
    skeletonChain first tail =
      (skeletonIncidences first tail).prod •
        Matrix.vecMulVec (skeletonColumn first)
          (skeletonRow (skeletonLast first tail)) := by
  induction tail generalizing first with
  | nil =>
      simp [skeletonChain, skeletonIncidences, skeletonLast, skeletonSafe_eq_outer]
  | cons link tail induction =>
      obtain ⟨count, next⟩ := link
      rw [skeletonChain, induction]
      rw [skeletonSafe_eq_outer, outer_mul, Matrix.mul_smul, outer_mul_outer]
      rw [skeletonIncidences, List.prod_cons, skeletonLast, skeletonIncidence,
        Matrix.dotProduct_mulVec]
      simp only [smul_smul, mul_comm]

theorem zero_mem_skeletonIncidences_iff (first : Bool) (tail : List (Nat × Bool)) :
    (0 : ZMod 3) ∈ skeletonIncidences first tail ↔ BadSkeleton first tail := by
  induction tail generalizing first with
  | nil => simp [skeletonIncidences, BadSkeleton]
  | cons link tail induction =>
      obtain ⟨count, next⟩ := link
      simp only [skeletonIncidences, List.mem_cons, BadSkeleton]
      rw [show (0 : ZMod 3) = skeletonIncidence first count next ↔
        skeletonIncidence first count next = 0 by exact eq_comm]
      rw [skeletonIncidence_eq_zero_iff, induction]

/-- Complete finite scan: no collective cancellation exists beyond one bad internal run. -/
theorem skeletonChain_eq_zero_iff (first : Bool) (tail : List (Nat × Bool)) :
    skeletonChain first tail = 0 ↔ BadSkeleton first tail := by
  rw [skeletonChain_factor, smul_eq_zero]
  have outer_ne :
      Matrix.vecMulVec (skeletonColumn first)
          (skeletonRow (skeletonLast first tail)) ≠ 0 :=
    outer_ne_zero (skeletonColumn_ne_zero first)
      (skeletonRow_ne_zero (skeletonLast first tail))
  simp only [outer_ne, or_false, List.prod_eq_zero_iff]
  exact zero_mem_skeletonIncidences_iff first tail

/-! ## Physical residue skeleton -/

/-- Embedding of the protected plane into the cleared three-dimensional residue space. -/
def skeletonLift (vector : Fin 2 → ZMod 3) : Fin 3 → ZMod 3 :=
  ![vector 0, 0, vector 1]

/-- Full cleared safe row; its restriction to the protected plane is `skeletonRow`. -/
def skeletonFullRow : Bool → Fin 3 → ZMod 3
  | false => ![1, 2, 2]
  | true => ![2, 0, 2]

theorem safeResidue_eq_outer (residue : Bool) :
    safeResidue residue =
      Matrix.vecMulVec (skeletonLift (skeletonColumn residue)) (skeletonFullRow residue) := by
  cases residue <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [safeResidue, skeletonLift, skeletonColumn, skeletonFullRow,
      Matrix.vecMulVec_apply]

private theorem residueTwoResidue_mulVec_skeletonLift (vector : Fin 2 → ZMod 3) :
    residueTwoResidue *ᵥ skeletonLift vector =
      skeletonLift (skeletonDefect *ᵥ vector) := by
  funext i
  fin_cases i <;>
    norm_num [residueTwoResidue, skeletonLift, skeletonDefect, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_succ]

private theorem residueTwoResidue_pow_mulVec_skeletonLift
    (count : Nat) (vector : Fin 2 → ZMod 3) :
    residueTwoResidue ^ count *ᵥ skeletonLift vector =
      skeletonLift (skeletonDefect ^ count *ᵥ vector) := by
  induction count with
  | zero => simp
  | succ count induction =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, induction,
        residueTwoResidue_mulVec_skeletonLift, pow_succ', Matrix.mulVec_mulVec]

private theorem skeletonFullRow_dot_skeletonLift
    (residue : Bool) (vector : Fin 2 → ZMod 3) :
    skeletonFullRow residue ⬝ᵥ skeletonLift vector = skeletonRow residue ⬝ᵥ vector := by
  cases residue <;>
    norm_num [skeletonFullRow, skeletonLift, skeletonRow, Matrix.dotProduct,
      Fin.sum_univ_succ]

private theorem skeletonFullIncidence_eq
    (left right : Bool) (count : Nat) :
    skeletonFullRow left ⬝ᵥ
        (residueTwoResidue ^ count *ᵥ skeletonLift (skeletonColumn right)) =
      skeletonIncidence left count right := by
  rw [residueTwoResidue_pow_mulVec_skeletonLift, skeletonFullRow_dot_skeletonLift,
    skeletonIncidence]

/-- Exact cleared three-dimensional product associated with a safe/defect residue skeleton. -/
def residueSkeletonChain : Bool → List (Nat × Bool) →
    Matrix (Fin 3) (Fin 3) (ZMod 3)
  | first, [] => safeResidue first
  | first, (count, next) :: tail =>
      safeResidue first * residueTwoResidue ^ count * residueSkeletonChain next tail

/-- The cleared physical residue skeleton has the same complete local-incidence factorization as
its protected-plane restriction. -/
theorem residueSkeletonChain_factor (first : Bool) (tail : List (Nat × Bool)) :
    residueSkeletonChain first tail =
      (skeletonIncidences first tail).prod •
        Matrix.vecMulVec (skeletonLift (skeletonColumn first))
          (skeletonFullRow (skeletonLast first tail)) := by
  induction tail generalizing first with
  | nil => simp [residueSkeletonChain, skeletonIncidences, skeletonLast, safeResidue_eq_outer]
  | cons link tail induction =>
      obtain ⟨count, next⟩ := link
      rw [residueSkeletonChain, induction, safeResidue_eq_outer, outer_mul,
        Matrix.mul_smul, outer_mul_outer, skeletonIncidences, List.prod_cons, skeletonLast,
        ← Matrix.dotProduct_mulVec, skeletonFullIncidence_eq]
      simp [smul_smul, mul_comm]

/-- The full cleared residue product vanishes exactly at one bad internal defect run. -/
theorem residueSkeletonChain_eq_zero_iff (first : Bool) (tail : List (Nat × Bool)) :
    residueSkeletonChain first tail = 0 ↔ BadSkeleton first tail := by
  rw [residueSkeletonChain_factor, smul_eq_zero]
  have outer_ne :
      Matrix.vecMulVec (skeletonLift (skeletonColumn first))
          (skeletonFullRow (skeletonLast first tail)) ≠ 0 := by
    apply outer_ne_zero
    · intro zero
      apply skeletonColumn_ne_zero first
      funext i
      fin_cases i
      · have entry := congr_fun zero 0
        simpa [skeletonLift] using entry
      · have entry := congr_fun zero 2
        simpa [skeletonLift] using entry
    · cases skeletonLast first tail
      · intro zero
        have entry := congr_fun zero 0
        norm_num [skeletonFullRow] at entry
      · intro zero
        have entry := congr_fun zero 0
        norm_num [skeletonFullRow] at entry
        exact (show (2 : ZMod 3) ≠ 0 by decide) entry
  simp only [outer_ne, or_false, List.prod_eq_zero_iff]
  exact zero_mem_skeletonIncidences_iff first tail

/-- One concrete residue-two run followed by its next safe atom. -/
structure DefectSkeletonLink where
  /-- Concrete residue-two atoms in the intervening defect run. -/
  defects : List (TagLetter × Nat)
  /-- Safe atom terminating the run, including its modulo-three phase. -/
  nextSafe : TagLetter × Nat × Bool

/-- Phase-and-length skeleton underlying concrete safe atoms and defect runs. -/
def defectSkeletonPattern : List DefectSkeletonLink → List (Nat × Bool) :=
  List.map fun link => (link.defects.length, link.nextSafe.2.2)

/-- Concrete rational atom product represented by a defect skeleton. -/
def defectSkeletonProduct (β : Nat) (body : List TagLetter) :
    (TagLetter × Nat × Bool) → List DefectSkeletonLink →
      Matrix (Fin 3) (Fin 3) ℚ
  | first, [] => residueTwoWallGenerator β body first
  | first, link :: tail =>
      residueTwoWallGenerator β body first *
        wordProduct (fun label => atom β body label.1 (3 * label.2 + 2)) link.defects *
          defectSkeletonProduct β body link.nextSafe tail

private def defectSkeletonNumerator (β : Nat) (body : List TagLetter) :
    (TagLetter × Nat × Bool) → List DefectSkeletonLink →
      Matrix (Fin 3) (Fin 3) ℤ
  | first, [] => safeNumerator β body first
  | first, link :: tail =>
      safeNumerator β body first *
        wordProduct (residueTwoNumerator β body) link.defects *
          defectSkeletonNumerator β body link.nextSafe tail

private def defectSkeletonAtomCount : List DefectSkeletonLink → Nat
  | [] => 1
  | link :: tail => 1 + link.defects.length + defectSkeletonAtomCount tail

private theorem cast_residueTwoWord
    (β : Nat) (body : List TagLetter) (word : List (TagLetter × Nat)) :
    castMatrix (wordProduct (residueTwoNumerator β body) word) =
      (64 : ℚ) ^ word.length •
        wordProduct (fun label => atom β body label.1 (3 * label.2 + 2)) word := by
  induction word with
  | nil => simp [wordProduct, castMatrix]
  | cons head tail induction =>
      rw [wordProduct_cons]
      change castMatrix
          (residueTwoNumerator β body head *
            wordProduct (residueTwoNumerator β body) tail) = _
      rw [show castMatrix
          (residueTwoNumerator β body head *
            wordProduct (residueTwoNumerator β body) tail) =
          castMatrix (residueTwoNumerator β body head) *
            castMatrix (wordProduct (residueTwoNumerator β body) tail) by
          simp only [castMatrix, Matrix.map_mul],
        cast_residueTwoNumerator, induction, wordProduct_cons, List.length_cons,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_succ']

private theorem cast_defectSkeletonNumerator
    (β : Nat) (body : List TagLetter) (first : TagLetter × Nat × Bool)
    (tail : List DefectSkeletonLink) :
    castMatrix (defectSkeletonNumerator β body first tail) =
      (64 : ℚ) ^ defectSkeletonAtomCount tail •
        defectSkeletonProduct β body first tail := by
  induction tail generalizing first with
  | nil =>
      simp [defectSkeletonNumerator, defectSkeletonAtomCount, defectSkeletonProduct,
        cast_safeNumerator]
  | cons link tail induction =>
      rw [defectSkeletonNumerator, defectSkeletonProduct]
      change castMatrix
          (safeNumerator β body first *
            wordProduct (residueTwoNumerator β body) link.defects *
              defectSkeletonNumerator β body link.nextSafe tail) = _
      rw [show castMatrix
          (safeNumerator β body first *
            wordProduct (residueTwoNumerator β body) link.defects *
              defectSkeletonNumerator β body link.nextSafe tail) =
          castMatrix (safeNumerator β body first) *
            castMatrix (wordProduct (residueTwoNumerator β body) link.defects) *
              castMatrix (defectSkeletonNumerator β body link.nextSafe tail) by
          simp only [castMatrix, Matrix.map_mul],
        cast_safeNumerator, cast_residueTwoWord, induction]
      simp only [defectSkeletonAtomCount, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      rw [pow_add, pow_add]
      norm_num
      ring_nf

private theorem mapped_residueTwoWord
    (β : Nat) (body : List TagLetter) (word : List (TagLetter × Nat)) :
    (wordProduct (residueTwoNumerator β body) word).map (Int.castRingHom (ZMod 3)) =
      residueTwoResidue ^ word.length := by
  induction word with
  | nil => simp [wordProduct]
  | cons head tail induction =>
      rw [wordProduct_cons, Matrix.map_mul, mapped_residueTwoNumerator, induction,
        List.length_cons, pow_succ']

private theorem mapped_defectSkeletonNumerator
    (β : Nat) (body : List TagLetter) (first : TagLetter × Nat × Bool)
    (tail : List DefectSkeletonLink) :
    (defectSkeletonNumerator β body first tail).map (Int.castRingHom (ZMod 3)) =
      residueSkeletonChain first.2.2 (defectSkeletonPattern tail) := by
  induction tail generalizing first with
  | nil =>
      simpa [defectSkeletonNumerator, defectSkeletonPattern, residueSkeletonChain] using
        mapped_safeNumerator β body first
  | cons link tail induction =>
      rw [defectSkeletonNumerator, Matrix.map_mul, Matrix.map_mul, mapped_safeNumerator,
        mapped_residueTwoWord, induction]
      rfl

/-- Every concrete defect skeleton without a bad internal run is exactly nonzero over the
rationals. -/
theorem defectSkeletonProduct_ne_zero_of_not_bad
    (β : Nat) (body : List TagLetter) (first : TagLetter × Nat × Bool)
    (tail : List DefectSkeletonLink)
    (good : ¬BadSkeleton first.2.2 (defectSkeletonPattern tail)) :
    defectSkeletonProduct β body first tail ≠ 0 := by
  intro product_zero
  have cast_zero := cast_defectSkeletonNumerator β body first tail
  rw [product_zero, smul_zero] at cast_zero
  have numerator_zero : defectSkeletonNumerator β body first tail = 0 :=
    (castMatrix_eq_zero_iff _).mp cast_zero
  have residue_zero :
      residueSkeletonChain first.2.2 (defectSkeletonPattern tail) = 0 := by
    rw [← mapped_defectSkeletonNumerator β body first tail, numerator_zero]
    simp
  exact good ((residueSkeletonChain_eq_zero_iff _ _).mp residue_zero)

/-! ## Exact reset of a pure defect block -/

private def clearedExteriorChange : Matrix (Fin 3) (Fin 3) ℤ :=
  !![-4, -4, 1;
      4, 0, 0;
      0, 0, -1]

private def integralExteriorChangeInv : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     -1, -1, -1;
      0, 0, -4]

private def defectExteriorNumerator (β : Nat) (body : List TagLetter)
    (label : TagLetter × Nat) : Matrix (Fin 3) (Fin 3) ℤ :=
  clearedExteriorChange * (residueTwoNumerator β body label).adjugateᵀ *
    integralExteriorChangeInv

private def defectExteriorResidue : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  !![2, 1, 1;
     0, 0, 0;
     0, 0, 0]

private def defectExteriorSeed (R : Type*) [OfNat R 0] [OfNat R 9] [OfNat R 22] :
    Fin 3 → R :=
  ![0, 22, 9]

private def defectExteriorRay (R : Type*) [OfNat R 0] [OfNat R 1] : Fin 3 → R :=
  ![1, 0, 0]

private theorem mapped_defectExteriorNumerator
    (β : Nat) (body : List TagLetter) (label : TagLetter × Nat) :
    (defectExteriorNumerator β body label).map (Int.castRingHom (ZMod 3)) =
      defectExteriorResidue := by
  let map := Int.castRingHom (ZMod 3)
  have mappedAdjugate :
      ((residueTwoNumerator β body label).adjugate).map map =
        ((residueTwoNumerator β body label).map map).adjugate :=
    map.map_adjugate _
  rw [defectExteriorNumerator, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
    mappedAdjugate, mapped_residueTwoNumerator]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [clearedExteriorChange, integralExteriorChangeInv, residueTwoResidue,
      defectExteriorResidue, Matrix.adjugate_fin_three, Matrix.transpose_apply,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    decide

private theorem cast_defectExteriorNumerator
    (β : Nat) (body : List TagLetter) (label : TagLetter × Nat) :
    castMatrix (defectExteriorNumerator β body label) =
      (16384 : ℚ) • exteriorTransition
        (atom β body label.1 (3 * label.2 + 2)) := by
  have change_cast : castMatrix clearedExteriorChange = (4 : ℚ) • exteriorChange := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [castMatrix, clearedExteriorChange, exteriorChange]
  have inverse_cast : castMatrix integralExteriorChangeInv = exteriorChangeInv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [castMatrix, integralExteriorChangeInv, exteriorChangeInv]
  have mappedAdjugate :
      castMatrix (residueTwoNumerator β body label).adjugate =
        (castMatrix (residueTwoNumerator β body label)).adjugate :=
    (Int.castRingHom ℚ).map_adjugate _
  rw [defectExteriorNumerator]
  change castMatrix
      (clearedExteriorChange * (residueTwoNumerator β body label).adjugateᵀ *
        integralExteriorChangeInv) = _
  rw [show castMatrix
      (clearedExteriorChange * (residueTwoNumerator β body label).adjugateᵀ *
        integralExteriorChangeInv) =
      castMatrix clearedExteriorChange *
          (castMatrix (residueTwoNumerator β body label).adjugate)ᵀ *
        castMatrix integralExteriorChangeInv by
      simp only [castMatrix, Matrix.map_mul, Matrix.transpose_map]]
  rw [change_cast, inverse_cast, mappedAdjugate, cast_residueTwoNumerator,
    Matrix.adjugate_smul, Matrix.transpose_smul]
  norm_num [exteriorTransition, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

private theorem mapped_defectExteriorWord
    (β : Nat) (body : List TagLetter) (word : List (TagLetter × Nat)) :
    (wordProduct (defectExteriorNumerator β body) word).map
        (Int.castRingHom (ZMod 3)) = defectExteriorResidue ^ word.length := by
  induction word with
  | nil => simp [wordProduct]
  | cons head tail induction =>
      rw [wordProduct_cons, Matrix.map_mul, mapped_defectExteriorNumerator, induction,
        List.length_cons, pow_succ']

private theorem defectExteriorResidue_mulVec_seed :
    defectExteriorResidue *ᵥ defectExteriorSeed (ZMod 3) =
      defectExteriorRay (ZMod 3) := by
  funext i
  fin_cases i <;>
    norm_num [defectExteriorResidue, defectExteriorSeed, defectExteriorRay,
      Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ]
  exact (show (31 : ZMod 3) = 1 by decide)

private theorem defectExteriorResidue_mulVec_ray :
    defectExteriorResidue *ᵥ defectExteriorRay (ZMod 3) =
      (2 : ZMod 3) • defectExteriorRay (ZMod 3) := by
  funext i
  fin_cases i <;>
    norm_num [defectExteriorResidue, defectExteriorRay, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_succ]

private theorem defectExteriorResidue_pow_succ_mulVec_seed (count : Nat) :
    defectExteriorResidue ^ (count + 1) *ᵥ defectExteriorSeed (ZMod 3) =
      (2 : ZMod 3) ^ count • defectExteriorRay (ZMod 3) := by
  induction count with
  | zero => simpa using defectExteriorResidue_mulVec_seed
  | succ count induction =>
      rw [show count + 1 + 1 = (count + 1) + 1 by omega, pow_succ',
        ← Matrix.mulVec_mulVec, induction, Matrix.mulVec_smul,
        defectExteriorResidue_mulVec_ray, smul_smul, pow_succ']
      rw [mul_comm]

private theorem cast_defectExteriorWord
    (β : Nat) (body : List TagLetter) (word : List (TagLetter × Nat)) :
    castMatrix (wordProduct (defectExteriorNumerator β body) word) =
      (16384 : ℚ) ^ word.length •
        wordProduct
          (fun label => exteriorTransition (atom β body label.1 (3 * label.2 + 2))) word := by
  induction word with
  | nil => simp [wordProduct, castMatrix]
  | cons head tail induction =>
      rw [wordProduct_cons]
      change castMatrix
          (defectExteriorNumerator β body head *
            wordProduct (defectExteriorNumerator β body) tail) = _
      rw [show castMatrix
          (defectExteriorNumerator β body head *
            wordProduct (defectExteriorNumerator β body) tail) =
          castMatrix (defectExteriorNumerator β body head) *
            castMatrix (wordProduct (defectExteriorNumerator β body) tail) by
          simp only [castMatrix, Matrix.map_mul],
        cast_defectExteriorNumerator, induction, wordProduct_cons, List.length_cons,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_succ']

private theorem exteriorState_defect_word
    (β : Nat) (body : List TagLetter) (word : List (TagLetter × Nat)) :
    exteriorState
        (wordProduct (fun label => atom β body label.1 (3 * label.2 + 2)) word) =
      wordProduct
          (fun label => exteriorTransition (atom β body label.1 (3 * label.2 + 2))) word *ᵥ
        exteriorState 1 := by
  induction word with
  | nil => simp [wordProduct]
  | cons head tail induction =>
      rw [wordProduct_cons, exteriorState_mul, wordProduct_cons,
        ← Matrix.mulVec_mulVec, induction]

private theorem cast_defectExteriorState
    (β : Nat) (body : List TagLetter) (word : List (TagLetter × Nat)) :
    castVector
        (wordProduct (defectExteriorNumerator β body) word *ᵥ defectExteriorSeed ℤ) =
      (16384 : ℚ) ^ word.length • exteriorState
        (wordProduct (fun label => atom β body label.1 (3 * label.2 + 2)) word) := by
  have seed_cast : castVector (defectExteriorSeed ℤ) = exteriorState 1 := by
    rw [exteriorState_one]
    funext i
    fin_cases i <;> norm_num [castVector, defectExteriorSeed]
  funext i
  rw [show castVector
      (wordProduct (defectExteriorNumerator β body) word *ᵥ defectExteriorSeed ℤ) i =
      (castMatrix (wordProduct (defectExteriorNumerator β body) word) *ᵥ
        castVector (defectExteriorSeed ℤ)) i by
      exact (Int.castRingHom ℚ).map_mulVec _ _ i]
  rw [cast_defectExteriorWord, seed_cast, Matrix.smul_mulVec_assoc,
    ← exteriorState_defect_word]

/-- Every nonempty pure residue-two block induces an invertible bridge. -/
theorem pureDefect_bridge_det_ne_zero
    (β : Nat) (body : List TagLetter) (word : List (TagLetter × Nat))
    (word_nonempty : word ≠ []) :
    (bridge ((3 : ℚ) ^ β)
      (wordProduct (fun label => atom β body label.1 (3 * label.2 + 2)) word)).det ≠ 0 := by
  obtain ⟨head, tail, rfl⟩ := List.exists_cons_of_ne_nil word_nonempty
  let integerState :=
    wordProduct (defectExteriorNumerator β body) (head :: tail) *ᵥ defectExteriorSeed ℤ
  have mappedFirst :
      ((integerState 0 : ℤ) : ZMod 3) = (2 : ZMod 3) ^ tail.length := by
    rw [show ((integerState 0 : ℤ) : ZMod 3) =
        (((wordProduct (defectExteriorNumerator β body) (head :: tail)).map
            (Int.castRingHom (ZMod 3))) *ᵥ defectExteriorSeed (ZMod 3)) 0 by
      simpa [integerState, defectExteriorSeed] using
        (Int.castRingHom (ZMod 3)).map_mulVec
          (wordProduct (defectExteriorNumerator β body) (head :: tail))
          (defectExteriorSeed ℤ) 0]
    rw [mapped_defectExteriorWord, List.length_cons,
      defectExteriorResidue_pow_succ_mulVec_seed]
    simp [defectExteriorRay]
  have integerFirst_ne : integerState 0 ≠ 0 := by
    intro integerFirst_zero
    rw [integerFirst_zero] at mappedFirst
    simpa using (pow_ne_zero tail.length (show (2 : ZMod 3) ≠ 0 by decide) mappedFirst.symm)
  have exteriorFirst_ne :
      exteriorState
        (wordProduct (fun label => atom β body label.1 (3 * label.2 + 2)) (head :: tail)) 0 ≠
          0 := by
    intro exteriorFirst_zero
    have castState := congr_fun (cast_defectExteriorState β body (head :: tail)) 0
    rw [Pi.smul_apply, exteriorFirst_zero, smul_zero] at castState
    change ((integerState 0 : ℤ) : ℚ) = 0 at castState
    exact integerFirst_ne (by exact_mod_cast castState)
  rw [bridge_det_eq_exteriorState_first]
  exact mul_ne_zero (by positivity) exteriorFirst_ne

/-! ## Rational bridge fracture -/

/-- Every nonzero singular two-by-two rational matrix is a nonzero outer product. -/
theorem exists_outer_of_det_eq_zero
    (matrix : Matrix (Fin 2) (Fin 2) ℚ) (matrix_ne : matrix ≠ 0)
    (det_zero : matrix.det = 0) :
    ∃ column row : Fin 2 → ℚ,
      column ≠ 0 ∧ row ≠ 0 ∧ matrix = Matrix.vecMulVec column row := by
  let a := matrix 0 0
  let b := matrix 0 1
  let c := matrix 1 0
  let d := matrix 1 1
  have determinant : a * d - b * c = 0 := by
    simpa [a, b, c, d, Matrix.det_fin_two] using det_zero
  by_cases a_ne : a ≠ 0
  · have d_eq : d = c * (b / a) := by
      field_simp [a_ne]
      linear_combination determinant
    refine ⟨![a, c], ![1, b / a], ?_, ?_, ?_⟩
    · intro zero
      exact a_ne (by simpa [a] using congr_fun zero 0)
    · intro zero
      have entry := congr_fun zero 0
      norm_num at entry
    · ext i j
      fin_cases i <;> fin_cases j
      · change a = a * 1
        ring
      · change b = a * (b / a)
        field_simp [a_ne]
      · change c = c * 1
        ring
      · change d = c * (b / a)
        exact d_eq
  · have a_zero : a = 0 := not_ne_iff.mp a_ne
    have bc_zero : b * c = 0 := by
      rw [a_zero] at determinant
      linear_combination -determinant
    by_cases b_ne : b ≠ 0
    · have c_zero : c = 0 := (mul_eq_zero.mp bc_zero).resolve_left b_ne
      have a_entry : matrix 0 0 = 0 := a_zero
      have c_entry : matrix 1 0 = 0 := c_zero
      refine ⟨![b, d], ![0, 1], ?_, ?_, ?_⟩
      · intro zero
        exact b_ne (by simpa [b] using congr_fun zero 0)
      · intro zero
        have entry := congr_fun zero 1
        norm_num at entry
      · ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.vecMulVec_apply, a, b, c, d, a_entry, c_entry]
    · have b_zero : b = 0 := not_ne_iff.mp b_ne
      have a_entry : matrix 0 0 = 0 := a_zero
      have b_entry : matrix 0 1 = 0 := b_zero
      have row_ne : ![c, d] ≠ (0 : Fin 2 → ℚ) := by
        intro row_zero
        have c_zero : c = 0 := by
          have entry := congr_fun row_zero 0
          simpa using entry
        have d_zero : d = 0 := by
          have entry := congr_fun row_zero 1
          simpa using entry
        have c_entry : matrix 1 0 = 0 := c_zero
        have d_entry : matrix 1 1 = 0 := d_zero
        apply matrix_ne
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [a, b, c, d, a_entry, b_entry, c_entry, d_entry]
      refine ⟨![0, 1], ![c, d], ?_, row_ne, ?_⟩
      · intro zero
        have entry := congr_fun zero 1
        norm_num at entry
      · ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.vecMulVec_apply, a, b, c, d, a_entry, b_entry]

/-- One transport followed by the next rank-one wall in a bridge fracture. -/
structure BridgeFractureLink where
  /-- Two-dimensional transport between consecutive rank-one walls. -/
  transport : Matrix (Fin 2) (Fin 2) ℚ
  /-- Column of the wall following the transport. -/
  column : Fin 2 → ℚ
  /-- Row of the wall following the transport. -/
  row : Fin 2 → ℚ

/-- Product of varying rank-one walls separated by arbitrary two-dimensional transports. -/
def bridgeFractureChain (column row : Fin 2 → ℚ) :
    List BridgeFractureLink → Matrix (Fin 2) (Fin 2) ℚ
  | [] => Matrix.vecMulVec column row
  | link :: tail =>
      Matrix.vecMulVec column row * link.transport *
        bridgeFractureChain link.column link.row tail

/-- Consecutive projective incidences in a varying rank-one bridge fracture. -/
def bridgeFractureIncidences (row : Fin 2 → ℚ) :
    List BridgeFractureLink → List ℚ
  | [] => []
  | link :: tail =>
      (row ⬝ᵥ (link.transport *ᵥ link.column)) ::
        bridgeFractureIncidences link.row tail

/-- Exterior row of the final wall in a bridge fracture. -/
def bridgeFractureLastRow (row : Fin 2 → ℚ) :
    List BridgeFractureLink → Fin 2 → ℚ
  | [] => row
  | link :: tail => bridgeFractureLastRow link.row tail

/-- A bridge fracture is one outer product times the product of its local incidences. -/
theorem bridgeFractureChain_factor (column row : Fin 2 → ℚ)
    (links : List BridgeFractureLink) :
    bridgeFractureChain column row links =
      (bridgeFractureIncidences row links).prod •
        Matrix.vecMulVec column (bridgeFractureLastRow row links) := by
  induction links generalizing column row with
  | nil => simp [bridgeFractureChain, bridgeFractureIncidences, bridgeFractureLastRow]
  | cons link tail induction =>
      rw [bridgeFractureChain, induction, Matrix.mul_smul, outer_mul, outer_mul_outer,
        ← Matrix.dotProduct_mulVec]
      simp [bridgeFractureIncidences, bridgeFractureLastRow, smul_smul, mul_comm]

/-- No collective cancellation exists in a rank-one fracture: the chain vanishes exactly at one
consecutive projective incidence. -/
theorem bridgeFractureChain_eq_zero_iff (column row : Fin 2 → ℚ)
    (links : List BridgeFractureLink) (column_ne : column ≠ 0)
    (lastRow_ne : bridgeFractureLastRow row links ≠ 0) :
    bridgeFractureChain column row links = 0 ↔
      (0 : ℚ) ∈ bridgeFractureIncidences row links := by
  rw [bridgeFractureChain_factor, smul_eq_zero]
  have outer_ne :
      Matrix.vecMulVec column (bridgeFractureLastRow row links) ≠ 0 :=
    outer_ne_zero column_ne lastRow_ne
  simp [outer_ne, List.prod_eq_zero_iff]

/-- A regular atom word induces a nonzero bridge. -/
theorem bridge_regular_word_ne_zero
    (β : Nat) (body : List TagLetter) (body_nonempty : body ≠ [])
    (middle : List (TagLetter × Nat))
    (regular : ∀ label ∈ middle, label ≠ (.b, 1)) :
    bridge ((3 : ℚ) ^ β)
      (wordProduct (fun label => atom β body label.1 label.2) middle) ≠ 0 := by
  let ρ : ℚ := 3 ^ β
  let M := wordProduct (fun label => atom β body label.1 label.2) middle
  intro bridge_zero
  have bridge_word_zero :
      wordProduct (bridge ρ) [M] = 0 := by
    simpa [wordProduct] using bridge_zero
  have chain_zero :
      exceptionalChain ρ [M] = 0 :=
    (exceptionalChain_eq_zero_iff ρ (by positivity) [M]).mpr bridge_word_zero
  exact two_exceptional_atoms_ne_zero β body body_nonempty middle regular
    (by simpa [ρ, M, exceptionalChain, atom] using chain_zero)

/-- A regular bridge is singular exactly on the first exterior-coordinate wall. -/
theorem bridge_regular_word_det_eq_zero_iff
    (β : Nat) (body : List TagLetter) (middle : List (TagLetter × Nat)) :
    (bridge ((3 : ℚ) ^ β)
      (wordProduct (fun label => atom β body label.1 label.2) middle)).det = 0 ↔
      exteriorState
        (wordProduct (fun label => atom β body label.1 label.2) middle) 0 = 0 := by
  rw [bridge_det_eq_exteriorState_first]
  have coefficient_ne : (9 * (3 : ℚ) ^ β / 2) ≠ 0 := by positivity
  exact mul_eq_zero.trans (by simp [coefficient_ne])

/-- Every regular wall bridge has a nonzero rank-one outer factorization. -/
theorem bridge_regular_word_outer
    (β : Nat) (body : List TagLetter) (body_nonempty : body ≠ [])
    (middle : List (TagLetter × Nat))
    (regular : ∀ label ∈ middle, label ≠ (.b, 1))
    (wall : exteriorState
      (wordProduct (fun label => atom β body label.1 label.2) middle) 0 = 0) :
    ∃ column row : Fin 2 → ℚ,
      column ≠ 0 ∧ row ≠ 0 ∧
        bridge ((3 : ℚ) ^ β)
            (wordProduct (fun label => atom β body label.1 label.2) middle) =
          Matrix.vecMulVec column row := by
  apply exists_outer_of_det_eq_zero
  · exact bridge_regular_word_ne_zero β body body_nonempty middle regular
  · exact (bridge_regular_word_det_eq_zero_iff β body middle).mpr wall

/-- Left-kernel row selected by a bridge middle block. -/
def bridgeCokernel (middle : Matrix (Fin 3) (Fin 3) ℚ) : Fin 2 → ℚ :=
  (exteriorSeed ᵥ* middle.adjugate) ᵥ* coreRightInverse

/-- The bridge cokernel is exactly the two oriented tail coordinates of the exterior state. -/
theorem bridgeCokernel_eq_exteriorTail (middle : Matrix (Fin 3) (Fin 3) ℚ) :
    bridgeCokernel middle =
      ![exteriorState middle 1, -4 * exteriorState middle 2] := by
  funext i
  fin_cases i <;>
    norm_num [bridgeCokernel, coreRightInverse, exteriorState, exteriorChange, exteriorSeed,
      Matrix.vecMul, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ] <;>
    ring

/-- On the bridge wall, the selected cokernel row retracts to the full exterior covector. -/
theorem bridgeCokernel_vecMul_coreInput_of_wall
    (middle : Matrix (Fin 3) (Fin 3) ℚ) (wall : exteriorState middle 0 = 0) :
    bridgeCokernel middle ᵥ* coreInput = exteriorSeed ᵥ* middle.adjugate := by
  let live := exteriorSeed ᵥ* middle.adjugate
  have wall_relation : -live 0 - live 1 + live 2 / 4 = 0 := by
    dsimp [live]
    norm_num [exteriorState, exteriorChange, exteriorSeed, Matrix.mulVec,
      Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_succ] at wall ⊢
    linear_combination wall
  have cokernel_eq : bridgeCokernel middle = ![live 0, live 2] := by
    funext i
    fin_cases i <;>
      simp [bridgeCokernel, coreRightInverse, live, Matrix.vecMul,
        Matrix.dotProduct, Fin.sum_univ_succ]
  rw [cokernel_eq]
  change ![live 0, live 2] ᵥ* coreInput = live
  funext i
  fin_cases i
  · norm_num [coreInput, Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_succ]
  · norm_num [coreInput, Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_succ]
    linear_combination wall_relation
  · norm_num [coreInput, Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_succ]
    rfl

/-- An invertible middle block gives a genuine nonzero projective cokernel on the wall. -/
theorem bridgeCokernel_ne_zero_of_isUnit
    (middle : Matrix (Fin 3) (Fin 3) ℚ) (middle_unit : IsUnit middle)
    (wall : exteriorState middle 0 = 0) :
    bridgeCokernel middle ≠ 0 := by
  intro cokernel_zero
  have live_zero : exteriorSeed ᵥ* middle.adjugate = 0 := by
    rw [← bridgeCokernel_vecMul_coreInput_of_wall middle wall, cokernel_zero]
    simp
  have annihilation : middle.det • exteriorSeed = 0 := by
    calc
      middle.det • exteriorSeed = exteriorSeed ᵥ* (middle.det • 1) := by
        funext i
        fin_cases i <;>
          norm_num [exteriorSeed, Matrix.vecMul, Matrix.dotProduct, Matrix.one_apply,
            Matrix.smul_apply, Fin.sum_univ_succ] <;>
          ring
      _ = exteriorSeed ᵥ* (middle.adjugate * middle) := by rw [Matrix.adjugate_mul]
      _ = (exteriorSeed ᵥ* middle.adjugate) ᵥ* middle := by
        rw [Matrix.vecMul_vecMul]
      _ = 0 := by rw [live_zero]; simp
  have determinant_ne : middle.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det middle).mp middle_unit).ne_zero
  have seed_ne : exteriorSeed ≠ 0 := by
    intro seed_zero
    have entry := congr_fun seed_zero 0
    norm_num [exteriorSeed] at entry
  exact smul_ne_zero determinant_ne seed_ne annihilation

/-- Every regular wall word exposes a nonzero oriented bridge cokernel. -/
theorem bridgeCokernel_regular_word_ne_zero
    (β : Nat) (body : List TagLetter) (body_nonempty : body ≠ [])
    (middle : List (TagLetter × Nat))
    (regular : ∀ label ∈ middle, label ≠ (.b, 1))
    (wall : exteriorState
      (wordProduct (fun label => atom β body label.1 label.2) middle) 0 = 0) :
    bridgeCokernel
      (wordProduct (fun label => atom β body label.1 label.2) middle) ≠ 0 := by
  apply bridgeCokernel_ne_zero_of_isUnit _ _ wall
  exact wordProduct_isUnit_of_mem _ middle (fun label member =>
    (atom_isUnit_iff β body body_nonempty label.1 label.2).mpr
      (regular label member))

/-- On the bridge wall, the displayed row annihilates the bridge from the left. -/
theorem bridgeCokernel_vecMul_bridge_of_wall
    (ρ : ℚ) (middle : Matrix (Fin 3) (Fin 3) ℚ)
    (wall : exteriorState middle 0 = 0) :
    bridgeCokernel middle ᵥ* bridge ρ middle = 0 := by
  let live := exteriorSeed ᵥ* middle.adjugate
  have retract :
      bridgeCokernel middle ᵥ* coreInput = live := by
    exact bridgeCokernel_vecMul_coreInput_of_wall middle wall
  calc
    bridgeCokernel middle ᵥ* bridge ρ middle =
        (bridgeCokernel middle ᵥ* coreInput) ᵥ* middle ᵥ* coreOutput ρ := by
          simp [bridge, Matrix.vecMul_vecMul]
    _ = (live ᵥ* middle) ᵥ* coreOutput ρ := by rw [retract]
    _ = (exteriorSeed ᵥ* (middle.adjugate * middle)) ᵥ* coreOutput ρ := by
          simp [live, Matrix.vecMul_vecMul]
    _ = (exteriorSeed ᵥ* (middle.det • (1 : Matrix (Fin 3) (Fin 3) ℚ))) ᵥ*
        coreOutput ρ := by rw [Matrix.adjugate_mul]
    _ = 0 := by
      funext i
      fin_cases i <;>
        norm_num [coreOutput, exteriorSeed, Matrix.vecMul, Matrix.dotProduct,
          Matrix.one_apply, Matrix.smul_apply, Fin.sum_univ_succ] <;>
        ring

end MatrixMortality.ParabolicBlade
