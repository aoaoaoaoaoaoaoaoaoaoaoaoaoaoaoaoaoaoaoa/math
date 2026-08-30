import Mathlib.Tactic

/-!
# Mixed-prime affine kernel

The raw letters `D(z) = (2 / 3)z` and `T(z) = (3 / 5)z + 1` satisfy several
short balanced relations.  Words act from right to left, matching matrix multiplication.
-/

namespace MatrixMortality.MixedPrimeKernel

/-- The two raw generators of the mixed-prime affine benchmark. -/
inductive Letter
  | dilate
  | translate
  deriving DecidableEq

/-- Rational affine action of one raw benchmark letter. -/
def action : Letter → ℚ → ℚ
  | .dilate, state => 2 / 3 * state
  | .translate, state => 3 / 5 * state + 1

/-- Act by a raw word from right to left, matching matrix multiplication. -/
def wordAction : List Letter → ℚ → ℚ
  | [], state => state
  | letter :: word, state => action letter (wordAction word state)

/-- Concatenation is composition in matrix-product order. -/
theorem wordAction_append (left right : List Letter) (state : ℚ) :
    wordAction (left ++ right) state = wordAction left (wordAction right state) := by
  induction left with
  | nil => rfl
  | cons letter left induction =>
      simp only [List.cons_append, wordAction, induction]

/-- Every raw affine relation remains valid in every two-sided word context. -/
theorem wordAction_context
    {left right : List Letter}
    (relation : ∀ state, wordAction left state = wordAction right state)
    (before after : List Letter) (state : ℚ) :
    wordAction (before ++ left ++ after) state =
      wordAction (before ++ right ++ after) state := by
  simp only [wordAction_append]
  rw [relation]

/-- Left side of the shortest relation reported by Cassaigne and Nicolas. -/
def cassaigneLeft : List Letter :=
  [.dilate] ++ List.replicate 10 .translate ++ List.replicate 2 .dilate ++
    [.translate] ++ List.replicate 2 .dilate ++ [.translate] ++
    List.replicate 10 .dilate

/-- Right side of the shortest relation reported by Cassaigne and Nicolas. -/
def cassaigneRight : List Letter :=
  List.replicate 2 .translate ++ List.replicate 6 .dilate ++
    List.replicate 2 .translate ++ List.replicate 2 .dilate ++
    [.translate, .dilate, .translate, .dilate, .translate] ++
    List.replicate 2 .dilate ++ List.replicate 2 .translate ++
    List.replicate 2 .dilate ++ [.translate, .dilate] ++
    List.replicate 2 .translate

/-- The published length-27 relation has distinct sides. -/
theorem cassaigne_ne : cassaigneLeft ≠ cassaigneRight := by
  decide

/-- The published length-27 raw words induce the same affine map. -/
theorem wordAction_cassaigne (state : ℚ) :
    wordAction cassaigneLeft state = wordAction cassaigneRight state := by
  norm_num [wordAction, action, cassaigneLeft, cassaigneRight, List.replicate_succ]
  ring

/-- Smaller side of the independent length-29 kernel relation. -/
def kernel29Left : List Letter :=
  [.dilate] ++ List.replicate 10 .translate ++ List.replicate 2 .dilate ++
    [.translate] ++ List.replicate 2 .dilate ++ [.translate] ++
    List.replicate 9 .dilate ++ [.translate] ++ List.replicate 2 .dilate

/-- Larger side of the independent length-29 kernel relation. -/
def kernel29Right : List Letter :=
  List.replicate 2 .translate ++ List.replicate 6 .dilate ++
    List.replicate 2 .translate ++ List.replicate 2 .dilate ++
    [.translate, .dilate, .translate, .dilate, .translate] ++
    List.replicate 2 .dilate ++ List.replicate 2 .translate ++
    List.replicate 2 .dilate ++ List.replicate 2 .translate ++
    List.replicate 2 .dilate ++ List.replicate 2 .translate

/-- The length-29 kernel relation has distinct sides. -/
theorem kernel29_ne : kernel29Left ≠ kernel29Right := by
  decide

/-- The independent length-29 raw words induce the same affine map. -/
theorem wordAction_kernel29 (state : ℚ) :
    wordAction kernel29Left state = wordAction kernel29Right state := by
  norm_num [wordAction, action, kernel29Left, kernel29Right, List.replicate_succ]
  ring

/-- Smaller side of the first independent length-30 kernel relation. -/
def kernel30aLeft : List Letter :=
  [.dilate] ++ List.replicate 6 .translate ++ [.dilate] ++
    List.replicate 2 .translate ++ [.dilate] ++ List.replicate 3 .translate ++
    List.replicate 2 .dilate ++ [.translate] ++ List.replicate 2 .dilate ++
    [.translate] ++ List.replicate 10 .dilate

/-- Larger side of the first independent length-30 kernel relation. -/
def kernel30aRight : List Letter :=
  List.replicate 2 .translate ++ List.replicate 8 .dilate ++
    List.replicate 4 .translate ++ [.dilate, .translate, .dilate, .translate] ++
    List.replicate 2 .dilate ++ [.translate] ++ List.replicate 2 .dilate ++
    [.translate] ++ List.replicate 2 .dilate ++ [.translate, .dilate] ++
    List.replicate 2 .translate

/-- Smaller side of the second independent length-30 kernel relation. -/
def kernel30bLeft : List Letter :=
  [.dilate] ++ List.replicate 6 .translate ++ List.replicate 2 .dilate ++
    [.translate, .dilate] ++ List.replicate 2 .translate ++
    List.replicate 2 .dilate ++ List.replicate 2 .translate ++
    List.replicate 2 .dilate ++ [.translate] ++ List.replicate 10 .dilate

/-- Larger side of the second independent length-30 kernel relation. -/
def kernel30bRight : List Letter :=
  List.replicate 2 .translate ++ List.replicate 10 .dilate ++
    List.replicate 3 .translate ++ List.replicate 3 .dilate ++
    List.replicate 4 .translate ++ List.replicate 2 .dilate ++ [.translate] ++
    List.replicate 3 .dilate ++ List.replicate 2 .translate

/-- Smaller side of the third independent length-30 kernel relation. -/
def kernel30cLeft : List Letter :=
  [.dilate] ++ List.replicate 6 .translate ++ List.replicate 2 .dilate ++
    List.replicate 3 .translate ++ List.replicate 3 .dilate ++
    [.translate, .dilate, .translate, .dilate, .translate] ++
    List.replicate 10 .dilate

/-- Larger side of the third independent length-30 kernel relation. -/
def kernel30cRight : List Letter :=
  List.replicate 2 .translate ++ List.replicate 9 .dilate ++
    [.translate, .dilate] ++ List.replicate 2 .translate ++ [.dilate] ++
    List.replicate 4 .translate ++ List.replicate 2 .dilate ++ [.translate] ++
    List.replicate 2 .dilate ++ [.translate] ++ List.replicate 3 .dilate ++
    [.translate]

/-- Each of the three length-30 kernel relations has distinct sides. -/
theorem kernel30_ne :
    kernel30aLeft ≠ kernel30aRight ∧
      kernel30bLeft ≠ kernel30bRight ∧
      kernel30cLeft ≠ kernel30cRight := by
  decide

/-- The first independent length-30 raw pair induces one affine map. -/
theorem wordAction_kernel30a (state : ℚ) :
    wordAction kernel30aLeft state = wordAction kernel30aRight state := by
  norm_num [wordAction, action, kernel30aLeft, kernel30aRight, List.replicate_succ]
  ring

/-- The second independent length-30 raw pair induces one affine map. -/
theorem wordAction_kernel30b (state : ℚ) :
    wordAction kernel30bLeft state = wordAction kernel30bRight state := by
  norm_num [wordAction, action, kernel30bLeft, kernel30bRight, List.replicate_succ]
  ring

/-- The third independent length-30 raw pair induces one affine map. -/
theorem wordAction_kernel30c (state : ℚ) :
    wordAction kernel30cLeft state = wordAction kernel30cRight state := by
  norm_num [wordAction, action, kernel30cLeft, kernel30cRight, List.replicate_succ]
  ring

end MatrixMortality.MixedPrimeKernel
