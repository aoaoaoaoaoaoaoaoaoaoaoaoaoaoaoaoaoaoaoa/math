import MatrixMortality.GuardedMixedPrimeOddFamilyParikh

/-!
# Uniform Parikh obstruction for pumped mixed-prime relations

This module isolates the list combinatorics shared by the seven certified length-`31 + 2k`
mixed-prime kernel families.  A common Parikh-balanced block inserted on both sides transports
every balanced prefix beyond the insertion sites by exactly the block length.  Consequently an
infinite prefix-balance census reduces to a bounded base window and one recurrence.
-/

set_option autoImplicit false

namespace MatrixMortality.GuardedMixedPrimeFork

open MixedPrimeKernel

/-- Concatenation of `power` copies of one word. -/
def repeatBlock {α : Type*} (block : List α) : ℕ → List α
  | 0 => []
  | power + 1 => block ++ repeatBlock block power

@[simp]
theorem repeatBlock_length {α : Type*} (block : List α) (power : ℕ) :
    (repeatBlock block power).length = power * block.length := by
  induction power with
  | zero => simp [repeatBlock]
  | succ power induction =>
      simp only [repeatBlock, List.length_append, induction]
      simp only [Nat.succ_mul, Nat.add_comm]

theorem repeatBlock_add {α : Type*} (block : List α) (leftPower rightPower : ℕ) :
    repeatBlock block (leftPower + rightPower) =
      repeatBlock block leftPower ++ repeatBlock block rightPower := by
  induction leftPower with
  | zero => simp [repeatBlock]
  | succ leftPower induction =>
      simp only [Nat.succ_add, repeatBlock, induction, List.append_assoc]

theorem repeatBlock_append_block {α : Type*} (block : List α) (power : ℕ) :
    repeatBlock block power ++ block = block ++ repeatBlock block power := by
  induction power with
  | zero => simp [repeatBlock]
  | succ power induction =>
      simp only [repeatBlock, List.append_assoc]
      rw [induction]

/-- Insert a repeated block at a fixed cut of a base word. -/
def pumpAt {α : Type*} (base : List α) (cut : ℕ) (block : List α) (power : ℕ) : List α :=
  base.take cut ++ repeatBlock block power ++ base.drop cut

@[simp]
theorem pumpAt_length {α : Type*} (base block : List α) (cut power : ℕ)
    (cut_le : cut ≤ base.length) :
    (pumpAt base cut block power).length = base.length + power * block.length := by
  simp only [pumpAt, List.length_append, repeatBlock_length, List.length_take,
    List.length_drop]
  omega

/-- A prefix beyond an insertion site gains exactly one block when the pump power increases.
The statement is at the Parikh-count level needed by contextual-fork cuts. -/
theorem pumpAt_succ_prefix_count
    {α : Type*} [DecidableEq α] (letter : α) (base block : List α)
    (cut power prefixLength : ℕ) (cut_le : cut ≤ base.length)
    (cut_le_prefix : cut ≤ prefixLength) :
    ((pumpAt base cut block (power + 1)).take
          (prefixLength + block.length)).count letter =
      ((pumpAt base cut block power).take prefixLength).count letter +
        block.count letter := by
  have cut_take_length : (base.take cut).length = cut := by
    simp only [List.length_take]
    omega
  have old_take :
      (pumpAt base cut block power).take prefixLength =
        base.take cut ++
          (repeatBlock block power ++ base.drop cut).take (prefixLength - cut) := by
    rw [pumpAt, List.append_assoc, List.take_append]
    simp only [cut_take_length]
    rw [(List.take_eq_self_iff _).2 (by omega)]
  have new_take :
      (pumpAt base cut block (power + 1)).take (prefixLength + block.length) =
        base.take cut ++ block ++
          (repeatBlock block power ++ base.drop cut).take (prefixLength - cut) := by
    simp only [pumpAt, repeatBlock, List.append_assoc]
    rw [List.take_append]
    simp only [cut_take_length]
    rw [(List.take_eq_self_iff _).2 (by omega)]
    have residual_eq : prefixLength + block.length - cut = block.length +
        (prefixLength - cut) := by omega
    rw [residual_eq, List.take_append]
    have block_take : block.take (block.length + (prefixLength - cut)) = block :=
      (List.take_eq_self_iff block).2 (by omega)
    rw [block_take, Nat.add_sub_cancel_left]
  rw [old_take, new_take]
  simp only [List.count_append]
  omega

/-- Pumping the same Parikh block on both relation sides transports balanced prefixes beyond
both insertion cuts. -/
theorem pumpAt_succ_prefix_count_eq_iff
    {α : Type*} [DecidableEq α] (letter : α)
    (leftBase rightBase block : List α) (leftCut rightCut power prefixLength : ℕ)
    (leftCut_le : leftCut ≤ leftBase.length) (rightCut_le : rightCut ≤ rightBase.length)
    (leftCut_le_prefix : leftCut ≤ prefixLength)
    (rightCut_le_prefix : rightCut ≤ prefixLength) :
    ((pumpAt leftBase leftCut block (power + 1)).take
          (prefixLength + block.length)).count letter =
        ((pumpAt rightBase rightCut block (power + 1)).take
          (prefixLength + block.length)).count letter ↔
      ((pumpAt leftBase leftCut block power).take prefixLength).count letter =
        ((pumpAt rightBase rightCut block power).take prefixLength).count letter := by
  rw [pumpAt_succ_prefix_count letter leftBase block leftCut power prefixLength
      leftCut_le leftCut_le_prefix,
    pumpAt_succ_prefix_count letter rightBase block rightCut power prefixLength
      rightCut_le rightCut_le_prefix]
  omega

/-- Removing the longer shifted prefix after one pump insertion yields the preceding suffix. -/
theorem pumpAt_succ_drop
    {α : Type*} (base block : List α) (cut power prefixLength : ℕ)
    (cut_le : cut ≤ base.length) (cut_le_prefix : cut ≤ prefixLength) :
    (pumpAt base cut block (power + 1)).drop (prefixLength + block.length) =
      (pumpAt base cut block power).drop prefixLength := by
  have cut_take_length : (base.take cut).length = cut := by
    simp only [List.length_take]
    omega
  have new_factorization :
      pumpAt base cut block (power + 1) =
        (base.take cut ++ block) ++ (repeatBlock block power ++ base.drop cut) := by
    simp only [pumpAt, repeatBlock, List.append_assoc]
  have old_factorization :
      pumpAt base cut block power =
        base.take cut ++ (repeatBlock block power ++ base.drop cut) := by
    simp only [pumpAt, List.append_assoc]
  have common_dropped :
      (base.take cut ++ block).drop (prefixLength + block.length) = [] := by
    rw [List.drop_eq_nil_iff]
    simp only [List.length_append, cut_take_length]
    omega
  have head_dropped : (base.take cut).drop prefixLength = [] := by
    rw [List.drop_eq_nil_iff, cut_take_length]
    exact cut_le_prefix
  rw [new_factorization, old_factorization]
  calc
    ((base.take cut ++ block) ++
          (repeatBlock block power ++ base.drop cut)).drop
        (prefixLength + block.length) =
      (base.take cut ++ block).drop (prefixLength + block.length) ++
        (repeatBlock block power ++ base.drop cut).drop
          (prefixLength + block.length - (base.take cut ++ block).length) :=
      List.drop_append
    _ = (repeatBlock block power ++ base.drop cut).drop (prefixLength - cut) := by
      rw [common_dropped, List.nil_append]
      congr 1
      simp only [List.length_append, cut_take_length]
      omega
    _ = (base.take cut).drop prefixLength ++
        (repeatBlock block power ++ base.drop cut).drop
          (prefixLength - (base.take cut).length) := by
      rw [head_dropped, List.nil_append, cut_take_length]
    _ = (base.take cut ++
          (repeatBlock block power ++ base.drop cut)).drop prefixLength :=
      List.drop_append.symm

theorem pumpAt_drop_cut
    {α : Type*} (base block : List α) (cut power : ℕ) (cut_le : cut ≤ base.length) :
    (pumpAt base cut block power).drop cut = repeatBlock block power ++ base.drop cut := by
  have take_length : (base.take cut).length = cut := by
    simp only [List.length_take]
    omega
  have factorization :
      pumpAt base cut block power =
        base.take cut ++ (repeatBlock block power ++ base.drop cut) := by
    simp only [pumpAt, List.append_assoc]
  have take_dropped : (base.take cut).drop cut = [] := by
    rw [List.drop_eq_nil_iff, take_length]
  rw [factorization, List.drop_append, take_dropped, List.nil_append, take_length,
    Nat.sub_self, List.drop_zero]

theorem head?_drop_eq_of_take_succ_eq
    {α : Type*} {left right : List α} (prefixLength : ℕ)
    (prefix_eq : left.take (prefixLength + 1) = right.take (prefixLength + 1)) :
    (left.drop prefixLength).head? = (right.drop prefixLength).head? := by
  rw [List.head?_drop, List.head?_drop]
  have at_prefix := congrArg (fun word => word[prefixLength]?) prefix_eq
  rw [List.getElem?_take_of_lt (i := prefixLength) (j := prefixLength + 1) (by omega),
    List.getElem?_take_of_lt (i := prefixLength) (j := prefixLength + 1) (by omega)]
    at at_prefix
  exact at_prefix

/-- The seven independently certified length-`31` seeds. -/
inductive PumpedKernelFamily
  | first
  | second
  | third
  | fourth
  | fifth
  | sixth
  | seventh
  deriving DecidableEq

private def decodeLetter (character : Char) : Letter :=
  if character = 'D' then .dilate else .translate

private def decodeWord (encoded : String) : List Letter :=
  encoded.toList.map decodeLetter

/-- Left length-`31` seed of a certified pump family. -/
def PumpedKernelFamily.leftBase : PumpedKernelFamily → List Letter
  | .first => decodeWord "DTTTTTTDTTTTDTDDDTTTDDTDDDDDDDD"
  | .second => decodeWord "DTTTTTTTTDDTDTDTDDTDDTTDDDDDDDD"
  | .third => decodeWord "DTTTTTTTTTTDDTDDTDDDDDDDDDTDTDD"
  | .fourth => decodeWord "DTTTTTTTTTTDDTDDTDTDTDDDDDDDDDD"
  | .fifth => decodeWord "DTTTTTTDDTTTDTTDDTDDTDDDDDDDDDD"
  | .sixth => decodeWord "DTTTTTTDDTDDDDTDDDTDDTDDDDDDDDT"
  | .seventh => decodeWord "DTTTTTTDDTDDDDTTTDDDDDDDDDDDTDD"

/-- Right length-`31` seed of a certified pump family. -/
def PumpedKernelFamily.rightBase : PumpedKernelFamily → List Letter
  | .first => decodeWord "TTDDDDDDDTDTDTTDTTDTDDTDTTDTTDT"
  | .second => decodeWord "TTDDDDDDTDDTDTTDTDTDDTTDTTTDDDT"
  | .third => decodeWord "TTDDDDDDTTDDTDTDTDDTTDDTTDTDDTT"
  | .fourth => decodeWord "TTDDDDDDTDTTTDTDDTTDDTTDDTTDDDT"
  | .fifth => decodeWord "TTDDDDDDDDDTTDTTDTTDDTTDDDDTDTT"
  | .sixth => decodeWord "TTDDDDDDDDDDDDTDTDTTDDTTDTTDTDD"
  | .seventh => decodeWord "TTDDDDDDDDDDDTDDTDTDDTTDTDDTDTT"

/-- Two-letter block inserted in a certified pump family. -/
def PumpedKernelFamily.block : PumpedKernelFamily → List Letter
  | .first | .fifth | .seventh => [.translate, .dilate]
  | .second | .third | .fourth | .sixth => [.dilate, .translate]

/-- Insertion cut on the left seed. -/
def PumpedKernelFamily.leftCut : PumpedKernelFamily → ℕ
  | .first | .fifth => 30
  | .second | .fourth => 29
  | .third => 25
  | .sixth | .seventh => 28

/-- Insertion cut on the right seed. -/
def PumpedKernelFamily.rightCut : PumpedKernelFamily → ℕ
  | .first => 29
  | .second | .fourth => 28
  | .third => 25
  | .fifth | .seventh => 28
  | .sixth => 27

/-- First prefix length at which removing one pump block reaches the preceding census. -/
def PumpedKernelFamily.shiftBoundary : PumpedKernelFamily → ℕ
  | .first | .fifth => 32
  | .second | .fourth => 31
  | .third => 27
  | .sixth | .seventh => 30

/-- Left word of a certified pump family at power `k`. -/
def PumpedKernelFamily.left (family : PumpedKernelFamily) (power : ℕ) : List Letter :=
  pumpAt family.leftBase family.leftCut family.block power

/-- Right word of a certified pump family at power `k`. -/
def PumpedKernelFamily.right (family : PumpedKernelFamily) (power : ℕ) : List Letter :=
  pumpAt family.rightBase family.rightCut family.block power

@[simp]
theorem PumpedKernelFamily.leftBase_length (family : PumpedKernelFamily) :
    family.leftBase.length = 31 := by
  cases family <;> decide

@[simp]
theorem PumpedKernelFamily.rightBase_length (family : PumpedKernelFamily) :
    family.rightBase.length = 31 := by
  cases family <;> decide

@[simp]
theorem PumpedKernelFamily.block_length (family : PumpedKernelFamily) :
    family.block.length = 2 := by
  cases family <;> rfl

theorem PumpedKernelFamily.leftCut_le (family : PumpedKernelFamily) :
    family.leftCut ≤ family.leftBase.length := by
  cases family <;> decide

theorem PumpedKernelFamily.rightCut_le (family : PumpedKernelFamily) :
    family.rightCut ≤ family.rightBase.length := by
  cases family <;> decide

@[simp]
theorem PumpedKernelFamily.left_length (family : PumpedKernelFamily) (power : ℕ) :
    (family.left power).length = 31 + 2 * power := by
  rw [PumpedKernelFamily.left, pumpAt_length _ _ _ _ family.leftCut_le]
  simp only [PumpedKernelFamily.leftBase_length, PumpedKernelFamily.block_length]
  omega

@[simp]
theorem PumpedKernelFamily.right_length (family : PumpedKernelFamily) (power : ℕ) :
    (family.right power).length = 31 + 2 * power := by
  rw [PumpedKernelFamily.right, pumpAt_length _ _ _ _ family.rightCut_le]
  simp only [PumpedKernelFamily.rightBase_length, PumpedKernelFamily.block_length]
  omega

/-- A positive proper relation prefix whose dilation counts agree. -/
def PumpedKernelFamily.BalancedPrefix
    (family : PumpedKernelFamily) (power prefixLength : ℕ) : Prop :=
  0 < prefixLength ∧ prefixLength < 31 + 2 * power ∧
    ((family.left power).take prefixLength).count .dilate =
      ((family.right power).take prefixLength).count .dilate

/-- The dynamic cuts generated from the terminal base cut. -/
def IsPumpedCut (power prefixLength : ℕ) : Prop :=
  ∃ index : Fin power, prefixLength = 30 + 2 * index.1

/-- Families whose prefix census contains the dynamic cuts. -/
def PumpedKernelFamily.HasPumpedCuts : PumpedKernelFamily → Prop
  | .first | .second | .fourth | .sixth => True
  | .third | .fifth | .seventh => False

/-- Exact target form of the seven-family balanced-prefix census. -/
def PumpedKernelFamily.AdmissibleBalancedPrefix
    (family : PumpedKernelFamily) (power prefixLength : ℕ) : Prop :=
  prefixLength = 3 ∨
    (family = .sixth ∧ (prefixLength = 27 ∨ prefixLength = 28)) ∨
    (family.HasPumpedCuts ∧ IsPumpedCut power prefixLength)

/-- Equality of dilation counts at one (not necessarily proper) prefix. -/
def PumpedKernelFamily.PrefixCountEq
    (family : PumpedKernelFamily) (power prefixLength : ℕ) : Prop :=
  ((family.left power).take prefixLength).count .dilate =
    ((family.right power).take prefixLength).count .dilate

instance PumpedKernelFamily.prefixCountEqDecidable
    (family : PumpedKernelFamily) (power prefixLength : ℕ) :
    Decidable (family.PrefixCountEq power prefixLength) := by
  unfold PumpedKernelFamily.PrefixCountEq
  infer_instance

theorem PumpedKernelFamily.admissibleBalancedPrefix_pos
    {family : PumpedKernelFamily} {power prefixLength : ℕ}
    (admissible : family.AdmissibleBalancedPrefix power prefixLength) :
    0 < prefixLength := by
  rcases admissible with prefix_three | static | pumped
  · omega
  · rcases static with ⟨_, prefix_twenty_seven | prefix_twenty_eight⟩ <;> omega
  · rcases pumped with ⟨_, index, prefix_eq⟩
    omega

theorem PumpedKernelFamily.admissibleBalancedPrefix_lt
    {family : PumpedKernelFamily} {power prefixLength : ℕ}
    (admissible : family.AdmissibleBalancedPrefix power prefixLength) :
    prefixLength < 31 + 2 * power := by
  rcases admissible with prefix_three | static | pumped
  · omega
  · rcases static with ⟨_, prefix_twenty_seven | prefix_twenty_eight⟩ <;> omega
  · rcases pumped with ⟨_, index, prefix_eq⟩
    have index_lt := index.2
    omega

theorem PumpedKernelFamily.succ_prefix_count_eq_iff
    (family : PumpedKernelFamily) (power prefixLength : ℕ)
    (leftCut_le_prefix : family.leftCut ≤ prefixLength)
    (rightCut_le_prefix : family.rightCut ≤ prefixLength) :
    ((family.left (power + 1)).take (prefixLength + 2)).count .dilate =
        ((family.right (power + 1)).take (prefixLength + 2)).count .dilate ↔
      ((family.left power).take prefixLength).count .dilate =
        ((family.right power).take prefixLength).count .dilate := by
  simpa only [PumpedKernelFamily.left, PumpedKernelFamily.right,
    PumpedKernelFamily.block_length] using
    pumpAt_succ_prefix_count_eq_iff Letter.dilate family.leftBase family.rightBase
      family.block family.leftCut family.rightCut power prefixLength family.leftCut_le
      family.rightCut_le leftCut_le_prefix rightCut_le_prefix

/-- Uniform induction principle for an exact pumped-prefix census. It reduces the infinite
census to the unpumped seed, one bounded window after pumping, a two-letter shift law, and the
same shift law for the proposed cut classification. -/
theorem PumpedKernelFamily.balancedPrefix_iff_of_shift
    (family : PumpedKernelFamily) (shiftBoundary : ℕ) (boundary_ge_three : 3 ≤ shiftBoundary)
    (base_census : ∀ prefixLength, 0 < prefixLength → prefixLength < 31 →
      (family.PrefixCountEq 0 prefixLength ↔
        family.AdmissibleBalancedPrefix 0 prefixLength))
    (small_census : ∀ power prefixLength, 0 < prefixLength →
      prefixLength < shiftBoundary → prefixLength < 31 + 2 * (power + 1) →
      (family.PrefixCountEq (power + 1) prefixLength ↔
        family.AdmissibleBalancedPrefix (power + 1) prefixLength))
    (left_cut_before_shift : ∀ prefixLength, shiftBoundary ≤ prefixLength →
      family.leftCut ≤ prefixLength - 2)
    (right_cut_before_shift : ∀ prefixLength, shiftBoundary ≤ prefixLength →
      family.rightCut ≤ prefixLength - 2)
    (admissible_shift : ∀ power prefixLength, shiftBoundary ≤ prefixLength →
      prefixLength < 31 + 2 * (power + 1) →
      (family.AdmissibleBalancedPrefix (power + 1) prefixLength ↔
        family.AdmissibleBalancedPrefix power (prefixLength - 2)))
    (power prefixLength : ℕ) :
    family.BalancedPrefix power prefixLength ↔
      family.AdmissibleBalancedPrefix power prefixLength := by
  induction power generalizing prefixLength with
  | zero =>
      constructor
      · rintro ⟨prefix_pos, prefix_lt, counts_eq⟩
        exact (base_census prefixLength prefix_pos (by omega)).mp counts_eq
      · intro admissible
        have prefix_pos := admissibleBalancedPrefix_pos admissible
        have prefix_lt := admissibleBalancedPrefix_lt admissible
        exact ⟨prefix_pos, prefix_lt,
          (base_census prefixLength prefix_pos prefix_lt).mpr admissible⟩
  | succ power induction =>
      constructor
      · rintro ⟨prefix_pos, prefix_lt, counts_eq⟩
        by_cases prefix_small : prefixLength < shiftBoundary
        · exact (small_census power prefixLength prefix_pos prefix_small prefix_lt).mp counts_eq
        · have boundary_le : shiftBoundary ≤ prefixLength := by omega
          have shifted_pos : 0 < prefixLength - 2 := by omega
          have shifted_lt : prefixLength - 2 < 31 + 2 * power := by omega
          have recurrence := family.succ_prefix_count_eq_iff power (prefixLength - 2)
            (left_cut_before_shift prefixLength boundary_le)
            (right_cut_before_shift prefixLength boundary_le)
          rw [show prefixLength - 2 + 2 = prefixLength by omega] at recurrence
          have shifted_counts := recurrence.mp counts_eq
          have shifted_admissible :=
            (induction (prefixLength - 2)).mp ⟨shifted_pos, shifted_lt, shifted_counts⟩
          exact (admissible_shift power prefixLength boundary_le prefix_lt).mpr
            shifted_admissible
      · intro admissible
        have prefix_pos := admissibleBalancedPrefix_pos admissible
        have prefix_lt := admissibleBalancedPrefix_lt admissible
        refine ⟨prefix_pos, prefix_lt, ?_⟩
        by_cases prefix_small : prefixLength < shiftBoundary
        · exact (small_census power prefixLength prefix_pos prefix_small prefix_lt).mpr admissible
        · have boundary_le : shiftBoundary ≤ prefixLength := by omega
          have shifted_admissible :=
            (admissible_shift power prefixLength boundary_le prefix_lt).mp admissible
          have shifted_balanced := (induction (prefixLength - 2)).mpr shifted_admissible
          have recurrence := family.succ_prefix_count_eq_iff power (prefixLength - 2)
            (left_cut_before_shift prefixLength boundary_le)
            (right_cut_before_shift prefixLength boundary_le)
          rw [show prefixLength - 2 + 2 = prefixLength by omega] at recurrence
          exact recurrence.mpr shifted_balanced.2.2

theorem pumpAt_succ_take_eq_one
    {α : Type*} (base block : List α) (cut power prefixLength : ℕ)
    (cut_le : cut ≤ base.length) (prefix_le : prefixLength ≤ cut + block.length) :
    (pumpAt base cut block (power + 1)).take prefixLength =
      (pumpAt base cut block 1).take prefixLength := by
  have cut_take_length : (base.take cut).length = cut := by
    simp only [List.length_take]
    omega
  have common_length : (base.take cut ++ block).length = cut + block.length := by
    simp only [List.length_append, cut_take_length]
  have prefix_le_common : prefixLength ≤ (base.take cut ++ block).length := by
    omega
  have new_factorization :
      pumpAt base cut block (power + 1) =
        (base.take cut ++ block) ++ (repeatBlock block power ++ base.drop cut) := by
    simp only [pumpAt, repeatBlock, List.append_assoc]
  have one_factorization :
      pumpAt base cut block 1 = (base.take cut ++ block) ++ base.drop cut := by
    simp only [pumpAt, repeatBlock, List.nil_append, List.append_assoc]
  rw [new_factorization, one_factorization,
    List.take_append_of_le_length prefix_le_common,
    List.take_append_of_le_length prefix_le_common]

theorem pumpAt_add_take_eq
    {α : Type*} (base block : List α) (cut referencePower extraPower prefixLength : ℕ)
    (cut_le : cut ≤ base.length)
    (prefix_le : prefixLength ≤ cut + referencePower * block.length) :
    (pumpAt base cut block (referencePower + extraPower)).take prefixLength =
      (pumpAt base cut block referencePower).take prefixLength := by
  have cut_take_length : (base.take cut).length = cut := by
    simp only [List.length_take]
    omega
  have common_length :
      (base.take cut ++ repeatBlock block referencePower).length =
        cut + referencePower * block.length := by
    simp only [List.length_append, cut_take_length, repeatBlock_length]
  have prefix_le_common :
      prefixLength ≤ (base.take cut ++ repeatBlock block referencePower).length := by
    omega
  have long_factorization :
      pumpAt base cut block (referencePower + extraPower) =
        (base.take cut ++ repeatBlock block referencePower) ++
          (repeatBlock block extraPower ++ base.drop cut) := by
    simp only [pumpAt, repeatBlock_add, List.append_assoc]
  have reference_factorization :
      pumpAt base cut block referencePower =
        (base.take cut ++ repeatBlock block referencePower) ++ base.drop cut := by
    simp only [pumpAt, List.append_assoc]
  rw [long_factorization, reference_factorization,
    List.take_append_of_le_length prefix_le_common,
    List.take_append_of_le_length prefix_le_common]

end MatrixMortality.GuardedMixedPrimeFork
