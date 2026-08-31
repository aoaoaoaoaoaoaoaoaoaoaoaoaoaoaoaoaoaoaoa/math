import MatrixMortality.DecimalSetterSuffix

/-!
# Complete decimal hidden-branch separation

The physical blocks `R_b R_c D_b` and `D_b R_c D_b` have the same first carrier cylinder.
Their complete inverse branches nevertheless retain an exact one-step cross-prime gap. A common
outer inverse word shifts that gap without erasing it, while decoding one common current carrier
through both branches exposes the precise discrepancy required between their later tails.
-/

namespace MatrixMortality.DecimalSetterSuffix

open MatrixMortality.DecimalSetterArithmetic
open MatrixMortality.DecimalSetterCarry
open MatrixMortality.DecimalSetterChamber
open MatrixMortality.PadicValuation

private instance factPrimeFive : Fact (Nat.Prime 5) :=
  ⟨by norm_num⟩

private theorem div_ten_decimalUnit_of_shell
    {value : ℚ} (value_shell : HasDecimalShell value 1 1) :
    HasDecimalShell (value / 10) 0 0 := by
  exact
    ⟨by simpa using div_hasValue value_shell.1 ten_hasDecimalShell.1,
      by simpa using div_hasValue value_shell.2 ten_hasDecimalShell.2⟩

/-- The complete hidden-phase inverse branches remain separated at every common unit tail.
Their difference retains the one-step `2`/`5` depth asymmetry erased by the first-cylinder
projection. -/
theorem hiddenInverseBranches_sub_hasDecimalShell
    {β : Nat} (body : List TagLetter) {E G μ tail : ℚ}
    (E_unit : HasDecimalShell E 0 0)
    (G_unit : HasDecimalShell G 0 0)
    (mu_unit : HasDecimalShell μ 0 0)
    (upper_unit : HasDecimalShell (hiddenRuleUpperCode β : ℚ) 0 0)
    (rule_trace_shell :
      HasDecimalShell
        (E * hiddenRuleUpperCode β + G * hiddenRuleLowerCode β body) 1 1)
    (erase_trace_shell :
      HasDecimalShell
        (E * hiddenRuleUpperCode β + G * hiddenEraseLowerCode β body) 1 1)
    (tail_unit : HasDecimalShell tail 0 0) :
    HasDecimalShell
      (hiddenRuleInverseBranch β body E G μ tail -
        hiddenEraseInverseBranch β body E G μ tail)
      ((tagEncode β body).length + 4) ((tagEncode β body).length + 5) := by
  have lower_difference_shell :
      HasDecimalShell
        ((hiddenRuleLowerCode β body : ℚ) - hiddenEraseLowerCode β body)
        ((tagEncode β body).length + 5) ((tagEncode β body).length + 6) := by
    simpa [hiddenRuleLowerCode, hiddenEraseLowerCode] using
      hiddenBlocks_lowerCode_sub_hasDecimalShell β body
  unfold hiddenRuleInverseBranch hiddenEraseInverseBranch
  exact physicalInverseCarrier_sameUpper_sub_hasDecimalShell
    (show 1 ≤ 2 * β + 3 by omega) E_unit G_unit mu_unit upper_unit
      rule_trace_shell erase_trace_shell tail_unit lower_difference_shell

/-- Decoding one current unit through the two hidden-phase blocks produces tails whose exact
cross-prime gap begins immediately beyond the common lower suffix. -/
theorem hiddenForwardBranches_sub_hasDecimalShell
    {β : Nat} (body : List TagLetter) {E G μ current : ℚ}
    (E_unit : HasDecimalShell E 0 0)
    (G_unit : HasDecimalShell G 0 0)
    (mu_unit : HasDecimalShell μ 0 0)
    (current_unit : HasDecimalShell current 0 0) :
    HasDecimalShell
      (forwardCarrier (2 * β + 3) E
          ((E * hiddenRuleUpperCode β + G * hiddenRuleLowerCode β body) / 10)
          (μ * G * hiddenRuleLowerCode β body) current -
        forwardCarrier (2 * β + 3) E
          ((E * hiddenRuleUpperCode β + G * hiddenEraseLowerCode β body) / 10)
          (μ * G * hiddenEraseLowerCode β body) current)
      ((tagEncode β body).length - 2 * β + 1)
      ((tagEncode β body).length - 2 * β + 2) := by
  have lower_difference_shell :
      HasDecimalShell
        ((hiddenRuleLowerCode β body : ℚ) - hiddenEraseLowerCode β body)
        ((tagEncode β body).length + 5) ((tagEncode β body).length + 6) := by
    simpa [hiddenRuleLowerCode, hiddenEraseLowerCode] using
      hiddenBlocks_lowerCode_sub_hasDecimalShell β body
  apply physicalForwardCarrier_sameUpper_sub_hasDecimalShell
    E_unit G_unit mu_unit current_unit
  convert lower_difference_shell using 1
  · push_cast
    omega
  · push_cast
    omega

/-- If the two hidden inverse branches meet at possibly different unit tails, those tails have
the exact asymmetric discrepancy forced by branch switching. -/
theorem hiddenInverseBranches_eq_forces_tail_sub_hasDecimalShell
    {β : Nat} (body : List TagLetter) {E G μ ruleTail eraseTail : ℚ}
    (E_unit : HasDecimalShell E 0 0)
    (G_unit : HasDecimalShell G 0 0)
    (mu_unit : HasDecimalShell μ 0 0)
    (rule_trace_shell :
      HasDecimalShell
        (E * hiddenRuleUpperCode β + G * hiddenRuleLowerCode β body) 1 1)
    (erase_trace_shell :
      HasDecimalShell
        (E * hiddenRuleUpperCode β + G * hiddenEraseLowerCode β body) 1 1)
    (rule_tail_unit : HasDecimalShell ruleTail 0 0)
    (erase_tail_unit : HasDecimalShell eraseTail 0 0)
    (branches_eq :
      hiddenRuleInverseBranch β body E G μ ruleTail =
        hiddenEraseInverseBranch β body E G μ eraseTail) :
    HasDecimalShell (ruleTail - eraseTail)
      ((tagEncode β body).length - 2 * β + 1)
      ((tagEncode β body).length - 2 * β + 2) := by
  have rule_trace_unit :
      HasDecimalShell
        ((E * hiddenRuleUpperCode β + G * hiddenRuleLowerCode β body) / 10) 0 0 :=
    div_ten_decimalUnit_of_shell rule_trace_shell
  have erase_trace_unit :
      HasDecimalShell
        ((E * hiddenRuleUpperCode β + G * hiddenEraseLowerCode β body) / 10) 0 0 :=
    div_ten_decimalUnit_of_shell erase_trace_shell
  have rule_constant_unit :
      HasDecimalShell (μ * G * hiddenRuleLowerCode β body) 0 0 := by
    simpa only [zero_add] using
      (mu_unit.mul G_unit).mul (hiddenRuleLowerCode_decimalUnit β body)
  have erase_constant_unit :
      HasDecimalShell (μ * G * hiddenEraseLowerCode β body) 0 0 := by
    simpa only [zero_add] using
      (mu_unit.mul G_unit).mul (hiddenEraseLowerCode_decimalUnit β body)
  have current_unit :
      HasDecimalShell (hiddenRuleInverseBranch β body E G μ ruleTail) 0 0 := by
    unfold hiddenRuleInverseBranch
    exact inverseCarrier_hasDecimalShell (show 1 ≤ 2 * β + 3 by omega)
      E_unit rule_trace_unit rule_constant_unit rule_tail_unit
  have decoded_difference := hiddenForwardBranches_sub_hasDecimalShell (β := β) body
    E_unit G_unit mu_unit current_unit
  have rule_decoded :
      forwardCarrier (2 * β + 3) E
          ((E * hiddenRuleUpperCode β + G * hiddenRuleLowerCode β body) / 10)
          (μ * G * hiddenRuleLowerCode β body)
          (hiddenRuleInverseBranch β body E G μ ruleTail) = ruleTail := by
    unfold hiddenRuleInverseBranch
    exact forwardCarrier_inverseCarrier (show 1 ≤ 2 * β + 3 by omega)
      E_unit rule_trace_unit rule_constant_unit rule_tail_unit
  have erase_decoded :
      forwardCarrier (2 * β + 3) E
          ((E * hiddenRuleUpperCode β + G * hiddenEraseLowerCode β body) / 10)
          (μ * G * hiddenEraseLowerCode β body)
          (hiddenRuleInverseBranch β body E G μ ruleTail) = eraseTail := by
    rw [branches_eq]
    unfold hiddenEraseInverseBranch
    exact forwardCarrier_inverseCarrier (show 1 ≤ 2 * β + 3 by omega)
      E_unit erase_trace_unit erase_constant_unit erase_tail_unit
  rw [rule_decoded, erase_decoded] at decoded_difference
  exact decoded_difference

/-- The complete hidden-phase branches are pointwise distinct on decimal-unit tails. -/
theorem hiddenInverseBranches_ne
    {β : Nat} (body : List TagLetter) {E G μ tail : ℚ}
    (E_unit : HasDecimalShell E 0 0)
    (G_unit : HasDecimalShell G 0 0)
    (mu_unit : HasDecimalShell μ 0 0)
    (upper_unit : HasDecimalShell (hiddenRuleUpperCode β : ℚ) 0 0)
    (rule_trace_shell :
      HasDecimalShell
        (E * hiddenRuleUpperCode β + G * hiddenRuleLowerCode β body) 1 1)
    (erase_trace_shell :
      HasDecimalShell
        (E * hiddenRuleUpperCode β + G * hiddenEraseLowerCode β body) 1 1)
    (tail_unit : HasDecimalShell tail 0 0) :
    hiddenRuleInverseBranch β body E G μ tail ≠
      hiddenEraseInverseBranch β body E G μ tail := by
  have difference_shell := hiddenInverseBranches_sub_hasDecimalShell body
    E_unit G_unit mu_unit upper_unit rule_trace_shell erase_trace_shell tail_unit
  exact sub_ne_zero.mp difference_shell.1.1

/-- Any common outer inverse word preserves the hidden-phase separation and adds its total
shift to both depths. Thus two complete addresses differing only at the hidden phase remain
distinct when their later tail and earlier blocks agree. -/
theorem hiddenInverseBranches_pullbackWord_sub_hasDecimalShell
    (outer : List BackwardBlock) {β : Nat} (body : List TagLetter) {E G μ tail : ℚ}
    (E_unit : HasDecimalShell E 0 0)
    (G_unit : HasDecimalShell G 0 0)
    (mu_unit : HasDecimalShell μ 0 0)
    (upper_unit : HasDecimalShell (hiddenRuleUpperCode β : ℚ) 0 0)
    (rule_trace_shell :
      HasDecimalShell
        (E * hiddenRuleUpperCode β + G * hiddenRuleLowerCode β body) 1 1)
    (erase_trace_shell :
      HasDecimalShell
        (E * hiddenRuleUpperCode β + G * hiddenEraseLowerCode β body) 1 1)
    (tail_unit : HasDecimalShell tail 0 0) :
    HasDecimalShell
      (BackwardBlock.pullbackWord outer (hiddenRuleInverseBranch β body E G μ tail) -
        BackwardBlock.pullbackWord outer (hiddenEraseInverseBranch β body E G μ tail))
      ((tagEncode β body).length + 4 + BackwardBlock.totalShift outer)
      ((tagEncode β body).length + 5 + BackwardBlock.totalShift outer) := by
  have rule_trace_unit :
      HasDecimalShell
        ((E * hiddenRuleUpperCode β + G * hiddenRuleLowerCode β body) / 10) 0 0 :=
    div_ten_decimalUnit_of_shell rule_trace_shell
  have erase_trace_unit :
      HasDecimalShell
        ((E * hiddenRuleUpperCode β + G * hiddenEraseLowerCode β body) / 10) 0 0 :=
    div_ten_decimalUnit_of_shell erase_trace_shell
  have rule_constant_unit :
      HasDecimalShell (μ * G * hiddenRuleLowerCode β body) 0 0 := by
    simpa only [zero_add] using
      (mu_unit.mul G_unit).mul (hiddenRuleLowerCode_decimalUnit β body)
  have erase_constant_unit :
      HasDecimalShell (μ * G * hiddenEraseLowerCode β body) 0 0 := by
    simpa only [zero_add] using
      (mu_unit.mul G_unit).mul (hiddenEraseLowerCode_decimalUnit β body)
  have rule_branch_unit :
      HasDecimalShell (hiddenRuleInverseBranch β body E G μ tail) 0 0 := by
    unfold hiddenRuleInverseBranch
    exact inverseCarrier_hasDecimalShell (show 1 ≤ 2 * β + 3 by omega)
      E_unit rule_trace_unit rule_constant_unit tail_unit
  have erase_branch_unit :
      HasDecimalShell (hiddenEraseInverseBranch β body E G μ tail) 0 0 := by
    unfold hiddenEraseInverseBranch
    exact inverseCarrier_hasDecimalShell (show 1 ≤ 2 * β + 3 by omega)
      E_unit erase_trace_unit erase_constant_unit tail_unit
  have branch_difference := hiddenInverseBranches_sub_hasDecimalShell body
    E_unit G_unit mu_unit upper_unit rule_trace_shell erase_trace_shell tail_unit
  exact BackwardBlock.pullbackWord_sub_hasDecimalShell outer
    rule_branch_unit erase_branch_unit branch_difference

/-- At the physical decimal calibration, every common outer word and common unit tail preserve
the hidden-phase distinction. The exact one-step cross-prime gap survives at unbounded composed
depth. -/
theorem emittedHiddenInverseBranches_pullbackWord_sub_hasDecimalShell
    (outer : List BackwardBlock) {β : Nat} (body : List TagLetter) {tail : ℚ}
    (beta_large : 2 ≤ β)
    (tail_unit : HasDecimalShell tail 0 0) :
    HasDecimalShell
      (BackwardBlock.pullbackWord outer (emittedHiddenRuleInverseBranch β body tail) -
        BackwardBlock.pullbackWord outer (emittedHiddenEraseInverseBranch β body tail))
      ((tagEncode β body).length + 4 + BackwardBlock.totalShift outer)
      ((tagEncode β body).length + 5 + BackwardBlock.totalShift outer) := by
  obtain ⟨gap_unit, lift_unit, marker_unit, upper_unit⟩ :=
    hiddenBlocks_calibrated_decimalUnits beta_large
  obtain ⟨rule_trace_shell, erase_trace_shell⟩ :=
    hiddenBlocks_trace_hasDecimalShell body beta_large
  have rule_trace_shell' :
      HasDecimalShell
        ((decimalGap ((10 : ℤ) ^ β) : ℚ) * hiddenRuleUpperCode β +
          (decimalLift ((10 : ℤ) ^ β) : ℚ) * hiddenRuleLowerCode β body) 1 1 := by
    simpa [transferTrace] using rule_trace_shell
  have erase_trace_shell' :
      HasDecimalShell
        ((decimalGap ((10 : ℤ) ^ β) : ℚ) * hiddenRuleUpperCode β +
          (decimalLift ((10 : ℤ) ^ β) : ℚ) * hiddenEraseLowerCode β body) 1 1 := by
    simpa [transferTrace] using erase_trace_shell
  unfold emittedHiddenRuleInverseBranch emittedHiddenEraseInverseBranch
  exact hiddenInverseBranches_pullbackWord_sub_hasDecimalShell outer body
    gap_unit lift_unit marker_unit upper_unit rule_trace_shell' erase_trace_shell' tail_unit

/-- Physical complete addresses with the same outer word and later unit tail cannot identify the
two hidden-phase blocks. -/
theorem emittedHiddenInverseBranches_pullbackWord_ne
    (outer : List BackwardBlock) {β : Nat} (body : List TagLetter) {tail : ℚ}
    (beta_large : 2 ≤ β)
    (tail_unit : HasDecimalShell tail 0 0) :
    BackwardBlock.pullbackWord outer (emittedHiddenRuleInverseBranch β body tail) ≠
      BackwardBlock.pullbackWord outer (emittedHiddenEraseInverseBranch β body tail) := by
  have difference_shell :=
    emittedHiddenInverseBranches_pullbackWord_sub_hasDecimalShell
      outer body beta_large tail_unit
  exact sub_ne_zero.mp difference_shell.1.1

/-- If complete physical addresses with a common outer word switch between the hidden blocks,
equality forces an exact asymmetric discrepancy between their later tails. -/
theorem emittedHiddenInverseBranches_pullbackWord_eq_forces_tail_sub_hasDecimalShell
    (outer : List BackwardBlock) {β : Nat} (body : List TagLetter)
    {ruleTail eraseTail : ℚ}
    (beta_large : 2 ≤ β)
    (rule_tail_unit : HasDecimalShell ruleTail 0 0)
    (erase_tail_unit : HasDecimalShell eraseTail 0 0)
    (addresses_eq :
      BackwardBlock.pullbackWord outer (emittedHiddenRuleInverseBranch β body ruleTail) =
        BackwardBlock.pullbackWord outer
          (emittedHiddenEraseInverseBranch β body eraseTail)) :
    HasDecimalShell (ruleTail - eraseTail)
      ((tagEncode β body).length - 2 * β + 1)
      ((tagEncode β body).length - 2 * β + 2) := by
  obtain ⟨gap_unit, lift_unit, marker_unit, upper_unit⟩ :=
    hiddenBlocks_calibrated_decimalUnits beta_large
  obtain ⟨rule_trace_shell, erase_trace_shell⟩ :=
    hiddenBlocks_trace_hasDecimalShell body beta_large
  have rule_trace_shell' :
      HasDecimalShell
        ((decimalGap ((10 : ℤ) ^ β) : ℚ) * hiddenRuleUpperCode β +
          (decimalLift ((10 : ℤ) ^ β) : ℚ) * hiddenRuleLowerCode β body) 1 1 := by
    simpa [transferTrace] using rule_trace_shell
  have erase_trace_shell' :
      HasDecimalShell
        ((decimalGap ((10 : ℤ) ^ β) : ℚ) * hiddenRuleUpperCode β +
          (decimalLift ((10 : ℤ) ^ β) : ℚ) * hiddenEraseLowerCode β body) 1 1 := by
    simpa [transferTrace] using erase_trace_shell
  have rule_trace_unit := div_ten_decimalUnit_of_shell rule_trace_shell'
  have erase_trace_unit := div_ten_decimalUnit_of_shell erase_trace_shell'
  have rule_constant_unit :
      HasDecimalShell
        ((code (nearyMarker β) : ℚ) * decimalLift ((10 : ℤ) ^ β) *
          hiddenRuleLowerCode β body) 0 0 := by
    simpa only [zero_add] using
      (marker_unit.mul lift_unit).mul (hiddenRuleLowerCode_decimalUnit β body)
  have erase_constant_unit :
      HasDecimalShell
        ((code (nearyMarker β) : ℚ) * decimalLift ((10 : ℤ) ^ β) *
          hiddenEraseLowerCode β body) 0 0 := by
    simpa only [zero_add] using
      (marker_unit.mul lift_unit).mul (hiddenEraseLowerCode_decimalUnit β body)
  have rule_branch_unit :
      HasDecimalShell (emittedHiddenRuleInverseBranch β body ruleTail) 0 0 := by
    unfold emittedHiddenRuleInverseBranch hiddenRuleInverseBranch
    exact inverseCarrier_hasDecimalShell (show 1 ≤ 2 * β + 3 by omega)
      gap_unit rule_trace_unit rule_constant_unit rule_tail_unit
  have erase_branch_unit :
      HasDecimalShell (emittedHiddenEraseInverseBranch β body eraseTail) 0 0 := by
    unfold emittedHiddenEraseInverseBranch hiddenEraseInverseBranch
    exact inverseCarrier_hasDecimalShell (show 1 ≤ 2 * β + 3 by omega)
      gap_unit erase_trace_unit erase_constant_unit erase_tail_unit
  have branches_eq := BackwardBlock.pullbackWord_injective_of_decimalUnits outer
    rule_branch_unit erase_branch_unit addresses_eq
  have branches_eq' :
      hiddenRuleInverseBranch β body
          (decimalGap ((10 : ℤ) ^ β)) (decimalLift ((10 : ℤ) ^ β))
            (code (nearyMarker β)) ruleTail =
        hiddenEraseInverseBranch β body
          (decimalGap ((10 : ℤ) ^ β)) (decimalLift ((10 : ℤ) ^ β))
            (code (nearyMarker β)) eraseTail := by
    simpa [emittedHiddenRuleInverseBranch, emittedHiddenEraseInverseBranch] using branches_eq
  exact hiddenInverseBranches_eq_forces_tail_sub_hasDecimalShell body
    gap_unit lift_unit marker_unit rule_trace_shell' erase_trace_shell'
      rule_tail_unit erase_tail_unit branches_eq'

end MatrixMortality.DecimalSetterSuffix
