import MatrixMortality.DecimalSetterGapCleanAncestry
import MatrixMortality.DecimalSetterThreeBlockSingleton

namespace MatrixMortality.DecimalSetterBridgeRay

open MatrixMortality.DecimalSetterAncestry
open MatrixMortality.DecimalSetterArithmetic
open MatrixMortality.DecimalSetterBridge
open MatrixMortality.DecimalSetterCarry
open MatrixMortality.DecimalSetterChamber
open MatrixMortality.DecimalSetterDepth
open MatrixMortality.DecimalSetterMatrix

theorem singletonPole_threeBlock_ruleCRoot_long_normalizedQuotient_eq
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current next : List NearyTile}
    (current_multi : 2 ≤ current.length) (current_ends : EndsInErase current)
    (next_multi : 2 ≤ next.length) (next_ends : EndsInErase next)
    (current_long : β + 3 ≤ (spell (nearyUpper β) current).length)
    (pole : HitsSquarePole β body [.erase targetLetter]
      [current, next, DecimalSetterMinimumBody.ruleCRoot]) :
    ((parsedRay β body [next, DecimalSetterMinimumBody.ruleCRoot]).2 /
        (parsedRay β body [next, DecimalSetterMinimumBody.ruleCRoot]).1) / 10 =
      (code (nearyMarker β) : ℚ) /
        code (peeledHeadWord β (next.map NearyTile.letter)) := by
  have β_pos : 0 < β := by omega
  let upperWord := spell (nearyUpper β) next ++ nearyMarker β
  let lowerWord := spell (nearyLower β body) next
  let k := (spell (nearyUpper β) next).length
  let width := k - 1
  let P := code upperWord
  let V := code lowerWord
  let H := code (front width upperWord)
  let M := code (nearyMarker β)
  let δ := upperBoundaryCode β next - lowerBoundaryCode β body next
  have suffix := singletonPole_threeBlock_ruleCRoot_long_suffix
    β_large body targetLetter current_multi current_ends next_multi next_ends current_long pole
  change lowerWord.length = width ∧ back width upperWord = lowerWord ∧
    P - V = H * 10 ^ width ∧ HasDecimalShell (H : ℚ) 0 0 at suffix
  have H_ne_nat : H ≠ 0 := by
    exact_mod_cast suffix.2.2.2.1.1
  have H_ne : (H : ℚ) ≠ 0 := by exact_mod_cast H_ne_nat
  have discrepancy_pos : V < P := by
    have rational := singletonPole_threeBlock_ruleCRoot_discrepancy_pos
      β_large body targetLetter current_ends pole
    change (V : ℚ) < P at rational
    exact_mod_cast rational
  have difference_cast : (((P - V : Nat) : ℚ)) = (P : ℚ) - V := by
    rw [Nat.cast_sub discrepancy_pos.le]
  have δ_eq : δ = (H : ℚ) * (10 : ℚ) ^ width := by
    change (P : ℚ) - V = (H : ℚ) * (10 : ℚ) ^ width
    rw [← difference_cast, suffix.2.2.1]
    norm_num
  have next_length_le_upper : next.length ≤ k := by
    dsimp only [k]
    rw [spell_nearyUpper]
    simpa using DecimalSetterChamber.length_le_tagEncode β (next.map NearyTile.letter)
  have k_two_le : 2 ≤ k := next_multi.trans next_length_le_upper
  have k_eq : k = width + 1 := by omega
  have scale_eq : upperScale β next = (10 : ℚ) ^ (width + 1) := by
    simp only [upperScale, k_eq, k]
  have ratio_eq :
      (parsedRay β body [next, DecimalSetterMinimumBody.ruleCRoot]).2 /
          (parsedRay β body [next, DecimalSetterMinimumBody.ruleCRoot]).1 =
        upperScale β next * DecimalSetterMatrix.marker β / δ := by
    exact parsedRay_pair_ruleCRoot_ratio_eq β_pos body next (by
      change δ ≠ 0
      rw [δ_eq]
      positivity)
  have next_nonempty : next ≠ [] := by
    intro next_nil
    simp [next_nil] at next_multi
  have head_eq : H = code (peeledHeadWord β (next.map NearyTile.letter)) := by
    dsimp only [H, width, upperWord]
    rw [front_punctuatedUpper_eq_peeledHeadWord β next_nonempty]
  rw [ratio_eq, scale_eq, δ_eq]
  change
    ((10 : ℚ) ^ (width + 1) * (M : ℚ) /
        ((H : ℚ) * (10 : ℚ) ^ width)) / 10 =
      (M : ℚ) / code (peeledHeadWord β (next.map NearyTile.letter))
  rw [← head_eq]
  field_simp [H_ne]
  ring

theorem singletonPole_threeBlock_ruleCRoot_long_reducedNumerator_coprime_gapFactor
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current next : List NearyTile}
    (current_multi : 2 ≤ current.length) (current_ends : EndsInErase current)
    (next_multi : 2 ≤ next.length) (next_ends : EndsInErase next)
    (current_long : β + 3 ≤ (spell (nearyUpper β) current).length)
    (pole : HitsSquarePole β body [.erase targetLetter]
      [current, next, DecimalSetterMinimumBody.ruleCRoot]) :
    IsCoprime (gapFactor β)
      ((((parsedRay β body [next, DecimalSetterMinimumBody.ruleCRoot]).2 /
        (parsedRay β body [next, DecimalSetterMinimumBody.ruleCRoot]).1) / 10).num) := by
  let M : ℤ := code (nearyMarker β)
  let H : ℤ := code (peeledHeadWord β (next.map NearyTile.letter))
  let reduced :=
    ((parsedRay β body [next, DecimalSetterMinimumBody.ruleCRoot]).2 /
      (parsedRay β body [next, DecimalSetterMinimumBody.ruleCRoot]).1) / 10
  have formula := singletonPole_threeBlock_ruleCRoot_long_normalizedQuotient_eq
    β_large body targetLetter current_multi current_ends next_multi next_ends current_long pole
  have reduced_eq : reduced = (M : ℚ) / H := by
    simpa only [reduced, M, H, Int.cast_natCast] using formula
  have H_ne : H ≠ 0 := by
    let upperWord := spell (nearyUpper β) next ++ nearyMarker β
    let width := (spell (nearyUpper β) next).length - 1
    have suffix := singletonPole_threeBlock_ruleCRoot_long_suffix
      β_large body targetLetter current_multi current_ends next_multi next_ends current_long pole
    have head_unit :
        HasDecimalShell (code (front width upperWord) : ℚ) 0 0 := by
      simpa only [upperWord, width] using suffix.2.2.2
    have next_nonempty : next ≠ [] := by
      intro next_nil
      simp [next_nil] at next_multi
    have head_eq :
        front width upperWord = peeledHeadWord β (next.map NearyTile.letter) := by
      simpa only [upperWord, width] using
        front_punctuatedUpper_eq_peeledHeadWord β next_nonempty
    rw [head_eq] at head_unit
    dsimp only [H]
    exact_mod_cast head_unit.1.1
  obtain ⟨common, numerator_eq, _⟩ :=
    Rat.exists_eq_mul_div_num_and_eq_mul_div_den M H_ne
  rw [← reduced_eq] at numerator_eq
  have reduced_dvd : reduced.num ∣ M := by
    refine ⟨common, ?_⟩
    rw [numerator_eq]
    ring
  have marker_coprime : IsCoprime (gapFactor β) M := by
    simpa only [M] using gapFactor_coprime_marker (by omega : 0 < β)
  exact IsCoprime.of_isCoprime_of_dvd_right marker_coprime reduced_dvd

theorem singletonPole_threeBlock_ruleCRoot_long_no_gapCleanIntegralCarrier
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current next : List NearyTile}
    (current_multi : 2 ≤ current.length) (current_ends : EndsInErase current)
    (next_multi : 2 ≤ next.length) (next_ends : EndsInErase next)
    (current_long : β + 3 ≤ (spell (nearyUpper β) current).length)
    (pole : HitsSquarePole β body [.erase targetLetter]
      [current, next, DecimalSetterMinimumBody.ruleCRoot]) :
    ¬∃ N D Nprev : ℤ,
      HasDecimalShell (N : ℚ) 0 0 ∧
        HasDecimalShell (D : ℚ) 0 0 ∧
          HasDecimalShell (Nprev : ℚ) 0 0 ∧
            D = decimalGap ((10 : ℤ) ^ β) * Nprev ∧
              IsCoprime (gapFactor β) N ∧
                RepresentsPeeledCarrier β
                  (parsedRay β body [next, DecimalSetterMinimumBody.ruleCRoot]) N D := by
  intro clean_carrier
  have β_pos : 0 < β := by omega
  have discrepancy_shell :=
    (singletonPole_threeBlock_ruleCRoot_multi_long_iff_discrepancyShell
      β_large body targetLetter current_multi current_ends next_ends pole).mp current_long
  have ancestry :=
    (pair_ruleCRoot_admitsUnitPeeledCarrier_iff_discrepancyShell β_pos body next).mpr
      discrepancy_shell
  have ratio_shell :
      HasDecimalShell
        ((parsedRay β body [next, DecimalSetterMinimumBody.ruleCRoot]).2 /
          (parsedRay β body [next, DecimalSetterMinimumBody.ruleCRoot]).1) 1 1 :=
    ((admitsUnitPeeledCarrier_iff_ratio_hasDecimalShell β_pos
      (parsedRay β body [next, DecimalSetterMinimumBody.ruleCRoot])).mp ancestry).2
  have numerator_dvd :
      gapFactor β ∣
        ((((parsedRay β body [next, DecimalSetterMinimumBody.ruleCRoot]).2 /
          (parsedRay β body [next, DecimalSetterMinimumBody.ruleCRoot]).1) / 10).num) :=
    (exists_gapCleanIntegralPeeledCarrier_iff_gapFactor_dvd_reducedNumerator
      β_pos (parsedRay β body [next, DecimalSetterMinimumBody.ruleCRoot]) ratio_shell).mp
        clean_carrier
  have numerator_coprime :=
    singletonPole_threeBlock_ruleCRoot_long_reducedNumerator_coprime_gapFactor
      β_large body targetLetter current_multi current_ends next_multi next_ends current_long pole
  have gap_unit := numerator_coprime.isUnit_of_dvd numerator_dvd
  have gap_gt_one : (1 : ℤ) < gapFactor β := by
    obtain ⟨offset, β_eq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt β_pos)
    rw [β_eq, gapFactor, pow_succ]
    have power_pos : (0 : ℤ) < 10 ^ offset := pow_pos (by norm_num) offset
    nlinarith
  rw [Int.isUnit_iff] at gap_unit
  omega

end MatrixMortality.DecimalSetterBridgeRay
