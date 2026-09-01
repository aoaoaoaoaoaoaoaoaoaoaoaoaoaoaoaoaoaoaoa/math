import MatrixMortality.DecimalSetterThreeBlockLongSupport
import MatrixMortality.DecimalSetterTwoBlockSingleton

namespace MatrixMortality.DecimalSetterBridgeRay

open MatrixMortality.DecimalSetterAncestry
open MatrixMortality.DecimalSetterArithmetic
open MatrixMortality.DecimalSetterBridge
open MatrixMortality.DecimalSetterCarry
open MatrixMortality.DecimalSetterChamber
open MatrixMortality.DecimalSetterDepth
open MatrixMortality.DecimalSetterMatrix

/-- A long `c b` three-block singleton pole collapses to the corresponding two-block pole. -/
theorem singletonPole_threeBlock_ruleCRoot_long_cb_forces_twoBlockPole
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current next : List NearyTile}
    (current_multi : 2 ≤ current.length) (current_ends : EndsInErase current)
    (next_multi : 2 ≤ next.length) (next_ends : EndsInErase next)
    (current_long : β + 3 ≤ (spell (nearyUpper β) current).length)
    {tail : List TagLetter}
    (next_letters : next.map NearyTile.letter = .c :: .b :: tail)
    (pole : HitsSquarePole β body [.erase targetLetter]
      [current, next, DecimalSetterMinimumBody.ruleCRoot]) :
    HitsSquarePole β body [.erase targetLetter]
      [current, DecimalSetterMinimumBody.ruleCRoot] := by
  have β_pos : 0 < β := by omega
  let upperWord := spell (nearyUpper β) next ++ nearyMarker β
  let lowerWord := spell (nearyLower β body) next
  let k := (spell (nearyUpper β) next).length
  let width := k - 1
  let Hn := code (front width upperWord)
  let δ := upperBoundaryCode β next - lowerBoundaryCode β body next
  let E := gap ((10 : ℚ) ^ β)
  let G := lift ((10 : ℚ) ^ β)
  let μ := DecimalSetterMatrix.marker β
  let T := boundaryTrace β body current
  let V := lowerBoundaryCode β body current
  let P := upperBoundaryCode β current
  let A := upperScale β current
  let B := upperScale β next
  let S := singletonTrace β targetLetter
  let q : ℚ := gapFactor β
  have suffix_data := singletonPole_threeBlock_ruleCRoot_long_suffix
    β_large body targetLetter current_multi current_ends next_multi next_ends current_long pole
  change lowerWord.length = width ∧ back width upperWord = lowerWord ∧
    code upperWord - code lowerWord = Hn * 10 ^ width ∧
      HasDecimalShell (Hn : ℚ) 0 0 at suffix_data
  have discrepancy_pos : code lowerWord < code upperWord := by
    have rational := singletonPole_threeBlock_ruleCRoot_discrepancy_pos
      β_large body targetLetter current_ends pole
    change (code lowerWord : ℚ) < code upperWord at rational
    exact_mod_cast rational
  have difference_cast :
      (((code upperWord - code lowerWord : Nat) : ℚ)) =
        (code upperWord : ℚ) - code lowerWord := by
    rw [Nat.cast_sub discrepancy_pos.le]
  have δ_eq : δ = (Hn : ℚ) * (10 : ℚ) ^ width := by
    change (code upperWord : ℚ) - code lowerWord =
      (Hn : ℚ) * (10 : ℚ) ^ width
    rw [← difference_cast, suffix_data.2.2.1]
    norm_num
  have next_length_le_upper : next.length ≤ k := by
    dsimp only [k]
    rw [spell_nearyUpper]
    simpa using DecimalSetterChamber.length_le_tagEncode β (next.map NearyTile.letter)
  have k_two_le : 2 ≤ k := next_multi.trans next_length_le_upper
  have k_eq : k = width + 1 := by omega
  have B_eq : B = (10 : ℚ) ^ (width + 1) := by
    simp only [B, upperScale, k_eq, k]
  have exact_equation :=
    (hitsSquarePole_singleton_pair_ruleCRoot_iff_discrepancyEquation
      β_pos body targetLetter current next).mp pole
  change δ * (T * S - 7 * E * μ * G * A) = G * V * B * μ * S at exact_equation
  rw [δ_eq, B_eq] at exact_equation
  have power_ne : (10 : ℚ) ^ width ≠ 0 := pow_ne_zero _ (by norm_num)
  have core :
      (Hn : ℚ) * (T * S - 7 * E * μ * G * A) =
        10 * G * V * μ * S := by
    apply mul_left_cancel₀ power_ne
    linear_combination exact_equation
  have next_nonempty : next ≠ [] := by
    intro next_nil
    simp [next_nil] at next_multi
  have head_eq : Hn = code (terminalHeadWord β) := by
    dsimp only [Hn, width, upperWord]
    rw [front_punctuatedUpper_eq_peeledHeadWord β next_nonempty]
    rw [next_letters]
    simp [peeledHeadWord, punctuatedUpper, tagEncode_cons, tagCode,
      terminalHeadWord, markerWord]
  rw [head_eq] at core
  let H : ℚ := code (terminalHeadWord β)
  change H * (T * S - 7 * E * μ * G * A) =
    10 * G * V * μ * S at core
  have H_eq : 9 * H = G := by
    dsimp only [H, G]
    rw [terminalHeadWord_code_eq]
    unfold terminalPrefix
    ring
  have H_complement : H - 10 * μ = -q := by
    have integer_relation := terminalHead_sub_ten_marker_eq_neg_gapFactor β
    dsimp only [H, μ, DecimalSetterMatrix.marker, q]
    exact_mod_cast integer_relation
  have E_eq : E = 9 * q := by
    simp [E, q, gap, gapFactor]
  have T_eq : T = E * P + G * V := by
    rfl
  have factorized :
      G * q * (S * (P - V) - 7 * μ * G * A) = 0 := by
    rw [T_eq] at core
    have raw :
        H * ((E * P + G * V) * S - 7 * E * μ * G * A) -
            10 * G * V * μ * S = 0 := sub_eq_zero.mpr core
    rw [E_eq] at raw
    calc
      G * q * (S * (P - V) - 7 * μ * G * A) =
          9 * H * q * (S * (P - V) - 7 * μ * G * A) := by rw [H_eq]
      _ = H * ((9 * q * P + G * V) * S - 7 * (9 * q) * μ * G * A) -
          10 * G * V * μ * S := by
            rw [show G = 9 * H by linarith [H_eq]]
            rw [show q = 10 * μ - H by linarith [H_complement]]
            ring
      _ = 0 := raw
  have G_ne : G ≠ 0 := (lift_tenPow_hasDecimalShell β_pos).1.1
  have q_ne : q ≠ 0 := by
    have q_pos : 0 < (gapFactor β : ℚ) := by
      exact_mod_cast gapFactor_pos β_pos
    exact ne_of_gt q_pos
  have discrepancy_eq : S * (P - V) = 7 * μ * G * A := by
    have inner_zero : S * (P - V) - 7 * μ * G * A = 0 := by
      rcases mul_eq_zero.mp factorized with Gq_zero | inner_zero
      · exact False.elim <| (mul_ne_zero G_ne q_ne) Gq_zero
      · exact inner_zero
    exact sub_eq_zero.mp inner_zero
  apply (hitsSquarePole_singleton_ruleCRoot_iff_traceDiscrepancy
    β_pos body targetLetter current).mpr
  simpa only [S, P, V, μ, G, A] using discrepancy_eq

/-- The entire long `c b` three-block chamber is empty. -/
theorem singletonPole_threeBlock_ruleCRoot_long_cb_impossible
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current next : List NearyTile}
    (current_multi : 2 ≤ current.length) (current_ends : EndsInErase current)
    (next_multi : 2 ≤ next.length) (next_ends : EndsInErase next)
    (current_long : β + 3 ≤ (spell (nearyUpper β) current).length)
    {tail : List TagLetter}
    (next_letters : next.map NearyTile.letter = .c :: .b :: tail) :
    ¬HitsSquarePole β body [.erase targetLetter]
      [current, next, DecimalSetterMinimumBody.ruleCRoot] := by
  intro pole
  have two_block_pole :=
    singletonPole_threeBlock_ruleCRoot_long_cb_forces_twoBlockPole
      β_large body targetLetter current_multi current_ends next_multi next_ends current_long
        next_letters pole
  have source_law : BlocksLaw [current, DecimalSetterMinimumBody.ruleCRoot] := by
    refine ⟨current_ends, ?_⟩
    exact ⟨[], .c, rfl⟩
  exact singletonTarget_twoBlockSource_impossible
    β_large body targetLetter source_law two_block_pole

end MatrixMortality.DecimalSetterBridgeRay
