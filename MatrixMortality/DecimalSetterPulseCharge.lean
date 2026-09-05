import MatrixMortality.NearyPulseCharge
import MatrixMortality.DecimalSetterThreeBlockSingletonNext

/-!
# Compiler-congruence extinction of peeled decimal heads

The exact suffix equality behind a decimal-unit peel leaves a one-pulse head
of length `β + 2`. Its pulse charge differs by one from the terminal marker.
The Neary body-length congruence therefore excludes the entire peeled-word
language, including both the `c b` and `c c` heads. Applied to the three-block
singleton classifier, this removes every long current above the `R_c` root.
-/

namespace MatrixMortality.DecimalSetterBridgeRay

open MatrixMortality.DecimalSetterArithmetic
open MatrixMortality.DecimalSetterBridge
open MatrixMortality.DecimalSetterCarry
open MatrixMortality.DecimalSetterChamber
open MatrixMortality.DecimalSetterDepth
open MatrixMortality.PadicValuation

/-- No physical word on the compiler's congruence class has its complete lower
spelling as the suffix left by a decimal-unit `β + 2`-digit upper peel. -/
theorem peeledSuffix_compilerCongruence_impossible
    {β : Nat} (β_large : 3 ≤ β) {body : List TagLetter}
    (body_divisible : β - 1 ∣ body.length) {word : List NearyTile}
    (upper_long : 2 ≤ (spell (nearyUpper β) word).length)
    (head_unit :
      HasDecimalShell (code (peeledHeadWord β (word.map NearyTile.letter)) : ℚ) 0 0) :
    back ((spell (nearyUpper β) word).length - 1)
      (spell (nearyUpper β) word ++ nearyMarker β) ≠
        spell (nearyLower β body) word := by
  intro suffix_eq
  have word_ne : word ≠ [] := by
    intro word_nil
    simp [word_nil, spell] at upper_long
  have decomposition := front_append_back ((spell (nearyUpper β) word).length - 1)
    (spell (nearyUpper β) word ++ nearyMarker β)
  rw [front_punctuatedUpper_eq_peeledHeadWord β word_ne, suffix_eq] at decomposition
  have encoded_long : 2 ≤ (tagEncode β (word.map NearyTile.letter)).length := by
    simpa only [spell_nearyUpper] using upper_long
  rcases peeledHead_trichotomy encoded_long with leading_b | cb | cc
  · obtain ⟨tail, _, head_eq⟩ := leading_b
    exact bTag_not_decimalUnit β (head_eq ▸ head_unit)
  · obtain ⟨tail, _, head_eq⟩ := cb
    have matching := decomposition.symm
    rw [head_eq] at matching
    exact shifted_neary_match_onePulse_impossible (by omega) body_divisible word
      (ones := 2) (zeros := β) (by omega) (by omega)
      (by simpa only [terminalHeadWord, List.replicate_succ,
        List.replicate_zero, List.cons_append, List.nil_append] using matching)
  · obtain ⟨tail, _, letters_eq, _, _⟩ := cc
    have double_unit :
        HasDecimalShell (code (peeledHeadWord β (.c :: .c :: tail)) : ℚ) 0 0 := by
      simpa only [letters_eq] using head_unit
    obtain ⟨zeros, zeros_pos, zeros_le, shape, _⟩ :=
      peeledDoubleCHead_unit_shape tail (by omega) double_unit
    have matching := decomposition.symm
    rw [letters_eq, shape] at matching
    exact shifted_neary_match_onePulse_impossible (by omega) body_divisible word
      (by omega) (by omega) matching

/-- A positive raw discrepancy cannot have the equal-depth shell required to
enter the multi-role pole class one step above `R_c`. -/
theorem positiveDiscrepancy_equalDepth_impossible
    {β : Nat} (β_large : 3 ≤ β) {body : List TagLetter}
    (body_divisible : β - 1 ∣ body.length) {word : List NearyTile}
    (upper_long : 2 ≤ (spell (nearyUpper β) word).length)
    (difference_pos : lowerBoundaryCode β body word < upperBoundaryCode β word) :
    ¬HasDecimalShell (upperBoundaryCode β word - lowerBoundaryCode β body word)
      (((spell (nearyUpper β) word).length : ℤ) - 1)
      (((spell (nearyUpper β) word).length : ℤ) - 1) := by
  intro difference_shell
  let upper := spell (nearyUpper β) word ++ nearyMarker β
  let lower := spell (nearyLower β body) word
  let width := (spell (nearyUpper β) word).length - 1
  have width_pos : 0 < width := by dsimp [width]; omega
  have width_lt : width < upper.length := by
    simp [upper, width, nearyMarker]
    omega
  have difference_pos_nat : code lower < code upper := by
    have cast_pos : (code lower : ℚ) < code upper := difference_pos
    exact_mod_cast cast_pos
  have shell : HasDecimalShell ((code upper : ℚ) - code lower) width width := by
    have width_cast : (width : ℤ) = ((spell (nearyUpper β) word).length : ℤ) - 1 := by
      dsimp [width]
      omega
    simpa only [upper, lower, upperBoundaryCode, lowerBoundaryCode, width_cast] using
      difference_shell
  obtain ⟨_, suffix_eq, _, head_unit⟩ := suffix_exhaustion_of_hasDecimalShell
    upper lower width width_pos width_lt difference_pos_nat shell
  have word_ne : word ≠ [] := by
    intro word_nil
    simp [word_nil, spell] at upper_long
  have head_eq := front_punctuatedUpper_eq_peeledHeadWord β word_ne
  have peeled_unit :
      HasDecimalShell (code (peeledHeadWord β (word.map NearyTile.letter)) : ℚ) 0 0 := by
    rw [← head_eq]
    exact head_unit
  exact peeledSuffix_compilerCongruence_impossible β_large body_divisible
    upper_long peeled_unit suffix_eq

/-- No multi-role target reaches a pole after one multi-digit block above
`R_c` on the compiler's body-length congruence class. -/
theorem multiPole_twoBlock_ruleCRoot_impossible
    {β : Nat} (β_large : 3 ≤ β) {body : List TagLetter}
    (body_divisible : β - 1 ∣ body.length) {target current : List NearyTile}
    (target_multi : 2 ≤ target.length) (target_ends : EndsInErase target)
    (current_upper_long : 2 ≤ (spell (nearyUpper β) current).length) :
    ¬HitsSquarePole β body target [current, DecimalSetterMinimumBody.ruleCRoot] := by
  intro pole
  have β_pos : 0 < β := by omega
  let T := boundaryTrace β body target
  let V := lowerBoundaryCode β body target
  let G := lift ((10 : ℚ) ^ β)
  let μ := DecimalSetterMatrix.marker β
  let H := upperBoundaryCode β DecimalSetterMinimumBody.ruleCRoot
  let A := upperScale β current
  let δ := upperBoundaryCode β current - lowerBoundaryCode β body current
  have H_ne : H ≠ 0 := (upperBoundaryCode_decimalUnit β_pos _).1.1
  have μ_pos : 0 < μ := DecimalSetterMatrix.marker_pos β
  have ρ_bound : (10 : ℚ) ≤ (10 : ℚ) ^ β := by
    simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 10) β_pos)
  have E_pos : 0 < gap ((10 : ℚ) ^ β) := by unfold gap; linarith
  have G_pos : 0 < G := by dsimp [G, lift]; linarith
  have upper_pos : 0 < upperBoundaryCode β target := by
    exact lt_of_le_of_ne (by unfold upperBoundaryCode; positivity)
      (Ne.symm (upperBoundaryCode_decimalUnit β_pos target).1.1)
  have V_pos : 0 < V := by
    exact lt_of_le_of_ne (by dsimp [V, lowerBoundaryCode]; positivity)
      (Ne.symm (lowerBoundaryCode_hasDecimalShell_of_endsInErase β body target_ends).1.1)
  have T_pos : 0 < T := by
    exact add_pos (mul_pos E_pos upper_pos) (mul_pos G_pos V_pos)
  have A_pos : 0 < A := by dsimp [A, upperScale]; positivity
  have cross := (hitsSquarePole_iff_rayEquation β_pos body target
    [current, DecimalSetterMinimumBody.ruleCRoot]).mp pole
  rw [parsedRay_pair_ruleCRoot_eq β_pos] at cross
  change T * (H * δ / μ ^ 2) = G * V * (A * H / μ) at cross
  have equation : δ * T = G * V * A * μ := by
    have raw : H * (δ * T) = H * (G * V * A * μ) := by
      calc
        H * (δ * T) = μ ^ 2 * (T * (H * δ / μ ^ 2)) := by
          field_simp [ne_of_gt μ_pos]
        _ = μ ^ 2 * (G * V * (A * H / μ)) := congrArg (μ ^ 2 * ·) cross
        _ = H * (G * V * A * μ) := by
          field_simp [ne_of_gt μ_pos]
    exact mul_left_cancel₀ H_ne raw
  have δ_eq : δ = G * V * A * μ / T := (eq_div_iff (ne_of_gt T_pos)).mpr equation
  have δ_pos : 0 < δ := by rw [δ_eq]; positivity
  have T_shell : HasDecimalShell T 1 1 :=
    DecimalSetterShallow.multiRoleErasureEnded_boundaryTrace_hasDecimalShell
      (by omega) body target_multi target_ends
  have A_shell : HasDecimalShell A
      (spell (nearyUpper β) current).length (spell (nearyUpper β) current).length := by
    simpa [A, upperScale] using ten_hasDecimalShell.pow
      (spell (nearyUpper β) current).length
  have numerator_shell := (((lift_tenPow_hasDecimalShell β_pos).mul
    (lowerBoundaryCode_hasDecimalShell_of_endsInErase β body target_ends)).mul
      A_shell).mul (marker_hasDecimalShell β_pos)
  have discrepancy_shell : HasDecimalShell δ
      (((spell (nearyUpper β) current).length : ℤ) - 1)
      (((spell (nearyUpper β) current).length : ℤ) - 1) := by
    rw [δ_eq]
    exact ⟨by simpa [G, V, μ] using div_hasValue numerator_shell.1 T_shell.1,
      by simpa [G, V, μ] using div_hasValue numerator_shell.2 T_shell.2⟩
  exact positiveDiscrepancy_equalDepth_impossible β_large body_divisible current_upper_long
    (sub_pos.mp δ_pos) discrepancy_shell

/-- The complete long `R_c` three-block singleton branch is empty on the
compiler's body-length congruence class, independently of gap-factor support. -/
theorem singletonPole_threeBlock_ruleCRoot_long_impossible
    {β : Nat} (β_large : 3 ≤ β) {body : List TagLetter}
    (body_divisible : β - 1 ∣ body.length)
    (targetLetter : TagLetter) {current next : List NearyTile}
    (current_multi : 2 ≤ current.length) (current_ends : EndsInErase current)
    (next_multi : 2 ≤ next.length) (next_ends : EndsInErase next)
    (current_long : β + 3 ≤ (spell (nearyUpper β) current).length) :
    ¬HitsSquarePole β body [.erase targetLetter]
      [current, next, DecimalSetterMinimumBody.ruleCRoot] := by
  intro pole
  have difference_pos := singletonPole_threeBlock_ruleCRoot_discrepancy_pos
    β_large body targetLetter current_ends pole
  have difference_shell :=
    (singletonPole_threeBlock_ruleCRoot_multi_long_iff_discrepancyShell
      β_large body targetLetter current_multi current_ends next_ends pole).mp current_long
  have upper_long : 2 ≤ (spell (nearyUpper β) next).length := by
    have length_le := length_le_tagEncode β (next.map NearyTile.letter)
    rw [← spell_nearyUpper, List.length_map] at length_le
    exact next_multi.trans length_le
  exact positiveDiscrepancy_equalDepth_impossible β_large body_divisible
    upper_long difference_pos difference_shell

/-- On the compiler image, the three-block singleton frontier has only two
arms: a deep root with a two-`c` intervener, or a short all-`c` current over `R_c`. -/
theorem singletonPole_threeBlock_compilerClassifier
    {β : Nat} (β_large : 3 ≤ β) {body : List TagLetter}
    (body_divisible : β - 1 ∣ body.length)
    (targetLetter : TagLetter) {current next root : List NearyTile}
    (source_law : BlocksLaw [current, next, root])
    (pole : HitsSquarePole β body [.erase targetLetter] [current, next, root]) :
    (2 ≤ (spell (nearyUpper β) root).length ∧
      next.length = 2 ∧ next.map NearyTile.letter = [.c, .c] ∧
        β + 3 ≤ (spell (nearyUpper β) current).length) ∨
      (root = DecimalSetterMinimumBody.ruleCRoot ∧
        2 ≤ current.length ∧ current.length ≤ β + 2 ∧
          current.map NearyTile.letter = List.replicate current.length .c) := by
  have current_multi :=
    singletonPole_threeBlock_forces_current_multi β_large body targetLetter source_law pole
  have next_multi :=
    singletonPole_threeBlock_forces_next_multi β_large body targetLetter source_law pole
  rcases singletonPole_threeBlock_classifier β_large body targetLetter source_law pole with
    deep | ⟨root_eq, long_or_short⟩
  · exact Or.inl deep
  · subst root
    rcases long_or_short with long | short
    · exact False.elim <| singletonPole_threeBlock_ruleCRoot_long_impossible
        β_large body_divisible targetLetter current_multi source_law.1
          next_multi source_law.2.1 long.1 pole
    · exact Or.inr ⟨rfl, current_multi, short.1, short.2.1⟩

end MatrixMortality.DecimalSetterBridgeRay
