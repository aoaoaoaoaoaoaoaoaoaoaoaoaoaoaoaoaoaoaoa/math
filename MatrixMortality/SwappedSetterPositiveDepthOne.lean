import MatrixMortality.SwappedSetterCompiler
import MatrixMortality.SwappedSetterFringeTag
import MatrixMortality.Undecidability.NearyCompiler

/-!
# Positive depth-one swapped-setter extinction

The regular fringe sieve leaves four prefix pairs. Two decode to impossible Neary residuals; the
other two have the terminal discrepancy, so an exact following pole is a genuine terminal match.
-/

namespace MatrixMortality.SwappedSetterFringe

/-- The exact valuation-one pole equation for a target Neary word. -/
def PositiveDepthOnePole (β : Nat) (body : List TagLetter) (discrepancy : ℤ)
    (targetWord : List NearyTile) : Prop :=
  let ρ : ℤ := 3 ^ β
  let μ : ℤ := 2 * ρ - 1
  let D : ℤ := ρ - 2
  let H : ℤ := 5 * ρ - 1
  let P : ℤ := swappedCode (spell (nearyUpper β) targetWord ++ nearyMarker β)
  let V : ℤ := swappedCode (spell (nearyLower β body) targetWord)
  discrepancy * D * P = H * (3 * μ - discrepancy) * V

/-- A hypothetical false pole immediately after one positive distinguished-boundary transfer. -/
structure PositiveDepthOnePoleWitness (β : Nat) (body : List TagLetter) where
  /-- Word producing the positive depth-one discrepancy. -/
  priorWord : List NearyTile
  /-- Word at the prospective next pole. -/
  targetWord : List NearyTile
  /-- Unmatched upper prefix after maximal suffix cancellation. -/
  upperPrefix : List Bool
  /-- Unmatched lower prefix after maximal suffix cancellation. -/
  sourcePrefix : List Bool
  /-- Bounded lower suffix of the prospective pole word. -/
  targetSuffix : List Bool
  /-- Cancelled common suffix of the preceding word. -/
  commonSuffix : List Bool
  /-- The upper prefix has one of the two stable positive-depth shapes. -/
  upperFringe : UpperFringe β upperPrefix
  /-- The lower prefix belongs to the physical block language. -/
  sourceFringe : SourceFringe sourcePrefix
  /-- The prospective lower suffix belongs to the physical target language. -/
  targetFringe : TargetFringe (β + 2) targetSuffix
  /-- The target suffix is the actual bounded suffix of the prospective lower spelling. -/
  targetSuffix_eq :
    targetSuffix = (spell (nearyLower β body) targetWord).rtake (β + 2)
  /-- Exact preceding upper factorization. -/
  upperFactorization :
    spell (nearyUpper β) priorWord ++ nearyMarker β = upperPrefix ++ commonSuffix
  /-- Exact preceding lower factorization. -/
  lowerFactorization :
    spell (nearyLower β body) priorWord = sourcePrefix ++ commonSuffix
  /-- Body-independent congruence forced by the prospective pole. -/
  poleCongruence : PoleCongruence β upperPrefix sourcePrefix targetSuffix
  /-- Exact prospective pole equation before modular reduction. -/
  exactPole :
    PositiveDepthOnePole β body
      ((swappedCode upperPrefix : ℤ) - swappedCode sourcePrefix) targetWord

/-- Every pole-compatible stable fringe is one of the four exact prefix pairs. -/
theorem poleCongruence_four_fringe_pairs
    {β : Nat} (β_large : 6 ≤ β) {upper source target : List Bool}
    (upper_fringe : UpperFringe β upper) (source_fringe : SourceFringe source)
    (target_fringe : TargetFringe (β + 2) target)
    (pole : PoleCongruence β upper source target) :
    (upper = SwappedSetterResidual.deltaOneUpper β ∧ source = []) ∨
      (upper = [true, true] ++ List.replicate β false ∧ source = []) ∨
      (upper = tagCode β .b ∧ source = List.replicate β false) ∨
      (upper = tagCode β .b ∧ source = List.replicate (β - 1) false) := by
  rcases upperFringe_source_sieve (show 2 ≤ β by omega) upper_fringe target_fringe pole with
      run | tag | allOnes
  · obtain ⟨ones, ones_lower, ones_upper, upper_eq, source_eq⟩ := run
    rcases runPole_terminal_shapes (show 5 ≤ β by omega) ones_lower ones_upper upper_eq
        source_eq target_fringe pole with deltaOne | terminal
    · left
      obtain ⟨upper_eq, source_eq⟩ := deltaOne
      exact ⟨by simpa [SwappedSetterResidual.deltaOneUpper] using upper_eq, source_eq⟩
    · right
      left
      exact terminal
  · obtain ⟨upper_eq, source_last⟩ := tag
    subst upper
    rcases tagPole_classify (show 5 ≤ β by omega) source_fringe source_last target_fringe pole with
        deltaThree | terminal
    · right
      right
      right
      exact ⟨rfl, deltaThree.1⟩
    · right
      right
      left
      exact ⟨rfl, terminal.1⟩
  · obtain ⟨upper_eq, source_last⟩ := allOnes
    have upper_code :
        2 * swappedCode (List.replicate (β + 2) true) + 1 = 9 * 3 ^ β := by
      calc
        2 * swappedCode (List.replicate (β + 2) true) + 1 = 3 ^ (β + 2) :=
          swappedCode_replicate_true (β + 2)
        _ = 9 * 3 ^ β := by rw [pow_add]; ring
    exact False.elim <| allOnes_sourceFringe_false β_large source_fringe source_last
      (by simpa [upper_eq] using upper_code) target_fringe pole

private theorem tagHaltsFrom_of_terminalPositiveDepthOnePole
    (β : Nat) (body : List TagLetter) (β_large : 1 < β)
    (body_long : β - 1 ≤ body.length) (targetWord : List NearyTile)
    (pole : PositiveDepthOnePole β body (5 * (3 : ℤ) ^ β - 1) targetWord) :
    TagHaltsFrom β (tagOutput body) (body.drop (β - 1) ++ [.b]) := by
  let ρ : ℤ := 3 ^ β
  let μ : ℤ := 2 * ρ - 1
  let D : ℤ := ρ - 2
  let H : ℤ := 5 * ρ - 1
  let P : ℤ := swappedCode (spell (nearyUpper β) targetWord ++ nearyMarker β)
  let V : ℤ := swappedCode (spell (nearyLower β body) targetWord)
  have pole_eq : H * D * P = H * (3 * μ - H) * V := by
    simpa [PositiveDepthOnePole, ρ, μ, D, H, P, V] using pole
  have rho_large : 3 ≤ ρ := by
    dsimp [ρ]
    have power_mono := Nat.pow_le_pow_right (by norm_num : 0 < 3) (show 1 ≤ β by omega)
    exact_mod_cast power_mono
  have D_ne : D ≠ 0 := by
    dsimp [D]
    omega
  have H_ne : H ≠ 0 := by
    dsimp [H]
    omega
  have calibration : D + H = 3 * μ := by
    dsimp [D, H, μ]
    ring
  have terminal_pole : (D * P + H * V) * H = 3 * H * μ * V := by
    calc
      (D * P + H * V) * H = H * D * P + H * H * V := by ring
      _ = H * (3 * μ - H) * V + H * H * V := by rw [pole_eq]
      _ = 3 * H * μ * V := by ring
  have code_eq_int : P = V :=
    (terminalDiscrepancy_pole_iff D_ne H_ne calibration).mp terminal_pole
  have code_eq_nat :
      swappedCode (spell (nearyUpper β) targetWord ++ nearyMarker β) =
        swappedCode (spell (nearyLower β body) targetWord) := by
    change
      (swappedCode (spell (nearyUpper β) targetWord ++ nearyMarker β) : ℤ) =
        (swappedCode (spell (nearyLower β body) targetWord) : ℤ) at code_eq_int
    exact_mod_cast code_eq_int
  exact tagHaltsFrom_of_swappedTernaryCode_eq β body β_large body_long targetWord <| by
    simpa [swappedCode] using code_eq_nat

/-- No positive depth-one pole witness exists unless the Neary source computation halts. -/
theorem positiveDepthOnePoleWitness_halts
    (envelope : NearyArithmeticEnvelope) (β_large : 6 ≤ envelope.β)
    (witness : PositiveDepthOnePoleWitness envelope.β envelope.body) :
    TagHaltsFrom envelope.β (tagOutput envelope.body) envelope.initial := by
  rcases poleCongruence_four_fringe_pairs β_large witness.upperFringe witness.sourceFringe
      witness.targetFringe witness.poleCongruence with deltaOne | terminalRun | terminalTag |
        deltaThree
  · obtain ⟨upper_eq, source_eq⟩ := deltaOne
    have upperFactorization := witness.upperFactorization
    have lowerFactorization := witness.lowerFactorization
    rw [upper_eq] at upperFactorization
    rw [source_eq] at lowerFactorization
    exact False.elim <| swappedDeltaOne_fringe_false (show 2 < envelope.β by omega)
      envelope.body envelope.body_divisible witness.priorWord witness.commonSuffix
      upperFactorization (by simpa using lowerFactorization)
  · obtain ⟨upper_eq, source_eq⟩ := terminalRun
    have discrepancy_eq :
        (swappedCode witness.upperPrefix : ℤ) - swappedCode witness.sourcePrefix =
          5 * (3 : ℤ) ^ envelope.β - 1 := by
      rw [upper_eq, source_eq]
      have code_nat :
          swappedCode ([true, true] ++ List.replicate envelope.β false) =
            5 * 3 ^ envelope.β - 1 := by
        simpa [swappedCode] using (swappedCode_terminalFringes envelope.β).1
      have code_int :
          (swappedCode ([true, true] ++ List.replicate envelope.β false) : ℤ) =
            5 * (3 : ℤ) ^ envelope.β - 1 := by
        calc
          (swappedCode ([true, true] ++ List.replicate envelope.β false) : ℤ) =
              ((5 * 3 ^ envelope.β - 1 : Nat) : ℤ) := by exact_mod_cast code_nat
          _ = 5 * (3 : ℤ) ^ envelope.β - 1 := by
            rw [Nat.cast_sub (by
              have power_pos : 0 < 3 ^ envelope.β := pow_pos (by norm_num) envelope.β
              omega : 1 ≤ 5 * 3 ^ envelope.β)]
            norm_num
      simpa using code_int
    have exactPole := witness.exactPole
    rw [discrepancy_eq] at exactPole
    exact tagHaltsFrom_of_terminalPositiveDepthOnePole envelope.β envelope.body
      (by omega) envelope.body_long witness.targetWord exactPole
  · obtain ⟨upper_eq, source_eq⟩ := terminalTag
    have discrepancy_eq :
        (swappedCode witness.upperPrefix : ℤ) - swappedCode witness.sourcePrefix =
          5 * (3 : ℤ) ^ envelope.β - 1 := by
      rw [upper_eq, source_eq]
      have tag_int :
          (swappedCode (tagCode envelope.β .b) : ℤ) =
            6 * (3 : ℤ) ^ envelope.β - 2 := by
        calc
          (swappedCode (tagCode envelope.β .b) : ℤ) =
              ((6 * 3 ^ envelope.β - 2 : Nat) : ℤ) := by
                exact_mod_cast swappedCode_tag_b envelope.β
          _ = 6 * (3 : ℤ) ^ envelope.β - 2 := by
            rw [Nat.cast_sub (by
              have power_pos : 0 < 3 ^ envelope.β := pow_pos (by norm_num) envelope.β
              omega : 2 ≤ 6 * 3 ^ envelope.β)]
            norm_num
      have source_code := swappedCode_replicate_false envelope.β
      have source_int :
          (swappedCode (List.replicate envelope.β false) : ℤ) =
            (3 : ℤ) ^ envelope.β - 1 := by
        have source_code_int :
            (swappedCode (List.replicate envelope.β false) : ℤ) + 1 =
              (3 : ℤ) ^ envelope.β := by exact_mod_cast source_code
        linarith
      rw [tag_int, source_int]
      ring
    have exactPole := witness.exactPole
    rw [discrepancy_eq] at exactPole
    exact tagHaltsFrom_of_terminalPositiveDepthOnePole envelope.β envelope.body
      (by omega) envelope.body_long witness.targetWord exactPole
  · obtain ⟨upper_eq, source_eq⟩ := deltaThree
    have upperFactorization := witness.upperFactorization
    have lowerFactorization := witness.lowerFactorization
    rw [upper_eq] at upperFactorization
    rw [source_eq] at lowerFactorization
    exact False.elim <| swappedDeltaThree_fringe_false (show 2 < envelope.β by omega)
      envelope.body envelope.body_divisible witness.priorWord witness.commonSuffix
      upperFactorization lowerFactorization

/-- Neary's emitted width is at least ten, so every compiler-produced positive depth-one pole
forces the simulated cyclic-tag computation to halt. -/
theorem compilerPositiveDepthOnePoleWitness_halts
    {period : Nat} (system : Undecidability.CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period)
    (witness : PositiveDepthOnePoleWitness
      (Undecidability.NearyCompiler.deletionWidth period)
      (Undecidability.NearyCompiler.body system input haltPhase period_pos)) :
    TagHaltsFrom
      (Undecidability.NearyCompiler.deletionWidth period)
      (tagOutput (Undecidability.NearyCompiler.body system input haltPhase period_pos))
      ((Undecidability.NearyCompiler.body system input haltPhase period_pos).drop
          (Undecidability.NearyCompiler.deletionWidth period - 1) ++ [.b]) := by
  let envelope :=
    Undecidability.NearyCompiler.arithmeticEnvelope system input haltPhase period_pos
  have width_large : 10 ≤ envelope.β := by
    dsimp [envelope]
    simp [Undecidability.NearyCompiler.deletionWidth]
    omega
  exact positiveDepthOnePoleWitness_halts envelope (by omega) witness

end MatrixMortality.SwappedSetterFringe
