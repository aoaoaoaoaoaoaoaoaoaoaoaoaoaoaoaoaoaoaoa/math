import MatrixMortality.SwappedSetterFringe

/-!
# Small swapped-setter fringes

The stable all-ones argument begins at width nine.  The two smaller widths are finite regular
languages; kernel reduction closes them without extending the trusted base.
-/

namespace MatrixMortality.SwappedSetterFringe

private def boolWords : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 =>
      (boolWords n).map (false :: ·) ++
        (boolWords n).map (true :: ·)

private theorem mem_boolWords_iff {word : List Bool} {length : Nat} :
    word ∈ boolWords length ↔ word.length = length := by
  induction length generalizing word with
  | zero => simp [boolWords]
  | succ length induction =>
      cases word with
      | nil => simp [boolWords]
      | cons head tail =>
          cases head <;> simp [boolWords, induction]

private def boolWordsUpTo (bound : Nat) : List (List Bool) :=
  (List.range (bound + 1)).flatMap boolWords

private theorem mem_boolWordsUpTo_iff {word : List Bool} {bound : Nat} :
    word ∈ boolWordsUpTo bound ↔ word.length ≤ bound := by
  simp only [boolWordsUpTo, List.mem_flatMap, List.mem_range, mem_boolWords_iff]
  constructor
  · rintro ⟨length, length_lt, word_length⟩
    omega
  · intro length_bound
    exact ⟨word.length, by omega, rfl⟩

private def sourceWords (bound : Nat) : List (List Bool) :=
  (boolWordsUpTo bound).map (spell fringeBlock)

private theorem phase_length_le_spelling_length (phases : List Bool) :
    phases.length ≤ (spell fringeBlock phases).length := by
  induction phases with
  | nil => simp [spell]
  | cons phase phases induction =>
      cases phase <;> simp [spell, fringeBlock] at induction ⊢ <;> omega

private theorem source_mem_sourceWords {bound : Nat} {source : List Bool}
    (source_fringe : SourceFringe source) (source_last : source.getLast? = some false)
    (source_length : source.length ≤ bound) :
    source ∈ sourceWords bound := by
  obtain ⟨phases, source_eq⟩ :=
    sourceFringe_complete_of_getLast?_false source_fringe source_last
  rw [source_eq]
  simp only [sourceWords, List.mem_map]
  refine ⟨phases, ?_, rfl⟩
  rw [mem_boolWordsUpTo_iff]
  exact (phase_length_le_spelling_length phases).trans (by simpa [source_eq] using source_length)

private def targetWords (width : Nat) : List (List Bool) :=
  let zeroCounts := (List.range (width + 1)).filter (2 ≤ ·)
  let zeroWords := zeroCounts.map (fun zeros => List.replicate zeros false)
  let pairWords := zeroCounts.flatMap fun zeros =>
    (boolWordsUpTo (width - zeros - 2)).map fun front =>
      front ++ [true, true] ++ List.replicate zeros false
  zeroWords ++ pairWords ++ [true :: List.replicate (width - 1) false]

private theorem target_mem_targetWords {width : Nat} {target : List Bool}
    (target_fringe : TargetFringe width target) : target ∈ targetWords width := by
  rcases target_fringe with ⟨length_bound, zero_run | pair_run | cut⟩
  · obtain ⟨zeros, zeros_lower, target_eq⟩ := zero_run
    rw [target_eq] at length_bound ⊢
    simp only [targetWords, List.mem_append, List.mem_map, List.mem_filter,
      List.mem_range, List.mem_flatMap, List.mem_singleton]
    left
    left
    exact ⟨zeros, ⟨by simpa using length_bound, by simpa using zeros_lower⟩, rfl⟩
  · obtain ⟨front, zeros, zeros_lower, target_eq⟩ := pair_run
    rw [target_eq] at length_bound ⊢
    simp only [targetWords, List.mem_append, List.mem_map, List.mem_filter,
      List.mem_range, List.mem_flatMap, List.mem_singleton]
    left
    right
    refine ⟨zeros, ⟨?_, by simpa using zeros_lower⟩, ?_⟩
    · have zeros_upper : zeros ≤ width := by
        simp only [List.length_append, List.length_cons, List.length_nil,
          List.length_replicate] at length_bound
        omega
      simpa using zeros_upper
    · refine ⟨front, ?_, rfl⟩
      rw [mem_boolWordsUpTo_iff]
      simp only [List.length_append, List.length_cons, List.length_nil,
        List.length_replicate] at length_bound
      omega
  · obtain ⟨_, target_eq⟩ := cut
    rw [target_eq]
    simp [targetWords]

private theorem swappedCode_lower_bound' (word : List Bool) (word_nonempty : word ≠ []) :
    3 ^ (word.length - 1) ≤ swappedCode word := by
  have mapped_nonempty : word.map Bool.not ≠ [] := by
    simpa using word_nonempty
  simpa [swappedCode] using ternaryCode_lower_bound (word.map Bool.not) mapped_nonempty

private theorem source_length_le_seven {source : List Bool}
    (source_last : source.getLast? = some false) (source_code : swappedCode source < 1093) :
    source.length ≤ 7 := by
  have source_nonempty : source ≠ [] := by
    intro source_empty
    subst source
    simp at source_last
  have lower := swappedCode_lower_bound' source source_nonempty
  by_contra length_large
  have exponent_large : 7 ≤ source.length - 1 := by omega
  have power_large : 3 ^ 7 ≤ 3 ^ (source.length - 1) :=
    Nat.pow_le_pow_right (by norm_num) exponent_large
  norm_num at power_large
  omega

-- Kernel reduction of the finite regular languages needs depth proportional to their expansions.
set_option maxRecDepth 100000 in
private theorem betaFiveTable :
    ∀ source ∈ sourceWords 7, ∀ target ∈ targetWords 7,
      swappedCode source < 1093 →
        ¬(((1093 : ℤ) - swappedCode source) * ((3 : ℤ) ^ 5 - 2) ≡
          (6 * (3 : ℤ) ^ 5 - 3 - ((1093 : ℤ) - swappedCode source)) * swappedCode target
            [ZMOD 9 * (3 : ℤ) ^ 5]) := by
  decide

theorem allOnes_sourceFringe_five_false
    {upper source target : List Bool}
    (source_fringe : SourceFringe source) (source_last : source.getLast? = some false)
    (code_lt : swappedCode source < swappedCode upper)
    (upper_code : 2 * swappedCode upper + 1 = 9 * 3 ^ 5)
    (target_fringe : TargetFringe 7 target)
    (pole : PoleCongruence 5 upper source target) : False := by
  have upper_code_eq : swappedCode upper = 1093 := by norm_num at upper_code ⊢; omega
  have source_code : swappedCode source < 1093 := by simpa [upper_code_eq] using code_lt
  have source_mem := source_mem_sourceWords source_fringe source_last
    (source_length_le_seven source_last source_code)
  have target_mem := target_mem_targetWords target_fringe
  have forbidden := betaFiveTable source source_mem target target_mem source_code
  apply forbidden
  norm_num [PoleCongruence, upper_code_eq] at pole ⊢
  exact pole

end MatrixMortality.SwappedSetterFringe
