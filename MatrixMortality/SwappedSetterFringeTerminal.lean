import MatrixMortality.SwappedSetterFringe

/-!
# Terminal swapped-setter fringes

The two surviving zero runs and the tag-prefix code are the terminal interfaces consumed by the
complete positive depth-one classifier.
-/

namespace MatrixMortality.SwappedSetterFringe

/-- A run upper fringe satisfying the pole is one of its two terminal zero runs. -/
theorem runPole_terminal_shapes
    {β ones : Nat} (β_large : 5 ≤ β) (ones_lower : 2 ≤ ones)
    (ones_upper : ones ≤ β + 1) {upper source target : List Bool}
    (upper_eq :
      upper = List.replicate ones true ++ List.replicate (β + 2 - ones) false)
    (source_eq : source = []) (target_fringe : TargetFringe (β + 2) target)
    (pole : PoleCongruence β upper source target) :
    (upper = List.replicate 3 true ++ List.replicate (β - 1) false ∧ source = []) ∨
      (upper = List.replicate 2 true ++ List.replicate β false ∧ source = []) := by
  let zeros := β + 2 - ones
  have zeros_pos : 1 ≤ zeros := by
    dsimp [zeros]
    omega
  have sum_eq : ones + zeros = β + 2 := by
    dsimp [zeros]
    omega
  have upper_code_raw := swappedCode_true_false_run ones zeros
  have upper_code : 2 * swappedCode upper + 2 = 9 * 3 ^ β + 3 ^ zeros := by
    rw [upper_eq]
    rw [sum_eq] at upper_code_raw
    simpa [pow_add, Nat.mul_comm] using upper_code_raw
  have zeros_lower : β - 1 ≤ zeros := by
    by_contra lower_failure
    have zeros_inside : zeros + 2 ≤ β := by omega
    subst source
    exact runPole_inside_false β_large zeros_pos zeros_inside upper_code target_fringe pole
  have zeros_upper : zeros ≤ β := by omega
  rcases (show zeros = β - 1 ∨ zeros = β by omega) with zeros_eq | zeros_eq
  · left
    refine ⟨?_, source_eq⟩
    have ones_eq : ones = 3 := by omega
    rw [upper_eq, ones_eq]
    congr 1
  · right
    refine ⟨?_, source_eq⟩
    have ones_eq : ones = 2 := by omega
    rw [upper_eq, ones_eq]
    congr 1

theorem swappedCode_tag_b_add_two (β : Nat) :
    swappedCode (tagCode β .b) + 2 = 6 * 3 ^ β := by
  rw [tagCode]
  simp only [List.cons_append, List.nil_append]
  rw [swappedCode_cons]
  simp only [List.length_append, List.length_replicate, List.length_singleton,
    Bool.not_true, ternaryDigit, pow_succ]
  rw [swappedCode_append]
  norm_num
  have false_code := swappedCode_replicate_false β
  nlinarith

theorem swappedCode_tag_b (β : Nat) :
    swappedCode (tagCode β .b) = 6 * 3 ^ β - 2 := by
  have code := swappedCode_tag_b_add_two β
  have power_pos : 0 < 3 ^ β := pow_pos (by norm_num) β
  omega

end MatrixMortality.SwappedSetterFringe
