import MatrixMortality.AsymmetricSeparatorCommutation
import MatrixMortality.AsymmetricSeparatorPeriod

/-!
# Excluding every wrong-phase scalar zero

Suffix comparability leaves only a lower word with a nonempty extra prefix. The slope equation
turns that prefix into a competing period; the source's `bcb` prefix and the lower-tile grammar
exclude every possible period length.
-/

namespace MatrixMortality.AsymmetricSeparatorRealization

open ChangedSeparatorTail

private theorem mixed_ne_of_period_obstruction (body upper lower : List Bool)
    (ends_true : ∃ stem, body = stem ++ [true])
    (slope_lower : -2 < -1 - periodicTernaryCode body)
    (slope_upper : -1 - periodicTernaryCode body < -3 / 2)
    (obstruction : ∀ middle, middle ++ [false] <+: lower →
      body ++ ([true, false] ++ middle ++ [true]) ≠
        ([true, false] ++ middle ++ [true]) ++ body) :
    tiltedTernaryCode (-1 - periodicTernaryCode body) upper ≠
      tiltedTernaryCode (7 - 9 * periodicTernaryCode body) lower := by
  intro equal
  have body_nonempty : body ≠ [] := by
    obtain ⟨stem, body_eq⟩ := ends_true
    simp [body_eq]
  have slopes_ne : -1 - periodicTernaryCode body ≠ 7 - 9 * periodicTernaryCode body := by
    linarith
  rcases asymmetric_suffix_comparable body upper lower body_nonempty equal with
    upper_suffix | lower_suffix
  · obtain ⟨part, lower_eq⟩ := upper_suffix
    have canceled : -1 - periodicTernaryCode body =
        tiltedTernaryCode (7 - 9 * periodicTernaryCode body) part := by
      have expanded :
          (ternaryCode upper : ℚ) + (-1 - periodicTernaryCode body) * 3 ^ upper.length =
            ternaryCode upper + 3 ^ upper.length *
              tiltedTernaryCode (7 - 9 * periodicTernaryCode body) part := by
        calc
          _ = tiltedTernaryCode (7 - 9 * periodicTernaryCode body) lower := equal
          _ = _ := by rw [← lower_eq, tiltedTernaryCode_append]
      have scale_positive : (0 : ℚ) < 3 ^ upper.length := by positivity
      nlinarith [expanded]
    have part_nonempty : part ≠ [] := by
      intro empty
      apply slopes_ne
      simpa only [empty, tiltedTernaryCode, ternaryCode_nil, Nat.cast_zero,
        List.length_nil, pow_zero, mul_one, zero_add] using canceled
    obtain ⟨middle, part_eq, commuting⟩ :=
      asymmetric_period_of_equation body part ends_true part_nonempty canceled
    have lower_prefix : middle ++ [false] <+: lower := by
      rw [← lower_eq, ← part_eq]
      exact List.prefix_append _ _
    exact obstruction middle lower_prefix commuting
  · obtain ⟨part, upper_eq⟩ := lower_suffix
    have canceled : tiltedTernaryCode (-1 - periodicTernaryCode body) part =
        7 - 9 * periodicTernaryCode body := by
      have expanded :
          (ternaryCode lower : ℚ) + 3 ^ lower.length *
            tiltedTernaryCode (-1 - periodicTernaryCode body) part =
              ternaryCode lower + (7 - 9 * periodicTernaryCode body) * 3 ^ lower.length := by
        calc
          _ = tiltedTernaryCode (-1 - periodicTernaryCode body) upper := by
            rw [← upper_eq, tiltedTernaryCode_append]
          _ = _ := equal
      have scale_positive : (0 : ℚ) < 3 ^ lower.length := by positivity
      nlinarith [expanded]
    by_cases empty : part = []
    · exact slopes_ne (by simpa [empty, tiltedTernaryCode] using canceled)
    · have below := tiltedTernaryCode_lt_neg_two _ slope_upper part empty
      linarith [below]

private theorem tagEncode_ends_true (β : Nat) (body : List TagLetter) (nonempty : body ≠ []) :
    ∃ stem, tagEncode β body = stem ++ [true] := by
  induction body using List.reverseRecOn with
  | nil => exact False.elim (nonempty rfl)
  | append_singleton body letter _ =>
      rw [tagEncode_append]
      cases letter with
      | b =>
          refine ⟨tagEncode β body ++ ([true] ++ List.replicate β false), ?_⟩
          simp [tagCode, List.append_assoc]
      | c => exact ⟨tagEncode β body, by simp [tagCode]⟩

/-- Every arbitrary lower-tile word is separated from every upper word in the wrong phase. -/
theorem wrongPhase_ne (β : Nat) (positive : 0 < β) (body : List TagLetter)
    (starts_bcb : body.take 3 = [.b, .c, .b])
    (upper : List Bool) (word : List NearyTile) :
    tiltedTernaryCode (bodySlope β body) upper ≠
      tiltedTernaryCode (16 + 9 * bodySlope β body) (spell (nearyLower β body) word) := by
  have body_eq : body = [.b, .c, .b] ++ body.drop 3 := by
    rw [← starts_bcb, List.take_append_drop]
  have nonempty : body ≠ [] := by rw [body_eq]; simp
  have b_mem : .b ∈ body := by rw [body_eq]; simp
  let zeros := β - 1
  let block := [true, false] ++ List.replicate zeros false ++ [true]
  have width_eq : β = zeros + 1 := by dsimp [zeros]; omega
  have code_b : tagCode β .b = block := by
    rw [width_eq]
    simp [tagCode, block, List.replicate_succ]
  have encoded_eq : tagEncode β body =
      block ++ [true] ++ block ++ tagEncode β (body.drop 3) := by
    conv_lhs => rw [body_eq]
    simp only [tagEncode_append, tagEncode_cons, tagEncode_nil, code_b]
    simp only [tagCode, List.append_nil, List.append_assoc]
  have encoded_prefix : [true, false] <+: tagEncode β body := by
    rw [encoded_eq]
    simp [block, List.append_assoc]
  have excluded := mixed_ne_of_period_obstruction (tagEncode β body) upper
    (spell (nearyLower β body) word) (tagEncode_ends_true β body nonempty)
    (bodySlope_gt_neg_two β positive body b_mem)
    (bodySlope_lt_neg_three_halves β body nonempty)
    (fun middle lower_prefix => by
      rw [encoded_eq]
      exact no_asymmetric_period zeros (tagEncode β (body.drop 3)) middle
        (spell (nearyLower β body) word)
        (lowerWord_no_10 β body encoded_prefix word zeros)
        (lowerWord_no_111 β body encoded_prefix word zeros) lower_prefix)
  have slope_eq : 16 + 9 * bodySlope β body = 7 - 9 * periodicTernaryCode (tagEncode β body) := by
    rw [bodySlope]
    ring
  rw [slope_eq, bodySlope]
  exact excluded

end MatrixMortality.AsymmetricSeparatorRealization
