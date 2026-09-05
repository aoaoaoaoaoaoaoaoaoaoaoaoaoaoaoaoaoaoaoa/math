import MatrixMortality.AsymmetricSeparatorSuffix

/-!
# The competing period forced by the wrong phase

After suffix cancellation, the wrong-phase equation expresses the body's periodic value as
the code of `10p`, increased by one. Its residue forces the final symbol of `p` to be zero;
changing that symbol to one gives an actual competing period.
-/

namespace MatrixMortality.AsymmetricSeparatorRealization

open ChangedSeparatorTail

private theorem shifted_period (body part : List Bool)
    (equation : -1 - periodicTernaryCode body =
      tiltedTernaryCode (7 - 9 * periodicTernaryCode body) part) :
    periodicTernaryCode body =
      (ternaryCode ([true, false] ++ part) + 1) /
        ((3 : ℚ) ^ ([true, false] ++ part).length - 1) := by
  have positive := ternaryPeriodDenominator_pos ([true, false] ++ part) (by simp)
  rw [eq_div_iff positive.ne']
  have normalized : -1 - periodicTernaryCode body =
      ternaryCode part + (7 - 9 * periodicTernaryCode body) * 3 ^ part.length := equation
  simp only [ternaryCode_append, ternaryCode_cons, ternaryCode_nil, ternaryDigit,
    List.length_append, List.length_cons, List.length_nil, Nat.cast_add, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_ofNat, pow_add]
  norm_num
  nlinarith [normalized]

/-- The wrong-phase slope equation forces a zero final digit and a commuting capped period. -/
theorem asymmetric_period_of_equation (body part : List Bool)
    (ends_true : ∃ stem, body = stem ++ [true]) (nonempty : part ≠ [])
    (equation : -1 - periodicTernaryCode body =
      tiltedTernaryCode (7 - 9 * periodicTernaryCode body) part) :
    ∃ middle, part = middle ++ [false] ∧
      body ++ ([true, false] ++ middle ++ [true]) =
        ([true, false] ++ middle ++ [true]) ++ body := by
  obtain ⟨stem, body_eq⟩ := ends_true
  have split : ∃ middle bit, part = middle ++ [bit] := by
    induction part using List.reverseRecOn with
    | nil => exact False.elim (nonempty rfl)
    | append_singleton middle bit _ => exact ⟨middle, bit, rfl⟩
  obtain ⟨middle, bit, part_eq⟩ := split
  have shifted := shifted_period body part equation
  have body_nonempty : body ≠ [] := by simp [body_eq]
  have body_denominator := (ternaryPeriodDenominator_pos body body_nonempty).ne'
  have part_denominator :=
    (ternaryPeriodDenominator_pos ([true, false] ++ part) (by simp)).ne'
  have cross : (ternaryCode body : ℚ) *
      (3 ^ ([true, false] ++ part).length - 1) =
        (ternaryCode ([true, false] ++ part) + 1) * (3 ^ body.length - 1) :=
    (div_eq_div_iff body_denominator part_denominator).mp shifted
  have cross_int : (ternaryCode body : ℤ) *
      (3 ^ ([true, false] ++ part).length - 1) =
        (ternaryCode ([true, false] ++ part) + 1) * (3 ^ body.length - 1) := by
    exact_mod_cast cross
  cases bit with
  | false =>
      refine ⟨middle, part_eq, ?_⟩
      have periodic_equal : periodicTernaryCode body =
          periodicTernaryCode ([true, false] ++ middle ++ [true]) := by
        rw [shifted, periodicTernaryCode, part_eq]
        congr 1
        · simp only [ternaryCode_append, ternaryCode_singleton, ternaryDigit,
            List.length_append, List.length_cons, List.length_nil, Nat.cast_add,
            Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_add]
          ring
        · simp
      exact (periodicTernaryCode_eq_iff_commute body _ body_nonempty (by simp)).mp periodic_equal
  | true =>
      have impossible : (1 : ℤ) = 0 := by
        simpa [body_eq, part_eq, ternaryCode_append, ternaryCode_singleton,
          ternaryCode_cons, ternaryCode_nil, ternaryDigit, pow_add,
          Int.add_emod, Int.sub_emod, Int.mul_emod] using
            congrArg (fun value : ℤ => value % 3) cross_int
      exact False.elim ((by decide : (1 : ℤ) ≠ 0) impossible)

end MatrixMortality.AsymmetricSeparatorRealization
