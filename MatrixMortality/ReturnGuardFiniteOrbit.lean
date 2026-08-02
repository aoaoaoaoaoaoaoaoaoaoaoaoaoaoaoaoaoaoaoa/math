import MatrixMortality.ReturnGuardPeriodicity

/-!
# Finite bounded-denominator endpoint dynamics

The local record ceiling places every bounded-denominator primitive execution in one explicit
finite rectangle.  Functionality then upgrades recurrence to eventual periodicity.
-/

namespace MatrixMortality.ReturnGuard

noncomputable section

/-- An infinite primitive endpoint execution together with the signed reverse contents at
every step.  Positivity fixes the rational representative; the denominator bound is data, not
an existential compactness assumption. -/
structure BoundedPrimitiveEndpointStream
    (prime depth denominatorBound : Nat)
    (centerNumerator driftNumerator scale : ℤ) where
  /-- Primitive numerator-denominator pair at one orbit index. -/
  state : Nat → ℤ × ℤ
  /-- Positive return wait selected at one orbit index. -/
  wait : Nat → Nat
  /-- Signed primitive content removed from the raw successor pair. -/
  content : Nat → ℤ
  /-- Complementary signed content in the cyclotomic determinant factorization. -/
  complement : Nat → ℤ
  denominator_positive : ∀ index, 0 < (state index).2
  denominator_le : ∀ index, (state index).2.natAbs ≤ denominatorBound
  denominator_unit : ∀ index, ¬(prime : ℤ) ∣ (state index).2
  reduction : ∀ index,
    PrimitiveEndpointReduction prime depth centerNumerator driftNumerator scale
      (wait index) (state index) (state (index + 1)) (content index)
  complementary : ∀ index,
    content index * complement index =
      driftNumerator * scale * ((prime : ℤ) ^ wait index - 1)

/-- Every wait of a bounded-denominator stream is bounded by the larger of the initial wait and
the universal record-ascent ceiling. -/
theorem BoundedPrimitiveEndpointStream.wait_le
    {prime depth denominatorBound : Nat} [Fact prime.Prime]
    {centerNumerator driftNumerator scale : ℤ}
    (stream :
      BoundedPrimitiveEndpointStream prime depth denominatorBound
        centerNumerator driftNumerator scale)
    (depth_two_le : 2 ≤ depth)
    (drift_unit : ¬(prime : ℤ) ∣ driftNumerator)
    (scale_unit : ¬(prime : ℤ) ∣ scale)
    (center_sub_scale_unit : ¬(prime : ℤ) ∣ centerNumerator - scale)
    (index : Nat) :
    stream.wait index ≤
      max (stream.wait 0)
        (denominatorRecordWaitBound prime depth denominatorBound
          centerNumerator driftNumerator scale) := by
  induction index with
  | zero => exact le_max_left _ _
  | succ index induction =>
      by_cases nondecreasing : stream.wait index ≤ stream.wait (index + 1)
      · have bounded :=
          (stream.reduction index).nonDecreasing_waits_le depth_two_le nondecreasing
            (stream.denominator_positive index)
            (stream.denominator_positive (index + 1))
            (stream.denominator_positive (index + 2))
            (stream.denominator_le index)
            (stream.denominator_le (index + 1))
            drift_unit scale_unit center_sub_scale_unit
            (stream.denominator_unit (index + 1))
            (by simpa only [Nat.add_assoc, Nat.reduceAdd] using
              stream.reduction (index + 1))
            (stream.complementary index)
        exact bounded.2.trans (le_max_right _ _)
      · exact (Nat.lt_of_not_ge nondecreasing).le.trans induction

/-- Every state in a bounded-denominator stream lies in one explicit integral rectangle. -/
theorem BoundedPrimitiveEndpointStream.state_mem_box
    {prime depth denominatorBound : Nat} [Fact prime.Prime]
    {centerNumerator driftNumerator scale : ℤ}
    (stream :
      BoundedPrimitiveEndpointStream prime depth denominatorBound
        centerNumerator driftNumerator scale)
    (depth_two_le : 2 ≤ depth)
    (drift_unit : ¬(prime : ℤ) ∣ driftNumerator)
    (scale_unit : ¬(prime : ℤ) ∣ scale)
    (center_sub_scale_unit : ¬(prime : ℤ) ∣ centerNumerator - scale)
    (index : Nat) :
    let waitBound :=
      max (stream.wait 0)
        (denominatorRecordWaitBound prime depth denominatorBound
          centerNumerator driftNumerator scale)
    let numeratorBound :=
      endpointSourceNumeratorBound prime depth waitBound denominatorBound
        driftNumerator scale
    stream.state index ∈
      Set.Icc (-(numeratorBound : ℤ)) numeratorBound ×ˢ
        Set.Icc (1 : ℤ) denominatorBound := by
  let waitBound :=
    max (stream.wait 0)
      (denominatorRecordWaitBound prime depth denominatorBound
        centerNumerator driftNumerator scale)
  let numeratorBound :=
    endpointSourceNumeratorBound prime depth waitBound denominatorBound
      driftNumerator scale
  have prime_gt_one : 1 < prime := (Fact.out : prime.Prime).one_lt
  have drift_ne : driftNumerator ≠ 0 := fun drift_zero =>
    drift_unit (drift_zero ▸ dvd_zero (prime : ℤ))
  have scale_ne : scale ≠ 0 := fun scale_zero =>
    scale_unit (scale_zero ▸ dvd_zero (prime : ℤ))
  have numerator_le : (stream.state index).1.natAbs ≤ numeratorBound := by
    simpa only [numeratorBound] using
      (stream.reduction index).source_numerator_le_box prime_gt_one
        (stream.wait_le depth_two_le drift_unit scale_unit center_sub_scale_unit index)
        (stream.denominator_le index) (stream.denominator_le (index + 1))
        drift_ne scale_ne (stream.complementary index)
  have numerator_le_cast :
      ((stream.state index).1.natAbs : ℤ) ≤ numeratorBound := by exact_mod_cast numerator_le
  have numerator_upper : (stream.state index).1 ≤ (numeratorBound : ℤ) :=
    Int.le_natAbs.trans numerator_le_cast
  have numerator_lower : -(numeratorBound : ℤ) ≤ (stream.state index).1 := by
    have negative_le_abs :
        -(stream.state index).1 ≤ ((stream.state index).1.natAbs : ℤ) := by
      simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -(stream.state index).1))
    linarith
  have denominator_upper : (stream.state index).2 ≤ (denominatorBound : ℤ) := by
    have cast : ((stream.state index).2.natAbs : ℤ) ≤ denominatorBound := by
      exact_mod_cast stream.denominator_le index
    exact Int.le_natAbs.trans cast
  exact ⟨⟨numerator_lower, numerator_upper⟩,
    ⟨stream.denominator_positive index, denominator_upper⟩⟩

/-- Bounded denominators force a repeated primitive endpoint state. -/
theorem BoundedPrimitiveEndpointStream.exists_state_repeat
    {prime depth denominatorBound : Nat} [Fact prime.Prime]
    {centerNumerator driftNumerator scale : ℤ}
    (stream :
      BoundedPrimitiveEndpointStream prime depth denominatorBound
        centerNumerator driftNumerator scale)
    (depth_two_le : 2 ≤ depth)
    (drift_unit : ¬(prime : ℤ) ∣ driftNumerator)
    (scale_unit : ¬(prime : ℤ) ∣ scale)
    (center_sub_scale_unit : ¬(prime : ℤ) ∣ centerNumerator - scale) :
    ∃ earlier later, earlier < later ∧ stream.state earlier = stream.state later := by
  let waitBound :=
    max (stream.wait 0)
      (denominatorRecordWaitBound prime depth denominatorBound
        centerNumerator driftNumerator scale)
  let numeratorBound :=
    endpointSourceNumeratorBound prime depth waitBound denominatorBound
      driftNumerator scale
  let box : Set (ℤ × ℤ) :=
    Set.Icc (-(numeratorBound : ℤ)) numeratorBound ×ˢ
      Set.Icc (1 : ℤ) denominatorBound
  have box_finite : box.Finite :=
    (Set.finite_Icc (-(numeratorBound : ℤ)) numeratorBound).prod
      (Set.finite_Icc (1 : ℤ) denominatorBound)
  exact box_finite.exists_lt_map_eq_of_forall_mem fun index => by
    simpa only [box, waitBound, numeratorBound] using
      stream.state_mem_box depth_two_le drift_unit scale_unit
        center_sub_scale_unit index

/-- A deterministic bounded-denominator stream is eventually periodic. -/
theorem BoundedPrimitiveEndpointStream.eventually_periodic
    {prime depth denominatorBound : Nat} [Fact prime.Prime]
    {centerNumerator driftNumerator scale : ℤ}
    (stream :
      BoundedPrimitiveEndpointStream prime depth denominatorBound
        centerNumerator driftNumerator scale)
    (depth_two_le : 2 ≤ depth)
    (drift_unit : ¬(prime : ℤ) ∣ driftNumerator)
    (scale_unit : ¬(prime : ℤ) ∣ scale)
    (center_sub_scale_unit : ¬(prime : ℤ) ∣ centerNumerator - scale)
    (successor : (ℤ × ℤ) → ℤ × ℤ)
    (deterministic : ∀ index, stream.state (index + 1) = successor (stream.state index)) :
    ∃ start period, 0 < period ∧
      ∀ offset,
        stream.state (start + offset + period) = stream.state (start + offset) := by
  obtain ⟨start, later, start_lt_later, repeated⟩ :=
    stream.exists_state_repeat depth_two_le drift_unit scale_unit center_sub_scale_unit
  let period := later - start
  have period_positive : 0 < period := Nat.sub_pos_of_lt start_lt_later
  have later_eq : later = start + period := (Nat.add_sub_of_le start_lt_later.le).symm
  have iterate_state : ∀ base offset,
      stream.state (base + offset) = successor^[offset] (stream.state base) := by
    intro base offset
    induction offset with
    | zero => simp
    | succ offset induction =>
        rw [Nat.add_succ, deterministic, Function.iterate_succ_apply']
        rw [induction]
  refine ⟨start, period, period_positive, fun offset => ?_⟩
  rw [show start + offset + period = (start + period) + offset by omega,
    ← later_eq, iterate_state, iterate_state, repeated]

end
end MatrixMortality.ReturnGuard
