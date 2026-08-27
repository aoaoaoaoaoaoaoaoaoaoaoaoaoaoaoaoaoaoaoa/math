import MatrixMortality.ReturnGuardIntegralLift

/-!
# Completeness of finite quotient certificates

The zero-wait quotient transfer is a rank-one reset whose kernel is the terminal residual.
Consequently every transition-closed quotient set which excludes annihilation already excludes
the terminal.  Safe certificate existence is therefore exactly cancellation unreachability.

Synchronized products of prime quotients cannot strengthen this certificate architecture:
every cancellation-free joint invariant projects to a cancellation-free invariant in each
factor.
-/

namespace MatrixMortality.ReturnGuard

noncomputable section

/-- The homogeneous terminal equation for one integral presentation, reduced modulo a quotient
factor. -/
def IsTerminalPairMod
    (factor : Nat) [Fact factor.Prime]
    (centerNumerator driftNumerator scale : ℤ)
    (pair : ℤ × ℤ) : Prop :=
  ((centerNumerator : ZMod factor) - (scale : ZMod factor)) *
        (pair.1 : ZMod factor) +
      (driftNumerator : ZMod factor) * (pair.2 : ZMod factor) =
    0

/-- The canonical primitive coordinates of the decoded terminal residual satisfy the
homogeneous terminal equation in every prime quotient. -/
theorem rationalPair_terminalResidual_isTerminalPairMod
    (parameters : Parameters)
    {centerNumerator driftNumerator scale : ℤ}
    (center_eq :
      parameters.center = (centerNumerator : ℚ) / scale)
    (drift_eq :
      drift parameters.center parameters.reset =
        (driftNumerator : ℚ) / scale)
    (scale_ne : scale ≠ 0)
    (factor : Nat) [Fact factor.Prime] :
    IsTerminalPairMod factor centerNumerator driftNumerator scale
      (rationalPair (terminalResidual parameters)) := by
  let terminal := terminalResidual parameters
  have scale_ne_rat : (scale : ℚ) ≠ 0 := by
    exact_mod_cast scale_ne
  have center_sub_one :
      parameters.center - 1 =
        (centerNumerator - scale : ℤ) / (scale : ℚ) := by
    rw [center_eq]
    rw [Int.cast_sub]
    field_simp [scale_ne_rat]
  have terminal_zero :
      (parameters.center - 1) * terminal +
          drift parameters.center parameters.reset = 0 := by
    dsimp [terminal]
    rw [terminalResidual]
    field_simp [parameters.center_sub_one_unit.1]
    ring
  have scaled_terminal_zero :
      (centerNumerator - scale : ℤ) * terminal +
          driftNumerator = 0 := by
    calc
      ((↑(centerNumerator - scale) : ℚ) * terminal +
          (driftNumerator : ℚ)) =
          scale * ((parameters.center - 1) * terminal +
            drift parameters.center parameters.reset) := by
        rw [center_sub_one, drift_eq]
        field_simp [scale_ne_rat]
      _ = 0 := by rw [terminal_zero]; simp
  have terminal_equation :
      (centerNumerator - scale : ℤ) * terminal.num +
          driftNumerator * terminal.den = 0 := by
    have numerator_eq :
        (terminal.num : ℚ) = terminal * terminal.den := by
      calc
        (terminal.num : ℚ) =
            ((terminal.num : ℚ) / terminal.den) * terminal.den := by
          field_simp
        _ = terminal * terminal.den := by rw [terminal.num_div_den]
    apply (Int.cast_injective :
      Function.Injective (fun integer : ℤ => (integer : ℚ)))
    push_cast
    rw [numerator_eq]
    rw [Int.cast_sub] at scaled_terminal_zero
    linear_combination (terminal.den : ℚ) * scaled_terminal_zero
  unfold IsTerminalPairMod
  simp only [rationalPair_fst, rationalPair_snd]
  simpa using
    congrArg (fun integer : ℤ => (integer : ZMod factor))
      terminal_equation

/-- At residue zero, every residual transfer is the terminal covector repeated in both rows. -/
theorem quotientTransfer_zero
    (factor prime depth : Nat) [Fact factor.Prime]
    (centerNumerator driftNumerator scale : ℤ) :
    quotientTransfer factor prime depth
        centerNumerator driftNumerator scale 0 =
      !![
        (centerNumerator : ZMod factor) - (scale : ZMod factor),
          (driftNumerator : ZMod factor);
        (centerNumerator : ZMod factor) - (scale : ZMod factor),
          (driftNumerator : ZMod factor)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quotientTransfer, integralResidualTransfer]

/-- A primitive homogeneous terminal pair is annihilated by the zero-residue quotient
transition. -/
theorem quotientTransition_zero_terminal_eq_cancelled
    {factor prime depth : Nat} [Fact factor.Prime]
    {centerNumerator driftNumerator scale : ℤ}
    {target : ℤ × ℤ}
    (target_primitive : IsCoprime target.1 target.2)
    (terminal : IsTerminalPairMod factor
      centerNumerator driftNumerator scale target) :
    quotientTransition
        (quotientTransfer factor prime depth
          centerNumerator driftNumerator scale 0)
        (quotientPairState factor target) = none := by
  let coordinates :
      Fin 2 → ZMod factor :=
    ![(target.1 : ZMod factor), (target.2 : ZMod factor)]
  have coordinates_ne : coordinates ≠ 0 :=
    zmod_pair_ne_zero_of_isCoprime target_primitive
  have coordinates_image_zero :
      Matrix.mulVec
          (quotientTransfer factor prime depth
            centerNumerator driftNumerator scale 0)
          coordinates = 0 := by
    rw [quotientTransfer_zero]
    ext i
    fin_cases i <;>
      simp [coordinates, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
        IsTerminalPairMod] at terminal ⊢
    all_goals exact terminal
  have weight_ne :
      ProjectiveLine.pairWeight
          (target.1 : ZMod factor) (target.2 : ZMod factor) ≠ 0 :=
    ProjectiveLine.pairWeight_ne_zero coordinates_ne
  have ray_image_zero :
      Matrix.mulVec
          (quotientTransfer factor prime depth
            centerNumerator driftNumerator scale 0)
          (ProjectiveLine.ray
            (ProjectiveLine.ofPair
              (target.1 : ZMod factor) (target.2 : ZMod factor))) = 0 := by
    have scaled_ray_zero :
        ProjectiveLine.pairWeight
            (target.1 : ZMod factor) (target.2 : ZMod factor) •
          Matrix.mulVec
            (quotientTransfer factor prime depth
              centerNumerator driftNumerator scale 0)
            (ProjectiveLine.ray
              (ProjectiveLine.ofPair
                (target.1 : ZMod factor) (target.2 : ZMod factor))) = 0 := by
      rw [← Matrix.mulVec_smul, ← ProjectiveLine.pair_eq_weight_smul_ray]
      exact coordinates_image_zero
    exact (smul_eq_zero.mp scaled_ray_zero).resolve_left weight_ne
  exact quotientTransition_point_of_image_eq_zero _ _ ray_image_zero

/-- Membership of a terminal pair in any quotient invariant forces annihilation at the
zero residue. -/
theorem terminal_mem_forces_cancelled
    {factor prime period depth : Nat} [Fact factor.Prime]
    (period_positive : 0 < period)
    {centerNumerator driftNumerator scale : ℤ}
    {target : ℤ × ℤ}
    (target_primitive : IsCoprime target.1 target.2)
    (terminal : IsTerminalPairMod factor
      centerNumerator driftNumerator scale target)
    {states : Set (QuotientState (ZMod factor))}
    (closed :
      QuotientInvariant factor prime period depth
        centerNumerator driftNumerator scale states)
    (target_mem : quotientPairState factor target ∈ states) :
    none ∈ states := by
  have image_mem := closed _ target_mem ⟨0, period_positive⟩
  rwa [quotientTransition_zero_terminal_eq_cancelled
    target_primitive terminal] at image_mem

/-- Existence of a closed quotient invariant containing the source and excluding
annihilation. -/
def HasCancellationFreeInvariant
    (factor prime period depth : Nat) [Fact factor.Prime]
    (centerNumerator driftNumerator scale : ℤ)
    (source : ℤ × ℤ) : Prop :=
  ∃ states : Set (QuotientState (ZMod factor)),
    QuotientInvariant factor prime period depth
        centerNumerator driftNumerator scale states ∧
      none ∉ states ∧
      quotientPairState factor source ∈ states

/-- Existence of a closed finite quotient invariant which contains the source while excluding
both annihilation and the target. -/
def HasQuotientCertificate
    (factor prime period depth : Nat) [Fact factor.Prime]
    (centerNumerator driftNumerator scale : ℤ)
    (source target : ℤ × ℤ) : Prop :=
  ∃ states : Set (QuotientState (ZMod factor)),
    QuotientInvariant factor prime period depth
        centerNumerator driftNumerator scale states ∧
      none ∉ states ∧
      quotientPairState factor source ∈ states ∧
      quotientPairState factor target ∉ states

/-- For a genuine terminal target, excluding annihilation already excludes the target. -/
theorem hasQuotientCertificate_iff_hasCancellationFreeInvariant
    {factor prime period depth : Nat} [Fact factor.Prime]
    (period_positive : 0 < period)
    {centerNumerator driftNumerator scale : ℤ}
    {source target : ℤ × ℤ}
    (target_primitive : IsCoprime target.1 target.2)
    (terminal : IsTerminalPairMod factor
      centerNumerator driftNumerator scale target) :
    HasQuotientCertificate factor prime period depth
        centerNumerator driftNumerator scale source target ↔
      HasCancellationFreeInvariant factor prime period depth
        centerNumerator driftNumerator scale source := by
  constructor
  · rintro ⟨states, closed, cancelled_absent, source_mem, _⟩
    exact ⟨states, closed, cancelled_absent, source_mem⟩
  · rintro ⟨states, closed, cancelled_absent, source_mem⟩
    refine ⟨states, closed, cancelled_absent, source_mem, ?_⟩
    intro target_mem
    exact cancelled_absent
      (terminal_mem_forces_cancelled period_positive target_primitive
        terminal closed target_mem)

/-- A cancellation-free invariant is already a physical immortality certificate; terminal
exclusion follows from its zero-residue transition. -/
theorem not_physical_isMortal_of_cancellationFreeQuotient
    (parameters : Parameters)
    {centerNumerator driftNumerator scale : ℤ}
    (center_eq :
      parameters.center = (centerNumerator : ℚ) / scale)
    (drift_eq :
      drift parameters.center parameters.reset =
        (driftNumerator : ℚ) / scale)
    (scale_ne : scale ≠ 0)
    {factor period : Nat} [Fact factor.Prime]
    (primitive :
      IsPrimitivePrimeDivisor factor parameters.prime period)
    {states : Set (QuotientState (ZMod factor))}
    (closed :
      QuotientInvariant factor parameters.prime period parameters.depth
        centerNumerator driftNumerator scale states)
    (cancelled_absent : none ∉ states)
    (reset_mem :
      quotientPairState factor (rationalPair 1) ∈ states) :
    ¬IsMortal
      (ReturnFamily.pairGenerator
        (ambient (parameters.prime : ℚ) parameters.depth)
        (cut parameters.center parameters.reset)) := by
  apply not_physical_isMortal_of_quotientInvariant parameters
    center_eq drift_eq scale_ne primitive closed cancelled_absent reset_mem
  intro terminal_mem
  exact cancelled_absent
    (terminal_mem_forces_cancelled primitive.exponent_positive
      (rationalPair_isCoprime (terminalResidual parameters))
      (rationalPair_terminalResidual_isTerminalPairMod parameters
        center_eq drift_eq scale_ne factor)
      closed terminal_mem)

/-- Reachability in one exact-order quotient automaton. -/
def QuotientReachable
    (factor prime period depth : Nat) [Fact factor.Prime]
    (centerNumerator driftNumerator scale : ℤ)
    (source target : QuotientState (ZMod factor)) : Prop :=
  Relation.ReflTransGen
    (QuotientStep factor prime period depth
      centerNumerator driftNumerator scale)
    source target

/-- The reachable quotient set is closed under every residue transition. -/
theorem quotientReachable_quotientInvariant
    (factor prime period depth : Nat) [Fact factor.Prime]
    (centerNumerator driftNumerator scale : ℤ)
    (source : QuotientState (ZMod factor)) :
    QuotientInvariant factor prime period depth
      centerNumerator driftNumerator scale
      {target | QuotientReachable factor prime period depth
        centerNumerator driftNumerator scale source target} := by
  intro target reachable residue
  exact reachable.tail ⟨residue, rfl⟩

/-- Every quotient invariant containing the source contains its full reachable closure. -/
theorem quotientReachable_mem_quotientInvariant
    {factor prime period depth : Nat} [Fact factor.Prime]
    {centerNumerator driftNumerator scale : ℤ}
    {source target : QuotientState (ZMod factor)}
    {states : Set (QuotientState (ZMod factor))}
    (closed :
      QuotientInvariant factor prime period depth
        centerNumerator driftNumerator scale states)
    (source_mem : source ∈ states)
    (reachable :
      QuotientReachable factor prime period depth
        centerNumerator driftNumerator scale source target) :
    target ∈ states := by
  induction reachable with
  | refl => exact source_mem
  | tail _ step induction =>
      obtain ⟨residue, transition⟩ := step
      rw [← transition]
      exact closed _ induction residue

/-- A cancellation-free invariant exists exactly when annihilation is unreachable from the
source. -/
theorem hasCancellationFreeInvariant_iff_cancelled_unreachable
    {factor prime period depth : Nat} [Fact factor.Prime]
    {centerNumerator driftNumerator scale : ℤ}
    {source : ℤ × ℤ} :
    HasCancellationFreeInvariant factor prime period depth
        centerNumerator driftNumerator scale source ↔
      ¬QuotientReachable factor prime period depth
        centerNumerator driftNumerator scale
        (quotientPairState factor source) none := by
  constructor
  · rintro ⟨states, closed, cancelled_absent, source_mem⟩ reachable
    exact cancelled_absent
      (quotientReachable_mem_quotientInvariant
        closed source_mem reachable)
  · intro cancelled_unreachable
    refine ⟨
      {target |
        QuotientReachable factor prime period depth
          centerNumerator driftNumerator scale
          (quotientPairState factor source) target},
      quotientReachable_quotientInvariant factor prime period depth
        centerNumerator driftNumerator scale
        (quotientPairState factor source),
      cancelled_unreachable,
      Relation.ReflTransGen.refl⟩

/-- For a terminal target, finite quotient certification is precisely cancellation
unreachability. -/
theorem hasQuotientCertificate_iff_cancelled_unreachable
    {factor prime period depth : Nat} [Fact factor.Prime]
    (period_positive : 0 < period)
    {centerNumerator driftNumerator scale : ℤ}
    {source target : ℤ × ℤ}
    (target_primitive : IsCoprime target.1 target.2)
    (terminal : IsTerminalPairMod factor
      centerNumerator driftNumerator scale target) :
    HasQuotientCertificate factor prime period depth
        centerNumerator driftNumerator scale source target ↔
      ¬QuotientReachable factor prime period depth
        centerNumerator driftNumerator scale
        (quotientPairState factor source) none :=
  (hasQuotientCertificate_iff_hasCancellationFreeInvariant
    period_positive target_primitive terminal).trans
    hasCancellationFreeInvariant_iff_cancelled_unreachable

/-- Unreachability of cancellation in one finite exact-order quotient directly certifies
physical immortality. -/
theorem not_physical_isMortal_of_cancelled_unreachable
    (parameters : Parameters)
    {centerNumerator driftNumerator scale : ℤ}
    (center_eq :
      parameters.center = (centerNumerator : ℚ) / scale)
    (drift_eq :
      drift parameters.center parameters.reset =
        (driftNumerator : ℚ) / scale)
    (scale_ne : scale ≠ 0)
    {factor period : Nat} [Fact factor.Prime]
    (primitive :
      IsPrimitivePrimeDivisor factor parameters.prime period)
    (cancelled_unreachable :
      ¬QuotientReachable factor parameters.prime period parameters.depth
        centerNumerator driftNumerator scale
        (quotientPairState factor (rationalPair 1)) none) :
    ¬IsMortal
      (ReturnFamily.pairGenerator
        (ambient (parameters.prime : ℚ) parameters.depth)
        (cut parameters.center parameters.reset)) := by
  obtain ⟨states, closed, cancelled_absent, reset_mem⟩ :=
    hasCancellationFreeInvariant_iff_cancelled_unreachable.mpr
      cancelled_unreachable
  exact not_physical_isMortal_of_cancellationFreeQuotient parameters
    center_eq drift_eq scale_ne primitive closed cancelled_absent reset_mem

/-- One raw wait applied simultaneously in two prime quotients. -/
noncomputable def synchronizedQuotientTransition
    (leftFactor rightFactor prime depth : Nat)
    [Fact leftFactor.Prime] [Fact rightFactor.Prime]
    (centerNumerator driftNumerator scale : ℤ) (wait : Nat) :
    QuotientState (ZMod leftFactor) × QuotientState (ZMod rightFactor) →
      QuotientState (ZMod leftFactor) × QuotientState (ZMod rightFactor) :=
  fun state =>
    (quotientTransition
        (quotientTransfer leftFactor prime depth
          centerNumerator driftNumerator scale wait)
        state.1,
      quotientTransition
        (quotientTransfer rightFactor prime depth
          centerNumerator driftNumerator scale wait)
        state.2)

/-- A joint state set closed under every common wait in two prime quotients. -/
def SynchronizedQuotientInvariant
    (leftFactor rightFactor prime leftPeriod rightPeriod depth : Nat)
    [Fact leftFactor.Prime] [Fact rightFactor.Prime]
    (centerNumerator driftNumerator scale : ℤ)
    (states :
      Set
        (QuotientState (ZMod leftFactor) ×
          QuotientState (ZMod rightFactor))) : Prop :=
  ∀ state ∈ states, ∀ residue : Fin (leftPeriod.lcm rightPeriod),
    synchronizedQuotientTransition leftFactor rightFactor prime depth
        centerNumerator driftNumerator scale residue state ∈ states

/-- A common-wait product invariant containing reset and excluding cancellation in either
component. -/
def HasSynchronizedCancellationFreeInvariant
    (leftFactor rightFactor prime leftPeriod rightPeriod depth : Nat)
    [Fact leftFactor.Prime] [Fact rightFactor.Prime]
    (centerNumerator driftNumerator scale : ℤ)
    (source : ℤ × ℤ) : Prop :=
  ∃ states :
      Set
        (QuotientState (ZMod leftFactor) ×
          QuotientState (ZMod rightFactor)),
    SynchronizedQuotientInvariant leftFactor rightFactor prime
        leftPeriod rightPeriod depth
        centerNumerator driftNumerator scale states ∧
      (∀ state ∈ states, state.1 ≠ none ∧ state.2 ≠ none) ∧
      (quotientPairState leftFactor source,
          quotientPairState rightFactor source) ∈ states

/-- Projection of a synchronized invariant onto its left quotient is a quotient invariant. -/
theorem synchronizedQuotientInvariant_leftProjection
    {leftFactor rightFactor prime leftPeriod rightPeriod depth : Nat}
    [Fact leftFactor.Prime] [Fact rightFactor.Prime]
    {centerNumerator driftNumerator scale : ℤ}
    {states :
      Set
        (QuotientState (ZMod leftFactor) ×
          QuotientState (ZMod rightFactor))}
    (closed :
      SynchronizedQuotientInvariant leftFactor rightFactor prime
        leftPeriod rightPeriod depth
        centerNumerator driftNumerator scale states)
    (leftPeriod_positive : 0 < leftPeriod)
    (rightPeriod_positive : 0 < rightPeriod) :
    QuotientInvariant leftFactor prime leftPeriod depth
      centerNumerator driftNumerator scale
      {left | ∃ right, (left, right) ∈ states} := by
  rintro left ⟨right, pair_mem⟩ residue
  have left_le_joint :
      leftPeriod ≤ leftPeriod.lcm rightPeriod :=
    Nat.le_of_dvd
      (Nat.lcm_pos leftPeriod_positive rightPeriod_positive)
      (Nat.dvd_lcm_left leftPeriod rightPeriod)
  let jointResidue : Fin (leftPeriod.lcm rightPeriod) :=
    ⟨residue, residue.isLt.trans_le left_le_joint⟩
  refine ⟨
    quotientTransition
      (quotientTransfer rightFactor prime depth
        centerNumerator driftNumerator scale jointResidue)
      right,
    ?_⟩
  simpa [synchronizedQuotientTransition] using
    closed (left, right) pair_mem jointResidue

/-- Projection of a synchronized invariant onto its right quotient is a quotient invariant. -/
theorem synchronizedQuotientInvariant_rightProjection
    {leftFactor rightFactor prime leftPeriod rightPeriod depth : Nat}
    [Fact leftFactor.Prime] [Fact rightFactor.Prime]
    {centerNumerator driftNumerator scale : ℤ}
    {states :
      Set
        (QuotientState (ZMod leftFactor) ×
          QuotientState (ZMod rightFactor))}
    (closed :
      SynchronizedQuotientInvariant leftFactor rightFactor prime
        leftPeriod rightPeriod depth
        centerNumerator driftNumerator scale states)
    (leftPeriod_positive : 0 < leftPeriod)
    (rightPeriod_positive : 0 < rightPeriod) :
    QuotientInvariant rightFactor prime rightPeriod depth
      centerNumerator driftNumerator scale
      {right | ∃ left, (left, right) ∈ states} := by
  rintro right ⟨left, pair_mem⟩ residue
  have right_le_joint :
      rightPeriod ≤ leftPeriod.lcm rightPeriod :=
    Nat.le_of_dvd
      (Nat.lcm_pos leftPeriod_positive rightPeriod_positive)
      (Nat.dvd_lcm_right leftPeriod rightPeriod)
  let jointResidue : Fin (leftPeriod.lcm rightPeriod) :=
    ⟨residue, residue.isLt.trans_le right_le_joint⟩
  refine ⟨
    quotientTransition
      (quotientTransfer leftFactor prime depth
        centerNumerator driftNumerator scale jointResidue)
      left,
    ?_⟩
  simpa [synchronizedQuotientTransition] using
    closed (left, right) pair_mem jointResidue

/-- Every cancellation-free synchronized certificate projects to a cancellation-free
certificate in each factor. -/
theorem hasSynchronizedCancellationFreeInvariant_imp_components
    {leftFactor rightFactor prime leftPeriod rightPeriod depth : Nat}
    [Fact leftFactor.Prime] [Fact rightFactor.Prime]
    (leftPeriod_positive : 0 < leftPeriod)
    (rightPeriod_positive : 0 < rightPeriod)
    {centerNumerator driftNumerator scale : ℤ}
    {source : ℤ × ℤ} :
    HasSynchronizedCancellationFreeInvariant
        leftFactor rightFactor prime leftPeriod rightPeriod depth
        centerNumerator driftNumerator scale source →
      HasCancellationFreeInvariant leftFactor prime leftPeriod depth
          centerNumerator driftNumerator scale source ∧
        HasCancellationFreeInvariant rightFactor prime rightPeriod depth
          centerNumerator driftNumerator scale source := by
  rintro ⟨states, closed, cancellation_free, source_mem⟩
  constructor
  · refine ⟨
      {left | ∃ right, (left, right) ∈ states},
      synchronizedQuotientInvariant_leftProjection closed
        leftPeriod_positive rightPeriod_positive,
      ?_,
      ⟨quotientPairState rightFactor source, source_mem⟩⟩
    rintro ⟨right, pair_mem⟩
    exact (cancellation_free (none, right) pair_mem).1 rfl
  · refine ⟨
      {right | ∃ left, (left, right) ∈ states},
      synchronizedQuotientInvariant_rightProjection closed
        leftPeriod_positive rightPeriod_positive,
      ?_,
      ⟨quotientPairState leftFactor source, source_mem⟩⟩
    rintro ⟨left, pair_mem⟩
    exact (cancellation_free (left, none) pair_mem).2 rfl

/-- Synchronized products cannot create a terminal certificate absent from either component:
every safe joint invariant already yields both single-factor certificates. -/
theorem hasSynchronizedCancellationFreeInvariant_imp_quotientCertificates
    {leftFactor rightFactor prime leftPeriod rightPeriod depth : Nat}
    [Fact leftFactor.Prime] [Fact rightFactor.Prime]
    (leftPeriod_positive : 0 < leftPeriod)
    (rightPeriod_positive : 0 < rightPeriod)
    {centerNumerator driftNumerator scale : ℤ}
    {source target : ℤ × ℤ}
    (target_primitive : IsCoprime target.1 target.2)
    (left_terminal :
      IsTerminalPairMod leftFactor
        centerNumerator driftNumerator scale target)
    (right_terminal :
      IsTerminalPairMod rightFactor
        centerNumerator driftNumerator scale target) :
    HasSynchronizedCancellationFreeInvariant
        leftFactor rightFactor prime leftPeriod rightPeriod depth
        centerNumerator driftNumerator scale source →
      HasQuotientCertificate leftFactor prime leftPeriod depth
          centerNumerator driftNumerator scale source target ∧
        HasQuotientCertificate rightFactor prime rightPeriod depth
          centerNumerator driftNumerator scale source target := by
  intro synchronized
  obtain ⟨left, right⟩ :=
    hasSynchronizedCancellationFreeInvariant_imp_components
      leftPeriod_positive rightPeriod_positive synchronized
  exact ⟨
    (hasQuotientCertificate_iff_hasCancellationFreeInvariant
      leftPeriod_positive target_primitive left_terminal).mpr left,
    (hasQuotientCertificate_iff_hasCancellationFreeInvariant
      rightPeriod_positive target_primitive right_terminal).mpr right⟩

end
end MatrixMortality.ReturnGuard
