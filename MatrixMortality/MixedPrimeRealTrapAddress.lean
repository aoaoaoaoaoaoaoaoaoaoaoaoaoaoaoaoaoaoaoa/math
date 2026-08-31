import MatrixMortality.MixedPrimeRealTrapReset

/-!
# Fixed-source rays in the mixed-prime real trap

For a source in the real trap, changing the wait changes only the target's Archimedean band
depth.  The normalized target mantissa is fixed by one of three source intervals.
-/

namespace MatrixMortality.MixedPrimeDebt

open PeriodicShell

/-- Above `1/3`, every wait from one source lies on the normalized ray with mantissa `2·source`.
The target band depth is the wait itself. -/
theorem shellStep_realTrap_upperRay
    (wait : ℕ) {source : ℚ} (source_lower : 1 / 3 < source)
    (source_upper : source ≤ 1 / 2) :
    shellStep wait source = realTrapBandPoint wait (2 * source) ∧
      realTrapMaxPredecessorWait (shellStep wait source) = wait := by
  have mantissa_lower : (2 / 3 : ℚ) < 2 * source := by linarith
  have mantissa_upper : 2 * source ≤ (1 : ℚ) := by linarith
  have point_eq :
      shellStep wait source = realTrapBandPoint wait (2 * source) := by
    simp only [shellStep, realTrapBandPoint]
    ring
  refine ⟨point_eq, ?_⟩
  rw [point_eq]
  exact realTrapMaxPredecessorWait_bandPoint wait mantissa_lower mantissa_upper

/-- Between `2/9` and `1/3`, every wait from one source lies on the normalized ray with
mantissa `3·source`.  The target band depth is one more than the wait. -/
theorem shellStep_realTrap_middleRay
    (wait : ℕ) {source : ℚ} (source_lower : 2 / 9 < source)
    (source_upper : source ≤ 1 / 3) :
    shellStep wait source = realTrapBandPoint (wait + 1) (3 * source) ∧
      realTrapMaxPredecessorWait (shellStep wait source) = wait + 1 := by
  have mantissa_lower : (2 / 3 : ℚ) < 3 * source := by linarith
  have mantissa_upper : 3 * source ≤ (1 : ℚ) := by linarith
  have point_eq :
      shellStep wait source = realTrapBandPoint (wait + 1) (3 * source) := by
    simp only [shellStep, realTrapBandPoint, pow_succ]
    ring
  refine ⟨point_eq, ?_⟩
  rw [point_eq]
  exact realTrapMaxPredecessorWait_bandPoint (wait + 1) mantissa_lower mantissa_upper

/-- At or below `2/9`, every wait from one source lies on the normalized ray with mantissa
`(9/2)·source`.  The target band depth is two more than the wait. -/
theorem shellStep_realTrap_lowerRay
    (wait : ℕ) {source : ℚ} (source_lower : 1 / 5 < source)
    (source_upper : source ≤ 2 / 9) :
    shellStep wait source = realTrapBandPoint (wait + 2) ((9 / 2) * source) ∧
      realTrapMaxPredecessorWait (shellStep wait source) = wait + 2 := by
  have mantissa_lower : (2 / 3 : ℚ) < (9 / 2) * source := by linarith
  have mantissa_upper : (9 / 2) * source ≤ (1 : ℚ) := by linarith
  have point_eq :
      shellStep wait source = realTrapBandPoint (wait + 2) ((9 / 2) * source) := by
    simp only [shellStep, realTrapBandPoint, pow_add]
    norm_num
    ring
  refine ⟨point_eq, ?_⟩
  rw [point_eq]
  exact realTrapMaxPredecessorWait_bandPoint (wait + 2) mantissa_lower mantissa_upper

/-- Above `1/3`, fixed-source one-step reachability is one computable ray equality. -/
theorem exists_shellStep_realTrap_upper_iff_candidate
    {source target : ℚ} (source_lower : 1 / 3 < source)
    (source_upper : source ≤ 1 / 2) :
    (∃ wait, shellStep wait source = target) ↔
      target = realTrapBandPoint (realTrapMaxPredecessorWait target) (2 * source) := by
  constructor
  · rintro ⟨wait, step_eq⟩
    have ray := shellStep_realTrap_upperRay wait source_lower source_upper
    have depth_eq : realTrapMaxPredecessorWait target = wait := by
      rw [← step_eq]
      exact ray.2
    rw [depth_eq]
    exact step_eq.symm.trans ray.1
  · intro candidate_eq
    let wait := realTrapMaxPredecessorWait target
    refine ⟨wait, ?_⟩
    exact (shellStep_realTrap_upperRay wait source_lower source_upper).1.trans
      candidate_eq.symm

/-- In `(2/9,1/3]`, fixed-source one-step reachability is one computable ray equality, provided
the target ray has reached depth one. -/
theorem exists_shellStep_realTrap_middle_iff_candidate
    {source target : ℚ} (source_lower : 2 / 9 < source)
    (source_upper : source ≤ 1 / 3) :
    (∃ wait, shellStep wait source = target) ↔
      1 ≤ realTrapMaxPredecessorWait target ∧
        target = realTrapBandPoint (realTrapMaxPredecessorWait target) (3 * source) := by
  constructor
  · rintro ⟨wait, step_eq⟩
    have ray := shellStep_realTrap_middleRay wait source_lower source_upper
    have depth_eq : realTrapMaxPredecessorWait target = wait + 1 := by
      rw [← step_eq]
      exact ray.2
    refine ⟨by rw [depth_eq]; omega, ?_⟩
    rw [depth_eq]
    exact step_eq.symm.trans ray.1
  · rintro ⟨depth_lower, candidate_eq⟩
    let wait := realTrapMaxPredecessorWait target - 1
    have depth_eq : wait + 1 = realTrapMaxPredecessorWait target := by
      simp only [wait]
      omega
    refine ⟨wait, ?_⟩
    exact (shellStep_realTrap_middleRay wait source_lower source_upper).1.trans
      (depth_eq ▸ candidate_eq.symm)

/-- In `(1/5,2/9]`, fixed-source one-step reachability is one computable ray equality, provided
the target ray has reached depth two. -/
theorem exists_shellStep_realTrap_lower_iff_candidate
    {source target : ℚ} (source_lower : 1 / 5 < source)
    (source_upper : source ≤ 2 / 9) :
    (∃ wait, shellStep wait source = target) ↔
      2 ≤ realTrapMaxPredecessorWait target ∧
        target = realTrapBandPoint
          (realTrapMaxPredecessorWait target) ((9 / 2) * source) := by
  constructor
  · rintro ⟨wait, step_eq⟩
    have ray := shellStep_realTrap_lowerRay wait source_lower source_upper
    have depth_eq : realTrapMaxPredecessorWait target = wait + 2 := by
      rw [← step_eq]
      exact ray.2
    refine ⟨by rw [depth_eq]; omega, ?_⟩
    rw [depth_eq]
    exact step_eq.symm.trans ray.1
  · rintro ⟨depth_lower, candidate_eq⟩
    let wait := realTrapMaxPredecessorWait target - 2
    have depth_eq : wait + 2 = realTrapMaxPredecessorWait target := by
      simp only [wait]
      omega
    refine ⟨wait, ?_⟩
    exact (shellStep_realTrap_lowerRay wait source_lower source_upper).1.trans
      (depth_eq ▸ candidate_eq.symm)

end MatrixMortality.MixedPrimeDebt
