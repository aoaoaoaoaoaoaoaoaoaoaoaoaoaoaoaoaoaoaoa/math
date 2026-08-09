import Frankl.OrbitReindex

namespace Frankl

open Real Set

theorem halfSupported_pair_low_of_mean_lt_half {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1)
    (hxRange : x ≤ 1 / 2 ∨ x = 1) (hyRange : y ≤ 1 / 2 ∨ y = 1)
    (hmean : (x + y) / 2 < 1 / 2) :
    x ≤ 1 / 2 ∧ y ≤ 1 / 2 := by
  constructor
  · rcases hxRange with hxHalf | rfl
    · exact hxHalf
    · linarith [hy.1]
  · rcases hyRange with hyHalf | rfl
    · exact hyHalf
    · linarith [hx.1]

theorem halfSupported_pair_low_of_max_ne_one {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1)
    (hxRange : x ≤ 1 / 2 ∨ x = 1) (hyRange : y ≤ 1 / 2 ∨ y = 1)
    (hmax : max x y ≠ 1) :
    x ≤ 1 / 2 ∧ y ≤ 1 / 2 := by
  constructor
  · rcases hxRange with hxHalf | hxOne
    · exact hxHalf
    · exfalso
      apply hmax
      rw [hxOne, max_eq_left hy.2]
  · rcases hyRange with hyHalf | hyOne
    · exact hyHalf
    · exfalso
      apply hmax
      rw [hyOne, max_eq_right hx.2]

/-- A fully identified one-orbit extreme on half-support coordinates collapses to the diagonal
point at the candidate mean. -/
theorem identifiedSingle_collapse_to_diagonal {ι : Type*} [Fintype ι]
    {left right : ι → ℝ}
    (hleft : ∀ i, left i ∈ Icc (0 : ℝ) 1)
    (hright : ∀ i, right i ∈ Icc (0 : ℝ) 1)
    (hhalf : HasHalfSupportCoordinates left right)
    (law : FiniteOrbitLaw left right abundanceTarget)
    {i : ι} (hi : i ∈ law.support) (hcard : law.support.card = 1)
    (hmean : orbitMean left right i = abundanceTarget) :
    orbitYuGap (singleLowOrbitLaw abundanceTarget 0) ≤ orbitYuGap law := by
  let single := reindexedSingleOrbitLaw law hi hcard
  let sorted := sortedOrbitLaw single
  let d := (max (left i) (right i) - min (left i) (right i)) / 2
  have hsingleGap : orbitYuGap single = orbitYuGap law :=
    reindexedSingleOrbitLaw_gap_eq law hi hcard
  have hsortedGap : orbitYuGap sorted = orbitYuGap single := sortedOrbitLaw_gap_eq single
  have hlow := halfSupported_pair_low_of_mean_lt_half
    (hleft i) (hright i) (hhalf i).1 (hhalf i).2 (by
      rw [show (left i + right i) / 2 = abundanceTarget by simpa [orbitMean] using hmean]
      exact abundanceTarget_lt_half)
  have haLower : 0 ≤ abundanceTarget - d := by
    have hcenter : (left i + right i) / 2 = abundanceTarget := by
      simpa [orbitMean] using hmean
    rw [← hcenter]
    dsimp [d]
    rw [show (left i + right i) / 2
        - (max (left i) (right i) - min (left i) (right i)) / 2 =
      min (left i) (right i) by
        rcases le_total (left i) (right i) with h | h <;>
          simp [min_eq_left, min_eq_right, max_eq_left, max_eq_right, h] <;> ring]
    exact le_min (hleft i).1 (hright i).1
  have haUpper : abundanceTarget + d ≤ 1 / 2 := by
    have hcenter : (left i + right i) / 2 = abundanceTarget := by
      simpa [orbitMean] using hmean
    rw [← hcenter]
    dsimp [d]
    rw [show (left i + right i) / 2
        + (max (left i) (right i) - min (left i) (right i)) / 2 =
      max (left i) (right i) by
        rcases le_total (left i) (right i) with h | h <;>
          simp [min_eq_left, min_eq_right, max_eq_left, max_eq_right, h] <;> ring]
    exact max_le hlow.1 hlow.2
  have hd : 0 ≤ d := div_nonneg (sub_nonneg.2
    (min_le_max : min (left i) (right i) ≤ max (left i) (right i))) (by norm_num)
  have hleftSorted :
      (sortedOrbitLeft (Function.const Unit (left i))
        (Function.const Unit (right i))) () = abundanceTarget - d := by
    have hcenter : (left i + right i) / 2 = abundanceTarget := by
      simpa [orbitMean] using hmean
    rw [← hcenter]
    dsimp [d, sortedOrbitLeft]
    rcases le_total (left i) (right i) with h | h <;>
      simp [min_eq_left, min_eq_right, max_eq_left, max_eq_right, h] <;> ring
  have hrightSorted :
      (sortedOrbitRight (Function.const Unit (left i))
        (Function.const Unit (right i))) () = abundanceTarget + d := by
    have hcenter : (left i + right i) / 2 = abundanceTarget := by
      simpa [orbitMean] using hmean
    rw [← hcenter]
    dsimp [d, sortedOrbitRight]
    rcases le_total (left i) (right i) with h | h <;>
      simp [min_eq_left, min_eq_right, max_eq_left, max_eq_right, h] <;> ring
  have hcanonical := singleLowOrbitLaw_gap_eq_of_coordinates sorted
    hleftSorted hrightSorted (by simp [sorted, single, sortedOrbitLaw,
      reindexedSingleOrbitLaw])
  have hcollapse := singleLowOrbit_collapse_le haLower haUpper hd
  exact ((hcollapse.trans_eq hcanonical).trans_eq hsortedGap).trans_eq hsingleGap

/-- A fully identified two-orbit extreme on half-support coordinates contracts to either the
canonical diagonal–diagonal family or the canonical diagonal–endpoint family. -/
theorem identifiedPair_collapse_to_canonical {ι : Type*} [Fintype ι]
    {left right : ι → ℝ}
    (hleft : ∀ i, left i ∈ Icc (0 : ℝ) 1)
    (hright : ∀ i, right i ∈ Icc (0 : ℝ) 1)
    (hhalf : HasHalfSupportCoordinates left right)
    (law : FiniteOrbitLaw left right abundanceTarget)
    {lower upper : ι} (hlowerUpper : lower ≠ upper)
    (hlower : lower ∈ law.support) (hupper : upper ∈ law.support)
    (hcard : law.support.card = 2)
    (hlowerMean : orbitMean left right lower < abundanceTarget)
    (hupperMean : abundanceTarget < orbitMean left right upper)
    (hlowerWeight : law.weight lower =
      lowerOrbitWeight (orbitMean left right lower) abundanceTarget
        (orbitMean left right upper))
    (hupperWeight : law.weight upper =
      upperOrbitWeight (orbitMean left right lower) abundanceTarget
        (orbitMean left right upper)) :
    (∃ a b : ℝ, ∃ haTarget : a ≤ abundanceTarget,
      ∃ htargetB : abundanceTarget ≤ b, ∃ hab : a < b,
        0 ≤ a ∧ b ≤ 1 / 2
          ∧ orbitYuGap
              (twoLowOrbitLaw a 0 abundanceTarget b 0 haTarget htargetB hab) ≤
            orbitYuGap law) ∨
      ∃ a q : ℝ, ∃ haTarget : a ≤ abundanceTarget,
        ∃ htargetEndpoint : abundanceTarget ≤ endpointOrbitMean q,
          ∃ haEndpoint : a < endpointOrbitMean q,
            0 ≤ a ∧ 0 ≤ q ∧ q ≤ 1
              ∧ orbitYuGap
                  (lowEndpointOrbitLaw a 0 abundanceTarget q haTarget htargetEndpoint
                    haEndpoint) ≤ orbitYuGap law := by
  let paired := reindexedPairOrbitLaw law hlowerUpper hlower hupper hcard
  let sorted := sortedOrbitLaw paired
  let a := orbitMean left right lower
  let d := (max (left lower) (right lower) - min (left lower) (right lower)) / 2
  let b := orbitMean left right upper
  let e := (max (left upper) (right upper) - min (left upper) (right upper)) / 2
  have hpairedGap : orbitYuGap paired = orbitYuGap law :=
    reindexedPairOrbitLaw_gap_eq law hlowerUpper hlower hupper hcard
  have hsortedGap : orbitYuGap sorted = orbitYuGap paired := sortedOrbitLaw_gap_eq paired
  have haTarget : a ≤ abundanceTarget := hlowerMean.le
  have htargetB : abundanceTarget ≤ b := hupperMean.le
  have hab : a < b := hlowerMean.trans hupperMean
  have hlowerLow := halfSupported_pair_low_of_mean_lt_half
    (hleft lower) (hright lower) (hhalf lower).1 (hhalf lower).2
    (hlowerMean.trans abundanceTarget_lt_half)
  have haLower : 0 ≤ a - d := by
    dsimp [a, d, orbitMean]
    rw [show (left lower + right lower) / 2
        - (max (left lower) (right lower) - min (left lower) (right lower)) / 2 =
      min (left lower) (right lower) by
        rcases le_total (left lower) (right lower) with h | h <;>
          simp [min_eq_left, min_eq_right, max_eq_left, max_eq_right, h] <;> ring]
    exact le_min (hleft lower).1 (hright lower).1
  have haUpper : a + d ≤ 1 / 2 := by
    dsimp [a, d, orbitMean]
    rw [show (left lower + right lower) / 2
        + (max (left lower) (right lower) - min (left lower) (right lower)) / 2 =
      max (left lower) (right lower) by
        rcases le_total (left lower) (right lower) with h | h <;>
          simp [min_eq_left, min_eq_right, max_eq_left, max_eq_right, h] <;> ring]
    exact max_le hlowerLow.1 hlowerLow.2
  have hd : 0 ≤ d := by
    exact div_nonneg (sub_nonneg.2
      (min_le_max : min (left lower) (right lower) ≤ max (left lower) (right lower)))
      (by norm_num)
  have hleftLower :
      (sortedOrbitLeft (reindexedPairCoordinate left lower upper)
        (reindexedPairCoordinate right lower upper)) false = a - d := by
    dsimp [a, d, paired, sorted, sortedOrbitLeft, reindexedPairCoordinate, orbitMean]
    rcases le_total (left lower) (right lower) with h | h <;>
      simp [min_eq_left, min_eq_right, max_eq_left, max_eq_right, h] <;> ring
  have hrightLower :
      (sortedOrbitRight (reindexedPairCoordinate left lower upper)
        (reindexedPairCoordinate right lower upper)) false = a + d := by
    dsimp [a, d, paired, sorted, sortedOrbitRight, reindexedPairCoordinate, orbitMean]
    rcases le_total (left lower) (right lower) with h | h <;>
      simp [min_eq_left, min_eq_right, max_eq_left, max_eq_right, h] <;> ring
  have hsortedLowerWeight : sorted.weight false = lowerOrbitWeight a abundanceTarget b := by
    simpa [sorted, paired, sortedOrbitLaw, reindexedPairOrbitLaw, reindexedPairWeight, a, b]
      using hlowerWeight
  have hsortedUpperWeight : sorted.weight true = upperOrbitWeight a abundanceTarget b := by
    simpa [sorted, paired, sortedOrbitLaw, reindexedPairOrbitLaw, reindexedPairWeight, a, b]
      using hupperWeight
  by_cases hupperEndpoint : max (left upper) (right upper) = 1
  · let q := min (left upper) (right upper)
    have hqZero : 0 ≤ q := le_min (hleft upper).1 (hright upper).1
    have hqOne : q ≤ 1 := (min_le_left _ _).trans (hleft upper).2
    have hbEndpoint : b = endpointOrbitMean q := by
      dsimp [b, q, orbitMean, endpointOrbitMean]
      calc
        (left upper + right upper) / 2 =
            (min (left upper) (right upper) + max (left upper) (right upper)) / 2 := by
          rw [min_add_max]
        _ = (min (left upper) (right upper) + 1) / 2 := by rw [hupperEndpoint]
    have htargetEndpoint : abundanceTarget ≤ endpointOrbitMean q := by
      rw [← hbEndpoint]
      exact htargetB
    have haEndpoint : a < endpointOrbitMean q := by
      rw [← hbEndpoint]
      exact hab
    have hleftUpper :
        (sortedOrbitLeft (reindexedPairCoordinate left lower upper)
          (reindexedPairCoordinate right lower upper)) true = q := by
      rfl
    have hrightUpper :
        (sortedOrbitRight (reindexedPairCoordinate left lower upper)
          (reindexedPairCoordinate right lower upper)) true = 1 := by
      exact hupperEndpoint
    have hcanonical := lowEndpointOrbitLaw_gap_eq_of_coordinates sorted
      haTarget htargetEndpoint haEndpoint hleftLower hrightLower hleftUpper hrightUpper
      (by simpa [hbEndpoint] using hsortedLowerWeight)
      (by simpa [hbEndpoint] using hsortedUpperWeight)
    have hcollapse := lowEndpointOrbit_collapse_le haLower haUpper hd hqZero hqOne
      haTarget htargetEndpoint haEndpoint
    exact Or.inr ⟨a, q, haTarget, htargetEndpoint, haEndpoint,
      by linarith [haLower], hqZero, hqOne,
      (((hcollapse.trans_eq hcanonical).trans_eq hsortedGap).trans_eq hpairedGap)⟩
  · have hupperLow := halfSupported_pair_low_of_max_ne_one
      (hleft upper) (hright upper) (hhalf upper).1 (hhalf upper).2 hupperEndpoint
    have hbLower : 0 ≤ b - e := by
      dsimp [b, e, orbitMean]
      rw [show (left upper + right upper) / 2
          - (max (left upper) (right upper) - min (left upper) (right upper)) / 2 =
        min (left upper) (right upper) by
          rcases le_total (left upper) (right upper) with h | h <;>
            simp [min_eq_left, min_eq_right, max_eq_left, max_eq_right, h] <;> ring]
      exact le_min (hleft upper).1 (hright upper).1
    have hbUpper : b + e ≤ 1 / 2 := by
      dsimp [b, e, orbitMean]
      rw [show (left upper + right upper) / 2
          + (max (left upper) (right upper) - min (left upper) (right upper)) / 2 =
        max (left upper) (right upper) by
          rcases le_total (left upper) (right upper) with h | h <;>
            simp [min_eq_left, min_eq_right, max_eq_left, max_eq_right, h] <;> ring]
      exact max_le hupperLow.1 hupperLow.2
    have he : 0 ≤ e := by
      exact div_nonneg (sub_nonneg.2
        (min_le_max : min (left upper) (right upper) ≤ max (left upper) (right upper)))
        (by norm_num)
    have hleftUpper :
        (sortedOrbitLeft (reindexedPairCoordinate left lower upper)
          (reindexedPairCoordinate right lower upper)) true = b - e := by
      dsimp [b, e, paired, sorted, sortedOrbitLeft, reindexedPairCoordinate, orbitMean]
      rcases le_total (left upper) (right upper) with h | h <;>
        simp [min_eq_left, min_eq_right, max_eq_left, max_eq_right, h] <;> ring
    have hrightUpper :
        (sortedOrbitRight (reindexedPairCoordinate left lower upper)
          (reindexedPairCoordinate right lower upper)) true = b + e := by
      dsimp [b, e, paired, sorted, sortedOrbitRight, reindexedPairCoordinate, orbitMean]
      rcases le_total (left upper) (right upper) with h | h <;>
        simp [min_eq_left, min_eq_right, max_eq_left, max_eq_right, h] <;> ring
    have hcanonical := twoLowOrbitLaw_gap_eq_of_coordinates sorted haTarget htargetB hab
      hleftLower hrightLower hleftUpper hrightUpper
      hsortedLowerWeight hsortedUpperWeight
    have hcollapse := twoLowOrbit_target_collapse_le haLower haUpper hd hbLower hbUpper he
      haTarget htargetB hab
    exact Or.inl ⟨a, b, haTarget, htargetB, hab, by linarith [haLower],
      by linarith [hbUpper, he],
      (((hcollapse.trans_eq hcanonical).trans_eq hsortedGap).trans_eq hpairedGap)⟩

/-- Complete analytic reduction on the exact target slice: every finite symmetric coupling has
a no-worse diagonal point, diagonal–diagonal law, or diagonal–endpoint law. -/
theorem orbitYuGap_exists_canonical_of_mem {ι : Type*} [Fintype ι]
    {left right : ι → ℝ}
    (hleft : ∀ i, left i ∈ Icc (0 : ℝ) 1)
    (hright : ∀ i, right i ∈ Icc (0 : ℝ) 1)
    (law : FiniteOrbitLaw left right abundanceTarget) :
    orbitYuGap (singleLowOrbitLaw abundanceTarget 0) ≤ orbitYuGap law ∨
      ((∃ a b : ℝ, ∃ haTarget : a ≤ abundanceTarget,
        ∃ htargetB : abundanceTarget ≤ b, ∃ hab : a < b,
          0 ≤ a ∧ b ≤ 1 / 2
            ∧ orbitYuGap
                (twoLowOrbitLaw a 0 abundanceTarget b 0 haTarget htargetB hab) ≤
              orbitYuGap law) ∨
        ∃ a q : ℝ, ∃ haTarget : a ≤ abundanceTarget,
          ∃ htargetEndpoint : abundanceTarget ≤ endpointOrbitMean q,
            ∃ haEndpoint : a < endpointOrbitMean q,
              0 ≤ a ∧ 0 ≤ q ∧ q ≤ 1
                ∧ orbitYuGap
                    (lowEndpointOrbitLaw a 0 abundanceTarget q haTarget htargetEndpoint
                      haEndpoint) ≤ orbitYuGap law) := by
  obtain ⟨reduced, hreducedGap, hextreme, hhalf⟩ :=
    orbitYuGap_exists_halfSupported_extreme_of_mem hleft hright law
  have hnewLeft :
      ∀ z, halfSupportOrbitLeft left z ∈ Icc (0 : ℝ) 1 := by
    rintro ⟨i, leftChoice, _⟩
    exact halfSupportKernelPoint_mem (hleft i) leftChoice
  have hnewRight :
      ∀ z, halfSupportOrbitRight right z ∈ Icc (0 : ℝ) 1 := by
    rintro ⟨i, _, rightChoice⟩
    exact halfSupportKernelPoint_mem (hright i) rightChoice
  rcases hextreme with ⟨i, hi, hcard, hmean⟩ |
      ⟨lower, upper, hlowerUpper, hlower, hupper, hcard,
        hlowerMean, hupperMean, hlowerWeight, hupperWeight⟩
  · exact Or.inl ((identifiedSingle_collapse_to_diagonal hnewLeft hnewRight hhalf
      reduced hi hcard hmean).trans hreducedGap)
  · rcases identifiedPair_collapse_to_canonical hnewLeft hnewRight hhalf reduced
      hlowerUpper hlower hupper hcard hlowerMean hupperMean hlowerWeight hupperWeight with
      hlow | hendpoint
    · right
      left
      rcases hlow with ⟨a, b, haTarget, htargetB, hab, haZero, hbHalf, hgap⟩
      exact ⟨a, b, haTarget, htargetB, hab, haZero, hbHalf, hgap.trans hreducedGap⟩
    · right
      right
      rcases hendpoint with
        ⟨a, q, haTarget, htargetEndpoint, haEndpoint, haZero, hqZero, hqOne, hgap⟩
      exact ⟨a, q, haTarget, htargetEndpoint, haEndpoint, haZero, hqZero, hqOne,
        hgap.trans hreducedGap⟩

/-- The three canonical objective families imply nonnegativity of the strict Yu gap for every
finite symmetric coupling whose marginal mean is at most the candidate target. -/
theorem orbitYuGap_nonneg_of_canonical_families {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {source : ℝ}
    (hleft : ∀ i, left i ∈ Icc (0 : ℝ) 1)
    (hright : ∀ i, right i ∈ Icc (0 : ℝ) 1)
    (law : FiniteOrbitLaw left right source) (hsourceTarget : source ≤ abundanceTarget)
    (hdiagonal : 0 ≤ orbitYuGap (singleLowOrbitLaw abundanceTarget 0))
    (hlow : ∀ (a b : ℝ) (haTarget : a ≤ abundanceTarget)
      (htargetB : abundanceTarget ≤ b) (hab : a < b),
      0 ≤ a → b ≤ 1 / 2 →
        0 ≤ orbitYuGap
          (twoLowOrbitLaw a 0 abundanceTarget b 0 haTarget htargetB hab))
    (hendpoint : ∀ (a q : ℝ) (haTarget : a ≤ abundanceTarget)
      (htargetEndpoint : abundanceTarget ≤ endpointOrbitMean q)
      (haEndpoint : a < endpointOrbitMean q),
      0 ≤ a → 0 ≤ q → q ≤ 1 →
        0 ≤ orbitYuGap
          (lowEndpointOrbitLaw a 0 abundanceTarget q haTarget htargetEndpoint haEndpoint)) :
    0 ≤ orbitYuGap law := by
  have hsourceOne : source < 1 :=
    hsourceTarget.trans_lt (abundanceTarget_lt_half.trans (by norm_num))
  let lifted := meanLiftOrbitLaw law hsourceTarget hsourceOne
    (abundanceTarget_lt_half.trans (by norm_num))
  have hliftedNonneg : 0 ≤ orbitYuGap lifted := by
    rcases orbitYuGap_exists_canonical_of_mem (meanLiftPoint_mem hleft)
      (meanLiftPoint_mem hright) lifted with hsingle | hpair
    · exact hdiagonal.trans hsingle
    · rcases hpair with hlowFamily | hendpointFamily
      · rcases hlowFamily with ⟨a, b, haTarget, htargetB, hab, haZero, hbHalf, hgap⟩
        exact (hlow a b haTarget htargetB hab haZero hbHalf).trans hgap
      · rcases hendpointFamily with
          ⟨a, q, haTarget, htargetEndpoint, haEndpoint, haZero, hqZero, hqOne, hgap⟩
        exact (hendpoint a q haTarget htargetEndpoint haEndpoint
          haZero hqZero hqOne).trans hgap
  exact orbitYuGap_nonneg_of_meanLift_of_mem hleft hright law hsourceTarget hsourceOne
    (abundanceTarget_lt_half.trans (by norm_num)) hliftedNonneg

end Frankl
