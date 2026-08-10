import Frankl.SelfPair

namespace Frankl

open Real Set

/-- The abundance threshold certified by the present Frankl reduction. -/
noncomputable def abundanceTarget : ℝ := 76469 / 200000

theorem abundanceTarget_gt_three_eighths : (3 : ℝ) / 8 < abundanceTarget := by
  norm_num [abundanceTarget]

theorem abundanceTarget_lt_half : abundanceTarget < (1 : ℝ) / 2 := by
  norm_num [abundanceTarget]

/-- The candidate threshold strictly improves the golden-ratio threshold. -/
theorem goldenRatioThreshold_lt_abundanceTarget :
    (3 - √5) / 2 < abundanceTarget := by
  have hsqrt : 0 ≤ √(5 : ℝ) := sqrt_nonneg 5
  have hsquare : (√(5 : ℝ)) ^ 2 = 5 := sq_sqrt (by norm_num)
  dsimp [abundanceTarget]
  nlinarith

/-- The mass on the lower mean in the two-point exact-mean decomposition. -/
noncomputable def lowerOrbitWeight (a t b : ℝ) : ℝ := (b - t) / (b - a)

/-- The mass on the upper mean in the two-point exact-mean decomposition. -/
noncomputable def upperOrbitWeight (a t b : ℝ) : ℝ := (t - a) / (b - a)

theorem orbitWeights_sum {a t b : ℝ} (hab : a < b) :
    lowerOrbitWeight a t b + upperOrbitWeight a t b = 1 := by
  dsimp [lowerOrbitWeight, upperOrbitWeight]
  field_simp [sub_ne_zero.mpr (ne_of_gt hab)]

theorem orbitWeights_mean {a t b : ℝ} (hab : a < b) :
    lowerOrbitWeight a t b * a + upperOrbitWeight a t b * b = t := by
  dsimp [lowerOrbitWeight, upperOrbitWeight]
  field_simp [sub_ne_zero.mpr (ne_of_gt hab)]
  ring

theorem lowerOrbitWeight_nonneg {a t b : ℝ} (htb : t ≤ b) (hab : a < b) :
    0 ≤ lowerOrbitWeight a t b := by
  exact div_nonneg (sub_nonneg.2 htb) (sub_nonneg.2 hab.le)

theorem upperOrbitWeight_nonneg {a t b : ℝ} (hat : a ≤ t) (hab : a < b) :
    0 ≤ upperOrbitWeight a t b := by
  exact div_nonneg (sub_nonneg.2 hat) (sub_nonneg.2 hab.le)

/-- The lower-orbit contraction coefficient is at most one once the upper mean is at least
`3/8`. -/
theorem lowerContractionFactor_le_one {b lowerWeight upperWeight : ℝ}
    (hupperWeight : 0 ≤ upperWeight) (hweightSum : lowerWeight + upperWeight = 1)
    (hb : 3 / 8 ≤ b) :
    lowerWeight + 2 * upperWeight * (1 - 4 * b / 3) ≤ 1 := by
  calc
    lowerWeight + 2 * upperWeight * (1 - 4 * b / 3) =
        lowerWeight + upperWeight + upperWeight * (1 - 8 * b / 3) := by ring
    _ = 1 + upperWeight * (1 - 8 * b / 3) := by rw [hweightSum]
    _ ≤ 1 := by nlinarith

/-- Exact-mean weights control the upper-orbit contraction coefficient. -/
theorem upperContractionFactor_le {a t b : ℝ}
    (ha₀ : 0 ≤ a) (htb : t ≤ b) (hb : b ≤ 1 / 2) (hab : a < b) :
    2 * upperOrbitWeight a t b * (1 - 4 * b / 3)
        + 2 * lowerOrbitWeight a t b * ((1 - a) / (1 + a)) ≤
      2 - 8 * t / 3 := by
  have hba : 0 < b - a := sub_pos.2 hab
  have hone : 0 < 1 + a := by linarith
  have hidentity :
      2 * upperOrbitWeight a t b * (1 - 4 * b / 3)
          + 2 * lowerOrbitWeight a t b * ((1 - a) / (1 + a))
          - (2 - 8 * t / 3) =
        4 * a * (2 * a - 1) * (b - t) / (3 * (1 + a) * (b - a)) := by
    dsimp [lowerOrbitWeight, upperOrbitWeight]
    field_simp [hba.ne', hone.ne']
    ring
  rw [← sub_nonpos]
  rw [hidentity]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) ha₀) (by linarith))
      (sub_nonneg.2 htb))
    (mul_nonneg (mul_nonneg (by norm_num) hone.le) hba.le)

theorem targetUpperContractionFactor_lt_one {a b : ℝ}
    (ha₀ : 0 ≤ a) (htb : abundanceTarget ≤ b)
    (hb : b ≤ 1 / 2) (hab : a < b) :
    2 * upperOrbitWeight a abundanceTarget b * (1 - 4 * b / 3)
        + 2 * lowerOrbitWeight a abundanceTarget b * ((1 - a) / (1 + a)) < 1 := by
  have hfactor := upperContractionFactor_le ha₀ htb hb hab
  exact hfactor.trans_lt (by norm_num [abundanceTarget])

/-- The endpoint contraction coefficient is at most one. -/
theorem endpointContractionFactor_le_one {q lowerWeight upperWeight : ℝ}
    (hq : 0 ≤ q) (hupperWeight : 0 ≤ upperWeight)
    (hweightSum : lowerWeight + upperWeight = 1) :
    lowerWeight + upperWeight * (1 - q) ≤ 1 := by
  calc
    lowerWeight + upperWeight * (1 - q) =
        lowerWeight + upperWeight - upperWeight * q := by ring
    _ = 1 - upperWeight * q := by rw [hweightSum]
    _ ≤ 1 := by nlinarith [mul_nonneg hupperWeight hq]

/-- Contracting the lower of two low orbits raises independent join entropy by no more than it
raises marginal entropy. -/
theorem lowerLowOrbitDeficit_le_marginal {a d b e lowerWeight upperWeight : ℝ}
    (ha₀ : 0 ≤ a - d) (ha₁ : a + d ≤ 1 / 2) (hd : 0 ≤ d)
    (hb₀ : 0 ≤ b - e) (hb₁ : b + e ≤ 1 / 2) (he : 0 ≤ e)
    (hlowerWeight : 0 ≤ lowerWeight) (hupperWeight : 0 ≤ upperWeight)
    (hweightSum : lowerWeight + upperWeight = 1) (hb : 3 / 8 ≤ b) :
    lowerWeight ^ 2 * selfPairDeficit a d
        + lowerWeight * upperWeight
          * (orbitDeficit (fun x ↦ binEntropy (join x (b - e))) a d
            + orbitDeficit (fun x ↦ binEntropy (join x (b + e))) a d) ≤
      lowerWeight * orbitDeficit binEntropy a d := by
  let marginalDeficit := orbitDeficit binEntropy a d
  have hmarginal : 0 ≤ marginalDeficit :=
    orbitDeficit_nonneg ha₀ (ha₁.trans (by norm_num)) hd
  have hself := selfPairDeficit_le_orbitDeficit ha₀ ha₁ hd
  have hlower := orbitDeficit_joinEntropy_le_affine ha₀ ha₁ hd hb₀ (by linarith : b - e ≤ 1 / 2)
  have hupper := orbitDeficit_joinEntropy_le_affine ha₀ ha₁ hd (by linarith : 0 ≤ b + e) hb₁
  have hselfScaled := mul_le_mul_of_nonneg_left hself (sq_nonneg lowerWeight)
  have hcrossScaled := mul_le_mul_of_nonneg_left (add_le_add hlower hupper)
    (mul_nonneg hlowerWeight hupperWeight)
  have hfactor := lowerContractionFactor_le_one hupperWeight hweightSum hb
  have hfactorScaled :
      lowerWeight * (lowerWeight + 2 * upperWeight * (1 - 4 * b / 3))
          * marginalDeficit ≤ lowerWeight * marginalDeficit := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hfactor hlowerWeight) hmarginal
  dsimp only [marginalDeficit] at hmarginal hselfScaled hcrossScaled hfactorScaled
  calc
    lowerWeight ^ 2 * selfPairDeficit a d
          + lowerWeight * upperWeight
            * (orbitDeficit (fun x ↦ binEntropy (join x (b - e))) a d
              + orbitDeficit (fun x ↦ binEntropy (join x (b + e))) a d) ≤
        lowerWeight ^ 2 * orbitDeficit binEntropy a d
          + lowerWeight * upperWeight
            * (((1 - 4 * (b - e) / 3) * orbitDeficit binEntropy a d)
              + ((1 - 4 * (b + e) / 3) * orbitDeficit binEntropy a d)) :=
      add_le_add hselfScaled hcrossScaled
    _ = lowerWeight
        * (lowerWeight + 2 * upperWeight * (1 - 4 * b / 3))
        * orbitDeficit binEntropy a d := by ring
    _ ≤ lowerWeight * orbitDeficit binEntropy a d := hfactorScaled

/-- Given its scalar coefficient bound, contracting the upper low orbit after the lower orbit has
been contracted raises independent entropy by no more than marginal entropy. -/
theorem upperLowOrbitDeficit_le_marginal {a b e lowerWeight upperWeight : ℝ}
    (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1 / 2)
    (hb₀ : 0 ≤ b - e) (hb₁ : b + e ≤ 1 / 2) (he : 0 ≤ e)
    (hlowerWeight : 0 ≤ lowerWeight) (hupperWeight : 0 ≤ upperWeight)
    (hfactor :
      2 * upperWeight * (1 - 4 * b / 3)
          + 2 * lowerWeight * ((1 - a) / (1 + a)) ≤ 1) :
    upperWeight ^ 2 * selfPairDeficit b e
        + 2 * lowerWeight * upperWeight
          * orbitDeficit (fun x ↦ binEntropy (join x a)) b e ≤
      upperWeight * orbitDeficit binEntropy b e := by
  let marginalDeficit := orbitDeficit binEntropy b e
  have hmarginal : 0 ≤ marginalDeficit :=
    orbitDeficit_nonneg hb₀ (hb₁.trans (by norm_num)) he
  have hself := selfPairDeficit_le_affine hb₀ hb₁ he
  have hcross := orbitDeficit_joinEntropy_le_ratio hb₀ hb₁ he ha₀ ha₁
  have hselfScaled := mul_le_mul_of_nonneg_left hself (sq_nonneg upperWeight)
  have hcrossCoefficient : 0 ≤ 2 * lowerWeight * upperWeight :=
    mul_nonneg (mul_nonneg (show 0 ≤ (2 : ℝ) by norm_num) hlowerWeight) hupperWeight
  have hcrossScaled := mul_le_mul_of_nonneg_left hcross hcrossCoefficient
  have hfactorScaled :
      upperWeight
          * (2 * upperWeight * (1 - 4 * b / 3)
            + 2 * lowerWeight * ((1 - a) / (1 + a)))
          * marginalDeficit ≤ upperWeight * marginalDeficit := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hfactor hupperWeight) hmarginal
  dsimp only [marginalDeficit] at hmarginal hselfScaled hcrossScaled hfactorScaled
  calc
    upperWeight ^ 2 * selfPairDeficit b e
          + 2 * lowerWeight * upperWeight
            * orbitDeficit (fun x ↦ binEntropy (join x a)) b e ≤
        upperWeight ^ 2 * (2 * (1 - 4 * b / 3) * orbitDeficit binEntropy b e)
          + 2 * lowerWeight * upperWeight
            * ((1 - a) / (1 + a) * orbitDeficit binEntropy b e) :=
      add_le_add hselfScaled hcrossScaled
    _ = upperWeight
        * (2 * upperWeight * (1 - 4 * b / 3)
          + 2 * lowerWeight * ((1 - a) / (1 + a)))
        * orbitDeficit binEntropy b e := by ring
    _ ≤ upperWeight * orbitDeficit binEntropy b e := hfactorScaled

/-- Contracting a low orbit against an endpoint orbit raises independent join entropy by no more
than marginal entropy. -/
theorem lowerEndpointOrbitDeficit_le_marginal {a d q lowerWeight upperWeight : ℝ}
    (ha₀ : 0 ≤ a - d) (ha₁ : a + d ≤ 1 / 2) (hd : 0 ≤ d)
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    (hlowerWeight : 0 ≤ lowerWeight) (hupperWeight : 0 ≤ upperWeight)
    (hweightSum : lowerWeight + upperWeight = 1) :
    lowerWeight ^ 2 * selfPairDeficit a d
        + lowerWeight * upperWeight
          * (orbitDeficit (fun x ↦ binEntropy (join x q)) a d
            + orbitDeficit (fun x ↦ binEntropy (join x 1)) a d) ≤
      lowerWeight * orbitDeficit binEntropy a d := by
  let marginalDeficit := orbitDeficit binEntropy a d
  have hmarginal : 0 ≤ marginalDeficit :=
    orbitDeficit_nonneg ha₀ (ha₁.trans (by norm_num)) hd
  have hself := selfPairDeficit_le_orbitDeficit ha₀ ha₁ hd
  have hcross := orbitDeficit_joinEntropy_le_endpoint ha₀ ha₁ hd hq₀ hq₁
  have hone : orbitDeficit (fun x ↦ binEntropy (join x 1)) a d = 0 := by
    simp [orbitDeficit, join_one_right]
  have hselfScaled := mul_le_mul_of_nonneg_left hself (sq_nonneg lowerWeight)
  have hcrossScaled := mul_le_mul_of_nonneg_left hcross
    (mul_nonneg hlowerWeight hupperWeight)
  have hfactor := endpointContractionFactor_le_one hq₀ hupperWeight hweightSum
  have hfactorScaled :
      lowerWeight * (lowerWeight + upperWeight * (1 - q)) * marginalDeficit ≤
        lowerWeight * marginalDeficit := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hfactor hlowerWeight) hmarginal
  dsimp only [marginalDeficit] at hmarginal hselfScaled hcrossScaled hfactorScaled
  rw [hone]
  simp only [add_zero]
  calc
    lowerWeight ^ 2 * selfPairDeficit a d
          + lowerWeight * upperWeight
            * orbitDeficit (fun x ↦ binEntropy (join x q)) a d ≤
        lowerWeight ^ 2 * orbitDeficit binEntropy a d
          + lowerWeight * upperWeight
            * ((1 - q) * orbitDeficit binEntropy a d) :=
      add_le_add hselfScaled hcrossScaled
    _ = lowerWeight * (lowerWeight + upperWeight * (1 - q))
        * orbitDeficit binEntropy a d := by ring
    _ ≤ lowerWeight * orbitDeficit binEntropy a d := hfactorScaled

end Frankl
