import Frankl.MeanLift

namespace Frankl

open Finset Set

/-- A finitely indexed probability law with one prescribed scalar moment. -/
structure FiniteMomentLaw (ι : Type*) [Fintype ι] (moment : ι → ℝ) (mean : ℝ) where
  /-- The mass assigned to each index. -/
  weight : ι → ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_sum : ∑ i, weight i = 1
  moment_sum : ∑ i, weight i * moment i = mean

namespace FiniteMomentLaw

variable {ι : Type*} [Fintype ι] {moment : ι → ℝ} {mean : ℝ}

/-- The live atoms of a finite moment law. -/
noncomputable def support (law : FiniteMomentLaw ι moment mean) : Finset ι :=
  univ.filter fun i ↦ 0 < law.weight i

theorem mem_support_iff (law : FiniteMomentLaw ι moment mean) (i : ι) :
    i ∈ law.support ↔ 0 < law.weight i := by
  simp [support]

theorem weight_pos_of_mem_support (law : FiniteMomentLaw ι moment mean) {i : ι}
    (hi : i ∈ law.support) :
    0 < law.weight i := by
  exact (law.mem_support_iff i).1 hi

theorem weight_eq_zero_of_not_mem_support (law : FiniteMomentLaw ι moment mean) {i : ι}
    (hi : i ∉ law.support) :
    law.weight i = 0 := by
  have hnot : ¬0 < law.weight i := by
    simpa only [law.mem_support_iff i] using hi
  exact le_antisymm (not_lt.mp hnot) (law.weight_nonneg i)

theorem sum_weight_eq_sum_support (law : FiniteMomentLaw ι moment mean)
    (observable : ι → ℝ) :
    ∑ i, law.weight i * observable i = ∑ i ∈ law.support, law.weight i * observable i := by
  classical
  exact (sum_subset (subset_univ law.support) fun i _ hi ↦ by
    rw [law.weight_eq_zero_of_not_mem_support hi, zero_mul]).symm

/-- The moment law concentrated at one atom whose moment is the prescribed mean. -/
noncomputable def pointMass (i : ι) (hi : moment i = mean) :
    FiniteMomentLaw ι moment mean := by
  classical
  exact
    { weight := fun r ↦ if r = i then 1 else 0
      weight_nonneg := fun r ↦ by by_cases hr : r = i <;> simp [hr]
      weight_sum := by simp
      moment_sum := by simp [hi] }

theorem pointMass_support (i : ι) (hi : moment i = mean) :
    (pointMass i hi).support = {i} := by
  classical
  ext r
  by_cases hr : i = r <;> simp [support, pointMass, hr, eq_comm]

/-- Convex interpolation inside one fixed-moment slice. -/
noncomputable def mix (p : ℝ) (left right : FiniteMomentLaw ι moment mean)
    (hp : p ∈ Icc (0 : ℝ) 1) : FiniteMomentLaw ι moment mean where
  weight i := p * left.weight i + (1 - p) * right.weight i
  weight_nonneg i :=
    add_nonneg (mul_nonneg hp.1 (left.weight_nonneg i))
      (mul_nonneg (sub_nonneg.2 hp.2) (right.weight_nonneg i))
  weight_sum := by
    rw [sum_add_distrib]
    rw [← mul_sum, ← mul_sum, left.weight_sum, right.weight_sum]
    ring
  moment_sum := by
    simp_rw [add_mul, mul_assoc]
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, left.moment_sum, right.moment_sum]
    ring

@[ext]
theorem ext {left right : FiniteMomentLaw ι moment mean}
    (hweight : left.weight = right.weight) :
    left = right := by
  cases left
  cases right
  simp_all

/-- Concavity of a functional on every segment in a fixed-moment finite simplex. -/
def IsConcaveFunctional (functional : FiniteMomentLaw ι moment mean → ℝ) : Prop :=
  ∀ (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) (left right : FiniteMomentLaw ι moment mean),
    p * functional left + (1 - p) * functional right ≤
      functional (mix p left right hp)

private noncomputable def threeDirection (i j k : ι) : ι → ℝ := by
  classical
  exact if moment i = moment j then
      fun r ↦ (if r = i then 1 else 0) + (if r = j then -1 else 0)
    else
      fun r ↦
        (if r = i then moment j - moment k else 0)
          + (if r = j then moment k - moment i else 0)
          + (if r = k then moment i - moment j else 0)

private theorem threeDirection_sum {i j k : ι} :
    ∑ r, threeDirection (moment := moment) i j k r = 0 := by
  classical
  by_cases hm : moment i = moment j
  · simp [threeDirection, hm, sum_add_distrib]
  · simp [threeDirection, hm, sum_add_distrib]

private theorem threeDirection_moment_sum {i j k : ι} :
    ∑ r, threeDirection (moment := moment) i j k r * moment r = 0 := by
  classical
  by_cases hm : moment i = moment j
  · simp [threeDirection, hm, add_mul, sum_add_distrib]
  · simp [threeDirection, hm, add_mul, sum_add_distrib]
    ring

omit [Fintype ι] in
private theorem threeDirection_ne_zero {i j k : ι}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    threeDirection (moment := moment) i j k ≠ 0 := by
  classical
  by_cases hm : moment i = moment j
  · intro hzero
    have hi := congr_fun hzero i
    simp [threeDirection, hm, hij] at hi
  · intro hzero
    have hk := congr_fun hzero k
    simp [threeDirection, hm, hik.symm, hjk.symm] at hk
    exact hm (sub_eq_zero.mp hk)

private theorem threeDirection_live {law : FiniteMomentLaw ι moment mean} {i j k r : ι}
    (hi : i ∈ law.support) (hj : j ∈ law.support) (hk : k ∈ law.support)
    (hdir : threeDirection (moment := moment) i j k r ≠ 0) :
    0 < law.weight r := by
  classical
  by_cases hm : moment i = moment j
  · have hr : r = i ∨ r = j := by
      by_contra hnot
      push Not at hnot
      apply hdir
      simp [threeDirection, hm, hnot.1, hnot.2]
    rcases hr with rfl | rfl
    · exact law.weight_pos_of_mem_support hi
    · exact law.weight_pos_of_mem_support hj
  · have hr : r = i ∨ r = j ∨ r = k := by
      by_contra hnot
      push Not at hnot
      apply hdir
      simp [threeDirection, hm, hnot.1, hnot.2.1, hnot.2.2]
    rcases hr with rfl | rfl | rfl
    · exact law.weight_pos_of_mem_support hi
    · exact law.weight_pos_of_mem_support hj
    · exact law.weight_pos_of_mem_support hk

private theorem exists_balanced_live_direction (law : FiniteMomentLaw ι moment mean)
    (hsupport : 2 < law.support.card) :
    ∃ direction : ι → ℝ,
      direction ≠ 0 ∧
        (∑ i, direction i) = 0 ∧
        (∑ i, direction i * moment i) = 0 ∧
        ∀ i, direction i ≠ 0 → 0 < law.weight i := by
  classical
  obtain ⟨i, j, k, hi, hj, hk, hij, hik, hjk⟩ :=
    Finset.two_lt_card_iff.mp hsupport
  let direction := threeDirection (moment := moment) i j k
  exact ⟨direction, threeDirection_ne_zero hij hik hjk,
    threeDirection_sum, threeDirection_moment_sum,
    fun r ↦ threeDirection_live hi hj hk⟩

private noncomputable def positiveDirectionSupport (direction : ι → ℝ) : Finset ι :=
  univ.filter fun i ↦ 0 < direction i

private noncomputable def negativeDirectionSupport (direction : ι → ℝ) : Finset ι :=
  univ.filter fun i ↦ direction i < 0

private theorem direction_supports_nonempty {direction : ι → ℝ}
    (hdirection : direction ≠ 0) (hsum : ∑ i, direction i = 0) :
    (positiveDirectionSupport direction).Nonempty ∧
      (negativeDirectionSupport direction).Nonempty := by
  classical
  have hpositive : (positiveDirectionSupport direction).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hnonpos : ∀ i, direction i ≤ 0 := by
      intro i
      exact not_lt.mp fun hi ↦ by
        have : i ∈ positiveDirectionSupport direction := by
          simp [positiveDirectionSupport, hi]
        simp [hempty] at this
    have hallzero : ∀ i, direction i = 0 := fun i ↦
      (Finset.sum_eq_zero_iff_of_nonpos fun i _ ↦ hnonpos i).1 hsum i (mem_univ i)
    exact hdirection (funext hallzero)
  have hnegative : (negativeDirectionSupport direction).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hnonneg : ∀ i, 0 ≤ direction i := by
      intro i
      exact not_lt.mp fun hi ↦ by
        have : i ∈ negativeDirectionSupport direction := by
          simp [negativeDirectionSupport, hi]
        simp [hempty] at this
    have hallzero : ∀ i, direction i = 0 := fun i ↦
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ hnonneg i).1 hsum i (mem_univ i)
    exact hdirection (funext hallzero)
  exact ⟨hpositive, hnegative⟩

private noncomputable def forwardStep (law : FiniteMomentLaw ι moment mean)
    (direction : ι → ℝ) (hnegative : (negativeDirectionSupport direction).Nonempty) : ℝ :=
  ((negativeDirectionSupport direction).image
    fun i ↦ law.weight i / (-direction i)).min' (hnegative.image _)

private noncomputable def backwardStep (law : FiniteMomentLaw ι moment mean)
    (direction : ι → ℝ) (hpositive : (positiveDirectionSupport direction).Nonempty) : ℝ :=
  ((positiveDirectionSupport direction).image
    fun i ↦ law.weight i / direction i).min' (hpositive.image _)

private theorem forwardStep_pos {law : FiniteMomentLaw ι moment mean} {direction : ι → ℝ}
    (hlive : ∀ i, direction i ≠ 0 → 0 < law.weight i)
    (hnegative : (negativeDirectionSupport direction).Nonempty) :
    0 < forwardStep law direction hnegative := by
  classical
  let values := (negativeDirectionSupport direction).image
    fun i ↦ law.weight i / (-direction i)
  have hmember := values.min'_mem (hnegative.image _)
  obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hmember
  have hdir : direction i < 0 := by
    simpa [negativeDirectionSupport] using hi
  have hweight : 0 < law.weight i := hlive i hdir.ne
  rw [forwardStep]
  rw [← heq]
  exact div_pos hweight (neg_pos.2 hdir)

private theorem backwardStep_pos {law : FiniteMomentLaw ι moment mean} {direction : ι → ℝ}
    (hlive : ∀ i, direction i ≠ 0 → 0 < law.weight i)
    (hpositive : (positiveDirectionSupport direction).Nonempty) :
    0 < backwardStep law direction hpositive := by
  classical
  let values := (positiveDirectionSupport direction).image
    fun i ↦ law.weight i / direction i
  have hmember := values.min'_mem (hpositive.image _)
  obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hmember
  have hdir : 0 < direction i := by
    simpa [positiveDirectionSupport] using hi
  have hweight : 0 < law.weight i := hlive i hdir.ne'
  rw [backwardStep]
  rw [← heq]
  exact div_pos hweight hdir

private theorem forwardStep_le_ratio {law : FiniteMomentLaw ι moment mean}
    {direction : ι → ℝ} (hnegative : (negativeDirectionSupport direction).Nonempty)
    {i : ι} (hi : direction i < 0) :
    forwardStep law direction hnegative ≤ law.weight i / (-direction i) := by
  classical
  apply Finset.min'_le
  exact Finset.mem_image.2 ⟨i, by simp [negativeDirectionSupport, hi], rfl⟩

private theorem backwardStep_le_ratio {law : FiniteMomentLaw ι moment mean}
    {direction : ι → ℝ} (hpositive : (positiveDirectionSupport direction).Nonempty)
    {i : ι} (hi : 0 < direction i) :
    backwardStep law direction hpositive ≤ law.weight i / direction i := by
  classical
  apply Finset.min'_le
  exact Finset.mem_image.2 ⟨i, by simp [positiveDirectionSupport, hi], rfl⟩

private theorem forward_weight_nonneg {law : FiniteMomentLaw ι moment mean}
    {direction : ι → ℝ} (hnegative : (negativeDirectionSupport direction).Nonempty)
    (hlive : ∀ i, direction i ≠ 0 → 0 < law.weight i) (i : ι) :
    0 ≤ law.weight i + forwardStep law direction hnegative * direction i := by
  by_cases hi : direction i < 0
  · have hstep := forwardStep_le_ratio (law := law) hnegative hi
    have hneg : 0 < -direction i := neg_pos.2 hi
    have hscaled := (mul_le_mul_of_nonneg_right hstep hneg.le)
    rw [div_mul_cancel₀ _ hneg.ne'] at hscaled
    nlinarith
  · exact add_nonneg (law.weight_nonneg i)
      (mul_nonneg (forwardStep_pos hlive hnegative).le (not_lt.mp hi))

private theorem backward_weight_nonneg {law : FiniteMomentLaw ι moment mean}
    {direction : ι → ℝ} (hpositive : (positiveDirectionSupport direction).Nonempty)
    (hlive : ∀ i, direction i ≠ 0 → 0 < law.weight i) (i : ι) :
    0 ≤ law.weight i - backwardStep law direction hpositive * direction i := by
  by_cases hi : 0 < direction i
  · have hstep := backwardStep_le_ratio (law := law) hpositive hi
    have hscaled := mul_le_mul_of_nonneg_right hstep hi.le
    rw [div_mul_cancel₀ _ hi.ne'] at hscaled
    linarith
  · have hproduct : backwardStep law direction hpositive * direction i ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (backwardStep_pos hlive hpositive).le (not_lt.mp hi)
    linarith [law.weight_nonneg i]

private noncomputable def forwardLaw (law : FiniteMomentLaw ι moment mean)
    (direction : ι → ℝ) (hsum : ∑ i, direction i = 0)
    (hmoment : ∑ i, direction i * moment i = 0)
    (hnegative : (negativeDirectionSupport direction).Nonempty)
    (hlive : ∀ i, direction i ≠ 0 → 0 < law.weight i) :
    FiniteMomentLaw ι moment mean where
  weight i := law.weight i + forwardStep law direction hnegative * direction i
  weight_nonneg := forward_weight_nonneg hnegative hlive
  weight_sum := by rw [sum_add_distrib, ← mul_sum, law.weight_sum, hsum, mul_zero, add_zero]
  moment_sum := by
    simp_rw [add_mul, mul_assoc]
    rw [sum_add_distrib, ← mul_sum, law.moment_sum, hmoment, mul_zero, add_zero]

private noncomputable def backwardLaw (law : FiniteMomentLaw ι moment mean)
    (direction : ι → ℝ) (hsum : ∑ i, direction i = 0)
    (hmoment : ∑ i, direction i * moment i = 0)
    (hpositive : (positiveDirectionSupport direction).Nonempty)
    (hlive : ∀ i, direction i ≠ 0 → 0 < law.weight i) :
    FiniteMomentLaw ι moment mean where
  weight i := law.weight i - backwardStep law direction hpositive * direction i
  weight_nonneg := backward_weight_nonneg hpositive hlive
  weight_sum := by rw [sum_sub_distrib, ← mul_sum, law.weight_sum, hsum, mul_zero, sub_zero]
  moment_sum := by
    simp_rw [sub_mul, mul_assoc]
    rw [sum_sub_distrib, ← mul_sum, law.moment_sum, hmoment, mul_zero, sub_zero]

private theorem forward_support_lt {law : FiniteMomentLaw ι moment mean}
    {direction : ι → ℝ} {hsum : ∑ i, direction i = 0}
    {hmoment : ∑ i, direction i * moment i = 0}
    (hnegative : (negativeDirectionSupport direction).Nonempty)
    (hlive : ∀ i, direction i ≠ 0 → 0 < law.weight i) :
    (forwardLaw law direction hsum hmoment hnegative hlive).support.card < law.support.card := by
  classical
  let values := (negativeDirectionSupport direction).image
    fun i ↦ law.weight i / (-direction i)
  have hmember := values.min'_mem (hnegative.image _)
  obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hmember
  have hdir : direction i < 0 := by
    simpa [negativeDirectionSupport] using hi
  have hzero :
      (forwardLaw law direction hsum hmoment hnegative hlive).weight i = 0 := by
    dsimp [forwardLaw]
    rw [forwardStep, ← heq]
    field_simp [hdir.ne]
    ring
  have hsubset : (forwardLaw law direction hsum hmoment hnegative hlive).support ⊆
      law.support := by
    intro r hr
    have hforward :=
      (forwardLaw law direction hsum hmoment hnegative hlive).weight_pos_of_mem_support hr
    apply (law.mem_support_iff r).2
    by_contra hnot
    have hweight : law.weight r = 0 := le_antisymm (not_lt.mp hnot) (law.weight_nonneg r)
    have hdirection : direction r = 0 := by
      by_contra hne
      exact (hlive r hne).ne' hweight
    dsimp [forwardLaw] at hforward
    rw [hweight, hdirection, mul_zero, add_zero] at hforward
    exact lt_irrefl 0 hforward
  have hiold : i ∈ law.support :=
    (law.mem_support_iff i).2 (hlive i hdir.ne)
  have hinew : i ∉ (forwardLaw law direction hsum hmoment hnegative hlive).support := by
    simp [mem_support_iff, hzero]
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2
    ⟨hsubset, fun heqSupport ↦ hinew (heqSupport ▸ hiold)⟩)

private theorem backward_support_lt {law : FiniteMomentLaw ι moment mean}
    {direction : ι → ℝ} {hsum : ∑ i, direction i = 0}
    {hmoment : ∑ i, direction i * moment i = 0}
    (hpositive : (positiveDirectionSupport direction).Nonempty)
    (hlive : ∀ i, direction i ≠ 0 → 0 < law.weight i) :
    (backwardLaw law direction hsum hmoment hpositive hlive).support.card < law.support.card := by
  classical
  let values := (positiveDirectionSupport direction).image
    fun i ↦ law.weight i / direction i
  have hmember := values.min'_mem (hpositive.image _)
  obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hmember
  have hdir : 0 < direction i := by
    simpa [positiveDirectionSupport] using hi
  have hzero :
      (backwardLaw law direction hsum hmoment hpositive hlive).weight i = 0 := by
    dsimp [backwardLaw]
    rw [backwardStep, ← heq]
    field_simp [hdir.ne']
    ring
  have hsubset : (backwardLaw law direction hsum hmoment hpositive hlive).support ⊆
      law.support := by
    intro r hr
    have hbackward :=
      (backwardLaw law direction hsum hmoment hpositive hlive).weight_pos_of_mem_support hr
    apply (law.mem_support_iff r).2
    by_contra hnot
    have hweight : law.weight r = 0 := le_antisymm (not_lt.mp hnot) (law.weight_nonneg r)
    have hdirection : direction r = 0 := by
      by_contra hne
      exact (hlive r hne).ne' hweight
    dsimp [backwardLaw] at hbackward
    rw [hweight, hdirection, mul_zero, sub_zero] at hbackward
    exact lt_irrefl 0 hbackward
  have hiold : i ∈ law.support :=
    (law.mem_support_iff i).2 (hlive i hdir.ne')
  have hinew : i ∉ (backwardLaw law direction hsum hmoment hpositive hlive).support := by
    simp [mem_support_iff, hzero]
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2
    ⟨hsubset, fun heqSupport ↦ hinew (heqSupport ▸ hiold)⟩)

private theorem exists_strict_split (law : FiniteMomentLaw ι moment mean)
    (hsupport : 2 < law.support.card) :
    ∃ (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
      (left right : FiniteMomentLaw ι moment mean),
      law = mix p left right ⟨hp.1.le, hp.2.le⟩ ∧
        left.support.card < law.support.card ∧
        right.support.card < law.support.card := by
  classical
  obtain ⟨direction, hdirection, hsum, hmoment, hlive⟩ :=
    exists_balanced_live_direction law hsupport
  obtain ⟨hpositive, hnegative⟩ := direction_supports_nonempty hdirection hsum
  let forward := forwardStep law direction hnegative
  let backward := backwardStep law direction hpositive
  have hforward : 0 < forward := forwardStep_pos hlive hnegative
  have hbackward : 0 < backward := backwardStep_pos hlive hpositive
  let p := backward / (forward + backward)
  have hp₀ : 0 < p := div_pos hbackward (add_pos hforward hbackward)
  have hp₁ : p < 1 := by
    rw [div_lt_one (add_pos hforward hbackward)]
    linarith
  let left := forwardLaw law direction hsum hmoment hnegative hlive
  let right := backwardLaw law direction hsum hmoment hpositive hlive
  refine ⟨p, ⟨hp₀, hp₁⟩, left, right, ?_, ?_, ?_⟩
  · apply FiniteMomentLaw.ext
    funext i
    change law.weight i =
      p * (law.weight i + forward * direction i) +
        (1 - p) * (law.weight i - backward * direction i)
    have balance : p * forward = (1 - p) * backward := by
      dsimp [p]
      field_simp [(add_pos hforward hbackward).ne']
      ring
    symm
    calc
      p * (law.weight i + forward * direction i) +
          (1 - p) * (law.weight i - backward * direction i) =
        law.weight i +
          (p * forward - (1 - p) * backward) * direction i := by ring
      _ = law.weight i := by rw [balance, sub_self, zero_mul, add_zero]
  · exact forward_support_lt hnegative hlive
  · exact backward_support_lt hpositive hlive

/-- A concave functional on a finite simplex with one moment constraint has a no-worse law
supported on at most two atoms. This is the elementary finite extreme-point reduction. -/
theorem exists_support_card_le_two {functional : FiniteMomentLaw ι moment mean → ℝ}
    (hconcave : IsConcaveFunctional functional) (law : FiniteMomentLaw ι moment mean) :
    ∃ reduced : FiniteMomentLaw ι moment mean,
      reduced.support.card ≤ 2 ∧ functional reduced ≤ functional law := by
  classical
  generalize hn : law.support.card = n
  induction n using Nat.strongRecOn generalizing law with
  | ind n ih =>
      by_cases hsmall : law.support.card ≤ 2
      · exact ⟨law, hsmall, le_rfl⟩
      · have hlarge : 2 < law.support.card := Nat.lt_of_not_ge hsmall
        obtain ⟨p, hp, left, right, hlaw, hleft, hright⟩ :=
          exists_strict_split law hlarge
        have hsegment := hconcave p ⟨hp.1.le, hp.2.le⟩ left right
        rw [← hlaw] at hsegment
        have hworse : functional left ≤ functional law ∨ functional right ≤ functional law := by
          by_contra hnot
          push Not at hnot
          have hleftPositive : 0 < p * (functional left - functional law) :=
            mul_pos hp.1 (sub_pos.2 hnot.1)
          have hrightPositive : 0 < (1 - p) * (functional right - functional law) :=
            mul_pos (sub_pos.2 hp.2) (sub_pos.2 hnot.2)
          nlinarith
        rcases hworse with hleftLaw | hrightLaw
        · have hleftN : left.support.card < n := by simpa [← hn] using hleft
          obtain ⟨reduced, hcard, hfunctional⟩ :=
            ih left.support.card hleftN left rfl
          exact ⟨reduced, hcard, hfunctional.trans hleftLaw⟩
        · have hrightN : right.support.card < n := by simpa [← hn] using hright
          obtain ⟨reduced, hcard, hfunctional⟩ :=
            ih right.support.card hrightN right rfl
          exact ⟨reduced, hcard, hfunctional.trans hrightLaw⟩

theorem support_nonempty (law : FiniteMomentLaw ι moment mean) : law.support.Nonempty := by
  classical
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  have hsum := law.sum_weight_eq_sum_support (fun _ ↦ (1 : ℝ))
  simp only [mul_one] at hsum
  rw [law.weight_sum, hempty] at hsum
  simp at hsum

/-- Two named live atoms exhaust a support of cardinality two. -/
theorem support_eq_pair_of_card_eq_two [DecidableEq ι]
    (law : FiniteMomentLaw ι moment mean) {i j : ι}
    (hij : i ≠ j) (hi : i ∈ law.support) (hj : j ∈ law.support)
    (hcard : law.support.card = 2) :
    law.support = {i, j} := by
  classical
  apply Finset.Subset.antisymm
  · intro r hr
    by_contra hpair
    have hir : i ≠ r := by
      intro hir
      subst r
      exact hpair (by simp)
    have hjr : j ≠ r := by
      intro hjr
      subst r
      exact hpair (by simp)
    have hthree : ({i, j, r} : Finset ι) ⊆ law.support := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hi
      · exact hj
      · exact hr
    have hthreeCard : ({i, j, r} : Finset ι).card = 3 := by
      simp [hij, hir, hjr]
    have hle := Finset.card_le_card hthree
    rw [hthreeCard, hcard] at hle
    omega
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hi
    · exact hj

/-- The two live masses in a two-atom law sum to one. -/
theorem two_support_weights_sum (law : FiniteMomentLaw ι moment mean) {i j : ι}
    (hij : i ≠ j) (hi : i ∈ law.support) (hj : j ∈ law.support)
    (hcard : law.support.card = 2) :
    law.weight i + law.weight j = 1 := by
  classical
  have hsupport := law.support_eq_pair_of_card_eq_two hij hi hj hcard
  have hsum := law.sum_weight_eq_sum_support (fun _ ↦ (1 : ℝ))
  simp only [mul_one] at hsum
  rw [law.weight_sum, hsupport] at hsum
  simpa [hij] using hsum.symm

/-- The two live weighted moments in a two-atom law realize the prescribed mean. -/
theorem two_support_moment_sum (law : FiniteMomentLaw ι moment mean) {i j : ι}
    (hij : i ≠ j) (hi : i ∈ law.support) (hj : j ∈ law.support)
    (hcard : law.support.card = 2) :
    law.weight i * moment i + law.weight j * moment j = mean := by
  classical
  have hsupport := law.support_eq_pair_of_card_eq_two hij hi hj hcard
  have hsum := law.sum_weight_eq_sum_support moment
  rw [law.moment_sum, hsupport] at hsum
  simpa [hij] using hsum.symm

/-- Exact mass identification for a two-atom law with ordered moments. -/
theorem two_support_weights_eq_orbitWeights (law : FiniteMomentLaw ι moment mean) {i j : ι}
    (hi : i ∈ law.support) (hj : j ∈ law.support) (hcard : law.support.card = 2)
    (hordered : moment i < moment j) :
    law.weight i = lowerOrbitWeight (moment i) mean (moment j) ∧
      law.weight j = upperOrbitWeight (moment i) mean (moment j) := by
  have hij : i ≠ j := fun hij ↦ by subst j; exact (lt_irrefl _ hordered)
  have hmass := law.two_support_weights_sum hij hi hj hcard
  have hmoment := law.two_support_moment_sum hij hi hj hcard
  have hden : moment j - moment i ≠ 0 := (sub_pos.2 hordered).ne'
  have hlowerIdentity :
      law.weight i * (moment j - moment i) = moment j - mean := by
    calc
      law.weight i * (moment j - moment i) =
          (law.weight i + law.weight j) * moment j
            - (law.weight i * moment i + law.weight j * moment j) := by ring
      _ = moment j - mean := by rw [hmass, hmoment, one_mul]
  have hupperIdentity :
      law.weight j * (moment j - moment i) = mean - moment i := by
    calc
      law.weight j * (moment j - moment i) =
          (law.weight i * moment i + law.weight j * moment j)
            - (law.weight i + law.weight j) * moment i := by ring
      _ = mean - moment i := by rw [hmass, hmoment, one_mul]
  constructor
  · rw [lowerOrbitWeight, eq_div_iff hden]
    exact hlowerIdentity
  · rw [upperOrbitWeight, eq_div_iff hden]
    exact hupperIdentity

/-- The sharpened finite extreme-point reduction: the surviving law is either a point mass at
the prescribed mean or has exactly two atoms whose moments strictly straddle that mean. -/
theorem exists_support_straddles {functional : FiniteMomentLaw ι moment mean → ℝ}
    (hconcave : IsConcaveFunctional functional) (law : FiniteMomentLaw ι moment mean) :
    ∃ reduced : FiniteMomentLaw ι moment mean,
      functional reduced ≤ functional law ∧
        ((∃ i, i ∈ reduced.support ∧ reduced.support.card = 1 ∧ moment i = mean) ∨
          ∃ i j, i ≠ j ∧ i ∈ reduced.support ∧ j ∈ reduced.support
            ∧ reduced.support.card = 2 ∧ moment i < mean ∧ mean < moment j) := by
  classical
  obtain ⟨reduced, hcard, hfunctional⟩ :=
    exists_support_card_le_two hconcave law
  have hcardPos : 0 < reduced.support.card := card_pos.2 reduced.support_nonempty
  have hcardCases : reduced.support.card = 1 ∨ reduced.support.card = 2 := by omega
  rcases hcardCases with hcardOne | hcardTwo
  · obtain ⟨i, hsupport⟩ := Finset.card_eq_one.mp hcardOne
    have hweight : reduced.weight i = 1 := by
      have hsum := reduced.sum_weight_eq_sum_support (fun _ ↦ (1 : ℝ))
      simp only [mul_one] at hsum
      rw [reduced.weight_sum, hsupport] at hsum
      simpa using hsum.symm
    have hmoment : moment i = mean := by
      have hsum := reduced.sum_weight_eq_sum_support moment
      rw [reduced.moment_sum, hsupport] at hsum
      simp only [sum_singleton] at hsum
      rw [hweight, one_mul] at hsum
      exact hsum.symm
    exact ⟨reduced, hfunctional,
      Or.inl ⟨i, by simp [hsupport], hcardOne, hmoment⟩⟩
  · obtain ⟨i, j, hij, hsupport⟩ := Finset.card_eq_two.mp hcardTwo
    have hiSupport : i ∈ reduced.support := by simp [hsupport]
    have hjSupport : j ∈ reduced.support := by simp [hsupport]
    have hiWeight : 0 < reduced.weight i := reduced.weight_pos_of_mem_support hiSupport
    have hjWeight : 0 < reduced.weight j := reduced.weight_pos_of_mem_support hjSupport
    have hmass := reduced.two_support_weights_sum hij hiSupport hjSupport hcardTwo
    have hmoment := reduced.two_support_moment_sum hij hiSupport hjSupport hcardTwo
    by_cases hmoments : moment i = moment j
    · rw [hmoments, ← add_mul, hmass, one_mul] at hmoment
      let left := pointMass i (hmoments.trans hmoment)
      let right := pointMass j hmoment
      have hiWeightLe : reduced.weight i ≤ 1 := by linarith
      have hp : reduced.weight i ∈ Icc (0 : ℝ) 1 := ⟨hiWeight.le, hiWeightLe⟩
      have hdecomposition :
          reduced = mix (reduced.weight i) left right hp := by
        apply FiniteMomentLaw.ext
        funext r
        by_cases hri : r = i
        · subst r
          simp [mix, left, right, pointMass, hij]
        · by_cases hrj : r = j
          · subst r
            simp [mix, left, right, pointMass, hri]
            linarith [hmass]
          · have hrSupport : r ∉ reduced.support := by
              rw [hsupport]
              simp [hri, hrj]
            have hrWeight := reduced.weight_eq_zero_of_not_mem_support hrSupport
            simp [mix, left, right, pointMass, hri, hrj, hrWeight]
      have hsegment := hconcave (reduced.weight i) hp left right
      rw [← hdecomposition] at hsegment
      have hiWeightLt : reduced.weight i < 1 := by linarith
      have hendpoint : functional left ≤ functional reduced ∨
          functional right ≤ functional reduced := by
        by_contra hnot
        push Not at hnot
        have hleftPositive :
            0 < reduced.weight i * (functional left - functional reduced) :=
          mul_pos hiWeight (sub_pos.2 hnot.1)
        have hrightPositive :
            0 < (1 - reduced.weight i) * (functional right - functional reduced) :=
          mul_pos (sub_pos.2 hiWeightLt) (sub_pos.2 hnot.2)
        nlinarith
      rcases hendpoint with hleft | hright
      · have hleftSupport := pointMass_support i (hmoments.trans hmoment)
        refine ⟨left, hleft.trans hfunctional,
          Or.inl ⟨i, by simp [left, hleftSupport], ?_, hmoments.trans hmoment⟩⟩
        simp [left, hleftSupport]
      · have hrightSupport := pointMass_support j hmoment
        refine ⟨right, hright.trans hfunctional,
          Or.inl ⟨j, by simp [right, hrightSupport], ?_, hmoment⟩⟩
        simp [right, hrightSupport]
    · rcases lt_or_gt_of_ne hmoments with hordered | hordered
      · have hlowerIdentity :
            mean - moment i = reduced.weight j * (moment j - moment i) := by
          calc
            mean - moment i =
                (reduced.weight i * moment i + reduced.weight j * moment j) - moment i :=
              congrArg (fun x ↦ x - moment i) hmoment.symm
            reduced.weight i * moment i + reduced.weight j * moment j - moment i =
                reduced.weight i * moment i + reduced.weight j * moment j
                  - (reduced.weight i + reduced.weight j) * moment i := by
              rw [hmass, one_mul]
            _ = reduced.weight j * (moment j - moment i) := by ring
        have hupperIdentity :
            moment j - mean = reduced.weight i * (moment j - moment i) := by
          calc
            moment j - mean = moment j -
                (reduced.weight i * moment i + reduced.weight j * moment j) :=
              congrArg (fun x ↦ moment j - x) hmoment.symm
            moment j -
                (reduced.weight i * moment i + reduced.weight j * moment j) =
              (reduced.weight i + reduced.weight j) * moment j
                - (reduced.weight i * moment i + reduced.weight j * moment j) := by
              rw [hmass, one_mul]
            _ = reduced.weight i * (moment j - moment i) := by ring
        have hlower : moment i < mean := by
          rw [← sub_pos, hlowerIdentity]
          exact mul_pos hjWeight (sub_pos.2 hordered)
        have hupper : mean < moment j := by
          rw [← sub_pos, hupperIdentity]
          exact mul_pos hiWeight (sub_pos.2 hordered)
        exact ⟨reduced, hfunctional,
          Or.inr ⟨i, j, hij, hiSupport, hjSupport, hcardTwo, hlower, hupper⟩⟩
      · have hlowerIdentity :
            mean - moment j = reduced.weight i * (moment i - moment j) := by
          calc
            mean - moment j =
                (reduced.weight i * moment i + reduced.weight j * moment j) - moment j :=
              congrArg (fun x ↦ x - moment j) hmoment.symm
            reduced.weight i * moment i + reduced.weight j * moment j - moment j =
                reduced.weight i * moment i + reduced.weight j * moment j
                  - (reduced.weight i + reduced.weight j) * moment j := by
              rw [hmass, one_mul]
            _ = reduced.weight i * (moment i - moment j) := by ring
        have hupperIdentity :
            moment i - mean = reduced.weight j * (moment i - moment j) := by
          calc
            moment i - mean = moment i -
                (reduced.weight i * moment i + reduced.weight j * moment j) :=
              congrArg (fun x ↦ moment i - x) hmoment.symm
            moment i -
                (reduced.weight i * moment i + reduced.weight j * moment j) =
              (reduced.weight i + reduced.weight j) * moment i
                - (reduced.weight i * moment i + reduced.weight j * moment j) := by
              rw [hmass, one_mul]
            _ = reduced.weight j * (moment i - moment j) := by ring
        have hlower : moment j < mean := by
          rw [← sub_pos, hlowerIdentity]
          exact mul_pos hiWeight (sub_pos.2 hordered)
        have hupper : mean < moment i := by
          rw [← sub_pos, hupperIdentity]
          exact mul_pos hjWeight (sub_pos.2 hordered)
        exact ⟨reduced, hfunctional,
          Or.inr ⟨j, i, hij.symm, hjSupport, hiSupport, hcardTwo, hlower, hupper⟩⟩

/-- The sharpened extreme-point reduction with the two surviving masses identified exactly. -/
theorem exists_support_straddles_with_weights
    {functional : FiniteMomentLaw ι moment mean → ℝ}
    (hconcave : IsConcaveFunctional functional) (law : FiniteMomentLaw ι moment mean) :
    ∃ reduced : FiniteMomentLaw ι moment mean,
      functional reduced ≤ functional law ∧
        ((∃ i, i ∈ reduced.support ∧ reduced.support.card = 1 ∧ moment i = mean) ∨
          ∃ i j, i ≠ j ∧ i ∈ reduced.support ∧ j ∈ reduced.support
            ∧ reduced.support.card = 2 ∧ moment i < mean ∧ mean < moment j
            ∧ reduced.weight i = lowerOrbitWeight (moment i) mean (moment j)
            ∧ reduced.weight j = upperOrbitWeight (moment i) mean (moment j)) := by
  obtain ⟨reduced, hfunctional, hsupport⟩ := exists_support_straddles hconcave law
  refine ⟨reduced, hfunctional, ?_⟩
  rcases hsupport with hsingleton | ⟨i, j, hij, hi, hj, hcard, hlower, hupper⟩
  · exact Or.inl hsingleton
  · obtain ⟨hlowerWeight, hupperWeight⟩ :=
      reduced.two_support_weights_eq_orbitWeights hi hj hcard (hlower.trans hupper)
    exact Or.inr
      ⟨i, j, hij, hi, hj, hcard, hlower, hupper, hlowerWeight, hupperWeight⟩

end FiniteMomentLaw

end Frankl
