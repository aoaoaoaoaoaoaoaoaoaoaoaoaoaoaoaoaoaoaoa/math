import MatrixMortality.DecimalSetterThreeBlockLongSupport

namespace MatrixMortality.DecimalSetterBridgeRay

open MatrixMortality.DecimalSetterAncestry
open MatrixMortality.DecimalSetterArithmetic
open MatrixMortality.DecimalSetterBridge
open MatrixMortality.DecimalSetterCarry
open MatrixMortality.DecimalSetterChamber
open MatrixMortality.DecimalSetterDepth
open MatrixMortality.PadicValuation

/-- A decimal-unit two-`c` peeled head exposes a smaller primitive gap factor. -/
theorem peeledDoubleCHead_unit_gapRelation
    {β : Nat} (tail : List TagLetter) (β_pos : 1 ≤ β)
    (head_unit :
      HasDecimalShell (code (peeledHeadWord β (.c :: .c :: tail)) : ℚ) 0 0) :
    ∃ suffix,
      1 ≤ suffix ∧ suffix ≤ β - 1 ∧
        9 *
            ((code (peeledHeadWord β (.c :: .c :: tail)) : ℤ) -
              10 * code (nearyMarker β)) =
          gapFactor suffix - 10 * gapFactor β := by
  obtain ⟨suffix, suffix_pos, suffix_le, _, head_relation⟩ :=
    peeledDoubleCHead_unit_shape tail β_pos head_unit
  have marker_identity := markerWord_code_identity β
  have marker_relation :
      9 * (code (nearyMarker β) : ℤ) + 7 = 52 * (10 : ℤ) ^ β := by
    simpa only [markerWord, nearyMarker] using (by exact_mod_cast marker_identity)
  refine ⟨suffix, suffix_pos, suffix_le, ?_⟩
  simp only [gapFactor]
  rw [show β + 2 = β + 2 by rfl, pow_add] at head_relation
  norm_num at head_relation
  linear_combination head_relation - 10 * marker_relation

/-- A long `c c` peeled-head pole forces the current lower code to absorb every primitive-gap
factor not shared with one strictly smaller relative-position gap. -/
theorem singletonPole_threeBlock_ruleCRoot_long_doubleC_forces_gapResonance
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current next : List NearyTile}
    (current_multi : 2 ≤ current.length) (current_ends : EndsInErase current)
    (next_multi : 2 ≤ next.length) (next_ends : EndsInErase next)
    (current_long : β + 3 ≤ (spell (nearyUpper β) current).length)
    {tail : List TagLetter}
    (next_letters : next.map NearyTile.letter = .c :: .c :: tail)
    (pole : HitsSquarePole β body [.erase targetLetter]
      [current, next, DecimalSetterMinimumBody.ruleCRoot]) :
    ∃ suffix,
      1 ≤ suffix ∧ suffix ≤ β - 1 ∧
        gapFactor β ∣
          (code (spell (nearyLower β body) current) : ℤ) * gapFactor suffix := by
  let upperWord := spell (nearyUpper β) next ++ nearyMarker β
  let width := (spell (nearyUpper β) next).length - 1
  have suffix_data := singletonPole_threeBlock_ruleCRoot_long_suffix
    β_large body targetLetter current_multi current_ends next_multi next_ends current_long pole
  have front_unit :
      HasDecimalShell (code (front width upperWord) : ℚ) 0 0 := by
    simpa only [upperWord, width] using suffix_data.2.2.2
  have next_nonempty : next ≠ [] := by
    intro next_nil
    simp [next_nil] at next_multi
  have front_eq :
      front width upperWord = peeledHeadWord β (next.map NearyTile.letter) := by
    simpa only [upperWord, width] using
      front_punctuatedUpper_eq_peeledHeadWord β next_nonempty
  have head_unit :
      HasDecimalShell (code (peeledHeadWord β (.c :: .c :: tail)) : ℚ) 0 0 := by
    rw [front_eq, next_letters] at front_unit
    exact front_unit
  obtain ⟨suffix, suffix_pos, suffix_le, coefficient_relation⟩ :=
    peeledDoubleCHead_unit_gapRelation tail (by omega) head_unit
  have support :=
    singletonPole_threeBlock_ruleCRoot_long_forces_headSupportProduct
      β_large body targetLetter current_multi current_ends next_multi next_ends current_long pole
  rw [next_letters] at support
  let q : ℤ := gapFactor β
  let V : ℤ := code (spell (nearyLower β body) current)
  have scaled_support :
      q ∣ V *
        (9 *
          ((code (peeledHeadWord β (.c :: .c :: tail)) : ℤ) -
            10 * code (nearyMarker β))) := by
    have scaled := support.mul_right 9
    simpa only [q, V, mul_assoc, mul_left_comm, mul_comm] using scaled
  have shifted_support : q ∣ V * (gapFactor suffix - 10 * q) := by
    rw [← coefficient_relation]
    exact scaled_support
  have correction : q ∣ V * (10 * q) := by
    exact dvd_mul_of_dvd_right (dvd_mul_left q 10) V
  have desired : q ∣ V * gapFactor suffix := by
    have summed := dvd_add shifted_support correction
    simpa [mul_sub] using summed
  exact ⟨suffix, suffix_pos, suffix_le, by simpa only [q, V] using desired⟩

/-- A common divisor of the ambient and relative-position gap factors has decimal period
dividing their exponent difference. -/
theorem gapFactor_commonDivisor_dvd_decimalPeriod
    {β suffix : Nat} (suffix_le : suffix ≤ β) {r : ℤ}
    (r_dvd_beta : r ∣ gapFactor β) (r_dvd_suffix : r ∣ gapFactor suffix) :
    r ∣ (10 : ℤ) ^ (β - suffix) - 1 := by
  let width := β - suffix
  have beta_eq : β = width + suffix := by
    dsimp only [width]
    omega
  have relation :
      gapFactor β =
        (10 : ℤ) ^ width * gapFactor suffix +
          7 * ((10 : ℤ) ^ width - 1) := by
    simp only [gapFactor, beta_eq, pow_add]
    ring
  have r_dvd_scaled_suffix : r ∣ (10 : ℤ) ^ width * gapFactor suffix :=
    r_dvd_suffix.mul_left _
  have r_dvd_seven_period : r ∣ 7 * ((10 : ℤ) ^ width - 1) := by
    rw [relation] at r_dvd_beta
    simpa using dvd_sub r_dvd_beta r_dvd_scaled_suffix
  have ten_coprime : IsCoprime ((10 : ℤ) ^ β) 7 :=
    (by norm_num : IsCoprime (10 : ℤ) 7).pow_left
  have twice_coprime : IsCoprime (2 * (10 : ℤ) ^ β) 7 :=
    (by norm_num : IsCoprime (2 : ℤ) 7).mul_left ten_coprime
  have beta_coprime_seven : IsCoprime (gapFactor β) (7 : ℤ) := by
    have shifted := twice_coprime.add_mul_left_left (-1)
    rw [show gapFactor β = 2 * (10 : ℤ) ^ β + 7 * (-1) by
      simp [gapFactor]
      ring]
    exact shifted
  have r_coprime_seven : IsCoprime r (7 : ℤ) :=
    IsCoprime.of_isCoprime_of_dvd_left beta_coprime_seven r_dvd_beta
  simpa only [width] using
    r_coprime_seven.dvd_of_dvd_mul_left r_dvd_seven_period

/-- Common divisors of two primitive gaps are exactly the relative-gap divisors whose decimal
period divides the exponent difference. -/
theorem gapFactor_commonDivisor_iff_relative_decimalPeriod
    {β suffix : Nat} (suffix_le : suffix ≤ β) (r : ℤ) :
    (r ∣ gapFactor β ∧ r ∣ gapFactor suffix) ↔
      (r ∣ gapFactor suffix ∧ r ∣ (10 : ℤ) ^ (β - suffix) - 1) := by
  constructor
  · rintro ⟨r_dvd_beta, r_dvd_suffix⟩
    exact ⟨r_dvd_suffix,
      gapFactor_commonDivisor_dvd_decimalPeriod suffix_le r_dvd_beta r_dvd_suffix⟩
  · rintro ⟨r_dvd_suffix, r_dvd_period⟩
    let width := β - suffix
    have beta_eq : β = width + suffix := by
      dsimp only [width]
      omega
    have relation :
        gapFactor β =
          (10 : ℤ) ^ width * gapFactor suffix +
            7 * ((10 : ℤ) ^ width - 1) := by
      simp only [gapFactor, beta_eq, pow_add]
      ring
    have first : r ∣ (10 : ℤ) ^ width * gapFactor suffix :=
      r_dvd_suffix.mul_left _
    have second : r ∣ 7 * ((10 : ℤ) ^ width - 1) :=
      r_dvd_period.mul_left 7
    refine ⟨?_, r_dvd_suffix⟩
    rw [relation]
    exact dvd_add first second

/-- If the ambient primitive gap is coprime to every smaller relative-position gap, the
complete ambient gap enters the current lower code on the long `c c` branch. -/
theorem singletonPole_threeBlock_ruleCRoot_long_doubleC_forces_gapFactor_currentLower
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current next : List NearyTile}
    (current_multi : 2 ≤ current.length) (current_ends : EndsInErase current)
    (next_multi : 2 ≤ next.length) (next_ends : EndsInErase next)
    (current_long : β + 3 ≤ (spell (nearyUpper β) current).length)
    {tail : List TagLetter}
    (next_letters : next.map NearyTile.letter = .c :: .c :: tail)
    (gap_pairwise :
      ∀ suffix, 1 ≤ suffix → suffix ≤ β - 1 →
        IsCoprime (gapFactor β) (gapFactor suffix))
    (pole : HitsSquarePole β body [.erase targetLetter]
      [current, next, DecimalSetterMinimumBody.ruleCRoot]) :
    gapFactor β ∣ (code (spell (nearyLower β body) current) : ℤ) := by
  obtain ⟨suffix, suffix_pos, suffix_le, product_dvd⟩ :=
    singletonPole_threeBlock_ruleCRoot_long_doubleC_forces_gapResonance
      β_large body targetLetter current_multi current_ends next_multi next_ends current_long
        next_letters pole
  exact (gap_pairwise suffix suffix_pos suffix_le).dvd_of_dvd_mul_right product_dvd

/-- Every ambient gap prime absent from the current lower code is a genuine relative-position
resonance: it divides a smaller gap and its decimal order divides the exponent difference. -/
theorem singletonPole_threeBlock_ruleCRoot_long_doubleC_exceptionalPrime_period
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current next : List NearyTile}
    (current_multi : 2 ≤ current.length) (current_ends : EndsInErase current)
    (next_multi : 2 ≤ next.length) (next_ends : EndsInErase next)
    (current_long : β + 3 ≤ (spell (nearyUpper β) current).length)
    {tail : List TagLetter}
    (next_letters : next.map NearyTile.letter = .c :: .c :: tail)
    {p : ℤ} (p_prime : Prime p) (p_dvd_gap : p ∣ gapFactor β)
    (p_absent : ¬p ∣ (code (spell (nearyLower β body) current) : ℤ))
    (pole : HitsSquarePole β body [.erase targetLetter]
      [current, next, DecimalSetterMinimumBody.ruleCRoot]) :
    ∃ suffix,
      1 ≤ suffix ∧ suffix ≤ β - 1 ∧
        p ∣ gapFactor suffix ∧ p ∣ (10 : ℤ) ^ (β - suffix) - 1 := by
  obtain ⟨suffix, suffix_pos, suffix_le, product_dvd⟩ :=
    singletonPole_threeBlock_ruleCRoot_long_doubleC_forces_gapResonance
      β_large body targetLetter current_multi current_ends next_multi next_ends current_long
        next_letters pole
  have p_dvd_product := p_dvd_gap.trans product_dvd
  have p_dvd_relative : p ∣ gapFactor suffix := by
    rcases p_prime.dvd_mul.mp p_dvd_product with current_support | relative_support
    · exact False.elim (p_absent current_support)
    · exact relative_support
  have period_support : p ∣ (10 : ℤ) ^ (β - suffix) - 1 :=
    gapFactor_commonDivisor_dvd_decimalPeriod (by omega) p_dvd_gap p_dvd_relative
  exact ⟨suffix, suffix_pos, suffix_le, p_dvd_relative, period_support⟩

end MatrixMortality.DecimalSetterBridgeRay
