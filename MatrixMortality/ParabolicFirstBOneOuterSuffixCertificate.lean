import MatrixMortality.ParabolicFirstBOneOuterSuffixCertificate0
import MatrixMortality.ParabolicFirstBOneOuterSuffixCertificate1

/-!
# Exact terminal suffix certificate below outer wait 211

The five tail-root chambers close in 96 exact suffix-tree nodes of depth at most five.
The unbounded chamber is first cut at inner wait 1448 by the analytic grammar gap.
-/

namespace MatrixMortality.ParabolicBlade

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBOneOuterSuffixCore_false_206_0_162
    (body : List TagLetter) (z : Nat) (z_lower : 7 ≤ z)
    (z_upper : z ≤ 8)
    (core : FirstBOneOuterSuffixCore body
      (firstBOneOuterSuffixH 0 206 162 z)
      (firstBOneOuterJ 206 162 z)
      (firstBOneOuterCorrection 206 162 z)) : False := by
  have interval : (7 ≤ z ∧ z ≤ 7) ∨ (8 ≤ z ∧ z ≤ 8) := by omega
  rcases interval with range0 | range1
  · exact firstBOneOuterSuffix_false_206_0_162_7_7 body z range0.1 range0.2 core
  · exact firstBOneOuterSuffix_false_206_0_162_8_8 body z range1.1 range1.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBOneOuterSuffixCore_false_207_2_202
    (body : List TagLetter) (z : Nat) (z_lower : 1 ≤ z)
    (z_upper : z ≤ 1)
    (core : FirstBOneOuterSuffixCore body
      (firstBOneOuterSuffixH 2 207 202 z)
      (firstBOneOuterJ 207 202 z)
      (firstBOneOuterCorrection 207 202 z)) : False := by
  exact firstBOneOuterSuffix_false_207_2_202_1_1 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBOneOuterSuffixCore_false_210_1_802
    (body : List TagLetter) (z : Nat) (z_lower : 4 ≤ z)
    (z_upper : z ≤ 4)
    (core : FirstBOneOuterSuffixCore body
      (firstBOneOuterSuffixH 1 210 802 z)
      (firstBOneOuterJ 210 802 z)
      (firstBOneOuterCorrection 210 802 z)) : False := by
  exact firstBOneOuterSuffix_false_210_1_802_4_4 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBOneOuterSuffixCore_false_210_0_812
    (body : List TagLetter) (z : Nat) (z_lower : 9 ≤ z)
    (z_upper : z ≤ 9)
    (core : FirstBOneOuterSuffixCore body
      (firstBOneOuterSuffixH 0 210 812 z)
      (firstBOneOuterJ 210 812 z)
      (firstBOneOuterCorrection 210 812 z)) : False := by
  exact firstBOneOuterSuffix_false_210_0_812_9_9 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBOneOuterSuffixCore_false_210_1_801
    (body : List TagLetter) (z : Nat) (z_lower : 380 ≤ z)
    (core : FirstBOneOuterSuffixCore body
      (firstBOneOuterSuffixH 1 210 801 z)
      (firstBOneOuterJ 210 801 z)
      (firstBOneOuterCorrection 210 801 z)) : False := by
  have z_upper : z ≤ 1447 := by
    have cap := firstBOneOuterRay_z_lt_1448 body z core
    omega
  have interval : (380 ≤ z ∧ z ≤ 380) ∨ (381 ≤ z ∧ z ≤ 382) ∨ (383 ≤ z ∧ z ≤ 389) ∨ (390 ≤ z ∧ z ≤
    409) ∨ (410 ≤ z ∧ z ≤ 486) ∨ (487 ≤ z ∧ z ≤ 487) ∨ (488 ≤ z ∧ z ≤ 1121) ∨ (1122 ≤ z ∧ z ≤ 1122)
    ∨ (1123 ≤ z ∧ z ≤ 1124) ∨ (1125 ≤ z ∧ z ≤ 1130) ∨ (1131 ≤ z ∧ z ≤ 1447) := by omega
  rcases interval with range0 | range1 | range2 | range3 | range4 | range5 | range6 | range7 |
    range8 | range9 | range10
  · exact firstBOneOuterSuffix_false_210_1_801_380_380 body z range0.1 range0.2 core
  · exact firstBOneOuterSuffix_false_210_1_801_381_382 body z range1.1 range1.2 core
  · exact firstBOneOuterSuffix_false_210_1_801_383_389 body z range2.1 range2.2 core
  · exact firstBOneOuterSuffix_false_210_1_801_390_409 body z range3.1 range3.2 core
  · exact firstBOneOuterSuffix_false_210_1_801_410_486 body z range4.1 range4.2 core
  · exact firstBOneOuterSuffix_false_210_1_801_487_487 body z range5.1 range5.2 core
  · exact firstBOneOuterSuffix_false_210_1_801_488_1121 body z range6.1 range6.2 core
  · exact firstBOneOuterSuffix_false_210_1_801_1122_1122 body z range7.1 range7.2 core
  · exact firstBOneOuterSuffix_false_210_1_801_1123_1124 body z range8.1 range8.2 core
  · exact firstBOneOuterSuffix_false_210_1_801_1125_1130 body z range9.1 range9.2 core
  · exact firstBOneOuterSuffix_false_210_1_801_1131_1447 body z range10.1 range10.2 core

end MatrixMortality.ParabolicBlade
