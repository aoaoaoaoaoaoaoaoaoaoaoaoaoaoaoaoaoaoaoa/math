import MatrixMortality.ParabolicFirstBZeroReduction
import MatrixMortality.ParabolicFirstBZeroSuffixCertificate0
import MatrixMortality.ParabolicFirstBZeroSuffixCertificate1
import MatrixMortality.ParabolicFirstBZeroSuffixCertificate2
import MatrixMortality.ParabolicFirstBZeroSuffixCertificate3
import MatrixMortality.ParabolicFirstBZeroSuffixCertificate4
import MatrixMortality.ParabolicFirstBZeroSuffixCertificate5
import MatrixMortality.ParabolicFirstBZeroSuffixCertificate6
import MatrixMortality.ParabolicFirstBZeroSuffixCertificate7
import MatrixMortality.ParabolicFirstBZeroSuffixCertificate8
import MatrixMortality.ParabolicFirstBZeroSuffixCertificate9
import MatrixMortality.ParabolicFirstBZeroSuffixCertificate10
import MatrixMortality.ParabolicFirstBZeroSuffixCertificate11
import MatrixMortality.ParabolicFirstBZeroSuffixCertificate12
import MatrixMortality.ParabolicFirstBZeroSuffixCertificate13
import MatrixMortality.ParabolicFirstBZeroSuffixCertificate14
import MatrixMortality.ParabolicFirstBZeroSuffixCertificate15
import MatrixMortality.ParabolicFirstBZeroSuffixCertificate16
import MatrixMortality.ParabolicFirstBZeroSuffixCertificate17
import MatrixMortality.ParabolicFirstBZeroSuffixCertificate18
import MatrixMortality.ParabolicFirstBZeroSuffixCertificate19
import MatrixMortality.ParabolicFirstBZeroSuffixCertificate20

/-!
# Exact terminal suffix certificate for the leading first-`b` cylinder

The 146 retained tail-root chambers close in 1,751 exact suffix-tree nodes of depth at
most ten. Eleven chambers are partitioned into a finite prefix and a semi-infinite ray.
-/

namespace MatrixMortality.ParabolicBlade

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_187_0_136
    (body : List TagLetter) (z : Nat)
    (z_lower : 2 ≤ z) (z_upper : z ≤ 2)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 187 136 z)
      (firstBOneOuterJ 187 136 z)
      (firstBOneOuterCorrection 187 136 z)) : False := by
  exact firstBZeroSuffix_false_187_0_136_2_2 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_190_5_168
    (body : List TagLetter) (z : Nat)
    (z_lower : 161 ≤ z) (z_upper : z ≤ 170)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 5 190 168 z)
      (firstBOneOuterJ 190 168 z)
      (firstBOneOuterCorrection 190 168 z)) : False := by
  have interval : (161 ≤ z ∧ z ≤ 161) ∨ (162 ≤ z ∧ z ≤ 163) ∨ (164 ≤ z ∧ z ≤ 169) ∨ (170 ≤ z ∧ z ≤
    170) := by omega
  rcases interval with range0 | range1 | range2 | range3
  · exact firstBZeroSuffix_false_190_5_168_161_161 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_190_5_168_162_163 body z range1.1 range1.2 core
  · exact firstBZeroSuffix_false_190_5_168_164_169 body z range2.1 range2.2 core
  · exact firstBZeroSuffix_false_190_5_168_170_170 body z range3.1 range3.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_199_2_541
    (body : List TagLetter) (z : Nat)
    (z_lower : 98 ≤ z) (z_upper : z ≤ 285)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 2 199 541 z)
      (firstBOneOuterJ 199 541 z)
      (firstBOneOuterCorrection 199 541 z)) : False := by
  have interval : (98 ≤ z ∧ z ≤ 98) ∨ (99 ≤ z ∧ z ≤ 100) ∨ (101 ≤ z ∧ z ≤ 104) ∨ (105 ≤ z ∧ z ≤ 121)
    ∨ (122 ≤ z ∧ z ≤ 238) ∨ (239 ≤ z ∧ z ≤ 239) ∨ (240 ≤ z ∧ z ≤ 240) ∨ (241 ≤ z ∧ z ≤ 285) := by
    omega
  rcases interval with range0 | range1 | range2 | range3 | range4 | range5 | range6 | range7
  · exact firstBZeroSuffix_false_199_2_541_98_98 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_199_2_541_99_100 body z range1.1 range1.2 core
  · exact firstBZeroSuffix_false_199_2_541_101_104 body z range2.1 range2.2 core
  · exact firstBZeroSuffix_false_199_2_541_105_121 body z range3.1 range3.2 core
  · exact firstBZeroSuffix_false_199_2_541_122_238 body z range4.1 range4.2 core
  · exact firstBZeroSuffix_false_199_2_541_239_239 body z range5.1 range5.2 core
  · exact firstBZeroSuffix_false_199_2_541_240_240 body z range6.1 range6.2 core
  · exact firstBZeroSuffix_false_199_2_541_241_285 body z range7.1 range7.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_200_2_707
    (body : List TagLetter) (z : Nat)
    (z_lower : 2 ≤ z) (z_upper : z ≤ 2)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 2 200 707 z)
      (firstBOneOuterJ 200 707 z)
      (firstBOneOuterCorrection 200 707 z)) : False := by
  exact firstBZeroSuffix_false_200_2_707_2_2 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_201_0_1036
    (body : List TagLetter) (z : Nat)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 201 1036 z)
      (firstBOneOuterJ 201 1036 z)
      (firstBOneOuterCorrection 201 1036 z)) : False := by
  by_cases z_small : z < 40
  · have z_upper : z ≤ 39 := by omega
    have interval : (0 ≤ z ∧ z ≤ 24) ∨ (25 ≤ z ∧ z ≤ 25) ∨ (26 ≤ z ∧ z ≤ 28) ∨ (29 ≤ z ∧ z ≤ 39) :=
      by omega
    rcases interval with range0 | range1 | range2 | range3
    · exact firstBZeroSuffix_false_201_0_1036_0_24 body z range0.1 range0.2 core
    · exact firstBZeroSuffix_false_201_0_1036_25_25 body z range1.1 range1.2 core
    · exact firstBZeroSuffix_false_201_0_1036_26_28 body z range2.1 range2.2 core
    · exact firstBZeroSuffix_false_201_0_1036_29_39 body z range3.1 range3.2 core
  · have z_lower : 40 ≤ z := by omega
    exact firstBZeroSuffix_false_201_0_1036_ray_40 body z z_lower core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_201_0_1037
    (body : List TagLetter) (z : Nat)
    (z_lower : 2 ≤ z) (z_upper : z ≤ 2)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 201 1037 z)
      (firstBOneOuterJ 201 1037 z)
      (firstBOneOuterCorrection 201 1037 z)) : False := by
  exact firstBZeroSuffix_false_201_0_1037_2_2 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_201_0_1038
    (body : List TagLetter) (z : Nat)
    (z_lower : 1 ≤ z) (z_upper : z ≤ 1)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 201 1038 z)
      (firstBOneOuterJ 201 1038 z)
      (firstBOneOuterCorrection 201 1038 z)) : False := by
  exact firstBZeroSuffix_false_201_0_1038_1_1 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_202_3_1774
    (body : List TagLetter) (z : Nat)
    (z_lower : 64 ≤ z) (z_upper : z ≤ 71)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 3 202 1774 z)
      (firstBOneOuterJ 202 1774 z)
      (firstBOneOuterCorrection 202 1774 z)) : False := by
  have interval : (64 ≤ z ∧ z ≤ 65) ∨ (66 ≤ z ∧ z ≤ 70) ∨ (71 ≤ z ∧ z ≤ 71) := by omega
  rcases interval with range0 | range1 | range2
  · exact firstBZeroSuffix_false_202_3_1774_64_65 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_202_3_1774_66_70 body z range1.1 range1.2 core
  · exact firstBZeroSuffix_false_202_3_1774_71_71 body z range2.1 range2.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_202_1_1795
    (body : List TagLetter) (z : Nat)
    (z_lower : 51 ≤ z) (z_upper : z ≤ 282)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 1 202 1795 z)
      (firstBOneOuterJ 202 1795 z)
      (firstBOneOuterCorrection 202 1795 z)) : False := by
  have interval : (51 ≤ z ∧ z ≤ 51) ∨ (52 ≤ z ∧ z ≤ 54) ∨ (55 ≤ z ∧ z ≤ 55) ∨ (56 ≤ z ∧ z ≤ 66) ∨
    (67 ≤ z ∧ z ≤ 67) ∨ (68 ≤ z ∧ z ≤ 191) ∨ (192 ≤ z ∧ z ≤ 192) ∨ (193 ≤ z ∧ z ≤ 193) ∨ (194 ≤ z ∧
    z ≤ 282) := by omega
  rcases interval with range0 | range1 | range2 | range3 | range4 | range5 | range6 | range7 |
    range8
  · exact firstBZeroSuffix_false_202_1_1795_51_51 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_202_1_1795_52_54 body z range1.1 range1.2 core
  · exact firstBZeroSuffix_false_202_1_1795_55_55 body z range2.1 range2.2 core
  · exact firstBZeroSuffix_false_202_1_1795_56_66 body z range3.1 range3.2 core
  · exact firstBZeroSuffix_false_202_1_1795_67_67 body z range4.1 range4.2 core
  · exact firstBZeroSuffix_false_202_1_1795_68_191 body z range5.1 range5.2 core
  · exact firstBZeroSuffix_false_202_1_1795_192_192 body z range6.1 range6.2 core
  · exact firstBZeroSuffix_false_202_1_1795_193_193 body z range7.1 range7.2 core
  · exact firstBZeroSuffix_false_202_1_1795_194_282 body z range8.1 range8.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_202_1_1796
    (body : List TagLetter) (z : Nat)
    (z_lower : 6 ≤ z) (z_upper : z ≤ 6)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 1 202 1796 z)
      (firstBOneOuterJ 202 1796 z)
      (firstBOneOuterCorrection 202 1796 z)) : False := by
  exact firstBZeroSuffix_false_202_1_1796_6_6 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_202_0_1844
    (body : List TagLetter) (z : Nat)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 202 1844 z)
      (firstBOneOuterJ 202 1844 z)
      (firstBOneOuterCorrection 202 1844 z)) : False := by
  by_cases z_small : z < 39
  · have z_upper : z ≤ 38 := by omega
    have interval : (0 ≤ z ∧ z ≤ 24) ∨ (25 ≤ z ∧ z ≤ 25) ∨ (26 ≤ z ∧ z ≤ 28) ∨ (29 ≤ z ∧ z ≤ 38) :=
      by omega
    rcases interval with range0 | range1 | range2 | range3
    · exact firstBZeroSuffix_false_202_0_1844_0_24 body z range0.1 range0.2 core
    · exact firstBZeroSuffix_false_202_0_1844_25_25 body z range1.1 range1.2 core
    · exact firstBZeroSuffix_false_202_0_1844_26_28 body z range2.1 range2.2 core
    · exact firstBZeroSuffix_false_202_0_1844_29_38 body z range3.1 range3.2 core
  · have z_lower : 39 ≤ z := by omega
    exact firstBZeroSuffix_false_202_0_1844_ray_39 body z z_lower core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_202_0_1845
    (body : List TagLetter) (z : Nat)
    (z_lower : 6 ≤ z) (z_upper : z ≤ 7)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 202 1845 z)
      (firstBOneOuterJ 202 1845 z)
      (firstBOneOuterCorrection 202 1845 z)) : False := by
  exact firstBZeroSuffix_false_202_0_1845_6_7 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_202_1_1870
    (body : List TagLetter) (z : Nat)
    (z_lower : 0 ≤ z) (z_upper : z ≤ 0)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 1 202 1870 z)
      (firstBOneOuterJ 202 1870 z)
      (firstBOneOuterCorrection 202 1870 z)) : False := by
  exact firstBZeroSuffix_false_202_1_1870_0_0 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_202_0_1923
    (body : List TagLetter) (z : Nat)
    (z_lower : 0 ≤ z) (z_upper : z ≤ 0)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 202 1923 z)
      (firstBOneOuterJ 202 1923 z)
      (firstBOneOuterCorrection 202 1923 z)) : False := by
  exact firstBZeroSuffix_false_202_0_1923_0_0 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_8_6950
    (body : List TagLetter) (z : Nat)
    (z_lower : 1117 ≤ z) (z_upper : z ≤ 1125)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 8 203 6950 z)
      (firstBOneOuterJ 203 6950 z)
      (firstBOneOuterCorrection 203 6950 z)) : False := by
  have interval : (1117 ≤ z ∧ z ≤ 1117) ∨ (1118 ≤ z ∧ z ≤ 1119) ∨ (1120 ≤ z ∧ z ≤ 1124) ∨ (1125 ≤ z
    ∧ z ≤ 1125) := by omega
  rcases interval with range0 | range1 | range2 | range3
  · exact firstBZeroSuffix_false_203_8_6950_1117_1117 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_8_6950_1118_1119 body z range1.1 range1.2 core
  · exact firstBZeroSuffix_false_203_8_6950_1120_1124 body z range2.1 range2.2 core
  · exact firstBZeroSuffix_false_203_8_6950_1125_1125 body z range3.1 range3.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_7_6951
    (body : List TagLetter) (z : Nat)
    (z_lower : 128 ≤ z) (z_upper : z ≤ 128)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 7 203 6951 z)
      (firstBOneOuterJ 203 6951 z)
      (firstBOneOuterCorrection 203 6951 z)) : False := by
  exact firstBZeroSuffix_false_203_7_6951_128_128 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_6_6952
    (body : List TagLetter) (z : Nat)
    (z_lower : 114 ≤ z) (z_upper : z ≤ 114)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 6 203 6952 z)
      (firstBOneOuterJ 203 6952 z)
      (firstBOneOuterCorrection 203 6952 z)) : False := by
  exact firstBZeroSuffix_false_203_6_6952_114_114 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_5_6954
    (body : List TagLetter) (z : Nat)
    (z_lower : 573 ≤ z) (z_upper : z ≤ 640)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 5 203 6954 z)
      (firstBOneOuterJ 203 6954 z)
      (firstBOneOuterCorrection 203 6954 z)) : False := by
  have interval : (573 ≤ z ∧ z ≤ 574) ∨ (575 ≤ z ∧ z ≤ 578) ∨ (579 ≤ z ∧ z ≤ 591) ∨ (592 ≤ z ∧ z ≤
    632) ∨ (633 ≤ z ∧ z ≤ 640) := by omega
  rcases interval with range0 | range1 | range2 | range3 | range4
  · exact firstBZeroSuffix_false_203_5_6954_573_574 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_5_6954_575_578 body z range1.1 range1.2 core
  · exact firstBZeroSuffix_false_203_5_6954_579_591 body z range2.1 range2.2 core
  · exact firstBZeroSuffix_false_203_5_6954_592_632 body z range3.1 range3.2 core
  · exact firstBZeroSuffix_false_203_5_6954_633_640 body z range4.1 range4.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_5_6955
    (body : List TagLetter) (z : Nat)
    (z_lower : 86 ≤ z) (z_upper : z ≤ 87)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 5 203 6955 z)
      (firstBOneOuterJ 203 6955 z)
      (firstBOneOuterCorrection 203 6955 z)) : False := by
  have interval : (86 ≤ z ∧ z ≤ 86) ∨ (87 ≤ z ∧ z ≤ 87) := by omega
  rcases interval with range0 | range1
  · exact firstBZeroSuffix_false_203_5_6955_86_86 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_5_6955_87_87 body z range1.1 range1.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_5_6961
    (body : List TagLetter) (z : Nat)
    (z_lower : 14 ≤ z) (z_upper : z ≤ 14)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 5 203 6961 z)
      (firstBOneOuterJ 203 6961 z)
      (firstBOneOuterCorrection 203 6961 z)) : False := by
  exact firstBZeroSuffix_false_203_5_6961_14_14 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_4_6962
    (body : List TagLetter) (z : Nat)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 4 203 6962 z)
      (firstBOneOuterJ 203 6962 z)
      (firstBOneOuterCorrection 203 6962 z)) : False := by
  by_cases z_small : z < 5966
  · have z_upper : z ≤ 5965 := by omega
    have interval : (0 ≤ z ∧ z ≤ 2993) ∨ (2994 ≤ z ∧ z ≤ 2995) ∨ (2996 ≤ z ∧ z ≤ 2999) ∨ (3000 ≤ z ∧
      z ≤ 3011) ∨ (3012 ≤ z ∧ z ≤ 3049) ∨ (3050 ≤ z ∧ z ≤ 3167) ∨ (3168 ≤ z ∧ z ≤ 3168) ∨ (3169 ≤ z
      ∧ z ≤ 3586) ∨ (3587 ≤ z ∧ z ≤ 3587) ∨ (3588 ≤ z ∧ z ≤ 3589) ∨ (3590 ≤ z ∧ z ≤ 5940) ∨ (5941 ≤
      z ∧ z ≤ 5941) ∨ (5942 ≤ z ∧ z ≤ 5943) ∨ (5944 ≤ z ∧ z ≤ 5949) ∨ (5950 ≤ z ∧ z ≤ 5965) := by
      omega
    rcases interval with range0 | range1 | range2 | range3 | range4 | range5 | range6 | range7 |
      range8 | range9 | range10 | range11 | range12 | range13 | range14
    · exact firstBZeroSuffix_false_203_4_6962_0_2993 body z range0.1 range0.2 core
    · exact firstBZeroSuffix_false_203_4_6962_2994_2995 body z range1.1 range1.2 core
    · exact firstBZeroSuffix_false_203_4_6962_2996_2999 body z range2.1 range2.2 core
    · exact firstBZeroSuffix_false_203_4_6962_3000_3011 body z range3.1 range3.2 core
    · exact firstBZeroSuffix_false_203_4_6962_3012_3049 body z range4.1 range4.2 core
    · exact firstBZeroSuffix_false_203_4_6962_3050_3167 body z range5.1 range5.2 core
    · exact firstBZeroSuffix_false_203_4_6962_3168_3168 body z range6.1 range6.2 core
    · exact firstBZeroSuffix_false_203_4_6962_3169_3586 body z range7.1 range7.2 core
    · exact firstBZeroSuffix_false_203_4_6962_3587_3587 body z range8.1 range8.2 core
    · exact firstBZeroSuffix_false_203_4_6962_3588_3589 body z range9.1 range9.2 core
    · exact firstBZeroSuffix_false_203_4_6962_3590_5940 body z range10.1 range10.2 core
    · exact firstBZeroSuffix_false_203_4_6962_5941_5941 body z range11.1 range11.2 core
    · exact firstBZeroSuffix_false_203_4_6962_5942_5943 body z range12.1 range12.2 core
    · exact firstBZeroSuffix_false_203_4_6962_5944_5949 body z range13.1 range13.2 core
    · exact firstBZeroSuffix_false_203_4_6962_5950_5965 body z range14.1 range14.2 core
  · have z_lower : 5966 ≤ z := by omega
    exact firstBZeroSuffix_false_203_4_6962_ray_5966 body z z_lower core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_4_6963
    (body : List TagLetter) (z : Nat)
    (z_lower : 98 ≤ z) (z_upper : z ≤ 103)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 4 203 6963 z)
      (firstBOneOuterJ 203 6963 z)
      (firstBOneOuterCorrection 203 6963 z)) : False := by
  have interval : (98 ≤ z ∧ z ≤ 98) ∨ (99 ≤ z ∧ z ≤ 99) ∨ (100 ≤ z ∧ z ≤ 102) ∨ (103 ≤ z ∧ z ≤ 103)
    := by omega
  rcases interval with range0 | range1 | range2 | range3
  · exact firstBZeroSuffix_false_203_4_6963_98_98 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_4_6963_99_99 body z range1.1 range1.2 core
  · exact firstBZeroSuffix_false_203_4_6963_100_102 body z range2.1 range2.2 core
  · exact firstBZeroSuffix_false_203_4_6963_103_103 body z range3.1 range3.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_4_6964
    (body : List TagLetter) (z : Nat)
    (z_lower : 50 ≤ z) (z_upper : z ≤ 51)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 4 203 6964 z)
      (firstBOneOuterJ 203 6964 z)
      (firstBOneOuterCorrection 203 6964 z)) : False := by
  have interval : (50 ≤ z ∧ z ≤ 50) ∨ (51 ≤ z ∧ z ≤ 51) := by omega
  rcases interval with range0 | range1
  · exact firstBZeroSuffix_false_203_4_6964_50_50 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_4_6964_51_51 body z range1.1 range1.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_3_6987
    (body : List TagLetter) (z : Nat)
    (z_lower : 206 ≤ z) (z_upper : z ≤ 313)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 3 203 6987 z)
      (firstBOneOuterJ 203 6987 z)
      (firstBOneOuterCorrection 203 6987 z)) : False := by
  have interval : (206 ≤ z ∧ z ≤ 206) ∨ (207 ≤ z ∧ z ≤ 208) ∨ (209 ≤ z ∧ z ≤ 213) ∨ (214 ≤ z ∧ z ≤
    229) ∨ (230 ≤ z ∧ z ≤ 297) ∨ (298 ≤ z ∧ z ≤ 313) := by omega
  rcases interval with range0 | range1 | range2 | range3 | range4 | range5
  · exact firstBZeroSuffix_false_203_3_6987_206_206 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_3_6987_207_208 body z range1.1 range1.2 core
  · exact firstBZeroSuffix_false_203_3_6987_209_213 body z range2.1 range2.2 core
  · exact firstBZeroSuffix_false_203_3_6987_214_229 body z range3.1 range3.2 core
  · exact firstBZeroSuffix_false_203_3_6987_230_297 body z range4.1 range4.2 core
  · exact firstBZeroSuffix_false_203_3_6987_298_313 body z range5.1 range5.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_3_6988
    (body : List TagLetter) (z : Nat)
    (z_lower : 69 ≤ z) (z_upper : z ≤ 76)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 3 203 6988 z)
      (firstBOneOuterJ 203 6988 z)
      (firstBOneOuterCorrection 203 6988 z)) : False := by
  have interval : (69 ≤ z ∧ z ≤ 70) ∨ (71 ≤ z ∧ z ≤ 75) ∨ (76 ≤ z ∧ z ≤ 76) := by omega
  rcases interval with range0 | range1 | range2
  · exact firstBZeroSuffix_false_203_3_6988_69_70 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_3_6988_71_75 body z range1.1 range1.2 core
  · exact firstBZeroSuffix_false_203_3_6988_76_76 body z range2.1 range2.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_3_6989
    (body : List TagLetter) (z : Nat)
    (z_lower : 41 ≤ z) (z_upper : z ≤ 43)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 3 203 6989 z)
      (firstBOneOuterJ 203 6989 z)
      (firstBOneOuterCorrection 203 6989 z)) : False := by
  have interval : (41 ≤ z ∧ z ≤ 41) ∨ (42 ≤ z ∧ z ≤ 43) := by omega
  rcases interval with range0 | range1
  · exact firstBZeroSuffix_false_203_3_6989_41_41 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_3_6989_42_43 body z range1.1 range1.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_3_6990
    (body : List TagLetter) (z : Nat)
    (z_lower : 30 ≤ z) (z_upper : z ≤ 30)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 3 203 6990 z)
      (firstBOneOuterJ 203 6990 z)
      (firstBOneOuterCorrection 203 6990 z)) : False := by
  exact firstBZeroSuffix_false_203_3_6990_30_30 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_3_6991
    (body : List TagLetter) (z : Nat)
    (z_lower : 23 ≤ z) (z_upper : z ≤ 23)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 3 203 6991 z)
      (firstBOneOuterJ 203 6991 z)
      (firstBOneOuterCorrection 203 6991 z)) : False := by
  exact firstBZeroSuffix_false_203_3_6991_23_23 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_3_6992
    (body : List TagLetter) (z : Nat)
    (z_lower : 19 ≤ z) (z_upper : z ≤ 19)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 3 203 6992 z)
      (firstBOneOuterJ 203 6992 z)
      (firstBOneOuterCorrection 203 6992 z)) : False := by
  exact firstBZeroSuffix_false_203_3_6992_19_19 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_3_6993
    (body : List TagLetter) (z : Nat)
    (z_lower : 16 ≤ z) (z_upper : z ≤ 16)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 3 203 6993 z)
      (firstBOneOuterJ 203 6993 z)
      (firstBOneOuterCorrection 203 6993 z)) : False := by
  exact firstBZeroSuffix_false_203_3_6993_16_16 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_3_6995
    (body : List TagLetter) (z : Nat)
    (z_lower : 12 ≤ z) (z_upper : z ≤ 12)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 3 203 6995 z)
      (firstBOneOuterJ 203 6995 z)
      (firstBOneOuterCorrection 203 6995 z)) : False := by
  exact firstBZeroSuffix_false_203_3_6995_12_12 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_3_7001
    (body : List TagLetter) (z : Nat)
    (z_lower : 7 ≤ z) (z_upper : z ≤ 7)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 3 203 7001 z)
      (firstBOneOuterJ 203 7001 z)
      (firstBOneOuterCorrection 203 7001 z)) : False := by
  exact firstBZeroSuffix_false_203_3_7001_7_7 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_2_7062
    (body : List TagLetter) (z : Nat)
    (z_lower : 122 ≤ z) (z_upper : z ≤ 306)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 2 203 7062 z)
      (firstBOneOuterJ 203 7062 z)
      (firstBOneOuterCorrection 203 7062 z)) : False := by
  have interval : (122 ≤ z ∧ z ≤ 123) ∨ (124 ≤ z ∧ z ≤ 128) ∨ (129 ≤ z ∧ z ≤ 147) ∨ (148 ≤ z ∧ z ≤
    264) ∨ (265 ≤ z ∧ z ≤ 265) ∨ (266 ≤ z ∧ z ≤ 306) := by omega
  rcases interval with range0 | range1 | range2 | range3 | range4 | range5
  · exact firstBZeroSuffix_false_203_2_7062_122_123 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_2_7062_124_128 body z range1.1 range1.2 core
  · exact firstBZeroSuffix_false_203_2_7062_129_147 body z range2.1 range2.2 core
  · exact firstBZeroSuffix_false_203_2_7062_148_264 body z range3.1 range3.2 core
  · exact firstBZeroSuffix_false_203_2_7062_265_265 body z range4.1 range4.2 core
  · exact firstBZeroSuffix_false_203_2_7062_266_306 body z range5.1 range5.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_2_7063
    (body : List TagLetter) (z : Nat)
    (z_lower : 56 ≤ z) (z_upper : z ≤ 77)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 2 203 7063 z)
      (firstBOneOuterJ 203 7063 z)
      (firstBOneOuterCorrection 203 7063 z)) : False := by
  have interval : (56 ≤ z ∧ z ≤ 56) ∨ (57 ≤ z ∧ z ≤ 57) ∨ (58 ≤ z ∧ z ≤ 61) ∨ (62 ≤ z ∧ z ≤ 74) ∨
    (75 ≤ z ∧ z ≤ 77) := by omega
  rcases interval with range0 | range1 | range2 | range3 | range4
  · exact firstBZeroSuffix_false_203_2_7063_56_56 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_2_7063_57_57 body z range1.1 range1.2 core
  · exact firstBZeroSuffix_false_203_2_7063_58_61 body z range2.1 range2.2 core
  · exact firstBZeroSuffix_false_203_2_7063_62_74 body z range3.1 range3.2 core
  · exact firstBZeroSuffix_false_203_2_7063_75_77 body z range4.1 range4.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_2_7064
    (body : List TagLetter) (z : Nat)
    (z_lower : 37 ≤ z) (z_upper : z ≤ 44)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 2 203 7064 z)
      (firstBOneOuterJ 203 7064 z)
      (firstBOneOuterCorrection 203 7064 z)) : False := by
  have interval : (37 ≤ z ∧ z ≤ 38) ∨ (39 ≤ z ∧ z ≤ 43) ∨ (44 ≤ z ∧ z ≤ 44) := by omega
  rcases interval with range0 | range1 | range2
  · exact firstBZeroSuffix_false_203_2_7064_37_38 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_2_7064_39_43 body z range1.1 range1.2 core
  · exact firstBZeroSuffix_false_203_2_7064_44_44 body z range2.1 range2.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_2_7065
    (body : List TagLetter) (z : Nat)
    (z_lower : 27 ≤ z) (z_upper : z ≤ 31)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 2 203 7065 z)
      (firstBOneOuterJ 203 7065 z)
      (firstBOneOuterCorrection 203 7065 z)) : False := by
  have interval : (27 ≤ z ∧ z ≤ 27) ∨ (28 ≤ z ∧ z ≤ 28) ∨ (29 ≤ z ∧ z ≤ 30) ∨ (31 ≤ z ∧ z ≤ 31) :=
    by omega
  rcases interval with range0 | range1 | range2 | range3
  · exact firstBZeroSuffix_false_203_2_7065_27_27 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_2_7065_28_28 body z range1.1 range1.2 core
  · exact firstBZeroSuffix_false_203_2_7065_29_30 body z range2.1 range2.2 core
  · exact firstBZeroSuffix_false_203_2_7065_31_31 body z range3.1 range3.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_2_7066
    (body : List TagLetter) (z : Nat)
    (z_lower : 22 ≤ z) (z_upper : z ≤ 23)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 2 203 7066 z)
      (firstBOneOuterJ 203 7066 z)
      (firstBOneOuterCorrection 203 7066 z)) : False := by
  have interval : (22 ≤ z ∧ z ≤ 22) ∨ (23 ≤ z ∧ z ≤ 23) := by omega
  rcases interval with range0 | range1
  · exact firstBZeroSuffix_false_203_2_7066_22_22 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_2_7066_23_23 body z range1.1 range1.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_2_7067
    (body : List TagLetter) (z : Nat)
    (z_lower : 18 ≤ z) (z_upper : z ≤ 19)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 2 203 7067 z)
      (firstBOneOuterJ 203 7067 z)
      (firstBOneOuterCorrection 203 7067 z)) : False := by
  have interval : (18 ≤ z ∧ z ≤ 18) ∨ (19 ≤ z ∧ z ≤ 19) := by omega
  rcases interval with range0 | range1
  · exact firstBZeroSuffix_false_203_2_7067_18_18 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_2_7067_19_19 body z range1.1 range1.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_2_7068
    (body : List TagLetter) (z : Nat)
    (z_lower : 16 ≤ z) (z_upper : z ≤ 16)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 2 203 7068 z)
      (firstBOneOuterJ 203 7068 z)
      (firstBOneOuterCorrection 203 7068 z)) : False := by
  exact firstBZeroSuffix_false_203_2_7068_16_16 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_2_7069
    (body : List TagLetter) (z : Nat)
    (z_lower : 14 ≤ z) (z_upper : z ≤ 14)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 2 203 7069 z)
      (firstBOneOuterJ 203 7069 z)
      (firstBOneOuterCorrection 203 7069 z)) : False := by
  exact firstBZeroSuffix_false_203_2_7069_14_14 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_2_7070
    (body : List TagLetter) (z : Nat)
    (z_lower : 12 ≤ z) (z_upper : z ≤ 12)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 2 203 7070 z)
      (firstBOneOuterJ 203 7070 z)
      (firstBOneOuterCorrection 203 7070 z)) : False := by
  exact firstBZeroSuffix_false_203_2_7070_12_12 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_2_7071
    (body : List TagLetter) (z : Nat)
    (z_lower : 11 ≤ z) (z_upper : z ≤ 11)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 2 203 7071 z)
      (firstBOneOuterJ 203 7071 z)
      (firstBOneOuterCorrection 203 7071 z)) : False := by
  exact firstBZeroSuffix_false_203_2_7071_11_11 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_2_7073
    (body : List TagLetter) (z : Nat)
    (z_lower : 9 ≤ z) (z_upper : z ≤ 9)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 2 203 7073 z)
      (firstBOneOuterJ 203 7073 z)
      (firstBOneOuterCorrection 203 7073 z)) : False := by
  exact firstBZeroSuffix_false_203_2_7073_9_9 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_2_7076
    (body : List TagLetter) (z : Nat)
    (z_lower : 7 ≤ z) (z_upper : z ≤ 7)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 2 203 7076 z)
      (firstBOneOuterJ 203 7076 z)
      (firstBOneOuterCorrection 203 7076 z)) : False := by
  exact firstBZeroSuffix_false_203_2_7076_7_7 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_3_7081
    (body : List TagLetter) (z : Nat)
    (z_lower : 1 ≤ z) (z_upper : z ≤ 1)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 3 203 7081 z)
      (firstBOneOuterJ 203 7081 z)
      (firstBOneOuterCorrection 203 7081 z)) : False := by
  exact firstBZeroSuffix_false_203_3_7081_1_1 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_2_7082
    (body : List TagLetter) (z : Nat)
    (z_lower : 5 ≤ z) (z_upper : z ≤ 5)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 2 203 7082 z)
      (firstBOneOuterJ 203 7082 z)
      (firstBOneOuterCorrection 203 7082 z)) : False := by
  exact firstBZeroSuffix_false_203_2_7082_5_5 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_2_7087
    (body : List TagLetter) (z : Nat)
    (z_lower : 4 ≤ z) (z_upper : z ≤ 4)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 2 203 7087 z)
      (firstBOneOuterJ 203 7087 z)
      (firstBOneOuterCorrection 203 7087 z)) : False := by
  exact firstBZeroSuffix_false_203_2_7087_4_4 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_2_7095
    (body : List TagLetter) (z : Nat)
    (z_lower : 3 ≤ z) (z_upper : z ≤ 3)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 2 203 7095 z)
      (firstBOneOuterJ 203 7095 z)
      (firstBOneOuterCorrection 203 7095 z)) : False := by
  exact firstBZeroSuffix_false_203_2_7095_3_3 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_2_7158
    (body : List TagLetter) (z : Nat)
    (z_lower : 1 ≤ z) (z_upper : z ≤ 1)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 2 203 7158 z)
      (firstBOneOuterJ 203 7158 z)
      (firstBOneOuterCorrection 203 7158 z)) : False := by
  exact firstBZeroSuffix_false_203_2_7158_1_1 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_1_7295
    (body : List TagLetter) (z : Nat)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 1 203 7295 z)
      (firstBOneOuterJ 203 7295 z)
      (firstBOneOuterCorrection 203 7295 z)) : False := by
  by_cases z_small : z < 573
  · have z_upper : z ≤ 572 := by omega
    have interval : (0 ≤ z ∧ z ≤ 308) ∨ (309 ≤ z ∧ z ≤ 309) ∨ (310 ≤ z ∧ z ≤ 313) ∨ (314 ≤ z ∧ z ≤
      324) ∨ (325 ≤ z ∧ z ≤ 363) ∨ (364 ≤ z ∧ z ≤ 364) ∨ (365 ≤ z ∧ z ≤ 570) ∨ (571 ≤ z ∧ z ≤ 572)
      := by omega
    rcases interval with range0 | range1 | range2 | range3 | range4 | range5 | range6 | range7
    · exact firstBZeroSuffix_false_203_1_7295_0_308 body z range0.1 range0.2 core
    · exact firstBZeroSuffix_false_203_1_7295_309_309 body z range1.1 range1.2 core
    · exact firstBZeroSuffix_false_203_1_7295_310_313 body z range2.1 range2.2 core
    · exact firstBZeroSuffix_false_203_1_7295_314_324 body z range3.1 range3.2 core
    · exact firstBZeroSuffix_false_203_1_7295_325_363 body z range4.1 range4.2 core
    · exact firstBZeroSuffix_false_203_1_7295_364_364 body z range5.1 range5.2 core
    · exact firstBZeroSuffix_false_203_1_7295_365_570 body z range6.1 range6.2 core
    · exact firstBZeroSuffix_false_203_1_7295_571_572 body z range7.1 range7.2 core
  · have z_lower : 573 ≤ z := by omega
    exact firstBZeroSuffix_false_203_1_7295_ray_573 body z z_lower core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_1_7296
    (body : List TagLetter) (z : Nat)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 1 203 7296 z)
      (firstBOneOuterJ 203 7296 z)
      (firstBOneOuterCorrection 203 7296 z)) : False := by
  by_cases z_small : z < 129
  · have z_upper : z ≤ 128 := by omega
    have interval : (0 ≤ z ∧ z ≤ 81) ∨ (82 ≤ z ∧ z ≤ 82) ∨ (83 ≤ z ∧ z ≤ 84) ∨ (85 ≤ z ∧ z ≤ 92) ∨
      (93 ≤ z ∧ z ≤ 128) := by omega
    rcases interval with range0 | range1 | range2 | range3 | range4
    · exact firstBZeroSuffix_false_203_1_7296_0_81 body z range0.1 range0.2 core
    · exact firstBZeroSuffix_false_203_1_7296_82_82 body z range1.1 range1.2 core
    · exact firstBZeroSuffix_false_203_1_7296_83_84 body z range2.1 range2.2 core
    · exact firstBZeroSuffix_false_203_1_7296_85_92 body z range3.1 range3.2 core
    · exact firstBZeroSuffix_false_203_1_7296_93_128 body z range4.1 range4.2 core
  · have z_lower : 129 ≤ z := by omega
    exact firstBZeroSuffix_false_203_1_7296_ray_129 body z z_lower core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_1_7297
    (body : List TagLetter) (z : Nat)
    (z_lower : 47 ≤ z) (z_upper : z ≤ 158)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 1 203 7297 z)
      (firstBOneOuterJ 203 7297 z)
      (firstBOneOuterCorrection 203 7297 z)) : False := by
  have interval : (47 ≤ z ∧ z ≤ 47) ∨ (48 ≤ z ∧ z ≤ 48) ∨ (49 ≤ z ∧ z ≤ 50) ∨ (51 ≤ z ∧ z ≤ 59) ∨
    (60 ≤ z ∧ z ≤ 127) ∨ (128 ≤ z ∧ z ≤ 128) ∨ (129 ≤ z ∧ z ≤ 158) := by omega
  rcases interval with range0 | range1 | range2 | range3 | range4 | range5 | range6
  · exact firstBZeroSuffix_false_203_1_7297_47_47 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_1_7297_48_48 body z range1.1 range1.2 core
  · exact firstBZeroSuffix_false_203_1_7297_49_50 body z range2.1 range2.2 core
  · exact firstBZeroSuffix_false_203_1_7297_51_59 body z range3.1 range3.2 core
  · exact firstBZeroSuffix_false_203_1_7297_60_127 body z range4.1 range4.2 core
  · exact firstBZeroSuffix_false_203_1_7297_128_128 body z range5.1 range5.2 core
  · exact firstBZeroSuffix_false_203_1_7297_129_158 body z range6.1 range6.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_1_7298
    (body : List TagLetter) (z : Nat)
    (z_lower : 33 ≤ z) (z_upper : z ≤ 65)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 1 203 7298 z)
      (firstBOneOuterJ 203 7298 z)
      (firstBOneOuterCorrection 203 7298 z)) : False := by
  have interval : (33 ≤ z ∧ z ≤ 33) ∨ (34 ≤ z ∧ z ≤ 34) ∨ (35 ≤ z ∧ z ≤ 38) ∨ (39 ≤ z ∧ z ≤ 59) ∨
    (60 ≤ z ∧ z ≤ 65) := by omega
  rcases interval with range0 | range1 | range2 | range3 | range4
  · exact firstBZeroSuffix_false_203_1_7298_33_33 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_1_7298_34_34 body z range1.1 range1.2 core
  · exact firstBZeroSuffix_false_203_1_7298_35_38 body z range2.1 range2.2 core
  · exact firstBZeroSuffix_false_203_1_7298_39_59 body z range3.1 range3.2 core
  · exact firstBZeroSuffix_false_203_1_7298_60_65 body z range4.1 range4.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_1_7299
    (body : List TagLetter) (z : Nat)
    (z_lower : 26 ≤ z) (z_upper : z ≤ 41)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 1 203 7299 z)
      (firstBOneOuterJ 203 7299 z)
      (firstBOneOuterCorrection 203 7299 z)) : False := by
  have interval : (26 ≤ z ∧ z ≤ 26) ∨ (27 ≤ z ∧ z ≤ 28) ∨ (29 ≤ z ∧ z ≤ 38) ∨ (39 ≤ z ∧ z ≤ 41) :=
    by omega
  rcases interval with range0 | range1 | range2 | range3
  · exact firstBZeroSuffix_false_203_1_7299_26_26 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_1_7299_27_28 body z range1.1 range1.2 core
  · exact firstBZeroSuffix_false_203_1_7299_29_38 body z range2.1 range2.2 core
  · exact firstBZeroSuffix_false_203_1_7299_39_41 body z range3.1 range3.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_1_7300
    (body : List TagLetter) (z : Nat)
    (z_lower : 21 ≤ z) (z_upper : z ≤ 29)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 1 203 7300 z)
      (firstBOneOuterJ 203 7300 z)
      (firstBOneOuterCorrection 203 7300 z)) : False := by
  have interval : (21 ≤ z ∧ z ≤ 21) ∨ (22 ≤ z ∧ z ≤ 22) ∨ (23 ≤ z ∧ z ≤ 28) ∨ (29 ≤ z ∧ z ≤ 29) :=
    by omega
  rcases interval with range0 | range1 | range2 | range3
  · exact firstBZeroSuffix_false_203_1_7300_21_21 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_1_7300_22_22 body z range1.1 range1.2 core
  · exact firstBZeroSuffix_false_203_1_7300_23_28 body z range2.1 range2.2 core
  · exact firstBZeroSuffix_false_203_1_7300_29_29 body z range3.1 range3.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_1_7301
    (body : List TagLetter) (z : Nat)
    (z_lower : 18 ≤ z) (z_upper : z ≤ 23)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 1 203 7301 z)
      (firstBOneOuterJ 203 7301 z)
      (firstBOneOuterCorrection 203 7301 z)) : False := by
  have interval : (18 ≤ z ∧ z ≤ 18) ∨ (19 ≤ z ∧ z ≤ 22) ∨ (23 ≤ z ∧ z ≤ 23) := by omega
  rcases interval with range0 | range1 | range2
  · exact firstBZeroSuffix_false_203_1_7301_18_18 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_1_7301_19_22 body z range1.1 range1.2 core
  · exact firstBZeroSuffix_false_203_1_7301_23_23 body z range2.1 range2.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_1_7302
    (body : List TagLetter) (z : Nat)
    (z_lower : 15 ≤ z) (z_upper : z ≤ 19)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 1 203 7302 z)
      (firstBOneOuterJ 203 7302 z)
      (firstBOneOuterCorrection 203 7302 z)) : False := by
  have interval : (15 ≤ z ∧ z ≤ 15) ∨ (16 ≤ z ∧ z ≤ 16) ∨ (17 ≤ z ∧ z ≤ 18) ∨ (19 ≤ z ∧ z ≤ 19) :=
    by omega
  rcases interval with range0 | range1 | range2 | range3
  · exact firstBZeroSuffix_false_203_1_7302_15_15 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_1_7302_16_16 body z range1.1 range1.2 core
  · exact firstBZeroSuffix_false_203_1_7302_17_18 body z range2.1 range2.2 core
  · exact firstBZeroSuffix_false_203_1_7302_19_19 body z range3.1 range3.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_1_7303
    (body : List TagLetter) (z : Nat)
    (z_lower : 14 ≤ z) (z_upper : z ≤ 16)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 1 203 7303 z)
      (firstBOneOuterJ 203 7303 z)
      (firstBOneOuterCorrection 203 7303 z)) : False := by
  have interval : (14 ≤ z ∧ z ≤ 14) ∨ (15 ≤ z ∧ z ≤ 16) := by omega
  rcases interval with range0 | range1
  · exact firstBZeroSuffix_false_203_1_7303_14_14 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_1_7303_15_16 body z range1.1 range1.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_1_7304
    (body : List TagLetter) (z : Nat)
    (z_lower : 12 ≤ z) (z_upper : z ≤ 14)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 1 203 7304 z)
      (firstBOneOuterJ 203 7304 z)
      (firstBOneOuterCorrection 203 7304 z)) : False := by
  have interval : (12 ≤ z ∧ z ≤ 12) ∨ (13 ≤ z ∧ z ≤ 14) := by omega
  rcases interval with range0 | range1
  · exact firstBZeroSuffix_false_203_1_7304_12_12 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_1_7304_13_14 body z range1.1 range1.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_1_7305
    (body : List TagLetter) (z : Nat)
    (z_lower : 11 ≤ z) (z_upper : z ≤ 12)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 1 203 7305 z)
      (firstBOneOuterJ 203 7305 z)
      (firstBOneOuterCorrection 203 7305 z)) : False := by
  have interval : (11 ≤ z ∧ z ≤ 11) ∨ (12 ≤ z ∧ z ≤ 12) := by omega
  rcases interval with range0 | range1
  · exact firstBZeroSuffix_false_203_1_7305_11_11 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_1_7305_12_12 body z range1.1 range1.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_1_7306
    (body : List TagLetter) (z : Nat)
    (z_lower : 10 ≤ z) (z_upper : z ≤ 11)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 1 203 7306 z)
      (firstBOneOuterJ 203 7306 z)
      (firstBOneOuterCorrection 203 7306 z)) : False := by
  have interval : (10 ≤ z ∧ z ≤ 10) ∨ (11 ≤ z ∧ z ≤ 11) := by omega
  rcases interval with range0 | range1
  · exact firstBZeroSuffix_false_203_1_7306_10_10 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_1_7306_11_11 body z range1.1 range1.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_1_7307
    (body : List TagLetter) (z : Nat)
    (z_lower : 9 ≤ z) (z_upper : z ≤ 10)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 1 203 7307 z)
      (firstBOneOuterJ 203 7307 z)
      (firstBOneOuterCorrection 203 7307 z)) : False := by
  have interval : (9 ≤ z ∧ z ≤ 9) ∨ (10 ≤ z ∧ z ≤ 10) := by omega
  rcases interval with range0 | range1
  · exact firstBZeroSuffix_false_203_1_7307_9_9 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_1_7307_10_10 body z range1.1 range1.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_1_7308
    (body : List TagLetter) (z : Nat)
    (z_lower : 9 ≤ z) (z_upper : z ≤ 9)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 1 203 7308 z)
      (firstBOneOuterJ 203 7308 z)
      (firstBOneOuterCorrection 203 7308 z)) : False := by
  exact firstBZeroSuffix_false_203_1_7308_9_9 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_1_7309
    (body : List TagLetter) (z : Nat)
    (z_lower : 8 ≤ z) (z_upper : z ≤ 8)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 1 203 7309 z)
      (firstBOneOuterJ 203 7309 z)
      (firstBOneOuterCorrection 203 7309 z)) : False := by
  exact firstBZeroSuffix_false_203_1_7309_8_8 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_1_7310
    (body : List TagLetter) (z : Nat)
    (z_lower : 8 ≤ z) (z_upper : z ≤ 8)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 1 203 7310 z)
      (firstBOneOuterJ 203 7310 z)
      (firstBOneOuterCorrection 203 7310 z)) : False := by
  exact firstBZeroSuffix_false_203_1_7310_8_8 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_1_7311
    (body : List TagLetter) (z : Nat)
    (z_lower : 7 ≤ z) (z_upper : z ≤ 7)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 1 203 7311 z)
      (firstBOneOuterJ 203 7311 z)
      (firstBOneOuterCorrection 203 7311 z)) : False := by
  exact firstBZeroSuffix_false_203_1_7311_7_7 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_1_7313
    (body : List TagLetter) (z : Nat)
    (z_lower : 6 ≤ z) (z_upper : z ≤ 6)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 1 203 7313 z)
      (firstBOneOuterJ 203 7313 z)
      (firstBOneOuterCorrection 203 7313 z)) : False := by
  exact firstBZeroSuffix_false_203_1_7313_6_6 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_1_7314
    (body : List TagLetter) (z : Nat)
    (z_lower : 6 ≤ z) (z_upper : z ≤ 6)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 1 203 7314 z)
      (firstBOneOuterJ 203 7314 z)
      (firstBOneOuterCorrection 203 7314 z)) : False := by
  exact firstBZeroSuffix_false_203_1_7314_6_6 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_1_7317
    (body : List TagLetter) (z : Nat)
    (z_lower : 5 ≤ z) (z_upper : z ≤ 5)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 1 203 7317 z)
      (firstBOneOuterJ 203 7317 z)
      (firstBOneOuterCorrection 203 7317 z)) : False := by
  exact firstBZeroSuffix_false_203_1_7317_5_5 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_1_7318
    (body : List TagLetter) (z : Nat)
    (z_lower : 5 ≤ z) (z_upper : z ≤ 5)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 1 203 7318 z)
      (firstBOneOuterJ 203 7318 z)
      (firstBOneOuterCorrection 203 7318 z)) : False := by
  exact firstBZeroSuffix_false_203_1_7318_5_5 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_1_7322
    (body : List TagLetter) (z : Nat)
    (z_lower : 4 ≤ z) (z_upper : z ≤ 4)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 1 203 7322 z)
      (firstBOneOuterJ 203 7322 z)
      (firstBOneOuterCorrection 203 7322 z)) : False := by
  exact firstBZeroSuffix_false_203_1_7322_4_4 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_1_7323
    (body : List TagLetter) (z : Nat)
    (z_lower : 4 ≤ z) (z_upper : z ≤ 4)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 1 203 7323 z)
      (firstBOneOuterJ 203 7323 z)
      (firstBOneOuterCorrection 203 7323 z)) : False := by
  exact firstBZeroSuffix_false_203_1_7323_4_4 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_1_7331
    (body : List TagLetter) (z : Nat)
    (z_lower : 3 ≤ z) (z_upper : z ≤ 3)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 1 203 7331 z)
      (firstBOneOuterJ 203 7331 z)
      (firstBOneOuterCorrection 203 7331 z)) : False := by
  exact firstBZeroSuffix_false_203_1_7331_3_3 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_1_7332
    (body : List TagLetter) (z : Nat)
    (z_lower : 3 ≤ z) (z_upper : z ≤ 3)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 1 203 7332 z)
      (firstBOneOuterJ 203 7332 z)
      (firstBOneOuterCorrection 203 7332 z)) : False := by
  exact firstBZeroSuffix_false_203_1_7332_3_3 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_1_7349
    (body : List TagLetter) (z : Nat)
    (z_lower : 2 ≤ z) (z_upper : z ≤ 2)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 1 203 7349 z)
      (firstBOneOuterJ 203 7349 z)
      (firstBOneOuterCorrection 203 7349 z)) : False := by
  exact firstBZeroSuffix_false_203_1_7349_2_2 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_1_7398
    (body : List TagLetter) (z : Nat)
    (z_lower : 1 ≤ z) (z_upper : z ≤ 1)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 1 203 7398 z)
      (firstBOneOuterJ 203 7398 z)
      (firstBOneOuterCorrection 203 7398 z)) : False := by
  exact firstBZeroSuffix_false_203_1_7398_1_1 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_1_7399
    (body : List TagLetter) (z : Nat)
    (z_lower : 1 ≤ z) (z_upper : z ≤ 1)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 1 203 7399 z)
      (firstBOneOuterJ 203 7399 z)
      (firstBOneOuterCorrection 203 7399 z)) : False := by
  exact firstBZeroSuffix_false_203_1_7399_1_1 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8095
    (body : List TagLetter) (z : Nat)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8095 z)
      (firstBOneOuterJ 203 8095 z)
      (firstBOneOuterCorrection 203 8095 z)) : False := by
  by_cases z_small : z < 3009
  · have z_upper : z ≤ 3008 := by omega
    have interval : (0 ≤ z ∧ z ≤ 547) ∨ (548 ≤ z ∧ z ≤ 548) ∨ (549 ≤ z ∧ z ≤ 549) ∨ (550 ≤ z ∧ z ≤
      553) ∨ (554 ≤ z ∧ z ≤ 564) ∨ (565 ≤ z ∧ z ≤ 565) ∨ (566 ≤ z ∧ z ≤ 602) ∨ (603 ≤ z ∧ z ≤ 752) ∨
      (753 ≤ z ∧ z ≤ 753) ∨ (754 ≤ z ∧ z ≤ 2954) ∨ (2955 ≤ z ∧ z ≤ 2956) ∨ (2957 ≤ z ∧ z ≤ 2960) ∨
      (2961 ≤ z ∧ z ≤ 2972) ∨ (2973 ≤ z ∧ z ≤ 3007) ∨ (3008 ≤ z ∧ z ≤ 3008) := by omega
    rcases interval with range0 | range1 | range2 | range3 | range4 | range5 | range6 | range7 |
      range8 | range9 | range10 | range11 | range12 | range13 | range14
    · exact firstBZeroSuffix_false_203_0_8095_0_547 body z range0.1 range0.2 core
    · exact firstBZeroSuffix_false_203_0_8095_548_548 body z range1.1 range1.2 core
    · exact firstBZeroSuffix_false_203_0_8095_549_549 body z range2.1 range2.2 core
    · exact firstBZeroSuffix_false_203_0_8095_550_553 body z range3.1 range3.2 core
    · exact firstBZeroSuffix_false_203_0_8095_554_564 body z range4.1 range4.2 core
    · exact firstBZeroSuffix_false_203_0_8095_565_565 body z range5.1 range5.2 core
    · exact firstBZeroSuffix_false_203_0_8095_566_602 body z range6.1 range6.2 core
    · exact firstBZeroSuffix_false_203_0_8095_603_752 body z range7.1 range7.2 core
    · exact firstBZeroSuffix_false_203_0_8095_753_753 body z range8.1 range8.2 core
    · exact firstBZeroSuffix_false_203_0_8095_754_2954 body z range9.1 range9.2 core
    · exact firstBZeroSuffix_false_203_0_8095_2955_2956 body z range10.1 range10.2 core
    · exact firstBZeroSuffix_false_203_0_8095_2957_2960 body z range11.1 range11.2 core
    · exact firstBZeroSuffix_false_203_0_8095_2961_2972 body z range12.1 range12.2 core
    · exact firstBZeroSuffix_false_203_0_8095_2973_3007 body z range13.1 range13.2 core
    · exact firstBZeroSuffix_false_203_0_8095_3008_3008 body z range14.1 range14.2 core
  · have z_lower : 3009 ≤ z := by omega
    exact firstBZeroSuffix_false_203_0_8095_ray_3009 body z z_lower core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8096
    (body : List TagLetter) (z : Nat)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8096 z)
      (firstBOneOuterJ 203 8096 z)
      (firstBOneOuterCorrection 203 8096 z)) : False := by
  by_cases z_small : z < 214
  · have z_upper : z ≤ 213 := by omega
    have interval : (0 ≤ z ∧ z ≤ 109) ∨ (110 ≤ z ∧ z ≤ 111) ∨ (112 ≤ z ∧ z ≤ 115) ∨ (116 ≤ z ∧ z ≤
      130) ∨ (131 ≤ z ∧ z ≤ 212) ∨ (213 ≤ z ∧ z ≤ 213) := by omega
    rcases interval with range0 | range1 | range2 | range3 | range4 | range5
    · exact firstBZeroSuffix_false_203_0_8096_0_109 body z range0.1 range0.2 core
    · exact firstBZeroSuffix_false_203_0_8096_110_111 body z range1.1 range1.2 core
    · exact firstBZeroSuffix_false_203_0_8096_112_115 body z range2.1 range2.2 core
    · exact firstBZeroSuffix_false_203_0_8096_116_130 body z range3.1 range3.2 core
    · exact firstBZeroSuffix_false_203_0_8096_131_212 body z range4.1 range4.2 core
    · exact firstBZeroSuffix_false_203_0_8096_213_213 body z range5.1 range5.2 core
  · have z_lower : 214 ≤ z := by omega
    exact firstBZeroSuffix_false_203_0_8096_ray_214 body z z_lower core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8097
    (body : List TagLetter) (z : Nat)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8097 z)
      (firstBOneOuterJ 203 8097 z)
      (firstBOneOuterCorrection 203 8097 z)) : False := by
  by_cases z_small : z < 326
  · have z_upper : z ≤ 325 := by omega
    have interval : (0 ≤ z ∧ z ≤ 60) ∨ (61 ≤ z ∧ z ≤ 61) ∨ (62 ≤ z ∧ z ≤ 62) ∨ (63 ≤ z ∧ z ≤ 66) ∨
      (67 ≤ z ∧ z ≤ 82) ∨ (83 ≤ z ∧ z ≤ 83) ∨ (84 ≤ z ∧ z ≤ 319) ∨ (320 ≤ z ∧ z ≤ 320) ∨ (321 ≤ z ∧
      z ≤ 321) ∨ (322 ≤ z ∧ z ≤ 325) := by omega
    rcases interval with range0 | range1 | range2 | range3 | range4 | range5 | range6 | range7 |
      range8 | range9
    · exact firstBZeroSuffix_false_203_0_8097_0_60 body z range0.1 range0.2 core
    · exact firstBZeroSuffix_false_203_0_8097_61_61 body z range1.1 range1.2 core
    · exact firstBZeroSuffix_false_203_0_8097_62_62 body z range2.1 range2.2 core
    · exact firstBZeroSuffix_false_203_0_8097_63_66 body z range3.1 range3.2 core
    · exact firstBZeroSuffix_false_203_0_8097_67_82 body z range4.1 range4.2 core
    · exact firstBZeroSuffix_false_203_0_8097_83_83 body z range5.1 range5.2 core
    · exact firstBZeroSuffix_false_203_0_8097_84_319 body z range6.1 range6.2 core
    · exact firstBZeroSuffix_false_203_0_8097_320_320 body z range7.1 range7.2 core
    · exact firstBZeroSuffix_false_203_0_8097_321_321 body z range8.1 range8.2 core
    · exact firstBZeroSuffix_false_203_0_8097_322_325 body z range9.1 range9.2 core
  · have z_lower : 326 ≤ z := by omega
    exact firstBZeroSuffix_false_203_0_8097_ray_326 body z z_lower core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8098
    (body : List TagLetter) (z : Nat)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8098 z)
      (firstBOneOuterJ 203 8098 z)
      (firstBOneOuterCorrection 203 8098 z)) : False := by
  by_cases z_small : z < 96
  · have z_upper : z ≤ 95 := by omega
    have interval : (0 ≤ z ∧ z ≤ 41) ∨ (42 ≤ z ∧ z ≤ 42) ∨ (43 ≤ z ∧ z ≤ 44) ∨ (45 ≤ z ∧ z ≤ 51) ∨
      (52 ≤ z ∧ z ≤ 95) := by omega
    rcases interval with range0 | range1 | range2 | range3 | range4
    · exact firstBZeroSuffix_false_203_0_8098_0_41 body z range0.1 range0.2 core
    · exact firstBZeroSuffix_false_203_0_8098_42_42 body z range1.1 range1.2 core
    · exact firstBZeroSuffix_false_203_0_8098_43_44 body z range2.1 range2.2 core
    · exact firstBZeroSuffix_false_203_0_8098_45_51 body z range3.1 range3.2 core
    · exact firstBZeroSuffix_false_203_0_8098_52_95 body z range4.1 range4.2 core
  · have z_lower : 96 ≤ z := by omega
    exact firstBZeroSuffix_false_203_0_8098_ray_96 body z z_lower core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8099
    (body : List TagLetter) (z : Nat)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8099 z)
      (firstBOneOuterJ 203 8099 z)
      (firstBOneOuterCorrection 203 8099 z)) : False := by
  by_cases z_small : z < 57
  · have z_upper : z ≤ 56 := by omega
    have interval : (0 ≤ z ∧ z ≤ 31) ∨ (32 ≤ z ∧ z ≤ 32) ∨ (33 ≤ z ∧ z ≤ 33) ∨ (34 ≤ z ∧ z ≤ 37) ∨
      (38 ≤ z ∧ z ≤ 56) := by omega
    rcases interval with range0 | range1 | range2 | range3 | range4
    · exact firstBZeroSuffix_false_203_0_8099_0_31 body z range0.1 range0.2 core
    · exact firstBZeroSuffix_false_203_0_8099_32_32 body z range1.1 range1.2 core
    · exact firstBZeroSuffix_false_203_0_8099_33_33 body z range2.1 range2.2 core
    · exact firstBZeroSuffix_false_203_0_8099_34_37 body z range3.1 range3.2 core
    · exact firstBZeroSuffix_false_203_0_8099_38_56 body z range4.1 range4.2 core
  · have z_lower : 57 ≤ z := by omega
    exact firstBZeroSuffix_false_203_0_8099_ray_57 body z z_lower core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8100
    (body : List TagLetter) (z : Nat)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8100 z)
      (firstBOneOuterJ 203 8100 z)
      (firstBOneOuterCorrection 203 8100 z)) : False := by
  by_cases z_small : z < 40
  · have z_upper : z ≤ 39 := by omega
    have interval : (0 ≤ z ∧ z ≤ 25) ∨ (26 ≤ z ∧ z ≤ 26) ∨ (27 ≤ z ∧ z ≤ 29) ∨ (30 ≤ z ∧ z ≤ 39) :=
      by omega
    rcases interval with range0 | range1 | range2 | range3
    · exact firstBZeroSuffix_false_203_0_8100_0_25 body z range0.1 range0.2 core
    · exact firstBZeroSuffix_false_203_0_8100_26_26 body z range1.1 range1.2 core
    · exact firstBZeroSuffix_false_203_0_8100_27_29 body z range2.1 range2.2 core
    · exact firstBZeroSuffix_false_203_0_8100_30_39 body z range3.1 range3.2 core
  · have z_lower : 40 ≤ z := by omega
    exact firstBZeroSuffix_false_203_0_8100_ray_40 body z z_lower core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8101
    (body : List TagLetter) (z : Nat)
    (z_lower : 22 ≤ z) (z_upper : z ≤ 934)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8101 z)
      (firstBOneOuterJ 203 8101 z)
      (firstBOneOuterCorrection 203 8101 z)) : False := by
  have interval : (22 ≤ z ∧ z ≤ 22) ∨ (23 ≤ z ∧ z ≤ 24) ∨ (25 ≤ z ∧ z ≤ 30) ∨ (31 ≤ z ∧ z ≤ 174) ∨
    (175 ≤ z ∧ z ≤ 175) ∨ (176 ≤ z ∧ z ≤ 176) ∨ (177 ≤ z ∧ z ≤ 180) ∨ (181 ≤ z ∧ z ≤ 934) := by
    omega
  rcases interval with range0 | range1 | range2 | range3 | range4 | range5 | range6 | range7
  · exact firstBZeroSuffix_false_203_0_8101_22_22 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_0_8101_23_24 body z range1.1 range1.2 core
  · exact firstBZeroSuffix_false_203_0_8101_25_30 body z range2.1 range2.2 core
  · exact firstBZeroSuffix_false_203_0_8101_31_174 body z range3.1 range3.2 core
  · exact firstBZeroSuffix_false_203_0_8101_175_175 body z range4.1 range4.2 core
  · exact firstBZeroSuffix_false_203_0_8101_176_176 body z range5.1 range5.2 core
  · exact firstBZeroSuffix_false_203_0_8101_177_180 body z range6.1 range6.2 core
  · exact firstBZeroSuffix_false_203_0_8101_181_934 body z range7.1 range7.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8102
    (body : List TagLetter) (z : Nat)
    (z_lower : 19 ≤ z) (z_upper : z ≤ 118)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8102 z)
      (firstBOneOuterJ 203 8102 z)
      (firstBOneOuterCorrection 203 8102 z)) : False := by
  have interval : (19 ≤ z ∧ z ≤ 19) ∨ (20 ≤ z ∧ z ≤ 20) ∨ (21 ≤ z ∧ z ≤ 25) ∨ (26 ≤ z ∧ z ≤ 76) ∨
    (77 ≤ z ∧ z ≤ 77) ∨ (78 ≤ z ∧ z ≤ 118) := by omega
  rcases interval with range0 | range1 | range2 | range3 | range4 | range5
  · exact firstBZeroSuffix_false_203_0_8102_19_19 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_0_8102_20_20 body z range1.1 range1.2 core
  · exact firstBZeroSuffix_false_203_0_8102_21_25 body z range2.1 range2.2 core
  · exact firstBZeroSuffix_false_203_0_8102_26_76 body z range3.1 range3.2 core
  · exact firstBZeroSuffix_false_203_0_8102_77_77 body z range4.1 range4.2 core
  · exact firstBZeroSuffix_false_203_0_8102_78_118 body z range5.1 range5.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8103
    (body : List TagLetter) (z : Nat)
    (z_lower : 17 ≤ z) (z_upper : z ≤ 63)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8103 z)
      (firstBOneOuterJ 203 8103 z)
      (firstBOneOuterCorrection 203 8103 z)) : False := by
  have interval : (17 ≤ z ∧ z ≤ 17) ∨ (18 ≤ z ∧ z ≤ 21) ∨ (22 ≤ z ∧ z ≤ 48) ∨ (49 ≤ z ∧ z ≤ 49) ∨
    (50 ≤ z ∧ z ≤ 63) := by omega
  rcases interval with range0 | range1 | range2 | range3 | range4
  · exact firstBZeroSuffix_false_203_0_8103_17_17 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_0_8103_18_21 body z range1.1 range1.2 core
  · exact firstBZeroSuffix_false_203_0_8103_22_48 body z range2.1 range2.2 core
  · exact firstBZeroSuffix_false_203_0_8103_49_49 body z range3.1 range3.2 core
  · exact firstBZeroSuffix_false_203_0_8103_50_63 body z range4.1 range4.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8104
    (body : List TagLetter) (z : Nat)
    (z_lower : 15 ≤ z) (z_upper : z ≤ 43)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8104 z)
      (firstBOneOuterJ 203 8104 z)
      (firstBOneOuterCorrection 203 8104 z)) : False := by
  have interval : (15 ≤ z ∧ z ≤ 15) ∨ (16 ≤ z ∧ z ≤ 18) ∨ (19 ≤ z ∧ z ≤ 36) ∨ (37 ≤ z ∧ z ≤ 43) :=
    by omega
  rcases interval with range0 | range1 | range2 | range3
  · exact firstBZeroSuffix_false_203_0_8104_15_15 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_0_8104_16_18 body z range1.1 range1.2 core
  · exact firstBZeroSuffix_false_203_0_8104_19_36 body z range2.1 range2.2 core
  · exact firstBZeroSuffix_false_203_0_8104_37_43 body z range3.1 range3.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8105
    (body : List TagLetter) (z : Nat)
    (z_lower : 14 ≤ z) (z_upper : z ≤ 32)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8105 z)
      (firstBOneOuterJ 203 8105 z)
      (firstBOneOuterCorrection 203 8105 z)) : False := by
  have interval : (14 ≤ z ∧ z ≤ 14) ∨ (15 ≤ z ∧ z ≤ 16) ∨ (17 ≤ z ∧ z ≤ 28) ∨ (29 ≤ z ∧ z ≤ 32) :=
    by omega
  rcases interval with range0 | range1 | range2 | range3
  · exact firstBZeroSuffix_false_203_0_8105_14_14 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_0_8105_15_16 body z range1.1 range1.2 core
  · exact firstBZeroSuffix_false_203_0_8105_17_28 body z range2.1 range2.2 core
  · exact firstBZeroSuffix_false_203_0_8105_29_32 body z range3.1 range3.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8106
    (body : List TagLetter) (z : Nat)
    (z_lower : 13 ≤ z) (z_upper : z ≤ 26)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8106 z)
      (firstBOneOuterJ 203 8106 z)
      (firstBOneOuterCorrection 203 8106 z)) : False := by
  have interval : (13 ≤ z ∧ z ≤ 14) ∨ (15 ≤ z ∧ z ≤ 23) ∨ (24 ≤ z ∧ z ≤ 26) := by omega
  rcases interval with range0 | range1 | range2
  · exact firstBZeroSuffix_false_203_0_8106_13_14 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_0_8106_15_23 body z range1.1 range1.2 core
  · exact firstBZeroSuffix_false_203_0_8106_24_26 body z range2.1 range2.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8107
    (body : List TagLetter) (z : Nat)
    (z_lower : 12 ≤ z) (z_upper : z ≤ 22)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8107 z)
      (firstBOneOuterJ 203 8107 z)
      (firstBOneOuterCorrection 203 8107 z)) : False := by
  have interval : (12 ≤ z ∧ z ≤ 12) ∨ (13 ≤ z ∧ z ≤ 13) ∨ (14 ≤ z ∧ z ≤ 20) ∨ (21 ≤ z ∧ z ≤ 22) :=
    by omega
  rcases interval with range0 | range1 | range2 | range3
  · exact firstBZeroSuffix_false_203_0_8107_12_12 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_0_8107_13_13 body z range1.1 range1.2 core
  · exact firstBZeroSuffix_false_203_0_8107_14_20 body z range2.1 range2.2 core
  · exact firstBZeroSuffix_false_203_0_8107_21_22 body z range3.1 range3.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8108
    (body : List TagLetter) (z : Nat)
    (z_lower : 11 ≤ z) (z_upper : z ≤ 19)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8108 z)
      (firstBOneOuterJ 203 8108 z)
      (firstBOneOuterCorrection 203 8108 z)) : False := by
  have interval : (11 ≤ z ∧ z ≤ 11) ∨ (12 ≤ z ∧ z ≤ 17) ∨ (18 ≤ z ∧ z ≤ 19) := by omega
  rcases interval with range0 | range1 | range2
  · exact firstBZeroSuffix_false_203_0_8108_11_11 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_0_8108_12_17 body z range1.1 range1.2 core
  · exact firstBZeroSuffix_false_203_0_8108_18_19 body z range2.1 range2.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8109
    (body : List TagLetter) (z : Nat)
    (z_lower : 10 ≤ z) (z_upper : z ≤ 16)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8109 z)
      (firstBOneOuterJ 203 8109 z)
      (firstBOneOuterCorrection 203 8109 z)) : False := by
  have interval : (10 ≤ z ∧ z ≤ 10) ∨ (11 ≤ z ∧ z ≤ 15) ∨ (16 ≤ z ∧ z ≤ 16) := by omega
  rcases interval with range0 | range1 | range2
  · exact firstBZeroSuffix_false_203_0_8109_10_10 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_0_8109_11_15 body z range1.1 range1.2 core
  · exact firstBZeroSuffix_false_203_0_8109_16_16 body z range2.1 range2.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8110
    (body : List TagLetter) (z : Nat)
    (z_lower : 9 ≤ z) (z_upper : z ≤ 14)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8110 z)
      (firstBOneOuterJ 203 8110 z)
      (firstBOneOuterCorrection 203 8110 z)) : False := by
  have interval : (9 ≤ z ∧ z ≤ 9) ∨ (10 ≤ z ∧ z ≤ 10) ∨ (11 ≤ z ∧ z ≤ 13) ∨ (14 ≤ z ∧ z ≤ 14) := by
    omega
  rcases interval with range0 | range1 | range2 | range3
  · exact firstBZeroSuffix_false_203_0_8110_9_9 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_0_8110_10_10 body z range1.1 range1.2 core
  · exact firstBZeroSuffix_false_203_0_8110_11_13 body z range2.1 range2.2 core
  · exact firstBZeroSuffix_false_203_0_8110_14_14 body z range3.1 range3.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8111
    (body : List TagLetter) (z : Nat)
    (z_lower : 9 ≤ z) (z_upper : z ≤ 13)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8111 z)
      (firstBOneOuterJ 203 8111 z)
      (firstBOneOuterCorrection 203 8111 z)) : False := by
  have interval : (9 ≤ z ∧ z ≤ 9) ∨ (10 ≤ z ∧ z ≤ 12) ∨ (13 ≤ z ∧ z ≤ 13) := by omega
  rcases interval with range0 | range1 | range2
  · exact firstBZeroSuffix_false_203_0_8111_9_9 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_0_8111_10_12 body z range1.1 range1.2 core
  · exact firstBZeroSuffix_false_203_0_8111_13_13 body z range2.1 range2.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8112
    (body : List TagLetter) (z : Nat)
    (z_lower : 8 ≤ z) (z_upper : z ≤ 12)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8112 z)
      (firstBOneOuterJ 203 8112 z)
      (firstBOneOuterCorrection 203 8112 z)) : False := by
  have interval : (8 ≤ z ∧ z ≤ 8) ∨ (9 ≤ z ∧ z ≤ 11) ∨ (12 ≤ z ∧ z ≤ 12) := by omega
  rcases interval with range0 | range1 | range2
  · exact firstBZeroSuffix_false_203_0_8112_8_8 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_0_8112_9_11 body z range1.1 range1.2 core
  · exact firstBZeroSuffix_false_203_0_8112_12_12 body z range2.1 range2.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8113
    (body : List TagLetter) (z : Nat)
    (z_lower : 8 ≤ z) (z_upper : z ≤ 11)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8113 z)
      (firstBOneOuterJ 203 8113 z)
      (firstBOneOuterCorrection 203 8113 z)) : False := by
  have interval : (8 ≤ z ∧ z ≤ 8) ∨ (9 ≤ z ∧ z ≤ 10) ∨ (11 ≤ z ∧ z ≤ 11) := by omega
  rcases interval with range0 | range1 | range2
  · exact firstBZeroSuffix_false_203_0_8113_8_8 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_0_8113_9_10 body z range1.1 range1.2 core
  · exact firstBZeroSuffix_false_203_0_8113_11_11 body z range2.1 range2.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8114
    (body : List TagLetter) (z : Nat)
    (z_lower : 7 ≤ z) (z_upper : z ≤ 10)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8114 z)
      (firstBOneOuterJ 203 8114 z)
      (firstBOneOuterCorrection 203 8114 z)) : False := by
  have interval : (7 ≤ z ∧ z ≤ 7) ∨ (8 ≤ z ∧ z ≤ 9) ∨ (10 ≤ z ∧ z ≤ 10) := by omega
  rcases interval with range0 | range1 | range2
  · exact firstBZeroSuffix_false_203_0_8114_7_7 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_0_8114_8_9 body z range1.1 range1.2 core
  · exact firstBZeroSuffix_false_203_0_8114_10_10 body z range2.1 range2.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8115
    (body : List TagLetter) (z : Nat)
    (z_lower : 7 ≤ z) (z_upper : z ≤ 9)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8115 z)
      (firstBOneOuterJ 203 8115 z)
      (firstBOneOuterCorrection 203 8115 z)) : False := by
  have interval : (7 ≤ z ∧ z ≤ 7) ∨ (8 ≤ z ∧ z ≤ 9) := by omega
  rcases interval with range0 | range1
  · exact firstBZeroSuffix_false_203_0_8115_7_7 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_0_8115_8_9 body z range1.1 range1.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8116
    (body : List TagLetter) (z : Nat)
    (z_lower : 7 ≤ z) (z_upper : z ≤ 8)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8116 z)
      (firstBOneOuterJ 203 8116 z)
      (firstBOneOuterCorrection 203 8116 z)) : False := by
  exact firstBZeroSuffix_false_203_0_8116_7_8 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8117
    (body : List TagLetter) (z : Nat)
    (z_lower : 7 ≤ z) (z_upper : z ≤ 8)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8117 z)
      (firstBOneOuterJ 203 8117 z)
      (firstBOneOuterCorrection 203 8117 z)) : False := by
  exact firstBZeroSuffix_false_203_0_8117_7_8 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8118
    (body : List TagLetter) (z : Nat)
    (z_lower : 6 ≤ z) (z_upper : z ≤ 7)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8118 z)
      (firstBOneOuterJ 203 8118 z)
      (firstBOneOuterCorrection 203 8118 z)) : False := by
  have interval : (6 ≤ z ∧ z ≤ 6) ∨ (7 ≤ z ∧ z ≤ 7) := by omega
  rcases interval with range0 | range1
  · exact firstBZeroSuffix_false_203_0_8118_6_6 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_0_8118_7_7 body z range1.1 range1.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8119
    (body : List TagLetter) (z : Nat)
    (z_lower : 6 ≤ z) (z_upper : z ≤ 7)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8119 z)
      (firstBOneOuterJ 203 8119 z)
      (firstBOneOuterCorrection 203 8119 z)) : False := by
  have interval : (6 ≤ z ∧ z ≤ 6) ∨ (7 ≤ z ∧ z ≤ 7) := by omega
  rcases interval with range0 | range1
  · exact firstBZeroSuffix_false_203_0_8119_6_6 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_0_8119_7_7 body z range1.1 range1.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8120
    (body : List TagLetter) (z : Nat)
    (z_lower : 6 ≤ z) (z_upper : z ≤ 7)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8120 z)
      (firstBOneOuterJ 203 8120 z)
      (firstBOneOuterCorrection 203 8120 z)) : False := by
  have interval : (6 ≤ z ∧ z ≤ 6) ∨ (7 ≤ z ∧ z ≤ 7) := by omega
  rcases interval with range0 | range1
  · exact firstBZeroSuffix_false_203_0_8120_6_6 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_0_8120_7_7 body z range1.1 range1.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8121
    (body : List TagLetter) (z : Nat)
    (z_lower : 6 ≤ z) (z_upper : z ≤ 6)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8121 z)
      (firstBOneOuterJ 203 8121 z)
      (firstBOneOuterCorrection 203 8121 z)) : False := by
  exact firstBZeroSuffix_false_203_0_8121_6_6 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8122
    (body : List TagLetter) (z : Nat)
    (z_lower : 5 ≤ z) (z_upper : z ≤ 6)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8122 z)
      (firstBOneOuterJ 203 8122 z)
      (firstBOneOuterCorrection 203 8122 z)) : False := by
  have interval : (5 ≤ z ∧ z ≤ 5) ∨ (6 ≤ z ∧ z ≤ 6) := by omega
  rcases interval with range0 | range1
  · exact firstBZeroSuffix_false_203_0_8122_5_5 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_0_8122_6_6 body z range1.1 range1.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8123
    (body : List TagLetter) (z : Nat)
    (z_lower : 5 ≤ z) (z_upper : z ≤ 6)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8123 z)
      (firstBOneOuterJ 203 8123 z)
      (firstBOneOuterCorrection 203 8123 z)) : False := by
  have interval : (5 ≤ z ∧ z ≤ 5) ∨ (6 ≤ z ∧ z ≤ 6) := by omega
  rcases interval with range0 | range1
  · exact firstBZeroSuffix_false_203_0_8123_5_5 body z range0.1 range0.2 core
  · exact firstBZeroSuffix_false_203_0_8123_6_6 body z range1.1 range1.2 core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8124
    (body : List TagLetter) (z : Nat)
    (z_lower : 5 ≤ z) (z_upper : z ≤ 5)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8124 z)
      (firstBOneOuterJ 203 8124 z)
      (firstBOneOuterCorrection 203 8124 z)) : False := by
  exact firstBZeroSuffix_false_203_0_8124_5_5 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8125
    (body : List TagLetter) (z : Nat)
    (z_lower : 5 ≤ z) (z_upper : z ≤ 5)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8125 z)
      (firstBOneOuterJ 203 8125 z)
      (firstBOneOuterCorrection 203 8125 z)) : False := by
  exact firstBZeroSuffix_false_203_0_8125_5_5 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8126
    (body : List TagLetter) (z : Nat)
    (z_lower : 5 ≤ z) (z_upper : z ≤ 5)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8126 z)
      (firstBOneOuterJ 203 8126 z)
      (firstBOneOuterCorrection 203 8126 z)) : False := by
  exact firstBZeroSuffix_false_203_0_8126_5_5 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8127
    (body : List TagLetter) (z : Nat)
    (z_lower : 5 ≤ z) (z_upper : z ≤ 5)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8127 z)
      (firstBOneOuterJ 203 8127 z)
      (firstBOneOuterCorrection 203 8127 z)) : False := by
  exact firstBZeroSuffix_false_203_0_8127_5_5 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8129
    (body : List TagLetter) (z : Nat)
    (z_lower : 4 ≤ z) (z_upper : z ≤ 4)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8129 z)
      (firstBOneOuterJ 203 8129 z)
      (firstBOneOuterCorrection 203 8129 z)) : False := by
  exact firstBZeroSuffix_false_203_0_8129_4_4 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8130
    (body : List TagLetter) (z : Nat)
    (z_lower : 4 ≤ z) (z_upper : z ≤ 4)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8130 z)
      (firstBOneOuterJ 203 8130 z)
      (firstBOneOuterCorrection 203 8130 z)) : False := by
  exact firstBZeroSuffix_false_203_0_8130_4_4 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8131
    (body : List TagLetter) (z : Nat)
    (z_lower : 4 ≤ z) (z_upper : z ≤ 4)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8131 z)
      (firstBOneOuterJ 203 8131 z)
      (firstBOneOuterCorrection 203 8131 z)) : False := by
  exact firstBZeroSuffix_false_203_0_8131_4_4 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8132
    (body : List TagLetter) (z : Nat)
    (z_lower : 4 ≤ z) (z_upper : z ≤ 4)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8132 z)
      (firstBOneOuterJ 203 8132 z)
      (firstBOneOuterCorrection 203 8132 z)) : False := by
  exact firstBZeroSuffix_false_203_0_8132_4_4 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8133
    (body : List TagLetter) (z : Nat)
    (z_lower : 4 ≤ z) (z_upper : z ≤ 4)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8133 z)
      (firstBOneOuterJ 203 8133 z)
      (firstBOneOuterCorrection 203 8133 z)) : False := by
  exact firstBZeroSuffix_false_203_0_8133_4_4 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8134
    (body : List TagLetter) (z : Nat)
    (z_lower : 4 ≤ z) (z_upper : z ≤ 4)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8134 z)
      (firstBOneOuterJ 203 8134 z)
      (firstBOneOuterCorrection 203 8134 z)) : False := by
  exact firstBZeroSuffix_false_203_0_8134_4_4 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8140
    (body : List TagLetter) (z : Nat)
    (z_lower : 3 ≤ z) (z_upper : z ≤ 3)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8140 z)
      (firstBOneOuterJ 203 8140 z)
      (firstBOneOuterCorrection 203 8140 z)) : False := by
  exact firstBZeroSuffix_false_203_0_8140_3_3 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8141
    (body : List TagLetter) (z : Nat)
    (z_lower : 3 ≤ z) (z_upper : z ≤ 3)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8141 z)
      (firstBOneOuterJ 203 8141 z)
      (firstBOneOuterCorrection 203 8141 z)) : False := by
  exact firstBZeroSuffix_false_203_0_8141_3_3 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8142
    (body : List TagLetter) (z : Nat)
    (z_lower : 3 ≤ z) (z_upper : z ≤ 3)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8142 z)
      (firstBOneOuterJ 203 8142 z)
      (firstBOneOuterCorrection 203 8142 z)) : False := by
  exact firstBZeroSuffix_false_203_0_8142_3_3 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8143
    (body : List TagLetter) (z : Nat)
    (z_lower : 3 ≤ z) (z_upper : z ≤ 3)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8143 z)
      (firstBOneOuterJ 203 8143 z)
      (firstBOneOuterCorrection 203 8143 z)) : False := by
  exact firstBZeroSuffix_false_203_0_8143_3_3 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8144
    (body : List TagLetter) (z : Nat)
    (z_lower : 3 ≤ z) (z_upper : z ≤ 3)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8144 z)
      (firstBOneOuterJ 203 8144 z)
      (firstBOneOuterCorrection 203 8144 z)) : False := by
  exact firstBZeroSuffix_false_203_0_8144_3_3 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8145
    (body : List TagLetter) (z : Nat)
    (z_lower : 3 ≤ z) (z_upper : z ≤ 3)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8145 z)
      (firstBOneOuterJ 203 8145 z)
      (firstBOneOuterCorrection 203 8145 z)) : False := by
  exact firstBZeroSuffix_false_203_0_8145_3_3 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8161
    (body : List TagLetter) (z : Nat)
    (z_lower : 2 ≤ z) (z_upper : z ≤ 2)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8161 z)
      (firstBOneOuterJ 203 8161 z)
      (firstBOneOuterCorrection 203 8161 z)) : False := by
  exact firstBZeroSuffix_false_203_0_8161_2_2 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8162
    (body : List TagLetter) (z : Nat)
    (z_lower : 2 ≤ z) (z_upper : z ≤ 2)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8162 z)
      (firstBOneOuterJ 203 8162 z)
      (firstBOneOuterCorrection 203 8162 z)) : False := by
  exact firstBZeroSuffix_false_203_0_8162_2_2 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8163
    (body : List TagLetter) (z : Nat)
    (z_lower : 2 ≤ z) (z_upper : z ≤ 2)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8163 z)
      (firstBOneOuterJ 203 8163 z)
      (firstBOneOuterCorrection 203 8163 z)) : False := by
  exact firstBZeroSuffix_false_203_0_8163_2_2 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8164
    (body : List TagLetter) (z : Nat)
    (z_lower : 2 ≤ z) (z_upper : z ≤ 2)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8164 z)
      (firstBOneOuterJ 203 8164 z)
      (firstBOneOuterCorrection 203 8164 z)) : False := by
  exact firstBZeroSuffix_false_203_0_8164_2_2 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8165
    (body : List TagLetter) (z : Nat)
    (z_lower : 2 ≤ z) (z_upper : z ≤ 2)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8165 z)
      (firstBOneOuterJ 203 8165 z)
      (firstBOneOuterCorrection 203 8165 z)) : False := by
  exact firstBZeroSuffix_false_203_0_8165_2_2 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8166
    (body : List TagLetter) (z : Nat)
    (z_lower : 2 ≤ z) (z_upper : z ≤ 2)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8166 z)
      (firstBOneOuterJ 203 8166 z)
      (firstBOneOuterCorrection 203 8166 z)) : False := by
  exact firstBZeroSuffix_false_203_0_8166_2_2 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8222
    (body : List TagLetter) (z : Nat)
    (z_lower : 1 ≤ z) (z_upper : z ≤ 1)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8222 z)
      (firstBOneOuterJ 203 8222 z)
      (firstBOneOuterCorrection 203 8222 z)) : False := by
  exact firstBZeroSuffix_false_203_0_8222_1_1 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8223
    (body : List TagLetter) (z : Nat)
    (z_lower : 1 ≤ z) (z_upper : z ≤ 1)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8223 z)
      (firstBOneOuterJ 203 8223 z)
      (firstBOneOuterCorrection 203 8223 z)) : False := by
  exact firstBZeroSuffix_false_203_0_8223_1_1 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8224
    (body : List TagLetter) (z : Nat)
    (z_lower : 1 ≤ z) (z_upper : z ≤ 1)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8224 z)
      (firstBOneOuterJ 203 8224 z)
      (firstBOneOuterCorrection 203 8224 z)) : False := by
  exact firstBZeroSuffix_false_203_0_8224_1_1 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8225
    (body : List TagLetter) (z : Nat)
    (z_lower : 1 ≤ z) (z_upper : z ≤ 1)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8225 z)
      (firstBOneOuterJ 203 8225 z)
      (firstBOneOuterCorrection 203 8225 z)) : False := by
  exact firstBZeroSuffix_false_203_0_8225_1_1 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8226
    (body : List TagLetter) (z : Nat)
    (z_lower : 1 ≤ z) (z_upper : z ≤ 1)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8226 z)
      (firstBOneOuterJ 203 8226 z)
      (firstBOneOuterCorrection 203 8226 z)) : False := by
  exact firstBZeroSuffix_false_203_0_8226_1_1 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_8227
    (body : List TagLetter) (z : Nat)
    (z_lower : 1 ≤ z) (z_upper : z ≤ 1)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 8227 z)
      (firstBOneOuterJ 203 8227 z)
      (firstBOneOuterCorrection 203 8227 z)) : False := by
  exact firstBZeroSuffix_false_203_0_8227_1_1 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_2_8383
    (body : List TagLetter) (z : Nat)
    (z_lower : 0 ≤ z) (z_upper : z ≤ 0)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 2 203 8383 z)
      (firstBOneOuterJ 203 8383 z)
      (firstBOneOuterCorrection 203 8383 z)) : False := by
  exact firstBZeroSuffix_false_203_2_8383_0_0 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_1_8713
    (body : List TagLetter) (z : Nat)
    (z_lower : 0 ≤ z) (z_upper : z ≤ 0)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 1 203 8713 z)
      (firstBOneOuterJ 203 8713 z)
      (firstBOneOuterCorrection 203 8713 z)) : False := by
  exact firstBZeroSuffix_false_203_1_8713_0_0 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_1_8714
    (body : List TagLetter) (z : Nat)
    (z_lower : 0 ≤ z) (z_upper : z ≤ 0)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 1 203 8714 z)
      (firstBOneOuterJ 203 8714 z)
      (firstBOneOuterCorrection 203 8714 z)) : False := by
  exact firstBZeroSuffix_false_203_1_8714_0_0 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_9872
    (body : List TagLetter) (z : Nat)
    (z_lower : 0 ≤ z) (z_upper : z ≤ 0)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 9872 z)
      (firstBOneOuterJ 203 9872 z)
      (firstBOneOuterCorrection 203 9872 z)) : False := by
  exact firstBZeroSuffix_false_203_0_9872_0_0 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_9873
    (body : List TagLetter) (z : Nat)
    (z_lower : 0 ≤ z) (z_upper : z ≤ 0)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 9873 z)
      (firstBOneOuterJ 203 9873 z)
      (firstBOneOuterCorrection 203 9873 z)) : False := by
  exact firstBZeroSuffix_false_203_0_9873_0_0 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_9874
    (body : List TagLetter) (z : Nat)
    (z_lower : 0 ≤ z) (z_upper : z ≤ 0)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 9874 z)
      (firstBOneOuterJ 203 9874 z)
      (firstBOneOuterCorrection 203 9874 z)) : False := by
  exact firstBZeroSuffix_false_203_0_9874_0_0 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_9875
    (body : List TagLetter) (z : Nat)
    (z_lower : 0 ≤ z) (z_upper : z ≤ 0)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 9875 z)
      (firstBOneOuterJ 203 9875 z)
      (firstBOneOuterCorrection 203 9875 z)) : False := by
  exact firstBZeroSuffix_false_203_0_9875_0_0 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_9876
    (body : List TagLetter) (z : Nat)
    (z_lower : 0 ≤ z) (z_upper : z ≤ 0)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 9876 z)
      (firstBOneOuterJ 203 9876 z)
      (firstBOneOuterCorrection 203 9876 z)) : False := by
  exact firstBZeroSuffix_false_203_0_9876_0_0 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_9877
    (body : List TagLetter) (z : Nat)
    (z_lower : 0 ≤ z) (z_upper : z ≤ 0)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 9877 z)
      (firstBOneOuterJ 203 9877 z)
      (firstBOneOuterCorrection 203 9877 z)) : False := by
  exact firstBZeroSuffix_false_203_0_9877_0_0 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_9878
    (body : List TagLetter) (z : Nat)
    (z_lower : 0 ≤ z) (z_upper : z ≤ 0)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 9878 z)
      (firstBOneOuterJ 203 9878 z)
      (firstBOneOuterCorrection 203 9878 z)) : False := by
  exact firstBZeroSuffix_false_203_0_9878_0_0 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_9879
    (body : List TagLetter) (z : Nat)
    (z_lower : 0 ≤ z) (z_upper : z ≤ 0)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 9879 z)
      (firstBOneOuterJ 203 9879 z)
      (firstBOneOuterCorrection 203 9879 z)) : False := by
  exact firstBZeroSuffix_false_203_0_9879_0_0 body z z_lower z_upper core

/-- The generated interval tree extinguishes one complete terminal chamber. -/
theorem firstBZeroSuffixCore_false_203_0_9880
    (body : List TagLetter) (z : Nat)
    (z_lower : 0 ≤ z) (z_upper : z ≤ 0)
    (core : FirstBOneOuterSuffixCore body
      (firstBZeroSuffixH 0 203 9880 z)
      (firstBOneOuterJ 203 9880 z)
      (firstBOneOuterCorrection 203 9880 z)) : False := by
  exact firstBZeroSuffix_false_203_0_9880_0_0 body z z_lower z_upper core

/-- The generated exact grammar extinguishes every retained leading-`b` tail
chamber. -/
theorem firstBZeroSuffixCore_false_of_candidate
    (body : List TagLetter) (x y j z : Nat)
    (candidate : FirstBZeroTailCandidate x y j z)
    (core : FirstBOneOuterSuffixCore body (firstBZeroSuffixH j x y z)
      (firstBOneOuterJ x y z) (firstBOneOuterCorrection x y z)) : False := by
  unfold FirstBZeroTailCandidate at candidate
  rcases candidate with
    ⟨i, i_lt, x_eq, y_eq, j_eq, z_lower, z_upper⟩
  interval_cases i
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_187_0_136 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_190_5_168 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_199_2_541 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_200_2_707 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_201_0_1036 body z core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_201_0_1037 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_201_0_1038 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_202_3_1774 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_202_1_1795 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_202_1_1796 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_202_0_1844 body z core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_202_0_1845 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_202_1_1870 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_202_0_1923 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_8_6950 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_7_6951 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_6_6952 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_5_6954 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_5_6955 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_5_6961 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_4_6962 body z core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_4_6963 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_4_6964 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_3_6987 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_3_6988 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_3_6989 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_3_6990 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_3_6991 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_3_6992 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_3_6993 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_3_6995 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_3_7001 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_2_7062 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_2_7063 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_2_7064 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_2_7065 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_2_7066 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_2_7067 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_2_7068 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_2_7069 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_2_7070 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_2_7071 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_2_7073 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_2_7076 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_3_7081 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_2_7082 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_2_7087 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_2_7095 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_2_7158 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_1_7295 body z core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_1_7296 body z core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_1_7297 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_1_7298 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_1_7299 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_1_7300 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_1_7301 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_1_7302 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_1_7303 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_1_7304 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_1_7305 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_1_7306 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_1_7307 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_1_7308 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_1_7309 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_1_7310 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_1_7311 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_1_7313 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_1_7314 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_1_7317 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_1_7318 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_1_7322 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_1_7323 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_1_7331 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_1_7332 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_1_7349 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_1_7398 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_1_7399 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8095 body z core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8096 body z core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8097 body z core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8098 body z core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8099 body z core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8100 body z core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8101 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8102 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8103 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8104 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8105 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8106 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8107 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8108 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8109 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8110 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8111 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8112 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8113 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8114 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8115 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8116 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8117 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8118 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8119 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8120 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8121 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8122 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8123 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8124 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8125 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8126 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8127 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8129 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8130 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8131 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8132 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8133 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8134 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8140 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8141 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8142 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8143 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8144 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8145 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8161 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8162 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8163 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8164 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8165 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8166 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8222 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8223 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8224 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8225 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8226 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_8227 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_2_8383 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_1_8713 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_1_8714 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_9872 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_9873 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_9874 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_9875 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_9876 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_9877 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_9878 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_9879 body z z_lower z_upper core
  · norm_num [firstBZeroTailX, firstBZeroTailY,
      firstBZeroTailPosition, firstBZeroTailLower,
      firstBZeroTailUpper] at x_eq y_eq j_eq z_lower z_upper
    subst x
    subst y
    subst j
    exact firstBZeroSuffixCore_false_203_0_9880 body z z_lower z_upper core

end MatrixMortality.ParabolicBlade
