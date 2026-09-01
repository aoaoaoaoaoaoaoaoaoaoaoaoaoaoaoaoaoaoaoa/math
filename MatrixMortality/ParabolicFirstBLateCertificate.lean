import MatrixMortality.ParabolicFirstBLateCertificate0
import MatrixMortality.ParabolicFirstBLateCertificate1
import MatrixMortality.ParabolicFirstBLateCertificate2
import MatrixMortality.ParabolicFirstBLateCertificate3

/-!
# Later-position suffix certificate

The four generated shards partition and recheck the 44 exact outer-root points. This module
exposes their aggregate classifier.
-/

namespace MatrixMortality.ParabolicBlade

/-- Every one of the 44 exact outer-root points dies in its complete tail cylinder. -/
theorem firstBLateTail_false_of_candidate
    (k j : Nat) (rest : List TagLetter) (x y z : Nat)
    (candidate : FirstBLateRootCandidate k x y)
    (root_eq : firstBTwoTailZDenominator
      (firstBLateTailA k (List.replicate j .c ++ .b :: rest) y)
      (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) x y * z =
        firstBTwoTailZNumerator
          (firstBLateTailA k (List.replicate j .c ++ .b :: rest) y)
          (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) x y) : False := by
  unfold FirstBLateRootCandidate at candidate
  rcases candidate with c209 | c210 | c211 | c212 | c213 | c214 |
    c418 | c443 | c513 | c602
  · rcases c209 with ⟨rfl, rfl, rfl⟩
    exact firstBLateTail_false_3_209_17 j rest z root_eq
  · rcases c210 with ⟨rfl, rfl, rfl⟩
    exact firstBLateTail_false_3_210_21 j rest z root_eq
  · rcases c211 with ⟨rfl, rfl, rfl⟩
    exact firstBLateTail_false_3_211_27 j rest z root_eq
  · rcases c212 with ⟨rfl, rfl, rfl⟩
    exact firstBLateTail_false_3_212_38 j rest z root_eq
  · rcases c213 with ⟨rfl, rfl, y_lower, y_upper⟩
    interval_cases y
    · exact firstBLateTail_false_3_213_64 j rest z root_eq
    · exact firstBLateTail_false_3_213_65 j rest z root_eq
    · exact firstBLateTail_false_3_213_66 j rest z root_eq
  · rcases c214 with ⟨rfl, rfl, y_lower, y_upper⟩
    interval_cases y
    · exact firstBLateTail_false_3_214_206 j rest z root_eq
    · exact firstBLateTail_false_3_214_207 j rest z root_eq
    · exact firstBLateTail_false_3_214_208 j rest z root_eq
    · exact firstBLateTail_false_3_214_209 j rest z root_eq
    · exact firstBLateTail_false_3_214_210 j rest z root_eq
    · exact firstBLateTail_false_3_214_211 j rest z root_eq
    · exact firstBLateTail_false_3_214_212 j rest z root_eq
    · exact firstBLateTail_false_3_214_213 j rest z root_eq
    · exact firstBLateTail_false_3_214_214 j rest z root_eq
    · exact firstBLateTail_false_3_214_215 j rest z root_eq
    · exact firstBLateTail_false_3_214_216 j rest z root_eq
    · exact firstBLateTail_false_3_214_217 j rest z root_eq
    · exact firstBLateTail_false_3_214_218 j rest z root_eq
    · exact firstBLateTail_false_3_214_219 j rest z root_eq
    · exact firstBLateTail_false_3_214_220 j rest z root_eq
    · exact firstBLateTail_false_3_214_221 j rest z root_eq
    · exact firstBLateTail_false_3_214_222 j rest z root_eq
    · exact firstBLateTail_false_3_214_223 j rest z root_eq
    · exact firstBLateTail_false_3_214_224 j rest z root_eq
    · exact firstBLateTail_false_3_214_225 j rest z root_eq
    · exact firstBLateTail_false_3_214_226 j rest z root_eq
    · exact firstBLateTail_false_3_214_227 j rest z root_eq
    · exact firstBLateTail_false_3_214_228 j rest z root_eq
    · exact firstBLateTail_false_3_214_229 j rest z root_eq
    · exact firstBLateTail_false_3_214_230 j rest z root_eq
    · exact firstBLateTail_false_3_214_231 j rest z root_eq
    · exact firstBLateTail_false_3_214_232 j rest z root_eq
    · exact firstBLateTail_false_3_214_233 j rest z root_eq
    · exact firstBLateTail_false_3_214_234 j rest z root_eq
    · exact firstBLateTail_false_3_214_235 j rest z root_eq
    · exact firstBLateTail_false_3_214_236 j rest z root_eq
  · rcases c418 with ⟨rfl, rfl, rfl⟩
    exact firstBLateTail_false_4_213_18 j rest z root_eq
  · rcases c443 with ⟨rfl, rfl, y_lower, y_upper⟩
    interval_cases y
    · exact firstBLateTail_false_4_214_43 j rest z root_eq
    · exact firstBLateTail_false_4_214_44 j rest z root_eq
    · exact firstBLateTail_false_4_214_45 j rest z root_eq
  · rcases c513 with ⟨rfl, rfl, rfl⟩
    exact firstBLateTail_false_5_214_13 j rest z root_eq
  · rcases c602 with ⟨rfl, rfl, rfl⟩
    exact firstBLateTail_false_6_213_2 j rest z root_eq

end MatrixMortality.ParabolicBlade
