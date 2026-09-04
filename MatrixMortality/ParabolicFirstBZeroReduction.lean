import MatrixMortality.ParabolicFirstBZeroReductionCertificate0
import MatrixMortality.ParabolicFirstBZeroReductionCertificate1
import MatrixMortality.ParabolicFirstBZeroReductionCertificate2
import MatrixMortality.ParabolicFirstBZeroReductionCertificate3
import MatrixMortality.ParabolicFirstBZeroReductionCertificate4
import MatrixMortality.ParabolicFirstBZeroReductionCertificate5
import MatrixMortality.ParabolicFirstBZeroReductionCertificate6
import MatrixMortality.ParabolicFirstBZeroReductionCertificate7
import MatrixMortality.ParabolicFirstBZeroReductionCertificate8
import MatrixMortality.ParabolicFirstBZeroReductionCertificate9
import MatrixMortality.ParabolicFirstBZeroReductionCertificate10
import MatrixMortality.ParabolicFirstBZeroReductionCertificate11
import MatrixMortality.ParabolicFirstBZeroReductionCertificate12
import MatrixMortality.ParabolicFirstBZeroReductionCertificate13
import MatrixMortality.ParabolicFirstBZeroReductionCertificate14
import MatrixMortality.ParabolicFirstBZeroReductionCertificate15
import MatrixMortality.ParabolicFirstBZeroReductionCertificate16
import MatrixMortality.ParabolicFirstBZeroReductionCertificate17
import MatrixMortality.ParabolicFirstBZeroReductionCertificate18
import MatrixMortality.ParabolicFirstBZeroReductionCertificate19
import MatrixMortality.ParabolicFirstBZeroReductionCertificate20
import MatrixMortality.ParabolicFirstBZeroReductionCertificate21
import MatrixMortality.ParabolicFirstBZeroReductionCertificate22
import MatrixMortality.ParabolicFirstBZeroReductionCertificate23
import MatrixMortality.ParabolicFirstBZeroReductionCertificate24
import MatrixMortality.ParabolicFirstBZeroReductionCertificate25

/-!
# Exact tail reduction for the leading first-`b` cylinder

The 3,243 outer-root points contract through 179 maximal killed ranges to 146 indexed
terminal chambers. Generated arithmetic is rechecked by the rational rectangle calculus.
-/

namespace MatrixMortality.ParabolicBlade

/-- The generated exact rectangle reduction maps every outer-root point to one of
the 146 indexed terminal chambers. -/
theorem firstBZeroTailCandidate_of_root_candidate
    (j : Nat) (rest : List TagLetter) (x y z : Nat)
    (candidate : FirstBZeroRootCandidate x y)
    (root_eq : firstBTwoTailZDenominator
      (firstBLateTailA 0 (List.replicate j .c ++ .b :: rest) y)
      (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) x y * z =
        firstBTwoTailZNumerator
          (firstBLateTailA 0 (List.replicate j .c ++ .b :: rest) y)
          (firstBTwoTailD (List.replicate j .c ++ .b :: rest)) x y) :
    FirstBZeroTailCandidate x y j z := by
  unfold FirstBZeroRootCandidate at candidate
  rcases candidate with outer0 | outer1 | outer2 | outer3 | outer4 | outer5 | outer6 | outer7 |
    outer8 | outer9 | outer10 | outer11 | outer12 | outer13 | outer14 | outer15 | outer16 | outer17
    | outer18 | outer19 | outer20 | outer21 | outer22 | outer23 | outer24 | outer25 | outer26 |
    outer27 | outer28 | outer29 | outer30 | outer31 | outer32 | outer33 | outer34 | outer35 |
    outer36 | outer37 | outer38 | outer39
  · rcases outer0 with ⟨rfl, rfl⟩
    exact firstBZeroTailCandidate_of_outer_81 j rest 8 z (by norm_num) (by norm_num) root_eq
  · rcases outer1 with ⟨rfl, rfl⟩
    exact firstBZeroTailCandidate_of_outer_87 j rest 9 z (by norm_num) (by norm_num) root_eq
  · rcases outer2 with ⟨rfl, rfl⟩
    exact firstBZeroTailCandidate_of_outer_125 j rest 19 z (by norm_num) (by norm_num) root_eq
  · rcases outer3 with ⟨rfl, rfl⟩
    exact firstBZeroTailCandidate_of_outer_132 j rest 22 z (by norm_num) (by norm_num) root_eq
  · rcases outer4 with ⟨rfl, rfl⟩
    exact firstBZeroTailCandidate_of_outer_134 j rest 23 z (by norm_num) (by norm_num) root_eq
  · rcases outer5 with ⟨rfl, rfl⟩
    exact firstBZeroTailCandidate_of_outer_136 j rest 24 z (by norm_num) (by norm_num) root_eq
  · rcases outer6 with ⟨rfl, rfl⟩
    exact firstBZeroTailCandidate_of_outer_147 j rest 31 z (by norm_num) (by norm_num) root_eq
  · rcases outer7 with ⟨rfl, rfl⟩
    exact firstBZeroTailCandidate_of_outer_153 j rest 36 z (by norm_num) (by norm_num) root_eq
  · rcases outer8 with ⟨rfl, rfl⟩
    exact firstBZeroTailCandidate_of_outer_154 j rest 37 z (by norm_num) (by norm_num) root_eq
  · rcases outer9 with ⟨rfl, rfl⟩
    exact firstBZeroTailCandidate_of_outer_155 j rest 38 z (by norm_num) (by norm_num) root_eq
  · rcases outer10 with ⟨rfl, rfl⟩
    exact firstBZeroTailCandidate_of_outer_161 j rest 45 z (by norm_num) (by norm_num) root_eq
  · rcases outer11 with ⟨rfl, rfl⟩
    exact firstBZeroTailCandidate_of_outer_163 j rest 48 z (by norm_num) (by norm_num) root_eq
  · rcases outer12 with ⟨rfl, rfl⟩
    exact firstBZeroTailCandidate_of_outer_165 j rest 51 z (by norm_num) (by norm_num) root_eq
  · rcases outer13 with ⟨rfl, rfl⟩
    exact firstBZeroTailCandidate_of_outer_172 j rest 65 z (by norm_num) (by norm_num) root_eq
  · rcases outer14 with ⟨rfl, rfl⟩
    exact firstBZeroTailCandidate_of_outer_175 j rest 73 z (by norm_num) (by norm_num) root_eq
  · rcases outer15 with ⟨rfl, rfl⟩
    exact firstBZeroTailCandidate_of_outer_178 j rest 83 z (by norm_num) (by norm_num) root_eq
  · rcases outer16 with ⟨rfl, rfl⟩
    exact firstBZeroTailCandidate_of_outer_179 j rest 87 z (by norm_num) (by norm_num) root_eq
  · rcases outer17 with ⟨rfl, rfl⟩
    exact firstBZeroTailCandidate_of_outer_181 j rest 96 z (by norm_num) (by norm_num) root_eq
  · rcases outer18 with ⟨rfl, rfl⟩
    exact firstBZeroTailCandidate_of_outer_182 j rest 101 z (by norm_num) (by norm_num) root_eq
  · rcases outer19 with ⟨rfl, rfl⟩
    exact firstBZeroTailCandidate_of_outer_183 j rest 107 z (by norm_num) (by norm_num) root_eq
  · rcases outer20 with ⟨rfl, rfl⟩
    exact firstBZeroTailCandidate_of_outer_184 j rest 113 z (by norm_num) (by norm_num) root_eq
  · rcases outer21 with ⟨rfl, rfl⟩
    exact firstBZeroTailCandidate_of_outer_185 j rest 120 z (by norm_num) (by norm_num) root_eq
  · rcases outer22 with ⟨rfl, rfl⟩
    exact firstBZeroTailCandidate_of_outer_186 j rest 127 z (by norm_num) (by norm_num) root_eq
  · rcases outer23 with ⟨rfl, rfl⟩
    exact firstBZeroTailCandidate_of_outer_187 j rest 136 z (by norm_num) (by norm_num) root_eq
  · rcases outer24 with ⟨rfl, y_lower, y_upper⟩
    exact firstBZeroTailCandidate_of_outer_188 j rest y z y_lower y_upper root_eq
  · rcases outer25 with ⟨rfl, y_lower, y_upper⟩
    exact firstBZeroTailCandidate_of_outer_189 j rest y z y_lower y_upper root_eq
  · rcases outer26 with ⟨rfl, y_lower, y_upper⟩
    exact firstBZeroTailCandidate_of_outer_190 j rest y z y_lower y_upper root_eq
  · rcases outer27 with ⟨rfl, y_lower, y_upper⟩
    exact firstBZeroTailCandidate_of_outer_191 j rest y z y_lower y_upper root_eq
  · rcases outer28 with ⟨rfl, y_lower, y_upper⟩
    exact firstBZeroTailCandidate_of_outer_192 j rest y z y_lower y_upper root_eq
  · rcases outer29 with ⟨rfl, y_lower, y_upper⟩
    exact firstBZeroTailCandidate_of_outer_193 j rest y z y_lower y_upper root_eq
  · rcases outer30 with ⟨rfl, y_lower, y_upper⟩
    exact firstBZeroTailCandidate_of_outer_194 j rest y z y_lower y_upper root_eq
  · rcases outer31 with ⟨rfl, y_lower, y_upper⟩
    exact firstBZeroTailCandidate_of_outer_195 j rest y z y_lower y_upper root_eq
  · rcases outer32 with ⟨rfl, y_lower, y_upper⟩
    exact firstBZeroTailCandidate_of_outer_196 j rest y z y_lower y_upper root_eq
  · rcases outer33 with ⟨rfl, y_lower, y_upper⟩
    exact firstBZeroTailCandidate_of_outer_197 j rest y z y_lower y_upper root_eq
  · rcases outer34 with ⟨rfl, y_lower, y_upper⟩
    exact firstBZeroTailCandidate_of_outer_198 j rest y z y_lower y_upper root_eq
  · rcases outer35 with ⟨rfl, y_lower, y_upper⟩
    exact firstBZeroTailCandidate_of_outer_199 j rest y z y_lower y_upper root_eq
  · rcases outer36 with ⟨rfl, y_lower, y_upper⟩
    exact firstBZeroTailCandidate_of_outer_200 j rest y z y_lower y_upper root_eq
  · rcases outer37 with ⟨rfl, y_lower, y_upper⟩
    exact firstBZeroTailCandidate_of_outer_201 j rest y z y_lower y_upper root_eq
  · rcases outer38 with ⟨rfl, y_lower, y_upper⟩
    exact firstBZeroTailCandidate_of_outer_202 j rest y z y_lower y_upper root_eq
  · rcases outer39 with ⟨rfl, y_lower, y_upper⟩
    exact firstBZeroTailCandidate_of_outer_203 j rest y z y_lower y_upper root_eq

end MatrixMortality.ParabolicBlade
