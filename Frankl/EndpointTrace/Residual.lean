import Frankl.EndpointTrace.ResidualTrace0
import Frankl.EndpointTrace.ResidualTrace1
import Frankl.EndpointTrace.ResidualTrace2
import Frankl.EndpointTrace.ResidualTrace3
import Frankl.EndpointTrace.ResidualTrace4
import Frankl.EndpointTrace.ResidualTrace5
import Frankl.EndpointTrace.ResidualTrace6
import Frankl.EndpointTrace.ResidualTrace7
import Frankl.EndpointTrace.ResidualTrace8
import Frankl.EndpointTrace.ResidualTrace9
import Frankl.EndpointTrace.ResidualTrace10
import Frankl.EndpointTrace.ResidualTrace11
import Frankl.EndpointTrace.ResidualTrace12
import Frankl.EndpointTrace.ResidualTrace13
import Frankl.EndpointTrace.ResidualTrace14
import Frankl.EndpointTrace.ResidualTrace15
import Frankl.EndpointTrace.ResidualTrace16
import Frankl.EndpointTrace.ResidualTrace17
import Frankl.EndpointTrace.ResidualTrace18
import Frankl.EndpointTrace.ResidualTrace19
import Frankl.EndpointTrace.ResidualTrace20
import Frankl.EndpointTrace.ResidualTrace21
import Frankl.EndpointTrace.ResidualTrace22
import Frankl.EndpointTrace.ResidualTrace23
import Frankl.EndpointTrace.ResidualTrace24
import Frankl.EndpointTrace.ResidualTrace25
import Frankl.EndpointTrace.ResidualTrace26

namespace Frankl

private theorem residualRootLLLLCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 4) ≤ a)
    (haUpper : a ≤ ((23 : ℝ) / 80))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 800)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hresidualRootLLLL : q ≤ ((31 : ℝ) / 1600)
  · by_cases hresidualRootLLLLL : a ≤ ((43 : ℝ) / 160)
    · by_cases hresidualRootLLLLLL : q ≤ ((31 : ℝ) / 3200)
      · by_cases hresidualRootLLLLLLL : a ≤ ((83 : ℝ) / 320)
        · exact residualRootLLLLLLLL_nonneg
            (by linarith) (by linarith) (by linarith) (by linarith)
        · exact residualRootLLLLLLLU_nonneg
            (by linarith) (by linarith) (by linarith) (by linarith)
      · exact residualRootLLLLLLU_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
    · by_cases hresidualRootLLLLLU : q ≤ ((31 : ℝ) / 3200)
      · by_cases hresidualRootLLLLLUL : a ≤ ((89 : ℝ) / 320)
        · exact residualRootLLLLLULL_nonneg
            (by linarith) (by linarith) (by linarith) (by linarith)
        · exact residualRootLLLLLULU_nonneg
            (by linarith) (by linarith) (by linarith) (by linarith)
      · exact residualRootLLLLLUU_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
  · exact residualRootLLLLU_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem residualRootLLLUCover {a q : ℝ}
    (haLower : ((23 : ℝ) / 80) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 40))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 800)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hresidualRootLLLU : q ≤ ((31 : ℝ) / 1600)
  · by_cases hresidualRootLLLUL : a ≤ ((49 : ℝ) / 160)
    · by_cases hresidualRootLLLULL : q ≤ ((31 : ℝ) / 3200)
      · by_cases hresidualRootLLLULLL : a ≤ ((19 : ℝ) / 64)
        · exact residualRootLLLULLLL_nonneg
            (by linarith) (by linarith) (by linarith) (by linarith)
        · exact residualRootLLLULLLU_nonneg
            (by linarith) (by linarith) (by linarith) (by linarith)
      · exact residualRootLLLULLU_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
    · by_cases hresidualRootLLLULU : q ≤ ((31 : ℝ) / 3200)
      · by_cases hresidualRootLLLULUL : a ≤ ((101 : ℝ) / 320)
        · exact residualRootLLLULULL_nonneg
            (by linarith) (by linarith) (by linarith) (by linarith)
        · exact residualRootLLLULULU_nonneg
            (by linarith) (by linarith) (by linarith) (by linarith)
      · exact residualRootLLLULUU_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
  · exact residualRootLLLUU_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem residualRootLLUCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 4) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 40))
    (hqLower : ((31 : ℝ) / 800) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 400)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hresidualRootLLU : a ≤ ((23 : ℝ) / 80)
  · exact residualRootLLUL_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)
  · by_cases hresidualRootLLUU : a ≤ ((49 : ℝ) / 160)
    · exact residualRootLLUUL_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)
    · exact residualRootLLUUU_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)

private theorem residualRootLULCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 4) ≤ a)
    (haUpper : a ≤ ((23 : ℝ) / 80))
    (hqLower : ((31 : ℝ) / 400) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 200)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hresidualRootLUL : a ≤ ((43 : ℝ) / 160)
  · by_cases hresidualRootLULL : q ≤ ((93 : ℝ) / 800)
    · exact residualRootLULLL_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)
    · exact residualRootLULLU_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)
  · by_cases hresidualRootLULU : q ≤ ((93 : ℝ) / 800)
    · exact residualRootLULUL_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)
    · exact residualRootLULUU_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)

private theorem residualRootLUUCover {a q : ℝ}
    (haLower : ((23 : ℝ) / 80) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 40))
    (hqLower : ((31 : ℝ) / 400) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 200)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hresidualRootLUU : a ≤ ((49 : ℝ) / 160)
  · by_cases hresidualRootLUUL : q ≤ ((93 : ℝ) / 800)
    · exact residualRootLUULL_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)
    · exact residualRootLUULU_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)
  · by_cases hresidualRootLUUU : q ≤ ((93 : ℝ) / 800)
    · exact residualRootLUUUL_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)
    · by_cases hresidualRootLUUUU : a ≤ ((101 : ℝ) / 320)
      · exact residualRootLUUUUL_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
      · exact residualRootLUUUUU_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)

private theorem residualRootULLLCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 4) ≤ a)
    (haUpper : a ≤ ((43 : ℝ) / 160))
    (hqLower : ((31 : ℝ) / 200) ≤ q)
    (hqUpper : q ≤ ((93 : ℝ) / 400)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hresidualRootULLL : q ≤ ((31 : ℝ) / 160)
  · by_cases hresidualRootULLLL : a ≤ ((83 : ℝ) / 320)
    · exact residualRootULLLLL_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)
    · exact residualRootULLLLU_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)
  · by_cases hresidualRootULLLU : a ≤ ((83 : ℝ) / 320)
    · exact residualRootULLLUL_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)
    · exact residualRootULLLUU_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)

private theorem residualRootULLUCover {a q : ℝ}
    (haLower : ((43 : ℝ) / 160) ≤ a)
    (haUpper : a ≤ ((23 : ℝ) / 80))
    (hqLower : ((31 : ℝ) / 200) ≤ q)
    (hqUpper : q ≤ ((93 : ℝ) / 400)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hresidualRootULLU : q ≤ ((31 : ℝ) / 160)
  · by_cases hresidualRootULLUL : a ≤ ((89 : ℝ) / 320)
    · exact residualRootULLULL_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)
    · exact residualRootULLULU_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)
  · by_cases hresidualRootULLUU : a ≤ ((89 : ℝ) / 320)
    · exact residualRootULLUUL_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)
    · by_cases hresidualRootULLUUU : q ≤ ((341 : ℝ) / 1600)
      · exact residualRootULLUUUL_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
      · exact residualRootULLUUUU_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)

private theorem residualRootULULCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 4) ≤ a)
    (haUpper : a ≤ ((43 : ℝ) / 160))
    (hqLower : ((93 : ℝ) / 400) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 100)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hresidualRootULUL : q ≤ ((217 : ℝ) / 800)
  · by_cases hresidualRootULULL : a ≤ ((83 : ℝ) / 320)
    · exact residualRootULULLL_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)
    · by_cases hresidualRootULULLU : q ≤ ((403 : ℝ) / 1600)
      · exact residualRootULULLUL_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
      · exact residualRootULULLUU_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
  · by_cases hresidualRootULULU : a ≤ ((83 : ℝ) / 320)
    · exact residualRootULULUL_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)
    · by_cases hresidualRootULULUU : q ≤ ((93 : ℝ) / 320)
      · exact residualRootULULUUL_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
      · exact residualRootULULUUU_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)

private theorem residualRootULUUCover {a q : ℝ}
    (haLower : ((43 : ℝ) / 160) ≤ a)
    (haUpper : a ≤ ((23 : ℝ) / 80))
    (hqLower : ((93 : ℝ) / 400) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 100)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hresidualRootULUU : q ≤ ((217 : ℝ) / 800)
  · by_cases hresidualRootULUUL : a ≤ ((89 : ℝ) / 320)
    · by_cases hresidualRootULUULL : q ≤ ((403 : ℝ) / 1600)
      · exact residualRootULUULLL_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
      · exact residualRootULUULLU_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
    · by_cases hresidualRootULUULU : q ≤ ((403 : ℝ) / 1600)
      · exact residualRootULUULUL_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
      · exact residualRootULUULUU_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
  · by_cases hresidualRootULUUU : a ≤ ((89 : ℝ) / 320)
    · by_cases hresidualRootULUUUL : q ≤ ((93 : ℝ) / 320)
      · exact residualRootULUUULL_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
      · exact residualRootULUUULU_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
    · by_cases hresidualRootULUUUU : q ≤ ((93 : ℝ) / 320)
      · exact residualRootULUUUUL_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
      · exact residualRootULUUUUU_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)

private theorem residualRootUULLCover {a q : ℝ}
    (haLower : ((23 : ℝ) / 80) ≤ a)
    (haUpper : a ≤ ((49 : ℝ) / 160))
    (hqLower : ((31 : ℝ) / 200) ≤ q)
    (hqUpper : q ≤ ((93 : ℝ) / 400)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hresidualRootUULL : q ≤ ((31 : ℝ) / 160)
  · by_cases hresidualRootUULLL : a ≤ ((19 : ℝ) / 64)
    · exact residualRootUULLLL_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)
    · exact residualRootUULLLU_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)
  · by_cases hresidualRootUULLU : a ≤ ((19 : ℝ) / 64)
    · by_cases hresidualRootUULLUL : q ≤ ((341 : ℝ) / 1600)
      · exact residualRootUULLULL_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
      · exact residualRootUULLULU_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
    · by_cases hresidualRootUULLUU : q ≤ ((341 : ℝ) / 1600)
      · exact residualRootUULLUUL_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
      · exact residualRootUULLUUU_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)

private theorem residualRootUULUCover {a q : ℝ}
    (haLower : ((49 : ℝ) / 160) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 40))
    (hqLower : ((31 : ℝ) / 200) ≤ q)
    (hqUpper : q ≤ ((93 : ℝ) / 400)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hresidualRootUULU : q ≤ ((31 : ℝ) / 160)
  · by_cases hresidualRootUULUL : a ≤ ((101 : ℝ) / 320)
    · exact residualRootUULULL_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)
    · exact residualRootUULULU_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)
  · by_cases hresidualRootUULUU : a ≤ ((101 : ℝ) / 320)
    · by_cases hresidualRootUULUUL : q ≤ ((341 : ℝ) / 1600)
      · exact residualRootUULUULL_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
      · exact residualRootUULUULU_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
    · by_cases hresidualRootUULUUU : q ≤ ((341 : ℝ) / 1600)
      · exact residualRootUULUUUL_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
      · exact residualRootUULUUUU_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)

private theorem residualRootUUULLCover {a q : ℝ}
    (haLower : ((23 : ℝ) / 80) ≤ a)
    (haUpper : a ≤ ((49 : ℝ) / 160))
    (hqLower : ((93 : ℝ) / 400) ≤ q)
    (hqUpper : q ≤ ((217 : ℝ) / 800)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hresidualRootUUULL : a ≤ ((19 : ℝ) / 64)
  · by_cases hresidualRootUUULLL : q ≤ ((403 : ℝ) / 1600)
    · exact residualRootUUULLLL_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)
    · exact residualRootUUULLLU_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)
  · by_cases hresidualRootUUULLU : q ≤ ((403 : ℝ) / 1600)
    · exact residualRootUUULLUL_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)
    · exact residualRootUUULLUU_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)

private theorem residualRootUUULUCover {a q : ℝ}
    (haLower : ((23 : ℝ) / 80) ≤ a)
    (haUpper : a ≤ ((49 : ℝ) / 160))
    (hqLower : ((217 : ℝ) / 800) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 100)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hresidualRootUUULU : a ≤ ((19 : ℝ) / 64)
  · by_cases hresidualRootUUULUL : q ≤ ((93 : ℝ) / 320)
    · exact residualRootUUULULL_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)
    · exact residualRootUUULULU_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)
  · by_cases hresidualRootUUULUU : a ≤ ((193 : ℝ) / 640)
    · by_cases hresidualRootUUULUUL : q ≤ ((93 : ℝ) / 320)
      · exact residualRootUUULUULL_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
      · exact residualRootUUULUULU_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
    · by_cases hresidualRootUUULUUU : q ≤ ((93 : ℝ) / 320)
      · exact residualRootUUULUUUL_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
      · exact residualRootUUULUUUU_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)

private theorem residualRootUUUULCover {a q : ℝ}
    (haLower : ((49 : ℝ) / 160) ≤ a)
    (haUpper : a ≤ ((101 : ℝ) / 320))
    (hqLower : ((93 : ℝ) / 400) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 100)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hresidualRootUUUUL : q ≤ ((217 : ℝ) / 800)
  · by_cases hresidualRootUUUULL : a ≤ ((199 : ℝ) / 640)
    · exact residualRootUUUULLL_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)
    · exact residualRootUUUULLU_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)
  · by_cases hresidualRootUUUULU : a ≤ ((199 : ℝ) / 640)
    · by_cases hresidualRootUUUULUL : q ≤ ((93 : ℝ) / 320)
      · exact residualRootUUUULULL_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
      · exact residualRootUUUULULU_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
    · by_cases hresidualRootUUUULUU : q ≤ ((93 : ℝ) / 320)
      · exact residualRootUUUULUUL_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
      · exact residualRootUUUULUUU_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)

private theorem residualRootUUUUUCover {a q : ℝ}
    (haLower : ((101 : ℝ) / 320) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 40))
    (hqLower : ((93 : ℝ) / 400) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 100)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hresidualRootUUUUU : q ≤ ((217 : ℝ) / 800)
  · by_cases hresidualRootUUUUUL : a ≤ ((41 : ℝ) / 128)
    · exact residualRootUUUUULL_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)
    · exact residualRootUUUUULU_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)
  · by_cases hresidualRootUUUUUU : a ≤ ((41 : ℝ) / 128)
    · by_cases hresidualRootUUUUUUL : q ≤ ((93 : ℝ) / 320)
      · exact residualRootUUUUUULL_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
      · exact residualRootUUUUUULU_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
    · by_cases hresidualRootUUUUUUU : q ≤ ((93 : ℝ) / 320)
      · exact residualRootUUUUUUUL_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
      · exact residualRootUUUUUUUU_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)

/-- The exact residual rectangle below the analytic conditional-mean core. -/
theorem endpointCertificateObjective_residual_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 4) ≤ a) (haUpper : a ≤ ((13 : ℝ) / 40))
    (hqLower : ((0 : ℝ) / 1) ≤ q) (hqUpper : q ≤ ((31 : ℝ) / 100)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hresidualRoot : q ≤ ((31 : ℝ) / 200)
  · by_cases hresidualRootL : q ≤ ((31 : ℝ) / 400)
    · by_cases hresidualRootLL : q ≤ ((31 : ℝ) / 800)
      · by_cases hresidualRootLLL : a ≤ ((23 : ℝ) / 80)
        · exact residualRootLLLLCover
            (by linarith) (by linarith) (by linarith) (by linarith)
        · exact residualRootLLLUCover
            (by linarith) (by linarith) (by linarith) (by linarith)
      · exact residualRootLLUCover
          (by linarith) (by linarith) (by linarith) (by linarith)
    · by_cases hresidualRootLU : a ≤ ((23 : ℝ) / 80)
      · exact residualRootLULCover
          (by linarith) (by linarith) (by linarith) (by linarith)
      · exact residualRootLUUCover
          (by linarith) (by linarith) (by linarith) (by linarith)
  · by_cases hresidualRootU : a ≤ ((23 : ℝ) / 80)
    · by_cases hresidualRootUL : q ≤ ((93 : ℝ) / 400)
      · by_cases hresidualRootULL : a ≤ ((43 : ℝ) / 160)
        · exact residualRootULLLCover
            (by linarith) (by linarith) (by linarith) (by linarith)
        · exact residualRootULLUCover
            (by linarith) (by linarith) (by linarith) (by linarith)
      · by_cases hresidualRootULU : a ≤ ((43 : ℝ) / 160)
        · exact residualRootULULCover
            (by linarith) (by linarith) (by linarith) (by linarith)
        · exact residualRootULUUCover
            (by linarith) (by linarith) (by linarith) (by linarith)
    · by_cases hresidualRootUU : q ≤ ((93 : ℝ) / 400)
      · by_cases hresidualRootUUL : a ≤ ((49 : ℝ) / 160)
        · exact residualRootUULLCover
            (by linarith) (by linarith) (by linarith) (by linarith)
        · exact residualRootUULUCover
            (by linarith) (by linarith) (by linarith) (by linarith)
      · by_cases hresidualRootUUU : a ≤ ((49 : ℝ) / 160)
        · by_cases hresidualRootUUUL : q ≤ ((217 : ℝ) / 800)
          · exact residualRootUUULLCover
              (by linarith) (by linarith) (by linarith) (by linarith)
          · exact residualRootUUULUCover
              (by linarith) (by linarith) (by linarith) (by linarith)
        · by_cases hresidualRootUUUU : a ≤ ((101 : ℝ) / 320)
          · exact residualRootUUUULCover
              (by linarith) (by linarith) (by linarith) (by linarith)
          · exact residualRootUUUUUCover
              (by linarith) (by linarith) (by linarith) (by linarith)

end Frankl
