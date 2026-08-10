import Frankl.EndpointTrace.LowRow0Trace0
import Frankl.EndpointTrace.LowRow0Trace1
import Frankl.EndpointTrace.LowRow0Trace2
import Frankl.EndpointTrace.LowRow0Trace3
import Frankl.EndpointTrace.LowRow0Trace4
import Frankl.EndpointTrace.LowRow0Trace5
import Frankl.EndpointTrace.LowRow0Trace6
import Frankl.EndpointTrace.LowRow0Trace7

namespace Frankl

private theorem lowRow0Cell0RootCover {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow0Cell0Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow0Cell1RootCover {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((1 : ℝ) / 1000) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hlowRow0Cell1Root : q ≤ ((129 : ℝ) / 8000)
  · by_cases hlowRow0Cell1RootL : q ≤ ((137 : ℝ) / 16000)
    · by_cases hlowRow0Cell1RootLL : q ≤ ((153 : ℝ) / 32000)
      · by_cases hlowRow0Cell1RootLLL : q ≤ ((37 : ℝ) / 12800)
        · by_cases hlowRow0Cell1RootLLLL : q ≤ ((249 : ℝ) / 128000)
          · by_cases hlowRow0Cell1RootLLLLL : a ≤ ((1 : ℝ) / 2000)
            · by_cases hlowRow0Cell1RootLLLLLL : q ≤ ((377 : ℝ) / 256000)
              · by_cases hlowRow0Cell1RootLLLLLLL : a ≤ ((1 : ℝ) / 4000)
                · by_cases hlowRow0Cell1RootLLLLLLLL : q ≤ ((633 : ℝ) / 512000)
                  · exact lowRow0Cell1RootLLLLLLLLL_nonneg
                      (by linarith) (by linarith) (by linarith) (by linarith)
                  · exact lowRow0Cell1RootLLLLLLLLU_nonneg
                      (by linarith) (by linarith) (by linarith) (by linarith)
                · exact lowRow0Cell1RootLLLLLLLU_nonneg
                    (by linarith) (by linarith) (by linarith) (by linarith)
              · exact lowRow0Cell1RootLLLLLLU_nonneg
                  (by linarith) (by linarith) (by linarith) (by linarith)
            · exact lowRow0Cell1RootLLLLLU_nonneg
                (by linarith) (by linarith) (by linarith) (by linarith)
          · by_cases hlowRow0Cell1RootLLLLU : a ≤ ((1 : ℝ) / 2000)
            · by_cases hlowRow0Cell1RootLLLLUL : q ≤ ((619 : ℝ) / 256000)
              · exact lowRow0Cell1RootLLLLULL_nonneg
                  (by linarith) (by linarith) (by linarith) (by linarith)
              · exact lowRow0Cell1RootLLLLULU_nonneg
                  (by linarith) (by linarith) (by linarith) (by linarith)
            · exact lowRow0Cell1RootLLLLUU_nonneg
                (by linarith) (by linarith) (by linarith) (by linarith)
        · by_cases hlowRow0Cell1RootLLLU : q ≤ ((491 : ℝ) / 128000)
          · exact lowRow0Cell1RootLLLUL_nonneg
              (by linarith) (by linarith) (by linarith) (by linarith)
          · exact lowRow0Cell1RootLLLUU_nonneg
              (by linarith) (by linarith) (by linarith) (by linarith)
      · by_cases hlowRow0Cell1RootLLU : q ≤ ((427 : ℝ) / 64000)
        · by_cases hlowRow0Cell1RootLLUL : q ≤ ((733 : ℝ) / 128000)
          · exact lowRow0Cell1RootLLULL_nonneg
              (by linarith) (by linarith) (by linarith) (by linarith)
          · exact lowRow0Cell1RootLLULU_nonneg
              (by linarith) (by linarith) (by linarith) (by linarith)
        · exact lowRow0Cell1RootLLUU_nonneg
            (by linarith) (by linarith) (by linarith) (by linarith)
    · by_cases hlowRow0Cell1RootLU : q ≤ ((79 : ℝ) / 6400)
      · by_cases hlowRow0Cell1RootLUL : q ≤ ((669 : ℝ) / 64000)
        · exact lowRow0Cell1RootLULL_nonneg
            (by linarith) (by linarith) (by linarith) (by linarith)
        · exact lowRow0Cell1RootLULU_nonneg
            (by linarith) (by linarith) (by linarith) (by linarith)
      · exact lowRow0Cell1RootLUU_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
  · by_cases hlowRow0Cell1RootU : q ≤ ((379 : ℝ) / 16000)
    · by_cases hlowRow0Cell1RootUL : q ≤ ((637 : ℝ) / 32000)
      · exact lowRow0Cell1RootULL_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
      · exact lowRow0Cell1RootULU_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
    · exact lowRow0Cell1RootUU_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow0Cell2RootCover {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((1 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hlowRow0Cell2Root : q ≤ ((3 : ℝ) / 64)
  · exact lowRow0Cell2RootL_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)
  · exact lowRow0Cell2RootU_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow0Cell3RootCover {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((1 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow0Cell3Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow0Cell4RootCover {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((3 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow0Cell4Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow0Cell5RootCover {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((1 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow0Cell5Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow0Cell6RootCover {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((5 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow0Cell6Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow0Cell7RootCover {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((3 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow0Cell7Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow0Cell8RootCover {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((7 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 4)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow0Cell8Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow0Cell9RootCover {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((1 : ℝ) / 4) ≤ q)
    (hqUpper : q ≤ ((9 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow0Cell9Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow0Cell10RootCover {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((9 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow0Cell10Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow0Cell11RootCover {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((5 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((11 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow0Cell11Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow0Cell12RootCover {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((11 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow0Cell12Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow0Cell13RootCover {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((3 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((13 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow0Cell13Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow0Cell14RootCover {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((13 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow0Cell14Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow0Cell15RootCover {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((7 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((15 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow0Cell15Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow0Cell16RootCover {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((15 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow0Cell16Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

/-- One horizontal row of the low endpoint rectangle. -/
theorem endpointCertificateObjective_lowRow0_nonneg {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hendpointCertificateObjective_lowRow0_nonneg16 : q ≤ ((1 : ℝ) / 1000)
  · exact lowRow0Cell0RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow0_nonneg15 : q ≤ ((1 : ℝ) / 32)
  · exact lowRow0Cell1RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow0_nonneg14 : q ≤ ((1 : ℝ) / 16)
  · exact lowRow0Cell2RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow0_nonneg13 : q ≤ ((3 : ℝ) / 32)
  · exact lowRow0Cell3RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow0_nonneg12 : q ≤ ((1 : ℝ) / 8)
  · exact lowRow0Cell4RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow0_nonneg11 : q ≤ ((5 : ℝ) / 32)
  · exact lowRow0Cell5RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow0_nonneg10 : q ≤ ((3 : ℝ) / 16)
  · exact lowRow0Cell6RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow0_nonneg9 : q ≤ ((7 : ℝ) / 32)
  · exact lowRow0Cell7RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow0_nonneg8 : q ≤ ((1 : ℝ) / 4)
  · exact lowRow0Cell8RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow0_nonneg7 : q ≤ ((9 : ℝ) / 32)
  · exact lowRow0Cell9RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow0_nonneg6 : q ≤ ((5 : ℝ) / 16)
  · exact lowRow0Cell10RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow0_nonneg5 : q ≤ ((11 : ℝ) / 32)
  · exact lowRow0Cell11RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow0_nonneg4 : q ≤ ((3 : ℝ) / 8)
  · exact lowRow0Cell12RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow0_nonneg3 : q ≤ ((13 : ℝ) / 32)
  · exact lowRow0Cell13RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow0_nonneg2 : q ≤ ((7 : ℝ) / 16)
  · exact lowRow0Cell14RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow0_nonneg1 : q ≤ ((15 : ℝ) / 32)
  · exact lowRow0Cell15RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  exact lowRow0Cell16RootCover
    (by linarith) (by linarith) (by linarith) (by linarith)

end Frankl
