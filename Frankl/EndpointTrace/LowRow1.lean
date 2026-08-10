import Frankl.EndpointTrace.LowRow1Trace0
import Frankl.EndpointTrace.LowRow1Trace1
import Frankl.EndpointTrace.LowRow1Trace2
import Frankl.EndpointTrace.LowRow1Trace3
import Frankl.EndpointTrace.LowRow1Trace4
import Frankl.EndpointTrace.LowRow1Trace5
import Frankl.EndpointTrace.LowRow1Trace6

namespace Frankl

private theorem lowRow1Cell0RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hlowRow1Cell0Root : a ≤ ((133 : ℝ) / 16000)
  · by_cases hlowRow1Cell0RootL : a ≤ ((149 : ℝ) / 32000)
    · by_cases hlowRow1Cell0RootLL : a ≤ ((181 : ℝ) / 64000)
      · by_cases hlowRow1Cell0RootLLL : a ≤ ((49 : ℝ) / 25600)
        · by_cases hlowRow1Cell0RootLLLL : q ≤ ((1 : ℝ) / 2000)
          · by_cases hlowRow1Cell0RootLLLLL : a ≤ ((373 : ℝ) / 256000)
            · by_cases hlowRow1Cell0RootLLLLLL : q ≤ ((1 : ℝ) / 4000)
              · exact lowRow1Cell0RootLLLLLLL_nonneg
                  (by linarith) (by linarith) (by linarith) (by linarith)
              · exact lowRow1Cell0RootLLLLLLU_nonneg
                  (by linarith) (by linarith) (by linarith) (by linarith)
            · exact lowRow1Cell0RootLLLLLU_nonneg
                (by linarith) (by linarith) (by linarith) (by linarith)
          · exact lowRow1Cell0RootLLLLU_nonneg
              (by linarith) (by linarith) (by linarith) (by linarith)
        · by_cases hlowRow1Cell0RootLLLU : q ≤ ((1 : ℝ) / 2000)
          · exact lowRow1Cell0RootLLLUL_nonneg
              (by linarith) (by linarith) (by linarith) (by linarith)
          · exact lowRow1Cell0RootLLLUU_nonneg
              (by linarith) (by linarith) (by linarith) (by linarith)
      · by_cases hlowRow1Cell0RootLLU : a ≤ ((479 : ℝ) / 128000)
        · exact lowRow1Cell0RootLLUL_nonneg
            (by linarith) (by linarith) (by linarith) (by linarith)
        · exact lowRow1Cell0RootLLUU_nonneg
            (by linarith) (by linarith) (by linarith) (by linarith)
    · by_cases hlowRow1Cell0RootLU : a ≤ ((83 : ℝ) / 12800)
      · exact lowRow1Cell0RootLUL_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
      · exact lowRow1Cell0RootLUU_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
  · by_cases hlowRow1Cell0RootU : a ≤ ((383 : ℝ) / 32000)
    · exact lowRow1Cell0RootUL_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)
    · exact lowRow1Cell0RootUU_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow1Cell1RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 1000) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hlowRow1Cell1Root : q ≤ ((129 : ℝ) / 8000)
  · by_cases hlowRow1Cell1RootL : q ≤ ((137 : ℝ) / 16000)
    · by_cases hlowRow1Cell1RootLL : a ≤ ((133 : ℝ) / 16000)
      · exact lowRow1Cell1RootLLL_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
      · exact lowRow1Cell1RootLLU_nonneg
          (by linarith) (by linarith) (by linarith) (by linarith)
    · exact lowRow1Cell1RootLU_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)
  · exact lowRow1Cell1RootU_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow1Cell2RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow1Cell2Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow1Cell3RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow1Cell3Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow1Cell4RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow1Cell4Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow1Cell5RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow1Cell5Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow1Cell6RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((5 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow1Cell6Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow1Cell7RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow1Cell7Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow1Cell8RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((7 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 4)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow1Cell8Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow1Cell9RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 4) ≤ q)
    (hqUpper : q ≤ ((9 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow1Cell9Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow1Cell10RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((9 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow1Cell10Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow1Cell11RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((5 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((11 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow1Cell11Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow1Cell12RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((11 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow1Cell12Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow1Cell13RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((13 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow1Cell13Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow1Cell14RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((13 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow1Cell14Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow1Cell15RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((7 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((15 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow1Cell15Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow1Cell16RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((15 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow1Cell16Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

/-- One horizontal row of the low endpoint rectangle. -/
theorem endpointCertificateObjective_lowRow1_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hendpointCertificateObjective_lowRow1_nonneg16 : q ≤ ((1 : ℝ) / 1000)
  · exact lowRow1Cell0RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow1_nonneg15 : q ≤ ((1 : ℝ) / 32)
  · exact lowRow1Cell1RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow1_nonneg14 : q ≤ ((1 : ℝ) / 16)
  · exact lowRow1Cell2RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow1_nonneg13 : q ≤ ((3 : ℝ) / 32)
  · exact lowRow1Cell3RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow1_nonneg12 : q ≤ ((1 : ℝ) / 8)
  · exact lowRow1Cell4RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow1_nonneg11 : q ≤ ((5 : ℝ) / 32)
  · exact lowRow1Cell5RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow1_nonneg10 : q ≤ ((3 : ℝ) / 16)
  · exact lowRow1Cell6RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow1_nonneg9 : q ≤ ((7 : ℝ) / 32)
  · exact lowRow1Cell7RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow1_nonneg8 : q ≤ ((1 : ℝ) / 4)
  · exact lowRow1Cell8RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow1_nonneg7 : q ≤ ((9 : ℝ) / 32)
  · exact lowRow1Cell9RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow1_nonneg6 : q ≤ ((5 : ℝ) / 16)
  · exact lowRow1Cell10RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow1_nonneg5 : q ≤ ((11 : ℝ) / 32)
  · exact lowRow1Cell11RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow1_nonneg4 : q ≤ ((3 : ℝ) / 8)
  · exact lowRow1Cell12RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow1_nonneg3 : q ≤ ((13 : ℝ) / 32)
  · exact lowRow1Cell13RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow1_nonneg2 : q ≤ ((7 : ℝ) / 16)
  · exact lowRow1Cell14RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow1_nonneg1 : q ≤ ((15 : ℝ) / 32)
  · exact lowRow1Cell15RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  exact lowRow1Cell16RootCover
    (by linarith) (by linarith) (by linarith) (by linarith)

end Frankl
