import Frankl.EndpointTrace.LowRow2Trace0
import Frankl.EndpointTrace.LowRow2Trace1
import Frankl.EndpointTrace.LowRow2Trace2

namespace Frankl

private theorem lowRow2Cell0RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 32))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hlowRow2Cell0Root : a ≤ ((3 : ℝ) / 128)
  · by_cases hlowRow2Cell0RootL : a ≤ ((5 : ℝ) / 256)
    · exact lowRow2Cell0RootLL_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)
    · exact lowRow2Cell0RootLU_nonneg
        (by linarith) (by linarith) (by linarith) (by linarith)
  · exact lowRow2Cell0RootU_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow2Cell1RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 1000) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow2Cell1Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow2Cell2RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow2Cell2Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow2Cell3RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow2Cell3Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow2Cell4RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 32))
    (hqLower : ((3 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow2Cell4Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow2Cell5RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow2Cell5Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow2Cell6RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 32))
    (hqLower : ((5 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow2Cell6Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow2Cell7RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 32))
    (hqLower : ((3 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow2Cell7Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow2Cell8RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 32))
    (hqLower : ((7 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 4)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow2Cell8Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow2Cell9RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 4) ≤ q)
    (hqUpper : q ≤ ((9 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow2Cell9Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow2Cell10RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 32))
    (hqLower : ((9 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow2Cell10Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow2Cell11RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 32))
    (hqLower : ((5 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((11 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow2Cell11Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow2Cell12RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 32))
    (hqLower : ((11 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow2Cell12Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow2Cell13RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 32))
    (hqLower : ((3 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((13 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow2Cell13Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow2Cell14RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 32))
    (hqLower : ((13 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow2Cell14Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow2Cell15RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 32))
    (hqLower : ((7 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((15 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow2Cell15Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow2Cell16RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 32))
    (hqLower : ((15 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow2Cell16Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

/-- One horizontal row of the low endpoint rectangle. -/
theorem endpointCertificateObjective_lowRow2_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 32))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hendpointCertificateObjective_lowRow2_nonneg16 : q ≤ ((1 : ℝ) / 1000)
  · exact lowRow2Cell0RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow2_nonneg15 : q ≤ ((1 : ℝ) / 32)
  · exact lowRow2Cell1RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow2_nonneg14 : q ≤ ((1 : ℝ) / 16)
  · exact lowRow2Cell2RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow2_nonneg13 : q ≤ ((3 : ℝ) / 32)
  · exact lowRow2Cell3RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow2_nonneg12 : q ≤ ((1 : ℝ) / 8)
  · exact lowRow2Cell4RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow2_nonneg11 : q ≤ ((5 : ℝ) / 32)
  · exact lowRow2Cell5RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow2_nonneg10 : q ≤ ((3 : ℝ) / 16)
  · exact lowRow2Cell6RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow2_nonneg9 : q ≤ ((7 : ℝ) / 32)
  · exact lowRow2Cell7RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow2_nonneg8 : q ≤ ((1 : ℝ) / 4)
  · exact lowRow2Cell8RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow2_nonneg7 : q ≤ ((9 : ℝ) / 32)
  · exact lowRow2Cell9RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow2_nonneg6 : q ≤ ((5 : ℝ) / 16)
  · exact lowRow2Cell10RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow2_nonneg5 : q ≤ ((11 : ℝ) / 32)
  · exact lowRow2Cell11RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow2_nonneg4 : q ≤ ((3 : ℝ) / 8)
  · exact lowRow2Cell12RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow2_nonneg3 : q ≤ ((13 : ℝ) / 32)
  · exact lowRow2Cell13RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow2_nonneg2 : q ≤ ((7 : ℝ) / 16)
  · exact lowRow2Cell14RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow2_nonneg1 : q ≤ ((15 : ℝ) / 32)
  · exact lowRow2Cell15RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  exact lowRow2Cell16RootCover
    (by linarith) (by linarith) (by linarith) (by linarith)

end Frankl
