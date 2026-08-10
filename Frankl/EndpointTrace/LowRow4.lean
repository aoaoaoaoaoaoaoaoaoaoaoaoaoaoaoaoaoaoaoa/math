import Frankl.EndpointTrace.LowRow4Trace0
import Frankl.EndpointTrace.LowRow4Trace1

namespace Frankl

private theorem lowRow4Cell0RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 16))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow4Cell0Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow4Cell1RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 16))
    (hqLower : ((1 : ℝ) / 1000) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow4Cell1Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow4Cell2RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 16))
    (hqLower : ((1 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow4Cell2Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow4Cell3RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 16))
    (hqLower : ((1 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow4Cell3Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow4Cell4RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 16))
    (hqLower : ((3 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow4Cell4Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow4Cell5RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 16))
    (hqLower : ((1 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow4Cell5Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow4Cell6RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 16))
    (hqLower : ((5 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow4Cell6Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow4Cell7RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 16))
    (hqLower : ((3 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow4Cell7Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow4Cell8RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 16))
    (hqLower : ((7 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 4)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow4Cell8Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow4Cell9RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 16))
    (hqLower : ((1 : ℝ) / 4) ≤ q)
    (hqUpper : q ≤ ((9 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow4Cell9Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow4Cell10RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 16))
    (hqLower : ((9 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow4Cell10Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow4Cell11RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 16))
    (hqLower : ((5 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((11 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow4Cell11Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow4Cell12RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 16))
    (hqLower : ((11 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow4Cell12Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow4Cell13RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 16))
    (hqLower : ((3 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((13 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow4Cell13Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow4Cell14RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 16))
    (hqLower : ((13 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow4Cell14Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow4Cell15RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 16))
    (hqLower : ((7 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((15 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow4Cell15Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow4Cell16RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 16))
    (hqLower : ((15 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow4Cell16Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

/-- One horizontal row of the low endpoint rectangle. -/
theorem endpointCertificateObjective_lowRow4_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 16))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hendpointCertificateObjective_lowRow4_nonneg16 : q ≤ ((1 : ℝ) / 1000)
  · exact lowRow4Cell0RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow4_nonneg15 : q ≤ ((1 : ℝ) / 32)
  · exact lowRow4Cell1RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow4_nonneg14 : q ≤ ((1 : ℝ) / 16)
  · exact lowRow4Cell2RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow4_nonneg13 : q ≤ ((3 : ℝ) / 32)
  · exact lowRow4Cell3RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow4_nonneg12 : q ≤ ((1 : ℝ) / 8)
  · exact lowRow4Cell4RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow4_nonneg11 : q ≤ ((5 : ℝ) / 32)
  · exact lowRow4Cell5RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow4_nonneg10 : q ≤ ((3 : ℝ) / 16)
  · exact lowRow4Cell6RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow4_nonneg9 : q ≤ ((7 : ℝ) / 32)
  · exact lowRow4Cell7RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow4_nonneg8 : q ≤ ((1 : ℝ) / 4)
  · exact lowRow4Cell8RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow4_nonneg7 : q ≤ ((9 : ℝ) / 32)
  · exact lowRow4Cell9RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow4_nonneg6 : q ≤ ((5 : ℝ) / 16)
  · exact lowRow4Cell10RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow4_nonneg5 : q ≤ ((11 : ℝ) / 32)
  · exact lowRow4Cell11RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow4_nonneg4 : q ≤ ((3 : ℝ) / 8)
  · exact lowRow4Cell12RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow4_nonneg3 : q ≤ ((13 : ℝ) / 32)
  · exact lowRow4Cell13RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow4_nonneg2 : q ≤ ((7 : ℝ) / 16)
  · exact lowRow4Cell14RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow4_nonneg1 : q ≤ ((15 : ℝ) / 32)
  · exact lowRow4Cell15RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  exact lowRow4Cell16RootCover
    (by linarith) (by linarith) (by linarith) (by linarith)

end Frankl
