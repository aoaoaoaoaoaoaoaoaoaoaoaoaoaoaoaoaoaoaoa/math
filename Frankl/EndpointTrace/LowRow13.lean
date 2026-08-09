import Frankl.EndpointTrace.LowRow13Trace0
import Frankl.EndpointTrace.LowRow13Trace1
import Frankl.EndpointTrace.LowRow13Trace2

namespace Frankl

private theorem lowRow13Cell0RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 64))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow13Cell0Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow13Cell1RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 1000) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow13Cell1Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow13Cell2RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow13Cell2Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow13Cell3RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow13Cell3Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow13Cell4RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow13Cell4Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow13Cell5RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow13Cell5Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow13Cell6RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 64))
    (hqLower : ((5 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow13Cell6Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow13Cell7RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow13Cell7Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow13Cell8RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 64))
    (hqLower : ((7 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 4)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow13Cell8Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow13Cell9RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 4) ≤ q)
    (hqUpper : q ≤ ((9 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow13Cell9Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow13Cell10RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 64))
    (hqLower : ((9 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow13Cell10Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow13Cell11RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 64))
    (hqLower : ((5 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((11 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow13Cell11Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow13Cell12RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 64))
    (hqLower : ((11 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow13Cell12Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow13Cell13RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((13 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow13Cell13Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow13Cell14RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 64))
    (hqLower : ((13 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow13Cell14Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow13Cell15RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 64))
    (hqLower : ((7 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((15 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow13Cell15Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow13Cell16RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 64))
    (hqLower : ((15 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow13Cell16Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

/-- One horizontal row of the low endpoint rectangle. -/
theorem endpointCertificateObjective_lowRow13_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 64))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hendpointCertificateObjective_lowRow13_nonneg16 : q ≤ ((1 : ℝ) / 1000)
  · exact lowRow13Cell0RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow13_nonneg15 : q ≤ ((1 : ℝ) / 32)
  · exact lowRow13Cell1RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow13_nonneg14 : q ≤ ((1 : ℝ) / 16)
  · exact lowRow13Cell2RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow13_nonneg13 : q ≤ ((3 : ℝ) / 32)
  · exact lowRow13Cell3RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow13_nonneg12 : q ≤ ((1 : ℝ) / 8)
  · exact lowRow13Cell4RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow13_nonneg11 : q ≤ ((5 : ℝ) / 32)
  · exact lowRow13Cell5RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow13_nonneg10 : q ≤ ((3 : ℝ) / 16)
  · exact lowRow13Cell6RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow13_nonneg9 : q ≤ ((7 : ℝ) / 32)
  · exact lowRow13Cell7RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow13_nonneg8 : q ≤ ((1 : ℝ) / 4)
  · exact lowRow13Cell8RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow13_nonneg7 : q ≤ ((9 : ℝ) / 32)
  · exact lowRow13Cell9RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow13_nonneg6 : q ≤ ((5 : ℝ) / 16)
  · exact lowRow13Cell10RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow13_nonneg5 : q ≤ ((11 : ℝ) / 32)
  · exact lowRow13Cell11RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow13_nonneg4 : q ≤ ((3 : ℝ) / 8)
  · exact lowRow13Cell12RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow13_nonneg3 : q ≤ ((13 : ℝ) / 32)
  · exact lowRow13Cell13RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow13_nonneg2 : q ≤ ((7 : ℝ) / 16)
  · exact lowRow13Cell14RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow13_nonneg1 : q ≤ ((15 : ℝ) / 32)
  · exact lowRow13Cell15RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  exact lowRow13Cell16RootCover
    (by linarith) (by linarith) (by linarith) (by linarith)

end Frankl
