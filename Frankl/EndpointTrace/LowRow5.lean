import Frankl.EndpointTrace.LowRow5Trace0
import Frankl.EndpointTrace.LowRow5Trace1

namespace Frankl

private theorem lowRow5Cell0RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 64))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow5Cell0Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow5Cell1RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 1000) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow5Cell1Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow5Cell2RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow5Cell2Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow5Cell3RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow5Cell3Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow5Cell4RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow5Cell4Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow5Cell5RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow5Cell5Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow5Cell6RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 64))
    (hqLower : ((5 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow5Cell6Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow5Cell7RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow5Cell7Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow5Cell8RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 64))
    (hqLower : ((7 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 4)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow5Cell8Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow5Cell9RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 4) ≤ q)
    (hqUpper : q ≤ ((9 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow5Cell9Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow5Cell10RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 64))
    (hqLower : ((9 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow5Cell10Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow5Cell11RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 64))
    (hqLower : ((5 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((11 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow5Cell11Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow5Cell12RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 64))
    (hqLower : ((11 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow5Cell12Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow5Cell13RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((13 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow5Cell13Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow5Cell14RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 64))
    (hqLower : ((13 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow5Cell14Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow5Cell15RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 64))
    (hqLower : ((7 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((15 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow5Cell15Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow5Cell16RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 64))
    (hqLower : ((15 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow5Cell16Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

/-- One horizontal row of the low endpoint rectangle. -/
theorem endpointCertificateObjective_lowRow5_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 64))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hendpointCertificateObjective_lowRow5_nonneg16 : q ≤ ((1 : ℝ) / 1000)
  · exact lowRow5Cell0RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow5_nonneg15 : q ≤ ((1 : ℝ) / 32)
  · exact lowRow5Cell1RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow5_nonneg14 : q ≤ ((1 : ℝ) / 16)
  · exact lowRow5Cell2RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow5_nonneg13 : q ≤ ((3 : ℝ) / 32)
  · exact lowRow5Cell3RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow5_nonneg12 : q ≤ ((1 : ℝ) / 8)
  · exact lowRow5Cell4RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow5_nonneg11 : q ≤ ((5 : ℝ) / 32)
  · exact lowRow5Cell5RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow5_nonneg10 : q ≤ ((3 : ℝ) / 16)
  · exact lowRow5Cell6RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow5_nonneg9 : q ≤ ((7 : ℝ) / 32)
  · exact lowRow5Cell7RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow5_nonneg8 : q ≤ ((1 : ℝ) / 4)
  · exact lowRow5Cell8RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow5_nonneg7 : q ≤ ((9 : ℝ) / 32)
  · exact lowRow5Cell9RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow5_nonneg6 : q ≤ ((5 : ℝ) / 16)
  · exact lowRow5Cell10RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow5_nonneg5 : q ≤ ((11 : ℝ) / 32)
  · exact lowRow5Cell11RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow5_nonneg4 : q ≤ ((3 : ℝ) / 8)
  · exact lowRow5Cell12RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow5_nonneg3 : q ≤ ((13 : ℝ) / 32)
  · exact lowRow5Cell13RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow5_nonneg2 : q ≤ ((7 : ℝ) / 16)
  · exact lowRow5Cell14RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow5_nonneg1 : q ≤ ((15 : ℝ) / 32)
  · exact lowRow5Cell15RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  exact lowRow5Cell16RootCover
    (by linarith) (by linarith) (by linarith) (by linarith)

end Frankl
