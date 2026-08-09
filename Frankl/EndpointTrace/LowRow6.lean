import Frankl.EndpointTrace.LowRow6Trace0
import Frankl.EndpointTrace.LowRow6Trace1

namespace Frankl

private theorem lowRow6Cell0RootCover {a q : ℝ}
    (haLower : ((5 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 32))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow6Cell0Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow6Cell1RootCover {a q : ℝ}
    (haLower : ((5 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 1000) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow6Cell1Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow6Cell2RootCover {a q : ℝ}
    (haLower : ((5 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow6Cell2Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow6Cell3RootCover {a q : ℝ}
    (haLower : ((5 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow6Cell3Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow6Cell4RootCover {a q : ℝ}
    (haLower : ((5 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 32))
    (hqLower : ((3 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow6Cell4Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow6Cell5RootCover {a q : ℝ}
    (haLower : ((5 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow6Cell5Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow6Cell6RootCover {a q : ℝ}
    (haLower : ((5 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 32))
    (hqLower : ((5 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow6Cell6Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow6Cell7RootCover {a q : ℝ}
    (haLower : ((5 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 32))
    (hqLower : ((3 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow6Cell7Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow6Cell8RootCover {a q : ℝ}
    (haLower : ((5 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 32))
    (hqLower : ((7 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 4)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow6Cell8Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow6Cell9RootCover {a q : ℝ}
    (haLower : ((5 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 4) ≤ q)
    (hqUpper : q ≤ ((9 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow6Cell9Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow6Cell10RootCover {a q : ℝ}
    (haLower : ((5 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 32))
    (hqLower : ((9 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow6Cell10Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow6Cell11RootCover {a q : ℝ}
    (haLower : ((5 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 32))
    (hqLower : ((5 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((11 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow6Cell11Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow6Cell12RootCover {a q : ℝ}
    (haLower : ((5 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 32))
    (hqLower : ((11 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow6Cell12Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow6Cell13RootCover {a q : ℝ}
    (haLower : ((5 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 32))
    (hqLower : ((3 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((13 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow6Cell13Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow6Cell14RootCover {a q : ℝ}
    (haLower : ((5 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 32))
    (hqLower : ((13 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow6Cell14Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow6Cell15RootCover {a q : ℝ}
    (haLower : ((5 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 32))
    (hqLower : ((7 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((15 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow6Cell15Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow6Cell16RootCover {a q : ℝ}
    (haLower : ((5 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 32))
    (hqLower : ((15 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow6Cell16Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

/-- One horizontal row of the low endpoint rectangle. -/
theorem endpointCertificateObjective_lowRow6_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 32))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hendpointCertificateObjective_lowRow6_nonneg16 : q ≤ ((1 : ℝ) / 1000)
  · exact lowRow6Cell0RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow6_nonneg15 : q ≤ ((1 : ℝ) / 32)
  · exact lowRow6Cell1RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow6_nonneg14 : q ≤ ((1 : ℝ) / 16)
  · exact lowRow6Cell2RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow6_nonneg13 : q ≤ ((3 : ℝ) / 32)
  · exact lowRow6Cell3RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow6_nonneg12 : q ≤ ((1 : ℝ) / 8)
  · exact lowRow6Cell4RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow6_nonneg11 : q ≤ ((5 : ℝ) / 32)
  · exact lowRow6Cell5RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow6_nonneg10 : q ≤ ((3 : ℝ) / 16)
  · exact lowRow6Cell6RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow6_nonneg9 : q ≤ ((7 : ℝ) / 32)
  · exact lowRow6Cell7RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow6_nonneg8 : q ≤ ((1 : ℝ) / 4)
  · exact lowRow6Cell8RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow6_nonneg7 : q ≤ ((9 : ℝ) / 32)
  · exact lowRow6Cell9RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow6_nonneg6 : q ≤ ((5 : ℝ) / 16)
  · exact lowRow6Cell10RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow6_nonneg5 : q ≤ ((11 : ℝ) / 32)
  · exact lowRow6Cell11RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow6_nonneg4 : q ≤ ((3 : ℝ) / 8)
  · exact lowRow6Cell12RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow6_nonneg3 : q ≤ ((13 : ℝ) / 32)
  · exact lowRow6Cell13RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow6_nonneg2 : q ≤ ((7 : ℝ) / 16)
  · exact lowRow6Cell14RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow6_nonneg1 : q ≤ ((15 : ℝ) / 32)
  · exact lowRow6Cell15RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  exact lowRow6Cell16RootCover
    (by linarith) (by linarith) (by linarith) (by linarith)

end Frankl
