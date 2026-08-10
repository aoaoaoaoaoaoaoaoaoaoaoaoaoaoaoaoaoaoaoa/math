import Frankl.EndpointTrace.LowRow14Trace0
import Frankl.EndpointTrace.LowRow14Trace1
import Frankl.EndpointTrace.LowRow14Trace2
import Frankl.EndpointTrace.LowRow14Trace3

namespace Frankl

private theorem lowRow14Cell0RootCover {a q : ℝ}
    (haLower : ((13 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 32))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow14Cell0Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow14Cell1RootCover {a q : ℝ}
    (haLower : ((13 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 1000) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow14Cell1Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow14Cell2RootCover {a q : ℝ}
    (haLower : ((13 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow14Cell2Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow14Cell3RootCover {a q : ℝ}
    (haLower : ((13 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow14Cell3Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow14Cell4RootCover {a q : ℝ}
    (haLower : ((13 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 32))
    (hqLower : ((3 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow14Cell4Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow14Cell5RootCover {a q : ℝ}
    (haLower : ((13 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow14Cell5Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow14Cell6RootCover {a q : ℝ}
    (haLower : ((13 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 32))
    (hqLower : ((5 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow14Cell6Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow14Cell7RootCover {a q : ℝ}
    (haLower : ((13 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 32))
    (hqLower : ((3 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow14Cell7Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow14Cell8RootCover {a q : ℝ}
    (haLower : ((13 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 32))
    (hqLower : ((7 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 4)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow14Cell8Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow14Cell9RootCover {a q : ℝ}
    (haLower : ((13 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 4) ≤ q)
    (hqUpper : q ≤ ((9 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow14Cell9Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow14Cell10RootCover {a q : ℝ}
    (haLower : ((13 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 32))
    (hqLower : ((9 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow14Cell10Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow14Cell11RootCover {a q : ℝ}
    (haLower : ((13 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 32))
    (hqLower : ((5 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((11 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow14Cell11Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow14Cell12RootCover {a q : ℝ}
    (haLower : ((13 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 32))
    (hqLower : ((11 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow14Cell12Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow14Cell13RootCover {a q : ℝ}
    (haLower : ((13 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 32))
    (hqLower : ((3 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((13 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow14Cell13Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow14Cell14RootCover {a q : ℝ}
    (haLower : ((13 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 32))
    (hqLower : ((13 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow14Cell14Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow14Cell15RootCover {a q : ℝ}
    (haLower : ((13 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 32))
    (hqLower : ((7 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((15 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow14Cell15Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow14Cell16RootCover {a q : ℝ}
    (haLower : ((13 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 32))
    (hqLower : ((15 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow14Cell16Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

/-- One horizontal row of the low endpoint rectangle. -/
theorem endpointCertificateObjective_lowRow14_nonneg {a q : ℝ}
    (haLower : ((13 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 32))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hendpointCertificateObjective_lowRow14_nonneg16 : q ≤ ((1 : ℝ) / 1000)
  · exact lowRow14Cell0RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow14_nonneg15 : q ≤ ((1 : ℝ) / 32)
  · exact lowRow14Cell1RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow14_nonneg14 : q ≤ ((1 : ℝ) / 16)
  · exact lowRow14Cell2RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow14_nonneg13 : q ≤ ((3 : ℝ) / 32)
  · exact lowRow14Cell3RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow14_nonneg12 : q ≤ ((1 : ℝ) / 8)
  · exact lowRow14Cell4RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow14_nonneg11 : q ≤ ((5 : ℝ) / 32)
  · exact lowRow14Cell5RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow14_nonneg10 : q ≤ ((3 : ℝ) / 16)
  · exact lowRow14Cell6RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow14_nonneg9 : q ≤ ((7 : ℝ) / 32)
  · exact lowRow14Cell7RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow14_nonneg8 : q ≤ ((1 : ℝ) / 4)
  · exact lowRow14Cell8RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow14_nonneg7 : q ≤ ((9 : ℝ) / 32)
  · exact lowRow14Cell9RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow14_nonneg6 : q ≤ ((5 : ℝ) / 16)
  · exact lowRow14Cell10RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow14_nonneg5 : q ≤ ((11 : ℝ) / 32)
  · exact lowRow14Cell11RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow14_nonneg4 : q ≤ ((3 : ℝ) / 8)
  · exact lowRow14Cell12RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow14_nonneg3 : q ≤ ((13 : ℝ) / 32)
  · exact lowRow14Cell13RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow14_nonneg2 : q ≤ ((7 : ℝ) / 16)
  · exact lowRow14Cell14RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow14_nonneg1 : q ≤ ((15 : ℝ) / 32)
  · exact lowRow14Cell15RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  exact lowRow14Cell16RootCover
    (by linarith) (by linarith) (by linarith) (by linarith)

end Frankl
