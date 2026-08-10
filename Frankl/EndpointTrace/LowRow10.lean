import Frankl.EndpointTrace.LowRow10Trace0
import Frankl.EndpointTrace.LowRow10Trace1
import Frankl.EndpointTrace.LowRow10Trace2

namespace Frankl

private theorem lowRow10Cell0RootCover {a q : ℝ}
    (haLower : ((9 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 32))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow10Cell0Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow10Cell1RootCover {a q : ℝ}
    (haLower : ((9 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 1000) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow10Cell1Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow10Cell2RootCover {a q : ℝ}
    (haLower : ((9 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow10Cell2Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow10Cell3RootCover {a q : ℝ}
    (haLower : ((9 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow10Cell3Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow10Cell4RootCover {a q : ℝ}
    (haLower : ((9 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 32))
    (hqLower : ((3 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow10Cell4Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow10Cell5RootCover {a q : ℝ}
    (haLower : ((9 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow10Cell5Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow10Cell6RootCover {a q : ℝ}
    (haLower : ((9 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 32))
    (hqLower : ((5 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow10Cell6Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow10Cell7RootCover {a q : ℝ}
    (haLower : ((9 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 32))
    (hqLower : ((3 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow10Cell7Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow10Cell8RootCover {a q : ℝ}
    (haLower : ((9 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 32))
    (hqLower : ((7 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 4)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow10Cell8Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow10Cell9RootCover {a q : ℝ}
    (haLower : ((9 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 4) ≤ q)
    (hqUpper : q ≤ ((9 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow10Cell9Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow10Cell10RootCover {a q : ℝ}
    (haLower : ((9 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 32))
    (hqLower : ((9 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow10Cell10Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow10Cell11RootCover {a q : ℝ}
    (haLower : ((9 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 32))
    (hqLower : ((5 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((11 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow10Cell11Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow10Cell12RootCover {a q : ℝ}
    (haLower : ((9 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 32))
    (hqLower : ((11 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow10Cell12Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow10Cell13RootCover {a q : ℝ}
    (haLower : ((9 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 32))
    (hqLower : ((3 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((13 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow10Cell13Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow10Cell14RootCover {a q : ℝ}
    (haLower : ((9 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 32))
    (hqLower : ((13 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow10Cell14Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow10Cell15RootCover {a q : ℝ}
    (haLower : ((9 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 32))
    (hqLower : ((7 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((15 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow10Cell15Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow10Cell16RootCover {a q : ℝ}
    (haLower : ((9 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 32))
    (hqLower : ((15 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow10Cell16Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

/-- One horizontal row of the low endpoint rectangle. -/
theorem endpointCertificateObjective_lowRow10_nonneg {a q : ℝ}
    (haLower : ((9 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 32))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hendpointCertificateObjective_lowRow10_nonneg16 : q ≤ ((1 : ℝ) / 1000)
  · exact lowRow10Cell0RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow10_nonneg15 : q ≤ ((1 : ℝ) / 32)
  · exact lowRow10Cell1RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow10_nonneg14 : q ≤ ((1 : ℝ) / 16)
  · exact lowRow10Cell2RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow10_nonneg13 : q ≤ ((3 : ℝ) / 32)
  · exact lowRow10Cell3RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow10_nonneg12 : q ≤ ((1 : ℝ) / 8)
  · exact lowRow10Cell4RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow10_nonneg11 : q ≤ ((5 : ℝ) / 32)
  · exact lowRow10Cell5RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow10_nonneg10 : q ≤ ((3 : ℝ) / 16)
  · exact lowRow10Cell6RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow10_nonneg9 : q ≤ ((7 : ℝ) / 32)
  · exact lowRow10Cell7RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow10_nonneg8 : q ≤ ((1 : ℝ) / 4)
  · exact lowRow10Cell8RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow10_nonneg7 : q ≤ ((9 : ℝ) / 32)
  · exact lowRow10Cell9RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow10_nonneg6 : q ≤ ((5 : ℝ) / 16)
  · exact lowRow10Cell10RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow10_nonneg5 : q ≤ ((11 : ℝ) / 32)
  · exact lowRow10Cell11RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow10_nonneg4 : q ≤ ((3 : ℝ) / 8)
  · exact lowRow10Cell12RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow10_nonneg3 : q ≤ ((13 : ℝ) / 32)
  · exact lowRow10Cell13RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow10_nonneg2 : q ≤ ((7 : ℝ) / 16)
  · exact lowRow10Cell14RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow10_nonneg1 : q ≤ ((15 : ℝ) / 32)
  · exact lowRow10Cell15RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  exact lowRow10Cell16RootCover
    (by linarith) (by linarith) (by linarith) (by linarith)

end Frankl
