import Frankl.EndpointTrace.LowRow11Trace0
import Frankl.EndpointTrace.LowRow11Trace1
import Frankl.EndpointTrace.LowRow11Trace2

namespace Frankl

private theorem lowRow11Cell0RootCover {a q : ℝ}
    (haLower : ((5 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((11 : ℝ) / 64))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow11Cell0Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow11Cell1RootCover {a q : ℝ}
    (haLower : ((5 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((11 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 1000) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow11Cell1Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow11Cell2RootCover {a q : ℝ}
    (haLower : ((5 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((11 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow11Cell2Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow11Cell3RootCover {a q : ℝ}
    (haLower : ((5 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((11 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow11Cell3Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow11Cell4RootCover {a q : ℝ}
    (haLower : ((5 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((11 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow11Cell4Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow11Cell5RootCover {a q : ℝ}
    (haLower : ((5 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((11 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow11Cell5Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow11Cell6RootCover {a q : ℝ}
    (haLower : ((5 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((11 : ℝ) / 64))
    (hqLower : ((5 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow11Cell6Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow11Cell7RootCover {a q : ℝ}
    (haLower : ((5 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((11 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow11Cell7Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow11Cell8RootCover {a q : ℝ}
    (haLower : ((5 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((11 : ℝ) / 64))
    (hqLower : ((7 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 4)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow11Cell8Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow11Cell9RootCover {a q : ℝ}
    (haLower : ((5 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((11 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 4) ≤ q)
    (hqUpper : q ≤ ((9 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow11Cell9Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow11Cell10RootCover {a q : ℝ}
    (haLower : ((5 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((11 : ℝ) / 64))
    (hqLower : ((9 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow11Cell10Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow11Cell11RootCover {a q : ℝ}
    (haLower : ((5 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((11 : ℝ) / 64))
    (hqLower : ((5 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((11 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow11Cell11Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow11Cell12RootCover {a q : ℝ}
    (haLower : ((5 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((11 : ℝ) / 64))
    (hqLower : ((11 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow11Cell12Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow11Cell13RootCover {a q : ℝ}
    (haLower : ((5 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((11 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((13 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow11Cell13Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow11Cell14RootCover {a q : ℝ}
    (haLower : ((5 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((11 : ℝ) / 64))
    (hqLower : ((13 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow11Cell14Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow11Cell15RootCover {a q : ℝ}
    (haLower : ((5 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((11 : ℝ) / 64))
    (hqLower : ((7 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((15 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow11Cell15Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow11Cell16RootCover {a q : ℝ}
    (haLower : ((5 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((11 : ℝ) / 64))
    (hqLower : ((15 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow11Cell16Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

/-- One horizontal row of the low endpoint rectangle. -/
theorem endpointCertificateObjective_lowRow11_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((11 : ℝ) / 64))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hendpointCertificateObjective_lowRow11_nonneg16 : q ≤ ((1 : ℝ) / 1000)
  · exact lowRow11Cell0RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow11_nonneg15 : q ≤ ((1 : ℝ) / 32)
  · exact lowRow11Cell1RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow11_nonneg14 : q ≤ ((1 : ℝ) / 16)
  · exact lowRow11Cell2RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow11_nonneg13 : q ≤ ((3 : ℝ) / 32)
  · exact lowRow11Cell3RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow11_nonneg12 : q ≤ ((1 : ℝ) / 8)
  · exact lowRow11Cell4RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow11_nonneg11 : q ≤ ((5 : ℝ) / 32)
  · exact lowRow11Cell5RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow11_nonneg10 : q ≤ ((3 : ℝ) / 16)
  · exact lowRow11Cell6RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow11_nonneg9 : q ≤ ((7 : ℝ) / 32)
  · exact lowRow11Cell7RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow11_nonneg8 : q ≤ ((1 : ℝ) / 4)
  · exact lowRow11Cell8RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow11_nonneg7 : q ≤ ((9 : ℝ) / 32)
  · exact lowRow11Cell9RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow11_nonneg6 : q ≤ ((5 : ℝ) / 16)
  · exact lowRow11Cell10RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow11_nonneg5 : q ≤ ((11 : ℝ) / 32)
  · exact lowRow11Cell11RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow11_nonneg4 : q ≤ ((3 : ℝ) / 8)
  · exact lowRow11Cell12RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow11_nonneg3 : q ≤ ((13 : ℝ) / 32)
  · exact lowRow11Cell13RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow11_nonneg2 : q ≤ ((7 : ℝ) / 16)
  · exact lowRow11Cell14RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow11_nonneg1 : q ≤ ((15 : ℝ) / 32)
  · exact lowRow11Cell15RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  exact lowRow11Cell16RootCover
    (by linarith) (by linarith) (by linarith) (by linarith)

end Frankl
