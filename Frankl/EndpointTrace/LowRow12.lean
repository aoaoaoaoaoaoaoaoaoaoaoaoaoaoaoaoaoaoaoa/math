import Frankl.EndpointTrace.LowRow12Trace0
import Frankl.EndpointTrace.LowRow12Trace1
import Frankl.EndpointTrace.LowRow12Trace2

namespace Frankl

private theorem lowRow12Cell0RootCover {a q : ℝ}
    (haLower : ((11 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 16))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow12Cell0Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow12Cell1RootCover {a q : ℝ}
    (haLower : ((11 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 16))
    (hqLower : ((1 : ℝ) / 1000) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow12Cell1Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow12Cell2RootCover {a q : ℝ}
    (haLower : ((11 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 16))
    (hqLower : ((1 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow12Cell2Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow12Cell3RootCover {a q : ℝ}
    (haLower : ((11 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 16))
    (hqLower : ((1 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow12Cell3Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow12Cell4RootCover {a q : ℝ}
    (haLower : ((11 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 16))
    (hqLower : ((3 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow12Cell4Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow12Cell5RootCover {a q : ℝ}
    (haLower : ((11 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 16))
    (hqLower : ((1 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow12Cell5Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow12Cell6RootCover {a q : ℝ}
    (haLower : ((11 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 16))
    (hqLower : ((5 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow12Cell6Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow12Cell7RootCover {a q : ℝ}
    (haLower : ((11 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 16))
    (hqLower : ((3 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow12Cell7Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow12Cell8RootCover {a q : ℝ}
    (haLower : ((11 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 16))
    (hqLower : ((7 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 4)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow12Cell8Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow12Cell9RootCover {a q : ℝ}
    (haLower : ((11 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 16))
    (hqLower : ((1 : ℝ) / 4) ≤ q)
    (hqUpper : q ≤ ((9 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow12Cell9Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow12Cell10RootCover {a q : ℝ}
    (haLower : ((11 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 16))
    (hqLower : ((9 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow12Cell10Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow12Cell11RootCover {a q : ℝ}
    (haLower : ((11 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 16))
    (hqLower : ((5 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((11 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow12Cell11Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow12Cell12RootCover {a q : ℝ}
    (haLower : ((11 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 16))
    (hqLower : ((11 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow12Cell12Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow12Cell13RootCover {a q : ℝ}
    (haLower : ((11 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 16))
    (hqLower : ((3 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((13 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow12Cell13Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow12Cell14RootCover {a q : ℝ}
    (haLower : ((11 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 16))
    (hqLower : ((13 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow12Cell14Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow12Cell15RootCover {a q : ℝ}
    (haLower : ((11 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 16))
    (hqLower : ((7 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((15 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow12Cell15Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow12Cell16RootCover {a q : ℝ}
    (haLower : ((11 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 16))
    (hqLower : ((15 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow12Cell16Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

/-- One horizontal row of the low endpoint rectangle. -/
theorem endpointCertificateObjective_lowRow12_nonneg {a q : ℝ}
    (haLower : ((11 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 16))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hendpointCertificateObjective_lowRow12_nonneg16 : q ≤ ((1 : ℝ) / 1000)
  · exact lowRow12Cell0RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow12_nonneg15 : q ≤ ((1 : ℝ) / 32)
  · exact lowRow12Cell1RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow12_nonneg14 : q ≤ ((1 : ℝ) / 16)
  · exact lowRow12Cell2RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow12_nonneg13 : q ≤ ((3 : ℝ) / 32)
  · exact lowRow12Cell3RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow12_nonneg12 : q ≤ ((1 : ℝ) / 8)
  · exact lowRow12Cell4RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow12_nonneg11 : q ≤ ((5 : ℝ) / 32)
  · exact lowRow12Cell5RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow12_nonneg10 : q ≤ ((3 : ℝ) / 16)
  · exact lowRow12Cell6RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow12_nonneg9 : q ≤ ((7 : ℝ) / 32)
  · exact lowRow12Cell7RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow12_nonneg8 : q ≤ ((1 : ℝ) / 4)
  · exact lowRow12Cell8RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow12_nonneg7 : q ≤ ((9 : ℝ) / 32)
  · exact lowRow12Cell9RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow12_nonneg6 : q ≤ ((5 : ℝ) / 16)
  · exact lowRow12Cell10RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow12_nonneg5 : q ≤ ((11 : ℝ) / 32)
  · exact lowRow12Cell11RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow12_nonneg4 : q ≤ ((3 : ℝ) / 8)
  · exact lowRow12Cell12RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow12_nonneg3 : q ≤ ((13 : ℝ) / 32)
  · exact lowRow12Cell13RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow12_nonneg2 : q ≤ ((7 : ℝ) / 16)
  · exact lowRow12Cell14RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow12_nonneg1 : q ≤ ((15 : ℝ) / 32)
  · exact lowRow12Cell15RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  exact lowRow12Cell16RootCover
    (by linarith) (by linarith) (by linarith) (by linarith)

end Frankl
