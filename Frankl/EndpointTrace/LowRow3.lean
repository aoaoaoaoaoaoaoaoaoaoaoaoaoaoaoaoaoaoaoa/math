import Frankl.EndpointTrace.LowRow3Trace0
import Frankl.EndpointTrace.LowRow3Trace1

namespace Frankl

private theorem lowRow3Cell0RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 64))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow3Cell0Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow3Cell1RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 1000) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow3Cell1Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow3Cell2RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow3Cell2Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow3Cell3RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow3Cell3Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow3Cell4RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow3Cell4Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow3Cell5RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow3Cell5Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow3Cell6RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 64))
    (hqLower : ((5 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow3Cell6Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow3Cell7RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow3Cell7Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow3Cell8RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 64))
    (hqLower : ((7 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 4)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow3Cell8Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow3Cell9RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 4) ≤ q)
    (hqUpper : q ≤ ((9 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow3Cell9Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow3Cell10RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 64))
    (hqLower : ((9 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow3Cell10Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow3Cell11RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 64))
    (hqLower : ((5 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((11 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow3Cell11Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow3Cell12RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 64))
    (hqLower : ((11 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow3Cell12Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow3Cell13RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((13 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow3Cell13Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow3Cell14RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 64))
    (hqLower : ((13 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow3Cell14Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow3Cell15RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 64))
    (hqLower : ((7 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((15 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow3Cell15Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow3Cell16RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 64))
    (hqLower : ((15 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow3Cell16Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

/-- One horizontal row of the low endpoint rectangle. -/
theorem endpointCertificateObjective_lowRow3_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 64))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hendpointCertificateObjective_lowRow3_nonneg16 : q ≤ ((1 : ℝ) / 1000)
  · exact lowRow3Cell0RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow3_nonneg15 : q ≤ ((1 : ℝ) / 32)
  · exact lowRow3Cell1RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow3_nonneg14 : q ≤ ((1 : ℝ) / 16)
  · exact lowRow3Cell2RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow3_nonneg13 : q ≤ ((3 : ℝ) / 32)
  · exact lowRow3Cell3RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow3_nonneg12 : q ≤ ((1 : ℝ) / 8)
  · exact lowRow3Cell4RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow3_nonneg11 : q ≤ ((5 : ℝ) / 32)
  · exact lowRow3Cell5RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow3_nonneg10 : q ≤ ((3 : ℝ) / 16)
  · exact lowRow3Cell6RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow3_nonneg9 : q ≤ ((7 : ℝ) / 32)
  · exact lowRow3Cell7RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow3_nonneg8 : q ≤ ((1 : ℝ) / 4)
  · exact lowRow3Cell8RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow3_nonneg7 : q ≤ ((9 : ℝ) / 32)
  · exact lowRow3Cell9RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow3_nonneg6 : q ≤ ((5 : ℝ) / 16)
  · exact lowRow3Cell10RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow3_nonneg5 : q ≤ ((11 : ℝ) / 32)
  · exact lowRow3Cell11RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow3_nonneg4 : q ≤ ((3 : ℝ) / 8)
  · exact lowRow3Cell12RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow3_nonneg3 : q ≤ ((13 : ℝ) / 32)
  · exact lowRow3Cell13RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow3_nonneg2 : q ≤ ((7 : ℝ) / 16)
  · exact lowRow3Cell14RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow3_nonneg1 : q ≤ ((15 : ℝ) / 32)
  · exact lowRow3Cell15RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  exact lowRow3Cell16RootCover
    (by linarith) (by linarith) (by linarith) (by linarith)

end Frankl
