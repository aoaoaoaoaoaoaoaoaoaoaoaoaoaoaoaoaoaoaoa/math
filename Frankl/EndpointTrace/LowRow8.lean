import Frankl.EndpointTrace.LowRow8Trace0
import Frankl.EndpointTrace.LowRow8Trace1

namespace Frankl

private theorem lowRow8Cell0RootCover {a q : ℝ}
    (haLower : ((7 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 8))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow8Cell0Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow8Cell1RootCover {a q : ℝ}
    (haLower : ((7 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 8))
    (hqLower : ((1 : ℝ) / 1000) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow8Cell1Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow8Cell2RootCover {a q : ℝ}
    (haLower : ((7 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 8))
    (hqLower : ((1 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow8Cell2Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow8Cell3RootCover {a q : ℝ}
    (haLower : ((7 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 8))
    (hqLower : ((1 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow8Cell3Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow8Cell4RootCover {a q : ℝ}
    (haLower : ((7 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 8))
    (hqLower : ((3 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow8Cell4Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow8Cell5RootCover {a q : ℝ}
    (haLower : ((7 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 8))
    (hqLower : ((1 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow8Cell5Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow8Cell6RootCover {a q : ℝ}
    (haLower : ((7 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 8))
    (hqLower : ((5 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow8Cell6Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow8Cell7RootCover {a q : ℝ}
    (haLower : ((7 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 8))
    (hqLower : ((3 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow8Cell7Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow8Cell8RootCover {a q : ℝ}
    (haLower : ((7 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 8))
    (hqLower : ((7 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 4)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow8Cell8Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow8Cell9RootCover {a q : ℝ}
    (haLower : ((7 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 8))
    (hqLower : ((1 : ℝ) / 4) ≤ q)
    (hqUpper : q ≤ ((9 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow8Cell9Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow8Cell10RootCover {a q : ℝ}
    (haLower : ((7 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 8))
    (hqLower : ((9 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow8Cell10Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow8Cell11RootCover {a q : ℝ}
    (haLower : ((7 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 8))
    (hqLower : ((5 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((11 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow8Cell11Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow8Cell12RootCover {a q : ℝ}
    (haLower : ((7 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 8))
    (hqLower : ((11 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow8Cell12Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow8Cell13RootCover {a q : ℝ}
    (haLower : ((7 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 8))
    (hqLower : ((3 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((13 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow8Cell13Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow8Cell14RootCover {a q : ℝ}
    (haLower : ((7 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 8))
    (hqLower : ((13 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow8Cell14Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow8Cell15RootCover {a q : ℝ}
    (haLower : ((7 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 8))
    (hqLower : ((7 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((15 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow8Cell15Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow8Cell16RootCover {a q : ℝ}
    (haLower : ((7 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 8))
    (hqLower : ((15 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow8Cell16Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

/-- One horizontal row of the low endpoint rectangle. -/
theorem endpointCertificateObjective_lowRow8_nonneg {a q : ℝ}
    (haLower : ((7 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 8))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hendpointCertificateObjective_lowRow8_nonneg16 : q ≤ ((1 : ℝ) / 1000)
  · exact lowRow8Cell0RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow8_nonneg15 : q ≤ ((1 : ℝ) / 32)
  · exact lowRow8Cell1RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow8_nonneg14 : q ≤ ((1 : ℝ) / 16)
  · exact lowRow8Cell2RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow8_nonneg13 : q ≤ ((3 : ℝ) / 32)
  · exact lowRow8Cell3RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow8_nonneg12 : q ≤ ((1 : ℝ) / 8)
  · exact lowRow8Cell4RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow8_nonneg11 : q ≤ ((5 : ℝ) / 32)
  · exact lowRow8Cell5RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow8_nonneg10 : q ≤ ((3 : ℝ) / 16)
  · exact lowRow8Cell6RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow8_nonneg9 : q ≤ ((7 : ℝ) / 32)
  · exact lowRow8Cell7RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow8_nonneg8 : q ≤ ((1 : ℝ) / 4)
  · exact lowRow8Cell8RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow8_nonneg7 : q ≤ ((9 : ℝ) / 32)
  · exact lowRow8Cell9RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow8_nonneg6 : q ≤ ((5 : ℝ) / 16)
  · exact lowRow8Cell10RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow8_nonneg5 : q ≤ ((11 : ℝ) / 32)
  · exact lowRow8Cell11RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow8_nonneg4 : q ≤ ((3 : ℝ) / 8)
  · exact lowRow8Cell12RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow8_nonneg3 : q ≤ ((13 : ℝ) / 32)
  · exact lowRow8Cell13RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow8_nonneg2 : q ≤ ((7 : ℝ) / 16)
  · exact lowRow8Cell14RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow8_nonneg1 : q ≤ ((15 : ℝ) / 32)
  · exact lowRow8Cell15RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  exact lowRow8Cell16RootCover
    (by linarith) (by linarith) (by linarith) (by linarith)

end Frankl
