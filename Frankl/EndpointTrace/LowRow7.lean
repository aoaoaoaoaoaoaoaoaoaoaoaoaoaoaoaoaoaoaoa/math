import Frankl.EndpointTrace.LowRow7Trace0
import Frankl.EndpointTrace.LowRow7Trace1

namespace Frankl

private theorem lowRow7Cell0RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 64))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow7Cell0Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow7Cell1RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 1000) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow7Cell1Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow7Cell2RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow7Cell2Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow7Cell3RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow7Cell3Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow7Cell4RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow7Cell4Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow7Cell5RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow7Cell5Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow7Cell6RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 64))
    (hqLower : ((5 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow7Cell6Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow7Cell7RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow7Cell7Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow7Cell8RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 64))
    (hqLower : ((7 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 4)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow7Cell8Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow7Cell9RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 4) ≤ q)
    (hqUpper : q ≤ ((9 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow7Cell9Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow7Cell10RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 64))
    (hqLower : ((9 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow7Cell10Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow7Cell11RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 64))
    (hqLower : ((5 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((11 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow7Cell11Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow7Cell12RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 64))
    (hqLower : ((11 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow7Cell12Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow7Cell13RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((13 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow7Cell13Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow7Cell14RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 64))
    (hqLower : ((13 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow7Cell14Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow7Cell15RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 64))
    (hqLower : ((7 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((15 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow7Cell15Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow7Cell16RootCover {a q : ℝ}
    (haLower : ((3 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 64))
    (hqLower : ((15 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow7Cell16Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

/-- One horizontal row of the low endpoint rectangle. -/
theorem endpointCertificateObjective_lowRow7_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 64))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hendpointCertificateObjective_lowRow7_nonneg16 : q ≤ ((1 : ℝ) / 1000)
  · exact lowRow7Cell0RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow7_nonneg15 : q ≤ ((1 : ℝ) / 32)
  · exact lowRow7Cell1RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow7_nonneg14 : q ≤ ((1 : ℝ) / 16)
  · exact lowRow7Cell2RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow7_nonneg13 : q ≤ ((3 : ℝ) / 32)
  · exact lowRow7Cell3RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow7_nonneg12 : q ≤ ((1 : ℝ) / 8)
  · exact lowRow7Cell4RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow7_nonneg11 : q ≤ ((5 : ℝ) / 32)
  · exact lowRow7Cell5RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow7_nonneg10 : q ≤ ((3 : ℝ) / 16)
  · exact lowRow7Cell6RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow7_nonneg9 : q ≤ ((7 : ℝ) / 32)
  · exact lowRow7Cell7RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow7_nonneg8 : q ≤ ((1 : ℝ) / 4)
  · exact lowRow7Cell8RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow7_nonneg7 : q ≤ ((9 : ℝ) / 32)
  · exact lowRow7Cell9RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow7_nonneg6 : q ≤ ((5 : ℝ) / 16)
  · exact lowRow7Cell10RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow7_nonneg5 : q ≤ ((11 : ℝ) / 32)
  · exact lowRow7Cell11RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow7_nonneg4 : q ≤ ((3 : ℝ) / 8)
  · exact lowRow7Cell12RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow7_nonneg3 : q ≤ ((13 : ℝ) / 32)
  · exact lowRow7Cell13RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow7_nonneg2 : q ≤ ((7 : ℝ) / 16)
  · exact lowRow7Cell14RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow7_nonneg1 : q ≤ ((15 : ℝ) / 32)
  · exact lowRow7Cell15RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  exact lowRow7Cell16RootCover
    (by linarith) (by linarith) (by linarith) (by linarith)

end Frankl
