import Frankl.EndpointTrace.LowRow15Trace0
import Frankl.EndpointTrace.LowRow15Trace1
import Frankl.EndpointTrace.LowRow15Trace2
import Frankl.EndpointTrace.LowRow15Trace3

namespace Frankl

private theorem lowRow15Cell0RootCover {a q : ℝ}
    (haLower : ((7 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((15 : ℝ) / 64))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow15Cell0Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow15Cell1RootCover {a q : ℝ}
    (haLower : ((7 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((15 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 1000) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow15Cell1Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow15Cell2RootCover {a q : ℝ}
    (haLower : ((7 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((15 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow15Cell2Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow15Cell3RootCover {a q : ℝ}
    (haLower : ((7 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((15 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow15Cell3Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow15Cell4RootCover {a q : ℝ}
    (haLower : ((7 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((15 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow15Cell4Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow15Cell5RootCover {a q : ℝ}
    (haLower : ((7 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((15 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow15Cell5Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow15Cell6RootCover {a q : ℝ}
    (haLower : ((7 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((15 : ℝ) / 64))
    (hqLower : ((5 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow15Cell6Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow15Cell7RootCover {a q : ℝ}
    (haLower : ((7 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((15 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow15Cell7Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow15Cell8RootCover {a q : ℝ}
    (haLower : ((7 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((15 : ℝ) / 64))
    (hqLower : ((7 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 4)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow15Cell8Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow15Cell9RootCover {a q : ℝ}
    (haLower : ((7 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((15 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 4) ≤ q)
    (hqUpper : q ≤ ((9 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow15Cell9Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow15Cell10RootCover {a q : ℝ}
    (haLower : ((7 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((15 : ℝ) / 64))
    (hqLower : ((9 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow15Cell10Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow15Cell11RootCover {a q : ℝ}
    (haLower : ((7 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((15 : ℝ) / 64))
    (hqLower : ((5 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((11 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow15Cell11Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow15Cell12RootCover {a q : ℝ}
    (haLower : ((7 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((15 : ℝ) / 64))
    (hqLower : ((11 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow15Cell12Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow15Cell13RootCover {a q : ℝ}
    (haLower : ((7 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((15 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((13 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow15Cell13Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow15Cell14RootCover {a q : ℝ}
    (haLower : ((7 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((15 : ℝ) / 64))
    (hqLower : ((13 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow15Cell14Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow15Cell15RootCover {a q : ℝ}
    (haLower : ((7 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((15 : ℝ) / 64))
    (hqLower : ((7 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((15 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow15Cell15Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem lowRow15Cell16RootCover {a q : ℝ}
    (haLower : ((7 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((15 : ℝ) / 64))
    (hqLower : ((15 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  exact lowRow15Cell16Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

/-- One horizontal row of the low endpoint rectangle. -/
theorem endpointCertificateObjective_lowRow15_nonneg {a q : ℝ}
    (haLower : ((7 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((15 : ℝ) / 64))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hendpointCertificateObjective_lowRow15_nonneg16 : q ≤ ((1 : ℝ) / 1000)
  · exact lowRow15Cell0RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow15_nonneg15 : q ≤ ((1 : ℝ) / 32)
  · exact lowRow15Cell1RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow15_nonneg14 : q ≤ ((1 : ℝ) / 16)
  · exact lowRow15Cell2RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow15_nonneg13 : q ≤ ((3 : ℝ) / 32)
  · exact lowRow15Cell3RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow15_nonneg12 : q ≤ ((1 : ℝ) / 8)
  · exact lowRow15Cell4RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow15_nonneg11 : q ≤ ((5 : ℝ) / 32)
  · exact lowRow15Cell5RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow15_nonneg10 : q ≤ ((3 : ℝ) / 16)
  · exact lowRow15Cell6RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow15_nonneg9 : q ≤ ((7 : ℝ) / 32)
  · exact lowRow15Cell7RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow15_nonneg8 : q ≤ ((1 : ℝ) / 4)
  · exact lowRow15Cell8RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow15_nonneg7 : q ≤ ((9 : ℝ) / 32)
  · exact lowRow15Cell9RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow15_nonneg6 : q ≤ ((5 : ℝ) / 16)
  · exact lowRow15Cell10RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow15_nonneg5 : q ≤ ((11 : ℝ) / 32)
  · exact lowRow15Cell11RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow15_nonneg4 : q ≤ ((3 : ℝ) / 8)
  · exact lowRow15Cell12RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow15_nonneg3 : q ≤ ((13 : ℝ) / 32)
  · exact lowRow15Cell13RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow15_nonneg2 : q ≤ ((7 : ℝ) / 16)
  · exact lowRow15Cell14RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_lowRow15_nonneg1 : q ≤ ((15 : ℝ) / 32)
  · exact lowRow15Cell15RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  exact lowRow15Cell16RootCover
    (by linarith) (by linarith) (by linarith) (by linarith)

end Frankl
