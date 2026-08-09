import Frankl.EndpointTrace.QOneRange0Trace0
import Frankl.EndpointTrace.QOneRange0Trace1

namespace Frankl

private theorem qOneCell0RootCover {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((25449 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hqOneCell0Root : a ≤ ((31849 : ℝ) / 12800000)
  · exact qOneCell0RootL_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)
  · exact qOneCell0RootU_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem qOneCell1RootCover {a q : ℝ}
    (haLower : ((25449 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((22249 : ℝ) / 3200000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  exact qOneCell1Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem qOneCell2RootCover {a q : ℝ}
    (haLower : ((22249 : ℝ) / 3200000) ≤ a)
    (haUpper : a ≤ ((63547 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  exact qOneCell2Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem qOneCell3RootCover {a q : ℝ}
    (haLower : ((63547 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((20649 : ℝ) / 1600000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  exact qOneCell3Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem qOneCell4RootCover {a q : ℝ}
    (haLower : ((20649 : ℝ) / 1600000) ≤ a)
    (haUpper : a ≤ ((20329 : ℝ) / 1280000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  exact qOneCell4Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem qOneCell5RootCover {a q : ℝ}
    (haLower : ((20329 : ℝ) / 1280000) ≤ a)
    (haUpper : a ≤ ((60347 : ℝ) / 3200000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  exact qOneCell5Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem qOneCell6RootCover {a q : ℝ}
    (haLower : ((60347 : ℝ) / 3200000) ≤ a)
    (haUpper : a ≤ ((139743 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  exact qOneCell6Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem qOneCell7RootCover {a q : ℝ}
    (haLower : ((139743 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((19849 : ℝ) / 800000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  exact qOneCell7Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem qOneCell8RootCover {a q : ℝ}
    (haLower : ((19849 : ℝ) / 800000) ≤ a)
    (haUpper : a ≤ ((177841 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  exact qOneCell8Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem qOneCell9RootCover {a q : ℝ}
    (haLower : ((177841 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((19689 : ℝ) / 640000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  exact qOneCell9Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem qOneCell10RootCover {a q : ℝ}
    (haLower : ((19689 : ℝ) / 640000) ≤ a)
    (haUpper : a ≤ ((215939 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  exact qOneCell10Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem qOneCell11RootCover {a q : ℝ}
    (haLower : ((215939 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((58747 : ℝ) / 1600000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  exact qOneCell11Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem qOneCell12RootCover {a q : ℝ}
    (haLower : ((58747 : ℝ) / 1600000) ≤ a)
    (haUpper : a ≤ ((254037 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  exact qOneCell12Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem qOneCell13RootCover {a q : ℝ}
    (haLower : ((254037 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((136543 : ℝ) / 3200000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  exact qOneCell13Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem qOneCell14RootCover {a q : ℝ}
    (haLower : ((136543 : ℝ) / 3200000) ≤ a)
    (haUpper : a ≤ ((58427 : ℝ) / 1280000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  exact qOneCell14Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

private theorem qOneCell15RootCover {a q : ℝ}
    (haLower : ((58427 : ℝ) / 1280000) ≤ a)
    (haUpper : a ≤ ((19449 : ℝ) / 400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  exact qOneCell15Root_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)

/-- One certified range of the deterministic endpoint. -/
theorem endpointCertificateObjective_qOneRange0_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((19449 : ℝ) / 400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hendpointCertificateObjective_qOneRange0_nonneg15 : a ≤ ((25449 : ℝ) / 6400000)
  · exact qOneCell0RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_qOneRange0_nonneg14 : a ≤ ((22249 : ℝ) / 3200000)
  · exact qOneCell1RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_qOneRange0_nonneg13 : a ≤ ((63547 : ℝ) / 6400000)
  · exact qOneCell2RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_qOneRange0_nonneg12 : a ≤ ((20649 : ℝ) / 1600000)
  · exact qOneCell3RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_qOneRange0_nonneg11 : a ≤ ((20329 : ℝ) / 1280000)
  · exact qOneCell4RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_qOneRange0_nonneg10 : a ≤ ((60347 : ℝ) / 3200000)
  · exact qOneCell5RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_qOneRange0_nonneg9 : a ≤ ((139743 : ℝ) / 6400000)
  · exact qOneCell6RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_qOneRange0_nonneg8 : a ≤ ((19849 : ℝ) / 800000)
  · exact qOneCell7RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_qOneRange0_nonneg7 : a ≤ ((177841 : ℝ) / 6400000)
  · exact qOneCell8RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_qOneRange0_nonneg6 : a ≤ ((19689 : ℝ) / 640000)
  · exact qOneCell9RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_qOneRange0_nonneg5 : a ≤ ((215939 : ℝ) / 6400000)
  · exact qOneCell10RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_qOneRange0_nonneg4 : a ≤ ((58747 : ℝ) / 1600000)
  · exact qOneCell11RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_qOneRange0_nonneg3 : a ≤ ((254037 : ℝ) / 6400000)
  · exact qOneCell12RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_qOneRange0_nonneg2 : a ≤ ((136543 : ℝ) / 3200000)
  · exact qOneCell13RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_qOneRange0_nonneg1 : a ≤ ((58427 : ℝ) / 1280000)
  · exact qOneCell14RootCover
      (by linarith) (by linarith) (by linarith) (by linarith)
  exact qOneCell15RootCover
    (by linarith) (by linarith) (by linarith) (by linarith)

end Frankl
