import Frankl.EndpointTrace.LowRow0
import Frankl.EndpointTrace.LowRow1
import Frankl.EndpointTrace.LowRow2
import Frankl.EndpointTrace.LowRow3
import Frankl.EndpointTrace.LowRow4
import Frankl.EndpointTrace.LowRow5
import Frankl.EndpointTrace.LowRow6
import Frankl.EndpointTrace.LowRow7
import Frankl.EndpointTrace.LowRow8
import Frankl.EndpointTrace.LowRow9
import Frankl.EndpointTrace.LowRow10
import Frankl.EndpointTrace.LowRow11
import Frankl.EndpointTrace.LowRow12
import Frankl.EndpointTrace.LowRow13
import Frankl.EndpointTrace.LowRow14
import Frankl.EndpointTrace.LowRow15
import Frankl.EndpointTrace.LowRow16

namespace Frankl

/-- The complete low endpoint rectangle has nonnegative certificate objective. -/
theorem endpointCertificateObjective_low_nonneg {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 4))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hendpointCertificateObjective_low_nonneg16 : a ≤ ((1 : ℝ) / 1000)
  · exact endpointCertificateObjective_lowRow0_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_low_nonneg15 : a ≤ ((1 : ℝ) / 64)
  · exact endpointCertificateObjective_lowRow1_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_low_nonneg14 : a ≤ ((1 : ℝ) / 32)
  · exact endpointCertificateObjective_lowRow2_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_low_nonneg13 : a ≤ ((3 : ℝ) / 64)
  · exact endpointCertificateObjective_lowRow3_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_low_nonneg12 : a ≤ ((1 : ℝ) / 16)
  · exact endpointCertificateObjective_lowRow4_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_low_nonneg11 : a ≤ ((5 : ℝ) / 64)
  · exact endpointCertificateObjective_lowRow5_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_low_nonneg10 : a ≤ ((3 : ℝ) / 32)
  · exact endpointCertificateObjective_lowRow6_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_low_nonneg9 : a ≤ ((7 : ℝ) / 64)
  · exact endpointCertificateObjective_lowRow7_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_low_nonneg8 : a ≤ ((1 : ℝ) / 8)
  · exact endpointCertificateObjective_lowRow8_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_low_nonneg7 : a ≤ ((9 : ℝ) / 64)
  · exact endpointCertificateObjective_lowRow9_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_low_nonneg6 : a ≤ ((5 : ℝ) / 32)
  · exact endpointCertificateObjective_lowRow10_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_low_nonneg5 : a ≤ ((11 : ℝ) / 64)
  · exact endpointCertificateObjective_lowRow11_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_low_nonneg4 : a ≤ ((3 : ℝ) / 16)
  · exact endpointCertificateObjective_lowRow12_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_low_nonneg3 : a ≤ ((13 : ℝ) / 64)
  · exact endpointCertificateObjective_lowRow13_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_low_nonneg2 : a ≤ ((7 : ℝ) / 32)
  · exact endpointCertificateObjective_lowRow14_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_low_nonneg1 : a ≤ ((15 : ℝ) / 64)
  · exact endpointCertificateObjective_lowRow15_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)
  exact endpointCertificateObjective_lowRow16_nonneg
    (by linarith) (by linarith) (by linarith) (by linarith)

end Frankl
