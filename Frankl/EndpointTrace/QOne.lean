import Frankl.EndpointTrace.QOneRange0
import Frankl.EndpointTrace.QOneRange1
import Frankl.EndpointTrace.QOneRange2
import Frankl.EndpointTrace.QOneRange3
import Frankl.EndpointTrace.QOneRange4
import Frankl.EndpointTrace.QOneRange5
import Frankl.EndpointTrace.QOneRange6
import Frankl.EndpointTrace.QOneRange7

namespace Frankl

/-- The deterministic endpoint is certified from the analytic corner to the target. -/
theorem endpointCertificateObjective_qOne_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((19099 : ℝ) / 50000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  by_cases hendpointCertificateObjective_qOne_nonneg7 : a ≤ ((19449 : ℝ) / 400000)
  · exact endpointCertificateObjective_qOneRange0_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_qOne_nonneg6 : a ≤ ((19249 : ℝ) / 200000)
  · exact endpointCertificateObjective_qOneRange1_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_qOne_nonneg5 : a ≤ ((57547 : ℝ) / 400000)
  · exact endpointCertificateObjective_qOneRange2_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_qOne_nonneg4 : a ≤ ((19149 : ℝ) / 100000)
  · exact endpointCertificateObjective_qOneRange3_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_qOne_nonneg3 : a ≤ ((19129 : ℝ) / 80000)
  · exact endpointCertificateObjective_qOneRange4_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_qOne_nonneg2 : a ≤ ((57347 : ℝ) / 200000)
  · exact endpointCertificateObjective_qOneRange5_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)
  by_cases hendpointCertificateObjective_qOne_nonneg1 : a ≤ ((133743 : ℝ) / 400000)
  · exact endpointCertificateObjective_qOneRange6_nonneg
      (by linarith) (by linarith) (by linarith) (by linarith)
  exact endpointCertificateObjective_qOneRange7_nonneg
    (by linarith) (by linarith) (by linarith) (by linarith)

end Frankl
