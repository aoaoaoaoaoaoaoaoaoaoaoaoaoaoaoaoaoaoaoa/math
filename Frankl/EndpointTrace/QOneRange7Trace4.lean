import Frankl.EndpointCertificate

namespace Frankl

private def qOneCell127RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((2425623 : ℚ) / 6400000) ((19099 : ℚ) / 50000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell127RootTree : Subdivision :=
.horizontal ((974059 : ℚ) / 2560000)
  (.horizontal ((9721541 : ℚ) / 25600000)
  (.horizontal ((19424033 : ℚ) / 51200000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((19462131 : ℚ) / 51200000)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((9759639 : ℚ) / 25600000)
  (.horizontal ((19500229 : ℚ) / 51200000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((19538327 : ℚ) / 51200000)
  (.leaf .interval)
  (.leaf .interval)))

private theorem qOneCell127RootTree_certified :
    certifySubdivision 12 64 32 qOneCell127RootRectangle
      CertificateObjective.endpointExpression qOneCell127RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell127Root_nonneg {a q : ℝ}
    (haLower : ((2425623 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((19099 : ℝ) / 50000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell127RootRectangle) (tree := qOneCell127RootTree)
  · norm_num [qOneCell127RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell127RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell127RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell127RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell127RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell127RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell127RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell127RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell127RootTree_certified

end Frankl
