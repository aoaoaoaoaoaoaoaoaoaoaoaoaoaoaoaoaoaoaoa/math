import Frankl.EndpointCertificate

namespace Frankl

private def residualRootUUUUUUULRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((41 : ℚ) / 128) ((13 : ℚ) / 40),
    RatBall.ofBounds ((217 : ℚ) / 800) ((93 : ℚ) / 320)⟩

private def residualRootUUUUUUULTree : Subdivision :=
.horizontal ((413 : ℚ) / 1280)
  (.vertical ((899 : ℚ) / 3200)
  (.horizontal ((823 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((823 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((899 : ℚ) / 3200)
  (.horizontal ((829 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((829 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootUUUUUUULTree_certified :
    certifySubdivision 12 64 32 residualRootUUUUUUULRectangle
      CertificateObjective.endpointExpression residualRootUUUUUUULTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootUUUUUUUL_nonneg {a q : ℝ}
    (haLower : ((41 : ℝ) / 128) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 40))
    (hqLower : ((217 : ℝ) / 800) ≤ q)
    (hqUpper : q ≤ ((93 : ℝ) / 320)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootUUUUUUULRectangle) (tree := residualRootUUUUUUULTree)
  · norm_num [residualRootUUUUUUULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUUUUUULRectangle, RatBall.ofBounds]
  · norm_num [residualRootUUUUUUULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUUUUUULRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootUUUUUUULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUUUUUULRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootUUUUUUULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootUUUUUUULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootUUUUUUULTree_certified

private def residualRootUUUUUUUURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((41 : ℚ) / 128) ((13 : ℚ) / 40),
    RatBall.ofBounds ((93 : ℚ) / 320) ((31 : ℚ) / 100)⟩

private def residualRootUUUUUUUUTree : Subdivision :=
.horizontal ((413 : ℚ) / 1280)
  (.vertical ((961 : ℚ) / 3200)
  (.horizontal ((823 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((823 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((961 : ℚ) / 3200)
  (.horizontal ((829 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((829 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootUUUUUUUUTree_certified :
    certifySubdivision 12 64 32 residualRootUUUUUUUURectangle
      CertificateObjective.endpointExpression residualRootUUUUUUUUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootUUUUUUUU_nonneg {a q : ℝ}
    (haLower : ((41 : ℝ) / 128) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 40))
    (hqLower : ((93 : ℝ) / 320) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 100)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootUUUUUUUURectangle) (tree := residualRootUUUUUUUUTree)
  · norm_num [residualRootUUUUUUUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUUUUUUURectangle, RatBall.ofBounds]
  · norm_num [residualRootUUUUUUUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUUUUUUURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootUUUUUUUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUUUUUUURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootUUUUUUUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootUUUUUUUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootUUUUUUUUTree_certified

end Frankl
