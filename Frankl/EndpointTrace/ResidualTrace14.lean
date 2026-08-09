import Frankl.EndpointCertificate

namespace Frankl

private def residualRootULUUULURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((43 : ℚ) / 160) ((89 : ℚ) / 320),
    RatBall.ofBounds ((93 : ℚ) / 320) ((31 : ℚ) / 100)⟩

private def residualRootULUUULUTree : Subdivision :=
.horizontal ((35 : ℚ) / 128)
  (.vertical ((961 : ℚ) / 3200)
  (.horizontal ((347 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((347 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((961 : ℚ) / 3200)
  (.horizontal ((353 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((353 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootULUUULUTree_certified :
    certifySubdivision 12 64 32 residualRootULUUULURectangle
      CertificateObjective.endpointExpression residualRootULUUULUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootULUUULU_nonneg {a q : ℝ}
    (haLower : ((43 : ℝ) / 160) ≤ a)
    (haUpper : a ≤ ((89 : ℝ) / 320))
    (hqLower : ((93 : ℝ) / 320) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 100)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootULUUULURectangle) (tree := residualRootULUUULUTree)
  · norm_num [residualRootULUUULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULUUULURectangle, RatBall.ofBounds]
  · norm_num [residualRootULUUULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULUUULURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootULUUULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULUUULURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootULUUULURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootULUUULURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootULUUULUTree_certified

private def residualRootULUUUULRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((89 : ℚ) / 320) ((23 : ℚ) / 80),
    RatBall.ofBounds ((217 : ℚ) / 800) ((93 : ℚ) / 320)⟩

private def residualRootULUUUULTree : Subdivision :=
.horizontal ((181 : ℚ) / 640)
  (.vertical ((899 : ℚ) / 3200)
  (.horizontal ((359 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((359 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((899 : ℚ) / 3200)
  (.horizontal ((73 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((73 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootULUUUULTree_certified :
    certifySubdivision 12 64 32 residualRootULUUUULRectangle
      CertificateObjective.endpointExpression residualRootULUUUULTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootULUUUUL_nonneg {a q : ℝ}
    (haLower : ((89 : ℝ) / 320) ≤ a)
    (haUpper : a ≤ ((23 : ℝ) / 80))
    (hqLower : ((217 : ℝ) / 800) ≤ q)
    (hqUpper : q ≤ ((93 : ℝ) / 320)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootULUUUULRectangle) (tree := residualRootULUUUULTree)
  · norm_num [residualRootULUUUULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULUUUULRectangle, RatBall.ofBounds]
  · norm_num [residualRootULUUUULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULUUUULRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootULUUUULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULUUUULRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootULUUUULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootULUUUULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootULUUUULTree_certified

private def residualRootULUUUUURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((89 : ℚ) / 320) ((23 : ℚ) / 80),
    RatBall.ofBounds ((93 : ℚ) / 320) ((31 : ℚ) / 100)⟩

private def residualRootULUUUUUTree : Subdivision :=
.horizontal ((181 : ℚ) / 640)
  (.vertical ((961 : ℚ) / 3200)
  (.horizontal ((359 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((359 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((73 : ℚ) / 256)
  (.vertical ((961 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((961 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootULUUUUUTree_certified :
    certifySubdivision 12 64 32 residualRootULUUUUURectangle
      CertificateObjective.endpointExpression residualRootULUUUUUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootULUUUUU_nonneg {a q : ℝ}
    (haLower : ((89 : ℝ) / 320) ≤ a)
    (haUpper : a ≤ ((23 : ℝ) / 80))
    (hqLower : ((93 : ℝ) / 320) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 100)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootULUUUUURectangle) (tree := residualRootULUUUUUTree)
  · norm_num [residualRootULUUUUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULUUUUURectangle, RatBall.ofBounds]
  · norm_num [residualRootULUUUUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULUUUUURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootULUUUUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULUUUUURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootULUUUUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootULUUUUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootULUUUUUTree_certified

end Frankl
