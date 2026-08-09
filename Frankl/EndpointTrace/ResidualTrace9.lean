import Frankl.EndpointCertificate

namespace Frankl

private def residualRootULLULURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((89 : ℚ) / 320) ((23 : ℚ) / 80),
    RatBall.ofBounds ((31 : ℚ) / 200) ((31 : ℚ) / 160)⟩

private def residualRootULLULUTree : Subdivision :=
.vertical ((279 : ℚ) / 1600)
  (.horizontal ((181 : ℚ) / 640)
  (.vertical ((527 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((527 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((181 : ℚ) / 640)
  (.vertical ((589 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((589 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootULLULUTree_certified :
    certifySubdivision 12 64 32 residualRootULLULURectangle
      CertificateObjective.endpointExpression residualRootULLULUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootULLULU_nonneg {a q : ℝ}
    (haLower : ((89 : ℝ) / 320) ≤ a)
    (haUpper : a ≤ ((23 : ℝ) / 80))
    (hqLower : ((31 : ℝ) / 200) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 160)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootULLULURectangle) (tree := residualRootULLULUTree)
  · norm_num [residualRootULLULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULLULURectangle, RatBall.ofBounds]
  · norm_num [residualRootULLULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULLULURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootULLULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULLULURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootULLULURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootULLULURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootULLULUTree_certified

private def residualRootULLUULRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((43 : ℚ) / 160) ((89 : ℚ) / 320),
    RatBall.ofBounds ((31 : ℚ) / 160) ((93 : ℚ) / 400)⟩

private def residualRootULLUULTree : Subdivision :=
.vertical ((341 : ℚ) / 1600)
  (.horizontal ((35 : ℚ) / 128)
  (.vertical ((651 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((651 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((35 : ℚ) / 128)
  (.vertical ((713 : ℚ) / 3200)
  (.horizontal ((347 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((347 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((713 : ℚ) / 3200)
  (.horizontal ((353 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((353 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))))

private theorem residualRootULLUULTree_certified :
    certifySubdivision 12 64 32 residualRootULLUULRectangle
      CertificateObjective.endpointExpression residualRootULLUULTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootULLUUL_nonneg {a q : ℝ}
    (haLower : ((43 : ℝ) / 160) ≤ a)
    (haUpper : a ≤ ((89 : ℝ) / 320))
    (hqLower : ((31 : ℝ) / 160) ≤ q)
    (hqUpper : q ≤ ((93 : ℝ) / 400)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootULLUULRectangle) (tree := residualRootULLUULTree)
  · norm_num [residualRootULLUULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULLUULRectangle, RatBall.ofBounds]
  · norm_num [residualRootULLUULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULLUULRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootULLUULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULLUULRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootULLUULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootULLUULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootULLUULTree_certified

private def residualRootULLUUULRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((89 : ℚ) / 320) ((23 : ℚ) / 80),
    RatBall.ofBounds ((31 : ℚ) / 160) ((341 : ℚ) / 1600)⟩

private def residualRootULLUUULTree : Subdivision :=
.horizontal ((181 : ℚ) / 640)
  (.vertical ((651 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((651 : ℚ) / 3200)
  (.leaf .interval)
  (.horizontal ((73 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootULLUUULTree_certified :
    certifySubdivision 12 64 32 residualRootULLUUULRectangle
      CertificateObjective.endpointExpression residualRootULLUUULTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootULLUUUL_nonneg {a q : ℝ}
    (haLower : ((89 : ℝ) / 320) ≤ a)
    (haUpper : a ≤ ((23 : ℝ) / 80))
    (hqLower : ((31 : ℝ) / 160) ≤ q)
    (hqUpper : q ≤ ((341 : ℝ) / 1600)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootULLUUULRectangle) (tree := residualRootULLUUULTree)
  · norm_num [residualRootULLUUULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULLUUULRectangle, RatBall.ofBounds]
  · norm_num [residualRootULLUUULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULLUUULRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootULLUUULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULLUUULRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootULLUUULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootULLUUULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootULLUUULTree_certified

end Frankl
