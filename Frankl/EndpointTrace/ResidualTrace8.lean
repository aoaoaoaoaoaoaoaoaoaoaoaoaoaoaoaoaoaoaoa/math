import Frankl.EndpointCertificate

namespace Frankl

private def residualRootULLLULRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 4) ((83 : ℚ) / 320),
    RatBall.ofBounds ((31 : ℚ) / 160) ((93 : ℚ) / 400)⟩

private def residualRootULLLULTree : Subdivision :=
.vertical ((341 : ℚ) / 1600)
  (.horizontal ((163 : ℚ) / 640)
  (.vertical ((651 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((651 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((163 : ℚ) / 640)
  (.vertical ((713 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((713 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootULLLULTree_certified :
    certifySubdivision 12 64 32 residualRootULLLULRectangle
      CertificateObjective.endpointExpression residualRootULLLULTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootULLLUL_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 4) ≤ a)
    (haUpper : a ≤ ((83 : ℝ) / 320))
    (hqLower : ((31 : ℝ) / 160) ≤ q)
    (hqUpper : q ≤ ((93 : ℝ) / 400)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootULLLULRectangle) (tree := residualRootULLLULTree)
  · norm_num [residualRootULLLULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULLLULRectangle, RatBall.ofBounds]
  · norm_num [residualRootULLLULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULLLULRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootULLLULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULLLULRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootULLLULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootULLLULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootULLLULTree_certified

private def residualRootULLLUURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((83 : ℚ) / 320) ((43 : ℚ) / 160),
    RatBall.ofBounds ((31 : ℚ) / 160) ((93 : ℚ) / 400)⟩

private def residualRootULLLUUTree : Subdivision :=
.vertical ((341 : ℚ) / 1600)
  (.horizontal ((169 : ℚ) / 640)
  (.vertical ((651 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((651 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((169 : ℚ) / 640)
  (.vertical ((713 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((713 : ℚ) / 3200)
  (.leaf .interval)
  (.horizontal ((341 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))))

private theorem residualRootULLLUUTree_certified :
    certifySubdivision 12 64 32 residualRootULLLUURectangle
      CertificateObjective.endpointExpression residualRootULLLUUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootULLLUU_nonneg {a q : ℝ}
    (haLower : ((83 : ℝ) / 320) ≤ a)
    (haUpper : a ≤ ((43 : ℝ) / 160))
    (hqLower : ((31 : ℝ) / 160) ≤ q)
    (hqUpper : q ≤ ((93 : ℝ) / 400)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootULLLUURectangle) (tree := residualRootULLLUUTree)
  · norm_num [residualRootULLLUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULLLUURectangle, RatBall.ofBounds]
  · norm_num [residualRootULLLUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULLLUURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootULLLUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULLLUURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootULLLUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootULLLUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootULLLUUTree_certified

private def residualRootULLULLRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((43 : ℚ) / 160) ((89 : ℚ) / 320),
    RatBall.ofBounds ((31 : ℚ) / 200) ((31 : ℚ) / 160)⟩

private def residualRootULLULLTree : Subdivision :=
.vertical ((279 : ℚ) / 1600)
  (.horizontal ((35 : ℚ) / 128)
  (.vertical ((527 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((527 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((35 : ℚ) / 128)
  (.vertical ((589 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((589 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootULLULLTree_certified :
    certifySubdivision 12 64 32 residualRootULLULLRectangle
      CertificateObjective.endpointExpression residualRootULLULLTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootULLULL_nonneg {a q : ℝ}
    (haLower : ((43 : ℝ) / 160) ≤ a)
    (haUpper : a ≤ ((89 : ℝ) / 320))
    (hqLower : ((31 : ℝ) / 200) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 160)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootULLULLRectangle) (tree := residualRootULLULLTree)
  · norm_num [residualRootULLULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULLULLRectangle, RatBall.ofBounds]
  · norm_num [residualRootULLULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULLULLRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootULLULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULLULLRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootULLULLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootULLULLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootULLULLTree_certified

end Frankl
