import Frankl.EndpointCertificate

namespace Frankl

private def residualRootULLUUUURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((89 : ℚ) / 320) ((23 : ℚ) / 80),
    RatBall.ofBounds ((341 : ℚ) / 1600) ((93 : ℚ) / 400)⟩

private def residualRootULLUUUUTree : Subdivision :=
.horizontal ((181 : ℚ) / 640)
  (.vertical ((713 : ℚ) / 3200)
  (.horizontal ((359 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((359 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((713 : ℚ) / 3200)
  (.horizontal ((73 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((73 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootULLUUUUTree_certified :
    certifySubdivision 12 64 32 residualRootULLUUUURectangle
      CertificateObjective.endpointExpression residualRootULLUUUUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootULLUUUU_nonneg {a q : ℝ}
    (haLower : ((89 : ℝ) / 320) ≤ a)
    (haUpper : a ≤ ((23 : ℝ) / 80))
    (hqLower : ((341 : ℝ) / 1600) ≤ q)
    (hqUpper : q ≤ ((93 : ℝ) / 400)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootULLUUUURectangle) (tree := residualRootULLUUUUTree)
  · norm_num [residualRootULLUUUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULLUUUURectangle, RatBall.ofBounds]
  · norm_num [residualRootULLUUUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULLUUUURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootULLUUUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULLUUUURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootULLUUUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootULLUUUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootULLUUUUTree_certified

private def residualRootULULLLRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 4) ((83 : ℚ) / 320),
    RatBall.ofBounds ((93 : ℚ) / 400) ((217 : ℚ) / 800)⟩

private def residualRootULULLLTree : Subdivision :=
.vertical ((403 : ℚ) / 1600)
  (.horizontal ((163 : ℚ) / 640)
  (.vertical ((31 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((31 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((163 : ℚ) / 640)
  (.vertical ((837 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((837 : ℚ) / 3200)
  (.horizontal ((329 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((329 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))))

private theorem residualRootULULLLTree_certified :
    certifySubdivision 12 64 32 residualRootULULLLRectangle
      CertificateObjective.endpointExpression residualRootULULLLTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootULULLL_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 4) ≤ a)
    (haUpper : a ≤ ((83 : ℝ) / 320))
    (hqLower : ((93 : ℝ) / 400) ≤ q)
    (hqUpper : q ≤ ((217 : ℝ) / 800)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootULULLLRectangle) (tree := residualRootULULLLTree)
  · norm_num [residualRootULULLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULULLLRectangle, RatBall.ofBounds]
  · norm_num [residualRootULULLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULULLLRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootULULLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULULLLRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootULULLLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootULULLLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootULULLLTree_certified

private def residualRootULULLULRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((83 : ℚ) / 320) ((43 : ℚ) / 160),
    RatBall.ofBounds ((93 : ℚ) / 400) ((403 : ℚ) / 1600)⟩

private def residualRootULULLULTree : Subdivision :=
.horizontal ((169 : ℚ) / 640)
  (.vertical ((31 : ℚ) / 128)
  (.horizontal ((67 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((67 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((31 : ℚ) / 128)
  (.horizontal ((341 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((341 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootULULLULTree_certified :
    certifySubdivision 12 64 32 residualRootULULLULRectangle
      CertificateObjective.endpointExpression residualRootULULLULTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootULULLUL_nonneg {a q : ℝ}
    (haLower : ((83 : ℝ) / 320) ≤ a)
    (haUpper : a ≤ ((43 : ℝ) / 160))
    (hqLower : ((93 : ℝ) / 400) ≤ q)
    (hqUpper : q ≤ ((403 : ℝ) / 1600)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootULULLULRectangle) (tree := residualRootULULLULTree)
  · norm_num [residualRootULULLULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULULLULRectangle, RatBall.ofBounds]
  · norm_num [residualRootULULLULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULULLULRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootULULLULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULULLULRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootULULLULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootULULLULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootULULLULTree_certified

end Frankl
