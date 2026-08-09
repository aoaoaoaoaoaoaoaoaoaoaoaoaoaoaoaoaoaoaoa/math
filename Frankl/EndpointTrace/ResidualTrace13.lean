import Frankl.EndpointCertificate

namespace Frankl

private def residualRootULUULULRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((89 : ℚ) / 320) ((23 : ℚ) / 80),
    RatBall.ofBounds ((93 : ℚ) / 400) ((403 : ℚ) / 1600)⟩

private def residualRootULUULULTree : Subdivision :=
.horizontal ((181 : ℚ) / 640)
  (.vertical ((31 : ℚ) / 128)
  (.horizontal ((359 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((359 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((31 : ℚ) / 128)
  (.horizontal ((73 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((73 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootULUULULTree_certified :
    certifySubdivision 12 64 32 residualRootULUULULRectangle
      CertificateObjective.endpointExpression residualRootULUULULTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootULUULUL_nonneg {a q : ℝ}
    (haLower : ((89 : ℝ) / 320) ≤ a)
    (haUpper : a ≤ ((23 : ℝ) / 80))
    (hqLower : ((93 : ℝ) / 400) ≤ q)
    (hqUpper : q ≤ ((403 : ℝ) / 1600)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootULUULULRectangle) (tree := residualRootULUULULTree)
  · norm_num [residualRootULUULULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULUULULRectangle, RatBall.ofBounds]
  · norm_num [residualRootULUULULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULUULULRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootULUULULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULUULULRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootULUULULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootULUULULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootULUULULTree_certified

private def residualRootULUULUURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((89 : ℚ) / 320) ((23 : ℚ) / 80),
    RatBall.ofBounds ((403 : ℚ) / 1600) ((217 : ℚ) / 800)⟩

private def residualRootULUULUUTree : Subdivision :=
.horizontal ((181 : ℚ) / 640)
  (.vertical ((837 : ℚ) / 3200)
  (.horizontal ((359 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((359 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((837 : ℚ) / 3200)
  (.horizontal ((73 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((73 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootULUULUUTree_certified :
    certifySubdivision 12 64 32 residualRootULUULUURectangle
      CertificateObjective.endpointExpression residualRootULUULUUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootULUULUU_nonneg {a q : ℝ}
    (haLower : ((89 : ℝ) / 320) ≤ a)
    (haUpper : a ≤ ((23 : ℝ) / 80))
    (hqLower : ((403 : ℝ) / 1600) ≤ q)
    (hqUpper : q ≤ ((217 : ℝ) / 800)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootULUULUURectangle) (tree := residualRootULUULUUTree)
  · norm_num [residualRootULUULUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULUULUURectangle, RatBall.ofBounds]
  · norm_num [residualRootULUULUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULUULUURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootULUULUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULUULUURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootULUULUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootULUULUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootULUULUUTree_certified

private def residualRootULUUULLRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((43 : ℚ) / 160) ((89 : ℚ) / 320),
    RatBall.ofBounds ((217 : ℚ) / 800) ((93 : ℚ) / 320)⟩

private def residualRootULUUULLTree : Subdivision :=
.horizontal ((35 : ℚ) / 128)
  (.vertical ((899 : ℚ) / 3200)
  (.horizontal ((347 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((347 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((899 : ℚ) / 3200)
  (.horizontal ((353 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((353 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootULUUULLTree_certified :
    certifySubdivision 12 64 32 residualRootULUUULLRectangle
      CertificateObjective.endpointExpression residualRootULUUULLTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootULUUULL_nonneg {a q : ℝ}
    (haLower : ((43 : ℝ) / 160) ≤ a)
    (haUpper : a ≤ ((89 : ℝ) / 320))
    (hqLower : ((217 : ℝ) / 800) ≤ q)
    (hqUpper : q ≤ ((93 : ℝ) / 320)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootULUUULLRectangle) (tree := residualRootULUUULLTree)
  · norm_num [residualRootULUUULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULUUULLRectangle, RatBall.ofBounds]
  · norm_num [residualRootULUUULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULUUULLRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootULUUULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULUUULLRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootULUUULLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootULUUULLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootULUUULLTree_certified

end Frankl
