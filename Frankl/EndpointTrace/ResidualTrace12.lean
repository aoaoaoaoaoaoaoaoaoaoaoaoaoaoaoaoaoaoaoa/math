import Frankl.EndpointCertificate

namespace Frankl

private def residualRootULULUUURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((83 : ℚ) / 320) ((43 : ℚ) / 160),
    RatBall.ofBounds ((93 : ℚ) / 320) ((31 : ℚ) / 100)⟩

private def residualRootULULUUUTree : Subdivision :=
.horizontal ((169 : ℚ) / 640)
  (.vertical ((961 : ℚ) / 3200)
  (.horizontal ((67 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))
  (.vertical ((961 : ℚ) / 3200)
  (.horizontal ((341 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((341 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootULULUUUTree_certified :
    certifySubdivision 12 64 32 residualRootULULUUURectangle
      CertificateObjective.endpointExpression residualRootULULUUUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootULULUUU_nonneg {a q : ℝ}
    (haLower : ((83 : ℝ) / 320) ≤ a)
    (haUpper : a ≤ ((43 : ℝ) / 160))
    (hqLower : ((93 : ℝ) / 320) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 100)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootULULUUURectangle) (tree := residualRootULULUUUTree)
  · norm_num [residualRootULULUUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULULUUURectangle, RatBall.ofBounds]
  · norm_num [residualRootULULUUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULULUUURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootULULUUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULULUUURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootULULUUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootULULUUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootULULUUUTree_certified

private def residualRootULUULLLRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((43 : ℚ) / 160) ((89 : ℚ) / 320),
    RatBall.ofBounds ((93 : ℚ) / 400) ((403 : ℚ) / 1600)⟩

private def residualRootULUULLLTree : Subdivision :=
.horizontal ((35 : ℚ) / 128)
  (.vertical ((31 : ℚ) / 128)
  (.horizontal ((347 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((347 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((31 : ℚ) / 128)
  (.horizontal ((353 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((353 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootULUULLLTree_certified :
    certifySubdivision 12 64 32 residualRootULUULLLRectangle
      CertificateObjective.endpointExpression residualRootULUULLLTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootULUULLL_nonneg {a q : ℝ}
    (haLower : ((43 : ℝ) / 160) ≤ a)
    (haUpper : a ≤ ((89 : ℝ) / 320))
    (hqLower : ((93 : ℝ) / 400) ≤ q)
    (hqUpper : q ≤ ((403 : ℝ) / 1600)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootULUULLLRectangle) (tree := residualRootULUULLLTree)
  · norm_num [residualRootULUULLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULUULLLRectangle, RatBall.ofBounds]
  · norm_num [residualRootULUULLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULUULLLRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootULUULLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULUULLLRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootULUULLLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootULUULLLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootULUULLLTree_certified

private def residualRootULUULLURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((43 : ℚ) / 160) ((89 : ℚ) / 320),
    RatBall.ofBounds ((403 : ℚ) / 1600) ((217 : ℚ) / 800)⟩

private def residualRootULUULLUTree : Subdivision :=
.horizontal ((35 : ℚ) / 128)
  (.vertical ((837 : ℚ) / 3200)
  (.horizontal ((347 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((347 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((837 : ℚ) / 3200)
  (.horizontal ((353 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((353 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootULUULLUTree_certified :
    certifySubdivision 12 64 32 residualRootULUULLURectangle
      CertificateObjective.endpointExpression residualRootULUULLUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootULUULLU_nonneg {a q : ℝ}
    (haLower : ((43 : ℝ) / 160) ≤ a)
    (haUpper : a ≤ ((89 : ℝ) / 320))
    (hqLower : ((403 : ℝ) / 1600) ≤ q)
    (hqUpper : q ≤ ((217 : ℝ) / 800)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootULUULLURectangle) (tree := residualRootULUULLUTree)
  · norm_num [residualRootULUULLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULUULLURectangle, RatBall.ofBounds]
  · norm_num [residualRootULUULLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULUULLURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootULUULLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULUULLURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootULUULLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootULUULLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootULUULLUTree_certified

end Frankl
