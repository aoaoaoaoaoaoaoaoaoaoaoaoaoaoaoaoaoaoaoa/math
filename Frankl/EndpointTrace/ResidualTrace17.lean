import Frankl.EndpointCertificate

namespace Frankl

private def residualRootUULULLRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((49 : ℚ) / 160) ((101 : ℚ) / 320),
    RatBall.ofBounds ((31 : ℚ) / 200) ((31 : ℚ) / 160)⟩

private def residualRootUULULLTree : Subdivision :=
.vertical ((279 : ℚ) / 1600)
  (.horizontal ((199 : ℚ) / 640)
  (.vertical ((527 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((527 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((199 : ℚ) / 640)
  (.vertical ((589 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((589 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootUULULLTree_certified :
    certifySubdivision 12 64 32 residualRootUULULLRectangle
      CertificateObjective.endpointExpression residualRootUULULLTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootUULULL_nonneg {a q : ℝ}
    (haLower : ((49 : ℝ) / 160) ≤ a)
    (haUpper : a ≤ ((101 : ℝ) / 320))
    (hqLower : ((31 : ℝ) / 200) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 160)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootUULULLRectangle) (tree := residualRootUULULLTree)
  · norm_num [residualRootUULULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUULULLRectangle, RatBall.ofBounds]
  · norm_num [residualRootUULULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUULULLRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootUULULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUULULLRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootUULULLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootUULULLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootUULULLTree_certified

private def residualRootUULULURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((101 : ℚ) / 320) ((13 : ℚ) / 40),
    RatBall.ofBounds ((31 : ℚ) / 200) ((31 : ℚ) / 160)⟩

private def residualRootUULULUTree : Subdivision :=
.vertical ((279 : ℚ) / 1600)
  (.horizontal ((41 : ℚ) / 128)
  (.vertical ((527 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((527 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((41 : ℚ) / 128)
  (.vertical ((589 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((589 : ℚ) / 3200)
  (.leaf .interval)
  (.horizontal ((413 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))))

private theorem residualRootUULULUTree_certified :
    certifySubdivision 12 64 32 residualRootUULULURectangle
      CertificateObjective.endpointExpression residualRootUULULUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootUULULU_nonneg {a q : ℝ}
    (haLower : ((101 : ℝ) / 320) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 40))
    (hqLower : ((31 : ℝ) / 200) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 160)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootUULULURectangle) (tree := residualRootUULULUTree)
  · norm_num [residualRootUULULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUULULURectangle, RatBall.ofBounds]
  · norm_num [residualRootUULULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUULULURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootUULULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUULULURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootUULULURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootUULULURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootUULULUTree_certified

private def residualRootUULUULLRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((49 : ℚ) / 160) ((101 : ℚ) / 320),
    RatBall.ofBounds ((31 : ℚ) / 160) ((341 : ℚ) / 1600)⟩

private def residualRootUULUULLTree : Subdivision :=
.horizontal ((199 : ℚ) / 640)
  (.vertical ((651 : ℚ) / 3200)
  (.horizontal ((79 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((79 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((651 : ℚ) / 3200)
  (.horizontal ((401 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((401 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootUULUULLTree_certified :
    certifySubdivision 12 64 32 residualRootUULUULLRectangle
      CertificateObjective.endpointExpression residualRootUULUULLTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootUULUULL_nonneg {a q : ℝ}
    (haLower : ((49 : ℝ) / 160) ≤ a)
    (haUpper : a ≤ ((101 : ℝ) / 320))
    (hqLower : ((31 : ℝ) / 160) ≤ q)
    (hqUpper : q ≤ ((341 : ℝ) / 1600)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootUULUULLRectangle) (tree := residualRootUULUULLTree)
  · norm_num [residualRootUULUULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUULUULLRectangle, RatBall.ofBounds]
  · norm_num [residualRootUULUULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUULUULLRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootUULUULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUULUULLRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootUULUULLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootUULUULLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootUULUULLTree_certified

end Frankl
