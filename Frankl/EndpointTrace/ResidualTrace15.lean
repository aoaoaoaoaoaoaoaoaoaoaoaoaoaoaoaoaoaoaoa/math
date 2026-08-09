import Frankl.EndpointCertificate

namespace Frankl

private def residualRootUULLLLRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((23 : ℚ) / 80) ((19 : ℚ) / 64),
    RatBall.ofBounds ((31 : ℚ) / 200) ((31 : ℚ) / 160)⟩

private def residualRootUULLLLTree : Subdivision :=
.vertical ((279 : ℚ) / 1600)
  (.horizontal ((187 : ℚ) / 640)
  (.vertical ((527 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((527 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((187 : ℚ) / 640)
  (.vertical ((589 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((589 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootUULLLLTree_certified :
    certifySubdivision 12 64 32 residualRootUULLLLRectangle
      CertificateObjective.endpointExpression residualRootUULLLLTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootUULLLL_nonneg {a q : ℝ}
    (haLower : ((23 : ℝ) / 80) ≤ a)
    (haUpper : a ≤ ((19 : ℝ) / 64))
    (hqLower : ((31 : ℝ) / 200) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 160)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootUULLLLRectangle) (tree := residualRootUULLLLTree)
  · norm_num [residualRootUULLLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUULLLLRectangle, RatBall.ofBounds]
  · norm_num [residualRootUULLLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUULLLLRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootUULLLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUULLLLRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootUULLLLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootUULLLLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootUULLLLTree_certified

private def residualRootUULLLURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((19 : ℚ) / 64) ((49 : ℚ) / 160),
    RatBall.ofBounds ((31 : ℚ) / 200) ((31 : ℚ) / 160)⟩

private def residualRootUULLLUTree : Subdivision :=
.vertical ((279 : ℚ) / 1600)
  (.horizontal ((193 : ℚ) / 640)
  (.vertical ((527 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((527 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((193 : ℚ) / 640)
  (.vertical ((589 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((589 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootUULLLUTree_certified :
    certifySubdivision 12 64 32 residualRootUULLLURectangle
      CertificateObjective.endpointExpression residualRootUULLLUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootUULLLU_nonneg {a q : ℝ}
    (haLower : ((19 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((49 : ℝ) / 160))
    (hqLower : ((31 : ℝ) / 200) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 160)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootUULLLURectangle) (tree := residualRootUULLLUTree)
  · norm_num [residualRootUULLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUULLLURectangle, RatBall.ofBounds]
  · norm_num [residualRootUULLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUULLLURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootUULLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUULLLURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootUULLLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootUULLLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootUULLLUTree_certified

private def residualRootUULLULLRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((23 : ℚ) / 80) ((19 : ℚ) / 64),
    RatBall.ofBounds ((31 : ℚ) / 160) ((341 : ℚ) / 1600)⟩

private def residualRootUULLULLTree : Subdivision :=
.horizontal ((187 : ℚ) / 640)
  (.vertical ((651 : ℚ) / 3200)
  (.leaf .interval)
  (.horizontal ((371 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((651 : ℚ) / 3200)
  (.leaf .interval)
  (.horizontal ((377 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootUULLULLTree_certified :
    certifySubdivision 12 64 32 residualRootUULLULLRectangle
      CertificateObjective.endpointExpression residualRootUULLULLTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootUULLULL_nonneg {a q : ℝ}
    (haLower : ((23 : ℝ) / 80) ≤ a)
    (haUpper : a ≤ ((19 : ℝ) / 64))
    (hqLower : ((31 : ℝ) / 160) ≤ q)
    (hqUpper : q ≤ ((341 : ℝ) / 1600)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootUULLULLRectangle) (tree := residualRootUULLULLTree)
  · norm_num [residualRootUULLULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUULLULLRectangle, RatBall.ofBounds]
  · norm_num [residualRootUULLULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUULLULLRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootUULLULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUULLULLRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootUULLULLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootUULLULLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootUULLULLTree_certified

end Frankl
