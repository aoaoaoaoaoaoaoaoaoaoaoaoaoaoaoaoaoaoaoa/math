import Frankl.EndpointCertificate

namespace Frankl

private def residualRootUULUULURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((49 : ℚ) / 160) ((101 : ℚ) / 320),
    RatBall.ofBounds ((341 : ℚ) / 1600) ((93 : ℚ) / 400)⟩

private def residualRootUULUULUTree : Subdivision :=
.horizontal ((199 : ℚ) / 640)
  (.vertical ((713 : ℚ) / 3200)
  (.horizontal ((79 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((79 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((713 : ℚ) / 3200)
  (.horizontal ((401 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((401 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootUULUULUTree_certified :
    certifySubdivision 12 64 32 residualRootUULUULURectangle
      CertificateObjective.endpointExpression residualRootUULUULUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootUULUULU_nonneg {a q : ℝ}
    (haLower : ((49 : ℝ) / 160) ≤ a)
    (haUpper : a ≤ ((101 : ℝ) / 320))
    (hqLower : ((341 : ℝ) / 1600) ≤ q)
    (hqUpper : q ≤ ((93 : ℝ) / 400)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootUULUULURectangle) (tree := residualRootUULUULUTree)
  · norm_num [residualRootUULUULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUULUULURectangle, RatBall.ofBounds]
  · norm_num [residualRootUULUULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUULUULURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootUULUULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUULUULURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootUULUULURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootUULUULURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootUULUULUTree_certified

private def residualRootUULUUULRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((101 : ℚ) / 320) ((13 : ℚ) / 40),
    RatBall.ofBounds ((31 : ℚ) / 160) ((341 : ℚ) / 1600)⟩

private def residualRootUULUUULTree : Subdivision :=
.horizontal ((41 : ℚ) / 128)
  (.vertical ((651 : ℚ) / 3200)
  (.horizontal ((407 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((407 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((651 : ℚ) / 3200)
  (.horizontal ((413 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((413 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootUULUUULTree_certified :
    certifySubdivision 12 64 32 residualRootUULUUULRectangle
      CertificateObjective.endpointExpression residualRootUULUUULTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootUULUUUL_nonneg {a q : ℝ}
    (haLower : ((101 : ℝ) / 320) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 40))
    (hqLower : ((31 : ℝ) / 160) ≤ q)
    (hqUpper : q ≤ ((341 : ℝ) / 1600)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootUULUUULRectangle) (tree := residualRootUULUUULTree)
  · norm_num [residualRootUULUUULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUULUUULRectangle, RatBall.ofBounds]
  · norm_num [residualRootUULUUULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUULUUULRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootUULUUULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUULUUULRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootUULUUULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootUULUUULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootUULUUULTree_certified

private def residualRootUULUUUURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((101 : ℚ) / 320) ((13 : ℚ) / 40),
    RatBall.ofBounds ((341 : ℚ) / 1600) ((93 : ℚ) / 400)⟩

private def residualRootUULUUUUTree : Subdivision :=
.horizontal ((41 : ℚ) / 128)
  (.vertical ((713 : ℚ) / 3200)
  (.horizontal ((407 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((407 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((713 : ℚ) / 3200)
  (.horizontal ((413 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((413 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootUULUUUUTree_certified :
    certifySubdivision 12 64 32 residualRootUULUUUURectangle
      CertificateObjective.endpointExpression residualRootUULUUUUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootUULUUUU_nonneg {a q : ℝ}
    (haLower : ((101 : ℝ) / 320) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 40))
    (hqLower : ((341 : ℝ) / 1600) ≤ q)
    (hqUpper : q ≤ ((93 : ℝ) / 400)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootUULUUUURectangle) (tree := residualRootUULUUUUTree)
  · norm_num [residualRootUULUUUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUULUUUURectangle, RatBall.ofBounds]
  · norm_num [residualRootUULUUUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUULUUUURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootUULUUUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUULUUUURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootUULUUUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootUULUUUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootUULUUUUTree_certified

end Frankl
