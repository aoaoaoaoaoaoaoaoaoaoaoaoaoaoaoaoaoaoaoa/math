import Frankl.EndpointCertificate

namespace Frankl

private def residualRootUULLULURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((23 : ℚ) / 80) ((19 : ℚ) / 64),
    RatBall.ofBounds ((341 : ℚ) / 1600) ((93 : ℚ) / 400)⟩

private def residualRootUULLULUTree : Subdivision :=
.horizontal ((187 : ℚ) / 640)
  (.vertical ((713 : ℚ) / 3200)
  (.horizontal ((371 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((371 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((713 : ℚ) / 3200)
  (.horizontal ((377 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((377 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootUULLULUTree_certified :
    certifySubdivision 12 64 32 residualRootUULLULURectangle
      CertificateObjective.endpointExpression residualRootUULLULUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootUULLULU_nonneg {a q : ℝ}
    (haLower : ((23 : ℝ) / 80) ≤ a)
    (haUpper : a ≤ ((19 : ℝ) / 64))
    (hqLower : ((341 : ℝ) / 1600) ≤ q)
    (hqUpper : q ≤ ((93 : ℝ) / 400)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootUULLULURectangle) (tree := residualRootUULLULUTree)
  · norm_num [residualRootUULLULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUULLULURectangle, RatBall.ofBounds]
  · norm_num [residualRootUULLULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUULLULURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootUULLULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUULLULURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootUULLULURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootUULLULURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootUULLULUTree_certified

private def residualRootUULLUULRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((19 : ℚ) / 64) ((49 : ℚ) / 160),
    RatBall.ofBounds ((31 : ℚ) / 160) ((341 : ℚ) / 1600)⟩

private def residualRootUULLUULTree : Subdivision :=
.horizontal ((193 : ℚ) / 640)
  (.vertical ((651 : ℚ) / 3200)
  (.leaf .interval)
  (.horizontal ((383 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((651 : ℚ) / 3200)
  (.horizontal ((389 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((389 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootUULLUULTree_certified :
    certifySubdivision 12 64 32 residualRootUULLUULRectangle
      CertificateObjective.endpointExpression residualRootUULLUULTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootUULLUUL_nonneg {a q : ℝ}
    (haLower : ((19 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((49 : ℝ) / 160))
    (hqLower : ((31 : ℝ) / 160) ≤ q)
    (hqUpper : q ≤ ((341 : ℝ) / 1600)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootUULLUULRectangle) (tree := residualRootUULLUULTree)
  · norm_num [residualRootUULLUULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUULLUULRectangle, RatBall.ofBounds]
  · norm_num [residualRootUULLUULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUULLUULRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootUULLUULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUULLUULRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootUULLUULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootUULLUULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootUULLUULTree_certified

private def residualRootUULLUUURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((19 : ℚ) / 64) ((49 : ℚ) / 160),
    RatBall.ofBounds ((341 : ℚ) / 1600) ((93 : ℚ) / 400)⟩

private def residualRootUULLUUUTree : Subdivision :=
.horizontal ((193 : ℚ) / 640)
  (.vertical ((713 : ℚ) / 3200)
  (.horizontal ((383 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((383 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((713 : ℚ) / 3200)
  (.horizontal ((389 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((389 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootUULLUUUTree_certified :
    certifySubdivision 12 64 32 residualRootUULLUUURectangle
      CertificateObjective.endpointExpression residualRootUULLUUUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootUULLUUU_nonneg {a q : ℝ}
    (haLower : ((19 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((49 : ℝ) / 160))
    (hqLower : ((341 : ℝ) / 1600) ≤ q)
    (hqUpper : q ≤ ((93 : ℝ) / 400)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootUULLUUURectangle) (tree := residualRootUULLUUUTree)
  · norm_num [residualRootUULLUUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUULLUUURectangle, RatBall.ofBounds]
  · norm_num [residualRootUULLUUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUULLUUURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootUULLUUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUULLUUURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootUULLUUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootUULLUUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootUULLUUUTree_certified

end Frankl
