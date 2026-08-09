import Frankl.EndpointCertificate

namespace Frankl

private def residualRootUUULLUURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((19 : ℚ) / 64) ((49 : ℚ) / 160),
    RatBall.ofBounds ((403 : ℚ) / 1600) ((217 : ℚ) / 800)⟩

private def residualRootUUULLUUTree : Subdivision :=
.horizontal ((193 : ℚ) / 640)
  (.vertical ((837 : ℚ) / 3200)
  (.horizontal ((383 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((383 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((837 : ℚ) / 3200)
  (.horizontal ((389 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((389 : ℚ) / 1280)
  (.vertical ((341 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((341 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))))

private theorem residualRootUUULLUUTree_certified :
    certifySubdivision 12 64 32 residualRootUUULLUURectangle
      CertificateObjective.endpointExpression residualRootUUULLUUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootUUULLUU_nonneg {a q : ℝ}
    (haLower : ((19 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((49 : ℝ) / 160))
    (hqLower : ((403 : ℝ) / 1600) ≤ q)
    (hqUpper : q ≤ ((217 : ℝ) / 800)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootUUULLUURectangle) (tree := residualRootUUULLUUTree)
  · norm_num [residualRootUUULLUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUULLUURectangle, RatBall.ofBounds]
  · norm_num [residualRootUUULLUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUULLUURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootUUULLUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUULLUURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootUUULLUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootUUULLUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootUUULLUUTree_certified

private def residualRootUUULULLRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((23 : ℚ) / 80) ((19 : ℚ) / 64),
    RatBall.ofBounds ((217 : ℚ) / 800) ((93 : ℚ) / 320)⟩

private def residualRootUUULULLTree : Subdivision :=
.horizontal ((187 : ℚ) / 640)
  (.vertical ((899 : ℚ) / 3200)
  (.horizontal ((371 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((371 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((899 : ℚ) / 3200)
  (.horizontal ((377 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((377 : ℚ) / 1280)
  (.leaf .interval)
  (.horizontal ((757 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval))))

private theorem residualRootUUULULLTree_certified :
    certifySubdivision 12 64 32 residualRootUUULULLRectangle
      CertificateObjective.endpointExpression residualRootUUULULLTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootUUULULL_nonneg {a q : ℝ}
    (haLower : ((23 : ℝ) / 80) ≤ a)
    (haUpper : a ≤ ((19 : ℝ) / 64))
    (hqLower : ((217 : ℝ) / 800) ≤ q)
    (hqUpper : q ≤ ((93 : ℝ) / 320)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootUUULULLRectangle) (tree := residualRootUUULULLTree)
  · norm_num [residualRootUUULULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUULULLRectangle, RatBall.ofBounds]
  · norm_num [residualRootUUULULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUULULLRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootUUULULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUULULLRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootUUULULLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootUUULULLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootUUULULLTree_certified

end Frankl
