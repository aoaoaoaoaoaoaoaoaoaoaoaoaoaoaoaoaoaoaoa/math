import Frankl.EndpointCertificate

namespace Frankl

private def residualRootLULUURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((43 : ℚ) / 160) ((23 : ℚ) / 80),
    RatBall.ofBounds ((93 : ℚ) / 800) ((31 : ℚ) / 200)⟩

private def residualRootLULUUTree : Subdivision :=
.horizontal ((89 : ℚ) / 320)
  (.vertical ((217 : ℚ) / 1600)
  (.horizontal ((35 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((35 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((217 : ℚ) / 1600)
  (.horizontal ((181 : ℚ) / 640)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((181 : ℚ) / 640)
  (.vertical ((93 : ℚ) / 640)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((93 : ℚ) / 640)
  (.leaf .interval)
  (.leaf .interval))))

private theorem residualRootLULUUTree_certified :
    certifySubdivision 12 64 32 residualRootLULUURectangle
      CertificateObjective.endpointExpression residualRootLULUUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootLULUU_nonneg {a q : ℝ}
    (haLower : ((43 : ℝ) / 160) ≤ a)
    (haUpper : a ≤ ((23 : ℝ) / 80))
    (hqLower : ((93 : ℝ) / 800) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 200)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootLULUURectangle) (tree := residualRootLULUUTree)
  · norm_num [residualRootLULUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLULUURectangle, RatBall.ofBounds]
  · norm_num [residualRootLULUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLULUURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootLULUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLULUURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootLULUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootLULUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootLULUUTree_certified

private def residualRootLUULLRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((23 : ℚ) / 80) ((49 : ℚ) / 160),
    RatBall.ofBounds ((31 : ℚ) / 400) ((93 : ℚ) / 800)⟩

private def residualRootLUULLTree : Subdivision :=
.horizontal ((19 : ℚ) / 64)
  (.vertical ((31 : ℚ) / 320)
  (.horizontal ((187 : ℚ) / 640)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((187 : ℚ) / 640)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((31 : ℚ) / 320)
  (.horizontal ((193 : ℚ) / 640)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((193 : ℚ) / 640)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootLUULLTree_certified :
    certifySubdivision 12 64 32 residualRootLUULLRectangle
      CertificateObjective.endpointExpression residualRootLUULLTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootLUULL_nonneg {a q : ℝ}
    (haLower : ((23 : ℝ) / 80) ≤ a)
    (haUpper : a ≤ ((49 : ℝ) / 160))
    (hqLower : ((31 : ℝ) / 400) ≤ q)
    (hqUpper : q ≤ ((93 : ℝ) / 800)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootLUULLRectangle) (tree := residualRootLUULLTree)
  · norm_num [residualRootLUULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLUULLRectangle, RatBall.ofBounds]
  · norm_num [residualRootLUULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLUULLRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootLUULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLUULLRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootLUULLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootLUULLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootLUULLTree_certified

end Frankl
