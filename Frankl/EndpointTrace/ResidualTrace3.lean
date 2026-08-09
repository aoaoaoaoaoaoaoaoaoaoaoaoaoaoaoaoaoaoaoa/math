import Frankl.EndpointCertificate

namespace Frankl

private def residualRootLLULRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 4) ((23 : ℚ) / 80),
    RatBall.ofBounds ((31 : ℚ) / 800) ((31 : ℚ) / 400)⟩

private def residualRootLLULTree : Subdivision :=
.horizontal ((43 : ℚ) / 160)
  (.vertical ((93 : ℚ) / 1600)
  (.horizontal ((83 : ℚ) / 320)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((83 : ℚ) / 320)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((93 : ℚ) / 1600)
  (.horizontal ((89 : ℚ) / 320)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((89 : ℚ) / 320)
  (.vertical ((217 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((217 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval))))

private theorem residualRootLLULTree_certified :
    certifySubdivision 12 64 32 residualRootLLULRectangle
      CertificateObjective.endpointExpression residualRootLLULTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootLLUL_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 4) ≤ a)
    (haUpper : a ≤ ((23 : ℝ) / 80))
    (hqLower : ((31 : ℝ) / 800) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 400)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootLLULRectangle) (tree := residualRootLLULTree)
  · norm_num [residualRootLLULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLULRectangle, RatBall.ofBounds]
  · norm_num [residualRootLLULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLULRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootLLULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLULRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootLLULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootLLULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootLLULTree_certified

private def residualRootLLUULRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((23 : ℚ) / 80) ((49 : ℚ) / 160),
    RatBall.ofBounds ((31 : ℚ) / 800) ((31 : ℚ) / 400)⟩

private def residualRootLLUULTree : Subdivision :=
.horizontal ((19 : ℚ) / 64)
  (.vertical ((93 : ℚ) / 1600)
  (.leaf .interval)
  (.horizontal ((187 : ℚ) / 640)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((93 : ℚ) / 1600)
  (.vertical ((31 : ℚ) / 640)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((193 : ℚ) / 640)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootLLUULTree_certified :
    certifySubdivision 12 64 32 residualRootLLUULRectangle
      CertificateObjective.endpointExpression residualRootLLUULTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootLLUUL_nonneg {a q : ℝ}
    (haLower : ((23 : ℝ) / 80) ≤ a)
    (haUpper : a ≤ ((49 : ℝ) / 160))
    (hqLower : ((31 : ℝ) / 800) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 400)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootLLUULRectangle) (tree := residualRootLLUULTree)
  · norm_num [residualRootLLUULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLUULRectangle, RatBall.ofBounds]
  · norm_num [residualRootLLUULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLUULRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootLLUULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLUULRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootLLUULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootLLUULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootLLUULTree_certified

private def residualRootLLUUURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((49 : ℚ) / 160) ((13 : ℚ) / 40),
    RatBall.ofBounds ((31 : ℚ) / 800) ((31 : ℚ) / 400)⟩

private def residualRootLLUUUTree : Subdivision :=
.horizontal ((101 : ℚ) / 320)
  (.vertical ((93 : ℚ) / 1600)
  (.horizontal ((199 : ℚ) / 640)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((199 : ℚ) / 640)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((93 : ℚ) / 1600)
  (.horizontal ((41 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((41 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootLLUUUTree_certified :
    certifySubdivision 12 64 32 residualRootLLUUURectangle
      CertificateObjective.endpointExpression residualRootLLUUUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootLLUUU_nonneg {a q : ℝ}
    (haLower : ((49 : ℝ) / 160) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 40))
    (hqLower : ((31 : ℝ) / 800) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 400)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootLLUUURectangle) (tree := residualRootLLUUUTree)
  · norm_num [residualRootLLUUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLUUURectangle, RatBall.ofBounds]
  · norm_num [residualRootLLUUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLUUURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootLLUUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLUUURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootLLUUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootLLUUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootLLUUUTree_certified

end Frankl
