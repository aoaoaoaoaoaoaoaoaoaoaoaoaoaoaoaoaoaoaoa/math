import Frankl.EndpointCertificate

namespace Frankl

private def residualRootLULLLRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 4) ((43 : ℚ) / 160),
    RatBall.ofBounds ((31 : ℚ) / 400) ((93 : ℚ) / 800)⟩

private def residualRootLULLLTree : Subdivision :=
.horizontal ((83 : ℚ) / 320)
  (.vertical ((31 : ℚ) / 320)
  (.vertical ((279 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((341 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((31 : ℚ) / 320)
  (.vertical ((279 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((169 : ℚ) / 640)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootLULLLTree_certified :
    certifySubdivision 12 64 32 residualRootLULLLRectangle
      CertificateObjective.endpointExpression residualRootLULLLTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootLULLL_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 4) ≤ a)
    (haUpper : a ≤ ((43 : ℝ) / 160))
    (hqLower : ((31 : ℝ) / 400) ≤ q)
    (hqUpper : q ≤ ((93 : ℝ) / 800)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootLULLLRectangle) (tree := residualRootLULLLTree)
  · norm_num [residualRootLULLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLULLLRectangle, RatBall.ofBounds]
  · norm_num [residualRootLULLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLULLLRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootLULLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLULLLRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootLULLLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootLULLLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootLULLLTree_certified

private def residualRootLULLURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 4) ((43 : ℚ) / 160),
    RatBall.ofBounds ((93 : ℚ) / 800) ((31 : ℚ) / 200)⟩

private def residualRootLULLUTree : Subdivision :=
.horizontal ((83 : ℚ) / 320)
  (.vertical ((217 : ℚ) / 1600)
  (.horizontal ((163 : ℚ) / 640)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((163 : ℚ) / 640)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((217 : ℚ) / 1600)
  (.horizontal ((169 : ℚ) / 640)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((169 : ℚ) / 640)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootLULLUTree_certified :
    certifySubdivision 12 64 32 residualRootLULLURectangle
      CertificateObjective.endpointExpression residualRootLULLUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootLULLU_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 4) ≤ a)
    (haUpper : a ≤ ((43 : ℝ) / 160))
    (hqLower : ((93 : ℝ) / 800) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 200)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootLULLURectangle) (tree := residualRootLULLUTree)
  · norm_num [residualRootLULLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLULLURectangle, RatBall.ofBounds]
  · norm_num [residualRootLULLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLULLURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootLULLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLULLURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootLULLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootLULLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootLULLUTree_certified

private def residualRootLULULRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((43 : ℚ) / 160) ((23 : ℚ) / 80),
    RatBall.ofBounds ((31 : ℚ) / 400) ((93 : ℚ) / 800)⟩

private def residualRootLULULTree : Subdivision :=
.horizontal ((89 : ℚ) / 320)
  (.vertical ((31 : ℚ) / 320)
  (.vertical ((279 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((35 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((31 : ℚ) / 320)
  (.horizontal ((181 : ℚ) / 640)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((181 : ℚ) / 640)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootLULULTree_certified :
    certifySubdivision 12 64 32 residualRootLULULRectangle
      CertificateObjective.endpointExpression residualRootLULULTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootLULUL_nonneg {a q : ℝ}
    (haLower : ((43 : ℝ) / 160) ≤ a)
    (haUpper : a ≤ ((23 : ℝ) / 80))
    (hqLower : ((31 : ℝ) / 400) ≤ q)
    (hqUpper : q ≤ ((93 : ℝ) / 800)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootLULULRectangle) (tree := residualRootLULULTree)
  · norm_num [residualRootLULULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLULULRectangle, RatBall.ofBounds]
  · norm_num [residualRootLULULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLULULRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootLULULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLULULRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootLULULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootLULULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootLULULTree_certified

end Frankl
