import Frankl.EndpointCertificate

namespace Frankl

private def residualRootLLLLLLLLRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 4) ((83 : ℚ) / 320),
    RatBall.ofBounds ((0 : ℚ) / 1) ((31 : ℚ) / 3200)⟩

private def residualRootLLLLLLLLTree : Subdivision :=
.vertical ((31 : ℚ) / 6400)
  (.horizontal ((163 : ℚ) / 640)
  (.vertical ((31 : ℚ) / 12800)
  (.horizontal ((323 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))
  (.vertical ((31 : ℚ) / 12800)
  (.horizontal ((329 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval)))
  (.leaf .interval)

private theorem residualRootLLLLLLLLTree_certified :
    certifySubdivision 12 64 32 residualRootLLLLLLLLRectangle
      CertificateObjective.endpointExpression residualRootLLLLLLLLTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootLLLLLLLL_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 4) ≤ a)
    (haUpper : a ≤ ((83 : ℝ) / 320))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 3200)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootLLLLLLLLRectangle) (tree := residualRootLLLLLLLLTree)
  · norm_num [residualRootLLLLLLLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLLLLLLRectangle, RatBall.ofBounds]
  · norm_num [residualRootLLLLLLLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLLLLLLRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootLLLLLLLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLLLLLLRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootLLLLLLLLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootLLLLLLLLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootLLLLLLLLTree_certified

private def residualRootLLLLLLLURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((83 : ℚ) / 320) ((43 : ℚ) / 160),
    RatBall.ofBounds ((0 : ℚ) / 1) ((31 : ℚ) / 3200)⟩

private def residualRootLLLLLLLUTree : Subdivision :=
.vertical ((31 : ℚ) / 6400)
  (.horizontal ((169 : ℚ) / 640)
  (.vertical ((31 : ℚ) / 12800)
  (.horizontal ((67 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))
  (.vertical ((31 : ℚ) / 12800)
  (.horizontal ((341 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval)))
  (.leaf .interval)

private theorem residualRootLLLLLLLUTree_certified :
    certifySubdivision 12 64 32 residualRootLLLLLLLURectangle
      CertificateObjective.endpointExpression residualRootLLLLLLLUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootLLLLLLLU_nonneg {a q : ℝ}
    (haLower : ((83 : ℝ) / 320) ≤ a)
    (haUpper : a ≤ ((43 : ℝ) / 160))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 3200)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootLLLLLLLURectangle) (tree := residualRootLLLLLLLUTree)
  · norm_num [residualRootLLLLLLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLLLLLURectangle, RatBall.ofBounds]
  · norm_num [residualRootLLLLLLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLLLLLURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootLLLLLLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLLLLLURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootLLLLLLLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootLLLLLLLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootLLLLLLLUTree_certified

private def residualRootLLLLLLURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 4) ((43 : ℚ) / 160),
    RatBall.ofBounds ((31 : ℚ) / 3200) ((31 : ℚ) / 1600)⟩

private def residualRootLLLLLLUTree : Subdivision :=
.horizontal ((83 : ℚ) / 320)
  (.leaf .interval)
  (.leaf .interval)

private theorem residualRootLLLLLLUTree_certified :
    certifySubdivision 12 64 32 residualRootLLLLLLURectangle
      CertificateObjective.endpointExpression residualRootLLLLLLUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootLLLLLLU_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 4) ≤ a)
    (haUpper : a ≤ ((43 : ℝ) / 160))
    (hqLower : ((31 : ℝ) / 3200) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 1600)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootLLLLLLURectangle) (tree := residualRootLLLLLLUTree)
  · norm_num [residualRootLLLLLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLLLLURectangle, RatBall.ofBounds]
  · norm_num [residualRootLLLLLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLLLLURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootLLLLLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLLLLURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootLLLLLLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootLLLLLLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootLLLLLLUTree_certified

private def residualRootLLLLLULLRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((43 : ℚ) / 160) ((89 : ℚ) / 320),
    RatBall.ofBounds ((0 : ℚ) / 1) ((31 : ℚ) / 3200)⟩

private def residualRootLLLLLULLTree : Subdivision :=
.vertical ((31 : ℚ) / 6400)
  (.horizontal ((35 : ℚ) / 128)
  (.vertical ((31 : ℚ) / 12800)
  (.horizontal ((347 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))
  (.vertical ((31 : ℚ) / 12800)
  (.horizontal ((353 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval)))
  (.leaf .interval)

private theorem residualRootLLLLLULLTree_certified :
    certifySubdivision 12 64 32 residualRootLLLLLULLRectangle
      CertificateObjective.endpointExpression residualRootLLLLLULLTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootLLLLLULL_nonneg {a q : ℝ}
    (haLower : ((43 : ℝ) / 160) ≤ a)
    (haUpper : a ≤ ((89 : ℝ) / 320))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 3200)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootLLLLLULLRectangle) (tree := residualRootLLLLLULLTree)
  · norm_num [residualRootLLLLLULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLLLULLRectangle, RatBall.ofBounds]
  · norm_num [residualRootLLLLLULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLLLULLRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootLLLLLULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLLLULLRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootLLLLLULLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootLLLLLULLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootLLLLLULLTree_certified

end Frankl
