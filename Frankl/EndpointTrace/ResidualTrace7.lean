import Frankl.EndpointCertificate

namespace Frankl

private def residualRootLUUUUURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((101 : ℚ) / 320) ((13 : ℚ) / 40),
    RatBall.ofBounds ((93 : ℚ) / 800) ((31 : ℚ) / 200)⟩

private def residualRootLUUUUUTree : Subdivision :=
.vertical ((217 : ℚ) / 1600)
  (.horizontal ((41 : ℚ) / 128)
  (.leaf .interval)
  (.vertical ((403 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((41 : ℚ) / 128)
  (.vertical ((93 : ℚ) / 640)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((93 : ℚ) / 640)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootLUUUUUTree_certified :
    certifySubdivision 12 64 32 residualRootLUUUUURectangle
      CertificateObjective.endpointExpression residualRootLUUUUUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootLUUUUU_nonneg {a q : ℝ}
    (haLower : ((101 : ℝ) / 320) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 40))
    (hqLower : ((93 : ℝ) / 800) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 200)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootLUUUUURectangle) (tree := residualRootLUUUUUTree)
  · norm_num [residualRootLUUUUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLUUUUURectangle, RatBall.ofBounds]
  · norm_num [residualRootLUUUUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLUUUUURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootLUUUUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLUUUUURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootLUUUUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootLUUUUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootLUUUUUTree_certified

private def residualRootULLLLLRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 4) ((83 : ℚ) / 320),
    RatBall.ofBounds ((31 : ℚ) / 200) ((31 : ℚ) / 160)⟩

private def residualRootULLLLLTree : Subdivision :=
.vertical ((279 : ℚ) / 1600)
  (.horizontal ((163 : ℚ) / 640)
  (.vertical ((527 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((527 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((163 : ℚ) / 640)
  (.vertical ((589 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((589 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootULLLLLTree_certified :
    certifySubdivision 12 64 32 residualRootULLLLLRectangle
      CertificateObjective.endpointExpression residualRootULLLLLTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootULLLLL_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 4) ≤ a)
    (haUpper : a ≤ ((83 : ℝ) / 320))
    (hqLower : ((31 : ℝ) / 200) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 160)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootULLLLLRectangle) (tree := residualRootULLLLLTree)
  · norm_num [residualRootULLLLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULLLLLRectangle, RatBall.ofBounds]
  · norm_num [residualRootULLLLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULLLLLRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootULLLLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULLLLLRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootULLLLLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootULLLLLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootULLLLLTree_certified

private def residualRootULLLLURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((83 : ℚ) / 320) ((43 : ℚ) / 160),
    RatBall.ofBounds ((31 : ℚ) / 200) ((31 : ℚ) / 160)⟩

private def residualRootULLLLUTree : Subdivision :=
.vertical ((279 : ℚ) / 1600)
  (.horizontal ((169 : ℚ) / 640)
  (.vertical ((527 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((527 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((169 : ℚ) / 640)
  (.vertical ((589 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((589 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootULLLLUTree_certified :
    certifySubdivision 12 64 32 residualRootULLLLURectangle
      CertificateObjective.endpointExpression residualRootULLLLUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootULLLLU_nonneg {a q : ℝ}
    (haLower : ((83 : ℝ) / 320) ≤ a)
    (haUpper : a ≤ ((43 : ℝ) / 160))
    (hqLower : ((31 : ℝ) / 200) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 160)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootULLLLURectangle) (tree := residualRootULLLLUTree)
  · norm_num [residualRootULLLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULLLLURectangle, RatBall.ofBounds]
  · norm_num [residualRootULLLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULLLLURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootULLLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULLLLURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootULLLLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootULLLLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootULLLLUTree_certified

end Frankl
