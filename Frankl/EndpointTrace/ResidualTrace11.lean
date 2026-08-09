import Frankl.EndpointCertificate

namespace Frankl

private def residualRootULULLUURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((83 : ℚ) / 320) ((43 : ℚ) / 160),
    RatBall.ofBounds ((403 : ℚ) / 1600) ((217 : ℚ) / 800)⟩

private def residualRootULULLUUTree : Subdivision :=
.horizontal ((169 : ℚ) / 640)
  (.vertical ((837 : ℚ) / 3200)
  (.horizontal ((67 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((67 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((837 : ℚ) / 3200)
  (.horizontal ((341 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((341 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootULULLUUTree_certified :
    certifySubdivision 12 64 32 residualRootULULLUURectangle
      CertificateObjective.endpointExpression residualRootULULLUUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootULULLUU_nonneg {a q : ℝ}
    (haLower : ((83 : ℝ) / 320) ≤ a)
    (haUpper : a ≤ ((43 : ℝ) / 160))
    (hqLower : ((403 : ℝ) / 1600) ≤ q)
    (hqUpper : q ≤ ((217 : ℝ) / 800)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootULULLUURectangle) (tree := residualRootULULLUUTree)
  · norm_num [residualRootULULLUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULULLUURectangle, RatBall.ofBounds]
  · norm_num [residualRootULULLUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULULLUURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootULULLUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULULLUURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootULULLUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootULULLUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootULULLUUTree_certified

private def residualRootULULULRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 4) ((83 : ℚ) / 320),
    RatBall.ofBounds ((217 : ℚ) / 800) ((31 : ℚ) / 100)⟩

private def residualRootULULULTree : Subdivision :=
.vertical ((93 : ℚ) / 320)
  (.horizontal ((163 : ℚ) / 640)
  (.vertical ((899 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((899 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((163 : ℚ) / 640)
  (.vertical ((961 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((961 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootULULULTree_certified :
    certifySubdivision 12 64 32 residualRootULULULRectangle
      CertificateObjective.endpointExpression residualRootULULULTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootULULUL_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 4) ≤ a)
    (haUpper : a ≤ ((83 : ℝ) / 320))
    (hqLower : ((217 : ℝ) / 800) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 100)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootULULULRectangle) (tree := residualRootULULULTree)
  · norm_num [residualRootULULULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULULULRectangle, RatBall.ofBounds]
  · norm_num [residualRootULULULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULULULRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootULULULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULULULRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootULULULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootULULULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootULULULTree_certified

private def residualRootULULUULRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((83 : ℚ) / 320) ((43 : ℚ) / 160),
    RatBall.ofBounds ((217 : ℚ) / 800) ((93 : ℚ) / 320)⟩

private def residualRootULULUULTree : Subdivision :=
.horizontal ((169 : ℚ) / 640)
  (.vertical ((899 : ℚ) / 3200)
  (.horizontal ((67 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((67 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((899 : ℚ) / 3200)
  (.horizontal ((341 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((341 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootULULUULTree_certified :
    certifySubdivision 12 64 32 residualRootULULUULRectangle
      CertificateObjective.endpointExpression residualRootULULUULTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootULULUUL_nonneg {a q : ℝ}
    (haLower : ((83 : ℝ) / 320) ≤ a)
    (haUpper : a ≤ ((43 : ℝ) / 160))
    (hqLower : ((217 : ℝ) / 800) ≤ q)
    (hqUpper : q ≤ ((93 : ℝ) / 320)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootULULUULRectangle) (tree := residualRootULULUULTree)
  · norm_num [residualRootULULUULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULULUULRectangle, RatBall.ofBounds]
  · norm_num [residualRootULULUULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULULUULRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootULULUULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootULULUULRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootULULUULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootULULUULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootULULUULTree_certified

end Frankl
