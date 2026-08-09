import Frankl.EndpointCertificate

namespace Frankl

private def residualRootUUUULUULRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((199 : ℚ) / 640) ((101 : ℚ) / 320),
    RatBall.ofBounds ((217 : ℚ) / 800) ((93 : ℚ) / 320)⟩

private def residualRootUUUULUULTree : Subdivision :=
.horizontal ((401 : ℚ) / 1280)
  (.vertical ((899 : ℚ) / 3200)
  (.horizontal ((799 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((799 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((899 : ℚ) / 3200)
  (.horizontal ((161 : ℚ) / 512)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((161 : ℚ) / 512)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootUUUULUULTree_certified :
    certifySubdivision 12 64 32 residualRootUUUULUULRectangle
      CertificateObjective.endpointExpression residualRootUUUULUULTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootUUUULUUL_nonneg {a q : ℝ}
    (haLower : ((199 : ℝ) / 640) ≤ a)
    (haUpper : a ≤ ((101 : ℝ) / 320))
    (hqLower : ((217 : ℝ) / 800) ≤ q)
    (hqUpper : q ≤ ((93 : ℝ) / 320)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootUUUULUULRectangle) (tree := residualRootUUUULUULTree)
  · norm_num [residualRootUUUULUULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUUULUULRectangle, RatBall.ofBounds]
  · norm_num [residualRootUUUULUULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUUULUULRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootUUUULUULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUUULUULRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootUUUULUULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootUUUULUULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootUUUULUULTree_certified

private def residualRootUUUULUUURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((199 : ℚ) / 640) ((101 : ℚ) / 320),
    RatBall.ofBounds ((93 : ℚ) / 320) ((31 : ℚ) / 100)⟩

private def residualRootUUUULUUUTree : Subdivision :=
.horizontal ((401 : ℚ) / 1280)
  (.vertical ((961 : ℚ) / 3200)
  (.horizontal ((799 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((799 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((961 : ℚ) / 3200)
  (.horizontal ((161 : ℚ) / 512)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((161 : ℚ) / 512)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootUUUULUUUTree_certified :
    certifySubdivision 12 64 32 residualRootUUUULUUURectangle
      CertificateObjective.endpointExpression residualRootUUUULUUUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootUUUULUUU_nonneg {a q : ℝ}
    (haLower : ((199 : ℝ) / 640) ≤ a)
    (haUpper : a ≤ ((101 : ℝ) / 320))
    (hqLower : ((93 : ℝ) / 320) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 100)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootUUUULUUURectangle) (tree := residualRootUUUULUUUTree)
  · norm_num [residualRootUUUULUUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUUULUUURectangle, RatBall.ofBounds]
  · norm_num [residualRootUUUULUUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUUULUUURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootUUUULUUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUUULUUURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootUUUULUUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootUUUULUUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootUUUULUUUTree_certified

private def residualRootUUUUULLRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((101 : ℚ) / 320) ((41 : ℚ) / 128),
    RatBall.ofBounds ((93 : ℚ) / 400) ((217 : ℚ) / 800)⟩

private def residualRootUUUUULLTree : Subdivision :=
.vertical ((403 : ℚ) / 1600)
  (.vertical ((31 : ℚ) / 128)
  (.horizontal ((407 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((407 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((407 : ℚ) / 1280)
  (.vertical ((837 : ℚ) / 3200)
  (.leaf .interval)
  (.vertical ((341 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((837 : ℚ) / 3200)
  (.leaf .interval)
  (.horizontal ((817 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval))))

private theorem residualRootUUUUULLTree_certified :
    certifySubdivision 12 64 32 residualRootUUUUULLRectangle
      CertificateObjective.endpointExpression residualRootUUUUULLTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootUUUUULL_nonneg {a q : ℝ}
    (haLower : ((101 : ℝ) / 320) ≤ a)
    (haUpper : a ≤ ((41 : ℝ) / 128))
    (hqLower : ((93 : ℝ) / 400) ≤ q)
    (hqUpper : q ≤ ((217 : ℝ) / 800)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootUUUUULLRectangle) (tree := residualRootUUUUULLTree)
  · norm_num [residualRootUUUUULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUUUULLRectangle, RatBall.ofBounds]
  · norm_num [residualRootUUUUULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUUUULLRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootUUUUULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUUUULLRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootUUUUULLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootUUUUULLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootUUUUULLTree_certified

end Frankl
