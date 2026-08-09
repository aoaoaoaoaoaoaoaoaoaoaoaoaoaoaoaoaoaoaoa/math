import Frankl.EndpointCertificate

namespace Frankl

private def residualRootUUULULURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((23 : ℚ) / 80) ((19 : ℚ) / 64),
    RatBall.ofBounds ((93 : ℚ) / 320) ((31 : ℚ) / 100)⟩

private def residualRootUUULULUTree : Subdivision :=
.horizontal ((187 : ℚ) / 640)
  (.horizontal ((371 : ℚ) / 1280)
  (.vertical ((961 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((961 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((377 : ℚ) / 1280)
  (.vertical ((961 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((961 : ℚ) / 3200)
  (.horizontal ((757 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((757 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval))))

private theorem residualRootUUULULUTree_certified :
    certifySubdivision 12 64 32 residualRootUUULULURectangle
      CertificateObjective.endpointExpression residualRootUUULULUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootUUULULU_nonneg {a q : ℝ}
    (haLower : ((23 : ℝ) / 80) ≤ a)
    (haUpper : a ≤ ((19 : ℝ) / 64))
    (hqLower : ((93 : ℝ) / 320) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 100)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootUUULULURectangle) (tree := residualRootUUULULUTree)
  · norm_num [residualRootUUULULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUULULURectangle, RatBall.ofBounds]
  · norm_num [residualRootUUULULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUULULURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootUUULULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUULULURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootUUULULURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootUUULULURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootUUULULUTree_certified

private def residualRootUUULUULLRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((19 : ℚ) / 64) ((193 : ℚ) / 640),
    RatBall.ofBounds ((217 : ℚ) / 800) ((93 : ℚ) / 320)⟩

private def residualRootUUULUULLTree : Subdivision :=
.horizontal ((383 : ℚ) / 1280)
  (.vertical ((899 : ℚ) / 3200)
  (.vertical ((1767 : ℚ) / 6400)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((763 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((899 : ℚ) / 3200)
  (.vertical ((1767 : ℚ) / 6400)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((769 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootUUULUULLTree_certified :
    certifySubdivision 12 64 32 residualRootUUULUULLRectangle
      CertificateObjective.endpointExpression residualRootUUULUULLTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootUUULUULL_nonneg {a q : ℝ}
    (haLower : ((19 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((193 : ℝ) / 640))
    (hqLower : ((217 : ℝ) / 800) ≤ q)
    (hqUpper : q ≤ ((93 : ℝ) / 320)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootUUULUULLRectangle) (tree := residualRootUUULUULLTree)
  · norm_num [residualRootUUULUULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUULUULLRectangle, RatBall.ofBounds]
  · norm_num [residualRootUUULUULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUULUULLRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootUUULUULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUULUULLRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootUUULUULLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootUUULUULLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootUUULUULLTree_certified

private def residualRootUUULUULURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((19 : ℚ) / 64) ((193 : ℚ) / 640),
    RatBall.ofBounds ((93 : ℚ) / 320) ((31 : ℚ) / 100)⟩

private def residualRootUUULUULUTree : Subdivision :=
.horizontal ((383 : ℚ) / 1280)
  (.vertical ((961 : ℚ) / 3200)
  (.horizontal ((763 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((763 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((961 : ℚ) / 3200)
  (.horizontal ((769 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((769 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootUUULUULUTree_certified :
    certifySubdivision 12 64 32 residualRootUUULUULURectangle
      CertificateObjective.endpointExpression residualRootUUULUULUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootUUULUULU_nonneg {a q : ℝ}
    (haLower : ((19 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((193 : ℝ) / 640))
    (hqLower : ((93 : ℝ) / 320) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 100)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootUUULUULURectangle) (tree := residualRootUUULUULUTree)
  · norm_num [residualRootUUULUULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUULUULURectangle, RatBall.ofBounds]
  · norm_num [residualRootUUULUULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUULUULURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootUUULUULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUULUULURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootUUULUULURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootUUULUULURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootUUULUULUTree_certified

end Frankl
