import Frankl.EndpointCertificate

namespace Frankl

private def residualRootUUUUULURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((41 : ℚ) / 128) ((13 : ℚ) / 40),
    RatBall.ofBounds ((93 : ℚ) / 400) ((217 : ℚ) / 800)⟩

private def residualRootUUUUULUTree : Subdivision :=
.vertical ((403 : ℚ) / 1600)
  (.horizontal ((413 : ℚ) / 1280)
  (.vertical ((31 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((31 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((413 : ℚ) / 1280)
  (.vertical ((837 : ℚ) / 3200)
  (.leaf .interval)
  (.horizontal ((823 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((837 : ℚ) / 3200)
  (.leaf .interval)
  (.horizontal ((829 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval))))

private theorem residualRootUUUUULUTree_certified :
    certifySubdivision 12 64 32 residualRootUUUUULURectangle
      CertificateObjective.endpointExpression residualRootUUUUULUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootUUUUULU_nonneg {a q : ℝ}
    (haLower : ((41 : ℝ) / 128) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 40))
    (hqLower : ((93 : ℝ) / 400) ≤ q)
    (hqUpper : q ≤ ((217 : ℝ) / 800)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootUUUUULURectangle) (tree := residualRootUUUUULUTree)
  · norm_num [residualRootUUUUULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUUUULURectangle, RatBall.ofBounds]
  · norm_num [residualRootUUUUULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUUUULURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootUUUUULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUUUULURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootUUUUULURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootUUUUULURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootUUUUULUTree_certified

private def residualRootUUUUUULLRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((101 : ℚ) / 320) ((41 : ℚ) / 128),
    RatBall.ofBounds ((217 : ℚ) / 800) ((93 : ℚ) / 320)⟩

private def residualRootUUUUUULLTree : Subdivision :=
.horizontal ((407 : ℚ) / 1280)
  (.vertical ((899 : ℚ) / 3200)
  (.horizontal ((811 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((811 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((899 : ℚ) / 3200)
  (.horizontal ((817 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((817 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootUUUUUULLTree_certified :
    certifySubdivision 12 64 32 residualRootUUUUUULLRectangle
      CertificateObjective.endpointExpression residualRootUUUUUULLTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootUUUUUULL_nonneg {a q : ℝ}
    (haLower : ((101 : ℝ) / 320) ≤ a)
    (haUpper : a ≤ ((41 : ℝ) / 128))
    (hqLower : ((217 : ℝ) / 800) ≤ q)
    (hqUpper : q ≤ ((93 : ℝ) / 320)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootUUUUUULLRectangle) (tree := residualRootUUUUUULLTree)
  · norm_num [residualRootUUUUUULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUUUUULLRectangle, RatBall.ofBounds]
  · norm_num [residualRootUUUUUULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUUUUULLRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootUUUUUULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUUUUULLRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootUUUUUULLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootUUUUUULLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootUUUUUULLTree_certified

private def residualRootUUUUUULURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((101 : ℚ) / 320) ((41 : ℚ) / 128),
    RatBall.ofBounds ((93 : ℚ) / 320) ((31 : ℚ) / 100)⟩

private def residualRootUUUUUULUTree : Subdivision :=
.horizontal ((407 : ℚ) / 1280)
  (.vertical ((961 : ℚ) / 3200)
  (.horizontal ((811 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((811 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((961 : ℚ) / 3200)
  (.horizontal ((817 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((817 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootUUUUUULUTree_certified :
    certifySubdivision 12 64 32 residualRootUUUUUULURectangle
      CertificateObjective.endpointExpression residualRootUUUUUULUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootUUUUUULU_nonneg {a q : ℝ}
    (haLower : ((101 : ℝ) / 320) ≤ a)
    (haUpper : a ≤ ((41 : ℝ) / 128))
    (hqLower : ((93 : ℝ) / 320) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 100)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootUUUUUULURectangle) (tree := residualRootUUUUUULUTree)
  · norm_num [residualRootUUUUUULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUUUUULURectangle, RatBall.ofBounds]
  · norm_num [residualRootUUUUUULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUUUUULURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootUUUUUULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUUUUULURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootUUUUUULURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootUUUUUULURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootUUUUUULUTree_certified

end Frankl
