import Frankl.EndpointCertificate

namespace Frankl

private def residualRootUUUULLURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((199 : ℚ) / 640) ((101 : ℚ) / 320),
    RatBall.ofBounds ((93 : ℚ) / 400) ((217 : ℚ) / 800)⟩

private def residualRootUUUULLUTree : Subdivision :=
.vertical ((403 : ℚ) / 1600)
  (.vertical ((31 : ℚ) / 128)
  (.horizontal ((401 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((401 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((401 : ℚ) / 1280)
  (.vertical ((837 : ℚ) / 3200)
  (.leaf .interval)
  (.vertical ((341 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((837 : ℚ) / 3200)
  (.leaf .interval)
  (.vertical ((341 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))))

private theorem residualRootUUUULLUTree_certified :
    certifySubdivision 12 64 32 residualRootUUUULLURectangle
      CertificateObjective.endpointExpression residualRootUUUULLUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootUUUULLU_nonneg {a q : ℝ}
    (haLower : ((199 : ℝ) / 640) ≤ a)
    (haUpper : a ≤ ((101 : ℝ) / 320))
    (hqLower : ((93 : ℝ) / 400) ≤ q)
    (hqUpper : q ≤ ((217 : ℝ) / 800)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootUUUULLURectangle) (tree := residualRootUUUULLUTree)
  · norm_num [residualRootUUUULLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUUULLURectangle, RatBall.ofBounds]
  · norm_num [residualRootUUUULLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUUULLURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootUUUULLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUUULLURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootUUUULLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootUUUULLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootUUUULLUTree_certified

private def residualRootUUUULULLRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((49 : ℚ) / 160) ((199 : ℚ) / 640),
    RatBall.ofBounds ((217 : ℚ) / 800) ((93 : ℚ) / 320)⟩

private def residualRootUUUULULLTree : Subdivision :=
.horizontal ((79 : ℚ) / 256)
  (.vertical ((899 : ℚ) / 3200)
  (.vertical ((1767 : ℚ) / 6400)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((787 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((899 : ℚ) / 3200)
  (.vertical ((1767 : ℚ) / 6400)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((793 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootUUUULULLTree_certified :
    certifySubdivision 12 64 32 residualRootUUUULULLRectangle
      CertificateObjective.endpointExpression residualRootUUUULULLTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootUUUULULL_nonneg {a q : ℝ}
    (haLower : ((49 : ℝ) / 160) ≤ a)
    (haUpper : a ≤ ((199 : ℝ) / 640))
    (hqLower : ((217 : ℝ) / 800) ≤ q)
    (hqUpper : q ≤ ((93 : ℝ) / 320)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootUUUULULLRectangle) (tree := residualRootUUUULULLTree)
  · norm_num [residualRootUUUULULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUUULULLRectangle, RatBall.ofBounds]
  · norm_num [residualRootUUUULULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUUULULLRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootUUUULULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUUULULLRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootUUUULULLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootUUUULULLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootUUUULULLTree_certified

private def residualRootUUUULULURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((49 : ℚ) / 160) ((199 : ℚ) / 640),
    RatBall.ofBounds ((93 : ℚ) / 320) ((31 : ℚ) / 100)⟩

private def residualRootUUUULULUTree : Subdivision :=
.horizontal ((79 : ℚ) / 256)
  (.vertical ((961 : ℚ) / 3200)
  (.horizontal ((787 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((787 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((961 : ℚ) / 3200)
  (.horizontal ((793 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((793 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootUUUULULUTree_certified :
    certifySubdivision 12 64 32 residualRootUUUULULURectangle
      CertificateObjective.endpointExpression residualRootUUUULULUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootUUUULULU_nonneg {a q : ℝ}
    (haLower : ((49 : ℝ) / 160) ≤ a)
    (haUpper : a ≤ ((199 : ℝ) / 640))
    (hqLower : ((93 : ℝ) / 320) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 100)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootUUUULULURectangle) (tree := residualRootUUUULULUTree)
  · norm_num [residualRootUUUULULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUUULULURectangle, RatBall.ofBounds]
  · norm_num [residualRootUUUULULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUUULULURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootUUUULULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUUULULURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootUUUULULURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootUUUULULURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootUUUULULUTree_certified

end Frankl
