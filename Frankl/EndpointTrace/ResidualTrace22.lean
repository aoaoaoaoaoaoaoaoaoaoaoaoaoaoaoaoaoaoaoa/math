import Frankl.EndpointCertificate

namespace Frankl

private def residualRootUUULUUULRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((193 : ℚ) / 640) ((49 : ℚ) / 160),
    RatBall.ofBounds ((217 : ℚ) / 800) ((93 : ℚ) / 320)⟩

private def residualRootUUULUUULTree : Subdivision :=
.horizontal ((389 : ℚ) / 1280)
  (.vertical ((899 : ℚ) / 3200)
  (.vertical ((1767 : ℚ) / 6400)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((155 : ℚ) / 512)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((899 : ℚ) / 3200)
  (.vertical ((1767 : ℚ) / 6400)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((781 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootUUULUUULTree_certified :
    certifySubdivision 12 64 32 residualRootUUULUUULRectangle
      CertificateObjective.endpointExpression residualRootUUULUUULTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootUUULUUUL_nonneg {a q : ℝ}
    (haLower : ((193 : ℝ) / 640) ≤ a)
    (haUpper : a ≤ ((49 : ℝ) / 160))
    (hqLower : ((217 : ℝ) / 800) ≤ q)
    (hqUpper : q ≤ ((93 : ℝ) / 320)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootUUULUUULRectangle) (tree := residualRootUUULUUULTree)
  · norm_num [residualRootUUULUUULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUULUUULRectangle, RatBall.ofBounds]
  · norm_num [residualRootUUULUUULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUULUUULRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootUUULUUULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUULUUULRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootUUULUUULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootUUULUUULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootUUULUUULTree_certified

private def residualRootUUULUUUURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((193 : ℚ) / 640) ((49 : ℚ) / 160),
    RatBall.ofBounds ((93 : ℚ) / 320) ((31 : ℚ) / 100)⟩

private def residualRootUUULUUUUTree : Subdivision :=
.horizontal ((389 : ℚ) / 1280)
  (.vertical ((961 : ℚ) / 3200)
  (.horizontal ((155 : ℚ) / 512)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((155 : ℚ) / 512)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((961 : ℚ) / 3200)
  (.horizontal ((781 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((781 : ℚ) / 2560)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootUUULUUUUTree_certified :
    certifySubdivision 12 64 32 residualRootUUULUUUURectangle
      CertificateObjective.endpointExpression residualRootUUULUUUUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootUUULUUUU_nonneg {a q : ℝ}
    (haLower : ((193 : ℝ) / 640) ≤ a)
    (haUpper : a ≤ ((49 : ℝ) / 160))
    (hqLower : ((93 : ℝ) / 320) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 100)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootUUULUUUURectangle) (tree := residualRootUUULUUUUTree)
  · norm_num [residualRootUUULUUUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUULUUUURectangle, RatBall.ofBounds]
  · norm_num [residualRootUUULUUUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUULUUUURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootUUULUUUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUULUUUURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootUUULUUUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootUUULUUUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootUUULUUUUTree_certified

private def residualRootUUUULLLRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((49 : ℚ) / 160) ((199 : ℚ) / 640),
    RatBall.ofBounds ((93 : ℚ) / 400) ((217 : ℚ) / 800)⟩

private def residualRootUUUULLLTree : Subdivision :=
.vertical ((403 : ℚ) / 1600)
  (.vertical ((31 : ℚ) / 128)
  (.horizontal ((79 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((79 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((837 : ℚ) / 3200)
  (.horizontal ((79 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((79 : ℚ) / 256)
  (.vertical ((341 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((341 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))))

private theorem residualRootUUUULLLTree_certified :
    certifySubdivision 12 64 32 residualRootUUUULLLRectangle
      CertificateObjective.endpointExpression residualRootUUUULLLTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootUUUULLL_nonneg {a q : ℝ}
    (haLower : ((49 : ℝ) / 160) ≤ a)
    (haUpper : a ≤ ((199 : ℝ) / 640))
    (hqLower : ((93 : ℝ) / 400) ≤ q)
    (hqUpper : q ≤ ((217 : ℝ) / 800)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootUUUULLLRectangle) (tree := residualRootUUUULLLTree)
  · norm_num [residualRootUUUULLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUUULLLRectangle, RatBall.ofBounds]
  · norm_num [residualRootUUUULLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUUULLLRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootUUUULLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUUULLLRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootUUUULLLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootUUUULLLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootUUUULLLTree_certified

end Frankl
