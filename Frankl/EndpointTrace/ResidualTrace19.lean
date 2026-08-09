import Frankl.EndpointCertificate

namespace Frankl

private def residualRootUUULLLLRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((23 : ℚ) / 80) ((19 : ℚ) / 64),
    RatBall.ofBounds ((93 : ℚ) / 400) ((403 : ℚ) / 1600)⟩

private def residualRootUUULLLLTree : Subdivision :=
.horizontal ((187 : ℚ) / 640)
  (.vertical ((31 : ℚ) / 128)
  (.horizontal ((371 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((371 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((31 : ℚ) / 128)
  (.horizontal ((377 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((377 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootUUULLLLTree_certified :
    certifySubdivision 12 64 32 residualRootUUULLLLRectangle
      CertificateObjective.endpointExpression residualRootUUULLLLTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootUUULLLL_nonneg {a q : ℝ}
    (haLower : ((23 : ℝ) / 80) ≤ a)
    (haUpper : a ≤ ((19 : ℝ) / 64))
    (hqLower : ((93 : ℝ) / 400) ≤ q)
    (hqUpper : q ≤ ((403 : ℝ) / 1600)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootUUULLLLRectangle) (tree := residualRootUUULLLLTree)
  · norm_num [residualRootUUULLLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUULLLLRectangle, RatBall.ofBounds]
  · norm_num [residualRootUUULLLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUULLLLRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootUUULLLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUULLLLRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootUUULLLLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootUUULLLLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootUUULLLLTree_certified

private def residualRootUUULLLURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((23 : ℚ) / 80) ((19 : ℚ) / 64),
    RatBall.ofBounds ((403 : ℚ) / 1600) ((217 : ℚ) / 800)⟩

private def residualRootUUULLLUTree : Subdivision :=
.horizontal ((187 : ℚ) / 640)
  (.vertical ((837 : ℚ) / 3200)
  (.horizontal ((371 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((371 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((837 : ℚ) / 3200)
  (.horizontal ((377 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((377 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootUUULLLUTree_certified :
    certifySubdivision 12 64 32 residualRootUUULLLURectangle
      CertificateObjective.endpointExpression residualRootUUULLLUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootUUULLLU_nonneg {a q : ℝ}
    (haLower : ((23 : ℝ) / 80) ≤ a)
    (haUpper : a ≤ ((19 : ℝ) / 64))
    (hqLower : ((403 : ℝ) / 1600) ≤ q)
    (hqUpper : q ≤ ((217 : ℝ) / 800)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootUUULLLURectangle) (tree := residualRootUUULLLUTree)
  · norm_num [residualRootUUULLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUULLLURectangle, RatBall.ofBounds]
  · norm_num [residualRootUUULLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUULLLURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootUUULLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUULLLURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootUUULLLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootUUULLLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootUUULLLUTree_certified

private def residualRootUUULLULRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((19 : ℚ) / 64) ((49 : ℚ) / 160),
    RatBall.ofBounds ((93 : ℚ) / 400) ((403 : ℚ) / 1600)⟩

private def residualRootUUULLULTree : Subdivision :=
.horizontal ((193 : ℚ) / 640)
  (.vertical ((31 : ℚ) / 128)
  (.horizontal ((383 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((383 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((31 : ℚ) / 128)
  (.horizontal ((389 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((389 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootUUULLULTree_certified :
    certifySubdivision 12 64 32 residualRootUUULLULRectangle
      CertificateObjective.endpointExpression residualRootUUULLULTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootUUULLUL_nonneg {a q : ℝ}
    (haLower : ((19 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((49 : ℝ) / 160))
    (hqLower : ((93 : ℝ) / 400) ≤ q)
    (hqUpper : q ≤ ((403 : ℝ) / 1600)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootUUULLULRectangle) (tree := residualRootUUULLULTree)
  · norm_num [residualRootUUULLULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUULLULRectangle, RatBall.ofBounds]
  · norm_num [residualRootUUULLULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUULLULRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootUUULLULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootUUULLULRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootUUULLULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootUUULLULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootUUULLULTree_certified

end Frankl
