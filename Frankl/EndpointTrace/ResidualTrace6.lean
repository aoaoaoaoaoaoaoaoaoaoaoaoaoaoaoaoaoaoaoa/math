import Frankl.EndpointCertificate

namespace Frankl

private def residualRootLUULURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((23 : ℚ) / 80) ((49 : ℚ) / 160),
    RatBall.ofBounds ((93 : ℚ) / 800) ((31 : ℚ) / 200)⟩

private def residualRootLUULUTree : Subdivision :=
.horizontal ((19 : ℚ) / 64)
  (.vertical ((217 : ℚ) / 1600)
  (.horizontal ((187 : ℚ) / 640)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((187 : ℚ) / 640)
  (.vertical ((93 : ℚ) / 640)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((93 : ℚ) / 640)
  (.leaf .interval)
  (.leaf .interval))))
  (.vertical ((217 : ℚ) / 1600)
  (.horizontal ((193 : ℚ) / 640)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((193 : ℚ) / 640)
  (.vertical ((93 : ℚ) / 640)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((93 : ℚ) / 640)
  (.leaf .interval)
  (.leaf .interval))))

private theorem residualRootLUULUTree_certified :
    certifySubdivision 12 64 32 residualRootLUULURectangle
      CertificateObjective.endpointExpression residualRootLUULUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootLUULU_nonneg {a q : ℝ}
    (haLower : ((23 : ℝ) / 80) ≤ a)
    (haUpper : a ≤ ((49 : ℝ) / 160))
    (hqLower : ((93 : ℝ) / 800) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 200)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootLUULURectangle) (tree := residualRootLUULUTree)
  · norm_num [residualRootLUULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLUULURectangle, RatBall.ofBounds]
  · norm_num [residualRootLUULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLUULURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootLUULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLUULURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootLUULURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootLUULURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootLUULUTree_certified

private def residualRootLUUULRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((49 : ℚ) / 160) ((13 : ℚ) / 40),
    RatBall.ofBounds ((31 : ℚ) / 400) ((93 : ℚ) / 800)⟩

private def residualRootLUUULTree : Subdivision :=
.horizontal ((101 : ℚ) / 320)
  (.vertical ((31 : ℚ) / 320)
  (.horizontal ((199 : ℚ) / 640)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((199 : ℚ) / 640)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((31 : ℚ) / 320)
  (.horizontal ((41 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((41 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootLUUULTree_certified :
    certifySubdivision 12 64 32 residualRootLUUULRectangle
      CertificateObjective.endpointExpression residualRootLUUULTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootLUUUL_nonneg {a q : ℝ}
    (haLower : ((49 : ℝ) / 160) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 40))
    (hqLower : ((31 : ℝ) / 400) ≤ q)
    (hqUpper : q ≤ ((93 : ℝ) / 800)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootLUUULRectangle) (tree := residualRootLUUULTree)
  · norm_num [residualRootLUUULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLUUULRectangle, RatBall.ofBounds]
  · norm_num [residualRootLUUULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLUUULRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootLUUULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLUUULRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootLUUULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootLUUULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootLUUULTree_certified

private def residualRootLUUUULRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((49 : ℚ) / 160) ((101 : ℚ) / 320),
    RatBall.ofBounds ((93 : ℚ) / 800) ((31 : ℚ) / 200)⟩

private def residualRootLUUUULTree : Subdivision :=
.vertical ((217 : ℚ) / 1600)
  (.horizontal ((199 : ℚ) / 640)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((199 : ℚ) / 640)
  (.vertical ((93 : ℚ) / 640)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((93 : ℚ) / 640)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootLUUUULTree_certified :
    certifySubdivision 12 64 32 residualRootLUUUULRectangle
      CertificateObjective.endpointExpression residualRootLUUUULTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootLUUUUL_nonneg {a q : ℝ}
    (haLower : ((49 : ℝ) / 160) ≤ a)
    (haUpper : a ≤ ((101 : ℝ) / 320))
    (hqLower : ((93 : ℝ) / 800) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 200)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootLUUUULRectangle) (tree := residualRootLUUUULTree)
  · norm_num [residualRootLUUUULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLUUUULRectangle, RatBall.ofBounds]
  · norm_num [residualRootLUUUULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLUUUULRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootLUUUULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLUUUULRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootLUUUULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootLUUUULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootLUUUULTree_certified

end Frankl
