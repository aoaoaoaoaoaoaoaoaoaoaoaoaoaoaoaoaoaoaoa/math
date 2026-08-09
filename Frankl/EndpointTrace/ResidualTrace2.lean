import Frankl.EndpointCertificate

namespace Frankl

private def residualRootLLLULLURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((23 : ℚ) / 80) ((49 : ℚ) / 160),
    RatBall.ofBounds ((31 : ℚ) / 3200) ((31 : ℚ) / 1600)⟩

private def residualRootLLLULLUTree : Subdivision :=
.horizontal ((19 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval)

private theorem residualRootLLLULLUTree_certified :
    certifySubdivision 12 64 32 residualRootLLLULLURectangle
      CertificateObjective.endpointExpression residualRootLLLULLUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootLLLULLU_nonneg {a q : ℝ}
    (haLower : ((23 : ℝ) / 80) ≤ a)
    (haUpper : a ≤ ((49 : ℝ) / 160))
    (hqLower : ((31 : ℝ) / 3200) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 1600)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootLLLULLURectangle) (tree := residualRootLLLULLUTree)
  · norm_num [residualRootLLLULLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLULLURectangle, RatBall.ofBounds]
  · norm_num [residualRootLLLULLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLULLURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootLLLULLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLULLURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootLLLULLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootLLLULLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootLLLULLUTree_certified

private def residualRootLLLULULLRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((49 : ℚ) / 160) ((101 : ℚ) / 320),
    RatBall.ofBounds ((0 : ℚ) / 1) ((31 : ℚ) / 3200)⟩

private def residualRootLLLULULLTree : Subdivision :=
.vertical ((31 : ℚ) / 6400)
  (.horizontal ((199 : ℚ) / 640)
  (.vertical ((31 : ℚ) / 12800)
  (.horizontal ((79 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))
  (.vertical ((31 : ℚ) / 12800)
  (.horizontal ((401 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval)))
  (.leaf .interval)

private theorem residualRootLLLULULLTree_certified :
    certifySubdivision 12 64 32 residualRootLLLULULLRectangle
      CertificateObjective.endpointExpression residualRootLLLULULLTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootLLLULULL_nonneg {a q : ℝ}
    (haLower : ((49 : ℝ) / 160) ≤ a)
    (haUpper : a ≤ ((101 : ℝ) / 320))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 3200)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootLLLULULLRectangle) (tree := residualRootLLLULULLTree)
  · norm_num [residualRootLLLULULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLULULLRectangle, RatBall.ofBounds]
  · norm_num [residualRootLLLULULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLULULLRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootLLLULULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLULULLRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootLLLULULLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootLLLULULLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootLLLULULLTree_certified

private def residualRootLLLULULURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((101 : ℚ) / 320) ((13 : ℚ) / 40),
    RatBall.ofBounds ((0 : ℚ) / 1) ((31 : ℚ) / 3200)⟩

private def residualRootLLLULULUTree : Subdivision :=
.vertical ((31 : ℚ) / 6400)
  (.horizontal ((41 : ℚ) / 128)
  (.vertical ((31 : ℚ) / 12800)
  (.horizontal ((407 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))
  (.vertical ((31 : ℚ) / 12800)
  (.horizontal ((413 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval)))
  (.leaf .interval)

private theorem residualRootLLLULULUTree_certified :
    certifySubdivision 12 64 32 residualRootLLLULULURectangle
      CertificateObjective.endpointExpression residualRootLLLULULUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootLLLULULU_nonneg {a q : ℝ}
    (haLower : ((101 : ℝ) / 320) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 40))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 3200)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootLLLULULURectangle) (tree := residualRootLLLULULUTree)
  · norm_num [residualRootLLLULULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLULULURectangle, RatBall.ofBounds]
  · norm_num [residualRootLLLULULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLULULURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootLLLULULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLULULURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootLLLULULURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootLLLULULURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootLLLULULUTree_certified

private def residualRootLLLULUURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((49 : ℚ) / 160) ((13 : ℚ) / 40),
    RatBall.ofBounds ((31 : ℚ) / 3200) ((31 : ℚ) / 1600)⟩

private def residualRootLLLULUUTree : Subdivision :=
.horizontal ((101 : ℚ) / 320)
  (.leaf .interval)
  (.leaf .interval)

private theorem residualRootLLLULUUTree_certified :
    certifySubdivision 12 64 32 residualRootLLLULUURectangle
      CertificateObjective.endpointExpression residualRootLLLULUUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootLLLULUU_nonneg {a q : ℝ}
    (haLower : ((49 : ℝ) / 160) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 40))
    (hqLower : ((31 : ℝ) / 3200) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 1600)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootLLLULUURectangle) (tree := residualRootLLLULUUTree)
  · norm_num [residualRootLLLULUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLULUURectangle, RatBall.ofBounds]
  · norm_num [residualRootLLLULUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLULUURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootLLLULUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLULUURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootLLLULUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootLLLULUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootLLLULUUTree_certified

private def residualRootLLLUURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((23 : ℚ) / 80) ((13 : ℚ) / 40),
    RatBall.ofBounds ((31 : ℚ) / 1600) ((31 : ℚ) / 800)⟩

private def residualRootLLLUUTree : Subdivision :=
.horizontal ((49 : ℚ) / 160)
  (.horizontal ((19 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((101 : ℚ) / 320)
  (.vertical ((93 : ℚ) / 3200)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((41 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)))

private theorem residualRootLLLUUTree_certified :
    certifySubdivision 12 64 32 residualRootLLLUURectangle
      CertificateObjective.endpointExpression residualRootLLLUUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootLLLUU_nonneg {a q : ℝ}
    (haLower : ((23 : ℝ) / 80) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 40))
    (hqLower : ((31 : ℝ) / 1600) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 800)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootLLLUURectangle) (tree := residualRootLLLUUTree)
  · norm_num [residualRootLLLUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLUURectangle, RatBall.ofBounds]
  · norm_num [residualRootLLLUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLUURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootLLLUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLUURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootLLLUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootLLLUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootLLLUUTree_certified

end Frankl
