import Frankl.EndpointCertificate

namespace Frankl

private def residualRootLLLLLULURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((89 : ℚ) / 320) ((23 : ℚ) / 80),
    RatBall.ofBounds ((0 : ℚ) / 1) ((31 : ℚ) / 3200)⟩

private def residualRootLLLLLULUTree : Subdivision :=
.vertical ((31 : ℚ) / 6400)
  (.horizontal ((181 : ℚ) / 640)
  (.vertical ((31 : ℚ) / 12800)
  (.horizontal ((359 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))
  (.vertical ((31 : ℚ) / 12800)
  (.horizontal ((73 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval)))
  (.leaf .interval)

private theorem residualRootLLLLLULUTree_certified :
    certifySubdivision 12 64 32 residualRootLLLLLULURectangle
      CertificateObjective.endpointExpression residualRootLLLLLULUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootLLLLLULU_nonneg {a q : ℝ}
    (haLower : ((89 : ℝ) / 320) ≤ a)
    (haUpper : a ≤ ((23 : ℝ) / 80))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 3200)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootLLLLLULURectangle) (tree := residualRootLLLLLULUTree)
  · norm_num [residualRootLLLLLULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLLLULURectangle, RatBall.ofBounds]
  · norm_num [residualRootLLLLLULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLLLULURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootLLLLLULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLLLULURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootLLLLLULURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootLLLLLULURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootLLLLLULUTree_certified

private def residualRootLLLLLUURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((43 : ℚ) / 160) ((23 : ℚ) / 80),
    RatBall.ofBounds ((31 : ℚ) / 3200) ((31 : ℚ) / 1600)⟩

private def residualRootLLLLLUUTree : Subdivision :=
.horizontal ((89 : ℚ) / 320)
  (.leaf .interval)
  (.leaf .interval)

private theorem residualRootLLLLLUUTree_certified :
    certifySubdivision 12 64 32 residualRootLLLLLUURectangle
      CertificateObjective.endpointExpression residualRootLLLLLUUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootLLLLLUU_nonneg {a q : ℝ}
    (haLower : ((43 : ℝ) / 160) ≤ a)
    (haUpper : a ≤ ((23 : ℝ) / 80))
    (hqLower : ((31 : ℝ) / 3200) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 1600)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootLLLLLUURectangle) (tree := residualRootLLLLLUUTree)
  · norm_num [residualRootLLLLLUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLLLUURectangle, RatBall.ofBounds]
  · norm_num [residualRootLLLLLUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLLLUURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootLLLLLUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLLLUURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootLLLLLUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootLLLLLUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootLLLLLUUTree_certified

private def residualRootLLLLURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 4) ((23 : ℚ) / 80),
    RatBall.ofBounds ((31 : ℚ) / 1600) ((31 : ℚ) / 800)⟩

private def residualRootLLLLUTree : Subdivision :=
.horizontal ((43 : ℚ) / 160)
  (.horizontal ((83 : ℚ) / 320)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((89 : ℚ) / 320)
  (.leaf .interval)
  (.leaf .interval))

private theorem residualRootLLLLUTree_certified :
    certifySubdivision 12 64 32 residualRootLLLLURectangle
      CertificateObjective.endpointExpression residualRootLLLLUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootLLLLU_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 4) ≤ a)
    (haUpper : a ≤ ((23 : ℝ) / 80))
    (hqLower : ((31 : ℝ) / 1600) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 800)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootLLLLURectangle) (tree := residualRootLLLLUTree)
  · norm_num [residualRootLLLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLLURectangle, RatBall.ofBounds]
  · norm_num [residualRootLLLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLLURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootLLLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLLURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootLLLLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootLLLLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootLLLLUTree_certified

private def residualRootLLLULLLLRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((23 : ℚ) / 80) ((19 : ℚ) / 64),
    RatBall.ofBounds ((0 : ℚ) / 1) ((31 : ℚ) / 3200)⟩

private def residualRootLLLULLLLTree : Subdivision :=
.vertical ((31 : ℚ) / 6400)
  (.horizontal ((187 : ℚ) / 640)
  (.vertical ((31 : ℚ) / 12800)
  (.horizontal ((371 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))
  (.vertical ((31 : ℚ) / 12800)
  (.horizontal ((377 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval)))
  (.leaf .interval)

private theorem residualRootLLLULLLLTree_certified :
    certifySubdivision 12 64 32 residualRootLLLULLLLRectangle
      CertificateObjective.endpointExpression residualRootLLLULLLLTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootLLLULLLL_nonneg {a q : ℝ}
    (haLower : ((23 : ℝ) / 80) ≤ a)
    (haUpper : a ≤ ((19 : ℝ) / 64))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 3200)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootLLLULLLLRectangle) (tree := residualRootLLLULLLLTree)
  · norm_num [residualRootLLLULLLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLULLLLRectangle, RatBall.ofBounds]
  · norm_num [residualRootLLLULLLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLULLLLRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootLLLULLLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLULLLLRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootLLLULLLLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootLLLULLLLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootLLLULLLLTree_certified

private def residualRootLLLULLLURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((19 : ℚ) / 64) ((49 : ℚ) / 160),
    RatBall.ofBounds ((0 : ℚ) / 1) ((31 : ℚ) / 3200)⟩

private def residualRootLLLULLLUTree : Subdivision :=
.vertical ((31 : ℚ) / 6400)
  (.horizontal ((193 : ℚ) / 640)
  (.vertical ((31 : ℚ) / 12800)
  (.horizontal ((383 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))
  (.vertical ((31 : ℚ) / 12800)
  (.horizontal ((389 : ℚ) / 1280)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval)))
  (.leaf .interval)

private theorem residualRootLLLULLLUTree_certified :
    certifySubdivision 12 64 32 residualRootLLLULLLURectangle
      CertificateObjective.endpointExpression residualRootLLLULLLUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem residualRootLLLULLLU_nonneg {a q : ℝ}
    (haLower : ((19 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((49 : ℝ) / 160))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((31 : ℝ) / 3200)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := residualRootLLLULLLURectangle) (tree := residualRootLLLULLLUTree)
  · norm_num [residualRootLLLULLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLULLLURectangle, RatBall.ofBounds]
  · norm_num [residualRootLLLULLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLULLLURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [residualRootLLLULLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [residualRootLLLULLLURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [residualRootLLLULLLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [residualRootLLLULLLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact residualRootLLLULLLUTree_certified

end Frankl
