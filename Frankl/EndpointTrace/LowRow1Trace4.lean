import Frankl.EndpointCertificate

namespace Frankl

private def lowRow1Cell0RootUURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((383 : ℚ) / 32000) ((1 : ℚ) / 64),
    RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000)⟩

private def lowRow1Cell0RootUUTree : Subdivision :=
.horizontal ((883 : ℚ) / 64000)
  (.horizontal ((1649 : ℚ) / 128000)
  (.vertical ((1 : ℚ) / 2000)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((1 : ℚ) / 2000)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((1883 : ℚ) / 128000)
  (.vertical ((1 : ℚ) / 2000)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((1 : ℚ) / 2000)
  (.leaf .interval)
  (.leaf .interval)))

private theorem lowRow1Cell0RootUUTree_certified :
    certifySubdivision 12 64 32 lowRow1Cell0RootUURectangle
      CertificateObjective.endpointExpression lowRow1Cell0RootUUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow1Cell0RootUU_nonneg {a q : ℝ}
    (haLower : ((383 : ℝ) / 32000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow1Cell0RootUURectangle) (tree := lowRow1Cell0RootUUTree)
  · norm_num [lowRow1Cell0RootUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell0RootUURectangle, RatBall.ofBounds]
  · norm_num [lowRow1Cell0RootUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell0RootUURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow1Cell0RootUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell0RootUURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow1Cell0RootUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow1Cell0RootUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow1Cell0RootUUTree_certified

private def lowRow1Cell1RootLLLRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 1000) ((133 : ℚ) / 16000),
    RatBall.ofBounds ((1 : ℚ) / 1000) ((137 : ℚ) / 16000)⟩

private def lowRow1Cell1RootLLLTree : Subdivision :=
.vertical ((153 : ℚ) / 32000)
  (.horizontal ((149 : ℚ) / 32000)
  (.vertical ((37 : ℚ) / 12800)
  (.horizontal ((181 : ℚ) / 64000)
  (.vertical ((249 : ℚ) / 128000)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))
  (.horizontal ((181 : ℚ) / 64000)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((37 : ℚ) / 12800)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((149 : ℚ) / 32000)
  (.horizontal ((181 : ℚ) / 64000)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))

private theorem lowRow1Cell1RootLLLTree_certified :
    certifySubdivision 12 64 32 lowRow1Cell1RootLLLRectangle
      CertificateObjective.endpointExpression lowRow1Cell1RootLLLTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow1Cell1RootLLL_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((133 : ℝ) / 16000))
    (hqLower : ((1 : ℝ) / 1000) ≤ q)
    (hqUpper : q ≤ ((137 : ℝ) / 16000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow1Cell1RootLLLRectangle) (tree := lowRow1Cell1RootLLLTree)
  · norm_num [lowRow1Cell1RootLLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell1RootLLLRectangle, RatBall.ofBounds]
  · norm_num [lowRow1Cell1RootLLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell1RootLLLRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow1Cell1RootLLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell1RootLLLRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow1Cell1RootLLLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow1Cell1RootLLLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow1Cell1RootLLLTree_certified

private def lowRow1Cell1RootLLURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((133 : ℚ) / 16000) ((1 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 1000) ((137 : ℚ) / 16000)⟩

private def lowRow1Cell1RootLLUTree : Subdivision :=
.vertical ((153 : ℚ) / 32000)
  (.horizontal ((383 : ℚ) / 32000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((383 : ℚ) / 32000)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow1Cell1RootLLUTree_certified :
    certifySubdivision 12 64 32 lowRow1Cell1RootLLURectangle
      CertificateObjective.endpointExpression lowRow1Cell1RootLLUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow1Cell1RootLLU_nonneg {a q : ℝ}
    (haLower : ((133 : ℝ) / 16000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 1000) ≤ q)
    (hqUpper : q ≤ ((137 : ℝ) / 16000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow1Cell1RootLLURectangle) (tree := lowRow1Cell1RootLLUTree)
  · norm_num [lowRow1Cell1RootLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell1RootLLURectangle, RatBall.ofBounds]
  · norm_num [lowRow1Cell1RootLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell1RootLLURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow1Cell1RootLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell1RootLLURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow1Cell1RootLLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow1Cell1RootLLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow1Cell1RootLLUTree_certified

private def lowRow1Cell1RootLURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 1000) ((1 : ℚ) / 64),
    RatBall.ofBounds ((137 : ℚ) / 16000) ((129 : ℚ) / 8000)⟩

private def lowRow1Cell1RootLUTree : Subdivision :=
.horizontal ((133 : ℚ) / 16000)
  (.horizontal ((149 : ℚ) / 32000)
  (.vertical ((79 : ℚ) / 6400)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((79 : ℚ) / 6400)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((383 : ℚ) / 32000)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow1Cell1RootLUTree_certified :
    certifySubdivision 12 64 32 lowRow1Cell1RootLURectangle
      CertificateObjective.endpointExpression lowRow1Cell1RootLUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow1Cell1RootLU_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((137 : ℝ) / 16000) ≤ q)
    (hqUpper : q ≤ ((129 : ℝ) / 8000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow1Cell1RootLURectangle) (tree := lowRow1Cell1RootLUTree)
  · norm_num [lowRow1Cell1RootLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell1RootLURectangle, RatBall.ofBounds]
  · norm_num [lowRow1Cell1RootLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell1RootLURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow1Cell1RootLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell1RootLURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow1Cell1RootLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow1Cell1RootLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow1Cell1RootLUTree_certified

end Frankl
