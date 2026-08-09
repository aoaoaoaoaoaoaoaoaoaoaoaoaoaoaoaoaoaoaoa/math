import Frankl.EndpointCertificate

namespace Frankl

private def qOneCell121RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((2311329 : ℚ) / 6400000) ((1165189 : ℚ) / 3200000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell121RootTree : Subdivision :=
.horizontal ((4641707 : ℚ) / 12800000)
  (.horizontal ((1852873 : ℚ) / 5120000)
  (.horizontal ((18509681 : ℚ) / 51200000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((18547779 : ℚ) / 51200000)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((9302463 : ℚ) / 25600000)
  (.horizontal ((18585877 : ℚ) / 51200000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((744959 : ℚ) / 2048000)
  (.leaf .interval)
  (.leaf .interval)))

private theorem qOneCell121RootTree_certified :
    certifySubdivision 12 64 32 qOneCell121RootRectangle
      CertificateObjective.endpointExpression qOneCell121RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell121Root_nonneg {a q : ℝ}
    (haLower : ((2311329 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((1165189 : ℝ) / 3200000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell121RootRectangle) (tree := qOneCell121RootTree)
  · norm_num [qOneCell121RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell121RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell121RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell121RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell121RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell121RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell121RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell121RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell121RootTree_certified

private def qOneCell122RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1165189 : ℚ) / 3200000) ((2349427 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell122RootTree : Subdivision :=
.horizontal ((935961 : ℚ) / 2560000)
  (.horizontal ((9340561 : ℚ) / 25600000)
  (.horizontal ((18662073 : ℚ) / 51200000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((18700171 : ℚ) / 51200000)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((9378659 : ℚ) / 25600000)
  (.horizontal ((18738269 : ℚ) / 51200000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((18776367 : ℚ) / 51200000)
  (.leaf .interval)
  (.leaf .interval)))

private theorem qOneCell122RootTree_certified :
    certifySubdivision 12 64 32 qOneCell122RootRectangle
      CertificateObjective.endpointExpression qOneCell122RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell122Root_nonneg {a q : ℝ}
    (haLower : ((1165189 : ℝ) / 3200000) ≤ a)
    (haUpper : a ≤ ((2349427 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell122RootRectangle) (tree := qOneCell122RootTree)
  · norm_num [qOneCell122RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell122RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell122RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell122RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell122RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell122RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell122RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell122RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell122RootTree_certified

private def qOneCell123RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((2349427 : ℚ) / 6400000) ((592119 : ℚ) / 1600000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell123RootTree : Subdivision :=
.horizontal ((4717903 : ℚ) / 12800000)
  (.horizontal ((9416757 : ℚ) / 25600000)
  (.horizontal ((3762893 : ℚ) / 10240000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((18852563 : ℚ) / 51200000)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((1890971 : ℚ) / 5120000)
  (.horizontal ((18890661 : ℚ) / 51200000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((18928759 : ℚ) / 51200000)
  (.leaf .interval)
  (.leaf .interval)))

private theorem qOneCell123RootTree_certified :
    certifySubdivision 12 64 32 qOneCell123RootRectangle
      CertificateObjective.endpointExpression qOneCell123RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell123Root_nonneg {a q : ℝ}
    (haLower : ((2349427 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((592119 : ℝ) / 1600000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell123RootRectangle) (tree := qOneCell123RootTree)
  · norm_num [qOneCell123RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell123RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell123RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell123RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell123RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell123RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell123RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell123RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell123RootTree_certified

end Frankl
