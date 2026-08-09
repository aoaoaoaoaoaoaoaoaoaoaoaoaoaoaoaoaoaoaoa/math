import Frankl.EndpointCertificate

namespace Frankl

private def qOneCell118RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1127091 : ℚ) / 3200000) ((2273231 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell118RootTree : Subdivision :=
.horizontal ((4527413 : ℚ) / 12800000)
  (.horizontal ((9035777 : ℚ) / 25600000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((72591 : ℚ) / 204800)
  (.leaf .interval)
  (.horizontal ((18166799 : ℚ) / 51200000)
  (.leaf .interval)
  (.leaf .interval)))

private theorem qOneCell118RootTree_certified :
    certifySubdivision 12 64 32 qOneCell118RootRectangle
      CertificateObjective.endpointExpression qOneCell118RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell118Root_nonneg {a q : ℝ}
    (haLower : ((1127091 : ℝ) / 3200000) ≤ a)
    (haUpper : a ≤ ((2273231 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell118RootRectangle) (tree := qOneCell118RootTree)
  · norm_num [qOneCell118RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell118RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell118RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell118RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell118RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell118RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell118RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell118RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell118RootTree_certified

private def qOneCell119RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((2273231 : ℚ) / 6400000) ((57307 : ℚ) / 160000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell119RootTree : Subdivision :=
.horizontal ((4565511 : ℚ) / 12800000)
  (.horizontal ((9111973 : ℚ) / 25600000)
  (.horizontal ((18204897 : ℚ) / 51200000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((3648599 : ℚ) / 10240000)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((9150071 : ℚ) / 25600000)
  (.horizontal ((18281093 : ℚ) / 51200000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((18319191 : ℚ) / 51200000)
  (.leaf .interval)
  (.leaf .interval)))

private theorem qOneCell119RootTree_certified :
    certifySubdivision 12 64 32 qOneCell119RootRectangle
      CertificateObjective.endpointExpression qOneCell119RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell119Root_nonneg {a q : ℝ}
    (haLower : ((2273231 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((57307 : ℝ) / 160000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell119RootRectangle) (tree := qOneCell119RootTree)
  · norm_num [qOneCell119RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell119RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell119RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell119RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell119RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell119RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell119RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell119RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell119RootTree_certified

private def qOneCell120RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((57307 : ℚ) / 160000) ((2311329 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell120RootTree : Subdivision :=
.horizontal ((4603609 : ℚ) / 12800000)
  (.horizontal ((9188169 : ℚ) / 25600000)
  (.horizontal ((18357289 : ℚ) / 51200000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((18395387 : ℚ) / 51200000)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((9226267 : ℚ) / 25600000)
  (.horizontal ((3686697 : ℚ) / 10240000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((18471583 : ℚ) / 51200000)
  (.leaf .interval)
  (.leaf .interval)))

private theorem qOneCell120RootTree_certified :
    certifySubdivision 12 64 32 qOneCell120RootRectangle
      CertificateObjective.endpointExpression qOneCell120RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell120Root_nonneg {a q : ℝ}
    (haLower : ((57307 : ℝ) / 160000) ≤ a)
    (haUpper : a ≤ ((2311329 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell120RootRectangle) (tree := qOneCell120RootTree)
  · norm_num [qOneCell120RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell120RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell120RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell120RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell120RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell120RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell120RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell120RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell120RootTree_certified

end Frankl
