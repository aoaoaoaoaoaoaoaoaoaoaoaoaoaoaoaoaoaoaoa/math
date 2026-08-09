import Frankl.EndpointCertificate

namespace Frankl

private def qOneCell124RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((592119 : ℚ) / 1600000) ((95501 : ℚ) / 256000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell124RootTree : Subdivision :=
.horizontal ((4756001 : ℚ) / 12800000)
  (.horizontal ((9492953 : ℚ) / 25600000)
  (.horizontal ((18966857 : ℚ) / 51200000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((3800991 : ℚ) / 10240000)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((9531051 : ℚ) / 25600000)
  (.horizontal ((19043053 : ℚ) / 51200000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((19081151 : ℚ) / 51200000)
  (.leaf .interval)
  (.leaf .interval)))

private theorem qOneCell124RootTree_certified :
    certifySubdivision 12 64 32 qOneCell124RootRectangle
      CertificateObjective.endpointExpression qOneCell124RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell124Root_nonneg {a q : ℝ}
    (haLower : ((592119 : ℝ) / 1600000) ≤ a)
    (haUpper : a ≤ ((95501 : ℝ) / 256000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell124RootRectangle) (tree := qOneCell124RootTree)
  · norm_num [qOneCell124RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell124RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell124RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell124RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell124RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell124RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell124RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell124RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell124RootTree_certified

private def qOneCell125RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((95501 : ℚ) / 256000) ((1203287 : ℚ) / 3200000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell125RootTree : Subdivision :=
.horizontal ((4794099 : ℚ) / 12800000)
  (.horizontal ((9569149 : ℚ) / 25600000)
  (.horizontal ((19119249 : ℚ) / 51200000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((19157347 : ℚ) / 51200000)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((9607247 : ℚ) / 25600000)
  (.horizontal ((3839089 : ℚ) / 10240000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((19233543 : ℚ) / 51200000)
  (.leaf .interval)
  (.leaf .interval)))

private theorem qOneCell125RootTree_certified :
    certifySubdivision 12 64 32 qOneCell125RootRectangle
      CertificateObjective.endpointExpression qOneCell125RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell125Root_nonneg {a q : ℝ}
    (haLower : ((95501 : ℝ) / 256000) ≤ a)
    (haUpper : a ≤ ((1203287 : ℝ) / 3200000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell125RootRectangle) (tree := qOneCell125RootTree)
  · norm_num [qOneCell125RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell125RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell125RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell125RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell125RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell125RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell125RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell125RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell125RootTree_certified

private def qOneCell126RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1203287 : ℚ) / 3200000) ((2425623 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell126RootTree : Subdivision :=
.horizontal ((4832197 : ℚ) / 12800000)
  (.horizontal ((1929069 : ℚ) / 5120000)
  (.horizontal ((19271641 : ℚ) / 51200000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((19309739 : ℚ) / 51200000)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((9683443 : ℚ) / 25600000)
  (.horizontal ((19347837 : ℚ) / 51200000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((3877187 : ℚ) / 10240000)
  (.leaf .interval)
  (.leaf .interval)))

private theorem qOneCell126RootTree_certified :
    certifySubdivision 12 64 32 qOneCell126RootRectangle
      CertificateObjective.endpointExpression qOneCell126RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell126Root_nonneg {a q : ℝ}
    (haLower : ((1203287 : ℝ) / 3200000) ≤ a)
    (haUpper : a ≤ ((2425623 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell126RootRectangle) (tree := qOneCell126RootTree)
  · norm_num [qOneCell126RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell126RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell126RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell126RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell126RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell126RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell126RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell126RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell126RootTree_certified

end Frankl
