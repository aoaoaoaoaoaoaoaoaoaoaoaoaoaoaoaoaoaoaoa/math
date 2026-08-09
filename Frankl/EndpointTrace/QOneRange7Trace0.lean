import Frankl.EndpointCertificate

namespace Frankl

private def qOneCell112RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((133743 : ℚ) / 400000) ((2158937 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell112RootTree : Subdivision :=
.horizontal ((171953 : ℚ) / 512000)
  (.horizontal ((8578601 : ℚ) / 25600000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((8616699 : ℚ) / 25600000)
  (.leaf .interval)
  (.leaf .interval))

private theorem qOneCell112RootTree_certified :
    certifySubdivision 12 64 32 qOneCell112RootRectangle
      CertificateObjective.endpointExpression qOneCell112RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell112Root_nonneg {a q : ℝ}
    (haLower : ((133743 : ℝ) / 400000) ≤ a)
    (haUpper : a ≤ ((2158937 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell112RootRectangle) (tree := qOneCell112RootTree)
  · norm_num [qOneCell112RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell112RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell112RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell112RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell112RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell112RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell112RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell112RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell112RootTree_certified

private def qOneCell113RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((2158937 : ℚ) / 6400000) ((1088993 : ℚ) / 3200000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell113RootTree : Subdivision :=
.horizontal ((4336923 : ℚ) / 12800000)
  (.horizontal ((8654797 : ℚ) / 25600000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((1738579 : ℚ) / 5120000)
  (.leaf .interval)
  (.leaf .interval))

private theorem qOneCell113RootTree_certified :
    certifySubdivision 12 64 32 qOneCell113RootRectangle
      CertificateObjective.endpointExpression qOneCell113RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell113Root_nonneg {a q : ℝ}
    (haLower : ((2158937 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((1088993 : ℝ) / 3200000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell113RootRectangle) (tree := qOneCell113RootTree)
  · norm_num [qOneCell113RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell113RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell113RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell113RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell113RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell113RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell113RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell113RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell113RootTree_certified

private def qOneCell114RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1088993 : ℚ) / 3200000) ((439407 : ℚ) / 1280000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell114RootTree : Subdivision :=
.horizontal ((4375021 : ℚ) / 12800000)
  (.horizontal ((8730993 : ℚ) / 25600000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((8769091 : ℚ) / 25600000)
  (.leaf .interval)
  (.leaf .interval))

private theorem qOneCell114RootTree_certified :
    certifySubdivision 12 64 32 qOneCell114RootRectangle
      CertificateObjective.endpointExpression qOneCell114RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell114Root_nonneg {a q : ℝ}
    (haLower : ((1088993 : ℝ) / 3200000) ≤ a)
    (haUpper : a ≤ ((439407 : ℝ) / 1280000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell114RootRectangle) (tree := qOneCell114RootTree)
  · norm_num [qOneCell114RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell114RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell114RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell114RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell114RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell114RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell114RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell114RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell114RootTree_certified

private def qOneCell115RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((439407 : ℚ) / 1280000) ((554021 : ℚ) / 1600000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell115RootTree : Subdivision :=
.horizontal ((4413119 : ℚ) / 12800000)
  (.horizontal ((8807189 : ℚ) / 25600000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((8845287 : ℚ) / 25600000)
  (.leaf .interval)
  (.leaf .interval))

private theorem qOneCell115RootTree_certified :
    certifySubdivision 12 64 32 qOneCell115RootRectangle
      CertificateObjective.endpointExpression qOneCell115RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell115Root_nonneg {a q : ℝ}
    (haLower : ((439407 : ℝ) / 1280000) ≤ a)
    (haUpper : a ≤ ((554021 : ℝ) / 1600000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell115RootRectangle) (tree := qOneCell115RootTree)
  · norm_num [qOneCell115RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell115RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell115RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell115RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell115RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell115RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell115RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell115RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell115RootTree_certified

private def qOneCell116RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((554021 : ℚ) / 1600000) ((2235133 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell116RootTree : Subdivision :=
.horizontal ((4451217 : ℚ) / 12800000)
  (.horizontal ((1776677 : ℚ) / 5120000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((8921483 : ℚ) / 25600000)
  (.leaf .interval)
  (.leaf .interval))

private theorem qOneCell116RootTree_certified :
    certifySubdivision 12 64 32 qOneCell116RootRectangle
      CertificateObjective.endpointExpression qOneCell116RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell116Root_nonneg {a q : ℝ}
    (haLower : ((554021 : ℝ) / 1600000) ≤ a)
    (haUpper : a ≤ ((2235133 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell116RootRectangle) (tree := qOneCell116RootTree)
  · norm_num [qOneCell116RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell116RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell116RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell116RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell116RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell116RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell116RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell116RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell116RootTree_certified

private def qOneCell117RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((2235133 : ℚ) / 6400000) ((1127091 : ℚ) / 3200000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell117RootTree : Subdivision :=
.horizontal ((897863 : ℚ) / 2560000)
  (.horizontal ((8959581 : ℚ) / 25600000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((8997679 : ℚ) / 25600000)
  (.leaf .interval)
  (.leaf .interval))

private theorem qOneCell117RootTree_certified :
    certifySubdivision 12 64 32 qOneCell117RootRectangle
      CertificateObjective.endpointExpression qOneCell117RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell117Root_nonneg {a q : ℝ}
    (haLower : ((2235133 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((1127091 : ℝ) / 3200000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell117RootRectangle) (tree := qOneCell117RootTree)
  · norm_num [qOneCell117RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell117RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell117RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell117RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell117RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell117RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell117RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell117RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell117RootTree_certified

end Frankl
