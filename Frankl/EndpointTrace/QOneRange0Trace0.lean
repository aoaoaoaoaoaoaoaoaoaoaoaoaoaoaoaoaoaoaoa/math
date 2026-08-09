import Frankl.EndpointCertificate

namespace Frankl

private def qOneCell0RootLRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 1000) ((31849 : ℚ) / 12800000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell0RootLTree : Subdivision :=
.horizontal ((44649 : ℚ) / 25600000)
  (.horizontal ((70249 : ℚ) / 51200000)
  (.horizontal ((121449 : ℚ) / 102400000)
  (.horizontal ((223849 : ℚ) / 204800000)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))
  (.horizontal ((159547 : ℚ) / 102400000)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((108347 : ℚ) / 51200000)
  (.horizontal ((39529 : ℚ) / 20480000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((235743 : ℚ) / 102400000)
  (.leaf .interval)
  (.leaf .interval)))

private theorem qOneCell0RootLTree_certified :
    certifySubdivision 12 64 32 qOneCell0RootLRectangle
      CertificateObjective.endpointExpression qOneCell0RootLTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell0RootL_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((31849 : ℝ) / 12800000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell0RootLRectangle) (tree := qOneCell0RootLTree)
  · norm_num [qOneCell0RootLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell0RootLRectangle, RatBall.ofBounds]
  · norm_num [qOneCell0RootLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell0RootLRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell0RootLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell0RootLRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell0RootLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell0RootLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell0RootLTree_certified

private def qOneCell0RootURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((31849 : ℚ) / 12800000) ((25449 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell0RootUTree : Subdivision :=
.horizontal ((82747 : ℚ) / 25600000)
  (.horizontal ((29289 : ℚ) / 10240000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((184543 : ℚ) / 51200000)
  (.leaf .interval)
  (.leaf .interval))

private theorem qOneCell0RootUTree_certified :
    certifySubdivision 12 64 32 qOneCell0RootURectangle
      CertificateObjective.endpointExpression qOneCell0RootUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell0RootU_nonneg {a q : ℝ}
    (haLower : ((31849 : ℝ) / 12800000) ≤ a)
    (haUpper : a ≤ ((25449 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell0RootURectangle) (tree := qOneCell0RootUTree)
  · norm_num [qOneCell0RootURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell0RootURectangle, RatBall.ofBounds]
  · norm_num [qOneCell0RootURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell0RootURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell0RootURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell0RootURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell0RootURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell0RootURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell0RootUTree_certified

private def qOneCell1RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((25449 : ℚ) / 6400000) ((22249 : ℚ) / 3200000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell1RootTree : Subdivision :=
.horizontal ((69947 : ℚ) / 12800000)
  (.horizontal ((24169 : ℚ) / 5120000)
  (.horizontal ((222641 : ℚ) / 51200000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((260739 : ℚ) / 51200000)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((158943 : ℚ) / 25600000)
  (.leaf .interval)
  (.leaf .interval))

private theorem qOneCell1RootTree_certified :
    certifySubdivision 12 64 32 qOneCell1RootRectangle
      CertificateObjective.endpointExpression qOneCell1RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell1Root_nonneg {a q : ℝ}
    (haLower : ((25449 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((22249 : ℝ) / 3200000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell1RootRectangle) (tree := qOneCell1RootTree)
  · norm_num [qOneCell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell1RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell1RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell1RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell1RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell1RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell1RootTree_certified

private def qOneCell2RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((22249 : ℚ) / 3200000) ((63547 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell2RootTree : Subdivision :=
.horizontal ((21609 : ℚ) / 2560000)
  (.horizontal ((197041 : ℚ) / 25600000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((235139 : ℚ) / 25600000)
  (.leaf .interval)
  (.leaf .interval))

private theorem qOneCell2RootTree_certified :
    certifySubdivision 12 64 32 qOneCell2RootRectangle
      CertificateObjective.endpointExpression qOneCell2RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell2Root_nonneg {a q : ℝ}
    (haLower : ((22249 : ℝ) / 3200000) ≤ a)
    (haUpper : a ≤ ((63547 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell2RootRectangle) (tree := qOneCell2RootTree)
  · norm_num [qOneCell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell2RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell2RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell2RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell2RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell2RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell2RootTree_certified

private def qOneCell3RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((63547 : ℚ) / 6400000) ((20649 : ℚ) / 1600000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell3RootTree : Subdivision :=
.horizontal ((146143 : ℚ) / 12800000)
  (.horizontal ((273237 : ℚ) / 25600000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((62267 : ℚ) / 5120000)
  (.leaf .interval)
  (.leaf .interval))

private theorem qOneCell3RootTree_certified :
    certifySubdivision 12 64 32 qOneCell3RootRectangle
      CertificateObjective.endpointExpression qOneCell3RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell3Root_nonneg {a q : ℝ}
    (haLower : ((63547 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((20649 : ℝ) / 1600000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell3RootRectangle) (tree := qOneCell3RootTree)
  · norm_num [qOneCell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell3RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell3RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell3RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell3RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell3RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell3RootTree_certified

end Frankl
