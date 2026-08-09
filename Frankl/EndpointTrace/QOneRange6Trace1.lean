import Frankl.EndpointCertificate

namespace Frankl

private def qOneCell107RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((2044643 : ℚ) / 6400000) ((515923 : ℚ) / 1600000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell107RootTree : Subdivision :=
.horizontal ((821667 : ℚ) / 2560000)
  (.horizontal ((8197621 : ℚ) / 25600000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((8235719 : ℚ) / 25600000)
  (.leaf .interval)
  (.leaf .interval))

private theorem qOneCell107RootTree_certified :
    certifySubdivision 12 64 32 qOneCell107RootRectangle
      CertificateObjective.endpointExpression qOneCell107RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell107Root_nonneg {a q : ℝ}
    (haLower : ((2044643 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((515923 : ℝ) / 1600000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell107RootRectangle) (tree := qOneCell107RootTree)
  · norm_num [qOneCell107RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell107RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell107RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell107RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell107RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell107RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell107RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell107RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell107RootTree_certified

private def qOneCell108RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((515923 : ℚ) / 1600000) ((2082741 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell108RootTree : Subdivision :=
.horizontal ((4146433 : ℚ) / 12800000)
  (.horizontal ((8273817 : ℚ) / 25600000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((1662383 : ℚ) / 5120000)
  (.leaf .interval)
  (.leaf .interval))

private theorem qOneCell108RootTree_certified :
    certifySubdivision 12 64 32 qOneCell108RootRectangle
      CertificateObjective.endpointExpression qOneCell108RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell108Root_nonneg {a q : ℝ}
    (haLower : ((515923 : ℝ) / 1600000) ≤ a)
    (haUpper : a ≤ ((2082741 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell108RootRectangle) (tree := qOneCell108RootTree)
  · norm_num [qOneCell108RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell108RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell108RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell108RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell108RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell108RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell108RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell108RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell108RootTree_certified

private def qOneCell109RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((2082741 : ℚ) / 6400000) ((210179 : ℚ) / 640000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell109RootTree : Subdivision :=
.horizontal ((4184531 : ℚ) / 12800000)
  (.horizontal ((8350013 : ℚ) / 25600000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((8388111 : ℚ) / 25600000)
  (.leaf .interval)
  (.leaf .interval))

private theorem qOneCell109RootTree_certified :
    certifySubdivision 12 64 32 qOneCell109RootRectangle
      CertificateObjective.endpointExpression qOneCell109RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell109Root_nonneg {a q : ℝ}
    (haLower : ((2082741 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((210179 : ℝ) / 640000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell109RootRectangle) (tree := qOneCell109RootTree)
  · norm_num [qOneCell109RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell109RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell109RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell109RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell109RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell109RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell109RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell109RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell109RootTree_certified

private def qOneCell110RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((210179 : ℚ) / 640000) ((2120839 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell110RootTree : Subdivision :=
.horizontal ((4222629 : ℚ) / 12800000)
  (.horizontal ((8426209 : ℚ) / 25600000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((8464307 : ℚ) / 25600000)
  (.leaf .interval)
  (.leaf .interval))

private theorem qOneCell110RootTree_certified :
    certifySubdivision 12 64 32 qOneCell110RootRectangle
      CertificateObjective.endpointExpression qOneCell110RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell110Root_nonneg {a q : ℝ}
    (haLower : ((210179 : ℝ) / 640000) ≤ a)
    (haUpper : a ≤ ((2120839 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell110RootRectangle) (tree := qOneCell110RootTree)
  · norm_num [qOneCell110RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell110RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell110RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell110RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell110RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell110RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell110RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell110RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell110RootTree_certified

private def qOneCell111RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((2120839 : ℚ) / 6400000) ((133743 : ℚ) / 400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell111RootTree : Subdivision :=
.horizontal ((4260727 : ℚ) / 12800000)
  (.horizontal ((1700481 : ℚ) / 5120000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((8540503 : ℚ) / 25600000)
  (.leaf .interval)
  (.leaf .interval))

private theorem qOneCell111RootTree_certified :
    certifySubdivision 12 64 32 qOneCell111RootRectangle
      CertificateObjective.endpointExpression qOneCell111RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell111Root_nonneg {a q : ℝ}
    (haLower : ((2120839 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((133743 : ℝ) / 400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell111RootRectangle) (tree := qOneCell111RootTree)
  · norm_num [qOneCell111RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell111RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell111RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell111RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell111RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell111RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell111RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell111RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell111RootTree_certified

end Frankl
