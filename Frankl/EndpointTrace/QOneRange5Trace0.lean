import Frankl.EndpointCertificate

namespace Frankl

private def qOneCell80RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((19129 : ℚ) / 80000) ((1549369 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell80RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell80RootTree_certified :
    certifySubdivision 12 64 32 qOneCell80RootRectangle
      CertificateObjective.endpointExpression qOneCell80RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell80Root_nonneg {a q : ℝ}
    (haLower : ((19129 : ℝ) / 80000) ≤ a)
    (haUpper : a ≤ ((1549369 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell80RootRectangle) (tree := qOneCell80RootTree)
  · norm_num [qOneCell80RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell80RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell80RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell80RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell80RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell80RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell80RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell80RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell80RootTree_certified

private def qOneCell81RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1549369 : ℚ) / 6400000) ((784209 : ℚ) / 3200000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell81RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell81RootTree_certified :
    certifySubdivision 12 64 32 qOneCell81RootRectangle
      CertificateObjective.endpointExpression qOneCell81RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell81Root_nonneg {a q : ℝ}
    (haLower : ((1549369 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((784209 : ℝ) / 3200000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell81RootRectangle) (tree := qOneCell81RootTree)
  · norm_num [qOneCell81RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell81RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell81RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell81RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell81RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell81RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell81RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell81RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell81RootTree_certified

private def qOneCell82RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((784209 : ℚ) / 3200000) ((1587467 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell82RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell82RootTree_certified :
    certifySubdivision 12 64 32 qOneCell82RootRectangle
      CertificateObjective.endpointExpression qOneCell82RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell82Root_nonneg {a q : ℝ}
    (haLower : ((784209 : ℝ) / 3200000) ≤ a)
    (haUpper : a ≤ ((1587467 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell82RootRectangle) (tree := qOneCell82RootTree)
  · norm_num [qOneCell82RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell82RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell82RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell82RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell82RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell82RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell82RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell82RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell82RootTree_certified

private def qOneCell83RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1587467 : ℚ) / 6400000) ((401629 : ℚ) / 1600000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell83RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell83RootTree_certified :
    certifySubdivision 12 64 32 qOneCell83RootRectangle
      CertificateObjective.endpointExpression qOneCell83RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell83Root_nonneg {a q : ℝ}
    (haLower : ((1587467 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((401629 : ℝ) / 1600000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell83RootRectangle) (tree := qOneCell83RootTree)
  · norm_num [qOneCell83RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell83RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell83RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell83RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell83RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell83RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell83RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell83RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell83RootTree_certified

private def qOneCell84RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((401629 : ℚ) / 1600000) ((325113 : ℚ) / 1280000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell84RootTree : Subdivision :=
.horizontal ((3232081 : ℚ) / 12800000)
  (.leaf .interval)
  (.leaf .interval)

private theorem qOneCell84RootTree_certified :
    certifySubdivision 12 64 32 qOneCell84RootRectangle
      CertificateObjective.endpointExpression qOneCell84RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell84Root_nonneg {a q : ℝ}
    (haLower : ((401629 : ℝ) / 1600000) ≤ a)
    (haUpper : a ≤ ((325113 : ℝ) / 1280000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell84RootRectangle) (tree := qOneCell84RootTree)
  · norm_num [qOneCell84RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell84RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell84RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell84RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell84RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell84RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell84RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell84RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell84RootTree_certified

private def qOneCell85RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((325113 : ℚ) / 1280000) ((822307 : ℚ) / 3200000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell85RootTree : Subdivision :=
.horizontal ((3270179 : ℚ) / 12800000)
  (.leaf .interval)
  (.leaf .interval)

private theorem qOneCell85RootTree_certified :
    certifySubdivision 12 64 32 qOneCell85RootRectangle
      CertificateObjective.endpointExpression qOneCell85RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell85Root_nonneg {a q : ℝ}
    (haLower : ((325113 : ℝ) / 1280000) ≤ a)
    (haUpper : a ≤ ((822307 : ℝ) / 3200000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell85RootRectangle) (tree := qOneCell85RootTree)
  · norm_num [qOneCell85RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell85RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell85RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell85RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell85RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell85RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell85RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell85RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell85RootTree_certified

private def qOneCell86RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((822307 : ℚ) / 3200000) ((1663663 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell86RootTree : Subdivision :=
.horizontal ((3308277 : ℚ) / 12800000)
  (.leaf .interval)
  (.leaf .interval)

private theorem qOneCell86RootTree_certified :
    certifySubdivision 12 64 32 qOneCell86RootRectangle
      CertificateObjective.endpointExpression qOneCell86RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell86Root_nonneg {a q : ℝ}
    (haLower : ((822307 : ℝ) / 3200000) ≤ a)
    (haUpper : a ≤ ((1663663 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell86RootRectangle) (tree := qOneCell86RootTree)
  · norm_num [qOneCell86RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell86RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell86RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell86RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell86RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell86RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell86RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell86RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell86RootTree_certified

private def qOneCell87RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1663663 : ℚ) / 6400000) ((210339 : ℚ) / 800000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell87RootTree : Subdivision :=
.horizontal ((26771 : ℚ) / 102400)
  (.leaf .interval)
  (.leaf .interval)

private theorem qOneCell87RootTree_certified :
    certifySubdivision 12 64 32 qOneCell87RootRectangle
      CertificateObjective.endpointExpression qOneCell87RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell87Root_nonneg {a q : ℝ}
    (haLower : ((1663663 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((210339 : ℝ) / 800000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell87RootRectangle) (tree := qOneCell87RootTree)
  · norm_num [qOneCell87RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell87RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell87RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell87RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell87RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell87RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell87RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell87RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell87RootTree_certified

private def qOneCell88RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((210339 : ℚ) / 800000) ((1701761 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell88RootTree : Subdivision :=
.horizontal ((3384473 : ℚ) / 12800000)
  (.leaf .interval)
  (.leaf .interval)

private theorem qOneCell88RootTree_certified :
    certifySubdivision 12 64 32 qOneCell88RootRectangle
      CertificateObjective.endpointExpression qOneCell88RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell88Root_nonneg {a q : ℝ}
    (haLower : ((210339 : ℝ) / 800000) ≤ a)
    (haUpper : a ≤ ((1701761 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell88RootRectangle) (tree := qOneCell88RootTree)
  · norm_num [qOneCell88RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell88RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell88RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell88RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell88RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell88RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell88RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell88RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell88RootTree_certified

private def qOneCell89RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1701761 : ℚ) / 6400000) ((172081 : ℚ) / 640000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell89RootTree : Subdivision :=
.horizontal ((3422571 : ℚ) / 12800000)
  (.leaf .interval)
  (.leaf .interval)

private theorem qOneCell89RootTree_certified :
    certifySubdivision 12 64 32 qOneCell89RootRectangle
      CertificateObjective.endpointExpression qOneCell89RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell89Root_nonneg {a q : ℝ}
    (haLower : ((1701761 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((172081 : ℝ) / 640000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell89RootRectangle) (tree := qOneCell89RootTree)
  · norm_num [qOneCell89RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell89RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell89RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell89RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell89RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell89RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell89RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell89RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell89RootTree_certified

private def qOneCell90RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((172081 : ℚ) / 640000) ((1739859 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell90RootTree : Subdivision :=
.horizontal ((3460669 : ℚ) / 12800000)
  (.leaf .interval)
  (.leaf .interval)

private theorem qOneCell90RootTree_certified :
    certifySubdivision 12 64 32 qOneCell90RootRectangle
      CertificateObjective.endpointExpression qOneCell90RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell90Root_nonneg {a q : ℝ}
    (haLower : ((172081 : ℝ) / 640000) ≤ a)
    (haUpper : a ≤ ((1739859 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell90RootRectangle) (tree := qOneCell90RootTree)
  · norm_num [qOneCell90RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell90RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell90RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell90RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell90RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell90RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell90RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell90RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell90RootTree_certified

private def qOneCell91RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1739859 : ℚ) / 6400000) ((439727 : ℚ) / 1600000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell91RootTree : Subdivision :=
.horizontal ((3498767 : ℚ) / 12800000)
  (.leaf .interval)
  (.leaf .interval)

private theorem qOneCell91RootTree_certified :
    certifySubdivision 12 64 32 qOneCell91RootRectangle
      CertificateObjective.endpointExpression qOneCell91RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell91Root_nonneg {a q : ℝ}
    (haLower : ((1739859 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((439727 : ℝ) / 1600000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell91RootRectangle) (tree := qOneCell91RootTree)
  · norm_num [qOneCell91RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell91RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell91RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell91RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell91RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell91RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell91RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell91RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell91RootTree_certified

private def qOneCell92RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((439727 : ℚ) / 1600000) ((1777957 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell92RootTree : Subdivision :=
.horizontal ((707373 : ℚ) / 2560000)
  (.leaf .interval)
  (.leaf .interval)

private theorem qOneCell92RootTree_certified :
    certifySubdivision 12 64 32 qOneCell92RootRectangle
      CertificateObjective.endpointExpression qOneCell92RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell92Root_nonneg {a q : ℝ}
    (haLower : ((439727 : ℝ) / 1600000) ≤ a)
    (haUpper : a ≤ ((1777957 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell92RootRectangle) (tree := qOneCell92RootTree)
  · norm_num [qOneCell92RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell92RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell92RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell92RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell92RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell92RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell92RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell92RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell92RootTree_certified

private def qOneCell93RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1777957 : ℚ) / 6400000) ((898503 : ℚ) / 3200000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell93RootTree : Subdivision :=
.horizontal ((3574963 : ℚ) / 12800000)
  (.leaf .interval)
  (.leaf .interval)

private theorem qOneCell93RootTree_certified :
    certifySubdivision 12 64 32 qOneCell93RootRectangle
      CertificateObjective.endpointExpression qOneCell93RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell93Root_nonneg {a q : ℝ}
    (haLower : ((1777957 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((898503 : ℝ) / 3200000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell93RootRectangle) (tree := qOneCell93RootTree)
  · norm_num [qOneCell93RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell93RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell93RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell93RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell93RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell93RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell93RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell93RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell93RootTree_certified

private def qOneCell94RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((898503 : ℚ) / 3200000) ((363211 : ℚ) / 1280000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell94RootTree : Subdivision :=
.horizontal ((3613061 : ℚ) / 12800000)
  (.leaf .interval)
  (.leaf .interval)

private theorem qOneCell94RootTree_certified :
    certifySubdivision 12 64 32 qOneCell94RootRectangle
      CertificateObjective.endpointExpression qOneCell94RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell94Root_nonneg {a q : ℝ}
    (haLower : ((898503 : ℝ) / 3200000) ≤ a)
    (haUpper : a ≤ ((363211 : ℝ) / 1280000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell94RootRectangle) (tree := qOneCell94RootTree)
  · norm_num [qOneCell94RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell94RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell94RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell94RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell94RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell94RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell94RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell94RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell94RootTree_certified

private def qOneCell95RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((363211 : ℚ) / 1280000) ((57347 : ℚ) / 200000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell95RootTree : Subdivision :=
.horizontal ((3651159 : ℚ) / 12800000)
  (.leaf .interval)
  (.leaf .interval)

private theorem qOneCell95RootTree_certified :
    certifySubdivision 12 64 32 qOneCell95RootRectangle
      CertificateObjective.endpointExpression qOneCell95RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell95Root_nonneg {a q : ℝ}
    (haLower : ((363211 : ℝ) / 1280000) ≤ a)
    (haUpper : a ≤ ((57347 : ℝ) / 200000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell95RootRectangle) (tree := qOneCell95RootTree)
  · norm_num [qOneCell95RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell95RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell95RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell95RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell95RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell95RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell95RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell95RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell95RootTree_certified

end Frankl
