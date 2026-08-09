import Frankl.EndpointCertificate

namespace Frankl

private def qOneCell4RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((20649 : ℚ) / 1600000) ((20329 : ℚ) / 1280000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell4RootTree : Subdivision :=
.horizontal ((184241 : ℚ) / 12800000)
  (.leaf .interval)
  (.leaf .interval)

private theorem qOneCell4RootTree_certified :
    certifySubdivision 12 64 32 qOneCell4RootRectangle
      CertificateObjective.endpointExpression qOneCell4RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell4Root_nonneg {a q : ℝ}
    (haLower : ((20649 : ℝ) / 1600000) ≤ a)
    (haUpper : a ≤ ((20329 : ℝ) / 1280000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell4RootRectangle) (tree := qOneCell4RootTree)
  · norm_num [qOneCell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell4RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell4RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell4RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell4RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell4RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell4RootTree_certified

private def qOneCell5RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((20329 : ℚ) / 1280000) ((60347 : ℚ) / 3200000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell5RootTree : Subdivision :=
.horizontal ((222339 : ℚ) / 12800000)
  (.leaf .interval)
  (.leaf .interval)

private theorem qOneCell5RootTree_certified :
    certifySubdivision 12 64 32 qOneCell5RootRectangle
      CertificateObjective.endpointExpression qOneCell5RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell5Root_nonneg {a q : ℝ}
    (haLower : ((20329 : ℝ) / 1280000) ≤ a)
    (haUpper : a ≤ ((60347 : ℝ) / 3200000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell5RootRectangle) (tree := qOneCell5RootTree)
  · norm_num [qOneCell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell5RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell5RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell5RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell5RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell5RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell5RootTree_certified

private def qOneCell6RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((60347 : ℚ) / 3200000) ((139743 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell6RootTree : Subdivision :=
.horizontal ((260437 : ℚ) / 12800000)
  (.leaf .interval)
  (.leaf .interval)

private theorem qOneCell6RootTree_certified :
    certifySubdivision 12 64 32 qOneCell6RootRectangle
      CertificateObjective.endpointExpression qOneCell6RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell6Root_nonneg {a q : ℝ}
    (haLower : ((60347 : ℝ) / 3200000) ≤ a)
    (haUpper : a ≤ ((139743 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell6RootRectangle) (tree := qOneCell6RootTree)
  · norm_num [qOneCell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell6RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell6RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell6RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell6RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell6RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell6RootTree_certified

private def qOneCell7RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((139743 : ℚ) / 6400000) ((19849 : ℚ) / 800000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell7RootTree : Subdivision :=
.horizontal ((59707 : ℚ) / 2560000)
  (.leaf .interval)
  (.leaf .interval)

private theorem qOneCell7RootTree_certified :
    certifySubdivision 12 64 32 qOneCell7RootRectangle
      CertificateObjective.endpointExpression qOneCell7RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell7Root_nonneg {a q : ℝ}
    (haLower : ((139743 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((19849 : ℝ) / 800000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell7RootRectangle) (tree := qOneCell7RootTree)
  · norm_num [qOneCell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell7RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell7RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell7RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell7RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell7RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell7RootTree_certified

private def qOneCell8RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((19849 : ℚ) / 800000) ((177841 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell8RootTree : Subdivision :=
.horizontal ((336633 : ℚ) / 12800000)
  (.leaf .interval)
  (.leaf .interval)

private theorem qOneCell8RootTree_certified :
    certifySubdivision 12 64 32 qOneCell8RootRectangle
      CertificateObjective.endpointExpression qOneCell8RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell8Root_nonneg {a q : ℝ}
    (haLower : ((19849 : ℝ) / 800000) ≤ a)
    (haUpper : a ≤ ((177841 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell8RootRectangle) (tree := qOneCell8RootTree)
  · norm_num [qOneCell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell8RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell8RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell8RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell8RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell8RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell8RootTree_certified

private def qOneCell9RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((177841 : ℚ) / 6400000) ((19689 : ℚ) / 640000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell9RootTree : Subdivision :=
.horizontal ((374731 : ℚ) / 12800000)
  (.leaf .interval)
  (.leaf .interval)

private theorem qOneCell9RootTree_certified :
    certifySubdivision 12 64 32 qOneCell9RootRectangle
      CertificateObjective.endpointExpression qOneCell9RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell9Root_nonneg {a q : ℝ}
    (haLower : ((177841 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((19689 : ℝ) / 640000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell9RootRectangle) (tree := qOneCell9RootTree)
  · norm_num [qOneCell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell9RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell9RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell9RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell9RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell9RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell9RootTree_certified

private def qOneCell10RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((19689 : ℚ) / 640000) ((215939 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell10RootTree : Subdivision :=
.horizontal ((412829 : ℚ) / 12800000)
  (.leaf .interval)
  (.leaf .interval)

private theorem qOneCell10RootTree_certified :
    certifySubdivision 12 64 32 qOneCell10RootRectangle
      CertificateObjective.endpointExpression qOneCell10RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell10Root_nonneg {a q : ℝ}
    (haLower : ((19689 : ℝ) / 640000) ≤ a)
    (haUpper : a ≤ ((215939 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell10RootRectangle) (tree := qOneCell10RootTree)
  · norm_num [qOneCell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell10RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell10RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell10RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell10RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell10RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell10RootTree_certified

private def qOneCell11RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((215939 : ℚ) / 6400000) ((58747 : ℚ) / 1600000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell11RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell11RootTree_certified :
    certifySubdivision 12 64 32 qOneCell11RootRectangle
      CertificateObjective.endpointExpression qOneCell11RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell11Root_nonneg {a q : ℝ}
    (haLower : ((215939 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((58747 : ℝ) / 1600000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell11RootRectangle) (tree := qOneCell11RootTree)
  · norm_num [qOneCell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell11RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell11RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell11RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell11RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell11RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell11RootTree_certified

private def qOneCell12RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((58747 : ℚ) / 1600000) ((254037 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell12RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell12RootTree_certified :
    certifySubdivision 12 64 32 qOneCell12RootRectangle
      CertificateObjective.endpointExpression qOneCell12RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell12Root_nonneg {a q : ℝ}
    (haLower : ((58747 : ℝ) / 1600000) ≤ a)
    (haUpper : a ≤ ((254037 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell12RootRectangle) (tree := qOneCell12RootTree)
  · norm_num [qOneCell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell12RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell12RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell12RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell12RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell12RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell12RootTree_certified

private def qOneCell13RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((254037 : ℚ) / 6400000) ((136543 : ℚ) / 3200000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell13RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell13RootTree_certified :
    certifySubdivision 12 64 32 qOneCell13RootRectangle
      CertificateObjective.endpointExpression qOneCell13RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell13Root_nonneg {a q : ℝ}
    (haLower : ((254037 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((136543 : ℝ) / 3200000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell13RootRectangle) (tree := qOneCell13RootTree)
  · norm_num [qOneCell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell13RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell13RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell13RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell13RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell13RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell13RootTree_certified

private def qOneCell14RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((136543 : ℚ) / 3200000) ((58427 : ℚ) / 1280000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell14RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell14RootTree_certified :
    certifySubdivision 12 64 32 qOneCell14RootRectangle
      CertificateObjective.endpointExpression qOneCell14RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell14Root_nonneg {a q : ℝ}
    (haLower : ((136543 : ℝ) / 3200000) ≤ a)
    (haUpper : a ≤ ((58427 : ℝ) / 1280000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell14RootRectangle) (tree := qOneCell14RootTree)
  · norm_num [qOneCell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell14RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell14RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell14RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell14RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell14RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell14RootTree_certified

private def qOneCell15RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((58427 : ℚ) / 1280000) ((19449 : ℚ) / 400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell15RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell15RootTree_certified :
    certifySubdivision 12 64 32 qOneCell15RootRectangle
      CertificateObjective.endpointExpression qOneCell15RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell15Root_nonneg {a q : ℝ}
    (haLower : ((58427 : ℝ) / 1280000) ≤ a)
    (haUpper : a ≤ ((19449 : ℝ) / 400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell15RootRectangle) (tree := qOneCell15RootTree)
  · norm_num [qOneCell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell15RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell15RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell15RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell15RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell15RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell15RootTree_certified

end Frankl
