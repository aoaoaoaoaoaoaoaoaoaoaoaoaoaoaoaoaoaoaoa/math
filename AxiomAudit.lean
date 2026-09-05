import Frankl
import MatrixMortality
import Verification.Audit

-- The reviewed snapshot owns the declaration inventory and its exact transitive dependencies.
verify_axioms "verification/axioms.txt" complete
