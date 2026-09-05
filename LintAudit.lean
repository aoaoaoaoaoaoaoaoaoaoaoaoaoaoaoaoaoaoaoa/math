import Frankl
import MatrixMortality
import Verification.Audit

-- The silent command becomes an error if any default environment linter finds a defect.
verify_environment MatrixMortality Frankl
