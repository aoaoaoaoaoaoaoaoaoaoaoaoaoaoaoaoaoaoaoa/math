# Verification Records

These files freeze the final outputs produced on 2026-07-21:

- [environment.txt](environment.txt): toolchain and dependency revisions;
- [axioms.txt](axioms.txt): exact accepted transitive-axiom output for the publication-facing
  Lean declarations; the verification suite fails on any byte-level change;
- [falsifier.txt](falsifier.txt): bounded exhaustive search independent of the Lean model;
- [validators.txt](validators.txt): static checks and reproducible document builds.

Rerun [scripts/check.sh](../scripts/check.sh) rather than treating these transcripts as proof.
