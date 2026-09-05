#!/usr/bin/env bash
set -euo pipefail

readonly ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$ROOT"

readonly SCRATCH="$(mktemp -d)"
trap 'rm -rf -- "$SCRATCH"' EXIT

readonly PYTHON_CHECKERS=(
  scripts/generate-parabolic-first-b-late-tail.py
  scripts/generate-parabolic-first-b-one-outer-suffix.py
  scripts/generate-parabolic-first-b-one-outer.py
  scripts/generate-parabolic-first-b-one-inner.py
  tools/audit_chhn_packing_rank.py
  tools/audit_m92_changed_separator_tail.py
  tools/audit_m82_asymmetric_return.py
  tools/audit_m92_run_length_hankel.py
  tools/audit_periodic_dft_floor.py
  tools/audit_rank_two_recompile.py
  tools/audit_mixed_prime_fork.py
  tools/audit_prefix_algebra.py
  tools/audit_six_state_sandwich.py
  tools/certify_cubic_source_decoder.py
  tools/certify_mixed_prime_completion.py
  tools/certify_mixed_prime_context_cuts.py
  tools/certify_mixed_prime_pump_families.py
  tools/certify_mixed_prime_factor_lattice.py
  tools/certify_mixed_prime_pumped_context.py
  tools/certify_mixed_prime_prefix_cloaks.py
  tools/certify_mixed_prime_prefix_pump_suffixes.py
  tools/certify_mixed_prime_prefix_factor_boundaries.py
  tools/certify_mixed_prime_suffix_factor_boundaries.py
  tools/certify_mixed_prime_odd_cloaks.py
  tools/certify_mixed_prime_pump_prefix_kernels.py
  tools/certify_frankl.py
  tools/explore_setter_projective.py
  tools/scour_source.py
)
uvx --from ruff==0.15.22 ruff check "${PYTHON_CHECKERS[@]}"
uvx --from ruff==0.15.22 ruff format --check "${PYTHON_CHECKERS[@]}"
uvx --from ty==0.0.58 ty check "${PYTHON_CHECKERS[@]}"
uv run scripts/generate-parabolic-first-b-one-funnel.py --check
uv run scripts/generate-parabolic-first-b-one-inner.py --check
uv run scripts/generate-parabolic-first-b-late-tail.py --check
uv run scripts/generate-parabolic-first-b-one-outer.py --check
uv run scripts/generate-parabolic-first-b-one-outer-suffix.py --check
uv run scripts/generate-parabolic-first-b-two-tail.py --check
uv run --script tools/audit_prefix_algebra.py
uv run --script tools/audit_chhn_packing_rank.py
uv run --script tools/audit_m92_changed_separator_tail.py
uv run --script tools/audit_m82_asymmetric_return.py
uv run --script tools/audit_m92_run_length_hankel.py
uv run --script tools/audit_periodic_dft_floor.py
uv run --script tools/audit_rank_two_recompile.py
uv run --script tools/audit_mixed_prime_fork.py self-check
uv run --script tools/audit_mixed_prime_fork.py thin 3 100
uv run --script tools/audit_six_state_sandwich.py
uv run --script tools/certify_cubic_source_decoder.py
uv run --script tools/certify_mixed_prime_completion.py
uv run --script tools/certify_mixed_prime_context_cuts.py
uv run --script tools/certify_mixed_prime_pump_families.py
uv run --script tools/certify_mixed_prime_factor_lattice.py
uv run --script tools/certify_mixed_prime_pumped_context.py
uv run --script tools/certify_mixed_prime_prefix_cloaks.py
uv run --script tools/certify_mixed_prime_prefix_pump_suffixes.py
uv run --script tools/certify_mixed_prime_prefix_factor_boundaries.py
uv run --script tools/certify_mixed_prime_suffix_factor_boundaries.py
uv run --script tools/certify_mixed_prime_odd_cloaks.py
uv run --script tools/certify_mixed_prime_pump_prefix_kernels.py
uv run --script tools/certify_frankl.py
uv run --script tools/explore_setter_projective.py --audit --primes 3
uv run --script tools/scour_source.py

rustfmt --edition 2021 --check tools/audit_mixed_prime_kernel.rs
rustc --crate-name mixed_prime_kernel_audit --edition 2021 -D warnings -C opt-level=2 \
  tools/audit_mixed_prime_kernel.rs -o "$SCRATCH/audit_mixed_prime_kernel"
"$SCRATCH/audit_mixed_prime_kernel" self-check

uv run --script tools/certify_mixed_prime_pump_families.py --seed-manifest \
  > "$SCRATCH/mixed-prime-pump-families.tsv"
rustfmt --edition 2021 --check tools/certify_mixed_prime_sandwich.rs
rustc --crate-name mixed_prime_sandwich_certificate --edition 2021 -D warnings -C opt-level=2 \
  tools/certify_mixed_prime_sandwich.rs -o "$SCRATCH/certify_mixed_prime_sandwich"
"$SCRATCH/certify_mixed_prime_sandwich" "$SCRATCH/mixed-prime-pump-families.tsv"
