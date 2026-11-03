# Exact supporting checks

Run `python3 -S -s -B run.py` from this directory with Python 3.11 or later. Only the standard library is needed; arithmetic
uses integers, rational numbers, and pairs of integers representing Gaussian
integers.

The [written proof](../proofs/PROOF.md) establishes reducibility of the full
asymptotic-rank sublevel over C in format (3,3,3,2), at the exact threshold
`a = cuberoot(62)`. These checks verify finite identities and hypotheses used
there. They do not formalize or replace Strassen's asymptotic-spectrum theorem,
the tight-support asymptotic-subrank theorem, or the geometric argument.
They make no claim about the separately restricted order-three question.

## Checked ingredients

- `check_geometry.py` reads `geometry_witness.json`. It builds all 1,134
  appended-column minor equations and computes their rational rank 26. It
  checks the one-dimensional kernel, three flattening ranks, the exact
  invertible change of basis sending the permutation tensor to twice small
  `cw_2`, and the rank-two point outside the fourth-mode rank-one locus.
- `check_exact_upper.py` constructs the 64-element group and the sparse
  Laurent maps directly. It verifies Walsh orthogonality, cancellation of
  every negative-degree coefficient, the 270 constant support terms, two
  ten-term `cw_8` degenerations, tight integer weights, exact marginal
  probabilities, and the integer inequalities giving the strict cutoff.
  It reads neither checker data file and imports neither other checker.
- `check_certificate.py` reads `certificate.json` and evaluates all 97,336
  ordered output coefficients against an explicit 73-to-46-dimensional map
  and its 88 source terms. It checks the required pole cancellation and
  270 constant target terms, expands the ten-term `cw_8` Laurent identity,
  and checks the 54-term tight support and its marginals. The expected
  tensors are reconstructed from their definitions. No generator is needed
  to verify the included certificate.

The geometry calculation is independent of the asymptotic-rank upper bound.
The two upper-bound checkers use distinct sparse and dense computations.
The proof supplies the implication from these finite constructions and the
two classical theorems to the asymptotic-rank bound and reducibility.

## Negative controls

Each checker accepts `--negative-control NAME`. The seven geometry controls
replace the tensor by one with a larger centroid, alter a coefficient, make
the basis map singular, collapse the outside point into one fourth-mode
direction, or invalidate the input schema. Their seven JSON fixtures are
included under `negative_controls/`.

The five sparse controls change the cancellation sign, remove a group term,
change Fourier normalization, collide tight labels, or change the marginal
denominator. The four dense controls remove the pole-cancelling map entry,
alter a target coefficient, change a border-decomposition scalar, or collide
tight labels. The dense checker also runs its four corruption checks during
each positive execution.

[NEGATIVE_CONTROLS.json](NEGATIVE_CONTROLS.json) registers the exact expected
stderr for all 16 controls. Each external control must exit with status 1,
empty stdout, and precisely its registered error.

## Integrity and execution

[CHECKERS.txt](CHECKERS.txt) contains the expected stdout SHA256 for each
positive checker. The runner executes every checker and control in three
modes: normal with hash seed 1, `-O` with seed 1, and normal with seed 8675309.
All positive outputs must be byte-identical and match their registered hashes.
This gives nine positive executions and 48 external negative-control executions.
Site initialization and bytecode writes are disabled; execution is sequential
and does not modify the package.

[SHA256SUMS](SHA256SUMS) covers every verification file except itself. The
runner enforces the exact file and directory inventory, complete manifest
and checker coverage, standard-library imports, absence of assertions and
inexact literals, and JSON with unique keys and integer numbers. Symbolic
links, nonregular files, bytecode, unregistered files, and additional
directories are rejected.

[SOURCE_BINDINGS.txt](SOURCE_BINDINGS.txt) records original and curated proof
hashes. The runner checks the two files in `proofs/` against their curated
hashes and requires exactly those two proof files. It checks all verification
and proof hashes again after execution. Any discrepancy exits nonzero,
including under `-O`.
