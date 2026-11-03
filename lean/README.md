# TR-23 finite certificate in Lean

`TR23.finiteCertificate : TR23.FiniteCertificate` proves explicit finite
identities and witness geometry used in the [TR-23 argument](../verification/core/proofs/PROOF.md).
It proves complete minor-row enumeration, the actual appended-minor equations,
the rank-26 matrix and its one-dimensional complex kernel, the witness
flattening ranks and Gaussian basis change. It also proves the finite Fourier
exchange, every required Laurent coefficient identity, tight integer weights
and marginal counts, the ten-term CW identity for every nonzero complex
parameter, the permutation-coordinate bridge, and the integer cutoffs.

**Only this finite certificate layer is formalized.** The theorem does not
formalize asymptotic or border rank, the classical Strassen spectrum or
tight-support theorems, entropy-to-subrank implications, the general
balanced-rank-to-kernel implication, the Zariski-open neighbourhood or
reducibility bridges. The paired-C8 / diagonal-cw8 basis bridge is also
omitted. These statements are not assumptions of the Lean theorem.

The proposition is in [TR23/Statement.lean](TR23/Statement.lean).
The coordinate definitions are in `GeometryDefinitions.lean`,
`ExchangeDefinitions.lean`, and `CWDefinitions.lean`; the exact certificate
data are in [certificate/](certificate/).

## Build and verify

The project uses Lean `v4.34.0-rc2` and Mathlib revision
`85e3a25e006c35636f0e53b0e9296caca2685bc0`. Dependency revisions are pinned
in `lake-manifest.json`. With [elan](https://github.com/leanprover/elan)
and Python 3.11 or later installed, run from this directory:

```sh
lake exe cache get
python3 -B audit/test_verify.py
python3 -B -O audit/test_verify.py
LEAN_NUM_THREADS=1 python3 -B audit/verify.py
```

The first command downloads the official Mathlib cache. The verifier checks
the fixed proposition, definitions, build configuration and certificate data;
cleans this package; and rebuilds every local proof module. It checks the
final theorem against its proposition and requires exactly `propext`,
`Classical.choice`, and `Quot.sound`. Missing inputs, changed fixed hashes,
proof placeholders, extra axiom declarations, failed builds, malformed
dependency output and changed verifier files cause a nonzero exit.
`SHA256SUMS` records the source, configuration and certificate inventory.

After a successful build, print the theorem's dependencies separately with:

```sh
lake env lean audit/Axioms.lean
```
