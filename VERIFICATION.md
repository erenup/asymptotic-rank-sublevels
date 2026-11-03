# Verification

Python checks use only the standard library. The mathematical programs use
exact integer, rational and Gaussian-integer arithmetic, with no
floating-point tolerance. The Lean theorem `TR23.finiteCertificate` proves
the finite certificate layer only; the asymptotic-rank and Zariski
arguments are written proofs in the [paper](paper/main.pdf). The outputs
below were observed with Python 3.12 from the repository root.

## Exact checks

```sh
python3 -S -s -B verification/run.py
python3 -S -s -B -O verification/run.py
```

Both commands exit zero with empty standard error and identical standard
output:

```text
PASS: check_certificate.py (normal, optimized, hash-seed)
PASS: check_exact_upper.py (normal, optimized, hash-seed)
PASS: check_geometry.py (normal, optimized, hash-seed)
PASS: 48 negative-control runs; 2 proof bindings
PASS: check_components.py (normal, optimized, hash-seed)
PASS: 36 negative-control runs; 4 proof bindings
RESULT: PASS TR-23 components finite verification
RESULT: PASS TR-23 verification
PASS: core/verification/run.py (normal, optimized, hash-seed)
PASS: 41 files authenticated; 6 integrity controls rejected
RESULT: PASS TR-23 exact verification
```

`5e341f6fcbb62576cb7b56019561831894fbfb6eb4c82b07102c4f2db0df974c`.

The entry point authenticates every file in `verification/` against its
manifest, binds the child runner `verification/core/verification/run.py` and
its manifest by digest, and runs the child in normal, optimized and
alternate hash-seed modes, requiring the same recorded output each time;
six altered inventories must be rejected. The child runner executes each
of the three checkers in three modes: ordinary Python with hash seed 1,
optimized Python with seed 1, and ordinary Python with seed 8675309. All
positive outputs must be byte-identical and match their registered hashes.
Each of the 16 registered negative controls must be rejected with its exact
registered diagnostic in each mode, giving 48 rejections. The child binds
the two files in `verification/core/proofs/` and every verification file by
hash, before and after execution. It then authenticates the component
manifest and requires the exact output of the component suite. See the
[exact-check guide](verification/README.md).

## Exact checks for component growth

```sh
python3 -S -s -B verification/core/components/verification/run.py
python3 -S -s -B -O verification/core/components/verification/run.py
```

Both commands exit zero with empty standard error and identical standard
output:

```text
PASS: check_components.py (normal, optimized, hash-seed)
PASS: 36 negative-control runs; 4 proof bindings
RESULT: PASS TR-23 components finite verification
```

The standard-output SHA256 is
`3db8176157c7fbb991a60715106a943122c2dbec007c761fa5d750ec906ef47b`.
The output is the same from inside `verification/core/components/verification/`. Twelve
negative controls are rejected in each of the three modes, and the four
documents in `verification/core/components/proofs/` are bound by hash. The checked finite
cases are listed in the [component-check guide](verification/core/components/verification/README.md).

## Lean finite certificate

The project pins Lean `v4.34.0-rc2` and Mathlib revision
`85e3a25e006c35636f0e53b0e9296caca2685bc0`; all nine dependency revisions
are pinned in [lake-manifest.json](lean/lake-manifest.json). From `lean/`:

```sh
lake exe cache get
python3 -B audit/test_verify.py
python3 -B -O audit/test_verify.py
LEAN_NUM_THREADS=1 python3 -B audit/verify.py
```

The result is recorded from a separate build log of these commands. Both
control-suite runs report `Ran 16 tests` and `OK`. The verifier checked the
literal certificate data, cleaned the package and rebuilt every local proof
module, each with `Build completed successfully`. It then ran
`lake env lean audit/Axioms.lean`, which prints the axioms of the final
theorem. The final output lines (command trace omitted) are:

```text
'TR23.finiteCertificate' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS: geometry literals, 126 minor rows, exchange map and tight weights
PASS: rebuilt 31 proof modules; all project Lean sources checked.
PASS: TR23.finiteCertificate uses exactly propext, Classical.choice, Quot.sound.
```

The 31 modules are `lean/TR23.lean` and the 30 files in `lean/TR23/`.
The verifier permits only the three displayed axioms and rejects proof
placeholders, extra axiom declarations, failed builds, changed fixed
hashes and changed verifier files. The formal proposition contains only
finite identities and witness geometry; see the [Lean guide](lean/README.md)
for its exact scope and the [section map](paper-lean-mapping/by-section.md)
for the paper results it supports.

## Paper-to-Lean correspondence map

```sh
python3 -S -s -B paper-lean-mapping/build_and_check.py
python3 -S -s -B -O paper-lean-mapping/build_and_check.py
```

Both commands exit zero with empty standard error and identical standard
output:

```text
PASS: 18 numbered results in 7 paper sections, in TeX order
PASS: 36 Lean certificate fields mapped to their declarations in 3 component certificates and TR23.finiteCertificate
PASS: 9 exact-check links and 11 supporting paper anchors
PASS: by-section.md result table and declaration references match the mapping
PASS: 24 mapping negative controls rejected
RESULT: PASS mapping structure; mathematical coverage is stated per entry
```

The standard-output SHA256 is
`d842e6cdc09188bc719316ba0053a9f6ddd8a80b5b6956f52ae01a5e3570a5ac`.
This checks references and the stated coverage of each entry. It does not
infer mathematical equivalence from prose and does not replace the Lean
build or the exact checks. See the [reading guide](paper-lean-mapping/README.md).

## Markdown math

```sh
python3 -I -B tools/check_markdown_math.py
python3 -I -B -O tools/check_markdown_math.py
```

The static guard checks the tracked Markdown files against the GitHub math
profile and runs its own positive and negative controls. Both commands give
the same result and end with:

```text
PASS: 21 tracked Markdown files; controls passed
```

`verification/core/components/proofs/DIRECTIONS.md` is not inspected: its bytes are bound by
`verification/core/components/verification/SHA256SUMS`, which the exact-check runner
authenticates, so it keeps its original backslash-delimited math and GitHub
shows those formulas as source text.

## Manuscript

The LaTeX build command is in the [paper guide](paper/README.md).

## File integrity

The root manifest lists every tracked file except itself. Run:

```sh
sha256sum --check SHA256SUMS
(cd paper && sha256sum --check SHA256SUMS)
```

Nested manifests in `verification/`, `verification/core/verification/`,
`verification/core/components/verification/` and `lean/` bind the exact suites, the proof documents and the Lean sources.
Dependency caches and regenerated build products are excluded. File hashes
establish byte identity; the commands above supply the verification
evidence.
