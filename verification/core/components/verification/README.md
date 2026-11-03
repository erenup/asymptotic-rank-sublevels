# Exact supporting checks

From this directory, run:

```sh
python3 -S -s -B run.py
```

The runner uses Python's standard library. It validates the complete verification
inventory and binds all four documents in `../proofs/`. The paths in `SHA256SUMS`
are relative to `components/`; the manifest binds the runner, checker, data,
control registry, output hash, documentation, and proof files, excluding only
the manifest itself. Unexpected files, symbolic links, duplicate entries,
unsafe manifest paths, and malformed JSON are rejected. The bound files are
checked again after execution. All failures use explicit exceptions rather
than Python assertions.

`check_components.py` uses exact rational Gaussian elimination, integer
arithmetic, and outward rational intervals for radicals. It checks:

- The twelve tensors `T_(n,s)` for `n = 3, 4, 5` and
  `s = 1, -1, 2/3, -1/n`: mode ranks, the intersection of all three lifted
  slice images, its scalar kernel, and the resulting coefficient equations.
  The diagonal reference tensor has compatibility-kernel dimension `n`.
- The threshold formula for `n = 3, ..., 12, 25`. Integer-root certificates
  give outward intervals proving `n^n < B_n^n < (n+1)^n` for these eleven
  values and verify the premise `(n+1)^n > 2 n^n`.
- Embedded permutation-tensor rank witnesses in the five formats
  `(3,3,3,3)`, `(3,3,3,3,2)`, `(3,2,3,2,3,3)`, `(3,3,3,3,3,3)`, and
  `(3,3,2,2)`: active triples, overlapping-triple cuts, and the two-term
  diagonal witness across every nontrivial cut. Two disjoint permutation
  cores have a mixed-pair flattening of rank nine.
- One explicit three-term `(9,3,2)` tensor from a matrix pencil with distinct
  eigenvalues, whose mode ranks are `(3,3,2)`.

The same pinned complete output is required in normal mode, under `-O`, and
with a second hash seed. Twelve negative controls must reject with their exact
registered diagnostics in all three modes, for 36 rejections. These include
removing two compatibility images, damaging a coefficient, replacing the
strict threshold premise by equality, reversing the radical difference, and
using a boundary flattening of rank four, as well as malformed input controls.

These are finite supporting checks. They do not establish the statements for
all parameters, component counts, Zariski closedness, density, irreducibility,
the asymptotic speedup theorem, or general border rank. Those claims and their
mathematical dependencies are addressed in the written proofs. The displayed
component-count formula in the finite output records the number of witness
triples plus one; it is not an enumeration of irreducible components. No
finite computation here resolves TR-22 or general three-mode irreducibility.
