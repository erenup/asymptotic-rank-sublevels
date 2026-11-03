# Exact verification

Run from the repository root with Python 3.11 or later:

```sh
python3 -S -s -B verification/run.py
python3 -S -s -B -O verification/run.py
```

[run.py](run.py) authenticates every file in this directory against
[SHA256SUMS](SHA256SUMS), binds the child runner and its manifest by digest,
runs the child in normal, optimized and alternate hash-seed modes, requires
the recorded output in each mode, and rejects altered inventories.

- [core/proofs/](core/proofs/): the plain-text statement and proof of the main theorem.
- [core/verification/](core/verification/): exact checks for the main construction; its
  runner also executes the component suite. See its [guide](core/verification/README.md).
- [core/components/](core/components/): plain-text proofs and exact checks for
  component growth and the grouping boundary.

These finite checks support the written proof; they do not replace any
all-parameter statement. The [review record](reviews/README.md) collects the
independent audits of the paper's mathematics.
