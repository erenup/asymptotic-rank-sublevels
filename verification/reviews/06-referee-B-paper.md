# Referee report B: fidelity of the paper

Reviewed: the 19-page draft of the paper with the component-growth section (now paper/main.tex and paper/sections/components.tex), against the accepted proofs in verification/core/proofs/ and verification/core/components/proofs/, together with the component checks in verification/core/components/verification/.

**Verdict: ACCEPT. Required corrections: none.**

This verdict covers the 19-page draft containing the main theorem and the new component-growth section. The reviewed files that are byte-identical to the repository files are:

| File | SHA256 |
| --- | --- |
| paper/sections/components.tex | `4b7c7b6404a2bf99dee54a9c9e01b752bae16c18e9a7db033712f3189d7f4b95` |
| paper/refs.bib | `b4781495cdf54991681ae69e81a7d73d33f11b871e426fcc8f76732611937e7f` |

## Independence and source binding

I reconstructed the mathematical arguments from the accepted proofs and wrote down my derivation before opening the candidate manuscript. Three separate audits, parts of this review, also recorded their expected arguments or scope before manuscript access. Their later reports supplement my own complete reading of the new section. Author internal audits were not used as evidence; there was no author contact or author-file edit.

The accepted reference consists of the reviewed statement and proof of the main theorem, the original paper and the reviewed component documents. All 17 component, original-paper and original-proof files used as sources for the draft equal those accepted files. DIRECTIONS.md and MERGING_BOUNDARY.md are byte-identical to the documents reviewed in reports 03 and 04; the other two component documents differ only by the removal of internal review/process wording.

## Preservation and mathematical fidelity

Removing only the line that inputs `sections/components.tex`, and its adjacent blank line, reproduces the earlier version of `main.tex`, which contains the main theorem only, byte for byte. No original theorem, proof, abstract, title, history paragraph or finite-formalization statement changes. The bibliography retains the entire original prefix and appends only the version-specific Alman–Li v2 and Björklund–Kaski entries. Reference renumbering follows the fresh build.

The new section contains exactly the accepted mathematical conclusions, with complete proofs suitable for a specialist reader:

- The appended-minor matrix defines the scalar-kernel open locus. The three balanced flattening bounds yield the exact local rank-one chart and its dimension. The text distinguishes a component of the determinantal locus from the actual asymptotic-rank sublevel; its inverse chart uses regular coordinate ratios, with agreement on overlaps. Grouping a complementary block for flattenings is explicitly separated from changing the rank convention.
- For every integer `n >= 3` and every nonzero complex `s`, the scalar cores are concise, have one-dimensional compatibility kernel, and have both ordinary rank and border rank exactly `n+1`. The coefficientwise symmetry argument covers every nonzero parameter, including exceptional-looking negative values. Relative closedness on the concise locus supplies the border-rank lower bound.
- The positive-real-root formula for `B_n` is unchanged, and `n < B_n < n+1` is proved. The paper applies the automatic Alman–Li theorem only to the three-mode `n`th grouped power, explicitly verifies `R > 2N`, and obtains the same asymptotic bound. It uses the sufficient ordinary-rank bound furnished by the displayed decomposition, without needing the more general border-rank phrasing of the accepted source. Every claimed conclusion is preserved.
- For all `k >= 4`, all `d_i >= 2`, and `B_n <= a < n+1`, the lower bound is exactly `binomial(t_n,3)+1`, with `t_n = #{i:d_i >= n}`. The separate permutation interval is `cuberoot(62) <= a < 4`, with `t_3`. The proof handles disjoint triples through spectator single-mode ranks, includes the additional rank-two diagonal component, and treats the case of no active triple. Local projections with sections give a surjective map of full sublevels and transfer the count in the correct direction under padding.
- For every `3 <= a < 4`, the full `(9,3,2)` sublevel equals the rank-at-most-three `9 x 6` determinantal variety. The dense simple-spectrum matrix-pencil argument, border closure, padding and matrix-factorization irreducibility proof are all present. No surjectivity from the original four-mode sublevel is asserted.
- The conditional full three-mode conjecture implication, its distinction from concise-tight-cubic conjectures and from `omega > 2`, and the fixed-format equivalence between finite attained values and uniform component bounds match the accepted source. The finite-vector lexicographic proof is valid. General three-mode irreducibility and TR-22 fixed-format finiteness remain open; no uniform bound, complete component classification or infinitely-valued fixed-format family is claimed.

The added results are explicitly outside the original finite Lean certificate. The section presents written all-parameter proofs with identified classical inputs, not conclusions from finite sampling.

## Credit and validation

Six bibliography entries covering five distinct works/catalogue sources were checked against freshly retrieved public primary material, plus the pinned TR-22 entry. These checks cover CHNVZ closedness and open questions; the CVZ spectral/tight-support formulations; Alman–Li v1/published numbering and v2's exact automatic speedup statement; Björklund–Kaski's precise conjecture restrictions; and the TR-23 catalogue quantifiers. The retained credit for the prior strict permutation-tensor speedup is accurate, and no priority claim was introduced.

A build from copied TeX inputs produces 19 pages with no final-log warnings, undefined references, duplicate labels or overfull/underfull box diagnostics. All fonts are embedded. Extracted PDF text equals the supplied draft exactly. I visually inspected the new-section pages and the continuation through the verification/bibliography pages; the mathematics and links render cleanly. The regenerated PDF has a different binary hash, while its text matches; the verdict is bound to the supplied draft.

The component runner, byte-identical to verification/core/components/verification/run.py with checker byte-identical to check_components.py there, passes with `python3 -I -B` and `python3 -I -O -B`, with identical complete stdout and empty stderr. Each invocation executes three positive interpreter modes, rejects 36 negative controls and verifies four proof bindings. These are finite supporting checks; the universal conclusions were checked through the written proofs. The original mathematics of the main theorem and the formal files are unchanged and were not re-reviewed as new results.
