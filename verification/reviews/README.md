# Review record

These reports record the independent informal AI-agent audits of the
paper's mathematics. Each auditor worked separately from the other auditors
and from the authors, wrote out its own derivation before running or
comparing with the authors' checks or text, checked every step, and ran its
own exact tests. Each report states exactly what was read before its
derivation was written. No report claims formal certification or external
peer review.

| Report | Scope | Verdict |
|---|---|---|
| [01](01-referee-A-main-theorem.md) | Main theorem: catalogue scope, Fourier exchange and the strict asymptotic-rank bound for the permutation tensor, ambient open set and relatively closed cover, cited sources, and the exact checks | Accept; no corrections |
| [02](02-referee-B-main-theorem.md) | Same scope, independent referee | Accept; no corrections |
| [03](03-referee-C-component-growth.md) | Component growth: the component count, scalar-kernel cores with their rank and cost bounds, the (9,3,2) grouping boundary, and the conditional observations | Accept; no corrections |
| [04](04-referee-B-component-growth.md) | Same scope, independent referee | Accept; no corrections |
| [05](05-referee-B-lean-statement.md) | Fidelity of the Lean proposition `TR23.FiniteCertificate` to the finite identities and witnesses of the written proof (statement only) | Accept; no changes required |
| [06](06-referee-B-paper.md) | Fidelity of the paper draft with the component-growth section to the accepted proofs, its citations and its build | Accept; no corrections |

Reports 02, 04, 05 and 06 are by the same referee (B); referees A and C are
different auditors.

No report requested a correction, so there is none to incorporate. The
scope limits that the reports record are stated in the repository: the
order-three question is left open ([README.md](../../README.md), lines 12–14
and 32–33), and the Lean theorem does not formalize the asymptotic-rank,
Zariski-open, reducibility or paired-to-diagonal basis-change bridges
([README.md](../../README.md), lines 104–109;
[lean/README.md](../../lean/README.md), lines 12–17).

The reviewed files relate to the repository as follows.

- Reports 01 and 02 reviewed the statement and proof now in
  [core/proofs/](../core/proofs/). These differ from the reviewed files only
  by the removal of provenance and process sentences;
  [SOURCE_BINDINGS.txt](../core/verification/SOURCE_BINDINGS.txt) records
  the reviewed and the current hashes. The three checkers in
  [core/verification/](../core/verification/) differ from the reviewed
  programs only in their command-line interface, input validation and
  message wording; `certificate.json`, `geometry_witness.json` and the
  contents of the seven geometry negative-control fixtures are
  byte-identical.
- Reports 03 and 04 reviewed the four documents now in
  [core/components/proofs/](../core/components/proofs/). MERGING_BOUNDARY.md
  is byte-identical; DIRECTIONS.md differs only in the target of one
  cross-reference link (line 351), so the line numbers cited in report 03
  are unchanged; COMPONENT_DERIVATION.md and CHECKS.md differ only by the
  removal of process sentences. The exact checks in
  [core/components/verification/](../core/components/verification/) were not
  part of the material of reports 03 and 04; report 06 ran them, with runner,
  checker and data byte-identical to the repository files.
- The four Lean files of report 05 are byte-identical to those in
  [lean/TR23/](../../lean/TR23/).
- For report 06, `paper/sections/components.tex` and `paper/refs.bib` are
  byte-identical to the reviewed files. `paper/main.tex` differs from the
  reviewed draft only in the title, the author block, the page layout, one
  sentence added to the abstract that states the component-growth theorem,
  four removed comment lines and the closing declarations; the PDF was
  rebuilt.

In addition, Wenqi Zhu (University of Oxford) checked the complete argument,
and Qiyuan Chen (Academy of Mathematics and Systems Science, Chinese Academy
of Sciences), a co-author, discussed the proof and agreed with it.
