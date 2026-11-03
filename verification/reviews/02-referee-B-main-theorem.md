# Referee report B: the main theorem

Reviewed: the written statement and proof now in verification/core/proofs/, and the exact checks now in verification/core/verification/, before the paper was typeset.

Verdict: **ACCEPT**. No mathematical correction is required. The proof
establishes a full negative answer to catalogue TR-23: over C, in format
(3,3,3,2), the asymptotic-rank sublevel at a=cuberoot(62) is reducible.
This verdict does not resolve the separately restricted order-three question
and does not assert novelty or publication readiness.

This is an independent review. I did not contact the author or see the other referee's report while preparing it.

## 1. Material reviewed and independence

Reviewed proof: SHA256
`8e8b58c8558b5cd938d44e0367bac0c93b40aec015e8a1dd17cf1071a1ee3a9f`, the
source hash recorded for verification/core/proofs/PROOF.md in
verification/core/verification/SOURCE_BINDINGS.txt. All reviewed files
remained byte-identical after all runs; the author's files were neither
edited nor used for execution.

Semantic exposure was limited to STATEMENT.md, PROOF.md, CHECKS.md, primary
sources and checker code and data. Of the checker directories, only the named
checkers were read; no prose, reviews or historical receipts from those
directories were opened. The geometry witness was consumed by the checker
and copied/mutated by a local isolated driver, not opened for substantive
review. No author report, notes, separate upper-bound write-up, other review
file or file of the other referee was read. There was no contact with the
author.

The proof was read before my derivation was written; every mathematical
step was then rederived, and the derivation was completed before any
checker was run. Two component audits, parts of this review, also
independently derived their assigned mathematics (the sources and upper
bound, and the geometry) before opening the proof. Their work did not use
the other referee's files.

## 2. Exact catalogue scope and current public status

Freshly fetched README.md:
`80fd90ceb736b5195a1ae003c931b6ef453301e391dcdceb6e7a8c84fbc6c052`.
Freshly fetched problem.tex:
`70378f9eb7540e2969eab453d94ebeb06ce5d5237e94db3118220e32361cbb48`.
Both were fetched into a new empty directory using python3 -I.

Both quantify over all algebraically closed fields, every k>=3, every
positive format, and every real threshold a>=0. They define asymptotic rank
using powers grouping corresponding modes and set the zero tensor's value
to zero. They ask for Zariski irreducibility, specifically exclusion of a
union of two proper Zariski-closed subsets. Therefore C, order4, positive
format(3,3,3,2), positive threshold cuberoot62 are within the exact universal
target; one example refutes it.

The current live catalogue says Open. Independently fetched arXiv
2411.15789v2 (latest revision7 June2026), Theorem1.2 p4, proves Zariski
closedness for any field, k>=3, all positive dimensions and real thresholds.
Its Section5 p17 explicitly leaves irreducibility open for k>=3. The STOC2025
version, Theorem2 p752 and irreducibility discussion p753, agrees. The
sublevel here is consequently a reducible algebraic variety, not just a
nonirreducible subset in an unspecified topology.

The bounded public search located no prior order-four reducible sublevel.
It examined41 arXiv phrase-search records, targeted arXiv/OpenAlex results,
primary-paper citation metadata, and the full searchable text of the recent
many-mode paper arXiv2602.11975. Several general-web endpoints failed or
returned irrelevant results; those are not counted as negative evidence.
This is a bounded status check, not a novelty certification.

The CVZ primary research PDF was independently re-fetched from arXiv and
is byte-identical to the archived source copy, SHA256
`80da2b563058bfc7d478fc0f47a510692192e0381ab546a09f723801342daf5c`.
The original1988/1991 Strassen publisher PDF downloads failed; their full
texts were not audited. This review checks the exact classical theorem
statements and hypotheses in the authenticated CVZ research paper and
rederives every specialized use. It does not claim to reprove the classical
Strassen theorems.

## 3. Proof audit

My full independently expanded derivation was written before the checker
runs. The following are the decisive checks, with no floating-point
inference.

**Spectrum and hypotheses.** In the full semiring of complex THREE-mode
tensors, CVZ arXiv1709.07851v3 Theorem1.1 and Proposition1.6 give
Rtilde(T)=max_phi phi(T). Spectral values dominate asymptotic subrank by
restriction monotonicity applied to powers. CVZ Definition4.1 and Theorem4.4
apply to supports with injective integer labels in each of exactly three
modes, summing to zero on support. Their uniform-support-distribution bound
is enough; no conjectured characterization of the tight-tensor spectrum is
used. Coefficient extraction by interpolation proves monotonicity for the
actual Laurent-map degenerations, because the combined output is polynomial.
This avoids assuming continuity of phi, or additivity of asymptotic rank.

**Finite exchange.** For G=(F2^2)^3, S={1,2,3}^3 and b=(1,1,1), the
intersection I=S intersect(S+b) has8 elements and the exterior E has18.
Translation by b pairs both fixed-point-freely. Character orthogonality
proves the exact 1/64-normalized64-term rank decomposition of the group
tensor. Under the stated maps, the only negative Laurent part is
`t^-2 C8`, exactly canceled by the adjoined paired C8. Cases with two or
three head selections vanish; the mixed S/E/head case is impossible.
The constant coefficient is the direct sum P^boxtimes3 plus C18, on disjoint
coordinates. Thus for every spectral point,
`phi(P)^3+phi(C18)<=64+phi(C8)`.

**Strict constant.** The printed q+2-term small-CW degeneration expands
exactly and gives phi(C8)<=10 over C; the paired-to-diagonal change of basis
is invertible and its factor2 is removed by scaling the head by1/2.
For C18, labels0,+/-1,...,+/-9 are injective and tight. Uniform support
marginals are1/3 at the head and1/27 at each other coordinate, giving
`Qtilde(C18)>=3*cuberoot81`. Therefore
`Rtilde(P)^3 <= 74-3*cuberoot81 < 62 < 64`.
The strict inequalities reduce to81>64,74-12=62,62<64; also27<62, so3<a<4.
The three-mode results are never applied directly to four-mode tensors.

**Ambient open neighbourhood.** At P, each9-by3 slice flattening has
column span the symmetric3-by3 matrices with zero diagonal. The1134-by27
appended-minor matrix L(P) therefore forces every repeated-index coefficient
of S to vanish and all six other coefficients to agree. Its kernel is CP,
so its rank is26. Polynomial nonvanishing of slice-rank3 minors and rank26
minors of L defines an open set U in the ENTIRE54-dimensional tensor space.
The universal identity L(T)T=0 forces ker L(T)=CT on U. Thus Z intersect U
is contained in X, where Z imposes the three balanced-flattening rank<=3
conditions and X is the fourth-mode rank<=1 determinantal set.
An independent derivation additionally specifies a26-by26 minor with
value+/-1 at P; this strengthening is not required to repair the proof.

**Full sublevel and properness.** Every matrix-flattening rank lower-bounds
asymptotic tensor rank, since its rank multiplies exactly under grouped
powers. Hence a<4 forces the ENTIRE sublevel Y into Z. Appending a fixed
nonzero vector preserves tensor rank in every power, by inclusion and
contraction. Therefore x=P tensor d0 belongs to Y intersect U. The second
point y=e000 tensor d0+e111 tensor d1 has asymptotic rank exactly2 and
fourth-mode rank2, so belongs to Y outside X. The two sets
`Y intersect X` and `Y intersect(V minus U)` are relatively Zariski closed,
cover all of Y, and are both proper, witnessed respectively by y and x.
This proves reducibility directly.

**Adversarial conclusions.** No hidden constructibility or semicontinuity
assumption is required. Even without the known global closedness theorem,
the proper relative-closed cover disproves topological irreducibility.
All rank-open conditions are explicit polynomial-minor conditions. U is
ambient, not an open subset only of a selected slice. The bound uses the
full spectrum and the correct three-mode tightness theorem; the final
four-mode passage is proved directly. Both witnesses are within the same
threshold and format. The field C legitimately supports Fourier division,
the quadratic basis change and interpolation. No arbitrary-characteristic
or order-three disproof is inferred.

## 4. Exact checker replay and new corruptions

The derivation was completed before every checker execution. Code
inspection found explicit SystemExit rejection, exact integer/Fraction
arithmetic and no assert-dependent mathematical tests. The three
mathematical checkers, now in verification/core/verification/, pass
normally and under python3 -I -O:

- check_geometry.py: singleton ranks(3,3,3), appended-minor
  rank26 and kernel dimension1, invertible basis identity, outside-point
  fourth-mode rank2 and balanced ranks(2,2,2).
- check_exact_upper.py: exact Fourier normalization, cancellation,
  216 main plus54 auxiliary constant terms, both CW8 formulas, injective
  tight labels, rational marginals and exact entropy separation.
- check_certificate.py: all46^3 output coefficients,88 source
  terms,270 constant terms, CW8 Laurent expansion and tight-support data.

All16 supplied corruption families reject normally and under -O: seven
geometry controls, five exact-upper controls, and four certificate controls.
I added two new mathematical corruptions:

1. Add the repeated-index term e000 to the six-permutation tensor.
   Rejected: `FAIL: L tensor-cubed P != 2 cw2`.
2. Flip the sign of one Fourier-map entry, row_matrix[0][0], in the upper
   certificate. Rejected: `FAIL: constant Laurent coefficient mismatch at (0, 0, 0)`.

Both reject in normal and optimized mode with identical return code, stdout
and stderr. All positive/control pairs likewise agree. The replay driver,
written independently for this review, writes only in a separate directory;
the reviewed files are unchanged. Exact commands, outputs, return codes and
input hashes were recorded.

Checker success certifies the finite identities and linear algebra only.
The spectrum and tight-support theorems remain explicitly identified
classical mathematical inputs, checked against primary research text.

## 5. Final decision

ACCEPT, with no required mathematical corrections. The claimed theorem
and its exact quantifiers follow from the written proof and established
classical inputs. Evidence does not support a rejection or a theorem-changing
restriction. The scope remains the universal catalogue TR-23 disproof via
one complex four-mode example; nothing here certifies novelty.
