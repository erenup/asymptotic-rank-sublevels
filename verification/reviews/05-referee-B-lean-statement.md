# Referee report B: fidelity of the Lean statement

Reviewed: the Lean proposition `TR23.FiniteCertificate` in lean/TR23/Statement.lean and its definition files lean/TR23/GeometryDefinitions.lean, lean/TR23/ExchangeDefinitions.lean and lean/TR23/CWDefinitions.lean. Only the statement was reviewed; the Lean proof of the finite certificate (lean/TR23.lean and the other files in lean/TR23/) was not part of this review.

Verdict: **ACCEPT**. Required changes: none for the declared finite algebraic identity and witness layer.

This is a statement-fidelity review, not acceptance of a completed Lean proof. The four source files define proof obligations; they do not assert an inhabitant of `TR23.FiniteCertificate`.

## Source binding and independent review

The four reviewed files are byte-identical to the repository files:

| File | SHA256 |
|---|---|
| lean/TR23/Statement.lean | `9a93cc03e2ae3c8535c1e8c122daf2540f5be09c31344f3813a6cadd977620d7` |
| lean/TR23/GeometryDefinitions.lean | `28e6be327fa61ac6a9039d9f285c32fc62094efdac02c23a366214672ea8d4fe` |
| lean/TR23/ExchangeDefinitions.lean | `0e9257d12c0da073204b67e220b89c9948c12ef1925ef4631e5a1e72b501492d` |
| lean/TR23/CWDefinitions.lean | `a346b234052fb28e2719add56ef81875bd020bae7c0700b000776e38303b0208` |

The written proof accepted in reports 01 and 02 is the source of verification/core/proofs/PROOF.md (SHA256 `8e8b58c8558b5cd938d44e0367bac0c93b40aec015e8a1dd17cf1071a1ee3a9f`, recorded in verification/core/verification/SOURCE_BINDINGS.txt). That mathematical verdict is not reopened here.

My own derivation was written independently before comparing against the proof and the reports of the component audits of this review. The geometry and CW audits derived the identities before consulting the proof; the exchange audit reconstructed the mathematics from the proof before comparing the Lean definitions. Their final reports were then read and checked against the definitions and my derivation; this report relies on their exact supplementary computations as identified below.

## Geometry and fields

Geometry coordinates are the full complex tensor spaces, with encoding
9i+3j+k. The three 9-by-3 flattenings have the intended singleton modes.
The matrix L(T) is the actual 1134-by-27 cofactor coefficient matrix of all
appended 4-by-4 minors, not an unrelated matrix with the desired rank.
All 126 increasing four-row choices are present. Enumeration completeness,
the appended-determinant identity for every complex T,S, and L(T)T=0 for
every T are certificate obligations without restrictive hypotheses.

The P fields require all three flattenings to have rank exactly 3, L(P) to
have rank exactly 26, and its kernel to equal C P for every candidate S.
They express the scalar-centroid finite fact over C. The explicit x=P tensor
d0 has fourth rank 1; y consists of two specified coordinate pure terms and
has fourth rank 2 and all three balanced ranks 2. Thus the concrete data for
the rank-two witness are represented faithfully, without introducing an
abstract asymptotic-rank premise. The complex basis matrix has determinant
-2i and sends P to 2cw2 with the correct orientation and factor.

The finite inputs used to construct the open neighbourhood are present:
polynomial cofactor definitions, universal identities, and ranks/kernel at P.
The statement does not formalize the generic balanced-rank-to-kernel
implication, its rank-nullity consequence, a Zariski-open set U, the inclusion
Z intersect U contained in X, or reducibility. Those bridges must not be
credited as proved if this finite certificate is later inhabited. This is
consistent with the declared finite input/witness scope and the accompanying
scope note's explicit exclusion of Zariski reducibility.

## Fourier exchange and degeneration coefficients

The group is (ZMod 2 squared) cubed, of size 64. The main, intersection and
residual sets have sizes 27, 8 and 18; source and target dimensions are 73
and 46. The digit map is required to be bijective and the shift is required
to be fixed-point-free. The character is the six-bit Walsh character, with
the exact factor 64 in its orthogonality identity.

The source is D64 direct-sum 64 times paired C8. Full contraction is defined
before the sparse factorization obligation, avoiding an assumption that
simply replaces the intended tensor transformation. The Laurent degrees are
0 on the main block, -2 at the head, and 1 on the residual block. Every
negative coefficient must vanish; the degree-zero coefficient must equal
64 times (P cubed direct-sum paired C18); every coefficient above degree 3
must vanish. All output coordinates and integer degrees in those ranges are
universally quantified. The common scaling and auxiliary cancellation signs
match the written proof.

The tight data concern the actual E-indexed support: 19 coordinates,
54 support triples, injective integer weights summing to zero on each triple,
and marginal counts 18 for the head and 2 for each other coordinate. These
are exact finite counting facts, not an assumed entropy-to-subrank theorem.

## CW identity and explicit omissions

For every nonzero complex t and all 729 output coordinates, the ten indexed
pure terms expand to

    cw8 + t*(sum e_a cubed - Sym(h,S,S)) - t^3*S cubed,

where S is the sum of the eight non-head basis vectors. The first eight
terms, auxiliary ninth term, and cancellation tenth term have the correct
indices, signs and powers. The constant-term field concerns the regular
polynomial at zero, so no inverse expression is evaluated there.

The exchange tensor uses paired C8 while this identity uses diagonal cw8.
The required complex change-of-basis bridge is absent. The scope note
explicitly says that it is omitted and that this is not every finite bridge
of the complete written proof; the source supports that description.

The aggregate also includes the actual coordinate-P bridge and strict integer
cutoffs 27<62<64<81. It neither assumes nor claims Strassen's spectrum theorem,
the tight-support asymptotic theorem, border/asymptotic tensor rank, entropy
bounds, the full reducibility theorem, or a solution of the order-three
restriction. There is no vacuous field restriction or hidden conclusion
assumption in the reviewed propositions.

## Verification

All four unchanged source files and a separate reviewer sanity file compile
under Lean 4.34.0-rc2 with Mathlib revision
`85e3a25e006c35636f0e53b0e9296caca2685bc0`. Sanity checks cover selected
encode/decode facts, dimension/cutoff facts, and field projections retaining
their universal quantifiers. Deliberately asserting the wrong coordinate
encoding is rejected. This is a definition/type/projection check only.
The initial reviewer cardinality proof using `decide` reached Lean's recursion
limit; replacing it by simplification of product cardinalities fixed the
reviewer helper. No reviewed source was changed.

Supplementary exact checks pass normally and under Python -O: complete
geometry row enumeration, explicit witness minors and Gaussian-integer
basis coordinates; exchange group/set/table/coefficient identities; and
all 729 CW Laurent expansions. The audits' corruption controls reject
wrong geometry tables, exchange scaling/degrees/weights/permutation entries,
and five independent CW errors. These executable checks supplement written
derivations and are not presented as Lean proofs of the certificate.

ACCEPT is limited to fidelity of this explicitly scoped finite statement.
There was no author contact and no author file was edited.
