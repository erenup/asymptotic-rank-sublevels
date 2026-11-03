# Referee report C: component growth and the grouping boundary

Reviewed: the written proofs now in verification/core/components/proofs/ (DIRECTIONS.md, COMPONENT_DERIVATION.md, MERGING_BOUNDARY.md and CHECKS.md), with the accepted main theorem in verification/core/proofs/ as background, before the paper section on component growth was typeset. No checker was part of the reviewed material.

**Mathematical verdict: ACCEPT the canonical note at its exact stated ranges.
No mathematical correction is required.** The component count, uniform cores
and cost bound, and full grouped boundary are all proved. This is one
independent review; the component audits described here are parts of it and
do not count as a second review.

## Independence and derivations

There was one exception to deriving first, which is stated here. While
locating statement boundaries in the interleaved canonical note, I read
lines 117–144 and 265–282 of DIRECTIONS.md before my own derivation was
complete. Those ranges include partial core and boundary proofs. I
therefore do **not** claim that I independently derived every item before
reading the submitted proofs.

To obtain unexposed derivations, three component audits, parts of this
review, were run from the statements only. Each wrote its own derivation
before opening the candidate proofs or another audit's reasoning. In
particular, the core/boundary audit derived both affected items without
even reading the proof of the main theorem. Its independent proof uses a
nonzero slice commutator and direct pencil interpolation, giving
substantive checks different from the candidate's proofs. The cost audit
read the independently fetched public speedup theorem, whose identity I
supplied from CHECKS.md, before deriving its explicit-family exchange; this
is attributed use of a literature method, not claimed independent discovery.

I separately wrote down the component mechanism and threshold inequalities
before reading the submitted versions, together with a record of what I had
read. The mathematical verdict rests on these written proofs and their
comparisons, not on a claim that my own reading order was fully
derive-first. There was no contact with the author and no author file was
edited. No review, mechanism audit or source audit prepared with the author
was opened. The reviewed CHECKS.md named other reports; their acceptance
claims were not used as evidence.

## Material reviewed and accepted background

Only the four documents DIRECTIONS.md, COMPONENT_DERIVATION.md,
MERGING_BOUNDARY.md and CHECKS.md were read. No computational checker was
supplied with them.

The accepted background is the statement and proof of the main theorem.
The proof read has SHA256
`aa58c53c50db98fff8f9650d6dbaa7b7fe88c3edba38f4909215914b61c777c3`,
identical to verification/core/proofs/PROOF.md. The background copies read
by the component audits have the same proof and statement bytes. Historical
spectral/tight-support and closedness inputs are treated as accepted
background, not newly certified by finite tests.

## Exact mathematical acceptance

All spaces here are over C and tensor powers group corresponding modes. Put

    B_n = ((n+1)^n + n^(2n/3) - ((n+1)^n-n^n)^(2/3))^(1/n).

The following scopes are accepted without weakening:

- For every integer n>=3, k>=4, every integer d_i>=2, and
  t_n=#{i:d_i>=n}, the full asymptotic-rank sublevel at every real
  B_n<=a<n+1 has at least binomial(t_n,3)+1 irreducible components.
  This includes arbitrary padding, disjoint active triples and t_n<3.
- The same bound with t_3 holds for every cuberoot(62)<=a<4 using the
  accepted permutation seed. Thus all d_i>=3 give binomial(k,3)+1,
  in particular at least five components in four such modes.
- For every n>=3 and every s in C*,
  T_(n,s)=sum_i e_i^(tensor 3)+s(sum_i e_i)^(tensor 3) is concise,
  K(T_(n,s))=C T_(n,s), ordinary rank and border rank are exactly n+1,
  and asymptotic rank is at most B_n, where n<B_n<n+1.
- The full sublevel in C^9 tensor C^3 tensor C^2 equals the rank-at-most-three
  9-by-6 determinantal variety for every 3<=a<4 and is irreducible.
- The local balanced-flattening mechanism, its rank-one component of dimension
  n^3+m-1 for n-by-n-by-n cores and fourth dimension m>=2, the local product
  chart, and the expressly conditional/open-problem observations in the
  canonical note hold as stated.

The count is a lower bound, not a list of all components. The cost is an upper
bound, not an exact asymptotic-rank computation. No fixed-format infinitely
valued family, solution of TR-22 finiteness, general three-mode reducibility
or irreducibility theorem, or matrix-multiplication exponent lower bound is
inferred. The n>=3 and s!=0 restrictions on the core geometry are essential.

## Component proof and padding

At a concise first slice, each balanced flattening has rank at most n exactly
when every other slice has its corresponding two-mode image contained in the
first slice's image. The three image conditions say those slices lie in K(T).
The appended-minor matrix makes the concise scalar-kernel locus polynomial
open. This proves the local equality with the fourth-mode rank-one locus in
the entire ambient tensor space, not only on a chosen linear section.

For each active triple I, a padded low-cost seed x_I lies in that open. Any
irreducible component C_I through it has a nonempty dense open in the closed
rank-one I|I-complement locus, and is therefore contained in that locus. On
a nonempty component open, an active single-mode rank is n. A mixed active/
spectator flattening has rank n times the spectator rank; the sublevel bound
forces the latter to one. Closedness extends rank<=1 to the whole component.
A seed for any other triple has rank n in an external mode and cannot lie in
C_I. This is the decisive separation argument, including disjoint triples.

The diagonal tensor with two summands has rank two across every nontrivial
cut, belongs to the sublevel, and lies outside all selected loci. It gives the
extra component. When t_n<3 the assertion is just nonemptiness.

The submitted padding argument is sound: coordinate compression has a section
preserving rank in every power and maps the larger sublevel surjectively onto
the smaller one. Closures of source-component images cover the target with
irreducible closed sets, so there cannot be fewer source components. My own
independent proof and that of the component audit also derive local rigidity
directly in arbitrary padded dimensions using the n-dimensional mode supports.

## Core rank and strict cost

The coefficient proof of K(T)=CT correctly uses a third distinct index and
divides only by s; it omits no nonzero parameter, including s=-1 or s=-1/n.
The border-rank lower bound is valid on the concise open: all concise rank-n
tensors are transforms of the diagonal tensor and have dim K=n. The condition
dim K>=n is closed there and therefore persists to concise border-rank-n
limits. Scalar K excludes those limits. The displayed n+1 terms supply the
matching upper bound. Independently, the slice commutator obstruction has
entry 2s and directly excludes border rank n.

The only new literature input in the submitted cost proof is the automatic
case of Alman–Li arXiv:2605.21738v2, Theorem 6.1, printed page 19. The source
was fetched publicly and has SHA256
`15827dbb7efdf35d5a5326b4019ac02b807ab75e056edd506c2c028c2f40ea1c`.
I checked its statement and the three-direction spectral argument in
Proposition 4.5. Border rank at most R in format N-by-N-by-N and R>2N give
exactly Rtilde<=R+N^(2/3)-(R-N)^(2/3). The automatic auxiliary rank bound N
holds in each orientation. No stronger direction-dependent low-rank choice
is assumed. Setting N=n^n, R=(n+1)^n satisfies R>2N by the binomial theorem.
Exact homogeneity of asymptotic rank under powers yields B_n. The strict
inequalities n<B_n<n+1 follow by elementary real inequalities, without
floating-point estimates.

The independent cost derivation also proves this particular family
application without leaving the new speedup theorem as a black box: use the
real frame A=[I|w]^(tensor m), a rational complement B with AB^t=0, and
Laurent maps whose negative cross terms vanish. An auxiliary one-slice matrix
term cancels the remaining pole, giving a direct-sum exchange with sizes
R,N,R-N. Symmetry gives all three orientations. The accepted tight-support
theorem applied to matrix-multiplication support proves that the three
one-slice spectral exponents sum to at least two, yielding the same bound. I
checked the explicit expansion, disjoint coordinate blocks, injective tight
weights and spectral inequality in that derivation. This is a written
all-parameter proof.

## Full grouped boundary and ancillary scope

Flattening rank below four is at most three and compresses the first factor
to dimension at most three. A dense open of all 3-by-3 matrix pairs consists
of diagonalizable pencils of rank three; closedness of border-rank<=3 gives
the bound for every pair, including singular and defective pencils. Padding
back gives the full upper inclusion. The matrix multiplication map from
9-by-3 and 3-by-6 matrices is surjective onto the rank<=3 locus and proves
irreducibility. No surjectivity of the ungrouped sublevel under grouping is
asserted. The independent audit additionally constructs a regular pencil
perturbation and derives R(Q^m)<=(m+1)3^m by interpolation for arbitrary Q.

The section-6 equivalence between fixed-format finiteness of asymptotic-rank
values and a uniform component bound is a valid conditional statement. Under
strict inclusion of algebraic sets, their component-count vectors ordered by
decreasing dimension strictly increase lexicographically. With ambient
dimension N and at most C components there are finitely many such vectors.
The argument does not supply C. Conditional irreducibility under the full
three-mode asymptotic-rank conjecture follows from the usual irreducible
support-space vector bundle. These observations leave the stated problems open.

## Exact checks and two additional corruptions

Because there are no submitted checkers, the core/boundary audit wrote an
independent integer/Fraction checker. It computes full mode-action
equalizers and slice commutators for (n,s)=(3,1),(3,-1),(3,-1/3),(4,2/5),(5,1),
checks perturbed regular-defective, singular-skew and zero pencils, and checks
Lagrange interpolation in every coordinate of powers 1,2,3. It also checks
rank-three/rank-four threshold witnesses and a determinantal factorization.
These are explicitly finite supporting checks; the universal results are the
written proofs above and in the independent derivations.

The baseline exits zero normally and under -O with identical output. The
checker and its runner use explicit SystemExit guards, not removable asserts.
Two retained input corruptions, without special rejection branches, fail in
both modes with exit one, empty stdout and the exact intended diagnostics:

1. Remove the dense summand from the first core: `FAIL: n3_s1: scalar-kernel
   nullity expected 1, got 3`.
2. Replace perturbation diagonal [1,2,3] by [1,1,1]: `FAIL: defective_regular:
   fewer than four simple-spectrum interpolation samples`.

The source hashes, recipes and all six normal/optimized execution records,
with all stdout and stderr, were retained. No new Lean formalization or fresh
rerun of the accepted certificate of the main theorem is claimed.

This report is supported by a written comparison of my derivation with the
three component audit reports, whose full texts and evidence I read.
