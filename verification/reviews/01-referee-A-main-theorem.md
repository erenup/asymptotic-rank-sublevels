# Referee report A: the main theorem

Reviewed: the written statement and proof now in verification/core/proofs/, and the exact checks now in verification/core/verification/, before the paper was typeset.

**Verdict: ACCEPT. No corrections required.**

This is an independent review. I did not contact the author or see the other referee's report while preparing it.

The submitted proof establishes that, over C, the full asymptotic-rank
sublevel in format (3,3,3,2) at threshold a = cuberoot(62) is reducible in
the relative Zariski topology. This disproves the catalogue's universal
assertion for all orders k >= 3. It does not resolve the separately
restricted order-three question. This is a mathematical acceptance, with
no priority or exhaustive novelty claim.

## Material reviewed and independence

Reviewed proof: SHA256
`8e8b58c8558b5cd938d44e0367bac0c93b40aec015e8a1dd17cf1071a1ee3a9f`, the
source hash recorded for verification/core/proofs/PROOF.md in
verification/core/verification/SOURCE_BINDINGS.txt.

I wrote my complete derivation before any submitted checker execution. Two
delegated checks, parts of this review, were derived independently before
checker exposure: the geometry, and the spectrum and Fourier exchange. I
read and checked the delegated results only after completing my own
derivation. I rely on the delegated exact execution results and the
explicitly identified original scan audit below; agreement alone is not
evidence for the theorem.

Before the derivations, exposure was restricted to the statement, the
proof, the list of checks and public sources. After the derivations, only
the three Python programs explicitly named in the list of checks were read:
the geometry checker check_geometry.py, the geometry control runner and the
upper-bound checker check_exact_upper.py. The geometry fixture was copied
and parsed as input. No submitted report, geometry or upper-bound
exposition, notes or review file was read. Writing drivers ran only in
separate replay directories. The reviewed files remained unchanged.

## Catalogue scope and public status

I independently fetched both live TR-23 README.md and problem.tex from
https://github.com/ajt60gaibb/OpenProblemsInNLA into a new empty directory
using isolated Python. The captured catalogue commit is
`d49c11a1b2091547235e4779f7e067ed4b65774d`. Both files quantify every
algebraically closed field, every order k >= 3, every positive format and
every real nonnegative threshold. Powers group corresponding factors. The
question concerns the actual asymptotic-rank sublevel with its Zariski
irreducibility, not an ordinary-rank locus, a selected slice or a Euclidean
closure. The complex field, order four, specified format and threshold meet
every hypothesis. A single proper relatively closed cover therefore refutes
the assertion as written.

The live catalogue still labels TR-23 Open. I independently checked
arXiv:2411.15789v2 (7 June 2026), Theorem 1.2 and Section 5, p.17. The former
proves sublevel closedness for all fields, orders k >= 3, formats and real
thresholds; the latter explicitly says irreducibility is open for k >= 3.
That PDF's SHA256 is
`2157342b2403b3d6810f3ae7c32fbcec9383a9f0ae88839eddae4ed4a0b158e2`.

A bounded independent literature check inspected the recent papers
arXiv:2605.21738v2, 2602.11975v1 and 2601.08119v1, and the author-hosted
final-2025 Wigderson--Zuiddam survey. It found no explicit TR-23 resolution
or result for this format and threshold. In particular, Alman--Li,
arXiv:2605.21738v2 (23 September 2026), Theorem 1.3, p.4, gives the stronger
known three-mode bound Rtilde(cw2) < 3.931. That bound must be included in
any assessment of prior work; I do not claim the rank improvement here is
new. It does not itself state the sublevel reducibility result under
review. The submitted Fourier argument is self-contained apart from the
identified classical theorems and does not depend on that newer numerical
constant.

The survey publisher returned HTTP 403, so only the explicitly distinguished
author-hosted 2025 copy was inspected. Some general search engines returned
interstitials or irrelevant results, and one OpenAlex search returned 429;
these failures were not counted as negative evidence. Successful arXiv and
citation metadata searches, source URLs, hashes and access limits were
recorded. This finite search does not establish novelty or exclude implicit
consequences in other work.

## Independent reconstruction of the upper bound

Let P be the sum of the six permutations of e0 tensor e1 tensor e2. In
G = (F2^2)^3, set S = {1,2,3}^3, b = (1,1,1),
I = S intersect (S+b), and E = G minus (S union (S+b)). Exact counting gives
|G| = 64, |S| = 27, |I| = 8 and |E| = 18. Translation by b pairs I and E
without fixed points. Walsh orthogonality decomposes the group tensor
K_G as 64 rank-one summands with coefficient 1/64, so K_G restricts from D64.

Apply, in every mode,

    f_g -> 1_S(g) x_g + t^-2 1_{g=b} z0 + t 1_E(g) z_g.

Crucially b belongs to S, so f_b has both its x_b and z0 branches. The
all-x terms give P to its third grouped power. With exactly one z0, the
two remaining group indices differ by b: two I indices give precisely
t^-2 C8, two E indices give C18 at degree zero, and an S/E pair is
impossible. Two z0 choices require group index zero, whose image vanishes;
three require b = 0. Terms with no z0 and an E choice have positive degree.
Thus this classification accounts for every Laurent term, including all
overlaps. Mapping the zero vector in an added disjoint C8 to -t^-2 z0
cancels all negative terms. The polynomial output has degree at most three
and constant term P^(grouped cube) direct-sum C18 on disjoint coordinates.
Consequently

    P^(grouped cube) direct-sum C18 <=deg D64 direct-sum C8.

The paired Cq is equivalent over C to the usual small cwq by invertible
maps on each pair e_j +/- i e_k and z0 -> e0/2. Expanding the displayed
q+2-term Laurent family in the submitted proof cancels every negative
coefficient and leaves cwq as constant term. It follows that phi(C8) <= 10
for every point of the full complex three-tensor spectrum.

I re-derived the needed degeneration monotonicity: interpolate the
constant coefficient of F(t) to its m-th grouped power at dm+1 nonzero
complex values. The constant tensor is a restriction of the direct sum
of those evaluations. Hence phi(T)^m <= (dm+1) phi(K)^m; taking m-th roots
proves phi(T) <= phi(K). No semicontinuity assumption is hidden here.

For C18 use injective integer weights 0, +/-1, ..., +/-9 on its nine pairs.
Every support triple has weight sum zero. The uniform distribution on the
54 support triples gives marginal mass 1/3 at zero and 1/27 at each of the
18 other labels. The three-factor tight-support theorem gives

    phi(C18) >= Qtilde(C18) >= exp((7/3) log 3) = 3 cuberoot(81).

Spectral additivity, multiplicativity and normalization now give, for every
point of the full complex three-tensor spectrum,

    phi(P)^3 <= 74 - 3 cuberoot(81).

The spectral maximum theorem implies the same bound for Rtilde(P)^3.
Exact integers establish strictness: 81 > 4^3, so 3 cuberoot(81) > 12,
and therefore 74 - 3 cuberoot(81) < 62 < 64. Also 27 < 62, so 3 < a < 4.
No approximate arithmetic is needed.

The relevant primary-source hypotheses were checked:

- Christandl--Vrana--Zuiddam, *Universal points in the asymptotic spectrum
  of tensors*, https://arxiv.org/abs/1709.07851v3, Theorem 1.1 and
  Proposition 1.6, pp.6--8; Definition 4.1, Theorem 4.4 and Corollary 4.5,
  pp.31--32. I directly read these passages. The spectrum is that of all
  complex three-tensors; the tight-support result is used only for C18,
  which has three factors. There is no extrapolation to four factors or
  conjectural completeness assumption for selected spectral functionals.
- The delegated source audit independently obtained and visually inspected
  the original Strassen scans: J. Reine Angew. Math. 384 (1988),
  Theorem 3.8, journal p.124, for the spectral characterization; and
  J. Reine Angew. Math. 413 (1991), Lemma 5.1, p.152 and Proposition 5.4,
  p.158, for the support lower bound and its passage to tensor subrank.
  The algebraically closed field hypothesis is satisfied by C.

Nonzero support coefficients do not require positivity or genericity:
a free support diagonal yields a tensor diagonal by rescaling its
individual entries in one mode. The chosen distribution need not maximize
entropy. The proof does not assume asymptotic rank itself is additive.

## Independent geometry and adversarial checks

Write W = T tensor d0 + S tensor d1. Let Z be the common locus where all
three balanced flattenings have rank at most three, and let X be the
fourth-mode rank-at-most-one locus. These are ambient Zariski closed sets,
defined by minors. X is exactly the tensors T tensor v, including zero.

For each of the three 9-by-3 flattenings of T, append each corresponding
column of S and take all four-row determinants. This gives a 1134-by-27
matrix L(T) with cubic polynomial coefficients and L(T)T = 0 identically.
If all T flattenings have rank three, the equations L(T)S = 0 are equivalent
to the three balanced rank bounds. At P, column-space membership forces
symmetry under every index transposition and vanishing of coefficients
with repeated indices. The six surviving coefficients must be equal.
Conversely P satisfies all equations. Thus ker L(P) = C P and rank L(P) = 26
by a written coefficient argument, independently of elimination software.

Let U require rank three for all T flattenings and rank L(T) >= 26. These
are polynomial open conditions in the entire 54-dimensional ambient V.
On U the nonzero kernel vector T forces rank exactly 26, so L(T)S = 0
implies S = lambda T. Therefore Z intersect U is contained in X.

Every matrix-flattening rank lower-bounds asymptotic tensor rank: grouped
powers produce matrix Kronecker powers of exactly multiplicative rank.
Since a < 4, the entire sublevel Y lies in Z. This step concerns every
point of Y and uses neither genericity nor a selected slice.

Appending a nonzero fourth vector preserves rank in every power by
inclusion and contraction. Thus x = P tensor d0 is in Y intersect U.
The second point

    y = e0 tensor e0 tensor e0 tensor d0
        + e1 tensor e1 tensor e1 tensor d1

has asymptotic rank exactly two, by its two-term decomposition and
fourth-mode flattening rank. Hence y belongs to Y but not to X.

The explicit cover is

    Y = (Y intersect X) union (Y intersect (V minus U)).

Both pieces are relatively Zariski closed. The point y proves the first
is proper, and x proves the second is proper. The cover requires no
closedness, constructibility or lower semicontinuity of Y. The separately
verified closedness theorem allows the word "variety" but is unnecessary
for this failure of irreducibility. No Euclidean closure is substituted.

I specifically challenged the overlapping b branch, possible negative
Laurent exponents, disjointness of the target summands, the full-spectrum
quantifier, field assumptions, order of the entropy theorem, openness in
the full ambient space and properness of both pieces. None revealed a gap.

## Exact replay and additional corruptions

The two checkers were inspected for exact arithmetic, independent target
construction and explicit SystemExit failures. No mathematical condition
depends on Python assert. The geometry checker uses integer,
Gaussian-integer and Fraction arithmetic; the upper checker uses integer
and Fraction arithmetic. Both use only the standard library.

There were **32 checker executions**, each case run normally and under -O:

| Suite | Positive | Supplied negative | Added negative | Total |
| --- | ---: | ---: | ---: | ---: |
| Geometry | 2 | 14 | 4 | 20 |
| Fourier / CW / tight support | 2 | 10 | 0 | 12 |
| Total | 4 | 24 | 4 | 32 |

All positives exited zero with PASS. All corruptions explicitly exited
one at the expected mathematical/schema gate. Every normal/-O pair had
identical exit status, stdout and stderr.

The two new corruptions, selected independently of the supplied controls,
were: (1) delete the complete first-mode index-2 slice of P, which fails
concision; and (2) replace the six permanent coefficients by permutation
parity signs. The alternating tensor passes the earlier rank/kernel gates
but rejects the claimed common-basis identity with cw2, as predicted by
alternation being preserved by a common basis change. They test distinct
mathematical premises and both reject in both modes.

The positive geometry execution confirms singleton ranks 3,3,3,
rank L(P) = 26, one-dimensional kernel, the exact Gaussian basis identity,
and outside ranks two. The upper execution checks all constant and
negative Laurent coefficients, Walsh normalization, both CW expansions,
injective weights and every marginal mass. Finite checks supplement the
written proof; they do not replace its asymptotic or topological arguments.

The accepted result is precisely the stated complex four-mode
counterexample. No correction, qualification of its mathematical claim,
or additional computation is required for acceptance.
