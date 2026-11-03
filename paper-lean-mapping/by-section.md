# Paper results and their checks

This map follows [the paper source](../paper/main.tex) and its section
[components.tex](../paper/sections/components.tex) in order. Theorems,
propositions and lemmas share one counter within each section. There are
eighteen numbered results: four theorems, nine lemmas and five
propositions. No numbered corollaries, definitions or remarks occur.
Equation numbers below are those of the paper.

| Result | Label | Title | Evidence |
| --- | --- | --- | --- |
| Theorem 1.1 | `thm:main` | Reducibility of the sublevel in format (3,3,3,2) | Paper proof; finite ingredients proved in Lean |
| Theorem 2.1 | `thm:spectrum` | Strassen's spectral characterization | Cited classical theorem; an input, not proved here |
| Lemma 2.2 | `lem:interpolation` | Spectral monotonicity under polynomial degenerations | Paper only |
| Theorem 2.3 | `thm:tight` | Strassen's tight-support theorem | Cited classical theorem; an input, not proved here |
| Lemma 3.1 | `lem:cw-basis` | Paired and small Coppersmith-Winograd tensors | Paper proof; finite ingredients proved in Lean |
| Lemma 3.2 | `lem:exchange` | The finite exchange | Paper proof; finite ingredients proved in Lean |
| Lemma 4.1 | `lem:appended` | Balanced flattenings and the appended-minor matrix | Paper only |
| Lemma 4.2 | `lem:scalar` | Concision and scalar kernel of P | Paper proof; finite ingredients proved in Lean |
| Proposition 4.3 | `prop:open` | The ambient open set forces fourth-mode rank one | Paper only |
| Lemma 5.1 | `lem:flatten` | Flattening ranks bound asymptotic rank | Paper only |
| Lemma 5.2 | `lem:append` | Appending a fixed vector | Paper only |
| Proposition 6.1 | `prop:components-chart` | The local rank-one chart | Paper only |
| Lemma 6.2 | `lem:general-core` | Concision and scalar kernel of the cores | Paper proof; exact checks of stated finite cases |
| Lemma 6.3 | `lem:general-core-rank` | Rank and border rank of the cores | Paper proof; exact checks of stated finite cases |
| Proposition 6.4 | `prop:components-core` | Asymptotic-rank bound for the cores | Paper proof; exact checks of stated finite cases |
| Theorem 6.5 | `thm:components-count` | Lower bound for the number of components | Paper proof; exact checks of stated finite cases |
| Proposition 6.6 | `prop:components-grouping` | The grouped three-mode sublevel | Paper proof; exact checks of stated finite cases |
| Proposition 6.7 | `prop:components-finite-values` | Finite values and bounded component counts | Paper only |

"Finite ingredients proved in Lean" means that some finite identities or
witness ranks used in the written proof are fields of the Lean proposition
`TR23.FiniteCertificate`. No numbered result is a Lean theorem in full.
The Lean coordinate definitions are in
[GeometryDefinitions.lean](../lean/TR23/GeometryDefinitions.lean),
[ExchangeDefinitions.lean](../lean/TR23/ExchangeDefinitions.lean) and
[CWDefinitions.lean](../lean/TR23/CWDefinitions.lean).

## 1. The main theorem and its context

Theorem 1.1 states that the sublevel $Y$ of asymptotic rank at most
$\sqrt[3]{62}$ in $`V=\mathbb C^3\otimes\mathbb C^3\otimes\mathbb C^3\otimes\mathbb C^2`$
is reducible, which refutes the irreducibility assertion quantified over
all orders. Its proof is in Section 5. It uses the witnesses (1.3), the
strict cost bound (1.4) proved in Section 3, and the cover (1.5).

The witness ranks used in that proof are Lean theorems:

| Lean theorem | Certificate field | Exact conclusion |
| --- | --- | --- |
| `TR23.Geometry.witness_y_fourth_rank` | `y_fourth_rank` | The fourth-mode flattening of $y$ has rank 2 |
| `TR23.Geometry.witness_y_outside_rank_one` | `y_outside_rank_one` | $y$ is not in the fourth-mode rank-at-most-one locus $X$ |
| `TR23.Geometry.witness_x_fourth_rank` | `x_fourth_rank` | The fourth-mode flattening of $`x=P\otimes d_0`$ has rank 1 |
| `TR23.Geometry.witness_y_balanced_rank` | `y_balanced_rank` | Each balanced flattening of $y$ has rank 2 |

`verification/core/verification/check_geometry.py:verify` computes the fourth-mode and
balanced ranks of $y$ with exact rational elimination. The inclusion $Y\subseteq Z$, the membership of $x$
in $Y$, the equality $`\widetilde R(y)=2`$, the relatively closed cover,
its properness and reducibility are proved in the paper.

## 2. The asymptotic spectrum and tight supports

Theorem 2.1 (Strassen's spectral characterization) and Theorem 2.3
(Strassen's tight-support theorem) are cited classical theorems, in the
formulations of Christandl, Vrana and Zuiddam. They are inputs of the
asymptotic-rank bound; neither is proved in the paper or formalized.
Both are applied only to three-mode tensors.

Lemma 2.2 proves monotonicity of spectral points under explicit Laurent
degenerations by interpolation. The bounds (2.2) between asymptotic subrank,
spectral points and rank are also written arguments. No Lean declaration
or exact check is assigned to this section.

## 3. A strict asymptotic-rank bound for the permutation tensor

**Lemma 3.1.** For $q=8$, the ten-term degeneration (3.3) and its
expansion (3.4) are a Lean theorem. `TR23.cwCertificate` proves both fields
of `TR23.CWCertificate`:

| Certificate field | Exact conclusion |
| --- | --- |
| `identity` | For every nonzero complex $t$ and all $9^3$ coordinate triples, the ten scaled pure tensors of (3.3) sum to the regular expression (3.4) |
| `constant_term` | The regular expression has value $`\mathrm{cw}_8`$ at $t=0$ |

`verification/core/verification/check_exact_upper.py:main` expands two ten-term
$`\mathrm{cw}_8`$ degenerations, and `verification/core/verification/check_certificate.py:border_check`
expands the ten-term identity stored in the certificate data. The
equivalence of $`C_q`$ and $`\mathrm{cw}_q`$ for every even $q$, the identity
for other $q$, and the resulting spectral bound are proved in the paper.
In particular, the paired-$`C_8`$ to diagonal $`\mathrm{cw}_8`$ basis change is
a written bridge. The formalized Gaussian change of basis for $P$ in
Section 7 does not replace it.

**The group and its Walsh decomposition, (3.5) to (3.8).**

| Lean theorem | Certificate field | Exact conclusion |
| --- | --- | --- |
| `TR23.Exchange.finite_group_card` | `group_card` | $`G=(\mathbb F_2^2)^3`$ has 64 elements |
| `TR23.Exchange.finite_set_cards` | `set_cards` | $S$, $I$ and $E$ have 27, 8 and 18 elements |
| `TR23.Exchange.finite_inner_translation` | `inner_translation` | $I$ is invariant under translation by $b$ |
| `TR23.Exchange.finite_residual_translation` | `residual_translation` | $E$ is invariant under translation by $b$ |
| `TR23.Exchange.finite_shift_fixed_point_free` | `shift_fixed_point_free` | Translation by $b$ has no fixed point |
| `TR23.Exchange.walsh_identity` | `walsh` | The triple character sum over $G$ is 64 when $x+y+z=0$ and 0 otherwise |

The Walsh identity uses the integer normalization 64; division by 64
gives (3.8). The rank bound $`\mathrm R(K_G)\leq64`$ is drawn in the paper.

**Lemma 3.2.** The coefficient identities of the finite exchange are
Lean theorems:

| Lean theorem | Certificate field | Exact conclusion |
| --- | --- | --- |
| `TR23.Exchange.finite_dimensions` | `dimensions` | The source and target coordinate sets have 73 and 46 elements |
| `TR23.Exchange.finite_digit_bijection` | `digit_bijection` | The digit map from $S$ to label triples of $P$ is bijective |
| `TR23.Exchange.contraction_factorization` | `contraction_factorization` | The dense and sparse contractions agree at every output triple |
| `TR23.Exchange.negative_coefficients` | `negative_coefficients` | Every coefficient of negative degree vanishes |
| `TR23.Exchange.constant_coefficient` | `constant_coefficient` | The degree-zero coefficient is 64 times that of $`P^{\boxtimes3}\oplus C_{18}`$ |
| `TR23.Exchange.upper_degree` | `upper_degree` | Every coefficient of degree above three vanishes |
| `TR23.finiteCertificate` | `permutation_bridge` | The coordinates of $P$ in the geometry layer equal the permutation coefficients of the exchange layer |

`verification/core/verification/check_exact_upper.py:main` builds the group, the Walsh
coefficients and the sparse Laurent maps directly.
`verification/core/verification/check_certificate.py:verify` evaluates all 97,336 ordered
output coefficients of the explicit 73-to-46-dimensional maps on the 88
source terms. Both check pole cancellation and the 270 constant target
terms. Reading the identities as Laurent-polynomial restrictions of
$`\Delta_{64}\oplus C_8`$ and deriving (3.11) from Lemma 2.2 are proved in
the paper.

**The tight auxiliary tensor and the constant, (3.12) to (3.14).**

| Lean theorem | Certificate field | Exact conclusion |
| --- | --- | --- |
| `TR23.Exchange.finite_tight_dimension` | `tight_dimension` | Each factor of $`C_{18}`$ has 19 coordinates |
| `TR23.Exchange.finite_tight_injective` | `tight_injective` | The integer weights are injective |
| `TR23.Exchange.finite_tight_support_card` | `tight_support_card` | The support has 54 triples |
| `TR23.Exchange.finite_tight_weight_sum` | `tight_weight_sum` | The weights sum to zero on every support triple |
| `TR23.Exchange.finite_tight_marginals` | `tight_marginals` | Each marginal count is 18 at the zero coordinate and 2 elsewhere |
| `TR23.finiteCertificate` | `tight_gain` | $`4^3\lt81`$ |
| `TR23.finiteCertificate` | `threshold_lower`, `threshold_upper` | $`3^3\lt62\lt4^3`$ |

These are the tight-support hypotheses of Theorem 2.3 for $`C_{18}`$ and the
integer comparisons behind (3.13) and (3.14). The entropy evaluation
$`\exp H=3\sqrt[3]{81}`$, the application of Theorem 2.3, and the
maximum over spectral points giving (1.4) are written calculations.
Both exchange checkers also verify the weights and the marginals, and
integer comparisons for the strict cutoff, including $`62\lt4^3`$.

## 4. Scalar centroids and an ambient open neighborhood

**The appended-minor matrix, (4.4) and (4.5).**

| Lean theorem | Certificate field | Exact conclusion |
| --- | --- | --- |
| `TR23.Geometry.rows_complete` | `row_enumeration` | The 126 four-row choices are strictly increasing, distinct, and include every increasing choice |
| `TR23.Geometry.appended_minor_identity` | `appended_minor_identity` | Each of the 1134 coordinates of $`L(T)S`$ is the corresponding appended determinant |
| `TR23.Geometry.self_kernel` | `self_kernel` | $`L(T)T=0`$ for every complex $T$ |

The minor identity and the self-kernel identity are proved over every
commutative ring; the certificate fields use the complex numbers.
`verification/core/verification/check_geometry.py:verify` rebuilds the same 1134 equations
for $P$ from the determinants.

**Lemma 4.1** is paper only. For concise $T$, the equivalence between
$W\in Z$ and $`L(T)S=0`$ is the general balanced-rank-to-kernel argument;
it is not a Lean statement.

**Lemma 4.2.**

| Lean theorem | Certificate field | Exact conclusion |
| --- | --- | --- |
| `TR23.Geometry.witness_P_flattening_rank` | `P_flattening_rank` | Each single-mode flattening of $P$ has rank 3 |
| `TR23.Geometry.P_minor_rank` | `P_minor_rank` | $`\mathrm{rank}\,L(P)=26`$ |
| `TR23.Geometry.P_kernel` | `P_kernel` | $`L(P)S=0`$ if and only if $S=cP$ for a complex scalar $c$ |

The geometry checker computes the same rank by rational elimination. The
identification of the centroid with $`\ker L(P)`$ is proved in the paper.

**Proposition 4.3** is paper only. Polynomial openness of $U$ in the full
ambient space and the inclusion $`Z\cap U\subseteq X`$ are written
arguments; the membership $x\in U$ uses Lemma 4.2.

## 5. The proper relatively closed cover

Lemma 5.1 (flattening ranks bound asymptotic rank) and Lemma 5.2
(appending a fixed vector) are paper only. The proof of Theorem 1.1 in
this section combines them with the witness ranks listed in Section 1
of this map, with Proposition 4.3 and with (1.4).

## 6. Component growth and a boundary under grouping

This section of the paper has no Lean counterpart. Its exact checks are in
[check_components.py](../verification/core/components/verification/check_components.py)
and cover only stated finite cases.

- **Proposition 6.1** (local rank-one chart) is paper only.
- **Lemma 6.2.** `verification/core/components/verification/check_components.py:check_core`
  checks twelve cores $`T_{n,s}`$ with $n=3,4,5$ and $s=1,-1,2/3,-1/n$:
  concision, the one-dimensional kernel $`K(T_{n,s})`$ spanned by
  $`T_{n,s}`$, and the coefficient relations of the proof. The lemma for
  every $n\geq3$ and every nonzero $s$ is proved in the paper.
- **Lemma 6.3.** `verification/core/components/verification/check_components.py:main` checks that
  the diagonal tensor $`D_n`$ has kernel of dimension $n$ for $n=3,4,5$.
  The equalities of rank and border rank with $n+1$, including the
  density argument, are proved in the paper.
- **Proposition 6.4.** `verification/core/components/verification/check_components.py:check_threshold`
  proves $`n^n\lt B_n^n\lt(n+1)^n`$ and $`(n+1)^n\gt2n^n`$ for
  $n=3,\ldots,12$ and $n=25$ with outward rational intervals. The bound
  $`\widetilde R(T_{n,s})\leq B_n`$ uses the automatic three-direction
  speedup theorem of Alman and Li, a cited input applied to three-mode
  tensors. The statement for every $n\geq3$ is proved in the paper.
- **Theorem 6.5.** `verification/core/components/verification/check_components.py:check_components`
  checks witness flattening ranks in the formats $(3,3,3,3)$,
  $(3,3,3,3,2)$, $(3,2,3,2,3,3)$, $(3,3,3,3,3,3)$ and $(3,3,2,2)$.
  The count it prints is the number of witness triples plus one, not
  an enumeration of components. The component bound, the distinctness
  of the chosen components and the projection argument are proved in the
  paper. Its interval $`\sqrt[3]{62}\leq a\lt4`$ uses Lemma 4.2 and (1.4).
- **Proposition 6.6.** `verification/core/components/verification/check_components.py:check_boundary`
  checks one explicit three-term tensor of format $(9,3,2)$ from a matrix
  pencil with distinct eigenvalues. Density, the border-rank bound for all
  $(3,3,2)$ tensors and irreducibility are proved in the paper.
- **Proposition 6.7** (finite values and bounded component counts) is
  paper only.

## 7. Exact verification and the finite formal layer

This section has no numbered result. It describes the exact checkers and
the scope of the Lean certificate. It also records a supplementary
identity that is proved in Lean but not used in the geometric argument:

| Lean theorem | Certificate field | Exact conclusion |
| --- | --- | --- |
| `TR23.Geometry.witness_basis_determinant` | `basis_determinant` | The Gaussian change-of-basis matrix has determinant $-2i$ |
| `TR23.Geometry.witness_basis_nonsingular` | `basis_nonsingular` | That determinant is nonzero |
| `TR23.Geometry.witness_basis_image` | `basis_image` | The matrix applied in all three modes sends $P$ to $`2\,\mathrm{cw}_2`$ |

The aggregate theorem `TR23.finiteCertificate` proves
`TR23.FiniteCertificate`, whose fields are the geometry certificate
`TR23.Geometry.geometryCertificate`, the exchange certificate
`TR23.Exchange.exchangeCertificate`, the identity `TR23.cwCertificate`,
the permutation bridge and three integer comparisons. Its permitted
axioms are `propext`, `Classical.choice` and `Quot.sound`. It does not
formalize asymptotic or border rank, Strassen's spectral or tight-support
theorems, the entropy-to-subrank implication, the general
balanced-rank-to-kernel equivalence, the open-neighborhood argument or the
relatively closed cover. The paired-$`C_8`$ to diagonal $`\mathrm{cw}_8`$
basis change is also omitted. None of these is a premise of the Lean
theorem.

The [mapping](mapping.json) records the same correspondence in
machine-readable form. Its checker reads the TeX sources, the Lean sources
and the exact checkers, and fails if a label, declaration, certificate
field, file or function named here is missing.
