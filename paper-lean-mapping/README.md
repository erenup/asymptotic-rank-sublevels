# From the irreducibility question to the checks

The catalogue question asks whether, for every algebraically closed field,
every order $k\geq3$, all positive factor dimensions and every real
threshold $a\geq0$, the set of tensors of asymptotic rank at most $a$ is
an irreducible variety. These sublevels are known to be Zariski closed.
One reducible sublevel is enough to refute the assertion over all orders.

The paper gives one in order four. Over $\mathbb C$, in
$`V=\mathbb C^3\otimes\mathbb C^3\otimes\mathbb C^3\otimes\mathbb C^2`$,

```math
Y=\{T\in V:\widetilde R(T)\leq\sqrt[3]{62}\}
```

is reducible. The order-three question is not settled.

| Symbol | Meaning |
| --- | --- |
| $`\widetilde R(T)`$ | Asymptotic rank: the limit of $`R(T^{\boxtimes m})^{1/m}`$, with corresponding modes grouped |
| $P$ | The three-mode tensor with coefficient one on the six permutations of $(0,1,2)$ |
| $x$, $y$ | $`P\otimes d_0`$ and $`e_0^{\otimes3}\otimes d_0+e_1^{\otimes3}\otimes d_1`$ |
| $X$ | Tensors whose fourth-mode flattening has rank at most one |
| $Z$ | Tensors whose three balanced flattenings have rank at most three |
| $L(T)$ | The $`1134\times27`$ matrix of appended minors of a first slice $T$ |
| $U$ | Tensors whose first slice is concise with $`\mathrm{rank}\,L(T)\geq26`$ |

## The argument in four steps

1. **A strict cost bound for $P$ (paper Sections 2 and 3).** A finite
   Fourier exchange degenerates $`\Delta_{64}\oplus C_8`$ to
   $`P^{\boxtimes3}\oplus C_{18}`$. Strassen's spectral characterization,
   his tight-support theorem for $`C_{18}`$, and the bound
   $`\phi(C_8)\leq10`$ give
   $`\widetilde R(P)^3\leq74-3\sqrt[3]{81}\lt62`$. The two classical
   theorems are cited and applied only to three-mode tensors.
2. **A scalar kernel (Section 4).** $L(P)$ has rank $26$ and kernel
   $\mathbb CP$. On the open set $U$ this persists, so
   $`Z\cap U\subseteq X`$.
3. **A proper closed cover (Section 5).** Flattening ranks bound asymptotic
   rank, so $Y\subseteq Z$. The point $x$ lies in $`Y\cap U`$ and $y$ lies in
   $Y$ outside $X$. Hence $Y$ is covered by the proper relatively closed
   subsets $`Y\cap X`$ and $`Y\cap(V\setminus U)`$.
4. **Component growth (Section 6).** Scalar-kernel cores $`T_{n,s}`$ in
   every dimension $n\geq3$ give at least $`\binom{t_n}{3}+1`$ components
   in every order $k\geq4$, with all $`d_i\geq2`$, for thresholds $`B_n\leq a\lt n+1`$. The grouped
   three-mode sublevel in format $(9,3,2)$ is irreducible for
   $`3\leq a\lt4`$.

Read [by-section.md](by-section.md) alongside the [paper](../paper/main.pdf).
It lists every numbered result in order with its evidence.
[mapping.json](mapping.json) records the paper labels, Lean declarations,
certificate fields, exact-check functions and coverage limits.

## What each kind of evidence establishes

The aggregate theorem of the [Lean project](../lean/README.md) is
`TR23.finiteCertificate : TR23.FiniteCertificate`. Its fields are the
explicit finite identities and witness geometry of steps 1 to 3: the
complete minor-row enumeration, the appended-minor equations, the rank and
kernel of $L(P)$, the witness flattening ranks, the finite group and
Walsh identities, every Laurent coefficient of the exchange, the tight
weights and marginal counts of $`C_{18}`$, the ten-term $`\mathrm{cw}_8`$
identity, the permutation-coordinate bridge and the integer comparisons
$`3^3\lt62\lt4^3\lt81`$. A supplementary Gaussian change of basis from $P$
to $`2\,\mathrm{cw}_2`$ is also included. The permitted axioms are
`propext`, `Classical.choice` and `Quot.sound`.

The Lean theorem does not formalize asymptotic or border rank, the
classical spectral and tight-support theorems, the entropy-to-subrank
step, the general balanced-rank-to-kernel equivalence, the open
neighborhood, the closed cover or reducibility. The paired-$`C_8`$ to
diagonal $`\mathrm{cw}_8`$ basis change is a written bridge. None of these
statements is an assumption of the Lean theorem, and no numbered result
of the paper is a Lean theorem in full. Step 4 has no Lean counterpart.

The [exact checks for steps 1 to 3](../verification/README.md) recompute
the same finite identities and ranks with integer, rational and
Gaussian-integer arithmetic, by two independent routes for the exchange.
The [component checks](../verification/core/components/verification/README.md) treat stated
finite cases of step 4. Every checker has registered negative controls
that must be rejected. These computations support the written argument;
they do not establish an all-parameter statement.

Everything else is proved in the paper, using as cited inputs Strassen's
two theorems, Zariski closedness of asymptotic-rank sublevels, and, in
step 4, the speedup theorem of Alman and Li.

## Check the correspondence

From the repository root, run:

```sh
python3 -S -s -B paper-lean-mapping/build_and_check.py
python3 -S -s -B -O paper-lean-mapping/build_and_check.py
```

The standard-library script indexes the numbered results of the TeX
sources in order, with the shared counter in each section. It indexes the
Lean declarations after masking comments and strings, the fields of the
four certificate structures, and the field assignments of the four
certificate theorems. Each of the 36 leaf certificate fields must be mapped
to exactly the theorem that fills it. Mapped exact-check functions must
exist in the named checkers. The result table in
[by-section.md](by-section.md) must equal the table generated from the
mapping, and every mapped declaration and check must be named there.

A missing paper label, numbered result, Lean file, declaration,
certificate field, exact-check file or function makes the script fail.
Twenty-four in-memory negative controls exercise these rejections without
changing any file. Both commands print the same output. The script does
not compile Lean, build the PDF or run the mathematical checks; their
commands are in the [Lean guide](../lean/README.md), the
[exact-check guide](../verification/README.md) and the
[verification record](../VERIFICATION.md).
