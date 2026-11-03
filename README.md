# Asymptotic Tensor-Rank Sublevels Need Not Be Irreducible

Authors: Wenqi Zhu; Qiyuan Chen; Ping Nie.

Wenqi Zhu — Mathematical Institute, Woodstock Road, University of Oxford, Oxford, UK, OX2 6GG — wenqi.zhu@maths.ox.ac.uk

Qiyuan Chen — Academy of Mathematics and Systems Science, Chinese Academy of Sciences, Beijing, China

Ping Nie — David R. Cheriton School of Computer Science, University of Waterloo — ping.nie@uwaterloo.ca

Read the [paper](paper/main.pdf) and its [LaTeX source](paper/main.tex).
The theorem answers the [catalogue question](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/d49c11a1b2091547235e4779f7e067ed4b65774d/tensor-computations/TR-23/README.md)
negatively for the assertion over all tensor orders; the order-three
question remains open.

## Main theorem

Over $\mathbb C$, in tensor format $(3,3,3,2)$, the set

```math
Y=\left\{T\in\mathbb C^3\otimes\mathbb C^3\otimes\mathbb C^3\otimes\mathbb C^2:
\widetilde R(T)\leq\sqrt[3]{62}\right\}
```

is reducible in the Zariski topology. Here
$`\widetilde R(T)=\lim_{m\to\infty}R(T^{\boxtimes m})^{1/m}`$ uses tensor
powers with corresponding modes grouped, and $`\widetilde R(0)=0`$.

This gives a **negative answer to the all-orders assertion** in the
catalogue, which quantifies over every algebraically closed field, every
order $k\geq3$, all positive mode dimensions, and every real threshold
$a\geq0$. The counterexample has order four. **The order-three question
remains open.**

The proof uses two explicit tensors. For the standard bases
$`e_0,e_1,e_2`$ of $\mathbb C^3$ and $`d_0,d_1`$ of $\mathbb C^2$, set

```math
P=\sum_{(i,j,k)\text{ a permutation of }(0,1,2)}e_i\otimes e_j\otimes e_k,
\qquad x=P\otimes d_0,
\qquad y=e_0\otimes e_0\otimes e_0\otimes d_0+e_1\otimes e_1\otimes e_1\otimes d_1.
```

A finite Fourier exchange, together with Strassen's asymptotic-spectrum
and tight-support theorems for three-mode tensors, gives

```math
\widetilde R(P)^3\leq74-3\sqrt[3]{81}<62,
```

so $x\in Y$; also $`\widetilde R(y)=2`$, so $y\in Y$. Let $X$ be the closed
locus of fourth-mode flattening rank at most one. A polynomial open set
$U$ in the full $54$-dimensional ambient space $V$ contains $x$ and
satisfies $`Y\cap U\subseteq X`$. Its finite core is the
$`1134\times27`$ appended-minor matrix $L(P)$, with kernel
$\mathbb CP$ and rank $26$. Since $y\notin X$,

```math
Y=(Y\cap X)\ \cup\ \bigl(Y\cap(V\setminus U)\bigr)
```

is a cover of the whole sublevel by two proper relatively Zariski-closed
subsets. No restriction to a linear slice is imposed.

## Component growth

For integers $n\geq3$, $k\geq4$ and $`d_i\geq2`$, put
$`t_n=\#\{i:d_i\geq n\}`$ and

```math
B_n=\left((n+1)^n+n^{2n/3}-\big((n+1)^n-n^n\big)^{2/3}\right)^{1/n}.
```

Then $`n<B_n<n+1`$, and for every real $`B_n\leq a<n+1`$ the full complex
asymptotic-rank sublevel in format $`(d_1,\ldots,d_k)`$ has at least
$`\binom{t_n}{3}+1`$ irreducible components. The bound with $`t_3`$ also
holds for $`\sqrt[3]{62}\leq a<4`$; when every $`d_i\geq3`$ this gives at
least $`\binom{k}{3}+1`$ components. These are lower bounds, not a
classification of all components.

The proof uses, for every $n\geq3$ and $`s\in\mathbb C\setminus\{0\}`$,
concise cores
$`T_{n,s}=\sum_{i=1}^n e_i^{\otimes3}+s(\sum_{i=1}^n e_i)^{\otimes3}`$
with scalar kernel $`K(T_{n,s})=\mathbb C T_{n,s}`$, ordinary and border
rank exactly $n+1$, and asymptotic rank at most $`B_n<n+1`$. The last
bound uses the automatic three-direction speedup theorem of Alman and Li,
applied to three-mode tensors. In contrast, the full grouped sublevel in
format $(9,3,2)$ is the rank-at-most-three $9$-by-$6$ determinantal variety
for every $`3\leq a<4`$, and is irreducible. General three-mode
irreducibility and fixed-format finiteness of asymptotic-rank values
(catalogue problem TR-22) remain open.

## Evidence status

- **Formally proved in Lean:** only the finite certificate layer.
  `TR23.finiteCertificate : TR23.FiniteCertificate` proves complete
  minor-row enumeration, the actual appended-minor equations, the rank-26
  matrix $L(P)$ and its one-dimensional complex kernel, the witness
  flattening ranks and a Gaussian basis change. It also proves the finite
  Fourier exchange, every required Laurent coefficient identity, tight
  integer weights and marginal counts, the ten-term $`\mathrm{cw}_8`$
  identity for every nonzero complex parameter, the permutation-coordinate
  bridge, and the integer cutoffs. The permitted axioms are exactly
  `propext`, `Classical.choice` and `Quot.sound`. The theorem does not
  formalize asymptotic or border rank, the classical Strassen spectrum or
  tight-support theorems, entropy-to-subrank implications, the general
  balanced-rank-to-kernel implication, the Zariski-open neighbourhood or
  reducibility bridges, or the paired-$`C_8`$ to diagonal $`\mathrm{cw}_8`$
  basis bridge. These statements are not assumptions of the Lean theorem.
  Neither the main theorem nor the component-growth theorem is a Lean
  theorem. See the [Lean guide](lean/README.md).
- **Exact computation:** standard-library checkers with integer, rational
  and Gaussian-integer arithmetic verify the Laurent coefficient identity
  in sparse and dense form, Walsh cancellation, the ten-term
  $`\mathrm{cw}_8`$ degenerations, tight-support weights and rational
  marginals, the appended-minor kernel, and the finite witness ranks.
  Further checks cover twelve scalar-kernel cores with $n=3,4,5$, the
  endpoint inequalities for $`B_n`$ for $n=3,\ldots,12$ and $n=25$, witness
  ranks in five component formats, and one $(9,3,2)$ pencil. Normal,
  optimized and second-hash-seed runs must agree, and 28 registered
  negative controls must reject in each mode. These finite checks support
  the written argument; they do not prove any all-parameter statement.
- **Proved in the paper only:** the passage from the finite identities to
  the bound on $`\widetilde R(P)`$, the interpolation lemma, the
  equivalence of paired and small Coppersmith–Winograd tensors, the
  balanced-rank-to-kernel equivalence, the ambient open set, the
  flattening and appending lemmas, the relatively closed cover and
  reducibility, and every result of the component-growth section. The
  cited inputs are Strassen's spectral and tight-support theorems in the
  formulation of Christandl, Vrana and Zuiddam, Zariski closedness of
  asymptotic-rank sublevels (Christandl, Hoeberechts, Nieuwboer, Vrana and
  Zuiddam), and the speedup theorem of Alman and Li. The
  [section map](paper-lean-mapping/by-section.md) gives the evidence for
  each numbered result.
- **Review:** the [review record](verification/reviews/README.md) contains
  the independent informal AI-agent audits of the main theorem, the
  component-growth results, the Lean statement and the paper; none requested
  a mathematical correction. Wenqi Zhu checked the complete argument, and
  Qiyuan Chen, a co-author, discussed the proof and agreed with it.
- **Open:** irreducibility of asymptotic-rank sublevels in order three,
  finiteness of the set of asymptotic-rank values in a fixed format, a
  complete list of components, and a three-mode replacement for the
  balanced-flattening argument. Exact values of $`\widetilde R(P)`$ and
  $`\widetilde R(T_{n,s})`$ are not determined here.

## Where to read

Start with the [guide from the question to the checks](paper-lean-mapping/README.md),
then the [paper](paper/main.pdf).
The [section-by-section map](paper-lean-mapping/by-section.md) lists every
numbered result with its Lean declarations, exact checks or written-only
status.

Plain-text versions are the [statement](verification/core/proofs/STATEMENT.md) and
[complete proof](verification/core/proofs/PROOF.md) of the main theorem, and the
[component-growth proof](verification/core/components/proofs/DIRECTIONS.md),
[permutation-seed argument](verification/core/components/proofs/COMPONENT_DERIVATION.md),
[grouping boundary](verification/core/components/proofs/MERGING_BOUNDARY.md) and
[computational scope](verification/core/components/proofs/CHECKS.md).
The formal proposition is in [Statement.lean](lean/TR23/Statement.lean)
and its proof in [TR23.lean](lean/TR23.lean). The
[Lean guide](lean/README.md), the exact-check guides for the
[main construction](verification/README.md) and the
[components](verification/core/components/verification/README.md), and the
[verification record](VERIFICATION.md) give reproduction details.

## Reproduce the checks

Use Python 3.11 or later, from the repository root:

```sh
python3 -S -s -B verification/run.py
python3 -S -s -B -O verification/run.py
python3 -S -s -B paper-lean-mapping/build_and_check.py
python3 -S -s -B -O paper-lean-mapping/build_and_check.py
python3 -I -B tools/check_markdown_math.py
sha256sum --check SHA256SUMS
(cd paper && sha256sum --check SHA256SUMS)
```

The entry point also executes the component suite. With the pinned Lean
toolchain installed through elan, run from `lean/`:

```sh
lake exe cache get
python3 -B audit/test_verify.py
python3 -B -O audit/test_verify.py
LEAN_NUM_THREADS=1 python3 -B audit/verify.py
```

The [paper guide](paper/README.md) gives the LaTeX build command.

## Layout

- `paper/`: manuscript source, section file, bibliography and PDF.
- `lean/`: the pinned Lean project for the finite certificate, with audit scripts and certificate data.
- `paper-lean-mapping/`: reading guide, result map, machine-readable mapping and its checker.
- `verification/`: one entry point for the exact checks; `core/proofs/` holds the plain-text statement and proof, `core/verification/` the exact checks for the main construction, and `core/components/` the plain-text proofs and exact checks for component growth and the grouping boundary.
- `tools/`: a static guard for GitHub Markdown math.

## License and citation

Files outside `paper/` are available under the [MIT license](LICENSE).
The files in `paper/`, including the manuscript source and PDF, are licensed
under [CC BY-SA 4.0](paper/LICENSE).
Citation information is in [CITATION.cff](CITATION.cff).

## Acknowledgements

We thank [NetMind.AI](https://www.netmind.ai/) and [AI4ALPHA](https://www.ai4alpha.ca/) for their
support of this project. The research of Wenqi Zhu was also supported by the Engineering and Physical Sciences Research
Council under grant EP/Y028872/1, *Mathematical Foundations of Intelligence: An "Erlangen Programme" for AI*.
