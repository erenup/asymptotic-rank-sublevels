# Components of asymptotic-rank sublevels and the boundary under grouping

All vector spaces are finite-dimensional over the complex numbers. Tensor
rank is ordinary tensor rank, and tensor powers group corresponding modes.
Write

\[
 Z_a(V_1,\ldots,V_k)=\{T:\widetilde R(T)\le a\},\qquad R(0)=0.
\]

These sublevels are Zariski closed [1]. Every bipartition flattening rank
is a lower bound on asymptotic rank: the flattening of a grouped power is
a Kronecker power, its matrix rank multiplies, and it bounds tensor rank.
We use the standard inequality \(\widetilde R\le\underline R\), where
\(\underline R\) denotes border rank. It follows by applying a polynomial
border degeneration to tensor powers and interpolating: the interpolation
factor is polynomial in the power, and disappears after taking roots.

## 1. Main component bound

For every integer \(n\ge3\), set

\[
 B_n=\left((n+1)^n+n^{2n/3}
       -\big((n+1)^n-n^n\big)^{2/3}\right)^{1/n}.
\]

Then \(n<B_n<n+1\). The roots here and below are positive real roots.

**Theorem.** Let \(k\ge4\), let \(d_i\ge2\), and put
\(t_n=\#\{i:d_i\ge n\}\). For every real \(a\) with
\(B_n\le a<n+1\), the variety
\(Z_a(\mathbb C^{d_1},\ldots,\mathbb C^{d_k})\) has at least
\(\binom{t_n}{3}+1\) irreducible components. In particular, when all
\(d_i\ge n\), the lower bound is \(\binom{k}{3}+1\).

The same bound with \(t_3\) holds throughout
\(\sqrt[3]{62}\le a<4\), using the permutation tensor and its explicit
asymptotic estimate [3]. Thus in four modes of dimensions at least three
there are at least five components at those thresholds.

The proof gives a lower bound, not a complete list of components. The
format varies in the assertion of unbounded component counts; no fixed
format is asserted to have infinitely many asymptotic-rank values.

## 2. A linear-algebra mechanism

Let \(A,B,C\) each have dimension \(n\), and write \(W=A\otimes B\otimes C\).
For \(T\in W\) define

\[
 E_{AB}(T)=\operatorname{im}(C^*\longrightarrow A\otimes B),
\]

and define \(E_{AC}(T),E_{BC}(T)\) similarly. After reordering factors, put

\[
 K(T)=(E_{AB}(T)\otimes C)\cap(E_{AC}(T)\otimes B)
                         \cap(E_{BC}(T)\otimes A)\subseteq W.
\]

Always \(T\in K(T)\). A tensor is concise if all three displayed image
spaces have dimension \(n\).

Let \(D\) have dimension \(m\ge2\). Write
\(F=\sum_{j=0}^{m-1}T_j\otimes d_j\). If \(T_0\) is concise, the
\(AB\mid CD\) flattening has rank at most \(n\) exactly when
\(E_{AB}(T_j)\subseteq E_{AB}(T_0)\) for every \(j\): the flattening
concatenates those column spaces, and the first already has dimension
\(n\). Consequently the three balanced flattenings all have rank at most
\(n\) exactly when

\[
                         T_j\in K(T_0)\quad\hbox{for all }j.       \tag{1}
\]

The concise locus where \(K(T)=\mathbb CT\) is open. Indeed append each
column of a variable tensor's flattening to the corresponding
\(n^2\)-by-\(n\) flattening of \(T\), and impose all
\((n+1)\)-row determinants. Together these give a polynomial matrix
\(L(T)\), linear in the variable tensor, whose kernel on the concise
locus is \(K(T)\). Always \(L(T)T=0\). Thus the additional condition is
\(\operatorname{rank}L(T)\ge n^3-1\), an open condition. Call this open
set \(\Omega\).

Let \(\mathcal F_n\subset W\otimes D\) be the variety cut out by the
three balanced rank bounds, and let \(X\) be its fourth-mode-rank-at-most-one
locus, the Segre cone \(\{T\otimes v:T\in W,v\in D\}\). Since
\(X\subset\mathcal F_n\), equation (1) gives the exact equality

\[
 \mathcal F_n\cap U=X\cap U,
 \qquad U=\{F:T_0\in\Omega\}.                                \tag{2}
\]

Whenever \(\Omega\ne\varnothing\), **\(X\) is an irreducible component
of \(\mathcal F_n\), of dimension \(n^3+m-1\)**. It is a closed
irreducible rank-one matrix variety. An irreducible closed subset of
\(\mathcal F_n\) containing \(X\) has a nonempty open intersection with
\(U\), which by (2) lies in \(X\). Density and closedness force that
subset to equal \(X\).

For \(a<n+1\), integrality of flattening ranks gives
\(Z_a(A,B,C,D)\subset\mathcal F_n\). Thus (2) isolates a closed piece of
the actual sublevel near any low-cost tensor in \(\Omega\). It does not
assert \(X\subseteq Z_a\). In fact

\[
 Z_a(A,B,C,D)\cap X
   =\{T\otimes v:T\in Z_a(A,B,C),\ v\in D\}.                    \tag{3}
\]

Appending a fixed nonzero vector preserves asymptotic rank, because
inclusion and contraction give opposite inequalities in every power.
Equation (3) exhibits the remaining three-mode geometry explicitly.

## 3. Explicit scalar-kernel tensors in every dimension

For \(n\ge3\), \(s\in\mathbb C^*\), and \(w=\sum_{i=1}^n e_i\), define

\[
 T_{n,s}=\sum_{i=1}^n e_i\otimes e_i\otimes e_i+s\,w\otimes w\otimes w.
                                                                  \tag{4}
\]

This tensor is concise and \(K(T_{n,s})=\mathbb CT_{n,s}\). To prove
conciseness, its two-mode slices are \(E_{ii}+sJ\), with \(J\) the
all-ones matrix. If
\(\operatorname{diag}(x)+s(\sum_i x_i)J=0\), the off-diagonal entries
give \(\sum_i x_i=0\), and then every \(x_i=0\).

For the kernel claim let \(S\in K(T_{n,s})\). Each two-mode image consists
of symmetric matrices, so \(S\) is symmetric in every pair of indices.
In its slice with third index \(k\), every off-diagonal entry has a common
value \(q_k\), satisfying

\[
                 q_k=s\left(\sum_i S_{iik}-nq_k\right).           \tag{5}
\]

For distinct \(j,k\), choose \(i\) different from both. Symmetry at
\((i,j,k)\) implies \(q_j=q_k\). Let the common value be \(q\).
Symmetry also makes every coefficient with exactly two equal indices
equal to \(q\). Writing \(b_k=S_{kkk}\), equation (5) becomes
\(q=s(b_k-q)\). Hence \(b_k=(1+1/s)q\) for every \(k\), and
\(S=(q/s)T_{n,s}\), as claimed.

Moreover

\[
                 R(T_{n,s})=\underline R(T_{n,s})=n+1.            \tag{6}
\]

The upper bound follows from (4). A concise tensor of rank at most \(n\)
has rank exactly \(n\); its factors in a minimal decomposition are bases
in each mode, so it is equivalent under invertible local maps to
\(D_n=\sum_i e_i^{\otimes3}\). For this diagonal tensor the three lifted
images intersect in the \(n\)-dimensional diagonal tensor space. The same
kernel dimension holds for all its local transforms. On the concise
open set, the condition \(\dim K(T)\ge n\) is closed, by the minors of
\(L(T)\). Rank-at-most-\(n\) tensors are dense in their border-rank
closure, also after restriction to that open set. Every concise tensor
of border rank at most \(n\) therefore has \(\dim K(T)\ge n\). The
scalar-kernel tensor (4) cannot have that border rank. This proves (6).

The three-mode speedup theorem [2] supplies the needed strict asymptotic
bound. Its automatic, three-direction form says that a tensor of format
\(N\times N\times N\) and border rank at most an integer \(R>2N\)
satisfies

\[
       \widetilde R(T)\le R+N^{2/3}-(R-N)^{2/3}<R.                \tag{7}
\]

Only this form is used, and it is applied only to three-mode tensors.
Apply it to the \(n\)-th grouped power of (4), with
\(N=n^n\), \(R=(n+1)^n\). The binomial expansion gives
\((1+1/n)^n>2\), so \(R>2N\). Border rank is submultiplicative and
asymptotic rank is exactly homogeneous under powers. Taking \(n\)-th
roots yields \(\widetilde R(T_{n,s})\le B_n<n+1\).
For completeness, if \(z=R-N>N\), then
\(B_n^n-N=z-z^{2/3}+N^{2/3}>0\), which also proves \(B_n>n\).

The permutation tensor
\(P=\sum_{(i,j,k)\in S_3(0,1,2)}e_i\otimes e_j\otimes e_k\)
provides the alternative three-dimensional input [3]:

\[
 K(P)=\mathbb CP,
 \qquad \widetilde R(P)^3\le74-3\sqrt[3]{81}<62.
\]

Its kernel identity also follows directly: the two-mode images are the
symmetric matrices with zero diagonal, so membership in all three lifted
images makes a tensor fully symmetric and zero whenever two indices
coincide. Only the six permutations of \((0,1,2)\) remain, with equal
coefficients. Its strict cost estimate is the explicit degeneration and
spectral estimate in [3].

## 4. Proof of the component count

It suffices first to use dimensions at most \(n\), with each active factor
of dimension exactly \(n\); the other factors may have any dimensions
between two and \(n-1\). Let \(Q\) be a concise tensor of format
\(n\times n\times n\) with \(K(Q)=\mathbb CQ\) and
\(\widetilde R(Q)\le a<n+1\). Use (4) or, for the stated
three-dimensional interval, use \(P\).

For each triple \(I\) of active factors, put \(x_I=Q\) on those factors
and \(e_0\) on all others. Then \(x_I\in Z_a\). Group the complement
of \(I\) into one space \(D\), choose its product basis, and select the
slice indexed by the all-zero complementary coordinate. Equation (2)
provides a full-ambient open neighborhood \(U_I\) of \(x_I\) such that

\[
 Z_a\cap U_I\subseteq X_I,
 \qquad X_I=\{F:\operatorname{rank}(F_{I\mid I^c})\le1\}.
\]

Choose an irreducible component \(C_I\) of \(Z_a\) containing \(x_I\).
The nonempty open \(C_I\cap U_I\) is dense in \(C_I\), and \(X_I\)
is closed; hence \(C_I\subseteq X_I\).

There is a stronger useful constraint: **every single-mode rank outside
\(I\) is at most one throughout \(C_I\)**. Fix \(i\in I\). On the
nonempty open of \(C_I\) where the \(i\)-th single-mode rank is \(n\),
write a nonzero tensor as \(A_I\otimes B_{I^c}\). For \(j\notin I\),
the \(\{i,j\}\)-flattening has rank

\[
             r_i(A_I)r_j(B_{I^c})=n\,r_j(B_{I^c})\le n.
\]

Here the equality is the Kronecker-product rank formula, and the last
inequality follows from \(a<n+1\). Thus the \(j\)-th rank is one on
that open set. The condition that it is at most one is closed, so holds
on all of \(C_I\). For distinct triples \(I,J\), choose
\(j\in J\setminus I\). The tensor \(x_J\) has \(j\)-th rank \(n\),
whereas every tensor in \(C_I\) has \(j\)-th rank at most one. Therefore
the chosen components are pairwise distinct.

Finally the diagonal tensor
\(d=\bigotimes_i e_0+\bigotimes_i e_1\) has asymptotic rank two,
and every nontrivial bipartition flattening has rank two. It lies outside
every \(X_I\). Any component containing \(d\) is consequently an
additional component. This proves \(\binom{t_n}{3}+1\).
If there are no active triples, the asserted lower bound is one and
follows from nonemptiness.

For arbitrary dimensions, compress each factor to dimension
\(\min(d_i,n)\) using a local projection with a coordinate inclusion as
section. Local maps do not increase rank in any power, and the section
preserves it. Thus the projection maps the larger-format sublevel onto
the smaller-format sublevel. A surjective morphism cannot decrease the
number of irreducible components in its source below that in its target:
the closures of the images of the finitely many source components are
irreducible closed subsets covering the target. Each target component
must equal one of those image closures. This completes the proof.

The same section-and-retraction argument propagates reducibility at a
fixed threshold under adding nonzero tensor factors. Arbitrary projection
is only rank nonincreasing; rank preservation is asserted for the embedded
copy and its chosen retraction.

## 5. An exact failure of transfer to three modes

**Proposition.** For every \(3\le a<4\), the full sublevel in
\(\mathbb C^9\otimes\mathbb C^3\otimes\mathbb C^2\) equals the
rank-at-most-three determinantal variety of its \(9\)-by-\(6\)
flattening. In particular it is irreducible.

The flattening bound proves one inclusion. For the other, a tensor with
that flattening rank at most three compresses to
\(\mathbb C^3\otimes\mathbb C^3\otimes\mathbb C^2\), padding a smaller
support if necessary. Every tensor of this format has border rank at most
three. To see this, represent it by two three-by-three matrices \((A,B)\).
The nonempty Zariski open where \(A\) is invertible and \(A^{-1}B\)
has distinct eigenvalues consists of pairs equivalent by invertible
left and right changes to \((I,\operatorname{diag}(\lambda_1,
\lambda_2,\lambda_3))\). Such a pair is the sum of three decomposable
tensors. That open is dense in the space of all pairs, so the closed
border-rank-at-most-three locus is the entire space. Asymptotic rank is
therefore at most three after compression and before padding back.
The determinantal variety is irreducible because every rank-at-most-three
matrix is a product of a nine-by-three matrix and a three-by-six matrix;
the parameter space is irreducible and the product map is surjective.

Grouping any two of the three-dimensional factors in format
\((3,3,3,2)\) produces \((9,3,2)\). Throughout
\(\sqrt[3]{62}\le a<4\), the original full four-mode sublevel is
reducible, while the full three-mode sublevel after grouping is
irreducible. This explicitly identifies a boundary of the method. It
does not assert surjectivity from the ungrouped sublevel onto the grouped
one.

## 6. What remains open

The full three-mode asymptotic-rank conjecture asserts
\(\widetilde R(T)=\max_i r_i(T)\) after compression to mode supports.
Under that conjecture, for every \(a\ge0\) the sublevel is the
subspace variety with each mode rank at most \(\lfloor a\rfloor\),
with the bounds capped at the ambient dimensions. It is irreducible:
choose the three support spaces in a product of Grassmannians, then choose
a tensor in their tensor product. The resulting vector bundle has
irreducible total space and surjects onto the subspace variety. If the
bound is zero the variety is \(\{0\}\). This implication is already
recorded in [1]. Three-mode reducibility would therefore refute the full
conjecture. It would not by itself establish \(\omega>2\), nor refute
the narrower conjecture restricted to concise tight cubic tensors [4].

The scalar-kernel proof above needs three different balanced flattenings
with a fourth mode holding simultaneous slices. In three modes those
constraints are not available. The proposition shows that a direct
grouping of the original example loses the obstruction. A reducible
linear section would not repair this gap: for example the irreducible
quadric \(xy=z^2\) has the reducible section \(z=0\).

For a fixed format, finiteness of the asymptotic-rank values remains open.
A uniform bound on the number of components of all its sublevels would
be equivalent to that finiteness. Indeed, if each closed subset in a
strict increasing chain in affine \(N\)-space has at most \(C\)
components, the vectors of component counts in dimensions
\(N,N-1,\ldots,0\) strictly increase lexicographically: until the first
differing dimension the higher-dimensional components coincide, and an
old component of the next dimension must coincide with one of the new
ones. There are only \(\binom{C+N+1}{N+1}\) such vectors. The converse
is immediate from finitely many closed sublevels. The theorem here gives
no uniform bound in a fixed format as the threshold varies, and no
infinitely valued family in one fixed format.

Finally, identifying all the actual components near the rank-one fourth
mode retains the geometry of \(Z_a(A,B,C)\) through (3). On the chart
in (2), the parametrization is
\(T\otimes(d_0+\sum_{j>0}\lambda_jd_j)\), giving
\((Z_a(A,B,C)\cap\Omega)\times\mathbb A^{m-1}\).
Determining those three-mode components explicitly, finding a three-mode
substitute for (1), and controlling components uniformly over all
thresholds in a fixed format are separate unresolved targets.

## References

1. M. Christandl, K. Hoeberechts, H. Nieuwboer, P. Vrana, J. Zuiddam,
   *Asymptotic tensor rank is characterized by polynomials*,
   [arXiv:2411.15789v2](https://arxiv.org/abs/2411.15789v2), especially
   the polynomial characterization and Section 5.
2. J. Alman, B. Li, *Asymptotic Rank Speedup Theorems, Revisited*,
   [arXiv:2605.21738v2](https://arxiv.org/abs/2605.21738v2),
   Theorem 6.1 and Corollary 6.1; the automatic three-direction bound is
   the only speedup used here.
3. *A reducible asymptotic-rank sublevel in format (3,3,3,2)*,
   [TR-23 proof](../../proofs/PROOF.md),
   Sections 2–4. Its spectral inputs are stated using
   Christandl–Vrana–Zuiddam, *Universal points in the asymptotic spectrum
   of tensors*, arXiv:1709.07851v3.
4. A. Björklund, P. Kaski, *The Asymptotic Rank Conjecture and the Set
   Cover Conjecture Are Not Both True*,
   [arXiv:2310.11926](https://arxiv.org/abs/2310.11926),
   the concise tight-tensor conjectures.
