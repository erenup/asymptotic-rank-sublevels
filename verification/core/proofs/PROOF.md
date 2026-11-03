# A reducible asymptotic-rank sublevel in format (3,3,3,2)

## Statement

Work over the complex numbers and use tensor rank with respect to all indicated
modes. For a tensor T, write R~(T)=lim_m R(T^{boxtimes m})^{1/m}, where
corresponding modes are grouped in each power. Let

    V = C^3 tensor C^3 tensor C^3 tensor C^2,
    a = cuberoot(62),
    Y = {T in V : R~(T) <= a}.

**Theorem.** Y is not irreducible. In particular, the universal assertion in
catalogue TR-23 is false. The counterexample has order four over C. No negative
answer to the separately restricted order-three question is asserted.

We give two explicit points in Y and a proper relatively closed cover of Y.
The only external mathematical inputs are the classical asymptotic-spectrum
theorem and the tight-support subrank theorem, stated precisely below. All
specialized tensor constructions and the geometric argument are proved here.

## 1. Two classical inputs

Consider the semiring of all complex three-mode tensors, with direct sum and
grouped tensor product. Its spectral points are nonnegative real-valued maps
phi that are additive, multiplicative, normalized by phi(D_r)=r on the
r-term diagonal tensor, and monotone under linear restrictions. Strassen's
asymptotic-spectrum theorem gives

    R~(T) = max_phi phi(T).

Also phi(T) >= Q~(T), where Q(T) is the largest r such that T restricts to
D_r and Q~(T)=lim_m Q(T^{boxtimes m})^{1/m}. The latter inequality follows
directly by applying phi to each such restriction and taking m-th roots.

These statements appear in Christandl--Vrana--Zuiddam, *Universal points in
the asymptotic spectrum of tensors*, arXiv:1709.07851v3, Theorem 1.1 and
Proposition 1.6, pp.6--8, which give the precise Strassen framework. We use
the spectrum of **all complex three-mode tensors**, not a claimed spectrum
of a selected family.

The same source, Definition 4.1, Theorem 4.4 and Corollary 4.5, pp.31--32,
states the tight-support subrank theorem. The consequence we need is this:
if a three-mode tensor has a support admitting injective integer weights in
each mode whose sum is zero on every support triple, then, for every
probability distribution p on that support,

    Q~(T) >= min_j exp(H(p_j)),

where p_j are its three marginals and H is entropy with natural logarithms.
This formulation is independent of the logarithm base. Nonzero support
coefficients cause no extra condition. These are established structural
theorems, not claims inferred from the finite checks in this package.

We will use spectral monotonicity under the explicit degenerations below.
For completeness, it follows from restriction monotonicity by interpolation.
Suppose restrictions of K for nonzero t give a polynomial tensor
F(t)=T+t T_1+...+t^d T_d. The constant coefficient of F(t)^{boxtimes m}
is T^{boxtimes m}. Interpolating at dm+1 distinct nonzero complex values
expresses this coefficient as a linear combination of dm+1 restrictions
of K^{boxtimes m}, hence as a restriction of their direct sum. Thus

    phi(T)^m <= (dm+1) phi(K)^m.

Taking m-th roots proves phi(T)<=phi(K). Laurent maps are allowed when
their combined output is the displayed polynomial; the cancellations below
verify exactly this condition. This also proves the border-rank inequalities
for spectral points used here.

## 2. The three-mode tensor and its strict cost bound

Let e_0,e_1,e_2 be the standard basis of C^3 and put

    P = sum_{(i,j,k) a permutation of (0,1,2)} e_i tensor e_j tensor e_k.

We prove R~(P)^3<62. No numerical approximation enters the proof.

For an even integer q, a *paired CW tensor* C_q has basis vectors z_0
and z_r indexed by a set of q elements with a fixed-point-free involution
r -> r'. Define

    C_q = sum_r (z_0 tensor z_r tensor z_r'
               + z_r tensor z_0 tensor z_r'
               + z_r tensor z_r' tensor z_0).

It is equivalent over C to the usual small Coppersmith--Winograd tensor

    cw_q = sum_{j=1}^q (e_0 tensor e_j tensor e_j
                     + e_j tensor e_0 tensor e_j
                     + e_j tensor e_j tensor e_0).

Indeed, for each pair replace its two vectors by e_j+i e_k and e_j-i e_k.
The paired quadratic form becomes twice the identity form. These maps are
invertible, and rescaling the zero vector removes the factor two. Rank,
asymptotic rank, subrank and spectral values are preserved by these changes
of basis and by a nonzero scalar.

The following q+2 rank-one terms tend to cw_q as t tends to zero:

    t^-2 sum_{j=1}^q (e_0+t e_j)^{tensor 3}
    - t^-3 (e_0+t^2 sum_j e_j)^{tensor 3}
    + (t^-3-q t^-2) e_0^{tensor 3}.

The e_0^{tensor 3} terms cancel. The terms of degree -1 with two e_0
factors cancel. The constant term is cw_q, and every remaining term has
positive degree. Thus phi(C_8)<=10 for every spectral point phi.

Here is the finite exchange supplying a strict improvement. Let

    G=(F_2^2)^3,  S={1,2,3}^3,  b=(1,1,1),
    I=S intersect(S+b),  E=G minus(S union(S+b)).

The integers 0,1,2,3 represent the two-bit group, and addition is bitwise
XOR in each coordinate. Consequently

    |G|=64, |S|=27, |I|=8, |E|=18.

Both I and E are invariant under r -> r+b, which has no fixed point.
The group tensor

    K_G = sum_{u+v+w=0} f_u tensor f_v tensor f_w

has rank at most 64: Walsh orthogonality gives

    K_G = (1/64) sum_{characters chi of G}
                         (sum_g chi(g) f_g)^{tensor 3}.

In each mode apply the Laurent map

    f_g -> 1_{g in S} x_g + t^-2 1_{g=b} z_0 + t 1_{g in E} z_g.

The constant terms using only x variables give P^{boxtimes 3}. This is
because three nonzero elements of F_2^2 sum to zero precisely when they
are its three distinct nonzero elements. Constant terms with one z_0
and two E-indices give C_18, paired by r -> r+b. The only negative-degree
terms are t^-2 C_8(z_0,x_i), with i in I and the same pairing.

To check the last assertion exhaustively by types: a term with one z_0,
one S-index and one E-index is impossible because (S+b) intersect E is
empty. Two z_0 factors require the remaining group index 0, whose image
is zero. Three z_0 factors require b=0, which is false. The terms without
z_0 and with at least one E-index have positive degree.

Adjoin a disjoint paired C_8 to the source. Send its zero vector to
-t^-2 z_0 and its eight other vectors to their x_i. Its image is exactly
-t^-2 C_8(z_0,x_i), cancelling every negative-degree term. We have proved
the degeneration

    P^{boxtimes 3} direct-sum C_18  <=deg  D_64 direct-sum C_8.

The two target summands use disjoint coordinates: 27 main coordinates
and 19 auxiliary coordinates in each mode. The combined output is a
polynomial of degree at most three. The finite coefficient check records
216 main and 54 auxiliary constant support terms, but the type argument
above proves the identity independently of that check.

Now assign weights 0,+1,-1,...,+9,-9 to the basis of C_18, with each
paired pair receiving opposite weights. The same weights in all three
modes are injective and sum to zero on every support triple. The uniform
distribution on its 54 support triples has marginal mass 1/3 at zero and
1/27 at each of the 18 other indices. Thus the tight-support theorem gives

    Q~(C_18) >= exp(-(1/3)log(1/3)-(18/27)log(1/27))
              = 3*9^(2/3) = 3*cuberoot(81) > 12.

For every spectral point, the finite exchange therefore implies

    phi(P)^3 + phi(C_18) <= 64+phi(C_8) <= 74,
    phi(P)^3 <= 74-3*cuberoot(81) < 62.

The spectral characterization yields the uniform bound

    R~(P)^3 <= 74-3*cuberoot(81) < 62.

In particular R~(P)<a=cuberoot(62)<4. The last strict comparisons use
only the integer inequalities 81>64 and 62<64.

## 3. A polynomial open set forced into fourth-mode rank one

Write A=B=C=C^3 and D=C^2, with fourth-mode basis d_0,d_1. Each element
of V has the unique form T tensor d_0+S tensor d_1 with T,S in A tensor B
tensor C. Let Z be the common rank-at-most-three locus of the three
balanced flattenings AB|CD, AC|BD and BC|AD. Let

    X={T tensor v : T in A tensor B tensor C, v in D}.

X is closed, defined by all two-by-two minors of the ABC|D flattening.
Every element of X belongs to Z.

For a three-mode tensor T, construct a matrix L(T) of linear equations
on the 27 coordinates of S as follows. For each of the three 9-by-3
flattenings of T, append one of the three corresponding columns of S.
Take the determinant on every choice of four rows, for all three columns
of S and all three flattenings. These 1134 equations are linear in S
and have cubic polynomial coefficients in T. Always L(T)T=0, since the
appended column is then a repeated column of T.

If all three single-mode flattenings of T have rank three, then the
balanced rank bounds for T tensor d_0+S tensor d_1 are equivalent to
L(T)S=0. Indeed a 9-by-6 balanced flattening is, after reordering columns,
the matrix [T_flat S_flat]. Its rank is at most three exactly when every
column of S_flat lies in the three-dimensional column space of T_flat.
The four-row determinants above express precisely that condition.

At T=P the three mode flattenings have rank three. For example its
AB image is the space of symmetric three-by-three matrices with zero
diagonal: it is spanned by e_0 e_1+e_1 e_0, e_0 e_2+e_2 e_0, and
e_1 e_2+e_2 e_1. Hence L(P)S=0 says that S is symmetric under each pair
of index exchanges, and that its coefficients vanish whenever any two
indices coincide. Its only possible nonzero coefficients are the six
permutations of (0,1,2), and these coefficients are all equal. Therefore

    ker L(P) = C P,   rank L(P)=26.

Define U to be the subset of V where the first slice T has all three
mode-flattening ranks three and rank L(T)>=26. These are polynomial open
conditions, and x=P tensor d_0 belongs to U. On U, T is nonzero and
L(T)T=0, so rank L(T)=26 and ker L(T)=C T. Consequently

    Z intersect U subset X:

the equations force S=lambda T, so the full tensor equals
T tensor(d_0+lambda d_1). This is an assertion about an open subset of
the entire 54-dimensional ambient space, not a restriction of the
asymptotic-rank question to a selected slice.

## 4. An explicit proper closed cover of the full sublevel

For every tensor, any matrix flattening has rank at most its asymptotic
tensor rank. To see this, the flattening of its m-th grouped power is
the m-th Kronecker power of the matrix flattening, up to coordinate
permutations. Its matrix rank is the m-th power of the original rank,
and it lower-bounds tensor rank. Taking m-th roots and limits proves
the claim. Because a<4, the balanced flattening ranks of every element
of Y are at most three. Thus Y is contained in Z.

Appending a fixed nonzero fourth-mode vector preserves tensor rank and
asymptotic rank. Inclusion gives one inequality, and contraction with a
linear functional taking value one on that vector gives the other,
for every power. Section 2 therefore shows x=P tensor d_0 is in Y.

The second explicit point is

    y=e_0 tensor e_0 tensor e_0 tensor d_0
      +e_1 tensor e_1 tensor e_1 tensor d_1.

Its tensor rank and asymptotic rank are exactly two, by the displayed
decomposition and its fourth-mode flattening rank. Since a>3>2, it
belongs to Y, while that flattening rank shows y is outside X.

Set

    Y_1=Y intersect X,   Y_2=Y intersect(V minus U).

Both sets are relatively Zariski closed in Y. Since Y is contained in Z
and Z intersect U is contained in X, they cover Y. They are both proper:
y is outside Y_1 and x is outside Y_2. This proves that Y is reducible.
The argument proves failure of topological irreducibility directly; it
does not need the separate theorem that asymptotic-rank sublevels are
Zariski closed. That known theorem identifies Y as a reducible variety.

The classical spectral and tight-support inputs are cited in Section 1.
No matrix-multiplication exponent bound, conjectural asymptotic-rank
identity, optimized decimal estimate, or generic-rank sample is used.
