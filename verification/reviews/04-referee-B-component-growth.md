# Referee report B: component growth and the grouping boundary

Reviewed: the written proofs now in verification/core/components/proofs/ (DIRECTIONS.md, COMPONENT_DERIVATION.md, MERGING_BOUNDARY.md and CHECKS.md), before the paper section on component growth was typeset. No checker was part of the reviewed material.

**Verdict: ACCEPT. No corrections requested.** This verdict applies to the four submitted documents DIRECTIONS.md, COMPONENT_DERIVATION.md, MERGING_BOUNDARY.md and CHECKS.md. It accepts the exact quantified results below, with the explicitly retained structural inputs. It does not certify literature priority or a Lean formalization.

This is an independent review. I did not contact the author or see the other referee's report (report 03) while preparing it.

## Accepted mathematical scope

Work over the complex numbers, with tensor rank using every indicated mode and powers grouping corresponding modes. For every integer n>=3, set

```math
 B_n=\left((n+1)^n+n^{2n/3}-((n+1)^n-n^n)^{2/3}\right)^{1/n}.
```

The following claims are accepted:

1. For every k>=4, every d_i>=2 and t_n=#{i:d_i>=n}, every asymptotic-rank sublevel with B_n<=a<n+1 has at least binomial(t_n,3)+1 irreducible components. The bound is a lower bound, not an exact enumeration. For t_n<3 it is the nonempty-sublevel bound one.
2. For the same k and dimensions, the n=3 component bound holds throughout cuberoot(62)<=a<4. When all d_i>=3, it is binomial(k,3)+1; in particular k=4 gives at least five components.
3. For every n>=3 and every nonzero complex s, T_(n,s)=sum_i e_i^tensor3+s(sum_i e_i)^tensor3 is concise, has scalar compatibility kernel, and has ordinary rank and border rank exactly n+1. Its asymptotic rank is at most B_n, with n<B_n<n+1. No equality with B_n is claimed.
4. For every 3<=a<4, the full grouped format(9,3,2) sublevel is exactly the rank-at-most-three locus of its9-by6 first flattening, and is irreducible.

The related local geometry claims are also correct: in balanced core dimensions n,n,n with a fourth factor of dimension m>=2, the fourth-mode rank-one locus is an irreducible component of the three-balanced-flattening rank<=n variety, of dimension n^3+m-1. Its actual asymptotic sublevel still retains three-mode geometry. No assertion that the entire rank-one locus belongs to the sublevel is made.

## Derive-first and access record

All my independent starting notes were written before my first access to the submitted proofs: a boundary/geometric note, a geometric note of my own, a core note and a second core attempt. The core attempt honestly left the balanced strict-cost step unresolved; it did not pretend to know the submitted B_n formula. It also proved why unbalanced scalar-kernel padding cannot replace a balanced concise seed in the uniform flattening argument. After comparison, the actual submitted balanced family and independently checked speedup resolve that specific gap.

Only DIRECTIONS.md, COMPONENT_DERIVATION.md, MERGING_BOUNDARY.md and CHECKS.md were opened and checked. In particular neither a review, mechanism audit or source audit prepared with the author nor the other referee's review was consulted. CHECKS.md's mentions of earlier acceptances were not used as evidence. No author contact or author-file modification occurred.

## Why the proofs pass

The compatibility matrix exactly expresses simultaneous slice-image containment when the first slice has full mode ranks. Its scalar kernel defines an ambient open set on which every slice is proportional. This forces the complement-of-triple flattening to have rank one. On the component containing a seed, mixed active/spectator flattenings then force every spectator mode to have rank at most one, including in the presence of several spectators. Different active triples consequently give different components, including disjoint triples. The two-term diagonal witness lies outside every selected rank-one cut and supplies the extra component.

The canonical proof first caps active dimensions at n, then uses a coordinate projection with an inclusion section. It maps the larger sublevel onto the smaller one; closures of irreducible-component images show that the larger format has at least as many components. Independent derivations also checked the result directly through moving support spaces/selected columns. This is a statement about full ambient sublevels, with no inference from an arbitrary reducible section.

The coefficientwise scalar-kernel calculation is valid for all complex s!=0, including s=-1 and s=-1/n. The border lower bound follows from closedness of the dimK>=n locus among concise tensors of border rank<=n; a separately reconstructed nonzero normalized-slice commutator gives the same bound. Thus both ordinary and border ranks are exactly n+1.

The independent primary-source check confirms the precise automatic three-direction statement of Alman–Li, arXiv:2605.21738v2, Theorem6.1 and Corollary6.1, printed pp19–20. The review goes further for this application: a written reconstruction derives the augmentation from an actual ordinary-rank-R decomposition into a degeneration V direct-sum X_(R-N) <=deg D_R direct-sum X_N, in all three orientations. It checks the vanishing blocks and parameter powers. Spectral duality and the tight-support subrank lower bound give the exponent2/3 and the claimed numerical upper bound. This avoids requiring the more general source assertions about arbitrary border decompositions or special low-rank slices.

For the explicit n-th power, N=n^n and R=(n+1)^n satisfy R>2N by the binomial expansion. Ordinary rank<=R is explicit; exact rank of that power is not assumed. Asymptotic rank is homogeneous under grouped powers, giving the displayed B_n. The strict endpoint inequalities follow exactly from R-N>N and positivity. The speedup is applied only to three grouped modes, then the low-cost seed is placed in the higher-order format.

For the grouped boundary, a dense open set of3-by3 matrix pencils is simultaneously equivalent to an identity/diagonal pair and has rank<=3. All pencils have border rank<=3; a separate line-interpolation argument establishes the same asymptotic upper bound directly. Support compression then identifies the entire(9,3,2) sublevel with the stated determinantal variety. A surjective matrix-product parametrization proves irreducibility. The result does not assert that grouping maps the ungrouped sublevel onto the whole grouped sublevel.

The retained structural inputs are explicitly identified: three-mode asymptotic-spectrum duality and degeneration monotonicity, the tight-support entropy/subrank theorem already used in the accepted main theorem, the accepted permutation-tensor exchange, and polynomial closedness of asymptotic-rank sublevels. The latter was independently checked in Christandl–Hoeberechts–Nieuwboer–Vrana–Zuiddam, arXiv:2411.15789v2, Theorem1.2, whose range includes arbitrary k>=3 and all real thresholds over C. Public version-specific primary sources were fetched directly into this review, without using the author's source-audit files.

## Exact checks and limitations

There is no new submitted computational checker; the submitted proofs are written all-parameter arguments. The reviewer therefore added an independent exact-rational suite. For n=3,4,5 and s=1,-1,2/3,-1/n, it computes actual pair-image annihilators and their lifted intersection, obtaining mode ranks n and compatibility-kernel dimension one in all12 cases. Diagonal reference kernels have dimension n. It also certifies outward rational radical bounds for n=3,...,12 and25, finite active-triple/extra-point rank witnesses, a disjoint-triple mixed rank-nine witness, and a grouped boundary sample.

Normal and optimized complete outputs are byte-identical. All12 controls reject in both modes, for24 rejecting runs, with exact matching diagnostics. In addition to malformed inputs, genuine mathematical corruptions include omitting two compatibility images, changing a tensor coefficient, replacing R by2N, reversing the radical difference, and submitting a boundary flattening of rank four. Failures use explicit SystemExit; the scripts have no Python assertions. I inspected the checker and harness, verified all eight recorded files and all26 outcome records, and confirmed output equality. These finite checks corroborate the formulas; they do not establish all-n topology or substitute for the written proof.

TR-22 fixed-format finiteness and general three-mode irreducibility remain open and are not accepted as solved. The conditional ARC/subspace-variety implication and the fixed-format equivalence between finite attained values and uniformly bounded component counts are correctly stated. The theorem's unbounded component counts vary the format. No matrix-multiplication exponent claim, exact component classification, exact asymptotic-rank formula, or new Lean result is inferred.

## Conclusion

The source and finite subreports are scoped contributions; this report issues the overall ACCEPT verdict. No correction or unresolved mathematical finding remains for the exact accepted scope.
