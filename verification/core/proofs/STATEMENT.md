# TR-23: asymptotic-rank sublevel irreducibility

For every algebraically closed field F, order k>=3, positive dimensions d_i,
and real a>=0, is the set

    {T in tensor_i F^{d_i}: asymptotic rank(T)<=a}

an irreducible algebraic variety? Asymptotic rank uses Kronecker powers
grouping corresponding modes; the zero tensor has rank zero. The source
proves Zariski closedness. The irreducibility assertion quantifies over all
orders at least three, not just order three.

Catalogue: https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/tensor-computations/TR-23

**Answer proved in this package: no.** Over C, in format (3,3,3,2), the
sublevel at a=cuberoot(62) is reducible. PROOF.md constructs two explicit
points and a proper relatively Zariski-closed cover of the entire sublevel.
One such example refutes the universally quantified catalogue assertion.
The proof makes no claim to refute the separately restricted order-three
irreducibility question.
