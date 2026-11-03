# Asymptotic Tensor-Rank Sublevels Need Not Be Irreducible

Authors: Wenqi Zhu; Qiyuan Chen; Ping Nie.

Wenqi Zhu — Mathematical Institute, Woodstock Road, University of Oxford, Oxford, UK, OX2 6GG — wenqi.zhu@maths.ox.ac.uk

Qiyuan Chen — Academy of Mathematics and Systems Science, Chinese Academy of Sciences, Beijing, China

Ping Nie — David R. Cheriton School of Computer Science, University of Waterloo — ping.nie@uwaterloo.ca

The [paper](main.pdf) proves that, over the complex numbers, the
asymptotic-rank sublevel at the cube root of 62 in tensor format
`(3,3,3,2)` is reducible in the Zariski topology. This answers the
assertion over all tensor orders negatively; the order-three question
remains open. Section 6 proves, for every order $k\geq4$ with all factor
dimensions at least two and every $n\geq3$, lower bounds for the number of
irreducible components of asymptotic-rank sublevels above an explicit
threshold $`B_n`$.

The source is [main.tex](main.tex), with the section
[sections/components.tex](sections/components.tex) and bibliography
[refs.bib](refs.bib). Build from this directory with LaTeX, BibTeX, and
`latexmk`:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error -outdir=build/ci main.tex
```

The rebuilt PDF is `build/ci/main.pdf`. The included `main.pdf` has the
same content. Standard TeX Live packages suffice. The source and PDF list
the authors above.

All files in this directory, including the manuscript source and PDF, are
licensed under [CC BY-SA 4.0](LICENSE).
