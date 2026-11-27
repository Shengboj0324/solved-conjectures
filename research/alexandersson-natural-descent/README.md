# Alexandersson's natural-descent conjecture

Status: unresolved research. No proof or counterexample is claimed. This note records a reproducible exact calculation, the attempted structural route, and the current literature screen. It does not count a finite search or a different polynomial as a solution.

Coordination: [issue 116](https://github.com/1337isnot1337/solved-conjectures/issues/116). Research started 20 November 2026. No Lean work is included.

## The full target

For a partition $\lambda$, let $\operatorname{SYT}(\lambda)$ be its standard Young tableaux. A natural descent of a tableau is an index $i$ for which $i+1$ lies in a strictly higher row than $i$. Define

```math
N_\lambda(t)=\sum_{T\in\operatorname{SYT}(\lambda)}t^{\operatorname{ndes}(T)}.
```

The conjecture asks that $N_\lambda(t)$ have only real zeros for every partition. The statement is explicitly attributed to Alexandersson (2026) in the author-maintained [SymCat open-problem page](https://www.symmetricfunctions.com/realRootedOpenProblems.htm), under “Tableaux, polytopes and Ehrhart theory.”

Natural descents differ from ordinary tableau descents, which ask for a strictly lower row. Brenti's theorem for column-strict labeled Ferrers posets concerns ordinary descents. It does not settle this target. [Brändén (2004)](https://doi.org/10.1023/B:JACO.0000047295.93525.df) proves interlacing results for that known class and for series-parallel posets. David Wagner's [Waterloo seminar abstract (2021)](https://uwaterloo.ca/combinatorics-and-optimization/events/algebraic-combinatorics-seminar-david-wagner-4) separately identifies the naturally labeled Ferrers class as unresolved.

## Exact evaluator

Write $s=|\lambda|$ and let $\Omega_\lambda(u)$ count weakly order-preserving maps from the Ferrers poset to $\{1,\ldots,u\}$. The standard order-polytope Eulerian numerator identity is

```math
\sum_{m\ge0}\Omega_\lambda(m+1)t^m
  =\frac{N_\lambda(t)}{(1-t)^{s+1}}.
```

For a partition with $\ell$ nonzero rows, the straight-shape case of the Kreweras–MacMahon determinant gives

```math
\Omega_\lambda(m+1)
 =\det\!\left[\binom{m+\lambda_i}{\lambda_i-i+j}\right]_{1\le i,j\le\ell}.
```

The determinant is cited, not a new formula: see [Ferroni–Morales–Panova, *Skew shapes, Ehrhart positivity, and beyond*, Proposition 2.2, equation (2.4)](https://doi.org/10.1112/plms.70204), which credits Kreweras for skew shapes and MacMahon for straight shapes. Here a binomial coefficient is zero when its lower index is negative or exceeds its nonnegative upper index.

Consequently the coefficient of $t^r$ is

```math
[t^r]N_\lambda(t)
 =\sum_{j=0}^r(-1)^j\binom{s+1}{j}\Omega_\lambda(r-j+1).
```

`natural_descent.py` evaluates each determinant by fraction-free Bareiss elimination and forms this numerator in integer arithmetic. The script also has a genuinely different calculation: a dynamic program adds the entries of a tableau one at a time, tracks the row of the last entry, and multiplies by $t$ exactly when the new entry is placed above the previous one.

The two methods agree for all 138 partitions of sizes 1 through 10. This verifies the implementation on independent finite data. It proves no universal root statement.

Replay:

```sh
python3 natural_descent.py --sanity-only
```

Expected output:

```json
{"independent_tableau_comparisons": 138, "maximum_size": 10}
```

The script can also generate seeded larger examples. Coefficients remain exact; floating-point roots are only a preliminary screen. `--exact` requests a Sturm root count through SymPy for every example, and otherwise exact counting is required before reporting any suspected counterexample. An exact run on larger random shapes was interrupted after its first completed example because integer Sturm arithmetic was too slow; it is not recorded as a completed range check.

## Structural route and precise gap

Let $Q_{\lambda,r}(t)$ count tableaux of shape $\lambda$ whose largest entry lies in row $r$, by natural descents. Deleting that largest entry gives the exact recurrence

```math
Q_{\lambda,r}(t)
 =\sum_j t^{[j>r]}Q_{\lambda-e_r,j}(t),
```

when row $r$ ends in a removable corner. The empty shape supplies the initial value. The total polynomial is $N_\lambda=\sum_r Q_{\lambda,r}$.

This has the form of familiar interlacing-preserving recurrences, but the summands come from different predecessor shapes. Real-rootedness of each predecessor by itself is insufficient; the required compatibility across shapes has not been established. No induction is complete without that additional invariant. The determinant formula alone also does not imply real-rootedness after the Eulerian transform.

## Literature screen and exclusions

Searches on 20 November 2026 used both available web search engines, exact author/name combinations, primary paper statements, author-maintained pages, and public research records. This is a bounded search, not a proof of absence of prior work.

| Candidate | Disposition | Evidence |
|---|---|---|
| Alexandersson's natural-descent conjecture | Active, unresolved here | Exact author-maintained statement linked above; distinct from the ordinary-descent theorem. |
| Pandey's parity conjecture | Excluded: previously disproved | [Public research record, section 6](https://github.com/demonstrandum-research/artifacts/blob/main/RESULTS.md), and [a later explicit priority correction](https://the-omega-institute.github.io/trureturing-mdbook/Problems/pandey-parity-conjecture-refutation.html). The isomorphism $\mathrm{GP}(7,2)\cong\mathrm{GP}(7,3)$ already refutes parity as an invariant; the same argument was published earlier. |
| Alexandersson–Alhajjar's skew-GT Ehrhart-positivity conjecture | Excluded: previously proved | [Jochemko–Menon, arXiv:2604.08394](https://arxiv.org/abs/2604.08394), Theorem 3.5; [author-maintained contextual statement](https://www.symmetricfunctions.com/ehrhart.htm). |
| Hill–Luo–Trinh–Vindas-Meléndez conjecture | Screened as another whole target; unresolved here | [arXiv:2607.15503](https://arxiv.org/abs/2607.15503), Conjecture 8.1, arbitrary positive parameter vector and dimension at least three. The special two-parameter theorem is already in that paper. |
| Gessel–Zhuang real-rootedness conjecture | Screened; no attempt claimed | [Two-sided permutation statistics via symmetric functions](https://arxiv.org/abs/2306.15785), Conjecture 7.1. Current specialist page records checks through size 50; these are not a full proof. |

The Pandey example matters for target selection: current aggregator pages can still label a conjecture open despite an existing explicit refutation. An apparently short new proof must survive a search for the exact obstruction, not just a check of a status label.

A [long-first-row theorem](long-first-row.md) now propagates real-rootedness from any fixed Ferrers tail to every sufficiently long first-row extension. It also gives strict consecutive interlacing and individual zero asymptotics.
