# The convex-polygon density in the binary Erdős–Szekeres limit

The Erdős–Sylvester problem asks for the minimum limiting density of convex $k$-tuples. Goaoc, Hubard, de Joannis de Verclos, Sereni and Volec define a particular limit $\ell_E$ by independent fair infinite binary strings. Their Proposition 17 in the 2018 preprint prints the estimate $\ell_E(\diamond_k)=2^{-k^2/8+O(k\log k)}$. Its proof bounds the probability by requiring a single monochromatic-orientation chain of half the size. Counting both hull chains gives an exact recurrence and the different leading exponent $1/4$ for this specified limit. [Preprint, §§3.4.1–3.4.2](https://arxiv.org/abs/1811.02236) · [Conference paper](https://doi.org/10.4230/LIPIcs.SOCG.2015.300).

Use their geometric presentation with a left and a right first-bit cluster, each distributed as an affine copy of the full measure. All cross slopes lie above all slopes internal to either cluster. Write $u_k$ for the probability that $k$ labeled samples form a cup, and $P_k$ for the probability that they are in convex position. The cap probability is also $u_k$ by the symmetry reversing the two digits and point order. We set $u_1=u_2=1$. The authors' cup recurrence is
```math
 u_k=\frac{k}{2^k-2}u_{k-1}\quad(k\ge2).
```
Indeed either all points are in the same half or exactly one is in the right half and the left points form a cup. For $k=2$ the recurrence follows directly from these same cases.

If both halves occur, the selected points are in convex position exactly when the left selection is a cup and the right selection a cap. In a convex polygon, an upper chain crossing to the right cannot have an internal edge on the left because that slope is below the cross slope. The lower chain cannot have an internal edge on the right. Conversely, a left cup followed by a cross edge to the rightmost point gives the lower chain. A cross edge from the leftmost point followed by the right cap gives the upper chain. All chosen points lie on these two hulls, by the strict slope inequalities. This also covers singleton parts and pairs. Conditional on the first-bit split, the two internal samples are independent. Thus for $k\ge2$,
```math
 (2^k-2)P_k=\sum_{j=1}^{k-1}\binom{k}{j}u_j u_{k-j}.
```
The all-equal first-bit event accounts for the subtracted two. For example the recurrence gives $P_3=1$ and $P_4=5/7$.

Put $Q_m=\prod_{i=1}^m(1-2^{-i})$, with $Q_0=1$ and $Q_\infty>0$. The cup recurrence gives $u_j=j!2^{1-j(j+1)/2}/Q_{j-1}$. Substitution and completion of the square give
```math
 P_k=\frac{k!\,2^{2-k/2-k^2/4}}{2^k-2}
 \sum_{j=1}^{k-1}\frac{2^{-(j-k/2)^2}}{Q_{j-1}Q_{k-j-1}}.
```
On either parity subsequence the summands translated by $k/2$ are bounded by the summable sequence $2^{-z^2}/Q_\infty^2$ on the integer or half-integer lattice. Dominated convergence therefore yields, with $\theta_s=\sum_{z\in\mathbb Z+s}2^{-z^2}$,
```math
 P_k\sim \frac{4\theta_{(k\bmod2)/2}}{Q_\infty^2}
 k!\,2^{-k^2/4-3k/2}.
```
In particular the leading quadratic coefficient is exactly $1/4$. The bound proved with just one chain in the preprint remains a valid one-sided upper estimate. The extremal density over all distributions and the total-count limit of Erdős and Hammer are separate open questions.
