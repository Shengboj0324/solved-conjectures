# Block sizes in prime-order Desarguesian planes

Let $P$ be $v$ noncollinear points, and let $M$ be the largest number of spanned lines of a common size. Size means the number of points of $P$ on the line. The whole ambient plane and its order can vary with $P$.

**Theorem.** Every such set in $\mathrm{PG}(2,p)$, $p$ prime, has $M\gg v^{5/7}$. Thus no sequence of point restrictions of prime-order Desarguesian planes realizes the Erdős–Purdy bound $M=O(\sqrt v)$. This includes restrictions whose densities in the ambient planes tend to zero.

Two estimates give the result. The first works over fields without a bound on their extension degrees whenever the characteristic is sufficiently large. The second works in arbitrary finite projective planes, including non-Desarguesian ones.

## From the number of lines to a repeated size

For any pairwise balanced design with $b$ blocks, let $m_j$ count size $j$ blocks. For every real $K\ge2$ there are at most $MK$ blocks of size at most $K$. Each larger block uses at least $K^2/2$ ordered pairs. Optimizing $MK+2v^2/K^2$ gives

```math
 b\ll v^{2/3}M^{2/3}.
```

Indeed, take $K=\max(2,(v^2/M)^{1/3})$, using $M\le\binom v2$. In particular, $b\gg v^{8/7}$ implies $M\gg v^{5/7}$.

Suppose instead that some line contains $k\ge cv$ points for a fixed $c>0$. If $k\ge v/2$, the ordinary-line estimate in [the profile proof](profiles.md) gives $m_2\ge v/2$. Otherwise the total number $I$ of point-line incidences is at least $k(v-k)\gg_c v^2$. The identity $\sum_B |B|^2=v(v-1)+I$ and Cauchy–Schwarz imply $b\ge I^2/(v(v-1)+I)\gg_c v^2$, since $I\le v(v-1)$. The bound on $b$ now gives $M\gg_c v^2$. In either case $M\gg_c v$.

Stevens and de Zeeuw's Corollary 14 gives one of these two alternatives for any $v$ affine points over a field of characteristic zero or of characteristic $p$ with $v\ll p^{7/6}$. For projective points, first extend the field to an infinite extension of the same characteristic if necessary. One can choose a line at infinity avoiding the finitely many points, and extending the field preserves their collinearity. We conclude $M\gg v^{5/7}$ in this range. [Stevens and de Zeeuw, §5.4](https://arxiv.org/abs/1609.06284).

## Concentration in an arbitrary finite plane

Let the ambient plane have order $q$ and $N=q^2+q+1$ lines. For a uniform random line let $X$ count its points of $P$. Counting ordered pairs of distinct points and using $(q+1)^2=N+q$ gives

```math
 a=\mathbb E X=\frac{v(q+1)}{N},\qquad
 \operatorname{Var}(X)=\frac{qv}{N}\left(1-\frac vN\right)\le a.
```

If $v\ge 32(q+1)$, then $a\ge32$. At least $3N/4$ lines have sizes in $[a-2\sqrt a,a+2\sqrt a]$ by Chebyshev. All these lines are spanned, and this interval contains at most $4\sqrt a+1$ integers. Consequently

```math
 M\gg N/\sqrt a\gg q^{5/2}/\sqrt v\gg v^{3/4}.
```

Here $v\le N$ gives the last inequality. For $q=p$ prime the two ranges exhaust all $v$, since $v<32(p+1)$ implies $v\ll p^{7/6}$. The original abstract-design conjecture remains open. The dense-restriction obstruction was known. The sparse prime-field conclusion uses the finite-field Beck theorem and is independent of how the subset is chosen. [Erdős–Purdy research and earlier constructions](README.md) · [Tracking issue](https://github.com/1337isnot1337/solved-conjectures/issues/780).

## The sharp order in the prime-plane model

Mark Lewko's October 2026 incidence theorem improves the sparse estimate. In fact, if $F_{\mathrm{prime}}(v)$ is the least possible $M$ among $v$-point restrictions of prime-order Desarguesian planes, allowing the prime to vary, then

```math
 F_{\mathrm{prime}}(v)=\Theta(v^{3/4}).
```

For the lower bound, consider $v$ points over any field of characteristic $p$, with $1/p=0$ in characteristic zero. For $j\ge 4(1+2v/p)$, let $s$ be the number of lines containing at least $j$ points. Lewko's Theorem 1 gives

```math
 js\le 3(vs)^{2/3}+v+(1+2v/p)s,
 \qquad s\ll v^2/j^3+v/j.
```

For the second inequality, absorb the last summand and use whichever of the first two summands is larger. Fix a sufficiently small absolute $c>0$. If a line has at least $cv$ points, the earlier crossing-pair argument gives $M\gg v$. Otherwise group lines with sizes at least $T$ in dyadic intervals $[j,2j)$ where $j=2^i T$, taking $T=\lceil C(1+v/p)\rceil$ for a sufficiently large absolute $C$. These lines contain in total at most a constant times

```math
 \sum_{T\le j<cv}(v^2/j+vj)\ll v^2/T+cv^2
```

unordered pairs. Choosing $c$ small and $C$ large leaves at least a constant times $v^2$ pairs on lines of size less than $T$. Those lines supply at most $M\sum_{j<T}\binom{j}{2}\ll MT^3$ pairs. This proves

```math
 M\gg \min\{v,\ v^2/(1+v/p)^3\}.
```

In particular $M\gg v$ whenever $v<32(p+1)$. The variance argument covers the complementary range with $M\gg v^{3/4}$. [Lewko, Theorem 1, v3](https://arxiv.org/abs/2609.27023v3).

For the matching upper bound, choose a prime between $\lceil\sqrt{2v}\rceil$ and $2\lceil\sqrt{2v}\rceil$ by Bertrand's postulate. The full plane has $p^2+p+1$ blocks, all of size $p+1$. In the [square-window restriction theorem](windows.md) its only nonempty window has width $2\lfloor\sqrt{p+1}\rfloor+1$, so its window average is $O(p^{3/2})$. The desired $v$ is a fraction bounded away from both zero and one of the order of the full design. Taking the exact-size restriction gives $M=O(p^{3/2})=O(v^{3/4})$ for every sufficiently large $v$. This is the order of the random plane restriction already obtained by Erdős and Purdy. The new lower bound holds over every choice of prime and subset. [Erdős and Purdy, Theorem 2](https://users.renyi.hu/~p_erdos/1978-42.pdf).
