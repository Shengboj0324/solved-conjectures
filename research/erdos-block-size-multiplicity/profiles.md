# Limiting block sizes in the Erdős–Purdy problem

Let a nontrivial pairwise balanced design have $v$ points, $b$ blocks, $m_k$ blocks of size $k$ and $M=\max_k m_k$. Every pair of points lies on exactly one block, and each block has between two and $v-1$ points. Write $F(v)$ for the minimum possible $M$. Erdős and Purdy conjectured $F(v)=c\sqrt v+o(\sqrt v)$ with an unspecified constant. Their order-of-growth problem remains open. [Original problem, equation (5) and Theorem 2](https://users.renyi.hu/~p_erdos/1978-42.pdf) · [Gyárfás, §2](https://users.renyi.hu/~gyarfas/Cikkek/101_Gyarfas_ErdosProblemsOnIrregularitiesOfLineSizesAndPointDegrees.pdf).

**Theorem.** Consider any sequence of such designs with $v\to\infty$ and $M/\sqrt v\to\alpha<\infty$. Form the block-size measures
```math
\mu_v=\frac1v\sum_{B}\delta_{|B|/\sqrt v}.
```
They have bounded mass and a common compact support. Each subsequential weak limit $\mu$ is supported on $[0,1]$, has density at most $\alpha$ with respect to length, and satisfies
```math
\int_0^1x^2\,d\mu(x)=1.
```
In particular $\liminf_{v\to\infty}F(v)/\sqrt v\ge3$. For a finite subsequential limit $T$ of $b/v$ one has
```math
T\ \ge\ \alpha\left[1-(1-3/\alpha)^{1/3}\right].
```
If $M/\sqrt v\to3$, then $\mu_v$ converges to three times length on $[0,1]$. Consequently $b/v\to3$, the total incidence count divided by $v^{3/2}$ tends to $3/2$, and the point degrees divided by $\sqrt v$ converge in empirical mean square to $3/2$. These are necessary conditions on a putative construction.

## Large blocks and total incidences

Choose $C$ with $M\le C\sqrt v$. The at most $\lceil\sqrt v\rceil$ small sizes supply $O_C(v)$ blocks. Each block larger than $\lceil\sqrt v\rceil$ accounts for at least $v$ ordered pairs, out of $v(v-1)$. Thus $b=O_C(v)$. For the total incidence count $I=\sum_B |B|$, pair counting and Cauchy–Schwarz give
```math
I^2\le b\sum_B |B|^2=b\,[v(v-1)+I],\qquad I\le b+v\sqrt b=O_C(v^{3/2}).
```

Suppose a block has $k=v-m\ge v/2$ points. Each other block meets it at most once. In a block meeting it once with $j\ge2$ outside points, the $j$ crossing pairs number at most the $j(j-1)$ ordered pairs of outside points. All such ordered outside pairs across blocks are distinct. Therefore at least $km-m(m-1)=m(v+1-2m)$ crossing pairs are themselves two-point blocks. By concavity this is at least $v/2$ for $1\le m\le v/2$. The argument is the ordinary-line count of Erdős and Purdy, Lemma 1, valid for abstract designs. Thus $M\le C\sqrt v$ rules out $k\ge v/2$ for sufficiently large $v$. Each outside point lies on at least $k$ blocks, one through each point of the given block. It follows that $k(v-k)\le I$, hence every block has size at most $2I/v=O_C(\sqrt v)$. [Erdős and Purdy, p. 206](https://users.renyi.hu/~p_erdos/1978-42.pdf).

Fix $\epsilon>0$ and put $K=\lceil(1+\epsilon)\sqrt v\rceil$. Truncate each of the $t$ blocks of size at least $K$ to any $K$ of its points. The truncations still intersect pairwise in at most one point. For the numbers $a_x$ of truncations through each point, $\sum_xa_x=tK$ and $\sum_x a_x(a_x-1)\le t(t-1)$. Cauchy–Schwarz, for $t>0$, gives
```math
t(K^2-v)\le v(K-1).
```
Thus $t=O_\epsilon(\sqrt v)$. Since the maximum size is $O_C(\sqrt v)$, those blocks contribute $O_{C,\epsilon}(v^{3/2})$ to the sum of squares.

## The limiting distribution

The mass of $\mu_v$ is $b/v=O_C(1)$ and its support is uniformly bounded. Every subsequence has a weakly convergent further subsequence. The truncation bound shows that the mass above $1+\epsilon$ tends to zero for every fixed $\epsilon>0$. The limiting measure is supported on $[0,1]$. For a nonnegative continuous function $g$ with compact support the integer sizes give
```math
\int g\,d\mu_v\le\frac{M}{\sqrt v}\,\frac1{\sqrt v}\sum_{k\ge0}g(k/\sqrt v).
```
The Riemann sum converges to $\int_0^\infty g(x)\,dx$, proving the density bound. The second moment is $(v(v-1)+I)/v^2\to1$. It passes to the limit because of the common compact support. Integrating $x^2$ against the maximal density yields $1\le\alpha/3$. Applying this to minimizers on any bounded convergent subsequence of $F(v)/\sqrt v$ proves the unconditional lower bound.

For given mass $T$, the largest second moment allowed by the density cap is attained by density $\alpha$ on $[1-T/\alpha,1]$. Indeed, density missing above this threshold has the same mass as the density below it and can be moved upwards. Thus $1\le\alpha[1-(1-T/\alpha)^3]/3$, as asserted. If $\alpha=3$, the nonnegative measure $3\,dx-\mu$ has zero second moment. It is absolutely continuous, so it is zero even at the origin. Every weak limit is then the same. Taking zeroth and first moments gives the limits for $b$ and $I$.

## Degrees at individual points

Let $d_x$ be the degree of point $x$. The sizes of its incident blocks obey $\sum_{B\ni x}(|B|-1)=v-1$. At most $M$ summands can equal any particular positive integer. In increasing order the $j$th summand is at least $j/M$, giving $d_x(d_x+1)\le2M(v-1)$ and $d_{\max}=O_C(v^{3/4})$.

Let $N$ be the points-by-blocks incidence matrix and $P$ orthogonal projection onto the subspace perpendicular to the all-ones vector. Each off-diagonal entry of $NN^{\mathsf T}$ is one. Hence $PNN^{\mathsf T}P=P\,\mathrm{diag}(d_x-1)P$ has operator norm at most $d_{\max}-1$. Applying $PN$ to the all-ones vector on blocks gives
```math
\sum_x(d_x-I/v)^2\le b(d_{\max}-1)=O_C(v^{7/4}).
```
After division by $v^2$ this tends to zero. At $\alpha=3$, the mean normalized degree $I/v^{3/2}$ tends to $3/2$.

[Research issue and prior-work search](https://github.com/1337isnot1337/solved-conjectures/issues/780) · [All-orders reduction](restriction.md) · [Square-window criterion](windows.md).
