# Prime-power mass and a characteristic-p obstruction

These are bounds and method limitations for [the equivalence](README.md) between the Erdős–Szemerédi window conjecture and Ruzsa's near-square divisor conjecture. Neither original conjecture is resolved here.

## A packing bound uniform in the number of small prime factors

Let $Q>1$ and $0<\delta<1$. Include the divisor $Q$ itself and consider the divisors of $Q^2$ in $[Q,Q(1+Q^{-\delta})]$. Express each divisor as $Q r$, where $r=u/v\in[1,1+Q^{-\delta}]$ is in lowest terms. The requirement $Qr\mid Q^2$ is equivalent to $uv\mid Q$: both $Qr$ and $Q/r$ must be integral, and $u,v$ are coprime.

Write $Q=\prod_p p^{e_p}$ and $r=\prod_p p^{x_p}$ with $|x_p|\leq e_p$. Normalize the weighted norm by
```math
\|x\|_Q=\frac{1}{\log Q}\sum_{p\mid Q}|x_p|\log p.
```
Each $x$ is in its unit ball. Two distinct ratios $r_1>r_2$ from the interval satisfy $1<r_1/r_2\leq 1+Q^{-\delta}$. In the reduced fraction $U/V=r_1/r_2$ we have $1/V\leq U/V-1\leq Q^{-\delta}$. Then $V\geq Q^\delta$ and $U>Q^\delta$. Consequently the corresponding exponent vectors are separated by
```math
\|x_1-x_2\|_Q=\frac{\log U+\log V}{\log Q}>2\delta.
```

**Dimension bound.** If the vectors span a real space of dimension $d$, the cluster has size at most $(1+1/\delta)^d$. For $d=0$ this is immediate. Otherwise the open balls of radius $\delta$ about the vectors are disjoint in that space; they lie in the radius-$1+\delta$ ball, and $d$-dimensional volume scales as the $d$th power of radius. This bound depends on the dimension of the cluster, not on the number of distinct prime divisors of $Q$.

**Mass bound.** Suppose there are $h$ primes of $Q$ that between them carry at least $(1-\delta/4)\log Q$ of the mass $\sum_p e_p\log p$. Then the cluster size is at most $(1+\lceil4/\delta\rceil)^h$. For each of those primes bin $x_p/e_p\in[-1,1]$ into intervals of width $2/M$, where $M=\lceil4/\delta\rceil$, placing the final endpoint in an extra bin. Two vectors in the same bins differ by total norm at most $2/M$ on these primes, and at most $2(\delta/4)$ on all other primes. The sum is at most $\delta$, in contradiction to separation. Count the bins. Thus any unbounded cluster with fixed power saving must simultaneously have unbounded exponent rank and unbounded mass concentration number.

## Characteristic-p degree analogue fails

There is no universal proof based solely on formal degree, divisibility and polynomial differences. Fix a prime $p$ and work over the fixed algebraic closure $K=\overline{\mathbf F_p}$. For every $m\geq2$ let
```math
Q_m(T)=T^{p^m}-T.
```
For each $(m-1)$-dimensional $\mathbf F_p$-linear subspace $V$ of the root field $\mathbf F_{p^m}$, set $D_V(T)=\prod_{v\in V}(T-v)$. These are distinct monic divisors of $Q_m$, all of degree $p^{m-1}$. Each $D_V$ is a sum of powers $T^{p^j}$ with coefficients in $K$. Indeed, starting with $D_{\{0\}}=T$, for $w\notin V$ one has
```math
D_{V+\mathbf F_p w}=D_V^p-D_V(w)^{p-1}D_V.
```
The identity follows by partitioning the larger space into the $p$ cosets of $V$ and using additivity and $\mathbf F_p$-linearity of the displayed powers. For distinct $V,W$ the common leading term cancels and
```math
\deg(D_V-D_W)\leq p^{m-2}
=\deg D_V-\frac{p-1}{p^2}\deg Q_m.
```
The number of hyperplanes is $(p^m-1)/(p-1)$ because nonzero linear functionals with the same kernel are nonzero scalar multiples. The family therefore gives arbitrarily large exact divisor clusters with a fixed relative power saving in the norm at infinity. The square-centering trick also carries this example to the square modulus $Q_m^2$ by multiplying each $D_V$ by $Q_m/D_{V_0}$ for a fixed hyperplane $V_0$.

The construction uses finite additive subgroups and the characteristic-$p$ cancellation. It does not give integer counterexamples. In particular it does not rule out characteristic-zero arguments or arguments using the real ordering.
