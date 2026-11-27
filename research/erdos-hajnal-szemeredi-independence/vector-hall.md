# Bounded Hall ratio and unbounded finite vector chromatic number

For every fixed $\varepsilon>0$ and all sufficiently large $n$, there is a graph on at most $n$ vertices with Hall ratio at most $4+\varepsilon$ and vector chromatic number at least $c\sqrt{\log\log n}$ for an absolute $c>0$. It can simultaneously satisfy Steiner's stronger conclusion that every subgraph $H$ has an independent set of the ambient graph meeting at least $|E(H)|/(4+\varepsilon)$ of its edges. Thus a uniform finite vector coloring cannot be deduced from the independence-ratio premise in Erdős, Hajnal and Szemerédi's uncountable problem. [Original question](https://users.renyi.hu/~p_erdos/1982-11.pdf) · [Steiner, Construction 2.1 and Lemma 4.1](https://doi.org/10.1007/s00493-025-00164-0).

## The layers and a sampling estimate

Use Steiner's independent layers $B_1,\ldots,B_k$, with $k=\lfloor(\log_4\log n)/3\rfloor$ and $N_i=|B_i|=\lfloor n^{1-4^i/\sqrt{\log n}}\rfloor$. For $i<j$ each possible edge independently appears with probability $1/N_j$. This is the convention used in the product in the proof of Lemma 2.2 and the expected edge count in the proof of Claim 4.2(2). The displayed definition in Construction 2.1 reverses the index inequality. The proof of Lemma 4.1 gives the two asserted independence properties with probability tending to one for the convention used in those computations. The sum of the layer sizes is at most $n$ for large $n$.

For each $x\in B_i$ and $j>i$, select a random representative $R_{xj}$ in $B_j$ as follows. When $x$ has neighbors there, choose one uniformly at random and retain it with probability $p/[1-(1-1/N_j)^{N_j}]$, for $p=1/2$. Otherwise record a null symbol, also used when the choice is discarded. The denominator is at least $1-e^{-1}$. For each fixed $i$, these variables are independent over pairs $(x,j)$. Each is uniform on its target conditional on being nonnull, with unconditional nonnull probability $p$. Every retained representative is an actual neighbor.

Put $t=1/[10(1+K_G) k^2]$, where $K_G$ is the absolute real Grothendieck constant. With probability tending to one we have both of the following, simultaneously for all $i$ and all indicated later layers. Averages here are uniform over $x\in B_i$.

* For every sign function $a$ on $B_j$, extended by zero at null, the empirical mean of $a(R_{xj})$ differs from $p\,\mathbb E_{B_j}a$ by at most $t$.
* For each $i<j<l$ and all sign functions $a,b$ on $B_j,B_l$, with the same convention, the empirical mean of $a(R_{xj})b(R_{xl})$ differs from $p^2\mathbb E a\,\mathbb E b$ by at most $t$.

Indeed, for each choice the $N_i$ scalar summands are independent, take values in $[-1,1]$, and have the expectations shown. Hoeffding's inequality bounds each failure probability by $2\exp(-t^2N_i/2)$. For each triple there are at most $2^{N_j+N_l}\le 2^{2N_{i+1}}$ choices, and there are at most $2k^3$ tests of layer indices including the one-function cases. The smallest successive size ratio grows at least as $\exp(c_0\sqrt{\log n})$ for a constant $c_0>0$, so $t^2N_i/N_{i+1}\to\infty$ uniformly. Also $N_k\ge n^{1-o(1)}$. The union bound tends to zero.

## The vector constraint

Fix any realization with these estimates. Give every vertex a unit vector $u_x$ in a real Hilbert space. Let $m_j=\mathbb E_{x\in B_j}u_x$ and write $Y_{xj}=u_{R_{xj}}$ for retained representatives, taking value zero at null. The first sign estimate bounds by $t$ the sum of the absolute errors in the probabilities of individual nonnull outcomes. Consequently
```math
 \|\mathbb E_x Y_{xj}-p m_j\|\le t,
 \qquad \mathbb P_x(R_{xj}\ne\varnothing)\ge p-t.
```
For a pair of layers form the rectangular matrix whose $(v,w)$ entry is the empirical joint probability of these two nonnull outcomes minus $p^2/(N_jN_l)$. The second sign estimate bounds its bilinear form on signs by $t$. The real Grothendieck inequality bounds the same form on inner products of arbitrary unit vectors by $K_G t$. Hence
```math
 \left|\mathbb E_x\langle Y_{xj},Y_{xl}\rangle-p^2\langle m_j,m_l\rangle\right|\le K_G t .
```
This uniformity allows the proposed vector coloring to depend on the entire graph. [Grothendieck inequality, scalar and Hilbert-space forms](https://arxiv.org/abs/1101.4195).

For $s=k-i$, put $W_x=\sum_{j>i}Y_{xj}$ and $M_i=p\sum_{j>i}m_j$. Expanding the square gives
```math
 \mathbb E_x\|W_x-M_i\|^2\le s+s(s-1)K_Gt+2ps^2t\le s+1 .
```
Indeed the diagonal terms in $\mathbb E\|W_x\|^2$ contribute at most $s$. The expected cross terms agree up to the displayed error with the cross terms of $\|M_i\|^2$, whose diagonal is nonnegative. Finally $\|\mathbb E W_x-M_i\|\le st$ and $\|M_i\|\le ps$.

If every edge satisfies $\langle u_x,u_y\rangle\le-\gamma$, each retained neighbor contributes at most $-\gamma$ to $\langle u_x,W_x\rangle$. Cauchy–Schwarz therefore gives
```math
 p\sum_{j>i}\langle m_i,m_j\rangle
 \le -\gamma(p-t)s+\sqrt{s+1}.
```
Sum over $1\le i<k$. The sum of all pairwise mean inner products is at least $-k/2$, by nonnegativity of $\|\sum_i m_i\|^2$ and $\|m_i\|\le1$. Thus
```math
 \gamma(p-t)\binom{k}{2}
 \le pk/2+\sum_{s=1}^{k-1}\sqrt{s+1}
 \le pk/2+k\sqrt{k}.
```
It follows that $\gamma=O(k^{-1/2})$ for every assignment. In a vector coloring with value $K$ the margin is $\gamma=1/(K-1)$, which proves the lower bound. Steiner's Hall and degree-weight events and the representative estimates all hold with probability tending to one in the joint probability space. Taking any common realization and forgetting the representatives gives the claimed ordinary graph. Adding isolated vertices gives exactly $n$ vertices if desired.

The known finite separating constructions already give unbounded fractional chromatic number, and Davies, Hatzel and Yepremyan announced the sharp Hall threshold $2+\varepsilon$ for fractional coloring. The argument here supplies a vector obstruction for Steiner's layered graphs. It gives finite examples and does not construct a graph of chromatic number $\aleph_1$. [Dvořák, Ossona de Mendez and Wu](https://arxiv.org/abs/1812.07327) · [Davies, Hatzel and Yepremyan, 2026 seminar announcement](https://www.math.princeton.edu/events/graphs-large-fractional-chromatic-number-and-small-hall-ratio-2026-04-16t190000).
