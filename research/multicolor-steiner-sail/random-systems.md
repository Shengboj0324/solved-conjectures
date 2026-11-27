# A positive multicolor sail density in almost every Steiner triple system

For every fixed $t\ge1$ and $0<\delta\le1$, there is a constant $c(t,\delta)>0$ with the following property. With probability tending to one, a uniformly random labeled Steiner triple system on $n$ vertices has, **simultaneously for all** $t$-colorings of its blocks and all sets $W$ of at least $\delta n$ vertices, at least $c(t,\delta)n^3$ monochromatic sails entirely in $W$. Orders are taken through $1,3\pmod6$. In particular a positive fraction of all sails are monochromatic and a maximal disjoint packing leaves $o(n)$ vertices with high probability, in the sense that the leftover fraction tends to zero in probability. This concerns almost every host in the original sampling model. [Original Ramsey question](https://users.renyi.hu/~gyarfas/Cikkek/182_jcd1.pdf) · [Kwan's comparison theorem](https://arxiv.org/abs/1611.02246).

## Deterministic counting argument

Use $a(u)=u^5/10000$. We only need the host to satisfy the following lower bound at finitely many $u$: every vertex set of size at least $un$ contains at least $a(u)n^2$ entire blocks. Starting with $d_0=\delta$, put $d_{i+1}=a(d_i)/(2t)$ for $0\le i<t$. Set $A=\min_{0\le i\le t}a(d_i)$, $D=4/A$ and $\eta=A/(8tD)$. Assume the lower bound at all $d_i$.

Fix any coloring and $W$ with $|W|\ge\delta n$. Suppose there are fewer than $\eta n^3$ monochromatic sails contained in $W$. Fewer than $n/D$ vertices are centers of more than $D\eta n^2$ such sails. Call these vertices exceptional. Since a vertex in a linear triple system belongs to at most $(n-1)/2$ blocks, the blocks meeting exceptional vertices total at most $n^2/(2D)$.

Starting with $U_0=W$, maintain nested sets $|U_i|\ge d_i n$ and $i$ distinct selected colors. Each selected color spans at most $D\eta n^2$ blocks inside $U_i$. For $i<t$, delete from the count inside $U_i$ all blocks of selected colors and all blocks meeting exceptional vertices. At least
```math
 \big(a(d_i)-tD\eta-1/(2D)\big)n^2\ge a(d_i)n^2/2
```
blocks remain. Some unused color $c$ accounts for at least $a(d_i)n^2/(2t)$ of them. By summing incidences there is a nonexceptional vertex $p\in U_i$ on at least $3a(d_i)n/(2t)$ of these blocks. Take $U_{i+1}$ to be the color-$c$ neighbors of $p$ **via triples entirely in $U_i$**. Linearity gives two distinct neighbors per block, so $|U_{i+1}|\ge d_{i+1}n$. Each internal $c$-block now gives a different monochromatic sail with center $p$, all seven of whose vertices lie in $W$. Thus the number of these blocks is at most $D\eta n^2$. Earlier colors retain their bounds by nesting. At $i=t$ the total number of blocks in $U_t$ is at most $tD\eta n^2<A n^2$, a contradiction. We may take $c(t,\delta)=\eta$.

This is a deterministic consequence of lower bounds for induced block counts and applies also to linear triple systems with the same bounds. The argument counts sails by their unique center and transversal.

## Uniform random hosts

Fix $u>0$. Run the random triangle removal process starting from $K_n$, for $m=\lfloor\beta n(n-1)/6\rfloor$ steps, with $\beta=u^2/100$. Fix a set $U$ of exactly $\lceil un\rceil$ vertices. At any of the first $m$ steps at most $3m$ pairs have been deleted, each spoiling at most $|U|-2$ originally available triangles of $U$. Therefore at least
```math
 \binom{|U|}{3}-3m(|U|-2)\ge u^3 n^3/10
```
triangles remain there for sufficiently large $n$. The process cannot stop early. Since the whole graph has at most $\binom n3$ triangles, the conditional chance of selecting a triangle in $U$ is at least $u^3/3$ at each step. The count stochastically dominates a binomial random variable with parameters $m,u^3/3$, by successive uniform random thresholds. Its mean is at least $u^5n^2/2100$ for large $n$. A Chernoff bound gives failure probability $\exp(-\Omega_u(n^2))$ for the bound $a(u)n^2$. The union bound over at most $2^n$ choices of $U$ has the same exponential order. Larger sets inherit the bound.

Apply Kwan's Theorem 2.4 with initial fraction $\beta$, the event above as its property, and the entire space of ordered partial systems as the conditioning event. The exponential tail is stronger than the required $\exp(-n^{2-b})$ for any fixed $b>0$ and large enough $n$. The theorem transfers the bound to the first $m$ blocks of a uniformly random ordered Steiner triple system with probability tending to one. Including the other blocks preserves it, and forgetting the order gives the claimed uniform labeled model. Only finitely many $u=d_0,\ldots,d_t$ are required for fixed $t,\delta$, so the deterministic argument applies with high probability. [Kwan, Theorem 2.4](https://arxiv.org/abs/1611.02246).

The macroscopic block-density condition can fail on particular Steiner systems with a linear-sized independent set. The ordinary multicolor problem for all systems is still open.
