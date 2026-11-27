# Near-linear transversals in hollow graphs

For every fixed $0<c<1$, for every sufficiently large $n$ there is a graph $G$ on $n$ vertices such that every maximal independent set has at least $cn$ vertices and
```math
\tau(G)\ge n\exp\bigl(-O_c(\sqrt{\log n\log\log n})\bigr).
```
In particular the Bollobás–Erdős–Tuza conjecture, if true, cannot hold for all these graphs with any uniform upper bound of order $n^{1-\epsilon}$, for any fixed $\epsilon>0$. The stated lower bound is still $o(n)$ and is **not a disproof** of [Erdős Problem 611](https://www.erdosproblems.com/611).

## Independent sets and transversals under graph substitution

To substitute nonempty graphs $F_v$ into a base graph $B$, take a copy of $F_v$ for each $v\in V(B)$ and make the join between two copies exactly when their base vertices are adjacent. The support of a maximal independent set (the base vertices of the copies it meets) is a maximal independent set of $B$. Its choices inside each supported copy are maximal independent sets of that copy. Conversely, every such combination is a maximal independent set of the substituted graph. Indeed, a missing base vertex nonadjacent to the support would allow adding a vertex from its copy; and the possibility of adding a vertex to a supported copy is determined only by the selection in that copy.

For a set $T$ of vertices in the substituted graph, mark each base vertex $v$ such that $T\cap F_v$ hits every maximal independent set of $F_v$. Then $T$ hits every maximal independent set in the substituted graph if and only if its marked base vertices hit every maximal independent set in $B$. For the converse, if an independent support avoids every marked vertex, choose separately in each supported copy a maximal set missing $T$. Thus if $\tau(F_v)=D$ for every base vertex, the new transversal number is exactly $D\tau(B)$.

## One recursive step

Let $F$ have $L$ vertices, minimum maximal independent-set size $i$ and transversal number $D$. For integers $1\le r<m$, take the base graph of [the labeled-clique construction](README.md) with the following parameters: $r$ cliques, each with $m$ labels, and one independent vertex per label. Its transversal number is $r+1$, and every maximal independent set contains at least $m-r$ of the independent vertices.

Replace each independent label vertex by a copy of $F$. Replace each clique vertex by a complete multipartite graph on $2D$ vertices with $D$ parts of size two. Its maximal independent sets are exactly its $D$ parts, so its transversal number is $D$. Thus both varieties of copy have transversal number $D$. The new graph has parameters
```math
L'=m(L+2rD),\qquad D'=(r+1)D,\qquad i'\ge(m-r)i.
```
In particular for $\rho=D/L$ and $\gamma=i/L$,
```math
\rho'=\frac{r+1}{m(1+2r\rho)}\rho,
\qquad
\gamma'\ge\frac{1-r/m}{1+2r\rho}\gamma.
```

## Iteration at fixed hollowness

Fix $0<c<1$, put $\eta=(1-c)/8$, and use $a_t=\eta/(t+1)^2$ for $t\ge1$. Start with an independent graph on $L_0\ge 2/a_1$ vertices. Its transversal number is one and its minimum maximal independent-set size is $L_0$, so $\rho_0=1/L_0$ and $\gamma_0=1$. At step $t$ put
```math
r_t=\left\lfloor a_t/\rho_{t-1}\right\rfloor,
\qquad m_t=\left\lceil r_t/a_t\right\rceil.
```
The steps are well-defined with $a_t/\rho_{t-1}\ge2$, as we now check. Assuming this inequality, $r_t\ge1$ and $r_t<m_t$. Since $m_t\ge r_t/a_t$, $r_t+1\le2r_t$ and $1+2r_t\rho_{t-1}\ge1$, one obtains $\rho_t\le2a_t\rho_{t-1}$. Also $a_{t+1}/a_t=((t+1)/(t+2))^2\ge4/9>2a_t$, so $a_{t+1}/\rho_t\ge a_t/\rho_{t-1}\ge2$. This proves the induction, starting at $t=1$.

We have $r_t/m_t\le a_t$ and $r_t\rho_{t-1}\le a_t$, and consequently
```math
\gamma_t\ge\gamma_{t-1}\frac{1-a_t}{1+2a_t}\ge (1-3a_t)\gamma_{t-1}.
```
All factors are positive. The product bound $\prod_{j=1}^t(1-3a_j)\ge1-3\sum_{j=1}^t a_j$ follows by induction. The sum of $1/(j+1)^2$ for $j\ge1$ is less than one, for instance by comparison to the telescoping $1/(j(j+1))$. Hence $\gamma_t\ge1-3\eta>c$ for every $t$.

It remains to estimate $\rho_t$. Since $a_t/\rho_{t-1}\ge2$, flooring retains at least half, and rounding $r_t/a_t$ upwards adds at most one. Thus
```math
\frac{1}{2\rho_{t-1}}\le m_t\le\frac{2}{\rho_{t-1}},
\qquad
\frac{a_t}{4}\rho_{t-1}\le \rho_t\le 2a_t\rho_{t-1}.
```
For the lower ratio bound, use $m_t\le2r_t/a_t$ and $1+2r_t\rho_{t-1}\le2$. Taking logarithms yields
```math
\log(1/\rho_t)=2\sum_{j=1}^t\log(j+1)+O_c(t)=\Theta_c(t\log(t+1)).
```
The exact order recurrence gives $\log L_t-\log L_{t-1}=\log(1/\rho_{t-1})+O(1)$ because $1\le1+2r_t\rho_{t-1}\le2$. Summing,
```math
\log L_t=\Theta_c(t^2\log(t+1)).
```
In particular $\log(1/\rho_t)=O_c(\sqrt{\log L_t\log\log L_t})$. Since $D_t=\rho_tL_t$, this proves the claimed bound along the orders $n=L_t$.

## Every sufficiently large order

Write $\gamma_* = 1-3\eta>c$ and fix an integer $K$ large enough that $\gamma_* K/(K+1)\ge c$. Given large $n$, choose the greatest $t$ such that $L_t\le n/K$ and put $k=\lfloor n/L_t\rfloor\ge K$. Replace every vertex of the step-$t$ graph by an independent set of $k$ or $k+1$ twins, assigning the larger size to exactly $n-kL_t$ vertices. Each fiber has transversal number one, so the substitution lemma leaves the transversal number exactly $D_t$. The minimum size of a maximal independent set is at least $k i_t\ge k\gamma_* L_t\ge cn$ because $n\lt(k+1)L_t$.

Maximality of $t$ gives $n\lt K L_{t+1}$, and the order bounds give $L_{t+1}\le4L_t/\rho_t$. Consequently the new relative transversal number is greater than $\rho_t^2/(4K)$. Since $\log L_t\le\log n$, this still gives $\tau\ge n\exp(-O_c(\sqrt{\log n\log\log n}))$.

Taking, for example, $c=1/2$ gives the same asymptotic lower bound for the maximum of $\beta(G)=i(G)\tau(G)/n$ in [Cooper–Hollars Question 7.1](https://arxiv.org/html/2607.15486v1#S7.SS1). Together with $\beta(G)\le n$, this determines the power exponent of that extremum, but not its asymptotic order.

## Scope and remaining gap

The use of multipartite substitutes with large transversal numbers differs from iterating one fixed graph on all vertices. Large independent sets in this construction are guaranteed by the numerous surviving copies of the previous graph, not by the multipartite copies, which can be very small as independent sets. The first-level construction and the recursive theorem are independent of random edges or least-size assumptions in the substituted cliques.

We still lose a multiplicative factor in $\rho_t$ at every step. This bound leaves the original $o(n)$ question open. The related conjecture for maximum independent sets only is not asserted here; these transversals must hit all maximal independent sets.
