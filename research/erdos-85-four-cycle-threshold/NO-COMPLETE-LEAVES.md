# Erdős’s four-cycle threshold conjecture

**The complete-component case is impossible, without a completion theorem.** Suppose a simple $q$-regular $C_4$-free graph $G$ on $q^2$ vertices exists, with $q\ge2$ even. Form its leave $M$ by joining distinct vertices with no common neighbor in $G$. Then every component of $M$ has order at least $2q$. In particular, the earlier reduction about many complete components is strictly superseded.

## Component balance

Let $A$ be the adjacency matrix of $G$, $B$ that of $M$, and $J$ the all-ones matrix. The common-neighbor counts give
$$
A^2=J+(q-1)I-B.
$$
In particular $M$ is $(q-1)$-regular. If $C$ is a component of $M$, the vector $1_C-(|C|/q^2)\mathbf 1$ is in the null space of $A^2$. Symmetry of $A$ puts it in the null space of $A$. Hence every vertex of $G$ has exactly $u=|C|/q$ neighbors in $C$. This makes $u$ a positive integer.

## Neighborhood parity

For any $v\in C$, $G[N_G(v)]$ is a matching with isolated vertices: a path of length two inside this neighborhood would close to a four-cycle through $v$. Every neighbor $x\notin C$ of $v$ has a common neighbor with $v$, because vertices of different leave components are not adjacent in $M$. Thus every such $x$ is matched inside $N_G(v)$.

If $|C|=q$, then $u=1$ and $M[C]=K_q$. There is exactly one vertex $w$ of $C$ in $N_G(v)$. It has no common neighbor with $v$ because $M[C]$ is complete, so it is isolated in $G[N_G(v)]$. The remaining $q-1$ vertices must all be matched among themselves. This contradicts that $q-1$ is odd. Thus no component has order $q$, and $|C|\ge2q$. For odd $q$, existence of $G$ already fails the handshaking parity on $q^2$ vertices.

## A constraint for larger components

The same reasoning gives more than the exclusion at $u=1$. Let $P_C$ be the graph with vertex set $C$ whose edges are exactly those edges of $G[C]$ that lie in a triangle having its third vertex outside $C$. For each $v\in C$, the outside-neighbor vertices in $N_G(v)$ number $q-u$. All are matched. The ones matched to inside-neighbor vertices are counted exactly by $d_{P_C}(v)$, since in a $C_4$-free graph each edge has at most one triangle. The remaining outside-neighbor vertices are paired off, so
$$
d_{P_C}(v)\equiv u\pmod 2.
$$
For odd $u$, every vertex of $P_C$ has positive odd degree. In particular, each vertex of $C$ has a neighbor in $G[C]$ to which it is nonadjacent in $M[C]$, and $G[C]$ has at least $|C|/2$ edges lying in a triangle with its third vertex outside $C$. For $u=2$, the graph $G[C]$ is 2-regular and $P_C$ is a union of whole cycles of $G[C]$: a nonempty proper subset of edges in a cycle has a vertex of degree one.

## Scope

This applies to the A-REG candidates in [Walters et al., *A Drop at Forty-Nine in Erdős Problem 85*](https://aixiv.online/abs/2610.02192) and gives at most $\lfloor q/2\rfloor$ leave components, none complete. For $4\mid q$ the earlier bipartite-component obstruction still applies independently. Neither argument rules out a connected nonbipartite leave. This is not a resolution of Erdős #85, nor an exclusion of the known regular graph at $q=4$.
