# Mallik–Diwan–Kothari degree-count conjecture

In [Conjecture 8.9](https://arxiv.org/html/2404.06445v3#S8.SS1) of *Extremal minimal bipartite matching covered graphs*, Mallik, Diwan and Kothari conjecture that every minimal $k$-extendable bipartite graph with $n$ vertices and $m$ edges has at least $2(m-n+2k)/(2k-1)$ vertices of degree $k+1$. Here minimal means that deleting any edge destroys $k$-extendability.

**The conjecture is false for every integer $k\geq 3$.** In fact, there is a counterexample for every even order $n$ from $4k+4$ through $6k-2$.

## Construction

Fix integers $k\geq 3$ and $k+2\leq t\leq 2k-1$. Put $r=2k-t$. Use bipartition $A=H_A\sqcup L_A$, $B=H_B\sqcup L_B$, where each $H$ has $k$ vertices and each $L$ has $t$ vertices. The edge set consists of exactly:

- All edges between $H_A$ and $L_B$, and all edges between $L_A$ and $H_B$.
- A perfect matching between $L_A$ and $L_B$.
- A matching of exactly $r$ edges between $H_A$ and $H_B$.

The first item gives two connected complete bipartite blocks. The second joins the blocks, so the graph is connected. Every low vertex has degree $k+1$. Every high vertex has degree $t$ or $t+1$, hence at least $k+2$. The graph has $n=2(k+t)$ vertices, with $n\geq 2k+2$.

## Extendability

Use Plummer's bipartite criterion, [Theorem 8.3 in the source paper](https://arxiv.org/html/2404.06445v3#S8). A balanced bipartite graph of this order is $k$-extendable if every nonempty $S\subseteq A$ of size at most $|A|-k=t$ has at least $|S|+k$ neighbors.

If $S$ meets both $H_A$ and $L_A$, its neighborhood is all of $B$, which has size $k+t\geq k+|S|$. If $S$ lies in $L_A$, its neighborhood is $H_B$ together with its distinct matched partners in $L_B$, hence has size $k+|S|$.

If $S$ lies in $H_A$, it sees all $t$ vertices of $L_B$. Exactly $k-r=t-k$ vertices of $H_A$ are unmatched in the high-to-high matching. Among the vertices in $S$, at least $|S|-(t-k)$ therefore have distinct partners in $H_B$. Consequently
```math
|N(S)|\geq t+|S|-(t-k)=|S|+k.
```
The inequality is still valid if $|S|-(t-k)$ is negative. This completes the extendability check.

## Minimality

An edge incident with a low vertex cannot be removed: the resulting degree $k$ violates the necessary minimum degree $k+1$ for a $k$-extendable graph ([Corollary 8.2](https://arxiv.org/html/2404.06445v3#S8)). Every other edge is a member of the high-to-high matching. For $S=H_A$ the neighborhood is $L_B$ plus the $r$ matched high vertices, of size $t+r=2k=|S|+k$. Deleting a high-to-high edge removes one of these neighbors because its only neighbor in $S$ was the other endpoint. Thus the same set $S$ fails Plummer's criterion after deleting any such edge. It is an admissible test set since $|S|=k\leq t$.

## Direct matching proof

The same extension and minimality argument can be given without invoking the Hall criterion. Delete the endpoints of any matching of size $k$, with $x$ of the deleted vertices in $H_A$ and $y$ in $H_B$. Then $k-x$ vertices were deleted in $L_A$, and $k-y$ in $L_B$. In the block $H_A,L_B$, the remaining high count minus the remaining low count is $d=r-x-y$. The same difference holds in the block $H_B,L_A$.

If $d\geq 0$, at most $x+y$ edges of the high-to-high matching were lost, leaving at least $d$. Use $d$ of them. If $d\lt 0$, at most $2k-x-y$ of the low-to-low matching edges were lost, leaving at least $t-2k+x+y=-d$. Use $-d$ of them. In both cases the two complete bipartite blocks now have equal part sizes and can each be perfectly matched. Such matchings of size $k$ exist to begin with, since $t\geq k$ and the low-to-low edges form a matching.

If a high-to-high edge is deleted, take any $k$ edges of the low-to-low matching. To extend them would require matching at least $r$ high vertices on each side to other high vertices: only $t-k=k-r$ low vertices remain on either side. Only $r-1$ high-to-high edges are available, so no extension exists.

Finally, consider deleting an edge incident with a low vertex $u\in L_A$, with matched low partner $v\in L_B$. If the deleted edge is $uv$, match the $k$ vertices of $H_B$ to distinct vertices of $L_A\setminus\{u\}$. If the deleted edge instead joins $u$ to some $h\in H_B$, match the $k-1$ vertices of $H_B\setminus\{h\}$ to distinct vertices of $L_A\setminus\{u\}$, and match $v$ to any vertex of $H_A$. In either case this matching of size $k$ uses all the remaining neighbors of $u$ without covering $u$, so it cannot extend. The case of a low vertex in $L_B$ is symmetric.

## Counts

Let $\ell$ denote the number of degree-$k+1$ vertices. The exact counts are
```math
\ell=2t,\qquad n=2(k+t),\qquad m=2kt+t+r.
```
Subtracting the degree count from the proposed bound gives
```math
\frac{2(m-n+2k)}{2k-1}-\ell=\frac{2r}{2k-1}>0.
```
For $t=k+2$ this gap is $2(k-2)/(2k-1)$. The smallest member, with $k=3$ and $t=5$, has 16 vertices, 36 edges, and only 10 vertices of degree 4. The conjecture requires at least $52/5$.

This does not refute Conjecture 8.10: here $\ell-n/2=t-k\geq 2$. The examples also have $n\lt6k$, so they do not contradict [He’s theorem](https://arxiv.org/html/2611.29504v1#S3) for the separate eventual edge bound in Conjecture 8.11.
