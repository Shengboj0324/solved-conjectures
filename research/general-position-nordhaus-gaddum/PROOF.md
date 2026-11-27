# Chandran–Di Stefano–Haritha–Thomas–Tuite general-position conjecture

Let $\gamma(G)=\chi_{\mathrm{gp},i}(G)$ denote the least number of colors in a partition of $V(G)$ into independent sets such that no shortest path of $G$ contains three vertices of one class. We prove both independent general-position inequalities in [Conjecture 9.3](https://arxiv.org/html/2408.13494v2#S9):
$$
\gamma(G)+\gamma(\overline G)\le n+1,\qquad
\gamma(G)\gamma(\overline G)\le ((n+1)/2)^2.
$$
The argument proves the stronger one-sided mixed inequality
$$
\gamma(G)+\chi(\overline G)\le n+1
\tag{1}
$$
for every finite graph $G$.

## A matching that avoids a prescribed vertex

**Lemma.** If $L$ is vertex-critical of chromatic number $k$ and its complement is connected, then for every vertex $x$ the graph $L-x$ has a matching with $k-1$ edges.

For $k=1$ the assertion is trivial. Write $r=k-1\ge1$. Gallai's theorem for vertex-critical graphs with connected complements gives $|V(L)|\ge2k-1$. Consequently $H=L-x$ has order $2r+t$ for an integer $t\ge0$. Vertex-criticality also gives $\delta(L)\ge r$ and rules out nonadjacent vertices with identical neighborhoods: a coloring after deleting one of them could reuse the other's color.

Suppose the maximum matching of $H$ has size at most $r-1$. By the Tutte–Berge formula there is a set $A$ of size $s$ such that $H-A$ has at least $t+s+2$ odd components. Since there are only $2r+t-s$ remaining vertices, we have $s\le r-1$. Every component has at least $r-s$ vertices, because $\delta(H)\ge r-1$. Hence
$$
0\le (2r+t-s)-(t+s+2)(r-s)=(t+s)(1-r+s).
$$
If $s=r-1$, the lower bound on the number of odd components equals the entire remaining order. Thus every vertex of $H-A$ is a singleton component; its neighbors in $L$ can only belong to $A\cup\{x\}$, a set of size $r$. Minimum degree forces all these vertices to have that same neighborhood, contrary to vertex-criticality. Otherwise $s<r-1$ and the displayed inequality forces $t=s=0$. In that case $H$ has exactly two components of order $r$ each. Each is a clique since $\delta(H)\ge r-1$, and $x$ must neighbor every vertex of both cliques since $\delta(L)\ge r$. Now $\overline L$ is disconnected, another contradiction. This proves the lemma.

## Assembling the coloring in the original graph metric

First assume $G$ is connected. Choose a minimal vertex subset $W$ with $\chi(\overline G[W])=\chi(\overline G)$ and put $U=V(G)\setminus W$. Let $C_1,\dots,C_s$ be the vertex sets of the connected components of $G[W]$. Write $L_i=\overline G[C_i]$ and $k_i=\chi(L_i)$. The graphs $L_i$ are joined completely in $\overline G[W]$, so $\sum_i k_i=\chi(\overline G)$ and each $L_i$ is vertex-critical by minimality of $W$. Moreover each $\overline L_i=G[C_i]$ is connected.

For any choice of a root $x_i\in C_i$, the matching lemma permits a coloring of $C_i\setminus\{x_i\}$ with $|C_i|-k_i$ independent general-position classes in the **full** graph $G$: use each matched edge of $L_i-x_i$ as one two-vertex class and give the other vertices singleton classes. Use disjoint palettes for distinct $C_i$. It remains to color $U\cup\{x_1,\ldots,x_s\}$ with at most $|U|+1$ additional colors. If $U$ is empty, connectedness gives $s=1$ and we use a singleton root class.

Suppose $U\ne\varnothing$. Order $U=(u_1,\ldots,u_m)$ by starting anywhere and at each step choosing $u_{j+1}$ to minimize its distance in $G$ from $u_j$ among all still unused vertices of $U$. Ties can be broken arbitrarily. Each $C_i$ has a neighbor in $U$ since $G$ is connected. Let its anchor be the earliest such vertex of $U$, and choose $x_i$ adjacent to its anchor. For each $u_j$ make a class containing all roots anchored there, and also $u_{j-1}$ if $j\ge2$. Use a separate singleton for $u_m$. These classes cover the remaining vertices exactly once.

For any one anchor $u_j$, the anchored roots are mutually nonadjacent, because they come from distinct components of $G[W]$. Their pairwise distances in $G$ are exactly two by the common anchor. For $j\ge2$, let $u=u_{j-1}$, $a=u_j$ and $d=d_G(u,a)$. The vertex $u$ is nonadjacent to each root anchored at $a$, since otherwise its component would have an earlier anchor. Moreover for each such root $x$,
$$
 d\le d_G(u,x)\le d+1.
$$
The upper bound uses $a x$. If $d_G(u,x)=d-1$, there is a shortest path from $a$ to $u$ beginning with $a,x$. The first vertex $b$ of $U$ after $x$ on this path is closer to $u$ than $a$ is and neighbors the component of $x$: a path cannot pass directly from that component of $G[W]$ into another one. When the order chose $a$ after $u$, every vertex strictly closer to $u$ than $a$ had already appeared. Thus $b$ precedes $a$, contradicting the choice of anchor. This proves the distance bounds.

A class is now independent, and any triangle of distances containing $u$ and two distinct roots satisfies strict triangle inequalities: the root-to-root distance is two, the other two distances are at least two, and their difference is at most one. All triangles of three roots have every distance equal to two. Consequently the class is general position in $G$, not just in an induced subgraph. This finishes the coloring, using at most
$$
\sum_i (|C_i|-k_i)+|U|+1=n-\chi(\overline G)+1
$$
classes.

For disconnected $G$, color its components separately and reuse colors: any shortest path stays in one component. The chromatic number of the complement is the sum of the complementary chromatic numbers of the components, because the complementary components are joined completely. Thus, writing $d_i=|V(G_i)|-\chi(\overline{G_i})\ge0$, the maximum number of colors used on a component is at most $\max_i(d_i+1)\le1+\sum_i d_i$. This proves (1) for every nonempty graph; the empty graph is immediate.

## The two asserted inequalities

In a graph all of whose connected components have diameter at most three, every independent set is in general position: among three same-component vertices in an independent set, each pair has distance at least two, so no triangle equality is possible. Hence $\gamma$ equals $\chi$ on that graph. Of a complementary pair, at least one graph always has this property. Indeed if $G$ is disconnected then $\overline G$ has diameter at most two. If $G$ is connected of diameter at least four, no adjacent pair can dominate its vertex set, as a dominating edge would put every pair of vertices at distance at most three. Thus every adjacent pair of $G$ has a common nonneighbor, and again $\overline G$ has diameter at most two.

Apply (1) in the orientation in which the complementary member satisfies $\gamma=\chi$. This proves the sum, and the product follows from $4ab\le(a+b)^2$. Both inequalities are sharp, with the sum attained for complete and empty complementary pairs and the product at odd orders attained by the split graph consisting of a clique of size $(n-1)/2$ joined to an independent set of size $(n+1)/2$ (and its complement).

## Sources

- [Chandran–Di Stefano–Haritha–Thomas–Tuite, *Colouring Graphs in General Position*, Conjecture 9.3](https://arxiv.org/html/2408.13494v2#S9).
- [Stehlík, *Critical graphs with connected complements*](https://doi.org/10.1016/S0095-8956(03)00069-8), Corollary 2 for the Gallai lower bound.
- Tutte–Berge matching formula, used in the first lemma.
- [The previously separate monophonic product disproof](https://github.com/1337isnot1337/solved-conjectures/pull/848) uses induced paths instead, and does not contradict these assertions.
