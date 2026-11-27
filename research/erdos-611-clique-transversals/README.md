# Bollobás–Erdős–Tuza maximal-independent-set conjecture

**Open.** The construction below shows that even with all maximal independent sets of size at least $cn$, their transversal number can be $(1-\sqrt c)\sqrt n+O(1)$ or larger. This improves the order of the lower-bound construction located in the literature audit, but it does not refute a sublinear upper bound.

## Target

The first part of [Erdős Problem 611](https://www.erdosproblems.com/611) asks whether a graph with $n$ vertices whose maximal cliques all have size at least $cn$ has a set of $o(n)$ vertices meeting all maximal cliques. Pass to the complement. Equivalently, if every maximal independent set of a graph $G$ has at least $cn$ vertices, is $\tau(G)=o(n)$? Here $\tau(G)$ is the minimum size of a set that meets every **inclusion-maximal** independent set. This is [Cooper–Hollars Conjecture 1.1](https://arxiv.org/html/2607.15486v1#S1), attributed there to Bollobás, Erdős and Tuza. It is not the related maximum-independent-set conjecture, nor the second part of #611.

## Construction and exact counts

Fix integers $m,r,L$ with $1\leq r<m$ and $L\geq1$. Take $r$ disjoint cliques $H_1,\ldots,H_r$ of size $m$, each with labels $1,\ldots,m$ once each. Add an independent set $I$ partitioned into label classes $I_1,\ldots,I_m$, each of size $L$. Each vertex of label $a$ in any $H_j$ is adjacent to every vertex of $I_a$ and to no other vertex in $I$. There are no edges between different $H_j$. The total number of vertices is $n=m(r+L)$.

**Minimum maximal independent-set size.** Let $J$ be any maximal independent set, let $b$ be its number of clique vertices, and let $a$ be the number of distinct labels among these vertices. Each clique contributes at most one, so $a\leq b\leq r$. The independent part of $J$ consists of every vertex from every unused label class, and none from any selected label class: any omitted nonneighbor of the selected clique vertices could be added to $J$. Therefore
```math
|J|=b+(m-a)L\ge b+(m-b)L\ge r+(m-r)L.
```
Equality occurs by taking one vertex from each clique with all $r$ labels distinct, then all unused label classes of $I$. The clique choices dominate all clique vertices and each excluded vertex of $I$ has a selected neighbor. Thus $i(G)=r+(m-r)L$.

**Upper bound on the transversal number.** Select one vertex from each of $r+1$ distinct label classes in $I$. Every maximal independent set blocks at most $r$ labels and contains all vertices of the other labels, so this selection hits every maximal independent set.

**Matching lower bound on the transversal number.** Let $T$ be any set of size at most $r$. Write $t$ for the number of its clique vertices and let $D$ be the set of labels represented by $T\cap I$. We have $|D|\le r-t$. For every $a\in D$, its clique vertex is outside $T$ in at least $r-t$ different cliques. Assign different cliques to these labels, choosing greedily: the number of eligible cliques for each label is at least the number of labels to assign. Select the label-$a$ vertex in its assigned clique. In each unassigned clique take any vertex outside $T$, which is possible since $m>r$. The selected clique vertices form an independent set $S$ disjoint from $T$. Adjoin every vertex of $I$ with unused label. This is a maximal independent set: all cliques contain a selected vertex and the only excluded vertices of $I$ are adjacent to selected vertices. It avoids $T\cap I$ because all labels in $D$ were used, and it avoids $T$ on the clique side by construction. Thus
```math
\tau(G)=r+1.
```

## Consequence at fixed $c$

Take $0<c<1$, choose $L=\lceil\sqrt c\,m\rceil$ and $r=m-L$ for sufficiently large $m$. Now $n=m^2$ and
```math
i(G)=r+L^2\ge cn,\qquad \tau(G)=m-L+1\ge (1-\sqrt c)\sqrt n.
```
For arbitrary sufficiently large $n$, let $m=\lfloor\sqrt n\rfloor$ and use $L=\lceil\sqrt{cn}\rceil$, $r=m-L>0$, then add $n-m^2$ additional twins to any label classes of $I$. Every class is still nonempty; the same transversal proof works unchanged. The minimum maximal independent-set size has not decreased: the bound $b+(m-a)L$ still holds. As before this is at least $r+L^2\ge cn$. Hence there is a deterministic example on every sufficiently large $n$ with $\tau(G)\ge (1-\sqrt c)\sqrt n-O(1)$.

## Recursive extension

[Graph substitution gives a near-linear lower bound](RECURSIVE.md) for every fixed $c<1$ and every sufficiently large order. In particular, no fixed power saving $O_c(n^{1-\epsilon})$ is possible. The original sublinear question remains open.

## Source and limits

- [Erdős, Gallai and Tuza, *Covering the cliques of a graph with vertices* (1992), Problem 2](https://doi.org/10.1016/0012-365X(92)90681-5) is a primary source for the clique-transversal question.
- [Cooper and Hollars, *Hitting all maximal independent sets in c-hollow graphs* (2026), Theorem 1.7](https://arxiv.org/html/2607.15486v1#S1) prove the lower bound $\Omega_c(n^{1/3}/\log n)$ by a random construction with a join of multiple disjoint-clique cores. The labeled clique construction above needs neither joins of multiple cores nor random edges.
- On 26 November 2026, searches covered the exact Erdős problem, the original article, the current preprint and its indexed title/citations, and formulations using both large maximal cliques and c-hollow maximal independent sets. No prior unrestricted resolution or explicit square-root construction was located in the sources reviewed. This is a bounded priority search.
- The argument gives no linear lower bound: within this exact family $m>r$ and $n\geq mr$ imply $\tau(G)<\sqrt n+1$. A new construction or an upper bound for general graphs is needed.
