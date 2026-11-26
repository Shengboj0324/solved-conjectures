# Erdős’s four-cycle threshold conjecture

This note gives restrictions on highly symmetric A-REG candidates, not a resolution. As in [Walters et al.](https://aixiv.online/abs/2610.02192), the relevant orders and degrees are $q^2$ and $q$ for powers of two $q$.

## Ordinary Cayley graphs

Let $K$ be a group of order $q^2$ and let $S=S^{-1}\subseteq K\setminus\{1\}$ have order $q$, using edges $x\sim xs$. In a $C_4$-free Cayley graph, every element $g\ne1$ has at most one ordered representation $g=st$ with $s,t\in S$: two representations give two common neighbors of $1,g$. Exactly $q(q-1)$ such products occur, so the set $D$ of nonidentity elements not represented has size $q-1$.

1. Every nontrivial involution is in $D$. Indeed, a representation $g=st$ of an involution gives the second representation $g=t^{-1}s^{-1}$, and equality of the two ordered pairs would give $g=1$. Thus $K$ has at most $q-1$ nonidentity involutions. Also $S$ contains no element of order four, because its square would be a represented nonidentity involution. In particular no group of exponent dividing four works: then all $q$ members of $S$ would have to be among at most $q-1$ involutions.
2. If distinct $s,t\in S$ commute, then $t=s^{-1}$, since otherwise $st=ts\ne1$ has two representations. Consequently $|S\cap U|\le2$ for any abelian subgroup $U$.
3. For any subgroup $U$ of index $j$, let $s_i$ be the counts of $S$ in its left cosets. The total number of ordered products in $U$ is $\sum_i s_i^2$: send $(s,t)$ to $(s^{-1},t)$ and note $st\in U$ if and only if both entries of the latter pair are in the same left coset. Exactly $q$ ordered products equal $1$, so
$$
\sum_i s_i^2-q\le q^2/j-1.
$$
This does not require $U$ to be normal. For index two it is the exact bound $(s_1-s_2)^2\le2(q-1)$.

If $U$ is abelian of index $2\le j\le \sqrt q/2$, the identity coset contributes at most two elements. The last display and Cauchy–Schwarz imply
$$
(q-2)^2/(j-1)-q\le q^2/j-1,
$$
or $q^2-4qj+4j\le (q-1)j(j-1)$. But for $q\ge16$, $4qj\le2q^{3/2}\le q^2/2$, while the right side is at most $q^2/4$. Thus such an abelian subgroup is impossible. Index one is excluded by item 2 alone for $q>2$.

## Abelian Cayley sum graphs

Let $K$ now be abelian of order $q^2$ and put $x\sim y$ exactly when $x+y\in S$, where $|S|=q$. For this to give a loopless $q$-regular graph, $S$ misses $2K$. Four-cycle-freeness says the nonzero ordered differences from $S$ are distinct. All nonzero involutions are again among the $q-1$ missing differences.

Write $j=[K:2K]=|K[2]|$. The leave graph has all the nonzero involutions as generators. Thus $j\le q$; if $j=q$, the leave consists exactly of the complete graphs on the cosets of $K[2]$, contradicting [the no-complete-component lemma](NO-COMPLETE-LEAVES.md). We obtain $j\le q/2$ because $j,q$ are powers of two. On the other hand, let $s_i$ be the counts in the $j-1$ nonidentity cosets of $2K$ (the last one is empty). Distinct differences inside $2K$ give
$$
\frac{q^2}{j-1}-q\le\sum_i s_i(s_i-1)\le q^2/j-|K[2]\cap 2K|.
$$
This implies $q^2/[j(j-1)]<q$, so $j>\sqrt q$. In particular, writing $q=2^k$, the abelian group must have more than $k/2$ and at most $k-1$ cyclic factors in its decomposition as a product of cyclic $2$-groups.

## Edge-transitive graphs

In any candidate each vertex is in a triangle: otherwise the $q$ neighbors and $q(q-1)$ endpoints of nonreturning two-step walks from that vertex are disjoint and all distinct, giving $q^2+1$ vertices with the root. In an edge-transitive graph this forces every edge into a triangle. Each lies in exactly one triangle by $C_4$-freeness, but the number of edges $q^3/2$ is not divisible by three for a power of two. Thus no candidate is edge-transitive. More generally, in a vertex-transitive candidate each vertex is in a constant number $t$ of triangles, divisible by three since $q^2t=3\,\#\{\text{triangles}\}$, and $1\le t\le q/2$. No general vertex-transitive or arbitrary-graph exclusion follows.

The terminology of deficient difference sets is standard. The statements here concern the required degree and order, not absence of all $C_4$-free Cayley graphs over these groups.
