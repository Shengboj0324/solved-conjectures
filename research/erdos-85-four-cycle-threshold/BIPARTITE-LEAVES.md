The extension tex_math_single_backslash is not supported for gfm
# Erdős’s four-cycle threshold conjecture

## No bipartite leave component when the degree is divisible by four

Let $G$ be a simple $q$-regular $C_4$-free graph on $q^2$ vertices. Its leave graph $M$ joins pairs with no common neighbor in $G$. As proved in [the structural note](README.md), $M$ is $(q-1)$-regular, its component orders are $qu_i$ with $\sum_i u_i=q$, and every vertex of $G$ has exactly $u_i$ neighbors in component $i$. Its adjacency matrix $B$ commutes with the adjacency matrix $A$ of $G$, with $A^2=J+(q-1)I-B$.

**Theorem.** If $4\mid q$, every component of $M$ is nonbipartite. More generally, if $q$ is even and $M$ has a bipartite component, then $M$ has exactly two components, both bipartite, and both $u_1,u_2$ are odd. In this case a necessary condition is $qu_1\equiv2\pmod8$.

To prove this, suppose $q$ is even and $M$ has $g>0$ bipartite components. Let $s_i$ be the vector supported on bipartite component $i$, equal to $1$ on one part and $-1$ on the other. Each part has the same order by regularity, so all $s_i$ have coordinate sum zero. For a connected positive-degree regular graph, its adjacency eigenvalue minus its degree occurs exactly when the graph is bipartite, in which case that eigenspace is spanned by the bipartition sign vector. Hence these vectors form a basis of the $-(q-1)$ eigenspace of $B$.

Because $A$ commutes with $B$, write $A s_j=\sum_i c_{ij}s_i$ with an integer matrix $C=(c_{ij})$. The entries in column $j$ are congruent to $u_j$ modulo 2: at any vertex, $A s_j$ sums $u_j$ signs. At vertices in nonbipartite components $A s_j$ is zero, so the presence of such a component would force every bipartite $u_j$ even. On the sign subspace the matrix identity gives
\[
C^2=2(q-1)I_g.
\]

Modulo 2, the image of $C$ equals its kernel. One inclusion follows from $C^2=0$ modulo 2. Conversely, if $Cx=0$ modulo 2, lift $x$ to an integer vector and put $y=Cx/2$. Then $Cy=(q-1)x$, so $Cy=x$ modulo 2. Therefore the rank of $C$ modulo 2 is $g/2$. But every column is constant modulo 2, so this rank is at most 1. As $g>0$, we get $g=2$ and an odd bipartite $u_j$, excluding all nonbipartite components. The two values $u_1,u_2$ sum to even $q$, so both are odd.

Now write $C=\begin{pmatrix}a&b\\c&d\end{pmatrix}$, all entries odd. Since the off-diagonal entry of $C^2$ vanishes and $b\ne0$, we have $d=-a$. Self-adjointness of $A$ on the two orthogonal sign vectors gives $u_1 b=u_2 c$. With $h=\gcd(u_1,u_2)$, write $b=(u_2/h)t$, $c=(u_1/h)t$ for an odd integer $t$. Odd squares are 1 modulo 8, so
\[
2(q-1)=a^2+bc\equiv1+u_1u_2\equiv qu_1\pmod 8.
\]
If $q\equiv0\pmod4$, the left side is 6 modulo 8 and the right side divisible by 4, a contradiction. In the only remaining even case $q\equiv2\pmod4$, the left side is 2 modulo 8, giving the stated necessary condition.

This excludes a connected bipartite leave and, for every degree divisible by four, all bipartite components, including when mixed with nonbipartite ones. It does not exclude connected nonbipartite leaves or settle A-REG. [Tracking issue #835](https://github.com/1337isnot1337/solved-conjectures/issues/835).
