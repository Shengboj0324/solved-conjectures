# Erdős’s four-cycle threshold conjecture

The eventual monotonicity question [Erdős #85](https://www.erdosproblems.com/85) remains open. This note imposes restrictions on the regular graphs used in the conditional route of [Walters et al., *A Drop at Forty-Nine in Erdős Problem 85*](https://zenodo.org/records/23519149). In their notation, proving A-REG for infinitely many powers-of-two degrees would suffice for a negative answer using their order-adjacent comparison. Their already reported finite drop is not a resolution.

**Current results.** A [neighborhood parity argument](NO-COMPLETE-LEAVES.md) excludes even one complete leave component, superseding the earlier net argument below; a [modulo-8 obstruction](BIPARTITE-LEAVES.md) excludes bipartite leave components when four divides q. A separate [affine incidence argument](POLARITY-EDIT-LOWER-BOUND.md) shows that any regular candidate needs more than q^(3/2)/100 deletions from the natural orthogonal polarity truncations. (See [the exact path checker](check_affine_paths.py).) [Further restrictions](CAYLEY-OBSTRUCTIONS.md) cover some symmetric graph classes. None excludes arbitrary connected nonbipartite leaves or settles #85.

## The leave graph

Assume a simple $q$-regular graph $G$ on $q^2$ vertices has no four-cycle. Define $M$ on the same vertex set by joining two distinct vertices if they have no common neighbor in $G$. Distinct vertices have at most one common neighbor in $G$. For the adjacency matrices $A$ of $G$ and $B$ of $M$,
```math
A^2=J+(q-1)I-B,
```
where $J$ is the all-ones matrix. Thus $M$ is $(q-1)$-regular and $A$ commutes with $B$.

Let $C_1,\ldots,C_s$ be the connected components of $M$. The space of vectors that are constant on each component is the $(q-1)$-eigenspace of $B$. For any vector $x$ in that space with coordinate sum zero, $A^2x=0$ and hence $Ax=0$ by symmetry of $A$. Since $A\mathbf 1=q\mathbf 1$, it follows that $A\mathbf 1_{C_i}=(|C_i|/q)\mathbf 1$. Consequently:
- Every component has order a positive multiple of $q$.
- Every vertex of $G$ has exactly $|C_i|/q$ neighbors in $C_i$.
- $\dim\ker A=s-1$ over the reals. Indeed any vector in the kernel is orthogonal to $\mathbf 1$ and satisfies $Bx=(q-1)x$.

## Many complete components are impossible

Suppose $q$ is even. Let $p$ be the number of components of $M$ of order $q$; these components are all copies of $K_q$. Write $d=q+1-p$. If $p\ge3$ and $q>4d^4$, then $G$ cannot exist.

For each complete component $C$, the $q$ sets $N_G(v)$ for $v\in C$ are disjoint $q$-sets, so they partition the points $V(G)$. For distinct complete components, each two neighborhoods from different classes meet in one point. This gives a net with $q^2$ points, degree $p$ and deficiency $d$. The displayed inequality is stronger than the sufficient inequality in [Bruck’s completion theorem, Corollary to Theorem 4.3](https://msp.org/pjm/1963/13-2/pjm-v13-n2-p05-p.pdf), so it extends to an affine plane of order $q$.

Every other neighborhood $N_G(v)$ also meets each of the original net lines once, by the definition of the connected components of $M$. It is a transversal to all $p$ given parallel classes. We next check that it is a line of the completed plane. In any affine plane of order $q$, a $q$-point set not on one line, whose pairs use at most $d$ directions, has $q-1\le d(d-1)$. To see this, take a line with as many of its points as possible, say $b$, and a point in the set outside the line. That point determines $b$ distinct directions to the points on the line, so $b\le d$. Count all other points from any one point of the set, using at most $d$ directions and at most $b-1$ other points per direction. Here a transversal can only use the $d$ missing directions, and $q>4d^4$ contradicts the inequality. Therefore all $q^2$ distinct neighborhoods of $G$ are lines in the completed plane.

Exactly one affine line through any point is not among these neighborhoods, since each point belongs to exactly $q$ neighborhoods. The $q$ missing lines form a parallel class. Any two neighborhoods from the same retained parallel class are disjoint. Hence the vertices indexing that class form a $q$-clique in $M$ and therefore a connected component. Thus, in fact, all $q$ retained classes correspond to complete components. We now derive a contradiction from this conclusion without any numerical search.

Complete the affine plane to a projective plane. Define a point-line duality sending an affine point $v$ to the projective line extending $N_G(v)$. Send the infinity point for a retained class to the missing-class line consisting of all vertices indexing that class. This is a missing-class line because two vertices in that class have no common neighbor, so they are not joined by an original affine line; all $q$ points of the class therefore lie on the same missing line. Send the infinity point of the missing class to the line at infinity. This is a bijection from points to lines and the incidence relation is symmetric: among affine points this is symmetry of adjacency in $G$; between affine and infinity points it is precisely the retained class of the neighborhood; between infinity points only incidences with the missing-class infinity point hold, including its self-incidence. Hence this is a polarity with exactly one absolute point (a point on its polar line), the missing-class infinity point.

For even $q$, a polarity cannot have only one absolute point. On the polar line of any nonabsolute point $P$, the involution $Q\mapsto Q^\perp\cap P^\perp$ has a fixed point, since the line has odd size $q+1$. Its fixed points are precisely the absolute points on the line. The polar line of an absolute point already contains that point. Thus every line contains an absolute point. One point cannot be on every projective line when $q>1$. This is the contradiction.

In particular, any such $G$ for large even $q$ would need at least $\Omega(q^{1/4})$ of its size-$q$ units in noncomplete components. A connected leave graph is not ruled out.

## A spanning-tree divisibility test and a Galois constraint

Write $L_M=(q-1)I-B$ for the leave graph Laplacian. On the orthogonal complement of $\mathbf 1$, $A^2=L_M$. The square of the product of nonzero eigenvalues of $A$ therefore equals
```math
q^2\prod_{i=1}^s |C_i|\,t(C_i).
```
where $t(C_i)$ is the number of spanning trees of $C_i$, by the matrix-tree theorem. The product of the nonzero eigenvalues of an integer matrix is integral up to sign, as seen from the first nonzero coefficient of its characteristic polynomial. Thus $\prod_i |C_i|t(C_i)$ is a square integer. If $M$ is connected, $t(M)$ itself must be a square since $|V(M)|=q^2$.

There is a separate sign constraint. For a positive eigenvalue $\mu$ of $L_M$ that is not a square in $\mathbb Q(\mu)$, the two square roots $\sqrt{\mu}$ and $-\sqrt{\mu}$ are Galois conjugate over $\mathbb Q(\mu)$. Their multiplicities in the spectrum on $\mathbf 1^\perp$ agree, because the latter is represented by a rational matrix. The entire contribution from this $\mu$ to the trace of $A$ is zero. The all-ones eigenvalue contributes $q$ and the total trace is zero because $G$ has no loops. Therefore at least one positive leave-Laplacian eigenvalue must be a square in its own real number field and must have an imbalance of the two root multiplicities. A leave graph for which all positive eigenvalues fail that field-square condition is impossible regardless of connectivity.

## Source and scope

Exact searches on the Erdős problem, the conditional route, the distinction between projective polarities and their affine deletions, and component and leave-graph terms found no later full resolution in the sources reviewed as of 26 November 2026. The source's specific case $q=4$ demonstrates why the unrestricted regular nonexistence assertion requires care. This note proves only the stated restrictions for candidate regular graphs, not A-REG. [Tracking issue #835](https://github.com/1337isnot1337/solved-conjectures/issues/835).
