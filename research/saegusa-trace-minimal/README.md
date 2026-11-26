# Saegusa’s trace-minimal graph conjecture

**Disposition:** false by a consequence of prior triangle extremal results. The independent counting refinement below extends the explicit order-$3d$ counterexamples from even $d\ge18$ to even $d\ge14$. This is an attribution and scope note, not an original resolution entry in the catalogue. Coordination: [#815](https://github.com/1337isnot1337/solved-conjectures/issues/815).

## Exact statement and reduction

[Saegusa (2008)](https://doi.org/10.1016/j.disc.2007.08.097), as stated in [Romero–Petingi, Conjecture 23](https://arxiv.org/html/2610.36127#S3), proposes that $E_{n-k}\vee S(n+k,2k)$ is trace-minimal among the $n+k$-regular graphs on $2n$ vertices, whenever $2\le k\le n-1$. Here $E_m$ is empty, $S(a,b)$ is any trace-minimal $b$-regular graph of order $a$, and trace ordering is lexicographic in adjacency power traces.

Put $d=n-k-1$. The complement of the proposed join has $K_{d+1}$ as a component. For every $d$-regular $N$-vertex graph $H$,
$$
 \tau(H)+\tau(\overline H)=\binom N3-\frac{Nd(N-1-d)}2.
$$
Indeed, every triple with both colors of edges in the complement pair has exactly two vertices meeting both colors within the triple. The traces of the first two positive powers are fixed in the regular class, and the third trace is $6\tau$. Thus any $d$-regular graph having more triangles than every competitor with a $K_{d+1}$ component refutes Saegusa's assertion at the corresponding parameters.

[Chen–Gong–Lu–Tu–Yuan, Theorem 1.3](https://arxiv.org/html/2610.39461#S5) prove exactly that strict inequality at $N=3d$ for every even $d\ge18$. Take $n=3d/2$ and $k=d/2-1$. This consequence does not require knowing the residual trace-minimizer. It also uses no unproved assertion about which graph is triangle-maximal.

## Counting refinement below the earlier range

The following argument extends the specific order-$3d$ witness to $d=14,16$.

**Claim.** A $D$-regular graph $X$ of order $2D+3$ has at least $3D/2+3$ triangles for $D=12,14$.

Suppose otherwise. Choose a vertex $v$ in at most two triangles, because the average is at most $3(3D/2+2)/(2D+3)<3$. Put $A=N(v)$, $B=V(X)\setminus(A\cup\{v\})$, $H=X[B]$, and $\ell=e(X[A])\le2$. Each $a\in A$ has $3+d_{X[A]}(a)$ nonneighbors in $B$, and each $w\in B$ has $d_H(w)$ nonneighbors in $A$. Hence $e(H)=3D/2+\ell$. If $\Delta(H)<D/2$, each edge $xy$ of $H$ has at least $D-d_H(x)-d_H(y)\ge 2$ common neighbors in $A$, a contradiction. Choose $w$ of maximum degree $h\in[D/2,D]$, set $H_0=H-w$, $e=e(H_0)=3D/2+\ell-h$, and put $S=N_H(w)$, $\alpha=\sum_{z\in S}d_{H_0}(z)$.

Partition triangles as follows:

* Triangles through $v$, or with two vertices in $A$ and one in $B$, number at least $a_\ell=0,D-5,2D-12$ for $\ell=0,1,2$, respectively. An edge in $A$ has at least $D-4-d_{X[A]}(x)-d_{X[A]}(y)$ common neighbors in $B$; the total includes the $\ell$ triangles through $v$.
* Triangles with an edge $wz$ in $H$ and a third vertex in $A$ number at least
  $$
  \max\{0,\;h(D-h-1)-2e,\;(h-3)(D-h)-2\ell\}.
  $$
  In the second bound, sum $D-d_H(w)-d_H(z)$ over $z\in S$, using $\alpha\le2e$. For the third bound sum instead over $a\in N_X(w)\cap A$, a set of size $D-h$: at least $h-3-d_{X[A]}(a)$ of the $h$ vertices of $S$ are neighbors of $a$. The degrees inside $A$ sum to $2\ell$. This row-count bound is the crucial extra restriction.
* The remaining triangles with exactly one vertex in $A$ number at least $[De-\sum_z d_{H_0}(z)^2-\alpha]_+$, using codegrees on edges of $H_0$. The triangles entirely in $H$ number at least $[\alpha-e]_+$, as the edges of $H_0[S]$ make triangles with $w$. Together these two types number at least $[De-\sum_z d_{H_0}(z)^2-e]_+$.

For the squared degree sum use the bound
$$
 U(e,h)=\max_{1\le t\le\min(e,h)}
 \min\big(2et,\ e^2+e-2(e-t)(t-2)\big).
$$
At $t=\Delta(H_0)$ the first bound is immediate from the handshaking lemma. The second counts $e-t$ edges not incident to a maximum-degree vertex; each is disjoint from at least $t-2$ of its star edges. Distinct pairs of intersecting edges have exactly one shared endpoint, so subtract twice the disjoint count from $e^2+e$. Here $e>0$ throughout.

Using this $U$, add the three stated lower bounds. The resulting lower bounds, in increasing order $h=D/2,\ldots,D$, are:

| $D$ | $\ell$ | Bounds |
|---|---|---|
| 12 | 0 | 36, 45, 44, 27, 30, 29, 24 |
| 12 | 1 | 36, 43, 50, 37, 28, 29, 28 |
| 12 | 2 | 34, 41, 46, 43, 22, 25, 28 |
| 14 | 0 | 64, 69, 72, 55, 44, 45, 42, 35 |
| 14 | 1 | 62, 73, 76, 67, 42, 45, 44, 41 |
| 14 | 2 | 56, 69, 78, 75, 54, 41, 42, 43 |

All exceed $3D/2+2$, a contradiction.

Apply this claim with $D=d-2$ to the complement of the $d$-regular residual graph of order $2d-1$ after removing a $K_{d+1}$. Each such complement has at least $3d/2$ triangles. The identity above bounds the triangles in every $d$-regular graph of order $3d$ with a clique component by
$$
 \binom{d+1}3+\binom{2d-1}3-\frac{(2d-1)d(d-2)}2-\frac{3d}2=3\binom d3-1.
$$
By contrast, the graph formed by three $K_d$'s and a cross matching covering all vertices has $3\binom d3$ triangles. The matching is realized by splitting each clique into two halves, designating one for each other clique, and matching the corresponding halves. Taking complements produces the asserted counterexamples at $d=14,16$, in addition to the prior $d\ge18$ family.

## Literature provenance

- [Saegusa](https://www.sciencedirect.com/science/article/pii/S0012365X07006760) proves the adjacent $k=1$ case; [Romero–Petingi](https://arxiv.org/abs/2610.36127) explicitly state the broader conjecture.
- [Chen–Gong–Lu–Tu–Yuan](https://arxiv.org/abs/2610.39461) provide the order-$3d$ triangle comparison and the neighborhood decomposition for their even $d\ge18$ range. The transfer to trace-minimality and the small-degree refinement were checked separately.
- [Cambie–de Joannis de Verclos–Kang](https://doi.org/10.1002/jgt.22857), [Lo and He–Hou–Ma–Xie](https://arxiv.org/html/2309.02993v2#S1) supply strong related triangle lower bounds on odd orders. They also imply the required raw quadratic triangle gap at sufficiently large $d$, but their cited numerical thresholds do not give the $d=14,16$ comparison here.
- Nov 26 searches: proposer plus exact conjecture phrasing, exact restatement plus complement/triangles, reverse title/author pairs, and indexed MathDB, Hexagon, ProofAtlas, and repository issues/code returned no earlier explicit identification in Saegusa's terminology. This does not change the prior-work dependence of the general disproof.
