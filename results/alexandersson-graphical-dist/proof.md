# Counterexamples to the graphical dist conjecture

**Theorem.** For every even $r\ge2$ there is a connected chordal graph of treewidth two and a vertex order such that its graphical dist polynomial has at least $r$ distinct nonreal zeros.

For an acyclic orientation, $e_w$ counts the earlier neighbors of $w$ whose edge points into $w$. Let $K$ be the number of distinct positive values of $e_w$. The polynomial in [Alexandersson’s conjecture](https://github.com/PerAlexandersson/RealRooted/issues/2641) is the sum of $t^K$ over acyclic orientations. We use its normalization $\mathbb E[t^K]$ under the uniform distribution on these orientations.

## An edge shared by triangles

Start with an edge $uv$. Attach vertices $h_1,\ldots,h_r$ adjacent to both ends and to none of each other. For each $i$, attach $m_i$ new vertices, each adjacent exactly to $u$ and $h_i$. Order $u$ first, then $v$, then all the new degree-two vertices, then all $h_i$. Outside the $h_i$ every earlier indegree is zero or one.

Constructing the graph by attaching a vertex to the two ends of an existing edge gives a uniform orientation rule. After choosing the direction of $uv$, each new vertex picks one of three positions relative to the directed edge on which it was attached. These give the three acyclic orientations of its new triangle compatible with that edge. They all extend an acyclic orientation of the old graph. Any directed cycle through the new vertex could be shortened along the old edge, or would be the forbidden directed triangle. Each old orientation has exactly three extensions, so the successive position choices are independent and uniform. The attachment order for this rule is a construction order for the graph and can differ from the vertex order used to compute $e_w$.

Conditional on $u\to v$, each $h_i$ comes after $u$ in the orientation of its triangle with probability $2/3$. Conditional on $v\to u$, the probability is $1/3$. Given the direction of $uv$, these events are independent over $i$. Write $B_i=1$ when $u\to h_i$. If $g_i\in\{0,1,2\}$ is the number of $u,v$ preceding $h_i$ in that triangle orientation, then

```math
e_{h_i}=g_i+X_i,\qquad
X_i\mid (u,v,h_i)\ \sim\ \begin{cases}
\mathrm{Bin}(m_i,2/3),& B_i=1,\\
\mathrm{Bin}(m_i,1/3),& B_i=0.
\end{cases}
```

This follows by placing the $m_i$ degree-two vertices in the three gaps belonging to the oriented edge $uh_i$. Exactly two gaps precede $h_i$ when $u\to h_i$, and one gap precedes $h_i$ otherwise.

## Counting distinct values above a threshold

Set $m_i=(r+i)m$ and $L=\lfloor(2r+1)m/3\rfloor$. For fixed $r$ and $m\to\infty$, with probability tending to one, $e_{h_i}>L$ holds exactly for the $i$ with $B_i=1$, and all these values above $L$ are distinct. Indeed the largest mean in the lower class is $2rm/3$ and the smallest in the upper class is $2(r+1)m/3$. Different upper-class means differ by at least $2m/3$. Each variance is $O_r(m)$ and $0\le g_i\le 2$, so Chebyshev’s inequality and a union bound prove the assertion.

Let $J_m$ count the distinct $e_{h_i}$ above $L$. Its probability polynomial and the polynomial of $r-J_m$ therefore both converge coefficientwise to

```math
P_r(t)=\frac{(1+2t)^r+(2+t)^r}{2\,3^r}.
```

Indeed the sum of the $B_i$ has binomial parameter $2/3$ or $1/3$ according to the direction of $uv$, with the two directions equally probable. The mixture is invariant under reflection about $r/2$.

For even $r$ the polynomial $P_r$ has $r$ simple nonreal zeros. The equation $(1+2t)/(2+t)=\zeta$ maps each of the $r$ distinct roots of $\zeta^r=-1$ to $t=(2\zeta-1)/(2-\zeta)$. The fractional linear map is real, invertible, and none of these $\zeta$ is real. For $r=2$ the polynomial is $(5+8t+5t^2)/18$.

## Supplying all lower values in the same graph

Attach $R$ copies of a star with $L$ edges by identifying **one leaf** of each copy with $u$. Put all other leaves before their respective centers, and all these additional vertices after the original graph. The centers have earlier indegree distributed as $\mathrm{Bin}(L,1/2)$ independently across stars and independently of the original orientations. Each star meets the rest at a single vertex, and every orientation of a tree is acyclic. The new leaves have earlier indegree zero and $e_u=0$ throughout.

For fixed $m$ and $L$, with probability tending to one as $R\to\infty$, every value from $1$ through $L$ occurs at some center. A union bound for the failure probability is $L(1-2^{-L})^R$. There are at most $r$ further distinct values. The polynomial of $L+r-K$ thus converges coefficientwise, for fixed $m$, to that of $r-J_m$. It is the reciprocal $t^{L+r}\mathbb E[t^{-K}]$ of the normalized graphical polynomial (allowing initial zero coefficients).

Choose disjoint disks about the $r$ simple zeros of $P_r$, each disjoint from the real axis. For all sufficiently large $m$, the polynomial of $r-J_m$ has a zero in every disk, by continuity of polynomial roots, or by Rouché’s theorem on their boundaries. Fix such an $m$. For all sufficiently large $R$ the polynomial of $L+r-K$ also has a zero in every disk, by the same boundary argument in fixed degree at most $L+r$. Reciprocation gives $r$ distinct nonreal roots of the original polynomial. The graph before attaching the stars is a 2-tree, having been built by adjoining vertices on edges. The pendant trees preserve chordality and treewidth two. This proves the theorem.

## An explicit 71-vertex counterexample

Take the same core with two vertices $h_1,h_2$ and 20 degree-two vertices attached on each of their edges to $u$. At $u$ attach a clique on ten vertices, one of them $u$. Add 18 more mutually nonadjacent vertices, each adjacent to the entire clique. The nine new clique vertices follow both $h_i$ in the order, and the 18 additional vertices come last. This connected chordal example has 71 vertices and 310 edges. The preceding asymptotic theorem gives the stronger treewidth bound using stars.

Here is an exact certificate that can be reproduced by counting sets of positive values. Write $Q(t)=\mathbb E[t^{12-K}]$. All earlier indegrees outside $h_1,h_2$ are at most ten. Conditional on the direction of $uv$ and the gap $g$ of a distinguished vertex, let $x$ mark the number of its 20 adjacent degree-two vertices pointing into it. Its count is $x^g(1+2x)^{20}$ when $u\to h$, and $x^g(2+x)^{20}$ when $h\to u$. To count the choices where none of those 20 vertices has earlier indegree one, replace the two expressions by $x^{g+20}$ and $x^g(1+x)^{20}$ respectively. In that restriction every degree-two vertex must precede $u$ in its triangle orientation. These four expressions determine the support of all positive earlier indegrees in the core, including the possible extra value one at $v$.

For a subset $S\subseteq\{1,\ldots,10\}$ the number of orientations of the attached graph for which all positive values lie in $S$ is

```math
(1+|S|)^{18}\prod_{j=1}^9(1+|S\cap\{1,\ldots,j\}|).
```

Indeed each successive clique vertex can be inserted in any gap of the oriented earlier clique. After the clique order is fixed, each of the 18 independent vertices also chooses a gap. Their choices are simultaneously acyclic, since the vertices in each gap can be placed consecutively in a total order. Inverting the displayed subset sums gives the number for each exact support. Combine it with the core support by set union. The normalized polynomial has denominator equal to the orientation count $2\cdot 3^{42}\cdot 10!\cdot 11^{18}$. The [integer and rational verifier](check.py) gives

```math
Q'(-7/10)^2-Q(-7/10)Q''(-7/10)<-1/40000.
```

For a real-rooted polynomial $Q$, the left-hand expression is nonnegative at every real argument. Away from roots this follows by logarithmic differentiation, and at the roots by continuity. Thus the graph’s graphical dist polynomial has a nonreal conjugate pair. The verifier independently checks the support formulas on four smaller ordered graphs by directing each edge both ways and testing acyclicity from the resulting arcs.
