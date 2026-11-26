# Erdős–Sárközy–Sós conjecture

## Weak Sidon sets suffice, but general capacity two does not lift by fixed tags

For $A\subset\mathbb Z$, write $Q(A)$ for the squared-gap sum over its distinct sumset sites divided by $|A+A|$. Call $A$ *weak Sidon* if sums of two **different** elements are unique. The conjecture for exact Sidon sets is equivalent to the same divergence assertion for weak Sidon sets. More precisely, any sequence of weak Sidon sets with bounded $Q(A)$ and sizes tending to infinity gives genuine Sidon sets of the same sizes and bounded $Q$.

### A bounded lifting principle

Let $B>2D\ge0$ be integers and choose tags $u_a\in[0,D]\cap\mathbb Z$. Put $A'=\{Ba+u_a:a\in A\}$. Different original sums cannot collide in the lift: their tagged sites lie in disjoint, ordered integer blocks $[Bs,Bs+2D]$. Pick one tagged site from every such block. The new gap is $B$ times the old gap plus an increment bounded in absolute value by $2D$. Minkowski's inequality, followed by normalization, shows that the squared-gap cost of the representatives has square root at most $B\sqrt{Q(A)}+2D$. The other tagged sums split gaps, which can only decrease the squared cost, or extend either edge by at most $2D$ once. Also $|A'+A'|\ge |A+A|$. Consequently
\[
 \sqrt{Q(A')}\le B\sqrt{Q(A)}+2D+\frac{2\sqrt2 D}{\sqrt{|A+A|}}.
\]
The lift preserves size and multiplies diameter by at most $B$, up to an additive $D$. In particular the constants may be chosen uniformly for a family.

### Turn every weak Sidon set into a genuine Sidon set

A fixed center $b$ belongs to at most one nontrivial triple $a<b<c$ with $a+c=2b$: otherwise two distinct off-diagonal pairs sum to $2b$. In increasing order, give $b$ a binary tag opposite the tag of $a$ if $b$ is such a center, and give it tag zero otherwise. The smaller endpoint already has its tag. In each triple the three tags are not all equal, so $u_a+u_c\ne 2u_b$. This is the only kind of nontrivial collision possible for a weak Sidon set. Thus $3a+u_a$ is genuinely Sidon. The 2025 [Sidon ideal paper, Theorem 1](https://math.colgate.edu/~integers/z91/z91.pdf) gives a two-part Sidon partition by layers of centers; the tag proof above is an alternative coloring and, crucially for the gap question, keeps **all** points rather than choosing one part.

One can also phrase the weak Sidon version using only off-diagonal sums, provided the actual endpoints $2\min A,2\max A$ are inserted before computing energy. In any gap of the restricted set with these endpoints, there is at most one interior diagonal $2a$: two distinct diagonals $2a<2b$ would have the off-diagonal sum $a+b$ strictly between. Restoring the diagonals can thus reduce the squared cost by at most a factor two. The normalization changes by a factor tending to one as the size grows. Omitting the endpoint cuts entirely is a different condition.

### A larger sufficient class

Make a 4-uniform hypergraph on $A$ whose edges are all four-element sets supporting an equality of two different off-diagonal sums. Suppose there is a vertex order in which at most $D$ such edges have any given vertex as their last vertex. Each all-distinct collision has one equality pairing (for ordered distinct $a<b<c<d$, only $a+d=b+c$ is possible). Assign tags in the specified order from $0,\ldots,D$. Each edge completed at a vertex excludes only one tag, because that variable has coefficient $1$ or $-1$. Encode the tags using base $2D+1$. All off-diagonal sums are now distinct: nontrivial equalities between off-diagonal pairs cannot share an endpoint, and different base sums cannot collide. Apply the binary lift to eliminate diagonals. Both operations preserve bounded whole-span $Q$ for fixed $D$. Bounded hypergraph degeneracy, or a bound $O(|X|)$ on the number of all-distinct collisions within every subset $X\subseteq A$, gives such an order by repeatedly deleting a minimum-degree vertex and reversing the deletion order.

### Why an arbitrary bound of two representations is not enough for this method

Take integer Sidon sets $X,Y$ of the same size $m$ and translate them so their minima are zero. For an integer $W>2\max Y$, let $A=\{Wx+y:x\in X,\ y\in Y\}$. Every sum determines the unordered pair of $X$ coordinates and the unordered pair of $Y$ coordinates. There are at most two matchings between the two pairs, so this is a genuine unordered-capacity-two family.

For any fixed finite tag alphabet of size $k$, view the tags as a coloring of the $m$ by $m$ array. Restrict to any $k+1$ rows. In each column some pair of these rows has the same tag; record one such pair and its tag. For $m>k\binom{k+1}{2}$ two columns record the same pair and tag. That monochromatic rectangle has equal opposite-corner sums. They stay equal under every common integer scaling and addition of the assigned tags, no matter how large the scale. Thus capacity two alone cannot imply the existence of a fixed-alphabet lift keeping every point. This is an obstruction to a method, not a bounded-$Q$ construction or a resolution of Erdős 153.
