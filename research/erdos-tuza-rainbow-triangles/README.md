# Erdős–Tuza’s rainbow disjoint-triangles problem

Erdős and Tuza singled out the disjoint union of two triangles among the graphs for which the balanced rainbow question was open. The host is $K_{6d+1}$, with each of six colors occurring on exactly $d$ edges at each vertex. Necessarily $d$ is even. The question asks for two vertex-disjoint triangles whose six edges use all six colors. The all-cliques result claimed by Kitamura in September 2026 concerns a different family of target graphs. [Erdős–Tuza (1993), p. 81](https://doi.org/10.1016/S0167-5060(08)70377-7) · [Clemen–Wagner, introduction](https://arxiv.org/abs/2303.15476) · [Problem 811 discussion](https://www.erdosproblems.com/forum/thread/811) · [Issue 809](https://github.com/1337isnot1337/solved-conjectures/issues/809)

## Every partition of the palette into three classes occurs on a triangle

**Theorem.** Partition the six colors of any balanced coloring of $K_{6d+1}$, $d>0$, into three nonempty groups in any prescribed way. There is a triangle with one edge from each group. In particular, any two prescribed colors occur together on some rainbow triangle.

**Tool.** A complete graph colored without a tricolored triangle has a partition into at least two nonempty parts such that every pair of parts is joined monochromatically, and at most two colors occur between parts. This is Gallai’s decomposition. We apply it to the three colors obtained after merging each prescribed group. [Gyárfás–Simonyi, Theorem A](https://www.renyi.hu/~simonyi/galcol.pdf)

**Equal groups.** For group sizes $2,2,2$ all three degrees are $2d$. If there were a Gallai partition, each part would contain all neighbors of an omitted color for each of its vertices and have size at least $2d+1$. A vertex in any other part sees the entire part in a single color, which has degree $2d$. This is impossible.

**Groups of sizes $1,2,3$.** Call the colors of the merged graph small, medium and large, with respective degrees $d,2d,3d$. In any Gallai partition, each part has at least $d+1$ vertices, since at least one color is absent between parts. Hence the small color cannot appear between parts. Every part has size at most $3d$, since an outside vertex sees it in a single color. If a part had no medium neighbor among the parts, all its small and medium edges would be internal, forcing at least $3d+1$ vertices. It must have exactly one medium neighbor, since two parts each of size at least $d+1$ exceed the medium degree. Thus the parts pair off by medium edges. Every vertex sees all vertices outside its pair in the large color. Each pair therefore has size at least $(6d+1)-3d=3d+1$, so there is exactly one pair. In that case small and large neighbors are internal to each part, exceeding the maximum part size. This rules out a Gallai partition.

**Groups of sizes $1,1,4$.** Write $A,B$ for the two colors of degree $d$ and let $H$ be their union. Its components have at least $2d+1$ vertices. We show that every component has at most $3d$ vertices if no desired triangle exists. In a component on $h$ vertices, apply Gallai’s decomposition to the induced complete graph using $A,B$ and the remaining merged color $C$. At least one of $A,B$ occurs between parts, since $H$ is connected there. If either of $A,B$ were absent between parts, every part would have size at least $d+1$, preventing either color from occurring between parts. Thus both $A,B$ occur between parts and $C$ is absent there. Every part has size at most $d$, since an outside vertex sees it in $A$ or $B$. All $h-1-2d$ neighbors of each vertex in $C$ within this component are internal to its part. Hence $h-2d\le d$. Finally, $6d+1$ cannot be the sum of component sizes between $2d+1$ and $3d$. Two components have at most $6d$ vertices, and three have at least $6d+3$. This proves the theorem.

## Consequence for palette constructions

A *palette* is the three-element set of colors on a rainbow triangle. The palette family of a lexicographic product on a common color set is the union of the two input families. A triangle using two outer blocks repeats a cross-edge color. The other possibilities read a triangle in one of the factors. Thus a balanced base can be amplified into a counterexample by taking all its powers if its palette family is intersecting. Conversely, a pair of complementary palettes in one base can be realized in two different blocks of its square. This lexicographic criterion predates this investigation. [July 2026 report, Lemma E](https://www.erdosproblemaday.com/report/811)

An intersecting family of triples on six colors extends to one choosing a single triple from every complementary pair. There are $2^{10}$ such maximal families before relabeling. The theorem excludes any family that misses a prescribed three-group partition. A further obstruction excludes the star consisting of all triples containing one designated color. To see this, the total number of monochromatic two-edge paths is $6(6d+1)\binom d2$. Each nonrainbow triangle contains at least one of these, so the number of rainbow triangles is at least

```math
{6d+1\choose3}-6(6d+1){d\choose2}=(6d+1)(3d^2+2d).
```

At most $(6d+1)d(6d-1)/2$ triangles contain an edge of the designated color, strictly fewer. The subtraction counts each monochromatic triangle three times, which is valid for this lower bound.

The [exact enumeration](palettes.py) reduces the 1,024 maximal families to 13 isomorphism classes and then to **three** surviving classes. It uses permutations of six labels, set containment and integer arithmetic. The full problem remains open. In a single host two complementary palettes can be represented by intersecting physical triangles, so this classification controls lexicographic-power constructions in particular.

## Exactly balanced colorings with few rainbow Eulerian subgraphs

**Theorem.** Let $H$ be any fixed finite simple graph in which every vertex has even degree and $|E(H)|=2h$ for odd $h$. For every positive even $d$ there is a completely balanced $2h$-coloring of $K_n$, $n=2hd+1$, with at most

```math
3hd\,|E(H)|\,n^{|V(H)|-2}
```

labeled rainbow copies of $H$. In particular the rainbow density tends to zero for both the six-cycle and the union of two triangles in Erdős and Tuza's question. The construction allows positive counts, so existence in all sufficiently large hosts remains open for these targets. [Erdős–Tuza (1993), p. 81](https://doi.org/10.1016/S0167-5060(08)70377-7)

**Construction.** Put $m=hd$. Start with the complete bipartite cut between $A$ of size $m$ and $B$ of size $m+1$. Remove the edges of a matching saturating $A$ and add a perfect matching on the $m$ vertices of $B$ touched by that matching. The resulting graph $G$ and its complement in $K_n$ are both $m$-regular. Decompose each into $h$ spanning $d$-regular subgraphs, using separate colors for the two graphs. For completeness, any even-regular graph can be oriented along Euler tours of its components. Splitting each vertex into outgoing and incoming copies gives a regular bipartite graph. Hall's theorem supplies a perfect matching, and removing it repeatedly partitions this graph into perfect matchings. Each projects to a spanning 2-factor. Group $d/2$ such factors per color.

Exactly $3m/2$ edges differ between $G$ and the cut. Every rainbow embedding of $H$ uses exactly $h$ edges of $G$. The number of its cut-crossing edges is even by summing the degrees on one side modulo two. Thus its image contains at least one of the $3m/2$ exceptional edges. Choose that edge, its preimage among the $|E(H)|$ edges, an orientation, and images of the other $|V(H)|-2$ vertices. The displayed bound follows.

**Sharp cut discrepancy.** For every $m$-regular graph on $2m+1$ vertices, every cut has at least $3m/2$ edges in its symmetric difference with the graph. Indeed, let the smaller side have size $a=m-t$. The cut has $a(2m+1-a)$ edges, and at most $am$ can lie in the graph. The difference therefore has at least

```math
a(2m+1-a)+(2m+1)m/2-2am=3m/2+t(2m-1-t)\ge 3m/2
```

edges. The construction attains this bound for every even $m\ge2$. This establishes optimality of the cut approximation only. The [independent construction check](near_cut.py) produces all individual edge colors directly using cyclic differences and verifies every vertex degree and the exact discrepancy.

## Two palette classes suffice

The surviving class of color degrees $(4,4,4,4,6,8)$ is impossible. Relabel it as

```math
\mathcal F=\{012,013,014,015,023,024,035,045,125,134\}.
```

Suppose a finite completely balanced coloring had all its rainbow palettes in $\mathcal F$. Take independent infinite strings of its vertices with uniform digits. Color any two strings by the color of their first differing digits. Two sampled strings agree forever with probability zero. Conditional on one string, the color of its edge to an independent string is exactly uniform on the six colors, by the equal degree in each color at each digit. Each rainbow triangle is read in one digit where the three strings have pairwise distinct symbols. If just two symbols agree at the first split, two edge colors coincide. Thus its palette lies in $\mathcal F$.

For a colored triangle $T$ with distinguished vertex $r$ and a color $c$, let $W(T,r,c)$ be the integer in the [certificate](four-vertex-weights.json), extended by vertex permutations and by color permutations preserving $\mathcal F$, and set it to zero on all other orbits. The order of triangle edges in each record is $01,02,12$. For a coloring of four vertices define

```math
S=\sum_w\ \sum_{r\ne w}\ \sum_{c=0}^5
 W(T_w,r,c)\bigl(6\mathbf1_{\{\mathrm{color}(rw)=c\}}-1\bigr),
```

where $T_w$ is the triangle obtained by deleting $w$. Conditional on the strings in $T_w$, the independent string at $w$ gives a uniform edge color to $r$. Every summand consequently has expectation zero. On the other hand the [integer verifier](four_vertex.py) visits all $6^6$ labeled four-vertex colorings, discards any with a forbidden triangle, and gives $12\le S\le2878$ in every remaining case. This contradicts zero expectation and excludes every finite balanced base in this class. The weights were found by linear programming. Their verification uses only the standard library, exact integer sums, and all labeled patterns.

An intersecting palette construction can therefore occur only inside the classes of degrees $(4,4,4,6,6,6)$ and $(5,5,5,5,5,5)$.

## The palettes that must actually occur

**Theorem.** A balanced coloring whose rainbow palettes are pairwise intersecting realizes either nine or ten distinct palettes. Up to relabeling, its palette family is the design

```math
\mathcal D=\{012,013,024,035,045,125,134,145,234,235\},
```

the family obtained by replacing one triple of this design by its complement, or the family obtained by deleting one triple. In the nine-palette case the two maximal extensions determine each other uniquely once the nine palettes are specified.

To see this, join two surviving labeled maximal families when they differ in one complementary pair. The [enumeration](palettes.py) checks that the 12 copies of the design each have ten neighbors of the other type, and each of the 120 families of the other type has a unique neighbor, a design. The resulting graph is the disjoint union of twelve stars. The enumeration also checks that every pair of colors belongs to exactly two triples of each design. For an actual palette family missing both choices in $j$ complementary pairs, its maximal extensions form a $j$-dimensional cube. Each extension passes every necessary test above because it contains all the actual palettes. A star has no 4-cycle, so $j\le1$. With $j=1$ the two extensions are adjacent and their intersection is the actual family. With $j=0$ all ten palettes occur.

## Positive density under a symmetry of the colors

**Theorem.** Suppose a permutation of the vertices of a completely balanced six-coloring induces three disjoint transpositions on the colors. Then the number of rainbow copies of two vertex-disjoint triangles is $\Omega(n^6)$ as $n=6d+1$ grows, with an absolute implied constant. In particular the conclusion applies when a permutation cyclically shifts all six colors, by taking its cube. The same lower bound holds if the induced permutation exists only as a symmetry of the triangle-palette counts.

Merge the colors according to the transpositions. Each of the three merged colors has degree $k=2d$ at every vertex; $n=3k+1$. Write $M$ and $R$ for the monochromatic and rainbow triangle counts in this three-coloring. Counting the monochromatic two-edge paths at their middle vertex gives the identity

```math
R=\binom n3-3n\binom k2+2M=nk+2M.
```

Indeed a two-colored triangle contributes one such path and a monochromatic triangle contributes three. Every three-coloring of $K_{17}$ has a monochromatic triangle. Some vertex has at least six neighbors in one color, among which an edge in that color finishes a triangle. Otherwise apply $R(3,3)=6$ to the six neighbors. For $n\ge17$, averaging over the 17-subsets therefore gives

```math
M\ge\frac{\binom n3}{\binom{17}3},\qquad R\ge nk+\frac1{340}\binom n3.
```

Each of these $R$ triangles uses one of the eight palettes choosing one color per pair. The prescribed symmetry takes each such palette to its complement, so their counts come in four equal pairs $(a_j,a_j)$. There are $\sum_{j=1}^4 a_j^2\ge R^2/16$ unordered pairs of triangles of complementary palettes. At most $n\binom{n-1}{2}^2$ ordered pairs of triangles meet at a vertex. Removing these gives the claimed order of growth. This also gives a linear number of vertex-disjoint copies by greedy selection, since a fixed vertex belongs to $O(n^5)$ copies.

For a finite threshold, deleting any set of at most $d$ vertices leaves a triangle transversal to the three pairs. Indeed the remaining graph has at least $5d+1$ vertices and maximum monochromatic degree at most $2d$. A coloring without a tricolored triangle would have a monochromatic star with at least two fifths of its order. [Gyárfás–Simonyi, Theorem 3](https://www.renyi.hu/~simonyi/galcol.pdf)

Hence there are at least $\lfloor d/3\rfloor+1$ mutually disjoint transversal triangles. If $d\ge72$, at least four of them have the same palette. The image of one of those under the symmetry has the complementary palette and can meet at most three of the four. This proves existence already at $d=72$ and above under the vertex symmetry hypothesis. If the color-preserving automorphisms are transitive on vertices, the result holds at **every** admissible order: start with one transversal triangle and its complementary image. Apply a uniformly random color-preserving automorphism to the latter. Its expected overlap with the former is $9/n<1$, since $n\ge13$.

For example, over a finite field of order $q\equiv1\pmod {12}$, color a difference by its multiplicative coset of the sixth powers. The six colors are well-defined on unoriented edges because $-1$ is a sixth power. Translations preserve colors and are transitive; multiplication by a primitive element cycles the six colors. The conclusion applies at every such field order. It also applies to arbitrary six-colorings with the stated symmetry, without a field or group model. The unrestricted Erdős–Tuza question remains open.

## A square-root bound on vertex-disjoint rainbow copies

For every fixed Eulerian graph $H$ with $2h$ edges, $h$ odd, and every even $d\ge2$, there is a completely balanced $2h$-coloring of $K_{2hd+1}$ in which **every rainbow copy of $H$ meets one set of at most $\lceil(1+\sqrt{1+4hd})/2\rceil$ vertices**. Thus for the two triangles in the original problem, the maximum number of vertex-disjoint rainbow copies can be $O(\sqrt n)$. The earlier bound on the number of copies by itself allowed linearly many vertex-disjoint copies.

The underlying graph statement gives an exact minimum. For even $m\ge2$, among all $m$-regular graphs on $2m+1$ vertices the least number of vertices one can remove to leave a complete bipartite cut is

```math
 t(m)=\min\{s:s(s-1)\ge m\}
 =\left\lceil\frac{1+\sqrt{1+4m}}2\right\rceil.
```

Here a cut consists of all edges between its two classes and no edges inside them. To prove the lower bound, let $S$ be a deletion set of size $s$. If the remaining graph is empty, either nothing remains or any remaining vertex has all $m$ neighbors in $S$, so $s\ge m\ge t(m)$. Otherwise let the cut classes have sizes $a,b>0$. Both are at most $m$. Put $p=m-a$, $q=m-b$, so $p+q=s-1$. The count of edges surviving deletion gives

```math
ab=\frac{(2m+1)m}{2}-sm+e(S),\qquad e(S)=\frac m2+pq.
```

Since $e(S)\le\binom{s}{2}$, this forces $s\ge t(m)$.

For equality take disjoint sets $A,B,S$ of sizes $m,m-s+1,s$ with $s=t(m)$. On $S$ take any simple graph $J$ with precisely $m/2$ edges. Partition $A$ into sets $A_x$ of size $\deg_J(x)$ indexed by $x\in S$, possible because their sizes sum to $m$. Use all edges between $A$ and $B$, the edges of $J$, and every edge $ax$ between $a\in A$ and $x\in S$ except those with $a\in A_x$. Each $a$ sees $m-s+1$ vertices of $B$ and $s-1$ of $S$. Each $b\in B$ sees exactly $A$. Each $x\in S$ sees $m-\deg_J(x)$ vertices of $A$ and $\deg_J(x)$ of $S$. These are all degrees $m$, and deleting $S$ leaves the desired cut.

Now take $m=hd$ and split this graph and its complement into $h$ spanning $d$-regular color classes each by the 2-factor argument above. A rainbow copy of $H$ would use exactly $h$ edges of the first graph. If it avoided $S$, those would be exactly its edges crossing a cut. Every Eulerian graph crosses a cut an even number of times, a contradiction. For $H$ equal to the disjoint union of two triangles, take $h=3$.

The parameter $t(m)$ is also the smallest possible transversal number for triangles containing an **odd** number of graph edges, over these regular graphs. In a complete ambient graph with edges labeled inside/outside the graph, all triangles have even edge sum exactly when the graph is a cut: fix a vertex, label every other vertex by its edge to that vertex, and use the triangle equation to recover every edge as the sum of its endpoint labels modulo two. This applies after every vertex deletion. A maximal vertex-disjoint collection of odd triangles covers all odd triangles with its vertices. Thus every regular graph in the statement has at least $t(m)/3$ vertex-disjoint odd triangles and the construction has at most $t(m)$. This sharp order applies to the parity obstruction. The existence of even one rainbow pair in every large balanced host remains open. [Independent construction check](cut_deletion.py)
