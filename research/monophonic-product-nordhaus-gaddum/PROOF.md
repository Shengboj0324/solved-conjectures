# Chandran–Di Stefano–Haritha–Thomas–Tuite monophonic product conjecture

Let $\chi_{\mathrm{mp},i}(G)$ be the minimum number of colors in a partition of $V(G)$ into independent sets such that no induced path contains three vertices of any one set. The monophonic product assertion of [Chandran S.V., Di Stefano, Haritha S., Thomas and Tuite, Conjecture 9.3](https://arxiv.org/html/2408.13494v2#S9) is
```math
\chi_{\mathrm{mp},i}(G)\chi_{\mathrm{mp},i}(\overline G)\le
\left(\frac{|V(G)|+1}{2}\right)^2.
```

**Theorem.** For every integer $s\ge3$, there is a graph $H_s$ on $15s$ vertices with
```math
\chi_{\mathrm{mp},i}(H_s)=\left\lceil\frac{13s}{2}\right\rceil,
\qquad \chi_{\mathrm{mp},i}(\overline{H_s})=9s.
```
These graphs disprove the product assertion. The first member has 45 vertices and product $20\cdot27=540>529$.

## A subdivision lemma

Let $F$ be a finite simple 3-connected graph of order at least six. Let $H$ be obtained by subdividing each edge of $F$ once. Write $A=V(F)$ for the original vertices, and $b_e$ for the subdivision vertex of $e\in E(F)$.

**Lemma.** A set of three vertices of $H$ lies on no common induced path if and only if it consists of three subdivision vertices whose edges of $F$ share a common endpoint. In particular, every independent monophonic set of size at least three is contained in $\{b_e:e\ni v\}$ for one $v\in V(F)$.

First, any cycle of $H$ is induced, since each included subdivision vertex uses its two incident edges in that cycle. Its length is at least six. If three marked vertices are on such a cycle, delete the interior of an arc between two consecutive marks that has at least one interior vertex. The remaining arc is an induced path through all three. Conversely, if three marked subdivision vertices share an original neighbor, an induced path through them would have one of them internal. It would then contain their common neighbor, which has three neighbors on the path, impossible.

Now take three marked vertices on no common cycle. The graph $H$ is 2-connected. Its only two-vertex cuts are endpoints $u,v$ of an edge of $F$, with one component $\{b_{uv}\}$ and one component consisting of every other surviving vertex. To see this, deleting two original vertices leaves the connected subdivision of $F-\{u,v\}$ plus attached subdividers or the single isolated $b_{uv}$. Deleting one original vertex and one subdivision vertex removes at most one edge from the 2-connected graph $F-u$, which retains connectivity. Deleting two subdivision vertices leaves connectivity by 3-edge-connectivity of $F$.

Apply the [Watkins–Mesner three-vertex cycle theorem](https://yu.math.gatech.edu/Papers/hajos6.pdf), Theorem (2.2). Its first obstruction requires three components from one two-vertex cut and is impossible here. Each of the other two obstructions assigns the marked vertices to pairwise disjoint unions of components of their respective two-vertex cuts, with either the three cuts sharing one endpoint and having distinct remaining endpoints, or with the three cuts pairwise disjoint. In either case the three isolated subdivision vertices of these cuts are distinct. If any selected component union includes the large component, the other two unions must each fit among the two removed original vertices and that cut’s isolated subdivision vertex. Neither other union can contain a large component (of size $|V(H)|-3>3$); their distinct isolated vertices are not in this three-element remainder. Thus each union is just its cut’s isolated vertex. The shared-endpoint obstruction gives precisely the star triples already handled. The disjoint-cuts obstruction says that deleting the three marked subdivision vertices leaves exactly two components, each containing one endpoint of each of their original edges.

It remains to account for that three-edge cut of $F$. Write its edges $e_i=u_iv_i$ for $i=1,2,3$, with distinct $u_i$ in one component $U$ of $F-\{e_1,e_2,e_3\}$ and distinct $v_i$ in the other $W$. There is a path from $u_1$ to $u_3$ inside $U-u_2$: otherwise the component of $u_1$ in $U-u_2$ would be cut off in $F-\{u_2,v_1\}$, contradicting 3-connectivity. Likewise there is a path from $v_3$ to $v_2$ inside $W-v_1$. Concatenate, in $H$, the stub $b_{e_1}u_1$, the first subdivided path, the subdivided edge $e_3$, the second subdivided path, and the stub $v_2 b_{e_2}$. Every internal subdivision vertex has both its neighbors on that path consecutively. The two endpoint stubs cannot cause a chord, because their other endpoints $v_1,u_2$ were avoided. Thus this is an induced path through all three marks. This proves the triple lemma. For the set statement, three distinct edges incident with a common vertex have pairwise distinct other endpoints. A fourth member could form a valid triple with either of the first two subdivision vertices only by also using their common endpoint; an original vertex cannot be such a member.

## Counting colors in the cubic case

Suppose $F$ is 3-connected and cubic on $k$ vertices. Let $T$ be the set of centers used by color classes of size at least three in an independent monophonic coloring of $H$. There are at least $|T|$ such colors. All $k$ original vertices and all subdividers of edges in $F[V(F)\setminus T]$ must be assigned to color classes of size at most two. Consequently, writing $e_F(S)$ for the number of edges internal to $S$,
```math
\begin{aligned}
\chi_{\mathrm{mp},i}(H)
&\ge |T|+\frac{k+e_F(V(F)\setminus T)}2\\
&=\frac{5k}{4}-\frac{|T|-e_F(T)}2\\
&\ge\frac{5k}{4}-\frac{\alpha(F)}2.
\end{aligned}
```
For the equality on the second line use $e(F)=3k/2$ and cubicity. On the third line, deleting at most one endpoint per edge in $F[T]$ leaves an independent set of size at least $|T|-e_F(T)$.

## The counterexample family and exact color counts

Take the prism $C_s\square K_2$ for $s\ge3$. Replace each vertex by a triangle with one port for each of its three incident edges, then connect the corresponding ports for every original edge. The resulting simple graph $F_s$ is cubic on $k=6s$ vertices. The prism remains connected after deleting any two edges: if two edges of the same cycle are deleted, the other cycle and all rungs connect everything; otherwise each cycle loses at most one edge and at least one rung survives. Deleting at most two vertices of $F_s$ leaves each triangle nonempty and connected and deletes at most two intertriangle edges. The prism argument therefore proves 3-connectivity of $F_s$.

At most one vertex per triangle belongs to an independent set. Equality $\alpha(F_s)=k/3$ also holds: choose the port pointing along a forward cycle edge at each vertex of the prism, using the same cyclic orientation on each ring. No pair of chosen ports points along the same edge in opposite directions. For the subdivision graph $H_s$ the lower bound is now $\lceil13k/12\rceil$.

For the matching upper bound, use one color for the three subdivision vertices incident at each of the $k/3$ selected ports. These are disjoint valid color classes by independence of the selected ports and the subdivision lemma. There remain $3k/2-3(k/3)=k/2$ subdivision vertices and $k$ original vertices. Pair the original vertices within their independent part, and pair the remaining subdivision vertices within theirs, allowing a singleton. The total number of colors is $k/3+k/2+\lceil k/4\rceil=\lceil13k/12\rceil$.

The $3k/2$ subdivision vertices form a clique in $\overline{H_s}$. To get a coloring with exactly that many colors, orient the internal edges of each triangle of $F_s$ cyclically and pair every original vertex with the subdivision vertex of its outgoing triangle edge. The pairs are disjoint and independent in the complement, and any pair is monophonic. All other subdivision vertices get singleton classes. This proves the exact counts.

For $s=3$ the product exceeds the conjectured value by 11. For every $s\ge4$, the difference is at least
```math
9s(13s/2)-\frac{(15s+1)^2}{4}
=\frac{9s^2-30s-1}{4}>0.
```
This is the complete disproof of the specified monophonic product bound. It does not decide either general-position inequality or claim a smallest counterexample among all graphs.
