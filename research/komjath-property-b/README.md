# Komjáth's property B problem

Komjáth asked whether every almost-disjoint family of countably infinite sets with no singleton intersections admits a two-coloring in which every edge contains both colors. Erdős recorded the question in 1987. The ordinary question remains open here. The result below gives a ZFC obstruction to requiring even two occurrences of each color. [Problem 602 and original reference](https://www.erdosproblems.com/602) · [Tracker discussion](https://www.erdosproblems.com/forum/thread/602) · [Research issue #846](https://github.com/1337isnot1337/solved-conjectures/issues/846).

## Sharp obstruction to two points of each color

**Theorem.** There is a family on a countable ground set satisfying all Komjáth's intersection hypotheses and admitting an ordinary proper two-coloring, for which every two-coloring has a member containing at most one point of one of the colors.

Start with an almost-disjoint family $\mathcal U$ of countably infinite subsets of a countable set $X$ that has no proper two-coloring. Here is the classical diagonal construction. Take $X=2^{<\omega}$. Enumerate its two-colorings as $c_f$, $f\in2^\omega$. On the infinite branch consisting of the finite prefixes of $f$, choose an infinite monochromatic subset $U_f$ in coloring $c_f$. Different branches have only finitely many common prefixes, and each coloring has a monochromatic member. Put $\mathcal U=\{U_f:f\in2^\omega\}$. The existence of such an almost-disjoint family without the singleton restriction goes back to Miller. [Hajnal–Juhász–Shelah on almost-disjoint families](https://shelah.logic.at/files/95606/19.pdf).

For each $x\in X$ take a fresh pair $P_x$ and a private disjoint countable ground set $Y_x$ carrying a copy $\mathcal U_x$ of $\mathcal U$. Include the following two types of edges:
```math
 D_U=\bigcup_{x\in U}P_x\quad (U\in\mathcal U),
 \qquad E_{x,V}=P_x\cup V\quad (V\in\mathcal U_x).
```
The whole ground set is countable and every edge is countably infinite. Two distinct $D$ edges meet in $2|U\cap U'|$ points. A $D$ edge and an $E$ edge meet in zero or two points. Edges in different private groups are disjoint, and two distinct edges in the same group meet in $2+|V\cap V'|$ points. All these intersections are finite and none is one.

Any coloring that gives the two members of each $P_x$ opposite colors is proper. Now suppose each edge has at least two points of each color. If some $P_x$ is mixed, there is a monochromatic $V\in\mathcal U_x$ under the coloring restricted to $Y_x$. Its edge $E_{x,V}$ has exactly one point of the opposite color. Hence every $P_x$ must be monochromatic. Their colors induce a coloring of $X$. Some $U\in\mathcal U$ is monochromatic in this coloring, which makes $D_U$ monochromatic. Both possibilities contradict the assumption. Thus demanding two points of each color already fails without any additional set-theoretic hypothesis.

The usual conclusion under a uniform finite bound on every pairwise intersection is stronger: essential disjointness gives infinitely many occurrences of each color. The example shows why this strategy cannot extend intact when the finite pairwise sizes are unbounded. The 2026 tracker proof claim concerns finite hypergraphs. [Bounded-intersection theorem and attribution](https://www.renyi.hu/~soukup/setop/otka61600/conflict_free.pdf) · [Existing proof claim and its stated scope](https://www.erdosproblems.com/forum/thread/602/proof-claims).
