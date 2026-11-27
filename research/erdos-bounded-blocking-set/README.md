# Erdős’s bounded blocking-set problem

Erdős asked whether there is an absolute constant $C$ such that every finite projective plane has a set $B$ with $1\le |B\cap L|\le C$ for every line $L$. The unrestricted problem remains open. The result below supplies a bound for all translation planes of bounded dimension over a kernel field of bounded characteristic, uniformly in the choice of spread and the field extension degree. [Erdős Problems 1159](https://www.erdosproblems.com/1159) · [Tracking issue #803](https://github.com/1337isnot1337/solved-conjectures/issues/803).

## Theorem

Let $K=\mathbb F_{p^d}$ and let $V=K^{2e}$. A spread is a family of $e$-dimensional $K$-subspaces of $V$ partitioning its nonzero vectors. Its affine plane has point set $V$ and lines all cosets of spread members. Adjoining one point at infinity per direction and a line containing these points gives its projective completion. This is the vector-space construction of translation planes over a subfield of their kernel. [André/Bruck–Bose representation](https://www.sciencedirect.com/science/article/pii/S1071579715000507).

**Theorem.** For every such spread with $d\ge e+1$, its projective plane has a blocking set meeting each line in at most

```math
 1+p^e\frac{p^{e+1}-1}{p-1}
```

points. For fixed $p,e$ the secant bound is uniform for all $d$. Indeed, when $d\le e$ the order is at most $p^{e^2}$, for which the points of a line meet all lines with largest intersection at most $p^{e^2}+1$.

## A graph with small intersections in every direction

Choose two spread members as complementary coordinate axes and identify them separately with $K^e$. Every direction other than the vertical one is the graph of a $K$-linear map $A:K^e\to K^e$. Put $F(x_1,\ldots,x_e)=(x_1^p,\ldots,x_e^p)$, and let $W\subset V$ be its graph. It has dimension $ed$ over $\mathbb F_p$.

For any $A$, the solution space of $F(x)=Ax$ has dimension at most $e$ over $\mathbb F_p$. Choose a maximal $K$-independent list of solutions $v_1,\ldots,v_s$. Every solution has the form $\sum_i a_i v_i$. Applying $F$ and $A$ to this expression gives $\sum_i(a_i^p-a_i)F(v_i)=0$. The vectors $F(v_i)$ are $K$-independent because coordinate Frobenius is semilinear and invertible. Thus every $a_i$ belongs to $\mathbb F_p$. This establishes the bound, including for singular $A$.

Consequently $\dim_{\mathbb F_p}(W\cap U)\le e$ for every spread member $U$. For the vertical direction the intersection is zero. For every direction the projection of $W$ into $V/U$ has codimension equal to $\dim_{\mathbb F_p}(W\cap U)$, since $W$ and $V/U$ both have dimension $ed$ over $\mathbb F_p$.

## Making every affine line meet the set

More generally, suppose $W\subset V$ has dimension $ed$ over $\mathbb F_p$ and its intersection with every direction has dimension at most $s$, where $s<d$. Choose an $(s+1)$-dimensional $\mathbb F_p$-subspace $D\subset K$ and one nonzero scalar from each of its one-dimensional $\mathbb F_p$-subspaces. Call the representative set $R$, so that $|R|=(p^{s+1}-1)/(p-1)$. Take the affine point set

```math
 B_0=\bigcup_{c\in R}c^{-1}W.
```

For a line $z+U$, let $H$ be the image of $W$ in $V/U$. The map

```math
 D\longrightarrow(V/U)/H,\qquad c\longmapsto (cz+U)+H
```

is $\mathbb F_p$-linear and its target has dimension at most $s$. Its kernel contains a nonzero scalar and hence also its representative $c\in R$. Thus $cz+U$ contains an element of $W$. Since $cU=U$, the original line meets $c^{-1}W$.

A coset of $U$ meets each $c^{-1}W$ in at most $p^s$ points: a nonempty intersection is a coset of $U\cap c^{-1}W=c^{-1}(U\cap W)$. Every affine line therefore has between one and $|R|p^s$ points of $B_0$. Add one point at infinity. The line at infinity meets the resulting set just there and each affine line gains at most one point. Taking $s=e$ for the Frobenius graph proves the theorem.

## Scope and earlier work

Erdős, Silverman and Stein gave a logarithmic upper bound for arbitrary projective planes. Constructions of Bruen–Fisher and Boros give absolute bounds for Desarguesian planes of fixed characteristic. Ughi and later authors considered unions of conics, and Asgarli, Ghioca and Yip establish obstructions to unions of bounded-degree curves in large characteristic. The proof above uses no multiplication on the set of slopes and applies to every spread in the specified vector space. Neither the extension degree $d$ nor the plane order $p^{de}$ appears in the displayed bound. Growing characteristic, unbounded spread dimension and general nontranslation planes remain outside this result. [Erdős’s 1981 problems, p. 35](https://users.renyi.hu/~p_erdos/1981-16.pdf) · [Asgarli–Ghioca–Yip, introduction and references](https://arxiv.org/abs/2510.15332) · [Green, remark after Problem 68](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf).

An existing Hall-plane construction of a small minimal blocking set permits secants growing with the plane order. A translation hyperoval would yield a particularly good initial graph intersection bound in characteristic two. Some translation planes have no translation hyperoval. The proof above starts with the weaker dimension bound $e$ and does not assume the existence of an oval. I found no previous general spread statement with these quantifiers in the sources consulted. Global priority and independent review remain unverified. [Blocking and Double Blocking Sets in Finite Planes](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v23i2p5) · [*On Translation Hyperovals in Semifield Planes*](https://arxiv.org/abs/2309.01451).

## A non-Desarguesian check

The [exact verifier](check_spread.py) takes $K=\mathbb F_8$ and represents $K^2$ by $E=\mathbb F_{64}$. For slopes $a\in E$ with $a^9=1$ it uses $x\mapsto ax^8$, and otherwise $x\mapsto ax$. These maps are $K$-linear. A collision of two different slopes with the same twist at $x\ne0$ is impossible. A collision between opposite twists would give $a/b=x^7$ or its inverse, hence $(a/b)^9=1$, so the two slopes would have the same relative norm and twist. Together with the vertical direction the graphs form a spread.

The verifier checks a failure of Pappus’s theorem on six explicit points, certifying that the plane is non-Desarguesian since every finite division ring is a field. It also enumerates all 4,161 projective lines. The 443-point blocking set has smallest intersection one and largest intersection 22. Run `python3 research/erdos-bounded-blocking-set/check_spread.py` from the repository root.
