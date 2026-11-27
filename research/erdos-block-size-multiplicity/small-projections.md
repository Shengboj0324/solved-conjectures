# Recovering a finite subfield from small projections

Let $F$ be any field. A coordinate projection has undirected slope $t$ when its fibers are lines of slope $t$, so for finite $t$ its values are $y-tx$. The following inverse lemma uses no bound on the size, characteristic or transcendence degree of $F$.

**Lemma.** Suppose $L\ge1$, $0<\delta\le1$, $A,B\subset F$ have at most $L$ elements each, and $E\subseteq A\times B$ has at least $\delta L^2$ points. Suppose also that a set $D\subset F$ of at least $\delta L$ slopes contains $0,1$ and that each projection $U_t=\{y-tx:(x,y)\in E\}$, $t\in D$, has size at most $L$. For $L$ sufficiently large in terms of $\delta$, there exist a finite subfield $H\subset F$, a nonzero $\lambda\in F$ and an affine translate of $\lambda H\times\lambda H$ containing $\gg_\delta L^2$ points of $E$. Moreover $\delta L\le |H|\ll_\delta L$. All losses and the threshold for $L$ are polynomial in $1/\delta$.

The near-extremal incidence mechanism is related to the subfield obstruction in Bourgain, Katz and Tao. Their remark after the proof of Theorem 6.2 describes the expected projective geometry. We prove the particular projection statement needed here, with uniformity in the ambient field. [Bourgain, Katz and Tao, §§4 and 6](https://arxiv.org/abs/math/0301343).

## Simultaneous control of all slopes

Regard $E$ as a bipartite graph on $A,B$. For the following sampling argument one may pad both classes with isolated vertices to integer size $L$, or first replace $L$ by its ceiling and $\delta$ by $\delta/4$. Discard vertices of $A$ with degree less than $\delta L/2$. At least $\delta L^2/2$ edges survive. Call an ordered pair of remaining left vertices bad if they have fewer than $\eta L$ common neighbors, where $\eta=\delta^4/4096$. Let $Z$ be the neighborhood of a uniform right vertex, and let $J$ count ordered bad pairs in $Z$. Then $\mathbb E|Z|\ge\delta L/2$ and $\mathbb EJ\le\eta L^2$. Choose an outcome with $|Z|-\delta J/(4\eta L)\ge\delta L/4$. This gives $|Z|\ge\delta L/4$ and $J\le(16\eta/\delta^2)|Z|^2\le\delta |Z|^2/256$.

Remove from $Z$ the vertices with more than $\delta |Z|/32$ bad partners in $Z$, leaving $X$ with $|X|\ge7|Z|/8$. Let $Y$ consist of right vertices with at least $\delta |X|/4$ neighbors in $X$. The retained graph on $X\times Y$ has at least $\delta L|X|/4$ edges, by the original degree cutoff. In particular $|X|,|Y|\gg_\delta L$. For every $x\in X,y\in Y$, there are at least $\delta |Z|/8$ neighbors $x'$ of $y$ in $X$ forming a good pair with $x$. Each supplies at least $\eta L$ choices of a common neighbor $y'$ of $x,x'$. This gives $\gg_\delta L^2$ three-edge walks from $x$ to $y$.

Fix a nonzero $t\in D$. Each such walk represents $y-tx$ as

```math
 (y'-tx)-(y'-tx')+(y-tx').
```

For fixed endpoints the first and third terms recover $y'$ and $x'$. Each value of $Y-tX$ therefore has $\gg_\delta L^2$ distinct representations in $U_t^3$, and $|Y-tX|\ll_\delta L$. Using this also at slope $1$, Ruzsa's triangle inequality gives

```math
 |X-tX|\le |X-Y|\,|Y-tX|/|Y|\ll_\delta |X|.
```

The bound holds at $t=0$ directly. Write $m=|X|$.

## From scalars to a field

For $B_0\ge1$, call a scalar $B_0$-good if $|X-tX|\le B_0 m$. If $m\ge2B_0$, there are at most $1+2B_0m$ such scalars. For each nonzero good $t$, Cauchy–Schwarz gives at least $m^3/B_0$ quadruples satisfying $x_1-tx_2=x_3-tx_4$. Exactly $m^2$ have $x_2=x_4$. Each of the remaining quadruples determines its scalar, and there are at most $m^4$ quadruples altogether.

A rational expression of **fixed** length in elements of $D$, with nonzero denominators, is $O_\delta(1)$-good with polynomial dependence on $1/\delta$. To see this, put $K=|X-X|/m\ll_\delta1$. The Plünnecke–Ruzsa inequality gives $|iX-jX|\le K^{i+j}m$ for nonnegative integers $i,j$ with $i+j>0$. For a $B_0$-good scalar $t$, Ruzsa covering applied to $tX-X$ puts $tX\subseteq T_t+(X-X)$, $|T_t|\le B_0$. For good $s,t$, the sets $(s\pm t)X$ lie in $T_s\pm T_t+2(X-X)$. Also $stX\subseteq sT_t+T_s-T_s+2(X-X)$. Subtracting from $X$ and applying the sumset bound controls the new constants polynomially. For $t\ne0$, inversion preserves $|X-tX|$ by scaling. This proves the assertion by induction. [Bourgain–Katz–Tao, §2](https://arxiv.org/abs/math/0301343) · [Petridis, Plünnecke–Ruzsa estimates](https://arxiv.org/abs/1101.3507).

Let $H=(D-D)/(D-D)$ with zero denominators excluded. Every member is uniformly good and hence $|H|\ll_\delta m$. As $0,1\in D$, we have $D\subseteq H$. If $r,s\in H$ and $z=r+s$, $r-s$ or $rs$, every element of $D-zD$ is a fixed-length expression in $D$, so $|D-zD|\ll_\delta m$. For sufficiently large $L$, this is less than $|D|^2$. A collision $d-ze=d'-ze'$ necessarily has $e\ne e'$ and gives $z\in H$. Inverses of nonzero members already belong to $H$ by reversing their quotients. Thus $H$ is a finite subfield, with the asserted size bounds.

## Recovering points in a single subplane

Every $t\in H^\times$ is $C_\delta$-good. Partition ordered unequal pairs of elements of $X$ according to the one-dimensional $H$-subspace $V=(x-x')H$ of $F$. Write $r_V$ for their counts. The same energy count, now summed over $t\in H^\times$, gives

```math
 \sum_V r_V^2\ge (|H|-1)(m^3/C_\delta-m^2)\gg_\delta m^4.
```

Indeed, two nonzero differences belong to the same $V$ precisely when their ratio belongs to $H^\times$. Since $\sum_V r_V=m(m-1)$, some $V=\lambda H$ has $r_V\gg_\delta m^2$. Within this direction, ordered pairs are counted inside the affine cosets of $V$. Some such coset therefore contains a set $X_0\subseteq X$ of at least $c_\delta m$ points.

For representatives $x$ of different cosets of $V$ meeting $X$, the sets $x-X_0$ are disjoint subsets of $X-X$, of size $|X_0|$ each. Hence $X$ meets only $O_\delta(1)$ cosets. The same argument with $Y-X$ proves the same bound for $Y$. Their product is covered by $O_\delta(1)$ translates of $\lambda H\times\lambda H$. Since $X\times Y$ retained $\gg_\delta L^2$ actual edges of $E$, one translate contains the required points. Every constant and largeness requirement used a fixed number of products, sums and powers of polynomial bounds in $1/\delta$.
