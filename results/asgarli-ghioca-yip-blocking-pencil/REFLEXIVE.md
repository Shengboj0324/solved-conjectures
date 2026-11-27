# Arbitrary families in characteristic greater than their degrees

Asgarli, Ghioca and Yip's Theorem 1.3 proves that the minimum number of bounded-degree curves needed to block the plane tends to infinity in characteristic greater than the degree bound. Their Theorem 1.4 gives an upper bound of order $\log q$. The following quantitative use of Entin's geometric monodromy theorem yields the matching lower bound. [Asgarli–Ghioca–Yip, §§1 and 3](https://arxiv.org/abs/2510.15332v2) · [Entin, Theorem 2](https://arxiv.org/abs/1805.05454).

**Theorem.** Fix $d\ge2$. Let $C_1,\ldots,C_k$ be distinct geometrically irreducible plane curves defined over $\mathbb F_q$, of degrees $2\le e_i\le d$. Assume their reduced union satisfies the hypotheses of Entin's Theorem 2, as it does when $\operatorname{char}\mathbb F_q>d$. If $k\le\log q/(8d\log(2d))$, then for $q$ sufficiently large in terms of $d$, at least $q^2/(2(d!)^k)$ lines miss all these curves over $\mathbb F_q$. In particular the minimum size of a blocking family with component degrees in $\{2,\ldots,d\}$ is $\Theta_d(\log q)$ throughout this characteristic range.

## Giving the ordered roots finite equations

Write the nonvertical affine lines as $y=ux+v$. Choose a nonzero homogeneous equation $G_i$ for each curve and put $f_i(X)=G_i(X,uX+v,1)$. Its leading coefficient is $a_i(u)=G_i(1,u,0)$, a nonzero polynomial because the line at infinity is not a component. All coefficients of $f_i$ have degree at most $d$ in $(u,v)$. On a nonempty open subset $U$ of this parameter plane, each section has degree $e_i$, is separable, and the sections have disjoint roots. The complementary locus is contained in the zero set of a nonzero polynomial $B$ of degree $O_d(k^2)$: use the product of the $a_i$, the individual discriminants, and the pairwise resultants. One may take $U$ to be its nonvanishing locus. Generic transversality holds under the stated monodromy hypotheses, and generic lines avoid the finite pairwise component intersections.

For component $i$ use a single group of $e_i$ root coordinates as in [the pencil proof](PROOF.md), with a basis of $\mathbb F_{q^{e_i}}$. Write their associated linear conjugate forms as $z_i^{(0)},\ldots,z_i^{(e_i-1)}$. Impose the $e_i$ coefficient equations below the leading term in

```math
 a_i(u)\prod_{h=0}^{e_i-1}(X-z_i^{(h)})=f_i(X).
```

Their degrees are at most $2d$. Over the algebraic closure, changing coordinates within each group makes the roots independent variables. Above $U$ this gives the finite étale cover whose fiber is the set of all orderings of each component's roots. Entin's geometric monodromy group $\prod_i S_{e_i}$ acts transitively on this fiber. Restricting to the dense open chart preserves the generic splitting fields and their monodromy. Hence the geometric covering is connected and, being étale over the smooth open plane, is irreducible. Its closure $V$ in the affine coefficient-equation space is an absolutely irreducible surface defined over $\mathbb F_q$. The closure is a component: above $U$ the equations already describe precisely this surface. Bézout gives $\deg V\le D=(2d)^{dk}$. This uses Entin's exact group theorem; no uniformity in the implicit error term of his counting theorem is required.

## Counting the lines

We have $D\le q^{1/8}$. Cafure and Matera's Theorem 7.1 with dimension two gives at least $q^2-D^2 q^{3/2}-5D^{13/3}q$ rational points on $V$ once $q>6D^2$. The excluded locus $B=0$ cuts a subvariety of dimension at most one and total degree at most $O_d(k^2)D$. It has at most $O_d(k^2)Dq$ rational points by the affine degree bound. For large $q$ in terms of $d$, at least $q^2/2$ rational points of $V$ above $U$ survive. [Cafure and Matera, Lemma 2.1 and Theorem 7.1](https://arxiv.org/html/math/0405302).

At each of those rational points the $e_i$ roots are distinct Frobenius conjugates of a single element of $\mathbb F_{q^{e_i}}$. Thus every $f_i$ is irreducible of degree $e_i\ge2$ and has no rational root. Its leading coefficient is nonzero, which also excludes an intersection at the point at infinity of the chosen line. A geometric fiber contains $\prod_i e_i!\le(d!)^k$ points, giving the asserted line count. The upper bound already follows from the source's conic construction or its degree-$d$ construction.

If further curves irreducible over $\mathbb F_q$ split geometrically, each contributes at most $d^2$ rational points, since every rational point lies on two distinct conjugate components and one can bound their intersection by Bézout (or count all pairwise intersections). Adding at most $k$ such curves spoils at most $kd^2(q+1)$ lines. This is less than the displayed number of missing lines throughout the stated logarithmic range for large $q$. Thus dropping geometric irreducibility in this way also preserves the order lower bound. Linear components are excluded throughout, as in the source problem.
