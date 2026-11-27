# The exact minimum for Frobenius exponents

Let $q=p^e$ and suppose the function $x^d$ on $\mathbb F_q$ equals $x^{p^j}$ for some $j\ge0$. This includes $d\equiv p^j\pmod{q-1}$, with $d\ge2$. Put $g=\gcd(e,j)$, $Q=p^g$ and $r=e/g$, taking $g=e$ when $j=0$. Then the exact pencil minimum is

```math
 b_d(q)=1+r(Q-1).
```

The maps $x\mapsto x^{p^j}+ux$ are linear over $K=\mathbb F_Q$. Each is bijective unless $-u=a^{p^j-1}$ for some $a\ne0$, by its kernel equation. In the exceptional case its image is

```math
 a^{p^j}\{y^{p^j}-y:y\in\mathbb F_q\}=a^{p^j}\ker(\operatorname{Tr}_{\mathbb F_q/K}).
```

The trace is invariant under the indicated Frobenius map. Both displayed subspaces before scaling have dimension $r-1$, since its fixed field is $K$ and the trace pairing of a finite separable extension is nondegenerate. As $a$ varies, $a^{p^j}$ ranges over all nonzero scalars. The nondegenerate trace pairing identifies all $K$-linear functionals with $x\mapsto\operatorname{Tr}(bx)$. Hence the translated exceptional value sets in the line test of [the main proof](PROOF.md) are precisely all affine $K$-hyperplanes in the $r$-dimensional space $\mathbb F_q$. A set of shift parameters blocks the pencil if and only if it meets all these hyperplanes.

The minimum size of an affine hyperplane blocking set is the classical Jamison–Brouwer–Schrijver theorem. For completeness, translate a blocking set $S$ so $0\in S$ and choose vector coordinates over $K$. For nonzero $w$, the set meets $w\cdot x=1$. Thus $\prod_{s\in S\setminus\{0\}}(1-w\cdot s)$ represents the indicator function of the origin on $K^r$. The unique representative of this function of degree less than $Q$ in each variable is $\prod_{i=1}^r(1-w_i^{Q-1})$. Uniqueness follows successively from the univariate root bound. Reducing the first polynomial using $w_i^Q=w_i$ never increases total degree, giving $|S|-1\ge r(Q-1)$. Conversely, the union of the $r$ coordinate axes has exactly $1+r(Q-1)$ points and meets every affine hyperplane. [Brouwer and Schrijver, *The blocking number of an affine space*](https://ir.cwi.nl/pub/9858/9858D.pdf).
