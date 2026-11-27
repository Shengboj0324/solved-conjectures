# Asgarli–Ghioca–Yip blocking-pencil problem

For a fixed $d\ge2$ and a prime power $q$, let $b_d(q)$ be the least number of translates $y=x^d-s$, $s\in\mathbb F_q$, whose projective closures together meet every rational line. Asgarli, Ghioca and Yip ask for the asymptotic behavior when $x\mapsto x^d$ permutes the field. They obtained logarithmic order when $\gcd(d,q-1)>1$ and a logarithmic upper bound in all characteristics. [Journal paper, Question 5.4](https://doi.org/10.1007/s10623-026-01958-z) · [arXiv v2, §5](https://arxiv.org/abs/2510.15332v2).

**Theorem.** For every fixed $d\ge2$, uniformly over all prime powers,

```math
 b_d(q)=\Theta_d(\log q).
```

The lower bound holds for any $k$ degree-$d$ polynomials $g_1,\ldots,g_k$ with the same nonzero leading coefficient. More precisely, put $D=d^{dk}$. If $q$ is sufficiently large in terms of $d$ and $1\le k\le (\log q)/(8d\log d)$, at least $q^2/(8d(d-1)D)$ rational lines miss every graph, including its projective closure.

## Choosing a common polynomial with no rational zero

Write $c$ for the common leading coefficient. For $u\in\mathbb F_q$ put $h_u(Y)=cY^d+uY$. Every ordered pair of different field elements collides under exactly one $h_u$. A fiber of size $j$ contains $j(j-1)$ ordered collisions and $j\le d$. At most $(d-1)q$ collisions occur for $u=0$. Thus some $u\ne0$ accounts for at least $q(q-d)/(q-1)\ge q/2$ collisions when $q$ is large. The number of values omitted by $h_u$ equals the sum of $j-1$ over its nonempty fibers, so it is at least $q/(2d)$. The derivative $cdY^{d-1}+u$ is a nonzero polynomial in every characteristic. At most $d-1$ values are images of its roots over the algebraic closure. There are therefore at least $q/(4d)$ choices of $a\in\mathbb F_q$ such that $h_u(Y)-a$ is squarefree and has no rational root. Fix one such $a$.

Write $g_i(X)=cX^d+\sum_{j<d}c_{ij}X^j$. Form the following monic polynomial in $Y$, with parameter $T$:

```math
 F_i(Y,T)=c^{-1}\left(cY^d+\sum_{j<d}c_{ij}Y^j T^{d-j}+uY-a\right).
```

At $T=0$ these polynomials all equal $c^{-1}(h_u(Y)-a)$. At $T=t\ne0$, the substitution $Y=tx$ shows that a rational zero is an intersection of $y=g_i(x)$ with the line

```math
 y=-u t^{1-d}x+a t^{-d}.
```

The unique point of each projective graph at infinity is $[0:1:0]$. The displayed line also misses this point. We count parameters $t$ at which all the polynomials have no rational zero.

## A curve recording the degrees of the roots

Let $e_1,\ldots,e_m$ be the degrees of the distinct irreducible factors of the common polynomial at zero. Each $e_j\ge2$ and $\sum_j e_j=d$. For each $j$, fix an $\mathbb F_q$-basis $b_{j1},\ldots,b_{j e_j}$ of $\mathbb F_{q^{e_j}}$. For every pair $i,j$, introduce $e_j$ independent coordinates $z_{ij\ell}$. Match the coefficients of $Y$ below the leading term in

```math
 \prod_{j=1}^m\prod_{h=0}^{e_j-1}
 \left(Y-\sum_{\ell=1}^{e_j} b_{j\ell}^{q^h}z_{ij\ell}\right)=F_i(Y,T)
 \qquad(1\le i\le k).
```

Frobenius permutes the factors in each inner product, so these are $kd$ equations over $\mathbb F_q$ in $kd+1$ variables. Each has total degree at most $d$. Over the algebraic closure, the $e_j$ linear forms in each group are independent: the matrix of the distinct field embeddings on a basis is nonsingular by separability. In the resulting split coordinates the left sides are monic polynomials in their ordered roots. For any fixed $T$ there are only finitely many choices for those roots.

At $T=0$, choose one root of each irreducible factor in its degree-$e_j$ extension and use its basis coordinates for every $i$. This gives an $\mathbb F_q$-point. For each $i$ the $d$ conjugates there are all distinct, by squarefreeness. The Jacobian of the elementary symmetric coefficients in $d$ ordered roots is, up to sign, their Vandermonde determinant. The Jacobian in the $kd$ coordinates other than $T$ is therefore invertible, also after returning to the basis coordinates. The point is smooth of dimension one and lies on a unique geometric irreducible component $C$. Frobenius fixes the point and hence this component, which is an absolutely irreducible affine curve defined over $\mathbb F_q$. Its map to the $T$-line is nonconstant because every fiber is finite. The affine Bézout inequality gives $\deg C\le D=d^{dk}$. [Cafure and Matera, §2, Bézout inequality](https://arxiv.org/html/math/0405302).

## Counting good parameters

For an absolutely irreducible affine curve of degree $\Delta\le D$, Cafure and Matera's Theorem 7.1 gives the lower bound below when $q>4D^2$, independently of the ambient dimension:

```math
 \# C(\mathbb F_q)\ge q-D^2\sqrt q-5D^{13/3}.
```

The discriminant of each $F_i$ as a polynomial in $Y$ is nonzero at $T=0$. Its $T$-degree is at most $d(2d-2)$, using the coefficient degree of the degree-$d$ discriminant. Remove the fiber at zero and all fibers above the zeros of these discriminants. Each fiber has at most $D$ geometric points by Bézout with the parameter hyperplane. Thus at most $D(1+kd(2d-2))$ points are removed. Since $D\le q^{1/8}$, at least $q/2$ rational points remain for sufficiently large $q$ depending only on $d$. [Cafure and Matera, Theorem 7.1](https://arxiv.org/html/math/0405302#S7).

At one such rational point every inner group in the product consists of the Frobenius conjugates of an element of $\mathbb F_{q^{e_j}}$. All roots in each $F_i$ are distinct. If the element had smaller degree, its conjugates in this group would repeat. Hence every group has orbit length $e_j\ge2$ and no $F_i$ has a rational zero. There are at least $q/(2D)$ distinct good values of $t$ since each fiber contains at most $D$ points.

Repeat for every admissible $a$ with the same $u$. A fixed affine line is counted by at most $d-1$ pairs $(a,t)$: its slope determines $t^{d-1}$ since $u\ne0$, and then its intercept determines $a$. This gives the stated number of distinct missing lines and the logarithmic lower bound, without a restriction on $\gcd(d,q-1)$ or the characteristic.

For the upper bound in the specified pencil, a nonvertical line meets the translate with parameter $s$ exactly when $s$ belongs to the value set of a degree-$d$ polynomial $x^d+ux+v$. This set has at least $q/d$ elements. Independently sampling $k$ parameters misses a particular line with probability at most $(1-1/d)^k$. Taking $k>2\log q/[-\log(1-1/d)]$ makes the expected number of missed nonvertical lines less than one. The vertical lines and the line at infinity pass through the common point $[0:1:0]$. Removing repeated sampled parameters yields the required blocking family. This is the order of the authors' greedy bound in Theorem 5.1. [Asgarli–Ghioca–Yip, §5](https://arxiv.org/abs/2510.15332v2).
