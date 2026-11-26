# Wang–Yang’s Eulerian square conjecture

Wang and Yang’s Conjecture 4.3 asserts strict positivity of all minors of $[A(n+k,k)]_{n,k\ge1}$, where $A(m,j)$ counts permutations of $m$ letters with $j-1$ descents. Write $E(a,b)$ for the number of permutations with $a$ ascents and $b$ descents, so they have $a+b+1$ letters. The source matrix has entries $E(n,k-1)$. Reversing a permutation gives $E(a,b)=E(b,a)$. Below the symmetric extension includes $a=0$. [Wang–Yang, §4](https://cfc.nankai.edu.cn/_upload/article/files/ca/07/264e89bc4d9bb418a6d91d482b90/ef62459f-bec2-470d-8199-b57a790de20a.pdf) · [Research issue](https://github.com/1337isnot1337/solved-conjectures/issues/804)

**Proposition.** Every principal minor of the symmetric matrix $E$ is strictly positive, for arbitrary finite index sets. Every two-by-two minor of $E$ with increasing row and column indices is strictly positive. The principal-minor assertion inside Wang and Yang’s indexing uses rows $S$ and columns $S+1$, for finite $S\subseteq\{1,2,\ldots\}$.

## A Gram integral

Let $p_j$ denote the density of the sum of $j$ independent uniform variables on $[0,1]$, with $p_1$ the indicator of $(0,1)$ up to endpoints. The cardinal-spline formula gives $p_{a+b+2}(b+1)=E(a,b)/(a+b+1)!$. It also follows by inclusion–exclusion for the volume of a cube slice and the explicit formula for Eulerian numbers. The symmetry $p_j(x)=p_j(j-x)$ and convolution therefore give

```math
\frac{E(a,b)}{(a+b+1)!}=\int_0^\infty p_{a+1}(x)p_{b+1}(x)\,dx.
```

The spline identity is classical. [Wang–Xu–Xu, Theorem 1.1](https://arxiv.org/abs/0808.2349)

Multiplication by the gamma integral for $(a+b+1)!$ gives a Gram matrix with functions $g_a(x,t)=t^a p_{a+1}(x)$ and positive measure $t e^{-t}\,dt\,dx$ on the positive quadrant. On $0<x<1$ the function $g_a(x,t)$ equals $(tx)^a/a!$. A linear combination with distinct $a$ vanishing almost everywhere there gives a polynomial in $t$ vanishing almost everywhere for almost every fixed $x$ in that interval. Every coefficient vanishes. Thus every finite family of the $g_a$ is linearly independent, proving strict positivity of its Gram determinant.

## Arbitrary row and column pairs

The densities $p_j$ are log-concave, by closure of log-concavity under convolution. For $0<x<y$ and $u\ge0$, log-concavity on interval support gives

```math
p_j(x)p_j(y-u)\ge p_j(y)p_j(x-u).
```

When the right side is positive, $x,y-u$ lie between $x-u$ and $y$ and have the same sum as the endpoints. Integrating over $0<u<1$ gives the nonnegative determinant for $(p_j,p_{j+1})$ at $(x,y)$. In the common interior of the supports the adjacent ratios $p_{j+1}(x)/p_j(x)$ are nondecreasing. Multiplying successive ratios proves the same two-row inequality for any $j<k$. If either point is outside the common interior, the nested supports $(0,j)\subset(0,k)$ give the inequality directly, up to measure-zero endpoints.

For the normalized matrix $B(a,b)=E(a,b)/(a+b+1)!$, the two-by-two determinant is the integral over $x<y$ of the product of the respective two-row spline determinants. This is the two-function integral Cauchy–Binet identity, so every such minor of $B$ is nonnegative. All entries of $B$ are positive. The factorials $H(a,b)=(a+b+1)!$ have strictly positive two-by-two minors because $H(a',b)/H(a,b)$ strictly increases with $b$ for $a'>a$. Multiplying the two strict/weak cross-product inequalities proves the two-by-two assertion for $E$.

Mixed minors of higher order remain open here. Brenti’s ordinary Eulerian triangle has entries indexed by the permutation length and descent number. Mao’s order-three result uses those indices. [Mao’s paper](https://arxiv.org/abs/2608.29224)

## Infinite mixed submatrices

The [spacing theorem](sparse-minors.md) proves strict total positivity of all orders on two independently prescribed infinite sequences of indices, including indices growing as $i^2\log i$. It combines a factorial cross-ratio bound near the diagonal with the leading Eulerian term far from it.

## A finite decision for any prescribed row set

**Proposition.** For every $A\ge1$, the entire rectangle with rows $0,\ldots,A$ and columns

```math
b\ge T(A)=\lceil16(A+2)^3\log(2A+4)\rceil
```

is strictly totally positive. The constant is deliberately coarse. Strict total positivity on any fixed nonempty set of rows with maximum $A$ and **all** columns is equivalent to strict positivity of its contiguous minors with first column less than $T(A)$. This leaves a finite exact decision for each prescribed row set.

**Proof.** Put $M=A+2$. Take $1\le d\le A+1$, increasing rows $0\le a_1<\cdots<a_d\le A$, and consecutive columns $t,\ldots,t+d-1$. Write $x_i=a_i+1$. The explicit Eulerian formula gives

```math
E(a,b)=\sum_{h=0}^a(-1)^h {a+b+2\choose h}(a+1-h)^{a+b+1}.
```

Divide row $i$ by $x_i^{a_i+t+1}$. In column $t+j$ the first summand becomes $x_i^j$. Each remaining base is at most $x_i(1-1/(A+1))$. Using $0\le j<d$ and bounding each binomial coefficient by $(t+2A+3)^A$, the error in every entry is at most $U\eta(t)$, where

```math
U=(A+1)^{d-1},\qquad \eta(t)=A(t+2A+3)^A e^{-t/(A+1)}.
```

The function $\eta$ decreases for $t\ge16M^3\log(2M)$, by logarithmic differentiation. At the latter real threshold $t_0$, we have $t_0+2A+3\le 2t_0$ and $\log(2t_0)\le7\log(2M)$. Consequently

```math
\eta(t)\le(2M)^{1+7M-16M^2}\quad(t\ge T(A)).
```

The main matrix $[x_i^j]$ has determinant $\prod_{i<h}(x_h-x_i)\ge1$. Multilinearity, or expansion by permutations, bounds the absolute perturbation by $d!U^d((1+\eta)^d-1)\le d!U^d2^d\eta$. Here $\eta<1$ and $d!U^d2^d\le(2M)^{M^2+M}$. The perturbation is strictly less than one, so every consecutive-column minor in the tail is positive. Fekete’s criterion for finite rectangular matrices says positivity of all contiguous minors implies strict total positivity. Apply it to each finite initial part of the tail. The same criterion on any fixed row set proves the final assertion by including the remaining contiguous minors with starting column below $T(A)$. [Fekete’s criterion, Fallat–Johnson–Sokal, Theorem 2.2](https://arxiv.org/abs/1612.02210)

## Where the spline argument stops

For the spline kernel itself, take rows $p_1,p_2,p_3$ and evaluation points $7/10,9/10,11/10$. The resulting matrix is

```math
\begin{pmatrix}1&1&0\\7/10&9/10&9/10\\49/200&81/200&59/100\end{pmatrix}.
```

Its determinant equals $-13/500$. Thus an application of integral Cauchy–Binet that requires every such spline determinant to have the same sign cannot be justified from the spline kernel. The Eulerian-square determinant involves an integral of a product, so this example concerns the auxiliary kernel alone.

The [arithmetic check](check.py) evaluates 144 of the spline integrals by multiplying exact piecewise polynomials and checking the Eulerian recurrence independently. It also checks all 4,356 two-by-two minors in the same block.

The [mixed-difference argument](differences.md) proves absolute monotonicity of the entire Eulerian square in both integer indices and strict positivity of all three-by-three minors using both constant margins in the symmetric extension.

A [fixed-offset asymptotic](diagonal-minors.md) proves strict positivity of every fixed mixed minor after translating both index sets sufficiently far along the diagonal. Its leading constant is a product of the two Vandermonde determinants.

For every fixed order, [both infinite tail rectangles](tail-minors.md) are strictly totally positive through that order, allowing arbitrary gaps and all indices on the other axis. Fixed-order verification is consequently reduced to a finite initial collection of solid minors.
