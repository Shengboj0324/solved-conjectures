# Hill–Luo–Trinh–Vindas-Meléndez conjecture

Conjecture 8.1 asks for magic positivity of every generalized parking-function polytope $\mathfrak X_n(\mathbf b)$, $n\ge3$, $b_i\ge1$. The Ehrhart polynomial is magic positive if in its expansion $E(t)=\sum_{i=0}^n\mu_i t^i(t+1)^{n-i}$ all $\mu_i$ are nonnegative. We reduce the full conjecture exactly to the boundary $b_1=1$ in every dimension. For every fixed dimension and every fixed tail $(b_2,\ldots,b_n)$, we also prove magic positivity for all sufficiently large $b_1$, with a finite explicit test for the whole ray. [Original paper, Conjecture 8.1](https://arxiv.org/abs/2607.15503) · [Issue 117](https://github.com/1337isnot1337/solved-conjectures/issues/117)

Write $P$ for the translate of $\mathfrak X_n(1,b_2,\ldots,b_n)$ by the negative all-ones vector. This is a down-closed polytope in the nonnegative orthant, meaning that $0\le y\le x\in P$ coordinatewise implies $y\in P$. Let $Q_m$ be the projection of $P$ onto any $m$ coordinates, with $Q_0$ a point. For all nonnegative integers $c$,

$$E_{\mathfrak X_n(1+c,b_2,\ldots,b_n)}(t)=\sum_{j=0}^n {n\choose j}c^j t^j E_{Q_{n-j}}(t).\tag{1}$$

In particular, for $0\le i\le n$,

$$\mu_i(\mathfrak X_n(1+c,b_2,\ldots,b_n))=\sum_{j=0}^i {n\choose j}c^j\mu_{i-j}(Q_{n-j}).\tag{2}$$

Here each projected polynomial is expanded in its ambient degree, and $E_{Q_0}=1$. For $m\ge1$, $Q_m$ is the down-shifted parking polytope with parameters

$$\left(1+\sum_{i=2}^{n-m+1} b_i,\ b_{n-m+2},\ldots,b_n\right).\tag{3}$$

**Proof of the geometric identities.** For general $\mathbf b$, put $u_j=b_1+\cdots+b_j-1$. The translated polytope is the downward closure of the convex hull of the coordinate permutations of $(u_1,\ldots,u_n)$. Indeed each integer parking vector, after shifting, lies in a coordinate box below such a permutation; conversely all vertices of each such box are shifted parking vectors. The convex hull of the union of the boxes is downward closed, as follows by decreasing coordinates in a convex combination. Increasing the first parameter by $c$ adds $c$ to each side of every box; the union of these enlarged boxes is the old union plus $[0,c]^n$. Taking convex hulls commutes with addition of this fixed convex cube. Projecting onto $m$ coordinates gives the analogous boxes on the largest $m$ side lengths $u_{n-m+1},\ldots,u_n$, since every other choice of side lengths is dominated by a permutation of these. Taking their consecutive differences gives (3).

For a down-closed compact convex set $V$, a fiber parallel to a coordinate axis over a projected integer point is an interval $[0,L]$. Adding a coordinate segment of integral length $s$ changes this fiber to $[0,L+s]$ and adds exactly $s$ lattice points. Thus the count increases by $s$ times the lattice count of the projection. All intermediate Minkowski sums stay down-closed, and projecting commutes with adding any other coordinate segment. Iterating over the $n$ segments of the dilated cube gives (1) at every nonnegative integer $t$, hence as a polynomial identity. Multiplication of a magic basis term in dimension $n-j$ by $t^j$ changes its index from $i-j$ to $i$ in dimension $n$. This proves (2).

**Reduction to $b_1=1$.** Assume the conjectured boundary result in every dimension at least three. Induct on dimension. The $j=0$ term in (2) is on that boundary. Every term with $j>0$ and $n-j\ge3$ is nonnegative by the induction hypothesis applied to (3). A two-dimensional projection has first parameter at least two. It therefore avoids the unique exceptional two-dimensional parking polytope $(1,1)$ in the authors’ Theorem 7.2. A one-dimensional projection is an interval of integral length at least one, with magic coefficients $1$ and $\mathrm{length}-1$; the zero-dimensional contribution is positive. This proves every term in (2) nonnegative and completes induction. The converse follows by specialization. Under the same boundary hypothesis, (2) also gives coefficientwise nonnegativity in the increment $c$.

**Unconditional finite decision for a fixed tail.** For $i\ge1$ let $p_i(c)$ denote the right side of (2), and let $a_{ij}=[c^j]p_i(c)$. Because every projected Ehrhart polynomial has constant term one, $a_{ii}=\binom ni>0$. Define

$$C=2+\left\lceil\max_{1\le i\le n}\ \max_{0\le j<i}\frac{|a_{ij}|}{\binom ni}\right\rceil.$$

For every real $c\ge C$, the leading term exceeds the sum of the absolute values of the others, by the geometric-series bound $\sum_{j<i}c^j<c^i/(c-1)$. Thus every magic coefficient is strictly positive for every integer $c\ge C$. Only $0\le c<C$ remain to test on that ray. The arbitrary-tail boundary assertion at $c=0$ remains open.

The [finite arithmetic check](check_cube.py) counts actual lattice points independently via sorted coordinates and the polytope's subset-sum inequalities. It compares both sides of (1) on sample tails at $n+1$ dilation values, enough to identify the polynomials. The proof uses the exact fiber count. The authors’ lattice-slice recurrence in Section 4 conditions on a coordinate height. Ferroni and Higashitani prove magic positivity for Pitman–Stanley polytopes and for certain positive simplex sums with sufficiently large weights. Neither cited theorem supplies the arbitrary-tail boundary claim. [Hill–Luo–Trinh–Vindas-Meléndez](https://arxiv.org/abs/2607.15503) · [Ferroni–Higashitani](https://arxiv.org/abs/2603.19194)

A [uniform positivity theorem](directions.md) treats neighborhoods of every direction involving the cube and one other parameter. The first nonconstant magic coefficient is nonnegative throughout the whole parameter space.
