# Hill–Luo–Trinh–Vindas-Meléndez conjecture

For each $n\ge3$ there are $\epsilon_n>0$ and $M_n<\infty$ with the following property. Put $a_1=b_1-1$, $a_i=b_i$ for $2\le i\le n$, and $S=\sum_i a_i$. If $S\ge M_n$ and, for **some** $k\in\{2,\ldots,n\}$,
```math
\sum_{i\notin\{1,k\}}a_i\le\epsilon_n S,
```
then all magic coefficients of the generalized parking-function polytope are strictly positive. Thus a sequence of counterexamples of unbounded size in fixed dimension would have to retain a positive fraction of the total size outside the two indicated coordinates, for every choice of $k$. Independently of size and without this hypothesis, the first nonconstant magic coefficient is nonnegative for **all** parameters. [Original conjecture 8.1](https://arxiv.org/abs/2607.15503) · [Earlier exact reduction](cube.md)

## The multivariate lattice enumerator

Write $I_r=\{x\in[0,1]^n:\sum_i x_i\le r\}$ for the independence polytope of the uniform matroid, for $1\le r\le n$. Up to an integral translation the parking polytope is $P(a)=\sum_{i=1}^n a_i I_{n-i+1}$. Indeed the support function of $I_r$ is the sum of the largest $r$ positive parts of a linear functional (padding by zeros). Consequently the support function of this Minkowski sum equals that of the downward closure of the permuted vectors with increasing entries $a_1,a_1+a_2,\ldots,\sum_i a_i$. These vectors and their coordinate boxes give the translated parking polytope. This support identity also defines $P(a)$ when some coordinates vanish.

McMullen's multivariate Ehrhart theorem gives $|P(a)\cap\mathbb Z^n|=\sum_{k=0}^n H_k(a)$ for integral nonnegative $a$, with $H_k$ homogeneous polynomials of degree $k$ and $H_0=1$. Hence $E_{P(a)}(t)=\sum_k H_k(a)t^k$. In particular, for dimension $n$ the $i$th magic coefficient is
```math
 \mu_i(a)=\sum_{k=0}^i(-1)^{i-k}\binom{n-k}{i-k}H_k(a).
```
This follows by taking the coefficient of $z^i$ in $(1-z)^nE_{P(a)}(z/(1-z))$. Its highest homogeneous part is $H_i$. [McMullen's theorem as stated by Böröczky and Ludwig, Theorem 22](https://dmg.tuwien.ac.at/ludwig/lattice.pdf)

Since $H_1$ is linear, increasing $a_i$ by one increases $\mu_1=H_1-n$ by $[t]E_{I_{n-i+1}}(t)$. Ferroni proved that *every* ordinary Ehrhart coefficient of every full-dimensional $I_r$ is strictly positive. Thus the first magic coefficient is minimized uniquely at $b_1=\cdots=b_n=1$. Its value there is nonnegative by the classical parking-polytope case of Liu–Zhang or Hill and coauthors. The same argument identifies every coordinate increment of this coefficient exactly. [Ferroni](https://arxiv.org/abs/2012.04711) · [Liu–Zhang](https://arxiv.org/abs/2607.03854)

## Directions with one tail parameter and the cube

For $u,v\ge0$, the cube fiber identity gives
```math
 E_{u I_n+v I_r}(t)=\sum_{j=0}^n \binom nj u^jt^j E_{I_{\min(r,n-j),\,n-j}}(vt),
```
where $I_{r,m}$ denotes the same independence polytope in $m$ coordinates and the zero-dimensional term is one. A coordinate projection of $I_r$ is the indicated uniform independence polytope, and adding coordinate segments to a down-closed polytope counts the projected fibers. This proves the identity for integral $u,v$ by the [fiber argument](cube.md), and hence polynomially in both variables. For real weights the formula evaluates the homogeneous polynomials $H_i$.

Every ordinary coefficient $H_i$ on this two-coordinate cone is strictly positive when $u+v>0$. All terms have nonnegative coefficients by Ferroni's theorem. If $v>0$, the $j=0$ term is strictly positive in every degree. If $v=0$, the $j=i$ term gives $\binom ni u^i>0$.

On the compact simplex $\sum a_i=1$, take the finite union $K$ of the line segments joining the first coordinate vertex to the other coordinate vertices. All $H_i$ have a common strictly positive lower bound on $K$. By continuity they still have such a bound $c>0$ on some neighborhood of $K$. If $\sum_{i\notin\{1,k\}}a_i\le\epsilon_n S$, the normalized vector lies in this neighborhood for small enough $\epsilon_n$, since moving the omitted coordinates' mass to the first coordinate changes its $\ell^1$ distance by at most $2\epsilon_n$. Each $H_k$ is bounded on the entire simplex. Homogeneity and the formula for $\mu_i$ now give $\mu_i(a)\ge cS^i-O_n(S^{i-1})$ there for $1\le i\le n$. Choose $M_n$ uniformly over these finitely many degrees. Also $\mu_0=1$. This proves the stated uniform positivity. The argument uses Ferroni's ordinary positivity on these specific directions and leaves the general interior directions open.
