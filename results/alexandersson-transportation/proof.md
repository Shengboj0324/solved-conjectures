# Alexandersson’s transportation polytope conjecture

Take an integer $m\ge2$ and the full transportation polytope $T_m$ with row sums $(1,1,m)$ and column sums $(2,1,\ldots,1)$, with $m$ ones. Both vectors have a nonunit entry and sum to $m+2$. Every cell can simultaneously be positive, as seen from the table with entries $r_ic_j/(m+2)$. The two first rows determine the third, and their two independent row-sum constraints leave dimension $2m$. Write $L_m(k)$ for the number of integer points in $kT_m$. Its Ehrhart series has numerator $H_m(z)$ and denominator $(1-z)^{2m+1}$.

## Counting every dilation

In the first two rows choose two arbitrary weak compositions of $k$ into $m+1$ parts. There are $\binom{k+m}{m}^2$ choices. The column with margin $2k$ can accommodate every such pair. A column of margin $k$ is invalid exactly when its two entries sum to at least $k+1$. Two columns cannot both be invalid, since the two rows contain only $2k$ units altogether.

For one specified invalid column, the $2m$ entries of the first two rows in the *other* columns have total at most $k-1$. Conversely any such nonnegative entries determine the two entries in the specified column, by the two row sums. There are $\binom{k-1+2m}{2m}$ choices, interpreted as zero when $k=0$. The third row fills all residual margins. Hence

```math
L_m(k)=\binom{k+m}{m}^{\!2}-m\binom{k-1+2m}{2m}.
```

For the first term, count pairs of weakly increasing lists of length $m$ with entries in $\{0,\ldots,k\}$. Sort the combined lists, breaking ties by giving the first list priority. The word of list labels has $m$ letters $A$ and $m$ letters $B$. The sorted numbers must increase strictly at each $BA$ and are otherwise weakly increasing. A word with $j$ such transitions gives $\binom{k+2m-j}{2m}$ choices, with zero when $k<j$. There are $\binom mj^2$ such words. Indeed the numbers of $A$'s already read at the transitions form a $j$-subset of $\{0,\ldots,m-1\}$, and the numbers of $B$'s form a $j$-subset of $\{1,\ldots,m\}$. In increasing order these two lists specify every turn from $B$ to $A$, so they reconstruct the word. Summing the binomial series in $k$ gives

```math
H_m(z)=B_m(z)-mz,\qquad B_m(z)=\sum_{j=0}^m\binom mj^2 z^j.
```

## A rational certificate

For a nonzero real polynomial $P$ with only real roots $\rho_i$, listed with multiplicity, logarithmic differentiation gives

```math
(P'(x))^2-P(x)P''(x)=P(x)^2\sum_i(x-\rho_i)^{-2}\ge0
```

away from its roots, and by continuity at the roots as well. Direct substitution of $x=-1/5$ in the formula for $H_{12}$ gives

```math
\begin{aligned}
5^{12}H_{12}(x)&=41\,780\,056,\\
5^{11}H'_{12}(x)&=-357\,481\,092,\\
5^{10}H''_{12}(x)&=12\,374\,409\,432.
\end{aligned}
```

Consequently $5^{22}((H'_{12})^2-H_{12}H''_{12})(-1/5)=-389\,210\,787\,898\,375\,728<0$. This disproves the conjecture. The [checker](check.py) independently obtains the whole numerator from the column-margin dynamic program and counts ten distinct real roots by Sturm’s theorem.

## An unbounded family of nonreal roots

**Theorem.** As $m\to\infty$, the number of nonreal zeros of $H_m$, counted with multiplicity, is $\Omega(\sqrt{m\log m})$.

Write $F_m(z)=B_m(-z)$. For the Legendre polynomial $P_m$ normalized by $P_m(1)=1$, the binomial expansion of Rodrigues’ formula yields

```math
F_m(z)=(1+z)^mP_m\!\left(\frac{1-z}{1+z}\right).
```

Indeed $P_m(x)=2^{-m}\sum_j\binom mj^2(x-1)^j(x+1)^{m-j}$. Thus $F_m$ has $m$ simple positive zeros $r_1<\cdots<r_m$, the transforms of the Legendre zeros in $(-1,1)$. Set $\theta=2\arctan\sqrt z$, so the argument of $P_m$ is $\cos\theta$. Bernstein's inequality gives

```math
(\sin\theta)^{1/2}\,|P_m(\cos\theta)|
\le \sqrt{\frac{2}{\pi(m+1/2)}}.
```

This is the case $\alpha=\beta=0$ of [NIST DLMF, Eq. 18.14.3](https://dlmf.nist.gov/18.14.E3).

On the interval $I_m=[1/m,(\log m)/(8m)]$ for all sufficiently large $m$, one has $(1+z)^m\le m^{1/8}$ and $\sin\theta=2\sqrt z/(1+z)\ge m^{-1/2}$. Consequently $|F_m(z)|=O(m^{-1/8})$ uniformly on $I_m$. Since $mz\ge1$, the perturbed polynomial $H_m(-z)=F_m(z)+mz$ is strictly positive throughout $I_m$.

There are $\Omega(\sqrt{m\log m})$ zeros of $F_m$ in $I_m$. To see this directly put $u(\theta)=\sqrt{\sin\theta}\,P_m(\cos\theta)$ and $s=m+1/2$. The Legendre differential equation gives

```math
u''+\left(s^2+\frac1{4\sin^2\theta}\right)u=0.
```

Every open interval $(a,a+\pi/s)$ inside $(0,\pi)$ contains a zero. Otherwise choose the sign of $u$ positive there and take $v(\theta)=\sin(s(\theta-a))$. The Wronskian $u'v-uv'$ decreases strictly inside, since its derivative is $-uv/(4\sin^2\theta)<0$. Its endpoint values are $-su(a)\le0$ and $su(a+\pi/s)\ge0$, a contradiction. In the $\theta$ coordinate the length of $I_m$ is at least $\sqrt{(\log m)/(8m)}-1/\sqrt m$, because $2/(1+y^2)\ge1$ for $0\le y\le1$. It therefore contains $\Omega(\sqrt{m\log m})$ disjoint intervals of length $\pi/s$. Between successive zeros the sign alternates, so $I_m$ contains that same order of magnitude of entire intervals where $F_m<0$ bounded by consecutive zeros.

To count the real roots that can survive elsewhere, consider any bounded interval $(r_i,r_{i+1})$ where $F_m<0$. A zero of $H_m(-z)$ there requires $|F_m(z)|/z=m$. For $z>r_1$,

```math
\frac{d^2}{dz^2}\log\frac{|F_m(z)|}{z}
=\frac1{z^2}-\sum_{j=1}^m\frac1{(z-r_j)^2}<0
```

away from the zeros, by the term $j=1$. A horizontal level is attained at most twice with multiplicities on each such interval. A tangency has multiplicity two by strict negativity of the second derivative. On $(r_m,\infty)$ the log derivative $\sum_j1/(z-r_j)-1/z$ is positive, so at most one root occurs there if $m$ is odd. No roots occur where $F_m\ge0$ for $z>0$. The coefficients of $H_m$ are positive, ruling out roots of $H_m$ on $[0,\infty)$. The bounded negative intervals have total capacity $2\lfloor m/2\rfloor$, with one further possible root on the final interval for odd $m$. Every negative interval wholly in $I_m$ contributes zero against its capacity of two. The claimed lower bound on the number of nonreal zeros follows.
