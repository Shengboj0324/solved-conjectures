# Primitive sets with density at prescribed dyadic scales

**Theorem.** Let $E$ be an infinite set of positive integers. Suppose there are $K<\infty$ and $0<\sigma<1$ such that for every real $u\ge0$ and $H\ge1$,

```math
|E\cap[u,u+H]|\le K H^\sigma.
```

There is a primitive set $A$ and a constant $c_E>0$ such that $A(2^n)\ge c_E2^n$ for every $n\in E$. In particular one may prescribe $n_i=\lfloor i^\alpha\rfloor$ for **every** real $\alpha>1$. For these exponents the inverse function $t^{1/\alpha}$ is concave, giving at most $1+(H+1)^{1/\alpha}$ indices in any interval of length $H$. At $\alpha=1$ the necessary reciprocal sum diverges.

The theorem applies to irregular sets with the displayed uniform count. The unrestricted characterization is [Erdős’s question, p. 101](https://www.renyi.hu/~p_erdos/1980-03.pdf). The prime-factor regularity idea and the observation that quotients between regular integers are exceptional go back to [Erdős, Sárközy and Szemerédi, pp. 40–41](https://combinatorica.hu/~p_erdos/1970-09.pdf). We need a bound uniform in **both** the earlier block and the distance to the later block.

## Counts of small prime factors

Let $\Omega(t;w)=\sum_{p\le w} v_p(t)$ count prime factors with multiplicity. Write $L(w)=\log\log w$ for $w\ge3$. For fixed $z\in(0,2)$ and real $3\le w\le X$,

```math
\frac1X\sum_{t\le X} z^{\Omega(t;w)}\ll_z (\log w)^{z-1}. \tag{1}
```

For $1<z<2$, write the summand as $\sum_{d\mid t}g(d)$ with $g$ multiplicative and $g(p^k)=(z-1)z^{k-1}$ for $p\le w$, zero at all other prime powers with $k\ge1$. Summing over $t$ and using $\lfloor X/d\rfloor\le X/d$ bounds the average by $\prod_{p\le w}(1+(z-1)/(p-z))\ll_z(\log w)^{z-1}$ by Mertens’ prime reciprocal estimate.

For $0<z<1$, put $f(t)=z^{\Omega(t;w)}$. It is completely multiplicative and lies in $(0,1]$. Chebyshev’s bound $\sum_{p^k\le v}\log p\ll v$ gives

```math
\sum_{t\le X} f(t)\log t
=\sum_{b\le X} f(b)\sum_{p^k\le X/b}f(p)^k\log p
\ll X\sum_{b\le X}\frac{f(b)}b.
```

Also $\sum_{t\le X} f(t)\log(X/t)\ll X$, by comparison with the integral of $\log(X/t)$. Adding and bounding the last harmonic sum by $\prod_{p\le X}(1-f(p)/p)^{-1}\ll_z \log X\,(\log w)^{z-1}$ proves (1). At $z=1$ the bound follows by counting.

For each $0<\epsilon<1$ there is $D=D(\epsilon)$ for which, uniformly for $X\ge3$, at most $X/32$ integers $t\le X$ violate either inequality

```math
(1-\epsilon)L(w)-D\le\Omega(t;w)\le(1+\epsilon)L(w)+D
\qquad(3\le w\le t). \tag{2}
```

Here are details of the simultaneous estimate. Take fixed $z_+>1$ and $z_-<1$ sufficiently close to one that $z_\pm-1-(1\pm\epsilon)\log z_\pm<0$. Markov’s inequality and (1) at one fixed cutoff bound the fraction violating (2), with tolerance $D_0$, by $C e^{-\kappa L(w)}(z_+^{-D_0}+z_-^{D_0})$ for some $C,\kappa>0$. Test the cutoffs $3$, $X$, and $\exp(\exp k)\in[3,X]$ for integers $k\ge1$. The total of the exponential factors is bounded independently of $X$. Choose $D_0$ to make the fraction at most $1/32$. Monotonicity of $\Omega(t;w)$ between adjacent cutoffs, whose $L$ values differ by at most one, now gives (2) with $D=D_0+2$. Call integers satisfying (2) regular.

## Divisibility between two blocks

Fix any $\sigma<\beta<1$. Choose $0<z<1$ and then $\epsilon>0$ so that $1-z-2\epsilon\log(1/z)>\beta$. Use the same $\epsilon,D$ in all blocks. If $m<n$, put $s=\min(m,n-m)$. For $s\ge4$ the number of pairs of regular integers

```math
2^{m-1}<b\le2^m,\qquad 2^{n-1}<a\le2^n,\qquad b\mid a
```

is $\ll_{\beta} 2^n s^{-\beta}$, taking $z,\epsilon$ as fixed functions of $\beta$. Indeed $w=2^{s/2}$ is at most $b$ and $a$. Both estimates (2) applied at $w$ imply for $q=a/b$ that $\Omega(q;w)\le2\epsilon L(w)+2D$. Since $q\le Q=2^{n-m+1}$ and $w\le Q$, (1) shows that the number of choices of $q$ is at most

```math
z^{-2D} (\log w)^{2\epsilon\log(1/z)}
\sum_{q\le Q} z^{\Omega(q;w)}\ll_{\beta} Q s^{-\beta}.
```

Multiplying by the number of possible $b$, at most $2^m$, proves the bound. Its dependence on $n-m$ controls the case of two large exponents relatively close together.

## Construction

Choose a large integer $T\ge4$. Starting with the least member of $E$ at least $T$, form $F\subseteq E$ greedily by choosing each subsequent least member at distance at least $T$ from the last chosen one. For every $n\in F$ we have, uniformly,

```math
\sum_{m\in F,\ m<n}\min(m,n-m)^{-\beta}
\le\sum_{m\in F,\ m<n}\bigl(m^{-\beta}+(n-m)^{-\beta}\bigr)
\ll_{K,\sigma,\beta} T^{\sigma-\beta}. \tag{3}
```

All distances on the right are at least $T$. In a distance range $[2^kT,2^{k+1}T)$ each sum has at most $K(2^kT)^\sigma$ terms by the hypothesis on translated intervals (truncate at zero if necessary). Summing the resulting geometric series proves (3).

For $n\in F$, start with all regular odd integers in $(2^{n-1},2^n]$. There are at least $(1/4-1/32)2^n$. Discard an integer if it has a divisor among the regular odd candidates of any earlier chosen block. The pair estimate and (3) discard at most $C 2^n T^{\sigma-\beta}$ integers, even when counting a discarded integer repeatedly. Choose $T$ large enough to leave at least $2^n/8$ per block.

Let $A$ be the union of the retained blocks and $\{2\}$. Each dyadic block is primitive internally. The deletions prevent divisibility between blocks, and every retained element is odd and greater than two. Every exponent $e\in E$ at or after the first chosen exponent has some $n\in F$ with $n\le e<n+T$. Hence $A(2^e)\ge2^n/8\ge2^{-T}2^e/8$. The finitely many earlier exponents have $A(2^e)\ge1$, which supplies the required positive constant for all of $E$.

## Exponent sets of full counting dimension

Write $N_E(H)=\sup_{u\ge0}|E\cap[u,u+H]|$. There is an absolute constant $C$ such that the same conclusion holds whenever

```math
\sum_{j\ge 1} \frac{N_E(2^j)}{2^j}
\exp\!\bigl(C\sqrt j\,(\log(2+j))^{3/2}\bigr)<\infty. \tag{4}
```

For example, $N_E(H)\ll H\exp(-c(\log H)^a)$ for any fixed $c>0$ and $1/2<a<1$ suffices. This includes $n_i=\lfloor i\exp((\log i)^a)\rfloor$ for every such $a$. Indeed $x\exp((\log x)^a)$ is increasing and eventually convex by differentiation. Its inverse is concave there, and a translated interval of length $H$ contains at most a constant plus the inverse at $H+O(1)$. If $H=x\exp((\log x)^a)$ then $\log x\sim\log H$, so this count is $O(H\exp(-\tfrac12(\log H)^a))$. On the other hand the count in the initial interval is $H^{1-o(1)}$, which exceeds every fixed power $H^\sigma$ with $\sigma<1$ for large $H$.

**Uniform moments.** The implied constant in (1) can be taken absolute throughout $0<z\le3/2$. For $1<z\le3/2$, the logarithm of the upper Euler product is at most $(z-1)\sum_{p\le w}1/p+O(\sum_p p^{-2})$ uniformly, including $p=2$ by increasing the constant. For $0<z\le1$, the Euler product in the harmonic sum is at most a constant times $\log X\,(\log w)^{z-1}$ by the same expansion, and this quantity is bounded below by a positive absolute constant. The Chebyshev estimate used in (1) also has an absolute constant.

**Simultaneous regularity.** Put $F(x)=\sqrt{(1+x)\log(2+x)}$ for $x\ge0$. There is an absolute $D$ such that for every $X\ge3$, all but at most $X/32$ positive integers up to $X$ satisfy

```math
|\Omega(t;w)-L(w)|\le D F(L(w))\qquad(3\le w\le t). \tag{5}
```

To see this, take $z=e^h$ in (1) with $|h|\le1/4$. Writing $x=L(w)$, the corresponding moment of $\exp(h(\Omega(t;w)-x))$ is at most $C_0\exp(C_1 h^2(1+x))$, since $e^h-1-h=O(h^2)$. Markov's inequality, with the sign of $h$ chosen for each tail and $|h|=\min(1/4,y/(2C_1(1+x)))$, bounds the fraction with deviation greater than $y$ by

```math
2 C_0\exp\bigl(-c_0\min(y^2/(1+x),y)\bigr).
```

For $y=B F(x)$, $B\ge1$, the minimum is at least a constant times $B\log(2+x)$, since $F(x)\gg\log(2+x)$. Test the grid of $L$ values used in (2), including both endpoints. For $B$ sufficiently large the sum over that grid of $2C_0(2+x)^{-c_1 B}$ is at most $1/32$, uniformly in $X$. Monotonicity between grid points, whose spacing is at most one, gives (5), increasing the absolute constant because $F(x+1)/F(x)$ is bounded.

**Divisibility and summation.** Use the regular numbers (5) in the construction. With $s=\min(m,n-m)$, $w=2^{s/2}$, $x=L(w)$, and $Q=2^{n-m+1}$ as before, each possible quotient has $\Omega(q;w)\le2D F(x)$. Apply (1) with $z=(1+x)^{-1/2}$ to bound the count of quotients by

```math
C_2 Q\exp\bigl(-x+zx+2D F(x)\log(1/z)\bigr)
\le C_3 Q e^{-x}\exp\bigl(C_4\sqrt{1+x}\,(\log(2+x))^{3/2}\bigr).
```

Here $e^x=(s/2)\log2$. For each interval $2^j\le s<2^{j+1}$, the pair count divided by $2^n$ is therefore at most $C_5 2^{-j}\exp(C\sqrt j\,(\log(2+j))^{3/2})$, increasing $C$ for the first few intervals. For fixed $n$, an earlier exponent with $2^j\le\min(m,n-m)<2^{j+1}$ lies in one of two intervals of length $2^j$, according as the minimum is $m$ or $n-m$. Hence there are at most $2N_E(2^j)$ such exponents. Take the spacing $T=2^J$. By (4), the tail starting at $j=J$ can be made small enough to discard fewer than $2^n/16$ candidates in every block. The rest of the earlier construction, including coverage of the intervening prescribed exponents, now gives one primitive set with the asserted uniform peaks.
