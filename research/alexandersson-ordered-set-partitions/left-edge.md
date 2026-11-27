# Alexandersson's ordered-set-partition conjecture

Fix a block threshold $j\ge2$. For any fixed $K$, the $K$ zeros of largest absolute value of $O_{n,j}$ are simple, negative, and strictly interlace with the corresponding end of the next row for all sufficiently large $n$. Their individual asymptotics depend on $n\bmod j$. The limiting functions are the $j$ sections of the exponential series. Combined with the [right-edge theorem](edge.md), this determines both extremes. The zeros in the intervening region remain part of the open conjecture. [Alexandersson's problem](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#set-partitions-and-trees)

Write $n=jm+s$, $0\le s<j$, and $D_j=j!\big((j+2)/(j+1)\big)^j$. Define
```math
 L_s(x)=s!\sum_{\ell\ge0}\frac{(-x)^\ell}{(s+j\ell)!},
 \qquad 0<\lambda_{s,1}<\lambda_{s,2}<\cdots
```
where the $\lambda_{s,k}$ are its zeros. For every fixed $k$ the $k$th zero of $O_{jm+s,j}$ in decreasing order of absolute value satisfies
```math
 t_{jm+s,k}=-\frac{D_jm^j}{\lambda_{s,k}}(1+o(1)).
```
In particular, if $s<j-1$ then $t_{n,k}<t_{n+1,k}<t_{n,k+1}$. If $s=j-1$, the degree increases and $t_{n+1,k}<t_{n,k}<t_{n+1,k+1}$. These inequalities hold for all $1\le k\le K$ once $m$ is sufficiently large.

## Reversing the polynomial

Use $A=\sum_{i=1}^{j-1}z^i/i!$, $C=\sum_{i\ge j}z^i/i!$, $G=(1-A)^{-1}$ and $H=j!z^{-j}CG$. Then $G(0)=H(0)=1$, $h=H'(0)=(j+2)/(j+1)$, and the first-block decomposition gives
```math
 c_{n,k}:=[t^k]O_{n,j}(t)/n!=(j!)^{-k}[z^{n-jk}]H(z)^kG(z).
```
For fixed $d$, $[z^d]H(z)^kG(z)\sim (kh)^d/d!$ as $k\to\infty$. Indeed $H^k=\sum_{a=0}^d\binom ka(H-1)^a$ through degree $d$, and only $a=d$ contributes to degree $d$ in $k$. This includes $d=0$. Consequently for every fixed $\ell$,
```math
 \frac{c_{jm+s,m-\ell}}{c_{jm+s,m}}\frac{1}{(D_jm^j)^\ell}
 \longrightarrow \frac{s!}{(s+j\ell)!}.
```

The reciprocal polynomials
```math
 Q_{m,s}(x)=\sum_{\ell=0}^{m}
 \frac{c_{jm+s,m-\ell}}{c_{jm+s,m}}
 \left(\frac{-x}{D_jm^j}\right)^\ell
```
converge to $L_s(x)$ locally uniformly on $\mathbb C$. To justify the limit under the sum, choose $B$ such that both $H$ and $G$ are coefficientwise bounded above by $(1-Bz)^{-1}$. This is possible by analyticity at zero, nonnegative coefficients, and constant terms one. Thus $[z^d]H^kG\le B^d\binom{k+d}{d}\le [B(k+d)]^d/d!$. For $k=m-\ell$, $d=s+j\ell$, we have $k+d\le 2jm$ for $m\ge1$. Also $[z^s]H^mG\ge c_jm^s$ for all sufficiently large $m$. After normalizing, the summands on $|x|\le R$ are bounded by $C_j(C'_j R)^\ell/(s+j\ell)!$. This is summable for every $R$.

## Reality, simplicity and the cyclic order of the limiting zeros

All zeros of $L_s$ are positive. One direct proof takes the finite sections $\sum_{\ell\ge0}\binom M{s+j\ell}M^{-s-j\ell} y^\ell$ for $M\ge s$. The doubly infinite upper Toeplitz matrix of coefficients of $(1+z/M)^M$ is totally nonnegative, being the $M$th power of a totally nonnegative bidiagonal matrix. Rows $ja$ and columns $jb+s$ form the Toeplitz matrix for the section, since $0\le s<j$. It is totally nonnegative. The finite Aissen–Schoenberg–Whitney theorem gives only nonpositive zeros for the section. Coefficientwise domination by $1/(s+j\ell)!$ gives uniform convergence on compact sets. Changing $y$ to $-x$ and multiplying by $s!$ gives the assertion by Hurwitz and $L_s(0)=1$. This reality property is also a special case of the hyper-Bessel zero theorem of Chaggara and Ben Romdhane. [Aissen–Schoenberg–Whitney](https://doi.org/10.1073/pnas.37.5.303) · [Chaggara–Ben Romdhane](https://doi.org/10.1080/10652469.2014.973191)

Each $L_s$ is a nonpolynomial entire function of order at most $1/j$, by comparison with $\exp(|x|^{1/j})$ for $|x|\ge1$. Hadamard factorization gives infinitely many positive zeros, a convergent sum of reciprocals, and $L_s(x)=\prod_k(1-x/\lambda_{s,k})$, initially listing zeros with multiplicity. Set $f_s(u)=u^s L_s(u^j)/s!$. The derivative cycle is $f_s'=f_{s-1}$ for $s\ge1$ and $f_0'=-f_{j-1}$. At positive $u$ away from zeros,
```math
 \frac{u f_s'(u)}{f_s(u)}
 =s-j\sum_k\frac{x}{\lambda_{s,k}-x},\qquad x=u^j.
```
Its derivative with respect to $x$ is strictly negative on every interval between poles. Between consecutive distinct positive zeros it runs from $+\infty$ to $-\infty$, so there is exactly one simple zero of $f_s'$ there. Before the first zero there is one if $s>0$ and none if $s=0$. At a zero of multiplicity $b$, differentiation retains multiplicity $b-1$.

In the $x$ coordinate, these statements for adjacent residue classes give the weak cyclic order
```math
 \lambda_{0,k}\le\lambda_{1,k}\le\cdots\le\lambda_{j-1,k}
 \le\lambda_{0,k+1}.
```
Indeed, the derivative of $f_s$ for $s>0$ has its $k$th positive zero at or before the $k$th positive zero of $f_s$, counting multiplicities. The derivative of $f_0$ has its $k$th at or before the $(k+1)$st of $f_0$. A repeated zero in any one class would occupy positions $k,k+1$ in that class and would force every class between them in the cyclic order to vanish at the same point. By the derivative cycle, $f_0$ and its first $j-1$ derivatives would vanish at the corresponding $u>0$. The equation $f_0^{(j)}=-f_0$ and uniqueness would force $f_0\equiv0$, contradicting $f_0(0)=1$. This proves simplicity. An equality between adjacent classes in the cyclic order would give a common positive zero of a function and its derivative, which also contradicts simplicity. All displayed inequalities are strict.

## Returning to the finite rows

Choose $\lambda_{s,K}<R<\lambda_{s,K+1}$ and disjoint small conjugation-invariant disks around the first $K$ zeros inside $|x|<R$. Uniform convergence and Rouché's theorem give exactly one zero of $Q_{m,s}$ in each small disk and $K$ in $|x|<R$ for all large $m$. Each is simple and real by complex conjugation, and tends to the center as the disks shrink. Since $Q_{m,s}(0)=1$, inversion $t=-D_jm^j/x$ takes these to the zeros of largest absolute value, with the displayed asymptotic. The strict order of the limiting zeros persists between adjacent rows. At the degree increase, $(m+1)^j/m^j\to1$, producing the indicated cyclic rollover.

The [integer-arithmetic check](check_left_edge.py) isolates the largest-modulus real candidates using rational sign brackets, certifies their ranks among the negative zeros by Descartes' rule, and checks consecutive ordering on both sides of a degree change. The analytic argument proves their ranks among all complex zeros.
