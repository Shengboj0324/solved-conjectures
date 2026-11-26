# Alexandersson's ordered-set-partition conjecture

For each fixed threshold $j\ge2$, a positive fraction of the rightmost zeros of the ordered-set-partition polynomials are simple, negative, and strictly interlace between consecutive rows. The fraction is independent of the row length. Their limiting right endpoint and the spacing of every fixed number of extreme zeros can be calculated explicitly. The location of the remaining zeros, including possible nonreal zeros, stays open. Here “rightmost” orders the **real** zeros.

Write $O_n(t)=O_{n,j}(t)$ and $P_k(z)=\sum_{s=0}^k z^s/s!$. Put $A=P_{j-1}-1$, $C=e^z-P_{j-1}$ and $D=1-A-tC$. Decomposing an ordered partition at its first block gives $[z^n]D^{-1}=O_n(t)/n!$. The original conjecture asks for every zero and every row. [Author's statement](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#set-partitions-and-trees) · [Initial recurrences and literature](PROGRESS.md)

Let $r$ be the unique positive solution of

$$2(j-1)\int_0^1 u^{j-2}e^{-ru}\,du=1.$$

Set $T(x)=(1-A(x))/C(x)$, $t_c=T(r)$, and $b=\sqrt{2/T''(r)}$. There exist $\eta_j>0$ and $N_j$ such that, for $n\ge N_j$, the first $\lfloor\eta_j n\rfloor$ real zeros $x_{n,1}>x_{n,2}>\cdots$ exist, are simple, and satisfy

$$x_{n+1,k+1}<x_{n,k}<x_{n+1,k}<t_c<0\qquad(1\le k\le\lfloor\eta_j n\rfloor).$$

For each fixed $k\ge1$,

$$x_{n,k}=t_c-\frac{k^2\pi^2r^2T''(r)}{2n^2}+O_{j,k}(n^{-3}),$$

where the implied constant may depend on $j,k$.

## The critical point

The sign of $T'$ is opposite to that of $B=A'C+(1-A)C'$. Direct differentiation and the integral remainder of the exponential series give

$$B=(2-z^{j-1}/(j-1)!)e^z-2P_{j-2}(z),\qquad
\frac{(j-1)!B(z)}{e^z z^{j-1}}=2(j-1)\int_0^1u^{j-2}e^{-zu}\,du-1.$$

The latter function decreases strictly from $1$ to $-1$ with negative derivative. Hence $r$ is the unique minimum of $T$ on the positive real axis, and $T''(r)>0$. The unique positive solution $\alpha$ of $A(\alpha)=1$ lies below $r$, since $B(\alpha)=A'(\alpha)C(\alpha)>0$. In particular $t_c<0$.

For $\alpha\le x\le r$, the function $|1-A(z)|$ on $|z|=x$ has its unique minimum at $z=x$. For $j=2$ this follows from $A(z)=z$. For $j\ge3$, if $V$ is uniform on $[0,1]$, then $V^{1/(j-1)}\ge V^{1/2}$. Taking expectations of $e^{-xV^{1/(j-1)}}$ in the critical-point equation gives $r\le r_3<7/6$. To verify the last bound, put $y=7/6$. Then $4(1-(1+y)e^{-y})/y^2<1$ follows from $e^y<13/4$ (sum terms through degree five and bound the tail by $(y^6/6!)/(1-y/7)$). Also $y^2<2\log 2$ follows from $\log 2>2(1/3+1/81)$. With $u_m=x^m/m!$, expansion of the square yields

$$|1-A(xe^{i\theta})|^2-(1-A(x))^2
=2\sum_{m=1}^{j-1}\left(u_m-\sum_{i=1}^{j-1-m}u_i u_{i+m}\right)(1-\cos m\theta).$$

The inner sum divided by $u_m$ is at most $e^{x^2/(m+1)}-1<1$, using $(m+1)\cdots(m+i)\ge(m+1)^i$. Every bracket is positive and the $m=1$ term is strict off the positive axis.

## Separating the two poles

For $t_c<t<0$, the smaller positive solution $s$ of $T(s)=t$ lies in $(\alpha,r)$. Fix $s<x<r$. Since $T(x)<t$, on the circle of radius $x$ we have $|1-A(z)|\ge A(x)-1>|t|C(x)\ge |tC(z)|$. The polynomial $1-A$ has exactly one zero in this circle. Indeed, $\alpha$ is simple, the triangle inequality excludes zeros inside $\alpha$, the preceding circle minimum excludes any other on its boundary, and no circle of radius in $(\alpha,r]$ carries a zero. Rouché's theorem therefore gives exactly one zero of $D$ in $|z|<x$, the simple zero $s$. Its coefficient contribution is $-s^{-n}/(sD_z(s,t))>0$, since $D_z(s,t)=C(s)T'(s)<0$. The same single-pole estimate is valid at $t=0$ with $s=\alpha$. In a small neighborhood of each such real parameter we may keep the contour fixed, and the ratio of the pole radius to the contour radius stays below one. A finite cover gives eventual positivity uniformly on each compact subinterval of $(t_c,0]$. For $t\ge0$ positivity follows from the coefficients and the constant term.

At $t=t_c$ there is a double zero at $r$. There is none inside $r$: any interior zero would persist, counted with multiplicity on a small surrounding circle, for $t\downarrow t_c$, whereas $s\to r$ and $s$ is the only zero inside every fixed radius between $s$ and $r$. Equivalently, for every fixed $y<r$, the circles chosen above enclose $|z|\le y$ and their unique zero eventually lies beyond $y$. On $|z|=r$ the strict circle minimum excludes every other zero. Choose $R>r$ with exactly this double zero in $|z|\le R$. The same contour separates its two continuations for nearby parameters, and the contour part of $[z^n]D^{-1}$ is uniformly $O(R^{-n})$, as is its first parameter derivative. This bound follows by differentiating the Cauchy integral on $|z|=R$.

For real $v>0$ small and $t=t_c+v^2$, these two poles are $s_\pm=r\pm bv+O(v^2)$. This follows by analytically inverting $(z-r)\sqrt{(T(z)-t_c)/(z-r)^2}$ near $r$, with the positive square root at $r$. Their amplitudes $K_\pm=-1/(s_\pm D_z(s_\pm,t))$ have $K_->0$, $K_+<0$ and opposite leading terms of size $1/(r C(r)T''(r)bv)$. Thus $\log(s_+/s_-)\ge c v$ and $\log(|K_+|/K_-)=O(v)$. For all large $n$, uniformly down to $v=0$, their combined contribution for $v>0$ is at least

$$c' s_-^{-n}\frac{1-e^{-cnv/2}}v.$$

On a sufficiently small fixed interval $0<v\le v_0$ this dominates the contour error, also in the limit $v\to0$. Together with the compact-interval argument, this proves $O_n(t)>0$ on $[t_c,\infty)$ for all sufficiently large $n$.

## Counting and interlacing the roots below the endpoint

For $t=t_c-h^2$, $0<h\le h_0$, analytic inversion gives conjugate poles $z_+(h)=r+ibh+O(h^2)$ and $z_-(h)=\overline{z_+(h)}$. Write $z_+=\rho e^{i\phi}$ and its amplitude $-1/(z_+D_z)=iL(h)/h$. Here $L$ extends analytically to $0$ with $L(0)=1/(rC(r)T''(r)b)>0$. Write $L=|L|e^{i\delta}$, taking $\phi(0)=\delta(0)=0$. Shrink $h_0$ so that $\phi'>0$, $\phi(h_0)<\pi/2$, $L$ never vanishes and $\rho/R\le\sigma<1$. Summing the two pole contributions gives

$$\frac{h\rho^n}{2|L|}\frac{O_n(t_c-h^2)}{n!}
=\sin\psi_n(h)+E_n(h),\qquad \psi_n=n\phi-\delta.$$

Uniformly on $[0,h_0]$, $E_n=O(h\sigma^n)$ and $E_n'=O((n+1)\sigma^n)$, by the fixed-contour bounds and differentiation of the normalization. Here $\psi_n'\ge c n$ for large $n$. Outside the windows $|\psi_n-k\pi|<\pi/6$ the sine is bounded away from zero. Inside each full window, the derivative of the sine has constant sign and magnitude at least $cn\sqrt3/2$, hence exactly one simple zero occurs, with $\psi_n=k\pi+O(\sigma^n)$. The half-window at zero has only the artificial zero from the prefactor $h$. Each assertion follows also at the window endpoints from the opposite signs there.

Choose $0<\eta_j<\phi(h_0)/(2\pi)$. The windows through $\lfloor\eta_j n\rfloor+2$ are full for large $n$. At the $k$th true zero, $\psi_{n+1}=\psi_n+\phi(h)$, where $c'/n\le\phi(h)<\pi/2$: the lower bound follows from $k\ge1$, bounded $\delta'$ and $\phi'(0)>0$. This phase lies strictly after the $k$th zero and before the $(k+1)$st zero of row $n+1$, since the exponential phase errors are smaller than $c'/n$. The map $h\mapsto t_c-h^2$ reverses the ordering, yielding the claimed inequalities. For fixed $k$, $\phi(h)=(b/r)h+O(h^2)$ and $\delta(h)=O(h)$ give $h=k\pi r/(bn)+O(n^{-2})$. Squaring gives the stated edge spacing.

## Relation to the literature

The classical two-dominant-term mechanism is described by Beraha, Kahane and Weiss. Here the denominator contains $e^z$, and the circle bound identifies the actual two nearest poles at the critical parameter. The weighted renewal interlacing theorem of Ahlberg and Alexandersson treats $1/(1-zR(tz^\ell))$ with a real-rooted polynomial seed. The block-size threshold assigns the same power of $t$ to every block of size at least $j$. Jalowy, Kabluchko and Marynych study ordinary Fubini polynomials weighted by **all** blocks. None of these sources gives the asserted threshold result in the form above. [Beraha–Kahane–Weiss](https://pmc.ncbi.nlm.nih.gov/articles/PMC388687/) · [Weighted renewal theorem](https://www.symmetricfunctions.com/realRootedInterlacing.htm) · [Ordinary Fubini zeros](https://link.springer.com/article/10.1007/s00365-026-09775-2)

The standard-library [finite check](check_edge.py) reconstructs the integer polynomials by first-block decomposition. It certifies the three largest real roots by disjoint rational sign brackets and a Descartes upper bound counting multiplicity, then orders those brackets across consecutive rows. This checks 48 extreme roots at thresholds 2, 3, 5 and 8 and row lengths 96, 97, 192 and 193. The general theorem follows from the pole argument above.
