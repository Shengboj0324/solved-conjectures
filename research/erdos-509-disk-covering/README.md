The extension tex_math_single_backslash is not supported for gfm
# Erdős–Herzog–Piranian disk-covering conjecture

[Erdős Problem #509](https://www.erdosproblems.com/509) asks whether the closed unit lemniscate of every monic polynomial has a finite disk cover whose radii sum to at most 2. For collinear zeros, the minimum sum is exactly **half the length of the real sublevel set**, after rotating the line to the real axis. The sharp worst-case sum in degree $n$ for this class is $2^{1-1/n}$. The result covers disconnected lemniscates in every degree. An explicit strip of nonzero width around this class also satisfies the original bound.

## Exact cover for collinear zeros

Let $Q(z)=\prod_{j=1}^n(z-x_j)$ with each $x_j$ real, and let $I=\{t\in\mathbb R:|Q(t)|\le1\}$. This is compact and is a finite union of disjoint closed intervals $[a_i,b_i]$. Every component contains a root: otherwise $\log|Q(t)|$ is strictly concave between the nearest roots, and cannot have a sublevel component strictly inside that gap. On either infinite outer gap, $|Q|$ is monotone away from the roots. Thus the number of intervals $m$ is at most $n$, and none of them is a singleton.

For $z=t+iy$, we have $|Q(z)|\ge|Q(t)|$, so every point of the complex sublevel set projects into $I$. Take one interval $[a,b]$ and write $z_0=t+i\sqrt{(t-a)(b-t)}$ for the point over $t\in[a,b]$ on its diameter semicircle. When $\lambda=(b-t)/(b-a)$, the circle identity is
\[
|z_0-x_j|^2=\lambda|a-x_j|^2+(1-\lambda)|b-x_j|^2.
\]
Both endpoints have modulus $|Q|=1$. Weighted AM–GM applied to the identity, then multiplied over the roots, gives $|Q(z_0)|\ge1$. Reflection gives the same lower bound on the opposite semicircle. For fixed $t$, $|Q(t+iy)|$ is strictly increasing in $|y|$ wherever the product is already positive. It follows that every point projecting into $[a,b]$ belongs to the closed disk of diameter $[a,b]$.

These disks have radius sum $|I|/2$. Conversely, projecting any disk cover onto the real axis covers $I$ by intervals whose total length is at most twice the sum of the radii. This proves optimality of the explicit cover for every collinear-root polynomial.

## Sharp uniform bound in each degree

Here is the one-dimensional Pólya inequality used to estimate the exact cost. If a monic polynomial $R$ has degree $n$ and $|R|\le1$ on a compact real set of length $\ell>0$, let $s_0<\cdots<s_n$ be the extrema of $T_n$ affinely scaled to $[-\ell/2,\ell/2]$. Choose quantile points $t_i$ in the compact set at the respective length coordinates $s_i+\ell/2$, taking its endpoints for the extreme coordinates. Then $t_j-t_i\ge s_j-s_i$ for $j>i$, since length between two real points cannot exceed their distance. Lagrange interpolation gives
\[
1
=\left|\sum_{i=0}^{n}\frac{R(t_i)}{\prod_{j\ne i}(t_i-t_j)}\right|
\le \sum_{i=0}^{n}\frac{1}{\big|\prod_{j\ne i}(s_i-s_j)\big|}
=2^{n-1}(2/\ell)^n.
\]
The final equality follows by interpolating $T_n(2t/\ell)$ at its extrema: the alternating values have the same signs as the denominator products. Thus $\ell\le 2^{2-1/n}$.

Now take $Q(z)=T_n(z/a)$ with $a=2^{1-1/n}$, so $Q$ is monic. Its real unit sublevel set is $[-a,a]$, because $|T_n(x)|>1$ for real $|x|>1$. The exact-cover formula attains radius sum $a$, proving sharpness.

## Roots in a strip

Translate and rotate the strip so the roots are $x_j+iy_j$ with $|y_j|\le h$. Multiplication by a complex unit restores monicity after a rotation without changing any modulus. Write $P(z)=\prod_j(z-x_j-iy_j)$ and retain $Q(z)=\prod_j(z-x_j)$. For any $z=t+iy$, set $y'=\operatorname{sgn}(y)\max(|y|-h,0)$. Then $|y-y_j|\ge |y'|$ for each $j$, and consequently
\[
|P(t+iy)|\ge |Q(t+iy')|.
\]
Hence the unit lemniscate of $P$ is contained in the vertical $h$-thickening of the unit lemniscate of $Q$. Enlarge each optimal diameter disk for $Q$ by $h$ to obtain a cover for $P$ of total radius at most
\[
\frac12\big|\{t\in\mathbb R:|Q(t)|\le1\}\big|+mh
\ \le\ 2^{1-1/n}+mh,\qquad m\le n.
\]
In particular the conjectured bound holds for every root configuration in a strip of half-width at most $(2-2^{1-1/n})/n$. No bound on the horizontal spread or number of disconnected components is needed. If $Q$ has fewer components, the actual criterion uses $m$ in place of $n$.

## Scope and provenance

The sharp real-length inequality is classical Pólya; it is proved above only to make the cover calculation self-contained. [Pommerenke's 1961 paper](https://doi.org/10.1307/mmj/1028998561) is the source for the connected case of the general problem and for the many-long-component obstruction to summing general individual radii. [Dubickas and Pritsker](https://math.okstate.edu/people/igor/DubickasPritsker.pdf) cite Pommerenke for an *internal* disk description of real-rooted lemniscates. That is distinct from the finite outer diameter-disk construction above. The exact collinear-cover argument and the strip extension were not located in the sources checked; no claim of priority beyond that search is made. The arbitrary-complex-root statement is not proved here. See [the current source and claim audit](https://erdosproblems.ai/wiki/problems/polynomials/E0509) and [tracking issue #839](https://github.com/1337isnot1337/solved-conjectures/issues/839).
