# Nathanson’s linear-form Sidon systems conjecture

**True.** The unrestricted multiplicity-one lower bound asked in [Nathanson, *The Bose–Chowla argument for Sidon sets*, journal §6(i)–(iii)](https://www.theoryofnumbers.com/melnathanson/pdfs/nath2022-198.pdf#page=13) holds for every fixed arity and all nonzero integer coefficients, including any signs. This resolves all three questions at once. See also [arXiv v3, §6](https://arxiv.org/html/2104.12711v3#S6).

For a form $\varphi(x)=\sum_{i=1}^h c_i x_i$, let $F_{\varphi,g}(N)$ be the greatest $q$ for which there are sets $A_i\subseteq[1,N]\cap\mathbb Z$, each of size $q$, on whose Cartesian product each output occurs at most $g$ times. Write $F_\varphi=F_{\varphi,1}$. The coordinate sets are separate; no common-set claim is made.

We prove
\[
 \liminf_{N\to\infty}\frac{F_\varphi(N)}{N^{1/h}}
 \ \ge\ \left(\frac{\max_i |c_i|}{\min_i|c_i|}\right)^{1/h}\ \ge\ 1.
\]
In particular §6(iii) is true, §6(ii) needs no excluded primes, and §6(i) follows since multiplicity one is at most $h!$.

## Coefficient-adjusted place values

Put $b_i=|c_i|$. Relabel the coordinates so that $b_1=u=\min_i b_i$ and $b_h=v=\max_i b_i$. Put $L=\operatorname{lcm}(b_1,\ldots,b_h)$. Choose an integer $r\ge2$ divisible by $L$ and put
\[
 s_i=\frac{u r^{i-1}}{b_i},\qquad A_i=\{1+s_i j:0\le j<r\}.
\]
The steps are positive integers: $s_1=1$, and $b_i\mid r$ for $i>1$. For a positive coefficient, set $y_i=j$; for a negative coefficient, set $y_i=r-1-j$. Thus the value of the form is
\[
 K+u\sum_{i=1}^h r^{i-1}y_i,
 \qquad 0\le y_i<r,
\]
with $K$ independent of the digits. Dividing the variable part by $u$, the usual base-$r$ uniqueness recovers every $y_i$ and hence each original coordinate. Equivalently, successive remainders modulo $r$ recover the digits from left to right in increasing place value. The output set is the entire arithmetic progression $K+u[0,r^h-1]$.

For $r\ge v/u$, the largest step is $s_h$: for $i<h$ the ratio $s_h/s_i=(b_i/v)r^{h-i}$ is at least one. All coordinates therefore fit in $[1,N]$ if $r^h\le(v/u)(N-1)$. For each sufficiently large $N$, choose the largest multiple of $L$ at most $((v/u)(N-1))^{1/h}$. Its deficit is at most the fixed number $L$; it tends to infinity and has the required limiting ratio to $N^{1/h}$. This proves the assertion for all sufficiently large $N$, not just a subsequence.

Nathanson’s §3 already illustrates ordinary mixed radix with special weights. Here the base is chosen from a fixed divisibility progression and each coordinate's step absorbs its prescribed coefficient. The positional-number-system principle itself is classical.

## A sharper general lower bound and the exact bilinear limit

Let $u\le v$ be the two largest absolute coefficients, counting multiplicity, and let $g_0=\gcd_i |c_i|$. The lower constant in fact satisfies
\[
 \liminf_{N\to\infty}\frac{F_\varphi(N)^h}{N}\ge\frac{u+v}{g_0}.
\]
Any multiplicity-one system satisfies
\[
 F_\varphi(N)^h\le\frac{\sum_i |c_i|}{g_0}(N-1)+1.
\]
This follows because the distinct outputs lie in a single residue class modulo $g_0$ in an interval of length at most $(N-1)\sum_i |c_i|$. In arity two the bounds agree asymptotically.

For the lower bound, divide the coefficients by $g_0$ and reduce negative coefficients to positive ones by reflecting the corresponding coordinate sets in $[1,N]$. Neither operation changes the number of representations. Relabel so that the normalized positive coefficients $b_i$ have $b_{h-1}=u/g_0$ and $b_h=v/g_0$. Put $M=\operatorname{lcm}_i b_i$. Assign each maximal prime power dividing $M$ to any coordinate whose coefficient is coprime to that prime, which is possible by the gcd-one condition. Let $M_i$ be the product of the prime powers assigned to $i$ (empty products equal one). Their product is $M$, they are pairwise coprime, and $\gcd(b_i,M_i)=1$.

Fix $J\ge1$ and $0\le D<2^J$. In the two last coordinates, let $U_{h-1}$ consist of all subset sums of the binary place values present in $D$, and let $U_h$ use the complementary bit positions among $0,\ldots,J-1$. Set $U_i=\{0\}$ for the other coordinates and $P_i=|U_i|$. Every integer in $[0,2^J-1]$ uniquely determines all upper digits $y_i\in U_i$ by the bits it uses. Also $\prod_i P_i=2^J$, $\max U_{h-1}=D$ and $\max U_h=2^J-1-D$.

For arbitrarily large integers $q$ divisible by each $M_i P_i$, let $r_i=q/(M_i P_i)$, $R_i=\prod_{j<i}r_j$, and $T=\prod_i r_i=q^h/(M2^J)$. Use the coordinate sets
\[
 A_i=\left\{\frac{M}{M_i}d_i+\frac{M}{b_i}(R_i x_i+T y_i):
 0\le d_i<M_i,\quad 0\le x_i<r_i,\quad y_i\in U_i\right\}.
\]
All steps are integral. The residue of the weighted output modulo $M_i$ recovers $d_i$, since all other coordinates contribute zero and $b_i(M/M_i)$ is invertible there. If $M_i=1$ the digit is predetermined. Subtract the known low contributions and divide by $M$. The result is
\[
 \sum_i R_i x_i+T\sum_i y_i.
\]
Its remainder modulo $T$ recovers the mixed-radix digits $x_i$, and its quotient recovers all binary upper digits. This proves unique representation. It also proves that each coordinate map is injective: if two triples of digits gave the same coordinate value, fixing all other digits would give an equal output for distinct digit tuples. Thus each coordinate has $M_i r_i P_i=q$ elements.

For fixed $J$, the $d_i$ contribution has bounded size, and each lower mixed-radix contribution for $i<h$ is $O_{\varphi,J}(q^{h-1})$. In coordinate $h$, the largest lower mixed-radix contribution equals $(M/b_h)(T-R_h)$. Combining it with the binary contributions gives
\[
 \operatorname{diam}(A_{h-1})
   =\frac{D}{2^J b_{h-1}}q^h+O_{\varphi,J}(q^{h-1}),\qquad
 \operatorname{diam}(A_h)
   =\frac{2^J-D}{2^J b_h}q^h+O_{\varphi,J}(q^{h-1}).
\]
The other diameters are $O_{\varphi,J}(q^{h-1})$. Both formulae use $MT=q^h/2^J$ and the fact that the minima are zero. Translate each set by one before reflecting the negative coordinates.

Write $\beta$ for the larger of the two leading diameter coefficients. For every fixed $\eta>0$ and all large $N$, the largest allowed $q$ at most $((N-1)/(\beta+\eta))^{1/h}$ gives all coordinate sets in $[1,N]$. The rounding loss is bounded because the allowed $q$ form a fixed arithmetic progression. Hence $\liminf F_\varphi(N)^h/N\ge1/(\beta+\eta)$. Let $\eta\downarrow0$ and approximate $b_{h-1}/(b_{h-1}+b_h)$ by $D/2^J$. Then $\beta$ tends to $1/(b_{h-1}+b_h)$ and the stated bound follows. In particular, for $h=2$,
\[
 \lim_{N\to\infty}\frac{F_\varphi(N)^2}{N}
 =\frac{|c_1|+|c_2|}{\gcd(|c_1|,|c_2|)}.
\]
No exact higher-arity leading constant is claimed. The resolution of the posed questions is for all arities.
