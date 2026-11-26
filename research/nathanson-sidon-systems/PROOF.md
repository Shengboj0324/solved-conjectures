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

## Removing the smallest-coefficient loss

In fact the lower constant improves to $(v/g_0)^{1/h}$, where $g_0=\gcd_i|c_i|$. Divide the form by $g_0$ and reflect negative-coordinate sets in the interval $[1,N]$, neither of which changes injectivity. Write the resulting positive coefficients as $b_i$, now of gcd one, put $v=\max b_i=b_h$, and put $M=\operatorname{lcm}_i b_i$.

Assign each maximal prime power dividing $M$ to a coordinate whose coefficient is coprime to that prime; the gcd-one condition ensures a choice. Let $M_i$ be the product of the prime powers assigned to coordinate $i$. These products are pairwise coprime, their product is $M$, and $\gcd(b_i,M_i)=1$. Empty products equal one.

Take $q$ an arbitrarily large multiple of $M$, put $r_i=q/M_i$ and $R_i=\prod_{j<i}r_j$, and use, before translating to positive integers,
\[
 A_i=\left\{\frac{M}{M_i}d_i+\frac{M}{b_i}R_i x_i:
                0\le d_i<M_i,\ 0\le x_i<r_i\right\}.
\]
The residue of the weighted output modulo $M_i$ recovers $d_i$, because all other contributions are multiples of $M_i$ and $b_i M/M_i$ is invertible there. For $M_i=1$ the digit is predetermined. In particular each coordinate map is also injective in its own digits. Once the low contributions are subtracted, division by $M$ gives $\sum_i R_i x_i$, with unique mixed-radix digits $x_i$. Each coordinate has size $M_i r_i=q$ and the weighted representation is unique.

The low term in each coordinate is bounded in terms of the fixed form. All high contributions for $i<h$ have size $O_\varphi(q^{h-1})$, and for $i=h$ the high contribution is at most $M R_h r_h/v=q^h/v$. Therefore all coordinate sets, translated by one and reflected as needed, lie in $[1,N]$ if $q^h\le v(N-K)$, for a sufficiently large fixed $K$ and all large $N$. The multiples of $M$ have bounded spacing. Restoring the gcd gives the claimed stronger lower constant.

## A sharp bilinear consequence

When $h=2$, the limit is in fact
\[
 \lim_{N\to\infty}\frac{F_\varphi(N)^2}{N}
   =\frac{|c_1|+|c_2|}{\gcd(|c_1|,|c_2|)}.
\]
More generally, writing $g_0=\gcd_i b_i$, any multiplicity-one system satisfies $q^h\le (\sum_i b_i/g_0)(N-1)+1$: its outputs lie in a single residue class modulo $g_0$ in an interval of length at most $(N-1)\sum_i b_i$. This proves the upper bound for the displayed bilinear limit.

For the lower bound, divide by the gcd and replace negative coefficients by positive ones via the reflection $x\mapsto N+1-x$ on the affected coordinates. Write the resulting coprime coefficients as $u,v>0$ and put $M=uv$. Fix $J\ge1$ and an integer $D$ with $0\le D<2^J$. Let $U$ be the set of binary sums of subsets of the bit positions present in $D$, and let $V$ use the complementary positions in $0,\ldots,J-1$. Then every number in $[0,2^J-1]$ has exactly one representation $x+y$ with $x\in U,y\in V$. Put $P=|U|$ and $Q=|V|$; $PQ=2^J$, $\max U=D$, and $\max V=2^J-1-D$.

Let $q$ run over multiples of $\operatorname{lcm}(vP,uQ)$ and put $a=q/(vP)$ and $b=q/(uQ)$. Use the coordinate sets
\[
 \begin{split}
 A&=\{d+v(i+abx): 0\le d<v,\ 0\le i<a,\ x\in U\},\\
 B&=\{e+u(aj+aby): 0\le e<u,\ 0\le j<b,\ y\in V\}.
 \end{split}
\]
Each set has size $q$: first recover $d$ modulo $v$ or $e$ modulo $u$ respectively, then recover the lower and upper digits in the quotient. A value of $uA+vB$ has the form
\[
 ud+ve+M(i+aj+ab(x+y)).
\]
Its residue modulo $v$ recovers $d$, and modulo $u$ recovers $e$ (including the trivial one-choice case of a modulus equal to one). Subtract $ud+ve$ and divide by $M$. Reduction modulo $a$ recovers $i$; division by $a$ and reduction modulo $b$ recovers $j$; the remaining quotient recovers $x+y$, which determines $x,y$. This proves injectivity.

Since $Mab=q^2/2^J$, the diameters are
\[
 \operatorname{diam}(A)=\frac{D}{2^J u}q^2+O_{u,v,J}(q),\qquad
 \operatorname{diam}(B)=\frac{2^J-D}{2^J v}q^2+O_{u,v,J}(q).
\]
Indeed their exact maxima are $v-1+v(a-1+abD)$ and $u-1+u(a(b-1)+ab(2^J-1-D))$; both minima are zero. Translate by one to make the sets positive. Let
\[
 \beta=\max\left\{\frac{D}{2^J u},\frac{2^J-D}{2^J v}\right\}.
\]
For any fixed $\eta>0$, the largest allowed $q$ no larger than $\sqrt{(N-1)/(\beta+\eta)}$ gives both diameters at most $N-1$ for all large $N$. The loss from the multiple-of condition is bounded independently of $N$. Thus $\liminf F_\varphi(N)^2/N\ge1/(\beta+\eta)$. First let $\eta\downarrow0$, then choose $D/2^J$ tending to $u/(u+v)$. This gives $\liminf\ge u+v$ as desired. Undo the gcd normalization and any sign reflections.

The bilinear calculation is a supplementary theorem, not a restriction of the solution of §6. No exact higher-arity leading constant is claimed.
