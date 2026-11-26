# Wang–Yang’s Eulerian square conjecture

Every fixed minor pattern, of arbitrary order and with independently specified row and column gaps, has a strictly positive determinant after all its indices are translated sufficiently far along the main diagonal. Its normalized determinant has an explicit positive leading term, even when the indices are adjacent.

Use $E(a,b)$ for the number of permutations with $a$ ascents and $b$ descents. Fix integer offsets $a_0<\cdots<a_{r-1}$ and $b_0<\cdots<b_{r-1}$. Define
```math
 K_N(a,b)=\frac{E(N+a,N+b)E(N,N)}{E(N+a,N)E(N,N+b)},\qquad M=2N+2.
```
Write $D=r(r-1)/2$ and $\Delta(a)=\prod_{i<j}(a_j-a_i)$, with analogous notation for $b$. Then
```math
 \det[K_N(a_i,b_j)]_{i,j=0}^{r-1}
 \sim \frac{\Delta(a)\Delta(b)}{\prod_{j=0}^{r-1}j!}\left(\frac4M\right)^D.
```
All normalizing row and column factors are positive. Thus the corresponding minor in the original matrix is eventually strictly positive. This treats a region complementary to the [spacing theorem](sparse-minors.md), which imposes increasing gaps. [Wang–Yang, Conjecture 4.3](https://cfc.nankai.edu.cn/_upload/article/files/ca/07/264e89bc4d9bb418a6d91d482b90/ef62459f-bec2-470d-8199-b57a790de20a.pdf)

## Highest-degree parts of the local expansion

Take a common integer shift of all offsets, absorbed into $N$, so that $a_i,b_j$ are nonnegative for the expansion below. For clarity the argument first proves the expansion at arbitrary nonnegative offsets, and then explains the original normalization for negative offsets. Put $s=a+b$, $d=(b-a)/2$. If $p_m$ is the density of the sum of $m$ independent uniform variables on $[0,1]$, the cardinal-spline identity gives
```math
 E(N+a,N+b)=\Gamma(M+s)\,p_{M+s}((M+s)/2+d).
```
The factor $\Gamma(M+s)/(\Gamma(M)M^s)$ has an expansion in $1/M$ whose coefficient of order $k$ has total degree at most $2k$ in $a,b$, with degree-$2k$ part $(s^2/2)^k/k!$. Indeed it is $\prod_{j=0}^{s-1}(1+j/M)$. In the logarithm, the coefficient at order $\ell$ is a constant times $\sum_{j=0}^{s-1}j^\ell$, of degree $\ell+1$. The only terms reaching degree $2k$ after exponentiation use $k$ copies of the first coefficient, whose quadratic part is $s^2/2$. For fixed negative integral $s$ the same calculation uses the inverse product and negatively oriented finite sums. The Faulhaber polynomials for the sums are valid for all integers. Thus the expansion applies directly with either sign, including the original normalization. [Eulerian spline identity](https://arxiv.org/abs/0808.2349)

After dividing the density by its leading constant times $M^{-1/2}$, the coefficient of order $M^{-k}$ likewise has degree at most $2k$, with top part $(-6d^2)^k/k!$. To see this, Fourier inversion after scaling gives, apart from the common constant and $M^{-1/2}$,
```math
 \int_{\mathbb R}\operatorname{sinc}\!\left(\frac{u}{2\sqrt M}\right)^{M+s}\cos(du/\sqrt M)\,du,
 \qquad \operatorname{sinc}(x)=\sin(x)/x.
```
The leading Gaussian is $\exp(-u^2/24)$. In the expansion of the sinc factor, every power of $s$ costs at least one factor of $1/M$, because $\log\operatorname{sinc}(u/(2\sqrt M))$ starts at order $1/M$. The cosine contributes degree $2j$ in $d$ at order $j$. Consequently only the degree-$2k$ term of the cosine against the leading Gaussian attains total degree $2k$. Its normalized integral is $(-1)^k d^{2k}12^k/(2^k k!)$, the even-moment formula for a centered Gaussian of variance 12.

These expansions may be integrated to any fixed order $k$. On $|u|\le M^\epsilon$, take $\epsilon>0$ sufficiently small for that order. Taylor's theorem for $\log\operatorname{sinc}$, the exponential and the cosine bounds the integrated remainder by $O(M^{-k-1})$, since each remainder is bounded by $M^{-k-1}$ times a fixed polynomial in $|u|$ times $\exp(-c u^2)$. On $M^\epsilon<|u|\le c_0\sqrt M$ use $|\operatorname{sinc}(u/(2\sqrt M))|^{M+s}\le\exp(-c u^2)$. On the complement, the absolute value of sinc is bounded by a fixed number less than one and its square has finite integral. These bounds apply to each of the finitely many offsets under consideration.

Products and inverses of formal expansions with constant one preserve the bound $2k$ on the degree of the $k$th coefficient. Taking only the degree-$2k$ parts commutes with those operations. Thus for the two factors together the top parts are the coefficients of $\exp((s^2/2-6d^2)/M)$. Its quadratic numerator is $-a^2-b^2+4ab$. The row and column normalization deletes the pure squares and every offset-independent factor. We obtain an expansion $K_N(a,b)\sim\sum_{k\ge0}M^{-k}P_k(a,b)$ with $\deg P_k\le2k$ and top part $(4ab)^k/k!$.

## Divided differences

Apply successive Newton divided differences to the rows on the lists $(a_0,\ldots,a_i)$ and to the columns on $(b_0,\ldots,b_j)$. This divides the determinant by $\Delta(a)\Delta(b)$. The entry indexed by $i,j$ annihilates every monomial whose row degree is below $i$ or column degree below $j$. Multiply that entry by $M^{(i+j)/2}$, a row and column scaling whose determinant factor is $M^D$. Terms with $2k<i+j$ vanish by the degree bound. At $2k=i+j$, only the top part can survive, and that monomial has degree $k$ in each coordinate. It vanishes unless $i=j=k$, in which case its divided difference is $4^k/k!$. The terms of higher order tend to zero after scaling, using the expansion to order at least $r$. The scaled matrix converges to a diagonal matrix with these positive entries. Its determinant gives the asserted asymptotic.

The [finite check](check_diagonal.py) builds Eulerian entries from their integer recurrence and uses fraction-free determinants before normalization. Across four fixed patterns of orders two through four, the exact ratios to the leading term at $N=400$ lie between $0.99$ and $1.01$.

## All slopes in the interior

The same positivity holds uniformly when the center $(A,B)$ tends to infinity with its slope in any fixed compact subinterval of $(0,\infty)$. Put $M=A+B+2$ and $p=(B+1)/M$ and define $K_{A,B}$ by replacing the row origin $N$ by $A$ and the column origin $N$ by $B$ in the previous normalization. Let $\sigma_p^2$ be the variance of the exponential tilt of the uniform distribution on $[0,1]$ with mean $p$. Then uniformly for $p$ in any compact subinterval of $(0,1)$,
```math
 \det[K_{A,B}(a_i,b_j)]\sim\frac{\Delta(a)\Delta(b)}{\prod_{j=0}^{r-1}j!}
 \left(\frac{1+p(1-p)/\sigma_p^2}{M}\right)^D.
```
In particular a counterexample sequence with fixed row and column gaps and growing indices cannot stay in such a cone.

Here are the changes in the proof. Write $Z(\tau)=\int_0^1 e^{\tau x}dx$. The tilted density $e^{\tau x}/Z(\tau)$ has mean $(\log Z)'(\tau)$ increasing strictly from zero to one, with derivative $(\log Z)''(\tau)=\sigma_p^2>0$. Choose $\tau$ for the stated $p$. Tilting the $M+s$ independent variables multiplies the original density formula by a factor which, when one recovers the original density, is $Z(\tau)^{M+s}e^{-\tau(Mp+b)}$. This splits into row, column and constant factors. It cancels from $K_{A,B}$.

The tilted sum is evaluated at its mean plus $d=b-ps$. Let $\phi_p(v)$ be the characteristic function of the centered tilted variable. In the scaled Fourier integral, the integrand is $\phi_p(u/\sqrt M)^{M+s}\exp(-idu/\sqrt M)$. Its leading Gaussian is $\exp(-\sigma_p^2u^2/2)$. Taylor expansion in $M^{-1/2}$ is valid to every fixed order, uniformly on the indicated compact parameter set. Indeed $\tau$ is bounded and the variances are bounded away from zero there. The log characteristic functions have uniform Taylor bounds at zero. Away from zero, the modulus is strictly less than one uniformly on compact frequency sets, and integration by parts in the explicit tilted density gives the uniform tail bound $O(1/|v|)$. The same three integration regions used above thus justify the remainders. Odd powers of $M^{-1/2}$ integrate to zero by parity: a contribution at an odd index is an odd polynomial in $u$ times the centered Gaussian.

At order $M^{-k}$ the coefficient still has total degree at most $2k$ in $a,b$. A factor involving $s$ costs at least two half-powers of $M^{-1/2}$ since $\log\phi_p$ starts at degree two. The offset-independent higher cumulants cost half-powers without raising the offset degree. Only the term of degree $2k$ from $\exp(-idu/\sqrt M)$ against the leading Gaussian can attain offset degree $2k$. Its normalized integral is $(-d^2/(2\sigma_p^2))^k/k!$. Combine with the factorial quadratic $s^2/2$ and remove the pure row and column terms. The surviving mixed quadratic is $(1+p(1-p)/\sigma_p^2)ab$. Applying the same divided differences yields the formula. Its leading factor is bounded away from zero on the compact set, giving uniform strict positivity.

The same checker computes six off-diagonal determinants at three different slopes by exact integer arithmetic. Only the comparisons with the limiting tilted variances use floating point. At $M=900$ the three normalized ratios are approximately $0.98943$, $0.99943$ and $0.99722$.
