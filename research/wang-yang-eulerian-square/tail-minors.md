# Wang–Yang’s Eulerian square conjecture

**Theorem.** For every fixed order $r$, there is an integer $T_r$ such that each of the following infinite rectangles of the Eulerian square is strictly totally positive of order $r$:
```math
 [E(a,b)]_{a\ge T_r,\ b\ge0},\qquad [E(a,b)]_{a\ge0,\ b\ge T_r}.
```
Both index sets in a minor can have arbitrary gaps. Consequently full positivity through any fixed order in Wang and Yang's original matrix is equivalent to checking finitely many solid minors in its initial corner. The argument establishes existence of the threshold; the estimates here do not supply a practical numerical value for it. The full conjecture quantifies over all orders. [Wang–Yang, Conjecture 4.3](https://cfc.nankai.edu.cn/_upload/article/files/ca/07/264e89bc4d9bb418a6d91d482b90/ef62459f-bec2-470d-8199-b57a790de20a.pdf)

We prove that every fixed offset pattern has positive determinant as $A+B\to\infty$ without any restriction on the aspect ratio. It suffices to treat nonnegative offsets $a_i,b_j$, translating each origin to its smallest index. We use the [tilted local expansion](diagonal-minors.md) and its notation $M=A+B+2$, $p=(B+1)/M$, $s=a+b$, $d=b-ps$. By transposition we may assume $p\le1/2$ (or simply swap the two lists of offsets). Fix the order and both lists for the remainder of the proof.

## The range down to logarithmically small slopes

For any fixed constant $C>1$, the determinant asymptotic of the tilted expansion continues to hold uniformly for $p\ge 1/(C\log M)$ and $p\le1/2$. We give the uniformity details since the variances of the original tilts now can tend to zero.

Write $\tau=-T\le0$ for the tilting parameter. If $T>0$ the mean is $p=1/T-1/(e^T-1)<1/T$, so $T\le C\log M$ in this range. For $T\ge1$, the variable $TX$ under the tilt has density $e^{-y}/(1-e^{-T})$ on $[0,T]$. Its mean and variance converge to those of the mean-one exponential distribution. The variance is bounded above and away from zero for all $T\ge1$ by continuity. On $0\le T\le1$, the unscaled tilt has the same variance bounds. Thus $1/\sigma_p=O(1+T)=O_C(\log M)$.

Standardize each tilted variable by subtracting its mean and dividing by its standard deviation; denote its characteristic function by $\chi_T$. These standardized laws have uniformly bounded exponential moments in a fixed neighborhood of zero, by the truncated-exponential description and the variance bounds. Their log characteristic functions therefore have uniform Taylor remainders on a fixed neighborhood of zero (the characteristic functions there are uniformly bounded away from zero). The laws form a continuous family on $0\le T\le\infty$ after adding the centered standardized exponential limit. For a fixed frequency annulus away from zero their moduli are uniformly below one: every member, including the limit, has a density and compactness gives uniformity. For all high frequencies their characteristic functions are uniformly $O(1/|u|)$, by integration of the exponential density or its uniformly bounded total variation in standardized coordinates.

The standardized Fourier integral in the [interior-slope calculation](diagonal-minors.md#all-slopes-in-the-interior) now uses $\chi_T(u/\sqrt M)^{M+s}$ and the factor $\exp(-i(d/\sigma_p)u/\sqrt M)$. Its leading Gaussian is $\exp(-u^2/2)$. The new parameter $d/\sigma_p$ is $O_C(\log M)$ for fixed offsets. For any fixed $L$, the resulting expansion through order $M^{-L}$ has remainder $O(M^{-L-1}(\log M)^{c_L})$, after removing the offset-independent density factor. Indeed on $|u|\le M^\epsilon$ one can take $\epsilon$ small in terms of $L$, use the uniform Taylor bounds above, expand through half-order $2L+1$, and integrate the remainder against a fixed Gaussian times a polynomial in $|u|$. Derivatives of the phase contribute at most fixed powers of $\log M$ and its odd half-orders integrate to zero. The two regions beyond $M^\epsilon$ have uniformly negligible tails by the characteristic-function bounds. Row and column normalization preserves expansions of this precision after increasing the log exponent: the normalized individual leading terms are one and all later coefficients at fixed offsets are polylogarithmically bounded.

Thus the coefficient at order $k$ has degree at most $2k$ in the offsets, and the degree-$2k$ part is $(c_pab)^k/k!$, where $c_p=1+p(1-p)/\sigma_p^2\ge1$. The coefficients of every fixed order are $O((\log M)^{O(1)})$ at the finitely many required offsets. After the divided differences and scalings $M^{(i+j)/2}$, the diagonal entries are $c_p^i/i!+O(M^{-1/2}(\log M)^{O(1)})$ and every off-diagonal entry is $O(M^{-1/2}(\log M)^{O(1)})$. Divide row $i$ by $c_p^i/i!$. This operation is uniformly bounded since $c_p\ge1$. The new matrix tends uniformly to the identity. This proves the determinant asymptotic and strict positivity in this entire range.

## The remaining thin rectangle

Let $D=r(r-1)/2$ for the order of this fixed pattern and take $C=6(D+3)$. Suppose $p<1/(C\log M)$. Set $x=B+b+1$. The explicit inclusion–exclusion formula for Eulerian numbers implies
```math
 E(A+a,B+b)=x^{M+s-1}(1+\delta_{a,b}),\qquad
 |\delta_{a,b}|\le (1+e^{-(M+s-1)/x})^{M+s}-1.
```
Indeed its terms other than the leading one, divided by that term, have absolute values $\binom{M+s}{j}(1-j/x)^{M+s-1}$ for $1\le j\le x$, with the endpoint contributing zero. Bound by the exponential and extend the binomial sum. As $x\le M/(C\log M)+O(1)$ the exponent $(M+s-1)/x\ge (C/3)\log M$ for large $M$. Therefore all the relative errors are $O(M^{1-C/3})=o(M^{-D})$.

The normalized leading entries are exactly $V_{a,b}=(1+b/(B+1))^a$. Their entries are uniformly bounded for the fixed offsets, so the determinant of the actual normalized matrix differs from $\det V$ by $o(M^{-D})$. For each fixed $B$, $\det V>0$ by the generalized Vandermonde determinant: the bases are increasing and positive and the increasing exponents are nonnegative integers. Equivalently the alternant is the positive ordinary Vandermonde times a Schur polynomial with nonnegative coefficients, nonzero at positive arguments. As $B\to\infty$, the binomial expansion and Cauchy–Binet give
```math
 \det V\sim (B+1)^{-D}\frac{\Delta(a)\Delta(b)}{\prod_{k=0}^{r-1}k!}.
```
The unique lowest-degree selection takes $k=0,\ldots,r-1$: its two determinants are $\det[\binom{a_i}{k}]=\Delta(a)/\prod k!$ and $\det[b_j^k]=\Delta(b)$. Combining the asymptotic with the finitely many bounded $B$ gives $\det V\gg(B+1)^{-D}\gg M^{-D}$ uniformly. The relative perturbations above cannot change its sign. This covers the thin rectangle even if the smaller index stays bounded.

## Passing to arbitrary gaps

We have proved eventual positivity as $A+B\to\infty$ for any fixed offset pattern. Apply it to consecutive rows and consecutive columns, for each of the finitely many orders $1,\ldots,r$. Thus for some $T_r$, every solid minor of order at most $r$ based at $(A,B)$ with $A+B\ge T_r$ is positive. Any finite subrectangle of either rectangle in the theorem has this property for its own solid minors. The Fekete–Schoenberg criterion states that a finite matrix is strictly totally positive of order $r$ if its contiguous minors through that order are strictly positive (for smaller rectangles use their maximal possible order). Arbitrary prescribed row and column sets fit inside such a finite consecutive subrectangle. This proves the assertion for both infinite rectangles. On the full square the only solid minors requiring a further check have starting indices $A+B<T_r$ and orders at most $r$. The same reasoning applies after deleting the zero-index row to match Wang and Yang's indexing. [Fekete–Schoenberg criterion, Theorem 2.2 of Choudhury–Kannan–Khare](https://math.iisc.ac.in/~khare/papers/sign-non-rev.pdf)
