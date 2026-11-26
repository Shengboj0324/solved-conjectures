# Exact prime-power factorizations cannot solve the square-mean basis problem

Companion to [Erdős #1192](https://www.erdosproblems.com/1192) and [the cyclic transfer and construction](README.md). This is an obstruction to an exact-tiling route, **not** a negative answer to #1192.

Let \(M=p^n\), with \(p\) prime and \(n\ge1\). Suppose \(A_1,\ldots,A_r\subseteq\mathbb Z/M\mathbb Z\) give an **exact colored factorization**: addition maps \(A_1\times\cdots\times A_r\) bijectively onto the group. Write \(B=\bigcup_i A_i\). Then for fixed \(r\ge2\),
\[
E_r(B)\gg_r Mnp \gg_r M\log M.
\]
If \(r\mid n\), the stronger lower bound \(E_r(B)\gg_r M(n/r)p^{r-1}\) holds. For \(r\mid n\), \(p>r\), the random carry-compatible construction in the companion note attains this last order. Thus even choosing the prime to grow with the modulus cannot avoid an unbounded loss in this entire class.

## 1. All such tiles have a digit ownership schedule

Let \(F_i(X)\in\mathbb Z[X]\) be the mask polynomial of \(A_i\), using representatives in \([0,M-1]\). Write \(|A_i|=p^{D_i}\); the exact factorization implies \(\sum_iD_i=n\). At every order \(p^k\) with \(1\le k\le n\), taking the Fourier transform of the factorization shows that some factor is zero at a primitive \(p^k\)-th root. Such vanishing means the irreducible polynomial \(\Phi_{p^k}\) divides \(F_i\). If \(F_i\) vanishes at \(d\) different orders, their product divides \(F_i\), and evaluating it at \(1\) gives \(p^d\mid |A_i|\). Taken over all factors the upper limits \(D_i\) sum to exactly \(n\). Thus each order \(k\) has exactly one owner, and \(A_i\) owns \(D_i\) levels.

At depth \(k\), assign to each residue modulo \(p^k\) the number of points above it. At an owned level, all \(p\) children of each parent at depth \(k-1\) have equal counts. Indeed the degree-\(<p^k\) polynomial formed from the projected counts is still divisible by
\(\Phi_{p^k}(X)=1+X^{p^{k-1}}+\cdots+X^{(p-1)p^{k-1}}\).
Its quotient has degree less than \(p^{k-1}\), giving exactly these equal coefficients.

Let \(d_i(k)\) denote the number of owned levels through depth \(k\). Every count at depth \(k\) is a multiple of \(p^{D_i-d_i(k)}\). This follows backwards from depth \(n\): for a step from \(k\) to \(k-1\), sum over children without changing the claimed divisibility if it is unowned; if owned, multiply one child's count by \(p\). At the root the count equals the smallest possible positive multiple \(p^{D_i}\). Moving downward, every nonempty node therefore has the smallest possible positive count at its depth. An owned level branches into all \(p\) children; an unowned level branches into exactly one child. In particular the probability measure on \(A_i\bmod p^k\) is uniform on \(p^{d_i(k)}\) points. The argument includes arbitrary, nonperiodic schedules and arbitrary dependence on the already chosen lower digits.

## 2. A sum of shell energies independent of the schedule

Let \(\phi_i\) be the normalized character sum of \(A_i\). The shell of exact order \(p^k\) has \((1-1/p)p^k\) characters. As in the companion note, when \(k\) is unowned by \(i\), Parseval at depth \(k\) minus Parseval at depth \(k-1\) gives mean \(|\phi_i|^2=p^{-d_i(k)}\) on that shell. Hence its contribution to \(E_r(A_i)/M\) is at least \((1-1/p)b_i(k)\), where
\[
b_i(k)=p^{\,2rD_i-2n+k-rd_i(k)}.
\]
This uses \(E_r(A_i)=|A_i|^{2r}M^{-1}\sum_\xi|\phi_i(\xi)|^{2r}\) and the power-mean inequality. The character of order 1 contributes exactly \(b_i(0)\).

Set \(S_k=\sum_i b_i(k)\) and \(Y_k=\sum_{i:\, k\ \mathrm{unowned\ by}\ i} b_i(k)\). At a step \(k\), each unowned term is multiplied by \(p\), and the sole owned term is multiplied by \(p^{1-r}\). Thus
\[
S_k-p^{1-r}S_{k-1}=(1-p^{-r})Y_k.
\]
Sum over \(k\), apply the shell lower bound, and put \(c=(1-1/p)/(1-p^{-r})\). This gives
\[
\begin{aligned}
M^{-1}\sum_i E_r(A_i)
 &\ge S_0+(1-1/p)\sum_{k=1}^n Y_k\\
 &=(1-cp^{1-r})S_0+cS_n+
     c(1-p^{1-r})\sum_{k=1}^{n-1}S_k\\
 &\ge \tfrac14 \sum_{k=0}^n S_k.
\end{aligned}
\]
The last inequality uses \(1/2\le c\le1\) and \(p^{1-r}\le1/2\).

The exponents of \(b_i(k)\) sum to zero, since \(\sum_i D_i=n\) and \(\sum_i d_i(k)=k\). All these integer exponents have the same residue \(k-2n\bmod r\). If that residue is \(j\in\{1,\ldots,r-1\}\), some exponent must be positive and is at least \(j\), so \(S_k\ge p^j\). There are at least \(\lfloor(n+1)/2\rfloor\) levels of nonzero residue, giving \(\sum_k S_k\gg np\). When \(r\mid n\) there are \(n/r\) levels of residue \(r-1\), giving \(\sum_k S_k\ge(n/r)p^{r-1}\). Finally, \(E_r(B)\ge r^{-1}\sum_i E_r(A_i)\), which proves both claims.

## 3. Matching upper bound when \(r\mid n\) and \(p>r\)

Set \(m=n/r\) and use the random periodic schedule in the companion note. A tightening of its first-divergence estimate retains the modular constraint at the first imbalanced digit itself. Given balanced prefixes, the two signed partial sums of all lower digits agree as integers, and the \(2r\) next free letters are fresh independent uniform variables. So equality at that digit, even discarding the requirement of imbalance, costs \(1/p\). Conditional on first imbalance and this equality, each subsequent digit still costs \(1/p\) by the same argument as in the companion proof. For color \(i\) indexed from \(0\), this changes \(m p^{i+1}\) there to \(m p^i\). The union bound via the finite \(L^{2r}\) norm triangle inequality gives an exact factorization with \(E_r(B)\ll_r M(1+m p^{r-1})\).

## Scope and attribution

The \(p\)-homogeneous classification of individual prime-power cyclic tiles is prior work: see Aihua Fan, Shilei Fan and Ruxi Shi, [*Compact open spectral sets in* \(\mathbb Q_p\)](https://arxiv.org/abs/1511.04837), and the prime-power case of the [Coven–Meyerowitz tiling conditions](https://arxiv.org/abs/math/9802122). Section 1 includes a short self-contained proof for simultaneous colored factorizations. The new step here is the schedule-independent quantitative energy obstruction and matching construction, not the tiling classification. No general small-energy *covering* need be a tiling, and the argument does not exclude overlaps, composite moduli with several prime factors, or noncyclic finite groups.
