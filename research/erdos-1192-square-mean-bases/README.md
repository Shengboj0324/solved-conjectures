# Erdős’s square-mean additive basis conjecture

[Research claim #802](https://github.com/1337isnot1337/solved-conjectures/issues/802) · [Erdős problem #1192](https://www.erdosproblems.com/1192)

**Status: open for general order.** This note proves a finite reformulation and an all-order logarithmic upper bound. It does not prove the requested linear bound. No Lean work.

For fixed \(r\ge2\), let \(R_A(n)\) count ordered \(r\)-tuples (repetition allowed) from \(A\) with sum \(n\). The question is whether some asymptotic basis \(A\subset\mathbb N\) of order \(r\) has \(\sum_{n\le x}R_A(n)^2=O_r(x)\), for every \(r\ge2\). Ordered and unordered conventions differ by at most the fixed factor \(r!\) in the representation function. For a finite set \(B\) in the integers or in a finite cyclic group write \(E_r(B)\) for the number of ordered \(2r\)-tuples with equal left and right sums.

## 1. A reduction that needs no mixed-energy estimates

**Transfer.** Suppose positive moduli \(M_j\to\infty\) have bounded consecutive ratios and for each \(j\) there is an \(r\)-basis \(B_j\) of \(\mathbb Z/M_j\mathbb Z\) with \(E_r(B_j)\ll M_j L(M_j)\). Here \(L\ge1\) is a nondecreasing function. Then there exists an asymptotic order-\(r\) integer basis \(A\) with \(\sum_{n\le x}R_A(n)^2\ll x L(x)\). Conversely, such an \(A\) furnishes solutions on **every** sufficiently large integer modulus \(M\) with \(E_r(B)\ll_r M L(2rM)\). In particular the desired linear estimate is equivalent to uniform critical energy for cyclic bases at any bounded-ratio sequence of scales.

For the forward direction, retain a subsequence with ratios in \([2,K]\) for a constant \(K\), by greedily advancing to the first modulus at least twice the last. Write \(B_j^0\subset[0,M_j-1]\) for canonical lifts and set \(D=\lceil 2rK\rceil\). Form the positive blocks
\[
V_j=\bigcup_{a=1}^{D}(aM_j+B_j^0).
\]
For \(2rM_j\le n<2rM_{j+1}\), modular coverage gives \(r\) elements of \(B_j^0\) summing to \(s<rM_j\) with \(n-s=kM_j\). We have \(r\le k\le D\). Lift the first \(r-1\) terms using shift \(M_j\) and the last using \((k-r+1)M_j\). This represents \(n\) using \(V_j\). Hence \(A=\bigcup_j V_j\) is a basis.

Reduction modulo \(M_j\) shows \(E_r(V_j)\le D^{2r}E_r(B_j)\): each residue tuple has at most \(D^{2r}\) lifts. For a finite set \(S\) of integers write \(P_S(\theta)=\sum_{s\in S} e^{2\pi i s\theta}\). Orthogonality gives \(\|P_S\|_{2r}^{2r}=E_r(S)\). Truncate to \(A\cap[1,x]\) and partition it into disjoint pieces \(W_j\subset V_j\) with \(M_j\le x\) (assign each point to its first block). By the triangle inequality and monotonicity of energy under inclusion,
\[
\|P_{A\cap[1,x]}\|_{2r}
 \le \sum_{M_j\le x} E_r(V_j)^{1/(2r)}
 \ll (x L(x))^{1/(2r)}.
\]
The last step is a geometric series using \(L(M_j)\le L(x)\). The desired bound follows because every representation of \(n\le x\) uses only positive elements at most \(x\). No extra assumption concerning mixed correlations is needed.

Conversely, take \(A\cap[1,2M]\). The integers in \([M,2M-1]\) supply modular coverage. Reduce that set modulo \(M\); choose one representative from the original set per residue. Each modular representation count is bounded by the sum of integer representation counts of that representative set over its at most \(2r+1\) possible integer sums in the residue. By Cauchy–Schwarz, \(E_r(B)\le(2r+1)\sum_{n\le2rM}R_A(n)^2\).

## 2. Carry-compatible random digit basis

**Theorem.** For every fixed order \(r\ge2\) there is an asymptotic order-\(r\) basis with \(A(x)=O_r(x^{1/r})\) and
\[
\sum_{n\le x}R_A(n)^2=O_r(x\log(2+x)).
\]

Fix a prime \(p>r\), and at scale \(m\) put \(M=p^{rm}\). Number the base-\(p\) digit positions \(k=0,\ldots,rm-1\), from least to most significant. For color \(i=0,\ldots,r-1\), index a set \(A_i\) by words \(x\in\{0,\ldots,p-1\}^m\). At positions \(i,i+r,\ldots,i+(m-1)r\), write the successive letters of \(x\) (the *free digits* of this color). At every other position write a uniform random digit, chosen independently for each color, position and possible prefix of the letters already written. All words with that same prefix get that same digit at that position.

The sum of one word of each color gives a bijection onto \(\mathbb Z/M\mathbb Z\), for **every** choice of the random tables. Read a target from the lowest digit upward, computing the carry from the digits already recovered. At each position every table digit is known and exactly one color has the free digit. This digit is uniquely determined modulo \(p\). Thus \(B=\bigcup_i A_i\) is an \(r\)-basis and \(|B|\le r p^m\).

To bound \(E_r(A_i)\), sample \(2r\) independent uniform words from that color, assigning \(r\) to each side. The normalized energy is the probability, conditional on the tables, of equal sums modulo \(M\). Average also over the tables. Let a prefix be *balanced* if the two multisets of prefixes of the current length agree. Balance at length \(j\) has probability at most \(r!p^{-rj}\): after fixing the left words the right prefixes must be one of at most \(r!\) reorderings. Imbalance, once present, persists at all longer prefixes.

Full balance costs at most \(r!p^{-rm}\). Otherwise suppose imbalance first occurs at the \(d\)-th free digit, position \(k=i+r(d-1)\). The event costs at most \(r!p^{-r(d-1)}\) through this position, discarding the constraints at the first imbalanced digit. At each higher digit, conditional on all revealed information, the probability to advance modular equality by one digit is exactly \(1/p\), whenever equality has held so far. To see this, the signed carry from lower digits is fixed. At a free position all \(2r\) next word letters are fresh independent uniform variables, so their signed sum is uniform modulo \(p\). At a table position the current prefix multiset is imbalanced. Some table entry has net coefficient \(c\) with \(0<|c|\le r<p\), so the uniform independent entry with coefficient \(c\) makes the signed sum uniform. At this position the table has not been exposed earlier. Thus this contribution is at most
\[
r!p^{-r(d-1)}p^{-(rm-1-k)}
  =\frac{r!p^{i+1}}{M}.
\]
Summing over \(d=1,\ldots,m\) and multiplying by \(|A_i|^{2r}=M^2\) gives
\[
\mathbb E E_r(A_i)\le r!(1+mp^{i+1})M.
\]
Use the finite-group version of the norm triangle inequality, with normalized counting measure on the dual group and \(P_C(\xi)=\sum_{c\in C}e^{2\pi i\xi c/M}\). Partition \(B\) into subsets of the colors first, so overlapping colors cause no complication. Convexity gives \(E_r(B)\le r^{2r-1}\sum_i E_r(A_i)\), including for deterministic tables. Some tables therefore realize \(E_r(B)=O_r((1+m)M)\). Use Section 1 with \(M=p^{rm}\). The same positive translated blocks give the size bound \(\sum_{M\le x} O_r(M^{1/r})=O_r(x^{1/r})\), regardless of any initial patch.

## 3. The logarithm is unavoidable in this exact prefix design

This obstruction concerns the design above, not #1192 itself. It applies to all deterministic choices of the tables, even ones not sampled independently. For a color \(A_i\) let \(\phi(\xi)=P_{A_i}(\xi)/p^m\). At resolution \(p^k\), i.e. modulo \(p^k\), write \(t_k=p^{d_i(k)}\), where \(d_i(k)\) is the number of that color's free positions among the \(k\) lowest digits. The residue distribution on its support is uniform on exactly \(t_k\) points, since the free digits determine and distinguish all prefixes. Parseval on \(\mathbb Z/p^k\mathbb Z\) gives
\[
\sum_{\xi:\,\mathrm{ord}(\xi)\mid p^k}|\phi(\xi)|^2=p^k/t_k,
\]
where \(\mathrm{ord}\) denotes the additive character's order. At a table digit (position \(k-1\)), \(t_k=t_{k-1}\), so on the shell of \((p-1)p^{k-1}\) characters of exact order \(p^k\),
\[
\frac{1}{(p-1)p^{k-1}}\sum_{\xi:\,\mathrm{ord}(\xi)=p^k}|\phi(\xi)|^2=t_k^{-1}.
\]
Power mean implies that this shell contributes at least \((p-1)p^{k-1}/t_k^r\) to \(\sum_\xi|\phi(\xi)|^{2r}\). Because \(k-rd_i(k)\) is bounded in absolute value by \(r\), each of the \((r-1)m\) table-position shells contributes at least a positive constant depending only on \(p,r\). Orthogonality gives \(E_r(A_i)=M\sum_\xi |\phi(\xi)|^{2r}\), hence
\[
E_r(B)\ge E_r(A_i)\gg_{p,r} m M.
\]
A choice of better tables with the same prefix geometry cannot remove this logarithm.

## Source and scope

- Imre Z. Ruzsa, [*A just basis*](https://doi.org/10.1007/BF01302934) (1990), Theorem 2, gives the stronger linear bound for order two. Min Tang’s [2010 follow-up](https://doi.org/10.1017/S0004972710000353) is likewise order two. The digit result is chiefly for orders beyond two.
- Erdős–Tetali’s [*Representations of integers as the sum of k terms*](https://doi.org/10.1016/0012-365X(90)90170-E) gives logarithmic pointwise counts for distinct summands at every fixed order; its theorem does not assert the linear square-mean estimate.
- Cédric Pilatte’s [order-three Sidon basis](https://doi.org/10.1112/S0010437X24007140) and Wei Niu’s [one-small-summand result](https://arxiv.org/abs/2607.11351) do not state the required critical square-mean estimate. A Sidon constraint controls two-term representations, not three-term energy.
- The public [Erdős Problem a Day report](https://www.erdosproblemaday.com/report/1192) proved the lower-energy hierarchy, finite small-modulus examples and an exact expansion of order-three mixed terms. Section 1 above instead uses a geometric norm bound that bypasses estimating those terms individually. The finite cyclic construction and logarithmic obstruction are not in that report.
- The original problem is indexed in [Erdős Problems](https://www.erdosproblems.com/1192), the [Erdős research wiki](https://erdosproblems.ai/wiki/problems/additive_bases/E1192/), [Wolfram MathWorld](https://mathworld.wolfram.com/ErdosProblems.html), and [Vela](https://problems.science/problems/erdos-problems/1192). Search also covered Hexagon’s result list, Conjectures.io and recent papers on economical bases. This audit is not an exclusive priority claim.

The remaining construction problem is uniform \(E_r(B)=O_r(M)\) with full modular coverage. One natural direction is to avoid sparse, uniformly occupied intermediate congruence projections, whose character shells force the loss above.
