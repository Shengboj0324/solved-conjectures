# Transferring almost-coverings of coordinate groups

This note enlarges the finite construction problem equivalent to [Erdős #1192](https://www.erdosproblems.com/1192). No conjecture is declared solved. Keep the order \(r\) fixed.

## Density-one is enough with a power-saving error

Let \(G\) be an abelian group of size \(M\), and suppose \(B\subseteq G\) has order-\(r\) energy \(E_r(B)\ll M\). Assume \(|G\setminus rB|/M\le C M^{-\epsilon}\) for fixed \(C,\epsilon>0\). Then a bounded number of translates of \(B\), together with \(B\) itself, is an \(r\)-basis of \(G\) with energy \(O(M)\).

Indeed choose \(s>1/\epsilon\) independent uniform \(t_j\in G\). The expected number of points missed by \(\bigcup_j(rB+t_j)\) is at most \(C^sM^{1-s\epsilon}=o(1)\). Each \(rB+t_j\) is contained in \(r(B\cup(B+t_j))\), since one summand can use the shifted copy and the others the original. The finite-group \(L^{2r}\) norm triangle inequality (after partitioning overlaps) bounds the energy of the resulting union by \((s+1)^{2r}E_r(B)\). This argument applies to general energy bounds \(O(M L(M))\) as well.

## A carry correction for any bounded number of cyclic coordinates

For fixed \(d\), let
\[
G=\prod_{i=0}^{d-1}\mathbb Z/b_i\mathbb Z,\qquad
w_0=1,\qquad w_i=\prod_{j<i}b_j,\qquad M=w_d.
\]
Assume every \(b_i\ge2\), with no coprimality required. If \(B\subseteq G\) is an \(r\)-basis, it yields an \(r\)-basis \(B'\subseteq\mathbb Z/M\mathbb Z\) satisfying
\[
E_r(B')\le (2r+1)^{d-1}r^{2r(d-1)} E_r(B).
\]
Thus one can aim directly at vector groups \(\mathbb F_p^d\) for **any fixed \(d\)** and a sequence of primes with bounded ratios. Neither working in a cyclic group nor producing an exact cover in one algebraic step is necessary.

**Coverage.** Lift a vector \(a\in G\) to \(L(a)=\sum_i w_i a_i\), choosing \(0\le a_i<b_i\). Given \(t\in[0,M-1]\), read its mixed-radix digits and choose \(a^{(1)},\ldots,a^{(r)}\in B\) summing to those digits in \(G\). Then
\[
\sum_{\ell} L(a^{(\ell)})-t=\sum_{i=0}^{d-1} w_{i+1} c_i,\qquad 0\le c_i\le r-1.
\]
The final term vanishes modulo \(M\). Form \(B'\) by adjoining to \(L(B)\) every translate by \(-\sum_{i=0}^{d-2} w_{i+1} c_i \pmod M\), for the bounded list of carry vectors. Use the appropriate translate on one of the \(r\) summands.

**Energy.** Consider two ordered \(r\)-tuples whose lifted integer sums agree modulo \(M\). Let \(D_i\) be the difference of the two ordinary coordinate sums in coordinate \(i\). There are signed integers \(s_0=0,s_1,\ldots,s_d\) with
\[
s_i+D_i=b_i s_{i+1}
\]
for \(i=0,\ldots,d-1\): peel off digits of the equality modulo \(M\) from the bottom. Since \(|D_i|\le r(b_i-1)\), induction gives \(|s_i|\le r\). Thus the difference between the two **group** sums in \(G\) is in the list of at most \((2r+1)^{d-1}\) vectors having coordinate \(i\) equal to \(-s_i\bmod b_i\). For each fixed such vector \(\delta\), the number of pairs with group-sum difference \(\delta\) is
\[
\sum_{x\in G}R_B(x)R_B(x+\delta)\le E_r(B)
\]
by Cauchy–Schwarz. This bounds the cyclic energy of \(L(B)\). The number of translates used in \(B'\) is at most \(r^{d-1}\) (including the original, the zero-carry case). Apply the norm triangle inequality to their union to finish.

Combine the two arguments and the [bounded-ratio gluing lemma](README.md): it would suffice, for every fixed \(r\), to construct \(O(p^{d/r})\) elements of \(\mathbb F_p^d\) whose \(r\)-sums miss only \(O(p^{d-\eta})\) vectors and have energy \(O(p^d)\), for any fixed \(d,\eta>0\) and growing primes with bounded ratios. For example, a generically birational addition map using a bounded number of individually critical-energy constituent curves would do. No such general construction is asserted here.

An exact-tiling warning: when \(d=r\) and the \(r\) color classes each have size \(p\), [Rédei's theorem](https://msp.org/pjm/1989/140-1/pjm-v140-n1-p04-p.pdf) forces a subgroup coset among the factors of any exact tiling. That factor alone has energy \(p^{2r-1}\), too large for \(r\ge2\). The warning does not apply to the power-saving near-cover criterion above.
