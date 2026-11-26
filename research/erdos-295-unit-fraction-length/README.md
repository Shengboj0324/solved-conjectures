# Erdős’s minimum-length unit-fraction conjecture

[Research issue #811](https://github.com/1337isnot1337/solved-conjectures/issues/811) · [Erdős #295](https://www.erdosproblems.com/295)

Let \(k(N)\) be the least length of a representation of \(1\) by distinct unit fractions with denominators at least \(N\). The conjecture asks whether \(k(N)-(e-1)N\to\infty\). The unrestricted conjecture remains open here. The estimates below apply to every expansion, not only one attaining \(k(N)\).

## Results

For a finite set of denominators \(D\subset[N,\infty)\cap\mathbb Z\) with \(\sum_{a\in D}1/a=1\), write \(k=|D|\), \(A=\max D\), and \(s=k-(e-1)N+3\). Then for all sufficiently large \(N\):
\[
s\bigl(\log N+\log A\bigr)\gg N.
\]
In particular any family with \(A\le N^C\), for fixed \(C\), needs \(k-(e-1)N\gg_C N/\log N\). A family with bounded excess must have some denominator of size \(\exp(\Omega(N))\).

Furthermore, along **any** sequence of expansions with \(N\to\infty\) and \(s=o(N/\log N)\),
\[
\liminf\frac{1}{N}\log\prod_{a\in D:\,a>3N}a\ \ge e.
\]
In this regime the large denominators are few, but collectively carry almost all of the large prime modulus of the near-consecutive block. The result does not show that such denominators cannot occur.

## A reciprocal-mass budget

Put \(T=N+k-1\), \(I=[N,T]\cap\mathbb Z\), and \(H=\sum_{a\in I}1/a\). The first \(k\) denominators give the maximum sum of \(k\) distinct reciprocals at least \(N\), so \(H\ge1\). Integral comparison gives \(H\le\log(T/(N-1))\) for \(N\ge2\). Thus \(T\ge e(N-1)\), \(s>0\), and
\[
0\le H-1\le\frac{T-e(N-1)}{e(N-1)}\ll s/N.
\]
Because the two sets have the same cardinality, subtracting \(1/T\) from each reciprocal gives the exact identity
\[
H-1
  =\sum_{a\in I\setminus D}\left(\frac1a-\frac1T\right)
   +\sum_{a\in D\setminus I}\left(\frac1T-\frac1a\right).
\]
All terms on the right are nonnegative. If \(s>N/20\), the first claimed tradeoff is immediate. Otherwise \(2.5N\le T\le2.8N\) for all sufficiently large \(N\). The identity now implies
\[
|[N,1.8N]\cap(\mathbb Z\setminus D)|+|D\cap(3N,\infty)|\ll s.
\]
Each missing or added term counted here charges at least a fixed positive constant times \(1/N\).

## From reciprocal mass to denominator height

Use the primes \(p\in[1.6N,1.8N]\). Their total logarithmic weight is \((0.2+o(1))N\) by the prime number theorem. The omitted primes in this interval have total weight \(O(s\log N)\). For every prime from the interval that is included, \(p\) is the unique multiple of \(p\) among the denominators up to \(3N\), since \(2p>3N\). If there were no multiple among the larger denominators, multiplying the claimed sum by \(p\) and reducing modulo \(p\) in the rationals with denominator prime to \(p\) would give \(1=0\pmod p\). Hence each included prime must divide at least one denominator greater than \(3N\).

Distinct primes can divide **the same** tail denominator. We charge their product, not their count. Their product divides the product of all tail denominators. Thus
\[
cN\le O(s\log N)+\sum_{a\in D:\,a>3N}\log a
       \le O(s(\log N+\log A))
\]
for an absolute \(c>0\), as claimed.

## Nearly the whole primorial appears in the tail

Now assume \(s=o(N/\log N)\), so \(T=eN+o(N)\). Fix \(0<\eta<1/4\). The reciprocal-budget identity shows that \(O_\eta(s)\) integers in \(I_\eta=[N,(e-\eta)N]\cap\mathbb Z\) are omitted. For a prime in
\[
\frac{100N}{\log N}\le p\le(e-\eta)N,
\]
there is a multiple in \(I_\eta\): use \(p\) itself if \(p\ge N\), and otherwise the smallest multiple at least \(N\), which is less than \(N+p\le2N\). Choose one such witness per prime. For large \(N\), the product of two primes above the lower threshold exceeds \(3N\), so different primes cannot have the same witness. All but \(O_\eta(s)\) of these primes therefore have at least one multiple in \(D\) at most \(3N\).

Fix such a prime and suppose no denominator in the tail is divisible by it. The multipliers \(a/p\) for denominators divisible by \(p\) form a nonempty subset \(J\) of \([1,L]\) for \(L=\lfloor 3N/p\rfloor\le0.03\log N\). The reduced fraction \(\sum_{j\in J}1/j=b/c\) has \(p\nmid c\), since \(L<p\). Its positive numerator is at most
\[
b\le(1+\log L)\operatorname{lcm}(1,\ldots,L)<p
\]
for all sufficiently large \(N\), uniformly in this range. Indeed the logarithm of this lcm is at most \(2L+O(1)\), by the prime number theorem. Then \(p\sum_{a\in D}1/a\) reduces modulo \(p\) to \(b/c\ne0\), contradicting \(p\sum 1/a=p\). Each witnessed prime must therefore divide the product of the tail denominators. The logarithmic weight of unwitnessed primes is \(O_\eta(s\log N)=o(N)\), while the prime threshold below \(100N/\log N\) costs only \(o(N)\) logarithmic weight. This proves
\[
\log\prod_{a\in D:\,a>3N}a\ge((e-\eta)-o_\eta(1))N.
\]
Let \(\eta\) tend to zero after taking the liminf.

## Prior work and limitations

- Erdős–Straus, solution of Monthly problem E2232, *American Mathematical Monthly* **78** (1971), 302–303, give the \(O(N/\log N)\) upper bound on the excess and the elementary constant lower bound; the [research wiki](https://erdosproblems.ai/wiki/problems/unit_fractions/E0295) traces the statement and their construction. Erdős–Graham's 1980 monograph and Bloom's [problem record](https://www.erdosproblems.com/295) preserve the unrestricted question.
- [Croot, *On unit fractions with denominators in short intervals*](https://www.impan.pl/shop/en/publication/transaction/download/product/83061), constructs expansions with small largest denominator but does not show a length-minimizing expansion has small height. [Bloom–Elsholtz's survey](https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf) discusses that distinction's surrounding results. [Bleicher–Erdős, *Denominators of Egyptian fractions II*](https://combinatorica.hu/~p_erdos/1976-10.pdf) concerns height bounds for representing prescribed rational numbers, not uniform height for minimum-length expansions here.
- The [recent exact-search report](https://erdosproblemaday.com/day/295-k17-exact) notes the standard \(p\)-adic restriction and separately certifies several finite bounds; it does not claim these uniform length–height estimates. Searches also checked the exact statement, the original references, adjacent Egyptian-fraction papers and current result trackers. No exclusive priority or full resolution is claimed.

A proof still needs to rule out a small number of exponentially large repair terms. Treating distinct prime divisors as necessarily needing distinct repair terms is invalid.
