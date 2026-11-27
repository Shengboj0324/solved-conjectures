# Erdős–Ruzsa conjecture

Fix $0<\theta<1/2$ and put $y=N^\theta$. Choose one residue independently and uniformly for every prime $y<p\le N$. With probability tending to one, the larger classes remove the same proportion, up to an error tending to zero, from **every** survivor set produced by arbitrary choices at the smaller primes. All the smaller primes may be used. Their residue assignments can be made after the larger classes have been revealed. There is no reciprocal-budget restriction in this statement.

Precisely, allow each prime $p\le y$ to be omitted or to forbid any one residue. Let $T$ be the surviving set in $[1,N]$ and $Z(T)$ its size after the larger classes are also forbidden. For constants $A_\theta,c_\theta>0$, except on an event of probability at most $\exp(-c_\theta N^\theta)$,
```math
 \sup_T\left|\frac{Z(T)}{|T|}-\prod_{y<p\le N}(1-1/p)\right|
 \le \frac{A_\theta}{\sqrt{\log N}}.
```
The product tends to $\theta$. In particular the worst small-prime assignment still leaves $\gg_\theta N/\log N$ survivors. A fixed positive tolerance in the display instead gives failure probability at most $\exp(-c_{\theta,t}N^\theta\log N)$. The result strengthens the [bounded-budget concentration estimate](random-residues.md). As in the original problem, an existential cover could still come from exceptional assignments. [Erdős–Ruzsa](https://www.sciencedirect.com/science/article/pii/0022314X80900323) · [Banks–Ford–Tao's random sieve and extremal interval sieve](https://arxiv.org/abs/1908.08613)

## The influence of a single large prime

Fix a small-prime assignment, let $S$ be its selected primes, and write $V(z)=\prod_{q\in S,\,q\le z}(1-1/q)$. The lower linear sieve at level $N/(\log N)^4$ gives $|T|\ge c_\theta NV(y)$. Its sieve parameter tends to $1/\theta>2$, its local discrepancy is at most one for every squarefree modulus, and $V(y)\gg1/\log N$ by Mertens even when all the small primes are used. Thus the total remainder $O(N/(\log N)^4)$ is negligible compared with the main term. The dimension bound is uniform by comparison with the full product over primes. [Motohashi, Iwaniec's linear sieve](https://mathweb.tifr.res.in/Documents/Publications/Lectures/tifr72.pdf)

Set $\epsilon=(1-\theta)/2$. For $y<p\le N^{1-\epsilon}$ and any residue $b\bmod p$ we claim that
```math
 |T\cap(b\bmod p)|\ll_\theta (N/p)V(y).
```
Indeed the progression in $[1,N]$ has $w=N/p+O(1)$ indices, and each selected prime $q\le y$ still forbids exactly one class of indices because $q\ne p$. Sieve these indices up to $z=\min(y,N^{\epsilon/4})$. Here $w\gg N^\epsilon$ and the upper-bound fundamental lemma gives $O_\theta(wV(z))$. Mertens' product over the full interval $(z,y]$ gives $V(z)/V(y)=O_\theta(1)$ since both cutoffs are fixed powers of $N$. This proves the claim. For the larger primes $p>N^{1-\epsilon}$ use the elementary bound $2N/p$ for a single class. [Banks–Ford, Lemma 2.2](https://arxiv.org/pdf/2605.01155)

Changing just the choice at $p$ alters $Z(T)$ by at most the sum of the bounds for the new and old classes. Write $d_p$ for this change bound. Partial summation with $\pi(v)\ll v/\log v$ now gives
```math
 \sum_{p>y} d_p^2\ll_\theta
 \frac{N^2 V(y)^2}{y\log y}+\frac{N^2}{N^{1-\epsilon}\log N}
 \ll_\theta \frac{|T|^2}{y\log y}.
```
The second term is absorbed because $1-\epsilon>\theta$ and $V(y)\gg1/\log N$. Incorporating the small-prime survival density into the change bounds is what allows all small primes to be used.

## A relative estimate uniform over the adversary

Let $\rho=\prod_{y<p\le N}(1-1/p)$. Independence gives $\mathbb E Z(T)=\rho|T|$. The bounded differences inequality and the preceding bound yield
```math
 \Pr\bigl(|Z(T)-\rho|T||>t|T|\bigr)\le 2\exp(-c_\theta t^2 y\log y).
```
There are at most $\prod_{p\le y}(p+1)\le\exp(Cy)$ different assignments by Chebyshev's estimate. Taking their union bound and then $t=A_\theta/\sqrt{\log N}$, with $A_\theta$ large enough, gives the stated high-probability bound. A fixed $t>0$ gives the stronger exponent. Since every $|T|\gg_\theta N/\log N$, the uniform lower bound follows as well. [McDiarmid](https://www.cambridge.org/core/books/abs/surveys-in-combinatorics-1989/on-the-method-of-bounded-differences/AABA597B562BDA7D89C6077E302694FB)
