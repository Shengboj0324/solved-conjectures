# Erdős–Ruzsa conjecture

Erdős and Ruzsa ask whether, for every large $N$, one can cover $[1,N]$ by one residue class for each of a set of distinct primes up to $N$ with bounded sum of reciprocals. Their question concerns the existence of exceptional assignments. The following gives an upper bound on the proportion of assignments that can participate in such a cover. The small moduli and their residues can be chosen after seeing **all** the random larger classes. [Original paper, p. 386](https://www.renyi.hu/~p_erdos/1980-29.pdf) · [Erdős problem 1200](https://www.erdosproblems.com/1200) · [Issue 63](https://github.com/1337isnot1337/solved-conjectures/issues/63)

**Theorem.** Fix $C>0$ and $0<\theta<1/2$, and put $y=N^\theta$. Choose one uniform residue independently for every prime $y<p\le N$. There are constants $a,b>0$, depending only on $C,\theta$, such that with probability at least
```math
1-\exp(-bN^\theta\log N),
```
at least $aN$ integers survive **every** choice of a set $P$ of small primes up to $y$ with $\sum_{p\in P}1/p\le C$ and arbitrary classes modulo these primes, in addition to **all** the larger random classes. The conclusion still holds with $aN/2$ survivors if any subset of large classes is discarded and any remaining large classes of total reciprocal cost at most $a/4$ are reassigned adversarially.

## Survivors before choosing the larger classes

Fix a small-prime assignment within budget and let $T$ be its survivors in $[1,N]$. The dimension-one lower-bound sieve gives $|T|\ge c_{C,\theta}N$ uniformly. Indeed the product of the forbidden classes at the primes dividing any squarefree $d$ specifies exactly one class modulo $d$, with count $N/d+O(1)$. Take the sieve level $D=N/(\log N)^4$. The total remainder at this level is $O(D)$ for the bounded Rosser weights. Mertens' theorem gives the usual dimension-one product bound for subsets of the primes. The sieve parameter $\log D/\log y$ tends to $1/\theta>2$, where the lower sieve function is positive. Finally $\prod_{p\in P}(1-1/p)\ge\exp(-2C)$. Whether a prime exactly at the cutoff is included can be handled by using $y+1$ as the sieve endpoint. [Motohashi, *Lectures on Sieve Methods and Prime Number Theory*, Iwaniec's linear sieve](https://mathweb.tifr.res.in/Documents/Publications/Lectures/tifr72.pdf)

## Concentration uniformly over all small-prime assignments

For this fixed $T$, let $Z$ count the elements of $T$ avoiding the random classes. Each element survives with probability $\prod_{y<p\le N}(1-1/p)=\theta+o(1)$ by Mertens' theorem. In particular $\mathbb EZ\ge 2aN$ for a fixed $a>0$ and sufficiently large $N$.

Changing the class of one large prime changes $Z$ by at most $2\lceil N/p\rceil\le4N/p$. By partial summation and $\pi(v)\ll v/\log v$, the sum of the squared change bounds over large primes is $O(N^2/(y\log y))$. The bounded differences inequality therefore gives $\Pr(Z<aN)\le\exp(-c y\log y)$. [McDiarmid, *On the method of bounded differences*](https://www.cambridge.org/core/books/abs/surveys-in-combinatorics-1989/on-the-method-of-bounded-differences/AABA597B562BDA7D89C6077E302694FB)

For each prime $p\le y$ there are at most $p+1$ decisions, including omission. Thus the number of all small-prime assignments, even ignoring the budget, is at most $\prod_{p\le y}(p+1)=\exp(O(y))$ by Chebyshev's estimate. The failure probability for any budget-admissible assignment is at most $\exp(O(y)-c y\log y)\le \exp(-bN^\theta\log N)$. This proves the simultaneous assertion. Discarding classes only adds survivors. Replacing large classes of cost at most $a/4$ can remove at most $aN/4+\pi(N)\le aN/2$ of the survivors once $N$ is large. This proves the robust assertion.

Equivalently, take the product of all large primes and use the Chinese remainder theorem to index their assignments by a single residue modulo this product. At most an $\exp(-bN^\theta\log N)$ fraction of those residues can be converted into a full bounded-cost cover, even allowing the stated reassignments. This estimate concerns that fraction, and leaves open whether there exists any assignment yielding a cover.

## Related results

Erdős and Ruzsa and later Hildebrand treated deterministic zero classes. The repository also has a [deterministic common-shift theorem](../../docs/erdos-ruzsa-research.md). Banks, Ford and Tao study prime gaps in a random residue-class sieve and relate them to a worst-case interval sieve. The result above combines a lower linear sieve, bounded differences and the count of small-prime assignments in the bounded-cost question. Searches in the small-sieve paper, its arbitrary-residue discussion, the interval-sieve literature and the July working report did not locate the stated simultaneous estimate. [Hildebrand](https://doi.org/10.4064/aa-48-3-209-260) · [Banks–Ford–Tao](https://arxiv.org/abs/1908.08613) · [July report](https://www.erdosproblemaday.com/report/1200)
