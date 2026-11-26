# Straus’s coprime sumset problem

For a fixed width, the largest coprime grid below a cutoff has asymptotically as many columns as the most frequent prime difference pattern has occurrences. Overlapping prime patterns cost a vanishing proportion of the columns. This compares the two extremal problems even without an asymptotic formula for either one.

Let $U_r(x)$ be the maximum number of columns of a grid with $r$ distinct positive rows, distinct positive columns, all entries at most $x$, and entries at distinct positions coprime. Write $G_r(x)$ for the maximum, over shapes $H=\{0=h_1<h_2<\cdots<h_r\}$, of the number of translates $p+H$ consisting entirely of primes at most $x$. Thus $G_r$ is the maximal prime difference count for $r-1$ differences in the notation of Libo Wu and Xiaosheng Wu. For every fixed $r\ge2$,

```math
 |U_r(x)-G_r(x)|\ll_r\frac{x(\log\log x)^r}{(\log x)^{r+1}},
 \qquad
 U_r(x)\sim G_r(x)\asymp_r\frac{x(\log\log x)^{r-1}}{(\log x)^r}.
```

The first comparison, which passes from common prime patterns to disjoint coprime grid entries, is the assertion here. The order of the prime difference maximum comes from the unconditional prime-pattern estimates of Wu and Wu. We include the estimates needed below to make the transfer explicit. [Wu–Wu, §3](https://arxiv.org/abs/1710.10942) · [Straus's original question](https://www.erdosproblems.com/432)

## A uniform bound for prime translates

A fixed set of $k$ distinct offsets in $[0,2x]$ has at most
```math
 O_k\left(\frac{x(\log\log x)^{k-1}}{(\log x)^k}\right)
 \tag{1}
```
prime translates with all entries in $[2,x]$. Normalize its smallest offset to zero. In a translate using a prime at most $z=x^{1/4}$, the position of that prime and its value determine the translate. Discard at most $k\pi(z)$ such translates. If the offsets cover all classes of a prime $p\le z$, none remain. Otherwise apply the upper bound of the fundamental lemma of the sieve to the forbidden classes modulo $p\le z$, with interval length $x$. If $\nu_p$ is the number of offset classes, this gives $O_k(x\prod_{p\le z}(1-\nu_p/p))$. [Banks–Ford, Lemma 2.2](https://arxiv.org/pdf/2605.01155)

Put $\Delta=\prod_{i<j}|h_i-h_j|\le(2x)^{\binom{k}{2}}$. For $p\nmid\Delta$ the factor is at most $(1-1/p)^k$ by Bernoulli's inequality. For $p\mid\Delta$ it is at most $1-1/p$. The excess product is therefore at most $(\Delta/\varphi(\Delta))^{k-1}\ll_k(\log\log x)^{k-1}$. The last bound follows by splitting at $y=\max(3,\log(3\Delta))$. Mertens' product below $y$ is $O(\log y)$, while above $y$ there are at most $\log\Delta/\log y$ prime divisors, each contributing $O(1/y)$ to the logarithm. Mertens' product to $z$ supplies the factor $(\log x)^{-k}$, giving (1).

For the matching lower bound on $G_r$, let $M$ be the product of primes up to $(\log x)/10$. Then $M\le x^{1/4}$ for large $x$ and $M/\varphi(M)\asymp\log\log x$. There are $P\asymp x/\log x$ primes in $(x/2,x]$, all in reduced classes modulo $M$. Discrete convexity of $\binom nr$ gives at least $\varphi(M)\binom{\lfloor P/\varphi(M)\rfloor}{r}\gg_r P^r/\varphi(M)^{r-1}$ subsets of $r$ primes in a single class. Each difference from the least prime is a multiple of $M$, so these subsets have at most $(x/M)^{r-1}$ shapes. Pigeonholing gives the asserted lower bound for $G_r$. This is the primorial averaging argument underlying the prime difference champion estimates.

## Passing between the two maxima

In a coprime grid below $x$, each column containing a composite uses at least one prime at most $\sqrt x$. Such a prime cannot be used by another column. After removing at most $\pi(\sqrt x)$ columns, the remaining columns are prime translates of one fixed shape. Consequently $U_r(x)\le G_r(x)+\pi(\sqrt x)$.

Conversely take a maximizing prime shape $H$. If two distinct translates intersect, their displacement $d$ lies in $(H-H)\setminus\{0\}$, a set of size at most $r(r-1)$. For each such $d$, $H\cup(d+H)$ has at least $r+1$ distinct elements. Fix $r+1$ of them and apply (1), shifting their minimum to zero. Every intersecting pair with displacement $d$ determines a translate of these $r+1$ offsets. There are consequently $O_r(x(\log\log x)^r/(\log x)^{r+1})$ intersecting pairs. Deleting at most one translate per pair leaves a disjoint family. Use rows $1+H$ and columns $p-1$ for its retained starting primes $p$. All entries are distinct primes, so this is a coprime grid. The estimates now follow.

Every such grid with at least two rows and columns extends to infinite positive row and column sets. Indeed each side omits a residue class modulo every prime, since two positions on the other side would otherwise give two entries divisible by that prime. To add a column, avoid the negatives of the existing rows modulo every prime dividing an old entry or a nonzero row difference. These are finitely many compatible requirements by the Chinese remainder theorem. The resulting column has new entries coprime to the old ones and to one another. Alternate sides and choose successively larger entries. The extension is Lee's construction. The grids witnessing $U_r(x)$ can depend on $x$, so these cutoffs do not determine the growth for a single pair of infinite sets. The single-grid theorem is [proved separately](README.md). [Lee's manuscript](https://github.com/lsngchl/Erdos432/blob/main/2026-06-23_Erdos432.pdf)

For any single pair in Straus's original question one also has $|A\cap[1,x]|,|B\cap[1,x]|\ll_{A,B,k}x/(\log x)^k$ for **every fixed** $k$. Fix $k$ elements on the opposite side. The composite entries up to $x+O(1)$ use at most $\pi(\sqrt{x+O(1)})$ different values, and any one value can occur at most $k$ times in these $k$ positions, even if different positions are permitted to give equal sums. The prime columns have fixed offsets, so $\Delta$ is constant in the proof of (1). This removes the $\log\log x$ factor. In particular, along any scales with $S_{A,B}(x)\ge x/(\log x)^C$ for a fixed $C$, each side must have at least $(\log x)^D$ elements up to $x$ for every fixed $D$ and all sufficiently large such scales. This follows from $S_{A,B}(x)\le|A\cap[1,x]|\cdot|B\cap[1,x]|$ by choosing $k>C+D$.
