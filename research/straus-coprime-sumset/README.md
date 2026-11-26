# Straus’s coprime sumset problem

Straus asked how large $S_{A,B}(x)=|(A+B)\cap[1,x]|$ can be for two infinite sets of positive integers if the distinct sums are pairwise coprime. This is Erdős problem 432. We show that **every prescribed subpolynomial lower bound is attainable at all sufficiently large scales**, unconditionally, by a single pair of infinite sets depending on the prescribed bound. The sets even give a coprime grid, meaning that sums at distinct positions have gcd one and hence are distinct. The maximum possible growth remains open. [Erdős–Graham, p. 85](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf) · [Problem record](https://www.erdosproblems.com/432) · [Research issue](https://github.com/1337isnot1337/solved-conjectures/issues/841)

**Theorem.** If $F:\mathbb N\to[1,\infty)$ and $\log F(x)/\log x\to0$, there are infinite $A,B\subset\mathbb N$ forming a coprime grid with $1\in B$ and

$$|\{a\in A:a+1\le x\}|\ge F(x)\qquad\text{for every sufficiently large integer }x.$$

The displayed lower bound therefore holds for $S_{A,B}(x)$. For example one can prescribe $F(x)=\exp(\log x/\log\log\log x)$ for large $x$. The choice of grid can depend on $F$. No fixed positive-power lower bound follows.

Sungchul Lee proves the uniform lower bound $(\log x/\log\log x)^2$ and proves attainment of every prescribed $x^{o(1)}$ **on a subsequence**. Lee also gives a stronger prime-grid result assuming Hardy–Littlewood. We use Lee’s finite-grid extension idea and the same standard sieve estimate. The change is in how rows and columns are added. A new column can be very large, yet its effect on the next row estimate is controlled by its logarithm. This permits continued growth of the first column's counting function between extensions. [Lee’s manuscript, the four theorems in §1](https://github.com/lsngchl/Erdos432/blob/main/2026-06-23_Erdos432.pdf)

## Adding a row after a large column

Fix a nondecreasing sequence $X_k$ with $X_k/k^d\to\infty$ for every fixed $d$, and $X_k\le e^{\sqrt k}$. We will prescribe it below. Let $G\times H$ be a finite coprime grid, $|G|=K$, $|H|=r$, $2\le r\le K$, and put $M=\max(G\cup H)$. Assume

$$\log(2M)\le K^4.\tag{1}$$

Each of $G,H$ omits at least one residue class modulo every prime. If, for example, $H$ covered every class modulo $p$, each of two distinct rows would contain an entry divisible by $p$, contrary to the coprime-grid property.

For each **fixed** $r$ and every sufficiently large $K$ (depending on $r$ and the chosen sequence $X_k$), a new row can be taken in $(X_{K+1},2X_{K+1}]$, uniformly over every grid satisfying (1). To prove this, write $X=X_{K+1}$, $Y=K^9$. Sieve this interval against the residue classes $-H\pmod p$ for all $p\le Y$. There are at most $\min(r,p-1)$ forbidden classes. By Lemma 2.2 of Banks and Ford the number of surviving integers is $\gg_r X/(\log Y)^r$. Indeed $\log X/\log Y\to\infty$, and the product of the surviving prime densities is $\gg_r(\log Y)^{-r}$ by Mertens’ theorem. The bound is uniform in the actual residues and in $M$. [Banks–Ford, Lemma 2.2](https://arxiv.org/pdf/2605.01155)

Let $\mathcal P$ consist of the prime divisors of old entries and of all nonzero differences of distinct elements of $H$. The logarithm of the product of those entries and absolute differences is at most $(Kr+\binom r2)\log(2M)$, so $|\mathcal P|\ll K^6$. For any $p\in\mathcal P$ larger than $Y$, at most $r(X/p+1)$ candidates have some $a+h\equiv0\pmod p$. Even before sieving, the union of these exceptional sets has size

$$O\big(K^7(X/Y+1)\big)=O(X/K^2+K^7)=o_r\big(X/(\log Y)^r\big).$$

The last estimate uses the assumed superpolynomial growth of $X_k$ and holds for each fixed $r$. Some candidate remains. Its new entries are coprime to every old entry. A prime dividing two new entries would divide their difference, hence would be in $\mathcal P$, also excluded. All entries exceed one, so this also excludes coinciding entries and repeated rows. After insertion (1) persists with $K+1$ in place of $K$, since the new coordinate is at most $2e^{\sqrt{K+1}}$.

## Adding a column and scheduling the extensions

When $\log(2M)\le K$, an additional column can be inserted with the updated height still satisfying (1) for the same $K$, for all large $K$. Form the squarefree product $Q$ of the primes dividing old entries or nonzero differences of rows. For each such prime choose a residue for the new column outside $-G\pmod p$. The Chinese remainder theorem gives a solution in $(M,M+Q]$, and the same divisor argument proves compatibility. Moreover

$$\log Q\le(Kr+\tbinom K2)\log(2M)\le2K^3.$$

Thus $\log(2(M+Q))\le K^4$ for large $K$. This step only needs $G$ to omit a residue class at every prime, so it applies also to the following initialization.

Choose $K_0$ sufficiently large for the row lemma at $r=2$. Take $H=\{1\}$ and take as rows $K_0$ numbers $p-1$ with distinct primes $K_0^2<p\le2K_0^2$. The prime number theorem supplies them. For primes $q\le K_0$ the rows omit $-1\pmod q$, and for larger $q$ there are fewer rows than residues. The first column step therefore gives two columns and satisfies (1).

At each fixed column count $r$, insert rows using the row lemma until $K$ is sufficiently large for its threshold at $r+1$, $K>r$, and $\log(2M)\le K$. All three conditions can be reached: the largest column stays fixed throughout this stage, and all newly added rows with insertion index $k$ are at most $2e^{\sqrt k}$. Add a column and repeat. One can require at least one new row in each stage. Since the bounds do not depend on the specific residue classes, the thresholds for later column counts may be chosen before constructing the columns. Both limiting sets are infinite. Any two positions in the limit occur together at a finite stage, hence their sums are coprime.

## Passing from row indices to every scale

Replace $F(x)$ by $\max(\log(2+x),\max_{1\le t\le x} F(t))$ if necessary. This dominates the original function, is nondecreasing, tends to infinity, and is still $x^{o(1)}$. Put

$$L_k=\min\{x\in\mathbb N:F(x)>k-1\},\qquad X_k=\min(e^{\sqrt k},L_k/4).$$

For every fixed $d$, $L_k/k^d\to\infty$, by applying $F(x)\le x^{1/(2d)}$ at $x=L_k$ for large $k$. The same property holds for $X_k$. All noninitial rows of index $k$ therefore satisfy $a_k+1\le 2X_k+1\le L_k$ for large $k$. By monotonicity of $L_k$, the first $k$ rows all have $a_i+1\le L_k$ for every sufficiently large $k$, including the fixed finite initialization. At scale $x$ take $k=\lceil F(x)\rceil$. Then $L_k\le x$, so the first column contributes at least $k$ distinct sums up to $x$. This completes the proof.

## Other prior results checked

Pomerance, Sárközy and Stewart construct large finite sumsets all of whose entries are prime. Tao and Ziegler produce prime sums for one triangular part of an infinite grid. Croot and Elsholtz study sumsets contained in the primes, including inverse results with three summands. The finite two-row computations in the August problem report and the elementary upper bound $S_{A,B}(x)\le\pi(x)$ concern different parts of the question. A search under the names Erdős, Straus and Ostmann, the phrases “coprime grid” and “pairwise coprime sumset”, and the uniform/subsequence growth formulations found no earlier proof of the displayed all-scales bound. [Pomerance–Sárközy–Stewart](https://doi.org/10.2140/pjm.1988.133.363) · [Tao–Ziegler](https://arxiv.org/abs/2301.10303) · [Croot–Elsholtz](https://arxiv.org/abs/math/0209137) · [August report](https://www.erdosproblemaday.com/report/432)

At each cutoff, the largest fixed-width extendable grid is asymptotically as large as the most frequent prime difference pattern. The separate [comparison proof](prime-patterns.md) controls intersecting translates and gives a necessary condition on both sides of a single near-prime-density sumset.
