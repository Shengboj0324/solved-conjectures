# Convex-polygon densities for balanced substitutions

For each fixed $k$ write $c_k$ for the limiting minimum density of convex $k$-subsets among planar sets in general position. The limit in the number of points exists by subsampling. Taking that limit first is essential. An error term growing with the number of substitution levels in the [finite size profile](COUNT-PROFILE.md) cannot by itself control this density. The construction below yields
```math
 \liminf_{k\to\infty}\frac{-\log_2 c_k}{k^2}\ge\frac12.
```
The Erdős–Szekeres theorem of Suk and double counting give the opposite bound $\limsup(-\log_2 c_k)/k^2\le1$. Goaoc and coauthors used a binary order-type limit to prove quadratic decay. Here the number of branches can be arbitrarily large. [Goaoc et al., Propositions 16–17](https://arxiv.org/abs/1811.02236) · [The binary probability](BINARY-LIMIT.md) · [Suk](https://arxiv.org/abs/1604.08657).

Fix $r\ge1$ and take the balanced Erdős–Szekeres template with $M=\binom{2r}{r}$ points and largest cup and cap sizes both $r+1$. Shear slightly to make all cross slopes nonzero, keeping the horizontal order and orientations. Repeat the [flat substitution](FLAT-SUBSTITUTION.md) at every level. Sample independent infinite sequences of uniform digits in $[M]$. A finite sample has almost surely distinct prefixes after finitely many levels. The order type of the sample then stabilizes because replacement preserves orientations on triples with distinct centers. This defines a limit of realizable planar order types: sampling with replacement from level $t$ differs from sampling without replacement with probability at most $\binom{k}{2}/M^t$. Let $U_k,D_k,P_k$ be its cup, cap and convex-position probabilities.

## One-chain probabilities

Let $A_k=\max(U_k,D_k)$ and $a_k=\min(U_k,D_k)$. For $k>r+1$, any cup or cap meeting several first-digit classes has exactly one repeated class, with $s\in\{1,\ldots,r\}$ samples outside it, each in a distinct class. The probability of any prescribed digit assignment is $M^{-k}$. There are at most $C_r k^s$ ways to choose the labels and digits of the outside singletons and the repeated digit. The probability for the remaining chain is at most $A_{k-s}$. If all digits agree, the conditional chain probability is unchanged. Thus
```math
 (1-M^{1-k})A_k\le C_r M^{-k}\sum_{s=1}^r k^s A_{k-s}.
```
Conversely take a fixed maximum base cup, repeat its minimum-ordinate center, and prescribe one of the last $r$ labels at each other center. Every remaining internal cup supplies a full cup. A maximum cap works at its maximum-ordinate center. Therefore $a_k\ge M^{-k}a_{k-r}$ for $k>r+1$. All initial probabilities are positive: inside a maximum base chain any subset of its points forms a chain.

These two recurrences imply, for each chain type $W=U,D$,
```math
 \log_2 W_k=-\frac{\log_2 M}{2r}k^2+O_r(k\log(k+1)).
```
For the lower bound, subtract $r$ at each step and sum the arithmetic progression of visited sizes. For the upper bound, expand until the size is at most $r+1$. Every branch decreases by between one and $r$, so the sum of visited sizes is at least $k+(k-r)+(k-2r)+\cdots=k^2/(2r)-O_r(k)$, stopping when the terms are at most $r+1$. There are at most $r^{k+1}$ branches and the other factors along any branch have product at most $(2C_r k^r)^k$.

## Two hull chains

A convex subset can be partitioned into a cup and a cap by assigning the two shared endpoints to one chain. Either group may be empty. Summing over the at most $2^k$ partitions of the sample labels, independence of the two disjoint subsamples bounds $P_k$ by the sum of the products $U_j D_{k-j}$ for those partitions. The minimum of $j^2+(k-j)^2$ is $k^2/2+O(1)$. For the reverse bound fix two different base centers and prescribe that the first $\lfloor k/2\rfloor$ labels occur in one and the rest in the other. The proper opposite internal chains join into a convex set. The digit assignments cost only $M^{-k}$, and the two chains are independent. Hence
```math
 \log_2 P_k=-\frac{\log_2 M}{4r}k^2+O_r(k\log(k+1)).
```
In particular $c_k\le P_k$ for each $k$. First let $k$ tend to infinity at fixed $r$, and then take $r\to\infty$, using $\log_2\binom{2r}{r}=2r-O(\log r)$. This gives the claimed bound for the extremal density. It does not identify the optimal density or resolve Erdős and Hammer's total-count limit.
