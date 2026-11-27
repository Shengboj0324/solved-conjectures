# Efficient constant-weight strong write-once memory codes

En Gad, Yaakobi, Jiang and Bruck established the capacity of constant-weight strong write-once memory (WOM) codes by a counting argument. They left open the construction of an efficient family attaining it. For integers $0\le W\le S\le n$, the state is an arbitrary $S$-element set of available positions in $[n]$. For every message the encoder must write a $W$-element subset of that state. The decoder gets the written subset alone. [Original paper, Definition 12, Proposition 13 and the paragraph continuing on p. 4216](https://yaakobi.net.technion.ac.il/files/2015/11/16_RM_Rewriting_IT15.pdf).

**Theorem.** There are uniform deterministic algorithms for constructing the code and for encoding and decoding in polynomial time in $n$. For $S=\lfloor w_s n\rfloor$ and $W=\lfloor w_x n\rfloor$, their number of message bits $k$ satisfies, for every fixed $0<w_x<w_s\le1$,

```math
 S H_2(W/S)-O_{w_s,w_x}\!\left(\frac{n\log\log n}{\log n}\right)
 \le k\le\log_2\binom SW .
```

Here $H_2$ is the binary entropy function. In particular the limiting rate is $w_sH_2(w_x/w_s)$, the capacity in Proposition 13. The cases $W=0$ or $W=S$ have one message and are attained exactly. All logarithms below are binary except in exponential probability estimates.

## Coloring one weight layer of a short block

Choose a length bound $L\ge1$. Let $0\le w\le u\le b\le L$ and $M=\binom uw$. Put

```math
 j=\max\{0,\lfloor\log_2(M/(4L))\rfloor\},\qquad Q=2^j.
```

There is a deterministically constructible labeling of all $w$-subsets of $[b]$ by $j$ bits such that the $w$-subsets of each $u$-set contain every label. If $Q=1$ use the empty label. Otherwise give the $w$-subsets independent uniform labels. A specified $u$-set misses a specified label with probability $(1-1/Q)^M\le e^{-M/Q}$. The expected number of missing pairs is at most $2^{2L}e^{-4L}<1$.

Fix the labels one at a time, choosing a value minimizing that conditional expectation. The expectation before the choice is the average of the possible next values. At the end the number of missing pairs is a nonnegative integer below one. For exact computation, the contribution of a pair is zero once witnessed and otherwise equals $(1-1/Q)^a$, where $a$ of its candidate subsets are still unassigned. The common denominator $Q^{2^L}$ has $O(L2^L)$ bits. Enumerating all events, all words and all labels, and performing the indicated rational comparisons, takes $2^{O(L)}$ bit operations up to polynomial factors in $L$. Any larger available set also sees every label by restriction to a $u$-subset.

## Choosing the block weights

Assume $0<W<S$ and put $\lambda=W/S$. Partition $[n]$ into consecutive blocks of length $L=\max(1,\lfloor\log_2 n\rfloor)$ and a possible shorter final block. Write $b_i$ for their lengths and $B=\lceil n/L\rceil$ for their number. For a block of length $b$ having $s$ available positions, its allowed output weights are

```math
 R(s)=\{\lfloor\lambda s\rfloor,\lceil\lambda s\rceil\}.
```

Given a state with block counts $s_i$, take all floors and round up exactly $W-\sum_i\lfloor\lambda s_i\rfloor$ nonintegral coordinates, in index order. This is possible since $\sum_i\lambda s_i=W$. The resulting $w_i$ lie in $R(s_i)$ and sum to $W$.

For each reachable pair $(b,w)$ let $u(b,w)$ be the least $s\in\{0,\ldots,b\}$ with $w\in R(s)$. It is at least $w$. Construct the preceding labeling with $u=u(b,w)$ and denote its output length by $j(b,w)$. An unreachable weight receives the empty label. Once the written word is known, the decoder can read its block weight $w$ and use the correct local labeling without knowing $s$.

## A fixed message length for every state

Compute the following integer as part of the code:

```math
 k=\min_{\substack{0\le s_i\le b_i\\\sum_i s_i=S}}
           \sum_{i=1}^B\min_{w\in R(s_i)} j(b_i,w).
```

A one-dimensional dynamic program over successive blocks and the accumulated count computes this number in polynomial time. Every rounded allocation admits at least $k$ label bits in total. Pad a $k$-bit message on the right with zeros and split it into consecutive strings of lengths $j(b_i,w_i)$. In block $i$ enumerate the $w_i$-subsets of its available positions until finding the assigned string. Since $s_i\ge u(b_i,w_i)$ the labeling theorem guarantees success. The union of these local words has exactly $W$ positions, all available.

The decoder concatenates the labels of the observed block subsets and reads the first $k$ bits. For an arbitrary $W$-set where the concatenation is too short, append zeros before reading. The encoder always reaches length $k$ and gives back the specified message. This defines a total surjective decoder on the required weight layer. The block searches cost at most $2^L$ trials per block. All local tables and their exact comparisons have polynomial size and running time because $L\le\max(1,\log_2 n)$.

## Rate

For any feasible $s,w$, write $u=u(b,w)$. Both $|w-\lambda s|<1$ and $|w-\lambda u|<1$ except that equality of $w$ with the unrounded value gives displacement zero. In particular $0\le s-u\le\lceil 2/\lambda\rceil$. Increasing the upper argument of $\binom uw$ one step multiplies it by at most $b+1$. The definition of $j$ therefore gives

```math
 j(b,w)\ge \log_2\binom sw-\lceil 2/\lambda\rceil\log_2(b+1)-\log_2(4L)-1.
```

Uniformly over $0\le s\le L$ and $w\in R(s)$, one has $\log_2\binom sw\ge sH_2(\lambda)-O(\log(L+1))$. For $s\ge2$, the binomial distribution with success probability $w/s$ has a mode at $w$, so its probability there is at least $1/(s+1)$. This gives $\log_2\binom sw\ge sH_2(w/s)-\log_2(s+1)$, including the deterministic endpoints. Also $|H_2(a)-H_2(b)|\le H_2(|a-b|)$: couple the two Bernoulli variables by thresholding the same uniform variable, and recover either from the other and their disagreement bit. Since $|w/s-\lambda|\le1/s$, it follows that $s|H_2(w/s)-H_2(\lambda)|\le sH_2(1/s)\le\log_2(e s)$. The cases $s=0,1$ satisfy the estimate directly.

Thus every term in the minimization is at least $s_iH_2(\lambda)-O_\lambda(\log(L+1))$. Summing proves $k\ge SH_2(\lambda)-O_\lambda(B\log(L+1))$. For fixed positive interior weights $\lambda$ is bounded away from zero as $n$ grows. Finally, fixing just one state allows only $\binom SW$ distinct outputs, so no code can have more than $\log_2\binom SW$ message bits. These bounds prove the theorem.

## Cooling-code consequence

In the binary low-power cooling model, $t$ specified coordinates must be zero and a transmitted word may have at most $w$ ones. Take $S=n-t$ and $W=\min(w,\lfloor S/2\rfloor)$. The encoder above meets the zero and weight constraints for every forbidden set. Its decoder recovers the message in polynomial time. For any fixed forbidden set the number of possible outputs is at most $\sum_{j=0}^{\min(w,S)}\binom Sj\le(S+1)\binom SW$. Consequently the optimal noiseless asymptotic rate at $t/n\to\tau$, $w/n\to\omega$, for $0<\tau<1$ and $\omega>0$, is attained efficiently and equals

```math
 (1-\tau)H_2\bigl(\min(\omega/(1-\tau),1/2)\bigr).
```

Chee, Etzion, Kiah and Vardy define this cooling model and discuss the efficiency and asymptotic optimality questions. The exact-weight existence capacity was already given by En Gad, Yaakobi, Jiang and Bruck. [Cooling codes, §§V, VII and VIII](https://ymchee66.github.io/home/PDF/coolingjournal.pdf) · [Strong WOM codes, Proposition 13](https://yaakobi.net.technion.ac.il/files/2015/11/16_RM_Rewriting_IT15.pdf).
