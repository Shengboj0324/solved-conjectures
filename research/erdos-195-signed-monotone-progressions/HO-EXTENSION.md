# Erdős–Graham monotone progression conjecture

Coordination: [#810](https://github.com/1337isnot1337/solved-conjectures/issues/810). This note concerns the signed domain, Erdős #195, not the now-settled nonnegative domain. **The signed problem remains open.**

## Extreme-pair obstruction for the fixed-parity splice

A finite word is *safe* for a tail order if its concatenation with that order on the unused values has no monotone 4-term arithmetic progression. [Ho's positive-integer solution, Lemma 2 and Algorithm 1](https://arxiv.org/html/2609.12780v1), extends an old prefix by a block of new odd terms, then a block of new even terms, using an odd-first binary tail. Ho's proof is also indexed at [OEIS A399656](https://oeis.org/A399656). The following is stronger than the failure of one particular absolute-value saturation: **no choice of finite blocks can provide that extension lemma on the signed integers.**

**Proposition.** Suppose a finite word $Q$ contains at least one odd integer and at least two different even integers. Let $b_-<b_+$ be the least and greatest even values in $Q$. If both occur after every odd entry of $Q$, then completing $Q$ with any odd-first tail necessarily creates a monotone four-term arithmetic progression.

**Proof.** Let $L,U$ be the least and greatest odd values in $Q$.

- If $L+U<2b_+$, use $(L,b_+,2b_+-L,3b_+-2L)$. The first two entries occur in the specified order in $Q$. The third is odd and exceeds $U$. Also $L<b_+$, so the fourth is even and exceeds $b_+$. Both are in the tail, in the required order.
- If $L+U>2b_-$, use $(U,b_-,2b_--U,3b_--2U)$. The third is odd and below $L$, and the fourth is even and below $b_-$. Again the four occur in order.

At least one of the two strict inequalities must hold since $b_-<b_+$. The common difference in either case is nonzero. $\square$

Given any old prefix, prescribe new even targets strictly below and above every old even value, and an odd target if needed. Any extension obtained by appending new odd values and then new even values puts the new global even extremes after every odd value. The proposition applies. Translating by one gives the mirror obstruction for even-first tails with the corresponding even-before-odd splice. Unlike the obstruction to an absolute cutoff, this argument does not assume that the odd block contains intervals, uses any particular order within a parity, or was constructed by a deterministic recursion.

It is still conceivable that an extension can interleave parities, or treat one direction per stage so that at least one of the two extreme even values is an earlier entry. The proposition does not exclude those variants.

## Closed triples do not guarantee extendability

In the prefix $(0,1,5,4)$, none of the four three-term subsequences in index order is an arithmetic progression. Yet no permutation of the signed integers can extend this prefix without a monotone 4-AP. The ordered pair $(0,1)$ forces $3$ before $2$, by the progression $(0,1,2,3)$; the ordered pair $(5,4)$ forces $2$ before $3$, by $(5,4,3,2)$. Therefore a finite-extension invariant must track compatible constraints on unused pairs, not merely close already ordered triples.
