# Erdős–Graham monotone progression conjecture

[Erdős #195](https://www.erdosproblems.com/195) · [Working issue #810](https://github.com/1337isnot1337/solved-conjectures/issues/810)

**Status: open.** The target is the largest \(k\) such that every permutation indexed by \(\mathbb N_0\) of **all signed integers** contains an increasing or decreasing arithmetic progression with \(k\) distinct terms. The known bounds are \(3\le k\le4\). These notes exhibit two obstructions to adapting natural-number constructions. They do not establish the value of \(k\).

Davis–Entringer–Graham–Simmons force a three-term progression already in the positive subsequence. [Adenwalla's Theorem 1](https://arxiv.org/abs/2211.04451) gives an integer permutation avoiding five terms. [Kohlmeyer–Kruer](https://hexagonmath.org/2611.00785v1) avoid four on \(\mathbb N_0\) (#196), not on \(\mathbb Z\). The [Erdős research wiki entry](https://erdosproblems.ai/wiki/problems/additive_combinatorics/E0195) records the older signed bounds. An exact-title and exact-domain literature screen, including the source papers, Erdős forum, Hexagon, Conjectures.io and repository claims, found no proof of the full signed problem.

## 1. Contiguous outward shells do not suffice

**Proposition.** Let \(0=T_0<T_1<\cdots\) be integer radii tending to infinity. Form a permutation of \(\mathbb Z\) by concatenating the finite shells
\[
\{n\in\mathbb Z:T_j\le |n|<T_{j+1}\}.
\]
In each shell, order the integers by a binary residue order with arbitrary preferences at the nodes (possibly a different order for every shell). Then the permutation contains a numerically increasing four-term arithmetic progression in increasing index order. The same obstruction applies to the corresponding nonnegative construction.

By a binary residue order, given distinct \(x,y\), compare their digits at the first differing binary place, read from least significant to most significant. The preferred child of the common node precedes the other. In particular, for opposite-parity values in any one shell, their relative order is determined by that shell's root preference.

**Proof.** Take a boundary \(T=T_j\) sufficiently large that \(0,1\) occur before every shell at or beyond \(T\). Choose an odd integer \(h\) strictly between \(3T/5\) and \(2T/3\). Both progressions
\[
0,h,2h,3h\qquad\text{and}\qquad 1,h+1,2h+1,3h+1
\]
have their first terms before the shell of their second terms, and second terms below \(T\) while third and fourth terms are above it. If the third and fourth terms occupy different shells for either progression, that progression is already in order. Otherwise each pair occupies one shell. The shell is the same for both pairs: if \((2h,3h)\) were in a strictly earlier shell than \((2h+1,3h+1)\), then \(3h<2h+1\), contrary to \(h>1\). (A later shell is impossible when each value is increased by one.) Since \(h\) is odd, the two pairs are opposite-parity pairs with opposite first-term parities. Exactly one agrees with the root preference. Its entire progression occurs in order. \(\square\)

This rules out arbitrary schedules of *contiguous shell boundaries*, not merely geometric radii, but says nothing against general noncontiguous prefix extensions.

## 2. The absolute-value replacement in the #196 extension fails

Kohlmeyer–Kruer's finite support saturates an old branching node by including a preferred value \(x\le 2y\) when a nonpreferred \(y\) is included. On \(\mathbb N_0\) the compatibility proof uses \(c=2b-a\le2b\) when both \(a,b\) are newly appended. The obvious signed substitute \(|x|\le C|y|\), with **any fixed finite** \(C\), cannot provide the same extension.

Use old prefix \(P=(0,1)\). Its closure condition is vacuous, and its only unfinished ordered pair gives \(0,1,2,3\), forcing the old root preference to be odd. Take integers \(B\ge2\) even and \(A>B\) odd with \(A\ge CB\). Let the finite augmented support consist of all even integers with \(|x|\le B\) and all odd integers with \(|x|\le A\). It satisfies absolute-value saturation at its sole old branching node. Append the new entries in any binary order preferring odd at the root.

The already ordered pair \((0,A)\) extrapolates to \(2A,3A\), both outside the support. To stop that four-term progression, the future root preference must put \(3A\) before \(2A\), requiring odd first. But the already ordered pair \((A,-B)\) extrapolates to \(-2B-A,-3B-2A\), both outside the support. Putting the latter before the former requires even first. Thus the new prefix has no single binary preference assignment compatible with both unfinished progressions. This is a failure of the proposed signed extension rule, not a proof that this prefix has no extension by other methods.

The obstruction is directional: when \(|c|>2|b|\) for \(c=2b-a\), the next two values can lie in the other tail from \(a\), whereas old-anchor threats can be in the original tail. A subsequent extension would need to replace the single preference on an entire two-sided residue node or otherwise avoid producing these conflicting pairs.
