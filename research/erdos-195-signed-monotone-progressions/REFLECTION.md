# Erdős–Graham monotone progression conjecture

[Erdős #195](https://www.erdosproblems.com/195) · [Issue #810](https://github.com/1337isnot1337/solved-conjectures/issues/810). The signed unrestricted question is open.

## Avoiding every odd common difference on the signed integers

A permutation of all signed integers can avoid every monotone 4-AP of odd common difference. The construction actually avoids every ordered odd–even–odd 3-AP, which is stronger in this direction: every odd-step 4-AP has such a consecutive triple in one of its first or last three terms.

Fix any enumeration \(b_1,b_2,\ldots\) of the even integers. Before appending \(b_i\), enlarge the set of previously listed odd integers to a finite interval of odds symmetric about \(b_i\). Append only the newly needed odds, in any order, then append \(b_i\). At step \(i\) take the interval large enough to contain every odd integer of absolute value at most \(i\), in addition to the odds already listed. These requirements are finite, so the procedure is a permutation of \(\mathbb Z\).

If an already listed odd \(a\) precedes the even \(b_i\), the reflected odd \(2b_i-a\) also precedes \(b_i\). Thus the ordered odd–even–odd triple is impossible, in either numerical direction. This does not require a one-sided inequality or a parity-block extension with an odd-first infinite tail. [LeSaulnier–Vijay](https://arxiv.org/abs/1004.1740) and [Adenwalla](https://arxiv.org/html/2211.04451v7) give restricted-difference constructions on the positive domain. This argument treats the two-sided signed domain directly; no priority claim is made for the restricted assertion.

## Why the directional rule cannot recurse

One tempting way to handle arbitrary common differences is to impose an analogous directional triple avoidance at each binary residue node: mark either child as preferred, and forbid any in-order 3-AP with its endpoints in that child and its middle in the other child. Taking the node of the common \(2\)-adic valuation would then exclude every 4-AP. In fact, this requirement is inconsistent already at the root and its preferred child.

**Proposition.** In a permutation of \(\mathbb Z\), choose a preferred parity, and choose a preferred residue modulo 4 within that parity. It is impossible to have both of the following:

1. No ordered odd-step triple with its two endpoints in the preferred parity.
2. No ordered triple of step congruent to \(2\bmod4\) with its two endpoints in the preferred residue modulo 4 within that parity.

**Proof.** At any nonpreferred element \(b\) at a node, write \(A_b\) for the finite set of preferred entries preceding it within the node. Avoiding the directional triple is equivalent to invariance of \(A_b\) under \(a\mapsto 2b-a\). The reflection has no fixed point in the preferred child, so \(|A_b|\) is even. A nonempty finite set cannot be invariant under reflections about two distinct centers: their composition is a nonzero translation. Since the \(A_b\) are nested as index increases, their sizes therefore increase by at least two at every successive nonpreferred entry after the first preferred entry. In any prefix of this node, if \(u\) entries are preferred and \(v\) nonpreferred, then \(u\ge2(v-r)\), where \(r\) is the finite number of nonpreferred entries before the first preferred entry.

Now take prefixes immediately before successive nonpreferred root entries \(b\). By the root rule the set of previously listed root-preferred entries is invariant under \(a\mapsto2b-a\). This reflection swaps the two residue classes modulo 4 inside the root-preferred parity, regardless of which parity was chosen. Its two child counts satisfy \(u=v\). But those counts tend to infinity, violating \(u\ge2(v-r)\) at the preferred child. \(\square\)

A full construction must allow some directional shorter triples and prevent them from extending. In terms of cross-parity comparisons, define \(s(e,o)=1\) if the even \(e\) precedes the odd \(o\). For a numerical progression \(a,b,c,d\) whose parities are odd, even, odd, even, a monotone 4-AP in either direction is exactly one of the patterns \(010,101\) in \((s(b,a),s(b,c),s(d,c))\). The stronger reflection rule excludes too many comparison patterns. This reformulation keeps only the necessary local restrictions.
