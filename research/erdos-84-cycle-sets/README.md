# Erdős–Faudree cycle-set conjecture

[Erdős #84](https://www.erdosproblems.com/84) · [Issue #820](https://github.com/1337isnot1337/solved-conjectures/issues/820).

**Status:** the lower-limit assertion \(f(n)/2^{n/2}\to\infty\) remains open. The first assertion \(f(n)=o(2^n)\) is [Verstraëte's theorem](https://mathweb.ucsd.edu/~jverstra/numcyc.pdf), strengthened by [Nenadov](https://arxiv.org/abs/2501.09904). [Botsford](https://zenodo.org/records/22966207) gives a constant-factor lower bound, not divergence. This note proves an exact obstruction for *all widths* of his zero-extra-vertex tile construction, including any final tile with the same terminal-path condition. It does not bound general cycle sets.

## The zero-cost theorem

Let \(H\) be a finite simple graph on \(2r+2\) vertices with terminals \(s,t\). Assume its set of odd lengths of simple \(s\)-to-\(t\) paths is exactly \(\{2r+1\}\). Define \(X=\{x:2x+1\text{ is an odd cycle length of }H\}\) and \(Q=\{r+1-\ell/2:\ell\text{ is an even terminal path length}\}\), as in Botsford §5.

Then:

1. \(H\) automatically has a continuation edge: removing it makes \(H\) bipartite with its endpoints of the same color and terminals of the same color.
2. \(X=Q\).
3. The even cycle lengths are exactly \(2+2|x-x'|\) for distinct \(x,x'\in X\), with \(4\) possibly added.

The third conclusion means a single optional bit, and the bit is irrelevant if \(X\) contains consecutive labels.

### Two rails

Write \(D=2r+1\). An odd terminal path of length \(D\) is Hamiltonian; order its vertices as \(v_0=s,\ldots,v_D=t\). Every chord \(v_iv_j\), \(i<j\), has \(j-i\) even: a nontrivial odd gap would permit the shortcut directly along this chord, giving a shorter odd terminal path. Two chords with disjoint path-edge intervals, even if they share a boundary vertex, could both be used as shortcuts; each changes parity, so their combined shortening would again give a shorter odd terminal path. Hence the intervals of gaps \(\{i,\ldots,j-1\}\) for all chords pairwise intersect. Finite intervals have a common gap, say \(a\). If there are no chords, choose any gap. All chords cross \(e=v_av_{a+1}\). Flip the original path parity on the segment to the right of \(e\). In \(H-e\) all edges join opposite colors, and both \(s,t\) and the two endpoints of \(e\) are respective equal-color pairs. This proves (1).

The graph \(H-e\) comprises a left rail \(L_i=v_i\) (\(0\le i\le a\)), a right rail \(R_j=v_{D-j}\) (\(0\le j\le b=D-a-1\)), and rungs \(L_iR_j\). Both rails are ordered from an outer terminal toward \(e\). Call two rungs inverted if their coordinates are \((i,j),(i',j')\) with \(i<i'\), \(j>j'\).

**Adjacent-inversion rule.** For an inverted pair, the terminal path that goes from \(s\) to \(L_i\), crosses to \(R_j\), walks to \(R_b\), crosses \(e\) backwards, walks to \(L_{i'}\), crosses to \(R_{j'}\), and finishes at \(t\) is simple. It uses \(e\), so it has odd length. That length is \(D+2-(i'-i)-(j-j')\), and must equal \(D\). Therefore \(i'=i+1\), \(j'=j-1\).

### Every outer path length is a one-rung length

The following holds for any pair of finite rails with the adjacent-inversion rule, even after truncating their ends: the lengths of simple paths between their two outer endpoints are exactly the lengths of paths that use one rung.

To prove this, induct on the number of rungs of a given simple path. The number is odd; a one-rung path needs nothing. Translate the outer endpoint coordinates to zero. Let \((i,j)\) be the first rung and \((i',j')\) the last. If these differ, the initial left rail segment visits every coordinate up to \(i\), and the final right rail segment every coordinate up to \(j'\). Thus \(i'>i\), \(j'<j\), and by the rule \(i'=i+1\), \(j'=j-1\). The middle subpath, reversed if needed, lies on the rails truncated to minima \(i'\) and \(j\): all its left vertices avoid \([0,i]\) and all its right vertices avoid \([0,j']\). Its length by induction equals \((p-i')+(q-j)+1\) for some rung \((p,q)\) there. Restoring the initial and final parts gives
\[
i+1+(p-i')+(q-j)+1+1+j'=p+q+1,
\]
a one-rung path length on the original rails. The converse inclusion is immediate. The rule is unchanged on reversing both rail orders, so the inner endpoints have the analogous property.

In the full graph, every even terminal path avoids \(e\); every odd cycle uses \(e\). By the preceding length statement, the even terminal paths have lengths \(i+j+1\) over rungs, while the odd cycles have lengths \(a-i+b-j+2=D+1-i-j\) over rungs. Both give the same label \(x=(D-i-j)/2\). This proves (2), including the case of no rungs.

### Even cycles are differences

All even cycles avoid \(e\). Given a cycle in the two rails, consider its minimum coordinates on each rail. Each is incident with a rung of the cycle: without a rung it would need two rail neighbors, one smaller. If one rung realizes both minima, remove it from the cycle. The rest is an outer-to-outer path in the rails truncated at those minima. By the length statement, its length is the length of a single-rung path there. Adding back the minima rung gives \(2+(p+q)-(i+j)\), a difference of two distinct labels doubled and then increased by two.

If no rung realizes both minima, choose the two rungs incident with them. They are inverted, so they have the form \((i,j+1),(i+1,j)\). The minimum left vertex can have no other rung in the cycle: a second one would either realize both minima or violate the adjacent-inversion rule with \((i+1,j)\). The symmetric argument holds for the minimum right vertex. The two rail edges toward the next coordinates are therefore forced, and the four edges close a 4-cycle. Conversely any such inverted pair gives a 4-cycle. Any pair of rungs with distinct labels cannot be inverted (an adjacent inversion has equal coordinate sums); the two rail segments between them and the two rungs give their claimed difference length. This proves (3).

## Consequence for arbitrary sequences of zero-cost substitutions

Start with a triangle and iteratively replace the distinguished edge by any tile satisfying the zero-cost theorem. By (1) every tile can continue, and by Botsford's exact substitution formula, insertion of width \(r\) shifts all previous odd labels by \(r\) and adds the local labels \(X\subseteq[1,r]\). All cross even cycle lengths are of the form \(2((y+r)-x)+2\) for a previous label \(y\) and a new label \(x\): this is precisely the crossing-cycle formula with \(Q=X\). The previous even differences are unchanged by translation, and the new internal even lengths are local label differences with the possible 4-cycle flag. Thus at every step the entire even spectrum is determined by the odd labels and at most one flag for length \(4\).

At total width \(w\), the graph has \(2w+3\) vertices and its odd labels lie in \([1,w+1]\), containing \(w+1\). There are at most \(2^w\) label sets and two flags. Summing over widths with \(2w+3\le n\) for isolate padding gives \(O(2^{n/2})\). Ordinary tiles already attain the matching order. The obstruction holds without a finite tile catalogue and with arbitrary choices of width.

Any successful variant of this method needs tiles with extra vertices, multiple odd terminal path lengths, or a construction other than two-terminal replacement.

## Priority screen and checks

The source trail includes the cycle-set survey literature, Verstraëte's original paper, Nenadov's 2026 publication, the [Erdős wiki](https://erdosproblems.ai/wiki/problems/extremal_graph_theory/E0084), the Dunås thesis through its catalogue and subsequent notes, and Botsford's full paper and computational supplement. Botsford's catalogue has two zero-cost tiles, both ordinary width-one tiles. His §16 explicitly leaves the full conjecture open, and the all-width rigidity theorem is not part of that paper. Exact-title and problem-number searches across arXiv, Hexagon, the Erdős forum, and GitHub found no full resolution of the lower-limit question.

As a sanity check, an independent DFS enumerated the terminal paths and simple cycles in every candidate rail graph obeying the inverted-pair rule through \(D=11\) (12,440 cases, counting different choices of the cut), plus 2,000 wider randomized fixtures. The proof uses no finite enumeration.
