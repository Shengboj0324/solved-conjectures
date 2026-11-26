# Songsuwan’s Node-Kayles branch-periodicity conjecture

[Conjecture 2, arXiv:2512.24221v2](https://arxiv.org/html/2512.24221v2#S4) · [Issue #822](https://github.com/1337isnot1337/solved-conjectures/issues/822). **Partial:** the full conjecture remains open.

## Period two when the only connected quiet residual is a leaf

Let \(H\) be a fixed connected rooted graph, rooted at \(v\), satisfying the following condition: for every vertex \(x\ne v\), deletion of the closed neighborhood of \(x\) either deletes \(v\), or leaves \(v\) as an isolated vertex in \(H-N_H[x]\). Let \(G\) be any finite host and \(u\) any of its vertices. Join \(u\) by a single edge to the root of each of \(k\) copies of \(H\).

**Theorem.** The resulting Node-Kayles Grundy sequence is eventually 2-periodic. The conclusion remains true with any fixed number of additional leaves at \(u\). A sufficient onset is
\[
1+(|V(G)|+1)(6|V(H)|+10).
\]

The condition includes stars rooted at their center, and every depth-two level-regular tree with branching sequence \((1,b)\). It also includes arbitrary connected graphs in which every vertex outside the root's closed neighborhood is adjacent to every neighbor of the root. Indeed, if a nonroot move does not delete \(v\), it then deletes all of its neighbors.

### Finite residual types

A move in a branch at its root removes \(u\). A move inside a branch at a nonroot vertex leaves \(u\) and removes the intact copy. Under the hypothesis, its only possible remaining attachment is one leaf at \(u\), and all other remaining components are detached. Their Grundy values add by xor. Let \(C_0\) be the set of detached xor values for the nonroot moves leaving no attachment, and \(C_1\) the values for those leaving one extra leaf. Write \(q=|C_0|+|C_1|\le |V(H)|-1\).

Use [Songsuwan's Leaf-Pair Lemma, Lemma 2.1](https://arxiv.org/html/2512.24221v2#S2), to reduce the number of additional leaves to \(\ell=0,1,2\), distinguished as zero, positive odd, or positive even. The lemma applies with the entire graph containing the intact copies regarded as the host; it does not bound that host's size. The leaf-adding map \(T\) on these labels sends \(0\mapsto1\), \(1\mapsto2\), \(2\mapsto1\).

Let \(F_\ell(k)\) be the value with the fixed host, \(k\) intact copies, and leaf label \(\ell\). In a game with \(k\ge1\), there are three kinds of options:

- Any move removing \(u\) leaves the other branches detached. Whether the move plays \(u\), a host neighbor, an added leaf, or one branch root determines which fixed detached components occur. Apart from this, the value depends only on the parities of \(k,\ell\); availability is constant for \(k\ge1\) at a fixed \(\ell\).
- A move inside the host not removing \(u\) changes only the host to a graph with fewer vertices.
- A quiet branch move gives \(F_\ell(k-1)\oplus c\) for \(c\in C_0\), or \(F_{T(\ell)}(k-1)\oplus c\) for \(c\in C_1\).

By induction on the host size, the first two kinds form a set \(S_\ell(k\bmod2)\) of options independent of \(k\) within its parity for sufficiently large \(k\), for all three leaf labels. The induction is simultaneous in the three labels. The starting case has host \(\{u\}\) and no quiet host moves.

### The two-move mex comparison

First take \(\ell=1,2\). A quiet move type copied in a second intact branch returns to the same leaf label, because \(T^2(\ell)=\ell\) there, and its two detached xor increments cancel. For sufficiently large \(k\), the candidate \(F_\ell(k-2)\) is not among the fixed-parity options from \(F_\ell(k)\), since those options also occurred at \(k-2\). Nor can it be an option reached by a quiet branch move. If it equaled \(F_{\ell'}(k-1)\oplus c\), this intermediate state's own options would include \(F_\ell(k-2)\oplus c=F_{\ell'}(k-1)\), which is impossible. Thus
\[
F_\ell(k)\le F_\ell(k-2)\qquad(\ell=1,2)
\]
by the least-excluded-value rule. Each parity subsequence is eventually constant.

For \(\ell=0\), options creating a leaf now have stable values at each parity and can be included in \(S_0\). The remaining moves all keep leaf label zero. The same two-move comparison establishes \(F_0(k)\le F_0(k-2)\) for all sufficiently large \(k\), proving the theorem.

### Quantitative onset

Suppose all smaller-host sequences are 2-periodic from index \(B\ge1\). For \(k\ge B\), each \(F_\ell(k)\), \(\ell=1,2\), is one of the first \(q+1\) omissions of its fixed set \(S_\ell(k\bmod2)\). On the parity of \(B\), the two-coordinate vector can undergo at most \(2q\) strict decreases in comparisons two steps apart. One comparison must give equality by \(B+4q+2\). Equality of the two-coordinate vector propagates to all subsequent steps, since the recurrence is a deterministic map from the previous vector and the current parity. Now the options into leaf label one have stable parity from \(B+4q+3\); the scalar label-zero recurrence takes at most \(q+1\) comparisons two steps apart to reach equality. The cost of a host induction layer is therefore at most \(6q+5\), and the stated conservative bound follows.

## Boundary of the proof

For a general branch, a quiet move can leave a nontrivial smaller rooted graph still attached. Making the move twice then appends two such graphs. Only in the leaf case does a known universal capping lemma return to the identical comparison state. It is not valid to discard pairs of arbitrary rooted graphs: Songsuwan's Twin Lemma requires a condition on the host and its quietly reachable states. Thus this argument does not say that arbitrary level-regular branches can be capped.

I searched the exact titles, author, manuscript/arXiv versions, and references on rooted attachments and repeated impartial games. Songsuwan's source gives the leaf case for every host and the depth-two formula for special level-regular hosts; the proof here covers the wider root-or-leaf residual condition for arbitrary hosts. No complete follow-up for Conjecture 2 was located.
