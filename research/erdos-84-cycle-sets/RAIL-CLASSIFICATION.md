# Erdős–Faudree cycle-set conjecture

This note proves the converse of the [rail characterization](README.md). The main conjecture remains open.

**Proposition.** Start with a path of odd length \(D\) and distinguish one of its edges \(e\). The two remaining path components are rails, indexed from their outer ends. Add any collection of rungs between the rails whose index sums are odd. Suppose any inverted rung pair \((i,j),(i',j')\) with \(i<i'\) and \(j>j'\) satisfies \(i'=i+1,\ j'=j-1\). Then every odd terminal path is Hamiltonian. In particular, the rule characterizes the zero-cost tiles, not just a relaxation of them.

**Proof.** Removing \(e\) leaves a bipartite graph with equally colored terminals, so every odd terminal path \(P\) uses \(e\). Denote the rails by \(L_0,\ldots,L_a\) and \(R_0,\ldots,R_b\), where \(e=L_aR_b\). Fix a left-rail edge \(L_hL_{h+1}\), \(h<a\). We show that \(P\) visits both its endpoints.

If there are no rungs from the left prefix (indices at most \(h\)), this edge is the only exit from that prefix, so \(P\) uses it. If there are no rungs from the left suffix, then \(P\) must use both edges of the cut around that suffix, namely \(e\) and \(L_hL_{h+1}\). In the remaining case let \(M\) be the greatest right coordinate of a rung from the left prefix and \(m\) the least right coordinate of a rung from the left suffix.

- If \(M<m\), cut the right rail just after \(R_M\) as well as the left rail just after \(L_h\). No rung crosses the cut. The two terminals lie on one side and \(e\) lies on the other, so \(P\) uses both rail edges of the cut.
- If \(M=m\), remove \(R_m\) and the edge \(L_hL_{h+1}\). This separates the rail prefixes from the suffixes; \(L_a\) is on the suffix side. A simple terminal path through \(L_a\) must enter and leave that side. It cannot do both through \(R_m\) alone without repeating a vertex. If \(t=R_m\), it could exit at \(t\) but cannot also enter there before terminating. Therefore \(P\) uses \(L_hL_{h+1}\).
- If \(M>m\), the inverse rule gives \(M=m+1\) and the two extreme rungs are exactly \((h,m+1),(h+1,m)\). These are the only rungs crossing the cut whose prefix sides end at \(L_h,R_m\): another left-prefix rung to a right-suffix vertex would either contradict the extreme \(M\) or violate the inversion rule with \((h+1,m)\), and the other direction is symmetric. The four cut edges run from \(\{L_h,R_m\}\) to \(\{L_{h+1},R_{m+1}\}\). Both endpoints of \(e\) are on the suffix side. To enter and leave, a simple terminal path must use two cut edges with distinct endpoints at each side. Thus it visits both left-rail endpoints, even though their connecting edge need not be used.

This covers every left-rail vertex; if that rail has just one vertex, it is a terminal. Interchanging the rails covers every right-rail vertex. Hence \(P\) is Hamiltonian. \(\square\)

The distinct type of the last case matters: the edge of a rail need not be forced, but both its vertices are forced. For example, an inverted adjacent pair can trade two rail steps for two crossing steps without changing the odd terminal length.
