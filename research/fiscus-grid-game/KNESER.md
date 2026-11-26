# Fiscus–Hurlbert–Myzelev–Pence Kneser game question

[Problem 29 of arXiv:2504.03448v2](https://arxiv.org/html/2504.03448v2#S5) asks who wins the authors’ normal-play dominating set game on $K(m,2)$ for $m\ge6$. **Player 1 wins on move three, from any opening.**

A vertex is a two-element subset of $[m]$. After some vertices are chosen, an unchosen pair is undominated exactly when it meets every chosen pair. Let $A$ and $B$ denote the first two moves. They cannot end the game: if $A$ meets $B$, their symmetric difference is a still-unchosen pair meeting both; if they are disjoint, take one point from each.

- If $A$ and $B$ meet, choose their symmetric difference. The three selected edges form a triangle on three ground points. A two-element set meeting all three edges must contain two of those three points, so it is itself chosen.
- If $A$ and $B$ are disjoint, choose any pair of ground points outside $A\cup B$. This is possible for $m\ge6$. A pair cannot meet three disjoint selected pairs.

Both replies create a dominating set and win immediately. The two static dominating-triple types and the domination number three were already given by Jaroslav Ivančo and Bohdan Zelinka, [Theorem 1 (1993)](https://dml.cz/bitstream/handle/10338.dmlcz/126050/MathBohem_118-1993-2_3.pdf). The game answer is a short application: every pair of distinct openings extends to one of those triples. This note is a companion to the distinct [grid counterexample](https://github.com/1337isnot1337/solved-conjectures/tree/main/results/fiscus-grid-game), not a second new named conjecture entry. No priority claim is made for the game corollary itself.
