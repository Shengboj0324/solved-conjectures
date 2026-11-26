# Fiscus–Hurlbert–Myzelev–Pence grid conjecture

**False.** Player 1 wins the authors’ normal-play dominating-set game on the ladder $P_2\square P_7$. This refutes the whole universal conjecture that Player 2 wins on every rectangular grid with both sides larger than one and an even number of vertices. The target is [Conjecture 24, §5, arXiv:2504.03448v2](https://arxiv.org/html/2504.03448v2#S5) and the same statement is [Conjecture 23, p. 16, in Hurlbert’s author-hosted manuscript](https://glennhurlbert.github.io/Papers/NDSGG.pdf#page=16).

## Rules and a two-neighborhood endgame

Players alternately select previously unchosen vertices into one shared set. The move that first makes that set a dominating set wins. It is legal to choose an already dominated but unchosen vertex. This is not the game in which each move must newly dominate something.

Label the ladder’s two rows $A_1,\ldots,A_7$ and $B_1,\ldots,B_7$. Horizontal neighbors have consecutive indices, and vertical neighbors are $A_i,B_i$. A center $v$ is *outstanding* if no vertex of its closed neighborhood $N[v]$ has yet been chosen. A move hits an outstanding center precisely when it belongs to that neighborhood. Winning means hitting the last outstanding center or centers.

A *pass* is an unchosen vertex outside all outstanding closed neighborhoods. If exactly two outstanding neighborhoods remain, are disjoint, and there are an even number of passes, the player about to move loses. The other player responds to a pass with a pass, and responds to a move into either neighborhood by immediately hitting the other. This also shows that the game does not end on a pass. In the tables below, after five picks there are nine unchosen vertices. Two disjoint outstanding neighborhoods centered at one corner and one noncorner then have sizes three and four, leaving an even number (two) of passes.

## Strategy through the fifth move

Player 1 opens at $A_2$. Player 2 cannot win on move two, because any move hits at most four centers and there are fourteen centers. The first column below lists the pair comprising Player 2’s move two and Player 1’s reply on move three. When Player 2’s move occurs in several rows, Player 1 can use any applicable row. For the first row only, $A_1$ and $B_1$ can be exchanged throughout: after $A_2$ is chosen they both belong just to the outstanding neighborhood at $B_1$, so they are interchangeable as *moves* (not as centers). In particular this row covers $B_1$ as a possible second move. Every other possible second move appears in the first column literally.

The second column lists two centers with disjoint outstanding neighborhoods at the end of move three. Player 2 therefore cannot win on move four. The third column lists unordered response pairs for moves four and five: whichever vertex Player 2 picks, Player 1 picks the other vertex of a pair containing it. The annotation following a pair is the complete set of outstanding centers **after** both those picks; a dash means Player 1 has won on move five. Every nondash annotation lists disjoint neighborhoods of one corner and one noncorner. Each applicable row covers all legal fourth moves except its expressly marked exception.

| Moves 2–3 | Two disjoint centers | Moves 4–5, with outstanding centers after both picks | Exception |
| --- | --- | --- | --- |
| A1/A6 | A4, B7 | A3/A5: B4,B7; A4/A5: B3,B7; A7/B4: –; A5/B2: B4,B7; B3/B5: A4,B7; B4/B6: –; B4/B7: – | B1 |
| A3/A7 | A5, B1 | A1/B5: –; A4/A5: B1,B6; A4/A6: B1,B5; B1/B5: –; B2/B5: –; B3/B6: A5,B1; B4/B7: A5,B1 | None |
| A4/B5 | A6, B1 | A1/A6: B3,B7; A3/B7: A6,B1; A7/B2: –; B1/B6: A7,B3; B3/B7: A6,B1; B4/B7: A6,B1 | A5 |
| A5/B7 | B1, B4 | A1/B3: –; A3/A6: B1,B4; A4/B2: –; A3/A7: B1,B4; B1/B4: –; B2/B5: –; A3/B6: B1,B4 | None |
| A7/B4 | A5, B1 | A1/A6: –; A3/A4: B1,B6; A5/B3: B1,B6; A6/B1: –; B2/B5: –; B6/B7: A5,B1 | None |
| B2/B6 | A4, A7 | A1/A5: A7,B4; A3/A5: A7,B4; A4/A7: –; A6/B4: –; A5/B1: A7,B4; B3/B5: A4,A7; A4/B7: – | None |
| B3/B7 | A4, B1 | A1/A5: –; A3/A6: B1,B5; A4/A6: B1,B5; A7/B4: A5,B1; A5/B1: –; A5/B2: –; B5/B6: A4,B1 | None |

The table uses only the ladder-neighborhood formula. For example, in the first row after the first three picks the outstanding centers are $A_4,B_3,B_4,B_5,B_7$. Choosing $A_3$ hits $A_4,B_3$ among these, and $A_5$ hits $A_4,B_5$. The pair leaves exactly $B_4,B_7$, whose closed neighborhoods are disjoint. All entries are checked by the same deletion rule, starting with every center and deleting the closed neighborhood of each pick. For the first-row exchange, the *moves* can be relabeled, but the named centers are unchanged, since the exchanged moves hit the same remaining centers.

## The two exceptions

1. **Chosen vertices A1, A2, A6, B1.** On move five choose $A_4$. The three surviving neighborhoods are
   - $N[B_3]=\{A_3,B_2,B_3,B_4\}$;
   - $N[B_5]=\{A_5,B_4,B_5,B_6\}$;
   - $N[B_7]=\{A_7,B_6,B_7\}$.

   Their union is the set of all nine unchosen vertices. The middle neighborhood meets each end, while the ends are disjoint. If Player 2 takes $A_5$ or $B_5$, Player 1 takes the other, leaving the two ends and zero passes among the seven unchosen vertices. Otherwise Player 2 hits at least one end. The remaining one or two neighborhoods are nonempty and have a common vertex (if two remain, they are the middle and the opposite end), so Player 1 can finish at once.

2. **Chosen vertices A2, A4, A5, B5.** On move five choose $A_1$. The surviving neighborhoods are
   - $N[B_3]=\{A_3,B_2,B_3,B_4\}$;
   - $N[A_7]=\{A_6,A_7,B_7\}$;
   - $N[B_7]=\{A_7,B_6,B_7\}$.

   The sole pass is $B_1$. If Player 2 hits $N[B_3]$, Player 1 answers at $A_7$, hitting both others. If Player 2 hits both corner neighborhoods, Player 1 answers at $B_3$. If Player 2 hits exactly one corner neighborhood (at $A_6$ or $B_6$), Player 1 takes $B_1$. If Player 2 takes $B_1$, Player 1 takes $A_6$. In these last two cases two disjoint neighborhoods of sizes four and three remain among the seven unchosen vertices, and the two-neighborhood endgame applies.

Thus the first player can win against every sequence of replies. No claim about the classification of all ladders or all winning initial vertices is needed to disprove the conjecture.

## Checks and attribution

[Strategy replay](verify_strategy.py) checks the written responses, their legality, all opponent replies (including passes), and the endgame hypotheses with direct graph-neighborhood operations. The proof above is a finite strategy using a general endgame lemma; it does not require running a minimax search to establish a winning move. No Lean verification is claimed. See the [scope and priority audit](AUDIT.md).
