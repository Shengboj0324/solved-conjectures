# Fiscus–Hurlbert–Myzelev–Pence grid conjecture

**False.** In the normal-play dominating set game of Fiscus, Hurlbert, Myzelev and Pence, Player 1 wins on the 14-vertex ladder $P_2\square P_7$ by opening in the second column. This refutes their [Conjecture 24 in arXiv:2504.03448v2](https://arxiv.org/html/2504.03448v2#S5), which predicts a Player 2 win on every even rectangular grid with both sides greater than one.

The proof gives Player 1’s responses and reduces the remaining play to an endgame with two disjoint closed neighborhoods. It uses the authors’ rule that any unchosen vertex can be picked, even if already dominated.

- [Proof and explicit strategy](PROOF.md)
- [Exact scope, priority search and independent checks](AUDIT.md)
- [Discovery issue #791](https://github.com/1337isnot1337/solved-conjectures/issues/791)

Run from this directory:

```sh
python3 verify_strategy.py
python3 check_minimax.py
```

The first script checks the written strategy; the second computes the game values independently. No Lean verification or external peer review is claimed.
