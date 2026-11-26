# Nathanson’s linear-form Sidon systems conjecture

**True.** For every fixed linear form with nonzero integer coefficients in $h$ variables, there are $h$ equal-sized sets in $[1,N]$ on whose Cartesian product the form is injective. Their sizes grow at least as a positive constant times $N^{1/h}$. This answers all three questions in [§6 of Nathanson’s paper](https://arxiv.org/html/2104.12711v3#S6) without any prime restrictions.

The proof uses integer place values adjusted to the fixed coefficients. A second construction gives a lower bound from the two largest absolute coefficients, and it yields the exact leading constant when there are two variables. The sets for different coordinates can differ, as in the source statement.

- [Complete proof](PROOF.md)
- [Source, priority search and mathematical review](AUDIT.md)
- [Exact arithmetic checks](verify.py), run with `python3 verify.py`
- [Discovery issue #798](https://github.com/1337isnot1337/solved-conjectures/issues/798)

No Lean verification is claimed.
