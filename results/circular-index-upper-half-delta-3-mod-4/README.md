# Graphs with circular chromatic index in the upper half for Δ ≡ 3 mod 4

[Catalogue](../../CONTENTS.md) · [Proof](PROOF.md) · [Exact checks](verify.py) · [Certificates](certificates.json) · [Issue #152](https://github.com/1337isnot1337/solved-conjectures/issues/152)

**Status:** Written proof of Theorem A, and computer-certified Proposition B. The note has been through one independent referee pass by a second model instance, which re-derived every hand claim, found no mathematical error and accepted the note; its minor points m1–m9 are applied. The note is otherwise unrefereed. Proposition B rests on stored certificates checked from the definition.

**Contributor:** [@aadrianvv](https://github.com/aadrianvv).

**Lean status:** full. Lean verifies Theorem A, Proposition B and Corollary C, as well as the ancillary connectivity, retained-block, support-classification and small-parameter claims. [Sources and verification](FORMALIZATION.md).

Primary source: J. Mazák and F. Zrubák, *Circular chromatic index of small graphs*, [arXiv:2603.08822](https://arxiv.org/abs/2603.08822), Section 8 (the remark after Problem 7).

## Result

A $`(p,q)`$-edge-colouring of a graph maps its edges to $`\mathbb Z_p`$ so that edges sharing a vertex get colours at circular distance at least $`q`$; it gives $`\chi'_c\le p/q`$. Mazák and Zrubák remark that for no $`\Delta\ge 8`$ was a single graph with maximum degree $`\Delta`$ and $`\chi'_c\in(\Delta+1/2,\Delta+1)`$ known. [Circulants with circular chromatic index in the upper half](../circular-index-upper-half-circulants/) and [Graphs with circular chromatic index in the upper half for Δ ≡ 2 mod 4](../circular-index-upper-half-delta-2-mod-4/) treat $`\Delta\equiv0,1,2\pmod4`$. This note treats $`\Delta\equiv3\pmod4`$.

**Theorem A.** For every $`g\ge15`$ there is a simple graph $`H_g`$ on $`n=6g+1`$ vertices with maximum degree $`\Delta=4g+3`$ and

```math
\chi'_c(H_g)=\frac{2n+9}{3}=\Delta+\frac23 .
```

**Proposition B (computer-certified).** For $`6\le g\le14`$ the same kind of construction, with base matchings and insertion blocks found by SAT and stored in [`certificates.json`](certificates.json), gives simple graphs on $`6g+1`$ vertices with $`\Delta=4g+3\in\{27,31,\dots,59\}`$ and $`\chi'_c=\Delta+2/3`$.

**Corollary C.** For every $`\Delta\equiv3\pmod4`$ with $`\Delta\ge27`$ there is a simple graph with maximum degree $`\Delta`$ and $`\chi'_c=\Delta+2/3\in(\Delta+1/2,\Delta+1)`$, by a hand proof for $`\Delta\ge63`$.

The construction extends the "Family B" scheme of Section 7.3 of the circulant result, as written out in the Δ ≡ 2 mod 4 note. The translates of two base matchings $`M_0`$ and $`M_1`$, coloured $`3a`$ in $`\mathbb Z_{2n}`$, give a perfect $`(2n,3)`$-colouring of a $`4g`$-regular circulant. Here the base vertex sets are $`W_0=[0,5]\cup[2g+7,4g]`$ and $`W_1=[1,6]\cup[2g+7,4g]`$, a member of a one-parameter family of admissible sets, and every colour class lives on a cyclic interval of 6 vertices and one of $`2g-6`$ vertices. This leaves room for three inserted blocks of three colour classes each: two blocks of length-1 edges, as in Family B, and a third block of edges of lengths 3 and 5. Each block raises $`\Delta`$ by one and keeps the colouring perfect, which gives a $`(2n+9,3)`$-colouring. The base matchings must have $`2g`$ distinct circulant lengths avoiding $`1,3,5`$; Section 4 of the note gives them by explicit formulas for every $`g\ge15`$, in four cases according to $`g\bmod4`$. The lower bound $`\chi'_c\ge|E|/\alpha'`$ with $`\alpha'\le(n-1)/2`$ meets the upper bound exactly. The graphs are not regular: three vertices have degree $`\Delta-1`$.

## Combined status for Δ ≥ 8

The [seven additional certificates by tomdif](../circular-index-upper-half-remaining-deltas/) fill the former gaps below. Together the notes cover every maximum degree at least eight.

With the two earlier results, every $`\Delta\ge8`$ except $`\Delta\in\{9,11,13,15,17,19,23\}`$ has a simple graph with maximum degree $`\Delta`$ and $`\chi'_c\in(\Delta+1/2,\Delta+1)`$:

| $`\Delta\bmod4`$ | covered | source |
|---|---|---|
| 0 | every $`\Delta\ge8`$ | [circulant result](../circular-index-upper-half-circulants/), Theorem 1 (proof) |
| 1 | $`\Delta\ge25`$; $`\Delta=21`$ | [Δ ≡ 2 mod 4 note](../circular-index-upper-half-delta-2-mod-4/), Theorem 1′ (proof); $`\Delta=21`$ by the computer-certified example of the circulant result, Section 7.3, as used in Corollary 3 of the Δ ≡ 2 mod 4 note |
| 2 | every $`\Delta\ge10`$ | Δ ≡ 2 mod 4 note: Theorem 1 for $`\Delta\ge26`$ (proof), Proposition 2 for $`\Delta=10,14,18,22`$ (computer-certified colourings of $`K_n-tK_2`$); $`\Delta=18`$ also by Theorem 2 of the circulant result (proof) |
| 3 | $`\Delta\ge27`$ | this note: Theorem A for $`\Delta\ge63`$ (proof), Proposition B for $`\Delta=27,\dots,59`$ (computer-certified) |

**Limits of the original construction.** The listing above predates the seven additional certificates. Inside this framework (forward insertion of blocks into the cyclic $`q=3`$ base with the $`k`$-family of base sets), exhaustive searches show that there is no graph of this form for $`\Delta=9,11,13,15,17,19,23`$; the mirror form of the insertion lemma, freer insertions and other denominators are not excluded. Searches for $`K_{11}-F`$ ($`\Delta=9`$) timed out. Problem 6 (connectivity) and Problem 7 (denominators $`q\ge6`$) of Mazák and Zrubák are not touched. No literature search was made beyond the sources of the earlier results; the referee checked the Mazák–Zrubák quotation against the arXiv HTML.

## Verification

Run from the repository root with Python 3.10 or later and no other dependencies:

```sh
python3 results/circular-index-upper-half-delta-3-mod-4/verify.py
```

For every $`15\le g\le60`$ (an optional argument changes the bound) the script builds $`M_0`$, $`M_1`$ and the three blocks from the formulas of Sections 4 and 5, and checks the claimed lengths. For each graph it checks that the base matchings are perfect on $`W_0`$ and $`W_1`$ with $`2g`$ distinct lengths, that each block class is a matching on the right vertex set, that the graph is simple and contains $`C_n(S)`$, that $`\Delta=4g+3`$ and $`|E|=2gn+9g`$, the $`(2n+9,3)`$-colouring per vertex from the definition, and $`|E|/((n-1)/2)=p/3=\Delta+2/3`$. It then runs the same checks on the nine certificates of Proposition B, read from `certificates.json`. Six negative controls must be rejected. The script ends with `ALL CHECKS PASSED`.

The script checks finitely many $`g`$. Theorem A for every $`g\ge15`$ rests on the written proof.

Optional checks, not run by CI, all standard library and locating their files relative to their own folder:

- [`indep_check.py`](indep_check.py) is the author's second verifier, which shares no code with `verify.py`. It assigns colours by closed formula and checks all pairs of adjacent edges for $`15\le g\le40`$ and the nine certificates.
- [`review/`](review) contains the referee report [`REVIEW.md`](review/REVIEW.md), the referee's log and scripts, and their recorded `.out` outputs. [`ref_verify.py`](review/ref_verify.py) is the referee's own verifier (Theorem A for $`15\le g\le80`$ with every admissible choice of the block-3 parameters, the certificates, and the window property for general $`k`$); [`mut_test.py`](review/mut_test.py) applies 26 mutations, all of which must be rejected. [`oneblock_brute.py`](review/oneblock_brute.py) and [`threeblock_g5.py`](review/threeblock_g5.py) re-derive the negative claims of Section 8 by exhaustive search without SAT, and [`wenum_check.py`](review/wenum_check.py) checks the enumeration of admissible base sets for $`g=2,3,4`$.

## Files

- [`PROOF.md`](PROOF.md): statement, definitions and lemmas, the base colouring, the explicit base matchings, the three blocks, the proof of Theorem A, the certificates, the split into proved, computed and open, verification, the referee pass and sources.
- [`verify.py`](verify.py): standard-library check of Theorem A for $`15\le g\le60`$ and of the certificates of Proposition B.
- [`certificates.json`](certificates.json): base matchings, insertion colours and blocks for $`6\le g\le14`$.
- [`indep_check.py`](indep_check.py): independent all-pairs re-check.
- [`review/`](review): the referee report, log and scripts.
