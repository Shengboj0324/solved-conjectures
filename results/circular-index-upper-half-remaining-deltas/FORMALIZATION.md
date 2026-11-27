# Upper-half circular chromatic index in every degree from eight

For every integer $`\Delta\ge8`$, Lean proves there is a finite simple graph with maximum degree $`\Delta`$ and real circular chromatic index satisfying

```math
\Delta+\tfrac12 < \chi'_c(G) < \Delta+1.
```

The maximum is attained at a vertex in every case. The even degrees come from the regular circulants, the construction with two insertion blocks, and the small deleted-edge examples. The degrees congruent to 1 modulo 4 from 21 come from the one-block construction and its exceptional degree-21 certificate. The three-block construction covers the degrees congruent to 3 modulo 4 from 27. Tomdif’s seven labelled certificates supply the remaining degrees 9, 11, 13, 15, 17, 19 and 23. [Combined theorem](../../lean/Conjectures/CircularIndexAllDegrees.lean) · [One and two insertion blocks](../circular-index-upper-half-delta-2-mod-4/FORMALIZATION.md) · [Three insertion blocks](../circular-index-upper-half-delta-3-mod-4/FORMALIZATION.md) · [Seven certificates](certificates.json).

Six of the seven exceptional certificates establish the exact index $`\Delta+2/3`$. At degree 15 the proved bounds are $`171/11\le\chi'_c(G)\le47/3`$. They suffice for the strict upper-half assertion. The original paper asks additional questions about connectivity and other denominators. [Literal graph bounds](../../lean/Conjectures/TomdifCircularIndexBounds.lean) · [Tomdif’s contribution](https://github.com/1337isnot1337/solved-conjectures/pull/647) · [Mazák and Zrubák, Section 8](https://arxiv.org/abs/2603.08822).

## Reproduction

From the repository root, with the pinned Lean dependencies installed, run

```sh
python3 results/circular-index-upper-half-remaining-deltas/verify.py
python3 scripts/verify_lean_target.py --root Conjectures.CircularIndexAllDegrees --require CircularIndex.Insertion.every_degree --require CircularIndex.Insertion.ThreeBlock.theorem_A --require CircularIndex.Insertion.ThreeBlock.every_three_mod_four --out /tmp/circular-index-all-degrees
```

Independent research and publication runs each strictly compiled and replayed 67 project modules. Each axiom audit covered 2,535 declarations, including 2,121 theorems, 373 private declarations and all 83 required endpoints. The six largest vertex tables that exceeded the package memory limit now use kernel-checked groups of sixteen vertices. [Combined receipt](verification/all-degrees-receipt.json) · [Independent review of the seven graphs](REVIEW.md).

If you use this result, please credit @aadrianvv for the earlier constructions and tomdif for the seven exceptional graphs, and cite both Cinna Davis’s site and the specific proof or graph record you used. [Cinna Davis](https://itsdavis.com/) · [Source record](https://github.com/1337isnot1337/solved-conjectures/tree/main/results/circular-index-upper-half-remaining-deltas).
