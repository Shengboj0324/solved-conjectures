# Real planar degree repetition at every order from sixteen

For every integer $n\ge16$, Lean constructs a set of $n$ rational points, embeds it in the real affine plane, and proves that it is noncollinear. Every degree occurs at most twice and some degree occurs exactly twice. A point’s degree counts the distinct real affine lines it spans with the other points. The pigeonhole lower bound applies to every real set of at least two points. [All-order theorem](../../lean/Conjectures/GyarfasPlanarUniform.lean) · [Optimality](../../lean/Conjectures/GyarfasPlanarOptimal.lean) · [Gyárfás’s original question, Section 4, Problem 4](https://users.renyi.hu/~gyarfas/Cikkek/101_Gyarfas_ErdosProblemsOnIrregularitiesOfLineSizesAndPointDegrees.pdf).

Write $n=2k+e$, with $k\ge8$ and $e\in\{0,1\}$. The $k$ off-axis points are $\left(1/(i+1),i^2/(i+1)\right)$ for $0\le i<k$. On the vertical axis the heights are $0,2,3,\ldots,k-1,2k-3$, with height $-1$ added for odd $n$. The line through off-axis points with distinct indices $i,j$ meets the axis at height $i+j$. Lean proves that these secants and the vertical line account for every coincidence used in the two degree formulas. [Coordinates and cardinality](../../lean/Conjectures/GyarfasPlanarConfiguration.lean) · [Secants](../../lean/Conjectures/GyarfasPlanarSecants.lean) · [Off-axis degrees](../../lean/Conjectures/GyarfasPlanarOffDegrees.lean) · [On-axis degrees](../../lean/Conjectures/GyarfasPlanarAxisDegrees.lean).

The degrees form the entire integer interval from $k+1-\lfloor k/2\rfloor$ through $2k+e-3$. Its size is $s=k+\lfloor k/2\rfloor-3+e$. The uniform bound $11\le3n-4s\le14$ proves the claimed $(3/4)n+O(1)$ estimate. [Spectrum and error bound](../../lean/Conjectures/GyarfasPlanarSpectrum.lean) · [Multiplicity argument](../../lean/Conjectures/GyarfasPlanarMultiplicity.lean).

Two independent runs strictly compiled all 13 project modules, audited all 369 declarations, and replayed each module with the pinned stock Lean kernel. Each audit covered 340 theorems, 121 private declarations and all 58 required endpoints. [All-order verification receipt](verification/uniform-receipt.json).

## The sixteen-point witness

Lean proves that the published configuration at order 16 consists of sixteen noncollinear rational points. After embedding them in the real affine plane, every number of incident spanned lines occurs at most twice. Exactly two points have degree 9. This settles the existence question in Section 4, Problem 4 of Gyárfás’s paper. [Lean theorem](../../lean/Conjectures/GyarfasPlanarWitness.lean) · [Gyárfás’s original question](https://users.renyi.hu/~gyarfas/Cikkek/101_Gyarfas_ErdosProblemsOnIrregularitiesOfLineSizesAndPointDegrees.pdf).

The eight off-axis points are $\left(1/(i+1),i^2/(i+1)\right)$ for $0\le i<8$. The other eight points are $(0,s)$ at heights $s\in\{0,2,3,4,5,6,7,13\}$.

For each pair of distinct points, the formalization identifies its affine span with either the vertical line through the first point or the line with the computed slope. Different directions through a point give different sets of real points. An injective map from rational slopes to real slopes therefore preserves the number of distinct incident lines and the multiplicity of each degree. Three of the listed points form a noncollinear triangle. [Affine lines and directions](../../lean/Conjectures/GyarfasPlanarLines.lean) · [Transfer to the real plane](../../lean/Conjectures/GyarfasPlanarRational.lean).

The independent checker computes the actual real-line incidences using primitive integer equations at 116 sample orders. [All-order proof](PROOF.md) · [Exact line counter](verify.py).

Independent research and publication runs each rebuilt three Lean modules from source, checked all 45 declarations and replayed every project module with the pinned stock kernel. The audit covered 31 theorems, nine private declarations and 13 required endpoints. [Verification receipt](verification/sixteen-receipt.json).

If you use the configuration or its Lean proof, please credit Cinna Davis, cite Gyárfás’s question and its attribution to Paul Erdős, and link both the author’s site and the proof record used. [Cinna Davis](https://itsdavis.com/) · [Specific proof record](https://github.com/1337isnot1337/solved-conjectures/tree/main/results/gyarfas-planar-degree-repetition).
