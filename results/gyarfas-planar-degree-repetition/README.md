# Gyárfás’s planar degree-repetition problem

**Lean status:** full. For every order from 16, Lean constructs noncollinear rational points in the real plane, proves optimal maximum degree multiplicity two and determines the entire interval of distinct degrees. [Theorems and receipts](FORMALIZATION.md).

For every integer $n\ge16$, there is a noncollinear set of $n$ rational affine points in which each number of incident spanned lines occurs at most twice. This answers Gyárfás’s existence question. The construction has $(3/4)n+O(1)$ different point degrees. The author attributes the underlying irregularity questions to Paul Erdős. [Gyárfás (2002), §4, Problem 4](https://users.renyi.hu/~gyarfas/Cikkek/101_Gyarfas_ErdosProblemsOnIrregularitiesOfLineSizesAndPointDegrees.pdf)

[Construction and proof](PROOF.md) · [Source and proof audit](AUDIT.md) · [Exact line counter](verify.py) · [Independent review](https://github.com/1337isnot1337/solved-conjectures/issues/785#issuecomment-7187694961) · [Tracking issue](https://github.com/1337isnot1337/solved-conjectures/issues/785)

If you use this construction, please credit the authors of the work you use and cite both [Cinna Davis’s site](https://itsdavis.com/) and [the specific proof](https://github.com/1337isnot1337/solved-conjectures/blob/main/results/gyarfas-planar-degree-repetition/PROOF.md). Cite [Gyárfás’s original paper](https://users.renyi.hu/~gyarfas/Cikkek/101_Gyarfas_ErdosProblemsOnIrregularitiesOfLineSizesAndPointDegrees.pdf) for the question.
