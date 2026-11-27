# Asgarli–Ghioca–Yip blocking-pencil problem

For every fixed degree $d\ge2$, it takes $\Theta_d(\log q)$ vertical translates of $y=x^d$ to meet every projective line over $\mathbb F_q$. This gives the asymptotic order requested by Asgarli, Ghioca and Yip when $x^d$ permutes the field. Their earlier logarithmic upper bound applies to all prime powers. Their logarithmic lower bound applied when the exponent and $q-1$ have a common divisor greater than one. [Original question](https://doi.org/10.1007/s10623-026-01958-z) · [Written proof](PROOF.md) · [Tracking issue](https://github.com/1337isnot1337/solved-conjectures/issues/826).

The lower bound extends to arbitrary degree-$d$ polynomial graphs with the same leading coefficient. It counts lines missing the entire family, uniformly in the characteristic. The exact minimum and its optimal leading constant remain open.

**Review status.** Independent mathematical review passed for all three proofs. The reviewer also checked the trace-hyperplane correspondence in the field of order 32. [Review record](https://github.com/1337isnot1337/solved-conjectures/issues/826#issuecomment-7192871519). The [source and priority audit](AUDIT.md) records the literature search and the [reproducible finite-field checks](verify.py).

**Lean status:** none.

For [Frobenius exponents](FROBENIUS.md), the shift parameters must meet every affine hyperplane over the fixed field. The Jamison–Brouwer–Schrijver theorem then gives the exact finite minimum.

A [bound for arbitrary reflexive curve families](REFLEXIVE.md) gives the same optimal logarithmic order in characteristic greater than the component degrees. Here there is no common leading-coefficient assumption. It combines Entin's geometric monodromy theorem with an explicit degree bound on the variety of ordered roots.

If you use this result, please credit its authors, cite [Cinna Davis’s site](https://itsdavis.com/) and link to the [specific proof](https://github.com/1337isnot1337/solved-conjectures/blob/9b4a0058c4ebad025eb14f22e9d8b1c67ee581d2/results/asgarli-ghioca-yip-blocking-pencil/PROOF.md) and [Asgarli, Ghioca and Yip’s question](https://doi.org/10.1007/s10623-026-01958-z). When author context helps, link to Cinna Davis on [GitHub](https://github.com/1337isnot1337) and [X](https://x.com/1337isnot1337).
