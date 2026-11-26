# Lean verification of the Caiolo–Ferroni–Hoster family

[The theorem `CaioloFerroniHoster.counterexample_family`](../../lean/Conjectures/CaioloFerroniHoster.lean)
constructs an actual finite Mathlib matroid for every prime power q ≥ 17.
It proves simplicity, rank five, and the two root conclusions. The dual Chow
quartic is positive everywhere on the real line. The dual right augmented
quintic has its only real zero at −1, where the derivative is nonzero.
Neither polynomial splits over the reals.

## Correspondence with the source

- The [graph-space module](../../lean/Conjectures/CaioloFerroniHosterGraphs.lean)
  uses the four Frobenius coefficients over the degree-four field extension,
  proves the graph dimension, and bounds pairwise intersection dimensions.
  [The matroid module](../../lean/Conjectures/CaioloFerroniHosterMatroid.lean)
  constructs the independence predicate and identifies the resulting flats.
  The construction follows Bérczi–Coron–Eur–Li's hyperplane coalescence.
  [Construction source](https://arxiv.org/html/2610.17135v1#S4.SS2)
- The [subspace-counting module](../../lean/Conjectures/CaioloFerroniHosterSubspaces.lean)
  proves the Gaussian recurrence by projection along a line.
  The [flag-counting module](../../lean/Conjectures/CaioloFerroniHosterFlags.lean)
  identifies the product-lattice flag counts and proves the exact change
  under replacement of the selected hyperplanes.
- The [arithmetic module](../../lean/Conjectures/CaioloFerroniHosterArithmetic.lean)
  uses the chain expansion of the characteristic-kernel recurrences in
  CFH Propositions 4.6–4.7. Lean proves the rank-five specialization of the
  gamma identities in Theorem 4.9 by expanding all possible internal rank
  sets. [Original statement and polynomial identities](https://arxiv.org/html/2605.28474v1)
- The [certificate](../../lean/Conjectures/CaioloFerroniHosterCertificate.lean)
  checks the exact polynomial identities for the discriminants after the
  shift q = 17 + s and proves their strict signs for all s ≥ 0. The proof
  then completes the square and shows the augmented polynomial has a
  strictly positive quartic factor.

## Kernel-level statement

`counterexample_family` is stated for `matroidDualChow` and `matroidDualAugmented`, the
rank-five chain expansions of Propositions 4.6–4.7. [The kernel-link module](../../lean/Conjectures/CaioloFerroniHosterKernelLink.lean)
proves that these equal the recursive invariants `Ranks.dualChow` and `Ranks.dualAug` for every
rank-five matroid on a finite projective point type. It first identifies the recursive flag
h-numbers with the inclusion–exclusion transform of the flat-flag counts
(`KernelLink.beta_eq_signed`). The rank development identifies those invariants with the
kernel definitions of the paper (`Ranks.dualChow_eq_kernel`, `Ranks.dualAug_eq_kernel`).
`KernelLink.counterexample_family_kernel` therefore gives the q ≥ 17 theorem for every
function satisfying the CFH kernel equations (Definitions 2.4, 2.7, 2.8, 3.1 and Theorem 2.3).
Before this module, only the unspecified bound of `Ranks.counterexamples` was stated at kernel level.

The strict target verifier passed for the 21-module closure: 1409 owned declarations, four
required endpoints, only `propext`, `Classical.choice` and `Quot.sound`, and stock-kernel replay.
[Receipt](../../docs/verification/cfh-kernel-link-20261126/receipt.json)

## Replay

With the pinned Lean 4.35.0 toolchain, run from the `lean/` directory.

```sh
lake build Conjectures.CaioloFerroniHoster
lake env python3 ../scripts/replay_lean.py --root Conjectures.CaioloFerroniHoster
lake build Conjectures.CaioloFerroniHosterKernelLink
lake env python3 ../scripts/replay_lean.py --root Conjectures.CaioloFerroniHosterKernelLink
```

The [dedicated GitHub Actions workflow](https://github.com/1337isnot1337/solved-conjectures/actions/workflows/lean-cfh.yml)
runs the strict target verifier from source. It publishes the axiom audit,
the pinned source and dependency hashes, and the replay transcript.

The local replay passed for all nine modules. The transitive axiom audit passed
for 452 theorem declarations. The main theorem uses only `propext`,
`Classical.choice`, and `Quot.sound`. The exact Python verifier also passed
as a separate check. [Verification issue #560](https://github.com/1337isnot1337/solved-conjectures/issues/560)
