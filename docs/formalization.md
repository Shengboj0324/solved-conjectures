# Full formalization campaign

## Chandran–Di Stefano–Haritha–Thomas–Tuite monophonic product conjecture

Lean verifies the 45-vertex counterexample, the exact color counts 20 and 27, and the complement count for every prism length. The original graph’s all-order color formula remains in the written proof. [Prism theorem](../lean/Conjectures/MonophonicPrismTheorems.lean) · [Research receipt](verification/lean-monophonic-prism-20261126/receipt.json).

## Wang–Yang’s six Fuss–Narayana matrices

Adam Benazouz formalized all six matrices in Conjecture 4.1 for every integer parameter at least two. Two independent strict builds, transitive axiom audits and stock-kernel runs verified 322 declarations across five modules and all seven registered endpoints. [Theorems](../lean/Conjectures/WangYangFussNarayana.lean) · [Research receipt](verification/lean-wang-yang-fuss-narayana-20261126/receipt.json) · [Original contribution](https://github.com/1337isnot1337/solved-conjectures/pull/840).

## Square-root-logarithmic growth of nonreal transportation roots

Lean proves the full-support counterexample and the square-root-logarithmic growth of nonreal roots, counted with multiplicity, for the Ehrhart numerators of the actual lattice polytopes. [Complete theorem](../lean/Conjectures/TransportationGrowthTheorems.lean) · [Research receipt](verification/lean-transportation-growth-20261126/receipt.json).

## Alexandersson’s transportation polytope conjecture

Lean proves the original counterexample from the integer points of a full-support, 24-dimensional lattice polytope. Its degree-twelve Ehrhart numerator has exactly two nonreal zeros. The asymptotic lower bound remains in the written proof. [Transportation theorem](../lean/Conjectures/TransportationTheorems.lean) · [Research receipt](verification/lean-transportation-geometry-20261126/receipt.json).

## Mallik–Diwan–Kothari degree-count conjecture

Lean constructs a minimal extendable bipartite counterexample for every stated even order and verifies its exact edge and degree counts. Explicit permutations identify the original 16-vertex search witness with the smallest family member. [Counterexample family](../lean/Conjectures/MallikDegreeTheorems.lean) · [Research receipt](verification/lean-mallik-degree-20261126/receipt.json).

## The Steiner triple system sail problem

Lean proves the uniform count, existence from order 84, the limiting lower density of 1/49, the one-color disjoint packing with limiting lower rate 1/4802, and the fixed disjoint-union Ramsey consequence. [Ramsey theorems](../lean/Conjectures/SteinerSailTheorems.lean) · [Research receipt](verification/lean-steiner-sails-20261126/receipt.json).

## Kovalev’s Hardy-duality counterexample

Lean proves the pointwise transfer inequality, the dimension threshold, the fourth-moment calculation and the exact rational separation. The Gaussian expectations and spherical Hardy-norm identities remain to be formalized. [Real inequalities and moment calculation](../lean/Conjectures/KovalevHardySeparation.lean) · [Research receipt](verification/lean-kovalev-hardy-separation-20261126/receipt.json).

## Nathanson’s linear-form Sidon systems

Lean proves all three original questions, the lower bound from the two largest absolute coefficients, the finite upper bound with the common coefficient divisor, and the exact bilinear limit for every choice of nonzero signed coefficients. [Sharp limit theorems](../lean/Conjectures/NathansonSidonSharpTheorems.lean) · [Research receipt](verification/lean-nathanson-sidon-sharp-20261126/receipt.json).

## Erdős–Gyárfás’s point-degree spectrum conjecture

Lean bounds the degree spectrum in every finite linear space, rules out the proposed square-root deficit and proves the same linear bound for real planar point sets. [Lean proof](../lean/Conjectures/ErdosGyarfasSpectrumTheorems.lean) · [Kernel receipt](verification/lean-erdos-gyarfas-spectrum-20261126/receipt.json).

## Fiscus–Hurlbert–Myzelev–Pence’s even-grid conjecture

Lean proves that Player 1 wins on the 14-vertex ladder, verifies all 16,384 positions and identifies all four winning openings. [Lean proof](../lean/Conjectures/FiscusGridCounterexample.lean) · [Kernel receipt](verification/lean-fiscus-ladder-20261126/receipt.json).

## Circular-index certificates within the package memory limit

The finite circular-index certificates for degrees 49, 50, 51, 53, 55 and 59 now verify their vertex tables in groups of sixteen. All six modules passed the normal Lake build under the configured 4.5 GB limit. The joint finite, stored-graph and all-degree proof suites also passed strict compilation, full axiom audit and stock-kernel replay twice. [Finite certificates](verification/lean-circular-bounded-20261126/finite/receipt.json) · [Stored insertions](verification/lean-circular-bounded-20261126/stored/receipt.json) · [All degrees](verification/lean-circular-bounded-20261126/all/receipt.json).

## Gyárfás’s construction at every order

For every order from 16, Lean constructs noncollinear rational points in the real plane, proves optimal maximum degree multiplicity two and determines the entire interval of distinct degrees. [Lean theorem](../lean/Conjectures/GyarfasPlanarUniform.lean) · [Kernel receipt](verification/lean-gyarfas-planar-uniform-20261126/receipt.json).

## Gyárfás’s planar degree-repetition problem at order 16

Lean constructs 16 noncollinear rational points in the real affine plane and proves that every spanned-line degree occurs at most twice. Degree 9 occurs twice. This answers the original existence question. The extension to every order from 16 and its exact count of distinct degrees have a written proof. [Lean theorem](../lean/Conjectures/GyarfasPlanarWitness.lean) · [Kernel receipt](verification/lean-gyarfas-planar-sixteen-20261126/receipt.json).

## Forward insertions in the three-block circular-index construction

Lean verifies the one- and three-block exclusions for all labelled small forward insertions, the classification of two-interval supports, connectivity of the infinite family, and both partial-block graphs with their exact indices. [Lean sources](../lean/Conjectures/CircularThreeBlockAdditional.lean) · [Receipt](verification/lean-circular-forward-insertions-20261126/receipt.json).

## The two truncated-square covering examples

Lean proves the exact Lebesgue areas and maximal four-shape covering scales of the parallelogram and rational pentagon, and the strict comparisons with the source’s trapezoid formula. The first comparison also holds near the boundary for every first truncation leg. Identifying this scale with symplectic capacity and proving the full strict bound for every convex body remain open in Lean. [Proof](../lean/Conjectures/MeylenderThalmaierPentagonArea.lean) · [Receipt](verification/lean-truncated-square-covers-20261126/receipt.json).

## Upper-half circular chromatic index examples in every degree from eight

For every integer maximum degree from eight, Lean constructs a finite simple graph whose real circular chromatic index is strictly between that degree plus one half and that degree plus one. The proof combines the two insertion families, regular circulants and tomdif’s seven exceptional examples. The three-block theorem gives the degree of every labelled vertex for every permitted packing. [Combined theorem](../lean/Conjectures/CircularIndexAllDegrees.lean) · [Three-block theorem](../lean/Conjectures/CircularThreeBlockTheorems.lean) · [Receipt](verification/lean-circular-all-degrees-20261126/receipt.json).

## The seventeen nonregular graphs of the circulant construction

Lean verifies the maximum degree and the exact real circular chromatic index for every nonregular graph in Section 7.3. An independent table comparison matches all 19,649 edge colours to the original certificates. The two standard replays each checked 27 project modules, 455 declarations, 327 theorem declarations, 70 private declarations and all 17 required endpoints. [Lean proof](../lean/Conjectures/CircularInsertionStoredBases.lean) · [Verification receipt](verification/lean-circular-stored-20261126/receipt.json).

## The plane-partition polynomial inequalities

Lean proves the strict Turán inequality for every index at least 12 and every real parameter at least 1. The consecutive roots strictly decrease from index 1 when the parameter exceeds 5 and from index 6 when it is at least 1. [Lean theorems](../lean/Conjectures/HeimNeuhauserPlanePartitionTheorems.lean) · [Joint verification receipt](verification/lean-plane-partition-full-20261126/receipt.json). The four certificate modules for indices 200 through 250 now elaborate their proofs sequentially under the 4,500 MB build limit. [Updated joint replay](verification/lean-plane-partition-resource-20261126/receipt.json).

## Upper-half circular chromatic index in every even degree from eight

For every integer parameter of at least six, Lean constructs both simple graphs with the prescribed order, maximum degree and exact circular chromatic index. It proves the four finite cases of Proposition 2 and the three degree ranges of Corollary 3. Lean also proves that the stated two-matching base has no solution at parameters three, four and five. [Family theorems](../lean/Conjectures/CircularInsertionFamilies.lean) · [Uniform receipt](verification/lean-circular-families-20261126/receipt.json) · [Small-base receipt](verification/lean-circular-families-20261126/small-base-receipt.json).

## Finite circular chromatic index certificates

Lean checks 43 finite simple graphs from the published colouring records. All 32 complete graphs with deletions have rigorous density and colouring bounds. Eleven insertion graphs have exact circular index equal to the maximum degree plus two thirds. [Finite theorems](../lean/Conjectures/CircularFiniteIndexTheorems.lean) · [Joint receipt](verification/lean-circular-finite-20261126/receipt.json).

## Shifted Lonely Runner counterexamples

Lean verifies the exact maximum at each of the 40 reported sizes, including attainment at a rational time. The upper bound holds at every real time. [Proof and reproduction](../results/shifted-lonely-runner-counterexamples/FORMALIZATION.md).

## Dukes’s revstack interlacing conjecture

Lean proves the source Eulerian formula for the actual revstack descent polynomial at every order at least three. Tracking the two parity classes through one maximum split gives the complete characterization of the unsorted words. The proof also turns the derivative inequality into strict interlacing of the literal descent polynomials and checks the transition from order three to four. The later finite transitions and the uniform derivative bound remain open in Lean. [Lean theorem](../lean/Conjectures/DukesRevstackFiniteStart.lean) · [Scoped receipt](verification/lean-dukes-revstack-enumeration-20261125/receipt.json)

## Braun–Bruegge’s bicyclic facet conjectures

[Lean wedge theorem](../lean/Conjectures/BraunBrueggeBicyclicWedge.lean). Gluing two connected graphs at one vertex multiplies the actual facet counts of their symmetric edge polytopes. The proof gives restriction and gluing maps on normalized polar vertices, with connectedness characterized on each factor's tight graph. The [scoped receipt](verification/lean-braun-bruegge-bicyclic-wedge-20261124/receipt.json) verifies six strict sources, 113 owned declarations and four endpoints, with stock-kernel replay.

For cycles of order at least three, the [cycle count](../lean/Conjectures/BraunBrueggeBicyclicCycleCount.lean) gives the exact even-order central binomial coefficient and the odd-order product of the order and the next smaller central binomial coefficient. The proof identifies actual polar vertices with cyclic integer steps of zero sum and at most one slack edge. The [cycle receipt](verification/lean-braun-bruegge-bicyclic-cycle-current-20261124/receipt.json) covers nine strict sources, 192 owned declarations, eight endpoints and pinned kernel replay.

The [theta count](../lean/Conjectures/BraunBrueggeBicyclicThetaCount.lean) proves the exact same-parity and mixed-parity formulas for the geometric facets of the three-path theta graph. It constructs the literal graph with shared endpoints, identifies its polar vertices with three integer step words, and counts each common-total fiber by its full paths and single slack positions. The [theta receipt](verification/lean-braun-bruegge-bicyclic-theta-20261124/receipt.json) checks 12 strict sources, 346 owned declarations and 10 required endpoints, with pinned kernel replay.

The [large-length mixed-parity comparison](../lean/Conjectures/BraunBrueggeBicyclicMixedLarge.lean) proves a strict geometric facet bound against the balanced odd-cycle wedge benchmark for every total length at least 144. It uses the Wallis product for the central sign-mass bounds and verifies all four cases of the comparison. The [receipt](verification/lean-braun-bruegge-bicyclic-mixed-large-20261124/receipt.json) records 21 strict sources, 623 owned declarations, 11 required endpoints and pinned kernel replay. The all-length comparison below includes the finite base.

Lean proves the sharp facet maximum for every finite connected simple bicyclic graph and constructs an attaining graph at every order at least four. A bridge gives an exact product of normalized polar counts. A core without bridges contains a cycle and an ear, and equality of cycle ranks makes the closed-ear wedge or open-ear theta embedding an isomorphism. The [scoped receipt](verification/lean-braun-bruegge-bicyclic-maximum-20261125/receipt.json) covers 73 strict sources, 1,846 owned declarations and 12 required endpoints, with pinned kernel replay. The [theta optimizer](../lean/Conjectures/BraunBrueggeThetaOptimizer.lean) now gives the exact maximum and all equality cases up to path permutation for every order at least ten. [Joint receipt](verification/lean-braun-bruegge-bicyclic-facets-20261126/receipt.json). [Lean theorem](../lean/Conjectures/BraunBrueggeBicyclicMaximum.lean)

## Braun–Bruegge’s minimum facet conjecture

Lean proves both global minimum clauses of Conjecture 2 for the actual facets of the symmetric edge polytope. It establishes the exact even and odd formulas and the equality criterion up to graph isomorphism. The scoped gate passed for 19 modules, all 433 owned declarations and 30 required endpoints, followed by pinned kernel replay. The matching-number refinement remains a written supplement. [Lean theorem](../lean/Conjectures/BraunBrueggeMinimum.lean) · [Verification receipt](verification/lean-braun-bruegge-complete-20261124/receipt.json)

## Ma–Tang’s random subset-sum threshold conjecture

[Incomplete lower-bound checkpoint](../research/ma-tang-lean-core/README.md): twenty Init-only modules establish the exact uniform kernel law, iid coverage bound, birthday conditioning, actual subset-sum coverage and uniform unordered subset probability. The endpoints `uniform_subset_coverage_scaled` and `uniform_subset_below_half` prove covering fraction at most 1/(4*2^r) and strictly below one half on the explicit mixed-group dimension sequence for every r≥4. Strict Lean 4.35.0 builds, transitive axiom checks of all 449 source-named declarations, and stock kernel replay passed ([log](../research/ma-tang-lean-core/verification/uniform-reproduction.log)). Threshold monotonicity, limiting real-log statement, universal upper bound, environment-wide audit and aggregate gate remain unverified. Count zero; uncompiled Mathlib alternatives remain in [draft #583](https://github.com/1337isnot1337/solved-conjectures/pull/583).

## Mazák–Zrubák conjecture on complete graphs minus an edge

The actual real circular coloring reduction and Hall construction of a spanning order of every actual edge are checked in sixteen modules (ten new, six reused). Strict builds, the complete audit of 526 declarations (417 theorems, zero private declarations, twelve required endpoints), and exact stock-kernel replay passed. Only `propext`, `Classical.choice`, and `Quot.sound` occur. Steps 4–8 and the final index equality remain outside this checkpoint; the result is incomplete and its complete-result count is zero. [Scope](../results/circular-index-complete-minus-edge/FORMALIZATION.md), [independent review](../results/circular-index-complete-minus-edge/LEAN_REVIEW.md), and [receipt](verification/lean-circular-complete-minus-edge-partial-20261124-162051/receipt.json).

## Dilcher–Kidwai–Tomkins’s Stern-polynomial conjecture

The [four-module partial](../results/stern-half-plane/FORMALIZATION.md) verifies the actual Stern recurrence and polynomial evaluation, the Schinzel identity, all-odd-index run coverage, and nonvanishing for every positive index under an explicit common-parabola hypothesis. All strict source builds, the owned/private audit of 134 declarations (105 theorems, 14 private declarations and eight required endpoints), and exact stock replay passed. The [independent review](../results/stern-half-plane/LEAN_REVIEW.md) and [receipt](verification/lean-stern-half-plane-partial-20261124-162051/receipt.json) preserve the exact scope. The near-one estimates, compact certificate and separate exterior proof remain unformalized; count zero.

## Hartke–Stolee–West–Yancey matching-excess conjecture

Complete Lean verification of the original tail-minimum divergence conjecture and the recorded quantitative bounds for every matching count at least two. The 22-module closure proves actual graph matching/edge counts, both general constructions, a bounded and attained maximum over all finite even graph orders, exact eventual stabilization, and the uniform all-tail limit. All fresh strict builds, the complete audit of 505 declarations (435 theorems, 32 private declarations, 42 required endpoints), and exact stock replay passed. [Scope](../results/hartke-stolee-west-yancey-matching-excess/FORMALIZATION.md), [independent review](../results/hartke-stolee-west-yancey-matching-excess/LEAN_REVIEW.md), and [receipt](verification/lean-hartke-matching-excess-complete-20261124-162051/receipt.json). One existing result; stronger growth and exact upper-bound questions remain outside scope. Aggregate/hosted/deployment status remains separate under [#563](https://github.com/1337isnot1337/solved-conjectures/issues/563).

## Ferroni–Higashitani’s first-three interior Ehrhart question

The [Lean proof of Question 5.12(a)](../lean/Conjectures/FerroniHigashitaniEhrhart.lean)
uses the dimension-170 Cayley boxes in the written proof. The refined lattice
is transported to the ordinary integer coordinate lattice by an explicit
real linear equivalence. Lean verifies the finite integral convex hull,
integer decomposition for every positive dilation, and the exact coset
counts. The binomial-basis formula for weighted compositions identifies the
unique Ehrhart polynomial and proves the claimed negative-evaluation
inequality. The unbounded-ratio family and regular triangulation are written supplements.



## Németh–Seberry–Shu’s biased Fourier supports

[Lean verifies the full support construction in §1](../lean/Conjectures/NemethSeberryShuFourierSampling.lean).
For every dense row sum and permitted amplitude, the witness has exact
cardinality and simultaneous Fourier error at most $4\sqrt{p\log p}$.
[The spectral formalization](../lean/Conjectures/NemethSeberryShuFourierSpectral.lean)
checks the Fourier eigenvectors of the actual binary circulant, character
orthogonality and the exact Parseval identity for every support.
The permanent asymptotic and the separation within a row sum remain open in Lean.

## Almirón–Moyano-Fernández’s normalized Wilf modules

[Lean proves the gap-antichain characterization and the exact fixed-semigroup
threshold](../lean/Conjectures/AlmironMoyanoWilfFixedThreshold.lean). For every
positive generator count, the threshold is the maximum of the individual
ceiling formulas over the actual admissible antichains, with one for an empty
class. The [sharp uniform construction](../lean/Conjectures/AlmironMoyanoWilfGeneratorCount.lean)
shows that across all semigroups of multiplicity $m$, the threshold is $m$
for each prescribed generator count from one to $m$. The development reuses
the existing proof of Question 4.8 and the normalized multiplicity bound.
Lean now verifies the [exact two-generator thresholds and fixed-multiplicity comparison](../lean/Conjectures/AlmironMoyanoWilfClassification.lean), including thresholds one and two at multiplicity two and threshold three at every larger multiplicity. The [gap family](../lean/Conjectures/AlmironMoyanoWilfGapFamily.lean) has maximum gap Wilf number $4-m$ for every $m\ge5$. [Kernel receipt](verification/lean-wilf-classification/receipt.json).

## Németh–Seberry–Shu conjecture

The [two-module formalization](../results/nemeth-seberry-shu/LEAN_STATUS.md)
proves the binary-circulant permanent congruence at every prime order and the
uniform dense-row counting reduction. It uses the actual `Matrix.permanent`
and the set of all binary supports. The missing analytic separation input is
an explicit hypothesis, so the full disproof remains incomplete in Lean.
An independent statement review, strict compilation, every-owned-declaration
audit, and stock-kernel replay passed. This milestone contributes zero complete
results to the campaign started on 24 November 2026 at 16:19:51 UTC.

## Benfield–Lippard’s stable Waring-gap symmetry conjecture

The [Lean proof](../lean/Conjectures/BenfieldLippardSymmetry.lean) refutes
Conjecture 10.1 at both exponents 64 and 128. It proves the exact stable
gap membership, the largest gap, and a pair of gaps reflected into each
other. The resulting strict gap-count inequality also refutes the
finite-domain interpretation of Conjecture 10.2. The proof uses the
L-shaped Apéry certificate and the exact fourth-generator gluing.

The three-module closure passed strict compilation, the all-owned audit
of 338 declarations including 234 private declarations and six required
endpoints, and stock-kernel replay. See the
[local receipt](verification/lean-waring-symmetry-20261124/receipt.json).


## Coulangeon–Lazzarini’s two-shell conjecture

[Lean refutes Conjecture 21 in dimension ten](../lean/Conjectures/CoulangeonLazzariniRealLattice.lean).
It verifies the full-rank discrete lattice in real space, identifies its first two
positive squared norms as 4 and 8, and checks the two spherical moment
identities and the failure at squared norm 9. The [integer-coordinate proof](../lean/Conjectures/CoulangeonLazzariniShells.lean)
also verifies the arbitrary-delay parity-lattice family.
The orthogonally indecomposable family and height results remain open in Lean.

## Cardon–Forgács–Piotrowski–Sorensen–White zero-sector reduction

The [exact counterexample](../lean/Conjectures/CardonZeroSector.lean) at
exponent three and damping log(16/15)/6 refutes Question 6.1. The
[uniform proof](../lean/Conjectures/CardonZeroSectorSmallDamping.lean)
shows that for each real exponent p > 2, all sufficiently small positive
damping parameters fail to preserve some strictly positive sector. Lean
checks the actual polynomial multiplier, complex root, and positive
sector angle.

All three modules passed strict compilation and pinned stock-kernel replay.
The [local audit receipt](verification/lean-cardon-zero-sector-20261124/receipt.json)
covers 68 declarations, including 35 private declarations and nine required
endpoints.



## Gawron–Miska–Ulas’s Thue–Morse sign-density conjecture

[Lean refutes Conjecture 5.8](../lean/Conjectures/ThueMorseSignDensity.lean) for
both original residues at exponent two. It derives the two coefficient
recurrences from the source product, checks all six binary suffix rows and
proves the two all-index identities. In the conjecture's input index, it proves
lower densities at least $1/512$ and $1/256$ and finite two-sided count bounds.
The separate exact density theorem for every arithmetic progression remains
open in Lean.

## Gravgaard–Lee’s mixed Lüroth sumset

[Lean proves Conjecture 2.2 and the interval from the written proof](../lean/Conjectures/GravgaardLeeMixedLuroth.lean).
The sum of the digit sets bounded above by three and four contains $[2879/3520,2]$
and represents every real residue modulo one. The proof checks the fifteen
branch containments and the geometric approximation argument for the closed
sumsets of infinite Lüroth expansions. The two-module local import closure
passed the pinned kernel replay.

## Gawron–Miska–Ulas’s Thue–Morse valuation conjecture

The [Lean proof](../lean/Conjectures/ThueMorseValuation.lean) formalizes the
disproof of the general clause of Conjecture 5.2. It verifies the exponent-17
counterexample and both valuations in the uniform family for every k ≥ 11,
with the indices in the same aligned block. The coefficient model is the
stabilized finite product. The exact modular certificates use carry-free
integer packing and ordinary kernel reduction.

All three modules passed strict source compilation and pinned stock-kernel
replay. The all-owned audit checked 123 declarations, including 96 private
declarations, and eight required endpoints. See the
[local receipt](verification/lean-thue-morse-valuation-20261124/receipt.json).

## Gravgaard–Lee’s large-digit Lüroth sumset

[Lean proves Conjecture 2.12 and the stronger interval in the written proof](../lean/Conjectures/GravgaardLeeLargeLuroth.lean).
For every integer $k\ge2$, the sum of the large-digit Lüroth set with itself contains
$(0,1/(k-1)]$. The witnesses have strictly increasing interleaved digits.
The development verifies both the convergence of the source's series and the half-open
digit intervals. See `conjecture_2_12`, `interval_subset_sum` and `interleaved_decomposition`.

## Steinke–Zakynthinou’s agnostic VC learning conjecture

The [framework paper's Conjecture 4.18](https://arxiv.org/pdf/2001.09122v3) is fully checked by `AgnosticVC.steinkeZakynthinou_framework_conjecture418`. Its distribution-free CMI takes the supremum over fixed paired pools, and both guarantees hold with common constant $`19{,}712`$ for every positive sample size. [Lean source](../lean/Conjectures/AgnosticVC/FixedPairing.lean)

The [combined theorem](../lean/Conjectures/AgnosticVC/Theorem.lean) proves the two bounds for the same proper learner. Lean checks the [bound for every fixed pairing](../lean/Conjectures/AgnosticVC/FixedPairing.lean), the iid information bound whenever its integrand is almost everywhere measurable, and a measurable Markov learner under the stated representative convention. The [Mathlib KL formulation](../lean/Conjectures/AgnosticVC/KLRates.lean) identifies the joint distribution and both marginals on the full output hypotheses. [Verification guide](verification.md#steinkezakynthinous-agnostic-vc-learning-conjecture)

The [local reconstruction theorem](../lean/Conjectures/AgnosticVC/LocalReconstructionMeasurable.lean) verifies both rates when countably many proper maps from at most $`k`$ observed features cover every finite trace. The [circle application](../lean/Conjectures/AgnosticVC/OrbitIidRates.lean) verifies a Borel learner on the same class for which globally ordered representatives fail completed measurability.

The [fixed-class disproof](../lean/Conjectures/AgnosticVC/CompletedFiniteGroups.lean) uses a VC-one class with two-point supports and requires universal measurability of the scalar expected empirical loss. Lean verifies a [measurable deviation envelope](../lean/Conjectures/AgnosticVC/FiniteSupportUniform.lean) with expectation at most $`2/\sqrt n+2/n`$ for the same class at every iid law and positive sample size.

The [discrete-noise learner](../lean/Conjectures/AgnosticVC/NoisySupportLearner.lean) verifies information for the actual named output and empirical excess on each sample. The [completed-iid theorem](../lean/Conjectures/AgnosticVC/NoisySupportIid.lean) verifies both rates for bounded-size supports with bounded pointwise overlap. Its countable list of eligible names is constructed separately for each iid law to verify measurability of the same learner.

The [rectangle density argument](../lean/Conjectures/AgnosticVC/IidRectangleDensity.lean) changes the sampling law to amplify positive outer mass of null-support hits. It gives the [completed-iid extension to unbounded-size supports](../lean/Conjectures/AgnosticVC/NoisySupportSharpIid.lean) under bounded overlap and sharp one-sided outer uniform convergence.

The [ambient standard Borel version of the disproof](../lean/Conjectures/AgnosticVC/ConditionalJointObstruction.lean) pushes every proper output law into a standard Borel space of all tuple codes. The conditional joint kernel recovers the probabilities of ambient Borel events. Restricting those events to the proper subclass gives its completed training kernel.

The independently seeded version in the same module rearranges the original iid pool, selector and seed by a measure-preserving map. For each ambient output event, intersecting with the all-zero selector produces a product event with an independent factor of positive measure. This recovers completed measurability of the training-and-seed rule and then of its empirical loss.

The [fair-label lower bound](../lean/Conjectures/AgnosticVC/FairLabelObstruction.lean) projects onto positive sectors and applies Fubini to exclude finitely many coordinate hyperplanes on negative sectors. The probability of a repeated sector is at most $`n^2/m`$. An arbitrary completed-measurable expected empirical loss within tolerance $`\epsilon`$ therefore has expectation at most $`\epsilon+n^2/m`$. Every measurable classifier has population loss $`1/2`$ under the independent fair labels. The final CMI conclusion takes the authors' published generalization inequality as an explicit hypothesis.

The [conditional joint-law reduction](../lean/Conjectures/AgnosticVC/ConditionalJointObstruction.lean) recovers a completed-measurable training kernel from the actual selector/output law on the completed iid pool, with almost-everywhere agreement. It applies to arbitrary pointwise probability measures and gives the same finite-support counterexample to the empirical rate.

## Steinke–Zakynthinou threshold formalization scope

[The full proper threshold theorem](../lean/Conjectures/SteinkeZakynthinou.lean) is checked. The finite learner uses the rational shifted-tree rule, noise scales with ratio $3/4$, and label-first rounding. In the CMI proof, giving the two pool slots in a row consecutive tags keeps the learner's order on selected samples. Summing row charges under the common iid selected-sample law bounds the information on the augmented output. A finite rank code then decodes the successor or maximum into the learner's actual threshold.

Gröchenig’s upper-density result is excluded after a [checked earlier resolution](../research/bounty-continuation-2026-11-21/grochenig-prior-resolution/). Its independent proof and verification receipts remain in [immutable Git history](https://github.com/1337isnot1337/solved-conjectures/blob/628270dc5e07d7924de265d2ac1beee4b5634b80/docs/verification/lean-grochenig-20261121/receipt.json). The reused KVZ results remain active.

The objective is to formalize every result in this repository, preserving its
quantifiers and discharging every mathematical dependency. Accepted work goes
to `main`. The Li counterexample is registered. The campaign is incomplete.

The higher-speed team's recent candidate receipts include the complete
41,472-code seven-coordinate finite enumeration at `3f6ee74c` and three
further closures at `75df6294`: the six-speed classification-to-bound
adapter, hyperplane residue calculations, and endpoint components. Their
source, axiom, and independent-kernel checks are recorded in
[`loneliness-3f6-component-receipts.json`](loneliness-3f6-component-receipts.json)
and [`loneliness-75df-component-receipts.json`](loneliness-75df-component-receipts.json).
Those receipts did not by themselves discharge the geometric assembly or the
lower-speed classification inputs. The later checkpoints below record the
accepted scope, including the conditional critical-seven assembly.

## Chen–Khare–Sahi fixed-parameter stable Hall checkpoint

Lean now identifies the displayed counterexample at `q=1/10`, `t=9/10`
with the complete stable Hall-orthogonal family in degree six. All eleven
partitions occur before specialization. The formalization proves the literal
power-sum expansion, injectivity of the six-variable polynomial coordinates,
the diagonal stable Hall pairing, and existence and uniqueness of the monic
dominance-triangular orthogonal family. Literal specialization to three
variables gives the `(4,2,0)` and `(4,1,1)` polynomials, with positive
normalizing values. Their normalized difference lies outside the full real
Muirhead semiring.

The degree-three source-convention conflict is also formal: at `q=t=1/2`,
the literal two-variable source formulas have truncated finite Hall pairing
`-1`, so they are not orthogonal for that form. This fixed-parameter stable
Hall theorem does not reconcile the manuscript's truncated finite-variable
Hall definition. The broader rectangular-translate and parameter families
retain their monic triangular eigenfunction characterizations; their stable
Hall identification is not established by this checkpoint. The result's
README badge remains partial.

The twelve new modules and seven reused semiring modules form an exact
nineteen-module closure. All nineteen sources passed strict compilation.
The unchanged modern owned/private audit covers eleven modules; the
unchanged complete audit covers 1,489 declarations, 1,294 theorem declarations, 950 private declarations and all 42 required endpoints. Only `propext`,
`Classical.choice` and `Quot.sound` occur. Stock-kernel replay passed for
this exact frozen nineteen-module closure, including all 41 object parts.
The combined repository gate and hosted validation remain separate pending
checks.

The earlier sixteen-module compatibility receipt remains a separate
checkpoint. Its strict sources and owned/private audit passed, but its
fresh stock replay remains pending. This nineteen-module replay shares
only seven modules with that closure and does not certify its other nine
modules.

See the [stable-Hall receipt](verification/lean-cks-hall-20261121/receipt.json).

## KVZ gamma-quotient theorem, 21 November 2026

Lean proves the literal kernel `Gamma(c+x+y) / Gamma(d+x+y)` for
arbitrary real `c`, `d`, and strictly increasing real node grids, assuming
only `c>d` and `d+x_i+y_j>0`. A proved translation to two positive grids
preserves every matrix entry. The empty determinant is included.

Write `delta=c-d`. For positive noninteger `delta`, every order is strict.
The determinant sign is the sign of
`(-1)^(r.choose 2) * product(j=0..r-1, falling(delta,j))`, with the empty
falling factorial equal to one. For a positive integer `delta=m`, minors
through order `m+1` are nonzero with sign `(-1)^(r.choose 2)`; every larger
minor vanishes. The third-order sign is the sign of `delta^2*(1-delta)`.
It is positive for `0<delta<1`, zero at `delta=1`, and negative for `delta>1`.
Thus the source's fixed third-order signature is corrected within this theorem.

The proof derives the all-order Wronskian criterion by exact mean-value
reductions, proves the power and gamma-density determinant signs, and
establishes the literal double gamma integral with its integrability
hypotheses. Two determinant composition arguments prove the final signs.
No unformalized Wronskian or composition theorem is assumed.

All 15 sources passed strict checks. The exact owned/private axiom audit
covers 195 declarations, 176 theorem declarations, and 54 private declarations, including all 62 required endpoints.
Only `propext`, `Classical.choice`, and `Quot.sound` occur. The pinned stock
checker replayed the exact frozen closure. The combined repository gate
and hosted validation remain separate pending checks.

See the [receipt](verification/lean-kvz-20261121/receipt.json).

## Chen–Khare–Sahi compatibility checkpoint

Replaced repeated monomial-product proof search with 115 proved pair identities and an indexed degree-at-most-six dispatch. Repaired strict-linter, arithmetic-normalization and deprecated-lemma failures in Translate, Boundary, Parameter and Unique. The existing public definitions and theorem statements are unchanged.

All 16 existing modules passed fresh strict Lean 4.35 compilation with warnings treated as errors. The complete owned/private audit checked 1,454 declarations, including 1,254 theorem declarations, 816 private declarations and all 49 required endpoints. Only `propext`, `Classical.choice` and `Quot.sound` are allowed. Independent stock-kernel replay of the revised closure and the combined repository gate remain pending. The README badge remains partial.

The current endpoints use the standard monic triangular Macdonald eigenfunctions. Stable Hall orthogonality followed by specialization is being formalized separately. The manuscript's literal truncated finite-variable Hall pairing conflicts with that convention; the [degree-three diagnostic](https://github.com/1337isnot1337/solved-conjectures/issues/201#issuecomment-7065320695) must be reconciled before claiming a full literal-source formalization.

## Chow full interlacing theorem, 21 November 2026

Lean proves consecutive interlacing for every type-D rank at least two,
with strict interlacing from rank three. The formal polynomials enumerate
the actual even-signed permutations using the source descent statistic.
The recurrence, factor of two, ordered cone inequalities, and strictness
argument are all proved internally.

All 11 sources passed strict checks. The complete audit covers 329
declarations, including 286 theorem declarations, 149 private declarations,
and all 48 required endpoints. The pinned stock checker replayed the
exact closure. The [receipt](verification/lean-chow-20261121/receipt.json)
records the source and object hashes. The combined repository gate remains
pending. Existing mathematical attribution is preserved.

## Oravcová–Soták relative classification, 21 November 2026

The formalization uses the actual distance graph on the integers. Its unconditional results include the greedy upper bound, periodic-word transport, loop concatenation, integer base change, the four unbounded one-parameter coloring families, the full two-parameter family, and the exceptional chromatic numbers. Theorem A, the Oravcová–Soták clique conclusion, and the primitive triangle-free corollary retain the explicitly named propositions `R5`, `R6`, `R7`, and `R8` as hypotheses. Those four real-loneliness classifications are not proved by this closure.

All nine new modules passed strict compilation with warnings treated as errors. The exact 28-module project closure passed an all-owned audit of 1239 declarations (1084 theorem declarations and 40 required endpoints) and independent stock-kernel replay. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. [Receipt](verification/lean-named-20261121/oravcova-receipt.json) and [source records](verification/lean-named-20261121/oravcova-source-evidence.json). The first five modules reproduced the audited objects exactly on their recorded recheck. All required endpoints are theorem declarations. The result remains partial, and no combined repository or hosted gate is claimed.

## Vishnyakova root-radius theorems, 21 November 2026

Lean proves the original sampled-sequence theorem and the weighted theorem.
Both statements cover every positive degree; the weighted statement covers
every positive real weight. The original class uses all ordered finite
Toeplitz minors of the actual samples. Its transform condition is derived
within Lean, including initial zero samples.

The proof verifies the centered disks, exact greatest root moduli, and
attainment within each class. It constructs the source transform and proves
its inverse and degree identity. Polarization, the tridiagonal argument,
and total nonnegativity of the binomial extremizer are also formalized.

All 17 sources passed strict checks. The complete audit checked 439
declarations, including 387 theorem declarations, 172 private declarations,
and all 66 required endpoints. The unchanged pinned checker replayed the
exact closure. See the
[receipt](verification/lean-vishnyakova-20261121/complete-receipt.json).
The result is fully verified at this scope. The combined repository gate
remains a separate pending check.

## Bernardi–Morales delta and event identities, 21 November 2026

`BernardiMorales.bernardi_morales_delta` proves the full literal delta-map count for every fixed color map, including nonsurjections. `bernardi_morales_event` proves the stronger source marked-event identity for every fixed surjection and marked set. The source probability determinant is also identified with the exact normalized membership count. The tuple definitions include the source's empty cyclic self-interval, full-subset diagonal event, singleton-complement fixed point and root-reaching tree semantics. No finite cutoff or unproved determinant identity is an input.

The 13-module closure passed strict compilation with warnings treated as errors, an all-owned audit of 269 declarations (205 theorem declarations and 23 required endpoints), and independent replay by the pinned stock kernel. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. All 13 strict source checks have preserved logs and source/object bindings; the six initial successes were rerun once to supply complete contemporaneous records. [Receipt](verification/lean-named-20261121/bernardi-receipt.json), [source records](verification/lean-named-20261121/bernardi-source-evidence.json), and [all-owned inventory](verification/lean-named-20261121/bernardi-all-owned-inventory.json).

The result is registered in the common imports, required endpoints, legacy-prefix audit and prebuild list. These local checks are separate from the combined accepted-root gate and hosted validation.

## Circular-index main theorems and regular examples, 21 November 2026

`CircularIndex.theorem_one` proves the full infinite construction for every `g ≥ 2`: the literal graph on `ZMod (6*g+1)` is `4g`-regular, stays connected after deletion of any fewer than `4g` vertices, and has real circular chromatic index `4g+2/3`. `theorem_two`, `graph31_complete`, and `graph33_complete` prove the full degree/connectivity/index assertions for the three listed finite circulants.

The lower bound concerns arbitrary real circular edge-colourings, through a proved rounding argument and an Archimedean limit. The connectivity proof establishes atom intersection, subgroup reduction, and the link to actual induced-graph connectedness. No published connectivity theorem is left as an assumption. The existing written construction and contributor attribution are preserved.

All 19 sources passed strict compilation. A fresh all-owned audit covered 601 declarations, including 500 theorem declarations and all 171 required endpoints; every transitive axiom was one of `propext`, `Classical.choice`, and `Quot.sound`. The unchanged pinned checker replayed the exact union of the three local root closures. [Receipt](verification/lean-named-20261121/circular-receipt.json) and [complete declaration inventory](verification/lean-named-20261121/circular-all-owned-inventory.json).

The row remains partial because the nonregular positive examples and the other Section 7 claims are outside this checkpoint. These local checks do not claim the combined package gate or hosted validation.

## Gilmore full matching identity rechecked, 21 November 2026

The complete `Conjectures.GilmoreCrossingNesting` source passed a fresh strict check, an all-owned audit of 449 declarations (346 theorem declarations, including 25 private declarations in the complete inventory) and all 20 required endpoints, and exact-closure stock-kernel replay. The audit includes the literal perfect-matching characterization, decoder surjectivity, statistic-preservation bridge, stabilized matrix product, and both final identities. [Receipt](verification/lean-named-20261121/gilmore-receipt.json).

The landing page previously described surjectivity and statistic preservation as unfinished despite those proofs already being present. The page and result-level verification status are now synchronized with the checked source. The combined package gate and hosted validation are not claimed by this receipt.

## Babai path spectra and Baricz–Pogány source recurrence, 21 November 2026

`BabaiPathSpectrum.spectrum_eq_interval` proves the full path-spectrum theorem for every `n ≥ 2`, `1 ≤ k < n`. It uses the actual finite distance graph and proves both inclusions, including the greedy upper bound and every modular-coloring/clique realization. Strict source compilation, the all-owned audit of 43 declarations and 12 required endpoints, and stock-kernel replay passed. [Receipt](verification/lean-named-20261121/babai-receipt.json).

`BariczPogany.source_recurrence_unique` and `source_recurrence_conjecture` make the source recurrence and its all-degree inequality explicit. The complete module passed strict sources, an all-owned audit of 65 declarations and seven required endpoints, and stock-kernel replay. [Receipt](verification/lean-named-20261121/baricz-receipt.json). The prior 2.5 GB strict attempt exhausted its memory cap; the unchanged source passed at the package's existing 4.5 GB cap.

Both modules are registered in the shared imports, required endpoints, and kernel list. Their complete result-level verification is distinct from the combined repository gate and hosted CI, which are not claimed by these local receipts.

## Horňák–Woźniak short arms of length at most two, 21 November 2026

Lean proves arbitrary vertex decomposability when the positive short arm has length at most two, assuming source tests 1 and 5. It also proves the unique-largest balancing step for a star with any number of arms. Strict compilation, a 958-theorem full-chain axiom audit and isolated kernel replay passed; the combined gate is pending.

## Horňák–Woźniak short-arm subset and merging, 21 November 2026

Lean realizes any positive partition with a sublist summing to the short arm by partitioning the remaining path, and reduces arbitrary partitions to those without a mergeable noncentral pair. These are partial steps toward the all-small branch. Strict compilation, a 945-theorem full-chain axiom audit and isolated kernel replay passed; the combined gate is pending.

## Horňák–Woźniak partitions containing a large part, 21 November 2026

Lean proves that tests 1 and 5 in the original finite index range realize every positive tripod partition containing a part larger than the positive shortest arm. The proof groups small parts, realizes the coarse partition, and refines it in the graph. The all-small case, four-arm reduction and existence constructions remain. Strict compilation, a 910-theorem full-chain axiom audit and isolated kernel replay passed; the combined gate is pending.

## Horňák–Woźniak large-part reduction, 21 November 2026

Lean reduces every tripod partition whose parts exceed a positive shortest arm to consecutive-size partitions within the source index bound and connects those to tests 1 and 5, with the upper-endpoint carry bound proved, using the graph-level balancing steps and a decreasing measure. It also proves the general refinement step when discarded central pieces fit the unused shortest arm. The small-part and four-arm reductions, admissibility ranges and existence constructions remain. Strict compilation, an 878-theorem full-chain axiom audit and isolated kernel replay passed; the combined gate is pending.

## Horňák–Woźniak tripod subset criterion, 21 November 2026

Lean proves the middle-window subset criterion in both directions when all parts exceed the shortest arm, reserves a largest part in the center at the assignment level, and proves the coarsening step with that central part unchanged. The remaining Barth reductions and existence constructions remain. Strict compilation, a 777-theorem full-chain axiom audit and isolated kernel replay passed; the combined gate is pending.

## Horňák–Woźniak arm assignment extraction, 21 November 2026

Lean extracts a capacity-respecting arm assignment for the noncentral classes of any connected star-graph partition. This supports the Barth reduction but does not yet prove it. Strict compilation, a 746-theorem full-chain axiom audit and isolated kernel replay passed; the combined gate is pending.

## Horňák–Woźniak reduction foundations, 21 November 2026

Lean constructs connected graph partitions from arbitrary positive lists fitting the arms, and proves two subset-sum balancing steps with a termination measure. The full Barth AVD reduction remains to be proved. Strict compilation, a 741-theorem full-chain axiom audit and isolated kernel replay passed; the combined gate is pending.

## Horňák–Woźniak source test 5, 21 November 2026

Lean formalizes the count-based existence trigger of source test 5 and uses it with tests 1 and 2 for the regular and exceptional graph partition cases, including a reserved short arm. Admissibility index ranges and reorderings, AVD reductions and existence constructions remain. Strict compilation, a 709-theorem full-chain axiom audit and isolated kernel replay passed; the combined gate is pending.

## Horňák–Woźniak source-level exceptional case, 21 November 2026

Lean proves the complete exceptional-size graph construction under the weaker residue bounds derived from tests 1 and 2, with a fifth-test witness, for the tripod and a reserved short arm. The stronger pairwise assumption is no longer required. Translating test 5, general AVD reductions and existence constructions remain. Strict compilation, a 681-theorem full-chain axiom audit and isolated kernel replay passed; the combined gate is pending.

## Horňák–Woźniak source-level zero slack, 21 November 2026

Lean derives the weaker residue bound from source tests 1 and 2, and proves every exceptional zero-slack graph partition under that bound and a fifth-test witness. Positive slack still assumes stronger pairwise bounds, and test 5 translation, AVD reductions and existence constructions remain. Strict compilation, a 580-theorem full-chain axiom audit and isolated kernel replay passed; the combined gate is pending.

## Horňák–Woźniak exceptional graph partitions, 21 November 2026

**Historical scope correction:** The earlier exceptional theorem required every pair of regular-arm residues to satisfy the bound, whereas admissibility only bounds the sum outside a largest residue. The repository checker accepts capacities (4, 7, 11), whose residues modulo 2 are (0, 1, 1), violating the pairwise hypothesis. Those earlier theorems do not cover every admissible triple; the later source-level exceptional theorem above removes this stronger hypothesis.

Lean proves every exceptional-size graph partition for the tripod and for a reserved short arm under stated residue and fifth-test hypotheses, covering zero and positive slack. Original-test translation, general AVD reductions, and existence constructions remain. Strict compilation, a 541-theorem full-chain axiom audit and isolated kernel replay passed; the combined gate is pending.

## Horňák–Woźniak zero-budget criterion, 21 November 2026

Lean proves the exact zero-budget packing criterion, bounds residue loss, and handles the exceptional zero-slack case with two positive quotient gaps from the pairwise residue test. Other zero-slack cases, full reductions and existence constructions remain. A 492-theorem axiom audit on the full HornakZero dependency chain and isolated kernel replay passed. The prior 407-theorem audit imported HornakReservedArm rather than HornakLargest; the new audit covers both. The combined repository gate is pending.

## Horňák–Woźniak positive-slack exceptional case, 21 November 2026

Lean derives the largest-count endpoint and all smaller counts with positive quotient slack under stated residue and fifth-test hypotheses, and handles a fourth arm reserved in the center. Zero slack, full source-test and AVD reductions, and existence constructions remain. Strict compilation, a 407-theorem axiom audit of the reserved-arm dependency and isolated kernel replay passed; the combined gate is pending.

## Horňák–Woźniak rho-two endpoint, 21 November 2026

Lean proves the rho-two exceptional endpoint construction for actual connected partitions under explicit endpoint equations, residue conditions and fifth-test input. Deriving those hypotheses, the smallest-count endpoint, full source-test and AVD reductions, and existence constructions remain. Strict compilation, a 396-theorem axiom audit and isolated kernel replay passed; the combined gate is pending.

## Horňák–Woźniak rho-one endpoint, 21 November 2026

Lean proves the rho-one exceptional endpoint, including selection of the wrapped arm from the stated three-arm residue conditions and fifth-test input. Rho-two, the smallest-count endpoint, full source-test and AVD reductions, and existence constructions remain. Strict compilation, a 333-theorem axiom audit and isolated kernel replay passed; the combined gate is pending.

## Horňák–Woźniak wrapped endpoint, 21 November 2026

Lean proves the wrapped-residue exceptional-piece endpoint through a connected graph partition under the chosen-arm bounds. Chosen-arm existence in remaining cases, further endpoint cases, the full AVD reductions and existence constructions remain. Strict compilation, a 289-theorem axiom audit and isolated kernel replay passed; the combined gate is pending.

## Horňák–Woźniak exceptional-piece foundations, 21 November 2026

Lean realizes reduced-arm allocations as actual connected partitions with one exceptional piece and proves the zero-carry and no-quotient-loss subcases, plus wrapped-residue identities. The other exceptional cases, full source-test and AVD reductions, and existence constructions remain. Strict compilation, a 280-theorem axiom audit and isolated kernel replay passed; the combined gate is pending.

## Horňák–Woźniak regular case, 21 November 2026

The regular two-size connected-partition case now follows for actual star graphs from the residue bounds and fifth-test witness, with no separate extremal-count hypothesis. Extra-piece cases, full source-test and AVD reductions, and existence constructions remain. Strict compilation, a 226-theorem axiom audit and isolated kernel replay passed; the combined gate is pending.

## Horňák–Woźniak graph realization, 21 November 2026

Every feasible two-size arm allocation now yields a connected partition of the actual star graph with the requested center and exact piece counts, in arbitrary order. The extra-piece cases, remaining endpoint hypotheses and AVD reductions remain. Strict compilation, a 205-theorem axiom audit and isolated kernel replay passed; the combined gate is pending.

## Horňák–Woźniak endpoint packing, 21 November 2026

Lean proves the complementary quotient/carry formulas, the regular endpoint packing with its explicit carry witness and transfer across any number of steps. Graph realization, remaining endpoint conditions, extra-piece cases and the AVD reductions remain. Strict compilation, a 120-theorem axiom audit and isolated kernel replay passed; the combined gate is pending.

## Horňák–Woźniak packing criterion, 21 November 2026

Lean now proves the exact ceiling-cost formula, the finite maximum and its one-step bound, the two-size arm-packing criterion and transfer to fewer larger pieces. Actual graph realization, endpoints and the AVD reductions remain. Strict compilation, an 82-theorem axiom audit and isolated kernel replay passed; the combined gate is pending.

## Horňák–Woźniak foundation, 21 November 2026

Lean defines the actual star-like graph and connected partitions, proves that center-free connected pieces lie in one arm, and proves the exact allocation criterion for fixed placements of larger pieces. Endpoint cases, the cited AVD reductions and existence constructions remain. Strict compilation, a 31-theorem axiom audit and isolated replay passed; the combined gate is pending.

## CKZ record conjectures completed, 21 November 2026

The original Conjectures 1 and 3 are proved for actual separable-permutation classes and all four record statistics, including singleton cases. The source-pinned, Apache-licensed trureturing dependency supplies the previously credited Conjecture 2 and permutation decomposition; this repository adds direct Pell certificates and the low-record comparison bridge. Strict compilation, a 1,132-theorem axiom audit and isolated kernel replay passed; the combined repository gate remains pending.

## CKZ low-record series, 21 November 2026

Three direct Pell certificates prove the required low-record generating-function coefficient inequalities, with the length-one exception explicit. Their identification with actual permutation counts and the arbitrary-index tail remain. Strict compilation, axiom audit and isolated kernel replay passed.

## CKZ certificate soundness, 21 November 2026

The CKZ checkpoint proves the verified finite polynomial certificates control their infinite Pell tails and give coefficientwise nonnegative Schröder substitutions for twelve tail-polynomial cases and four recurrence seeds. Arbitrary-index propagation and the actual permutation-class bridge remain open in this checkpoint. Strict compilation, a 213-theorem axiom audit and isolated kernel replay passed; the combined repository gate is pending.

## Prior-resolution withdrawal, 21 November 2026

The Karp–Vishnyakova–Zhang Bessel-ratio unimodality entry is no longer an active collection target. [Trure issue 25199](https://github.com/the-omega-institute/trureturing/issues/25199), published on 1 November, already contains a complete analytic proof for the same full domain. The [correction record](../research/kvz-bessel-unimodality/PRIOR_RESOLUTION_CORRECTION.md) preserves the mathematical reviews and attributes the prior resolution. The duplicate result and computational checks are removed; no shared Lean source or formalization receipt is changed, and no Lean work was performed for this correction.

## Zhu Jacobi–Stirling checkpoint

`Conjectures.ZhuJacobiStirling` derives the complete coefficientwise counterexample from the recurrence and checks the determinant identity and ordered-field negative region. The standalone strict source check, all-owned axiom audit and stock-kernel replay passed; the merged-package gate is pending. See [issue 163](https://github.com/1337isnot1337/solved-conjectures/issues/163).

## Han–Sabag–Kostina–Hassibi checkpoint

`Conjectures.HanSabagCounterexample` checks the rational matrix witness, the exact sparse infimum, a uniform lower bound over all sparse encoders, and a uniform gap over the open channel-gain interval. Matching lower bounds and approaching feasible encoders establish all four individual assignment infima. The module passed standalone strict source compilation, the all-owned axiom audit and stock-kernel replay; the combined gate is pending. See [issue 197](https://github.com/1337isnot1337/solved-conjectures/issues/197).

## Sonntag–Teichert checkpoint

`Conjectures.SonntagTeichert` proves the finite tournament theorem via blocker duality and representative counting. The forward oriented-graph two-star classification and an explicit realization with arbitrary additional isolated vertices are checked. The standalone strict source check, all-owned axiom audit and stock-kernel replay passed; the combined repository gate is pending. See [issue 70](https://github.com/1337isnot1337/solved-conjectures/issues/70).

## Brown–Mol counterfamily

`Conjectures.BrownMolInfiniteFamily` proves the literal trees have diameter four and a nonzero subtree root inside the forbidden disk for all sufficiently large parameters. `Conjectures.BrownMolCounterexample` separately verifies the explicit 1001-vertex example by exact integer arithmetic. Both results use a count of actual connected induced vertex sets. Strict standalone source checks, all-owned axiom audit and stock-kernel replay passed; the combined gate is pending. See [issue 210](https://github.com/1337isnot1337/solved-conjectures/issues/210).

## Coordination, 18 November 2026

The four active lanes in [issue 1](https://github.com/1337isnot1337/solved-conjectures/issues/1) are:

- Concrete CUT is complete through compact quotient/residue certificates.
  That worker has checked the exact analytic profile for Erdős 607, including
  its integral constant, mean, variance, and global phase bound.
  It now handles the uniform Fourier bounds.
- Pham denominator degree is complete. That worker now handles the
  exact generating function and its analytic evaluation for Erdős 607. Its
  Sylvester–Gallai dependency and finite core/gap foundations are checked.
- Compact Motzkin: finite signed-grid characters, compact-group measure, and
  the exact two-difference formula. The same worker has completed the
  all-parameter gap-five/gap-seven character formulas and an odd-cycle density
  theorem.
- Root: shared integration, the corrected finite Euler product, and the local
  coefficient analysis for Erdős 607. Its actual geometric counting identity
  is checked for every point count.

The other team coordinates in
[issue 2](https://github.com/1337isnot1337/solved-conjectures/issues/2). It owns
the independent `ThreeDistanceGraph*` density proof under
[issue 9](https://github.com/1337isnot1337/solved-conjectures/issues/9),
the completed rectangle asymptotic under
[issue 10](https://github.com/1337isnot1337/solved-conjectures/issues/10), and the
geometric dependencies of the lonely-runner classifications. Haralambis was
published in `22f3a5a`; the full distance-graph endpoint was published in
`a7b1ca1`. A third team coordinates higher-speed families, exact examples,
modular lifting, and the four-speed classification in
[issue 12](https://github.com/1337isnot1337/solved-conjectures/issues/12) and
[issue 13](https://github.com/1337isnot1337/solved-conjectures/issues/13).
That team also owns Graffiti.pc 318 in
[issue 15](https://github.com/1337isnot1337/solved-conjectures/issues/15) and
the newly added fixed-hyperplane loneliness result in
[issue 16](https://github.com/1337isnot1337/solved-conjectures/issues/16).
Its unregistered modules and separate validation lanes are described in
[`lean-candidates.md`](lean-candidates.md).
Read the coordination threads before changing lanes. Post new claims before editing.

## Complete mathematical formalizations

The fixed-scale solitaire counterexample and corrected arbitrary-layer
solitaire theorem are complete. The corrected theorem concerns actual recurrent
configurations and every positive horizontal scale tending to infinity.
Its finite and analytic chains passed source, axiom and independent kernel
checks, including the maximality of the actual stable reference.

Three-player War, Batista's Egyptian-fraction theorem, and the full CUT Family B
threshold are complete. Family B includes arbitrary infinite cut sets and
proves its base formula internally.

The full symmetric four-point and nonmixed-gap density theorems are complete,
including normalization, literal tile semantics, periodic attainments and the
stated sharp local bounds. The concurrent team's proofs were published in
`6c09508` and merged here through `9b4fff3`.

The general finite CUT decision theorem is complete, with two independent
constructions. Both prove that a finite test accepts exactly the proposed
representations of the actual game. Candidate enumeration is complete when a
representation exists. Both concrete games are now complete as well:
`CutPeriod.Weight.both_games_exact` identifies their actual recursive values
and proves least eventual period 12, saltus 8, and earliest start 7.
Its complete 23-module closure passed independent kernel replay.

Pham's primary and dual limiting-series identities are complete. The proof
derives stabilization from actual finite orbit levels, solves finite-prefix
recursions, and proves reduced denominator degrees 5 and 10. It uses no
published rationality or degree bound. Its 36-module closure passed strict
source checks, a 1,080-declaration axiom audit, and independent kernel replay.

The finite Motzkin theorem is also checked: every finite abelian group generated
by the two marked elements has an attaining independent set and an attaining
circle character with the same normalized value. The full compact-group
equality is now checked as well: actual Borel-set density equals the
continuous-character supremum for arbitrary compact Hausdorff abelian groups
with invariant probability measure, including zero differences. Its 34-module
closure passed strict sources, the 664-theorem axiom audit, and independent
kernel replay. The relation-basis formulas and finite-relation attainment
have also passed a 39-module closure with a 729-theorem audit. The cyclic
formulas for every positive modulus, gcd scaling, odd-cycle criterion, and
stated example passed a 48-module closure with an 812-theorem audit. The
exhaustive basis classification, explicit rational interval witnesses, and
exact algorithmic claims remain in progress.

Graffiti.pc Conjecture 318 and its stated sharpness example are complete.
The theorem is quantified over every finite connected simple graph of order at
least two. It uses Mathlib graph distance, counts each undirected complement
edge once, and derives the total-dominating-pair and total-domination-number
conclusions. The contributed proof credit remains with
[@JesterInABarrel](https://x.com/JesterInABarrel/status/2123233964827812334).
The three graph modules passed local checks and the hosted base candidate job
before accepted registration.

The runner family and example components are also registered. They include
the consecutive family for every parameter and every runner count from 2
through 14, the two exceptional eight-speed families, and classification
within all three stated eight-speed product families. The seven- and
eight-speed exceptional examples have exact global values. These statements
do not supply exhaustive higher-speed classifications. The complete fixed-hyperplane theorem is registered, including its original
uniform probability, exact counting, Haar-shift, endpoint and sharpness
statements. Its exact 72-module closure passed fresh strict sources, the
all-owned/raw-private audit, and stock kernel replay.

The verified snapshot `c0cf593` passed its source build, the audit of 6,954
project theorem declarations, and independent kernel replay of all 152 proof
modules and both roots. The separate `a7b1ca1` checkpoint passed its complete
hosted source/audit/kernel workflow. The `c862951` integration renamed the two
independent rectangle modules to resolve a namespace collision, replayed both,
and passed the combined source build and 7,581-declaration audit.
Local verification and hosted CI receipts are
recorded separately.
The subsequent `18bf908` Pham/finite-Motzkin checkpoint passed the hosted full
source, audit, and kernel workflow for all 219 accepted proof modules and both
roots, in [run 44450524136](https://github.com/1337isnot1337/solved-conjectures/actions/runs/44450524136).
See [the status report](lean-status.md) for declarations and checked scope.

The full growing-rectangle theorem is complete. The real-to-grid bridge,
cumulative partition asymptotic, both reservation regimes, and the uniform
limit for every width at least the height are checked. The 46-module closure
passed independent kernel replay and its 587-declaration axiom audit.

The unconditional four-speed gap theorem is complete. The cutoff 5,832 and
finite modular certificates prove that the only directions below `2/9` are
`[1,2,3,4]` and `[1,3,4,7]`, up to positive scaling and permutation. Both have
value `1/5`, and the four-speed runner bound follows. All 84 modules in the
closure have source, axiom, and independent kernel component coverage.

The finite plane classification covers all 122,880 indexed candidates. Its
`FourSpeedGap` input is now a proved theorem. With that input, every positive
primitive five-speed tuple below `1/5` either has all coordinates at most
279,841 or contains a dilated critical quadruple. In the second case its
value is `s/(5s+1)`. The bounded five-speed classification remains separate work.

## Campaign checklist

1. CUT is complete: the general finite test, exhaustive candidate enumeration,
   both actual game identifications, and exact arithmetic parameters are proved.
2. Pham is complete: actual orbit limits, both rational identities, and exact
   reduced-denominator minimality are proved.
3. Distance graphs are complete: all density and character formulas, small
   exceptions, periodic attainments, and the infinite discrepancy branch.
4. Two-difference Motzkin is complete: the general compact equality,
   exhaustive relation-basis classification, cyclic criteria, literal
   attaining witnesses, exact evaluator, and explicit complexity bounds
   are proved and registered.
5. Haralambis is complete: its exact density equality and optimal pair-sum
   periodic attainment were published in `22f3a5a`.
6. Five-speed spectrum: complete the modular lifting/enumeration outside the
   checked critical families. The four-speed gap is proved; the rational-plane
   certificate and coordinate-cutoff reductions are checked.
7. Tight six speeds and critical planes: the uniform reduction, complete
   equality classification, plane enumeration and large-norm consequence.
8. Six-speed spectrum: the remaining family branch, norm reduction, modular
   lifting, and exhaustive classification; the consecutive family is checked.
9. Eight-runner equality cases: the norm reduction, complete modular
   certificates and lifting to the three listed directions.
10. Nine-runner equality case: the norm reduction, modular certificates and
    uniqueness of the consecutive direction.
11. Ten-runner equality case: discharge the lower-runner assumptions of the
    checked norm reduction, then prove exhaustive modular classification and uniqueness.
12. Seven-speed spectrum: norm reduction and complete lifting/enumeration;
    the infinite family and all 27 exceptional values are checked.
13. Eight-speed spectrum: norm reduction and exhaustive lifting outside the
    three classified product families; the listed exceptional values are checked.
14. Eleven-through-fourteen-runner equality: discharge the lower-runner assumptions
    of the checked norm reductions, then prove all modular classifications and uniqueness.
15. Growing rectangles are complete: real tiling semantics, cumulative
    partition estimates, and the uniform asymptotic over every width `w ≥ h`.
16. Erdős 607 is complete: actual geometric counting, exact formal and
    analytic generating functions, Fourier extraction, the local limit and
    tail estimates, and the sharp asymptotic with its exact prefactor are
    proved and registered.
17. Graffiti.pc Conjecture 318 is complete, including the all-order theorem
    and sharp five-vertex example.
18. Loneliness on a fixed hyperplane is complete. Its original uniform
    probability estimate, exceptional-subspace description, exact counting
    polynomials, Haar-shift limits, endpoint density and sharpness are proved.
19. Li coefficient sign: the 44-module development includes actual tree
    properties, all connected partition types, full elementary coefficients,
    finite-colour stability and exact connected-partition counts. Its
    complete verification and registration are recorded below.

The pair-sum maximum theorem and the checked values of 31 finite speed lists
are reusable components. They do not establish any exhaustive classification.
The common interface is `Conjectures.LonelinessPairBridge`.

## Verification and continuation

Use the pinned toolchain and Mathlib manifest in `lean/`. Run
`scripts/verify_lean.sh` from the repository root. It builds accepted modules
one at a time, builds the root imports, audits every project theorem including
private declarations, and replays each accepted module with `leanchecker`.
The only permitted transitive axioms are `propext`, `Classical.choice` and
`Quot.sound`.

The full hosted gate at `3349777d40eacc26df93df09dad3d95c0333e59b`
passed on 18 November 2026: 433 proof modules, both roots, and an audit of
11,867 project theorem declarations. The
[receipt](accepted-3349777-hosted-receipt.json) records every replayed module
and links the exact workflow run. Later source registrations require their
own merged receipts.

The hosted Lean action performs setup and cache retrieval; the shared script
performs the source build. This prevents simultaneous large certificate
reductions from exhausting runner memory. No source, axiom or kernel gate is
omitted.

The earlier large higher-pile CUT automata remain preserved outside the accepted
roots. They are no longer needed for either concrete theorem. The accepted
compact certificate route has seven new modules and independently checked
collision and lower-option arguments for every pile size.
See [the concrete CUT plan](../results/cut-arithmetic-periodicity/LEAN_PLAN.md).

Refresh remote `main` before each publication. Preserve concurrent sources,
merge shared imports/audit lists additively, and publish a verified snapshot.
A finite verifier, partial lemma or passing CI run does not close a stronger
mathematical statement.


## Latest verification and candidate boundaries

The full 397-module checkpoint at `42fff1a2` passed hosted source checking,
a 10,843-theorem axiom audit, and independent replay of every accepted
module and both roots. Later registrations retain their own component
receipts; the current accepted closure has 482 proof modules and two roots.

The next analytic candidates derive the actual core Gaussian bound, core
weight limit, mean and variance limits, characteristic-product limit,
Gaussian integral, and supported lattice/Fourier integral limit. Exact
branch coefficients and the Fourier change of variables are checked in
separate tasks. Their current source drafts are not accepted proofs.
The final coefficient draft connects these limits to the literal geometric
record count and the stated prefactor. It has its own `sharp-asymptotic`
candidate task and still requires all three verification gates.


## Five-speed finite certificate checkpoint, 19 November 2026

All 260 scalar tables and 574 required canonical-plane candidates are now
published in 24 separately gated groups. Their complete hosted gates are
still running. The 29-module cached-root checkpoint at `108168d` passed its
full hosted source, axiom, and stock-kernel gate. The new packed selector
and oracle let the previously failing p1789 ordinary row compile locally.
The repaired map 26 and bounded block helper passed their local source,
axiom, and independent kernel gates. Eight new groups cover all 164 maps;
the final aggregate and complete root-prime coverage remain open. See
[the scoped checkpoint](five-speed-packed-bounded-candidates.md). Accepted
roots are unchanged, and Li remains last.


## Five-speed root candidate and component gates, 19 November 2026

The 227-module finite-assembly closure passed hosted source compilation,
the owned transitive axiom audit, and stock-kernel replay. Its coverage
hypotheses are still explicit. Five of the 24 scalar/plane groups also
passed their complete hosted gates. A complete p179 root candidate is now
published in 14 modules; only its cache, packed oracle, helper, and first
part have local source evidence so far. Its full hosted gate remains
pending. See [the exact scope](five-speed-root179-candidate.md) and
[component receipts](five-speed-receipts/hosted-component-index.json).


## Frankl counting components — 19 November 2026

Six proof modules were checked at `57d699c770471fc898850079bde384a269da5d4f` in
[run 44475531664](https://github.com/1337isnot1337/solved-conjectures/actions/runs/44475531664).
All four component jobs rebuilt their exact source closures, audited all
113 project theorem declarations using only `propext`, `Classical.choice`, and
`Quot.sound`, and replayed all six kernel objects with the unchanged pinned
checker. The accepted root, required endpoints, and replay list now include
those exact modules. The full merged-package run is a separate gate.

This verifies the general local-certificate implication, actual graph
bijection, finite lopsided-conditioning theorem, and numerical inequalities.
It does not yet verify either complete Frankl result. See
[the scope and remaining obligations](frankl-formalization.md) and
[the exact hosted receipt](frankl-foundations-hosted-receipt.json).


## Frankl large-generator theorem — 19 November 2026

The full `k ≥ 15` theorem is checked: in every finite `k`-uniform generating family with exactly three generators through each point and pairwise intersections of size at most one, every point belongs to at least `657/1000` of the distinct unions, including the empty union. The cyclic span-four theorem and the `3 ≤ k ≤ 14` high-girth cases remain incomplete.

The exact 16-module closure at `663f72751f7cfb13e533050985072e59204cbd26`
passed strict source checking, a 231-theorem transitive axiom audit, and
independent kernel replay in [job 135402205987](https://github.com/1337isnot1337/solved-conjectures/actions/runs/44477677129/job/135402205987).
The only allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.
The probability estimates, lopsided dependence, query independence, and
bijection with actual distinct unions are all proved internally. Thirteen
additional modules are registered here. The full merged-package gate is
separate from this exact component receipt.
See [the source-hash receipt](frankl-large-hosted-receipt.json).

## Hadamard automorphism lane, 19 November 2026

[Issue 21](https://github.com/1337isnot1337/solved-conjectures/issues/21) owns
`HadamardAutomorphism*.lean`, separately from the sequence and border work
in issue 17. The signed-automorphism theorem and both norm-obstruction proofs
are complete. Their actual matrix, signed-group, field, integer, and ideal
definitions are connected internally; the final statements retain no
unproved structural or number-theoretic hypotheses.

The registered source, standard-axiom, and unchanged pinned-kernel receipts are:

| Component | Snapshot | Modules replayed | Project theorems audited | Receipt |
| --- | --- | ---: | ---: | --- |
| Arithmetic and integral-basis coefficients | `56cb125e` | 5 | 38 | [Receipt](verification/hadamard-automorphism-arithmetic-56cb125e.json) |
| Literal Fourier matrix and determinant quotient | `ee1be6e0` | 6 | 32 | [Receipt](verification/hadamard-automorphism-fourier-ee1be6e0.json) |
| Signed normalization and cycle coordinates | `e9a9bb45` | 7 | 100 | [Receipt](verification/hadamard-automorphism-permutation-e9a9bb45.json) |
| Quadratic field and constructed-prime class order | `ae7871fc` | 9 | 111 | [Receipt](verification/hadamard-automorphism-class-order-ae7871fc.json) |
| Cyclotomic unit descent and norm exclusion | `7098a0e8` | 12 | 128 | [Receipt](verification/hadamard-automorphism-cyclotomic-7098a0e8.json) |
| Complete matrix and signed-group assembly | `fb6b6e06` | 28 | 297 | [Receipt](verification/hadamard-automorphism-assembly-fb6b6e06.json) |
| Independent relative-ideal-norm proof | `fb6b6e06` | 15 | 164 | [Receipt](verification/hadamard-automorphism-class-alternative-fb6b6e06.json) |
| Quadratic-field uniqueness and integer-coordinate iff | `0a1deef7` | 16 | 157 | [Receipt](verification/hadamard-automorphism-quadratic-model-0a1deef7.json) |

The closures overlap; these counts are not additive. Their union has 37 proof
source modules, excluding import-only candidate wrappers. All are registered
in the root imports, required-theorem audit, and replay list. The full theorem
uses Mathlib's actual Hadamard predicate, and the quotient cardinality result
applies to every subgroup of the actual signed automorphism group.

The quadratic-field uniqueness and exact integer-coordinate equivalence are
also checked. The separate sequence, quotient enumeration, and fixed-border
statements remain under issue 17. The later fixed-border common multiplier
bound and 151-orbit statement are complete under
[issue 22](https://github.com/1337isnot1337/solved-conjectures/issues/22), in
the 12 `HadamardBorderSymmetry*.lean` files described below. These do not
establish Hadamard existence at 2396. Li has not been started.

## Frankl local certificate checkers — 19 November 2026

The accepted package now includes `FranklLocalCertificate` and
`FranklLocalMaximalCover`. The first checker tests every boundary pair
`M ⊆ E ⊆ B`. A successful nonzero nonnegative integer weight vector gives
an abundant point in the actual family of distinct unions.

The maximal-cover checker is proved equal to the first checker. For each
inside pattern, it uses the union of all local generators contained in the
allowed inside and exterior set. It therefore avoids enumerating every local
union without changing the compatible-pattern count.

The exact five-module closure at `ad07e385` passed strict source checks, an
explicit import-all audit of 66 project theorems, all eight required endpoint
checks, and the unchanged pinned kernel replay.
[Hosted receipt](verification/frankl-maximal-cover-ad07e385.json) ·
[Scope and reproduction](frankl-fc-formalization.md#local-maximal-cover-checker).

This registration asserts no finite window weight certificate. The cyclic
window data, graph reduction, and complete span-four assembly remain separate.
The full merged-package gate is also separate from this exact component check.

## Frankl FC and small cyclic components — 19 November 2026

The accepted package now contains the full Vaughan shortcut. Every finite
union-closed family containing three distinct triples through a common point
has an abundant point in the union of those triples. The proof has no ambient
ground-size restriction and does not assume that the family contains the
empty set. Classification, integer certificates, and finite-support transport
are all proved in Lean.

Every nontrivial cyclic span-four generator family on at most six sites also
has an abundant point. The proof permits arbitrary generator sizes and cyclic
overlaps. It uses exact search trees, the Vaughan shortcut, a Pasch certificate,
and the two-point shortcut.

Further checked results concern the specified 35-edge residual graph. Its
period-seven, period-eight, and period-ten words are zero. Every nonzero
period-nine word generates a family with an abundant point. These statements
retain explicit residual-graph membership. The reduction of arbitrary larger
cyclic families to that graph still needs its finite window and rank data.

At source snapshot `6544adcc`, the exact 53-module closure passed strict source
checks, an import-all audit of 2,057 project theorems, 56 required endpoint
checks, visibility checks for all 534 private certificate nodes, and stock
kernel replay of every module. The 50 newly registered sources match that
snapshot byte for byte.
[Hosted receipt](verification/frankl-fc-packet-6544adcc.json) ·
[Detailed scope and reproduction](frankl-fc-formalization.md).

The complete span-four theorem and the small-degree high-girth theorem remain
incomplete. The full merged-package gate is separate from these component
checks. Li remains deferred.

## Frankl mask checker and exact domains — 19 November 2026

The accepted package includes `FranklLocalMaskCertificate` and
`FranklLocalMaskDomains`. The mask checker decodes the actual finite generator
family and counts each compatible inside set once. Its domain constructor
proves the exact inside and boundary powersets, including code bounds and
absence of duplicate inside codes. Literal quotient masks can therefore be
checked without assuming an injective unwrapping map.

At `a632fc82`, all ten sources passed strict checking, an import-all audit of
163 project theorems, all 38 required endpoints, and stock kernel replay of
every module. The two newly registered sources match that snapshot exactly.
[Hosted receipt](verification/frankl-mask-domains-a632fc82.json) ·
[Scope and reproduction](frankl-fc-formalization.md#local-mask-checker-and-domains).

This registers reusable checker semantics. The full finite weight collection
and graph/rank tables remain separate obligations. The complete span-four
theorem remains incomplete, and the full merged-package gate is separate.

## Complete fixed-border symmetry theorem — 19 November 2026

Issue 22 is complete. The 12 `HadamardBorderSymmetry*.lean` sources prove
the cyclic common multiplier bound and the 151-orbit lower bound from the
literal sign and autocorrelation hypotheses. The final statement quantifies
over arbitrary finite abelian domains and every subgroup preserving all four
rows. The full row-preserving group is also defined and covered explicitly.

The proof constructs the subgroup splitting, rather than assuming product
coordinates. It then transports the rows, correlations, full automorphism
subgroup, and actual orbit quotient. The symmetry obstruction uses compressed
energy 608 and correlation 596 directly, so the fourteen-pattern enumeration
and normalized baseline forms are unnecessary inputs.

At `682d0917`, the complete 12-module closure passed strict source compilation,
the standard-axiom audit of 216 project theorems, all required endpoints, and
independent replay by the unchanged pinned kernel checker. Source and gate
hashes match the archived receipt. The earlier product-domain assembly passed
its ten-module, 154-theorem gate at `2006a76a`.
[Full receipt](verification/hadamard-border-transfer-682d0917.json) ·
[Product-domain receipt](verification/hadamard-border-main-2006a76a.json) ·
[Statement and proof](../results/hadamard-2396/BORDER.md#lean-verification).

The complete closure can be reproduced from the repository root with:

```bash
python3 scripts/verify_hadamard_border_symmetry_candidate.py transfer
```

All 12 sources are now registered in the accepted root, theorem audit, and
kernel-replay list. The separate merged-package gate still applies. This
registration does not include the sequence restrictions, quotient certificates,
pattern enumeration, or matrix border construction owned by issue 17.

## Frankl cyclic assembly and weight helpers — 19 November 2026

The accepted package includes the all-period span-four assembly with its
original eleven finite-check premises: eight graph, rank and literal-weight
checks, plus three actual short-period weight checks. The family transfer
retains arbitrary finite union-closed families and requires no empty member.
The theorem is still conditional; the concrete finite packet is unfinished.

The unchanged components passed five hosted proof jobs:

| Closure | Modules | Audited theorems | Private finite nodes |
| --- | ---: | ---: | ---: |
| Assembly and weight batches | 76 | 2,440 | 597 |
| Literal period-7/8/9 pilot | 25 | 378 | 24 |
| Word coverage | 1 | 22 | 0 |
| Exact injective transport | 23 | 371 | 0 |
| Cached mask evaluator | 10 | 155 | 0 |

Each job rebuilt its complete closure, audited every owned theorem with
explicit private imports, and replayed the exact closure with the unchanged
pinned stock checker. Only the three standard logical axioms are allowed.
The closures overlap; their union has 86 modules. This registration adds
32 unchanged proof modules, bringing the accepted set to 636 proof modules
plus two roots. The merged full-package gate remains separate.

The pilot checks only 16 original rows at each of periods seven, eight and
nine. The transport and caching theorems are generic. The 9,448-class orbit
dataset remains candidate data; it does not prove the full arithmetic,
transport or coverage tables.

[Assembly receipt](verification/frankl-span-four-77fa9a75.json) ·
[Pilot receipt](verification/frankl-cyclic-pilot-77fa9a75.json) ·
[Word-coverage receipt](verification/frankl-word-coverage-77fa9a75.json) ·
[Transport receipt](verification/frankl-mask-transport-5d86c291.json) ·
[Cache receipt](verification/frankl-mask-cached-5d86c291.json) ·
[Remaining finite work](frankl-cyclic-weight-orbits.md).

## Sharp cyclic cover, voltage normalization, and border transport

Thirteen new modules are registered after four exact component closures
passed strict source checks, the standard axiom whitelist, and independent
replay with the unchanged pinned kernel checker.

The sharp connected 95-vertex graph has an actual cyclic covering map, an
explicit simple 32-cycle, and exhaustive kernel certificates excluding
lengths 4, 8, and 16. Its seven-module closure audited 288 project theorems
at `c6735b93`. Arbitrary seven-voltage normalization constructs a graph
isomorphism for every abelian group, preserves actual cycle lengths, and
identifies the sharp graph in the same voltage class. Its four-module
closure audited 131 project theorems at `0cf8667d`. The universal cover
cycle theorem remains under issue 18.

The finite-border bridge transports the actual matrices and all five
certificate identities through canonical flattening, quotient relabeling,
and reflection. Its two-module closure audited 66 project theorems at
`23b2b187`; the finite certificate identities remain explicit inputs.
The actual-row bridge constructs a permutation, signs, and lifted translations
from explicit compression-shape premises. It preserves sign-valuedness and
every combined autocorrelation. Its two-module closure audited 14 project
theorems at `14ab84e7`. Deriving the compression shapes, checking the literal
finite certificate, and final Hadamard assembly remain under issue 17.

Reproduce the four exact closures from the repository root after installing
the pinned Lean environment:

```sh
python3 scripts/verify_erdos_gyarfas_sharp_candidate.py main
python3 scripts/verify_erdos_gyarfas_voltage_candidate.py normalization
python3 scripts/verify_hadamard_fixed_border_candidate.py fin16
python3 scripts/verify_hadamard_border_normalization_candidate.py main
```

The accepted-package root, required-theorem audit, and replay list contain
all thirteen modules. [Exact statements and receipts](lean-status.md#complete-sharp-95-vertex-example-and-arbitrary-voltage-normalization).

[Sharp example receipt](verification/erdos-gyarfas-sharp-main-c6735b93.json) ·
[Voltage receipt](verification/erdos-gyarfas-voltage-normalization-0cf8667d.json) ·
[Finite-border receipt](verification/hadamard-fixed-border-fin16-23b2b187.json) ·
[Row-operation receipt](verification/hadamard-border-normalization-main-14ab84e7.json).


## Universal cover, literal border, and length-598 registrations

The universal seven-voltage abelian-cover theorem is complete together with
the previously registered sharp 95-vertex example. The literal finite-border
matrices and the full length-598 order-eleven obstruction are also registered.
Their exact passing closures have 17/304, 3/1246, and 8/141 project
modules/audited theorems respectively; these overlapping counts are not
additive. Every closure passed strict source checks, the transitive
standard-axiom whitelist, and independent pinned-kernel replay. The finite
certificate gates also reproduce their exact public inputs and generated
sources. All recorded hashes were compared before registration.

Twenty new proof modules and 85 required declarations join the accepted
root, prebuild list, and audit. The accepted proof list now has 754 modules,
plus its two roots. This component registration does not replace the full
merged-package gate. [Exact statements and receipts](lean-status.md#complete-universal-abelian-cover-cycle-theorem).

The earlier Motzkin evaluator and explicit rational-interval closures are
also registered, including arithmetic complexity and actual interval-set
attainment. The prime-257 minimum-pair-20 support probe is registered only
for its stated narrow scope. The final relation-basis registration below
completes Motzkin. The remaining higher-runner classifications are incomplete.
Li remains last.


## Complete Motzkin relation classification

The 41-module relation-basis closure at `244cbd23` passed strict source checks,
the 743-theorem standard-axiom audit, and independent pinned-kernel replay.
The endpoint constructs all relation bases and derives the compact-density
trichotomy without a classification premise. Its two new modules and seven
new required declarations are registered from the unchanged receipt, after
comparison of all 52 recorded paths. This closes the last stated Motzkin
obligation; the earlier equality, evaluator, complexity bounds, and explicit
witnesses are already registered. [Exact scope and receipt](lean-status.md#complete-two-difference-motzkin-theorem).


## Complete fixed-border construction and length-1197 reduction

The fixed-border construction now starts with an arbitrary finite abelian
group, an actual subgroup of index four, and the four original sign rows
with their prescribed raw correlations. It constructs the normalized rows,
actual core and border, and final Hadamard matrix. The size-149 case returns
`Fin 2396`; all fourteen baseline patterns are derived with actual
row-operation witnesses. This completes the stated conditional border result.

The length-1197 Legendre component proves that the actual common-multiplier
order divides 27 and constructs the needed invariant quotient of order three.
The sharper bound of nine and finite quotient/no-lift packet remain open
formalization obligations. Four exact `e25e0dcd` component receipts cover
17/1441, 9/164, 22/282, and 2/11 modules/audited project theorems; the closures
overlap. All fifty recorded paths match, and 31 new modules with
17 required declarations are registered. The accepted prebuild now contains
787 proof modules and two roots. [Exact scope and receipts](lean-status.md#complete-conditional-fixed-border-construction-and-fourteen-patterns).
The full merged gate remains separate; Li remains last.

## Complete Frankl high-girth bound — 19 November 2026

Registered the full all-point `518208/1000000` distinct-union frequency
theorem for every `k ≥ 3` under three-regularity and incidence girth at least
sixteen. The proof connects the actual boundary-conditioned graph counts to
all K03–K14 numerical certificates and uses the accepted large-generator
theorem for `k ≥ 15`. The empty union is included; its removal and both girth
formulations are proved as well.

The exact 64-module closure passed fresh strict sources, an all-owned
1,363-declaration axiom audit with 35 required endpoints, and unchanged
stock-kernel replay at `f421f4434ffc8117a57a14b99c19818e76dcfd8e`.
The 47 new modules and 34 new required endpoints are registered after checking
the current source blobs against that receipt. The merged full-package gate
remains separate. Cyclic span-four verification continues in issue 20; the
Frankl directory and the overall campaign remain incomplete. Li remains last.

[Exact receipt](verification/frankl-components-44516856625/high-girth-theorem.json) ·
[Scope](lean-status.md#complete-frankl-high-girth-frequency-theorem).


## Complete Erdős 607 asymptotic

The literal geometric count now has its full sharp asymptotic, with the exact
constant from the note. The 78-module closure at `36b13722` passed strict
sources, the 1,582-project-theorem standard-axiom audit, and independent
pinned-kernel replay. The actual analytic generating function and Fourier
coefficient identity passed their 39-module/867-theorem closure at
`daa7d2c5`. Neither final endpoint assumes a local limit, tail bound,
measurability, dominating function, or coefficient-transfer theorem specific
to this problem; the closure supplies them.

The exact unchanged receipts are archived after comparison of all 93 recorded
paths. This registers 44 proof modules and 20 required endpoints, for
878 accepted proof modules plus two roots. [Exact statement and receipts](lean-status.md#complete-erdős-607-line-size-asymptotic).
The full merged gate remains separate. Li remains last.


## Actual Legendre-pair matrix and quotient transport

The actual two-row construction is checked for every finite abelian group: a Legendre pair yields a sign matrix of order twice the group cardinality plus two, with the required Hadamard Gram identity. In particular, a length-1197 pair yields an actual order-2396 Hadamard matrix. The proof derives the row-sum normalization internally.

The quotient transport is also checked. From the actual centered rows and an order-27 subgroup of common multipliers, Lean derives the order-133 quotient rows, their bounds, weighted sums and correlations, and the order-21 layer constraints used by the finite no-lift argument. No abstract quotient-data certificate is assumed. The final exclusion of order 27 and the sharper multiplier bound of nine remain pending the complete finite certificate and final assembly.

Both exact closures at `20e04e589d227086cc926579fc70806594d8f817` passed strict source checks with warnings treated as errors, the standard-axiom whitelist audit, and independent pinned-kernel replay. The 29 distinct source, verification-script, workflow and toolchain-pin paths in the two receipts were checked against current main before registration. 8 previously unregistered proof modules and 13 named endpoints are added; the accepted prebuild list grows from 878 to 886 proof modules, plus the two roots. Verification of the merged accepted package remains a separate gate.
[Exact endpoints and receipts](lean-status.md#actual-legendre-pair-matrix-and-quotient-transport).

## Complete two-speed insertion result, 19 November 2026

The full [two-insertion note](../results/lonely-runner-two-insertions/PROOF.md)
is now checked and registered: unrestricted positive speeds for every
`p ≥ 3`, the specified real witness interval, the Goddyn–Wong acceleration
criterion, common-dilation value bound, all small and unbounded branches,
and the literal three-insertion obstruction with an outside witness.
No finite certificate or cutoff is an unproved hypothesis.

The exact 27-module closure passed fresh warning-as-error source checks
without disabling linters, an audit of all 563 owned declarations
(424 theorems, 11 private declarations, 49 required theorem endpoints),
and exact stock-kernel replay of every module in a separate process.
The checked source snapshot is `9f51470529423e8135c08de881cd56f5b1fd9a95`;
its [raw receipt and original evidence](verification/two-insertions-exact-44524198858/)
were authenticated before registration. Eighteen new proof modules and
49 required endpoints are registered, with all 27 source hashes guarded.
The accepted prebuild list now contains 904 proof modules plus two roots.
The merged-package gate remains separate. Li remains last.
[Exact scope](lean-status.md#complete-unrestricted-two-speed-insertion-theorem).

## Six-speed realization direction, 19 November 2026

Both congruence classes in the proposed spectrum now have an unconditional
Lean realization theorem. Every `P ≥ 7` with `P % 6 = 1 or 5` is realized
by six distinct positive primitive speeds with exact value `(P−1)/(6P)`.
The proof includes the all-parameter progression family and `P=11`.
The exact 11-module closure passed fresh strict sources, the audit of all
392 owned declarations including 30 private declarations, and 11 exact
stock-kernel replay targets. All 15 required endpoints are theorems.
Two proof modules and 13 endpoints are registered, with all checked source
blobs guarded; the accepted list has 906 proof modules plus two roots.
The universal six-speed classification and merged-package gate remain separate.
[Scope and original evidence](lean-status.md#six-speed-spectrum-complete-realization).

## Complete fixed-hyperplane theorem

All original statements of the fixed-hyperplane note are registered. They
use the original ordered positive, pairwise-distinct integer sample and
the actual time maximum. The general normal is primitive and real-admissible;
the endpoint formula alone additionally requires every normal coordinate
to be nonzero.

The theorem closure proves the deterministic bound and exact containing-torus
maximum, the uniform `O(1/N)` probability error over all shifts, fixed-shift
and independent Haar-shift laws, the exact finite proper-subspace description,
the denominator quasipolynomial, the actual subthreshold numerator at every
`N≥1` with degree at most `k−2`, the endpoint frequency including `k=2`,
and the sharp `(1,2,3)` example. No density, finite-fan, Ehrhart, counting
or classification statement is an unproved premise.

[Run 44531509741/job 135585736594](https://github.com/1337isnot1337/solved-conjectures/actions/runs/44531509741/job/135585736594)
freshly checked the exact 72-module closure at `ee1f018fef258cdd54f73af31cdaf6485fd151cb`.
Sources used warnings as errors with no linter override. The all-owned audit
checked 1,403 declarations, including 1,149 theorems and 44
private declarations, and confirmed theorem kind for all 106 required
endpoints. Only `propext`, `Classical.choice` and `Quot.sound`
were allowed. All 72 modules passed exact singleton stock-kernel replay in
fresh one-worker processes.

The [unchanged raw receipt](verification/hyperplane-main-exact-44531509741/receipt.json)
has SHA-256 `1c0d6a6fbe2ea16bbcfa88808ec8d83f0e412217e76c03803780ff0737fa1c15`.
The [preservation record](verification/hyperplane-main-exact-44531509741/preservation.json)
authenticates the actual original source, object, audit, log and progress
bytes. Artifact `14535236819` has ZIP SHA-256 `27d65f3b5d667260dfad8d639f6d1182a3b5e54c032a2e2954d7764e060fe638`.

Registration adds 63 previously unregistered proof modules and 102 new
required endpoints, with all 72 checked source blobs guarded. The accepted
list has 969 proof modules plus two roots. This completes the fixed-hyperplane
result; verification of the merged accepted package remains a separate gate.
The [result-level scope](../results/loneliness-on-a-hyperplane/LEAN.md)
records the precise sample, formulas and distributional formulation.

## Conditional nine-through-thirteen speed norm reduction

The 81-module closure of `LonelinessTightNormBounds` is checked and
registered. For a positive primitive `k`-tuple with `9≤k≤13` and actual
loneliness value at most `1/(k+1)`, it proves the literal squared-norm
cutoff and a listed prime dividing no speed, under the explicit hypothesis
`∀ m, 1≤m → m<k → LonelyRunnerBound m`. The basis geometry,
nearest-plane bounds, all 7,936 KZ subset rows and prime-product margins
are proved internally.

[Run 44530735399/job 135583044214](https://github.com/1337isnot1337/solved-conjectures/actions/runs/44530735399/job/135583044214)
passed at `8162a5dfbe89e441600e7a3bbcc03b573df0880e`: all 81 strict source checks, the all-owned
audit of 1,696 declarations (1,445 theorems and 538 private declarations),
all 25 required theorem endpoints, and all 81 exact singleton stock-kernel
replays. Sources and audit used warnings as errors without a linter override;
the only allowed axioms were `propext`, `Classical.choice` and `Quot.sound`.

The [unchanged receipt](verification/loneliness-large-norm-exact-44530735399/receipt.json)
has SHA-256 `fba4b952a87271f9691e983dd69dafc0be5c07617e412884eb82f2894ec2fef5`.
The [preservation record](verification/loneliness-large-norm-exact-44530735399/preservation.json)
authenticates the actual original sources, objects, audit and process records.
Artifact `14535137698` has ZIP SHA-256
`b6678fb2e27c872d01a2bbd6bea9982abc42411e79999b6c4113961195ab3366`.

Registration adds 64 proof modules and 25 required endpoints. The accepted
list then contains 1,033 proof modules plus two roots. The merged-package
gate remains separate. Lower-runner assumptions, exhaustive modular
classification and final uniqueness remain open, so no result directory
becomes complete from this reduction.
[Exact hypotheses, cutoffs and scope](loneliness-large-norm-lean.md).

## Six-speed reduced fraction component

The exact reduced arithmetic forms and their unconditional realization are
registered in `LonelinessSixSpectrumArithmetic`. This includes the necessary
odd-denominator/gap consequence and the explicit `4/27` obstruction to treating
that condition as sufficient. All 12 modules passed strict source checking,
the all-owned/private standard-axiom audit (421 declarations), eight required
endpoint checks, and exact stock-kernel replay in job 135607998981 of run
44537865221. The unchanged evidence was authenticated from the original ZIP.
[Scope and receipt](lean-status.md#six-speed-spectrum-reduced-fraction-arithmetic).
The universal classification and merged-package check remain separate.


### Six-speed sporadic arithmetic checkpoint

`LonelinessSixSporadicBounds` now proves the nine original sporadic values and their arithmetic consequences, including permutation invariance, the proposed spectrum parameter form, `d < 3*q` for any positive representing denominator, and `q = 6*a + 1` for the reduced fraction. Exact job `135612147649` in run `44539038584` passed 13 fresh strict source checks, the complete 465-declaration audit, and 13 independent stock-kernel targets. Its unchanged evidence is recorded in `docs/verification/six-sporadic-exact-44539038584/`. Only the passing six-arithmetic job is used; the failed seven/eight sibling is excluded. This finite-table consequence does not establish universal six-speed classification.


### Higher spectrum realization and sharp candidate bounds

The registered `LonelinessSevenSpectrumRealization` and `LonelinessEightSpectrumRealization` modules construct distinct positive primitive speed tuples for every proposed seven/eight spectrum value. `LonelinessHigherSpectrumBounds` proves the 27 seven-speed and 17 eight-speed table values, all stated candidate-family spectrum forms, reduced-fraction identities, and the sharp bounds `5*d <= 13*q` and `17*d <= 21*q` for every positive representing denominator, with explicit optimality witnesses. Candidate membership and permutations are stated explicitly; universal tuple exhaustiveness is not assumed or concluded.

Exact run `44541874811`, job `135622052992`, passed all 16 fresh strict source checks, the complete 647-declaration audit, and 16 exact stock-kernel replays. The 26 required theorem endpoints and unchanged authenticated evidence are recorded in `docs/verification/seven-eight-spectrum-exact-44541874811/`. The failed sibling triangle and six-plane jobs are excluded from this acceptance record. Full seven/eight classification remains partial.


## Direct five-runner lower-bound candidate

The candidate `LonelinessFiveRunnerTheorem` joins the actual KZ geometry,
all smaller runner bounds, five complete modular certificates, and gcd
normalization to target `LonelyRunnerBound 5`. It retains both primitive
equality directions at `1/6`. Its final closure remains outside the accepted
root until the fresh strict-source, all-owned/private-axiom, and exact
stock-kernel gate passes. [Proof components and current scope](five-runner-exact-candidate.md).

### Higher-speed triangle consequence checkpoint

`LonelinessHigherTriangleConsequences` proves actual integer-distance-graph triangles for the stated six/seven/eight candidate families and all 53 sporadic rows, including the signed six-speed third family and gcd rescaling. Its Zhu implications for six, seven, and eight distances keep the exact primitive near-tight classification hypotheses explicit. They establish coloring and triangle consequences from those hypotheses; they do not establish the missing exhaustive classifications.

Exact [run 44545339492, job 135634276616](https://github.com/1337isnot1337/solved-conjectures/actions/runs/44545339492/job/135634276616) at `788e2572b877750158bd471191ef9701c50b93bd` passed 34 fresh strict source checks, the complete 1,024-declaration audit (805 theorems, 36 private declarations), all 23 required endpoints, and 34 independent exact stock-kernel targets. The original ZIP, receipt, source/control snapshot, object facets, audit, and logs were authenticated before preserving the unchanged evidence in [verification/higher-triangle-exact-44545339492](verification/higher-triangle-exact-44545339492/). Registration adds one module and 23 endpoints. Failed six-plane sibling jobs are excluded; the merged-package gate and unconditional result completion remain separate.



## Renault dependency proof and prime-307 pilot, 19 November 2026

The Renault foundation checkpoint passed its fresh source, complete owned/private axiom audit, and exact stock-kernel gate at `f6b37c31b67d4905a03ebafca4e427aaf36d8ad8`. It includes all eight universal real phase lemmas and the maximization, gcd-orbit, shift, fiber-arithmetic, and relabeling components. The full five-speed lower bound remains a separate candidate under [issue 38](https://github.com/1337isnot1337/solved-conjectures/issues/38); the foundation pass does not complete that bound or the five-speed spectrum.

The prime-307 pilot at `7bfbeef3715b82f33bae00493f05c72d7a6978e4` passed the same verification stages for minimum-pair roots 2 and 153. It preserves the original checker propositions and uses a proved equality to the faster counted-bit implementation. Full coverage for primes 271, 307, and 313 remains active. No whole-prime certificate or unconditional six-speed classification follows from this pilot.

Both unchanged receipts and their authenticated source, audit, control, and log evidence are preserved under [verification/renault-foundations-44549206241](verification/renault-foundations-44549206241/) and [verification/p307-pilot-44540677853](verification/p307-pilot-44540677853/). Exact counts, run links, and scope are recorded in [the Lean status](lean-status.md#renault-foundations-and-six-speed-prime-pilot-19-november-2026). Accepted registries and result-completion markers are unchanged.

## Conditional critical-seven classification checkpoint

The seven-coordinate critical-plane assembly and its large-norm family
conclusion are registered through `LonelinessSevenCoordinateClassification`
and `LonelinessSevenCoordinateLargeNormFamily`. All finite enumeration,
signed-coordinate transport, integer product parameters, gcd reduction, and
actual real-time family values are internal to the proof.

The remaining inputs are exactly `h5 : LonelyRunnerBound 5` and
`h6 : PrimitiveSixClassification`. The first is the lower bound `1/6` for
every nonempty positive distinct list of at most five speeds. The second
classifies every positive distinct primitive six-speed list of value at most
`1/7` as a permutation of `[1,2,3,4,5,6]`. Neither input is claimed
discharged by this component.

Under these inputs, a rational two-plane in seven coordinates has value
`1/7` exactly when it is a signed coordinate permutation of the standard
product plane. The standard-plane value direction is unconditional. A
positive primitive seven-speed tuple of value below `1/7` and Euclidean
norm at least `7*42^10` is a literal permutation of
`[1,2,3,4,5,6,7*s]`, with `s >= 1` and exact value `s/(7*s+1)`.

Exact [run 44547965580, job 135643591005](https://github.com/1337isnot1337/solved-conjectures/actions/runs/44547965580/job/135643591005)
at `d082b9a7adbed4144ccc9a961023bcae46f00e3d` passed 105 fresh strict
source checks, the 2,105-declaration all-owned/private audit (1,864 theorems,
630 private declarations), all 23 required endpoints, and 105 independent
exact stock-kernel replays. Its original 635-file archive was authenticated;
425 unchanged evidence files are preserved in
[verification/critical-seven-exact-44547965580](verification/critical-seven-exact-44547965580/).
The archive and receipt hashes, process logs, and validation report are
recorded there.

Registration adds 47 modules and 23 required endpoints. The complete finite
and source checks do not establish unconditional seven-speed exhaustiveness:
the lower-dimensional hypotheses and the remaining global classification
are still open. The merged-package gate and original-result completion
remain separate.


### Seven-speed low-gap reduction for the eight-speed proof

The accepted `LonelinessSevenLowGapInput` module proves the exact three seven-speed bases below `3/23` within the stated candidate classification, their value `1/8`, and the positive gcd-scaled conclusion for arbitrary positive distinct lists under the explicit primitive seven-speed classification premise. This supplies the literal low-gap input used by the eight-coordinate plane argument. It does not remove the classification premise or mark an original result complete.

Acceptance uses the original passing job `135655971010` in [run 44551449045](https://github.com/1337isnot1337/solved-conjectures/actions/runs/44551449045) at `aac4fff06ba8f6678d60a1665ab4790562cbbc5a`: 17 fresh strict project modules, all 663 owned/raw declarations (494 theorems, 16 private declarations), eight required endpoints, and 17 exact stock-kernel target replays. Artifact `14542014520` has ZIP SHA256 `256cfdb7f4e00cee8253f0f8c2e59037d9e3bcb4db428d3484054a7c7ed33077`; the raw receipt hash is `4d5996deff454e567510b3445317d11bea3ba1b65e8e6047d3637c8e41c30211`. The authenticated raw evidence is preserved in [`verification/seven-low-gap-exact-44551449045/`](verification/seven-low-gap-exact-44551449045/).


### Six-plane permutation coverage and chunk-join component

The 20-module finite-data component is accepted for its exact scope: all 43,200 coordinate-permutation lookup cells, three nested certificate pilots of 32/256/1,280 cases for the first pattern pair, and the generic quotient/remainder joins needed to combine a complete collection of certificate chunks. The largest pilot covers 1,280 cases; the pilots are not disjoint. The generic full-coverage conclusion retains the numerical chunk checks as hypotheses. This does not assert that all 1,152,000 candidate-pair cases are checked and does not establish the six-plane classification.

Original job `135655971048` in [run 44551449045](https://github.com/1337isnot1337/solved-conjectures/actions/runs/44551449045) at `aac4fff06ba8f6678d60a1665ab4790562cbbc5a` passed 20 fresh strict sources, all 414 owned/raw declarations (317 theorems, zero private declarations), nine required endpoints, and 20 exact independent stock-kernel targets. Artifact `14543834207` has ZIP SHA256 `1a8fa5d2400e25a00ca381c16a98be42f765cf7b199a07e171dfbb648dce5067`; the raw receipt hash is `e648e84040f83963f18d44152638d02c3c800e1e3ee1624a2de96d50285c67ee`. The authenticated original evidence is preserved in [`verification/six-plane-coverage-exact-44551449045/`](verification/six-plane-coverage-exact-44551449045/). The complete pair table has a separate verification and acceptance path.


### Six-speed norm geometry from an explicit plane gap

The 52-module norm component is accepted. For a positive primitive six-speed vector with loneliness value at most `1/6`, it proves Euclidean norm strictly below `21829`, assuming `LonelyRunnerBound 4` and that every rational two-dimensional plane containing the vector has space value at least `2/11`. It constructs a reduced integral basis, proves all five Gram-prefix bounds, and proves the determinant identity internally. The five required endpoints are `exists_gram_data`, `numerical_margin`, `squaredNorm_lt`, `norm_lt`, and `natural_squaredNorm_lt` in `Loneliness.SixSpectrumNormGeometry`.

The norm bound is stronger than the original ambient bound `163350`. This component retains its plane-gap and four-speed hypotheses. It does not prove arbitrary rational-subspace covolume bounds, the finite off-critical classification, or the complete six-speed spectrum. The result-level completion status is unchanged.

Original [run 44555513834](https://github.com/1337isnot1337/solved-conjectures/actions/runs/44555513834), job `135670390120`, passed at `f66de17709f2dd9f46c96cd1fc9b0ed3b60fda2a`: 52 fresh strict source modules, all 1,269 owned/raw declarations (1,051 theorems, 60 private declarations), five required endpoints, and 52 exact independent stock-kernel targets. The axiom whitelist was exactly `propext`, `Classical.choice`, and `Quot.sound`. Verification budgets and warning settings were unchanged.

Artifact `14544624570` has ZIP SHA256 `541410f007a756a1a10fee1c5abebb53d6cd6c40ecf163c576d0df9a18f15a11`; the unchanged receipt hash is `1ac075b71fe894ee81f37c8bab28dc9679b4528371c9afaef61ee14f4fc81a5c`. All 65 original source/control/helper/configuration files matched the passing tree. All 317 archive members were authenticated. The 213 unchanged raw evidence files are preserved under [`verification/six-spectrum-norm-exact-44555513834/`](verification/six-spectrum-norm-exact-44555513834/), with a separate preservation record and archive inventory. `scripts/validate_six_spectrum_norm_archive.py` reproduces the offline provenance checks; it does not claim a new Lean execution. `LonelinessKZSmallData` and `LonelinessSixSpectrumNormGeometry` are now registered with the accepted root and verifier.


## Product-plane speed bridge checkpoint (2026-11-19)

The accepted registry now includes `Conjectures.LonelinessProductPlaneSpeeds` and its four actual integer-speed endpoints. [Run 44553736720](https://github.com/1337isnot1337/solved-conjectures/actions/runs/44553736720), job `135664057075`, freshly checked its exact 40-module closure, audited 860 owned/raw declarations (730 theorems and 10 private declarations), and separately replayed every project module in the pinned stock kernel. Original source and artifact bytes were authenticated and preserved under [`docs/verification/product-plane-speeds-exact-44553736720`](verification/product-plane-speeds-exact-44553736720/).

The bridge extracts the full integer speed list from membership in an explicitly signed/permuted product plane, with integrality supplied by a base coordinate equal to one. Its final theorem invokes the already proved product-family arithmetic to obtain `W ++ [q*s]` under the stated primitive, positivity, residue, and value hypotheses. Geometric exhaustiveness and every finite spectrum classification premise remain separate. This checkpoint does not change the completion status of any spectrum result.


## Five-speed norm component, 19 November 2026

The positive primitive five-speed norm cutoff `347142` at threshold `1/6`
and the existence of a coordinate-avoiding prime among
`149, 151, 163, 167, 173` are checked and registered. The two new norm modules
passed fresh source checking, the all-owned/private axiom audit, and exact
stock kernel replay of their full 108-module closure. All 15 component
endpoints are required by the gate. See the
[original receipt and authenticated evidence](verification/loneliness-five-runner-norm-44555436644/README.md).

The complete five-speed finite classification still requires its separate
certificate gate. This norm component does not complete a result-directory
classification or discharge any higher-speed finite enumeration.

## Six-coordinate plane semantics (19 November 2026)

The six-coordinate plane semantic component is accepted from [run 44557816556](https://github.com/1337isnot1337/solved-conjectures/actions/runs/44557816556), job `135681972978`, at source commit `fdd22c92c4e8c88a486881b5561e95be5c44cd62`. Its exact 63-module closure passed fresh strict source compilation, the complete owned and private declaration audit, and 63 independent stock-kernel target replays. The audit checked 1,313 owned/raw declarations, 1,055 theorems, 15 private declarations, and all 31 required theorem endpoints. The allowed axioms were exactly `propext`, `Classical.choice`, and `Quot.sound`.

For a coordinate-free rational two-dimensional plane in six coordinates with actual space value below `2/11`, the semantic theorem recognizes one of the three original planes, up to coordinate signs and permutations: `(s,2s,3s,4s,5s,t)`, `(s,3s,4s,5s,9s,t)`, or `(s,t,s+t,2s+t,3s+t,3s+2t)`. The proof retains explicit inputs for the four-speed runner bound, the exact five-speed low-gap classification, and complete candidate-pair certificate coverage. The five-speed input is separately derived from `Loneliness.FiveSpeedCertificate.SporadicExhaustion`. The enumeration interface checks all 720 permutation ranks and proves that complete direction lookups and row/block certificate checks imply `CandidatePairsChecked`.

This acceptance supplies the semantic bridge and exact coverage interface. It does not discharge `SporadicExhaustion`, supply the complete numerical pair certificate, or establish unconditional six-plane or six-speed spectrum classification. The later wrapper that discharges the four-speed hypothesis and the separate complete finite-data gate are outside this receipt. Result-level completion boxes are unchanged.

Artifact `14550615276` contains 10,650,461 bytes and has ZIP SHA-256 `236667c95848500328181d1b15b1414ec6544a68daa31b27884e6974f19a4eeb`. The unchanged original receipt has SHA-256 `431d8358951a12ba901f94a124724a07a26802dcc7f43a65110ab5ba530f625a`. All 76 historical proof-source, helper, configuration, and controller Git blobs were authenticated; all 383 archive members, object hashes, process records, and audit data were checked. The 257 unchanged raw evidence files, archive inventory, and separate preservation record are under [`verification/six-plane-semantics-exact-44557816556/`](verification/six-plane-semantics-exact-44557816556/).

The original command was `python3 scripts/verify_higher_spectrum_realization_exact.py six-plane-semantics` at the stated source commit. `scripts/validate_spectrum_archive.py` reproduces the offline archive checks; preservation is not a new Lean execution. The eight new semantic modules, their seven previously unlisted five-speed dependencies, and the 31 required endpoints are appended to the accepted root, prebuild, and audit registries. `LonelinessSixPlaneDefs` and `LonelinessSixPlaneEnumeration` were already registered from the earlier coverage component.

## Unconditional five-speed bound and primitive transport, 19 November 2026

The full Renault gate passed at `93022640cfd5f8c4fa2ce837dd8743d101374f2d`: 106 fresh strict project sources, 3,003 audited owned declarations including 230 private declarations, 100 required theorem endpoints, and 106 exact unchanged stock-kernel targets. `Loneliness.Renault.five_speed_lonelyRunnerBound` has no unproved lower-runner premise. The common-time theorem covers every positive five-tuple, including repeats. This closes a lower-bound dependency; it does not close the five-speed spectrum classification.

The primitive-classification transport and distinct-positive-padding gates also passed, on their full 15- and 16-module closures. Padding shows that exact-length primitive bounds suffice for the full bound at that length without an additional smaller-runner premise. The closed-sublevel classification and values of its families remain explicit hypotheses. Lower-runner assumptions in norm or classification proofs remain separate obligations.

All three downloaded artifacts and their source/object/control/log/profile/audit digests were authenticated before registration. Original receipts and durable evidence are in `docs/verification/renault-five-speed-44556621749/`, `docs/verification/runner-bound-transport-44557243499/`, and `docs/verification/runner-bound-padding-44559299513/`. Registration adds 23 module roots and 109 theorem endpoints; the merged accepted-package gate remains separate. The campaign is incomplete and Li remains last.

## Six-speed prime-product reduction checkpoint (2026-11-19)

The accepted registry includes `LonelinessSixSpectrumFieldsDefs` and `LonelinessSixSpectrumFieldsProduct`, with 16 named endpoints. Original [run 44559208975](https://github.com/1337isnot1337/solved-conjectures/actions/runs/44559208975), job `135691218139`, freshly checked all nine project modules, audited 266 owned/raw declarations (202 theorems and 13 private declarations), and separately replayed all nine modules in the pinned stock kernel. Original evidence is authenticated and preserved under [`docs/verification/six-fields-product-exact-44559208975`](verification/six-fields-product-exact-44559208975/).

These proofs identify the exact 80 signed triple factors and show that sufficient finite prime covers, together with the actual squared norm and the explicit prime-product inequality, force an actual additive triangle for a positive sextuple below `1/6`. Prime coverage remains an input over every nonzero raw residue tuple, including repeated residues. No numerical prime certificate, orbit completeness, sporadic exhaustion, or universal spectrum classification is claimed by this checkpoint.

## Conditional gcd shift component (19 November 2026)

The arbitrary-modulus nine-speed gcd shift test is checked and registered.
With positive distinct speeds, `LonelyRunnerBound 8`, and `d ≥ 2`, a nonempty
exceptional set with literal gcd-weighted ceiling cost below `d` implies
loneliness strictly greater than `1/10`. The gate checks the positive
floor-cost and ceiling-cost formulations, residue transport, and the general
gcd-weighted grid count.

The two new modules and 20 required endpoints passed fresh compilation of
their exact 17-module closure, the complete owned/private declaration audit,
five quantified statement assertions, and exact stock kernel replay in
[run 44562942517](https://github.com/1337isnot1337/solved-conjectures/actions/runs/44562942517).
The [authenticated evidence](verification/loneliness-gcd-shift-44562942517/README.md)
preserves the original receipt and exact scope. The eight-speed hypothesis
is retained; no unconditional nine-speed classification or finite census
is accepted by this checkpoint.


### Six-speed first-cover support reduction checkpoint

The support-to-prime-cover bridge is accepted from [run 44563135178, job 135701825289](https://github.com/1337isnot1337/solved-conjectures/actions/runs/44563135178/job/135701825289), exact source commit `3273ac1a24ea061b0cbd73244e2ac57c08d491ec`. Its [preserved original evidence](verification/six-fields-support-exact-44563135178/preservation.json) covers 22 fresh strict source checks, all 837 owned and raw declarations, 545 theorems, 72 private declarations, 22 required endpoints, and 22 exact stock-kernel targets. Five newly registered modules include the existing public multiplicity and arbitrary-arity support-list helpers, plus the three six-field support/transport modules.

The resulting theorem applies to all nonzero raw residue sextuples. It proves the required transport under signs, permutations, congruences, and modular units, retains multiplicity, and reduces the cover to explicit checked support trees and retained-row relation checks. Inverse validity, all root checks, and all retained-row checks remain premises. This checkpoint proves the reduction; the numerical prime covers and full six-speed classification remain incomplete.

### Accepted six-plane family membership bridge

The exact six-plane membership bridge is registered from [run 44563135178, job 135701825634](https://github.com/1337isnot1337/solved-conjectures/actions/runs/44563135178/job/135701825634), candidate `3273ac1a24ea061b0cbd73244e2ac57c08d491ec`. The fresh 66-module gate checked 1,795 owned and raw declarations, 1,449 theorems, 49 private declarations, all five endpoints, and 66 separate stock-kernel targets. Authenticated original evidence is preserved unchanged in [verification/six-plane-families-exact-44563135178](verification/six-plane-families-exact-44563135178/).

`Loneliness.SixPlane.literal_parameters_of_mem_critical_plane` turns actual positive integer membership in a classified plane into the two literal product families with both positive integer parameters or the full signed real third family. `primitive_family_of_mem_critical_plane` derives the two `6s` product families under primitivity and actual value below `1/6`. `not_mem_critical_plane_of_not_literal_families` gives the exact off-critical condition required by the norm proof. The acceptance adds only `LonelinessSixPlaneFamilies` and its five named endpoints. The classification of low-value planes, complete finite pair coverage, five-speed exhaustion, and third-family evaluation retain their own proof obligations. No result-level completion status changes.

## Complete tight-five threshold classification (19 November 2026)

Lean now proves that every positive primitive five-speed tuple with loneliness
at most `1/6` is a permutation of `[1,2,3,4,5]` or `[1,3,4,5,9]`, and its value
is exactly `1/6`. The complete gcd-normalized statement covers all positive
lists of length five. The same proof supplies an unconditional five-speed
lower bound, independently of the previously registered Renault proof.

The complete 250-source closure passed fresh strict compilation, all 7,586
named theorem obligations, four literal statements, the raw/private axiom
audit, and exact stock kernel replay. All 7,070 finite frames reproduce from
the published generators. No lower-runner or prime-classification premise
remains. See the [original passing run and authenticated evidence](verification/loneliness-five-runner-exact-44549751944/README.md).

This completes the tight-five classification at `1/6`. The separate
five-speed spectrum theorem classifies all values below `1/5` and retains
its remaining finite-exhaustion obligations. Its result-level status is unchanged.

## Modular support, unit orbits and literal binary lifts, 19 November 2026

Four authenticated component closures are now registered: support multiplicities
and the finite-tree consumer (98 modules, 63 required endpoints), unit-orbit
transport (26/8), literal seven-speed binary roots (34/58), and byte-count/check
equality (8/15). Their exact source, all-owned/private audit and stock-kernel
receipts are linked in the [component scope record](verification/modular-support-components-20261119.md).
The registration includes all 55 generated multiplicity source files from the
passing artifact and preserves every earlier accepted registry entry.

The seven-speed literal check retains the six-speed runner bound and does not
prove initial-support exhaustiveness. The multiplicity and orbit interfaces
retain their terminal and covering hypotheses. The byte evaluator has a
universal equality proof; its interrupted benchmark supplies no speedup result.
The separate prime-251 closed-lift gate and bounded initial-cut pilot have
passed their exact component gates; their limited scopes are recorded below. The merged accepted package
still requires its separate complete source, audit and stock-replay run.

## Order-nine automorphism subgroups and orbits

The existing `HadamardLegendreOrderNineGroup` and
`HadamardLegendreOrderNineOrbits` modules are registered from the exact passing
hosted run 44523474204. They prove that a nontrivial odd automorphism subgroup
on an abelian group of order nine has order three, three fixed points, and
exactly five orbits. The two nonsingleton orbits are the nonzero cosets of the
fixed subgroup.

The four-source closure is byte-identical to its original strict-source,
axiom-audit, and stock-kernel checkpoint. A fresh local strict-source check
and complete audit additionally cover all 68 owned and raw declarations,
including nine private declarations and all 13 required endpoints. The local
repeat stock replay timed out; the original hosted kernel pass is the
preserved passing evidence. [Scope, exact receipts, and both outcomes](verification/hadamard-order-nine-orbits-44523474204/README.md).

This registers two auxiliary modules. The length-1197 order-27 exclusion and
the finite quotient/no-lift packet remain outstanding.

## Initial cut pilot and prime-251 binary lifts, 19 November 2026

Two further component gates passed from source
`8abe17f1b329ca1df0ae81f4e0b2c4425d1b03a6` and are registered with their exact
checked sources. The [scope and preserved evidence](verification/modular-cut-and-closed-lift-components-20261119.md)
record the source, all-owned/private declaration audit, and stock-kernel checks.

The cut pilot passed its complete 53-module closure and 54 required endpoints
in [run 44577155795](https://github.com/1337isnot1337/solved-conjectures/actions/runs/44577155795).
It proves the complete small initial list for five speeds, denominator six and
prime eleven, plus the validity of all 19 prime-251 rows and only cuts 0 through
3 of the minimum-pair-four root. Exactly 30 generated sources were compiled,
audited, replayed and added. The other 105 generated sources remain outside
this accepted scope. Prime-251 initial-support coverage is still incomplete.

The closed binary-lift component passed 33 modules and 23 required endpoints
in [run 44577160577](https://github.com/1337isnot1337/solved-conjectures/actions/runs/44577160577).
It checks all 19 ordered prime-251 roots, 2,451 states and 19 complete
128-child binary branches, to maximum depth two. Its classification theorem
retains the six-speed runner bound and the premise that the tuple is
represented by one of those roots. It does not establish initial-support
coverage or the full seven-speed classification.

Registration preserves all earlier entries and adds four imports, 68 audit
names and 33 explicit prebuild/replay modules. No result-directory completion
status changes. A complete merged-package source, audit and kernel replay
remains a separate verification obligation.

## Rational integer-point lattices and six-speed norm components

The registered components construct the full integer-point lattice of
every rational coordinate subspace, prove its span and rank, and identify its
squared covolume with the Gram determinant of an actual integer lattice basis.
They prove squared covolume at least one. In rank four in six coordinates,
the lower bound is six when the subspace contains an integer vector whose
coordinates are nonzero and pairwise unequal up to sign.

Suppose an integer matrix has r columns lying in a rational subspace of
dimension r, and its Gram determinant is positive. The proof gives an
exact factorization of the column Gram determinant as a nonzero integer
square times the full lattice's squared covolume. It therefore bounds the
full lattice's squared covolume by the column Gram determinant. The endpoints do not
identify that integer with the cardinality of a finite quotient.

The rectangular components also prove integer-parameter recovery under an
integer left inverse, primitive basis transfer, Cauchy--Binet and integer Gram
identities, and the literal map Gram determinants 3, 9 and 8. The six-by-four
Gram lower bound assumes positive Gram determinant, nonzero rows and rows
that are pairwise unequal up to sign; it derives the bound six internally.

The original norm constants 9075, 54450 and 163350 now use the covolume of the
actual full integer-point lattice. The 9075 theorem assumes rank four,
containment of the speed vector, and distinct positive primitive speeds.
The 54450 and 163350 theorems hold for every rational coordinate subspace,
without a rank or containment premise. All three norm theorems retain
`hfour : CoordinateSubspace.LonelyRunnerBound 4` and `hplane`, the containing-plane gap
hypothesis, as well as positivity, primitivity and loneliness at most `1/6`.
These are component theorems. The unconditional plane-gap deduction and the
remaining exhaustive classification are not supplied here; the six-speed
spectrum result remains partially formalized.

The complete 60-module hosted gate passed at `e815f14555472b873683f491bc878eb16d4eb0a4` ([run and job](https://github.com/1337isnot1337/solved-conjectures/actions/runs/44590263136/job/135794055426)). It checked all fresh strict sources, all owned and private declarations, all 50 required theorem endpoints, and one exact stock-kernel target per module. The permitted axioms were only `propext`, `Classical.choice`, and `Quot.sound`. The unchanged receipt has SHA-256 `4a3f6a5df8723dc21f2b5eb2899a10ea55b47b9eb0538cd48927016c0195e4ee`. The merged accepted-package check remains a separate obligation.

[Preserved receipt](verification/rectangular-lattice-exact-44590263136/receipt.json).

## Prime filtering and proved runner classes, 19 November 2026

Twelve prime-filtering modules are registered. They formalize Lemma 2 and
Corollary 3 of Barajas and Serra, *The lonely runner with seven runners*
(Electronic Journal of Combinatorics 15 (2008), R48, DOI 10.37236/772).
The proofs produce an actual prime-power unit, preserve higher residues
when starting from a coprime seed, and derive modular witnesses and bounds
for the real-valued loneliness function.

For positive speeds, the verified `1/7` consequence assumes that every
7-adic valuation level below the maximum contains at most three distinct
speeds. The highest level has no cardinality restriction. Repeated speeds
are allowed. A separate uniform-valuation theorem gives the `1/p` bound
for any base `p ≥ 2`, with no restriction on the number of speeds.
The four- and five-input exceptional lower levels, and the unrestricted
six-speed runner theorem, remain pending.

[Run 44591941338](https://github.com/1337isnot1337/solved-conjectures/actions/runs/44591941338)
at `e6d53ced9fd3b6ad4a311c3eecbe1fcbd0cdd491` passed the complete
18-module closure: fresh strict sources, 68 required theorem endpoints,
33 literal quantified contracts, the full audit of 299 owned declarations
(243 theorems and 10 private declarations), and 18 exact singleton stock-kernel
replays. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
All 116 original artifact members and every source, object, process record,
audit inventory and pinned control hash were authenticated. The receipt
SHA-256 is `009a768a638e275c6705f1bc08c316ca3686553bd591c2c25765fc29531ed394`.

[Original evidence and exact scope](verification/prime-filtering-exact-44591941338/README.md).
Every previous accepted entry is preserved. Li remains outside the accepted
roots. The complete merged-package gate remains a separate obligation;
no result-directory completion status changes.

## Conditional two-parameter radius estimate

For an integer matrix with two columns and a finite nonempty row set, the theorem uses the actual real column span and the actual line generated by a primitive signed integer parameter pair. The primitive premise is `Int.gcd x y = 1` on the parameters. For any real upper bound `C` on every squared row norm, `plane_value_le` bounds the plane value by the line value plus `1/2 * sqrt(C / (x^2+y^2))`.

If the actual plane value is at least `2/11` and the actual line value is strictly below `1/6`, the proof gives `x^2+y^2 < 1089*C`. Taking the exact finite maximum of the squared row norms gives the natural-number bound `x.natAbs^2 + y.natAbs^2 < 1089 * maxRowSq A`. An explicit coordinate-equality theorem carries this bound to a natural six-speed vector. It does not separately require the natural speed vector to be positive, distinct or primitive, and adds no rank, integer-left-inverse, four-speed or six-speed-classification premise.

The plane gap remains an assumption. This theorem does not classify the 78 maps or complete the six-speed spectrum.

The complete 13-module hosted gate passed at `6932e0ba9c532f86fbf9e5fb23aff9e55b8e99f9` ([run and job](https://github.com/1337isnot1337/solved-conjectures/actions/runs/44593469748/job/135805428239)). It checked all fresh strict sources, all 295 owned declarations including 13 private declarations, all 6 required theorem endpoints, and one exact stock-kernel target per module. The permitted axioms were only `propext`, `Classical.choice`, and `Quot.sound`. The unchanged raw receipt has SHA-256 `b4722be2222c18d959a57252b8bc797e71a489c41d6c3c0b92647fadaf663de7`. A merged accepted-package source, audit and kernel pass remains a separate obligation.

[Preserved receipt](verification/two-parameter-radius-exact-44593469748/receipt.json).

## Six-speed norm bounds with the four-speed input discharged

The three new six-speed lattice norm bounds supply the proved four-speed runner theorem internally. They retain the containing-plane gap, positivity and primitivity of the natural speed vector, and loneliness at most `1/6`. The bound with constant 9075 additionally assumes a rational subspace of rank four containing the speed vector and pairwise distinct speeds. The bounds with constants 54450 and 163350 apply to every rational coordinate subspace, without a rank, containment or distinctness premise. The lattice is the actual full integer-point lattice.

The new endpoints end in `_of_plane_gap`. They remove the explicit `hfour` input and retain `hplane : SixSpectrumNormGeometry.ContainingPlaneGap v`. The old endpoints keep their original signatures. These results do not prove the containing-plane gap or complete the six-speed classification.

The complete 113-module hosted gate passed at `14f3403c7afe204c85b376df0f02c68c86c7fea0` ([run and job](https://github.com/1337isnot1337/solved-conjectures/actions/runs/44591091795/job/135796982020)). It checked all fresh strict sources, all 3108 owned declarations including 90 private declarations, all 3 required theorem endpoints, and one exact stock-kernel target per module. The permitted axioms were only `propext`, `Classical.choice`, and `Quot.sound`. The unchanged raw receipt has SHA-256 `af61227a92a04443c42d8c928139f13a9bb201b3bfd5b359f464138f2d3ae5ac`. A merged accepted-package source, audit and kernel pass remains a separate obligation.

[Preserved receipt](verification/lattice-norm-four-speed-exact-44591091795/receipt.json).

## Seven-coordinate implications with the five-speed input discharged

The new seven-coordinate critical-plane and large-norm statements supply Renault's proved five-speed runner theorem internally. Every new endpoint retains `hsix : PrimitiveSixClassification`. The plane results concern rational subspaces of dimension two. One classifies coordinate-free planes with value at most `1/7`; another assumes equality to `1/7` without a separate coordinate-free premise; the third states that equality is equivalent to `StandardProductPlane`.

The quantitative results concern positive primitive natural speed vectors with Euclidean norm at least `7 * 42^10`. Below loneliness `1/7`, such a vector is a permutation of `[1,2,3,4,5,6,7*s]` for an integer `s >= 1`, and its loneliness is `s/(7*s+1)`. The family equivalence puts the strict loneliness inequality on the left side of its equivalence. No separate distinctness premise is added. The six-speed classification remains an assumption; these implications do not establish the full seven-speed classification.

The complete 171-module hosted gate passed at `9c5b1203a4405508254332b1d13dd19f9bdefe38` ([run and job](https://github.com/1337isnot1337/solved-conjectures/actions/runs/44592471446/job/135801829445)). It checked all fresh strict sources, all 4246 owned declarations including 850 private declarations, all 6 required theorem endpoints, and one exact stock-kernel target per module. The permitted axioms were only `propext`, `Classical.choice`, and `Quot.sound`. The unchanged raw receipt has SHA-256 `25d85fa1a9a5fa514e1a1505d370790f273656bafa3a9c4b991316ba9f043b5e`. A merged accepted-package source, audit and kernel pass remains a separate obligation.

[Preserved receipt](verification/critical-seven-five-speed-exact-44592471446/receipt.json).

## Four-input prime filtering, 19 November 2026

Twenty modules are registered for the four-input filtering step in the
seven-runner argument. For four natural inputs nonzero modulo seven and
any exponent `m`, the theorem gives `1 <= j <= 5` and `0 <= k <= 6` such
that `j + k*7^m` is coprime to `7^(m+1)` and each actual folded residue
is at least `7^m`. Every input divisible by seven keeps its full residue
relative to multiplication by `j`. Repeated inputs are allowed.

The finite quotient sampling, symmetry reduction, ten canonical decision
checks and natural arithmetic transport are all proved. No finite-check
hypothesis remains. The higher-family seed must still be safe under the
selected multiplier `j`; this component does not supply that seed or prove
the unrestricted six-speed runner theorem. The five-input lower-level
case also remains outside this component.

[Run 44601096014](https://github.com/1337isnot1337/solved-conjectures/actions/runs/44601096014)
at `8d1933b7b568515fe5bf7e8b474fe22e284521e8` passed 20 fresh strict
source checks, four literal contracts, all seven required endpoints,
the complete owned and raw-occurrence audit, and 20 exact singleton
stock-kernel replays. The audit covers 133 declarations and 97 theorems.
Its closed raw dependency graph has 5,101 nodes and 70,060 edges, with
only `propext`, `Classical.choice`, and `Quot.sound`. All 128 original
artifact members and exact source, object, import, control, log and profile
bindings were independently authenticated.

[Original evidence and exact scope](verification/prime-filtering-four-exact-44601096014/README.md).
All prior accepted entries, verification code and the axiom whitelist are
preserved. No result-directory completion status changes. The full merged
accepted-package gate remains a separate obligation.


## Li coefficient-sign counterexample

The 44-module development is registered with 71 required theorem
endpoints. The original hosted gate passed at source snapshot
`20e0e95eb421cf8ea728d34aa29a6d0eb1137789`: all 44 fresh strict sources,
25 literal contracts, 1,247 owned declaration names (932 theorems and
95 private names), all 71 required endpoints, and 44 exact stock-kernel
targets. The separate hosted supplement passed against the same object
bytes and covers every reachable serialized proof occurrence. Both
original artifacts and the complete baseline backup were authenticated
and independently reviewed before this registration.
The original 38-module contribution is by [aadrianvv](https://github.com/aadrianvv)
in [PR #35](https://github.com/1337isnot1337/solved-conjectures/pull/35),
original head `fb700255fed86b6ac29b4980ff4704fa46adab63`.

The explicit tree has 31 vertices, maximum degree 4, one degree-4 vertex with
exactly one leaf neighbour, and is neither a spider nor a caterpillar. Every
one of the 6,842 integer partition types is realized by genuine nonempty,
disjoint, covering connected vertex blocks. Exactly eight connected
partitions have type `(3,2^14)`. An equivalence with deleted-edge subsets gives
exactly `2^30 = 1,073,741,824` connected vertex partitions in total.

For every finite colour type of cardinality at least 31, the actual
proper-colouring polynomial has full elementary coefficients
`[e₂¹⁴e₃]=29` and `[e₂⁸e₃⁵]=−6304`. The five degree-31 coefficients using only
`e₂,e₃` are `29, 83, −6304, −6800, −8384`. Full-coordinate restriction and
colour-renaming theorems prove stability. No separate infinite-variable
symmetric-function ring is constructed, and 31 is a sufficient degree-bound
threshold without a minimality claim for these coefficients.

The positive coefficient contradicts Li's strict-negative prediction in
Problem 4.9. The leaf count contradicts the first question of Problem 4.6.
The count eight contradicts the separate informal prediction
`b_(3,2^14)=1`; uniqueness of the degree-4 vertex remains true. The negative
coefficient proves that this tree is not elementary-positive.

The original Python dynamic program and the vertex-deletion contribution
argument remain alternative explanations. The formal development proves the
main conclusions independently; it does not certify those Python programs
or every numerical step of the alternative argument. The separate graph-
distance and branching source `LiStructure` is outside this 44-module
acceptance. Its dedicated verification closure also includes `LiBasic`.

[Theorem inventory, scope and attribution](../results/li-coefficient-sign/LEAN.md).
The complete merged accepted-package gate remains separate. Earlier dated
checkpoints retain their historical scope, including their former Li queue
status. The repository-wide campaign remains incomplete.

The original [run 44599210697, job 135825706963](https://github.com/1337isnot1337/solved-conjectures/actions/runs/44599210697/job/135825706963)
produced artifact `14568527194`, ZIP SHA-256
`281b57fd87cf7d6123cdcabff4a5803f3d426116dbb4a9aa01370318b2a138ed`.
The unchanged receipt SHA-256 is
`da585dbd99530825af7bac8c4730c1a6666bfa151ce98ad4c6f52b9d537aa09d`.
All 272 original members, source/object/direct-import bindings, process
logs and profiles, original git controls, and compiler/checker pins have
been authenticated. The artifact authentication SHA-256 is
`cc956d198ed081f35fb7ea35ff22aaf9bbec7b3ce2138519c43db53d778fef29`;
the independent root review SHA-256 is
`9de0d30a11a09d0c54bfdd76358f6ef2e3abdcc07254c314af520bbfbd04361b`.

The [raw-occurrence supplement, run 44606051622 / job 135849912826](https://github.com/1337isnot1337/solved-conjectures/actions/runs/44606051622/job/135849912826)
passed at `26ef845d1ec4adb15e0c87c9264905baeb69491f` against the exact original
44 compiled objects. It rechecked all 25 literal contracts and traversed
17,647 dependency nodes and 316,338 edges from all 1,247 owned declarations.
The scan indexed 22 differing theorem bodies across the imported environment;
none was reachable from those roots, so no extra variant alias checks were
needed. The trust-zero checked-kernel negative control was rejected. The
only transitive axioms were `propext`, `Classical.choice`, and `Quot.sound`.

The raw artifact is `14569498196`, ZIP SHA-256
`7ea288555021d503775aa3886fc59edc65ae9a096ca26bb9add7e9950b1e1489`,
with receipt SHA-256
`8cb7e81896bc67b3c68ed976f256e6894b6c52318063ab0894360fed1d0a8b46`.
The preserved baseline backup is artifact `14569584489`, ZIP SHA-256
`dfbb03a7571256df786f9c28f45b306cb924f89403ba403d81063072e6f1eb2f`;
its inner archive equals the original baseline ZIP byte for byte.
The raw-artifact authentication SHA-256 is
`6abda54c54c591fef864220fd7624374ad25af865a94989204969305eecb0610`;
the independent review SHA-256 is
`8f14f2f5844973ea3d432b741185e01a8385841fc0d8f8b90e7181e88f5d6aee`.
The supplement retains the original source-build and stock-replay evidence;
it does not claim to have repeated those stages.

## Actual rational-lattice quotient index

For a rational coordinate subspace E of dimension r, let L be its actual full integer-point lattice. An integer matrix A with r columns in E and positive Gram determinant generates the sublattice M = columnSubmodule E A. Relative to an actual integer basis of L, the columns have an integer square coordinate matrix C. Lean proves that the quotient cardinality Nat.card (L ⧸ M) equals the absolute determinant of C and is positive. It then proves the exact identity det(AᵀA) = [L:M]² * covolume(L)². The containment, dimension and positive-Gram hypotheses are explicit; no saturation or quotient-index identity is assumed.

This identifies the integer determinant factor in the earlier Gram/covolume comparison with the actual finite lattice quotient. It does not discharge the containing-plane gap or complete the six-speed classification. The six-speed result remains partial.

The complete 20-module hosted gate passed at `a8577e5da31b851ce64333aa921b39c6623e0389` ([run and job](https://github.com/1337isnot1337/solved-conjectures/actions/runs/44606981694/job/135853171450)). It checked all fresh strict sources, selected declaration values and types for 446 owned names including 12 private names, all 5 required theorem endpoints, and one exact stock-kernel target per module. The audit includes raw/private-name visibility; it is not a separate audit of every duplicate theorem body occurrence. The permitted axioms were only `propext`, `Classical.choice`, and `Quot.sound`. The unchanged raw receipt has SHA-256 `62b4ab2b3b0dcdaa55b210e5de3e8322e7e6b57201b05e085983d8ff0882afa2`. A merged accepted-package source, audit and kernel pass remains a separate obligation.

[Preserved receipt](verification/rational-lattice-quotient-exact-44606981694/receipt.json).

## Fang–Zhang–Zhao universal conjecture

This formalizes a previously resolved result. A complete ordinary disproof was public by 26 October 2026; it is excluded from new-resolution credit. See the [priority correction](../research/campaign-20261121/PRIOR_RESOLUTION_CORRECTION.md).

`Conjectures.FangZhangZhao.conjecture_false` checks the source binomial sum and its iterated log-convexity operator using the exact parameter m=6. The stronger all-m≥4 theorem remains unformalized. The module build, standard axiom check, and isolated kernel replay passed; the full repository gate is pending.

## Sun–Zhao iterated ratios

This formalizes a previously resolved result. A complete ordinary disproof was public by 27 October 2026; it is excluded from new-resolution credit. See the [priority correction](../research/campaign-20261121/PRIOR_RESOLUTION_CORRECTION.md).

`Conjectures.SunZhao.conjecture_false` directly computes the source recurrence over the rationals and refutes its even-order clause at k=12, n=12. The module build, standard axiom check, and isolated kernel replay passed; the full repository gate is pending. The prior ordinary proof and the source match are documented in the correction record.

## Zhang deletion values

`ZhangDeletion.question84` proves the strict loneliness inequality for all n≥4, 1≤r≤n−2, using actual real distances and the real-time value. `large_deletion_exact` and `small_deletion_exact` prove the full deletion-value formula for n≥3 and 1≤r≤n−1. The small-deletion upper bound is discharged internally via the pair-sum maximizer and a signed modular certificate, without assuming Liu’s theorem. The seven-module closure passed local kernel replay and the three endpoints use only the allowed axioms; the full repository gate is pending.

## Baricz–Pogány coefficient positivity

`BariczPogany.conjecture` proves strict positivity for every degree n≥2 and every real |ν|<1/2, using the source factorial-product coefficients and the uniquely determined formal quotient. `source_recurrence` derives the source’s coefficient recurrence explicitly. `explicit_lower_bound` proves the stronger stated bound; no analytic convergence is assumed. Strict compilation, the isolated kernel replay and endpoint axiom checks passed. The full repository gate is pending.

## López Pouso–Segura quadrature counterexample

`LopezPousoSegura.both_upper_bounds_fail` checks the exact n=2 counterexample, including the Legendre roots, standard weights, cubic integral exactness, and the pi/square-root comparison. The eventual-even-degree strengthening remains unformalized. Strict compilation, isolated kernel replay, and endpoint axiom checks passed; the full repository gate is pending.

## Dospolova–Germanskov–Zaporozhets factorial family

`DospolovaGermanskovZaporozhets` checks all factorial-sequence equalities and strict expected range for an actual Gaussian process, with almost-sure boundedness, nondegenerate increment and deterministic local-range limits explicit. Intrinsic volumes, determinism of those limits, and Vitale’s limit remain unformalized. Strict source compilation, isolated kernel replay and endpoint axiom checks passed; the full repository gate is pending.

## Gilmore crossing–nesting matrix and paths

`GilmoreCrossingNesting.original_conjecture` proves the original crossing–nesting identity, and `gilmore_conjecture` includes alignment and size parameters, over any commutative ring. The finite block product is identified with paths, which are in bijection with literal perfect matchings; the crossing, nesting and alignment inequalities are checked and the weighted sum is transferred across the bijection. Strict compilation, isolated stock-kernel replay and endpoint axiom checks passed; the combined gate is pending.

## Chen–Khare–Sahi semiring separator

`ChenKhareSahi.generatorValues_exact` checks all 38 listed rational separator values and `separation_negative` checks the negative value at the displayed normalized polynomials. The listed product inequalities and negative value are also transferred to the real separator; `P420_eigen` and `P411_eigen` check the cleared rational eigenoperator identities. `dominance_decomposes` proves that every majorization difference through degree six telescopes into the explicitly enumerated covers. `product_decomposition` checks that every product of normalized monomials of total degree at most six is a nonnegative combination of normalized monomials. `ReducedCone.separator_nonnegative` checks every nonnegative combination of the reduced cover products, and `reduced_cone_excludes_counterexample` excludes the displayed difference from that cone. `HomSemiring.degree_six_reduces` proves every degree-six expression made from source generators using same-degree addition, multiplication and nonnegative real scaling belongs to that cone. `monicEigen420_unique` and `monicEigen411_unique` establish the unique real monic eigenfunctions with precisely the source dominance-triangular support; the particular polynomials are therefore characterized directly, without a general Macdonald-polynomial library. `FullSemiring.homogeneous_component` extracts degree six from arbitrary mixed-degree semiring expressions by polynomial coefficient uniqueness. `conjecture_counterexample` combines this with the unique monic triangular eigenfunction characterizations to refute the semiring implication under the standard monic triangular eigenfunction interpretation at the stated parameters. Rectangular translation identities for the generators and eigenoperator are checked for every shift. `FullSemiring.leading_factor` factors every nonzero semiring expression into a power of xyz times a semiring expression strictly positive at (2,1,0). `FullSemiring.saturated` proves cancellation of every such power, and `shifted_counterexamples` proves nonmembership for all explicit shifted polynomial pairs, which also satisfy the shifted eigenoperator equations. The Hall–Littlewood symmetrization and strict nonmembership for 3/4≤t<1 are verified. Explicit parameter-dependent eigenfunctions are proved continuous at q=0, uniquely satisfy the full source monic triangular eigenfunction characterization, and yield the stated nonmembership family at sufficiently small positive q. `shifted_support420` and `shifted_support411` prove the full dominance supports are exactly the shifted base supports; `shiftedEigen420_unique` and `shiftedEigen411_unique` identify the unique monic source eigenfunctions for every shift. `shifted_source_counterexamples` proves the complete rectangular-translate family. The isolated replay passed; the combined repository gate remains pending.

## López Pouso–Segura central-node perturbation

`perturb1_hasDeriv`, `perturb2_hasDeriv`, their second-derivative companions and `perturb2_ode` verify the explicit perturbation functions and ODE coefficients. `asymptotic_product_algebra` and `asymptotic_normalized_coefficients` verify the final fourth-order coefficient. `eventual_violation_of_three_approximations` derives eventual failure from the three displayed factor approximations with vanishing second-order remainders, including the intermediate amplitude-product reduction. Controlled parameter-dependent ODE and root expansions, the gamma-ratio expansion and those factor approximations remain unformalized.

## López Pouso–Segura Bessel-weight convexity

`Conjectures.LopezPousoSeguraBesselConvex`, `Conjectures.LopezPousoSeguraBesselMidpoint` and `Conjectures.LopezPousoSeguraBesselAverage` prove strict trapezoid and midpoint inequalities, the weighted-average identity, and the signs and strict monotonicity of all three source sequences under explicit convexity, antiderivative, positive-weight and endpoint hypotheses. `Conjectures.LopezPousoSeguraBesselLimit` transfers the first sequence’s limit to the third for divergent positive weights, while `Conjectures.LopezPousoSeguraBesselGap` derives the second limit from the first and stated zero/weight asymptotics. `Conjectures.LopezPousoSeguraBesselConstant` derives all three limit constants from the source asymptotics and the explicit deviation-sum identity. `Conjectures.LopezPousoSeguraBesselDiverge` derives divergence of the weight sums from those assumptions. `Conjectures.LopezPousoSeguraBesselMixture` proves strict convexity for a nonzero positive mixture of the rational kernels, under explicit integrability hypotheses. `Conjectures.LopezPousoSeguraBesselODE` transfers strict convexity of the squared phase function to its inverse-phase derivative on the positive axis under explicit ODE and positivity hypotheses. `Conjectures.LopezPousoSeguraBesselEndpoint` extends this through zero under endpoint continuity and connects the mixture and ODE hypotheses to all three sign statements. `Conjectures.LopezPousoSeguraBesselFinite` derives the kernel integrability hypotheses for any finite positive measure and applies the result to all three sign statements. `Conjectures.LopezPousoSeguraBesselTannery` proves the deviation-resolvent dominated-convergence step, and `Conjectures.LopezPousoSeguraBesselResolve` checks the resolvent remainder estimate and constant extraction under their stated hypotheses. `Conjectures.LopezPousoSeguraBesselScaled` restores the original scaled resolvent, and `Conjectures.LopezPousoSeguraBesselSummable` derives absolute summability from the cubic error bound. `Conjectures.LopezPousoSeguraBesselDenominator` proves the denominator correction tends to zero under a concrete summable majorant; `Conjectures.LopezPousoSeguraBesselMajorant` derives that majorant from linear weight growth, inverse-square root error and quadratic lower bounds. `Conjectures.LopezPousoSeguraBesselDecomp` combines the deviation and denominator limits, and `Conjectures.LopezPousoSeguraBesselSeries` proves the two required series converge from the growth bounds. `Conjectures.LopezPousoSeguraBesselBridge` combines these estimates and reduces the deviation constant to the main resolvent identity and the reference expansion. `Conjectures.LopezPousoSeguraBesselGrowth` derives the comparison growth bounds from the reference terms and combines the two resolvent expansions into all three exact limits. `Conjectures.LopezPousoSeguraBesselConditional` combines the signs, monotonicity and exact limits into one theorem with all analytic inputs explicit. `Conjectures.LopezPousoSeguraBesselReference` proves the reference kernel integral, its first derivative at zero, and the Bernoulli coefficient. The Bessel identification, endpoint continuity, special-function asymptotics, main resolvent identity and reference Euler–Maclaurin expansion remain to be formalized; repository-wide verification is pending.

## Johnson four-node Pfaffian bound

`Conjectures.JohnsonPfaffianFour` proves the log-convex four-point inequality and the bound for all three matchings on four ordered nodes, using the explicit four-by-four Pfaffian formula. `Conjectures.JohnsonPfaffianUncross` proves that uncrossing improves the matching product and decreases total edge span for any four ordered vertices. `Conjectures.JohnsonPfaffianIntervals` proves the source interval twin-vertex pigeonhole lemma; `Conjectures.JohnsonPfaffianSummation` proves the summation-by-parts deduction of the endpoint inequality from nonnegative prefix sums. `Conjectures.JohnsonPfaffianTelescoping` and `Conjectures.JohnsonPfaffianSource` prove the all-order source kernel factorization with nonnegative interval coefficients. `Conjectures.JohnsonPfaffianProduct` proves product expansion into interval intersections and complement scaling; `Conjectures.JohnsonPfaffianMatching` defines the signed matching-sum Pfaffian and proves diagonal scaling, and `Conjectures.JohnsonPfaffianSmall` connects it to the verified four-node case. `Conjectures.JohnsonPfaffianRotation` constructs a bijection on canonical matchings, proves crossing-count invariance, and derives cyclic invariance of the matching-sum Pfaffian. `Conjectures.JohnsonPfaffianSwap` constructs the adjacent-vertex involution and proves it has no fixed point when the adjacent edge is absent. `Conjectures.JohnsonPfaffianParity` proves crossing-parity reversal and cancellation of the actual signed matching sum off the adjacent edge for twin rows over any commutative ring. `Conjectures.JohnsonPfaffianResidual` characterizes residual matchings and proves the order-preserving relabeling to the smaller standard vertex set, giving the full twin-row Pfaffian deletion identity. `Conjectures.JohnsonPfaffianSparse` proves the source sparse-support zero-or-twin reduction for interval matrices over any commutative ring, and verifies that restriction to the remaining ordered vertices preserves interval supports and their weights. `Conjectures.JohnsonPfaffianRestriction` groups restricted interval coefficients and proves the full sparse-support reduction to a smaller interval matrix. `Conjectures.JohnsonPfaffianCoefficients` proves the source coefficientwise nonnegativity and homogeneity of the interval Pfaffian in every even order. `Conjectures.JohnsonPfaffianPositive` specializes the result to nonnegative real interval coefficients and proves nonnegativity of the actual Pfaffian matching sum. `Conjectures.JohnsonPfaffianPrefix` proves nonnegativity of each bordered prefix matching sum by differentiating the coefficient-positive interval Pfaffian. `Conjectures.JohnsonPfaffianExpansion` proves the first-row expansion and the endpoint bound expressed through the last prefix difference. `Conjectures.JohnsonPfaffianEndpoint` and `Conjectures.JohnsonPfaffianOuter` regroup interior coefficients and identify that difference with the smaller principal Pfaffian, establishing the source endpoint inequality for every positive even order. The all-order matching induction and repository-wide verification remain open.

## Ferreira–Simon Wright log-concavity disproof

`Conjectures.FerreiraSimonWright` proves a continuous family of counterexamples
to the original conjecture using beta zero and alpha approaching one from
below. The source-defined infinite Wright series, its Gamma normalization,
the uniform coefficient bound, and the limiting midpoint violation are all
inside the formal proof. The four registered endpoints are
`scaled_wright_limit`, `boundary_counterexamples`,
`exists_boundary_counterexample`, and `boundary_conjecture_false` in namespace
`FerreiraSimonWright`.

Strict compilation with warnings treated as errors, the existing modern
owned-extension audit of every declaration including private declarations,
and stock-kernel replay of the complete local import closure passed. This
module has no other project-module dependencies, so its owned inventory is
also its entire project closure. The
[validation receipt](verification/lean-wright-20261121/wright-receipt.json)
records 25 declarations, 22 theorems, eight private declarations, and the
standard three-axiom whitelist. The root result is a full disproof of the
universal source conjecture; the additional positive-beta and all-slope
families remain unformalized. The combined repository gate remains pending.


## Fan–Tringali’s power-monoid length-set conjecture

Complete Lean verification of the original 2018 conjecture: every finite nonempty set of integers at least two is realized as the entire atom-length set in both the ordinary and restricted finitary power monoids of every Dedekind-finite monoid with infinitely many distinct positive powers. No ambient commutativity or cancellation is assumed. [`finite_spectrum_power_monoids`](../lean/Conjectures/FanTringaliMonoid.lean) proves the full transfer, and [`natural_length_system`](../lean/Conjectures/FanTringaliNaturalSystem.lean) proves the exact reduced-natural-number system.

All 18 frozen modules passed strict source builds, the all-owned/private axiom audit (432 declarations, 350 theorems, three private declarations, 28 required endpoints), and stock kernel replay. [Scope and reproduction](../results/fan-tringali-power-monoid-lengths/LEAN.md), [statement review](../results/fan-tringali-power-monoid-lengths/LEAN_REVIEW.md), and [complete receipt](verification/lean-fan-tringali-complete-20261124-162051/receipt.json). The separate survey irreducible formulation, prescribed multiplicities and relative cancellativity remain unformalized. The scoped pass does not claim an aggregate repository pass or a current public deployment; those gates are reported separately, including the dependency-cache blocker in [#563](https://github.com/1337isnot1337/solved-conjectures/issues/563). This is one completed existing entry.


## Ulas’s disjoint-block square-product conjecture

Partial Lean verification: for every positive block length, a positive repeatable count exists and every positive multiple of it has infinitely many disjoint square-product collections. The [source-matched finite-collection development](../lean/Conjectures/UlasDisjointSquareBlocks.lean) also reduces eventual infinitude at every sufficiently large count to prime-avoiding tail collections. The analytic/probabilistic parity input and odd-prime binary-code argument remain explicit obligations, as recorded in the [scope report](../results/ulas-disjoint-square-blocks/FORMALIZATION.md). All six modules passed fresh strict builds, the all-owned axiom audit and exact stock-kernel replay; see the [receipt](verification/lean-ulas-20261124-162051/verification.json). This entry is not counted as completely formalized.



## Gravgaard–Lee’s mixed upper/lower Lüroth conjecture

Partial Lean verification: exact genuine-series endpoint bounds and upper sum inclusion, all linked one-step interval refinements, and actual bounded-digit cylinder containment/compactness are checked. The [scope report](../results/gravgaard-lee-upper-lower-luroth/FORMALIZATION.md) identifies the remaining nonzero-tail repair, reverse inclusion and modulo-one conclusion. The [five-module closure receipt](verification/lean-gravgaard-lee-upper-lower-20261124-162051/receipt.json) records strict builds, the all-owned/private axiom audit and stock kernel replay. This does not repeat or recount the separate already verified mixed-(3,4) or large-digit conjectures.
