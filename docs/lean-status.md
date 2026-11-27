# Lean verification status

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

## Dukes’s revstack interlacing conjecture

Lean proves the source Eulerian formula for the actual revstack descent polynomial at every order at least three. Tracking the two parity classes through one maximum split gives the complete characterization of the unsorted words. The proof also turns the derivative inequality into strict interlacing of the literal descent polynomials and checks the transition from order three to four. The later finite transitions and the uniform derivative bound remain open in Lean. [Lean theorem](../lean/Conjectures/DukesRevstackFiniteStart.lean) · [Scoped receipt](verification/lean-dukes-revstack-enumeration-20261125/receipt.json)

## Braun–Bruegge’s bicyclic facet conjectures

[Lean wedge theorem](../lean/Conjectures/BraunBrueggeBicyclicWedge.lean). Gluing two connected graphs at one vertex multiplies the actual facet counts of their symmetric edge polytopes. The proof gives restriction and gluing maps on normalized polar vertices, with connectedness characterized on each factor's tight graph. The [scoped receipt](verification/lean-braun-bruegge-bicyclic-wedge-20261124/receipt.json) verifies six strict sources, 113 owned declarations and four endpoints, with stock-kernel replay.

For cycles of order at least three, the [cycle count](../lean/Conjectures/BraunBrueggeBicyclicCycleCount.lean) gives the exact even-order central binomial coefficient and the odd-order product of the order and the next smaller central binomial coefficient. The proof identifies actual polar vertices with cyclic integer steps of zero sum and at most one slack edge. The [cycle receipt](verification/lean-braun-bruegge-bicyclic-cycle-current-20261124/receipt.json) covers nine strict sources, 192 owned declarations, eight endpoints and pinned kernel replay.

The [theta count](../lean/Conjectures/BraunBrueggeBicyclicThetaCount.lean) proves the exact same-parity and mixed-parity formulas for the geometric facets of the three-path theta graph. It constructs the literal graph with shared endpoints, identifies its polar vertices with three integer step words, and counts each common-total fiber by its full paths and single slack positions. The [theta receipt](verification/lean-braun-bruegge-bicyclic-theta-20261124/receipt.json) checks 12 strict sources, 346 owned declarations and 10 required endpoints, with pinned kernel replay.

The [large-length mixed-parity comparison](../lean/Conjectures/BraunBrueggeBicyclicMixedLarge.lean) proves a strict geometric facet bound against the balanced odd-cycle wedge benchmark for every total length at least 144. It uses the Wallis product for the central sign-mass bounds and verifies all four cases of the comparison. The [receipt](verification/lean-braun-bruegge-bicyclic-mixed-large-20261124/receipt.json) records 21 strict sources, 623 owned declarations, 11 required endpoints and pinned kernel replay. The full comparison below includes the finite base.

The [full theta comparison](../lean/Conjectures/BraunBrueggeBicyclicThetaReindex.lean) bounds the actual facet count for every admissible simple three-path theta graph by the balanced odd-cycle wedge benchmark for its order. Lean checks the exact finite recurrence against the binomial formula and reduces all mixed-parity rows at total lengths 5 through 143 in the kernel. The [attainment module](../lean/Conjectures/BraunBrueggeBicyclicWedgeAttainment.lean) constructs graphs attaining the benchmark at every order at least four, including the order-four diamond with 12 facets. The [scoped receipt](verification/lean-braun-bruegge-bicyclic-theta-bound-20261124/receipt.json) covers 57 strict modules, 1,478 owned declarations and 13 required endpoints, with pinned kernel replay.

The [bridge factorization](../lean/Conjectures/BraunBrueggeBicyclicBridgePolar.lean) counts the polar vertices of a graph split at a bridge. The [unicyclic formula](../lean/Conjectures/BraunBrueggeBicyclicUnicyclic.lean) gives the exact cycle count times one factor of two per bridge, with an analogous independent sign count for trees. The [cycle comparison](../lean/Conjectures/BraunBrueggeBicyclicCycleProducts.lean) bounds products of two cycle counts with any number of bridges by the balanced odd-cycle benchmark. The [scoped receipt](verification/lean-braun-bruegge-bicyclic-unicyclic-20261124/receipt.json) covers 35 strict modules, 847 owned declarations and 13 required endpoints, with pinned kernel replay.

Lean proves the sharp facet maximum for every finite connected simple bicyclic graph and constructs an attaining graph at every order at least four. A bridge gives an exact product of normalized polar counts. A core without bridges contains a cycle and an ear, and equality of cycle ranks makes the closed-ear wedge or open-ear theta embedding an isomorphism. The [scoped receipt](verification/lean-braun-bruegge-bicyclic-maximum-20261125/receipt.json) covers 73 strict sources, 1,846 owned declarations and 12 required endpoints, with pinned kernel replay. The [theta optimizer](../lean/Conjectures/BraunBrueggeThetaOptimizer.lean) now gives the exact maximum and all equality cases up to path permutation for every order at least ten. [Joint receipt](verification/lean-braun-bruegge-bicyclic-facets-20261126/receipt.json). [Lean theorem](../lean/Conjectures/BraunBrueggeBicyclicMaximum.lean)

## Braun–Bruegge’s minimum facet conjecture

Lean proves both global minimum clauses of Conjecture 2 for the actual facets of the symmetric edge polytope. It establishes the exact even and odd formulas and the equality criterion up to graph isomorphism. The scoped gate passed for 19 modules, all 433 owned declarations and 30 required endpoints, followed by pinned kernel replay. The matching-number refinement remains a written supplement. [Lean theorem](../lean/Conjectures/BraunBrueggeMinimum.lean) · [Verification receipt](verification/lean-braun-bruegge-complete-20261124/receipt.json)

## Ma–Tang’s random subset-sum threshold conjecture

[Incomplete lower-bound checkpoint](../research/ma-tang-lean-core/README.md): twenty Init-only modules establish the exact uniform kernel law, iid coverage bound, birthday conditioning, actual subset-sum coverage and uniform unordered subset probability. The endpoints `uniform_subset_coverage_scaled` and `uniform_subset_below_half` prove covering fraction at most 1/(4*2^r) and strictly below one half on the explicit mixed-group dimension sequence for every r≥4. Strict Lean 4.35.0 builds, transitive axiom checks of all 449 source-named declarations, and stock kernel replay passed ([log](../research/ma-tang-lean-core/verification/uniform-reproduction.log)). Threshold monotonicity, limiting real-log statement, universal upper bound, environment-wide audit and aggregate gate remain unverified. Count zero; uncompiled Mathlib alternatives remain in [draft #583](https://github.com/1337isnot1337/solved-conjectures/pull/583).

## Mazák–Zrubák conjecture on complete graphs minus an edge

The actual real circular coloring reduction and Hall construction of a spanning order of every actual edge are checked in sixteen modules (ten new, six reused). Strict builds, the complete audit of 526 declarations (417 theorems, zero private declarations, twelve required endpoints), and exact stock-kernel replay passed. Only `propext`, `Classical.choice`, and `Quot.sound` occur. Steps 4–8 and the final index equality remain outside this checkpoint; the result is incomplete and its complete-result count is zero. [Scope](../results/circular-index-complete-minus-edge/FORMALIZATION.md), [independent review](../results/circular-index-complete-minus-edge/LEAN_REVIEW.md), and [receipt](verification/lean-circular-complete-minus-edge-partial-20261124-162051/receipt.json).

## Ferroni–Higashitani’s first-three interior Ehrhart question

Lean proves the [literal inequality in Question 5.12(a)](../lean/Conjectures/FerroniHigashitaniEhrhart.lean)
for the dimension-170 IDP lattice polytope. The weighted composition prefix
gives the unique Ehrhart polynomial from its value at every positive integer.
The proof identifies the three negative evaluations with counts in the actual
topological interiors. The [scoped receipt](verification/lean-ferroni-higashitani-complete-20261124/receipt.json)
records 14 strict source builds, 409 owned declarations, 16 required endpoints,
and stock-kernel replay.






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

## Coulangeon–Lazzarini’s two-shell conjecture

[Lean refutes Conjecture 21 in dimension ten](../lean/Conjectures/CoulangeonLazzariniRealLattice.lean).
It verifies the full-rank discrete lattice in real space, identifies its first two
positive squared norms as 4 and 8, and checks the two spherical moment
identities and the failure at squared norm 9. The [integer-coordinate proof](../lean/Conjectures/CoulangeonLazzariniShells.lean)
also verifies the arbitrary-delay parity-lattice family.
The orthogonally indecomposable family and height results remain open in Lean.

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

## Gravgaard–Lee’s large-digit Lüroth sumset

[Lean proves Conjecture 2.12 and the stronger interval in the written proof](../lean/Conjectures/GravgaardLeeLargeLuroth.lean).
For every integer $k\ge2$, the sum of the large-digit Lüroth set with itself contains
$(0,1/(k-1)]$. The witnesses have strictly increasing interleaved digits.
The development verifies both the convergence of the source's series and the half-open
digit intervals. See `conjecture_2_12`, `interval_subset_sum` and `interleaved_decomposition`.

## Steinke–Zakynthinou’s agnostic VC learning conjecture

The companion paper's Conjecture 4.18 uses distribution-free information on fixed paired supersamples. Its two guarantees hold for every positive sample size by [the Lean theorem](../lean/Conjectures/AgnosticVC/FixedPairing.lean). The COLT bounty version uses conditional mutual information for iid data. [Companion paper, Definition 1.1 and Conjecture 4.18](https://arxiv.org/pdf/2001.09122v3)

Lean proves the two guarantees for a single proper learner. The original CMI is at most $`19{,}712d`$ nats, and the expected empirical excess on every sample is at most $`583\sqrt{d/n}`$. The [fixed-pairing theorem](../lean/Conjectures/AgnosticVC/FixedPairing.lean) bounds every deterministic paired pool for arbitrary hypothesis sets. The population theorem specifies measurability of its chosen representatives and discharges this assumption for countable measurable classes, countable instance domains with measurable singletons, and classes ordered with a countable initial segment of measurable predictors realizing every finite trace. A separate theorem requires only almost-everywhere measurability of the pool information to obtain the iid bound. [Theorem](../lean/Conjectures/AgnosticVC/Theorem.lean) · [Verification receipt](../results/steinke-zakynthinou-agnostic-vc/verification.json)

The negative statements are also formalized. The [global Borel disproof](../lean/Conjectures/AgnosticVC/BorelChoiceObstruction.lean) has standard Borel spaces and Borel finite-trace tests. The [completed-iid disproof](../lean/Conjectures/AgnosticVC/CompletedFiniteGroups.lean) defeats every candidate constant with a VC-one class of finite supports. Measurability of the scalar expected empirical loss under one completed iid law suffices for the disproof. The [written analysis](../research/steinke-zakynthinou-agnostic-vc/completed-finite-groups.md) proves class-by-class distribution-uniform convergence in outer probability and quantifies its sample-size dependence. The general standard Borel completed-iid conjecture remains open in this repository.

The [local reconstruction theorem](../lean/Conjectures/AgnosticVC/LocalReconstructionMeasurable.lean) proves the actual iid CMI bound $`197{,}120d+32k`$ nats for classes with measurable proper reconstructions from at most $`k`$ rows. It retains the empirical rate and covers the [circle-orbit example](../lean/Conjectures/AgnosticVC/OrbitIidRates.lean) with $`k=1`$.

For a single VC-one class of disjoint two-point supports, Lean verifies that the empirical rate is impossible when the scalar expected loss must be universally measurable. The [verified uniform-deviation envelope](../lean/Conjectures/AgnosticVC/FiniteSupportUniform.lean) has expectation at most $`2/\sqrt n+2/n`$ for that class under every iid law. A [written learner](../research/steinke-zakynthinou-agnostic-vc/completed-disjoint-support-learner.md) proves both rates for the same class with measurability on each completed iid law.

The [integer-noise learner](../lean/Conjectures/AgnosticVC/NoisySupportIid.lean) gives actual iid CMI at most $`20s`$ nats and all-sample expected empirical excess at most $`m/n+8/\sqrt n`$ for bounded support size $`m`$ and overlap $`s`$. The [sharp-deviation extension](../lean/Conjectures/AgnosticVC/NoisySupportSharpIid.lean) removes the support-size restriction given a sharp outer uniform-convergence bound. A positive-outer-mass event of too many hits on a null support would violate that bound under a reweighted iid law.

The [conditional joint-law disproof](../lean/Conjectures/AgnosticVC/ConditionalJointObstruction.lean) derives the literal finite-support obstruction from measurability of the actual conditional selector/output kernel used for iid CMI. Lean also verifies the version with conditional laws on an ambient standard Borel code space, where the proper subclass has the trace Borel sigma-algebra. The [repeated-feature lemmas](../lean/Conjectures/AgnosticVC/RepeatedFeatureReadout.lean) verify a measurable version for any repeated-feature readout and an almost-sure hit bound for every null finite support.

The [seeded-pool disproof](../lean/Conjectures/AgnosticVC/ConditionalJointObstruction.lean) assumes completed measurability only of the actual ambient output on the iid pool, fair selector and independent seed, along with ordinary seed expectations on every fixed sample. It derives the empirical-loss contradiction directly from those random variables.

The [fair-label disproof](../lean/Conjectures/AgnosticVC/FairLabelObstruction.lean) forces iid CMI at least $`n/32`$ for tolerance at most $`1/8`$, allowing improper outputs. Lean verifies the benchmark, population and empirical loss estimates, and the contradiction for every candidate constant, with the published generalization inequality as an explicit premise.

## Steinke–Zakynthinou threshold theorem

[Lean proves the proper real-threshold case of Conjecture 6](../lean/Conjectures/SteinkeZakynthinou.lean). For every positive sample size the same measurable learner works for every iid labeled distribution and every fixed sample. Its outputs are finite closed thresholds. Lean bounds original paired-pool CMI by 300 nats or 600 bits and expected empirical excess by $`512/\sqrt n`$, including arbitrary ties and label noise. The source statement in bits with the infimum over all thresholds is `SteinkeZakynthinou.properThresholdTheorem_bits`. The written proof supplies sharper information constants and separate efficiency and determinism extensions. All 28 modules in the Lean theorem’s project import closure passed the pinned kernel replay. The standalone audit checked 806 declarations against the standard axiom whitelist.

Gröchenig’s upper-density result is excluded after a [checked earlier resolution](../research/bounty-continuation-2026-11-21/grochenig-prior-resolution/). Its independent proof and verification receipts remain in [immutable Git history](https://github.com/1337isnot1337/solved-conjectures/blob/628270dc5e07d7924de265d2ac1beee4b5634b80/docs/verification/lean-grochenig-20261121/receipt.json). The reused KVZ results remain active.

The shared package is in [`lean`](../lean/).
It uses Lean **4.35.0** and Mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`, as pinned in the existing manifest.
The campaign has incorporated the source collection and layout through commit
`daad0edf918f12cd57f6b30d3f16b28e7a12d2c5`. Earlier receipts below retain their
original checked scope.

Unregistered proofs and their separate hosted checks are tracked in
[`lean-candidates.md`](lean-candidates.md). Their presence in the repository
does not expand the accepted scope in the table below.

At candidate snapshot `75df6294`, the six-speed classification-to-bound
adapter passed its 21-module closure and 284-theorem axiom audit. The
hyperplane residue and endpoint-component closures also passed, covering
26 modules/463 theorems and 29 modules/490 theorems respectively. Each job
rebuilt sources, checked the standard axiom whitelist, independently replayed
every project kernel object, and confirmed unchanged sources. These older receipts retain their original scope; the table below records
subsequent registrations. In particular, the adapter retains its five-speed
bound and primitive six-speed classification hypotheses. Exact job links and
scopes are in [`loneliness-75df-component-receipts.json`](loneliness-75df-component-receipts.json).

A complete formalization here means that Lean checks the mathematical conclusion
from the definitions in the indicated files. The correspondence between those
definitions and an external publication remains subject to mathematical review.
Published mathematical theorems that have not been formalized are hypotheses,
never additional Lean axioms.

The README uses ✅ for complete formalization of the stated result, 🟢 for
partial formalization with a computer-assisted proof, 🟡 for partial
formalization, and ⬜ when a result has no Lean verification. Essential computer-assisted
proofs are documented separately in the catalogue and result package.

| Note | Status | Checked scope and remaining gap |
| --- | --- | --- |
| Steinke–Zakynthinou’s agnostic VC learning conjecture | Partial | Lean verifies the fixed-pool rate and empirical accuracy. The iid information and measurable learner results retain the hypotheses in the [scope audit](../results/steinke-zakynthinou-agnostic-vc/SCOPE.md). |
| Steinke–Zakynthinou agnostic threshold problem | Complete | Lean proves the proper real-threshold prize statement, including measurability, original CMI for arbitrary iid labeled distributions, and empirical accuracy on every fixed sample. The exact source bounds follow with the common constant 1024. The [scope review](../results/steinke-zakynthinou-thresholds/LEAN_REVIEW.md) checks the constant-zero comparator, the Borel Markov kernel, and the KL of the selector and the actual cutoff. |
| Johnson's conjecture | Partial | Lean defines the actual Pfaffian as a signed sum over matchings, proves its diagonal scaling and cyclic rotation identities, checks the source bound for all matchings on four ordered nodes, and proves the product-improving, span-decreasing local uncrossing step. Lean also proves the all-order source kernel interval-factor decomposition, the interval twin-vertex pigeonhole lemma and the endpoint deduction from nonnegative prefix sums. Lean constructs the adjacent-vertex involution on canonical matchings and proves it has no fixed points off the matched adjacent edge. Over any commutative ring, Lean proves crossing-parity reversal, cancellation off the adjacent edge for twin rows, and the full twin-row deletion identity after relabeling the residual matchings to the smaller standard vertex set. Lean also proves the sparse-support alternative: an uncovered vertex gives zero, otherwise the interval matrix has a deletable twin pair and reduces to a smaller interval matrix with grouped coefficients. Lean proves coefficientwise nonnegativity and homogeneity of the interval-matrix Pfaffian polynomial in every even order, and nonnegativity for arbitrary nonnegative real interval coefficients. Lean also proves nonnegativity of the bordered prefix matching sums. Lean proves the first-row expansion and an endpoint bound in terms of the final prefix difference. Lean identifies that difference with the smaller principal Pfaffian and proves the source endpoint inequality for every positive even order. The general matching induction and the full repository gate remain open. |
| Brown–Mol's conjecture | Complete | Lean proves the explicit 1001-vertex counterexample and that all sufficiently large members of the literal tree family have diameter four and a nonzero subtree root in the forbidden disk. It counts actual connected induced vertex sets and establishes the infinite family through local analytic inverses and logarithmic derivatives. Strict standalone compilation, all-owned axiom audit and stock-kernel replay passed; the combined repository gate is pending. |
| Ekhad–Zeilberger’s most unfair bet conjecture | Not formalized | Written proof of the extremal bound, with a finite exact comparison of pairs. |
| Kauers–Koutschan recurrence conjecture | Not formalized | Written proof and exact symbolic verification of both recurrences for all lengths. |
| Kovalev's conjecture | Partial | Lean proves the pointwise transfer inequality, the dimension threshold, the fourth-moment calculation and the exact rational separation. The Gaussian expectations and spherical Hardy-norm identities remain to be formalized. [Real inequalities and moment calculation](../lean/Conjectures/KovalevHardySeparation.lean) · [Research receipt](verification/lean-kovalev-hardy-separation-20261126/receipt.json). |
| Roos–Seiringer's conjecture | Not formalized | Complete proposed computer-assisted proof of the full radial Dirichlet kernel assertion. Analytic tails and an essential exact certificate over 184 closed intervals cover the entire positive real axis; source scaling covers all positive chemical potentials. Two independent mathematical/code reviews, a separate priority audit and full replays passed. The unaveraged kernel is outside the claim. No Lean formalization is claimed. |
| Dospolova–Germanskov–Zaporozhets's conjecture | Partial | Lean checks the positive factorial family, exact ultra-log-concavity and scaled ratios, countable-limit step, and strict expected sample range for an actual Gaussian process under almost-sure boundedness and deterministic local-range-limit assumptions. Intrinsic volumes, determinism of those local limits, and Vitale's limiting theorem remain unformalized. Strict source compilation, isolated kernel replay and endpoint axiom checks passed; full repository gate pending. |
| Chen–Khare–Sahi's conjecture | Partial: literal source convention unresolved | At q=1/10, t=9/10, Lean proves the complete stable Hall family over all eleven degree-six partitions, literal power-sum coordinates and polynomial injectivity, unique monic dominance-triangular orthogonality, three-variable specialization, positive normalization, and full Muirhead-semiring nonmembership. The degree-three finite-Hall source conflict is formal. All 19 modules passed strict sources, complete owned/private audits and exact stock replay. Broader families remain eigenfunction-characterized; the separate earlier 16-module compatibility replay and the combined repository gate remain pending. |
| Ferreira–Simon's conjecture | Not formalized | Complete proposed analytic proof of the beta-prime self-convolution identity for its full real-parameter range. Two independent mathematical reviews and 18 supplementary exact formal-parameter checks passed. No Lean formalization is claimed. |
| Lyon's conjecture | Not formalized | Complete proposed computer-assisted proof for every positive real shape. Analytic tails and an essential exact integer certificate covering 4256 real intervals establish the derivative sign. Two independent mathematical/code reviews and full certificate replays passed. No Lean theorem or partial Lean credit is claimed. |
| Han–Sabag–Kostina–Hassibi's conjecture | Complete source formalization; merged-package gate pending | Lean proves the original matrix feasibility, rational witness, exact sparse infimum and all four individual assignment infima, plus the uniform gap throughout the stated open gain interval. Standalone strict source compilation, all-owned axiom audit and stock-kernel replay passed; the merged-package gate is pending. |
| López Pouso–Segura's node conjecture | Partial | Lean checks the two Legendre roots, standard weight formula, exact cubic quadrature, and the two failed inequalities; the degree-two polynomial and its derivative are connected to mathlib’s shifted Legendre polynomial. Strict source compilation, one-module kernel replay and endpoint axiom checks passed. Lean also verifies the explicit perturbation functions, derivatives, differential equations final coefficient algebra, and the deduction of the scaled limit and eventual violation from three separate factor approximations with vanishing second-order remainders. Controlled ODE and root asymptotics, the gamma-ratio expansion, those factor approximations and the full repository gate remain pending. |
| Vishnyakova's conjecture | Complete | Lean proves the original sampled-sequence and weighted transform-class theorems for every positive degree and weight. The proof uses all finite ordered Toeplitz minors and proves both centered disks and attained exact radii. All 17 modules passed strict sources, the complete axiom audit, and stock-kernel replay. |
| Novelli–Thibon's conjecture | Not formalized | Complete proposed proof of the intended monomial-product Conjecture 5.7 for all partitions and independent parameters, plus the adjacent all-size hook-coefficient formula. Two internal mathematical reviews and exact convention checks passed. The source index correction and priority limits are explicit; Schur positivity and general traces are not claimed. |
| López Pouso–Segura's conjectures | Partial | Lean proves all three signs, strict monotonicity and exact limits conditionally on the stated finite mixture, phase ODE, endpoint, zero/weight asymptotics and two resolvent expansions. It also proves the reference kernel integral and the dominated-convergence and comparison steps linking those inputs to the limits. The Bessel identification, special-function inputs, reference Euler–Maclaurin remainder and full repository gate remain open. |
| Simon's stable-infimum conjecture | Not formalized | Complete proposed proof of the full parameterwise convex order, including the Brownian endpoint. The independent review checks the prior Mellin transform, increasing logarithmic Lévy measures, exponential integrability and conditional Jensen argument. No numerical or finite-case inference is used. |
| Ferreira–Simon's stochastic-order conjecture | Not formalized | Complete proposed proof for every pair of real parameters in the source interval. The Poisson-series scale and strict sequence-norm comparison give a simultaneous coupling, both endpoint limits and the associated Mittag–Leffler inequalities. Independent internal review passed. |
| Ferreira–Simon's diagonal Mittag–Leffler conjecture | Not formalized | Complete proposed proof of strict increase throughout the full unit parameter interval. The independent audit checks the Pollard integral, classical sine quantile, derivative signs, reciprocal pairing and strictness. No numerical or finite-case argument is used. |
| McCrea's conjecture | Not formalized | Complete proposed proof of the unique linear-density crossover for every modulus at least three. Positive coefficient asymptotics handle the floor, and the exponent difference has exactly one zero in the stated interval. Independent internal review and exact profile-word diagnostics passed. |
| Chen–Kitaev–Zhang's record conjectures | Complete | Lean proves the original Conjectures 1 and 3 for actual separable-permutation classes and all four record statistics, with every stated length and singleton case. The credited source-pinned trureturing proof supplies the previously resolved Conjecture 2 tail and permutation decomposition; direct Pell certificates prove the remaining low-record comparisons. Strict standalone compilation, a 1,132-theorem axiom audit and isolated stock-kernel replay passed; the combined repository gate is pending. |
| Zhu's generalized Jacobi–Stirling conjecture | Complete source formalization; merged-package gate pending | Lean proves the original recurrence, the 3×3 determinant identity, the exact coefficient −4, the negation of coefficientwise positivity of all finite Hankel minors, and the stated counterexample region over every linearly ordered field. The standalone source passed strict compilation, an all-owned axiom audit, and stock-kernel replay. The combined repository gate has not yet passed for this registration. |
| Circulants with circular chromatic index in the upper half | Partial overall; main theorems and regular supplement complete | Lean proves the actual `4g`-regular and `4g`-connected graph with real circular index `4g+2/3` for every `g ≥ 2`, and the complete degree/connectivity/index statements for C25, C31 and C33. The real-colouring lower bound and atom/subgroup connectivity arguments are proved internally. Strict sources, an all-owned audit of 601 declarations/500 theorem declarations and 171 required endpoints, and exact stock-kernel replay passed. [Local receipt](verification/lean-named-20261121/circular-receipt.json). The nonregular Section 7 examples, structural/insertion lemmas, SAT exclusions, combined repository gate, and hosted validation remain separate. |
| Graphs with circular chromatic index in the upper half for Δ ≡ 2 mod 4 | Not formalized | Written proof of Theorems 1 and 1′ (`Δ = 4g+2` and `Δ = 4g+1`, `g >= 6`, `χ'_c = Δ+2/3`) after one independent model referee pass, which found no errors. The standard-library verifier checks the construction for `6 <= g <= 60` and the `K_n-tK_2` colourings of Proposition 2 (`Δ = 10, 14, 18, 22`). No proof-assistant formalization is claimed. |
| Graphs with circular chromatic index in the upper half for Δ ≡ 3 mod 4 | Not formalized | Written proof of Theorem A (`Δ = 4g+3`, `g >= 15`, `χ'_c = Δ+2/3`) after one independent model referee pass, which found no mathematical errors. Proposition B (`Δ = 27, ..., 59`) rests on stored certificates. The standard-library verifier checks the construction for `15 <= g <= 60` and the nine certificates from the definition. No proof-assistant formalization is claimed. |
| Malek's conjecture | Not formalized | Complete written all-degree negative-transform proof with all equality cases, two independent internal reviews and exact scalar identity checks. The permanent endpoint is prior work; the named subsidiary is documented in the Minc site's linked survey. No proof-assistant work is claimed. |
| Mazák–Zrubák conjecture on complete graphs minus an edge | Partially formalized | The actual real-coloring reduction and Hall spanning edge order (Steps 1–3) passed sixteen strict source builds, the complete 526-declaration audit, and exact stock replay. Steps 4–8 and the final all-even-degree equality remain outside this checkpoint; count zero. [Scope](../results/circular-index-complete-minus-edge/FORMALIZATION.md). The written proof and its finite cross-checks retain their original scope. |
| Circular chromatic index of complete graphs minus a few edges | Not formalized | Written second proof of Mazák–Zrubák Conjecture 2 for every odd `n >= 7` and exact values for `K_n` minus 2 or 3 edges for small `n`, after two independent model referee passes; the colourings for `n = 19, 23, 27, 47` and the later symmetry and structure lemmas are unrefereed. The standard-library verifiers check the 32 explicit colourings and search exhaustively for perfect sequencings of `K_n-e` for `n <= 9` and of `K_7` minus two edges; optional SAT runs with a DRUP certificate generator treat `n = 7, 9`. No proof-assistant formalization is claimed. |
| Baricz–Pogány's asymptotic-coefficient positivity conjecture | Complete | Original factorial products, formal division, all-degree strict positivity and the explicit lower bound are proved. The source coefficient recurrence uniquely determines the same sequence; its inequality is now an explicit endpoint. Strict compilation, an all-owned audit of 65 declarations/55 theorem declarations and all seven required endpoints, and stock-kernel replay passed. [Local receipt](verification/lean-named-20261121/baricz-receipt.json); combined repository gate pending. Source-access and priority limits are unchanged. |
| Pula–Song–Wanless conjecture | Not formalized | Complete written proof of the all-parameter threshold, including its equality case and unique boundary minimizer. Real-rooted minor equalization and van der Waerden completion replace disputed dependencies. Exact identity checks supplement the proof. The full Minc Problems 14 and 15 remain outside its scope. |
| Perron root of permanental compounds | Not formalized | Written FPRAS proof for every nonnegative rational matrix and every compound degree, with deterministic zero detection. Exact finite checks supplement the argument. This is the randomized approximation formulation of Minc Problem 18; exact polynomial-time eigenvalue computation and the characteristic-polynomial problem are outside its scope. |
| Oravcová–Soták conjecture for five to eight distances | Partial | The formalization uses the actual distance graph on the integers. Its unconditional results include the greedy upper bound, periodic-word transport, loop concatenation, integer base change, the four unbounded one-parameter coloring families, the full two-parameter family, and the exceptional chromatic numbers. Theorem A, the Oravcová–Soták clique conclusion, and the primitive triangle-free corollary retain the explicitly named propositions `R5`, `R6`, `R7`, and `R8` as hypotheses. Those four real-loneliness classifications are not proved by this closure. All nine new modules passed strict compilation with warnings treated as errors. The exact 28-module project closure passed an all-owned audit of 1239 declarations (1084 theorem declarations and 40 required endpoints) and independent stock-kernel replay. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. [Receipt](verification/lean-named-20261121/oravcova-receipt.json). Combined package gate remains pending. |
| Johnson–Kaya–Matzke conjecture on Babai spectra of paths | Complete | Lean proves the exact spectrum interval for every `n ≥ 2` and `1 ≤ k < n`, using the actual `SimpleGraph.chromaticNumber` of the distance graph on `Fin n`. It proves the independence and coloring bounds, greedy coloring, and modular-coloring/clique realization of every allowed value. Strict compilation, an all-owned audit of 43 declarations/39 theorem declarations and all 12 required endpoints, and stock-kernel replay passed. No published input remains a hypothesis. [Local receipt](verification/lean-named-20261121/babai-receipt.json); the combined repository gate and hosted validation remain separate. |
| Ferreira–Simon's Wright log-concavity conjecture | Complete original-conjecture disproof | The actual infinite Wright series has a continuous beta-zero counterexample family, with admissible alpha approaching one. Strict compilation, the complete 25-declaration owned audit including eight private declarations, and independent stock-kernel replay passed. The positive-beta refinements in the written proof and the combined repository gate remain separate and pending. |
| Karp–Vishnyakova–Zhang's gamma-quotient conjecture | Complete | Lean proves the literal gamma quotient on every strictly ordered real grid with c>d and positive denominator arguments. Noninteger differences are strict at every order; integer m gives nonzero minors through order m+1 and zero larger minors. The exact signature and third-order correction are checked. All 15 modules passed strict sources, the complete owned/private audit, and stock-kernel replay. The combined repository gate remains pending. |
| Alexandersson's Fuss–Catalan conjecture | Complete | Lean proves the literal Fuss–Dyck enumeration and closed formula, real-rootedness, the exact simple-negative-root count, and scalar reduction to the ordinary case. It proves that any ordinary-case relation between root multisets transfers; the cited ordinary-case interlacing theorems themselves are not re-proved. Strict standalone compilation, all-owned axiom audit and isolated stock-kernel replay passed; the combined repository gate is pending. |
| Sagan–Swanson conjecture | Not formalized | Written proof of all four stated asymptotic normality assertions using actual means and variances; finite model checks are supplementary. |
| Bernardi–Morales's delta-process conjecture | Complete | Lean proves published Conjectures 27–28 for all admissible parameters: the literal delta-map tree count for every fixed color map, and the complete marked interval-event count and source probability determinant for every fixed surjection. Full subsets, singleton complements and the singular averaging case are included. The 13-module closure passed strict compilation with warnings treated as errors, an all-owned audit of 269 declarations (205 theorem declarations and 23 required endpoints), and independent replay by the pinned stock kernel. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. [Receipt](verification/lean-named-20261121/bernardi-receipt.json). Combined package gate and hosted validation remain separate. |
| Gilmore's crossing–nesting conjecture | Complete | Lean proves the full crossing–nesting identity for the stabilized product-defined matrix, with alignment and size refinements, over every commutative ring. Canonical matching lists enumerate exactly the literal perfect matchings; their weights count the actual crossing, nesting and alignment inequalities. Fresh strict compilation, the all-owned audit of 449 declarations (346 theorem declarations, including private declarations) and all 20 required endpoints, and stock-kernel replay passed. [Local receipt](verification/lean-named-20261121/gilmore-receipt.json). The combined repository gate and hosted validation are separate. |
| Currie's conjecture on complexity 2n+1 and critical exponent | Not formalized | Written proof for all twenty words of the journal and arXiv versions, computer-assisted in finitely many described places, after one independent model referee pass. The standard-library verifier checks the morphism identities, exact factor sets, the hypotheses of the insertion lemmas, the short bispecial factors and the exact inequalities in `Q(λ)` for the 72 families; brute-force cross-checks cover bounded lengths and prefixes. No proof-assistant formalization is claimed. |
| Dawkins–Nappo–Tong–Zimbizi wild-number conjecture for n ≥ 155 | Not formalized | Written proof for every `n >= 155` after one independent model referee pass per theorem; the conjecture remains open for `13 <= n <= 154`. The standard-library verifier rechecks the local-lemma and cluster-expansion conditions in exact rationals. |
| Chow's conjecture | Complete | Lean proves consecutive interlacing at every rank at least two, strictly from rank three, for the actual even-signed permutation enumerators. The proof derives the refinement recurrence and all root inequalities internally. All 11 modules passed strict sources, the complete axiom audit, and stock-kernel replay. |
| Németh–Seberry–Shu conjecture | Partial | Lean proves the actual permanent congruence for every prime order, cross-row injectivity, and the dense-row counting reduction with its uniform finite-family premise explicit. Both modules passed strict compilation, the all-owned audit, and stock-kernel replay. The analytic separation theorem and quadratic refinement remain unformalized. [Scope and receipt](../results/nemeth-seberry-shu/LEAN_STATUS.md). |
| Dilcher–Kidwai–Tomkins’s Stern-polynomial conjecture | Partial | Four checked modules prove the actual recurrence and the all-index local-criterion reduction. The near-one estimates, compact certificate and exterior argument remain unformalized. [Scope](../results/stern-half-plane/FORMALIZATION.md) · [Review](../results/stern-half-plane/LEAN_REVIEW.md) · [Receipt](verification/lean-stern-half-plane-partial-20261124-162051/receipt.json). |
| Hartke–Stolee–West–Yancey matching-excess conjecture | Complete | Original Conjecture 9.15 for actual finite simple graphs, with exact extremal stabilization and quantitative bounds for both constants and tail minima. All 22 strict sources, the all-owned/private audit and exact stock replay passed. [Scope](../results/hartke-stolee-west-yancey-matching-excess/FORMALIZATION.md) · [Receipt](verification/lean-hartke-matching-excess-complete-20261124-162051/receipt.json). |
| Ulas’s disjoint-block square-product conjecture | Partial | The checked uniform repeatable-count construction gives infinitely many collections at every positive multiple of the constructed count. Prime-avoiding tail counts remain unformalized. [Scope](../results/ulas-disjoint-square-blocks/FORMALIZATION.md). |
| Gravgaard–Lee’s mixed upper/lower Lüroth conjecture | Complete | Exact interval equality and original modulo-one conclusion for every k≥2, with actual infinite upper/lower expansions. All 12 strict sources, the complete axiom audit and exact stock replay passed. [Scope](../results/gravgaard-lee-upper-lower-luroth/FORMALIZATION.md) · [Receipt](verification/lean-gravgaard-lee-upper-lower-complete-20261124-162051/receipt.json). |
| Fan–Tringali’s power-monoid length-set conjecture | Complete original 2018 conjecture | Both power monoids of every Dedekind-finite monoid with infinitely many distinct positive powers, and the exact reduced natural-number system. All 18 modules passed strict source builds, the complete declaration/axiom audit and stock kernel replay. Survey irreducibles, multiplicities and relative cancellativity remain unformalized. [Scope](../results/fan-tringali-power-monoid-lengths/LEAN.md). |
| Sonntag–Teichert conjecture | Complete source formalization; merged-package gate pending | Lean proves the tournament theorem, the forward classification of separated oriented-graph cases as two stars, and an explicit realization for every pair of stars with arbitrary additional isolated vertices. The standalone strict source check, all-owned axiom audit and stock-kernel replay passed; the combined repository gate is pending. |
| Horňák–Woźniak conjecture | Partial | Lean proves arbitrary vertex decomposability for tripods with a positive short arm of length at most two, conditional on source tests 1 and 5. For all positive short-arm lengths it proves partitions containing a larger part under those tests, realizes partitions with a sublist summing to the short arm unconditionally, and reduces the remainder to partitions with no mergeable noncentral pair. The general all-small case, four-arm reduction, existence constructions and combined gate remain. Strict compilation, a 958-theorem full-chain axiom audit and isolated kernel replay passed. |
| L-solitaire | Complete for both the counterexample and corrected theorem | Actual moves for arbitrary layer sets containing 1; all recurrent states; classification and maximality of stable references; one-column interlacing; the explicit uniform profile bound and convergence for every diverging scale. The separate fixed-scale counterexample remains checked. |
| Three-player War | Complete for all three explicit cycling deals | Distinct ranks and round-robin deal sizes; exact transition rules; returns after 90, 180, and 19,320 turns; no earlier positive return; all three players active at every nonnegative time. |
| Pham denominator degree | Complete | Both exact rational identities follow from actual Bulgarian-solitaire cycles and coefficientwise stabilization of their first-entry levels. The primitive period-10 words have reduced denominator degrees 5 and 10, with coprimality and minimality against every nonzero alternative denominator. No published rationality or degree-bound theorem is assumed. |
| Batista Egyptian fractions | Complete | An ordered lexicographically first solution uniquely maximizes the last denominator for every admissible positive `k` outside residue class 1. The proof uses the elementary global comparison and a kernel-reduced exhaustive certificate below 100, with proved denominator bounds; no published comparison theorem is a hypothesis. |
| CUT Family B | Complete | The actual well-founded mex games have identical values at every positive pile size iff `3x < y`, including infinite cut sets. The six-block base formula, preservation under all even cuts, and discrepancy by `4x` are proved internally. |
| CUT arithmetic periodicity | Complete | The uniform terminating decision test and exhaustive candidate enumeration are proved for every finite cut set and proposed arithmetic tail. Compact quotient/residue certificates identify both actual example games at every pile size and prove least eventual period 12, saltus 8, and earliest start 7, hence positive-pile preperiod 6. |
| Loneliness on a fixed hyperplane | Complete | Original ordered positive distinct sample; deterministic maximum and velocity bound; uniform O(1/N) error over all shifts; fixed and independent Haar-shift laws; exact finite-subspace and positive-N quasipolynomial counts with degree bound; full-support endpoint formula including k=2; sharp (1,2,3) example. The complete 72-module closure passed strict sources, all-owned/private audit and exact stock replay. |
| Graffiti.pc Conjecture 318 ([@JesterInABarrel](https://x.com/JesterInABarrel/status/2123233964827812334)) | Complete | The all-order theorem uses actual graph distances and undirected complement-edge counts. Every total dominating set contains an adjacent total dominating pair; every minimal set has size two. The stated five-vertex graph proves sharpness of a one-unit relaxation. |
| Hadamard order-2396 partial results | Partial overall; automorphism, fixed-border construction and symmetry, and length-598 obstruction complete | The full signed-automorphism group excludes order 479, with both norm proofs checked. The fixed-border common multiplier group is cyclic of order dividing four and every preserving subgroup leaves at least 151 sign orbits. On any finite abelian group with a subgroup of index four, the original four sign rows and raw correlation equations yield an actual bordered Hadamard matrix; normalization, the literal finite border, and all fourteen size-149 baseline patterns are proved. The length-598 order-eleven obstruction is complete. The actual two-row Hadamard construction and quotient transport are checked. For length 1197, the actual common multiplier order is proved to divide 27; exclusion of order 27 and the finite quotient/no-lift certificates remain candidates. |
| Lonely-runner two insertions | Complete | Every `p ≥ 3` and arbitrary positive integer speeds have a common witness in `[1/(p+2),1/p]` with clearance at least `1/(p+2)`. The unbounded branch, all small cases, interval-good base insertion, Goddyn–Wong acceleration criterion, common-dilation value bound, and literal three-insertion obstruction are proved. |
| Zhang's Question 8.4: deletion values of the lonely runner | Complete theorem; full gate pending | Lean proves the exact values in both ranges for every n≥3, 1≤r≤n−1, and the strict inequality for n≥4, using actual real distances and speeds. The small-deletion upper bound is proved internally via rational maximizers and the modular certificate; Liu's theorem is not assumed. The seven-module closure passed local kernel replay, and the theorem endpoints use only allowed axioms. Full repository gate pending. |
| Zhang's Question 8.5 for 18 ≤ n ≤ 57: shifted lonely runner counterexamples | Complete for the published range | All 40 rational certificates attain their recorded maxima over all real times and give $\Gamma(n)<1/(n+1)$ for $18\le n\le57$. The remaining sizes 58–94 are open. [Lean proof and receipt](../results/shifted-lonely-runner-counterexamples/FORMALIZATION.md). |
| Erdős–Gyárfás abelian covers | Complete for the stated voltage-cover theorem and sharpness | Every seven-label voltage cover of the singly subdivided tetrahedron over every abelian group contains an actual simple cycle of length 4, 8, 16, or 32. The 64-node literal certificate, its collision-branch soundness, and voltage normalization are checked. The connected 95-vertex cyclic cover attains least power-of-two cycle length 32. The general minimum-degree-three conjecture is outside this result. |
| Li coefficient sign | Complete for the explicit counterexample | Full coefficients +29 and −6304, all 6,842 partition types, exact count eight, and `2^30` genuine connected partitions. All 44 source checks, 25 literal contracts, owned and raw-occurrence audits, and 44 exact stock replays passed. Alternative Python proof implementations remain outside this Lean scope. |
| Frankl generating families | Partial: both frequency bounds complete; cyclic span-four pending | The all-point high-girth bound is checked for every `k ≥ 3`: incidence girth at least 16 and exactly three generators through each point imply frequency at least `518208/1000000` among distinct unions. The `k ≥ 15` linear-family bound is also checked with frequency `657/1000`. Both include the empty union. The complete Vaughan shortcut, small-cycle cases, local checker semantics, and conditional all-period assembly are checked. The remaining cyclic span-four graph/transport certificates and unconditional assembly are still being verified. |
| Erdős 607 line sizes | Complete | Lean proves the exact realizability and geometric counting identity for every natural point count, the coefficientwise and analytic generating functions, Fourier extraction, the actual finite-product limit and domination, and the sharp asymptotic for the actual record count with prefactor 3/(16√(6π)A^(1/4)), where A=π²/12+(log 2)²/2. No unproved local-limit, tail, or coefficient-transfer premise remains. |
| Growing rectangles | Complete | The logarithmic asymptotic is proved uniformly for every `w ≥ h` as `h → ∞`, for literal integer-sided real-position tilings counted by block multiset. The real-to-grid bridge, cumulative partition asymptotic, both packing reservations, and exact leading constant are checked. |
| Distance graphs with three missing differences | Complete | The actual extremal densities and circle maxima for `{1,k,k+5}` and `{1,k,k+7}` are classified for every positive `k`, including every small exception. Explicit periodic optima, the exact Conjecture 39 discrepancy, and infinitely many strict counterexamples are proved. |
| Two-difference Motzkin theorem | Complete | The exact compact-group character formula, exhaustive relation-basis trichotomy, all-modulus cyclic formulas, gcd scaling, odd-cycle criterion, and stated example are checked. The literal fixed character window and rational interval unions attain the stated bounds. The exact floor-sum evaluator, Hermite independence number, attaining character, and explicit arithmetic-operation and integer-size bounds are checked and registered. |
| Tight six speeds and critical planes | Partial | The consecutive six-speed set has global value `1/7`. The complete split certificate for the prime-257 minimum-pair-20 probe is checked and registered, including its original normalized-support exclusion without a certificate premise. Full prime coverage, uniqueness, unconditional plane classification, and the large-norm consequence remain open. |
| Six-speed spectrum | Partial; complete realization direction | Every proposed value `(P−1)/(6P)` for `P ≥ 7`, `P % 6 = 1 or 5`, is attained by six distinct positive primitive speeds. The consecutive and progression families, the `P=11` boundary and displayed finite examples have checked exact global values. The universal family and off-family classification remains incomplete. |
| Eight-runner equality cases | Partial | All three displayed sets have global value `1/8`. Exhaustiveness remains open. |
| Nine-runner equality case | Partial | The consecutive set has global value `1/9`. Uniqueness remains open. |
| Symmetric four-point density | Complete | Exact real packing and covering densities for every literal translated symmetric four-point integer set, including common-divisor normalization. Both periodic constructions and the two sharp local interval lengths are proved. |
| Packing with two nonmixed gaps | Complete | The exact three-case packing and real circle formula for every positive gap pair and arbitrary positive gap counts, including gcd normalization, literal tile semantics, periodic attainment, and the stated example. |
| Haralambis three-difference theorem | Complete | Exact equality of actual extremal density and real circle value for every positive triple, with no coprimality premise. An optimal periodic set has a pair-sum period. The proof includes finite balanced orientations, signed defects, odd periods, interval counting, and the explicit `{2,5,9}` example. |
| Five-speed spectrum | Partial | All twelve example values and both critical-family reductions are checked. The unconditional four-speed gap theorem is proved: below `2/9`, precisely the two scaled critical directions occur, both with value `1/5`. This also proves the four-speed runner bound. The unconditional five-speed lower bound `L(v) ≥ 1/6` is also proved by Renault’s argument. All 122,880 indexed plane cases and the five-speed coordinate cutoff are checked, and their gap input is now available. The bounded five-speed classification remains open. |
| Tight nine-speed sets | Partial | The consecutive direction has exact global value `1/10`. The norm cutoff and prime selection are checked under explicit smaller-dimensional runner bounds. Those bounds, exhaustive modular classification and uniqueness remain open. |
| Seven-speed spectrum | Partial | Realization, the 27 displayed exceptional values, and sharp candidate bounds are checked. The critical-plane classification and large-norm family bridge are registered under explicit `LonelyRunnerBound 5` and primitive tight-six classification hypotheses. Unconditional tuple exhaustiveness remains open. |
| Eight-speed spectrum | Partial | All three displayed product families are classified and evaluated within those families, including both exceptional `s=1` values. All 17 displayed sporadic values are checked. The norm bound and exhaustive classification outside the families remain open. |
| Eleven-through-fourteen-runner equality | Partial | The displayed equality directions have their exact global values. Norm cutoffs and prime selection are checked under explicit smaller-dimensional runner bounds. Those bounds, modular exhaustiveness and uniqueness remain open. |

The full verification receipts are collected in [Lean verification checkpoints, part 1](lean-checkpoints-1.md), [Lean verification checkpoints, part 2](lean-checkpoints-2.md).

## Complete gamma-quotient theorem

[Read checkpoint](lean-checkpoints-1.md#complete-gamma-quotient-theorem).

## Complete Chow interlacing theorem

[Read checkpoint](lean-checkpoints-1.md#complete-chow-interlacing-theorem).

## Complete root-radius theorems

[Read checkpoint](lean-checkpoints-1.md#complete-root-radius-theorems).

## Formalizations of previously resolved results

[Read checkpoint](lean-checkpoints-1.md#formalizations-of-previously-resolved-results).

## War

[Read checkpoint](lean-checkpoints-1.md#war).

## Exact denominator certificates

[Read checkpoint](lean-checkpoints-1.md#exact-denominator-certificates).

## Complete Egyptian-fraction theorem

[Read checkpoint](lean-checkpoints-1.md#complete-egyptian-fraction-theorem).

## CUT Family B

[Read checkpoint](lean-checkpoints-1.md#cut-family-b).

## Reverse-solitaire dynamics

[Read checkpoint](lean-checkpoints-1.md#reverse-solitaire-dynamics).

## Exact loneliness certificates

[Read checkpoint](lean-checkpoints-1.md#exact-loneliness-certificates).

## Reproduce

[Read checkpoint](lean-checkpoints-1.md#reproduce).

## Validation receipt, 18 November 2026

[Read checkpoint](lean-checkpoints-1.md#validation-receipt-18-november-2026).

## Completed Batista checkpoint, 18 November 2026

[Read checkpoint](lean-checkpoints-1.md#completed-batista-checkpoint-18-november-2026).

## CUT automata foundations

[Read checkpoint](lean-checkpoints-1.md#cut-automata-foundations).

## Binary-semantics checkpoint, 18 November 2026

[Read checkpoint](lean-checkpoints-1.md#binary-semantics-checkpoint-18-november-2026).

## Complete padding and lower-value semantics

[Read checkpoint](lean-checkpoints-1.md#complete-padding-and-lower-value-semantics).

## Complete two-pile certificate

[Read checkpoint](lean-checkpoints-1.md#complete-two-pile-certificate).

## Numerical error languages

[Read checkpoint](lean-checkpoints-1.md#numerical-error-languages).

## Finite decision tests and paused continuation

[Read checkpoint](lean-checkpoints-1.md#finite-decision-tests-and-paused-continuation).

## Resumed campaign, 18 November 2026

[Read checkpoint](lean-checkpoints-1.md#resumed-campaign-18-november-2026).

## Complete general CUT decision test

[Read checkpoint](lean-checkpoints-1.md#complete-general-cut-decision-test).

## Checked analytic solitaire transfer

[Read checkpoint](lean-checkpoints-1.md#checked-analytic-solitaire-transfer).

## Complete symmetric four-point densities

[Read checkpoint](lean-checkpoints-1.md#complete-symmetric-four-point-densities).

## General finite CUT decision theorem

[Read checkpoint](lean-checkpoints-1.md#general-finite-cut-decision-theorem).

## Checked five-speed components

[Read checkpoint](lean-checkpoints-1.md#checked-five-speed-components).

## Local extension validation, 18 November 2026

[Read checkpoint](lean-checkpoints-1.md#local-extension-validation-18-november-2026).

## Exact density theorems

[Read checkpoint](lean-checkpoints-1.md#exact-density-theorems).

## Common loneliness interface

[Read checkpoint](lean-checkpoints-1.md#common-loneliness-interface).

## Rectangle combinatorial inputs

[Read checkpoint](lean-checkpoints-1.md#rectangle-combinatorial-inputs).

## Gap-five and gap-seven character classification

[Read checkpoint](lean-checkpoints-1.md#gap-five-and-gap-seven-character-classification).

## Complete Haralambis theorem, 18 November 2026

[Read checkpoint](lean-checkpoints-1.md#complete-haralambis-theorem-18-november-2026).

## Combined verified checkpoint, 18 November 2026

[Read checkpoint](lean-checkpoints-1.md#combined-verified-checkpoint-18-november-2026).

## Additive integration, 19 November 2026

[Read checkpoint](lean-checkpoints-1.md#additive-integration-19-november-2026).

## Complete distance-graph classifications, 18 November 2026

[Read checkpoint](lean-checkpoints-1.md#complete-distance-graph-classifications-18-november-2026).

## Rectangle components, 18 November 2026

[Read checkpoint](lean-checkpoints-1.md#rectangle-components-18-november-2026).

## Two-direction plane reduction

[Read checkpoint](lean-checkpoints-1.md#two-direction-plane-reduction).

## Complete Pham denominator result, 19 November 2026

[Read checkpoint](lean-checkpoints-1.md#complete-pham-denominator-result-19-november-2026).

## Checked finite Motzkin theorem, 19 November 2026

[Read checkpoint](lean-checkpoints-1.md#checked-finite-motzkin-theorem-19-november-2026).

## Pham and finite Motzkin integration receipt

[Read checkpoint](lean-checkpoints-1.md#pham-and-finite-motzkin-integration-receipt).

## Complete rectangle asymptotic, 19 November 2026

[Read checkpoint](lean-checkpoints-1.md#complete-rectangle-asymptotic-19-november-2026).

## Finite planes and coordinate cutoffs, 19 November 2026

[Read checkpoint](lean-checkpoints-1.md#finite-planes-and-coordinate-cutoffs-19-november-2026).

## Combined rectangle and plane integration, 19 November 2026

[Read checkpoint](lean-checkpoints-1.md#combined-rectangle-and-plane-integration-19-november-2026).

## Complete concrete CUT games, 19 November 2026

[Read checkpoint](lean-checkpoints-1.md#complete-concrete-cut-games-19-november-2026).

## Erdős 607 checked foundations, 19 November 2026

[Read checkpoint](lean-checkpoints-1.md#erdős-607-checked-foundations-19-november-2026).

## Hosted verification of the Pham/finite-Motzkin checkpoint

[Read checkpoint](lean-checkpoints-1.md#hosted-verification-of-the-phamfinite-motzkin-checkpoint).

## CUT and line-size foundation integration, 19 November 2026

[Read checkpoint](lean-checkpoints-1.md#cut-and-line-size-foundation-integration-19-november-2026).

## Graph theorem, runner families, and deterministic hyperplane registration

[Read checkpoint](lean-checkpoints-1.md#graph-theorem-runner-families-and-deterministic-hyperplane-registration).

## Concurrent registration union

[Read checkpoint](lean-checkpoints-1.md#concurrent-registration-union).

## Erdős 607 geometry and analytic profile, 19 November 2026

[Read checkpoint](lean-checkpoints-1.md#erdős-607-geometry-and-analytic-profile-19-november-2026).

## Complete four-speed gap and runner bound

[Read checkpoint](lean-checkpoints-1.md#complete-four-speed-gap-and-runner-bound).

## General compact Motzkin equality, 19 November 2026

[Read checkpoint](lean-checkpoints-1.md#general-compact-motzkin-equality-19-november-2026).

## Relation formulas, Euler correction, and finite tuple reconstruction

[Read checkpoint](lean-checkpoints-1.md#relation-formulas-euler-correction-and-finite-tuple-reconstruction).

## Exact generating function and cyclic Motzkin formulas, 19 November 2026

[Read checkpoint](lean-checkpoints-1.md#exact-generating-function-and-cyclic-motzkin-formulas-19-november-2026).

## Full hosted verification of the 397-module checkpoint

[Read checkpoint](lean-checkpoints-1.md#full-hosted-verification-of-the-397-module-checkpoint).

## Hosted replay of the four-speed integration snapshot

[Read checkpoint](lean-checkpoints-1.md#hosted-replay-of-the-four-speed-integration-snapshot).

## Five-speed finite certificate checkpoint, 19 November 2026

[Read checkpoint](lean-checkpoints-1.md#five-speed-finite-certificate-checkpoint-19-november-2026).

## Five-speed root candidate and component gates, 19 November 2026

[Read checkpoint](lean-checkpoints-1.md#five-speed-root-candidate-and-component-gates-19-november-2026).

## Frankl counting components — 19 November 2026

[Read checkpoint](lean-checkpoints-1.md#frankl-counting-components--19-november-2026).

## Frankl large-generator theorem — 19 November 2026

[Read checkpoint](lean-checkpoints-1.md#frankl-large-generator-theorem--19-november-2026).

## Hadamard automorphism arithmetic

[Read checkpoint](lean-checkpoints-1.md#hadamard-automorphism-arithmetic).

## Hadamard automorphism Fourier component

[Read checkpoint](lean-checkpoints-1.md#hadamard-automorphism-fourier-component).

## Hadamard automorphism permutation component

[Read checkpoint](lean-checkpoints-1.md#hadamard-automorphism-permutation-component).

## Hadamard quadratic field and class-order component

[Read checkpoint](lean-checkpoints-1.md#hadamard-quadratic-field-and-class-order-component).

## Hadamard cyclotomic norm obstruction

[Read checkpoint](lean-checkpoints-1.md#hadamard-cyclotomic-norm-obstruction).

## Complete Hadamard order-479 automorphism obstruction

[Read checkpoint](lean-checkpoints-1.md#complete-hadamard-order-479-automorphism-obstruction).

## Complete independent ideal-class norm obstruction

[Read checkpoint](lean-checkpoints-1.md#complete-independent-ideal-class-norm-obstruction).

## Complete quadratic integer model

[Read checkpoint](lean-checkpoints-1.md#complete-quadratic-integer-model).

## Frankl local certificate checkers — 19 November 2026

[Read checkpoint](lean-checkpoints-1.md#frankl-local-certificate-checkers--19-november-2026).

## Frankl FC and small cyclic components — 19 November 2026

[Read checkpoint](lean-checkpoints-1.md#frankl-fc-and-small-cyclic-components--19-november-2026).

## Frankl mask checker and exact domains — 19 November 2026

[Read checkpoint](lean-checkpoints-1.md#frankl-mask-checker-and-exact-domains--19-november-2026).

## Complete fixed-border multiplier and orbit bounds

[Read checkpoint](lean-checkpoints-1.md#complete-fixed-border-multiplier-and-orbit-bounds).

## Frankl cyclic assembly and weight helpers — 19 November 2026

[Read checkpoint](lean-checkpoints-1.md#frankl-cyclic-assembly-and-weight-helpers--19-november-2026).

## Complete sharp 95-vertex example and arbitrary-voltage normalization

[Read checkpoint](lean-checkpoints-1.md#complete-sharp-95-vertex-example-and-arbitrary-voltage-normalization).

## Fixed-border certificate transport

[Read checkpoint](lean-checkpoints-1.md#fixed-border-certificate-transport).

## Actual row normalization from compression shapes

[Read checkpoint](lean-checkpoints-1.md#actual-row-normalization-from-compression-shapes).

## Exact fixed character-window witness

[Read checkpoint](lean-checkpoints-1.md#exact-fixed-character-window-witness).

## Exact Motzkin evaluator and explicit rational intervals

[Read checkpoint](lean-checkpoints-1.md#exact-motzkin-evaluator-and-explicit-rational-intervals).

## Prime-257 minimum-pair-20 support certificate

[Read checkpoint](lean-checkpoints-1.md#prime-257-minimum-pair-20-support-certificate).

## Checked order-11 fiber component

[Read checkpoint](lean-checkpoints-1.md#checked-order-11-fiber-component).

## Complete universal abelian-cover cycle theorem

[Read checkpoint](lean-checkpoints-1.md#complete-universal-abelian-cover-cycle-theorem).

## Complete literal finite-border certificate

[Read checkpoint](lean-checkpoints-1.md#complete-literal-finite-border-certificate).

## Complete length-598 order-eleven obstruction

[Read checkpoint](lean-checkpoints-1.md#complete-length-598-order-eleven-obstruction).

## Complete two-difference Motzkin theorem

[Read checkpoint](lean-checkpoints-1.md#complete-two-difference-motzkin-theorem).

## Complete conditional fixed-border construction and fourteen patterns

[Read checkpoint](lean-checkpoints-1.md#complete-conditional-fixed-border-construction-and-fourteen-patterns).

## Checked length-1197 reduction to order 27

[Read checkpoint](lean-checkpoints-1.md#checked-length-1197-reduction-to-order-27).

### Exact receipts and registration

[Read checkpoint](lean-checkpoints-1.md#exact-receipts-and-registration).

## Complete Frankl high-girth frequency theorem

[Read checkpoint](lean-checkpoints-2.md#complete-frankl-high-girth-frequency-theorem).

## Complete Erdős 607 line-size asymptotic

[Read checkpoint](lean-checkpoints-2.md#complete-erdős-607-line-size-asymptotic).

## Actual Legendre-pair matrix and quotient transport

[Read checkpoint](lean-checkpoints-2.md#actual-legendre-pair-matrix-and-quotient-transport).

## Complete unrestricted two-speed insertion theorem

[Read checkpoint](lean-checkpoints-2.md#complete-unrestricted-two-speed-insertion-theorem).

## Six-speed spectrum: complete realization

[Read checkpoint](lean-checkpoints-2.md#six-speed-spectrum-complete-realization).

## Complete fixed-hyperplane theorem

[Read checkpoint](lean-checkpoints-2.md#complete-fixed-hyperplane-theorem).

## Conditional nine-through-thirteen speed norm reduction

[Read checkpoint](lean-checkpoints-2.md#conditional-nine-through-thirteen-speed-norm-reduction).

## Six-speed spectrum reduced fraction arithmetic

[Read checkpoint](lean-checkpoints-2.md#six-speed-spectrum-reduced-fraction-arithmetic).

### Six-speed sporadic values and denominator bounds

[Read checkpoint](lean-checkpoints-2.md#six-speed-sporadic-values-and-denominator-bounds).

### Seven- and eight-speed spectrum realizations and exact candidate bounds

[Read checkpoint](lean-checkpoints-2.md#seven--and-eight-speed-spectrum-realizations-and-exact-candidate-bounds).

## Five-runner lower-bound candidate

[Read checkpoint](lean-checkpoints-2.md#five-runner-lower-bound-candidate).

### Higher-speed triangle consequences under primitive classification

[Read checkpoint](lean-checkpoints-2.md#higher-speed-triangle-consequences-under-primitive-classification).

## Renault foundations and six-speed prime pilot, 19 November 2026

[Read checkpoint](lean-checkpoints-2.md#renault-foundations-and-six-speed-prime-pilot-19-november-2026).

## Critical seven-coordinate planes and large-norm family

[Read checkpoint](lean-checkpoints-2.md#critical-seven-coordinate-planes-and-large-norm-family).

### Accepted seven-speed low-gap input for the eight-coordinate argument

[Read checkpoint](lean-checkpoints-2.md#accepted-seven-speed-low-gap-input-for-the-eight-coordinate-argument).

### Accepted six-plane direction coverage and certificate chunk joins

[Read checkpoint](lean-checkpoints-2.md#accepted-six-plane-direction-coverage-and-certificate-chunk-joins).

### Six-speed norm geometry from an explicit plane gap

[Read checkpoint](lean-checkpoints-2.md#six-speed-norm-geometry-from-an-explicit-plane-gap).

## Product-plane integer speed bridge (2026-11-19)

[Read checkpoint](lean-checkpoints-2.md#product-plane-integer-speed-bridge-2026-11-19).

## Five-speed norm and prime avoidance, 19 November 2026

[Read checkpoint](lean-checkpoints-2.md#five-speed-norm-and-prime-avoidance-19-november-2026).

## Six-coordinate plane semantics (19 November 2026)

[Read checkpoint](lean-checkpoints-2.md#six-coordinate-plane-semantics-19-november-2026).

## Unconditional five-speed bound and primitive transport, 19 November 2026

[Read checkpoint](lean-checkpoints-2.md#unconditional-five-speed-bound-and-primitive-transport-19-november-2026).

## Six-speed finite-field prime-product reduction (2026-11-19)

[Read checkpoint](lean-checkpoints-2.md#six-speed-finite-field-prime-product-reduction-2026-11-19).

## Conditional gcd shift test (19 November 2026)

[Read checkpoint](lean-checkpoints-2.md#conditional-gcd-shift-test-19-november-2026).

### Six-speed first-cover support reduction: accepted component

[Read checkpoint](lean-checkpoints-2.md#six-speed-first-cover-support-reduction-accepted-component).

### Accepted six-plane membership-to-family bridge

[Read checkpoint](lean-checkpoints-2.md#accepted-six-plane-membership-to-family-bridge).

## Complete tight-five classification and independent finite lower bound (19 November 2026)

[Read checkpoint](lean-checkpoints-2.md#complete-tight-five-classification-and-independent-finite-lower-bound-19-november-2026).

## Modular support, unit orbits and literal binary lifts, 19 November 2026

[Read checkpoint](lean-checkpoints-2.md#modular-support-unit-orbits-and-literal-binary-lifts-19-november-2026).

## Seven-speed norm and reduced prime sets, 19 November 2026

[Read checkpoint](lean-checkpoints-2.md#seven-speed-norm-and-reduced-prime-sets-19-november-2026).

## Order-nine automorphism subgroups and orbits

[Read checkpoint](lean-checkpoints-2.md#order-nine-automorphism-subgroups-and-orbits).

## Initial cut pilot and prime-251 binary lifts, 19 November 2026

[Read checkpoint](lean-checkpoints-2.md#initial-cut-pilot-and-prime-251-binary-lifts-19-november-2026).

## Rational integer-point lattices and six-speed norm components

[Read checkpoint](lean-checkpoints-2.md#rational-integer-point-lattices-and-six-speed-norm-components).

## Prime filtering and proved runner classes, 19 November 2026

[Read checkpoint](lean-checkpoints-2.md#prime-filtering-and-proved-runner-classes-19-november-2026).

## Conditional two-parameter radius estimate

[Read checkpoint](lean-checkpoints-2.md#conditional-two-parameter-radius-estimate).

## Six-speed norm bounds with the four-speed input discharged

[Read checkpoint](lean-checkpoints-2.md#six-speed-norm-bounds-with-the-four-speed-input-discharged).

## Seven-coordinate implications with the five-speed input discharged

[Read checkpoint](lean-checkpoints-2.md#seven-coordinate-implications-with-the-five-speed-input-discharged).

## Four-input prime filtering, 19 November 2026

[Read checkpoint](lean-checkpoints-2.md#four-input-prime-filtering-19-november-2026).

## Li coefficient-sign counterexample

[Read checkpoint](lean-checkpoints-2.md#li-coefficient-sign-counterexample).

## Actual rational-lattice quotient index

[Read checkpoint](lean-checkpoints-2.md#actual-rational-lattice-quotient-index).

## Complete Wright log-concavity disproof

[Read checkpoint](lean-checkpoints-2.md#complete-wright-log-concavity-disproof).

## Fan–Tringali’s power-monoid length-set conjecture

[Read checkpoint](lean-checkpoints-2.md#fantringalis-power-monoid-length-set-conjecture).

## Ulas’s disjoint-block square-product conjecture

[Read checkpoint](lean-checkpoints-2.md#ulass-disjoint-block-square-product-conjecture).

## Gravgaard–Lee’s mixed upper/lower Lüroth conjecture

[Read checkpoint](lean-checkpoints-2.md#gravgaardlees-mixed-upperlower-lüroth-conjecture).

## Hartke–Stolee–West–Yancey matching-excess conjecture

[Read checkpoint](lean-checkpoints-2.md#hartkestoleewestyancey-matching-excess-conjecture).
