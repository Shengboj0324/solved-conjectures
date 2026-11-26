# History

## 2026-11-26 — Fiscus–Hurlbert–Myzelev–Pence grid conjecture

The first player can force a win on the 14-vertex ladder, contradicting the conjecture for all even rectangular grids. The written strategy matches every possible reply, with an independent exact minimax check. [Proof](results/fiscus-grid-game/PROOF.md) · [Audit](results/fiscus-grid-game/AUDIT.md) · [Issue #791](https://github.com/1337isnot1337/solved-conjectures/issues/791).

## 2026-11-26 — Caiolo–Ferroni–Hoster kernel-level Lean statement

A new [Lean module](lean/Conjectures/CaioloFerroniHosterKernelLink.lean) proves that the rank-five chain formulas of the existing counterexample equal the recursive dual Chow invariants of the rank-threshold development. Those invariants were already identified with the CFH kernel definitions. The explicit bound q ≥ 17 now holds for the kernel-defined dual Chow and dual right augmented Chow functions. The [publication audit](results/caiolo-ferroni-hoster/AUDIT.md) no longer calls the result non-Lean-verified. The verification level, attribution and conjecture count are unchanged. [Receipt](docs/verification/cfh-kernel-link-20261126/receipt.json)

## 2026-11-26 — Erdős–Gyárfás point-degree spectrum conjecture

Erdős and Gyárfás asked whether abstract linear spaces can realize all but a square-root number of the possible point degrees. Counting pairs between points of low and high degree proves that at least one seventeenth of the order is missing. The same bound answers their separate question about real planar point sets. [Proof](results/erdos-gyarfas-point-degree-spectrum/PROOF.md) · [Source and independent review](results/erdos-gyarfas-point-degree-spectrum/AUDIT.md).

## 2026-11-26 — Wang–Yang's Fuss–Narayana conjecture

A product determinant and two triangular positivity criteria prove Wang and Yang's 2018 Conjecture 4.1 for every Fuss parameter. [Proof](results/wang-yang-fuss-narayana/proof.md) · [Source audit](results/wang-yang-fuss-narayana/sources.md) · [Issue 98](https://github.com/1337isnot1337/solved-conjectures/issues/98)

## Forward insertions in the three-block circular-index construction

Lean verifies the one- and three-block exclusions for all labelled small forward insertions, the classification of two-interval supports, connectivity of the infinite family, and both partial-block graphs with their exact indices. [Theorems and receipts](results/circular-index-upper-half-delta-3-mod-4/FORMALIZATION.md).

## 2026-11-26 — Gyárfás’s planar degree-repetition problem

Gyárfás asked whether a real planar point set can have every point degree repeated at most twice. Rational coordinates now give such a set at every order at least 16 and yield asymptotically three quarters as many distinct degrees as points. [Proof](results/gyarfas-planar-degree-repetition/PROOF.md) · [Source and independent review](results/gyarfas-planar-degree-repetition/AUDIT.md).

For every order from 16, Lean constructs noncollinear rational points in the real plane, proves optimal maximum degree multiplicity two and determines the entire interval of distinct degrees. [Theorems and receipts](results/gyarfas-planar-degree-repetition/FORMALIZATION.md).

## 2026-11-26 — Verify the two truncated-square covering comparisons

Lean proves the exact Lebesgue areas and maximal four-shape covering scales of the parallelogram and rational pentagon, and the strict comparisons with the source’s trapezoid formula. The first comparison also holds near the boundary for every first truncation leg. Identifying this scale with symplectic capacity and proving the full strict bound for every convex body remain open in Lean. [Proof and receipt](results/meylender-thalmaier-truncated-square/FORMALIZATION.md).

## 2026-11-26 — Verify the circular index examples for every maximum degree from eight

For every integer maximum degree from eight, Lean constructs a finite simple graph whose real circular chromatic index is strictly between that degree plus one half and that degree plus one. The proof combines the two insertion families, regular circulants and tomdif’s seven exceptional examples. The three-block theorem gives the degree of every labelled vertex for every permitted packing. [Full theorem and verification](results/circular-index-upper-half-remaining-deltas/FORMALIZATION.md).

## 2026-11-26 — Prove the type B Poincaré real-rootedness conjecture

A pole-cancelling differential identity and a weighted Rolle argument prove real-rootedness, simplicity and strict consecutive-rank interlacing for every rank. [Proof and audit](results/ferroni-pagaria-vecchi-type-b/).

## 2026-11-26 — Verify all seventeen stored nonregular circulants

Lean verifies the maximum degree and the exact real circular chromatic index for every nonregular graph in Section 7.3. An independent table comparison matches all 19,649 edge colours to the original certificates. The two standard replays each checked 27 project modules, 455 declarations, 327 theorem declarations, 70 private declarations and all 17 required endpoints. [Proof and original data](results/circular-index-upper-half-circulants/FORMALIZATION.md).

## 2026-11-26 — Verify both plane-partition polynomial conjectures in Lean

Lean proves the strict Turán inequality for every index at least 12 and every real parameter at least 1. The consecutive roots strictly decrease from index 1 when the parameter exceeds 5 and from index 6 when it is at least 1. [Turán proof](results/heim-neuhauser-troeger-plane-partition-turan/FORMALIZATION.md) · [Root inequalities](results/heim-neuhauser-plane-partition-polynomization/FORMALIZATION.md).

## 2026-11-26 — Verify the normal occurrence intervals in Mazák–Zrubák

Lean verifies Lemma 5(3) of the written proof for the literal order, including the exact consecutive-position transitions and singleton intervals at special columns. [Scope and receipt](results/circular-index-complete-minus-edge/FORMALIZATION.md).

## 2026-11-26 — Verify the paired special columns and literal normal starts

Lean verifies the first two column assertions in Step 5 of the Mazák–Zrubák proof. The row-interval structure and final index equality remain separate. [Scope and receipt](results/circular-index-complete-minus-edge/FORMALIZATION.md).

## 2026-11-26 — Verify the Gaussian-profile deviation rate

Lean checks the exact quadratic and cubic rate coefficients and unique Legendre tilt. The arithmetic large-deviation transfer remains separate. [Scope and receipt](results/pomerance-sarkozy-fluctuations/FORMALIZATION.md).

## 2026-11-26 — Verify both Cyrusian–Kaplan ordinarization conclusions

Lean verifies exact quasipolynomiality and eventual strict increase for the literal fixed-ordinarization numerical-semigroup count. This is not the all-genus Bras-Amorós conjecture. [Scope and receipt](results/cyrusian-kaplan-ordinarization/FORMALIZATION.md).

## 2026-11-26 — Verify the unbounded one- and two-block circular index constructions

For every integer parameter of at least six, Lean constructs both simple graphs with the prescribed order, maximum degree and exact circular chromatic index. It proves the four finite cases of Proposition 2 and the three degree ranges of Corollary 3. Lean also proves that the stated two-matching base has no solution at parameters three, four and five. [Theorems, source data and verification](results/circular-index-upper-half-delta-2-mod-4/FORMALIZATION.md).

## 2026-11-26 — Verify the exact Cyrusian–Kaplan quasipolynomial

Lean proves all-positive-genus quasipolynomiality and exact degree in every residue for each fixed positive ordinarization number. The entry's separate eventual monotonicity corollary is outside this checkpoint. [Scope and receipt](results/cyrusian-kaplan-ordinarization/FORMALIZATION.md).

## 2026-11-26 — Verify literal deleted-edge run rigidity in Lean

Step 4 of @aadrianvv’s proof of the Mazák–Zrubák conjecture is now checked on the actual edge order. The table and final index equality remain separate. [Scope and receipt](results/circular-index-complete-minus-edge/FORMALIZATION.md).

## 2026-11-26 — Verify 43 finite circular-index examples in Lean

Lean checks 43 finite simple graphs from the published colouring records. All 32 complete graphs with deletions have rigorous density and colouring bounds. Eleven insertion graphs have exact circular index equal to the maximum degree plus two thirds. [Colourings, checks and receipt](results/circular-index-complete-minus-edges/FORMALIZATION.md).

## 2026-11-26 — Verify the disjoint rational triangulation of ordinarization cells

Lean constructs rational open simplices for the actual sign fibres by induction over their strict rows. Their exact lattice summation and eventual monotonicity remain separate. [Scope and receipt](results/cyrusian-kaplan-ordinarization/FORMALIZATION.md).

## 2026-11-26 — Verify both bicyclic facet maxima

Lean proves the bicyclic bound with attainment and characterizes every theta maximizer up to permuting its path lengths. [Proof and verification](results/braun-bruegge-bicyclic-facets/FORMALIZATION.md).

## 2026-11-26 — Verify rational vertices of the actual ordinarization cells

Lean checks that the compact weak sign cells are finite convex hulls of rational vertices. Their disjoint rational triangulation and the correction estimate remain. [Scope and receipt](results/cyrusian-kaplan-ordinarization/FORMALIZATION.md).

## 2026-11-26 — Verify the ordinarization sign arrangement and lattice

Lean checks the literal disjoint strata, exact relative interiors, and primitive integer hyperplane lattices. The open Ehrhart count and asymptotic correction remain. [Scope and receipts](results/cyrusian-kaplan-ordinarization/FORMALIZATION.md).

## 2026-11-26 — Verify the open-simplex lattice count

Lean checks the exact rational quasipolynomial on every positive lattice height in an injective integral ray chart. Applying this to the actual ordinarization sign strata remains open. [Scope and receipt](results/cyrusian-kaplan-ordinarization/FORMALIZATION.md).

## 2026-11-26 — Verify the ordinarization count lower bounds

Lean checks both baseline Pascal increments, the off-hyperplane comparison and a full-dimensional box of actual encodings. The full Ehrhart and monotonicity statements remain. [Scope and receipts](results/cyrusian-kaplan-ordinarization/FORMALIZATION.md).

## 2026-11-26 — Verify the exact ordinarization encoding

Lean checks the literal semigroup count in the fixed normalized region and the binomial baseline. The Ehrhart and monotonicity claims remain. [Scope and receipt](results/cyrusian-kaplan-ordinarization/FORMALIZATION.md).

## 2026-11-26 — Restore the verified complete-minus-one-edge checkpoint

The precise Steps 1–3 Lean reduction is registered on main. The final equality is still outside the verified scope. [Proof and both receipts](results/circular-index-complete-minus-edge/FORMALIZATION.md).

## 2026-11-26 — Complete the Wilf-module formalization

Lean verifies the normalized gap and module-threshold questions of Almirón and Moyano-Fernández, including the exact dependence on both generators and comparison at a fixed multiplicity. [Proof and receipt](results/almiron-moyano-wilf-module-questions/LEAN.md).

## 2026-11-26 — Verify the shifted Lonely Runner certificates

Lean proves Zhang’s strict bound for 18 through 57 runners using aadrianvv’s and tomdif’s published configurations. Each recorded maximum is attained. [Proof and verification](results/shifted-lonely-runner-counterexamples/FORMALIZATION.md).

## 2026-11-26 — Verify exponential event-bound transfers

Lean checks both exponential rate inequalities under superexponentially
small errors, including zero-probability events.
[Proof scope and receipt](results/pomerance-sarkozy-fluctuations/FORMALIZATION.md).

## 2026-11-26 — Verify exact finite Bernoulli tilting

Lean checks normalization, the tilted joint atom weight, and
finite-event upper and lower bounds.
[Proof scope and receipt](results/pomerance-sarkozy-fluctuations/FORMALIZATION.md).

## 2026-11-26 — Complete Lean formalization of Burstein’s A218225 enumeration conjecture

Lean verifies literal equinumerosity of `X = Av(2134, 42153, 24153)` and `Y = Av(2143, 42135, 24135)` for every length `n : ℕ`, and proves that their common nonempty generating series is the unique zero-constant-term solution to `P = (1 + P)(x + (1 - x)P^2)`. The six-module closure passed strict compilation, the 815-declaration all-owned axiom audit, and stock-kernel replay. [Lean scope and receipt](results/burstein-a218225-enumeration/FORMALIZATION.md).

## 2026-11-26 — Verify pointwise rare-deviation cumulant estimates

Lean checks the tilted Bernoulli derivatives and the exact
variance-weighted cubic Taylor estimate.
[Proof scope and receipt](results/pomerance-sarkozy-fluctuations/FORMALIZATION.md).

## 2026-11-26 — Verify how finite marginals determine the process limit

Lean verifies the finite-marginal uniqueness and tightness-to-limit
argument for Pomerance–Sárközy’s process.
[Proof scope and receipt](results/pomerance-sarkozy-fluctuations/FORMALIZATION.md).

## 2026-11-26 — Verify a process tightness criterion for Pomerance–Sárközy

Lean checks the base-32 grid probability bound, the uniform
continuous-path modulus, and the tightness criterion.
[Proof scope and receipt](results/pomerance-sarkozy-fluctuations/FORMALIZATION.md).

## 2026-11-26 — Verify the literal Schröder tree enumeration

Lean splits each nonleaf tree at its first child, derives the
counting recurrence, and identifies the count at each positive
leaf size with Mathlib’s small Schröder number.
[Scope and receipt](results/separable-derangements-limit/FORMALIZATION.md).

## 2026-11-26 — Verify critical spine weights and conditional limit steps

Lean checks normalization of the offspring and child-index weights,
the exact factorization on finite spine records, and the conditional
miss-product and finite-instance transfer arguments.
[Scope and receipts](results/separable-derangements-limit/FORMALIZATION.md).

## 2026-11-26 — Verify the bounded array law for Pomerance–Sárközy’s process

Lean verifies the weak Gaussian limit for independently sampled centered
bounded rows with a convergent normalized variance, including the zero
variance case. [Proof scope and receipt](results/pomerance-sarkozy-fluctuations/FORMALIZATION.md).

## 2026-11-26 — Verify finite spine-record counts for separable derangements

Lean checks that same-diagonal points first split at a direct-sum
node. A fixed spine prefix with sufficiently many leaves has exactly
the same count as the trees available at its terminal node.
[Scope and receipt](results/separable-derangements-limit/FORMALIZATION.md).

## 2026-11-25 — Verify the weighted Tom–Vailaya path tests

Lean proves independence for the path test rows used to compare
transfer matrices. It checks the polynomial evaluation argument at
$q=1$ and the determinant lift to the rational function field.
[Scope and receipt](results/tom-vailaya-weighted-trace/FORMALIZATION.md).

## 2026-11-26 — Verify the separable derangement displacement identities

Lean checks the actual diagonal point counts in direct and skew sums
and proves that a skew sum’s diagonal meets at most one child.
[Scope and receipt](results/separable-derangements-limit/FORMALIZATION.md).

## 2026-11-25 — Verify Tom–Vailaya’s color basis and endpoint reflection

Lean proves invertibility of the symbolic color basis and derives the
literal closure trace from agreement of the weighted path tests. It also
checks the reversal of the endpoint closure and its color variables.
[Scope and receipts](results/tom-vailaya-weighted-trace/FORMALIZATION.md).

## 2026-11-25 — Verify the weighted Tom–Vailaya path column identities

Lean checks the generating identity, the coefficient recurrence for
weighted path transfer, the sums of the color columns, and the
finite-color cutoff.
[Scope and receipt](results/tom-vailaya-weighted-trace/FORMALIZATION.md).

## 2026-11-25 — Verify endpoint gluing in Tom–Vailaya’s proof

Lean proves the ordered product formula for the color matrices of
literal glued graphs by matching the shared vertex color and factoring
the weights.
[Scope and receipt](results/tom-vailaya-weighted-trace/FORMALIZATION.md).

## 2026-11-26 — Verify Shumyatsky’s exact conclusion under four simple-group inputs

Lean assembles the original statement for every finite group by
induction on the group order, with four external finite-simple-group
results stated as explicit premises.
[Scope and receipt](results/shumyatsky-conjugate-prime-spectrum/FORMALIZATION.md).

## 2026-11-26 — Verify the socle action in Shumyatsky’s multifactor lift

The permutation action on the actual simple factors descends to the
socle quotient. Lean checks the required transitivity and transports
the conditional multifactor lift back to the actual subgroup.
[Scope and receipt](results/shumyatsky-conjugate-prime-spectrum/FORMALIZATION.md).

## 2026-11-25 — Verify the color transfer trace in Tom–Vailaya’s proof

Lean verifies the ascent-weighted finite-color trace of actual endpoint
closure, including repeated directed arcs, loop vanishing and the
two-vertex path-edge matrix.
[Scope and receipt](results/tom-vailaya-weighted-trace/FORMALIZATION.md).

## 2026-11-25 — Verify Pomerance–Sárközy's finite arithmetic-to-Poisson event bound

Lean checks the finite uniform shifted arithmetic count law against the
independent joint Poisson count law, for every event of the vector.
[Scope and receipt](results/pomerance-sarkozy-fluctuations/FORMALIZATION.md).

## 2026-11-26 — Verify Gaschütz’s finite lifting lemma

Lean proves the lift-count invariant for finite generating tuples and
the ordered-pair corollary used in Shumyatsky’s proof.
[Scope and receipt](results/shumyatsky-conjugate-prime-spectrum/FORMALIZATION.md).

## 2026-11-26 — Verify Shumyatsky’s actual single-factor lift

Lean checks that the outer action factors through the socle quotient,
then carries out the inner adjustments under the explicit
almost-simple automorphism and generation hypotheses.
[Scope and receipt](results/shumyatsky-conjugate-prime-spectrum/FORMALIZATION.md).

## 2026-11-25 — Verify shifted-tail inputs for Pomerance–Sárközy’s process

Lean checks the shifted integer tail-product reindexing and the moving
positive-part expectation under weak convergence and bounded second
moments. [Scope and receipt](results/pomerance-sarkozy-fluctuations/FORMALIZATION.md).

## 2026-11-26 — Verify the Hall and coprime-complement steps in Shumyatsky’s proof

Lean constructs the required subgroup of a solvable quotient. It
verifies the coprime complement and the resulting cyclicity under
the coprime-automorphism hypothesis.
[Scope and receipt](results/shumyatsky-conjugate-prime-spectrum/FORMALIZATION.md).

## 2026-11-25 — Verify Shumyatsky’s transitive simple factors

Lean realizes each nonabelian minimal normal subgroup as a direct
power of a nonabelian simple group, with the actual coordinate factors
forming one orbit under ambient conjugation.
[Scope and receipt](results/shumyatsky-conjugate-prime-spectrum/FORMALIZATION.md).

## 2026-11-25 — Verify Shumyatsky’s actual socle quotient

Lean proves that the socle is the direct product of the minimal
normal subgroups when all are nonabelian, and applies the conditional
simultaneous lift to this quotient.
[Scope and receipt](results/shumyatsky-conjugate-prime-spectrum/FORMALIZATION.md).

## 2026-11-25 — Verify the Bernoulli-array Fourier estimate for Pomerance–Sárközy

Lean checks the quantitative finite product error and the general normal
limit for rows of non-identical Bernoulli coordinates.
[Scope and receipt](results/pomerance-sarkozy-fluctuations/FORMALIZATION.md).

## 2026-11-25 — Verify the Poisson difference limit for Pomerance–Sárközy

Lean checks the weak limit of the exact independent Poisson difference
on its square-root scale. [Scope and receipt](results/pomerance-sarkozy-fluctuations/FORMALIZATION.md).

## 2026-11-25 — Verify the reciprocal-prime input for Pomerance–Sárközy

Lean verifies the bounded-error reciprocal-prime estimate using exact
Mangoldt counts and Abel summation.
[Scope and receipt](results/pomerance-sarkozy-fluctuations/FORMALIZATION.md).

## 2026-11-25 — Verify the abelian reduction and cyclic quotient normalization

Lean proves the required abelian complement conjugacy and reduces the
original statement by quotient order. It also verifies the prescribed
quotient images of an existing conjugate generating pair.
[Scope and receipts](results/shumyatsky-conjugate-prime-spectrum/FORMALIZATION.md).

## 2026-11-25 — Verify the simultaneous and prime-power kernel lifts

Lean combines the adjustments on commuting normal factors and checks
the prime-power kernel lift under the complement-conjugacy hypothesis.
[Scope and receipts](results/shumyatsky-conjugate-prime-spectrum/FORMALIZATION.md).

## 2026-11-25 — Verify Shumyatsky’s conditional multifactor lift

Lean completes the reserved return labels and constructs a conjugate
pair in the prescribed inner cosets. The multifactor prime-spectrum
lift takes the two-generator lifting property as an explicit hypothesis.
[Scope and receipts](results/shumyatsky-conjugate-prime-spectrum/FORMALIZATION.md).

## 2026-11-25 — Verify independent closed-word labels in Shumyatsky’s lift

Lean constructs the two rooted words from the directed tree moves
and realizes any two compatible labels independently.
[Scope and receipts](results/shumyatsky-conjugate-prime-spectrum/FORMALIZATION.md).

## 2026-11-25 — Verify the two available directed moves in Shumyatsky’s lift

Lean selects directed tree representatives and one unused return
move in every second cycle, with two further nontree moves available.
[Scope and receipts](results/shumyatsky-conjugate-prime-spectrum/FORMALIZATION.md).

## 2026-11-25 — Verify the permutation cycles and spanning tree in Shumyatsky’s lift

Lean constructs the actual indexed cycles and a spanning tree preserving
all cut-cycle paths. Directed representatives and independent labels remain.
[Scope and receipts](results/shumyatsky-conjugate-prime-spectrum/FORMALIZATION.md).

## 2026-11-25 — Verify cyclic gluing and the factor-stabilizer prime transfer

Lean checks the actual product conjugator from the paired cycle data
and the prime-spectrum transfer from two closed words whose factor
labels generate the inner automorphisms.
[Scope and receipts](results/shumyatsky-conjugate-prime-spectrum/FORMALIZATION.md).

## 2026-11-25 — Verify Pomerance–Sárközy's joint Poisson count law

Lean verifies the exact independent Poisson sum law, the countable
pushforward bound and the Poisson moments.
[Scope and receipt](results/pomerance-sarkozy-fluctuations/FORMALIZATION.md).

## 2026-11-25 — Verify Shumyatsky’s simple factors and closed-walk label products

Lean proves that automorphisms permute the minimal normal coordinate
factors and checks the restriction of a closed word to its base factor.
[Scope and receipts](results/shumyatsky-conjugate-prime-spectrum/FORMALIZATION.md).

## 2026-11-25 — Verify Pomerance–Sárközy's distribution comparisons

Lean verifies the categorical-to-Bernoulli and Bernoulli-to-Poisson
bounds, including finite products of the actual probability laws.
[Scope and receipt](results/pomerance-sarkozy-fluctuations/FORMALIZATION.md).

## 2026-11-25 — Verify the factor automorphisms in Shumyatsky’s lift

Lean reconstructs the action on the actual direct product, checks the
conjugacy relation, and identifies right cosets of inner automorphisms.
[Scope and receipts](results/shumyatsky-conjugate-prime-spectrum/FORMALIZATION.md).

## 2026-11-25 — Verify Pomerance–Sárközy's threshold identities

Lean verifies the near-threshold expectation bound and the exact
tail-product reindexing. [Scope and receipt](results/pomerance-sarkozy-fluctuations/FORMALIZATION.md).

## 2026-11-25 — Verify Shumyatsky’s prime-spectrum reduction and cycle closure

Lean verifies the cardinality steps and the conjugate-cycle equations
in aadrianvv’s written contribution. The result is partially formalized.
[Scope and receipts](results/shumyatsky-conjugate-prime-spectrum/FORMALIZATION.md).

## 2026-11-25 — Verify the order-thirteen recurrence for A189281

Lean proves that the alternate operator annihilates the actual
permutation count at every natural index. Its polynomial parity
certificates and four initial indices all transfer to the count.
[Scope and combined receipt](results/kauers-koutschan-recurrence/FORMALIZATION.md).

## 2026-11-25 — Verify Kauers–Koutschan Conjecture 10 in full

Lean identifies the exact forbidden-rise count with the sixteen-mask
derangement sum and proves the source order-eight recurrence at every
natural index.
[Scope and complete receipt](results/kauers-koutschan-recurrence/FORMALIZATION.md).

## 2026-11-25 — Verify the Kauers–Koutschan column series and Schur moment

Lean checks the composition reindexing of the original count, the formal
signed column series, and the bivariate Schur moment as a derangement
divided difference. The final coefficient extraction remains.
[Scope and receipts](results/kauers-koutschan-recurrence/FORMALIZATION.md).

## 2026-11-25 — Verify the Kauers–Koutschan signed block expansion

Lean proves the exact factorial count of legal block orders for each
selected adjacency set, and the signed expansion of the original
permutation count.
[Scope and receipt](results/kauers-koutschan-recurrence/FORMALIZATION.md).

## 2026-11-25 — Verify the Kauers–Koutschan finite-sum recurrence

Lean proves the exact finite sum satisfies the original order-eight
operator at every index and verifies inclusion–exclusion for the actual
permutations. The equality between the two counts remains.
[Scope and receipt](results/kauers-koutschan-recurrence/FORMALIZATION.md).

## 2026-11-25 — Verify Kauers–Koutschan's divided sums in Lean

Lean checks the all-index derangement divided-sum recurrence and shifted
cutoff identity, alongside the recovered coefficient certificate from
PR #281. The permutation-count and coefficient evaluation bridges remain.
[Scope and receipts](results/kauers-koutschan-recurrence/FORMALIZATION.md).

## 2026-11-25 — Verify Pomerance–Sárközy's finite-window comparison

Lean verifies the quantitative total-variation bound between the exact
arithmetic and independent residue laws.
[Scope and receipt](results/pomerance-sarkozy-fluctuations/FORMALIZATION.md).

## 2026-11-25 — Verify Pomerance–Sárközy's CRT inclusion probabilities

Lean verifies the exact shifted residue count, independent product
model and uniform inclusion-probability error.
[Scope and receipt](results/pomerance-sarkozy-fluctuations/FORMALIZATION.md).

## 2026-11-25 — Check Pomerance–Sárközy's exact finite prime tails in Lean

Lean verifies the literal exceptional-offset count, threshold comparison
and finite factorial bound using distinct prime-factor witnesses.
[Scope and receipt](results/pomerance-sarkozy-fluctuations/FORMALIZATION.md).

## 2026-11-25 — Verify Novelli–Thibon's Schur determinant and hook coefficients

Lean proves the actual Jacobi–Trudi/bialternant bridge, including
zero-row padding. It then derives the exact hook formula from the
source's stable ordinary Schur-expansion premise.
[Scope and receipt](results/novelli-thibon/FORMALIZATION.md).

## 2026-11-25 — Verify Novelli–Thibon's virtual alphabet interpolation

Lean counts the actual finite fundamental words, carries out the
negative-multiplicity continuation and derives the literal source
cell product from that same interpolation polynomial.
[Scope and receipt](results/novelli-thibon/FORMALIZATION.md).

## 2026-11-25 — Verify Novelli–Thibon's signed hook cell product

Lean evaluates the original graph sum in the signed fundamental
alphabet, computes the residual elementary coefficients, and checks
the hook and nonhook specialized determinants.
[Scope and receipt](results/novelli-thibon/FORMALIZATION.md).

## 2026-11-25 — Verify Novelli–Thibon's source graph-to-Laurent monomial certificate

Lean checks the original finite commutative graph sum against a
genuine Laurent polynomial and proves its signed Schur coordinate
monomial product. The adjacent hook claim is still open in Lean.
[Scope and receipt](results/novelli-thibon/FORMALIZATION.md).

## 2026-11-25 — Verify Novelli–Thibon's standard tableaux and normalized monomial product

Lean proves the standard-tableau bijection and the exact signed
monomial product for the normalized finite filling model.
[Scope and receipt](results/novelli-thibon/FORMALIZATION.md).

## 2026-11-25 — Verify Novelli–Thibon's Pieri diagram-chain extraction

Lean proves the signed alternant recurrence, the vertical two-box
start, and the Schur first moments in terms of literal diagram chains.
[Scope and receipt](results/novelli-thibon/FORMALIZATION.md).

## 2026-11-25 — Check Novelli–Thibon's diagram counts and first-order formula

Lean proves the optional-edge cancellation, the literal row and leg
counts, and the full dual-number formula for normalized fillings.
[Scope and receipt](results/novelli-thibon/FORMALIZATION.md).

## 2026-11-25 — Check Novelli–Thibon's universal finite-alphabet comparison identity

Lean verifies stable standardization, the fundamental word fibers,
and the exact weighted linear response for every finite alphabet.
[Scope and receipt](results/novelli-thibon/FORMALIZATION.md).

## 2026-11-25 — Complete Lean verification of González D’León–Wachs’s equal-variable result

Lean verifies the boundary color formulas, the printed three-color
example, strict coefficient log-concavity across all positive color
counts, and the complete real-root multiset.
[Scope and receipts](results/gonzalez-dleon-wachs-complete-graphs/FORMALIZATION.md).

## 2026-11-25 — Verify the actual Gamma expectation and real-zero count

Lean identifies the moments with an actual shifted sum of independent
Gamma laws and checks the complete-graph real-zero theorem, including
the simple-root bracket in odd degree.
[Scope and receipt](results/gonzalez-dleon-wachs-complete-graphs/FORMALIZATION.md).

## 2026-11-25 — Verify positive Laguerre roots and strict coefficient log-concavity

Lean verifies all Laguerre roots as distinct and positive, removes the
formal moment factorization input, and proves that the signed rank
coefficients are strictly log-concave for at least two equal colors.
[Scope and receipts](results/gonzalez-dleon-wachs-complete-graphs/FORMALIZATION.md).

## 2026-11-25 — Verify the literal complete-graph Laguerre formula

Lean proves the weighted labeled exponential formula and formal
Lagrange inversion, and connects the actual recursive Möbius
polynomial to the exact Laguerre formula for all nonempty complete
graphs with at least two equal variables.
[Scope and receipt](results/gonzalez-dleon-wachs-complete-graphs/FORMALIZATION.md).

## 2026-11-25 — Verify the finite one-block Möbius recurrence by size

Lean transports the literal weighted lower intervals to canonical
vertex sets and verifies the exact finite recurrence and characteristic
sum in terms of their block sizes.
[Scope and receipt](results/gonzalez-dleon-wachs-complete-graphs/FORMALIZATION.md).

## 2026-11-25 — Factor the literal weighted Möbius values over blocks

Lean constructs the actual lower interval as a product of its labeled
block intervals and proves the ordinary-fibre Möbius sum factors.
[Scope and receipt](results/gonzalez-dleon-wachs-complete-graphs/FORMALIZATION.md).

## 2026-11-25 — Check literal one-block weighted Möbius cancellation

Lean counts actual one-block extensions and groups the resulting Möbius
cancellation by ordinary partitions. This checks a finite recurrence step,
not the remaining EGF/Lagrange bridge.
[Scope and receipt](results/gonzalez-dleon-wachs-complete-graphs/FORMALIZATION.md).

## 2026-11-25 — Bound the Lassalle finite-row checks in the aggregate build

Lean checks rows 31 through 42 separately and combines them to retain
the original theorem through row 53 under the pinned memory limit.
[Scope and receipts](results/defant-engen-miller-lassalle/FORMALIZATION.md).

## 2026-11-25 — Verify all Lassalle base rows and the exact conditional theorem

Lean checks all 53 finite quotient rows and proves a zero in the rational
Bessel bracket. The original conjecture reduces to the actual permutation-count
bridge and classical Bessel product data.
[Scope and receipts](results/defant-engen-miller-lassalle/FORMALIZATION.md).

## 2026-11-25 — Formalize the literal weighted complete-graph Möbius polynomial

Lean checks the finite weighted bond order, rank and recursive Möbius
values. The literal polynomial reduces to the verified Laguerre
expression through the explicit EGF/Lagrange input.
[Scope and receipts](results/gonzalez-dleon-wachs-complete-graphs/FORMALIZATION.md).

## 2026-11-25 — Verify the complete-graph Laguerre formal-series calculation

Lean checks the actual equal-variable homogeneous coefficients and the
formal Laguerre and Gamma moment identities. This checkpoint keeps the
weighted bond-poset bridge and the root and probability inputs separate.
[Scope and receipt](results/gonzalez-dleon-wachs-complete-graphs/FORMALIZATION.md).

## 2026-11-25 — Verify the Lassalle approximation estimate in Lean

Lean verifies the normalized coefficient expansion, discrete Bernstein
differences, and all truncation-error bounds. The remaining analytic
input is the specified Bessel-product decomposition; the literal
permutation-count bridge remains separate.
[Scope and receipts](results/defant-engen-miller-lassalle/FORMALIZATION.md).

## 2026-11-25 — Verify the Lassalle interval certificate in Lean

Lean checks sound directed rounding, all 205 bisection boxes, and the
eventual determinant argument conditional on the analytic approximation.
The literal permutation-count formulation is separate from the checked
coefficient model.
[Scope and receipt](results/defant-engen-miller-lassalle/FORMALIZATION.md).

## 2026-11-25 — Verify the actual Sobolewski–Ulas partition congruences

Lean verifies exact partition recurrences by multiset bijections and a
closed 25-state residue certificate for every input. Every explicit
source-layer member is an actual exception. The reverse inclusion
still uses the sufficiency direction of Legendre’s three-square
theorem; the all-base claim also uses Durand.
[Scope and receipt](results/sobolewski-ulas-exception-regularity/FORMALIZATION.md).

## 2026-11-25 — Reduce the original Sobolewski–Ulas statement in Lean

Lean connects the bounded gaps, finite kernels, and non-erasing gap
expansion to the literal exceptional binary-partition enumeration.
The all-base conclusion remains conditional on the written partition
classification and the Cobham–Durand implication.
[Scope and receipt](results/sobolewski-ulas-exception-regularity/FORMALIZATION.md).

## 2026-11-25 — Verify the Sobolewski–Ulas power-of-two obstruction in Lean

Lean proves nonregularity of the exact source-layer enumeration at
every positive power of two. The proof verifies the logarithmic
remainder and applies a finite integer recurrence-state argument.
Other bases and the partition-function identification remain separate.
[Scope and receipt](results/sobolewski-ulas-exception-regularity/FORMALIZATION.md).

## 2026-11-25 — Complete Lean verification of McNamara–Steingrímsson’s disproof

Lean verifies aadrianvv’s written counterexample (#651), including the
exact cardinalities at ranks 44, 45 and 46 of the literal closed
permutation interval. The strict dip disproves the original Conjecture
9.4. [Lean proof and complete receipt](results/mcnamara-steingrimsson-rank-unimodality/FORMALIZATION.md).

## 2026-11-25 — Verify the normalized Sobolewski–Ulas exception counts in Lean

Lean checks the literal normalized set, its repeated-digit counting
identities and the unbounded remainder in the actual enumeration. It
also proves nonperiodicity without using an external regularity theorem.
[Scope and receipt](results/sobolewski-ulas-exception-regularity/FORMALIZATION.md).

## 2026-11-25 — Identify the exceptional block and pointed downset counts

Lean distinguishes first and later omissions from the permutation itself
and proves later-slot uniqueness. It also identifies the coefficients
counting actual pointed downsets at lengths at least three. This advances
aadrianvv’s written counterexample without claiming the final repeated
rank census. [Scope and receipt](results/mcnamara-steingrimsson-rank-unimodality/FORMALIZATION.md).

## 2026-11-25 — Factor the repeated McNamara–Steingrímsson interval

Lean proves that any intermediate permutation factors through the actual
host-block positions it uses. All but one of the long factors are full;
if the omitted block is after the first, the short factor is full too.
This is the structural step in aadrianvv’s written disproof, not its final
rank count. [Scope and receipt](results/mcnamara-steingrimsson-rank-unimodality/FORMALIZATION.md).

## 2026-11-25 — Check the two-summand interval counts in Lean

Lean proves the exact positive-rank convolution for the interval between the pointed endpoint and its direct sum with the longer pointed endpoint. It uses actual permutation counts and proves the two families disjoint. The full repeated-sum interval remains separate. [Scope and receipt](results/mcnamara-steingrimsson-rank-unimodality/FORMALIZATION.md).

## 2026-11-25 — Verify classical containment in the interval rank-unimodality disproof in Lean

Lean verifies the literal layered and pointed pattern criteria, normalization to permutations of `Fin n`, greedy weighted enumeration, and pointed occurrences in direct sums. Credit for the written disproof remains with the contribution in #651. Lean also counts every literal rank of the small pointed interval. The full repeated-sum interval count remains separate. [Lean scope](results/mcnamara-steingrimsson-rank-unimodality/FORMALIZATION.md).

## 2026-11-25 — Complete Rossi’s permutohedron root conjecture in Lean

Lean proves all sizes in Conjecture 6.16. It checks the omitted finite sign grid by exact dyadic witnesses and uses the uniform analytic argument thereafter. It verifies the complete root multisets for the literal rank polynomial and Rossi’s evaluated characteristic face sum. [Lean scope and receipt](results/rossi-permutohedron-roots/FORMALIZATION.md).

## 2026-11-25 — Extend the shifted-runner certificates through 57

Tomdif’s [PR #660](https://github.com/1337isnot1337/solved-conjectures/pull/660) adds a rational counterexample for 57 runners and improves the two submitted bounds for 55 and 56. Independent exact rational checks verify all three maxima, including attaining times. The package now covers 18–57; 58–94 is outside the verified range. Aadrianvv’s earlier certificates and verifier are unchanged. This is not Lean verified. [Independent review](results/shifted-lonely-runner-counterexamples/REVIEW.md).

## 2026-11-25 — Verify Athanasiadis–Chapoton polar duality in Lean

Lean proves Conjecture 6.2 for every finite preorder. The actual polar dilates have equivalent lattice-point sets, hence equal Ehrhart series and numerators. The real transfer is a positively homogeneous homeomorphism. [Lean scope](results/athanasiadis-chapoton-polar-duality/FORMALIZATION.md) · [Receipt](results/athanasiadis-chapoton-polar-duality/verification/receipt.json).

## 2026-11-25 — Verify part of the ordinary D’Arcais root conjecture in Lean

Lean verifies the ordinary generating-function recurrence, the strict root comparisons for indices 6–50 and all real parameters at least 1, and the central Fourier integral bound under explicit saddle estimates. [Lean scope](results/heim-neuhauser-ordinary-darcais-root/FORMALIZATION.md) · [Receipt](results/heim-neuhauser-ordinary-darcais-root/verification/receipt.json).

## 2026-11-25 — Verify the second-largest-terminal decomposition and limit reduction in Lean

Lean verifies the literal four-pattern class, its canonical split by a unique marker gap, the binomial interleaving count, and the block-deletion lemma for tableau walks. The exact leading amplitude follows in Lean from explicit counting and gap estimates. [Lean scope](results/pantone-bona-second-largest-terminal/FORMALIZATION.md) · [Receipt](results/pantone-bona-second-largest-terminal/verification/receipt.json).

## 2026-11-25 — Identify Rossi’s face polynomials in Lean

Lean counts the literal ordered partitions including the empty face, proves their Stirling-number counts, and identifies the rank polynomial and evaluated signed characteristic face sum with the Eulerian model. The rank formulation is equivalent in Conjecture 6.16. The complete finite-grid bridge remains separate. [Lean scope](results/rossi-permutohedron-roots/FORMALIZATION.md).

## 2026-11-25 — Verify Rossi’s full analytic sign grid in Lean

Lean now proves the exact root multiset for the Eulerian recurrence model at every length at least 128, including the central point, both endpoint regimes, and the reflected half. The finite initial certificates and the literal characteristic-polynomial bridge remain separate. [Lean scope](results/rossi-permutohedron-roots/FORMALIZATION.md).

## 2026-11-25 — Verify Rossi’s positive-coordinate bulk signs in Lean

Lean controls all remaining pole pairs by a telescoping strict tail estimate and proves the margin greater than one on the open positive half of the bulk sign grid. The reflected, central and endpoint signs and finite-grid certificates remain separate. [Lean scope](results/rossi-permutohedron-roots/FORMALIZATION.md).

## 2026-11-25 — Verify the two Rossi series expansions in Lean

Lean connects the Eulerian recurrence to both analytic series, evaluates the exact nearest conjugate poles, and proves the bulk quadratic binomial estimate. The uniform signs and finite-grid witnesses remain separate. [Lean scope](results/rossi-permutohedron-roots/FORMALIZATION.md).

## 2026-11-25 — Verify Rossi’s root-count reduction in Lean

Lean proves that an exact alternating negative grid gives the prescribed simple roots, using the Eulerian recurrence's degree and derivative and Rossi’s reciprocal change of variable. The two sign-grid regimes and characteristic-polynomial identification remain to be formalized. [Lean scope](results/rossi-permutohedron-roots/FORMALIZATION.md).


## 2026-11-25 — Prove Shumyatsky’s conjugate prime-spectrum conjecture

A pair of conjugates in every finite group generates a subgroup with the full prime spectrum. The proof lifts pairs across permuted simple factors and treats fixed simple factors via almost-simple generation. [Proof and audit](results/shumyatsky-conjugate-prime-spectrum/)


## 2026-11-25 — Disprove McNamara–Steingrímsson’s interval rank-unimodality conjecture

A repeated direct-sum construction gives a classical permutation-pattern interval with a strict rank dip. Distinct subpatterns are counted by their sum decompositions, and a separate exact integer checker reproduces all three coefficients. [Proof and audit](results/mcnamara-steingrimsson-rank-unimodality/)

## 2026-11-25 — Verify all seven of tomdif’s real circular-index bounds in Lean

Lean proves the exact maximum degree and real circular-index bounds of each submitted graph. Six indices equal `Δ+2/3`; the degree-15 graph is bracketed by `171/11` and `47/3`. The earlier degree families remain separate. [Lean scope](results/circular-index-upper-half-remaining-deltas/REVIEW.md).

## 2026-11-25 — Publish tomdif’s graph-colouring and shifted-runner certificates

[PR #647](https://github.com/1337isnot1337/solved-conjectures/pull/647) supplies the seven missing maximum degrees for the upper-half circular chromatic index, completing the combined coverage for all degrees at least eight. [PR #646](https://github.com/1337isnot1337/solved-conjectures/pull/646) extends the shifted-runner counterexamples through 56, leaving 57–94 outside the checked range. Both contributions are by [tomdif](https://github.com/tomdif); the exact certificates were independently replayed.

## 2026-11-25 — Verify the Xu–Zhou sharpness family in Lean

Lean verifies exactly `2*t` Laplacian eigenvalues in the closed interval `[4, 5*t+1]` for the graph with diameter `4*t` and `t ≥ 1` doubled layers. This attains the original upper bound for `c=t−1`. [Lean scope](results/xu-zhou-laplacian-diameter/FORMALIZATION.md).

## 2026-11-25 — Verify the Xu–Zhou diameter–Laplacian conjecture in Lean

Lean verifies the entire original admissible parameter range. The literal clique-chain Laplacian has at most twice the layer surplus eigenvalues at least four. Completing the distance layers, retaining the exact number of vertices, and extending low eigencoordinates by zero proves the requested closed-interval count for the actual graph. The written sharpness family remains separate. [Lean scope](results/xu-zhou-laplacian-diameter/FORMALIZATION.md).

## 2026-11-25 — Xu–Zhou tridiagonal quotient in Lean

Lean proves the nonnegative eigenvalue bound for the actual tridiagonal quotient, including the kernel at the closed cutoff. The lift to the full clique-chain Laplacian remains separate. [Lean scope](results/xu-zhou-laplacian-diameter/FORMALIZATION.md).

## 2026-11-25 — Xu–Zhou Laplacian reductions in Lean

Lean verifies the closed-cutoff spectral count argument, the actual distance-layer completion and retained cardinalities, and a finite marking budget. The quotient bound and full conjecture are separate. [Lean scope](results/xu-zhou-laplacian-diameter/FORMALIZATION.md).

## 2026-11-25 — Verify the Higashitani–Kummer–Michałek counterexample in Lean

Lean constructs the unique Ehrhart polynomial of the literal six-pair polytope, proves its degree bound and count identity at every natural dilation, and checks a root off the canonical line. This refutes both published clauses; the independent Wronskian and stronger canonical-line witness remain written supplements. [Lean scope](results/hkm-ehrhart/FORMALIZATION.md).

## 2026-11-25 — HKM literal lattice-point counts in Lean

Lean verifies the convolution for the literal six-part lattice count and checks all twelve evaluations used in the root certificate. The off-line root follows for any degree-at-most-eleven polynomial with the literal counts. The corresponding Ehrhart polynomial degree and existence are not yet verified. [Lean scope](results/hkm-ehrhart/FORMALIZATION.md).

## 2026-11-25 — Exact HKM lattice membership in Lean

Lean proves both directions of the signed-mass characterization for every integer dilation and every complete multipartite symmetric edge polytope with at least two nonempty parts. The lattice-point count and Ehrhart identification are separate. [Lean scope](results/hkm-ehrhart/FORMALIZATION.md).

## 2026-11-25 — Higashitani–Kummer–Michałek Lean checkpoint

The published Lean scope reuses the root and local count checkpoints and verifies necessary signed-mass conditions and finiteness for the actual dilated polytope. The exact lattice-point count is not assumed to be checked. [Lean scope](results/hkm-ehrhart/FORMALIZATION.md).

## 2026-11-25 — Complete Lean verification of Nuttall’s conjecture

Lean verifies the signed extended-Chebyshev criterion, discharges the theta-tail constraint, and proves strict signs for every ordered cumulant grid through any finite order. It also proves existence of the least cumulant index as stated by John Nuttall. The separate RH-equivalent problem is unchanged. [Lean scope](results/nuttall-cumulants/FORMALIZATION.md).

## 2026-11-25 — Nuttall negative-region bound and integral dominance

Lean checks the absolute integral bound on the negative region, the exact comparison ratio and the eventual dominance of the positive box. The strict cumulant Hankel sign follows conditionally on the remaining distinct-node theta tail sign. [Lean scope](results/nuttall-cumulants/FORMALIZATION.md).

## 2026-11-25 — Nuttall lower bound on the moving-box integral

Lean verifies the product-measure volume, the kernel product and signed integrand bounds, and the uniform lower bound after integration on the moving box. This does not control the complement. [Lean scope](results/nuttall-cumulants/FORMALIZATION.md).

## 2026-11-25 — Nuttall derivative determinant on the moving box

Lean verifies the uniform signed lower bound in §6 (15) on the specified box, including a quantitative Vandermonde perturbation estimate and the exact factors removed from rows and columns. This does not yet compare the signed integrals. [Lean scope](results/nuttall-cumulants/FORMALIZATION.md).

## 2026-11-25 — Nuttall uniform theta derivative ratios

Lean verifies the inverse-scale error bound on the normalized derivative ratios used for the positive-box estimate. One error constant and one threshold work for any fixed finite range of orders. The determinant lower bound itself is not claimed. [Lean scope](results/nuttall-cumulants/FORMALIZATION.md).

## 2026-11-25 — Ferreira–Simon diagonal Lean checkpoint

AlexisFimeyer verifies strict monotonicity of the explicit Pollard density integral and differentiation of the Mittag–Leffler series and integral. The diagonal inequality remains conditional on the local Pollard representation. [Original PR #626](https://github.com/1337isnot1337/solved-conjectures/pull/626) · [Lean scope](results/ferreira-simon-diagonal/FORMALIZATION.md).

## 2026-11-25 — Nuttall scalar tail comparison

Lean verifies the scalar moment integral bound and the final scalar dominance limit. The estimates have not yet been linked to the signed determinant integrals. [Lean scope](results/nuttall-cumulants/FORMALIZATION.md).

## 2026-11-25 — Nuttall full theta Wronskian tail signs

Lean transfers the first-mode polynomial calculation to the full theta kernel. It checks the normalized Hankel determinant limit and the eventual strict Wronskian signs, simultaneously for any bounded range of sizes. Distinct-node evaluation and the higher cumulant signs remain separate. [Lean scope](results/nuttall-cumulants/FORMALIZATION.md).

## 2026-11-25 — Nuttall first-mode Hankel degrees and signs

A Schur complement proves the exact adjacent-minor recurrence. Lean verifies nonvanishing, the exact degree and leading-coefficient sign in every size, and the normalized evaluation limit. The transfer to the complete theta kernel is not part of this change. [Lean scope](results/nuttall-cumulants/FORMALIZATION.md).

## 2026-11-25 — Nuttall Hankel polynomial identity

Lean proves the differential identity for the shifted-minor square difference, and its exact degree and leading coefficient when the unshifted Hankel polynomial is nonzero. This does not yet establish the adjacent-minor recurrence or its analytic sign. [Lean scope](results/nuttall-cumulants/FORMALIZATION.md).

## 2026-11-25 — Nuttall Hankel determinant integral

Lean checks the weighted integral formula for every derivative order and gives the exact signed integral for each cumulant Hankel-matrix entry. Andréief’s identity and Vandermonde normalization give the determinant-level product integral with both reversal signs cancelled. The strict sign step is still open. [Lean scope](results/nuttall-cumulants/FORMALIZATION.md).

## 2026-11-25 — Nuttall weighted cumulant representation

Lean checks the factorial moment identity and proves equivalence of the literal repeated-tail recursion with the single-integral formula at every order and every nonnegative argument. Higher determinant signs remain unformalized. [Lean scope](results/nuttall-cumulants/FORMALIZATION.md).

## 2026-11-25 — Revised Tan–Zhou conjecture

Completed Lean verification of the revised monotone conjecture using unreduced Lüroth denominators. The proof formalizes the cylinder upper bound and obtains the lower bound from a nested interval construction with a Hölder inverse address map. See the [formalization](results/revised-tan-zhou-luroth/FORMALIZATION.md) and [local receipt](results/revised-tan-zhou-luroth/verification/receipt.json).

## 2026-11-25 — Nuttall calculus of repeated tails

Lean checks the fundamental theorem for the literal repeated tails and the exact derivative index shift at every order, including derivatives beyond the tail order. This is groundwork for the Wronskian identities, not a sign theorem. [Lean scope](results/nuttall-cumulants/FORMALIZATION.md).

## 2026-11-25 — Nuttall termwise differentiation and derivative bounds

Lean checks termwise differentiation of the literal infinite theta series in every order, a global double-exponential derivative bound, and a uniform bound on every differentiated tail after the first mode. Higher Wronskians are not checked. [Lean scope](results/nuttall-cumulants/FORMALIZATION.md).

## 2026-11-25 — Nuttall derivatives of the theta summands

Lean checks the polynomial recurrence, exact degree and leading coefficient for derivatives of every individual theta summand in every order. It does not differentiate the infinite sum. [Lean scope](results/nuttall-cumulants/FORMALIZATION.md).

## 2026-11-25 — Nuttall first-mode asymptotic

Lean checks the exact first-term correction, a uniform exponential tail bound, the leading ratio limit, and the global double-exponential bound for derivative order zero. [Lean scope](results/nuttall-cumulants/FORMALIZATION.md).

## 2026-11-25 — Dilcher–Kidwai–Tomkins’s Stern-polynomial conjecture

Published the checked Stern-polynomial recurrence and conditional continued-fraction reduction; added unconditional nonvanishing on the positive real axis. The full complex half-plane proof remains partially formalized. [Lean scope](results/stern-half-plane/FORMALIZATION.md).

## 2026-11-25 — Nuttall's conjecture

Checked the theta kernel and order-one cumulant-minor positivity for every cumulant order, both for literal iterated tails and in the single-integral formulation. The higher-order conjecture remains only partially formalized. [Lean scope](results/nuttall-cumulants/FORMALIZATION.md).

## 2026-11-25 — Németh–Seberry–Shu conjecture

Published checked Fourier, spectral, modular permanent, and conditional dense-row counting components, and verified the strict amplitude separation bridge. This does not complete Lean verification of the asymptotic disproof. [Lean scope](results/nemeth-seberry-shu/FORMALIZATION.md).

## 2026-11-25 — Burstein’s descent-top shape-Wilf conjecture

Published the Lean refutations of original Conjectures 16 and 17 on the same six-row board with suffix 1. The stronger every-suffix construction remains written only. [Lean scope](results/burstein-descent-top-shape-wilf/FORMALIZATION.md).

## 2026-11-25 — Benfield–Lippard’s stable Waring-gap parity conjecture

Published the exact Lean proof of both original stable-exception parity assertions for every exponent at least two. The stronger two-adic congruences remain written only. [Lean scope](results/benfield-lippard-waring-gap-parity/FORMALIZATION.md).

## 2026-11-25 — Cardon–Forgács–Piotrowski–Sorensen–White conjecture

Lean now verifies the uniform small-positive-damping obstruction for every real p > 2. The originally checked p = 3 source is unchanged. [Exact scope](results/cardon-zero-sector/LEAN.md).

## 2026-11-25 — Ćurgus–Mascioni’s Fréchet root-matching extremizer question

Kernel-checked the exact nonuniqueness counterexample on all quadratics with the stated operator, including all minimizing permutations and the continuous family of inequivalent extrema. General attainment and the cubic example remain written only. [Lean scope](results/curgus-mascioni-frechet/FORMALIZATION.md).

## 2026-11-25 — Ferroni–Morales–Panova’s cylindric Ehrhart-positivity conjecture

Kernel-checked the relaxed-seam unpinned counterexample under both column-comparison conventions. The separate standard-boundary positivity theorem remains outside Lean scope. [Scope](results/fmp-cylindric/FORMALIZATION.md).

## 2026-11-25 — Csordas–Vishnyakova conjecture

Completed Lean verification of the original Conjecture 3.6 counterexample, including every test coefficient at every real argument and the actual polynomial-approximation definition. The earlier genus-restricted theorem is not impugned. [Scope](results/csordas-vishnyakova/FORMALIZATION.md).

## 2026-11-25 — Wagner's Laguerre-operator conjecture

Completed Lean verification of the original Conjecture 4.3 counterexample. Actual polynomial approximants establish membership of the input, and the first Laguerre transform fails the eventual sign requirement. The old failed draft has been superseded by an exact source build, axiom audit and stock replay. [Scope](results/wagner-laguerre-operator/FORMALIZATION.md).

## Benfield–Lippard’s stable Waring-gap symmetry conjecture

On 24 November 2026 the [complete original conjecture disproof](results/benfield-lippard-waring-gap-symmetry/LEAN.md) established both counterexamples at exponents 64 and 128, including the actual stable exception cardinality and reflected-gap witnesses. The seven-module strict build, all-owned audit (335 declarations, 248 theorems), and independent replay passed. Discovery attribution and the priority caveat remain unchanged. [PR #570](https://github.com/1337isnot1337/solved-conjectures/pull/570).

## 2026-11-25 — Ma–Tang’s random subset-sum threshold conjecture

Completed the exact original Lean formalization, including the actual second-order limsup, the third-log lower correction and convergence along the mixed orders. The published mathematical result and rank are unchanged. The separate bounded-remainder refinements are outside the Lean scope. [Scope](results/ma-tang-random-subset-sums/FORMALIZATION.md) · [Receipt](results/ma-tang-random-subset-sums/verification/limsup-receipt.json).

## 2026-11-24: Exact rank threshold for the Caiolo–Ferroni–Hoster conjecture

A [supplement](results/caiolo-ferroni-hoster/RANKS.md) to the existing entry proves that dual Chow real-rootedness holds for all matroids of rank r exactly when r ≤ 4, and that both dual polynomials fail in every rank at least five. The same construction is used with the rank as a parameter. [Lean theorem](lean/Conjectures/CaioloFerroniHosterRanks.lean). Rank four remains undecided for the augmented and interlacing assertions. The rank-five attribution is unchanged and no new conjecture is counted.

## 2026-11-24 — Gravgaard–Lee’s Lüroth diameter question

Completed Lean verification of the exact positive sum hull, including equality of the total diameter, and the exact threshold for coverage modulo one. Direct cylinder refinement replaces the use of the general thickness theorem. See the [formalization](results/gravgaard-lee-diameter-condition/FORMALIZATION.md) and [local receipt](results/gravgaard-lee-diameter-condition/verification/receipt.json).

## 2026-11-24 — Ulas’s disjoint-block square-product conjecture

Completed Lean verification of the common-length theorem for every positive length. The proof fills the prime-avoiding tail gap in the research branch’s partial formalization and retains the affine construction and residue argument. The catalogue row keeps its established position. See the [scope](results/ulas-disjoint-square-blocks/FORMALIZATION.md) and [local receipt](results/ulas-disjoint-square-blocks/verification/receipt.json).

## 2026-11-24 — Verify Braun–Bruegge’s minimum facet conjecture in Lean

Lean proves the exact global lower bound and the unique class of minimizers for the facets of the symmetric edge polytope. The complete scoped Lean gate passed. [Formalization](results/braun-bruegge-minimum-facets/FORMALIZATION.md)

## 2026-11-24 — Hartke–Stolee–West–Yancey matching-excess conjecture

Completed the full Lean formalization of the existing entry, including actual graph witnesses for every input, the universal edge bound, attained all-order extremal constants, Hetyei extension and eventual stabilization, and the tail-minimum divergence with the recorded quantitative bound. The 22-module frozen closure passed strict sources, the complete owned/private audit and exact stock replay; independent mathematical and primary-statement reviews passed. The original proof, proposer and proof-author credits, priority qualifications, ranked position and unrelated catalogue rows are preserved. This is one complete existing result, not separate counts for constructions or bounds. The [scope](results/hartke-stolee-west-yancey-matching-excess/FORMALIZATION.md), [review](results/hartke-stolee-west-yancey-matching-excess/LEAN_REVIEW.md) and [receipt](docs/verification/lean-hartke-matching-excess-complete-20261124-162051/receipt.json) keep proof verification separate from aggregate/hosted/deployment obligations.

## Feldheim–Feldheim’s weighted tail conjecture

On 24 November 2026 the existing entry received a [complete Lean formalization](results/feldheim-weighted-tail/FORMALIZATION.md) of original Conjecture 1 for all positive weights and arbitrary independent nonnegative laws without compact support, including atoms. The theorem uses actual probability events and a literal infinite limsup. The twenty-module source closure passed strict compilation, a complete transitive axiom audit and exact stock-kernel replay, with independent statement, source and evidence reviews. Naomi Dvora Feldheim and Ohad Noy Feldheim retain original proposer and earlier-method credit; the recorded proof credit to Cinna Davis and its priority qualification are preserved. The norm and finite-threshold supplements remain unformalized. This updates the verification status of one existing entry without changing its rank or adding a result row; aggregate and deployment obligations remain separate.

## Hajdu–Sárközy’s shifted-product total primitivity conjecture

On 24 November 2026 the existing entry received a complete Lean proof of the original conjecture for all exponent pairs and every finite modification, the full summable-family theorem, and all nonzero-shift two-variable little-o perturbations. Thirteen new modules reuse the eleven unchanged perturbation modules. The mixed-coefficient determinant, actual coefficient-tail count, ordered limit, sparse-factor incidence sum, real-threshold bridge, and p-series specialization are proved. The full twenty-four-module closure passed strict source builds, complete transitive axiom audit and exact stock-kernel replay, followed by independent review. Publication metadata checks bind the unchanged sources to that proof evidence without calling a preflight a new rebuild. The optional extension to more than two variables is not separately formalized. The existing rank, proposer/proof attribution and priority qualification are retained; no new entry or extra corollary count is added.

## Gawron–Miska–Ulas’s Thue–Morse sign-density conjecture

On 24 November 2026 the [complete original Conjecture 5.8 disproof](results/gawron-miska-ulas-thue-morse-sign-density/LEAN.md) established both finite-prefix counterexamples using the actual infinite-product coefficients. All three modules strictly compiled, the all-owned audit passed (250 declarations, 212 theorems), and independent replay passed. The separate stronger exact-density theorem remains outside this Lean scope. Discovery attribution and the bounded priority caveat remain unchanged. [PR #565](https://github.com/1337isnot1337/solved-conjectures/pull/565).

## Kovalev’s square-root Taylor-section zero-free conjecture

On 24 November 2026 the [complete Lean formalization](results/kovalev-zero-free/FORMALIZATION.md) proved the original square-root conjecture for every section degree and every point of the closed unit disk, with the stronger theorem for every positive geometric-polynomial length. The coefficients are identified with the actual iterated derivatives. Twenty-one strict source builds, the all-owned/private axiom audit and exact stock-kernel replay passed and received independent evidence and statement reviews. Leonid V. Kovalev is the original proposer; the recorded proof credit to Cinna Davis and the bounded priority qualification are preserved. Fractional-exponent, arbitrary-segment and adjacent trigonometric supplements remain unformalized. This updates one existing entry; aggregate verification and public deployment remain separate obligations in [#563](https://github.com/1337isnot1337/solved-conjectures/issues/563).

## 2026-11-24: Formalize the Thue–Morse valuation disproof

The [Lean proof](lean/Conjectures/ThueMorseValuation.lean) verifies the exponent-17 witness and the full uniform counterexample family for every k ≥ 11. See the [local build, axiom audit and kernel replay receipt](docs/verification/lean-thue-morse-valuation-publication-20261124/receipt.json).

## 2026-11-24 — Verify Ferroni–Higashitani Question 5.12(a) in Lean

The [Lean proof](results/ferroni-higashitani-early-interior-ehrhart/FORMALIZATION.md) constructs the dimension-170 lattice polytope, proves integer decomposition at every positive dilation, characterizes its Ehrhart polynomial by the closed lattice-point counts, and proves the strict inequality at the first three negative evaluations.

## Gravgaard–Lee’s mixed upper/lower Lüroth conjecture

On 24 November 2026 the [complete Lean proof](results/gravgaard-lee-upper-lower-luroth/FORMALIZATION.md) established the exact sum interval and original Conjecture 2.6 for every matching digit threshold k≥2. The proof formalizes the existing direct refinement argument, including the finite zero-tail repair and actual infinite expansions. All 12 sources passed strict compilation, the all-owned/private axiom audit and exact stock replay; the source statement and full receipt were independently reviewed. Maiken Gravgaard and Ying Wai Lee are the original proposers; the recorded proof by Cinna Davis and its priority qualifications are preserved. The two reused Lüroth modules and threshold-two boundary are not counted as new results. Aggregate and deployment checks remain separate.

## 2026-11-24 — Fan–Tringali’s power-monoid length-set conjecture

Completed the Lean proof of the original 2018 conjecture for ordinary and restricted finitary power monoids of arbitrary Dedekind-finite non-torsion monoids, together with the exact reduced-natural-number length system. The 18-module closure includes the graph construction, all no-carry divisor and factorization lifts, and a fully proved noncommutative unit normalization and monoid transfer. Strict source builds, the complete all-owned/private axiom audit and stock kernel replay passed. The existing result row and mathematical attribution are retained; this is one existing result. Survey irreducibles, multiplicities and relative cancellativity remain unformalized supplements. The dedicated verifier/workflow and exact receipts keep the scoped proof pass separate from aggregate dependency-cache and hosted deployment obligations.

## Steinerberger’s greedy-energy Fourier conjecture

On 24 November 2026 the [complete Lean disproof](results/steinerberger-greedy-fourier/FORMALIZATION.md) verified an actual infinite greedy sequence whose stated weighted absolute Fourier sum is not O(log n). The four modules include direct greedy admissibility, exact Fourier recurrences, a quadratic lower bound along an unbounded family of prefixes, and the asymptotic negation. The independent source review corrected the Kritzinger citation to arXiv:2109.06298v4, Theorem 4 and Algorithm 3, page 15. The existing entry, its rank and its priority qualification are retained. The sharp limsup constant and the stronger all-initialization and all-tie-breaking assertions remain written supplements.

## 2026-11-24 — Verify Coulangeon–Lazzarini’s two-shell counterexample in Lean

The [Lean proof](lean/Conjectures/CoulangeonLazzariniRealLattice.lean) constructs the full-rank discrete lattice in dimension ten, verifies the spherical second moments for squared norms 4 and 8, and proves failure at squared norm 9. The [integer-coordinate module](lean/Conjectures/CoulangeonLazzariniShells.lean) verifies the elementary arbitrary-delay family.

## 2026-11-24 — Verify Gravgaard–Lee’s mixed Lüroth theorem in Lean

The [Lean proof](lean/Conjectures/GravgaardLeeMixedLuroth.lean) checks the source digit sets, all fifteen interval containments and the passage to the infinite expansions. It proves the stronger ordinary interval and Conjecture 2.2 on all real residues.

## 2026-11-24 — Verify Gravgaard–Lee’s large-digit Lüroth theorem in Lean

The [Lean proof](lean/Conjectures/GravgaardLeeLargeLuroth.lean) verifies Conjecture 2.12 for every digit bound and the stronger interval with strictly increasing interleaved digits from the [written result](results/gravgaard-lee-large-luroth/). It checks the convergent source series and the half-open digit intervals.

## Gessel–Zhuang’s pinnacle-set gamma-positivity conjecture

On 24 November 2026 the [complete Lean formalization](results/gessel-zhuang-pinnacle-gamma/LEAN-AUDIT.md) proved the literal pinnacle-set and peak-count inverse-descent polynomials gamma-positive for every positive size, with the original weight and center. Both source conjectures belong to one existing entry. The actual permutation/history bijection and statistic bridges, fixed-path real splitting and symmetry, and full gamma expansion are proved. All 25 project modules passed strict compilation, the all-owned axiom audit, and stock-kernel replay. Ira M. Gessel and Yan Zhuang are the original proposers; the existing proof credit to Cinna Davis and GPT-6.2 Astra and the prior-art and priority qualifications are preserved.

## Hajdu–Sárközy’s shifted-power perturbation conjecture

On 24 November 2026 the existing entry received a complete Lean proof of the original conjecture and the nonzero-shift symmetric-difference theorem. All exponents at least two, actual real-threshold counts, arbitrary nontrivial positive-integer factor sets, every finite modification, and the zero-root convention are included. Eleven modules passed strict builds, the complete declaration/axiom audit and stock-kernel replay, followed by independent statement and proof review. The recorded determinant/bin argument is formalized with an elementary incidence bound and a proved double-prefix summation. The stronger retained-limsup supplement remains unformalized. The existing rank, proposers, proof attribution, and priority qualification are retained; no new conjecture entry is added.

## Rowland–Sistos Barrón conjecture

On 24 November 2026 the [complete Lean formalization](results/rowland-sistos-barron/LEAN_STATUS.md) proved the actual minimum recurrence rank of every power of the recorded integer sequence, the exact formula for every exponent at least 49, and failure of eventual quasipolynomiality over every characteristic-zero field. Strict compilation, every-owned-declaration axiom audit, and stock-kernel replay passed for all 17 modules. The proof follows the existing argument credited to Cinna Davis and GPT-6.2 Astra; Eric Rowland and Jesús Sistos Barrón are the original proposers. The source’s undefined term pseudo-polynomial, the separate general-rank clause, and the priority qualifications remain explicit.

## Johnson's conjecture

On 24 November 2026 the [complete Lean proof](results/johnson-pfaffian/LEAN-AUDIT.md) closed the general even-order, every-matching gap. It formalizes the recorded circular interval-product argument, including the stronger unconditional matrix-class theorem and the exact source-kernel bridge. All thirty project modules passed strict compilation, the audit of every owned declaration, and stock-kernel replay. William Johnson's conjecture, endpoint inequality and uncrossing reduction are credited; the repository proof credit and bounded priority assessment are preserved.

## 2026-11-24: Verify the Caiolo–Ferroni–Hoster family in Lean

The [formal proof](lean/Conjectures/CaioloFerroniHoster.lean) verifies the full
simple rank-five family for all prime powers q ≥ 17. Both dual polynomials
fail to split over the reals, and the augmented quintic has a single simple
real root. [Verification issue #560](https://github.com/1337isnot1337/solved-conjectures/issues/560)

## Juhnke’s arbitrary-step lattice-path log-concavity conjecture

On 24 November 2026 the [complete Lean proof](results/juhnke-lattice-paths/LEAN-AUDIT.md) established log-concavity and unimodality for every dimension and step count in the original unrestricted path convention. All 18 modules passed strict compilation, the audit of every owned declaration, and stock-kernel replay. The proof follows the recorded argument of Cinna Davis and GPT-6.2 Astra, credits Martina Juhnke and the classical Brenti translation criterion, and preserves the existing priority qualification. Both boundary dimensions are included in this one result.

## 2026-11-24 — Steinerberger’s quantitative Feldheim-tail conjecture

The [complete Lean disproof](results/steinerberger-feldheim-tail/LEAN-AUDIT.md) refutes both original existential inequalities with the actual probability law, expectation, median, independent coordinates, and product-event probabilities. The inequalities fail for every positive threshold. All four modules passed strict source compilation, an audit of every owned declaration, and stock-kernel replay; the integrator independently checked the original statements. The additional smoothing and asymptotic supplements remain outside the verified scope. This formalizes the recorded argument of Cinna Davis and GPT-6.2 Astra and retains the existing priority qualifications.

## 2026-11-24: Compact ranked results index

The README lists two side-by-side problem/status pairs, with approximate competition ranks and ties. The established significance order, result links, attribution markers, and Lean statuses are preserved. The site builder reads the index down the left half and then the right half; the README checker and regression tests enforce the same layout and rank order.

## 2026-11-24: Verify three short-proof Lean targets

- [Wilf-module questions](results/almiron-moyano-wilf-module-questions/LEAN.md): Question 4.8 and parts (1), (2), and (6) of Question 4.13. Partial coverage of the collection entry.
- [Cardon et al.](results/cardon-zero-sector/LEAN.md): exact negative answer to Question 6.1.
- [Chappelon–Ramírez Alfonsín–Stamate](results/chappelon-ramirez-stamate-leaf-type/LEAN.md): exact disproof of Conjecture 4.4.

The [scoped verification receipt](docs/verification/first-short-proof-lean-batch.md) records the pinned compiler, all-owned axiom audit, and stock kernel replay. The original conjecture disproofs do not certify the stronger written supplements.

## 2026-11-24: Prove Pantone–Bóna’s third-largest-terminal asymptotic

The [written proof](results/pantone-bona-third-largest-terminal/) resolves Conjecture 6.2 for $A_{5,3}$ with exact leading constant $9\sqrt3/(16\pi)$. See [issue #382](https://github.com/1337isnot1337/solved-conjectures/issues/382) for source audit and scope. This is distinct from the other asymptotic conjectures in the same paper.

### Consolidated repeated conjecture entries

Four later proof packages targeted conjectures already present in the collection. Each remains counted once, at its original entry. The newer material remains available on the original pages: [Higashitani–Kummer–Michałek](results/hkm-ehrhart/INTERLACING-CL.md) has a noninterlacing pair whose individual roots lie on the canonical line; [Sagan–Swanson](results/sagan-swanson-normality/LOCAL-LIMIT.md) has a uniform lattice local limit; [Zhu](results/zhu-jacobi-stirling/NUMERICAL-MOMENTS.md) has a sharp numerical moment classification; and [Chow](results/chow-conjecture/ALTERNATIVE-PROOF.md) has an independent proof. No original proof, Lean status, or attribution was dropped.

## 2026-11-24: Resolve matching-excess divergence and two plane-partition conjectures

- [Matching-excess divergence](results/hartke-stolee-west-yancey-matching-excess/) follows from an explicit graph construction and binary long division. The stronger rate question is separate.
- [Plane-partition polynomial Turán inequalities](results/heim-neuhauser-troeger-plane-partition-turan/) hold on the full real parameter range of Conjecture 2.
- [Plane-partition nth-root polynomization](results/heim-neuhauser-plane-partition-polynomization/) holds on both real parameter ranges of Conjecture 1.
- [Ordinary D’Arcais nth-root conjecture](results/heim-neuhauser-ordinary-darcais-root/) holds for all real parameters at least 1, using a uniform Fourier sign and exact finite bridge.
- [Both quantitative Feldheim-tail bounds](results/steinerberger-feldheim-tail/) fail for the same smooth strictly log-concave distribution; the original qualitative theorem remains intact.
- A separate [two-quantile-spacing argument](results/steinerberger-feldheim-tail/LINEAR-EXISTENCE.md) proves a smaller universal existential linear coefficient.
- [Waring-gap symmetry](results/benfield-lippard-waring-gap-symmetry/) fails at two power-of-two exponents, and [Waring-gap parity](results/benfield-lippard-waring-gap-parity/) holds at every exponent.
- [The Feldheim–Feldheim weighted tail conjecture](results/feldheim-weighted-tail/) holds for arbitrary independent laws, even with atoms.
- [Burstein’s refined shape-Wilf equivalence](results/burstein-descent-top-shape-wilf/) fails uniformly over all suffix permutations.
- [Rossi’s permutohedron characteristic roots](results/rossi-permutohedron-roots/) satisfy all three intervals of Conjecture 6.16 at every index.
- [Hajdu–Sárközy’s shifted-power perturbation conjecture](results/hajdu-sarkozy-shifted-power-perturbations/): Proof of the remaining square case under the full little-o perturbation condition, including finite modifications. Prior higher powers are credited.
- [Hajdu–Sárközy’s shifted-product total primitivity conjecture](results/hajdu-sarkozy-shifted-products/): Proves the original bivariate claim for the remaining coprime exponents using a summable union of scaled power sets; non-coprime exponents were known.
- [Hegyvári’s conjecture](results/hegyvari-floor-doubling/): Proves strong completeness of the two-ray set across the remaining rational ratios that are not powers of two, with exact strong-completeness obstructions.
- [Ma–Tang’s random subset-sum threshold conjecture](results/ma-tang-random-subset-sums/): Proves the sharp universal second-order coefficient, with an independently audited bounded-remainder match along orders three times a power of two.
- [Féray’s conjugate-power word-measure conjectures](results/feray-conjugate-power-word/): Proves both cycle limits and total-variation mixing for the stated permutation word, with sharp distance asymptotic e⁻¹/(n−1).
- [Xu–Zhou’s diameter–Laplacian conjecture](results/xu-zhou-laplacian-diameter/): Proves the complete parameterized bound for the high Laplacian spectrum of a graph of given diameter, including the closed endpoint.
- [Han’s simultaneous spherical-harmonic saturation question](results/han-spherical-harmonic-saturation/): Constructs one real orthonormal basis per degree attaining both sharp Lᵖ growth regimes for every basis vector simultaneously.
- [Steinerberger’s small-average eigenfunction norm question](results/steinerberger-small-average-eigenfunction-norms/): Refutes the proposed near-linear lower bound and constructs real spherical bases with optimal aggregate and per-mode L¹ sizes.
- [Pomerance–Sárközy’s fluctuation conjecture](results/pomerance-sarkozy-fluctuations/): Proves the density-one refinement and the quarter-power Gaussian law for the count associated with n plus its distinct prime factors.
- [Ulas’s disjoint-block square-product conjecture](results/ulas-disjoint-square-blocks/): For every fixed common block length, proves infinitely many disjoint square-product collections at every sufficiently large fixed number of blocks.
- [Kovalev’s linear Lipschitz clustering questions](results/kovalev-lipschitz-clustering/): Constructs convex-hull-preserving finite-subset retractions with a dimension-free linear Lipschitz bound, uniformly for every target size.
- [Revised Tan–Zhou conjecture](results/revised-tan-zhou-luroth/): Determines the exact Hausdorff dimension from the lower order of every nonincreasing approximation function for Lüroth convergents.
- [Simmons–Weiss’s Hausdorff-measure question](results/simmons-weiss-hausdorff/): Proves natural-Hausdorff-almost-sure non-bad approximation after every irrational translate of a bounded continued-fraction Cantor set.
- [Gravgaard–Lee’s mixed Lüroth sumset conjecture](results/gravgaard-lee-mixed-luroth/): Proves that the mixed bounded-digit Lüroth sum represents every residue modulo one, with an explicit ordinary interval in the sum.
- [Gravgaard–Lee’s large-digit Lüroth sumset conjecture](results/gravgaard-lee-large-luroth/): Gives a positive-length ordinary sum interval for every lower digit threshold, using two expansions whose combined digits strictly increase.
- [Gravgaard–Lee’s Lüroth diameter question](results/gravgaard-lee-diameter-condition/): Removes the digit-bound separation condition when total diameter is at least one and determines the exact positive sum hull.
- [Gravgaard–Lee’s mixed upper/lower Lüroth conjecture](results/gravgaard-lee-upper-lower-luroth/): Determines the exact sum interval for all matching upper and lower Lüroth digit thresholds, including genuine expansions at the required endpoints.
- [Dougherty-Bliss–Galván–Polley–Shuster’s separable derangement conjecture](results/separable-derangements-limit/): Proves the derangement proportion tends to zero, with every fixed diagonal count diverging in probability.
- [Dougherty-Bliss–Galván–Polley–Shuster’s separable derangement asymptotic conjecture](results/separable-derangements-asymptotic/): Refutes every proposed fixed power exponent by exact finite two-branch counting and saturation of the occupation loss.
- [Fan’s interval Riesz capacity-ratio conjecture](results/fan-interval-riesz-capacity/): Proves the full negative-exponent conjecture and the nontrivial one-dimensional Clark–Laugesen range, with equality conditions.
- [Kovalev’s square-root Taylor-section zero-free conjecture](results/kovalev-zero-free/): The beta–gamma diameter-disk comparison proves zero-freeness in the closed unit disk for every section, also for powers between zero and one-half.
- [Dilcher–Kidwai–Tomkins’s Stern-polynomial conjecture](results/stern-half-plane/): Proves that all zeros of all Stern polynomials lie strictly to the left of Re z = 1. Analytic estimates and an exact compact-region certificate cover all binary run lengths.
- [Chern–Fu–Lin’s joint Eulerian equidistribution conjecture](results/chern-fu-lin-joint-eulerian/): Proves the joint descent and inverse-descent equidistribution of Conjecture 6.2 at every length by exact formal generating functions.
- [Dukes’s revstack interlacing conjecture](results/dukes-revstack/): Proves the strict interlacing throughout the full nondegenerate range n≥3 and records the small-n defect in the printed statement.
- [González D’León–Wachs’s complete-graph specialization question](results/gonzalez-dleon-wachs-complete-graphs/): Gives an exact Laguerre product and Gamma-moment formula, strict ordinary coefficient log-concavity, and the real-zero count for equal variables.
- [Almirón–Moyano-Fernández’s Wilf-module questions](results/almiron-moyano-wilf-module-questions/): Answers the small Wilf-threshold gap question negatively and characterizes exact normalized semimodule thresholds through multiplicity and the gap poset.
- [Defant–Engen–Miller’s Lassalle refinement conjecture](results/defant-engen-miller-lassalle/): Proves strict log-concavity in every nontrivial row of the first-value refinement of the Lassalle sequence.
- [Sagan–Wilson’s plactic centralizer conjecture](results/sagan-wilson-plactic/): Proves eventual stability of all plactic centralizers of powers, with an alphabet-only cutoff independent of word length.
- [Sagan–Wilson’s plactic coefficient-mode conjecture](results/sagan-wilson-plactic-mode/): Disproves the proposed middle mode and determines the asymptotic position of every mode in both natural coefficient rows.
- [Juhnke’s arbitrary-step lattice-path log-concavity conjecture](results/juhnke-lattice-paths/): Proves all-dimensional log-concavity for the unrestricted east/north arbitrary-step path counts.
- [Athanasiadis–Chapoton’s polar preorder duality conjecture](results/athanasiadis-chapoton-polar-duality/): A lattice-preserving transfer gives the same Ehrhart series for opposite polar preorder polytopes, with convex mutations and a finite numerator model.
- [Athanasiadis–Chapoton’s q-zeta reciprocity conjecture](results/athanasiadis-chapoton-q-zeta/): Proves the remaining full q-form of Conjecture 4.9 by coordinate-weighted reciprocity and Boolean interpolation.
- [Athanasiadis–Chapoton’s transmuted M-triangle duality conjecture](results/athanasiadis-chapoton-transmuted-m/): Proves the original reciprocal identity in every preorder by specializing weighted reciprocity, independent of lattice realization.
- Priority correction: Roy's square-partition sign table was already resolved by [Myeongjin Kang, MathDB:2611.00121v2](https://mathdb.com/abs/2611.00121v2), publicly posted before the independent injection argument. The latter and its different higher-power extension are [archived on the research branch](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/roy-square-partitions/INDEPENDENT-ARGUMENT.md), not counted in the main catalogue.
- [Gawron–Miska–Ulas’s Thue–Morse valuation conjecture](results/gawron-miska-ulas-thue-morse-valuation/): Refutes general 2-adic block constancy at exponent 17 and gives counterexamples for every k≥11.
- [Sobolewski–Ulas’s binary-partition exception regularity conjecture](results/sobolewski-ulas-exception-regularity/): Uses a repeated-digit counting remainder and Cobham’s theorem for substitutions to exclude regularity in every integer base.
- [Gawron–Ulas’s partition-sign nonperiodicity conjecture](results/gawron-ulas-partition-signs/): Oblique root-of-unity growth proves each sign occurs infinitely often on every index progression, for all coprime odd permitted-part steps at least three.
- [Steinerberger’s greedy-energy Fourier conjecture](results/steinerberger-greedy-fourier/): Exact dyadic Fourier magnitudes refute the logarithmic bound for every singleton start and give the sharp logarithm-squared constant.
- [Ćurgus–Mascioni’s Fréchet root-matching extremizer question](results/curgus-mascioni-frechet/): Proves general attainment and the exact lower-degree loss at infinity, refutes general uniqueness, and determines the source cubic value and unique extremizer.
- [Chern–Fu–Lin’s three-statistic equidistribution conjecture](results/chern-fu-lin-three-statistic/): A minimum decomposition and an exact marked generating-function kernel prove equality in every length for the full three-statistic distribution.
- [Gawron–Miska–Ulas’s Thue–Morse sign-density conjecture](results/gawron-miska-ulas-thue-morse-sign-density/): Exact signed block identities show both alleged zero-density exceptions instead have strictly positive lower densities.
- [Charlton et al.’s distinct D’Arcais zeros question](results/darcais-distinct-right-half-plane-zeros/): Infinitely many distinct right-half-plane zero values via scaled entire limits, with the inverse-index scale on a positive-density family. Prior non-Hurwitz theorem credited.
- [Fan–Tringali’s power-monoid length-set conjecture](results/fan-tringali-power-monoid-lengths/): Proof in the full original monoid scope. In the reduced setting, graph maximal cliques also permit arbitrary multiplicities of prescribed lengths.
- [Burstein’s A218225 enumeration conjecture](results/burstein-a218225-enumeration/): Both previously unresolved avoidance classes have the same maximum-insertion tree and the recorded algebraic generating function. The earlier first class is credited.
- [Sokal’s Apéry moment threshold](results/sokal-apery-moment-threshold/): Proof of the previously unresolved excluded interval, completing the classical threshold with the earlier positive result. The Hamburger exception at one quarter and a positive alternative proof are included.

The 2026-11-25 Lean checkpoint verifies the moment continuation, the lower-endpoint obstruction, and exact Hankel exclusions near zero and one quarter. [Scope](results/sokal-apery-moment-threshold/FORMALIZATION.md) · [Receipt](results/sokal-apery-moment-threshold/verification/receipt.json).
- [Gessel–Zhuang’s pinnacle-set gamma-positivity conjecture](results/gessel-zhuang-pinnacle-gamma/): Proof for every fixed pinnacle set by real-rooted height-path refinements. Gives Conjecture 7.2 by summation; Conjecture 7.1 is separate.
- [Chappelon–Ramírez Alfonsín–Stamate’s leaf-type conjecture](results/chappelon-ramirez-stamate-leaf-type/): Uniform refutation of the original genus bound. The maximum leaf type at every large genus has leading coefficient two thirds and a sharp square-root-order deficit.
- [Ferroni–Higashitani’s first-three interior Ehrhart question](results/ferroni-higashitani-early-interior-ehrhart/): A very ample, IDP counterfamily fails at the first three interior counts, answering Question 5.12(a). The already resolved part (b) is distinct.
- [Ferroni–Morales–Panova’s cylindric Ehrhart-positivity conjecture](results/fmp-cylindric/): Refutes the exact relaxed-seam unpinned conjecture and proves positivity for standard periodic partition boundaries.
- [Braun–Bruegge’s bicyclic facet conjectures](results/braun-bruegge-bicyclic-facets/): Proves the sharp global bicyclic facet maximum and the exact theta-graph optimizers, including the previously open mixed-parity cases.
- [Braun–Bruegge’s minimum facet conjecture](results/braun-bruegge-minimum-facets/): Proves both global minimum clauses and a stronger sharp bound at fixed maximum matching size, with unique complete-bipartite minimizers.
- [Cyrusian–Kaplan’s ordinarization quasipolynomial question](results/cyrusian-kaplan-ordinarization/): Proves a genus quasipolynomial for every fixed ordinarization number, valid at every positive genus, and eventual strict monotonicity.
- The [Feldheim finite-threshold supplements](results/feldheim-weighted-tail/FINITE-THRESHOLD.md) now cover distinct nonatomic laws and [sharpen the i.i.d. constants](results/steinerberger-feldheim-tail/LINEAR-EXISTENCE.md).
- A [sharp rate test for convex log tails](results/steinerberger-feldheim-tail/CONVEX-HAZARD-RATE.md) distinguishes divergent and convergent square-integral scales.
- The [exact differential equation](results/pantone-bona-asymptotic/ode-proof.md) previously guessed for the terminal-largest pattern class is now proved separately from the asymptotic.

The two plane-partition proofs use exact rational and integer certificates, not sampled real parameters. No Lean, external review, or exclusive priority claims are made.

## 2026-11-24: Prove Pantone–Bóna’s second-smallest-terminal asymptotic

The [written proof](results/pantone-bona-second-smallest-terminal/) resolves Conjecture 6.1 for $A_{5,2}$ with exact leading constant $9\sqrt3/(16\pi)$. See [issue #383](https://github.com/1337isnot1337/solved-conjectures/issues/383) for source audit and scope. This is distinct from the other asymptotic conjectures in the same paper.

## 2026-11-24: Prove Pantone–Bóna’s second-largest-terminal asymptotic

The [written proof](results/pantone-bona-second-largest-terminal/) resolves the distinct Conjecture 6.3, with exact leading constant $27\sqrt3/(32\pi)$ for the $A_{5,4}$ class and a general second-largest-terminal result. See [issue #380](https://github.com/1337isnot1337/solved-conjectures/issues/380) for exact supplementary checks and scope. The guessed differential equation is not claimed.

## 2026-11-24: Prove Pantone–Bóna’s asymptotic conjecture

The [written proof](results/pantone-bona-asymptotic/) resolves Conjecture 6.4 with leading constant $625\sqrt3/(192\pi)$ and extends the asymptotic to the equal-index pattern family. See [issue #377](https://github.com/1337isnot1337/solved-conjectures/issues/377) for scope and exact supplementary checks. No D-finiteness, Lean, external referee review, or priority claim is made.

## 2026-11-24: Prove Bétermin’s FCC/BCC cold-spot assertion
- [Meylender–Thalmaier’s truncated-square conjecture](results/meylender-thalmaier-truncated-square/): Proves the strict systolic bound for every truncated-square product and disproves the proposed optimizer.

The [written proof](results/betermin-fcc-bcc-cold-spots/) identifies Gaussian minimizers with deep holes for FCC and BCC at every positive scale, corrects the printed BCC representative, and covers the two families in every rank at least three. [Issue #371](https://github.com/1337isnot1337/solved-conjectures/issues/371) records audit and scope. No optimization over lattice shapes, Lean verification, external referee review or priority claim.

## 2026-11-24: Refute the Coulangeon–Lazzarini two-shell conjecture

The [written disproof](results/coulangeon-lazzarini-two-shells/) gives a dimension-ten lattice with two initial spherical 2-design shells and a third anisotropic shell, and constructs indecomposable lattices delaying the first failure arbitrarily long. [Issue #365](https://github.com/1337isnot1337/solved-conjectures/issues/365) records scope and review. Exact shell enumeration is supplementary; there is no Lean or external referee review.

## 2026-11-25 — Verify Alexandersson’s parking excedance counterexample in Lean

AlexisFimeyer’s [contribution in #630](https://github.com/1337isnot1337/solved-conjectures/pull/630) proves the marked counting recurrence and its bijection with actual parking words, identifies the exact length-17 coefficient row, and proves the existence of a nonreal root. One-step kernel certificates reduce replay memory without changing the theorem. The scoped strict build, axiom audit, and stock-kernel replay passed. [Lean scope](results/alexandersson-parking-excedance/FORMALIZATION.md) · [Receipt](results/alexandersson-parking-excedance/verification/receipt.json).

## 2026-11-24: Refute Alexandersson’s parking-function excedance conjecture

The [exact counterexample](results/alexandersson-parking-excedance/) violates the Laguerre inequality at length 17. Two independent recurrences agree on the coefficient vector. [Issue #106](https://github.com/1337isnot1337/solved-conjectures/issues/106) records scope and previous work. No priority, Lean verification, or external referee review is claimed.

## 2026-11-24: Reconcile publication, issue closure and site validation

Required research-to-main publication and discovery issue closure after review. Preserved the established mathematical-significance ordering while placing the newly published results at their relative ranks. Repaired the malformed Merlini–Sala–Sala summary cells; strengthened website duplicate-entry and ordering checks. The mathematical statements and verification markers are unchanged. The README column now explicitly says Lean verification status.

## 2026-11-24: Publish the reviewed weighted trace identity

The [Tom–Vailaya weighted trace conjecture](results/tom-vailaya-weighted-trace/) is proved for its full stated domain (journal Conjecture 74, arXiv Conjecture 5.16). The proof identifies finite color transfers with the published forest-triple matrices under endpoint reflection. Independent direct forest and proper-color enumerations agree at 585 exact specializations. The separate Ellzey positivity and unimodality conjecture is not claimed. [Issue #338](https://github.com/1337isnot1337/solved-conjectures/issues/338) records scope and review; no Lean or external referee verification is claimed.

## 2026-11-24: Publish five reviewed theta-kernel and Li-coefficient results

- [Nuttall's conjecture](results/nuttall-cumulants/): Complete proposed proof of Conjecture 1 in §4.5: for each finite order r, every sufficiently high repeated-tail cumulant of the Riemann theta kernel is strictly reverse regular through order r on the entire nonnegative node domain. The separate RH-equivalent Toeplitz positivity problem remains unresolved.
- [Coffey–Smith conjecture](results/coffey-smith/): Complete proposed unconditional disproof of Smith’s named conjunction: if RH holds the dyadic coefficient square mass is O(N^(-1/2) log³ N), so both proposed positive-fraction sets have density zero for 0<ε<1/4; without RH the polynomial upper bound fails. The weaker Coffey upper-bound assertion alone is not refuted.
- [Chaudhary–Khmiri–Mazhouda conjecture](results/chaudhary-khmiri-mazhouda/): Complete proposed computer-assisted disproof of the universal automorphic Li-coefficient monotonicity claim. The admissible GL1 imaginary norm twist L(s+8i,χ₋₃) has Re(λ(2)−λ(1))<−3/2, certified by rational interval bounds. No GRH assumption.
- [Merlini–Sala–Sala conjecture](results/merlini-sala-sala/): Complete proposed unconditional refutation of the logarithmic and all-ε subpower growth conjecture for the tiny Li term: limsup |λtiny(n)|/n^(1/4)=∞. The authors’ weaker linear stability conjecture is not resolved.
- [Wang–Yang's conjecture](results/wang-yang/): Complete proposed disproof of the author-manuscript Conjecture 1.10: for every fixed coefficient index, the signed forward differences of the Xi coefficients have infinitely many values of each strict sign. Final journal wording has not been checked; the adjacent logarithmic conjecture is separate.

The original independent mathematical reviews and bounded prior-art audits are preserved. The automorphic Li certificate was independently replayed against its pinned source blob; the other four written proofs need no numerical computation. Corrected trailing whitespace in the README results heading and passed the exact 79-row validator. No Lean or external referee verification is claimed.

## 2026-11-24: Publish four previously reviewed research results

Promoted [Csordas–Vishnyakova conjecture](results/csordas-vishnyakova/), [Cardon–Forgács–Piotrowski–Sorensen–White conjecture](results/cardon-zero-sector/), [Wagner's Laguerre-operator conjecture](results/wagner-laguerre-operator/), [Rowland–Sistos Barrón conjecture](results/rowland-sistos-barron/). The written arguments and prior independent reviews were checked against the original statements. The Cardon rational discriminant and Rowland exact replay through M=100 passed. The Wagner statement is pinned to the author preprint; the Rowland interpretation of pseudo-polynomial is disclosed. No Lean verification or exclusive priority is claimed. Original research records are preserved.

## 2026-11-24: Publish two independently reviewed counterexample packages

The [Caiolo–Ferroni–Hoster](results/caiolo-ferroni-hoster/) and [Higashitani–Kummer–Michałek](results/hkm-ehrhart/) research candidates pass an internal mathematical audit against their original statements and exact-arithmetic replays. Each refutes the whole stated universal conjecture (including its accompanying extension or second clause); each is counted once. The source proofs and verifier blobs are preserved, with review and provenance recorded separately. No Lean verification, external referee approval, or exclusive priority is claimed. Issues [#111](https://github.com/1337isnot1337/solved-conjectures/issues/111) and [#316](https://github.com/1337isnot1337/solved-conjectures/issues/316) track discovery and publication.

## 2026-11-24: Research and publication branch split

The [research branch](https://github.com/1337isnot1337/solved-conjectures/tree/research/research) keeps current investigations and their review materials. The main branch publishes reviewed results, including rigorously established partial theorems if labeled with their exact scope. Git history is retained.

## 2026-11-23 — Full-decider rational simulation and a denominator criterion

The [complex BSS campaign](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/complex-bss-p-vs-np/README.md) gives a uniform polynomial-size rational simulation of every total standard BSS decider using one common deformation parameter. All fixed-input gate germs are holomorphic, and shared pair clearing supplies small polynomial numerator and denominator circuits. A separate proved criterion extracts bounded boundary jets if the supplied denominator is locally nonvanishing near every false input; the decider has not been shown to supply that property. Two independent full reviews checked the construction and criterion. Exact complete-program examples retain false poles and can hide the support beyond exponentially many generic coefficients. An independently checked irreducible bihomogeneous example shows why ordinary coefficient-tensor ranks are not monotone under multiplication by an easy cofactor. The target separation remains unresolved in [issue #248](https://github.com/1337isnot1337/solved-conjectures/issues/248); no solved-result or Lean-status promotion is made.

## 2026-11-23 — Supplied exclusion factors and counting-oracle limits

The [complex BSS campaign](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/complex-bss-p-vs-np/README.md) proves that the supplied exclusion polynomial in a one-equality saturated path removes all extraneous logarithmic poles. The remaining localized polynomial remainder has integer multiplicity values. An irreducible exclusion, or a supplied small complete factor list, gives normalized finite jets with fully charged polynomial cost; arbitrary factor recovery remains open. A separate countable-field argument freezes any countable-range oracle computation of a polynomial value into a small ordinary arithmetic circuit. A uniform cyclic fiber exhibits permanent as a weighted trace even though its unweighted invariants are constant. This excludes a counting-to-value shortcut and leaves graph decision separate. Primary counting, compact Toda and high-degree division results were checked in their exact versions and directions. Two full internal reviews and nine finite exact check groups passed. The HN separation and unrestricted normalization remain unresolved in [issue #248](https://github.com/1337isnot1337/solved-conjectures/issues/248); no Results or Lean-status promotion is made.

## 2026-11-23 — Full partitions, marked gcds and a partial weighted compiler

The [complex BSS campaign](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/complex-bss-p-vs-np/README.md) proves a degree-independent one-split gluing identity for supplied Hilbert certificates and preserves exact failures of free path enumeration, stable row normalization and proper full-transcript compactification. A two-gcd quotient identifies the remaining uniform-double-pole Hermite operation. A short coprime polynomial pair has a canonical modular inverse whose low deformation jet contains the permanent; this blocks a free implicit-inverse operation without claiming gcd hardness. The cutting continuation constructs exact weighted word extensions and sparse-name postponement. Review repaired an omitted slot-selection cost; the resulting O((log tau)^(5/4)) target still depends on an unproved recursive interface, input compression and essential use of the hypothetical HN decider. Each note has a separate internal review. Seven exact symbolic check groups passed. The source audit preserves the direction of IPS implications and the cutting theorem's field and representation hypotheses. [Issue #248](https://github.com/1337isnot1337/solved-conjectures/issues/248) remains open; the target separation is unresolved, with no Results or Lean-status promotion.

## 2026-11-24 — Completed two-family square-chain test and charged-height refinement

The τ campaign (#260, review PR #288) completes the proposed degree-32 extension test for the two displayed Bremner elliptic families, including all Hadamard and rational-scaling variants. Exact cross-family, ordinary-self and complementary resultants are certified by 309, 625 and 379 integer Sylvester determinants. The complementary proof includes a self-contained rational-root exclusion using two congruence-lattice certificates and checks every remaining rational fiber. Michael E. Paul's Table 1 entry 4 example is reconstructed and proved to lie outside the two-family union, so the result does not classify arbitrary chains. A separate consequence of Risler's classical theorem and charged coefficient height improves the recorded integer-root upper bound to 32·2^(s−h_K(s))/sqrt(s+1) and gives μ(n)≥n+sqrt(n/K)+(1/2)log₂n−1 for every nonzero consecutive-root multiple. These remain exponential and nearly linear bounds. New source and extraction audits retain every input-degree and constant-model dependency; exact long-jet and fixed-filter examples expose the remaining unknown-cofactor projection gap. Three workers and the root supplied separate internal reviews and exact certificates. The full τ conjecture, the required superpolynomial all-multiples bound and the BSS separation remain unresolved. Work stays in research, with no Results or Lean-status promotion.

## 2026-11-23 — Generic challenge bounds and hard rational primitives

The [complex BSS campaign](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/complex-bss-p-vs-np/README.md) gives a parameter-uniform conversion from generic challenges to finite challenges while preserving adaptive depth. The reviewed critical-incidence bound excludes polynomial-resource permanent verifiers with o((log m)^(1/3)) generic rounds. The separate uniform simulation retains N^{O(h+1)} cost, and the cutting audit retains weighted cancellation and the contracting-field hypothesis. A charged Laurent-polynomial reduction makes rational exactness equivalent to the permanent graph. Exact sampled differential identities, original-circuit division guards and the earlier graph theorem yield a superpolynomial lower bound for numerical rational primitive circuits on a nonempty Zariski-open set. The proof does not supply a fixed-level upper bound for unrestricted exactness or settle the marked Hermite family. Both arguments have separate internal reviews. The full HN separation remains unresolved in [issue #248](https://github.com/1337isnot1337/solved-conjectures/issues/248); no Results-table or Lean-status promotion is made.

## 2026-11-23 — Marked factors and regular-value certificate obstructions

The [complex BSS campaign](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/complex-bss-p-vs-np/README.md) packs a full saturated accepting path into one short polynomial with a uniquely marked resultant multiplicity. Exact deformed-resolvent and Hermite identities identify sufficient aggregate extraction operations, with the conventional exponential degree costs retained. Pointwise quotient, finite-jet and generator-initial-form counterexamples delimit failed regular-value certificates. The direct regular-value decision-tree obstruction has a complete generic-path and border-factor proof. A projective coefficient-norm sampling argument extends the obstruction to independent existential parameters through explicit scaled critical equations. A short proper rational input with simple and double poles has a hard Hermite part, excluding an unrestricted aggregate closure assertion while leaving the constant-residue marked family open. A square-zero algebra reformulates permanent as a socle coefficient, proves the cost of faithful scalar representations, and supplies a sound but asymptotically incomplete reduced quadratic predicate. The soft-transition counterexample uses a complete correct BSS program. Separate internal reviews and primary-source checks accompany the notes. The aggregate bounds and full HN separation remain unresolved in [issue #248](https://github.com/1337isnot1337/solved-conjectures/issues/248); no Results-table or Lean-status promotion is made.

## 2026-11-24 — Exact square-chain obstruction and root-history reductions

The τ campaign (#260) completes the proposed extension test for the first displayed Bremner elliptic family and its Hadamard transforms: no two nondegenerate rational members have the same normalized prefix and different final coefficient. The written proof includes an explicit rational quotient and an exact degree-88 resultant certificate; a dependency-free verifier checks it through a proved degree bound and 89 exact Sylvester determinants. Both independent workers reviewed all exceptional-domain cases. The construction remains fixed degree and does not resolve τ.

The same checkpoint records an exact prime-by-prime minimum for truncated root-difference energy, its product and first-zero history laws, and a charged cover by primitive-exponent equations. The proposed polynomial energy budget is explicitly proved τ-equivalent and remains unproved. Local exact checks and independent symbolic identities passed. No Results-table or Lean-status promotion was made. See `research/shub-smale-tau/SQUARE_CHAIN_EXTENSION.md`, `COLLISION_ENERGY.md` and `PRIMITIVE_BIRTHS.md`.

## 2026-11-24 — τ root selection and multiplicity obstruction

The open τ campaign (#260) now proves that neighboring shifted gcds do not select the integer parity classes even for the exact consecutive-root polynomial. A charged O(k^3)-gate integer polynomial realizes all 2^k−1 positive multiplicity classes while having at most two integer roots, so a polynomial multiplicity-class count cannot remove the cofactor-support restriction. The translation-boundary test is also preserved. Independent worker reviews and 24 exact gcd checks plus 14 dense cyclotomic multiplicity checks passed. This does not prove τ, radical hardness or a BSS separation. See `research/shub-smale-tau/ROOT_SELECTION.md`.

## 2026-11-23 — Integer gate budgets and adaptive prime-support obstruction

The [Shub–Smale τ research](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/shub-smale-tau/INTEGER_GATE_BUDGETS.md) records exact integer gate inequalities: a coprime addition has a product-of-parent-values resultant budget, units on at least five integer evaluation points have one sign, and nonzero integer multiplication gives a bounded-cancellation escape estimate. None has been amortized over arbitrary circuit histories. The constant-parent and shared-factor cases remain explicit.

A valid two-anchor S-unit bound is paired with a counterexample to its proposed prime-support estimate. The monic primitive squarefree polynomial x^(n+1)−x has exact fixed divisor equal to the product of primes p with p−1 dividing n. The unconditional Fan–Pollack theorem makes this support superpolynomial in circuit length along an infinite sequence, simultaneously at every nonzero integer evaluation, despite at most three integer roots. This does not refute τ or the separate harmonic Galois statistic. Primary theorem versions, finite checks and internal review are recorded in [issue #260](https://github.com/1337isnot1337/solved-conjectures/issues/260).

## 2026-11-23 — Recovering an unknown cofactor of small radical degree

The [Shub–Smale τ research](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/shub-smale-tau/COFACTOR_RECOVERY.md) removes the supplied-factorization hypothesis from the powered-cofactor reduction. A length-s program for H=F_N Q yields a nonzero integer scalar multiple of F_N with O((s+1)(d+1)^14) gates, where d is the number of distinct complex roots of Q. Shifted logarithmic derivatives, a charged finite jet, exact Padé reconstruction and low-degree gcds recover bases grouped by their multiplicities. No program for Q is given, and arbitrary multiplicities and overlap with the prescribed roots are allowed.

All three workers and root reviewed the proof, including nonuniform scalar choices and shared denominator clearing. Five exact recovery cases pass, with deliberately nonintegral residual scalars. This is a restricted circuit-existence theorem: d is not bounded by a polynomial in s, and no unrestricted τ bound or BSS separation is obtained. Research remains tracked in [issue #260](https://github.com/1337isnot1337/solved-conjectures/issues/260).

## 2026-11-23 — Removing arbitrary powers of a small cofactor support

The [Shub–Smale τ research](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/shub-smale-tau/README.md) now proves a charged extraction from F_N times supplied powers whose bases have small total degree. A short geometric-sum identity lifts an integer Bezout certificate to arbitrary powers with logarithmic dependence on their exponents. Endpoint transport removes the cofactor without expanding its powers and permits roots shared with the required interval. All scalar construction and exact quotient costs are included.

The proof was independently reviewed, and exact checks cover the scaled Sylvester certificate, repeated and overlapping bases, and the rational-scalar amendment. The separate symbolic anchored-jet obstruction uses the pinned border theorem and retains its stronger compiler quantifiers. No unrestricted extraction, integer-root bound, or BSS separation is claimed; see [issue #260](https://github.com/1337isnot1337/solved-conjectures/issues/260).

## 2026-11-23 — Anchored cofactor extraction and arithmetic selection

The [Shub–Smale τ research](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/shub-smale-tau/README.md), tracked in [issue #260](https://github.com/1337isnot1337/solved-conjectures/issues/260), gives an endpoint-anchored extraction from a consecutive-root multiple with cost polynomial in the unknown cofactor's degree. A division-free quotient matrix makes the output-degree independence explicit. The degree of an unrestricted cofactor may still be exponential in circuit length.

The checkpoint also proves an integer recurrence for finite jets of a coalescing Boolean inverse, identifies the global coefficient field of a selected Frobenius action, preserves an explicit Newton lift that never becomes exact at finite precision, and extends square-chain prime divisibility to dense integer root sets with an unknown cofactor. The elliptic specialization bound is labeled as a consequence of Mazur's theorem and standard division-polynomial identities. Imported theorem versions, internal reviews and exact finite checks are recorded separately. Citation autolinks damaged by an earlier math-format conversion are repaired.

No full τ bound, counterexample, unrestricted all-multiples lower bound or BSS separation is claimed. The work remains in research, with no Results-table or Lean-status promotion.

## 2026-11-23 — Saturated BSS paths and radical-jet extraction criterion

The [complex BSS campaign](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/complex-bss-p-vs-np/README.md) now retains the full generic accepting path: its equality ideal, saturated by all nonzero branch conditions, has radical equal to the resultant ideal. An explicit four-radical identity makes a degree-independent low-jet radical bound sufficient for the target separation; that bound remains unproved and is kept distinct from the cited Radical Conjecture. Exact examples defeat bounded-input-jet reconstruction, polynomial multiplicity-class counts, and reading regular values from unsaturated rational graph equations. A separate rational identity excludes the proposed orbit-product compression. Monic auxiliary finite fibers give a sound three-block verifier, while bounded-depth root enumeration and Kummer towers reduce to the already excluded finite-prefix format. The actual witness dependencies and costs, internal adversarial reviews, and source distinctions are recorded. The HN separation remains unresolved in [issue #248](https://github.com/1337isnot1337/solved-conjectures/issues/248); no solved-result or Lean-status claim is added.

## 2026-11-23 — Continuous finite-fiber verification and pole-cluster obstructions

The [complex BSS campaign](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/complex-bss-p-vs-np/README.md) gives an actual uniform three-block cyclic finite-fiber verifier, with soundness for all complex matrices and explicit exponential-size completeness. Polynomial-size completeness remains unproved. Finite identity tests exclude polynomial root support and several multiplicity restrictions, with complete witnesses and charged circuit bounds. A finite-etale moving-challenge conversion retains its generic admissibility hypothesis and records exact collision, escape, and rational-sampling failures. Separate counterexamples show cancellation by a relative-invariant resultant cofactor and a permanent coefficient in the first reciprocal trace of a finite pole cluster of a short irreducible denominator; escaping poles carry the opposite coefficient. Internal adversarial reviews and source checks accompany the notes. The HN separation and unrestricted-multiple extraction remain unresolved, and [issue #248](https://github.com/1337isnot1337/solved-conjectures/issues/248) remains active. No solved-results or Lean-status entry is added.

## 2026-11-23 — Tau normalization, prime averaging and quadratic folds

The [tau campaign](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/shub-smale-tau/README.md) proves fully charged reductions between rational, integer and monic integer root bounds; a coefficient-sensitive larger sieve; and simultaneous Galois selection with explicit limitations on prime costs and root identification. Finite-prime approximate inverses imitate every prescribed cut-minor valuation while retaining at most three integer denominator roots. A separate lattice argument proves d ≥ (7/6)log₂N−6 for quadratic compositions constant on N consecutive integers, with exact finite fold certificates. Matrix-power and rational Chebyshev restrictions identify arithmetic information beyond degree. A finite-jet and implicit-branch argument shows that low-degree factors of small arithmetic circuits with arbitrary unary polynomial gates have polynomial border complexity, excluding this ordinary factor-extraction route under the accepted border lower bound. Internal adversarial review and the expanded exact verifier passed. The arithmetic fewnomial optimization remains conditional on the unresolved source dependency, and neither the full tau conjecture nor the all-multiples BSS criterion is solved. Research continues in [issue #260](https://github.com/1337isnot1337/solved-conjectures/issues/260).

## 2026-11-23 — Directional resultant extraction and continued quantifier research

The [complex BSS campaign](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/complex-bss-p-vs-np/README.md) continues with a logarithmic-jet extraction controlled by the number of distinct extraneous cofactor roots along a tagged triangle scaling. Together with the BCJS character filter it forces any polynomial-size hypothetical resultant multiple to have superpolynomial directional squarefree degree in every such direction. A separate bound controls the total squarefree extraneous degree with arbitrary multiplicities. A cofactor-independent divided-difference construction proves polynomial equivalence with charged universal chart Nullstellensatz certificates; an exact short syzygy shows why coordinatewise finite-part extraction cannot be assumed cheap. Recursive critical incidences handle finite witness trees, and a dimension argument converts continuous universal blocks with nondense nonfull fibers to fixed finite tests. Dense moving-hole fibers and failed compactification are preserved as counterexamples. Independent internal reviews and explicit resource bounds accompany each note. The unrestricted cofactor bound and full continuous hierarchy bridge remain open; work is continuing in [issue #248](https://github.com/1337isnot1337/solved-conjectures/issues/248), with no solved-result or Lean-status change.

## 2026-11-23 — Tau inverse reduction and arithmetic source audit

The [continued tau research](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/shub-smale-tau/README.md) proves a linear-cost equivalence between all consecutive-root multiples and charged Boolean inverse representatives, reconstructs the classical block-product upper bound, and records a real-root gate-count consequence of Risler's Proposition 3.1. Adversarial source review found an explicit failure in an unrestricted tropical valuation proof; the stronger proposed arithmetic bounds remain conditional. Exact counterexample and cofactor checks passed. The full tau conjecture and the superpolynomial all-multiples lower bound remain unresolved; no solved-results entry or Lean theorem was added.

## 2026-11-23 — Finite-challenge barriers and restricted resultant multiples

The [complex BSS campaign](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/complex-bss-p-vs-np/README.md) now proves a real critical-point extension for finite residual families, including radical-only correctness and arbitrary deterministic BSS paths. A block version handles finite Boolean universal challenges followed by local complex existential witnesses without keeping the exponential full witness array in the final incidence. These are verifier-format obstructions under the imported permanent bound, not a BSS separation. Separate jet lemmas prove quantitative lower bounds for all nonconstant univariate compositions of the quadratic resultant and for multiples polynomial in the resultant and few small-circuit parameters, with no degree bound on that polynomial dependence. The application extracts jets before specialization, preserving the counterexample to the original order of operations. An explicit bounded-counterexample cutoff example records a failed extension to continuous universal quantifiers. A small irreducible annihilator with a small observable whose trace specializes to the permanent records why an unspecified degree-independent trace operation cannot close the remaining resultant gap. Complete equations, complexity bounds, and internal adversarial reviews are included. Arbitrary resultant cofactors and a fixed-level continuous hierarchy bridge remain unresolved; no solved-results or Lean-status change. [Issue #248](https://github.com/1337isnot1337/solved-conjectures/issues/248).

## 2026-11-23 — Critical-incidence obstruction to permanent certificates

The [critical-incidence proof](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/complex-bss-p-vs-np/CRITICAL_INCIDENCE_BARRIER.md) rules out polynomial-size Boolean divergence potentials for all true numerical permanent instances under the standing border lower bound. Arbitrary instance-dependent complex constants and circuit topology are allowed. A small selected gradient span gives a polynomial-size incidence whose every projected component has codimension at least one; the singular-witness jet theorem then bounds permanent border complexity. The resulting certificate lower bound is exp(Omega((log m)^(4/3))) and holds on a nonempty Zariski-open set for every subthreshold budget. Supporting notes preserve bounded-rank constructions, exact failed gradient ansatz and canonical certificates, nonlinear component-selection counterexamples, and the actual cost of batching sum-check. Independent internal reviews and three finite checkers are recorded separately from formal verification. The BSS separation and arbitrary-resultant-multiple criterion remain unresolved; no solved-results entry or Lean source changes. [Issue #248](https://github.com/1337isnot1337/solved-conjectures/issues/248).

## 2026-11-23 — Shub–Smale tau research and circuit-invariant obstructions

Added [research on the τ-conjecture](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/shub-smale-tau/README.md), tracked in [issue #260](https://github.com/1337isnot1337/solved-conjectures/issues/260), with the initial checkpoint merged through [PR #263](https://github.com/1337isnot1337/solved-conjectures/pull/263). The notes prove exact digit recursions; simultaneous maximal-rank examples even for a primitive squarefree polynomial with one integer root; a primitive squarefree consecutive-root multiple with identical first jets; a cofactor-robust first-coefficient divisibility bound; prime collision and cancellation identities; and elementary superpolynomial prime support in short constants. They reconstruct the classical all-multiples BSS reduction with fixed complex constants removed, and identify two restricted root-count formulations that are equivalent to the missing τ bound. Exact finite checks and independent internal review support the stated lemmas. The τ-conjecture, the needed superpolynomial consecutive-multiple bound, and the BSS separation remain unresolved; no solved-results entry or Lean verification is claimed.

## 2026-11-23 — Existential graph and boundary barriers over C

The [complex BSS research campaign](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/complex-bss-p-vs-np/README.md) now includes reviewed singular-witness and dense omitted-boundary Taylor-jet arguments. Small existential presentations of a low-degree polynomial graph, or dense existential images omitting that graph, imply small border circuits. A graph factor in a degeneration of existential hypersurfaces has the same consequence. With the standing permanent lower bound, these exclude the proposed positive resultant initial-factor and six-resultant existential constructions and place the permanent graph outside both nonuniform NP_C and coNP_C. They do not separate P_C from NP_C. The notes retain the explicit homogenization and escape-order counterexamples, record the analytic primary source, and preserve the earlier restricted smooth-certificate result with its scope. Internal mathematical reviews are distinguished from formal verification; no Lean source or solved-results classification changes. [Issue #248](https://github.com/1337isnot1337/solved-conjectures/issues/248).


## 2026-11-23 — Three-evaluation Fourier filter for quadratic resultants

A [cube-root-of-unity character filter](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/complex-bss-p-vs-np/FOURIER_RESULTANT_FILTER.md) extracts the VNP-hard BCJS grid coefficient from three tensor-resultant evaluations as the first nonzero homogeneous part. It transfers the imported 2^{Omega((log N)^{4/3})} border lower bound to generic quadratic resultants. Even the cofactor 1+a* causes the filter to expose a degree-one term, so the exclusion-complexity target and P_C versus NP_C remain open. [Finite checker](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/complex-bss-p-vs-np/verify_fourier_filter.py).

## 2026-11-23 — Smooth algebraic certificates imply small circuits

The [smooth-certificate note](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/complex-bss-p-vs-np/SMOOTH_CERTIFICATE_BARRIER.md) proves a regular implicit-circuit lemma and its extension to positive-dimensional regular witness fibers. A polynomial graph with such a certificate has polynomial arithmetic-circuit complexity. Using the standing permanent lower bound, this excludes generically regular polynomial-size existential encodings of the permanent graph, but **does not** exclude general NP_C witnesses. [Finite Newton check](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/complex-bss-p-vs-np/verify_smooth_implicit.py).

## 2026-11-23 — Valiant’s extended hypothesis, two-branch research

A variable-scale first lift gives a written superquasipolynomial permanent lower bound under the contracting hypothesis. In the flat case a bounded-degree construction recovers the source exponent, and a cut-dependent placement handles balanced cuts covered by few Hamming balls. A tensor-train decomposition and a shared matrix-product circuit identify where independent rank multiplication fails. The unrestricted flat implication remains open. [Research proofs and finite checks](https://github.com/1337isnot1337/solved-conjectures/tree/research/research/valiant-extended/) · [Issue #256](https://github.com/1337isnot1337/solved-conjectures/issues/256) · [PR #257](https://github.com/1337isnot1337/solved-conjectures/pull/257)

The follow-up derives an [explicit contracting rate](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/valiant-extended/CONTRACTION.md#4-an-explicit-rate-in-the-contracting-case) and an [ordinary partition-rank bound](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/valiant-extended/DIAGONAL.md) for cuts sharing vertex classes, with a finite diagonal-restriction check. [Adversarial review thread](https://github.com/1337isnot1337/solved-conjectures/discussions/259).

The [unitriangular law test](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/valiant-extended/LOCAL_LAW.md) treats every group order outside contraction. A [bipartite graph-tensor comparison](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/valiant-extended/BIPARTITE.md) gives an asymptotic conversion above Type-I unicast capacity and a stronger threshold sufficient for the permanent separation.

## 2026-11-23 — Complex BSS separation research and failed reductions

Added [research notes](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/complex-bss-p-vs-np/README.md) for the full uniform complex BSS separation with arbitrary machine constants. The exact model/source audit was merged through [PR #252](https://github.com/1337isnot1337/solved-conjectures/pull/252). This checkpoint adds the sound growing-alternation weighted protocol, counterexamples to its immediate compressions, a boundary extraction lemma, the sub-log-log alternation threshold, explicit resultant and matching incidences, and multiplier/coordinate-weight obstructions. Exact symbolic checks validate the listed identities. The incidence and fixed-level hierarchy bridges remain unresolved; no separation, new solved-conjecture count, or Lean verification is claimed. The canonical graph lower bound is credited to [PR #249](https://github.com/1337isnot1337/solved-conjectures/pull/249), the Anthropic lower bound, and Bürgisser's factor transfer. [Tracking issue #248](https://github.com/1337isnot1337/solved-conjectures/issues/248).

## 2026-11-23 — Newton-polytope obstruction for BCJS tensor-resultant coefficients

Proved that, after at most one extra padding coordinate, grid-assignment monomials in the BCJS tensor determinant are midpoints of supported monomial exponents 0 and 2v. This rules out isolating the hard degree-s grid coefficient by diagonal monomial rescaling at that padding dimension. [Proof](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/complex-bss-p-vs-np/GRID_NEWTON_BARRIER.md) · [Checks](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/complex-bss-p-vs-np/verify_grid_newton.py). The BSS separation remains open.

## 2026-11-23 — Put major theorem consequences immediately after solved results

Moved the imported-theorem consequences directly below the root Results section and listed the quantitative BSS permanent-graph lower bound first. The catalogue now uses the same category and order. This increases visibility while keeping these consequences separate from the solved-conjecture count and preserving the distinction between the permanent-graph obstruction and the open $`\mathsf P_{\mathbb C}`$ versus $`\mathsf{NP}_{\mathbb C}`$ separation.

## 2026-11-23 — Dimension obstruction for cofactor-robust resultant jets

Proved an orbit-dimension/vanishing-ideal lemma for the quadratic resultant: a special family of dimension $d$ and the natural two GL(n+1) symmetries cannot fill the resultant hypersurface when $d+2(n+1)^2<N_n-1$. An arbitrary nonzero cofactor can then mask all bounded-order jets on that orbit. [Research note](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/complex-bss-p-vs-np/SYMMETRY_JET_BARRIER.md). The result neither bounds the cofactor's circuit complexity nor separates complex P from NP.

## 2026-11-23 — Boolean Hamiltonicity transfer research

Recorded a self-contained investigation of the proposed arithmetic-to-Boolean P-versus-NP transfer. Proved the shared minimal component, all cycle-union coefficients, the first overlap layer, and a restriction preserving Hamiltonicity while killing the exact-cycle predicate. A stronger obstruction gives monotone logarithmic-space predicates with the same logarithmic band of higher components. Small monotone formulas refute the tested all-cut-rank bounds; the support-quotient analysis identifies the remaining efficiency gap. Internal cross-review and exact finite checks passed. No unrestricted circuit lower bound or P != NP proof is claimed, and the work remains outside the solved-results table. [Notes and checks](https://github.com/1337isnot1337/solved-conjectures/tree/research/research/boolean-hamiltonicity/) · [Issue #251](https://github.com/1337isnot1337/solved-conjectures/issues/251) · [PR #253](https://github.com/1337isnot1337/solved-conjectures/pull/253).

## 2026-11-23 — Quadratic resultant exclusion barrier and permanent zero-testing

Added a [research note](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/complex-bss-p-vs-np/RESULTANT_EXCLUSION.md) under the open complex BSS campaign #248. It proves a precise sufficient exclusion-complexity criterion for separating nonuniform P_C from NP_C, records why the exponential degree of quadratic resultants prevents the known border-factor theorem from closing that criterion, and derives a quantitative lower bound for testing whether the permanent is zero. The complex BSS separation remains open; the decision lower bound is a deduction from imported factoring theory and the repository's standing VP != VNP assumption. No new solved-conjecture row was added.

## 2026-11-23 — Adoption of the Anthropic VP ≠ VNP standing assumption

The [agent policy](AGENTS.md#standing-research-assumption-anthropics-vp-versus-vnp-proof) now directs repository work to take Anthropic's VP ≠ VNP theorem, proof, and stated scope as true and accurate. The root index, catalogue, and weighted 3-CNF note now describe the border lower bound as a consequence of this imported theorem rather than as a speculative if-then claim. This research premise is not a statement of independent external review or a new Lean formalization; new reductions and implications still require proofs.

## 2026-11-23 — Quantitative permanent-graph decision consequence

Added a complete written deduction of the $`2^{\Omega((\log m)^{4/3})}`$ deterministic complex computation-tree lower bound for deciding the permanent graph. The proof combines the pinned Anthropic border lower bound with Bürgisser's corrected factor theorem, handles defined divisions through a single path numerator, and records an explicit $`m^2\log m`$ loss, an elementary $`m^{10}`$ alternative, arbitrary constants, and the uniform BSS simulation. Three internal adversarial reviews found no remaining gap after model clarifications. This is recorded as a consequence of imported theorems, with no additional solved-conjecture count, no new Lean-verification claim, and no $`\mathsf P_{\mathbb C}\ne\mathsf{NP}_{\mathbb C}`$ claim. [Proof and audits](https://github.com/1337isnot1337/solved-conjectures/tree/research/research/bss-permanent-graph/) · [Issue #247](https://github.com/1337isnot1337/solved-conjectures/issues/247) · [PR #249](https://github.com/1337isnot1337/solved-conjectures/pull/249) · [Separate BSS campaign #248](https://github.com/1337isnot1337/solved-conjectures/issues/248)

## 2026-11-23 — VP versus VNP application to sparse 3-CNF

Added an explicit 3-occurrence 3-CNF encoding whose weighted satisfying-assignment polynomial projects to the Hamiltonian-cycle polynomial in every characteristic. Finite checks cover n=3,4 and structural checks n=5..8. The border-circuit lower bound is obtained from the Anthropic VP ≠ VNP theorem, now adopted as valid for repository research under `AGENTS.md`. The original source had not received independent human review when this note was first written. This is not counted as an additional solved conjecture. [Construction and checks](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/vp-vnp-bounded-occurrence-3cnf/README.md).

## 2026-11-22 — Written proofs for the iid bounty scope

The fair-label disproof now includes a direct proof of the information inequality on the actual iid experiment. A separate written theorem obtains the positive rates whenever a measurable ERM has the companion paper's global consistency property. The circle-orbit example rules out that premise even when an ordinary Borel ERM exists. [Disproof and information calculation](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/steinke-zakynthinou-agnostic-vc/completed-finite-groups.md#fair-labels-and-improper-learners) · [Positive theorem](results/steinke-zakynthinou-agnostic-vc/PROOF.md#a-measurable-globally-consistent-erm-suffices)

## 2026-11-22 — Fair-label information lower bound for the literal iid conjecture

For each positive sample size $`n`$, a VC-one benchmark with $`8n^2`$ sectors forces CMI at least $`n/32`$ for empirical tolerance at most $`1/8`$, even with improper outputs. Lean verifies the outer-measure realization of every label pattern on distinct sectors, the collision bound, the population loss, and the conclusion from the COLT paper's generalization inequality. [Lean theorem](lean/Conjectures/AgnosticVC/FairLabelObstruction.lean) · [Written proof](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/steinke-zakynthinou-agnostic-vc/completed-finite-groups.md#fair-labels-and-improper-learners)

## 2026-11-22 — The actual seeded CMI experiment

Lean verifies that a proper learner meeting the empirical rate cannot yield a measurable ambient output random variable in the original independent pool, selector and seed experiment. Restricting to the all-zero selector transfers completed measurability to the first column and seed. The proof uses ordinary seed expectations on each sample. [Lean theorem](lean/Conjectures/AgnosticVC/ConditionalJointObstruction.lean) · [Written proof](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/steinke-zakynthinou-agnostic-vc/completed-finite-groups.md)

## 2026-11-22 — Ambient standard Borel output and the agnostic VC disproof

Lean verifies the finite-support disproof when conditional information is computed on the ambient standard Borel space of classifier codes. Properness still restricts the output to the trace Borel subclass. The manuscript now contains the finite-support construction, the conditional-law reduction, and the class-by-class uniform-convergence proof. [Lean theorem](lean/Conjectures/AgnosticVC/ConditionalJointObstruction.lean) · [Manuscript](results/steinke-zakynthinou-agnostic-vc/paper.pdf)

## 2026-11-22 — Completed-iid rates for unbounded supports with bounded overlap

Lean verifies the reweighted iid experiment and its occupancy bound. Under a sharp expected outer uniform-deviation bound $`B\sqrt{d/n}`$, the integer-noise learner attains actual iid CMI at most $`20s`$ nats and expected empirical excess at most $`(16B^2+9)\sqrt{d/n}`$ for overlap $`s`$, allowing infinite supports. [Lean learner theorem](lean/Conjectures/AgnosticVC/NoisySupportSharpIid.lean) · [Lean null-support argument](lean/Conjectures/AgnosticVC/IidRectangleDensity.lean)

## 2026-11-22 — Completed-iid rates for bounded-size supports

Lean verifies a proper integer-noise learner with actual iid CMI at most $`20s`$ nats and expected empirical excess at most $`m/n+8/\sqrt n`$ for support size $`m`$ and pointwise overlap $`s`$. Almost surely the eligible names have positive marginal support mass, so they belong to a countable family for each iid law. [Combined Lean theorem](lean/Conjectures/AgnosticVC/NoisySupportIid.lean) · [Proof and scope](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/steinke-zakynthinou-agnostic-vc/completed-disjoint-support-learner.md)

## 2026-11-22 — Disproof from the actual iid selector/output law

Lean verifies the empirical-rate obstruction assuming the actual conditional selector/output law in iid CMI has a measurable version on the completed pool. The proof permits arbitrary pointwise output measures and almost-everywhere agreement. The all-zero selector gives the learner's kernel after dropping the independent ghost column. [Lean disproof](lean/Conjectures/AgnosticVC/ConditionalJointObstruction.lean) · [Proof and scope](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/steinke-zakynthinou-agnostic-vc/completed-finite-groups.md)

## 2026-11-22 — Finite score channels for agnostic VC learning

Lean verifies the fixed-pool information bound of $`20s`$ nats for integer-noise signed support counts with overlap $`s`$, together with the argmax regret and eligibility bounds. A written completed-iid learner gives 12 nats and $`2/\sqrt n+2/n`$ empirical excess for disjoint two-point supports. [Finite Lean channel](lean/Conjectures/AgnosticVC/CompactScoreNoise.lean) · [Completed-iid proof](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/steinke-zakynthinou-agnostic-vc/completed-disjoint-support-learner.md)

## 2026-11-22 — Sharp uniform convergence for the universal-measurability counterexample

Lean verifies that one VC-one class with disjoint two-point supports defeats every candidate empirical-rate constant when the scalar expected loss must be universally measurable on the sample space. The [same class has a measurable uniform-deviation envelope](lean/Conjectures/AgnosticVC/FiniteSupportUniform.lean) of expected value at most $`2/\sqrt n+2/n`$ for every iid law and sample size. The disproof uses a dependent pushforward to test universal measurability and all-sample accuracy at the resulting size. [Lean disproof](lean/Conjectures/AgnosticVC/CompletedFiniteGroups.lean) · [Proof and scope](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/steinke-zakynthinou-agnostic-vc/completed-finite-groups.md#universal-measurability-on-the-sample-space)

## 2026-11-22 — Randomized-learner formulation of the completed-iid obstruction

The [finite-support disproof](lean/Conjectures/AgnosticVC/CompletedFiniteGroups.lean) now directly quantifies over a learner with an arbitrary independent random seed. Measurability of its realized loss under the completed product experiment gives the scalar measurability used in the obstruction. All proper hypotheses have population loss one under the test law. [Proof and source scope](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/steinke-zakynthinou-agnostic-vc/completed-finite-groups.md)

## 2026-11-22 — Measurable reconstruction for the agnostic VC learner

Lean proves both agnostic rates for classes whose finite traces can be realized by countably many measurable proper reconstructions using at most $`k`$ input rows. The same learner has expected empirical excess at most $`583\sqrt{d/n}`$ on every sample and actual iid CMI at most $`197{,}120d+32k`$ nats. The [circle-orbit class](lean/Conjectures/AgnosticVC/OrbitIidRates.lean) admits one-row reconstruction and attains both rates with a Borel learner, even though the globally ordered representative rule fails there. [General Lean theorem](lean/Conjectures/AgnosticVC/LocalReconstructionMeasurable.lean) · [Argument and scope](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/steinke-zakynthinou-agnostic-vc/measurable-local-reconstruction.md)

## 2026-11-22 — Scalar expected-loss obstruction for agnostic VC learning

The [Lean disproof](lean/Conjectures/AgnosticVC/CompletedFiniteGroups.lean) for completed iid laws now needs only measurability of the real-valued expected empirical loss. For any proposed universal constant the exhibited VC-one class forces this quantity to be nonmeasurable if the empirical excess bound holds on every sample. The scalar obstruction is independent of the output sigma-algebra. [Proof and scope](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/steinke-zakynthinou-agnostic-vc/completed-finite-groups.md)

## 2026-11-22 — Distribution-free agnostic VC conjecture in the framework paper

Lean verifies [Conjecture 4.18](https://arxiv.org/pdf/2001.09122v3) with common constant $`19{,}712`$ for every positive sample size and arbitrary hypothesis classes of finite positive VC dimension. The [theorem](lean/Conjectures/AgnosticVC/FixedPairing.lean) gives both the bound on whole-output selector information for every fixed paired pool and the samplewise empirical rate. It includes $`n<d`$ by using a constant proper learner. The COLT formulation uses the iid CMI and its [measurability scope](results/steinke-zakynthinou-agnostic-vc/SCOPE.md) is recorded separately.

## 2026-11-22 — Finite-support counterexamples for completed-iid proper learners

Lean verifies the [failure of the Conjecture 6 empirical rate](lean/Conjectures/AgnosticVC/CompletedFiniteGroups.lean) for every proposed constant on a VC-one class with finite disjoint supports. The [written proof](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/steinke-zakynthinou-agnostic-vc/completed-finite-groups.md) gives distribution-uniform convergence in outer probability and quantifies why it lacks the absolute VC-one bound at the counterexample sample size. A [separate Lean counterexample](lean/Conjectures/AgnosticVC/BorelChoiceObstruction.lean) covers globally Borel kernels on standard Borel spaces with Borel trace feasibility. The scope of the original bounty awaits clarification.

## 2026-11-22 — Information bound for every fixed pairing in agnostic VC learning

The [fixed-pairing theorem](lean/Conjectures/AgnosticVC/FixedPairing.lean) bounds whole-output selector information by $`19{,}712d`$ nats on every paired pool, using the same proper learner and samplewise empirical bound. Comparing the two choices in a row to the common deleted sample removes the permutation average. The population theorem still requires the stated measurability convention. Added written scope results for [Borel trace feasibility](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/steinke-zakynthinou-agnostic-vc/borel-traces-and-randomized-selection.md) and [dominated marginals](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/steinke-zakynthinou-agnostic-vc/dominated-marginals.md).

## 2026-11-22 — Shifted lonely runner counterexamples for 18 ≤ n ≤ 54

Added [exact counterexample certificates](results/shifted-lonely-runner-counterexamples/) to the shifted Lonely Runner Conjecture for every `n` with `18 <= n <= 54`, a partial answer to Zhang's Question 8.5 (arXiv:2608.13599v3), which was open for `18 <= n <= 94` after Blanco–Criado–Santos (`5 <= n <= 17`) and Poliakova (`n >= 95`). Each certificate is checked exactly by a standard-library verifier with two independent methods. The range `55 <= n <= 94` remains open and nothing is claimed there; the heuristic searches stopped at `n = 55`, which is not evidence for the conjecture. For `41 <= n <= 54` the speeds are not `1..n`, as the conjecture allows. Not formalized. Contributed by [@aadrianvv](https://github.com/aadrianvv). [Issue #110](https://github.com/1337isnot1337/solved-conjectures/issues/110)

## 2026-11-22 — Graphs with circular chromatic index in the upper half for Δ ≡ 3 mod 4

Extended the answer to the remark in Section 8 of Mazák and Zrubák, *Circular chromatic index of small graphs* (arXiv:2603.08822), that no graph with maximum degree `Δ >= 8` and circular chromatic index in `(Δ+1/2, Δ+1)` was known, to `Δ ≡ 3 mod 4`. For every `g >= 15` an explicit simple graph on `6g+1` vertices has `Δ = 4g+3` and `χ'_c = Δ+2/3`. The construction uses a one-parameter family of base vertex sets for the perfect `(2n,3)`-colouring of a `4g`-regular circulant, in which every colour class lives on two cyclic intervals of sizes 6 and `2g-6`; besides the two blocks of length-1 edges of Family B, a third inserted block of edges of lengths 3 and 5 fits, and the base matchings, with lengths avoiding 1, 3 and 5, are given by explicit formulas. Stored SAT certificates give the same for `6 <= g <= 14`, so every `Δ ≡ 3 mod 4` with `Δ >= 27` has such a graph. With the earlier results, every `Δ >= 8` except `Δ ∈ {9, 11, 13, 15, 17, 19, 23}` now has one; for the remaining values the forward insertion framework of the note admits no example. The package contains the written proof, a standard-library verifier for `15 <= g <= 60` and the certificates, an independent standard-library re-check, and the report and scripts of one independent model referee pass, which found no mathematical errors; its minor points are applied. No Lean verification was performed.

## 2026-11-22 — Graphs with circular chromatic index in the upper half for Δ ≡ 2 mod 4

Extended the answer to the remark in Section 8 of Mazák and Zrubák, *Circular chromatic index of small graphs* (arXiv:2603.08822), that no graph with maximum degree `Δ >= 8` and circular chromatic index in `(Δ+1/2, Δ+1)` was known. For every `g >= 6` an explicit simple graph on `6g+1` vertices has `Δ = 4g+2` and `χ'_c = Δ+2/3`, and a variant with one insertion block has `Δ = 4g+1` and `χ'_c = Δ+2/3`. The proof solves the base matching problem of Family B in the circulant result by explicit formulas for every `g >= 7` (a stored base for `g = 6`), where SAT had solved it only for `6 <= g <= 13`. With the computer-checked colourings of `K_n-tK_2` for `Δ = 10, 14, 18, 22` and the circulants for `Δ ≡ 0 mod 4`, every even `Δ >= 8` has such a graph, and so does every `Δ ≡ 1 mod 4` with `Δ >= 21`. `Δ ≡ 3 mod 4` and `Δ = 9, 13, 17` remain open. The package contains the written proof, a standard-library verifier for `6 <= g <= 60` and the certificates, and the report and scripts of one independent model referee pass, which found no errors; no Lean verification was performed.

## 2026-11-21 — Circular chromatic index of complete graphs minus a few edges

Gave a second, shorter proof of Conjecture 2 of Mazák and Zrubák, *Circular chromatic index of small graphs* (arXiv:2603.08822): `χ'_c(K_n-e) = n` for every odd `n >= 7`. A smaller value would give a cyclic order of the edges in which every `m = (n-1)/2` consecutive edges are disjoint, and the residue classes of such an order force an edge to occur twice. Determined `χ'_c` for `K_n` minus two or three edges for small `n`, among them `χ'_c(K_11-2K_2) = 32/3`, which refutes the note's own earlier Conjecture H; the corrected Conjecture H′, `χ'_c(K_n-F) = n - 1/⌈m/t⌉` for `2 <= t <= m-1`, is stated without proof. Explicit colourings below `n` for `K_n-tK_2` at `n = 15, 19, 23, 27, 47` give graphs with `χ'_c` in `(Δ+1/2, Δ+1)` for `Δ = 14, 18, 22, 26, 46`. The package contains the written proof, the 32 colourings with a standard-library checker, a standard-library exhaustive search for perfect sequencings, optional SAT exclusions with a DRUP certificate generator, and the reports and scripts of two independent model referee passes. The colourings for `n = 19, 23, 27, 47` and the symmetry and structure lemmas added after the second pass are unrefereed; no Lean verification was performed.

## 2026-11-22 — Wild number of complete graphs for n ≥ 155

Added a [partial result](results/wild-number-complete-graphs/) on Conjecture 6.1 of Dawkins, Nappo, Tong and Zimbizi (arXiv:2610.22142): for every `n >= 155` and every minimum proper edge colouring of `K_n`, the wild number equals the source's lower bound. Odd `n >= 189` uses the lopsided local lemma (Theorem A), odd `155 <= n <= 187` a self-contained cluster-expansion lemma with sharper counts (Theorem B), and even `n` follows from `n-1`. Each theorem passed one independent model referee pass; the standard-library verifier rechecks every numerical condition in exact rationals. The conjecture stays open for `13 <= n <= 154`, the limit of this counting method; partial material for continuing, including a reduction of `n = 13, 14` to a finite statement and an unfinished cube-and-conquer run, is kept in the result's `continuation/` folder. Contributed by [@aadrianvv](https://github.com/aadrianvv). No Lean formalization. [Issue #155](https://github.com/1337isnot1337/solved-conjectures/issues/155)

## 2026-11-21 — Steinke–Zakynthinou’s agnostic VC learning conjecture

The [manuscript](results/steinke-zakynthinou-agnostic-vc/paper.pdf) and [combined Lean theorem](lean/Conjectures/AgnosticVC/Theorem.lean) establish a partial result on the unrestricted Conjecture 6. The multiscale entropy learner returns a member of the original hypothesis class. Its original selector-information and all-sample empirical bounds are verified under the [documented measurability conventions](results/steinke-zakynthinou-agnostic-vc/). Independent review is pending.

## 2026-11-21 — Measurable scope and source-class review

The [general VC manuscript](results/steinke-zakynthinou-agnostic-vc/paper.pdf) now includes a formal correspondence for both VC-one obstructions to Borel learning. The positive result covers countable domains and classes with a countable measurable subclass that realizes every finite trace. The [threshold review](results/steinke-zakynthinou-thresholds/LEAN_REVIEW.md) verifies the returned cutoff as a Borel Markov kernel, the source comparator at infinity, and the integrated KL relative to the actual conditional marginals. The [combined threshold theorem](lean/Conjectures/SteinkeZakynthinou.lean) uses the same learner for all iid labeled distributions and all fixed samples.

## 2026-11-21 — Proper agnostic thresholds with constant original CMI

Added a complete proposed proof of the separately rewarded threshold
case of Steinke–Zakynthinou Conjecture6. A shifted folded-rank tree,
private-tag rounding, and an adaptive rank-code conversion give a proper
finite real threshold with constant original information for every iid
distribution and the required empirical accuracy on every sample.
The complete argument passed two independent internal reviews and a fresh
primary-source audit found no exact prior resolution. The finite checker
audits indexing only; the theorem is not Lean-verified. No sponsor
acceptance, prize submission, bonus, or payment is claimed. This is one
target, with the proper and improper offers treated as alternatives.
[Proof and record](results/steinke-zakynthinou-thresholds/) ·
[Research issue](https://github.com/1337isnot1337/solved-conjectures/issues/223)


## 2026-11-21 — Gröchenig result withdrawn after checked prior resolution

The upper-density assertion in Gröchenig’s Problem 4.12 was already refuted by Alexanja Senke’s public September 2026 manuscript. The [correction record](https://github.com/1337isnot1337/solved-conjectures/tree/research/research/bounty-continuation-2026-11-21/grochenig-prior-resolution/) contains two independent mathematical reconstructions, root’s check, the exact hypothesis comparison, signed-source chronology, and the separate direct-payment eligibility audit. The earlier proof gives coefficient sign-change densities 1/Q and infinite upper zero density for every positive integer Q; Q=2 strictly covers the repository’s upper-density counterexample. The separate lower-density and central-dominance sections of the prior manuscript were not certified by this review.

Under the collection-exclusion rule, removed the duplicate result directory and independent writeups, fourteen dedicated Lean modules, their root imports and required endpoints, replay entries, the Python verification step, catalogue and site references, and the dedicated historical verification packet. All six reused KVZ modules and their canonical verification evidence remain. The valid independent construction and completed Lean verification remain available at [commit 628270dc](https://github.com/1337isnot1337/solved-conjectures/commit/628270dc5e07d7924de265d2ac1beee4b5634b80).

The selected joint ledger changes from twelve packages and ten named families to eleven packages and nine named families. The parallel campaign’s current table changes from thirteen packages to twelve, comprising seven proofs and five disproofs. These arithmetic corrections do not constitute a fresh review or bounty-eligibility endorsement of the other packages. Earlier entries below record historical actions and are superseded wherever they count Gröchenig as a new resolution. No exact direct-payment offer was verified, and the paid-target continuation remains at zero completions.


## 2026-11-21 — Gröchenig upper-density disproof verified in Lean

Lean constructs one real coefficient sequence in ℓ¹(ℤ), with absolute mass one and support on the even integers. Its actual Gaussian shift sum is nonzero, has an entire extension and locally finite real zeros, and satisfies D⁺(c)=1/2 and D⁺(Z(f))≥1. Coefficient sign changes use the source convention that skips zero coefficients.

All 20 modules in the exact closure passed strict source checks, the complete owned-declaration axiom audit, and stock-kernel replay. The closure contains 14 Gröchenig modules and six reused KVZ kernel modules; all 20 were audited as owned modules. The audit covers 351 declarations, 310 theorem declarations, 78 private declarations, and 157 required endpoints. The [receipt](https://github.com/1337isnot1337/solved-conjectures/blob/628270dc5e07d7924de265d2ac1beee4b5634b80/docs/verification/lean-grochenig-20261121/receipt.json) retains the exact gate evidence.

The separate lower-density inequality remains unresolved here. The combined repository gate and hosted validation remain separate checks.

## 2026-11-21 — Chen–Khare–Sahi stable Hall witness checked

Added twelve Lean modules and checked their exact nineteen-module closure. At q=1/10 and t=9/10, the full eleven-partition degree-six family is identified by stable Hall orthogonality, monic dominance triangularity and literal polynomial coordinates. Its three-variable specialization has positive normalization and yields the full Muirhead-semiring counterexample. The degree-three truncated finite-Hall conflict is also proved. Strict sources, both complete owned/private audits and the exact stock replay passed. The README remains partial because the manuscript convention is unresolved and the broader families still have only the eigenfunction identification. The previous sixteen-module compatibility receipt and its pending replay are preserved separately; neither the combined repository gate nor hosted validation is claimed.


## 2026-11-21 — Gamma-quotient theorem verified in Lean

Completed the all-order Karp–Vishnyakova–Zhang gamma-quotient theorem on its
full real translated domain. Proved the exact sign, noninteger strictness,
positive-integer cutoff, and third-order signature correction. The literal
gamma convolution and all Wronskian and determinant-composition obligations
are proved internally. All 15 strict sources, the complete owned/private
audit, and exact stock-kernel replay passed. Registered 62 required endpoints
and marked the result complete. The combined repository gate and hosted
validation remain pending.


## 2026-11-21 — Chen–Khare–Sahi strict compatibility repairs

Replaced repeated monomial-product proof search with 115 proved pair identities and an indexed degree-at-most-six dispatch. Repaired strict-linter, arithmetic-normalization and deprecated-lemma failures in Translate, Boundary, Parameter and Unique. The existing public definitions and theorem statements are unchanged.

All 16 existing modules passed fresh strict Lean 4.35 compilation with warnings treated as errors. The complete owned/private audit checked 1,454 declarations, including 1,254 theorem declarations, 816 private declarations and all 49 required endpoints. Only `propext`, `Classical.choice` and `Quot.sound` are allowed. Independent stock-kernel replay of the revised closure and the combined repository gate remain pending. The README badge remains partial.

The current endpoints use the standard monic triangular Macdonald eigenfunctions. Stable Hall orthogonality followed by specialization is being formalized separately. The manuscript's literal truncated finite-variable Hall pairing conflicts with that convention; the [degree-three diagnostic](https://github.com/1337isnot1337/solved-conjectures/issues/201#issuecomment-7065320695) must be reconciled before claiming a full literal-source formalization.

## 2026-11-21 — Chow conjecture fully verified in Lean

Proved consecutive interlacing of the ordinary type-D Eulerian polynomials
for every rank at least two, with strictness from rank three. The source
bridge enumerates actual even-signed permutations and proves the refinement
recurrence and factor of two. All 11 sources, the 329-declaration audit,
and exact stock-kernel replay passed. Registered 48 required endpoints
and updated the result badge to complete. The combined gate remains pending.

## 2026-11-21 — Oravcová–Soták relative theorem formalized

Added nine modules for the actual integer distance graphs, all explicit coloring certificates and unbounded families, and the complete classification deduction relative to four stated spectrum propositions. Preserved @aadrianvv’s proof and certificate attribution. All nine new modules passed strict compilation with warnings treated as errors. The exact 28-module project closure passed an all-owned audit of 1239 declarations (1084 theorem declarations and 40 required endpoints) and independent stock-kernel replay. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. The README remains partial because `R5`–`R8` are still hypotheses. The shared-package gate remains pending.

## 2026-11-21 — Original Vishnyakova theorem verified in Lean

Completed the sampled-sequence theorem using all ordered finite Toeplitz
minors of the actual polynomial samples. Proved the centered disk and
attainment of the exact radius within that class, including initial zero
samples in the necessity argument. The full 17-module closure also contains
the weighted theorem. Strict sources, the 439-declaration audit, and stock
kernel replay passed. Registered 40 additional endpoints, bringing the
required total to 66. Updated the result badge to complete.
The combined repository gate remains pending.

## 2026-11-21 — Vishnyakova weighted theorem verified in Lean

Proved the centered-disk bound and exact attained outer radius for every
positive weight and positive degree in the source transform class.
The formalization constructs the actual transform and proves the required
polarization and tridiagonal arguments. Strict source checks, an audit of
238 owned declarations, and exact stock-kernel replay passed.
Registered seven modules and 26 required endpoints. The original sampled
class is undergoing separate checks, so the overall badge remains partial.
The combined repository gate and hosted validation remain pending.

## 2026-11-21 — Bernardi–Morales conjectures formalized

Formalized both published delta-process Conjectures 27–28 for every stated parameter, using literal subset tuples, cyclic interval events and the next-complement delta rule. The tree count allows arbitrary fixed color maps; the event identity and source probability determinant use fixed surjections. The 13-module closure passed strict compilation with warnings treated as errors, an all-owned audit of 269 declarations (205 theorem declarations and 23 required endpoints), and independent replay by the pinned stock kernel. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Updated the complete result-level badge and all registrations. The shared-package gate remains pending.

## 2026-11-21 — Ekhad–Zeilberger’s most unfair bet conjecture

**November 25 overlap-score checkpoint.** Lean now proves the exact finite overlap covariance identity and the maximum of the unrestricted normalized overlap score, including the two equivalent endpoint forms and strict exclusion of nonconstant losers. The probabilistic asymptotic link and the full-alphabet restriction remain written. [Lean scope](results/ekhad-zeilberger-unfair-bet/FORMALIZATION.md).

**November 25 variance checkpoint.** Lean gives a finite lower variance bound for the literal signed window count at every sample length, using the orthogonality of the two-endpoint projection. Equal interiors with a one-step cross-overlap force zero self-overlaps for nonconstant words. The overlap covariance identity and asymptotic win probability remain separate. [Lean scope](results/ekhad-zeilberger-unfair-bet/FORMALIZATION.md).

**November 25 Lean checkpoint.** The finite overlap bounds, exact constant-loser extremizers, and the variance floor for at least three letters are now verified. The probabilistic expansion and binary projection remain separate. [Lean scope](results/ekhad-zeilberger-unfair-bet/FORMALIZATION.md).

Proved the extremal asymptotic advantage for every word length from a variance lower bound for overlapping occurrences. The proof also classifies extremizers with and without a full-alphabet requirement. [Proof and checker](results/ekhad-zeilberger-unfair-bet/) · [Research issue](https://github.com/1337isnot1337/solved-conjectures/issues/219)

## 2026-11-21 — Kauers–Koutschan recurrence conjecture

Added a complete proposed proof of the two published recurrences for A189281. Inclusion–exclusion and a rank-one complex Gaussian matrix give a Schur sum in derangement numbers. Exact polynomial substitution gives zero for every coefficient in both parity classes. [Proof and checker](results/kauers-koutschan-recurrence/) · [Research issue](https://github.com/1337isnot1337/solved-conjectures/issues/218)

## 2026-11-21 — Horňák–Woźniak short arms of length at most two

Proved arbitrary vertex decomposability for tripods with positive short arm at most two under source tests 1 and 5, and established the unique-largest balancing step for general star graphs. Strict compilation, a 958-theorem full-chain axiom audit and isolated kernel replay passed. The general all-small case, four-arm reduction, existence constructions and combined gate remain.

## 2026-11-21 — Horňák–Woźniak short-arm subset and merging

Proved unconditionally that a positive partition with a sublist summing to the shortest arm is realizable, and reduced all other partitions to the case without a mergeable noncentral pair. Strict compilation, a 945-theorem full-chain axiom audit and isolated kernel replay passed. The remaining all-small case, four-arm reduction, existence constructions and combined gate remain.

## 2026-11-21 — Circular-index main theorems and regular examples formalized

Added the complete all-parameter circulant construction, the 25-vertex theorem, and both 31/33-vertex regular examples, with actual real circular chromatic indices, regular degrees, and vertex-deletion connectivity. The atom and subgroup proofs are internal to the formalization. The 19-module closure passed strict sources, an all-owned audit of 601 declarations/500 theorem declarations and 171 required endpoints, and exact pinned stock-kernel replay. Registered the checked closure and synchronized the partial overall badge; the nonregular examples, remaining Section 7 claims, combined package gate, and hosted validation remain separate.

## 2026-11-21 — Horňák–Woźniak partitions containing a large part

Proved that source tests 1 and 5 realize every positive tripod partition containing a part larger than the positive shortest arm, using greedy grouping and graph refinement. Strict compilation, a 910-theorem full-chain axiom audit and isolated kernel replay passed. All-small partitions, the four-arm reduction, existence constructions and combined gate remain.

## 2026-11-21 — Wright log-concavity conjecture disproved in Lean

Formalized the actual infinite Wright series and a continuous counterexample
family with beta zero and alpha tending to one from below. Gamma reflection,
a uniform summable coefficient bound, and dominated convergence give a strict
three-point midpoint violation. This refutes the original universal conjecture;
the written positive-beta refinements remain unformalized. Strict source
compilation, an audit of all 25 owned declarations including eight private
declarations, and independent pinned-kernel replay passed. Registered the module
and four required theorem endpoints. The combined repository gate remains
separate and pending.

## 2026-11-21 — Horňák–Woźniak large-part reduction

Proved the complete tripod reduction for partitions whose parts all exceed a positive shortest arm, by graph-level balancing and well-founded induction. Also proved refinement when discarded central pieces fit the otherwise unused shortest arm. Strict compilation, an 878-theorem full-chain axiom audit and isolated kernel replay passed; the small-part and four-arm reductions, existence constructions and combined gate remain.

## 2026-11-21 — Gilmore full matching identity rechecked

Rechecked the complete Gilmore source with strict compilation, an all-owned declaration/axiom audit and stock-kernel replay. The checks cover 449 declarations and all 20 required endpoints, including the exhaustive matching bijection and preservation of the source statistics. Corrected the stale landing page and synchronized the full result-level verification badge. The combined package gate and hosted validation remain separate.

## 2026-11-21 — Babai spectra fully formalized; Baricz–Pogány source recurrence verified

Added the complete Babai path-spectrum formalization, including both bounds and constructive realization for every allowed value, with credit to aadrianvv for the written proof. Added source-recurrence uniqueness and a direct source-recurrence inequality endpoint to Baricz–Pogány. Both passed strict source checks, all-owned axiom audits, and stock-kernel replay. Registered the Babai module and all new endpoints, corrected the stale Baricz–Pogány landing-page claims, and synchronized the full result-level badges and status pages. The combined repository gate and hosted validation remain separate.

## 2026-11-21 — Horňák–Woźniak tripod subset criterion

Proved both directions of the middle-window subset criterion when all parts exceed the shortest arm, the largest-center assignment exchange, and the coarsening step with the central part kept largest. Strict compilation, a 777-theorem full-chain axiom audit and isolated kernel replay passed. The remaining Barth reductions, existence constructions and combined gate remain.

## 2026-11-21 — Horňák–Woźniak arm assignment extraction

Proved that every connected star-graph partition assigns its noncentral classes to arms with total size at most each arm capacity. Strict compilation, a 746-theorem full-chain axiom audit and isolated kernel replay passed. The remaining Barth reduction, existence constructions and combined gate remain.

## 2026-11-21 — Horňák–Woźniak reduction foundations

Proved graph tiling for arbitrary positive lists of pieces and two subset-sum balancing steps with a termination measure. These are supporting lemmas, not the full Barth AVD reduction. Strict compilation, a 741-theorem full-chain axiom audit and isolated kernel replay passed; the remaining reduction and combined gate are pending.

## 2026-11-21 — Horňák–Woźniak source test 5

Formalized the count-based existence trigger for source test 5 and used it with tests 1 and 2 in the regular and exceptional graph partition cases. Strict compilation, a 709-theorem full-chain axiom audit and isolated kernel replay passed. Admissibility index ranges, AVD reductions, existence constructions and the combined gate remain.

## 2026-11-21 — Horňák–Woźniak source-level exceptional case

Removed the stronger pairwise restriction from the positive-slack endpoint and proved all exceptional-size graph partitions under the weaker source-derived residue bounds and a fifth-test witness. Strict compilation, a 681-theorem full-chain axiom audit and isolated kernel replay passed. Test 5 translation, general AVD reductions, existence constructions and the combined gate remain.

## 2026-11-21 — Horňák–Woźniak source-level zero slack

Derived the weaker residue consequence of original tests 1 and 2 and proved all exceptional zero-slack graph partitions under it and a fifth-test witness. Positive slack still assumes stronger pairwise bounds. Strict compilation, a 580-theorem full-chain axiom audit and isolated kernel replay passed; source translation, AVD reductions and combined gate remain.

## 2026-11-21 — Horňák–Woźniak hypothesis scope correction

The exceptional formalization assumes all pairwise residue bounds, stronger than the original admissibility tests. The repository checker accepts capacities (4, 7, 11), with residues (0, 1, 1) modulo 2, which violate the stronger bound. The formal theorem remains conditional on its explicit hypotheses; extending it to all admissible cases remains work.

## 2026-11-21 — Horňák–Woźniak exceptional graph partitions

Proved all zero-slack exceptional cases, combined them with positive slack, and constructed the exceptional-size partitions for the tripod and for a reserved short arm under explicit residue and fifth-test hypotheses. The full chain passed a 541-theorem axiom audit and isolated kernel replay. Original-test translation, general AVD reductions, existence constructions and the combined gate remain.

## 2026-11-21 — Horňák–Woźniak zero-budget criterion

Proved the exact zero-budget packing criterion and the exceptional zero-slack branch with two positive quotient gaps. The full HornakZero dependency chain passed a 492-theorem axiom audit and isolated kernel replay. Correction: the earlier 407-theorem audit imported HornakReservedArm rather than HornakLargest; the new audit includes both. Other zero-slack cases, AVD reductions and the combined gate remain.

## 2026-11-21 — Horňák–Woźniak positive-slack exceptional case

Derived the largest-count endpoint and all smaller counts with positive quotient slack under the stated residue and fifth-test hypotheses, and handled a fourth arm reserved in the center. Strict compilation, a 407-theorem axiom audit of the reserved-arm dependency and isolated kernel replay passed; zero slack, full reductions and the combined gate remain.

## 2026-11-21 — Horňák–Woźniak rho-two endpoint

Proved the three-arm rho-two endpoint construction through actual connected partitions under its explicit endpoint equations, residue conditions and fifth-test input. Strict compilation, a 396-theorem axiom audit and isolated kernel replay passed; the smallest-count endpoint, derivation of hypotheses, full AVD reductions and combined gate remain.

## 2026-11-21 — Horňák–Woźniak rho-one endpoint

Proved the three-arm choice and connected-partition endpoint for the exceptional-piece rho-one case from the stated residue conditions and fifth-test input. Strict compilation, a 333-theorem axiom audit and isolated kernel replay passed; rho-two, the smallest-count endpoint, full AVD reductions and the full gate remain.

## 2026-11-21 — Horňák–Woźniak wrapped endpoint

Proved the wrapped-residue exceptional-piece endpoint through an actual connected partition under the required chosen-arm bounds. Strict compilation, a 289-theorem axiom audit and isolated kernel replay passed; chosen-arm existence in the remaining cases, full AVD reductions and the full gate remain.

## 2026-11-21 — Horňák–Woźniak exceptional-piece foundations

Constructed actual connected graph partitions with one exceptional piece from reduced-arm allocations; proved the zero-carry and no-quotient-loss subcases and wrapped-residue identities. Strict compilation, a 280-theorem axiom audit and isolated kernel replay passed; remaining exceptional cases, AVD reductions and the full gate remain.

## 2026-11-21 — Horňák–Woźniak regular two-size case

Proved the regular two-consecutive-size connected-partition case for actual star graphs from the residue bounds and fifth-test witness, including extremal-count construction and transfer. Strict compilation, a 226-theorem axiom audit and isolated kernel replay passed; extra-piece cases, full reductions and the full gate remain.

## 2026-11-21 — Horňák–Woźniak connected partition realization

Proved that every feasible two-size arm allocation realizes an actual connected partition, including exact center and piece counts and arbitrary ordering. Strict compilation, a 205-theorem axiom audit and isolated kernel replay passed; extra-piece cases, endpoint hypotheses, AVD reductions and the full gate remain.

## 2026-11-21 — Horňák–Woźniak endpoint packing

Proved the complementary quotient and carry formulas, regular endpoint packing under its explicit carry witness, and transfer across arbitrarily many budget steps. Strict compilation, a 120-theorem axiom audit and isolated kernel replay passed; graph realization, remaining endpoint conditions, AVD reductions and the full gate remain.

## 2026-11-21 — Horňák–Woźniak packing criterion

Proved the exact per-arm ceiling-cost formula, the finite maximum for larger-piece allocations, the full two-size arm-packing criterion and the budget-transfer bound. Strict compilation, an 82-theorem axiom audit and isolated kernel replay passed; graph realization, endpoints, AVD reductions and the full gate remain.

## 2026-11-21 — Horňák–Woźniak Lean foundation

Formalized the actual star-like graph, connected partitions, center-free arm localization and fixed-large-pieces capacity criterion. Strict compilation, a 31-theorem axiom audit and isolated kernel replay passed; endpoint arguments, reduction theorems and the full combined gate remain.

## 2026-11-21 — Circulants with circular chromatic index in the upper half

Answered the remark in Section 8 of Mazák and Zrubák, *Circular chromatic index of small graphs* (arXiv:2603.08822), that no graph with maximum degree `Δ >= 8` and circular chromatic index in `(Δ+1/2, Δ+1)` was known. For every `g >= 2` the circulant `C_{6g+1}(1,...,2g-2, 2g+1, 3g)` is `4g`-regular and `4g`-connected with circular chromatic index `4g+2/3`, and `C_25(1,2,3,7,...,12)` is 18-regular and 18-connected with index `75/4`; this gives the non-trivial reading of their Problem 6 for `d ≡ 0 mod 4`, `d >= 8`, and for `d = 18`. The lower bound is `|E|/α'`, the upper bound an explicit colouring in which every window of consecutive classes is a near-perfect matching, and the connectivity follows from the classical atom lemmas, reproved in the note. Computer-certified further examples include `C_31(1,2,3,7,...,12)` with index `93/5` and non-regular graphs with index `Δ+2/3` for `Δ ≡ 1, 2 mod 4`, `25 <= Δ <= 54`, and `Δ = 21`. Problem 7 (denominators `q >= 6`), the reading `χ'_c = d+1/2` exactly of Problem 6, and `Δ ≡ 3 mod 4` remain open. The package contains the written proof, two standard-library verifiers, the certificates, the SAT search scripts and the referee's report and scripts; one independent model referee pass found no mathematical error. The note is otherwise unrefereed; no Lean verification was performed.

## 2026-11-21 — CKZ record conjectures formalized

Lean proves original Conjectures 1 and 3 for actual separable-permutation classes, all four record statistics, and all stated lengths, including the singleton. It uses the credited, Apache-licensed source-pinned trureturing Conjecture 2 tail and permutation decomposition and direct Pell certificates for the remaining comparisons. Strict compilation, a 1,132-theorem axiom audit and isolated kernel replay passed; the combined repository gate is pending.

## 2026-11-21 — CKZ low-record series inequalities

Proved the three low-record generating-function coefficient inequalities with direct Pell certificates, including the exceptional length-one term in the first comparison. Strict compilation, all-owned axiom audit and isolated kernel replay passed. The actual permutation-count bridge and all-index tail remain.

## 2026-11-21 — CKZ certificate soundness

Proved the finite certificates imply nonnegative infinite Pell series and, after Schröder substitution, nonnegative coefficients for twelve tail-polynomial cases and four recurrence seeds. Strict compilation, a 213-theorem axiom audit and isolated stock-kernel replay passed; arbitrary-index propagation, actual permutation-class connections and the combined repository gate remain.

## 2026-11-21 — CKZ Lean checkpoint

Checked the Schröder series and three low-record reductions, uniform numerator inequalities and all 16 finite integer-list certificates, together with the interpretation of list operations as the stated polynomials. The all-index coefficient argument and permutation-class bridge remain. Strict compilation, 123-theorem all-owned axiom audit and isolated stock-kernel replay passed; the combined repository gate is pending.

## 2026-11-21 — Fuss–Catalan simple roots in Lean

Verified the exact simple-negative-root count and proved that arbitrary ordinary-case root relations transfer to the Fuss case via equality of root multisets. The cited ordinary-case interlacing results themselves are not re-proved. Strict compilation, 448-theorem all-owned axiom audit and isolated stock-kernel replay passed; the combined repository gate is pending.

## 2026-11-21 — Fuss–Catalan conjecture in Lean

Proved the closed enumeration and real-rootedness for the literal Fuss–Dyck path sum for all stated parameters, including the slot/block bijection, cycle count, boundary and scalar reduction. The auxiliary simple-root count and cited interlacing transfers remain unformalized. Strict source compilation, 409-theorem all-owned axiom audit and isolated stock-kernel replay passed; the combined repository gate is pending.

## 2026-11-21 — Fuss–Catalan path bijection in Lean

Constructed the explicit equivalence between good block sequences and literal Fuss–Dyck words and verified both pattern counts. The slot-data-to-block bijection remains. Strict compilation, 236-theorem axiom audit and isolated stock-kernel replay passed; the combined repository gate is pending.

## 2026-11-21 — Fuss–Catalan slot count in Lean

Verified the exact binomial count for choosing occupied and excess-bearing slots and distributing positive excess by stars and bars. The bijections to block sequences and actual paths remain. Strict compilation, 151-theorem axiom audit and isolated stock-kernel replay passed; the combined repository gate is pending.

## 2026-11-21 — Fuss–Catalan rotation count in Lean

Proved that in every rotation-invariant finite collection of length-L integer sequences with sum -1, exactly one in L sequences is a good rotation. Instantiation and the path-counting bridge remain. Strict compilation, 137-theorem axiom audit and isolated stock-kernel replay passed; the combined repository gate is pending.

## 2026-11-21 — Fuss–Catalan cycle lemma in Lean

Proved unique good rotation and aperiodicity for integer sequences summing to -1 and verified real-rootedness of the complete closed-form polynomial including the constant boundary. The finite counting bridge to the actual path enumerator remains. Strict compilation, 123-theorem axiom audit and isolated stock-kernel replay passed; the combined repository gate is pending.

## 2026-11-21 — Fuss–Catalan real-rooted binomial sum in Lean

Proved the real-rootedness of the exact indexed binomial sum in the written coefficient formula for all parameters, including its derivative factorization and fractional-linear substitution. The path enumeration remains. Strict compilation, all-owned axiom audit and isolated stock-kernel replay passed; the combined repository gate is pending.

## 2026-11-21 — Fuss–Catalan Lean checkpoint

Formalized real-root preservation by differentiation and reversal/translation, together with exact coefficients, degree and nonnegative-axis positivity for the binomial factor. The polynomial identification and path enumeration remain; standalone compilation, axiom audit and isolated kernel replay passed.

## 2026-11-21 — Brown–Mol infinite counterfamily in Lean

Formalized the all-sufficiently-large diameter-four counterfamily, including the analytic root existence argument, the exact tree diameter and the literal subtree generating function. Strict source compilation, all-owned axiom audit and kernel replay passed; the combined repository gate is pending.

## 2026-11-21 — Brown–Mol finite tree counterexample in Lean

Formalized the literal branch graph as a tree, its all-parameter subtree generating function and the explicit 1001-vertex counterexample. Strict source compilation, all-owned axiom audit and kernel replay of the five-module closure passed. The stronger infinite-family result and combined repository gate remain pending.

## 2026-11-21 — Brown–Mol finite polynomial root in Lean

Checked the r=200 polynomial factor has a nonzero root inside the forbidden disk via an exact Gaussian-integer certificate and a general log-derivative bound. Strict standalone source compilation, all-owned axiom audit and stock-kernel replay passed. The tree/subtree-polynomial identification, infinite family and combined gate remain pending.

## 2026-11-21 — Johnson's conjecture

Added the [complete proposed proof](results/johnson-pfaffian/) of Conjecture 7.1 for all positive nonincreasing log-convex kernels, all finite even ordered real configurations, and all perfect matchings. The argument proves a stronger matrix theorem for products of circular interval factors. Replacing a wrapped interval by its complement changes only positive vertex factors, so Johnson's existing additive-interval endpoint inequality applies after any cyclic cut. Adjacent-pair deletion proves all noncrossing matching bounds, and the credited uncrossing reduction gives all matchings. The source's endpoint theorem, rainbow bound, and earlier nonvanishing resolution are not claimed as new.

Separate combinatorics, analysis, and root mathematical reviews passed. The supplementary exact checker passed its gauge, cyclic-sign, adjacent-pair, and logarithmic-reconstruction checks; no finite computation is a premise of the universal proof. The primary-source and seven-archive priority audit found no earlier exact resolution within its explicit limits. The additional [AIM/OpenAI audit](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/2026-11-21-aim-openai-priority/AUDIT.md), committed separately, covers 178,246 native UTF-8 bodies, 933 PDF extractions, and 2,029 embedded text records, including a complete normalized native residual pass. Binary exclusions and semantic-search limits remain explicit.

This subgroup's reviewed proposed-resolution tally is now thirteen: seven proofs and six disproofs. The earlier withdrawn families remain excluded. These are unrefereed claims with internal reviews. No Lean work was performed for this result.

## 2026-11-21 — Johnson–Kaya–Matzke path-spectrum conjecture

Proved Conjecture 2.1 of Johnson, Kaya and Matzke: for every `n >= 2` and `1 <= k <= n-1`, the Babai `k`-spectrum of the path `P_n` consists of the integers from `ceil(n/(n-k))` to `k+1`. The authors had proved one inclusion; the other follows from the bound `n-k` on independent sets of the distance graph. The package contains an elementary written proof and a standard-library brute-force check of all 16,369 distance sets with `n <= 14`. The note is unrefereed; no Lean verification was performed.

## 2026-11-21 — Complete Sonntag–Teichert realization in Lean

Formalized an explicit oriented graph realizing any two disjoint stars and proving all additional vertices are isolated in its domination hypergraph. Together with the tournament theorem and forward classification, this completes the result package in Lean. Strict source compilation, all-owned axiom audit and stock-kernel replay passed; the combined repository gate remains pending.

## 2026-11-21 — Sonntag–Teichert oriented-graph classification in Lean

Proved the forward two-star classification for separated domination hypergraphs of arbitrary finite oriented graphs. The proof checks the blocker product, both bicliques and singleton-part argument. Strict source compilation, all-owned axiom audit and stock-kernel replay passed. The converse realization and combined repository gate remain pending.

## 2026-11-21 — Brown–Mol's and Kovalev's conjectures

Added two complete proposed analytic disproofs after separate mathematical reviews, root reviews, primary-source comparisons, and retrospective full-content archive audits.

The [Brown–Mol package](results/brown-mol/) constructs an infinite diameter-four tree family whose subtree roots enter the conjectured forbidden disk. A self-contained local logarithm and Rouché argument proves the whole family; the established Beraha–Kahane–Weiss mechanism is credited. A separate exact certificate verifies a 1001-vertex example. The earlier ArtificialZeng theorem covers diameter at most three and explicitly leaves the general annulus open. The distinct origin-centered disk theorem and the conjecture's outer inequality are not claimed here.

The [Kovalev package](results/kovalev-hardy-duality/) constructs positive diagonal counterexamples to the lower Hardy-duality comparison in every matrix order at least 500001. The normalized supporting functional has dual norm exactly one over the full real matrix space. Conditional Jensen, a chi-square variance bound, classical Bessel integrals, and elementary rational estimates prove a uniform strict separation. No search over dimensions or numerical quadrature is required; the threshold is not optimized. The upper comparison remains unresolved by this argument.

All three supplementary standard-library checkers passed. The full-content Principia, Trure, mxym, AFTD, and ArtificialZeng audits found no earlier matching full resolution within their documented limits. The two earlier Principia collisions remain withdrawn. This subgroup's reviewed proposed-resolution tally rises from ten to twelve: six proofs and six disproofs. These are unrefereed claims with internal reviews, not independently accepted mathematical results. No Lean work was performed. The existing Sonntag–Teichert catalogue label was normalized to the supported partial-status spelling after the site gate rejected its previous wording; its checked tournament scope and pending oriented-graph classification are unchanged. A stale KVZ Bessel catalogue row reintroduced by the concurrent Baricz–Pogány update was removed again, preserving the prior-resolution withdrawal.

## 2026-11-21 — Prior-resolution correction for KVZ Bessel-ratio unimodality

Withdrew the older Karp–Vishnyakova–Zhang Bessel-ratio unimodality entry after reading [Trure issue 25199](https://github.com/the-omega-institute/trureturing/issues/25199), created and last updated on 1 November 2026. It supplies a complete correct analytic proof for every ordered real order pair above minus one and every ordered positive scale pair, including equal orders, equal scales, and negative orders. The remaining tasks named in that issue are formal translation and repository admission, not missing mathematics.

The result directory, duplicate research proof/checker, active catalogue and status entries, site alias, and verifier workflow references are removed. Historical reviews remain with prominent superseding corrections and immutable links to the earlier local proof. The [correction record](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/kvz-bessel-unimodality/PRIOR_RESOLUTION_CORRECTION.md) gives the exact statement comparison and verified Wronskian argument. Mathematical correctness of the independent reproof does not restore priority. This older entry was outside the current fourteen-target audit, so the current subgroup tally is unchanged. No Lean source or proof execution is part of this correction.

## 2026-11-21 — Sonntag–Teichert tournament theorem in Lean

Formalized the tournament domination-hypergraph theorem from finite arc and domination definitions. Strict standalone compilation, an all-owned axiom audit and stock-kernel replay passed. The additional classification and realization of oriented graphs with missing arcs, and the combined repository gate, remain pending.

## 2026-11-21 — Prior-resolution correction for Fang–Zhang–Zhao and Sun–Zhao

Withdrew two previously counted packages after a complete-text archive audit found earlier full disproofs. Principia's [26 October commit](https://github.com/PrincipiaMathOrg/math-solutions/blob/c18609e47b635722206b9a2e9dcd402d0edcfb0a/mathdb/368345/solution.tex) proves the same complete Fang–Zhang–Zhao Hoggatt failure family. Its [27 October commit](https://github.com/PrincipiaMathOrg/math-solutions/blob/34b8b155d7db464ad7306f70b16d3af9cee34501/site-backup/mathdb-332483/mathdb-332483-solution.tex) contains the same exact Sun–Zhao ratio counterexample. Both public dates precede this campaign; internal manuscript dates are unnecessary to establish that fact.

The earlier filename screens missed numeric archive paths. Root and separate reviewers read the actual proofs, checked the statement conventions and authenticated the public commit histories. The result directories, catalogue entries, duplicate computational checks and workflow references are removed. Existing unique formalizations by the separate team are preserved and explicitly attributed to previously resolved results. No Lean source or proof execution is part of this correction. The Han and Zhang catalogue statuses also regain canonical `Complete` labels so the existing site validator can read the already-recorded scopes; their pending combined gates are retained.

The [correction record](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/campaign-20261121/PRIOR_RESOLUTION_CORRECTION.md) gives the exact comparisons and counting changes. This subgroup's committed proposed-resolution tally falls from twelve to ten. The selected joint checkpoint falls from eleven to ten named families because Sun–Zhao was never admitted to that stricter subset. Earlier historical counts are superseded. Retrospective full-content archive audits continue before further promotions.

## 2026-11-21 — Baricz–Pogány coefficient theorem in Lean

Formalized the original factorial-product coefficients, formal quotient uniqueness, strict positivity in every degree, and the explicit lower bound. Strict compilation, isolated stock-kernel replay, and endpoint axiom checks passed; the combined repository gate remains pending.

## 2026-11-21 — Complete Han sparse-assignment infima in Lean

Formalized the lower bound and matching approaching feasible encoders for each of the four sparse assignments. Together with the earlier matrix witness and open-family gap, this completes the stated disproof package in Lean. Strict source compilation, all-owned axiom audit and stock-kernel replay passed; the combined repository gate remains pending.

## 2026-11-21 — Zhang deletion values in Lean

Formalized @aadrianvv’s strict inequality and the exact deletion values in both ranges, including a self-contained proof of the Liu upper bound. The seven-module closure passed local kernel replay and the endpoint axiom audit; the combined repository gate remains pending.

## 2026-11-21 — Exact sparse infimum in Lean

Proved the sparse infimum is exactly 481/441 by constructing feasible sparse encoders with power arbitrarily close to the lower bound. Strict source compilation, all-owned axiom audit and stock-kernel replay passed; the combined repository gate remains pending. The separate exact infima for the other assignments remain to be formalized.

## 2026-11-21 — Han–Sabag–Kostina–Hassibi Lean counterexample

Formalized the actual real-matrix witness, the universal sparse-encoder lower bound and a uniform gap across the stated open channel-gain interval. Standalone strict compilation, an all-owned axiom audit and stock-kernel replay passed. The individual exact assignment infima and combined repository gate remain pending.

## 2026-11-21 — Roos–Seiringer's conjecture

Added a complete proposed proof of the radial Dirichlet kernel nonnegativity assertion in §5 of *BCS Critical Temperature on Half-Spaces*. The proof gives strict positivity for every positive real argument and the continuous zero endpoint. The source scaling then covers every positive chemical potential. This is the whole scalar assertion identified by the authors, not a selected dimension of an arbitrary-dimensional conjecture; the unaveraged kernel is outside the claim.

The [package](results/roos-seiringer-kernel/) derives an exact entire series and proves both unbounded ends analytically. On the remaining interval, outward-rounded integer arithmetic and an analytic derivative bound certify 184 closed intervals covering every point. The computation is an essential part of the proof, with explicit truncation errors and coverage checks.

Two independent mathematical/code reviews and an independent source/priority audit passed. Full replays reproduce 367 evaluations and the recorded exact margin and leaf hash. The source paper, thesis, closest later papers, current author lists and public proof archives were checked; no earlier resolution was found within that documented coverage. The result remains unrefereed. No Lean work was performed. This subgroup's reviewed proposed-resolution tally is twelve.

## 2026-11-21 — Zhu Jacobi–Stirling Lean proof

Formalized the unweighted Jacobi–Stirling recurrence, the leading Hankel determinant and its coefficient −4, the negation of the full coefficientwise minor assertion, and the stated negative region. The standalone module passed strict source compilation, the all-owned axiom audit and stock-kernel replay. The combined repository gate is pending.

## 2026-11-21 — Mazák–Zrubák conjecture on complete graphs minus an edge

Proved Conjecture 2 of Mazák and Zrubák: for every even `d >= 6`, the circular chromatic index of `K_{d+1}` minus an edge is `d+1`. By Guichard's theorem a smaller value would give a proper `(d+1)`-edge-colouring whose digraph of consecutive colours is acyclic; the proof derives a contradiction from the longest-path levels of such a colouring. The package contains the written proof, a standard-library check of the lemmas for `d=4` and of the ordering obstruction for `d=6`, an optional SAT check from the definition, and the scripts of one independent model referee pass, which found no mathematical error. The scripts did not complete `d=8`. The note is otherwise unrefereed; no Lean verification was performed.

## 2026-11-21 — Dospolova–Germanskov–Zaporozhets's conjecture

Added a complete proposed analytic disproof of Conjecture 3.6 in *On Steiner entire function*. For every positive c, the sequence c^k/k! satisfies all the proposed ultra-log-concavity inequalities with equality. A nontrivial Gaussian-bounded compact has expected global Gaussian range strictly larger than twice its maximal deterministic local oscillation. Vitale's published normalized-ratio limit then excludes the entire factorial family.

The [package](results/dospolova-germanskov-zaporozhets/) credits the published Gaussian-process theorems and prominently explains the alternative short deduction from Long's earlier support-function results. The new contribution is the strictness deduction and its application to the later realizability conjecture. No earlier explicit resolution or equivalent strict obstruction was found in the documented searches, subject to the stated access limits.

Three independent mathematical reviews passed. Integration was held when OCR made Vitale's Theorem 1 appear strict; actual local rendering of printed pages 356–357 confirms the non-strict symbol and all normalization constants. The [source-symbol audit](results/dospolova-germanskov-zaporozhets/SOURCE_GLYPH_GATE.md) preserves the correction history. No computation or Lean verification is part of this proof. This subgroup's reviewed proposed-resolution tally is eleven.

## 2026-11-21 — Chen–Khare–Sahi's conjecture

Added a complete proposed disproof of Conjecture 5's Macdonald Muirhead-semiring implication. The exact rational functional separates the normalized difference for the partitions (4,2,0) and (4,1,1), at q=1/10 and t=9/10, from the entire degree-six semiring cone. A written homogeneity and dominance-cover argument proves that 38 products and seven ordinary monomials exhaust the required generators. This is a full universal-conjecture refutation. The proof also establishes an infinite rectangular-translate family; a separate Hall–Littlewood argument gives a continuous interior parameter family.

Two independent mathematical reviews passed. Three standard-library exact checkers verify the full cone table, both Macdonald eigenidentities, a separate Hall-inner-product construction, and the negative rational functional value. The [source audit](results/chen-khare-sahi-macdonald/SOURCE_AUDIT.md) distinguishes Sra's existing evaluation-positivity theorem for the very same pair from the stronger semiring assertion, and records current literature and archive searches with their limits. No prior settlement of this semiring claim was found. The subgroup's reviewed proposed-resolution tally is ten; all remain unrefereed and no Lean work was performed.

## 2026-11-21 — Ferreira–Simon's conjecture

Added a complete proposed analytic proof of Conjecture 1 in *Convolution of beta prime distribution*: the independent square-root beta mixture gives the self-convolution for the full original parameter range. The proof rederives the sum's Mellin transform, evaluates the mixing factor with a classical quadratic transformation, and proves equality in law by holomorphic continuation and characteristic-function uniqueness.

Two independent mathematical derivations passed, as did 18 supplementary exact symbolic identities. The [package](results/ferreira-simon-beta-prime/) records the current primary-source and archive search, including the distinction from the November 2026 restricted additive-decomposition result and the paper's separately refuted Conjectures 2 and 3. No earlier settlement of this identity was found within the stated access and indexing limits. This subgroup's reviewed tally is nine. No Lean work was performed.

## 2026-11-21 — Joint eleven-family checkpoint

Admitted Han–Sabag–Kostina–Hassibi's exact matrix disproof to the [joint ledger](https://github.com/1337isnot1337/solved-conjectures/tree/research/research/2026-11-21-joint-results/) after additional independent mathematical, source, priority and provenance reviews. The selected reviewed set now contains thirteen packages: seven from the current four-worker group and six from the parallel campaign. Removing corrected-source Novelli–Thibon from the strict count and merging the two López Pouso–Segura packages gives eleven named families. Other newer parallel packages remain outside this selected review until separately admitted.

The [mathematical audit](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/2026-11-21-han-sabag-independent-review/AUDIT.md) reconstructs the exact feasible point, all sparse assignments and the open family, using a separate rational Gaussian-elimination checker. The [priority audit](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/2026-11-21-han-sabag-independent-review/PRIORITY.md) compares both source versions and records bounded search coverage and access gaps. The strict gap between infima avoids relying on optimizer nonattainment. The result remains confined to the displayed matrix conjecture, with no new general communication-code claim. Sun–Zhao's additional exact ratio counterexample passed independent mathematical review but remains outside this strict tally pending the full 2020 journal version and the author's Maple archive. No Lean work was performed.

## 2026-11-21 — Lyon's conjecture

Added a complete proposed computer-assisted proof of the strict decrease of the transformed gamma median for every positive real shape. Analytic arguments prove the ranges at most one tenth and at least seven. On the intervening compact interval, exact outward-rounded integer arithmetic certifies 4258 median brackets and 4256 covering cells. A written convexity argument extends each strict bound to every real point in its cell; this is not a sample-based monotonicity inference.

Two independent mathematical/code reviews and complete exact replays passed. The [package](results/lyon-gamma-median/) includes all enclosure formulas, untrusted bracket proposals, the verifier and a current source audit. The target remains explicitly open in the original author's 10 November 2026 manuscript; the search found no prior settlement within its recorded limits. This subgroup's reviewed tally is eight. The verification legend now describes the unformalized marker as no Lean verification, while essential computer-assisted proofs are stated explicitly in the catalogue and packages. No Lean work or partial Lean credit was added.

## 2026-11-21 — Strict joint ten-family checkpoint

Updated the [joint ledger](https://github.com/1337isnot1337/solved-conjectures/tree/research/research/2026-11-21-joint-results/) after the complete Gröchenig mathematical and priority cross-review. This selected review contains twelve proposed result packages: seven developed by the current four-worker group and five by the parallel issue-156 group. Excluding the corrected-source Novelli–Thibon package leaves eleven direct-source packages; grouping the two López Pouso–Segura packages leaves ten named conjecture/problem families. Novelli–Thibon remains an additional documented result. Later packages in the parallel group's live checkpoint, including Han–Sabag–Kostina–Hassibi, remain outside this selected review.

The ledger now states McCrea's exact density interval, the positive-degree range of Vishnyakova's theorem, and the unresolved lower-density clause of Gröchenig's problem. It distinguishes the completed all-profile Coulter–Do–Moskovsky asymptotic theorem from the initial reversal already implicit in the authors' 2022 data; that qualified research remains uncounted. Rivero, Cavey–Lee and Simon subroof work also remain uncounted. Prior-resolution withdrawals and access limits are retained. All packages remain unrefereed; no Lean work was performed.

The full research-site build and content, link, mathematics and metadata checks passed at commit 444696374a21085f0c8193db5facab49ede6e616, run 44879720088. Earlier checkpoint entries below preserve the historical counts and are superseded by this stricter accounting.

## 2026-11-21 — Sun–Zhao's conjecture

Added a complete proposed disproof of Conjecture 5.2 in arXiv:1602.04359v4. The twelfth iterated ratio sequence fails its required log-convexity at center thirteen, using only entries retained after the specified truncation. An exact binomial-product comparison and a rational logarithm certificate give the same strict sign. The root reviewer independently regenerated the recurrence, used a different logarithm truncation and remainder, and directly iterated the ratios.

The [historical package](https://github.com/1337isnot1337/solved-conjectures/tree/fa34b035f4853c8e790bd520171739ee17923a56/results/sun-zhao-iterated-ratios/) includes both reviews and a multi-source prior-resolution audit. The full journal version and author's Maple archive were inaccessible; the resolved statement is the fully inspected latest arXiv conjecture. Neither the first-ratio theorem nor the different quadratic log-convexity transform is misidentified as the target. This subgroup's reviewed tally is seven; no Lean work was performed.

## 2026-11-21 — Han–Sabag–Kostina–Hassibi's conjecture

Added a complete proposed disproof of the explicit Lyapunov positivity conjecture in arXiv:2406.17196v2. A rational two-channel encoder has power 23825/22491, while the infimum over all encoders with one nonzero per column is 481/441. The strict gap is 706/22491. The proof classifies every sparse assignment with arbitrary nonzero coefficients and extends the example to an open interval of channel gains. It does not rely on optimizer nonattainment or claim a separate general communication-code result.

Two independent source and mathematical reviews passed, together with 16 exact rational and symbolic checks. The [package](results/han-sabag-kostina-hassibi/) records the original source, related primary papers, public issue/archive searches and access limits. This subgroup's independently reviewed campaign tally is six; the earlier joint checkpoint retains its separate attribution. No Lean work was performed.

## 2026-11-21 — Currie's conjecture on complexity 2n+1 and critical exponent

Proved Conjecture 19 of Currie's *Words with factor complexity 2n+1 and minimal critical exponent* (Electron. J. Combin. 33(3), #P3.31), which is Conjecture 1 of arXiv:2507.09387v3: each of the ten listed morphic images of the fixed point of `[01,2,02]` or of its reversal has factor complexity `2n+1` and critical exponent exactly `2+1/(λ²-1)`, where `λ` is the real root of `x³-2x²+x-1`, and the same holds for the ten arXiv morphisms. The words reduce to three languages; insertion lemmas describe all their bispecial factors, which are ordinary, and the critical-exponent inequality is proved for 72 families by exact arithmetic in `Q(λ)`. The package contains the written proof, a standard-library verifier for the computer-assisted steps with brute-force cross-checks, and the scripts of one independent model referee pass, which found no error. The note is otherwise unrefereed; no Lean verification was performed.

## 2026-11-21 — Joint ten-family research checkpoint

Recorded an [attributed joint ledger](https://github.com/1337isnot1337/solved-conjectures/tree/research/research/2026-11-21-joint-results/) covering eleven complete proposed result packages, conservatively grouped into ten named conjecture families. Seven packages were developed by the current four-worker group and four by the parallel issue-156 group, with separate cross-reviews before inclusion. The two López Pouso–Segura packages count as one family. Full assertions, source scope, proof mechanisms, review records and priority limits are linked individually.

The [final global issue-history audit](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/2026-11-21-joint-results/PRIORITY_REFRESH.md) records the earlier Sturm proof that required withdrawal, the confirmed CKZ preregistration without a proof, and the retained targets' bounded search results. Previously resolved KVZ targets, the Boudabsa–Simon and Heim–Neuhauser reproofs, and partial or interpretation-dependent work contribute zero. All retained notes remain unrefereed. The later Gröchenig package is outside this checkpoint pending an additional cross-review. No Lean work was performed.

## 2026-11-21 — Gröchenig's problem

Added a complete proposed counterexample to the upper Beurling-density comparison in Problem 4.12. Finite Gaussian blocks with alternating coefficient signs place zeros twice as densely as their coefficient support; recursive separation and a summable tail budget combine them into one nonzero entire function with absolutely summable coefficients. The coefficient sign-change upper density is exactly one half, while the real-zero upper density is at least one. The separate lower-density assertion remains undecided here.

Two independent internal mathematical reviews and 784 exact algebra and error-budget checks passed. The prior-art audit includes the original problem, related sampling and sign-retrieval papers, recent November 2026 literature, public solution archives, and repository issues 80 and 121. No earlier resolution of the exact upper comparison was located within that documented audit. The issue-156 campaign tally is five proposed resolutions; all remain unrefereed. No Lean work was performed.



## 2026-11-21 — López Pouso–Segura's node conjecture

Added a complete proposed disproof of the published strict node and partial-moment upper inequalities, Conjectures 3 and 7. The exact two-point Gauss–Legendre rule supplies one common counterexample. A controlled expansion from the Legendre equation proves a positive fourth-order correction at the smallest positive node for every sufficiently large even degree, so an eventual interpretation of the exact node bound also fails.

The two linked assertions count together. Existing general node/weight expansions are credited; the leading asymptotic constant and the separate Bessel-limit package are not contradicted. Independent internal mathematical review and exact symbolic consistency checks passed. The source audit records both search engines, public proof archives, global issue histories and a related inaccessible full text. The work remains unrefereed, and no Lean work was performed.

## 2026-11-21 — Corrected Fang–Zhang–Zhao Sturm priority

Removed the Sturm package from the result catalogue and active status/verifier registrations after locating the full earlier proof in [TT issue 18758](https://github.com/the-omega-institute/trureturing/issues/18758), posted on 18 October 2026. Its all-real-base, all-Hoggatt-parameter theorem and six-step Jackson/Hadamard proof already settle the exact conjecture. The later incomplete Lean formalization does not affect this ordinary mathematical priority determination.

The independent reproof is retained as [credited research](https://github.com/1337isnot1337/solved-conjectures/tree/research/research/fang-zhang-zhao-sturm/), with the [detailed prior comparison](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/2026-11-21-special-functions-fzz-priority/AUDIT.md). It counts as zero new resolutions. The separate issue-156 subgroup checkpoint is corrected from five to four; the universal infinite-log-convexity disproof is a different assertion and is audited separately. Earlier addition entries below are historical and superseded by this correction.

## 2026-11-21 — Vishnyakova's conjecture

Added a complete proposed proof of the outer-root-radius conjecture for every polynomial degree and every positive real weight. The proof gives the stronger disk centered at minus half the weight, and the all-one parameter vector attains the claimed outer radius. A complex-parameter tridiagonal argument and reciprocal-segment lemma establish half-plane zero exclusion; Grace–Walsh–Szegő and Hurwitz extend it to arbitrary independent real parameters. The equal-parameter recurrence and disk theorem from the earlier October report are credited explicitly. The original and weighted conjectures count as one family.

Two independent internal mathematical reviews and 73 exact algebraic checks passed. The source audit distinguishes prior low-degree and equal-parameter results, the neighboring already-disproved root-gap question, and later multiplication-closure theorems. No earlier full root-radius resolution was found within that documented audit; access limits and lack of external review remain explicit. The issue-156 campaign tally is five after its two priority corrections. No Lean work was performed. The Alexandersson–Leite peak-nesting conjecture was separately excluded after an earlier full informal disproof was located; its independently checked reproof is retained only as credited research.

## 2026-11-21 — Novelli–Thibon's conjecture

Added a complete proposed proof of the intended monomial-product Conjecture 5.7 for all partitions and independent parameters. A universal word-comparison identity determines every first derivative at the unit parameter point, and the Pieri rule extracts the tableau exponent. The source's printed exponent index is corrected using its own example. A separate product evaluation, derived from the credited Carlsson–Mellit theorem, also proves the adjacent hook-coefficient formula; it is part of the same named package.

Two internal mathematical reviews passed. The result includes an exact standard-library checker and a bounded source and priority audit covering both arXiv versions, published metadata, related primary literature, web searches, global GitHub proof searches and repository history. No earlier full monomial-product resolution was found in the inspected material; the access limits are recorded. The notes remain unrefereed. The separate Schur-positivity and general trace conjectures remain outside the claim, and no Lean work was performed.

## 2026-11-21 — Restored prior-resolution exclusions for two KVZ targets

Removed the reintroduced reciprocal q-gamma and Hankel-product packages and their result, status and verifier registrations. Both targets had already been excluded on November 20; today's reintroduction mistakenly reversed that established priority decision. Neither counts as a new resolution. The other Karp–Vishnyakova–Zhang targets are separate and are retained.

The reciprocal assertion was proved in [Knowledge Sense's October 13 manuscript](https://github.com/KnowledgeSense/math/blob/b95a52a54597e8b01c1a28486f2a9b29a3a54c58/preprints/Strict-Sign-Regularity-of-the-Reciprocal-Jackson-q-Gamma-Kernel-October-13-2026/build/source/strict-sign-regularity-of-the-reciprocal-jackson-q-gamma-kernel.tex), preserved at revision `b95a52a54597e8b01c1a28486f2a9b29a3a54c58`. Its full proof covers every base between zero and one, every determinant order and all increasing positive real grids. The Hankel-product negation already follows from Simon's 2012 beta–gamma kernel theorem, [arXiv:1207.6464](https://arxiv.org/pdf/1207.6464), through the logarithmic coordinate change and common translation recorded in the [November 20 correction](https://github.com/1337isnot1337/solved-conjectures/blob/a354c349b80c70bb575ffc0230d17c3ced5ec7f7/research/kvz-hankel-product/PRIOR-SIMON-CORRECTION.md). Both prior implications were reread and checked.

The campaign checkpoint was reduced by two and now links to a [priority correction](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/campaign-20261121/kvz-prior-resolution.md). The withdrawn independent proofs remain available in commit history, including the [pre-cleanup snapshot](https://github.com/1337isnot1337/solved-conjectures/tree/0e4d396261505b89eb5dddbd264be7a212d3e78c/results). Their mathematical validity does not make the targets previously open. The older November 21 addition entries below are historical records superseded by this correction.

## 2026-11-21 — Corrected Hankel-product prior-art error

Removed the reintroduced Karp–Vishnyakova–Zhang Hankel-product result directory, catalogue entries, site registration, and verifier references. Simon's *Produit Beta-Gamma et régularité du signe*, arXiv:1207.6464 (2012), printed page 4 theorem and page 16 Remark (b), already refutes the full assertion after the logarithmic change of variables. Issue 94 had documented this exclusion on 20 November; the current campaign failed to check that issue before reintroducing the claim. The new elementary examples remain mathematically valid but cannot count as a new resolution. Their previous versions remain in Git history, not in the result catalogue.

The issue-156 campaign tally is corrected from six to five. The original-source theorem and its coordinate change were reread independently. The separate reciprocal q-gamma, Hoggatt, McCrea, and Bessel-weight results are unaffected. Zhao's Motzkin-root conjecture was also excluded after a prior Chinese-language complete proof was located in xzwwwwww/math. Future candidate screening must search the repository's issue history as well as current files and external literature.

## 2026-11-21 — Simon's stable-infimum conjecture

Added a complete proposed proof of the convex-order conjecture in Remark 6 of Simon's 2014 EJP article, throughout the full parameter interval and including its Brownian endpoint. The established stable-infimum Mellin transform gives two logarithmic Lévy densities that increase with the parameter. Their difference supplies an independent mean-one multiplier, and conditional Jensen gives the claimed order. The factorization and Mellin transform are credited to prior work.

An independent internal mathematical review passed. The package records direct checks of the original and final source statements, earlier Mellin formulas, later related papers, a 2026 survey, more than forty focused searches and five public solution archives. No earlier full resolution was found within that documented search; the priority limits are explicit. The proof uses no numerical or finite-case inference, and no Lean work was performed. The notes remain unrefereed.

## 2026-11-21 — López Pouso–Segura's conjectures

Added complete proposed proofs of the three Bessel-weight sequence conjectures in the 2025 published article. A positive-measure representation proves strict convexity of the inverse squared-phase derivative; trapezoidal errors give the C and E monotonicity. A Fourier–Bessel resolvent identity fixes both limiting constants, and a weighted-average identity gives the K statement. The three linked assertions count as one named result. The finite-degree Gauss–Legendre conjectures are outside the result.

Two independent internal mathematical reviews passed. The package includes a source and prior-resolution audit with access limits, and a standard-library exact checker for the algebraic identities. It remains unrefereed; no Lean work was performed. The same checkpoint preserves unresolved symbolic parking-polytope research through dimension six and records prior resolutions that were excluded from the campaign tally.

## 2026-11-21 — Ferreira–Simon stochastic and diagonal conjectures

Added complete proposed proofs of the two distinct full-parameter conjectures in Remarks 7(b) and 5(b) of Ferreira and Simon's *Mittag-Leffler functions and convex ordering*. The first uses a common Poisson arrival series and strict sequence-norm monotonicity to establish stochastic order. The second uses the classical Lamperti sine quantile, logarithmic contraction and reciprocal pairing to establish diagonal Mittag–Leffler monotonicity.

Both arguments passed separate internal mathematical reviews. The packages contain source and prior-resolution audits covering the original statements, earlier formulations, neighboring theorems, current follow-ups and public solution archives, with access limits stated explicitly. Classical representations are credited. The stochastic assertion's 2014 and 2025 formulations count as one target; endpoint bounds and crossing-point corollaries are not additional conjectures. These are written analytic proofs and require no numerical verifier. The notes remain unrefereed. No Lean work was performed.

## 2026-11-21 — Hankel products and McCrea's conjecture

The Hankel-product novelty claim in this entry was withdrawn later on 21 November; see the correction above. McCrea's result is unchanged.

Added a complete proposed disproof of Karp–Vishnyakova–Zhang's general sign-regular Hankel-product conjecture. An elementary family has exact rational order-two minors of opposite signs; a second family has strictly sign-regular factors of every order and the same failure. Both families resolve one conjecture, with the original unrestricted-signature hypothesis checked directly. Root and combinatorics reviews passed. The published final-page access limit is recorded alongside the verified arXiv versions.

Added a complete proposed proof of McCrea's unique linear-density crossover conjecture for every modulus at least three. Positive large-power generating functions yield local coefficient asymptotics through a self-contained Fourier argument that handles the floor. Between the two means, the exponent difference is strictly decreasing with opposite endpoint signs. Independent analysis review and exact profile-word diagnostics passed. This is distinct from the previously resolved fixed-number Franklin inequality. Both packages include current priority audits, remain unrefereed, and add no Lean work.

## 2026-11-21 — Chen–Kitaev–Zhang and Zhu conjectures

Added complete proposed proofs of Chen–Kitaev–Zhang's original record Conjectures 1 and 3, and a complete disproof of Zhu's unweighted generalized Jacobi–Stirling conjecture. The record proof supplies three all-length coefficient comparisons and credits the previously public Conjecture 2 tail argument. Zhu's disproof is an exact polynomial determinant identity with a negative coefficient and an open real counterexample region.

Both packages include separate internal mathematical audits, source and priority searches with stated limits, and standard-library exact replay scripts. They remain unrefereed. The two record assertions form one named package and are not split by statistic or length. Burcroff's conjecture was excluded after a September manuscript proving the stronger unbalanced-product theorem was found and checked; the independent reproof remains in research notes. No Lean work was performed. The site's non-formalized status registrations also cover the three Hoggatt and reciprocal-q-gamma packages added earlier today.

## 2026-11-21 — Hoggatt and reciprocal q-gamma conjectures

Added three complete proposed resolutions from the named-conjecture research in [issue 156](https://github.com/1337isnot1337/solved-conjectures/issues/156). Fang–Zhang–Zhao's Sturm conjecture follows from geometric root separation, a Jackson derivative interlacing lemma, and an all-row Hadamard induction; the proof covers every real base greater than one and every integer Hoggatt parameter at least two. Their distinct universal infinite-log-convexity conjecture is false for every parameter at least four, by an exact parameter-polynomial factorization and two explicit integer calculations. Karp–Vishnyakova–Zhang's reciprocal q-gamma kernel is strictly sign regular at every order throughout the source's full base interval, by a q-binomial double series and two finite Cauchy–Binet expansions.

Each argument has a separate internal mathematical review and a documented current prior-resolution search. The Hoggatt disproof also has independent direct plane-partition enumeration. The two Hoggatt packages and reciprocal-kernel package include reproducible exact diagnostics. The proofs remain unrefereed, and inaccessible later full texts are recorded as priority limitations. Parameter subcases and the discrete reciprocal-kernel corollary are not counted separately. No Lean work was performed. Segura's modified-Bessel-product conjecture was excluded after a 2026 prior resolution was located.

## 2026-11-20 — Malek's conjecture

Added a complete proposed proof of Malek's all-degree negative-transform subpermanent inequality, including equality. The reciprocal-mean capacity cost improves the optimized-slice estimate enough to separate the lower and upper constants in every proper degree. The permanent endpoint is credited to prior work. Two independent internal reviews and a standard-library rational checker found no gap; the proof is unrefereed. A bounded audit of primary literature, recent transform followups, and public repositories found no earlier complete endpoint theorem. The original 1989 full text remained inaccessible, while Cheon–Wanless's 2005 survey states the exact conjecture. This is a named subsidiary in the Minc site's linked literature, not an additional numbered entry. No Lean work was performed.

## 2026-11-20 — Independent outside confirmation of Németh–Seberry–Shu

[Yair Lavi's Minc Conjecture 27 record](https://yair-lavi.com/mincs-list/conjecture-27/index.html) now identifies the conjecture as disproved by Cinna Davis and GPT-6.2 Astra, including the quadratic lower bound, and reports an independent audit that found no gap. The main index marks this outside confirmation with ★, separate from Lean status. This is not journal peer review.

## 2026-11-20 — Sagan–Swanson formula rendering

Replaced an unsupported fixed-width TeX spacing command by standard spacing in the two Sagan–Swanson proof copies. The displayed formula is unchanged. The unsupported command blocked the native MathML site build after catalogue registration was repaired.

## 2026-11-20 — Oravcová–Soták distance-graph conjecture

Added the classification of primitive distance sets of size five through eight with maximum chromatic number, relative to the repository's five-, six-, seven- and eight-speed spectrum classifications. The package contains a written proof, 62 periodic colourings, loop certificates for four one-parameter families, base loops for the two-parameter six-distance family, an independent standard-library verifier, and a separate SAT scan. The note is unrefereed and conditional on the spectrum classifications; no Lean verification was performed. Contributed by [@aadrianvv](https://github.com/aadrianvv) in [PR #144](https://github.com/1337isnot1337/solved-conjectures/pull/144).

## 2026-11-20 — Repaired an omitted result registration

Registered the existing `baricz-pogany-coefficients` package in the shared catalogue, root index and status map after its orphan landing page blocked the site build. The mathematical files and their stated scope were preserved. This is integration of previously published work from issue #112, not a new result of the Minc campaign.

## 2026-11-20 — Pula–Song–Wanless conjecture

Added a complete proposed proof of the named threshold conjecture for all positive block sizes with `n>1`. At `n>=m+sqrt(m)` the stated boundary matrix uniquely minimizes the permanent. The equality threshold is included. A real-rooted-minor argument replaces a gap in the available 2011 equalization proof; a separate van der Waerden completion proves uniqueness. The known cohesive and non-barycentric directions are credited and independently checked. The result includes two written independent reviews, exact identity audits and a source audit through November 2026. The notes are unrefereed and priority remains provisional. This does not resolve the unrestricted Minc Problems 14 or 15, and no Lean verification was performed.

## 2026-11-20 — Perron root of permanental compounds

Added a general FPRAS theorem for Minc Problem 18's approximation formulation. The result covers every nonnegative rational input and every compound degree, with deterministic zero detection. A stable-symbol trace bound, cyclic permanent reduction and rational grid give the algorithm without constructing the compound. The directory includes the full proof, exact finite checks, two independent reviews and a source audit. This is not an exact polynomial-time eigenvalue-computation claim, and it does not solve the characteristic-polynomial problem. No Lean verification was performed.

The Minc research record also documents partial Gyires and integrality results without counting them as full resolutions.

## 2026-11-20 — Zhang's Question 8.4

Answered Zhang's Question 8.4: the deletion values `LR([n-1] \ {r})` are `1/r` when `2r > n-1` and `2/D_r` when `2r <= n-1`, so the strict inequality holds for all `n >= 4` and `1 <= r <= n-2`. The package contains an elementary proof and an exact standard-library verifier for `n <= 40`. The note is unrefereed; no Lean verification was performed. Contributed by [@aadrianvv](https://github.com/aadrianvv) in [PR #143](https://github.com/1337isnot1337/solved-conjectures/pull/143).

## 2026-11-20 — Removed previously resolved conjectures

Removed the result entries and duplicate research writeups for Karp's
coefficient-positivity conjecture, Karp–Vishnyakova–Zhang's reciprocal
q-gamma and Hankel-product conjectures, Simon's Le Roy conjecture, and
Gatzweiler–Krattenthaler's unrestricted shifted-product Conjecture 4.
Earlier exact resolutions were established by Principia Math In Progress
(MathDB 323156 and 349140), Knowledge Sense's October 2026 preprint,
Simon's Beta–Gamma theorem, and the CoPEER archive. The
[prior audits at the pre-removal revision](https://github.com/1337isnot1337/solved-conjectures/tree/a354c349b80c70bb575ffc0230d17c3ced5ec7f7/results)
record the source and scope for each correction.

Removed standalone research writeups for the previously resolved binomial
Eulerian, intrinsic-volume sequence, and inverse-gamma Newton-series
targets. The catalogue and verification instructions now describe the
remaining collection.

## 2026-11-20 — Chow proof rendering

Replaced an obsolete bold-math command in the two Chow proof copies
with standard mathematical markup after it blocked the research-site build.
The mathematical statement is unchanged.


## 2026-11-20 — Karp–Vishnyakova–Zhang's Bessel-ratio unimodality conjecture

**Superseded on 21 November 2026:** the exact conjecture was already proved in [Trure issue 25199](https://github.com/the-omega-institute/trureturing/issues/25199) on 1 November. The following entry records the historical independent reproof, which is excluded from the original-result collection.

Added a complete proof of the full surviving unimodality assertion for all
ordered real orders greater than minus one and all ordered positive scales.
The Bessel differential equation gives a Wronskian derivative with at most
one positive-to-negative sign change. Positive series terms determine the
endpoint signs and give the complete monotonicity/unique-maximum
classification, including negative orders and every equality case.

The separate stronger log-concavity clause was already refuted and is not
claimed here. Root and analysis completed independent written audits.
Exact rational series checks passed 130 coefficient identities and ten
endpoint/positivity checks. The prior-work audit distinguishes adjacent-order,
same-argument, and Kaiser–Bessel results from this full assertion. No outside
peer review or exclusive priority is claimed.

[Historical proof, classification, exact checks, and source audit](https://github.com/1337isnot1337/solved-conjectures/tree/260d8cd070fc6642edd722b16e52370a91ab73f7/results/kvz-bessel-unimodality/).

## 2026-11-20 — Ferreira–Simon's Wright log-concavity conjecture

Added a complete disproof of the conjectured equivalence between the
gamma-defined parameter threshold and log concavity of the Wright density.
Gamma reflection and log convexity give a uniform summable coefficient
bound. The resulting differentiated-series limit has explicit curvature
of the wrong sign on entire intervals of admissible parameters, including
strictly interior positive beta.

The full written proof passed separate root and algebra reviews. Exact
rational-polynomial checks passed for the general curvature identity and
the displayed derivative values. The analytic convergence argument supplies
the counterexample intervals. The source audit records both search engines,
current author records, later primary-paper comparisons, and full-text
access limits. No outside peer review or exclusive priority is claimed.

[Proof, source audit, and exact algebra](results/ferreira-simon-wright/).

## 2026-11-20 — Karp–Vishnyakova–Zhang's gamma-quotient conjecture

Added a complete proof of all-order sign regularity for the additive gamma
quotient with every positive parameter difference. An explicit Wronskian gives
the signs for the power kernel; two gamma-density integral transforms transfer
those signs to the quotient through continuous Cauchy–Binet. The proof includes
absolute integrability, strictness, all integer rank cutoffs, and translated
domains with positive gamma arguments.

The source's proposed fixed third-order signature is corrected within the same
result. Two independent reviews of the full proof passed. A standard-library
verifier passed 115 exact rational checks of half-integer signs, integer rank,
and gamma-moment normalization. These finite diagnostics are supplementary to
the all-parameter proof. The source audit records both search engines, primary
theorem comparisons, public solution checks, and inaccessible-source limits.
No external peer review or absolute priority guarantee is claimed.

[Proof, source audit, and exact checks](results/kvz-gamma-quotient/).

## 2026-11-20 — Alexandersson's Fuss–Catalan conjecture

Recorded a short uniform deduction of the named real-rootedness conjecture.
Classical Kreweras/cycle-lemma enumeration shows that, after fixing the
number of north steps and north runs, the Fuss parameter changes only a
positive scalar. The real-zero polynomial is already known from the
ordinary-Dyck work of Bóna and coauthors and Wang–Zhang. A self-contained
Rolle argument is included for independent checking.

The complete argument passed independent review. Direct enumeration of
10,188 paths across 18 parameter pairs checked the exact source convention.
These finite comparisons are diagnostic. The attribution record expressly
credits both classical ingredients and records an inaccessible recent
paper; no unconditional novelty claim is made. This entry is distinguished
from a new enumeration or a new root-preserving theorem.
[Proof, classical attribution, and checks](results/alexandersson-fuss-catalan/).

## 2026-11-20 — Sagan–Swanson conjecture

Added a complete proof of asymptotic normality for all four q-Stirling
coefficient distributions in the proportional regime of Conjecture 7.8.
An exact conditioned probability model reduces the elementary and complete
homogeneous symmetric-function families to one theorem. A direct Fourier
bound controls the conditioning, and exponential tilting proves convergence
of the actual means and variances. The limiting variance is positive and
has order $n^3$.

Independent source/model and analytic audits passed, followed by a separate
review of the full written proof. The standard-library verifier passed 168
exact identities against the four original recurrences. These finite checks
do not replace the asymptotic proof. The literature record distinguishes
older row-distribution and fixed-parameter theorems, as well as the already
resolved bottom-heaviness conjecture, and states the access limits.
[Proof, source audit, and model checks](results/sagan-swanson-normality/).

## 2026-11-20 — Bernardi–Morales's delta-process conjecture

Added complete written proofs of the delta-process tree-probability identity
and the stronger event-determinant identity, published as Conjectures 27–28
and numbered 21–22 in the preprint. The tree count holds for each fixed
color map, and the event identity holds for each fixed surjection.

The two arguments use cycle Laplacians and cyclic adjugates, respectively.
The event proof explicitly handles full subsets, where the cycle matrix is
singular. Separate internal reviews checked the original event definitions,
the determinant identities, and membership-coefficient extraction.
The standard-library verifiers passed locally on Python 3.12.14: 71 fixed
maps and 111,721 tree-process pairs; 25 arbitrary-matrix determinant checks;
and 342 marked-surjection profiles with 438,952 literal event determinants.
The literature audit records checked sources and access limits. External
peer review and author confirmation have not been obtained.
[Result, both proofs, and checks](results/bernardi-morales-delta/).

## 2026-11-20 — Gilmore and Chow conjectures

Added an all-row proof of
Gilmore's crossing–nesting matrix identity with an alignment refinement,
and a proof of consecutive type-D Eulerian interlacing.

The weak Chow assertion is a direct consequence of Savage–Visontai's
published refinement theorem; that dependency and the separate strictness
argument are explicit. Each result includes its primary conjecture source,
a bounded literature audit, precise scope, and reproducible exact checks.
A second agent independently checked each mathematical argument. The
published verifiers passed locally on Python 3.12.14, with SymPy 1.14.0 for
Chow's checks. No Lean work was performed.
[Result entries and scope](CONTENTS.md#polynomial-identities-and-positivity).

## 2026-11-20 — Németh–Seberry–Shu conjecture

Added a written disproof of the all-row-sums conjecture for prime-order
binary circulant permanents and linked the quadratic strengthening.
[Result and scope](results/nemeth-seberry-shu/).

## 2026-11-20 — Horňák–Woźniak and Sonntag–Teichert conjectures

Added written proofs and literature checks for both connected-partition
conjectures of Horňák and Woźniak and for Sonntag and Teichert's
tournament domination hypergraph conjecture. The respective exact
cross-checks pass. The same campaign added partial results for the Erdős
essential-component, Erdős–Sauer, Bollobás–Erdős–Tuza and Erdős–Oler
conjectures. [Proofs and research notes](CONTENTS.md).

## 2026-11-19 — Four-input prime filtering

Registered 20 modules after the complete hosted source, literal-statement,
owned/raw-occurrence audit and stock-kernel gate passed. Ten canonical
finite checks now give an unconditional arithmetic filter for four inputs
nonzero modulo seven, with actual folded bounds and higher-residue
preservation relative to one of the multipliers 1 through 5.
The unrestricted six-speed runner theorem remains pending.
[Scope and original evidence](docs/verification/prime-filtering-four-exact-44601096014/README.md).

## 2026-11-19 — Prime filtering and proved runner classes

Registered twelve modules after the complete 18-module hosted gate passed
strict sources, 33 literal contracts, all 299 owned declarations, and exact
stock-kernel replay. The proofs formalize the published prime-filtering
lemma and seeded distance corollary. The `1/7` runner consequence retains
the three-distinct-speeds budget at each valuation level below the maximum.
The unrestricted six-speed bound remains pending.
[Scope and original evidence](docs/verification/prime-filtering-exact-44591941338/README.md).

## 2026-11-19 — Registered order-nine automorphism subgroup and orbit proofs

Registered the two existing modules for odd automorphism subgroups of abelian
groups of order nine. They prove subgroup order three, three fixed points,
and five orbits in the nontrivial case. The four unchanged source modules
retain their original hosted strict-source, axiom, and stock-kernel pass.
A fresh local strict-source check and complete 68-declaration audit also
passed; the separate local repeat stock replay timed out and is preserved
with its actual outcome. The length-1197 order-27 exclusion remains pending.
[Exact scope and evidence](docs/verification/hadamard-order-nine-orbits-44523474204/README.md).

## 2026-11-19 — Complete tight-five classification and independent finite lower bound

Registered the complete primitive and gcd-normalized five-speed equality
classification at `1/6`, with exactly `[1,2,3,4,5]` and `[1,3,4,5,9]` as primitive
directions. The proof also gives an independent finite derivation of the
five-speed lower bound; the earlier Renault proof remains registered.

The original run 44549751944 passed all 250 fresh strict source modules,
7,586 required theorem endpoints, 7,070 finite frames, the complete raw/private
axiom audit, and exact stock kernel replay. Every finite source was reproduced
and the original artifact authenticated. The full five-speed spectrum below
`1/5` remains incomplete.
[Exact statements and preserved evidence](docs/verification/loneliness-five-runner-exact-44549751944/README.md).

## 2026-11-19 — GitHub proof rendering and results index

- Simplified the README results table to directory links and Lean status emoji.
- Standardized Markdown math for GitHub and kept native MathML on the reading site.

## 2026-11-19 — Conditional norm reductions for nine through thirteen speeds

- Registered the actual primitive-speed norm cutoffs and prime-selection
  theorems, retaining every smaller-dimensional runner bound as an explicit
  hypothesis. The basis geometry and all 7,936 KZ subset rows are proved internally.
- Exact run 44530735399 checked 81 strict sources, 1,696 owned/raw declarations
  (1,445 theorems and 538 private declarations), 25 required theorem endpoints
  and 81 exact stock-kernel targets. Original evidence is authenticated under
  `docs/verification/loneliness-large-norm-exact-44530735399/`.
- Added 64 proof modules and 25 required endpoints. The equality classifications
  remain partial; lower-runner bounds, modular exhaustiveness and uniqueness
  are still required. The merged accepted-package gate remains separate.

## 2026-11-19 — Complete fixed-hyperplane formalization

- Registered the original fixed-hyperplane probability, counting, Haar-shift,
  endpoint and sharpness statements, preserving the ordered positive distinct
  sampling model and all original hypotheses.
- Exact run 44531509741 at `ee1f018fef258cdd54f73af31cdaf6485fd151cb` checked all 72 sources with warnings as
  errors, all 1,403 owned declarations (1,149 theorems and 44 private declarations),
  all 106 required theorem endpoints and all 72 exact stock-kernel targets.
- Preserved the unchanged raw receipt and authenticated original evidence under
  `docs/verification/hyperplane-main-exact-44531509741/`.
  Registration adds 63 proof modules and 102 previously unregistered endpoints.
  The merged accepted-package gate remains separate.


## 2026-11-19 — Both six-speed spectrum realization branches

Registered the unconditional existence theorem for every proposed six-speed
value `(P−1)/(6P)`, for `P ≥ 7` congruent to one or five modulo six.
The witnesses are positive, distinct and primitive; their exact global
values include actual attaining times. The 11-module closure passed fresh
strict sources, the audit of all 392 owned declarations including 30 private
declarations, and every exact stock-kernel target. All 15 required endpoints
are theorems. Universal classification remains incomplete.
[Scope](docs/lean-status.md#six-speed-spectrum-complete-realization) ·
[Receipt](docs/verification/six-spectrum-realization-44527134869/receipt.json).


## 2026-11-19 — Complete unrestricted two-speed insertion theorem

Registered the full two-speed insertion result, including the arbitrary
positive speeds, prescribed interval, Goddyn–Wong acceleration criterion,
common-dilation value bound, small and unbounded branches, and literal
three-insertion obstruction. The exact 27-module closure passed fresh
strict source checks, an audit of all 563 owned declarations including
11 private declarations, and exact stock-kernel replay of every module.
All 49 required endpoints are theorems. The registration adds 18 proof
modules and preserves the checked source hashes.
[Scope](docs/lean-status.md#complete-unrestricted-two-speed-insertion-theorem) ·
[Raw receipt](docs/verification/two-insertions-exact-44524198858/receipt.json).
The merged-package gate remains separate.


## 2026-11-19 — Actual Legendre-pair construction and quotient transport

Registered the matrix constructed from an actual Legendre pair, including the order-2396 specialization, and the actual invariant quotient/layer data used to exclude order 27. Their exact closures passed all three gates: construction, five modules and 87 project theorems; quotient transport, eighteen modules and 353 project theorems. Eight previously unregistered modules and thirteen named endpoints were added. The full finite no-lift certificate and final multiplier bound of nine remain pending.
[Statements and receipts](docs/lean-status.md#actual-legendre-pair-matrix-and-quotient-transport).

## 2026-11-19 — Complete Erdős 607 line-size asymptotic

Registered the sharp asymptotic for the actual real-plane record count, with
the exact leading constant. The proof discharges the characteristic-product
limit, Fourier domination, core-lattice integral, Gaussian constant, and
normalization. Its 78-module closure passed strict sources, a 1,582-theorem
standard-axiom audit, and independent pinned-kernel replay at `36b13722`.

The analytic generating function and actual Fourier coefficient identity also
passed their 39-module/867-theorem closure at `daa7d2c5`. Both exact receipts
are archived after comparison of all 93 recorded paths. The 44 new proof
modules and 20 required endpoints complete the stated note, alongside its
earlier geometry and formal-series proofs. The full merged-package gate is
separate; Li remains last.
[Exact statement and receipts](docs/lean-status.md#complete-erdős-607-line-size-asymptotic).

## 2026-11-19 — Complete Frankl high-girth frequency theorem

Registered the full all-point `518208/1000000` distinct-union bound for every
uniform generator size at least three, under three-regularity and incidence
girth at least sixteen. Actual boundary configurations, finite fiber
averaging, all twelve small-degree certificates, and the large-degree
linearity consequence discharge every proof input. Both girth formulations
and removal of the empty union are included.

The exact 64-module closure passed fresh strict sources, the all-owned
1,363-declaration axiom audit, and pinned stock-kernel replay. The 47 new
modules and 34 new required endpoints are registered; the full merged gate
remains separate. The cyclic span-four result and the overall campaign
remain incomplete. [Checked scope and receipt](docs/lean-status.md#complete-frankl-high-girth-frequency-theorem).

## 2026-11-19 — Complete conditional Hadamard border construction

Registered the full fixed-border construction from the original sign rows
and correlation equations on every finite abelian group with an index-four
subgroup. The proof derives normalization, checks the actual core and literal
border, and returns the final matrix. Its size-149 specialization has order
2396. The fourteen baseline patterns are exhaustive with actual row-operation
witnesses. Binary rows satisfying the hypotheses are still required.

The length-1197 multiplier group is also proved to have order dividing 27,
with its invariant quotient of order three constructed. The sharper bound of
nine and finite quotient/no-lift proof remain pending. Four exact passing
source/audit/kernel receipts register 31 modules and 17 required endpoints,
after comparison of all fifty recorded paths. The full merged gate remains
separate. [Scope and receipts](docs/lean-status.md#complete-conditional-fixed-border-construction-and-fourteen-patterns).

## 2026-11-19 — Complete two-difference Motzkin formalization

Registered the exhaustive integer relation-basis classification and its
compact-density trichotomy. Every pair now receives the appropriate zero-rank,
one-relation, or rank-two Hermite formula without an assumed basis. The exact
41-module closure passed strict sources, a 743-theorem standard-axiom audit,
and independent pinned-kernel replay. Two modules and seven required
endpoints join the accepted package after comparison of every recorded hash.

This closes the stated Motzkin note, including its earlier compact and cyclic
equalities, exact evaluator with complexity bounds, and explicit attaining
witnesses. The full merged-package gate remains separate. Li remains last.
[Exact scope and receipt](docs/lean-status.md#complete-two-difference-motzkin-theorem).

## 2026-11-19 — Checked sharp cover, voltage normalization, and border transport

Registered thirteen unchanged proof modules after four exact hosted closures
passed strict source checks, standard-axiom audits, and independent replay
with the unchanged pinned kernel checker. The connected 95-vertex cyclic
cover has attained least power-of-two cycle length 32; its seven-module
closure audited 288 project theorems. Arbitrary seven-voltage normalization
passed in four modules with 131 audited theorems. Finite-border transport
passed in two modules with 66 audited theorems, retaining its finite
certificate identities as inputs. Actual-row normalization passed in two
modules with 14 audited theorems, retaining its compression-shape inputs.

The universal cover theorem remains under issue 18. Deriving the compression
shapes, checking the literal finite certificate, and final Hadamard assembly
remain under issue 17. The actual row-operation scope in issue 26 is complete.
Li remains deferred. [Checked scope and receipts](docs/lean-status.md#complete-sharp-95-vertex-example-and-arbitrary-voltage-normalization).

## 2026-11-19 — Checked cyclic assembly and weight transport

Registered 32 unchanged proof modules after five hosted source, axiom and
stock-kernel gates passed. The accepted packet includes the conditional
all-period span-four assembly, its arbitrary-family transfer, the 48-case
literal weight pilot, exact overlap enumeration, and injective weight
transport with a proved cached evaluator. The concrete graph, rank and full
weight tables remain unfinished. No complete span-four theorem is claimed.
[Scope and receipts](docs/lean-status.md#frankl-cyclic-assembly-and-weight-helpers--19-november-2026).

## 2026-11-19 — Complete fixed-border multiplier and orbit bounds

Registered all 12 border-symmetry proof modules after their exact closure at
`682d0917` passed strict sources, a 216-theorem standard-axiom audit, and the
unchanged pinned kernel replay. The theorem applies to actual sign rows on
every finite abelian group with a subgroup of size 149 and index four.
The full common multiplier group is cyclic of order dividing four, and every
preserving subgroup leaves at least 151 actual sign orbits. Product coordinates
and all transports are proved; no split-domain or normalized-pattern premise
is added. The proof uses raw compressed correlations and does not require
the fourteen-pattern enumeration.
[Receipt](docs/verification/hadamard-border-transfer-682d0917.json) ·
[Checked statement](docs/lean-status.md#complete-fixed-border-multiplier-and-orbit-bounds).

Issue 22 is complete. The separate sequence restrictions and fixed-border
construction remain under issue 17. Issue 23 takes the sharp 95-vertex
Erdős–Gyárfás example in separate candidate sources. Li remains deferred.

## 2026-11-19 — Checked literal mask checker and exact domains

Registered two exact local-mask checker modules after their ten-module hosted
gate passed at `a632fc82`. The gate checked 163 project theorems, 38 required
endpoints, and every module with the stock kernel checker. The checker counts
actual compatible sets and proves its finite domains. Full window data and
the complete span-four theorem remain separate obligations.
[Receipt](docs/verification/frankl-mask-domains-a632fc82.json).

## 2026-11-19 — Checked Vaughan theorem and small cyclic components

Registered the full three-triples Vaughan theorem and every nontrivial cyclic
span-four family on at most six sites. Further period-seven-through-ten
results retain an explicit residual-graph hypothesis. The exact 53-module
closure passed strict sources, a 2,057-theorem axiom audit, checks of all 534
private certificate nodes, and stock kernel replay at `6544adcc`. Its 50 new
proof sources are unchanged. The full span-four theorem remains incomplete.
[Receipt](docs/verification/frankl-fc-packet-6544adcc.json).

## 2026-11-19 — Checked Frankl local certificate semantics

Registered the integer local checker and its equivalent maximal-cover checker.
Their exact five-module closure passed strict source checks, a 66-theorem axiom
audit, and independent kernel replay at `ad07e385`. Both checkers count actual
distinct inside patterns. No finite window weight table is asserted by this
registration. The full merged-package check remains separate.
[Receipt](docs/verification/frankl-maximal-cover-ad07e385.json).

## 2026-11-19 — Complete Hadamard automorphism obstruction

The full signed row/column automorphism theorem at order 2396 passed its
28-module strict-source, 297-theorem standard-axiom, and unchanged pinned-kernel
gate at `fb6b6e06`. The actual automorphism group and all subgroup quotients
have cardinalities not divisible by 479. The independent relative-ideal-norm
proof also passed its 15-module, 164-theorem gate. Sixteen additional proof
source files are registered, bringing this lane to 37; their closures include
the earlier 12-module, 128-theorem cyclotomic descent check at `7098a0e8`.
[Assembly receipt](docs/verification/hadamard-automorphism-assembly-fb6b6e06.json) ·
[Independent proof receipt](docs/verification/hadamard-automorphism-class-alternative-fb6b6e06.json) ·
[Descent receipt](docs/verification/hadamard-automorphism-cyclotomic-7098a0e8.json).
The expanded quadratic-model closure also passed all three gates at `0a1deef7`,
with 16 modules and 157 audited theorems, proving uniqueness of the quadratic
subfield and the exact equal-parity integer-coordinate equivalence.
[Quadratic-model receipt](docs/verification/hadamard-automorphism-quadratic-model-0a1deef7.json).

The separate sequence and border results remain pending. Issue 22 claims the
later fixed-border common multiplier and 151-orbit tail. The status inventory
now explicitly includes the two-insertion and Erdős–Gyárfás cover obligations;
Li remains deferred.

## 2026-11-19 — Checked quadratic field and ideal-class witness

Registered six Hadamard automorphism proof files that construct the actual
quadratic fixed field and a prime above 599 of norm 599 and exact ideal-class
order five. The nine-module closure passed strict sources, a 111-theorem axiom
audit, and independent pinned-kernel replay at `ae7871fc`. The universal
prime-pair alternative and full automorphism assembly remain candidates.
[Receipt](docs/verification/hadamard-automorphism-class-order-ae7871fc.json).

## 2026-11-19 — Checked Hadamard automorphism permutation component

Six proof files now cover explicit diagonal normalization, fixed-point and
cycle counts, cyclic reindexing, integer transport, and the signed automorphism
subgroup. Their seven-module closure passed strict source checks, a 100-theorem
axiom audit, and independent pinned-kernel replay at `e9a9bb45`. The full
obstruction still awaits cyclotomic descent and final assembly.
[Receipt](docs/verification/hadamard-automorphism-permutation-e9a9bb45.json).

## 2026-11-19 — Checked Hadamard automorphism Fourier component

Registered the explicit Fourier, binary overlap, indicator, and determinant
components after strict source checks, a 32-theorem transitive axiom audit,
and independent pinned-kernel replay of their six-module closure at `ee1be6e0`.
The full automorphism and ideal-class statements remain candidates.
[Receipt](docs/verification/hadamard-automorphism-fourier-ee1be6e0.json).

## 2026-11-19 — Checked Hadamard automorphism arithmetic

Registered the arithmetic and integral-basis coefficient component of the
order-479 automorphism obstruction. The five-module candidate closure passed
strict source checks, a 38-theorem transitive axiom audit, and independent
pinned-kernel replay at `56cb125e`, with unchanged sources. The full matrix
and cyclotomic assembly, and the separate ideal-class argument, remain
candidates. [Receipt](docs/verification/hadamard-automorphism-arithmetic-56cb125e.json).

## 2026-11-19 — Complete Frankl large-generator frequency bound

Registered the full all-`k ≥ 15` bound of `657/1000` for every point, with
actual distinct-union counting and the original size, regularity, and linear
intersection hypotheses. Its 16-module closure passed strict sources, a
231-theorem transitive axiom audit, and pinned-kernel replay at `663f7275`.
The high-girth cases `3 ≤ k ≤ 14` and cyclic span-four theorem remain in
progress. [Receipt](docs/frankl-large-hosted-receipt.json).

## 2026-11-19 — Checked Frankl counting foundations

Registered six proof modules after their exact hosted source, transitive axiom,
and pinned-kernel gates passed at `57d699c7`. The packet proves the general
weighted local-certificate implication, the incidence-graph bijection, finite
lopsided conditioning, and the all-parameter numerical criterion. Both full
Frankl results remain incomplete. [Receipt](docs/frankl-foundations-hosted-receipt.json).

## 2026-11-19 — Searchable collection website

Added a GitHub Pages site with search, subject filters, and individual result pages.
Updated result titles, citation metadata, and links to the maintainer's website.
The README now shows the Lean and computational verification workflows.
Reconciled five index flags with the existing partial results in the [Lean status report](docs/lean-status.md).
Mathematical claims and checked proof scopes are unchanged.

## 2026-11-19 — Partial results for three open problems

Published the two Frankl generator results, the two-speed Lonely Runner insertion theorem and a sharp bound for abelian covers in the Erdős–Gyárfás search. Each entry gives its hypotheses and reproducible checks. [Catalogue](CONTENTS.md#partial-results-on-open-problems)

## 2026-11-19 — Formal generating function and cyclic Motzkin formulas

- Registered the exact coefficientwise generating function after its
  14-module strict source check, 496-theorem axiom audit, and kernel replay.
- Registered the all-modulus cyclic formulas, gcd scaling, odd-cycle
  criterion, exact example, and abstract rational-circle attainment after
  the 48-module source check, 812-theorem audit, and kernel replay.
- Added 14 proof modules, giving 482 proof modules and two roots. The empty
  cyclic candidate wrapper is excluded. The full merged gate remains pending.
- Recorded the completed historical full check of `42fff1a2`: 397 proof
  modules, both roots, and 10,843 audited theorems.
- Added separate unregistered gates for Gaussian integration, branch
  coefficients, coefficient rescaling, the actual supported integral limit,
  exhaustive Motzkin relation bases, rational interval witnesses, the fixed
  character window, and the final sharp coefficient theorem.


## 2026-11-19 — Order-479 automorphisms excluded at Hadamard order 2396

Added a cyclotomic obstruction for every candidate matrix, with a second ideal-class proof. The index-four core search also has common multiplier group size at most four. [Scope and proofs](results/hadamard-2396/)

## 2026-11-19 — Partial results at Hadamard order 2396

Added two verified symmetry restrictions, the finite enumeration and a conditional border construction for the open order-2396 existence problem. [Scope and checks](results/hadamard-2396/)

## 2026-11-19 — Relation formulas, Euler correction, and tuple reconstruction

- Registered the Motzkin formulas for stated relation generators and
  finite-relation Borel attainment after a 39-module strict source check,
  729-theorem axiom audit, and independent kernel replay.
- Registered the uniform corrected finite Euler product after its eight-module
  closure passed strict sources, a 122-theorem audit, and independent replay.
- Registered finite tuple/core/tail reconstruction and cumulative cost counting
  from the earlier nine-module, 307-theorem hosted receipt.
- Added 13 checked proof modules, giving 468 proof modules and two roots.
  Full merged verification remains pending. Motzkin basis existence and the
  cyclic/evaluator claims, and the line-size sharp asymptotic, remain open.

## 2026-11-19 — General compact Motzkin equality

- Registered the exact density/continuous-character equality for arbitrary
  compact Hausdorff abelian groups, including zero differences.
- The exact 34-module hosted closure passed strict sources, a 664-theorem axiom
  audit, and independent kernel replay with unchanged source and gate hashes.
- Added 22 checked proof modules to the concurrent 433-module package. The
  combined 455-module hosted gate remains pending; ancillary rank, cyclic,
  evaluation, and complexity claims remain candidates.

## 2026-11-19 — Exact line-size geometry and saddle profile

- Proved the real-plane realizability criterion and exact geometric record
  count for every point count; the 20-module closure passed source, the
  342-theorem ownership audit, and independent kernel replay.
- Proved the exact saddle constant and moment identities from the literal
  integral, with a five-module, 137-theorem audit and kernel replay.
- Registered these checked components and the smooth Euler kernel. The
  exact generating function, corrected product estimate, Fourier bounds,
  and sharp asymptotic remain ongoing work.

## 2026-11-18 (America/Chicago) — Complete four-speed gap

- Proved the all-size four-speed gap and both critical directions below `2/9`,
  including their exact value `1/5` and the four-speed runner lower bound.
- Registered 36 additional modules after exact dependency coverage, an
  1,880-theorem ownership/axiom audit, and independent kernel checks.
- Supplied the previously explicit gap input to the existing five-speed
  plane and cutoff reductions. The bounded five-speed enumeration remains open.

## 2026-11-19 — Complete concrete CUT games and line-size foundations

- Identified both actual recursive CUT games with their proposed sequence at
  every natural pile size. Proved least eventual arithmetic period 12, saltus
  8, and earliest period-12 start 7. Seven compact certificate modules passed
  source checks and the 1,127-declaration ownership audit; all 23 project
  modules in their exact closure passed independent kernel replay.
- Checked seven Erdős 607 foundations, including ordinary-line existence for
  actual finite real-plane point sets, the selected-graph cost identity, and
  the core-to-gap weight equivalence. Geometric sufficiency and the asymptotic
  theorem remain in progress.
- Recorded successful hosted full source, axiom, and kernel verification of
  the 219-module Pham/finite-Motzkin checkpoint `18bf908`.

[Home](README.md) · [Catalogue](CONTENTS.md)

## 2026-11-18 (America/Chicago) — Graph theorem and runner components

- Registered the all-order Graffiti.pc318 theorem and its sharp five-vertex
  example after local and hosted source, axiom, and independent kernel checks.
  The contributed proof remains credited to @JesterInABarrel.
- Registered the consecutive runner family for counts 2 through 14, both
  exceptional eight-speed families, classification within all three stated
  eight-speed product families, and the displayed higher-speed examples.
  Exhaustive higher-speed classifications remain open.
- Registered the exact shifted hyperplane maximum, its attaining point, and
  the upper bound for every orthogonal integer velocity. The statistical and
  counting parts remain open.
- Kept the finite four-speed assembly, KZ arithmetic, reduced-basis geometry,
  Haar/Fourier, and closed-search developments under separate candidate gates.

## 2026-11-19 — Complete rectangle asymptotic and finite plane reduction

- Completed the growing-rectangle theorem for literal real-position tilings,
  uniformly over every `w ≥ h`. The 46-module proof includes the cumulative
  partition estimate and passed the 587-declaration axiom audit and kernel replay.
- Registered the unconditional four-speed cutoff 5,832 and all 64 finite plane
  certificate blocks, covering 122,880 indexed cases. Both hosted matrix runs
  passed source, axiom, and stock kernel checks.
- Registered the plane classification and five-speed cutoff 279,841 with the
  four-speed gap retained as an explicit mathematical input. The exhaustive
  five-speed classification remains in progress.
- Preserved the concurrent completed Pham proof, finite Motzkin theorem, and
  separate unregistered candidate developments.

## 2026-11-19 — Complete Pham proof and finite Motzkin theorem

- Derived both Pham limiting-series identities from actual Bulgarian-solitaire
  cycles and first-entry levels. Proved reduced denominator degrees 5 and 10
  and minimality against every nonzero alternative denominator. The complete
  36-module closure passed source checks, its 1,080-declaration axiom audit,
  and independent kernel replay.
- Completed the Motzkin equality and both attaining witnesses for every finite
  abelian group generated by the two differences. The 12-module closure passed
  independent kernel replay and the 115-declaration Motzkin audit passed.
  The arbitrary compact-group theorem and later algorithmic claims remain open.
- Added exact-closure replay for a selected candidate root. Six protocol tests
  check closure validation, object staging and checker failure propagation.

## 2026-11-19 — Additive Lean integration

- Combined 177 accepted proof modules with both project roots. The merged
  source build and compiled/direct standard-axiom audits passed; the audit
  checked 7,581 theorem declarations.
- Renamed the two independent finite rectangle inputs to `RectangleFinite`
  after detecting a collision with the concurrent shelf-packing proof. Both
  renamed modules passed fresh strict source checks and independent kernel replay.
- Preserved the separate candidate workflows and their unregistered sources.
  The component kernel receipts and the full merged hosted gate are recorded
  separately in the Lean status report.

## 2026-11-18 — Random lonely runners on a fixed hyperplane

- Added the conditional limiting law for Beck and Everett’s statistical question, the finite-subspace description of exceptional velocities, and the unshifted endpoint density for full-support normals.

## 2026-11-18 — Corrected solitaire and combined formalizations

- Completed the corrected L-solitaire theorem in Lean for arbitrary layer sets,
  actual recurrent configurations, and every diverging horizontal scale. The
  finite dynamics, stable-reference classification, analytic bound and limit
  transfer passed source, axiom and independent kernel checks.
- Merged the concurrent density and loneliness foundations, and identified the
  two real distance definitions through a checked pair-sum interface.
- Completed the all-parameter gap-five/gap-seven character formulas and the
  general odd-cycle density theorem. Added finite rectangle packing/counting
  inputs and the exact actual-pile CUT composition theorem.
- Passed the combined source build, the 6,954-theorem standard-axiom audit,
  and independent kernel replay of all 152 accepted proof modules and both
  roots. The replay list is checked against the source-import closure.

## 2026-11-18 — Graffiti.pc Conjecture 318 (credited to @JesterInABarrel)

- Added the all-order proof of Conjecture 318 **credited to [@JesterInABarrel](https://x.com/JesterInABarrel/status/2123233964827812334)**, its stronger total-dominating-pair theorem, and a sharp five-vertex counterexample to lowering the hypothesis by one.
- Checked 419,235 labeled graphs (7,337 satisfying the hypothesis); Lean formalization remains open.

## 2026-11-18 — Complete distance-graph classifications

- Proved the exact gap-five and gap-seven density tables for every positive parameter, including optimal periodic constructions.
- Proved the exact Conjecture 39 discrepancy and infinitely many strict counterexamples.
- Added checked finite rectangle-tiling and Euler-product components; the uniform rectangle asymptotic remains incomplete.
- Added the two-integer-direction plane reduction with the four-speed gap retained as an explicit hypothesis.

## 2026-11-19 — Equality for eleven through fourteen runners

- Classified the primitive equality cases using published binary sieves and an additional integer-direction calculation.

## 2026-11-18 — Complete Haralambis formalization

- Proved the three-difference density theorem and an optimal pair-sum-period construction for every positive triple.
- Proved the general greedy packing bound and the lonely-runner lower bound for at most three speeds.
- Added coordinate coalescence, integer directions, real-span dimension, and rational subspace extensions to the five-speed reduction.
- Recorded the successful hosted Lean build, axiom audit, and kernel replay for the previous density/CUT checkpoint.

## 2026-11-19 — Eight-speed loneliness spectrum

- Added the full classification below 1/8, the three families, and the table of 17 sporadic tuples.

## 2026-11-19 — Seven-speed loneliness spectrum

- Added the full classification below 1/7, the table of 27 sporadic tuples and the corollary on Zhu’s triangle conjecture for six and seven distances.

## 2026-11-18 — Checked density, CUT, and loneliness proofs

- Added complete symmetric four-point packing/covering and nonmixed-gap packing/circle proofs, including common-divisor normalization.
- Added the complete general finite CUT test and completeness of candidate enumeration.
- Added exact real-time loneliness certificates, both critical-family reductions, and the infinite five-speed family.
- Updated the formalization index to distinguish these checked components from the remaining spectrum classification.

## 2026-11-19 — Ten-runner equality classification

- Added the proof that only consecutive primitive speeds attain 1/10 and the verifier for its 28 modular certificates.

## 2026-11-19 — Collection navigation

- Split the landing page, full result catalogue, and verification instructions.
- Added landing pages for results that previously opened as file listings.
- Grouped result files under `results/` and moved the shared Lean package to `lean/`.
- Updated navigation, CI commands, and certificate-generation paths.
- Kept mathematical statements and formalization status unchanged.

## 2026-11-18 — Formalization campaign resumed

- Completed the CUT Family B theorem for the actual recursively defined games,
  including infinite cut sets and the sharp discrepancy bound.
- Added exact reverse-solitaire preimage semantics and uniform arithmetic-tail
  graph recognizers.
- Added a general loneliness maximum theorem and 31 kernel-checked exact values.
- Completed the symmetric four-point packing and covering densities, including
  attainments and sharp interval lengths.
- Continued the corrected solitaire and remaining density/automata proofs.
- Kept Li last and tracked active lanes in issue 1.

This file records collection-level changes, not a complete discovery or priority timeline. For individual additions and revisions, see [the commit history](https://github.com/1337isnot1337/solved-conjectures/commits/main/). Ongoing formalization work is recorded in [the status report](docs/lean-status.md) and [campaign notes](docs/formalization.md).


## 2026-11-19: universal abelian-cover theorem and further exact components

Registered the complete abelian voltage-cover cycle theorem and retained
the sharp 95-vertex example. Also registered the literal finite-border
certificate and the full length-598 order-eleven multiplier obstruction.
Exact source, axiom, and kernel receipts are recorded in `docs/verification`.
The Motzkin evaluator, explicit rational interval witnesses, and narrow
prime-257 minimum-pair-20 support certificate were registered separately.
The remaining collection results are still in progress; Li has not started.

## 2026-11-19: Rational-lattice and Gram components

Registered the eight rectangular/rational-lattice sources and their 50 theorem endpoints after the complete hosted source, owned/private axiom, and stock-kernel gate passed. The six-speed spectrum remains partial; the norm components retain `hfour` and `hplane`.

## 2026-11-19: Conditional two-parameter radius estimate

Registered `Conjectures.LonelinessTwoParameterRadius` and its 6 theorem endpoints after the complete 13-module hosted source, owned/private axiom, and stock-kernel gate passed. The result status remains partial; the retained hypotheses are stated in the status report.

## 2026-11-19: Six-speed norm bounds with the four-speed input discharged

Registered `Conjectures.LonelinessSixSpectrumLatticeNormFourSpeed` and its 3 theorem endpoints after the complete 113-module hosted source, owned/private axiom, and stock-kernel gate passed. The result status remains partial; the retained hypotheses are stated in the status report.

## 2026-11-19: Seven-coordinate implications with the five-speed input discharged

Registered `Conjectures.LonelinessSevenCoordinateFiveSpeed` and its 6 theorem endpoints after the complete 171-module hosted source, owned/private axiom, and stock-kernel gate passed. The result status remains partial; the retained hypotheses are stated in the status report.

## 2026-11-19: Actual rational-lattice quotient index

Registered `Conjectures.LonelinessRationalLatticeQuotient` and its 5 theorem endpoints after the complete 20-module hosted source, selected-declaration axiom audit with raw/private visibility, and stock-kernel gate passed. The result status remains partial; the retained hypotheses are stated in the status report.

## 2026-11-20 — Erdős–Granville–Pomerance–Spiro conjecture

Added a written partial result for arbitrary natural density-zero target sets.
The three input families in the [divisor-sum proof](results/erdos-granville-pomerance-spiro/)
have combined natural density about 53.46%. The computational workflow checks
finite algebra and congruence cases. The full conjecture remains open.

## 2026-11-20 — Horňák–Woźniak conjecture

Added a [proof of both vertex-decomposability conjectures](results/hornak-wozniak/) for tripods and four-arm trees with a one-edge arm. The endpoint argument removes the middle-arm bound and shows that three of the five admissibility tests suffice. The catalogue links the literature check and reproducible allocation checks.

## 2026-11-20 — Sonntag–Teichert conjecture

Added a [proof of connectivity for tournament domination hypergraphs](results/sonntag-teichert/) on their nonisolated vertices. The argument uses minimal closed in-neighbourhoods and also characterizes the disconnected cases for oriented graphs.





