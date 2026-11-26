# Independent audit of the CFH counterexample in Lean (2026-11-25)

**Scope.** I checked the repository's Lean claims for
[results/caiolo-ferroni-hoster](../../results/caiolo-ferroni-hoster/) on this machine:

- whether the Lean files build;
- which axioms the main theorems depend on;
- whether the proofs pass the stock kernel replay;
- whether the Lean definitions match the CFH paper (arXiv:2605.28474v1).

The written proof was not re-refereed beyond spot checks.

## Environment

- macOS arm64, 14 cores.
- elan 4.4.0 (Homebrew `elan-init`) with toolchain `leanprover/lean4:v4.35.0`, as pinned in `lean/lean-toolchain`.
- Mathlib `56a00585…` (tag v4.35.0) and all other dependencies at the revisions in `lake-manifest.json`.
- Repository commit `81a553c5` (main), on local branch `local/cfh-rank4-and-lean-audit`.

## Results

| Check | Result |
|---|---|
| `lake build Conjectures.CaioloFerroniHoster Conjectures.CaioloFerroniHosterRanks` | **Pass** (3561 jobs, 11 min) |
| `#print axioms` on the six headline theorems ([Axioms.lean](Axioms.lean)) | Only `propext`, `Classical.choice`, `Quot.sound` ([output](axioms_output.txt)) |
| grep of the 20 CFH files for `sorry`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `opaque`, `admit` | None found |
| Stock `leanchecker` replay via `scripts/replay_lean.py --root Conjectures.CaioloFerroniHoster` | **Pass**, 9/9 modules ([log](replay_rank5.txt)) |
| Same replay for `--root Conjectures.CaioloFerroniHosterRanks` | **Pass**, 16/16 modules ([log](replay_ranks.txt)) |
| `results/caiolo-ferroni-hoster/verify_counterexample.py` | Pass (q = 17 integers and the degree-43 positivity certificate) |
| Independent kernel-definition check ([kernel_vs_chain.py](kernel_vs_chain.py)), written from the paper only | **Pass** on 16 lattices of ranks 3–5 |

The headline theorems in the axiom check are:

- `counterexample_family`
- `Ranks.kernel_realRooted_iff`
- `Ranks.dualChow_realRooted_iff`
- `Ranks.counterexamples`
- `Ranks.dualChow_negRooted_of_rank_le_four`
- `Ranks.dualAug_negRooted_of_rank_le_three`

The 16 lattices in the independent check are Boolean B₃–B₅, U(4,6), U(5,7), PG(3,2), and random binary matroids of ranks 4 and 5.

## Statement versus paper

**What `counterexample_family` says.** For every prime power q ≥ 17 there is an actual Mathlib `Matroid` on a finite type with:

- the whole type as ground set;
- every set of at most 2 elements independent, i.e. simple;
- `eRank = 5`;
- a degree-4 dual Chow polynomial that is positive on all of ℝ;
- a degree-5 augmented polynomial whose only real zero is −1, and that zero is simple;
- neither polynomial splitting over ℝ.

This is exactly a disproof of Conjecture 7.3 and of its augmented companion, *provided* the two polynomials are CFH's H\* and F\*.

**How the polynomials are defined.**

- `matroidDualChow M` is Σ_S α(S)·chowWeight(S) and `matroidDualAugmented M` is Σ_S α(S)·augmentedWeight(S).
- Here α(S) = `Nat.card (FlatFlag M M.E S)` counts chains of genuine flats (Mathlib `IsFlat`, `eRk`) with rank set S.
- The weights are the chain expansion of CFH Prop. 4.6, (F\*)⁻¹_st = (−1)^ρ(1+…+x^ρ), combined with Prop. 4.7, H\* = F\*·(ζ^rev)^sgn. I re-derived this by hand: combining the last step turns the [g+1]_x factor into [g]_x, exactly as `chowWeight` does.

**The Bridge file matches the paper.** In `CaioloFerroniHosterRankBridge.lean`:

- `chi` is Def 2.8;
- `dualKernel = (χ^rev)^sgn` is Def 3.1;
- `reduced` and `IsChow` give H = −κ̄⁻¹, Def 2.4;
- `IsRightKLS` is Thm 2.3: f_ss = 1, deg < ρ/2, κ = f^rev f⁻¹ written as κf = f^rev;
- F = H·f^rev is Def 2.7.

I compared each against the paper text. `revF` uses `reflect (ρ t − ρ s)`, which is only correct when deg ≤ ρ. That holds for χ and for KLS functions.

## Findings

**Follow-up (2026-11-26).** Finding 1 is closed by the new module `lean/Conjectures/CaioloFerroniHosterKernelLink.lean` (theorem `counterexample_family_kernel`). Finding 2 is fixed in the same change. Both are on the fork's `main` ([fork PR](https://github.com/Shengboj0324/solved-conjectures/pull/1)) and have not been merged upstream.


1. **Definitional gap: minor, not a soundness problem.** The q ≥ 17 theorem `counterexample_family` is stated with the chain-formula polynomials. No Lean theorem identifies them with the kernel-defined H\*, F\* of the paper. The docstring is the only link. The kernel-linked result `Ranks.counterexamples` (and `kernel_realRooted_iff`) only proves failure "for all q ≥ N" with N unspecified.
   - So the precise claim "every prime power q ≥ 17" holds at kernel level only modulo the hand-checkable identity chowWeight-sum = H\*.
   - My Python check confirms that identity exactly on 16 lattices, and the repo's own incidence-recursion replay agrees at q = 17.
   - A Lean lemma `matroidDualChow M = (Ranks.dualChow M).map _` for rank-5 matroids would close the gap.
2. **Out-of-date wording.** `results/caiolo-ferroni-hoster/AUDIT.md` still says "unrefereed, non-Lean-verified". This contradicts `LEAN_REVIEW.md`, the README ✅, and this replay.
3. **Supplement scope is stated correctly.** RANKS.md says the interlacing clause is not in Lean, and the rank-4 augmented and interlacing cases are open. This matches the code: `dualAug_negRooted_of_rank_le_three` stops at r ≤ 3. See [the rank-four sharpness notes](../caiolo-ferroni-hoster-rank4-sharpness/README.md).
4. **Status of the result.** Mathematically, the claimed disproof holds up under every check I ran. It remains unrefereed and does not claim priority.

## Reproduce

```bash
cd lean
lake build Conjectures.CaioloFerroniHoster Conjectures.CaioloFerroniHosterRanks
```

```bash
cd lean
lake env lean ../research/caiolo-ferroni-hoster-lean-audit/Axioms.lean
```

```bash
cd lean
lake env python3 ../scripts/replay_lean.py --root Conjectures.CaioloFerroniHoster
```

```bash
cd lean
lake env python3 ../scripts/replay_lean.py --root Conjectures.CaioloFerroniHosterRanks
```

```bash
python3 -I research/caiolo-ferroni-hoster-lean-audit/kernel_vs_chain.py
```
