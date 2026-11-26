# Rank-four dual Chow interlacing: sharpness, a slack identity and searches

**Status:** research notes, unreviewed. This does not resolve the open rank-four case of
[Caiolo–Ferroni–Hoster §7.2](https://arxiv.org/html/2605.28474v1#S7.SS2) recorded in
[RANKS.md](../../results/caiolo-ferroni-hoster/RANKS.md). It proposes no catalogue entry and does not
change any attribution. Written with Claude (Anthropic) assistance. No priority claim.

## Relation to existing repository work

- **The reduction is the one already used in issue #675.** By CFH Theorem 4.9, put
  A = β₁₂₃, B = β₁₃ + β₂₃, E = β₁₂ and D = β₂. Then strict interlacing holds when BE > AD. Interlacing
  fails iff BE < AD. Real-rootedness of F\* is (B+E)² ≥ 4AD, which BE ≥ AD implies.
  [reduction_check.py](reduction_check.py) rechecks this symbolically. Below, R = AD/(BE).
- **Paving matroids are already covered.** [PAVING.md](../caiolo-ferroni-hoster-paving/PAVING.md)
  proves real-rootedness and interlacing for paving matroids of every rank. Section 2 below
  re-derives the rank-four case by a different, elementary route. That route uses a plane identity
  and de Bruijn–Erdős. It is recorded only because the identity is reused in Section 3. It is not a
  new result.
- **The hyperplane-complement theorems of #675 (2, 3, 4 outside points, and 5–6 under a condition)
  do not reach the near-extremal examples of Section 4.** In those examples every plane misses
  almost all points.

## 1. Plane decomposition of the slack (exact)

Let M be a simple rank-four matroid with n points and f₂ lines. Set X = D = f₂ − 1. For a plane P,
let p_P be its number of points, L_P its number of lines, and |μ_P| = Σ_{ℓ⊂P}(|ℓ|−1) − p_P + 1
its absolute Möbius invariant. Then

  E·B − X·A = Σ_P [ E(p_P + L_P − 2) − X·|μ_P| ] − (n−1)·E. (1)

[identity_check.py](identity_check.py) checks this exactly on 300 random subsets of PG(3,3).

## 2. Rank-four paving matroids (subsumed by PAVING.md)

If every line has two points, (1) becomes

  2(EB − XA) = (n−2)·Σ_P g(p_P) − (n−1)²(n−2), with g(p) = −p² + (2n+1)p − 3n + 1.

g is concave, and g(3) = 3n−5 ≤ g(n−1). So each plane contributes at least 3n−5. Every point lies on
at least n−1 planes: apply de Bruijn–Erdős to the contraction at that point. Hence EB > XA.

## 3. Line-level form of the slack (exact)

For a line ℓ, let s_ℓ be its number of points and t_ℓ the number of planes through it. Put
Π = Σ_P p_P and

  K = f₂·Σ_ℓ (s_ℓ−1)t_ℓ − (Σ_ℓ (s_ℓ−1))(Σ_ℓ t_ℓ) = f₂² · Cov_lines(s, t).

Then

  E·B − X·A = −K + Σ_ℓ t_ℓ(s_ℓ − n) + (E+X)·Π − (2E+X)·f₃ − (n−1)·E. (2)

[covariance_check.py](covariance_check.py) checks this exactly on random subsets of PG(3,q) for
q = 3, 5, 7.

**Consequence.** At leading order, only K can make the slack negative. A counterexample therefore
needs a positive covariance between the number of points on a line and the number of planes through
it. Combined with Π ≥ Σ_ℓ s_ℓ (de Bruijn–Erdős again), a violation needs roughly
Cov(s,t) ≳ (mean s)². In PG(3,q) restrictions t_ℓ ≤ q+1. Adding full lines, planes or books of planes
to random sets lowered R in every test ([structured.py](structured.py)).

## 4. The inequality is asymptotically sharp (heuristic and exact numerics)

**Heuristic.** Let S ⊂ PG(3,q) contain each point independently with probability c/q, so |S| ≈ cq².
Replacing every flag count by its expectation gives

  1 − R ≈ (c/q)·( 1/(c−1+e^{−c}) + 1/(1−(1+c)e^{−c}) ) + O(q⁻²),

which is minimized near c ≈ 2.4, where 1 − R ≈ 5.08/q.

**Exact values.** [random_sets.py](random_sets.py) computed exact flag counts for single samples at
c = 2.5:

| q | 7 | 11 | 13 | 17 | 19 |
|---|---|---|---|---|---|
| R | 0.573 | 0.681 | 0.716 | 0.768 | 0.787 |
| q·(1−R) | 3.0 | 3.5 | 3.7 | 3.9 | 4.05 |

The last row is rising toward the predicted ≈ 5.1.

**Implication, if the heuristic is made rigorous.** sup R = 1 over simple rank-four matroids.
Then no bound AD ≤ (1−ε)·BE with fixed ε > 0 holds, and any proof of the rank-four inequality must
be sharp to first order. A rigorous version needs concentration for the flag counts of random
subsets; that is not done here.

## 5. Searches (no violation found)

| Family | Largest R found | Script |
|---|---|---|
| U(4,n) | → 1/4 | [families.py](families.py) |
| PG(3,q), AG(3,q) | → 1/2 | [families.py](families.py) |
| rank-four BCEL coalescence (k = 3) | → 2/5, exact rational functions of q | [families.py](families.py) |
| all simple binary rank-four matroids (2¹⁵ subsets of PG(3,2)) | 0.3462 | [pg_search.py](pg_search.py) |
| hill climbing in PG(3,q), q = 3, 5, 7, 11, 13 | 0.4226, 0.5244, 0.5913, 0.6911, 0.7242 | [pg_fast.py](pg_fast.py), [climb_fast.py](climb_fast.py), [logs](logs/) |
| random sets plus full lines, planes or books, q = 13 | below the random baseline | [structured.py](structured.py) |

**The rank-five mechanism does not descend to rank four.** In the coalescence family, the
leading coefficient of γ₂ is (k−2)(k−3)/2, which vanishes at k = 3.

The fast engine [pg_fast.py](pg_fast.py) matches the slow engine [pg_search.py](pg_search.py) at
q = 3 and q = 5.

## Reproduce

Python 3.9+ with SymPy and NumPy:

```sh
cd research/caiolo-ferroni-hoster-rank4-sharpness
python3 -I reduction_check.py
python3 -I identity_check.py
python3 -I covariance_check.py
python3 -I families.py
python3 -I pg_search.py 2
python3 -I random_sets.py 7 11 13
```

`climb_fast.py q steps seed [c]` writes its best set to `logs/` (not committed).

## Open directions

- Make Section 4 rigorous with concentration bounds for random subsets.
- Search for configurations with a positive covariance between s and t outside projective
  restrictions, e.g. truncations of non-representable rank-five matroids.
- Prove BE ≥ AD from (2), using a combinatorial bound on K that is sharp to first order.
