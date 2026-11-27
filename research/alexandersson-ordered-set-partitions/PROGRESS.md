# Alexandersson's ordered-set-partition conjecture

**Status (20 November 2026): open.** No complete proof or counterexample is claimed. This is a research note for [issue #108](https://github.com/1337isnot1337/solved-conjectures/issues/108), not an accepted result.

On 26 November a [dominant-pole argument](edge.md) established strict interlacing of a positive fraction of the rightmost real zeros for every fixed threshold. It also gives the limiting endpoint and the spacing of each fixed number of extreme zeros. The full real-rootedness and interlacing conjecture remains open.

A [reciprocal limit at the left edge](left-edge.md) also establishes strict interlacing for each fixed number of the zeros of largest absolute value. Their leading constants are zeros of the sections of the exponential series, in a strict cyclic order across all residues of the row length.

## Primary statement

Let O_{n,j}(t) be the generating polynomial for ordered set partitions of [n] in which t counts blocks of cardinality at least j, with j >= 2. Alexandersson conjectures that for **every** such j and all n, O_{n,j}(t) has only real zeros and that consecutive polynomials O_{n,j}, O_{n+1,j} interlace. This is one jointly named conjecture, not separate solutions for each value of j. Source: [Alexandersson's SymCat open-problem page](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#set-partitions-and-trees), maintained and updated 19 November 2026, section "Set partitions and trees"; source itself records initial checks j<=5, n<=30. This page is an author-maintained public problem statement, not a peer-reviewed 2026 article for this specific conjecture.

## All-parameter recurrences and the exact bottleneck

For j>=2, set O_{0,j}=1. Consider the first block in an ordered set partition of [n]. A block of size s can be chosen in binom(n,s) ways and contributes weight 1 if s<j and t if s>=j. Therefore

    O_{n,j}(t) = sum_{s=1}^n binom(n,s) t^{[s>=j]} O_{n-s,j}(t).        (1)

This recursively defines every coefficient by nonnegative integers, but **nonnegative coefficients do not imply real-rootedness**.

Let

    A_j(z)=sum_{s=1}^{j-1} z^s/s!,
    C_j(z)=sum_{s=j}^infinity z^s/s!,
    F_j(z,t)=sum_{n=0}^infinity O_{n,j}(t) z^n/n!.

The sequence construction yields the source's EGF

    F_j(z,t)=1/(1-A_j(z)-t C_j(z)).                              (2)

The following formal-series identities hold for *every* j>=2 (they are reformulations, not independent conjecture resolutions):

    [t^k] O_{n,j}(t) = n![z^n] C_j(z)^k/(1-A_j(z))^(k+1);       (3)

    F_j'(z,t) = (2+(t-1) z^(j-1)/(j-1)!) F_j(z,t)^2-F_j(z,t). (4)

**Proof of (3):** expand F as a geometric series in t C/(1-A), which is valid in Q[t][[z]] because C has order j. Extract the coefficient of t^k. **Proof of (4):** write B=A+t C, so F=(1-B)^(-1). Direct differentiation of the two tails of the exponential series shows B'=B+1+(t-1) z^(j-1)/(j-1)!. Consequently F'=B'F^2=(2+(t-1) z^(j-1)/(j-1)!)F^2-F.

Set H_n(t)=sum_{r=0}^n binom(n,r) O_{r,j}(t)O_{n-r,j}(t), the nth EGF coefficient of F^2. Comparing (4) gives the exact **nonlinear differential-convolution recurrence**

    O_{n+1,j}(t) = 2H_n(t)-O_{n,j}(t)
                   +(t-1)binom(n,j-1) H_{n-j+1}(t),           (5)

with the last term absent if n<j-1. Formula (5) is potentially useful for induction, but the t-1 multiplier creates a signed combination. Neither (4) nor (5) supplies a root-preserving or interlacing operator. The missing theorem is precisely a compatibility/total-positivity property strong enough to pass from the lower rows to each O_{n,j}; it is **not** supplied by classical closure under positive sums.

## Exact diagnostics

Run `python3 research/alexandersson-ordered-set-partitions/verify.py` (standard library). The script checks (1) against (5) using exact integer polynomials for j=2,...,10 and n<=45, and checks all coefficientwise Newton necessary inequalities for real-rootedness for j=2,...,18, n<=140. The latter are a **necessary** condition only and cannot certify real-rootedness or interlacing. A separate offline exact Sturm isolation checked interlacing for j=6,...,22 and n<=7j-1, while a discriminant scan checked j=6,...,60 and n<4j. These finite diagnostics found no disproof; because they are finite, no conjecture resolution is claimed.

## Literature screen and continuation

The [author-maintained current catalogue](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#set-partitions-and-trees), dated 19 November 2026, still records this exact all-j conjecture. Searches by the complete polynomial notation and exact phrases, including 2026 results, did not locate a complete proof. By contrast, the **unordered** set-partition big-block conjecture P_{n,j} has known j=2 and j=3 cases, and should not be confused with this ordered version. Sagan–Sundaram, [*Ordered set partition posets*](https://arxiv.org/abs/2506.23355), studies a different refinement poset and is not a solution to this generating-polynomial problem. Alexandersson's later [2026 Eulerian paper](https://arxiv.org/abs/2609.07325) resolves several *different* Eulerian/peak problems, not the all-j ordered large-block statement in the checked abstract. Unindexed, unpublished, or inaccessible work may exist, so this is a bounded search conclusion, not a priority claim.

**Next step:** seek a stability-preserving refinement of (5) or a total-positivity theorem for the coefficient-extraction kernel in (3). Keep real-rootedness and consecutive interlacing as separate obligations; failure of the latter alone suffices to refute the full assertion. Avoid counting any fixed j or bounded n as a complete result. No Lean work.
