# Erdős–Szemerédi LCM-window conjecture

**Status: open.** The full window conjecture is equivalent to Ruzsa's near-square divisor conjecture, even if the latter is restricted to square integers. This is a reduction, not a resolution of either problem.

## Statements and sources

- **Erdős–Szemerédi, [Erdős #873](https://www.erdosproblems.com/873).** Given a strictly increasing sequence $A$ of positive integers and $\epsilon>0$, does there exist $k$ such that the number $F(A,X,k)$ of consecutive length-$k$ windows of LCM less than $X$ is less than $X^\epsilon$ for every $X>0$? See [Erdős, *Some of my forgotten problems in number theory*, pp. 48–49](https://hrj.episciences.org/125/pdf).
- **Ruzsa, [Erdős #886](https://erdosproblems.ai/wiki/problems/divisors/E0886).** For every $\eta>0$, is there a uniform bound depending on $\eta$ on the number of divisors of $n$ in $(\sqrt n,\sqrt n+n^{1/2-\eta})$?
- **Relative divisor form.** For every $c>0$, is there a uniform bound depending on $c$ on the number of distinct divisors $d_1<\cdots<d_j$ of any integer $q$ with $d_j-d_1\leq d_1 q^{-c}$?

The proposed equivalence is between these three full statements, plus the restriction of Ruzsa's statement to square $n$. Problem 887's bound by an absolute constant simultaneously for every fixed coefficient of $n^{1/4}$ is a different question.

## Exact centering at a square integer

The relative divisor statement implies Ruzsa's statement, since $d_1>\sqrt n$ makes the span of the proposed window less than $d_1 n^{-\eta}$. Ruzsa's statement trivially implies its restriction to squares.

Conversely, write $a=d_1$ in a relative cluster for $q$. Each $d_i$ maps to
```math
D_i=(q/a)d_i,\qquad Q=q^2.
```
Here $q/a$ is an integer; $D_i$ divides $Q$ because $Q/D_i=a(q/d_i)$. Also $D_1=q=\sqrt Q$, and
```math
D_j-q\leq q^{1-c}=Q^{1/2-c/2}.
```
Discard $D_1$ to get strict inequality at the lower endpoint, and use the square bound at exponent $c/4$ to get strict inequality at the upper endpoint for $q>1$. Add one to the resulting bound. Finite exceptions can always be absorbed in a uniform bound.

## Relative divisor bound implies the LCM-window bound

Fix $\epsilon>0$, let $c=\epsilon/2$, and let $K$ be the bound in the relative divisor form at $c$. Choose $k>K$. In a good window starting at $a_i$, its span $H=a_{i+k-1}-a_i$ satisfies
```math
H>a_i q^{-c}>a_i X^{-c},\qquad q=\mathrm{lcm}(a_i,\ldots,a_{i+k-1})\lt X.
```
Split all qualifying starts into $k$ residue classes of indices modulo $k$, and within each class by the dyadic range $2^u\leq a_i<2^{u+1}$. The intervals from starts in one class are disjoint. In a fixed dyadic range, distinct starts are separated by more than $2^u X^{-c}$, so there are at most $1+X^c$ of them. There are at most $1+\log_2 X$ ranges for $X\geq1$. Thus
```math
F(A,X,k)\leq k(1+X^c)(1+\log_2 X)
```
uniformly in $A$; for sufficiently large $X$ this is strictly less than $X^\epsilon$. Enlarge the fixed $k$ beyond the resulting cutoff. The count cannot increase when the window length increases, and below that cutoff the enlarged windows cannot occur because their last term is at least their length. For $0<X\leq1$ the count is zero. In particular, $k$ can be chosen independently of the sequence, even though #873 allows it to depend on the sequence.

## Unbounded relative divisor clusters disprove the LCM-window bound

If the relative statement fails, fix $c>0$ at which it fails. For each $j\geq2$ take an arbitrarily large $q_j$ with $j$ distinct divisors in a cluster as above. Distinctness makes the span positive; unbounded cluster size permits $q_j$ arbitrarily large for each $j$.

For a cluster with modulus $q=q_j$, smallest term $a$ and span $H$, let $M=\lfloor q^c/4\rfloor$. For $q$ large this is positive. Dilate the cluster by each integer $s=M,\ldots,2M-1$. The resulting $j$-tuples are strictly ordered and pairwise disjoint: $sH\leq (2M-1)a q^{-c}<a/2$. Each has LCM at most $sq<2Mq$. Thus the increasing list of these $jM$ terms contains $M$ distinct consecutive length-$j$ windows with LCM below $X=2Mq$. For every
```math
0<\gamma<\frac{c}{1+c},
```
all sufficiently large $q$ give $M>X^\gamma$.

Build one increasing sequence by concatenating these finite lists successively for $j=2,3,\ldots$, taking $q_j$ so large that the first term $M a$ of each list exceeds the preceding last term. For any fixed $k$, every list with $j\geq k$ supplies at least $M$ good length-$k$ windows by taking the first $k$ terms of each of its $j$-tuples. This violates #873 for the fixed exponent $\gamma$, along arbitrarily large values of $X$, in a **single** sequence. Changing the strict inequality at the endpoints of the divisor interval has no effect on the equivalence because one may use smaller positive exponents.

## Search and scope

On 26 November 2026 the original problem statements, the separate corpus entries for [#873](https://erdosproblems.ai/wiki/problems/integer_sequences/E0873) and [#886](https://erdosproblems.ai/wiki/problems/divisors/E0886), and citation and title searches were compared. [Letendre's short-interval paper](https://arxiv.org/html/2503.12146v1), [Althöfer's note](https://althofer.de/on-erdos_873-based-on-letendre.pdf) and the [July #873 report](https://erdosproblemaday.com/report/873) give partial bounds, including the known range $\epsilon>1/4$ for #873. They do not state the reverse implication from the full window bound to Ruzsa's conjecture. The papers and notes on the separate critical-coefficient [Problem 887](https://erdosproblems.ai/wiki/problems/divisors/E0887) do not give a full resolution for #886. No earlier proof/disproof or statement of the equivalence was located in the sources checked; this is a bounded search, not a priority guarantee.

Next step: in the square reduction, write a divisor of $Q^2$ near $Q$ as $Q u/v$ with $(u,v)=1$. Then $uv\mid Q$. The remaining problem is to bound the number of distinct coprime pairs $u>v$ with $uv\mid Q$ and $(u-v)/v$ smaller than a fixed negative power of $Q$.
