# Erdős–Hajnal set-mapping conjecture

Erdős and Hajnal asked whether $H(n)-\log_2 n\to\infty$. Their $H(n)$ is the smallest $h$ for which one can assign to each proper subset $A$ of an $n$-point set $X$ an element outside $A$, so that every $h$-subset sees every element of $X$ among the values on its subsets. It suffices to consider sets of exactly $h$ points by monotonicity. Their 1968 theorem gives $H(n)<\log_2 n+(3+o(1))\log_2\log_2 n$. The conjectured lower bound remains open here. [Original paper, pp. 345–348](https://www.renyi.hu/~p_erdos/1968-01.pdf) · [Tracking issue #796](https://github.com/1337isnot1337/solved-conjectures/issues/796).

The argument below gives

```math
 H(n)\le \log_2 n+\log_2\log_2 n+O(1).
```

It applies to all sufficiently large orders. It uses the freedom to assign distinct missing-color requests to different subsets after a random first coloring.

## Comparison of the two conventions

Let $H_0(n)$ allow an arbitrary map $g:2^X\to X$. For $n\ge2$,

```math
 H_0(n)\le H(n)\le H_0(n)+1 .
```

Extending an exterior map arbitrarily to $X$ proves the left inequality. For the right inequality, put $h=H_0(n)$ and retain $g(A)$ on each proper $A$ for which $g(A)\notin A$. On the other proper subsets choose any exterior value. Given an $(h+1)$-set $Y$ and a desired value $c$, there is an $h$-set $Z\subseteq Y\setminus\{c\}$. Some $A\subseteq Z$ has $g(A)=c$ and this value survives the modification. If $h=n$, the upper inequality follows from $H(n)\le n$ by assigning $X\setminus\{c\}$ to $c$ for every $c$. Thus the divergent-gap conjecture is equivalent under the two conventions, including when a construction is first obtained for arbitrary colors. [Unrestricted problem statement](https://www.erdosproblems.com/624).

## Matching missing colors to facets

**Theorem.** Let $X$ have $n$ points, let $q\ge2$ be the number of colors, and take $2\le h\le n$. Put $L=2^{h-1}-h$. If

```math
 \binom n{h-1}\binom{(n-h+1)q}{h+1}
       \exp\!\left(-\frac{(h+1)L}{q}\right)<1,
```

there is a coloring of $2^X$ such that every $h$-set sees all $q$ colors on its subsets. A binomial coefficient is zero when its upper argument is smaller than its lower argument.

Color every set of size at most $h-2$ independently and uniformly with one of the $q$ colors. For each $h$-set $Y$, create a request $(Y,c)$ for each color $c$ missing from its colored subsets. The eligible sets for a request are the $h$ facets of $Y$, namely its subsets of size $h-1$.

Fix a facet $T$ and consider requests from the sets $T\cup\{i\}$, with $i\in X\setminus T$. For each $i$ there are $L$ already colored subsets of $T\cup\{i\}$ that contain $i$. Indeed, the free part in $T$ can have any size up to $h-3$, excluding the $h$ choices of sizes $h-2$ and $h-1$. For $h=2$ this gives zero. These collections of subsets are disjoint for different $i$.

Choose $h+1$ distinct possible requests incident to $T$. If $r_i$ of their colors are requested on $T\cup\{i\}$, its $L$ subsets just counted must all avoid those $r_i$ different colors. Independence across $i$ bounds the probability of all the chosen requests occurring by

```math
 \prod_{i:r_i>0}(1-r_i/q)^L
 \le \exp\left(-\frac{L}{q}\sum_i r_i\right)
 =\exp\left(-\frac{(h+1)L}{q}\right).
```

For $L=0$ the avoidance probability is one. There are $(n-h+1)q$ possible requests incident to $T$. Union bounds over the choices of requests and then over $T$ give the displayed sufficient condition. Fix a coloring in which each facet is eligible for at most $h$ requests.

In the bipartite graph from requests to eligible facets every request has degree $h$, and every facet has degree at most $h$. For any collection of requests $S$, counting its $h|S|$ edges at its neighbors gives $|N(S)|\ge |S|$. Hall's theorem provides a distinct eligible facet for every request. Give each matched facet its requested color and complete the coloring arbitrarily. Every formerly missing color on every $Y$ has acquired a witness.

## The bound for the original conjecture

For $q=n$, the product of the two binomial coefficients is at most $n^{h-1}n^{2(h+1)}$. If $L\ge3n\ln n$, the union bound is at most $n^{-2}<1$. For all sufficiently large $n$, taking $h=\lceil\log_2(8n\ln n)\rceil$ gives $h\le n$ and $L\ge3n\ln n$. This proves the asserted upper bound for $H_0(n)$ and the convention comparison transfers it to $H(n)$.

## Source and scope

The original paper chooses one rank of subsets in its upper-bound argument. Gyárfás's later account restates the divergent-gap question. The modern problem page records Alon's positive-fraction image estimates, and the July 2026 working report considers the integrality obstruction and finite thresholds. None of those sources gives the matching argument above. [Erdős–Hajnal](https://www.renyi.hu/~p_erdos/1968-01.pdf) · [Gyárfás, *Problems and memories*](https://www.renyi.hu/~gyarfas/Cikkek/ar2erdos.pdf) · [Erdős Problems discussion](https://www.erdosproblems.com/forum/thread/624) · [Working report](https://erdosproblemaday.com/report/624).

The unrestricted problem is also exactly the existence of a binary $(n,n-h)$ cooling code with $n$ disjoint codesets. Identify a word with its support and each codeset with one color. An encoder can avoid any given $n-h$ coordinates precisely when the remaining $h$ coordinates contain a witness of that color. Conversely, any unused words can be assigned to arbitrary colors. In the terminology of zero-fixing sources, this is a map whose image contains every output on each allowed coordinate subcube. Estimates of distributional closeness to uniform require a separate check before they imply full coverage. The search included these formulations. This is a research upper bound with no claim of global priority or independent review. [Chee–Etzion–Kiah–Vardy, §IV](https://ymchee66.github.io/home/PDF/coolingjournal.pdf) · [Pudlák–Rödl, §§5–6](https://arxiv.org/abs/1904.07949).
