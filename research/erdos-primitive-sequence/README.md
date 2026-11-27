# Erdős’s primitive sequence problem

Erdős asks which increasing sequences of positive exponents $E=\{n_1,n_2,\ldots\}$ admit a primitive set $A$ and a constant $c>0$ with $A(2^n)\ge c2^n$ for every $n\in E$. Here $A(x)$ counts positive integers in $A$ up to $x$, and two distinct members of a primitive set cannot divide one another. This is the prescribed-scale part of [Erdős Problem 892](https://www.erdosproblems.com/892), stated on [p. 101 of Erdős’s 1980 survey](https://www.renyi.hu/~p_erdos/1980-03.pdf). The unrestricted characterization and the separate gcd-free domination question remain open. [Research issue 821](https://github.com/1337isnot1337/solved-conjectures/issues/821)

## A sufficient condition for prescribed peaks

The [construction and proof](prescribed-scales.md) establish the required peaks for every prescribed exponent set with at most $K H^\sigma$ points in each interval of length $H\ge1$, for any fixed $\sigma<1$ with $\sigma>0$. In particular this includes all $n_i=\lfloor i^\alpha\rfloor$ with $\alpha>1$. The construction uses one primitive set for all requested scales. The [full-counting-dimension extension](prescribed-scales.md#exponent-sets-of-full-counting-dimension) also allows every uniformly bounded interval count $N_E(H)\ll H\exp(-c(\log H)^a)$ for $1/2<a<1$. For example, it covers $n_i=\lfloor i\exp((\log i)^a)\rfloor$, for which no upper bound $N_E(H)\ll H^\sigma$ with fixed $\sigma<1$ holds.

## An obstruction in every translated interval of exponents

The [July 2026 report](https://www.erdosproblemaday.com/report/892) proves that $\sum_{n\in E}1/n$ must converge. That condition alone allows arbitrarily long intervals of consecutive exponents. An older short-interval theorem of Erdős, Sárközy and Szemerédi rules these out. They bound $\sum_{x<a\le xt}1/a$ for primitive $A$ by $O(\log t/\sqrt{\log\log t})$ uniformly in $x$ for large $t$. [Debrecen paper, pp. 38–39](https://combinatorica.hu/~p_erdos/1970-09.pdf)

Indeed, for nonnegative integers $u$ and $h\ge3$,

```math
c\,|E\cap[u,u+h]|\le \sum_{k=u}^{u+h}2^{-k}A(2^k)
\le 2 + 2\sum_{2^u<a\le 2^{u+h},\ a\in A}\frac1a
\ll 1+\frac h{\sqrt{\log h}}.
```

The terms $a\le2^u$ contribute at most two. Each other $a$ contributes a geometric tail beginning at $\lceil\log_2 a\rceil$. In particular the union of exponent intervals $[2^{j^2},2^{j^2}+j]$ for $j\ge2$ has a convergent reciprocal sum but cannot support the required density peaks. Its $j$th interval alone violates the bound as $j$ tends to infinity.

## Literature and attribution

- Erdős, Sárközy and Szemerédi already state on p. 38 that convergence of the Erdős weighted sum and the Behrend–Erdős–Sárközy–Szemerédi global harmonic estimate together are insufficient for primitive domination. On pp. 40–41 they construct high-density sets by controlling prime factors up to every cutoff and bound densities of multipliers between their members. The prescribed-scale proof applies that idea to interactions between *prescribed* dyadic blocks. [Original paper](https://combinatorica.hu/~p_erdos/1970-09.pdf)
- Martin and Pomerance give an existence theorem for smoothly growing counting functions. Their introduction phrases a convergence-only version of the question. The joint insufficiency above was already known. [Martin–Pomerance, pp. 521–523](https://publi.math.unideb.hu/paper/1619/download/)
- Besicovitch’s classical construction chooses its scales recursively. Lichtman gives a related construction for a different divisibility relation. Neither construction, as stated there, takes an arbitrary supplied sequence of scales as input. [Besicovitch](https://doi.org/10.1007/BF01448032) · [Lichtman, §5](https://www.cambridge.org/core/journals/forum-of-mathematics-pi/article/proof-of-the-erdos-primitive-set-conjecture/7D838547DEF207B0442E6DCB8BBAA657)
- The July report separates the gcd convention, smooth domination, and prescribed dyadic peaks. The [current discussion](https://www.erdosproblems.com/forum/thread/892) addresses the meaning of a nontrivial gcd solution. [July report](https://www.erdosproblemaday.com/report/892)
