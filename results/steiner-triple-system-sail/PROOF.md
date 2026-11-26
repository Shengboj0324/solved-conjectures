# The Steiner triple system sail problem

A Steiner triple system on $n$ points has three points per block and exactly one block through each pair of points. A *sail* consists of a block $T$ and the three distinct blocks joining a point $p\notin T$ to its points. The latter three meet only at $p$. Granath, Gyárfás, Hardee, Watson and Wu raised the Ramsey question for the sail. Gyárfás’s Question 2.8 asks whether every sufficiently large system has a monochromatic sail in every red–blue block coloring. [Original paper](https://users.renyi.hu/~gyarfas/Cikkek/182_jcd1.pdf) · [Question 2.8 in *Problems close to my heart*](https://real.mtak.hu/162708/1/ejc40.pdf).

**Theorem.** In every red–blue coloring of the blocks of any Steiner triple system of order $n>1$, the number $L$ of monochromatic sails satisfies
```math
 (294n-288)L\ \ge\ n(n-1)\big[n(n-3)-81(n-1)\big].
```
In particular every such coloring has a monochromatic sail for $n\ge84$. As $n$ tends to infinity through admissible orders, at least $(1/49-o(1))$ of all sails are monochromatic. Each sail has a unique center and a unique transversal block, so it is counted once.

## Count the spokes at each point

Give the pair $xy$ the color of its unique block. Let $d_R(x)$ and $d_B(x)$ count the red and blue neighbors of $x$. Their sum is $n-1$, and the red and blue block degrees of $x$ are $d_R(x)/2$ and $d_B(x)/2$. Put
```math
 D=\sum_x\big(d_R(x)-d_B(x)\big)^2.
```
For each nonincident point–block pair $(p,T)$, let $j(p,T)$ count the points $x\in T$ such that $px$ has the color of $T$. Thus $L$ counts $j=3$. Write $S$ for the number of pairs with $j=1$.

Call $(p,T)$ mixed when the three pair colors from $p$ to $T$ include both colors. At fixed $p$, every pair consisting of a red and a blue neighbor belongs to a block avoiding $p$. Each mixed block accounts for two of these pairs. The total number $M$ of mixed pairs therefore satisfies
```math
 2M=\sum_p d_R(p)d_B(p).
```
Write $J=\sum_{p\notin T}j(p,T)$, summed over all points and blocks. For a neighbor $p$ of $x$ of color $c$, exactly $d_c(x)/2-1$ blocks through $x$ have color $c$ and avoid $p$. Hence
```math
 J=\tfrac12\sum_x(d_R(x)^2+d_B(x)^2)-n(n-1).
```
The mixed pairs have $j=1$ or $2$ and the others have $j=0$ or $3$. Consequently $J=2M-S+3L$, giving the identity
```math
 S=3L+n(n-1)-D/2. \tag{1}
```

## Opposite-colored blocks force an odd spoke count

Take disjoint blocks $T$ red and $U$ blue. Count the red pairs between them in a $3$-by-$3$ array. If all six values $j(p,T)$ for $p\in U$ and $j(q,U)$ for $q\in T$ were even, each row indexed by $p\in U$ would have an even number of reds. Each column indexed by $q\in T$ would have an even number of blues, hence an odd number of reds. The same array would have an even and an odd total number of reds. Thus some cross point–block pair has $j=1$ or $3$.

Let $r,b$ be the total numbers of red and blue blocks. The number of intersecting red–blue block pairs is $\sum_x d_R(x)d_B(x)/4\le n(n-1)^2/16$. Each of the $S+L$ odd point–block pairs certifies at most $(n-1)/2$ disjoint red–blue block pairs since this is the total number of blocks through its point. By (1),
```math
 rb\le \frac{n(n-1)^2}{16}+\frac{n-1}{2}(S+L)
    \le\frac{9n(n-1)^2}{16}+2(n-1)L. \tag{2}
```

## Combine the counts

Each block contributes six to the sum of its color’s pair degrees. Thus $r+b=n(n-1)/6$ and $6(r-b)=\sum_x(d_R(x)-d_B(x))$. By Cauchy–Schwarz, $36(r-b)^2\le nD$. Since $S\ge0$, (1) gives $D\le6L+2n(n-1)$. It follows that
```math
 rb=\tfrac14\big((r+b)^2-(r-b)^2\big)
 \ge\frac{n^2(n-1)(n-3)-6nL}{144}. \tag{3}
```
Combining (2) and (3) yields the theorem. Its right side is positive for integer $n\ge84$. The total number of sails is $n(n-1)(n-3)/6$, the number of choices of a block and an outside point. Dividing by this quantity gives the limiting fraction.

## Vertex-disjoint monochromatic sails

Granath and coauthors also asked about disjoint unions of Ramsey configurations. For the sail the bound above gives a linear packing in one color. Each point belongs to exactly $7(n-1)(n-3)/6$ sails. As center it has $(n-1)(n-3)/6$ choices of a transversal block. As a point on the transversal it has $(n-1)(n-3)/2$ choices of that block and the center. In the remaining role choose the center $p$ in $n-1$ ways. Its block with the specified point fixes the intersection point on the transversal, through which there are $(n-3)/2$ allowable transversal blocks. These three roles exhaust the sail’s seven vertices.

One color supplies at least $L/2$ sails. Greedily choose disjoint sails of that color. Each selected sail removes at most $49(n-1)(n-3)/6$ candidates, by summing the point incidences over its seven vertices. Thus in every red–blue coloring there are at least $3L/[49(n-1)(n-3)]$ pairwise vertex-disjoint sails of one color for $n>3$. In particular this is at least $(1/4802-o(1))n$ as $n$ grows. Any fixed disjoint union of sails is therefore 2-Ramsey. [Original disjoint-copy question, §5](https://users.renyi.hu/~gyarfas/Cikkek/182_jcd1.pdf).

The theorem answers the stated two-color question for all Steiner triple systems. The corresponding question for three or more colors is separate.
