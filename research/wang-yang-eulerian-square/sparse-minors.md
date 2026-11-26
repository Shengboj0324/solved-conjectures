# Infinite submatrices with all mixed minors positive

Let $E(a,b)$ count permutations with $a$ ascents and $b$ descents. The following gives mixed minors of unbounded order for [Wang–Yang’s Eulerian square conjecture](README.md).

**Theorem.** Let $(u_i)$ and $(v_j)$ be increasing unbounded sequences of positive integers. Suppose each sequence, written $(x_i)$, eventually satisfies

```math
 x_{i+1}\le2x_i,\qquad
 x_{i+1}-x_i\ge12\sqrt{x_i}\,(\log x_i)^{1/4}.
```

After deleting a finite initial part of the row and column sequences, the infinite matrix $[E(u_i,v_j)]$ is strictly totally positive. In particular both axes can use $x_i=\lceil i^2\log(i+2)\rceil$. The two sets of indices may be chosen independently. Every finite square minor of the resulting matrix is positive, with no restriction on its order or its distance from the diagonal. The unrestricted conjecture remains open.

For the example, the successive differences are asymptotic to $2i\log i$ by the mean value theorem. The required lower bound has order $i(\log i)^{3/4}$, and the successive ratios tend to one. All logarithms below are natural.

## Cross ratios in two ranges

For adjacent values $a<a'$ of the row sequence and $b<b'$ of the column sequence write

```math
 Q=\frac{E(a,b)E(a',b')}{E(a,b')E(a',b)}.
```

We prove $Q\ge16$ uniformly once both starting indices are large. Symmetry allows us to suppose $a\ge b$. The [spline argument](README.md#arbitrary-row-and-column-pairs) shows that $E(a,b)/(a+b+1)!$ has nonnegative minors of order two. Hence $Q$ is at least the corresponding factorial cross ratio, and

```math
 \log Q\ge\sum_{r=a+1}^{a'}\log\!\left(1+\frac{b'-b}{r+b+1}\right)
 \ge\frac{(a'-a)(b'-b)}{a'+b'+1}.
```

The second bound uses $\log(1+x)\ge x/(1+x)$ for $x\ge0$. When $b\le a\le32b\log b$, the denominator is at most $5a$. The gap conditions give

```math
 \log Q\ge\frac{144}{5}\sqrt{b/a}\,(\log a\log b)^{1/4}
 \ge\frac{144}{5\sqrt{32}}>\log16.
```

When $a\ge32b\log b$, use the first term $P(x,y)=(y+1)^{x+y+1}$ of the Eulerian inclusion–exclusion formula at the four corners. The terms after it satisfy

```math
 \left|\frac{E(x,y)}{P(x,y)}-1\right|
 \le \sum_{h=1}^{y}\binom{x+y+2}{h}e^{-h(x+y+1)/(y+1)}
 \le \exp\!\bigl((x+y+2)e^{-(x+y+1)/(y+1)}\bigr)-1.
```

The expression inside the outer exponential is at most $(4a+2)e^{-a/(3b)}$ for $x\in\{a,a'\}$ and $y\in\{b,b'\}$. For $a\ge32b\log b$ this bound decreases as $a$ increases and tends uniformly to zero as $b\to\infty$. Thus all four relative errors are at most $1/10$ for large $b$. The cross ratio of $P$ is exactly $((b'+1)/(b+1))^{a'-a}$, so

```math
 \log Q\ge (a'-a)\frac{b'-b}{b'+1}+2\log(9/11).
```

Here the first term is at least $48\sqrt{a/b}(\log a\log b)^{1/4}$ since $b'+1\le3b$. This exceeds $\log16-2\log(9/11)$ uniformly for all sufficiently large $b$.

## All orders

For any larger rectangle, its log cross ratio is the sum of those for its adjacent rectangles by cancellation. Hence all cross ratios in the retained infinite matrix are at least 16. Take any finite square submatrix $M$ in increasing index order. Positively scale its columns in succession and then divide each row by its diagonal entry so that the resulting matrix $K$ has diagonal one and

```math
 K_{i,i+1}=K_{i+1,i}
 =\sqrt{\frac{M_{i,i+1}M_{i+1,i}}{M_{ii}M_{i+1,i+1}}}\le\tfrac14.
```

Explicitly, the ratio of the column multipliers $c_{i+1}/c_i$ is the square root of $M_{ii}M_{i+1,i}/(M_{i,i+1}M_{i+1,i+1})$. Positive cross ratios greater than one make the ratios of successive columns nondecreasing down the rows. Thus, moving rightwards from the diagonal in row $i$, each entry is at most one fourth the preceding entry, by comparison with the corresponding ratio in the row beginning on that diagonal position. Moving leftwards gives the same bound with the reciprocal ratios. Therefore $K_{ij}\le4^{-|i-j|}$ and the sum off the diagonal of every row is at most $2/3$. Multiplying all off-diagonal entries by a parameter in $[0,1]$ preserves strict diagonal dominance, so the determinant cannot vanish along this path from the identity. It is positive at the endpoint. Positive scaling preserves its sign, proving the theorem.
