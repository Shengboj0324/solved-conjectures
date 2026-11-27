# A power gap for designs represented over any field

**Theorem.** There are absolute constants $c,\epsilon>0$ such that every noncollinear set of $v$ points in a projective plane over **any field** spans at least $c v^{1/2+\epsilon}$ lines of a single size. The field may vary arbitrarily with $v$. Consequently an abstract Erdős–Purdy construction at the conjectured square-root scale would have to use designs unrepresentable over fields.

The original problem allows every finite linear space. In particular it imposes neither Desargues' theorem nor representability. This is a necessary condition for a solution to the original problem. [Erdős and Purdy, §2](https://users.renyi.hu/~p_erdos/1978-42.pdf) · [Erdős problem 734](https://www.erdosproblems.com/734).

## A line of directions with small projections

Write $b$ for the number of spanned lines, $M$ for the maximum size multiplicity and $K=\max(2,b/v)$. Constants implicit in $K^{O(1)}$ have absolute exponents. We will show, whenever $v$ exceeds a fixed polynomial in $K$, that $M\gg v^{3/4}/K^{O(1)}$.

If a line contains at least $v/2$ points, the [ordinary-line argument](profiles.md) gives $M\ge v/2$ and proves the assertion. Otherwise every line has size at most $2I/v$, where $I$ is the total number of incidences. Indeed, each point off a $k$-point line determines $k$ different lines meeting it. By the pair identity and Cauchy–Schwarz, $I\le b+v\sqrt b\le 2\sqrt K v^{3/2}$ when $v\ge K$. Hence the maximum line size is at most $4\sqrt{Kv}$. At least $3v/4$ points have degree at most $8\sqrt{Kv}$. Among the $b\le Kv$ lines, one contains at least $c\sqrt{v/K}$ of these low-degree points, by counting their pairs. Send this line to infinity by a projectivity. Its size bound leaves at least $v/2$ affine points when $v$ exceeds a fixed multiple of $K$.

An invertible linear coordinate change makes three of the selected directions vertical, horizontal and of slope one. This follows from the action of projectivities on triples on a projective line, or by choosing the first two as coordinate axes and rescaling one axis. Every line in a selected direction containing an affine point joins that point to the selected point at infinity. Thus there are at most $8\sqrt{Kv}$ nonempty parallel lines in each such direction. The vertical and horizontal directions put the affine points in a grid $A\times B$ with $|A|,|B|\le L=\lceil8\sqrt{Kv}\rceil$. There are $\gg\sqrt{v/K}$ selected finite slopes, including $0,1$. The [small-projections lemma](small-projections.md) applies with $\delta=c_0/K$ for a sufficiently small absolute $c_0$. Its threshold is met when $v$ is sufficiently large polynomially in $K$.

We obtain a translate of $\lambda H\times\lambda H$ over a finite subfield $H$ of order $q$, containing $u\ge v/K^{O(1)}$ of our points, with

```math
 \sqrt v/K^{O(1)}\ll q\ll K^{O(1)}\sqrt v.
```

Take the projective closure of this affine subplane. An invertible projectivity of the ambient plane sends it to the standard copy of $\mathrm{PG}(2,H)$. Include all original points on this projective subplane in $u$, which preserves the lower bound.

## Keeping track of all points outside the subplane

There are $N=q^2+q+1$ subplane lines. Extend them to ambient lines. Two distinct extensions intersect at a point of the subplane, since their linear equations are defined over $H$ in the standard coordinates. Consequently each point outside the subplane belongs to at most one extension. A uniform subplane line has subplane occupancy $X$ with mean $a=u(q+1)/N$ and variance at most $a$ by [the exact plane variance](prime-planes.md). The number $Z$ of additional original points on its extension has mean at most $v/N$.

Chebyshev and Markov imply that at least $N/2$ extensions have $|X-a|\le2\sqrt a$ and $Z\le4v/N$. The bound is immediate also when there are no outside points. Here $a\gg\sqrt v/K^{O(1)}$, so for $v$ sufficiently large polynomially in $K$ these are all spanned lines. Their full sizes belong to an interval containing at most $1+4\sqrt a+4v/N$ integers. Using $a\le q+1$, $N\gg v/K^{O(1)}$ and the upper bound for $q$ gives

```math
 M\gg \frac{N}{1+\sqrt a+v/N}\gg \frac{v^{3/4}}{K^{O(1)}}.
```

Finally [the elementary line-count bound](prime-planes.md) gives $K\ll 1+(M/\sqrt v)^{2/3}$. Fix $\epsilon>0$ sufficiently small. If $M\le v^{1/2+\epsilon}$, then $K\ll v^{2\epsilon/3}$, so every polynomial largeness requirement above holds for all sufficiently large $v$. The last lower bound then exceeds $v^{1/2+\epsilon}$ upon making $\epsilon$ smaller if necessary. This contradiction proves the theorem, with the constant $c$ absorbing bounded orders. For the sharp exponent in prime planes and the classical matching upper construction, see the [prime-plane argument](prime-planes.md).

The [exact finite checker](check_field.py) verifies the direction-energy identity for every one of the 65,536 subsets of the sixteen-element field over its four-element subfield. It enumerates every extended subplane line for four proper field inclusions and checks both the exterior-point bound and the exact variance on 126 restrictions. Run `python3 research/erdos-block-size-multiplicity/check_field.py` from the repository root.
