The extension tex_math_single_backslash is not supported for gfm
# Tuite–Thomas–Chandran circulant conjecture

**Exact order spectrum.** There is a circulant of diameter two and monophonic position number two precisely for $n\in\{4,5,8\}$ or $n\ge11$ with $n\ne15$.

The literal [Tuite–Thomas–Chandran Conjecture 4.5](https://oro.open.ac.uk/92086/13/92086final.pdf#page=21) asserted existence for every $n\ge11$. [Kang’s preprint](https://mathdb.com/pdf/2611.00020v1) already disproves that statement by showing that order 15 is impossible, and supplies a finite positive screen through order 40. The new part below is an explicit, uniform existence proof for all remaining orders, not a new disproof or a larger numerical cutoff.

## Reduction to neighborhoods

On $\mathbb Z_n$ take the circulant with a nonempty symmetric jump set $S$ not containing zero. The open neighborhood of $v$ is $v+S$ modulo $n$. Our sets have $S\cap(S-S)=\varnothing$ and $S\cup(S-S)=\mathbb Z_n$, so the graph is triangle-free of diameter two.

For independent vertices $x,y,z$, call a vertex *private to $x,y$* if it is in both of their neighborhoods but not in the neighborhood of $z$. If two pairs have private vertices, then after relabeling the pairs as $xy,yz$ the induced path $x,u,y,v,z$ witnesses the triple: $u,v$ are nonadjacent since both neighbor $y$ in a triangle-free graph, and every other potential chord is excluded by independence or privacy. Any triple with two edges is already an induced path. A triple with exactly one edge $xy$ and isolated $z$ lies on $x,y,u,z$ for a common neighbor $u$ of $y,z$; triangle-freeness excludes the chord $xu$. It follows that two private pairs for every independent triple suffice for monophonic position number two.

## The unbounded families

In the following table all intervals are integer intervals and taken modulo $n$. The small orders outside the displayed ranges are dealt with separately.

| Order | Minimum parameter | Jump set $S$ |
|---|---:|---|
| $3k-1$ | $k\ge4$ | $[k,2k-1]$ |
| $3k+1$ | $k\ge5$ | $[k,2k+1]\setminus\{k+1,2k\}$ |
| $3k$ | $k\ge10$ | $[k-1,2k+1]\setminus\{k,k+2,2k-2,2k\}$ |

Every set is symmetric. A triangle would yield three jumps with sum $n$ or $2n$ as ordinary integers; negating the jumps reduces the latter to the former. For $3k-1$ the minimum sum exceeds $n$. For $3k+1$ the only possible pattern is $(k,k,k+1)$, and $k+1$ is deleted. For $3k$ each jump in a sum of $n$ must be at most $k+2$, so all three must be in $\{k-1,k+1\}$; their sum cannot be $3k$.

We check distance two using only positive nonjumps at most $n/2$, since differences are symmetric. For $3k-1$ they are $1,\ldots,k-1$, all interval differences. For $3k+1$ they are $1,\ldots,k-1,k+1$: difference 1 occurs in the middle interval, differences $2,\ldots,k-1$ are the middle interval minus $k$, and $k+1$ is the difference of the extremes. For $3k$ they are $1,\ldots,k-2,k,k+2$: differences 1 and 3 occur in $[k+3,2k-3]$, difference 2 is $(k+1)-(k-1)$, differences $4,\ldots,k-2$ are the middle interval minus $k-1$, difference $k$ is $(2k-1)-(k-1)$, and $k+2$ uses the extremes.

### Triples in a short arc

Write $S=L+F$ with $L=\min S$ and $F\subseteq[0,d]$, where $d=\max S-L$. A triple fitting in an arc of length $d$ can be rotated to $0,a,c$ with $c=a+b\le d$ and $a,b>0$. Two ways to find a vertex private to $0,a$ are:
- Pick $w=L+a+j$ with $j<b$ and $j,a+j\in F$. Then $w<L+c$ and cannot belong to $c+S$ even modulo $n$: the wrapped part of $c+S$ stops below $L$ in all three families, since $\max S+d-n<L$.
- Pick $w=L+c+h$ with $h\in[0,d]\setminus F$ and $b+h,c+h\in F$. This avoids $c+S$ using its hole $h$.

In both cases $w\in S\cap(a+S)$. Reflection around the endpoints exchanges $a$ and $b$, so it suffices to prove a private vertex for $0,a$ at each ordered pair of gaps. For $3k-1$, always take $j=0$. For $3k+1$ the holes of $F$ are $1,k$ and the short nonjumps are $1,\ldots,k-1,k+1$. Take $j=0$ unless $a=1$. If $a=1$ and $b\ge3$, take $j=2$; if $a=1$ and $b\in\{1,2\}$, take $h=1$.

For $3k$ the holes of $F$ are $1,3,k-1,k+1$ and the short nonjumps are $1,\ldots,k-2,k,k+2$. The following assignments cover all cases. Each proposed hole is a hole of $F$, and the two required indices lie in $F$ since $k\ge10$.

| Gap $a$ | Other gap $b$ | Assignment |
|---|---|---|
| $a\notin\{1,3\}$ | any | $j=0$ |
| $a=1$ | $b\ge5$ | $j=4$ |
| $a=1$ | $b=1,2$ | $h=3$ |
| $a=1$ | $b=3,4$ | $h=1$ |
| $a=3$ | $b\ge3$ | $j=2$ |
| $a=3$ | $b=1,2$ | $h=3$ |

### Triples not in a short arc

Consider the three positive cyclic gaps of an independent triple. Each gap or its complement lies among short nonjumps. A gap at least $n-d$ would put all three in a short arc, so for the cases left here every gap must itself be a short nonjump.

For $3k-1$ all three gaps would be at most $k-1$, impossible. For $3k+1$ the only short-nonjump sum of $3k+1$ is the multiset $(k-1,k+1,k+1)$. Rotate and reflect to the triple $0,k-1,2k$. Vertex $k$ is private to $0,2k$: its two signed differences are $k,-k\in S$, and its difference from $k-1$ is 1. Reflection fixing $2k$ and exchanging $0,k-1$ provides the second private pair.

For $3k$ the gap multisets are $(k,k,k)$, $(k-2,k,k+2)$, and $(k-4,k+2,k+2)$. Indeed the only short nonjumps exceeding $k-2$ are $k,k+2$, and then the sum determines each possibility. Here are their witnesses:
- For $0,k,2k$, vertex $2k-1$ is private to $0,k$, with jumps $2k-1,k-1,-1$ to the respective vertices. Translating by $k$ gives the other pairs.
- For $0,k-2,2k-2$, vertex $2k-3$ is private to $0,k-2$, with jumps $2k-3,k-1,-1$. Vertex $3k-3$ is private to $k-2,2k-2$: its jumps are $2k-1,k-1$, but $3k-3\notin S$.
- For $0,k-4,2k-2$, vertex $k-1$ is private to $0,2k-2$, with jumps $k-1,-(k-1)$ and with jump 3 from the middle vertex. Reflection fixing $2k-2$ and exchanging $0,k-4$ gives the second pair.

This proves the two-private-pair criterion for all orders in the table.

## Small orders and originality boundary

At orders $4,5,8,12,13,18,21,24,27$ take symmetric jump magnitudes, respectively
\[
\{1\},\ \{1\},\ \{1,4\},\ \{2,3\},\ \{2,3\},\ \{3,4,5\},\
\{3,4,5\},\ \{4,5,6,7\},\ \{4,5,6,7\}.
\]
Their exact diameter, triangle-freeness and private-pair conditions can be checked by testing $S-S$ and the triples containing zero. For all other orders below 30, either an unbounded formula already applies or there is no valid graph. Specifically, the original paper’s Theorem 4.4 rules out orders 6, 7, 9 and 10 even without the circulant restriction; orders 1 and 2 have no connected graph of diameter two; the only connected circulant of order 3 is complete. At order 15 the previous proof is also short to replay: test the $2^7$ symmetric nonzero jump choices against triangle-freeness and diameter two. Only the two choices with magnitudes $\{1,4,6\}$ or $\{2,3,7\}$ survive, both blow-ups of a 5-cycle with an independent class of three vertices. These are open twins. An induced path can contain at most two of them, as each neighbor of one is adjacent to all of them, so the triple is monophonic.

The finite source checks and prior order-15 refutation are credited. Searches under the exact title, conjecture number, jump-set/circulant terminology, the latest survey, MathDB and Hexagon found no prior unbounded existence construction covering the three classes. This completes the order spectrum through a uniform symbolic construction, but is not counted as a new literal refutation of Conjecture 4.5. [Tracking issue #845](https://github.com/1337isnot1337/solved-conjectures/issues/845).
