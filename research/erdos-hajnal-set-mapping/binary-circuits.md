# Common circuits obstruct a binary construction

A single binary matroid of rank at most $h-1$ on $X$ supplies witnesses for one color in the Erdős–Hajnal problem. Every $h$-set contains a circuit, meaning a minimal nonempty set of columns with binary sum zero. One might give a different matroid to each color and color its circuits accordingly. The obstruction below applies even if loops and parallel columns are allowed.

**Theorem.** Suppose $q\ge6$ binary matroids on the same $n$ labeled elements have ranks at most $r$, and no two of them have a common circuit. There is an integer $m\ge\min(n,q)/112$ with

```math
 \binom m3\le 2^{2r}.
```

Consequently, on $n$ elements, $n-1$ such matroids require $r\ge\tfrac32\log_2 n-O(1)$.

## Two simple restrictions

Let $\ell_i$ and $e_i$ count the one- and two-element circuits in matroid $i$. Disjointness gives $\sum_i\ell_i\le n$ and $\sum_i e_i\le\binom n2$. Pick the two matroids with the smallest values of $\ell_i/n+e_i/n^2$. The sum of their two values is at most twice the average and hence at most $3/q$.

Discard their loops, leaving $N\ge n-3n/q\ge n/2$ elements. Join two remaining elements by an edge if their columns agree in either representation. Each such equality is a two-element circuit there. This graph has at most $3n^2/q$ edges. A graph with $N$ vertices and $e$ edges has an independent set of size at least $N^2/(N+2e)$, as follows by putting the vertices in random order and keeping each vertex that precedes all its neighbors, followed by Cauchy–Schwarz. Thus there is a common restriction of size at least

```math
 \frac{(n/2)^2}{n+6n^2/q}
 =\frac{nq}{4q+24n}\ge\frac{\min(n,q)}{28}.
```

On this restriction the columns are nonzero and distinct in each representation.

## A common circuit from two triples

Write the columns as $a_x$ and $b_x$ in two copies of $\mathbb F_2^r$, padding with zero coordinates if necessary. Choose a uniform random linear functional on each copy, independently. Every retained element satisfies both equations $u(a_x)=v(b_x)=1$ with probability $1/4$. Fix a choice for which the set $W$ of such elements has size $m\ge\min(n,q)/112$.

In either representation on $W$, every nonempty zero-sum set has even size, by applying the chosen functional. Its size is at least four, by the distinctness of the columns. In particular a zero sum of size at most six is a circuit. A proper zero-sum subset would split it into two disjoint nonempty zero sums, each of size at least four.

Map each three-element subset $T$ of $W$ to $(\sum_{x\in T}a_x,\sum_{x\in T}b_x)$. A collision of two distinct triples would make their symmetric difference a nonempty zero sum of size at most six in both representations. This would be a common circuit. The map is therefore injective and its codomain has $2^{2r}$ elements. Finally $(m-2)^3/6\le\binom m3$ for $m\ge2$, which gives the claimed logarithmic bound.

## Allowing arbitrary choices inside each nullspace

The same obstruction applies if a color uses only nonempty zero sums of a binary matrix of **rank exactly** $h-1$, even when its designer can discard any unwanted zero sums subject to covering every $h$-set. To see this, take a circuit $C$. Extend the independent columns of $C$ minus one element to a basis of the whole matrix. Adjoining the omitted element gives an $h$-set of columns with nullity one, on which $C$ is the unique nonempty zero sum. The color has to use $C$. If two such colors had a common circuit, the same subset would have to receive both colors. At most one color can use the empty set, so the conclusion still applies if that color is omitted.

Thus $n$ color classes obtained this way require $h\ge\tfrac32\log_2 n-O(1)$. The matching construction achieves $h\le\log_2 n+\log_2\log_2 n+O(1)$ with unrestricted classes. The rank-exact assertion leaves open methods using lower-rank matrices from which a selection of circuits can be discarded, and general nonlinear color classes. [Matching construction and original question](README.md).

Chee, Etzion, Kiah and Vardy use subspaces of dimension $n-h+1$ with zero removed to build cooling codes, and note that such subspaces cannot be globally disjoint when their dimension exceeds $n/2$. The proof above permits arbitrary overlap on unused words and forces a conflicting circuit on at most six coordinates for the two selected matrices when the inequality fails. [Cooling codes, §§IV-D and IV-F](https://ymchee66.github.io/home/PDF/coolingjournal.pdf).
