# Welton–Khudairi–Tuite lower general position product conjecture

**Status: partial.** This note proves the bound whenever its right-hand side is at most four. More generally, for all finite connected graphs,
$$
 \operatorname{gp}^-(G\square H)\ge
 \min\{4,\operatorname{gp}^-(G),\operatorname{gp}^-(H)\}.
$$
It also gives an unrestricted criterion when a small maximal set has a suitable projection. It does not prove Conjecture 2.10 in full.

The primary source is [Welton–Khudairi–Tuite, *Lower General Position in Cartesian Products*, Conjecture 2.10](https://arxiv.org/html/2404.19451#S2). [The survey](https://arxiv.org/abs/2501.19385) repeats it as Conjecture 5.14. The original paper reports tests through factor order six; the argument here holds at all factor orders and is independent of those computations.

## Product orientations and a projection test

Write $L(a,b)$ for the line determined by distinct vertices $a,b$: all $x$ such that one of (a,b,x) lies between the other two. When $x\notin\{a,b\}$, the middle type of $x$ on that line is unique; name its three possible values $a,b,*$, with $*$ denoting the candidate. At an endpoint, both appropriate middle types are allowed, so the distance equality convention works also for repeated coordinates.

The distance in the Cartesian product is the sum of factor distances. Thus a betweenness for three product vertices holds precisely when its middle type is allowed in both factors. Indeed, the nonnegative triangle slacks in the two coordinates add, and their sum is zero precisely when both vanish.

Let $S$ be general position in the product with projection $P$ that is general position in $G$. If $|S|<\operatorname{gp}^-(G)$, then $|P|\le |S|$ and $P$ can be extended by some $x\notin P$. At that $x$, no pair of elements of $S$ with different first coordinates can witness collinearity with $(x,y)$, for any $y$. Thus if the first projection is injective, $S$ is not maximal. More generally, if $|S|<\operatorname{gp}^-(H)$ and there is at most one pair with repeated first coordinate, choose $y$ outside the line of its two different second coordinates. This line is nonuniversal since the pair is a general-position set of size less than $\operatorname{gp}^-(H)$. Then $(x,y)$ extends $S$.

## No maximal triple below both factor numbers

Assume both factor numbers exceed three and $S=\{(a_i,b_i):i=0,1,2\}$ is general position. If one projection has all coordinates equal, the other projection is injective and general position, so the projection test applies. If one projection has exactly two images, it is general position and exactly one pair repeats a coordinate, so the test again applies. The test also covers a three-vertex projection that is general position.

It remains that each projection is a triple of distinct collinear vertices. Their middle indices differ, since $S$ is general position. Relabel so $a_0$ lies between $a_1,a_2$, and $b_1$ between $b_0,b_2$. Put
$$
 X=V(G)\setminus L(a_1,a_2),\qquad
 Y=V(H)\setminus L(b_0,b_2).
$$
Both are nonempty. Fix $x\in X,y\in Y$. Maximality would require some pair of $S$ blocking $(x,y)$. Pair 12 cannot block it in the first factor, and pair 02 cannot block it in the second. Consequently pair 01 must block it with a shared, unique middle type $m\in\{0,1,*\}$.

**Metric observation.** Let $a_0$ be between $a_1,a_2$, and $x\notin L(a_1,a_2)$. If $x\in L(a_0,a_1)$ with middle type $0$ or $*$, then $x$ cannot be on $L(a_0,a_2)$ with type $2$ or $*$. To see this, set $p=d(a_0,a_1)$, $q=d(a_0,a_2)$, and $r=d(x,a_0)>0$. The forbidden second condition gives $d(x,a_2)=|q-r|$. If the first condition has type 0, $d(x,a_1)=p+r$. For $r\le q$ the two distances sum to $p+q$, and for $r>q$ they differ by $p+q$, putting $x$ on the excluded line. If the first condition has type $*$, $d(x,a_1)=p-r$ and $r\le p$. For $r\le q$, their sum is $p+q-2r<p+q$; for $r>q$ it is $p-q<p+q$. Both contradict the triangle inequality.

Now look at $(x,b_2)$. Pair 12 still cannot block it. Pair 01 can block it only if $m=1$, because $b_1$ is the middle in the second projection. For pair 02, the second coordinate $b_2$ allows only types $2$ and $*$. If $m=0$ or $m=*$, the metric observation excludes both of these for the first coordinate. Hence maximality forces $m=1$. But applying the same argument in the swapped factors, exchanging indices 0 and 1, to $(a_2,y)$ forces $m=0$. Contradiction.

The analogous pair argument is immediate: a product pair has two distinct coordinates in at least one factor, and if that pair is not maximal in the factor, any point off its line extends the product pair. A singleton extends unless the product consists of one vertex. This completes the bound.

## Remaining case

Any counterexample must therefore have a maximal product general-position set of size at least four, with more than one repeated-coordinate pair in every general-position projection used by the above test. Two non-general-position projections can obey several different, nonmatching middle orientations; this proof does not force them into the three-point obstruction.
