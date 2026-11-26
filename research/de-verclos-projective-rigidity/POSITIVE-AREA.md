# Rigidity from positive area of one support

**Theorem.** Let $`\mu,\nu`$ be Borel probability measures in the plane, each giving zero mass to every affine line. Suppose their iid order-type distributions agree at all finite sizes. If the support of $`\mu`$ has positive planar Lebesgue measure, then an invertible real projective transformation $`P`$ satisfies $`\nu=P_*\mu`$. Neither measure needs a density or bounded support. For example, the theorem applies when the support is a compact set of positive area and empty interior. The full dimensional threshold in [de Joannis de Verclos’s conjecture](https://arxiv.org/abs/1811.02236) also includes zero-area supports.

Use the [strict secant lemma and the coupling relation](SECANTS.md). Let $`R`$ denote that relation, $`E=\operatorname{supp}\mu`$, and $`E_0\subset E`$ a bounded compact portion of positive area. Let $`f`$ be its Borel selector. The preimage of the target equator has dimension at most one. By inner regularity and Lusin’s theorem for **area on $`E_0`$**, choose a positive-area compact $`K\subset E_0`$ on which $`f`$ is continuous and takes values in the finite chart. Write $`K^*`$ for the planar density-one points of $`K`$ belonging to $`K`$.

## Incidence at a density point

For distinct collinear $`q,r,x`$ with $`q\in K^*`$ and arbitrary $`(r,w),(x,z)\in R`$, the projective points $`[f(q)],[w],[z]`$ are collinear. Indeed there are points of $`K`$ approaching $`q`$ from both sides of $`rx`$ since $`q`$ has density one. The source orientations have opposite signs along the two sequences. Continuity of $`f`$ on $`K`$ and inequality (1) of the secant argument force the common limiting target determinant to vanish. The target representatives may lie on the equator.

Fubini supplies a single line $`L`$ containing three different points $`a,b,c\in K^*`$. Their finite images are distinct by injectivity and collinear by incidence. Make projective chart changes in source and target taking the two lines to infinity and sending the three corresponding directions, in order, to horizontal, vertical and slope one. These choices exist because the projective group of a line acts transitively on ordered triples of distinct points, and each such line map extends to a plane projectivity. $`L`$ and the preimage of the corresponding target line have zero area. On their complement we may therefore choose a compact positive-area portion of $`K`$ inside the two charts, with bounded image. Source chart changes are local diffeomorphisms and preserve positivity of area there. Call the transformed compact set $`A`$ and the transformed selector $`T`$.

Two points of $`A`$ on a horizontal line have images on a horizontal line by incidence at $`a`$. The same holds for the vertical and slope-one directions using $`b,c`$. Only incidence is used after the chart changes. Thus there are bounded functions $`F,G`$ on the two coordinate projections such that $`T(x,y)=(F(x),G(y))`$, and

```math
F(x+h)-F(x)=G(y+h)-G(y) \quad\text{whenever }(x,y),(x+h,y+h)\in A. \tag{2}
```

## Local functional equation on a planar set of positive area

Choose a density square $`I\times J`$ of side $`d`$ in which the missing area of $`A`$ is less than $`10^{-8}d^2`$. Let $`I_0,J_0`$ be the concentric intervals of length $`d/2`$. Let $`X\subset I_0`$ consist of columns missing at most $`d/100`$ of $`J`$ and define $`Y\subset J_0`$ by the analogous row condition. Fubini gives $`|I_0\setminus X|,|J_0\setminus Y|<10^{-6}d`$.

Fix $`|h|<d/8`$. For any $`x_1,x_1+h,x_2,x_2+h\in X`$, choose $`y,y+h\in J`$ so that $`(x_i,y),(x_i+h,y+h)\in A`$ for both $`i`$. The four column exceptions have total length at most $`4d/100`$, and $`|J\cap(J-h)|\geq7d/8`$. Equation (2) shows that $`F(x+h)-F(x)`$ has a common value $`D(h)`$ for all $`x,x+h\in X`$. At least one such pair exists by the bound on $`I_0\setminus X`$. For $`y,y+h\in Y`$, choose $`x,x+h\in X`$ with $`(x,y),(x+h,y+h)\in A`$. Inside $`I_0\cap(I_0-h)`$ the two bad rows exclude at most $`2d/100`$ and the two translates of the column exception exclude less than $`2\cdot10^{-6}d`$. Hence $`G(y+h)-G(y)=D(h)`$ as well.

For $`|h|,|k|,|h+k|<d/16`$, some $`x,x+h,x+h+k`$ all belong to $`X`$. The three translated central intervals have overlap of length at least $`d/2-2d/16`$, and their three exceptions have total length below $`3\cdot10^{-6}d`$. Telescoping yields $`D(h+k)=D(h)+D(k)`$. This locally additive function is bounded by $`2\sup|F|`$, hence continuous at zero: for any positive integer $`m`$, $`m|D(h)|=|D(mh)|\leq2\sup|F|`$ whenever $`m|h|<d/16`$. Additivity, rational multiples and continuity give $`D(h)=s h`$ on $`(-d/16,d/16)`$ for one real $`s`$.

On the concentric subintervals of length $`d/64`$, all differences between members of $`X`$ are in this range, as are all differences between members of $`Y`$. There $`F(x)=sx+t`$ on $`X`$ and $`G(y)=sy+u`$ on $`Y`$. The resulting central square has area $`d^2/4096`$. Removing the missing part of $`A`$ and the two exceptional strips removes at most $`(10^{-8}+2\cdot10^{-6})d^2`$, so a set of positive area remains. On it $`T`$ agrees with $`(x,y)\mapsto(sx+t,sy+u)`$. Injectivity forces $`s\ne0`$. Conjugating by the two chart maps gives an invertible projectivity $`P`$ agreeing with the original $`[f]`$ on a measurable positive-area set $`B\subset K`$. Discard $`B\setminus K^*`$, which is null.

## Extension to the entire correspondence

Take any $`(x,z)\in R`$. Polar-coordinate Fubini about $`x`$ gives at least two different lines through $`x`$ each containing a positive-length set of points of $`B`$ away from $`x`$. On each such line choose distinct $`q,r\in B\setminus\{x\}`$. Incidence at $`q`$ places $`[z]`$ on $`P(q)P(r)`$, the image of this line. The two distinct image lines meet precisely at $`P(x)`$ in the projective plane. Thus $`[z]=P(x)`$ for every pair in $`R`$. The coupling has marginals $`\mu`$ and $`j_*\nu`$, so $`\nu=P_*\mu`$. Any pole line has $`\mu`$-mass zero. This concludes the proof.

The use of positive area is explicit in the density-point incidence argument, the selection of three anchors, the two-dimensional functional equation and the final polar slices. The secant and coupling results already apply at Hausdorff dimension greater than one. The zero-area case of the conjecture remains open here.
